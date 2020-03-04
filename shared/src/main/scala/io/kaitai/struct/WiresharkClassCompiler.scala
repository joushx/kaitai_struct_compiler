package io.kaitai.struct

import io.kaitai.struct.datatype.DataType._
import io.kaitai.struct.datatype.LittleEndian
import io.kaitai.struct.exprlang.Ast.expr.{Bool, EnumByLabel, IntNum, Name}
import io.kaitai.struct.format.{AttrSpec, ClassSpec, ClassSpecs, EnumSpec}
import io.kaitai.struct.languages.components.{LanguageCompiler, LanguageCompilerStatic}

import scala.collection.mutable.ListBuffer

class WiresharkClassCompiler(classSpecs: ClassSpecs, topClass: ClassSpec) extends AbstractCompiler {

  val out = new StringLanguageOutputWriter(indentCharacter)

  override def compile: CompileLog.SpecSuccess = {
    generateEnums
    generateProtocolDefinition
    generateFieldDefinitions
    generateDissectionFunction

    CompileLog.SpecSuccess(
      "",
      List(CompileLog.FileSuccess(
        outFileName(topClass.nameAsStr),
        out.result
      ))
    )
  }

  def generateEnums = {
    topClass.enums.foreach(e => generateEnum(e))
  }

  def generateEnum(e: (String, EnumSpec)) = {
    val name = e._1
    val spec = e._2

    out.puts(s"local $name = {")
    spec.map.foreach(entry => {
      val key = entry._1
      val value = entry._2

      if(value.doc.summary.isDefined) {
        out.puts(s"${indentCharacter}-- ${value.doc.summary.get}")
      }
      out.puts(s"""${indentCharacter}[$key] = "${value.name}",""")
    })
    out.puts("}")
  }

  def generateProtocolDefinition = {
    val protocolName = dissectorName(topClass.nameAsStr)
    val name = topClass.nameAsStr
    out.puts(
      s"""
         |-- protocol definition
         |local $protocolName = Proto("$name", "$name")
         |""".stripMargin
    )
  }

  def generateFieldDefinitions = {
    val attributes = enumerateUniqueAttributes

    out.puts("-- field definition")
    attributes
      .filter(a => !a.dataType.isInstanceOf[UserTypeInstream] && !a.dataType.isInstanceOf[UserTypeFromBytes] && !a.dataType.isInstanceOf[SwitchType])
      .foreach(attr => {
      val fieldId = buildFieldName(attr.path)
      val fieldName = attr.id.humanReadable
      val abbr = buildAbbreviation(topClass.meta.id.get, attr.path, attr.id.humanReadable)
      var dataType = "bytes"
      attr.dataType match {
        case t: Int1Type => {
          dataType = if (t.signed) "int8" else "uint8"
        }
        case t: IntMultiType => {
          val width = t.width.width
          width match {
            case 2 => dataType = if (t.signed) "int16" else "uint16"
            case 4 => dataType = if (t.signed) "int32" else "uint32"
            case 8 => dataType = if (t.signed) "int64" else "uint64"
          }
        }
        case t: BytesLimitType => {
          dataType = "bytes"
        }
        case t: BooleanType => {
          dataType = "bool"
        }
        case t: EnumType => {
          t.basedOn match {
            case s: Int1Type => dataType = if (s.signed) "int8" else "uint8"
          }
          out.puts("-- todo: enum")
        }
        case _ => {
          println(attr.dataType)
        }
      }

      val doc = if (attr.doc.summary.isDefined) s""""${attr.doc.summary.get}"""" else "nil"

        if(dataType == "bytes") {
          out.puts(s"""local f${fieldId}_$fieldName = ProtoField.$dataType("$abbr", "$fieldName", nil, $doc)""".stripMargin)
        }
        else {
          out.puts(s"""local f${fieldId}_$fieldName = ProtoField.$dataType("$abbr", "$fieldName", base.DEC, nil, nil, $doc)""".stripMargin)
        }
    })

    out.puts(
      s"""
         |-- field registration
         |${dissectorName(topClass.nameAsStr)}.fields = {""".stripMargin)

    out.puts(indentCharacter + attributes.filter(a => !a.dataType.isInstanceOf[UserTypeInstream] && !a.dataType.isInstanceOf[UserTypeFromBytes] && !a.dataType.isInstanceOf[SwitchType])
      .map(a => {
      val fieldName = a.id.humanReadable
      val fieldId = buildFieldName(a.path)
      s"f${fieldId}_$fieldName"
    }).mkString(", "))

    out.puts("}")
  }

  def enumerateUniqueAttributes(): List[AttrSpec] = {
    val result = ListBuffer[AttrSpec]()
    enumerateAttributesForRoot(topClass, result)
    return result.result().distinct
  }

  /**
    * Get a list of attributes
    */
  def enumerateAttributesForRoot(parent: ClassSpec, result: ListBuffer[AttrSpec]): Unit = {
    parent.seq.foreach(attribute => {
      result += attribute

      attribute.dataType match {
        case t: UserTypeInstream => {
          enumerateAttributesForRoot(t.classSpec.get, result)
        }
        case t: UserTypeFromBytes => {
          val classSpec = t.classSpec.get
          enumerateAttributesForRoot(classSpec, result)
        }
        case t: SwitchType => {
          t.cases.foreach(c => {
            c._2 match {
              case t: UserTypeInstream => {
                enumerateAttributesForRoot(t.classSpec.get, result)
              }
              case t: UserTypeFromBytes => {
                enumerateAttributesForRoot(t.classSpec.get, result)
              }
              case _ => {
                out.puts(s"-- ${c._2}")
              }
            }
          })
        }
        case _ => {
          out.puts(s"-- ${attribute.dataType}")
        }
      }
    })
  }

  def generateDissectionFunction() = {
    val protocolName = dissectorName(topClass.nameAsStr)
    val name = topClass.nameAsStr
    out.puts(
      s"""
        |-- main dissector function
        |function $protocolName.dissector(tvb, pinfo, tree)
        |${indentCharacter}pinfo.cols.protocol:set("$name")
        |${indentCharacter}local root = tree:add($protocolName, tvb(0))
        |""".stripMargin
    )

    out.puts(s"${indentCharacter}local offset = 0")
    generateSeq(indentCharacter, "root", topClass.seq)

    out.puts("end")
  }

  def generateSeq(indent: String, parentName: String, specs: List[AttrSpec]) = {
    specs.foreach(spec => generateField(indent, parentName, spec))
  }

  def generateField(indent: String, parentName: String, spec: AttrSpec) = {
    //out.puts(s"${indent}-- ${spec.path.mkString(".")}")

    spec.dataType match {
      case t: UserTypeFromBytes =>
        generateUserTypeFromBytes(indent, parentName, spec, t)
      case t: SwitchType => {
        generateSwitchType(indent, parentName, spec, t)
      }
      case t: UserTypeInstream => {
        generateUserTypeIntstream(indent, parentName, spec, t)
      }
      case t: Int1Type => {
        generateInt1Type(indent, parentName, spec, t)
      }
      case t: IntMultiType => {
        generateIntMultiType(indent, parentName, spec, t)
      }
      case t: BytesLimitType => {
        generateBytesLimitType(indent, parentName, spec,  t)
      }
      case t: BooleanType => {
        generateBooleanType(indent, parentName, spec, t)
      }
      case t: EnumType => {
        generateEnumType(indent, parentName, spec, t)
      }
      case t: BitsType => {
        generateBitsType(indent, parentName, spec, t)
      }
      case t: BytesEosType => {
        out.puts(indent + "-- EOS?")
      }
      case t: StrFromBytesType => {
        generateStrFromBytesType(indent, parentName, spec, t)
      }
      case _ => {
        out.puts(s"${indent}-- ${spec.dataType.getClass.getName}")
      }
    }
  }

  def generateSwitchType(indent: String, parentName: String, spec: AttrSpec, switchType: SwitchType): Unit = {
    out.puts(s"${indent}local ${spec.id.humanReadable}_value = true --todo")

    switchType.cases.foreach(c => {
      c._1 match {
        case b: Bool => {
          out.puts(s"${indent}if (${spec.id.humanReadable}_value == ${b.n}) then")
        }
        case b: EnumByLabel => {
          out.puts(s"${indent}if(${spec.id.humanReadable}_value == ${b.enumName.name}[${b.label.name}]) then -- TODO")
        }
        case b: Name => {
          out.puts(s"${indent}if(${spec.id.humanReadable}) then")
        }
        case b: IntNum => {
          out.puts(s"${indent}if(${spec.id.humanReadable}_value == ${b.n}) then")
        }
        case _ => {
          out.puts(s"${indent}if (true) then -- TODO")
        }
      }

      c._2 match {
        case t: UserTypeInstream => {
          generateSeq(indent + indentCharacter, parentName, t.classSpec.get.seq)
        }
        case t: UserTypeFromBytes => {
          generateSeq(indent + indentCharacter, parentName, t.classSpec.get.seq)
        }
        case b: BytesEosType => {
          out.puts(s"$indent$indentCharacter-- EOS???")
        }
        case _ => {
          out.puts(s"$indent$indentCharacter -- ${c._2}")
        }
      }

      out.puts(s"${indent}end")
    })
  }

  def generateUserTypeFromBytes(indent: String, parentName: String, spec: AttrSpec, t: UserTypeFromBytes): Unit = {
    val fieldName = spec.id.humanReadable
    val fieldId = buildFieldName(spec.path)
    out.puts(s"""${indent}local $fieldName = $parentName:add("$fieldName")""")

    generateSeq(indent, fieldName, t.classSpec.get.seq)
  }

  def generateInt1Type(indent: String, parentName: String, spec: AttrSpec, t: Int1Type): Unit = {
    val fieldName = spec.id.humanReadable
    val fieldId = buildFieldName(spec.path)

    generateGenericField(indent, parentName, s"f${fieldId}_$fieldName", 1)
  }

  def generateIntMultiType(indent: String, parentName: String, spec: AttrSpec, t: IntMultiType): Unit = {
    val fieldName = spec.id.humanReadable
    val fieldId = buildFieldName(spec.path)

    var littleEndian: Boolean = if (topClass.meta.endian.isDefined) topClass.meta.endian.get.equals(LittleEndian) else false
    if (t.endian.isDefined) {
      littleEndian = t.endian.get.equals(LittleEndian)
    }

    generateGenericField(indent, parentName, s"f${fieldId}_$fieldName", t.width.width, littleEndian = littleEndian)
  }

  def generateBytesLimitType(indent: String, parentName: String, spec: AttrSpec, t: BytesLimitType): Unit = {
    val fieldName = spec.id.humanReadable
    val fieldId = buildFieldName(spec.path)
    var size = 0
    t.size match {
      case s: IntNum => {
        size = s.n.intValue()
      }
    }

    generateGenericField(indent, parentName, s"f${fieldId}_$fieldName", size)
  }

  def generateUserTypeIntstream(indent: String, parentName: String, spec: AttrSpec, t: UserTypeInstream): Unit = {
    val fieldName = spec.id.humanReadable
    val fieldId = buildFieldName(spec.path)
    out.puts(s"""${indent}local $fieldName = $parentName:add("$fieldName")""")

    generateSeq(indent, fieldName, t.classSpec.get.seq)
  }

  def generateBooleanType(indent: String, parentName: String, spec: AttrSpec, t: BooleanType): Unit = {
    val fieldName = spec.id.humanReadable
    val fieldId = buildFieldName(spec.path)

    out.puts(s"$indent$parentName:add(f${fieldId}_$fieldName, tvb(offset, 1))")
  }

  def generateEnumType(indent: String, parentName: String, spec: AttrSpec, t: EnumType): Unit = {
    val fieldName = spec.id.humanReadable
    val fieldId = buildFieldName(spec.path)

    generateGenericField(indent, parentName, s"f${fieldId}_$fieldName", 1)
  }

  def generateBitsType(indent: String, parentName: String, spec: AttrSpec, t: BitsType): Unit = {
    val fieldName = spec.id.humanReadable
    val fieldId = buildFieldName(spec.path)

    generateGenericField(indent, parentName, s"f${fieldId}_$fieldName", 1)
  }

  def generateStrFromBytesType(indent: String, parentName: String, spec: AttrSpec, t: StrFromBytesType): Unit = {
    val fieldName = spec.id.humanReadable
    val fieldId = buildFieldName(spec.path)
    var size = 0
    t.bytes match {
      case s: BytesLimitType => {
        s.size match {
          case u: IntNum => {
            size = u.n.intValue()
          }
          case _ => {
            out.puts(s"-- ${s.size}")
          }
        }
      }
      case _ => {
        out.puts(s"-- ${t.bytes}")
      }
    }

    generateGenericField(indent, parentName, s"f${fieldId}_$fieldName", 1)
  }

  def generateGenericField(indent: String, parentName: String, fieldName: String, size: Int, littleEndian: Boolean = false): Unit = {
    val addFunction = if(littleEndian) "add_le" else "add"
    out.puts(s"$indent$parentName:$addFunction($fieldName, tvb(offset, $size))")
    out.puts(s"${indent}offset = offset + $size")
  }

  def buildAbbreviation(rootName: String, path: List[String], id: String): String = {
    if (path.length > 2) {
      val joinedPath = path.slice(0, path.length - 2).filter(p => p != "types").mkString(".")
      s"$rootName.$joinedPath.$id"
    }
    else {
      s"$rootName.$id"
    }
  }

  def buildFieldName(path: List[String]): String = {
    var result = ""

    if(path.length > 2) {
      result += "_"
    }

    result += path.slice(0, path.length-2).filter(p => p != "types").mkString("_")

    return result
  }
  def indentCharacter: String = "\t"
  def outFileName(topClassName: String): String = s"$topClassName.lua"
  def dissectorName(topClassName: String): String = s"${topClassName}_proto"
}

object WiresharkClassCompiler extends LanguageCompilerStatic {
  override def getCompiler(tp: ClassTypeProvider, config: RuntimeConfig): LanguageCompiler = ???
}
