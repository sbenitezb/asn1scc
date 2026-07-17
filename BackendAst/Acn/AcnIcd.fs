module AcnIcd

open FsUtils
open CommonTypes
open Asn1AcnAst
open Asn1AcnAstUtilFunctions
open DAst
open DAstUtilFunctions


let createIcdTas (r:Asn1AcnAst.AstRoot) (id:ReferenceToType) (icdAux:IcdArgAux) (td:FE_TypeDefinition) (typeDefinition:TypeDefinitionOrReference) nMinBytesInACN nMaxBytesInACN hasAcnDefinition (acnParameters:AcnGenericTypes.AcnParameter list) =
    let icdRows, compositeChildren = icdAux.rowsFunc "" "" [];
    let icdAcnParameters =
        acnParameters |>
        List.map(fun p ->
            let prmType =
                match p.asn1Type with
                | AcnGenericTypes.AcnParamType.AcnPrmInteger  _      -> IcdPrmBasic "INTEGER"
                | AcnGenericTypes.AcnParamType.AcnPrmBoolean  _      -> IcdPrmBasic "BOOLEAN"
                | AcnGenericTypes.AcnParamType.AcnPrmNullType _      -> IcdPrmBasic "NULL"
                | AcnGenericTypes.AcnParamType.AcnPrmRefType (md,ts) -> IcdPrmRefTas (md.Value, ts.Value)
            {IcdAcnParameter.name = p.name; prmType = prmType})
    let icdTas =
        {
            IcdTypeAss.typeId = id
            tasInfo = id.tasInfo
            asn1Link = None;
            acnLink = None;
            name =
                match icdAux.name with
                | Some n -> n
                | None   -> td.asn1Name
            kind = icdAux.baseAsn1Kind;
            canBeEmbedded  = icdAux.canBeEmbedded
            createRowsFunc = icdAux.rowsFunc
            comments =
                let asn1Comments =
                    match id.tasInfo with
                    | None -> []
                    | Some tasInfo ->
                        match r.typeAssignmentsMap.TryFind (tasInfo.modName, tasInfo.tasName) with
                        | None -> []
                        | Some ts -> ts.Comments |> Seq.toList

                asn1Comments@icdAux.commentsForTas
            acnParameters = icdAcnParameters
            rows  = icdRows
            compositeChildren = compositeChildren
            minLengthInBytes = nMinBytesInACN;
            maxLengthInBytes = nMaxBytesInACN
            hasAcnDefinition = hasAcnDefinition
            hash = "" // will be calculated later
        }
    let icdHash = CalculateIcdHash.calcIcdTypeAssHash icdTas
    {icdTas with hash = icdHash}
