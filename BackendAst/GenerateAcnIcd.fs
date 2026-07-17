module GenerateAcnIcd
open System.Globalization
open System
open System.Numerics
open System.IO
open FsUtils
open CommonTypes
open DAst
open DastFold
open DAstUtilFunctions
open Antlr.Asn1
open Antlr.Acn
open Antlr.Runtime



let acnTokens = [
        "endianness"; "big"; "little"; "encoding"; "pos-int"; "twos-complement"; "BCD"; "ASCII";
        "IEEE754-1985-32"; "IEEE754-1985-64"; "size"; "null-terminated"; "align-to-next"; "byte";
        "word"; "dword"; "encode-values"; "true-value"; "false-value"; "pattern"; "present-when";
        "determinant"; "DEFINITIONS"; "BEGIN"; "END"; "CONSTANT"; "NOT"; "INTEGER"; "BOOLEAN"; "NULL"] |> Set.ofList

let Kind2Name  = GenerateUperIcd.Kind2Name


let makeEmptyNull (s:string) =
    match s with
    | null  -> null
    | _     -> match s.Trim() with "" -> null | _ -> s

// Generate a formatted version of the ACN grammar given as input,
// using the stringtemplate layouts.

let PrintAcnAsHTML stgFileName (r:AstRoot)  =
    let colorize (t: IToken, tasses: string array) =
            let lt = icd_acn.LeftDiple stgFileName ()
            let gt = icd_acn.RightDiple stgFileName ()
            let containedIn = Array.exists (fun elem -> elem = t.Text)
            let isAcnKeyword = acnTokens.Contains t.Text
            let isType = containedIn tasses
            let safeText = t.Text.Replace("<",lt).Replace(">",gt)
            let uid =
                match isType with
                |true -> icd_acn.TasName stgFileName safeText (ToC safeText)
                |false -> safeText
            let colored =
                match t.Type with
                |acnLexer.StringLiteral
                |acnLexer.BitStringLiteral -> icd_acn.StringLiteral stgFileName safeText
                |acnLexer.UID -> uid
                |acnLexer.COMMENT
                |acnLexer.COMMENT2 -> icd_acn.Comment stgFileName safeText
                |_ -> safeText
            if isAcnKeyword then icd_acn.AcnKeyword stgFileName safeText else colored

    let tasNames = r.Files |> Seq.collect(fun f -> f.Modules) |> Seq.collect(fun x -> x.TypeAssignments) |> Seq.map(fun x -> x.Name.Value) |> Seq.toArray

    r.acnParseResults |>
    Seq.map(fun pr -> pr.fileName, pr.tokens) |>
    Seq.map(fun (fName, tokens) ->
            //let f = r.Files |> Seq.find(fun x -> Path.GetFileNameWithoutExtension(x.FileName) = Path.GetFileNameWithoutExtension(fName))
            //let tasNames = f.Modules |> Seq.collect(fun x -> x.TypeAssignments) |> Seq.map(fun x -> x.Name.Value) |> Seq.toArray
            let content = tokens |> Seq.map(fun token -> colorize(token,tasNames))
            icd_acn.EmitFilePart2  stgFileName (Path.GetFileName fName) (content )
    )

let PrintAcnAsHTML2 stgFileName (r:AstRoot)  (icdHashesToPrint:string list) =
    let icdHashesToPrintSet = icdHashesToPrint |> Set.ofList
    // TAS name -> hashes of the selected tables of that TAS, deterministic
    // order (more than one element only when the same TAS name exists in
    // several modules).
    let fileTypeAssignments =
        r.icdHashes.Values |>
        Seq.collect id |>
        Seq.choose(fun z ->
            match z.tasInfo with
            | Some ts when icdHashesToPrintSet.Contains z.hash  -> Some (ts.tasName, z.hash)
            | _ -> None) |>
        Seq.distinct |>
        Seq.groupBy fst |>
        Seq.map(fun (tasName, pairs) -> (tasName, pairs |> Seq.map snd |> Seq.sort |> Seq.toList)) |>
        Map.ofSeq

    // The "ACN" link of a table header targets #ACN_<hash>; that anchor must
    // exist exactly once in the document (roadmap B5 / R6: the old code
    // re-emitted it at every occurrence of the name - duplicate anchors,
    // invalid HTML).  The anchor is placed on the token that defines the ACN
    // encoding spec of the TAS: a module-level occurrence (brace depth 0)
    // directly followed by '[', '{' or '<'.  A TAS whose ACN properties only
    // appear at a usage site (e.g. the type of an ACN-inserted child) falls
    // back to its first occurrence.  Every other occurrence renders as a
    // plain link to the ASN.1 definition.
    let anchorTokenOfName : Map<string, string*int> =
        let significant (tok: IToken) =
            match tok.Type with
            | t when t = acnLexer.WS || t = acnLexer.COMMENT || t = acnLexer.COMMENT2 -> false
            | _ -> true
        let defSites   = System.Collections.Generic.Dictionary<string, string*int>()
        let firstSites = System.Collections.Generic.Dictionary<string, string*int>()
        for pr in r.acnParseResults do
            let mutable braceDepth = 0
            pr.tokens |> Array.iteri(fun idx tok ->
                match tok.Text with
                | "{" -> braceDepth <- braceDepth + 1
                | "}" -> braceDepth <- braceDepth - 1
                | _   ->
                    match tok.Type = acnLexer.UID && fileTypeAssignments.ContainsKey tok.Text with
                    | false -> ()
                    | true  ->
                        match firstSites.ContainsKey tok.Text with
                        | false -> firstSites.[tok.Text] <- (pr.fileName, idx)
                        | true  -> ()
                        let nextSignificant = pr.tokens.[idx+1 ..] |> Array.tryFind significant
                        let isDefSite =
                            match braceDepth, nextSignificant with
                            | 0, Some nt -> nt.Text = "[" || nt.Text = "{" || nt.Text = "<"
                            | _, _       -> false
                        match isDefSite && not (defSites.ContainsKey tok.Text) with
                        | true  -> defSites.[tok.Text] <- (pr.fileName, idx)
                        | false -> ())
        fileTypeAssignments |>
        Map.toList |>
        List.choose(fun (name, _) ->
            match defSites.TryGetValue name with
            | true, site -> Some (name, site)
            | false, _ ->
                match firstSites.TryGetValue name with
                | true, site -> Some (name, site)
                | false, _   -> None) |>
        Map.ofList

    let colorize (fName: string) (idx: int) (t: IToken) =
            let lt = icd_acn.LeftDiple stgFileName ()
            let gt = icd_acn.RightDiple stgFileName ()
            let isAcnKeyword = acnTokens.Contains t.Text
            let safeText = t.Text.Replace("<",lt).Replace(">",gt)
            let uid =
                match fileTypeAssignments.TryFind t.Text with
                | Some (mainHash::extraHashes) ->
                    match anchorTokenOfName.TryFind t.Text with
                    | Some site when site = (fName, idx) ->
                        // definition site: one ACN_<hash> anchor per selected
                        // table of this TAS (the extra ones - same TAS name in
                        // another module - as invisible empty-text anchors)
                        let extraAnchors = extraHashes |> List.map(fun h -> icd_acn.TasName stgFileName "" h)
                        (extraAnchors @ [icd_acn.TasName stgFileName safeText mainHash]) |> String.concat ""
                    | _ -> icd_acn.TasName2 stgFileName safeText mainHash
                | Some [] | None -> safeText
            let colored =
                match t.Type with
                |acnLexer.StringLiteral
                |acnLexer.BitStringLiteral -> icd_acn.StringLiteral stgFileName safeText
                |acnLexer.UID -> uid
                |acnLexer.COMMENT
                |acnLexer.COMMENT2 -> icd_acn.Comment stgFileName safeText
                |_ -> safeText
            if isAcnKeyword then icd_acn.AcnKeyword stgFileName safeText else colored

    r.acnParseResults |>
    Seq.map(fun pr -> pr.fileName, pr.tokens) |>
    Seq.map(fun (fName, tokens) ->
            let content = tokens |> Seq.mapi(fun idx token -> colorize fName idx token)
            icd_acn.EmitFilePart2  stgFileName (Path.GetFileName fName) (content)
    ) |> Seq.toList

let foldGenericCon = GenerateUperIcd.foldGenericCon
let foldRangeCon   = GenerateUperIcd.foldRangeCon

type SequenceRow = {
    sClass              : string
    nIndex              : BigInteger
    chName              : string
    sComment            : string
    sPresentWhen        : string
    sType               : string
    sAsn1Constraints    : string
    sMinBits            : string
    sMaxBits            : string
    noAlignToNextSize   : string
    soUnit              : string option
}
let enumStg : GenerateUperIcd.StgCommentLineMacros =
    {
        NewLine                  = icd_acn.NewLine
        EmitEnumItem             = icd_acn.EmitEnumItem
        EmitEnumItemWithComment  = icd_acn.EmitEnumItemWithComment
        EmitEnumInternalContents = icd_acn.EmitEnumInternalContents
    }

let handleNullType stgFileName (encodingPattern : AcnGenericTypes.PATTERN_PROP_VALUE option) defaultRetValue =
    match encodingPattern with
    | Some(AcnGenericTypes.PATTERN_PROP_BITSTR_VALUE bitStr)       -> icd_acn.NullTypeWithBitPattern  stgFileName  bitStr.Value
    | Some(AcnGenericTypes.PATTERN_PROP_OCTSTR_VALUE byteList     )-> icd_acn.NullTypeWithBytePattern stgFileName  (byteList |> List.map (fun z -> z.Value))
    | None                                                        -> defaultRetValue



let emitSequenceComponent (r:AstRoot) stgFileName (optionalLikeUperChildren:Asn1Child list) (i:int) (ch:SeqChildInfo) =
    let GetCommentLine = GenerateUperIcd.GetCommentLineFactory stgFileName enumStg
    let sClass = if i % 2 = 0 then (icd_acn.EvenRow stgFileName ()) else (icd_acn.OddRow stgFileName ())
    let nIndex = BigInteger i
    let sPresentWhen, bAlwaysAbsent =
        match ch with
        | AcnChild  _ -> "always", false
        | Asn1Child ch  ->
            let aux1 = function
                | 1 -> "st"
                | 2 -> "nd"
                | 3 -> "rd"
                | _ -> "th"
            match ch.Optionality with
            | None                      -> "always", false
            | Some(Asn1AcnAst.AlwaysPresent)   -> "always", false
            | Some(Asn1AcnAst.AlwaysAbsent)    -> "never", true
            | Some(Asn1AcnAst.Optional opt)    ->
                match opt.acnPresentWhen with
                | None  ->
                    let nBit =  optionalLikeUperChildren |> Seq.findIndex(fun x -> x.Name.Value = ch.Name.Value) |> (+) 1
                    sprintf "when the %d%s bit of the bit mask is set" nBit (aux1 nBit), false
                | Some (AcnGenericTypes.PresenceWhenBool presWhen)     ->
                    let dependency = r.deps.acnDependencies |> List.find(fun d -> d.asn1Type = ch.Type.id )
                    //match dependency.dependencyKind with
                    sprintf "when %s is true" presWhen.AsString , false
                | Some (AcnGenericTypes.PresenceWhenBoolExpression acnExp)  ->
                    let _, debugStr = AcnGenericCreateFromAntlr.printDebug acnExp
                    sprintf "when %s is true" debugStr, false

    let sType, sComment, sAsn1Constraints, nAlignToNextSize, soUnit  =
        match ch with
        | Asn1Child ch  ->
            let sType =
                let defaultRetValue =
                    match ch.Type.Kind with
                    | ReferenceType o when not o.baseInfo.hasExtraConstrainsOrChildrenOrAcnArgs ->
                        icd_acn.EmitSeqChild_RefType stgFileName ch.Type.FT_TypeDefinition.[CommonTypes.ProgrammingLanguage.ActiveLanguages.Head].asn1Name (ToC ch.Type.FT_TypeDefinition.[CommonTypes.ProgrammingLanguage.ActiveLanguages.Head].asn1Name)
                    | OctetString o -> "OCTET STRING"
                    | _ ->
                        match ch.Type.ActualType.Kind with
                        | Sequence _
                        | Choice _
                        | SequenceOf _ ->
                            icd_acn.EmitSeqChild_RefType stgFileName ch.Type.id.AsString.RDD (ToC ch.Type.id.AsString.RDD)
                        | _            ->
                            icd_acn.EmitSeqChild_RefType stgFileName ch.Type.FT_TypeDefinition.[CommonTypes.ProgrammingLanguage.ActiveLanguages.Head].asn1Name (ToC ch.Type.FT_TypeDefinition.[CommonTypes.ProgrammingLanguage.ActiveLanguages.Head].asn1Name)
                match ch.Type.ActualType.Kind with
                | DAst.NullType       o  when o.baseInfo.acnProperties.encodingPattern.IsSome  ->
                                                handleNullType stgFileName o.baseInfo.acnProperties.encodingPattern defaultRetValue
                | _                       -> defaultRetValue
            let soUnit =  GenerateUperIcd.getUnits ch.Type
            sType, GetCommentLine ch.Comments ch.Type, ch.Type.ConstraintsAsn1Str |> Seq.StrJoin "", AcnEncodingClasses.getAlignmentSize ch.Type.acnAlignment, soUnit
        | AcnChild ch   ->
            let commentLine =
                ch.Comments |> Seq.StrJoin (enumStg.NewLine stgFileName ())


            let sType,consAsStt =
                match ch.Type with
                | Asn1AcnAst.AcnInteger                o ->
                    let constAsStr = DAstAsn1.createAcnInteger (o.cons@o.withcons) |> Seq.StrJoin ""
                    match o.inheritInfo with
                    | None                              ->  icd_acn.Integer           stgFileName ()    , constAsStr
                    | Some inhInfo                      ->  icd_acn.EmitSeqChild_RefType stgFileName inhInfo.tasName (ToC inhInfo.tasName) , constAsStr
                | Asn1AcnAst.AcnNullType               o ->
                    let sType = handleNullType stgFileName o.acnProperties.encodingPattern (icd_acn.NullType           stgFileName ())
                    sType, ""
                | Asn1AcnAst.AcnBoolean                o -> icd_acn.Boolean           stgFileName (), ""
                | Asn1AcnAst.AcnReferenceToEnumerated  o -> icd_acn.EmitSeqChild_RefType stgFileName o.tasName.Value (ToC o.tasName.Value), ""
                | Asn1AcnAst.AcnReferenceToIA5String   o -> icd_acn.EmitSeqChild_RefType stgFileName o.tasName.Value (ToC o.tasName.Value), ""
            sType, commentLine, consAsStt, AcnEncodingClasses.getAlignmentSize ch.Type.acnAlignment, None
    let name = ch.Name
    let noAlignToNextSize = if nAlignToNextSize = 0I then None else (Some nAlignToNextSize)
    let acnMaxSizeInBits = ch.acnMaxSizeInBits - nAlignToNextSize
    let acnMinSizeInBits = (if bAlwaysAbsent then 0I else ch.acnMinSizeInBits) - nAlignToNextSize
    let sMaxBits, sMaxBytes = acnMaxSizeInBits.ToString(), BigInteger(System.Math.Ceiling(double(acnMaxSizeInBits)/8.0)).ToString()
    let sMinBits, sMinBytes = acnMinSizeInBits.ToString(), BigInteger(System.Math.Ceiling(double(acnMinSizeInBits)/8.0)).ToString()
    // old pipeline: no bit-offset column (roadmap D1 populates it in the new pipeline only)
    icd_acn.EmitSeqOrChoiceRow stgFileName sClass nIndex ch.Name sComment  sPresentWhen  sType sAsn1Constraints sMinBits sMaxBits noAlignToNextSize soUnit None None


let rec printType stgFileName (tas:GenerateUperIcd.IcdTypeAssignment) (t:Asn1Type) (m:Asn1Module) (r:AstRoot)  isAnonymousType : string list=
    let GetCommentLine = GenerateUperIcd.GetCommentLineFactory stgFileName enumStg

    let hasAcnDef = r.acnParseResults |> Seq.collect (fun p -> p.tokens) |> Seq.exists(fun x -> x.Text = tas.name)

    let sTasName = tas.name
    let sKind = Kind2Name stgFileName t
    let sMaxBits, sMaxBytes = t.acnMaxSizeInBits.ToString(), BigInteger(System.Math.Ceiling(double(t.acnMaxSizeInBits)/8.0)).ToString()
    let sMinBits, sMinBytes = t.acnMinSizeInBits.ToString(), BigInteger(System.Math.Ceiling(double(t.acnMinSizeInBits)/8.0)).ToString()
    let sMaxBitsExplained =  ""
    let sCommentLine = GetCommentLine tas.comments t
    let myParams colSpan=
        t.acnParameters |>
        List.mapi(fun i x ->
            let sType = match x.asn1Type with
                            | AcnGenericTypes.AcnParamType.AcnPrmInteger    _         -> "INTEGER"
                            | AcnGenericTypes.AcnParamType.AcnPrmBoolean    _         -> "BOOLEAN"
                            | AcnGenericTypes.AcnParamType.AcnPrmNullType   _         -> "NULL"
                            | AcnGenericTypes.AcnParamType.AcnPrmRefType(_,ts)     -> icd_acn.EmitSeqChild_RefType stgFileName ts.Value (ToC ts.Value)

            icd_acn.PrintParam stgFileName (i+1).AsBigInt x.name sType colSpan)



    let handlePrimitive (sAsn1Constraints:string)   =
        let ret = icd_acn.EmitPrimitiveType stgFileName isAnonymousType sTasName (ToC sTasName) hasAcnDef sKind sMinBytes sMaxBytes sMaxBitsExplained sCommentLine ( if sAsn1Constraints.Trim() ="" then "N.A." else sAsn1Constraints) sMinBits sMaxBits (myParams 2I) (sCommentLine.Split [|'\n'|]) t.unitsOfMeasure
        [ret]
    match t.Kind with
    | Integer    o   ->
        let sAsn1Constraints = o.AllCons |> List.map (foldRangeCon (fun z -> z.ToString())) |> Seq.StrJoin ""
        handlePrimitive sAsn1Constraints
    | Real    o   ->
        let sAsn1Constraints = o.AllCons |> List.map (foldRangeCon (fun z -> z.ToString())) |> Seq.StrJoin ""
        handlePrimitive sAsn1Constraints
    | Boolean   o   ->
        let sAsn1Constraints = o.AllCons |> List.map (foldGenericCon (fun z -> z.ToString().ToUpper() )) |> Seq.StrJoin ""
        handlePrimitive sAsn1Constraints
    | NullType  o   ->
        let sAsn1Constraints = ""
        handlePrimitive sAsn1Constraints
    | Enumerated  o   ->
        let sAsn1Constraints = ""
        handlePrimitive sAsn1Constraints
    | ObjectIdentifier  o   ->
        let sAsn1Constraints = ""
        handlePrimitive sAsn1Constraints
    |ReferenceType o when  o.baseInfo.encodingOptions.IsNone ->
        printType stgFileName tas o.resolvedType m r isAnonymousType
    |Sequence seq   ->
        let optionalLikeUperChildren =
            seq.Asn1Children
            |> Seq.filter (fun x ->
                match x.Optionality with
                | None  -> false
                | Some (Asn1AcnAst.Optional opt)  ->
                    match opt.acnPresentWhen with
                    | Some (AcnGenericTypes.PresenceWhenBool _) -> false
                    | Some (AcnGenericTypes.PresenceWhenBoolExpression _) -> false
                    | None                      -> true
                | _                               -> false)
            |> Seq.toList
        let SeqPreamble =
            match optionalLikeUperChildren with
            | []    -> None
            | _     ->
                let arrsOptWihtNoPresentWhenChildren =
                    optionalLikeUperChildren |> Seq.mapi(fun i c -> icd_acn.EmitSequencePreambleSingleComment stgFileName (BigInteger (i+1)) c.Name.Value)

                let nLen = optionalLikeUperChildren |> Seq.length
                let ret = icd_acn.EmitSeqOrChoiceRow stgFileName (icd_acn.OddRow stgFileName ()) 1I "Preamble" (icd_acn.EmitSequencePreambleComment stgFileName arrsOptWihtNoPresentWhenChildren)  "always"  "Bit mask" "N.A." (nLen.ToString()) (nLen.ToString()) None None None None
                Some ret
        let emitSequenceRow (i:int, curResult:string list) (ch:SeqChildInfo) =
            let di, newLines =
                match ch with
                | AcnChild  _ -> 1, [emitSequenceComponent r stgFileName optionalLikeUperChildren i ch]
                | Asn1Child ach  ->
                                1, [emitSequenceComponent r stgFileName optionalLikeUperChildren i ch]
                (*
                    match ach.Type.Kind with
                    | OctetString o when o.baseInfo.acnEncodingClass = Asn1AcnAst.SizeableAcnEncodingClass.SZ_EC_uPER ->
                        let lengthLine =
                            let sClass = if i % 2 = 0 then (icd_acn.EvenRow stgFileName ()) else (icd_acn.OddRow stgFileName ())

                            icd_acn.EmitSeqOrChoiceRow stgFileName sClass (BigInteger i) "length" "uper length determinant"  "???"  "OCTET STRING" "N/A" sMinBits sMaxBits None None None None

                        1, [emitSequenceComponent r stgFileName optionalLikeUperChildren i ch]
                    | _ -> 1, [emitSequenceComponent r stgFileName optionalLikeUperChildren i ch]
                *)
            (i+di, curResult@newLines)
        let arChildren idx =
            seq.children |>
            Seq.fold emitSequenceRow (idx, []) |>
            snd
//        let arChildren idx =
//            seq.children |>
//            Seq.mapi(fun i ch -> emitSequenceComponent r stgFileName optionalLikeUperChildren (idx + i) ch )
//            |> Seq.toList
        let childTasses =
            seq.children |>
            Seq.map(fun ch ->
                    match ch with
                    | Asn1Child ch  ->
                        match ch.Type.Kind with
                        | ReferenceType o when not o.baseInfo.hasExtraConstrainsOrChildrenOrAcnArgs -> []
                        | _     ->
                            match ch.Type.ActualType.Kind with
                            | Sequence _
                            | Choice _
                            | SequenceOf _ ->
                                let chTas = {tas with name=ch.Type.id.AsString.RDD; t=ch.Type; comments = Array.concat [ tas.comments; [|sprintf "Acn inline encoding in the context of %s type and %s component" tas.name ch.Name.Value|]]; isBlue = true }
                                printType stgFileName chTas ch.Type m r isAnonymousType
                            | _            -> []
                    | AcnChild _       -> [])|>
            Seq.collect id |> Seq.toList
        let arRows =
            match SeqPreamble with
            | None          -> arChildren 1
            | Some(prm)     -> prm::(arChildren 2)
        let seqRet = icd_acn.EmitSequenceOrChoice stgFileName isAnonymousType sTasName (ToC sTasName) hasAcnDef "SEQUENCE" sMinBytes sMaxBytes sMaxBitsExplained sCommentLine arRows (myParams 4I) (sCommentLine.Split [|'\n'|])
        [seqRet] @ childTasses
    |Choice chInfo   ->
        let EmitSeqOrChoiceChild (i:int) (ch:ChChildInfo)  getPresence =
            let sClass = if i % 2 = 0 then (icd_acn.EvenRow stgFileName ()) else (icd_acn.OddRow stgFileName ())
            let nIndex = BigInteger i
            let sComment = GetCommentLine ch.Comments ch.chType

            let sPresentWhen = getPresence i ch

            let sType =
                let defaultRetValue = icd_acn.EmitSeqChild_RefType stgFileName ch.chType.FT_TypeDefinition.[CommonTypes.ProgrammingLanguage.ActiveLanguages.Head].asn1Name (ToC ch.chType.FT_TypeDefinition.[CommonTypes.ProgrammingLanguage.ActiveLanguages.Head].asn1Name)
                match ch.chType.Kind with
                | ReferenceType o when not o.baseInfo.hasExtraConstrainsOrChildrenOrAcnArgs -> defaultRetValue
                | _  ->
                    match ch.chType.ActualType.Kind with
                    | Sequence _
                    | Choice _
                    | SequenceOf _ ->
                        icd_acn.EmitSeqChild_RefType stgFileName ch.chType.id.AsString.RDD (ToC ch.chType.id.AsString.RDD)
                    | DAst.NullType       o  when o.baseInfo.acnProperties.encodingPattern.IsSome  ->
                                                    handleNullType stgFileName o.baseInfo.acnProperties.encodingPattern defaultRetValue
                    | _                       -> defaultRetValue

            let sAsn1Constraints = ch.chType.ConstraintsAsn1Str |> Seq.StrJoin ""
            let sMaxBits, sMaxBytes = ch.chType.acnMaxSizeInBits.ToString(), BigInteger(System.Math.Ceiling(double(ch.chType.acnMaxSizeInBits)/8.0)).ToString()
            let sMinBits, sMinBytes = ch.chType.acnMinSizeInBits.ToString(), BigInteger(System.Math.Ceiling(double(ch.chType.acnMinSizeInBits)/8.0)).ToString()
            let soUnit = GenerateUperIcd.getUnits ch.chType
            icd_acn.EmitSeqOrChoiceRow stgFileName sClass nIndex ch.Name.Value sComment  sPresentWhen  sType sAsn1Constraints sMinBits sMaxBits None soUnit None None
        let children = chInfo.children
        let children = children |> List.filter(fun ch -> match ch.Optionality with  Some (Asn1AcnAst.ChoiceAlwaysAbsent) -> false | _ -> true)
        let arrRows =
            match chInfo.ancEncClass with
            | CEC_uper          ->
                let ChIndex, curI =
                    //let optChild = chInfo.children |> Seq.mapi(fun i c -> icd_uper.EmitChoiceIndexSingleComment stgFileName (BigInteger (i+1)) c.Name.Value)
                    match children.Length <= 1 with
                    | true    -> [], 1
                    | false     ->
                        let sComment = icd_acn.EmitChoiceIndexComment stgFileName ()
                        let indexSize = (GetChoiceUperDeterminantLengthInBits(BigInteger(Seq.length children))).ToString()
                        let ret = icd_acn.EmitSeqOrChoiceRow stgFileName (icd_acn.OddRow stgFileName ()) (BigInteger 1) "ChoiceIndex" sComment  "always"  "unsigned int" "N.A." indexSize indexSize None None None None
                        [ret], 2
                    //icd_acn.EmitSeqOrChoiceRow stgFileName sClass nIndex ch.Name.Value sComment  sPresentWhen  sType sAsn1Constraints sMinBits sMaxBits
                let getPresenceWhenNone_uper (i:int) (ch:ChChildInfo) =
                    match children.Length <= 1 with
                    | true  -> "always"
                    | false ->
                        let index = children |> Seq.findIndex (fun z -> z.Name.Value = ch.Name.Value)
                        sprintf "ChoiceIndex = %d" index
                    //sprintf "ChoiceIndex = %d" i
                let EmitChild (i:int) (ch:ChChildInfo) = EmitSeqOrChoiceChild i ch  getPresenceWhenNone_uper
                let arChildren = children |> Seq.mapi(fun i ch -> EmitChild (curI + i) ch) |> Seq.toList
                ChIndex@arChildren
            | CEC_enum    (r,d)     ->
                let getPresence (i:int) (ch:ChChildInfo) =
                    let refToStr id =
                        match id with
                        | ReferenceToType sn -> sn |> List.rev |> List.head |> (fun x -> x.AsString)

                    sprintf "%s = %s" (refToStr d.id) ch.Name.Value
                let EmitChild (i:int) (ch:ChChildInfo) = EmitSeqOrChoiceChild i ch  getPresence
                children |> Seq.mapi(fun i ch -> EmitChild (1 + i) ch) |> Seq.toList
            | CEC_presWhen      ->
                let getPresence (i:int) (ch:ChChildInfo) =
                    let getPresenceSingle (pc:AcnGenericTypes.AcnPresentWhenConditionChoiceChild) =
                        match pc with
                        | AcnGenericTypes.PresenceInt   (rp, intLoc) -> sprintf "%s=%A" rp.AsString intLoc.Value
                        | AcnGenericTypes.PresenceStr   (rp, strLoc) -> sprintf "%s=%A" rp.AsString strLoc.Value
                    ch.acnPresentWhenConditions |> Seq.map getPresenceSingle |> Seq.StrJoin " AND "
                let EmitChild (i:int) (ch:ChChildInfo) = EmitSeqOrChoiceChild i ch  getPresence
                children |> Seq.mapi(fun i ch -> EmitChild (1 + i) ch) |> Seq.toList
        let chRet = icd_acn.EmitSequenceOrChoice stgFileName isAnonymousType sTasName (ToC sTasName) hasAcnDef "CHOICE" sMinBytes sMaxBytes sMaxBitsExplained sCommentLine arrRows (myParams 4I) (sCommentLine.Split [|'\n'|])
        let childTasses =
            chInfo.children |>
            Seq.map(fun ch ->
                    match ch.chType.Kind with
                    | ReferenceType o when not o.baseInfo.hasExtraConstrainsOrChildrenOrAcnArgs -> []
                    | _  ->
                        match ch.chType.ActualType.Kind with
                        | Sequence _
                        | Choice _
                        | SequenceOf _ ->
                            let chTas = {tas with name=ch.chType.id.AsString.RDD; t=ch.chType; comments = Array.concat [ tas.comments; [|sprintf "Acn inline encoding in the context of %s type and %s component" tas.name ch.Name.Value|]]; isBlue = true }
                            printType stgFileName chTas ch.chType m r isAnonymousType
                        | _            -> [] )|>
            Seq.collect id |> Seq.toList
        [chRet]@childTasses
    | IA5String  o  ->
        let nMin, nMax, encClass = o.baseInfo.minSize.acn, o.baseInfo.maxSize.acn, o.baseInfo.acnEncodingClass
        let sType, characterSizeInBits =
            match encClass with
            | Asn1AcnAst.Acn_Enc_String_uPER                                   characterSizeInBits             -> "NUMERIC CHARACTER" , characterSizeInBits.ToString()
            | Asn1AcnAst.Acn_Enc_String_uPER_Ascii                             characterSizeInBits             -> "ASCII CHARACTER"   , characterSizeInBits.ToString()
            | Asn1AcnAst.Acn_Enc_String_Ascii_Null_Terminated                  (characterSizeInBits, nullChars)  -> "ASCII CHARACTER"  , characterSizeInBits.ToString()
            | Asn1AcnAst.Acn_Enc_String_Ascii_External_Field_Determinant      (characterSizeInBits, rp)        -> "ASCII CHARACTER"   , characterSizeInBits.ToString()
            | Asn1AcnAst.Acn_Enc_String_Ascii_Deduced                          characterSizeInBits              -> "ASCII CHARACTER"   , characterSizeInBits.ToString()
            | Asn1AcnAst.Acn_Enc_String_CharIndex_External_Field_Determinant  (characterSizeInBits, rp)        -> "NUMERIC CHARACTER" , characterSizeInBits.ToString()
        let ChildRow (lineFrom:BigInteger) (i:BigInteger) =
            let sClass = if i % 2I = 0I then icd_acn.EvenRow stgFileName () else icd_acn.OddRow stgFileName ()
            let nIndex = lineFrom + i
            let sFieldName = icd_acn.ItemNumber stgFileName i
            let sComment = ""
            icd_acn.EmitChoiceChild stgFileName sClass nIndex sFieldName sComment  sType "" characterSizeInBits characterSizeInBits
        let NullRow (lineFrom:BigInteger) (i:BigInteger) =
            let sClass = if i % 2I = 0I then icd_acn.EvenRow stgFileName () else icd_acn.OddRow stgFileName ()
            let nIndex = lineFrom + i
            let sFieldName = icd_acn.ItemNumber stgFileName i
            let sComment = "NULL Character"
            icd_acn.EmitChoiceChild stgFileName sClass nIndex sFieldName sComment  sType "" characterSizeInBits characterSizeInBits

        let comment = "Special field used by ACN indicating the number of items."
        let sCon = t.ConstraintsAsn1Str |> Seq.StrJoin ""
        let sCon =  if sCon.Trim() ="" then "N.A." else sCon
        let lenDetSize = GetNumberOfBitsForNonNegativeInteger ( (o.baseInfo.maxSize.acn - o.baseInfo.minSize.acn))
        let arRows, sExtraComment =
            match encClass with
            | Asn1AcnAst.Acn_Enc_String_uPER                                  nSizeInBits              ->
                let lengthLine = icd_acn.EmitChoiceChild stgFileName (icd_acn.OddRow stgFileName ()) 1I "Length" comment    "unsigned int" sCon (lenDetSize.ToString()) (lenDetSize.ToString())
                lengthLine::(ChildRow 1I 1I)::(icd_acn.EmitRowWith3Dots stgFileName ())::(ChildRow 1I ( nMax))::[], ""
            | Asn1AcnAst.Acn_Enc_String_uPER_Ascii                            nSizeInBits              ->
                let lengthLine = icd_acn.EmitChoiceChild stgFileName (icd_acn.OddRow stgFileName ()) 1I "Length" comment    "unsigned int" sCon (lenDetSize.ToString()) (lenDetSize.ToString())
                lengthLine::(ChildRow 1I 1I)::(icd_acn.EmitRowWith3Dots stgFileName ())::(ChildRow 1I ( nMax))::[], ""
            | Asn1AcnAst.Acn_Enc_String_Ascii_Null_Terminated                  (nSizeInBits, nullChars)  ->
                (ChildRow 0I 1I)::(icd_acn.EmitRowWith3Dots stgFileName ())::(ChildRow 0I ( nMax))::(NullRow 0I ( (nMax+1I)))::[],""
            | Asn1AcnAst.Acn_Enc_String_Ascii_External_Field_Determinant      (nSizeInBits, rp)        ->
                (ChildRow 0I 1I)::(icd_acn.EmitRowWith3Dots stgFileName ())::(ChildRow 0I ( nMax))::[], sprintf "Length determined by external field %s" (rp.AsString)
            | Asn1AcnAst.Acn_Enc_String_CharIndex_External_Field_Determinant  (nSizeInBits, rp)        ->
                (ChildRow 0I 1I)::(icd_acn.EmitRowWith3Dots stgFileName ())::(ChildRow 0I ( nMax))::[], sprintf "Length determined by external field %s" (rp.AsString)
            | Asn1AcnAst.Acn_Enc_String_Ascii_Deduced                          nSizeInBits              ->
                (ChildRow 0I 1I)::(icd_acn.EmitRowWith3Dots stgFileName ())::(ChildRow 0I ( nMax))::[], "Length is deduced from the size of the enclosing container/PDU (no length determinant is encoded)."
        let sCommentLine = match sCommentLine with
                           | null | ""  -> sExtraComment
                           | _          -> sprintf "%s%s%s" sCommentLine (icd_acn.NewLine stgFileName ()) sExtraComment

        let strRet = icd_acn.EmitSizeable stgFileName isAnonymousType sTasName  (ToC sTasName) hasAcnDef (Kind2Name stgFileName t) sMinBytes sMaxBytes sMaxBitsExplained (makeEmptyNull sCommentLine) arRows (myParams 2I) (sCommentLine.Split [|'\n'|])
        [strRet]
    | ReferenceType _
    | OctetString _
    | BitString  _
    | SequenceOf _   ->
        let nMin, nMax, encClass =
            match t.Kind with
            | OctetString o   ->
               o.baseInfo.minSize.acn, o.baseInfo.maxSize.acn, o.baseInfo.acnEncodingClass
            | BitString   o   ->
                o.baseInfo.minSize.acn, o.baseInfo.maxSize.acn, o.baseInfo.acnEncodingClass
            | SequenceOf  o   ->
                o.baseInfo.minSize.acn, o.baseInfo.maxSize.acn, o.baseInfo.acnEncodingClass
            | ReferenceType o   ->
                match o.baseInfo.encodingOptions with
                | None      -> raise(BugErrorException "")
                | Some eo   ->
                    eo.minSize.acn, eo.maxSize.acn, eo.acnEncodingClass
            | _                            -> raise(BugErrorException "")
        let ChildRow (lineFrom:BigInteger) (i:BigInteger) =
            let sClass = if i % 2I = 0I then icd_acn.EvenRow stgFileName () else icd_acn.OddRow stgFileName ()
            let nIndex = lineFrom + i
            let sFieldName = icd_acn.ItemNumber stgFileName i
            let sComment = ""
            let sType, sAsn1Constraints, sMinBits, sMaxBits =
                match t.Kind with
                | SequenceOf(seqOf) ->
                    let child = seqOf.childType
                    let sAsn1Constraints = child.ConstraintsAsn1Str |> Seq.StrJoin ""
                    let ret = ( if sAsn1Constraints.Trim() ="" then "N.A." else sAsn1Constraints)
                    let sMaxBits, sMaxBytes = child.acnMaxSizeInBits.ToString(), BigInteger(System.Math.Ceiling(double(child.acnMaxSizeInBits)/8.0)).ToString()
                    let sMinBits, sMinBytes = child.acnMinSizeInBits.ToString(), BigInteger(System.Math.Ceiling(double(child.acnMinSizeInBits)/8.0)).ToString()
                    let sType =
                        icd_acn.EmitSeqChild_RefType stgFileName child.FT_TypeDefinition.[CommonTypes.ProgrammingLanguage.ActiveLanguages.Head].asn1Name (ToC child.FT_TypeDefinition.[CommonTypes.ProgrammingLanguage.ActiveLanguages.Head].asn1Name)
//                        match child.Kind with
//                        | ReferenceType ref -> icd_acn.EmitSeqChild_RefType stgFileName ref.baseInfo.tasName.Value (ToC ref.baseInfo.tasName.Value)
//                        | _                       -> Kind2Name stgFileName child
                    sType, ret, sMinBits, sMaxBits
                | OctetString        _         -> "OCTET", "", "8", "8"
                | BitString          _         -> "BIT", "", "1","1"
                | ReferenceType o   ->
                    match o.baseInfo.encodingOptions with
                    | None      -> raise(BugErrorException "")
                    | Some eo   ->
                        match eo.octOrBitStr with
                        | ContainedInOctString  -> "OCTET", "", "8", "8"
                        | ContainedInBitString  -> "BIT", "", "1","1"
                | _                            -> raise(BugErrorException "")
            icd_acn.EmitChoiceChild stgFileName sClass nIndex sFieldName sComment  sType sAsn1Constraints sMinBits sMaxBits
        let sFixedLengthComment = sprintf "Length is Fixed equal to %A, so no length determinant is encoded." nMax
        let arRows, sExtraComment =
            match encClass, nMax >= 2I with
            | Asn1AcnAst.SZ_EC_FIXED_SIZE, _
            | Asn1AcnAst.SZ_EC_LENGTH_EMBEDDED _, _                     ->
                let sizeUperRange =  CommonTypes.Concrete(nMin, nMax)
                let sFixedLengthComment (nMax: BigInteger) =
                    sprintf "Length is fixed to %A elements (no length determinant is needed)." nMax
                let LengthRow =
                    let nMin, nLengthSize =
                        match sizeUperRange with
                        | CommonTypes.Concrete(a,b)  when a=b       -> 0I, 0I
                        | CommonTypes.Concrete(a,b)                 -> (GetNumberOfBitsForNonNegativeInteger(b - a)), (GetNumberOfBitsForNonNegativeInteger(b - a))
                        | CommonTypes.NegInf(_)                     -> raise(BugErrorException "")
                        | CommonTypes.PosInf(b)                     ->  8I, 16I
                        | CommonTypes.Full                          -> 8I, 16I
                    let comment = "Special field used by ACN to indicate the number of items present in the array."
                    let ret = t.ConstraintsAsn1Str |> Seq.StrJoin "" //+++ t.Constraints |> Seq.map PrintAsn1.PrintConstraint |> Seq.StrJoin ""
                    let sCon = ( if ret.Trim() ="" then "N.A." else ret)

                    icd_acn.EmitChoiceChild stgFileName (icd_acn.OddRow stgFileName ()) (BigInteger 1) "Length" comment    "unsigned int" sCon (nMin.ToString()) (nLengthSize.ToString())

                match sizeUperRange with
                | CommonTypes.Concrete(a,b)  when a=b && b<2I     -> [ChildRow 0I 1I], "The array contains a single element."
                | CommonTypes.Concrete(a,b)  when a=b && b=2I     -> (ChildRow 0I 1I)::(ChildRow 0I 2I)::[], (sFixedLengthComment b)
                | CommonTypes.Concrete(a,b)  when a=b && b>2I     -> (ChildRow 0I 1I)::(icd_acn.EmitRowWith3Dots stgFileName ())::(ChildRow 0I b)::[], (sFixedLengthComment b)
                | CommonTypes.Concrete(a,b)  when a<>b && b<2I    -> LengthRow::(ChildRow 1I 1I)::[],""
                | CommonTypes.Concrete(a,b)                       -> LengthRow::(ChildRow 1I 1I)::(icd_acn.EmitRowWith3Dots stgFileName ())::(ChildRow 1I b)::[], ""
                | CommonTypes.PosInf(_)
                | CommonTypes.Full                                -> LengthRow::(ChildRow 1I 1I)::(icd_acn.EmitRowWith3Dots stgFileName ())::(ChildRow 1I 65535I)::[], ""
                | CommonTypes.NegInf(_)                           -> raise(BugErrorException "")

            | Asn1AcnAst.SZ_EC_ExternalField relPath,false    ->
                (ChildRow 0I 1I)::[], sprintf "Length is determined by the external field: %s" relPath.AsString
            | Asn1AcnAst.SZ_EC_ExternalField relPath,true     ->
                (ChildRow 0I 1I)::(icd_acn.EmitRowWith3Dots stgFileName ())::(ChildRow 0I (nMax))::[], sprintf "Length determined by external field %s" relPath.AsString
            | Asn1AcnAst.SZ_EC_Deduced, false ->
                (ChildRow 0I 1I)::[], "Length is deduced from the size of the enclosing container/PDU (no length determinant is encoded)."
            | Asn1AcnAst.SZ_EC_Deduced, true ->
                (ChildRow 0I 1I)::(icd_acn.EmitRowWith3Dots stgFileName ())::(ChildRow 0I (nMax))::[], "Length is deduced from the size of the enclosing container/PDU (no length determinant is encoded)."
            | Asn1AcnAst.SZ_EC_TerminationPattern bitPattern, false ->
                (ChildRow 0I 1I)::[], sprintf "Length is determined by the stop marker '%s'" bitPattern.Value
            | Asn1AcnAst.SZ_EC_TerminationPattern bitPattern, true ->
                (ChildRow 0I 1I)::(icd_acn.EmitRowWith3Dots stgFileName ())::(ChildRow 0I (nMax))::[], sprintf "Length is determined by the stop marker '%s'" bitPattern.Value



        let sCommentLine = match sCommentLine with
                           | null | ""  -> sExtraComment
                           | _          -> sprintf "%s%s%s" sCommentLine (icd_acn.NewLine stgFileName ()) sExtraComment

        let sizeRet = icd_acn.EmitSizeable stgFileName false (*isAnonymousType*) sTasName  (ToC sTasName) hasAcnDef (Kind2Name stgFileName t) sMinBytes sMaxBytes sMaxBitsExplained (makeEmptyNull sCommentLine) arRows (myParams 2I) (sCommentLine.Split [|'\n'|])
        [sizeRet]
    | other -> raise (BugErrorException $"Unsupported kind for printType: {other}")
let PrintTas stgFileName (tas:GenerateUperIcd.IcdTypeAssignment) (m:Asn1Module) (r:AstRoot)   =
    //let isAnonymousType = blueTasses |> Seq.exists (fun x -> x = tas.Name.Value)
    let tasses = printType stgFileName tas tas.t  m r  tas.isBlue
    tasses |> List.map (icd_acn.EmitTass stgFileName ) |> Seq.StrJoin "\n"


// Name of the .acn file that defines the given module (the file whose token
// stream contains the module name), if any.
let moduleAcnFileName (r:AstRoot) (moduleName:string) =
    match r.acnParseResults |> Seq.tryFind(fun (rp) -> rp.tokens |> Seq.exists (fun (token:IToken) -> token.Text = moduleName)) with
    | Some (rp) -> (Some (Path.GetFileName(rp.fileName)))
    | None                  -> None

// Module comments with the ASN.1 comment markers stripped.
let moduleCleanedComments (m:Asn1Module) =
    m.Comments |> Array.map (fun x -> x.Trim().Replace("--", "").Replace("/*", "").Replace("*/",""))

let PrintModule stgFileName (m:Asn1Module) (f:Asn1File) (r:AstRoot)   =
    //let blueTasses = GenerateUperIcd.getModuleBlueTasses m |> Seq.map snd
    //let sortedTas = m.TypeAssignments //spark_spec.SortTypeAssignments m r acn |> List.rev
    let icdTasses = GenerateUperIcd.getModuleIcdTasses m

    let tases = icdTasses |> Seq.map (fun x -> PrintTas stgFileName x m r )
    let comments = moduleCleanedComments m
    let moduleName = m.Name.Value
    let title = if comments.Length > 0 then moduleName + " - " + comments.[0] else moduleName
    let commentsTail = if comments.Length > 1 then comments.[1..] else [||]
    let acnFileName = moduleAcnFileName r moduleName

    icd_acn.EmitModule stgFileName title (Path.GetFileName(f.FileName)) acnFileName commentsTail tases

let PrintNavLink stgFileName sTitle sTarget   =
    icd_acn.EmitNavLink stgFileName sTitle sTarget

let PrintTasses stgFileName (f:Asn1File)  (r:AstRoot)   =
    f.Modules |> Seq.map (fun  m -> PrintModule stgFileName m f r ) |> String.concat "\n"

let PrintNavLinks stgFileName (f:Asn1File)  (r:AstRoot)   =
    f.Modules |> Seq.map (fun  m -> PrintNavLink stgFileName m.Name.Value m.Name.Value ) |> String.concat "\n"

let emitCss (r:AstRoot) stgFileName   outFileName =
    let cssContent = icd_acn.RootCss stgFileName ()
    File.WriteAllText(outFileName, cssContent.Replace("\r", ""))

let selectTypeWithSameHash (lst:IcdTypeAss list) =
    match lst with
    | x1::[] -> x1
    | _      ->
        lst |> List.minBy(
            fun z ->
                let (ReferenceToType nodes) = z.typeId;
                nodes.Length)


let emitTypeCol stgFileName (r:AstRoot) (sType : IcdTypeCol) =
    match sType with
    | IcdPlainType label -> label
    | TypeHash hash ->
        let label = (selectTypeWithSameHash (r.icdHashes[hash])).name
        icd_acn.EmitSeqChild_RefType stgFileName label hash

// Hash of the table emitted for the type assignment (modName, tasName) — the
// link target for an ACN parameter whose type is a TAS. None when that TAS has
// no table in the selected set (e.g. filtered out by -icdPdus); the caller then
// falls back to plain text instead of emitting a dead link.
let tryFindTasTableHash (r:AstRoot) (selectedHashes:Set<string>) (modName:string) (tasName:string) : string option =
    r.icdHashes |>
    Map.toSeq |>
    Seq.collect snd |>
    Seq.choose(fun z ->
        match z.tasInfo with
        | Some ti when ti.modName = modName && ti.tasName = tasName -> Some z.hash
        | Some _ -> None
        | None -> None) |>
    Seq.filter selectedHashes.Contains |>
    Seq.sort |>
    Seq.tryHead

// One PrintParam row per ACN parameter of a parameterized type — restores the
// old pipeline's "ACN Parameters" section above the field rows (roadmap B2).
let emitTasParams stgFileName (r:AstRoot) (selectedHashes:Set<string>) (icdTas:IcdTypeAss) (colSpan:BigInteger) =
    icdTas.acnParameters |>
    List.mapi(fun i p ->
        let sType =
            match p.prmType with
            | IcdPrmBasic label -> label
            | IcdPrmRefTas (modName, tasName) ->
                match tryFindTasTableHash r selectedHashes modName tasName with
                | Some hash -> icd_acn.EmitSeqChild_RefType stgFileName tasName hash
                | None      -> tasName
        icd_acn.PrintParam stgFileName (i+1).AsBigInt p.name sType colSpan)


// ============================================================================
// Per-row bit offset ("starts at" column) - roadmap D1.
// The offset of a row is the cumulative bit position at which the field starts,
// measured from the start of the type/table. It is an exact number while every
// preceding row is fixed-size and guaranteed present; a "min..max" range once a
// preceding row is variable-size or optional; and "variable" once a repetition
// has been elided by a ThreeDOTs row (the hidden repeats make the position
// unbounded from the row list alone). CHOICE alternatives all restart at the
// same offset - after the fixed choice-index preamble, if any - because exactly
// one alternative is present on the wire; optional/conditional SEQUENCE rows
// contribute 0 to the guaranteed minimum (they may be absent). Computed purely
// from the already-rendered rows, so it does not touch the content hash or the
// generated code.
type private IcdRowOffset =
    | OffExact    of BigInteger
    | OffRange    of BigInteger * BigInteger
    | OffVariable
    | OffNone                        // the ThreeDOTs row itself: no offset

let private computeRowOffsets (kind:string) (rows: IcdRow list) : IcdRowOffset list =
    let isAlways (rw:IcdRow) = rw.sPresent = "always"
    let isNever  (rw:IcdRow) = rw.sPresent = "never"
    let offsetOf (curMin:BigInteger) (curMax:BigInteger) (variable:bool) =
        if variable then OffVariable
        elif curMin = curMax then OffExact curMin
        else OffRange(curMin, curMax)
    match kind with
    | "CHOICE" ->
        // Leading "always" rows are the choice-index preamble (the ACN index
        // determinant, when present); they accumulate into the base offset that
        // every alternative restarts from.
        let preamble = rows |> List.takeWhile (fun rw -> rw.rowType <> ThreeDOTs && isAlways rw)
        let rest = rows |> List.skip preamble.Length
        let preambleOffsets, (baseMin, baseMax) =
            preamble |> List.mapFold (fun (cMin, cMax) rw ->
                offsetOf cMin cMax false, (cMin + rw.minLengthInBits, cMax + rw.maxLengthInBits)) (0I, 0I)
        // An alternative is a maximal run of rows sharing the same presence
        // condition; each restarts at the base offset, and rows within it (e.g.
        // a sizeable alternative's Length + content) accumulate because they are
        // all present once that alternative is selected.
        let restOffsets =
            rest |> List.mapFold (fun (cMin, cMax, variable, curCond, prevSub) rw ->
                match rw.rowType with
                // Collapsed SEQUENCE OF element (roadmap D2): the alternative's
                // header row already carries the whole array size, so the element
                // rows and the ThreeDOTs that closes the group are transparent.
                | SubItemRow -> OffNone, (cMin, cMax, variable, curCond, true)
                | ThreeDOTs ->
                    match prevSub with
                    | true  -> OffNone, (cMin, cMax, variable, curCond, false)
                    | false -> OffNone, (cMin, cMax, true, curCond, false)
                | _ ->
                    let cMin, cMax, variable =
                        if curCond <> Some rw.sPresent then baseMin, baseMax, false
                        else cMin, cMax, variable
                    offsetOf cMin cMax variable,
                    (cMin + rw.minLengthInBits, cMax + rw.maxLengthInBits, variable, Some rw.sPresent, false)) (baseMin, baseMax, false, None, false)
            |> fst
        preambleOffsets @ restOffsets
    | _ ->
        // SEQUENCE / SEQUENCE OF / sizeable / primitive: linear accumulation.
        // A guaranteed-present row advances the minimum by its own minimum; an
        // optional/conditional row advances only the maximum (it may be absent);
        // an always-absent row advances neither.
        rows |> List.mapFold (fun (cMin, cMax, variable, prevSub) rw ->
            match rw.rowType with
            // Collapsed SEQUENCE OF element (roadmap D2): the header row already
            // accounts for the whole array size, so the element rows show no
            // offset and do not advance the parent's position.
            | SubItemRow -> OffNone, (cMin, cMax, variable, true)
            // A ThreeDOTs that closes a collapsed SEQUENCE OF group is
            // transparent; a top-level ThreeDOTs (elided repeats of an embedded
            // sizeable) makes downstream offsets unbounded.
            | ThreeDOTs ->
                match prevSub with
                | true  -> OffNone, (cMin, cMax, variable, false)
                | false -> OffNone, (cMin, cMax, true, false)
            | _ ->
                let minContrib = if isAlways rw then rw.minLengthInBits else 0I
                let maxContrib = if isNever rw then 0I else rw.maxLengthInBits
                offsetOf cMin cMax variable, (cMin + minContrib, cMax + maxContrib, variable, false)) (0I, 0I, false, false)
        |> fst

let private offsetDisplayBits (n:BigInteger) = n.ToString(CultureInfo.InvariantCulture)

let private offsetDisplay (off:IcdRowOffset) : string option =
    match off with
    | OffExact n    -> Some (offsetDisplayBits n)
    | OffRange(a,b) -> Some (sprintf "%s..%s" (offsetDisplayBits a) (offsetDisplayBits b))
    | OffVariable   -> Some "variable"
    | OffNone       -> None

// The "No" (index) column string of each row - roadmap D2.  A collapsed
// SEQUENCE OF's element rows (SubItemRow) are sub-numbered "topIndex.elementIndex"
// under their header FieldRow so the reader sees they belong to the array; every
// other row returns None, so the template keeps rendering the plain integer
// $nIndex$ (the byte output of tables without any collapse is unchanged).
// ThreeDOTs carry no number.
let private computeRowIndexOverrides (rows: IcdRow list) : string option list =
    rows |> List.mapFold (fun lastTop rw ->
        match rw.rowType with
        | SubItemRow ->
            let k = match rw.idxOffset with Some z -> z | None -> 1
            Some (sprintf "%d.%d" lastTop k), lastTop
        | ThreeDOTs -> None, lastTop
        | _ ->
            let n = match rw.idxOffset with Some z -> z | None -> 1
            None, n) 0 |> fst

let emitIcdRow stgFileName (r:AstRoot) (soOffset:string option) (soIndexOverride:string option) (rw:IcdRow) =
    let i = match rw.idxOffset with Some z -> z | None -> 1
    let sComment = rw.comments |> Seq.StrJoin (icd_uper.NewLine stgFileName ())
    // No constraint -> empty cell.  "N.A." is manufactured noise (roadmap A4).
    let sConstraint = match rw.sConstraint with None -> "" | Some x -> x
    let sClass = if i % 2 = 0 then (icd_acn.EvenRow stgFileName ()) else (icd_acn.OddRow stgFileName ())
    match rw.rowType with
    |ThreeDOTs -> icd_acn.EmitRowWith3Dots stgFileName ()
    | _        -> icd_acn.EmitSeqOrChoiceRow stgFileName sClass (BigInteger i) rw.fieldName sComment  rw.sPresent  (emitTypeCol stgFileName r rw.sType) sConstraint (rw.minLengthInBits.ToString()) (rw.maxLengthInBits.ToString()) None rw.sUnits soOffset soIndexOverride

// All usage paths that share this table.  More than one element means that
// byte-identical specializations were merged into a single table by the
// normalized content hash (roadmap B4).  Deterministic order.
let usageSitesOfHash (r:AstRoot) (hash:string) : string list =
    match r.icdHashes.TryFind hash with
    | Some lst -> lst |> List.map(fun z -> z.typeId.AsString) |> List.distinct |> List.sort
    | None -> []

let emitTas2 stgFileName (r:AstRoot) (selectedHashes:Set<string>) (displayName:string) (icdTas:IcdTypeAss)  =
    // The table itself is identified by its own usage path (title/nav); the
    // remaining sites of a merged table are listed as a table comment.
    let otherUsageSites =
        usageSitesOfHash r icdTas.hash |> List.filter(fun site -> site <> icdTas.typeId.AsString)
    let comments =
        match otherUsageSites with
        | [] -> icdTas.comments
        | _  -> icdTas.comments @ [sprintf "Used by: %s" (otherUsageSites |> String.concat ", ")]
    let sCommentLine = comments |> Seq.StrJoin (icd_uper.NewLine stgFileName ())
    let offsets = computeRowOffsets icdTas.kind icdTas.rows
    let indexOverrides = computeRowIndexOverrides icdTas.rows
    let arRows =
        List.map3 (fun rw off soIdx -> emitIcdRow stgFileName r (offsetDisplay off) soIdx rw) icdTas.rows offsets indexOverrides
    let bHasAcnDef = icdTas.hasAcnDefinition
    let sMaxBitsExplained = ""
    icd_acn.EmitSequenceOrChoice stgFileName false displayName icdTas.hash bHasAcnDef (icdTas.kind) (icdTas.minLengthInBytes.ToString()) (icdTas.maxLengthInBytes.ToString()) sMaxBitsExplained sCommentLine arRows (emitTasParams stgFileName r selectedHashes icdTas 4I) (sCommentLine.Split [|'\n'|])

(*
let rec PrintType2 stgFileName (r:AstRoot)  acnParams (icdTas:IcdTypeAss): string list =
    seq {
        let htmlContent = emitTas2 stgFileName acnParams icdTas
        yield htmlContent
        for c in icdTas.rows do
            match c.sType with
            | IcdPlainType _ -> ()
            | IcdRefType (_, IcdTypeAssHas hash) ->
                match r.icdHashes.TryFind hash with
                | Some chIcdTas ->
                    yield! PrintType2 stgFileName r (fun _ -> []) chIcdTas
                | None -> ()
    } |> Seq.toList
let printTas2 stgFileName (r:AstRoot) (ts:TypeAssignment) : string list =
    let myParams colSpan=
        ts.Type.acnParameters |>
        List.mapi(fun i x ->
            let sType =
                match x.asn1Type with
                | AcnGenericTypes.AcnParamType.AcnPrmInteger    _         -> "INTEGER"
                | AcnGenericTypes.AcnParamType.AcnPrmBoolean    _         -> "BOOLEAN"
                | AcnGenericTypes.AcnParamType.AcnPrmNullType   _         -> "NULL"
                | AcnGenericTypes.AcnParamType.AcnPrmRefType(_,ts)     -> icd_acn.EmitSeqChild_RefType stgFileName ts.Value (ToC ts.Value)
            icd_acn.PrintParam stgFileName (i+1).AsBigInt x.name sType colSpan)

    PrintType2 stgFileName r myParams ts.Type.icdFunction.typeAss
*)

let rec getMySelfAndChildren (r:AstRoot) (icdTas:IcdTypeAss) =
    seq {
        yield icdTas.hash
        for c in icdTas.rows do
            match c.sType with
            | IcdPlainType _ -> ()
            | TypeHash( hash) ->
                match r.icdHashes.TryFind hash with
                | Some chIcdTas ->
                    yield! getMySelfAndChildren r (selectTypeWithSameHash chIcdTas)
                | None -> ()

    } |> Seq.toList
(*
let PrintTasses2 stgFileName (r:AstRoot) : string list =
    let pdus = r.args.icdPdus |> Option.map Set.ofList
    r.icdHashes.Values |>
    Seq.collect id |>
    Seq.choose(fun z ->
        match z.tasInfo with
        | None -> None
        | Some ts when pdus.IsNone || pdus.Value.Contains ts.tasName -> Some z
        | Some _ -> None ) |>
    Seq.collect(fun icdTas -> getMySelfAndChildren r icdTas) |>
    Seq.distinct |>
    Seq.choose(fun hash ->
        let acnParams colSpan = []
        match r.icdHashes.TryFind hash with
        | Some chIcdTas -> Some (emitTas2 stgFileName r (fun _ -> []) (selectTypeWithSameHash chIcdTas))
        | None -> None) |>
    Seq.toList
*)
// Returns the hashes of the ICD type assignments that are reachable from the
// requested PDU roots (all type assignments when -icdPdus is not given), in
// document order. This is the set of tables printed in the new-pipeline ICD
// and dumped by -icdRaw.
let selectIcdHashesToPrint (r:DAst.AstRoot) : string list =
    let pdus = r.args.icdPdus |> Option.map Set.ofList
    seq {
        for f in r.Files do
            for m in f.Modules do
                for tas in m.TypeAssignments do
                    match pdus.IsNone || pdus.Value.Contains tas.Name.Value with
                    | true  ->
                        match tas.Type.icdTas with
                        | Some icdTas ->
                            let icdTassesHash = getMySelfAndChildren r icdTas
                            yield! icdTassesHash
                        | None -> ()
                    | false -> ()
    } |> Seq.distinct |> Seq.toList

// The representative IcdTypeAss of every selected hash, in the given order.
let private representativesOf (r:AstRoot) (icdHashesToPrint:string list) : (string*IcdTypeAss) list =
    icdHashesToPrint |>
    List.choose(fun h -> r.icdHashes.TryFind h |> Option.map(fun lst -> h, selectTypeWithSameHash lst))

// Display names of the selected tables, keyed by hash.  A display name shared
// by several tables (an in-context specialization reusing the bare TAS name,
// R7) is disambiguated with the usage context - "Samples (as Telemetry.smpl)"
// - while the TAS definition itself keeps the bare name.  Used for the nav
// pane, the table titles and the -icdRaw name field (roadmap B4).
let buildDisplayNameMap (r:AstRoot) (icdHashesToPrint:string list) : Map<string,string> =
    let contextOf (tas:IcdTypeAss) (withModule:bool) =
        let (ReferenceToType nodes) = tas.typeId
        let nodes =
            match withModule, nodes with
            | false, (MD _)::rest -> rest
            | _ -> nodes
        nodes |> List.map(fun n -> n.AsString) |> String.concat "."
    let proposed =
        representativesOf r icdHashesToPrint |>
        List.groupBy(fun (_, tas) -> tas.name) |>
        List.collect(fun (name, members) ->
            match members with
            | [(h, _)] -> [(h, name)]
            | _ ->
                let tasBearing = members |> List.filter(fun (_, tas) -> tas.tasInfo.IsSome)
                match tasBearing with
                | _::_::_ ->
                    // the same TAS name exists in more than one module: qualify everything with the full path
                    members |> List.map(fun (h, tas) -> (h, sprintf "%s (as %s)" name (contextOf tas true)))
                | _ ->
                    members |> List.map(fun (h, tas) ->
                        match tas.tasInfo with
                        | Some _ -> (h, name)  // the TAS definition keeps the bare name
                        | None   -> (h, sprintf "%s (as %s)" name (contextOf tas false)))) |>
        Map.ofList
    // Deterministic last-resort uniquification, in document order (two
    // distinct tables normally differ in name or usage context by now).
    let addHash (used:Set<string>, acc:Map<string,string>) (hash:string) =
        match proposed.TryFind hash with
        | None -> (used, acc)
        | Some name ->
            let rec unique candidate n =
                match used.Contains candidate with
                | false -> candidate
                | true  -> unique (sprintf "%s #%d" name n) (n+1)
            let finalName = unique name 2
            (used.Add finalName, acc.Add(hash, finalName))
    icdHashesToPrint |> List.fold addHash (Set.empty, Map.empty) |> snd

// True when -icdPdus was given and this table is one of the requested PDU
// roots; the nav pane lists those first and renders them visually distinct.
let isIcdPduRoot (r:AstRoot) (tas:IcdTypeAss) =
    match r.args.icdPdus, tas.tasInfo with
    | Some roots, Some ti -> roots |> List.contains ti.tasName
    | _, _ -> false

// Groups the selected hashes by their owning ASN.1 module, in file/module
// declaration order; inside a module the tables keep their first-reference
// order, except that the -icdPdus roots come first (roadmap B4).  The final
// group without file/module collects tables whose module is not among the
// compiled files (defensive; should not happen).
let orderTablesByModule (r:AstRoot) (icdHashesToPrint:string list) : (Asn1File option * Asn1Module option * string list) list =
    let reps = representativesOf r icdHashesToPrint
    let groups =
        [ for f in r.Files do
            for m in f.Modules do
                let mine = reps |> List.filter(fun (_, tas) -> tas.typeId.ModName = m.Name.Value)
                let ordered =
                    match r.args.icdPdus with
                    | None   -> mine
                    | Some _ ->
                        let roots, others = mine |> List.partition(fun (_, tas) -> isIcdPduRoot r tas)
                        roots@others
                match ordered with
                | [] -> ()
                | _  -> yield (Some f, Some m, ordered |> List.map fst) ]
    let claimed = groups |> List.collect(fun (_, _, hs) -> hs) |> Set.ofList
    let leftover = icdHashesToPrint |> List.filter(fun h -> not (claimed.Contains h))
    match leftover with
    | [] -> groups
    | _  -> groups@[(None, None, leftover)]

// One nav-pane entry of the new-pipeline document.
type IcdNavEntry = {
    navDisplayName : string
    navHash        : string
    navIsPduRoot   : bool
}

// One rendered module of the new-pipeline document body plus what the nav
// pane needs for it (body and nav are grouped by module, roadmap B4).
type IcdDocModule = {
    docModName    : string option  // None: fallback group without a module header
    docContent    : string
    docNavEntries : IcdNavEntry list
}

let printTasses3 stgFileName (r:DAst.AstRoot) : (string list)*(IcdDocModule list) =
    let icdHashesToPrint = selectIcdHashesToPrint r
    let selectedHashes = icdHashesToPrint |> Set.ofList
    let displayNames = buildDisplayNameMap r icdHashesToPrint
    let displayNameOf (tas:IcdTypeAss) =
        match displayNames.TryFind tas.hash with
        | Some dn -> dn
        | None    -> tas.name
    let moduleGroups = orderTablesByModule r icdHashesToPrint
    let docModules =
        moduleGroups |>
        List.map(fun (soFile, soModule, hashes) ->
            let tables =
                representativesOf r hashes |>
                List.map(fun (_, tas) -> (tas, emitTas2 stgFileName r selectedHashes (displayNameOf tas) tas))
            let navEntries =
                tables |> List.map(fun (tas, _) ->
                    {navDisplayName = displayNameOf tas; navHash = tas.hash; navIsPduRoot = isIcdPduRoot r tas})
            let wrappedTables = tables |> List.map (fun (_, tasContent) -> icd_acn.EmitTass stgFileName tasContent)
            let content =
                match soFile, soModule with
                | Some f, Some m ->
                    // Unlike the old pipeline, sModName is the bare module name: the
                    // EmitModule anchor (ICD_<module>) must match the nav module link.
                    icd_acn.EmitModule stgFileName m.Name.Value (Path.GetFileName(f.FileName)) (moduleAcnFileName r m.Name.Value) (moduleCleanedComments m) wrappedTables
                | _, _ ->
                    wrappedTables |> String.concat "\n"
            {docModName = soModule |> Option.map(fun m -> m.Name.Value); docContent = content; docNavEntries = navEntries})
    let orderedHashes = moduleGroups |> List.collect(fun (_, _, hs) -> hs)
    (orderedHashes, docModules)

// ============================================================================
// -icdRaw : deterministic, machine-readable JSON dump of the new-pipeline ICD
// model (the same reachable IcdTypeAss set that printTasses3 renders as HTML).
// Tables are identified by a stable id (display name + typeId usage path)
// instead of the MD5 content hash, so the dump stays diffable across compiler
// changes that only affect rendered details. No timestamps, stable ordering,
// invariant to machine/locale (ASCII-only output, invariant-culture numbers).
// ============================================================================

type private JsonValue =
    | JString of string
    | JNumber of BigInteger
    | JBool of bool
    | JNull
    | JArray of JsonValue list
    | JObject of (string*JsonValue) list

let private jsonEscapeString (s:string) =
    // Normalize line endings so the dump is byte-identical regardless of the
    // source file's EOL convention: a block comment read from a CRLF checkout
    // (e.g. on Windows/WSL) must produce the same JSON as an LF checkout (CI).
    // Without this the golden files would depend on the checkout's line endings.
    let s = s.Replace("\r\n", "\n").Replace("\r", "\n")
    let sb = System.Text.StringBuilder()
    sb.Append('"') |> ignore
    s |> Seq.iter(fun c ->
        match c with
        | '"'  -> sb.Append("\\\"") |> ignore
        | '\\' -> sb.Append("\\\\") |> ignore
        | '\b' -> sb.Append("\\b")  |> ignore
        | '\f' -> sb.Append("\\f")  |> ignore
        | '\n' -> sb.Append("\\n")  |> ignore
        | '\r' -> sb.Append("\\r")  |> ignore
        | '\t' -> sb.Append("\\t")  |> ignore
        | c when c < ' ' || c > '~' -> sb.AppendFormat(CultureInfo.InvariantCulture, "\\u{0:x4}", int c) |> ignore
        | c    -> sb.Append(c) |> ignore)
    sb.Append('"') |> ignore
    sb.ToString()

let rec private formatJson (indentLevel:int) (jv:JsonValue) : string =
    let pad    = String.replicate indentLevel "  "
    let padIn  = String.replicate (indentLevel+1) "  "
    match jv with
    | JNull         -> "null"
    | JBool true    -> "true"
    | JBool false   -> "false"
    | JNumber bi    -> bi.ToString(CultureInfo.InvariantCulture)
    | JString s     -> jsonEscapeString s
    | JArray []     -> "[]"
    | JArray items  ->
        let inner = items |> List.map (fun it -> padIn + formatJson (indentLevel+1) it) |> String.concat ",\n"
        "[\n" + inner + "\n" + pad + "]"
    | JObject []     -> "{}"
    | JObject fields ->
        let inner = fields |> List.map (fun (k,v) -> padIn + jsonEscapeString k + ": " + formatJson (indentLevel+1) v) |> String.concat ",\n"
        "{\n" + inner + "\n" + pad + "}"

// Stable identifier of an ICD table: display name + typeId usage path.
let private icdTasStableId (tas:IcdTypeAss) =
    sprintf "%s@%s" tas.name tas.typeId.AsString

// Maps each selected hash to a unique stable id. Two distinct tables normally
// differ in name or usage path; should they ever coincide, a deterministic
// #2/#3... suffix (in nav order) keeps the ids unique.
let private buildStableIdMap (r:AstRoot) (icdHashesToPrint:string list) : Map<string,string> =
    let addHash (used:Set<string>, acc:Map<string,string>) (hash:string) =
        match r.icdHashes.TryFind hash with
        | None -> (used, acc)
        | Some lst ->
            let baseId = icdTasStableId (selectTypeWithSameHash lst)
            let rec unique candidate n =
                match used.Contains candidate with
                | false -> candidate
                | true  -> unique (sprintf "%s#%d" baseId n) (n+1)
            let finalId = unique baseId 2
            (used.Add finalId, acc.Add(hash, finalId))
    icdHashesToPrint |> List.fold addHash (Set.empty, Map.empty) |> snd

let private jsonOfIcdTypeCol (r:AstRoot) (stableIds:Map<string,string>) (col:IcdTypeCol) =
    match col with
    | IcdPlainType label -> JObject [ ("kind", JString "plain"); ("value", JString label) ]
    | TypeHash hash ->
        // A reference row normally targets a table in the selected set; a
        // dangling reference (hash unknown) is dumped as null so that the ICD
        // test invariants can detect it rather than crash the compiler.
        let referencedId =
            match stableIds.TryFind hash with
            | Some sid -> Some sid
            | None ->
                match r.icdHashes.TryFind hash with
                | Some lst -> Some (icdTasStableId (selectTypeWithSameHash lst))
                | None -> None
        match referencedId with
        | Some sid -> JObject [ ("kind", JString "reference"); ("id", JString sid) ]
        | None     -> JObject [ ("kind", JString "reference"); ("id", JNull) ]

let private icdRowTypeName (rowType:IcdRowType) =
    match rowType with
    | FieldRow                    -> "FieldRow"
    | ReferenceToCompositeTypeRow -> "ReferenceToCompositeTypeRow"
    | LengthDeterminantRow        -> "LengthDeterminantRow"
    | PresentDeterminantRow       -> "PresentDeterminantRow"
    | PaddingRow                  -> "PaddingRow"
    | SubItemRow                  -> "SubItemRow"
    | ThreeDOTs                   -> "ThreeDOTs"

// The cumulative bit offset ("starts at") of a row - roadmap D1. exact/range
// carry finite bounds; variable (post-ThreeDOTs) and none (the ThreeDOTs row
// itself) carry null bounds. display mirrors the HTML "Offset (bits)" column.
let private jsonOfOffset (off:IcdRowOffset) =
    let s (n:BigInteger) = n.ToString(CultureInfo.InvariantCulture)
    match off with
    | OffExact n    -> JObject [ ("kind", JString "exact");    ("minBits", JNumber n); ("maxBits", JNumber n); ("display", JString (s n)) ]
    | OffRange(a,b) -> JObject [ ("kind", JString "range");    ("minBits", JNumber a); ("maxBits", JNumber b); ("display", JString (sprintf "%s..%s" (s a) (s b))) ]
    | OffVariable   -> JObject [ ("kind", JString "variable"); ("minBits", JNull);     ("maxBits", JNull);     ("display", JString "variable") ]
    | OffNone       -> JObject [ ("kind", JString "none");     ("minBits", JNull);     ("maxBits", JNull);     ("display", JNull) ]

let private jsonOfIcdRow (r:AstRoot) (stableIds:Map<string,string>) (off:IcdRowOffset) (rw:IcdRow) =
    JObject [
        ("idxOffset", match rw.idxOffset with Some i -> JNumber (BigInteger i) | None -> JNull)
        ("fieldName", JString rw.fieldName)
        ("comments", JArray (rw.comments |> List.map JString))
        ("sPresent", JString rw.sPresent)
        ("sType", jsonOfIcdTypeCol r stableIds rw.sType)
        ("sConstraint", match rw.sConstraint with Some c -> JString c | None -> JNull)
        ("minLengthInBits", JNumber rw.minLengthInBits)
        ("maxLengthInBits", JNumber rw.maxLengthInBits)
        ("sUnits", match rw.sUnits with Some u -> JString u | None -> JNull)
        ("rowType", JString (icdRowTypeName rw.rowType))
        ("offset", jsonOfOffset off)
    ]

// ACN parameter of a parameterized type. Mirrors the HTML rendering: the
// parameter's type is a reference to the TAS's table when that table is part
// of the emitted set, otherwise the plain TAS name.
let private jsonOfIcdAcnParameter (r:AstRoot) (stableIds:Map<string,string>) (selectedHashes:Set<string>) (p:IcdAcnParameter) =
    let typeJson =
        match p.prmType with
        | IcdPrmBasic label -> JObject [ ("kind", JString "plain"); ("value", JString label) ]
        | IcdPrmRefTas (modName, tasName) ->
            let referencedId =
                tryFindTasTableHash r selectedHashes modName tasName
                |> Option.bind stableIds.TryFind
            match referencedId with
            | Some sid -> JObject [ ("kind", JString "reference"); ("id", JString sid) ]
            | None     -> JObject [ ("kind", JString "plain"); ("value", JString tasName) ]
    JObject [ ("name", JString p.name); ("type", typeJson) ]

let private jsonOfIcdTas (r:AstRoot) (stableIds:Map<string,string>) (selectedHashes:Set<string>) (stableId:string) (displayName:string) (tas:IcdTypeAss) =
    JObject [
        ("id", JString stableId)
        // The rendered label of the table/nav entry: the bare type name,
        // disambiguated with the usage context when several tables share it.
        ("name", JString displayName)
        ("kind", JString tas.kind)
        ("tasInfo",
            match tas.tasInfo with
            | Some ti -> JObject [ ("modName", JString ti.modName); ("tasName", JString ti.tasName) ]
            | None    -> JNull)
        ("module", JString tas.typeId.ModName)
        ("usagePath", JString tas.typeId.AsString)
        // Every usage path that shares this table; more than one element means
        // byte-identical specializations were merged by the normalized hash.
        ("usageSites", JArray (usageSitesOfHash r tas.hash |> List.map JString))
        ("hasAcnDefinition", JBool tas.hasAcnDefinition)
        ("minLengthInBytes", JNumber tas.minLengthInBytes)
        ("maxLengthInBytes", JNumber tas.maxLengthInBytes)
        ("comments", JArray (tas.comments |> List.map JString))
        ("acnParameters", JArray (tas.acnParameters |> List.map (jsonOfIcdAcnParameter r stableIds selectedHashes)))
        ("rows", JArray (List.map2 (jsonOfIcdRow r stableIds) (computeRowOffsets tas.kind tas.rows) tas.rows))
    ]

let DoWorkIcdRawJson (r:AstRoot) (outFileName:string) =
    let icdHashesToPrint = selectIcdHashesToPrint r
    let selectedHashes = icdHashesToPrint |> Set.ofList
    let displayNames = buildDisplayNameMap r icdHashesToPrint
    // The dump follows the rendered document order: grouped by module, PDU
    // roots first when -icdPdus is given (roadmap B4).
    let orderedHashes = orderTablesByModule r icdHashesToPrint |> List.collect(fun (_, _, hs) -> hs)
    let stableIds = buildStableIdMap r orderedHashes
    let tables =
        orderedHashes |>
        List.choose(fun hash ->
            match r.icdHashes.TryFind hash with
            | Some lst ->
                let tas = selectTypeWithSameHash lst
                let displayName =
                    match displayNames.TryFind hash with
                    | Some dn -> dn
                    | None    -> tas.name
                Some (jsonOfIcdTas r stableIds selectedHashes stableIds.[hash] displayName tas)
            | None -> None)
    let navOrder = orderedHashes |> List.choose stableIds.TryFind |> List.map JString
    let root = JObject [ ("navOrder", JArray navOrder); ("tables", JArray tables) ]
    File.WriteAllText(outFileName, formatJson 0 root + "\n")

let PrintAsn1FileInColorizedHtml (stgFileName:string) (r:AstRoot) (icdHashesToPrint:string list) (emittedAsn1Anchors: System.Collections.Generic.HashSet<string>) (f:Asn1File) =
    let debug (tsName:string) =
        r.icdHashes.Values |>
        Seq.collect id |>
        Seq.filter(fun ts -> ts.name = tsName) |>
        Seq.iter(fun ts ->
            let content = DAstUtilFunctions.serializeIcdTasToText ts
            let fileName = sprintf "%s_%s.txt" tsName ts.hash
            File.WriteAllText(fileName, content))
    //debug("ALPHA-TC-SECONDARY-HEADER")
    //let tryCreateRefType = CreateAsn1AstFromAntlrTree.CreateRefTypeContent
    let icdHashesToPrintSet = icdHashesToPrint |> Set.ofList
    // Names of the TASes defined in the ASN.1 sources: only those names have a
    // definition-site token ("Name ::= ...") that can carry ASN1_<hash> anchors.
    let asn1DefinedTasNames =
        r.Files |>
        List.collect(fun f -> f.Modules) |>
        List.collect(fun m -> m.TypeAssignments) |>
        List.map(fun ts -> ts.Name.Value) |>
        Set.ofList
    let representativeOf (hash:string) = selectTypeWithSameHash r.icdHashes.[hash]
    // Every selected table's header links "#ASN1_<its own hash>", so every
    // selected hash needs an anchor at a TAS definition site (roadmap B5 / R6:
    // names mapping to several hashes used to render as plain text - no anchor
    // at all - leaving the ASN.1 link of all their tables dead).  A hash is
    // attributed to the table's own name when that name is a real TAS; tables
    // with synthetic names that never appear in the sources (e.g. the
    // "<path>_OCT_STR" CONTAINING wrappers) are anchored at the definition of
    // the TAS at the root of their usage path.
    let anchorNameOfHash (hash:string) : (string*string) option =
        let rep = representativeOf hash
        match asn1DefinedTasNames.Contains rep.name with
        | true  -> Some (rep.name, hash)
        | false ->
            let (ReferenceToType nodes) = rep.typeId
            match nodes with
            | _::(TA tasName)::_ when asn1DefinedTasNames.Contains tasName -> Some (tasName, hash)
            | _ -> None
    let usagePathLength (hash:string) =
        let (ReferenceToType nodes) = (representativeOf hash).typeId
        nodes.Length
    // TAS name -> the hashes anchored at its definition site, shortest usage
    // path first: the head is the TAS's own (standalone) table, which is what
    // the source token links to.
    let fileTypeAssignments : Map<string, string list> =
        icdHashesToPrint |>
        List.choose anchorNameOfHash |>
        List.groupBy fst |>
        List.map(fun (tasName, pairs) ->
            (tasName, pairs |> List.map snd |> List.sortBy(fun h -> (usagePathLength h, h)))) |>
        Map.ofList


    //let blueTasses = f.Modules |> Seq.collect(fun m -> getModuleBlueTasses m)
    let blueTassesWithLoc =
              f.TypeAssignments |>
              Seq.map(fun x -> x.Type) |>
              Seq.collect(fun x -> GetMySelfAndChildren x) |>
              Seq.choose(fun x -> match x.Kind with
                                  |ReferenceType ref    ->
                                    match f.TypeAssignments |> Seq.tryFind(fun y -> y.Name.Value = ref.baseInfo.tasName.Value) with
                                    | Some tas  -> Some(ref.baseInfo.tasName.Value, tas.Type.Location.srcLine, tas.Type.Location.charPos)
                                    | None      -> None
                                  | _                           -> None ) |> Seq.toArray
    let colorize (t: IToken, idx: int, blueTassesWithLoc: (string*int*int) array) =

            let blueTas = blueTassesWithLoc |> Array.tryFind(fun (_,l,c) -> l=t.Line && c=t.CharPositionInLine)
            let lt = icd_uper.LeftDiple stgFileName ()
            let gt = icd_uper.RightDiple stgFileName ()
            let isAsn1Token = GenerateUperIcd.asn1Tokens.Contains t.Text
            //let isType = containedIn tasses
            let safeText = t.Text.Replace("<",lt).Replace(">",gt)
            let uid () =
                let checkWsCmt (tok: IToken) =
                    match tok.Type with
                    |asn1Lexer.WS
                    |asn1Lexer.COMMENT
                    |asn1Lexer.COMMENT2 -> false
                    |_ -> true
                let findToken = Array.tryFind(fun tok -> checkWsCmt tok)
                let findNextToken = f.Tokens.[idx+1..] |> findToken
                let findPrevToken = Array.rev f.Tokens.[0..idx-1] |> findToken
                
                //let findNextToken = f.Tokens.[idx+1..] |> Array.tryFind(fun tok -> checkWsCmt tok)
                //let findPrevToken = f.Tokens.[0..idx-1] |> Array.tryFindBack(fun tok -> checkWsCmt tok)

                let nextToken =
                    let size = Seq.length(f.Tokens) - 1
                    match findNextToken with
                    |Some(tok) -> tok
                    |None -> if idx = size then t else f.Tokens.[idx+1]
                let prevToken =
                    match findPrevToken with
                    |Some(tok) -> tok
                    |None -> if idx = 0 then t else f.Tokens.[idx-1]
                match fileTypeAssignments.TryFind t.Text with
                | None -> safeText
                | Some ([]) -> safeText
                | Some (mainHash::extraHashes) ->
                    match nextToken.Type = asn1Lexer.ASSIG_OP && prevToken.Type <> asn1Lexer.LID with
                    | false -> icd_uper.TasName2 stgFileName safeText mainHash
                    | true  ->
                        // Definition site: one ASN1_<hash> anchor per attributed
                        // table.  HashSet.Add reports whether the hash is new -
                        // a second definition of the same name (same TAS name in
                        // another module) must not repeat anchors already
                        // emitted, so only fresh ones are anchored here.
                        let freshHashes = (mainHash::extraHashes) |> List.filter(fun h -> emittedAsn1Anchors.Add h)
                        let extraAnchors =
                            freshHashes |>
                            List.filter(fun h -> h <> mainHash) |>
                            List.map(fun h -> icd_uper.BlueTas stgFileName h "")
                        let tokenHtml =
                            match freshHashes |> List.contains mainHash with
                            | true  -> icd_uper.TasName stgFileName safeText mainHash
                            | false -> icd_uper.TasName2 stgFileName safeText mainHash
                        (extraAnchors @ [tokenHtml]) |> String.concat ""
            let colored () =
                match t.Type with
                |asn1Lexer.StringLiteral
                |asn1Lexer.OctectStringLiteral
                |asn1Lexer.BitStringLiteral -> icd_uper.StringLiteral stgFileName safeText
                |asn1Lexer.UID -> uid ()
                |asn1Lexer.COMMENT
                |asn1Lexer.COMMENT2 -> icd_uper.Comment stgFileName safeText
                |_ -> safeText
            match blueTas with
            |Some (s,_,_) -> icd_uper.BlueTas stgFileName (ToC s) safeText
            |None -> if isAsn1Token then icd_uper.Asn1Token stgFileName safeText else (colored ())
    let asn1Content = f.Tokens |> Seq.mapi(fun i token -> colorize(token,i,blueTassesWithLoc)) |> Seq.toList
    icd_uper.EmitFilePart2  stgFileName (Path.GetFileName f.FileName ) (asn1Content )


let DoWork (r:AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (stgFileName:string) (asn1HtmlStgFileMacros:string option)   outFileName =
    let files1 =  TL "GenerateAcnIcd_PrintTasses" (fun () -> r.Files |> List.map (fun f -> PrintTasses stgFileName f r ))
    let (icdHashesToPrint, docModules) = TL "GenerateAcnIcd_printTasses3" (fun () -> printTasses3 stgFileName r)
    let files1b = docModules |> List.map(fun dm -> dm.docContent)
    let bAcnParamsMustBeExplained = true
    let asn1HtmlMacros =
        match asn1HtmlStgFileMacros with
        | None  -> stgFileName
        | Some x -> x
    // one anchor-uniqueness scope for the whole document (the colorized ASN.1
    // parts of all files end up in the same HTML page)
    let emittedAsn1Anchors = System.Collections.Generic.HashSet<string>()
    let files2 = TL "GenerateAcnIcd_PrintAsn1FileInColorizedHtml" (fun () -> r.Files |> List.map (PrintAsn1FileInColorizedHtml asn1HtmlMacros r icdHashesToPrint emittedAsn1Anchors))
    let files3 = TL "GenerateAcnIcd_PrintAcnAsHTML2" (fun () -> PrintAcnAsHTML2 stgFileName r icdHashesToPrint)

    // Nav pane grouped by module, mirroring the document body; the -icdPdus
    // roots come first within their module and render visually distinct.
    let navLinks =
        docModules |>
        List.collect(fun dm ->
            let headerLink =
                match dm.docModName with
                | Some mn -> [icd_acn.EmitNavModule stgFileName mn]
                | None    -> []
            let entryLinks =
                dm.docNavEntries |>
                List.map(fun e ->
                    match e.navIsPduRoot with
                    | true  -> icd_acn.EmitNavLinkRootPdu stgFileName e.navDisplayName e.navHash
                    | false -> icd_acn.EmitNavLink stgFileName e.navDisplayName e.navHash)
            headerLink @ entryLinks) |>
        String.concat "\n"

    let cssFileName = Path.ChangeExtension(outFileName, ".css")
    let htmlContent = TL "GenerateAcnIcd_RootHtml" (fun () -> icd_acn.RootHtml stgFileName files1 files2 bAcnParamsMustBeExplained files3 (Path.GetFileName(cssFileName)) navLinks)
    let htmlContentb = TL "GenerateAcnIcd_RootHtml_b" (fun () -> icd_acn.RootHtml stgFileName files1b files2 bAcnParamsMustBeExplained files3 (Path.GetFileName(cssFileName)) navLinks)

    File.WriteAllText(outFileName, htmlContent.Replace("\r",""))
    File.WriteAllText(outFileName.Replace(".html", "_new.html"), htmlContentb.Replace("\r",""))
    let cssFileName = Path.ChangeExtension(outFileName, ".css");
    TL "GenerateAcnIcd_emitCss" (fun () -> emitCss r stgFileName cssFileName)


