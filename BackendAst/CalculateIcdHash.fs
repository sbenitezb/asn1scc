module CalculateIcdHash

open System
open System.IO
open System.Numerics
open System.Security.Cryptography
open DAst

// Helper functions for serialization
let writeOption (writer: BinaryWriter) (writeValue: 'a -> unit) (opt: 'a option) =
    match opt with
    | Some value ->
        writer.Write(true)
        writeValue value
    | None ->
        writer.Write(false)

let writeList (writer: BinaryWriter) (writeItem: 'a -> unit) (lst: 'a list) =
    writer.Write(lst.Length)
    lst |> List.iter writeItem

let writeString (writer: BinaryWriter) (str: string) =
    writer.Write(str)

let writeInt (writer: BinaryWriter) (i : int) =
    writer.Write(i)

let writeBigInteger (writer: BinaryWriter) (bi: BigInteger) =
    let bytes = bi.ToByteArray()
    writer.Write(bytes.Length)
    writer.Write(bytes)

let writeIcdTypeCol (writer: BinaryWriter) (icdTypeCol: IcdTypeCol) =
    match icdTypeCol with
    | TypeHash s ->
        writer.Write(0uy) // Tag for TypeHash
        writeString writer s
    | IcdPlainType s ->
        writer.Write(1uy) // Tag for IcdPlainType
        writeString writer s

let writeIcdRowType (writer: BinaryWriter) (icdRowType: IcdRowType) =
    let tag =
        match icdRowType with
        | FieldRow -> 0uy
        | ReferenceToCompositeTypeRow -> 1uy
        | LengthDeterminantRow -> 2uy
        | PresentDeterminantRow -> 3uy
        | ThreeDOTs -> 4uy
        // appended after ThreeDOTs so the existing tags (and therefore the
        // hashes of all padding-free tables) stay unchanged
        | PaddingRow -> 5uy
        // appended after PaddingRow for the same reason: only tables that
        // actually collapse a SEQUENCE OF (roadmap D2) carry SubItemRow rows,
        // so no existing table's hash changes.
        | SubItemRow -> 6uy
    writer.Write(tag)

let writeIcdAcnParameter (w: BinaryWriter) (p: IcdAcnParameter) =
    writeString w p.name
    match p.prmType with
    | IcdPrmBasic label ->
        w.Write(0uy) // Tag for IcdPrmBasic
        writeString w label
    | IcdPrmRefTas (modName, tasName) ->
        w.Write(1uy) // Tag for IcdPrmRefTas
        writeString w modName
        writeString w tasName

let writeIcdRow (w: BinaryWriter) (icdRow: IcdRow) =
    writeOption w (writeInt w) icdRow.idxOffset
    writeString w icdRow.fieldName
    writeList w (writeString w) icdRow.comments
    writeString w icdRow.sPresent
    writeIcdTypeCol w icdRow.sType
    writeOption w (writeString w) icdRow.sConstraint
    writeBigInteger w icdRow.minLengthInBits
    writeBigInteger w icdRow.maxLengthInBits
    writeOption w (writeString w) icdRow.sUnits
    writeIcdRowType w icdRow.rowType

// The hash is the table's identity: records with equal hashes are merged into
// a single ICD table.  Auto-generated determinant comments name their target
// by the *usage path* ("size determinant for TEST-CASE.MyPDU.payload.alt-20-1.
// parameterIds" vs "... for TEST-CASE.Payload-20-1.parameterIds"), which made
// byte-identical encodings hash differently at every use site (roadmap B4).
// The hash is therefore computed on a normalized copy in which any comment
// path below the record's own typeId is relativized to a fixed marker.  Paths
// that point outside the type (cross-table determinant references) stay
// absolute on purpose: they describe genuinely different wire relations.
let private normalizeForHash (t1: IcdTypeAss) =
    let selfPathDot = t1.typeId.AsString + "."
    let normalizeComment (c: string) = c.Replace(selfPathDot, "$SELF$.")
    { t1 with
        comments = t1.comments |> List.map normalizeComment
        rows = t1.rows |> List.map (fun rw -> { rw with comments = rw.comments |> List.map normalizeComment }) }

let calcIcdTypeAssHash (t0: IcdTypeAss) =
    let t1 = normalizeForHash t0
    use ms = new MemoryStream()
    use w = new BinaryWriter(ms)

    // Serialize the IcdTypeAss fields
    writeOption w (writeString w) t1.asn1Link
    writeOption w (writeString w) t1.acnLink
    writeString w t1.name
    writeString w t1.kind
    writeList w (writeString w) t1.comments
    // ACN parameters are rendered table content (the "ACN Parameters" rows
    // above the field rows), so they take part in the table identity: a
    // parameterized table must not dedup-merge with an otherwise identical
    // table of a non-parameterized type.
    writeList w (writeIcdAcnParameter w) t1.acnParameters
    writeBigInteger w t1.minLengthInBytes
    writeBigInteger w t1.maxLengthInBytes
    writeList w (writeIcdRow w) t1.rows

    w.Flush()
    ms.Position <- 0L
    let bytes = ms.ToArray()
    // Compute the hash
    let hashAlgorithm = MD5.Create()
    let hash = hashAlgorithm.ComputeHash(bytes)
    Convert.ToHexString(hash)


