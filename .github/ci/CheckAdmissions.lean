import Lean
import Lean.Util.Sorry

/-! Repository-wide admission audit. Arguments are module names discovered from
source paths, not namespaces or a list of theorem names. `importAll` also loads
private declarations and proof bodies from Lean's module system. -/

open Lean Lean.Parser

private def moduleName (s : String) : Name :=
  (s.splitOn ".").foldl Name.str Name.anonymous

/-- Tokenize code using Lean's lexer, including interpolated expressions. -/
private partial def sourceTokens (interpolant := false) : ParserFn := fun c initial => Id.run do
  let stackSize := initial.stackSize
  let mut s := initial
  let mut braces := 0
  let mut previous := ""
  while true do
    s := whitespace c s
    if c.atEnd s.pos || (interpolant && braces == 0 && c.get s.pos == '}') then
      return s.mkNode `ciTokens stackSize
    if c.get s.pos == '/' && c.getNext s.pos == '-' then
      -- Unlike ordinary comments, Lean treats doc comments as grammar tokens.
      s := finishCommentBlock false 1 c (s.setPos (c.next (c.next s.pos)))
      continue
    let before := s
    if c.get s.pos == '"' && previous.endsWith "!" then
      s := interpolatedStrFn (sourceTokens true) c s
    else
      s := tokenFn [] c s
    if s.hasError || s.pos == before.pos then
      -- Custom notation can introduce punctuation absent from the base lexer.
      -- Lake checks its grammar; skip only this Unicode character here.
      s := before.setPos (c.next before.pos)
      previous := ""
      continue
    let token := s.stxStack.back
    previous := if token.isIdent then token.getId.toString else token.getAtomVal
    if previous == "{" then braces := braces + 1
    if previous == "}" then braces := braces - 1
  return s.mkNode `ciTokens stackSize

private partial def admissionToken? (stx : Syntax) : Option Syntax :=
  match stx with
  | .atom _ word => if word == "sorry" || word == "admit" then some stx else none
  | .ident _ _ name _ =>
      if name == `sorryAx || name == `_root_.sorryAx || name == `admit then some stx else none
  | .node _ kind children =>
      if kind == strLitKind || kind == charLitKind || kind == nameLitKind ||
          kind == interpolatedStrLitKind then none
      else children.findSome? admissionToken?
  | _ => none

private def isExternalModule (name : Name) : Bool :=
  name != `External && (`External).isPrefixOf name

private def auditSource (env : Environment) (path : System.FilePath) : IO Unit := do
  let input ← IO.FS.readFile path
  let ictx := mkInputContext input path.toString
  let state := (sourceTokens false).run ictx { env, options := {} }
    (getTokenTable env) (mkParserState ictx.inputString)
  if let some token := admissionToken? state.stxStack.back then
    let pos := ictx.fileMap.toPosition (token.getPos?.getD { byteIdx := 0 })
    throw <| IO.userError s!"Admission outside src/External: {path}:{pos.line}:{pos.column + 1}"

def main (args : List String) : IO UInt32 := do
  let sourceDir :: names := args
    | throw <| IO.userError "Expected the source directory followed by all source module names"
  if names.isEmpty then
    throw <| IO.userError "No source modules were supplied to the admission audit"
  initSearchPath (← findSysroot)
  let lexerEnv ← mkEmptyEnvironment
  for name in names do
    unless isExternalModule (moduleName name) do
      auditSource lexerEnv (System.FilePath.mk sourceDir / (name.replace "." "/" ++ ".lean"))
  let modules := names.toArray.map moduleName
  let imports := modules.map fun name => { module := name, importAll := true : Import }
  let env ← importModules imports {} (loadExts := false)
  for name in modules do
    unless env.header.moduleNames.contains name do
      throw <| IO.userError s!"Source module was not imported: {name}"
  let mut declarations := 0
  let mut admissions := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[idx]!
    if modules.contains origin then
      declarations := declarations + 1
      if let .axiomInfo _ := info then
        throw <| IO.userError s!"Project axiom is not permitted: {name} (module {origin})"
      if info.type.hasSorry || (info.value? true).any Expr.hasSorry then
        -- External.lean at the source root is not inside the External directory.
        unless isExternalModule origin do
          throw <| IO.userError s!"Admission outside src/External: {name} (module {origin})"
        admissions := admissions + 1
  IO.println s!"Admission audit passed: {modules.size} modules, {declarations} declarations, \
    {admissions} direct admissions, all in src/External."
  return 0
