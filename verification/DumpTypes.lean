import Lean
import MatrixTransport
import MatrixTransport.Paper

/-! Kernel declaration types for the mathematical statement correspondence. -/

open Lean Elab Command

set_option maxRecDepth 10000

run_cmd do
  let env ← getEnv
  let requestPath ← liftIO <| IO.getEnv "MATRIX_TRANSPORT_TYPE_REQUEST"
  let requested ← match requestPath with
    | none => pure (#[] : Array String)
    | some path => do
      let raw ← liftIO <| IO.FS.readFile path
      let value ← match Json.parse raw with
        | .ok value => pure value
        | .error msg => throwError "Invalid declaration request JSON: {msg}"
      match fromJson? value with
      | .ok names => pure (names : Array String)
      | .error msg => throwError "Expected an array of declaration names: {msg}"
  let entries := env.constants.toList.mergeSort
    fun a b ↦ a.1.toString false < b.1.toString false
  let mut found : Array String := #[]
  let mut rows : Array Json := #[]
  for (name, info) in entries do
    let text := name.toString false
    let project := (`MatrixTransport).isPrefixOf name || (`LiZouTransport).isPrefixOf name ||
      "_private.MatrixTransport.".isPrefixOf text
    if project || requested.contains text then
      if info.isUnsafe || info.isPartial then
        if requested.contains text then
          throwError "Unsafe or partial declaration requested: {name}"
        continue
      found := found.push text
      let axioms ← collectAxioms name
      for ax in axioms do
        if !(#[`propext, `Classical.choice, `Quot.sound]).contains ax then
          throwError "Unpermitted axiom {ax} in {name}"
      let kind := match info with
        | .thmInfo _ => "theorem"
        | .defnInfo _ => "definition"
        | .opaqueInfo _ => "opaque"
        | .axiomInfo _ => "axiom"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
        | .quotInfo _ => "quotient"
      let pretty ← liftTermElabM do
        withOptions (fun opts ↦ opts.setBool `pp.all true) do
          return (← Meta.ppExpr info.type).pretty
      let moduleName := match env.getModuleIdxFor? name with
        | none => env.mainModule.toString false
        | some idx => env.header.moduleNames[idx.toNat]!.toString false
      rows := rows.push <| Json.mkObj [
        ("name", toJson text), ("origin", toJson (if project then "project" else "standard")),
        ("kind", toJson kind), ("module", toJson moduleName),
        ("type_repr", toJson (reprStr info.type)), ("type_pretty", toJson pretty),
        ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial),
        ("axioms", toJson (axioms.map fun ax ↦ ax.toString false))]
  for name in requested do
    if !found.contains name then
      throwError "Requested declaration is absent from the compiled environment: {name}"
  liftIO <| IO.println "DECLARATION_TYPES_BEGIN"
  liftIO <| IO.println (Json.mkObj [
    ("schema_version", toJson (1 : Nat)), ("lean_version", toJson Lean.versionString),
    ("requested_standard_names", toJson requested), ("declarations", Json.arr rows)]).compress
  liftIO <| IO.println "DECLARATION_TYPES_END"
