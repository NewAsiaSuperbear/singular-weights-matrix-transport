import Lean
import MatrixTransport
import MatrixTransport.Paper

open Lean Elab Command

private def projectDeclaration (name : Name) : Bool :=
  let s := name.toString false
  (`MatrixTransport).isPrefixOf name || (`LiZouTransport).isPrefixOf name ||
    "_private.MatrixTransport.".isPrefixOf s

run_cmd do
  let env ← getEnv
  let entries := (env.constants.toList.filter fun (name, _) ↦ projectDeclaration name).mergeSort
    fun a b ↦ a.1.toString false < b.1.toString false
  let mut rows : Array Json := #[]
  for (name, info) in entries do
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient"
    let axioms ← if info.isUnsafe || info.isPartial then pure #[] else collectAxioms name
    for ax in axioms do
      if !(#[`propext, `Classical.choice, `Quot.sound]).contains ax then
        throwError "Unpermitted axiom {ax} in {name}"
    rows := rows.push <| Json.mkObj [
      ("name", toJson (name.toString false)), ("kind", toJson kind),
      ("axioms", toJson (axioms.toList.map fun ax ↦ ax.toString false)),
      ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial)]
  liftIO <| IO.println "MANUSCRIPT_DECLARATIONS_BEGIN"
  liftIO <| IO.println (Json.mkObj [("schema_version", toJson (1 : Nat)),
    ("declarations", Json.arr rows)]).compress
  liftIO <| IO.println "MANUSCRIPT_DECLARATIONS_END"
