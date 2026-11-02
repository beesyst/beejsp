import SubspaceBridge.NewmanCompletion
import Lean
open Lean Elab Command
run_cmd do
  let mut todo := [`JSP000334.newman_conjecture_complete]
  let mut seen : NameSet := {}
  let mut rows : Array Json := #[]
  let mut axioms : Array String := #[]
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if !seen.contains n then
      seen := seen.insert n
      let ci ← getConstInfo n
      let ds := (ci.type.getUsedConstants.toList ++
        ((ci.value? true).map (fun e => e.getUsedConstants.toList)).getD []).eraseDups
      todo := ds ++ todo
      if ci.isAxiom then axioms := axioms.push n.toString
      rows := rows.push (Json.mkObj [("name",toJson n.toString), ("dependencies",toJson (ds.map Name.toString))])
  logInfo (Json.compress (Json.mkObj [("axioms",toJson axioms),("nodes",Json.arr rows)]))
