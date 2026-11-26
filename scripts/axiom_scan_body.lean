open Lean Elab Command

/-- `#scan_axioms Prefix` checks every theorem declared in a module whose name starts with `Prefix` (equation lemmas
that exist in the compiled modules included). Each must depend only on `propext`, `Quot.sound` and `Classical.choice`, and no module
under the prefix may declare an axiom. A problem is an error, so `lean` exits non-zero. Besides the totals it prints
one line per module with the number of theorems that depend on `Classical.choice`. -/
elab "#scan_axioms " pfx:ident : command => do
  let env ← getEnv
  let p := pfx.getId
  let allowed : List Name := [``propext, ``Quot.sound, ``Classical.choice]
  let all := env.constants.fold (init := (#[] : Array (Name × ConstantInfo))) fun acc n ci => acc.push (n, ci)
  let mut theorems : Nat := 0
  let mut usesChoice : Nat := 0
  let mut modules : Array Name := #[]
  let mut perModule : NameMap Nat := {}
  let mut bad : Array String := #[]
  for (name, ci) in all do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx.toNat]!
    unless p.isPrefixOf modName do continue
    unless modules.contains modName do modules := modules.push modName
    match ci with
    | .axiomInfo _ => bad := bad.push s!"axiom declared: {name} (module {modName})"
    | .thmInfo _ =>
      theorems := theorems + 1
      let axs ← collectAxioms name
      if axs.contains ``Classical.choice then
        usesChoice := usesChoice + 1
        perModule := perModule.insert modName (perModule.getD modName 0 + 1)
      let extra := axs.filter (fun a => !allowed.contains a)
      unless extra.isEmpty do bad := bad.push s!"{name}: {extra.toList}"
    | _ => pure ()
  logInfo m!"AXIOM_SCAN modules={modules.size} theorems={theorems} using_Classical.choice={usesChoice} problems={bad.size}"
  for (m, n) in perModule.toList do
    logInfo m!"CHOICE_MODULE {m} {n}"
  unless bad.isEmpty do
    throwError m!"axiom scan failed:\n{"\n".intercalate bad.toList}"
