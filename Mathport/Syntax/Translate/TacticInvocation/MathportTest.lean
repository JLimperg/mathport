/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Mathport.Syntax.Translate.Basic

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Command Lean.Elab.Tactic

namespace Mathport.Translate.TacticInvocation

syntax hyp := ident ":" term (":=" term)?
syntax goal := "{" hyp,*,? "⊢" term "}"

abbrev HypStx := TSyntax ``hyp
abbrev GoalStx := TSyntax ``goal

def elabHyp : HypStx → TermElabM (Name × Expr × Option Expr)
  | `(hyp| $userName:ident : $type:term := $val:term) => do
    let type ← elabTerm type none
    let val ← elabTerm val type
    return (userName.getId, type, val)
  | `(hyp| $userName:ident : $type:term) =>
    return (userName.getId, ← elabTerm type none, none)
  | _ => throwUnsupportedSyntax

def elabGoal : GoalStx → TermElabM (LocalContext × LocalInstances × Expr)
  | `(goal| { $hyps:hyp,* ⊢ $tgt:term }) =>
    withLCtx {} {} $ go 0 hyps tgt
  | _ => throwUnsupportedSyntax
  where
    go (i : Nat) (hyps : Array (TSyntax ``hyp)) (tgt : Term) :
        TermElabM (LocalContext × LocalInstances × Expr) := do
      if h : i < hyps.size then
        match ← elabHyp hyps[i] with
        | (userName, type, some val) =>
          withLetDecl userName type val λ _ => go (i + 1) hyps tgt
        | (userName, type, none) =>
          withLocalDecl userName .default type λ _ => go (i + 1) hyps tgt
      else
        let tgt ← elabTerm tgt none
        synthesizeSyntheticMVarsNoPostponing
        return (← getLCtx, ← getLocalInstances, tgt)
    termination_by _ => hyps.size - i

def elabPreState (goals : Array GoalStx) : TermElabM (Array MVarId) :=
  goals.mapM λ stx => do
    let (lctx, localInstances, tgt) ← elabGoal stx
    return (← mkFreshExprMVarAt lctx localInstances tgt).mvarId!

def compareGoal (expectedLCtx : LocalContext)
    (expectedLocalInstances : LocalInstances) (expectedTarget : Expr)
    (actualGoal : MVarId) : MetaM (Option MessageData) :=
  withMVarContext actualGoal do
    let expectedFVarIds := expectedLCtx.getFVarIds
    let actualFVarIds := (← getLCtx).getFVarIds
    if h₁ : expectedFVarIds.size = actualFVarIds.size then
      let mut subst : FVarSubst := {}
      for h₂ : i in [:actualFVarIds.size] do
        have : i < actualFVarIds.size := by simp_all [Membership.mem]
        have : i < expectedFVarIds.size := by simp_all [Membership.mem]
        let actualFVarId := actualFVarIds[i]
        let actualDecl ← getLocalDecl actualFVarId
        let expectedFVarId := expectedFVarIds[i]
        let expectedDecl ← withLCtx expectedLCtx expectedLocalInstances $
          getLocalDecl expectedFVarId

        let actualName := actualDecl.userName
        let expectedName := expectedDecl.userName

        let actualType ← instantiateMVars actualDecl.type
        let expectedType := subst.apply (← instantiateMVars expectedDecl.type)

        let actualVal ← actualDecl.value?.mapM instantiateMVars
        let expectedVal :=
          (← expectedDecl.value?.mapM instantiateMVars).map subst.apply

        if actualName != expectedName || actualType != expectedType ||
           actualVal != expectedVal then
          return m!"expected hypothesis '{printHyp expectedName expectedType expectedVal}' but got '{printHyp actualName actualType actualVal}'"
        subst := subst.insert expectedFVarId (mkFVar actualFVarId)

      let actualTarget ← instantiateMVars (← getMVarType actualGoal)
      let expectedTarget := subst.apply (← instantiateMVars expectedTarget)
      if actualTarget != expectedTarget then
        return m!"expected target '{expectedTarget}' but got '{actualTarget}'"

      return none
    else
      return "expected {expectedFVarIds.size} hypotheses but got {actualFVarIds.size}"
  where
    printHyp (userName : Name) (type : Expr) (value? : Option Expr) :
        MessageData :=
      let valueMsg :=
        match value? with
        | none => m!""
        | some v => m!" := {v}"
      m!"{userName} : {type}{valueMsg}"

private def err (msg : MessageData) : MetaM α :=
  throwError "mathport_test: {msg}"

elab "#mathport_test" preGoals:goal+ tac:tactic postGoals:goal* : command =>
  liftTermElabM none do
    let preGoals ← elabPreState preGoals
    let expectedPostGoals ← postGoals.mapM elabGoal
    let (_, { goals := actualPostGoals }) ← evalTactic tac
      |>.run { elaborator := .anonymous }
      |>.run { goals := preGoals.toList }
    let actualPostGoals := actualPostGoals.toArray
    if eq : expectedPostGoals.size = actualPostGoals.size then
      for h : i in [:expectedPostGoals.size] do
        have h₁ : i < expectedPostGoals.size := by simp_all [Membership.mem]
        have h₂ : i < actualPostGoals.size   := by simp_all [Membership.mem]
        let (lctx, localInstances, tgt) := expectedPostGoals[i]
        let msg? ← compareGoal lctx localInstances tgt actualPostGoals[i]
        if let (some msg) := msg? then
          err m!"mismatch in goal {i + 1}: {msg}"
    else
      err m!"expected {expectedPostGoals.size} goals, but got {actualPostGoals.size}"

end Mathport.Translate.TacticInvocation
