/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Mathport.Binary
import Mathport.Syntax.Expr3ToExpr
import Mathport.Syntax.Translate.Basic
import Mathport.Syntax.Translate.TacticInvocation.MathportTest

open Lean Lean.Elab.Term Lean.Elab.Command Lean.Meta Lean.PrettyPrinter
open Mathport.Syntax (expr3ToExpr)

namespace Mathport.Translate.TacticInvocation

structure Context where
  binportCtx : Binary.Context
  cmdCtx : Elab.Command.Context
  cmdState : Elab.Command.State

/--
Translate an elaborated Lean 3 expression to a Lean 4 `Expr`.
-/
def trExpr3 (ctx : Context) (uniqueNameToFVarId : HashMap Name FVarId)
    (e : Lean3.Expr) : MetaM Expr := do
  let e ← expr3ToExpr uniqueNameToFVarId e
  Binary.trExprCore ctx.binportCtx ctx.cmdCtx ctx.cmdState e none

def trGoalCore (ctx : Context) (goal : AST3.Goal) : TermElabM GoalStx := do
  go 0 {} #[]
  where
    go (i : Nat) (uniqueNameToFVarId : HashMap Name FVarId)
        (hyps : Array HypStx) : TermElabM GoalStx := do
      if h : i < goal.hyps.size then
        let hyp := goal.hyps[i]
        let type ← trExpr3 ctx uniqueNameToFVarId hyp.type
        let val? ← show MetaM _ from
          hyp.value.mapM (trExpr3 ctx uniqueNameToFVarId)
        let recurse (fvar : Expr) (stx : HypStx) :=
          go (i + 1) (uniqueNameToFVarId.insert hyp.name fvar.fvarId!)
              (hyps.push stx)
        match val? with
        | none =>
          let stx ← `(hyp| $(mkIdent hyp.pp):ident : $(← delab type):term)
          withLocalDeclD hyp.pp type λ fvar => recurse fvar stx
        | some val =>
          let stx ← `(hyp| $(mkIdent hyp.pp):ident : $(← delab type):term :=
                             $(← delab val):term)
          withLetDecl hyp.pp type val λ fvar => recurse fvar stx
      else
        let tgt ← delab (← trExpr3 ctx uniqueNameToFVarId goal.target)
        `(goal| { $hyps:hyp,* ⊢ $tgt:term })
    termination_by _ => goal.hyps.size - i

def trGoal (binportCtx : Binary.Context) (goal : AST3.Goal) :
     CommandElabM GoalStx := do
  let ctx := { binportCtx, cmdCtx := ← read, cmdState := ← get }
  liftTermElabM none $ trGoalCore ctx goal

def trTacticInvocation (binportCtx : Binary.Context)
    (invocation : AST3.TacticInvocation) : M Command := do
  let (true) := invocation.success
    | err "invocation was not successful"
  let (some tactic) := invocation.ast
    | err "tactic is not available"
  let start ← trGoals invocation.start
  let «end» ← trGoals invocation.end
  let tactic ← trTactic tactic
  `(command| #mathport_test $start:goal* $tactic:tactic $«end»:goal*)
  where
    err {α} (msg : MessageData) : CommandElabM α :=
      throwError "error while translating tactic invocation in declaration '{invocation.declName}':{indentD msg}"

    trGoals (goals : Array AST3.Goal) : CommandElabM (Array GoalStx) :=
      try
        goals.mapM (TacticInvocation.trGoal binportCtx)
      catch e =>
        err e.toMessageData

def trTacticInvocation? (binportCtx : Binary.Context)
    (invocation : AST3.TacticInvocation) : M (Option Format) := do
  println! "[tactic] {repr invocation.ast}"
  try
    let cmd ← trTacticInvocation binportCtx invocation
    liftCoreM $ formatCommand cmd
  catch e =>
    println! "{← e.toMessageData.toString}"
    return none

def trTacticInvocations (binportCtx : Binary.Context)
    (invocations : Array AST3.TacticInvocation) : M Format := do
  let fmts ← invocations.filterMapM (trTacticInvocation? binportCtx)
  return Format.joinSep fmts.toList "\n\n"

end Mathport.Translate.TacticInvocation
