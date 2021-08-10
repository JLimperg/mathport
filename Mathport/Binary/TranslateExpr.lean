/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam

Lean3 uses snake_case for everything.

As of now, Lean4 uses:
- camelCase for defs
- PascalCase for types
- snake_case for proofs
-/
import Lean
import Mathport.Util.Misc
import Mathport.Util.String
import Mathport.Binary.Basic
import Mathport.Binary.Number
import Mathport.Binary.Decode
import Mathport.Binary.Coe
import Mathport.Binary.TranslateName

namespace Mathport.Binary

open Lean Lean.Meta

def trExprCore (ctx : Context) (st : State) (cmdCtx : Elab.Command.Context) (cmdState : Elab.Command.State) (e : Expr) (ind? : Option (Name × Expr × List Name)) : MetaM Expr := do
  match ind? with
  | none => core e
  | some ⟨indName, indType, lps⟩ =>
    withLocalDeclD indName indType fun x => do
      let e := e.replace fun e => if e.isConstOf indName then some x else none
      let e ← core e
      let e := e.replace fun e =>
        if e == x then some (mkConst indName $ lps.map mkLevelParam)
        else if !e.hasFVar then (some e)
        else none
      e
where
  core e := do
    let mut e ← replaceConstNames e
    e ← expandCoe e
    e ← Meta.transform e (pre := translateNumbers)
    match (getRenameMap cmdState.env).find? `auto_param with
    | none     => pure ()
    | some ap4 => e ← Meta.transform e (pre := translateAutoParams ap4)
    e

  replaceConstNames (e : Expr) : MetaM Expr := do
    e.replaceConstNames fun n => (getRenameMap cmdState.env).find? n

  translateNumbers e : MetaM TransformStep :=  do
    match isConcreteNat? e with
    | some n => TransformStep.done $ mkNatLit n
    | none   =>
      match isNumber? e with
      | none => TransformStep.visit e
      | some info@⟨n, level, type, hasZero?, hasOne?, hasAdd?⟩ =>
        -- TODO: we will want to avoid wrapping "normal" Nat numbers
        -- (current workaround is for the OfNat instances to `no_index` the numbers)
        let inst := mkAppN (mkConst `OfNat.mk [level]) #[type, mkNatLit n, e]
        TransformStep.done $ mkAppN (mkConst `OfNat.ofNat [level]) #[type, mkNatLit n, inst]

  translateAutoParams (ap4 : Name) (e : Expr) : MetaM TransformStep :=
    -- def auto_param : Sort u → name → Sort u :=
    -- λ (α : Sort u) (tac_name : name), α
    if e.isAppOfArity ap4 2 then do
      let level    := e.getAppFn.constLevels!.head!
      let type     := e.getArg! 0
      let tacName3 ← Meta.reduce (e.getArg! 1)
      try
        let tacName3 ← decodeName tacName3
        let tacName ← mkCandidateLean4NameForKindIO tacName3 ExprKind.eDef
        let substr : Expr := mkAppN (mkConst `String.toSubstring) #[toExpr $ tacName.toString]
        let tacSyntax := mkAppN (mkConst `Lean.Syntax.ident) #[mkConst `Lean.SourceInfo.none, substr, toExpr tacName, toExpr ([] : List (Prod Name (List String)))]
        let e' := mkAppN (mkConst `autoParam [level]) #[type, tacSyntax]
        unless ← Meta.isDefEq e e' do throwError "[translateAutoParams] introduced non-defeq, {e} != {e'}"
        TransformStep.done e'
      catch ex => do
        -- they prove theorems about auto_param!
        println! "[decode] {(← ex.toMessageData.toString)}"
        -- strip the auto_param?
        TransformStep.visit e
    else
      TransformStep.visit e

  mkCandidateLean4NameForKindIO (n3 : Name) (eKind : ExprKind) : IO Name := do
    (mkCandidateLean4NameForKind n3 eKind).toIO ctx st cmdCtx cmdState

def trExpr (e : Expr) (ind? : Option (Name × Expr × List Name) := none) : BinportM Expr := do
  let ctx ← read
  let st ← get
  let cmdCtx ← readThe Elab.Command.Context
  let cmdState ← getThe Elab.Command.State
  liftMetaM $ trExprCore ctx st cmdCtx cmdState e ind?

end Mathport.Binary
