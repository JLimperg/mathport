/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Mathport.Syntax.AST3

open Lean Lean.Meta

namespace Mathport.Syntax

/--
Translate a Lean 3 `expr` to a Lean 4 `Expr`. Many forms are not supported,
notably metavariables. Note that the translated `Expr` still lives in the Lean 3
environment, so names of constants have not been aligned. Use `trExpr` to do
this.
-/
def expr3ToExpr [Monad m] [MonadError m] (hyps : HashMap Name FVarId) :
    Lean3.Expr → m Expr
  | .var n => return .bvar n
  | .sort l => return .sort l
  | .const n lvls => return .const n lvls.toList
  | .mvar .. => throwUnsupported "mvar"
  | .local uniqName .. => do
    let (some fvarId) := hyps[uniqName]
      | throwError "internal error during translation: unknown unique fvar name {uniqName}"
    return .fvar fvarId
  | .app f e => return .app (← expr3ToExpr hyps f) (← expr3ToExpr hyps e)
  | .lam name bi type body =>
    return .lam name (← expr3ToExpr hyps type) (← expr3ToExpr hyps body) bi
  | .Pi name bi type body =>
    return .forallE name (← expr3ToExpr hyps type) (← expr3ToExpr hyps body) bi
  | .let name type value body =>
    return .letE name (← expr3ToExpr hyps type) (← expr3ToExpr hyps value)
      (← expr3ToExpr hyps body) (nonDep := false)
  | .annotation _ e => expr3ToExpr hyps e
  | .field _ _ => throwUnsupported "field"
  | .typed_expr _ val => expr3ToExpr hyps val -- TODO use mkExpectedTypeHint?
  | .structinst .. => throwUnsupported "structinst"
  | .prenum n => return mkNatLit n
  | .nat n => return mkNatLit n
  | .quote .. => throwUnsupported "quote"
  | .choice .. => throwUnsupported "choice"
  | .string s => return mkStrLit s
  | .no_equation => throwUnsupported "no_equation"
  | .equation .. => throwUnsupported "equation"
  | .equations .. => throwUnsupported "equations"
  | .equations_result .. => throwUnsupported "equations_result"
  | .as_pattern .. => throwUnsupported "as_pattern"
  | .delayed_abstraction .. => throwUnsupported "delayed_abstraction"
  | .sorry .. => throwUnsupported "sorry"
  | .rec_fn .. => throwUnsupported "rec_fn"
  | .proj .. => throwUnsupported "proj"
  | .ac_app .. => throwUnsupported "ac_app"
  | .perm_ac .. => throwUnsupported "perm_ac"
  | .cc_proof .. => throwUnsupported "cc_proof"
  where
    throwUnsupported {α} (what : String) : m α :=
      throwError "cannot translate expressions involving {what}"

end Mathport.Syntax
