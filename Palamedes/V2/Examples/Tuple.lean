import Palamedes.V2.Synthesizer
import Mathlib.Lean.Expr

open Gen CorrectGen


open Lean Meta Elab Tactic Term Conv in
elab "tuple2exists" binder_name:ident : conv => withMainContext do
  let name ← elabAsFVar binder_name
  let g ← getMainGoal
  let body ← instantiateMVars (← Conv.getLhs)
  let type ← instantiateMVars (← name.getType)
  -- do something for prof of > 2 elements?
  let x := type.getAppArgs[0]!
  let y := type.getAppArgs[1]!
  -- get bvar indices for x, y binders
  let xidx := body.looseBVarRange + 1
  let yidx := body.looseBVarRange
  let replaced := body.replace (fun inner =>
    if inner.isAppOf `Prod.fst then
      let appArg := inner.appArg!
      if appArg.isFVarOf name then
        some (Expr.bvar xidx)
      else none
    else if inner.isAppOf `Prod.snd then
    let appArg := inner.appArg!
      if appArg.isFVarOf name then
        some (Expr.bvar yidx)
      else none
    else none
  )
  -- if nothing changed, die
  if replaced == body then
    throwUnsupportedSyntax
  else
    -- build the ∧ v = (x,y) clause
    let f := (.const `Prod.mk [0,0])
    let tup := mkApp4 f x y  (.bvar xidx) (.bvar yidx)
    let v := (.fvar name)
    let u ← getLevel type
    let eq := mkApp3 (mkConst ``Eq [u]) type v tup
    let newBody := mkAnd replaced eq
    -- build ∃x, ∃y
    let exists_y := mkApp2 (mkConst `Exists [u]) y (mkLambda `y BinderInfo.default y newBody)
    let exists_x := mkApp2 (mkConst `Exists [u]) x (mkLambda `x BinderInfo.default x exists_y)
    -- Create a new goal and prove it with aesop
    let goalTy' ← mkAppM ``Eq #[body,exists_x]
    let g' ← mkFreshExprMVar (some goalTy')
    let _ ← runTactic g'.mvarId! (← `(tactic| aesop))
    -- update lhs using the proof from aesop
    Conv.updateLhs exists_x g'


def genTupleOneElem : CorrectGen (λ (v: Int × Nat) => v.1 > 2) := by
  conv =>
    congr;
    intro v;
    tuple2exists v
  cgenerator_search

def genTupleOneElem2 : CorrectGen (λ (v: Int × Nat) => v.2 > 2) := by
  conv =>
    congr;
    intro v;
    tuple2exists v
  cgenerator_search
