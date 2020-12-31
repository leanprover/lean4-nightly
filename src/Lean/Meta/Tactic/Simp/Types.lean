/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.AppBuilder
import Lean.Meta.Tactic.Simp.SimpLemmas

namespace Lean.Meta
namespace Simp

def defaultMaxSteps := 100000

structure Result where
  expr   : Expr
  proof? : Option Expr := none -- If none, proof is assumed to be `refl`
  deriving Inhabited

abbrev Cache := ExprMap Result

structure Config where
  maxSteps   : Nat  := defaultMaxSteps
  contextual : Bool := false
  memoize    : Bool := true
  singlePass : Bool := false
  zeta       : Bool := true
  beta       : Bool := true
  eta        : Bool := true
  proj       : Bool := true
  ctorEq     : Bool := true

structure Context where
  config     : Config
  parent?    : Option Expr := none
  simpLemmas : SimpLemmas

structure State (σ : Type) where
  user     : σ -- user state
  cache    : Cache := {}
  numSteps : Nat := 0

abbrev SimpM (σ : Type) := ReaderT Context $ StateRefT (State σ) $ MetaM

inductive Step where
  | visit : Result → Step
  | done  : Result → Step

def Step.result : Step → Result
  | Step.visit r => r
  | Step.done r => r

structure Methods (σ : Type) where
  pre        : Expr → SimpM σ Step          := fun e => return Step.visit { expr := e }
  post       : Expr → SimpM σ Step          := fun e => return Step.done { expr := e }
  discharge? : Expr → SimpM σ (Option Expr) := fun e => return none

/- Internal monad -/
abbrev M (σ : Type) := ReaderT (Methods σ) $ SimpM σ

def pre (e : Expr) : M σ Step := do
  (← read).pre e

def post (e : Expr) : M σ Step := do
  (← read).post e

def discharge? (e : Expr) : M σ (Option Expr) := do
  (← read).discharge? e

def getConfig : M σ Config :=
  return (← readThe Context).config

@[inline] def withParent (parent : Expr) (f : M σ α) : M σ α :=
  withTheReader Context (fun ctx => { ctx with parent? := parent }) f

end Simp

export Simp (SimpM)

end Lean.Meta
