module

public import VerifiedGarbage.Spec.Ffdh.Contract

/-! # Complete private-key generation and its permitted rejection leakage -/

@[expose] public section

namespace VG.Spec.Ffdh

open VG.Spec.Rsa (powMod)
open VG.Spec.RsaKeyGen (Rand)

/-- The two native budgets: range rejections and degenerate public values. -/
structure KeyRetries where
  keys : Nat
  scalars : Nat

def initialKeyRetries : KeyRetries := ⟨128, 128⟩

def keyInit (len : Nat) : Option (List Nat) :=
  if 64 ≤ len && len ≤ 1024 then some [128, 128, len, len] else none

inductive KeySearchOutcome where
  | entropy (retries : KeyRetries)
  | accepted (x y : Nat)
  | exhausted

structure KeySearchResult where
  outcome : KeySearchOutcome
  used : Nat
  /-- Only these rejection/acceptance statuses may leak; scalar bytes remain secret. -/
  statuses : List Nat

def KeySearchResult.consume (n status : Nat) (r : KeySearchResult) : KeySearchResult :=
  { r with used := n + r.used, statuses := status :: r.statuses }

def KeySearchResult.status (r : KeySearchResult) : Nat :=
  match r.outcome with | .entropy _ => 0 | .accepted .. => 1 | .exhausted => 3

def KeySearchResult.retries (r : KeySearchResult) : KeyRetries :=
  match r.outcome with | .entropy retries => retries | _ => ⟨0, 0⟩

/-- Native key search. Range rejection decreases the scalar budget; a
degenerate-public-value rejection decreases the key budget and resets the
scalar budget. The host receives an entropy request instead of an attempt
status. -/
def keySearch (a : Parameters) (len : Nat) (retries : KeyRetries) (rand : Rand) : KeySearchResult :=
  if retries.keys = 0 ∨ retries.scalars = 0 then ⟨.exhausted, 0, []⟩ else
  if rand.length < len then ⟨.entropy retries, 0, []⟩ else
  let x := scalarOfOctets a (rand.take len)
  let status := keyStatus a x
  if status = 1 then ⟨.accepted x (powMod a.g x a.p), len, [1]⟩ else
  if status = 2 then
    if retries.scalars ≤ 1 then ⟨.exhausted, len, [2]⟩ else
      (keySearch a len ⟨retries.keys, retries.scalars - 1⟩ (rand.drop len)).consume len 2
  else if status = 3 then
    if retries.keys ≤ 1 then ⟨.exhausted, len, [3]⟩ else
      (keySearch a len ⟨retries.keys - 1, 128⟩ (rand.drop len)).consume len 3
  else ⟨.exhausted, len, [status]⟩
termination_by 128 * retries.keys + retries.scalars
decreasing_by all_goals omega

end VG.Spec.Ffdh
