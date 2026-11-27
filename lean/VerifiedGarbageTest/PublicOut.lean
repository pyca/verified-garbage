module

import VerifiedGarbage.TCB.Rust
meta import VerifiedGarbage.TCB.Rust
import VerifiedGarbageTest.RenderOnly
meta import VerifiedGarbageTest.RenderOnly
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# Public outputs (`Api.publicOut`)

A function `(x: u32) -> u32` of a secret `x`, whose contract allows any result.
Code that returns `x` meets it, in constant time, and an `Api` that says its
result is public refuses it (`returnsSecret_not`): what a contract, of one run,
cannot say. Code that returns a constant is an `Artifact` of that `Api`
(`artifact`), with a proof of it, which no default gives.
-/

-- `#guard_msgs` compares every message of its command, which would include
-- the lakefile's profile of it (`ci/lean_profile.py`).
set_option profiler false

namespace VG.Test.PublicOut
open VG VG.AArch64

def sig : Sig := { params := [("x", .int .u32 false)], ret := some .u32 }

/-- The postcondition, which says nothing. -/
def Nothing (_ : BitVec 32) : Prop := True

def contract {M : ISA} (A : Abi M) : Contract M := sig.contract A (post := fun x _ _ _ => Nothing x)

/-- Its result is public. -/
def out : PublicOut sig where
  out _ := fun _x _m _m' (r : BitVec 32) => [r.toNat]

def api : Api where
  module := "test"
  name := "vg_test_public"
  sig := sig
  contracts := some fun A _ => contract A
  publicOut := some out
  summary := "Nothing."
  safety := ["None."]

/-- A state with the argument `x`. -/
def entry (x : BitVec 64) : State where
  gpr r := if r = .x0 then x else 0
  sp := 0x10000
  mem _ := 0
  rd := []
  wr := []

theorem entry_pre (x : BitVec 64) : (contract abi).pre (entry x) := by
  sig_pre [contract, sig, abi, argRegs, stackBelow, entry]

theorem pub (x y : BitVec 64) : (contract abi).pub (entry x) (entry y) := by
  sig_pub_keep [contract, sig, abi, argRegs, entry]

/-- Code that returns its argument. -/
def returnsSecret : Prog isa := .block []

theorem returnsSecret_verified : Verified target returnsSecret (contract abi) := by
  refine ⟨fun s _ => ⟨_, _, .block rfl, ⟨fun _ _ => rfl, rfl, fun _ _ => rfl⟩, ?_⟩,
    .of_leakage (fun _ => []) (fun s t s' _ e => by cases e with | block e =>
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e; exact e.2.symm)
      (fun _ _ _ _ _ => rfl), ⟨entry 0, entry_pre 0⟩⟩
  sig_post [contract, sig, abi, argRegs]
  exact True.intro

/-- Its result is not public. -/
theorem returnsSecret_not : ¬ out.Of abi returnsSecret (contract abi) := fun h =>
  absurd (h (entry 0) (entry 1) _ _ _ _ (entry_pre 0) (entry_pre 1) (pub 0 1) rfl (.block rfl) (.block rfl))
    (by decide)

/-- Code that returns 2. -/
def returnsTwo : Prog isa := .block [.movz .x .x0 2 0]

theorem returnsTwo_verified : Verified target returnsTwo (contract abi) := by
  refine ⟨fun s _ => ⟨_, _, .block rfl, ⟨fun r hr => ?_, rfl, fun _ _ => rfl⟩, ?_⟩,
    .of_leakage (fun _ => []) (fun s t s' _ e => by cases e with | block e => cases e; rfl)
      (fun _ _ _ _ _ => rfl), ⟨entry 0, entry_pre 0⟩⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · sig_post [contract, sig, abi, argRegs]
    exact True.intro

theorem returnsTwo_public : out.Of abi returnsTwo (contract abi) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ _ _ e₁ e₂
  cases e₁ with | block e₁ => cases e₂ with | block e₂ => cases e₁; cases e₂; rfl

def artifact : Artifact (renderOnly target) where
  api := api
  code := returnsTwo
  contract := contract abi
  verified := renderOnly_verified returnsTwo_verified
  publicOutOk := returnsTwo_public

-- No default proves it, whatever the code: the `Api` says what is public.
/-- error: could not synthesize default value for field 'publicOutOk' of 'VG.Artifact' using tactics -/
#guard_msgs (substring := true) in
example : Artifact (renderOnly target) where
  api := api
  code := returnsTwo
  contract := contract abi
  verified := renderOnly_verified returnsTwo_verified

end VG.Test.PublicOut
