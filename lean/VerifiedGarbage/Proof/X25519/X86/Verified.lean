module

import VerifiedGarbage.Proof.X25519.X86.Main
meta import VerifiedGarbage.Proof.X25519.X86.Main
public import VerifiedGarbage.Proof.X25519.X86.Lit
meta import VerifiedGarbage.Proof.X25519.X86.Lit
public import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.X25519.X86.Contract
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.X25519.X86.Field32.Call
import VerifiedGarbage.Proof.X25519.X86.Field32.Verified
import VerifiedGarbage.Proof.X25519.X86.Finish
import VerifiedGarbage.Proof.X25519.X86.Fold
import VerifiedGarbage.Proof.X25519.X86.Setup
import VerifiedGarbage.Spec.Rc2
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.X25519.X86.Field32.Call
meta import VerifiedGarbage.Proof.X25519.X86.Field32.Verified
meta import VerifiedGarbage.Proof.X25519.X86.Finish
meta import VerifiedGarbage.Proof.X25519.X86.Fold
meta import VerifiedGarbage.Proof.X25519.X86.Setup
meta import VerifiedGarbage.Spec.Rc2

/-!
# X25519 on x86 (32-bit): `Verified`

Constant time (by taint tracking: the only branches are on the loop counters,
and every address is a pointer plus a constant or the counter, through the
inversion's call of `vg_gf25519_r32_pow250`),
satisfiability, and the shared contract of `Spec/`.
-/

@[expose] public section

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86

/-- The taint analysis starts with the stack arguments public, and the words
holding `out` and `scratch` known to be the base addresses of the writable
regions, and the 8 bytes below `esp`, where the inversion's call pushes, apart
from them. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [32, 4096], argLen := 20, argBases := [(4, 0), (16, 1)],
    room := 8 }

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hsc := hp.sc_fit; have ho := hp.out_fit; have hs := hp.sp_fit
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simpa [hp.wr] using hp.out_sc, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩ fun _ => ⟨hp.sp_room, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_using [hsc, ho]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [hs]) hp.ret_out hp.args_out
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [hs]) hp.ret_sc hp.args_sc
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.stk_out
    · exact hp.stk_sc

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.X25519.x25519X86.pre s₁) (h₂ : Proof.X25519.x25519X86.pre s₂)
    (hpub : Proof.X25519.x25519X86.pub s₁ s₂) : VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1, a2, a3⟩ := hpub
  have hp₁ := Pre.of _ h₁; have hp₂ := Pre.of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [outR, a0, a3]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hp₁.sp_fit h4 hk, VG.X86.Taint.argByte_eq hp₂.sp_fit h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 ∨ (k - 4) / 4 = 2 ∨ (k - 4) / 4 = 3 := by omega_using [hk]
    rcases this with h | h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2
    · exact congrArg _ a3

theorem x25519_ct : ConstantTime isa Proof.X25519.x25519X86.pre Proof.X25519.x25519X86.pub
    Impl.X25519.X86.x25519 :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000, 0x4000` at `0x8004`. -/
def satMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x30 else
  if a = 0x8011 then 0x40 else 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x8004, 16⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 4096⟩]

theorem x25519_ok (s : State) (hs : Proof.X25519.x25519X86.pre s) :
    ∃ t s', Exec isa Impl.X25519.X86.x25519 s t s' ∧ abiPreserved s s' ∧ Proof.X25519.x25519X86.post s s' :=
  x25519_correct (Pre.of s hs)

theorem x25519_verified :
    Verified X86.target Impl.X25519.X86.x25519 (Spec.X25519.x25519Contract X86.abi 8) :=
  Verified.of_correct x25519_ok x25519_ct (by
    have a0 : arg satState 0 = 0x1000 := by decide
    have a1 : arg satState 1 = 0x2000 := by decide
    have a2 : arg satState 2 = 0x3000 := by decide
    have a3 : arg satState 3 = 0x4000 := by decide
    have e : argAddr satState 0 = 0x8004 := by decide
    have esp : satState.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, Proof.X25519.x25519X86, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, stackBelow]
      [a0, a1, a2, a3, e, esp] using Proof.X25519.X86.satState)

end VG.Proof.X25519.X86
