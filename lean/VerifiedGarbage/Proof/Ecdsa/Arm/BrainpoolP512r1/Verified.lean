module

import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Config
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Lit
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.Arm
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Config
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
meta import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Main
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Lit
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
import VerifiedGarbage.Proof.Framework.Arm.TaintMono
meta import VerifiedGarbage.Proof.Framework.Arm.TaintMono
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Spec.BrainpoolP512r1
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Spec.BrainpoolP512r1
meta import VerifiedGarbage.Spec.Ecdsa.Generic
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `Ecdsa.Arm.BrainpoolP512r1.Contract`, which this module and modules that import it used -/

section

/-!
# ECDSA over brainpoolP512r1 on 32-bit ARM: the contract the proof is written against

The facts of `Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP512r1.inst` for 32-bit ARM, by name:
`vg_ecdsa_brainpoolp512r1_sign(out, d, digest, k, scratch)`, with `out`, `d`, `digest`
and `k` in `r0`–`r3` and `scratch` on the stack (AAPCS), the result in `r0`
(the low word of `r1:r0`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm.BrainpoolP512r1

open VG VG.Arm Spec.Weierstrass Spec.Ecdsa

/-- The signature of the arguments, as the specification computes it. -/
abbrev sig (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith Spec.BrainpoolP512r1.curve (ofBytes (bytesAt m d 64)) (hashToInt Spec.BrainpoolP512r1.curve (bytesAt m digest 64))
    (ofBytes (bytesAt m k 64))

def signArm : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let d : Region := ⟨State.addr (s.gpr .r1), 64⟩
    let digest : Region := ⟨State.addr (s.gpr .r2), 64⟩
    let k : Region := ⟨State.addr (s.gpr .r3), 64⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 8192⟩
    let args : Region := ⟨State.addr s.sp, 4⟩
    s.rd = [d, digest, k, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      out.Disjoint args ∧ scratch.Disjoint args ∧
      (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 64 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 64 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 8192 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32
  post s s' :=
    match sig s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2)) (State.addr (s.gpr .r3)) with
    | some rs => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
      bytesAt s'.mem (State.addr (s.gpr .r0)) 128 = encode Spec.BrainpoolP512r1.curve rs
    | none => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
      bytesAt s'.mem (State.addr (s.gpr .r0)) 128 = List.replicate 128 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

end VG.Proof.Ecdsa.Arm.BrainpoolP512r1

end

end

/-!
# ECDSA over brainpoolP512r1 on 32-bit ARM: `Verified`

brainpoolP512r1 is a curve the proof supports (`brainpoolp512r1_ok`, and `Law` for its group law,
which the registration file supplies: `Proof.BrainpoolP512r1.law`), so `sign_ok` gives
the contract's postcondition; `r4`–`r11` and `lr` are restored and `sp`
kept. Constant time by taint tracking: the only branches are on loop
counters, and every address is `r12` (the working space, from the stack
argument) or `lr` (`out`) plus a constant or a counter.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm.BrainpoolP512r1

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass

theorem pre_of {s : State} (h : signArm.pre s) : Pre brainpoolp512r1 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem sign_arm (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (s : State) (hs : signArm.pre s) :
    ∃ t s', Exec isa signBrainpoolP512r1 s t s' ∧ abiPreserved s s' ∧ signArm.post s s' := by
  have hp := pre_of hs
  obtain ⟨t, s', he, K, hpost⟩ := sign_ok brainpoolp512r1_ok hL hp
  refine ⟨t, s', he, ⟨fun r hr => ?_, K.sp⟩, ?_⟩
  swap
  · simp only [signArm, BitVec.setWidth_append_eq_right]
    exact hpost
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact K.saved (.r4, 0) (by decide)
  · exact K.saved (.r5, 4) (by decide)
  · exact K.saved (.r6, 8) (by decide)
  · exact K.saved (.r7, 12) (by decide)
  · exact K.saved (.r8, 16) (by decide)
  · exact K.saved (.r9, 20) (by decide)
  · exact K.saved (.r10, 24) (by decide)
  · exact K.saved (.r11, 28) (by decide)
  · exact K.saved (.lr, 32) (by decide)

/-- The taint analysis starts with the register arguments public, the stack
argument too, and that word known to be the base address of `scratch`. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [128, 8192], argLen := 4,
    argBases := [(0, 1)] }

theorem wf₀_pre {u : Bool} {s : State} {extra : List Region} (hp : Pre (brainpoolp512r1With u) s extra) :
    VG.Arm.Taint.Wf τ₀ s := by
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀, brainpoolp512r1With, show Spec.BrainpoolP512r1.curve.len = 64 from rfl], ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨hp.sp_fit, ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    exact hp.out_sc
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · simpa only [State.addr, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] using hp.out_fit
    · simpa only [State.addr, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] using hp.sc_fit
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.out_args.symm
    · exact hp.sc_args.symm
  · intro p hm
    simp only [τ₀, List.mem_singleton] at hm
    subst hm
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem argByte_eq (s : State) (k : Nat) :
    VG.Arm.Taint.argByte s k = stackArgAddr s 0 + BitVec.ofNat 64 k := by
  simp [VG.Arm.Taint.argByte, stackArgAddr]

theorem agree₀ {u : Bool} {s t : State} {extraS extraT : List Region}
    (hs : Pre (brainpoolp512r1With u) s extraS) (ht : Pre (brainpoolp512r1With u) t extraT) (pub : signArm.pub s t) :
    VG.Arm.Taint.Agree τ₀ s t := by
  obtain ⟨hsp, h0, h1, h2, h3, ha⟩ := pub
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀_pre hs, wf₀_pre ht,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => hsp, fun k hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · rw [hs.wr, ht.wr]; simp only [outR, scR, ptr, scPtr, h0, ha]
  · rw [argByte_eq, argByte_eq, Mem.readW_byte s.mem _ hk, Mem.readW_byte t.mem _ hk]
    exact congrArg (fun v : BitVec 32 => v.extractLsb' (8 * k) 8) ha

/-- `τ₀` without the regions, which the code's timing does not need (no address or branch is
read back from memory): the analysis from it does not track the public bytes of `scratch`. -/
def τ₁ : VG.Arm.Taint.T := { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, argLen := 4 }

/-- `τ₁` says no more than `τ₀`. -/
theorem agree₁ {s t : State} (h : VG.Arm.Taint.Agree τ₀ s t) : VG.Arm.Taint.Agree τ₁ s t :=
  VG.Arm.Taint.leS_sound (σ := τ₀) ⟨RegSet.subset_refl _, id, .inr ⟨rfl, rfl⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, .inl rfl,
    fun _ h => (List.not_mem_nil h).elim⟩ h

theorem sign_ct : ConstantTime isa signArm.pre signArm.pub signBrainpoolP512r1 :=
  VG.Taint.constantTime (A := taint) τ₁
    (fun _ _ hs ht pub => agree₁ (agree₀ (pre_of hs) (pre_of ht) pub)) (by native_taint_decide)

end VG.Proof.Ecdsa.Arm.BrainpoolP512r1
