module

public import VerifiedGarbage.Impl.Ecdsa.P224.Arm
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.UmaalLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Impl.Ecdsa.P224.Arm
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P224.UmaalLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Arm.TaintSym
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.MulLit
import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.P224.Point
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Spec.Ecdsa.P224
import VerifiedGarbage.Proof.Weierstrass.Arm.MontModuli
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Lit
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P224.MulLit
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Main
meta import VerifiedGarbage.Proof.P224.Point
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Spec.Ecdsa.P224
meta import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.Weierstrass.Arm.MontModuli
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
import VerifiedGarbage.Proof.Framework.Arm.TaintMono
meta import VerifiedGarbage.Proof.Framework.Arm.TaintMono
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.P224
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Spec.Ecdsa.Generic
meta import VerifiedGarbage.Spec.P224
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `Ecdsa.Arm.P224.Verified`, which this module and modules that import it used -/

section

/-! ### `Ecdsa.Arm.P224.Contract`, which this module and modules that import it used -/

section

/-!
# ECDSA over P-224 on 32-bit ARM: the contract the proof is written against

The facts of `Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P224.inst` for 32-bit ARM, by name:
`vg_ecdsa_p224_sign(out, d, digest, k, scratch)`, with `out`, `d`, `digest`
and `k` in `r0`–`r3` and `scratch` on the stack (AAPCS), the result in `r0`
(the low word of `r1:r0`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm.P224

open VG VG.Arm Spec.Weierstrass Spec.Ecdsa

/-- The signature of the arguments, as the specification computes it. -/
abbrev sig (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith Spec.P224.curve (ofBytes (bytesAt m d 28)) (hashToInt Spec.P224.curve (bytesAt m digest 28))
    (ofBytes (bytesAt m k 28))

def signArm : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 56⟩
    let d : Region := ⟨State.addr (s.gpr .r1), 28⟩
    let digest : Region := ⟨State.addr (s.gpr .r2), 28⟩
    let k : Region := ⟨State.addr (s.gpr .r3), 28⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 8192⟩
    let args : Region := ⟨State.addr s.sp, 4⟩
    s.rd = [d, digest, k, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      out.Disjoint args ∧ scratch.Disjoint args ∧
      (s.gpr .r0).toNat + 56 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 28 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 28 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 28 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 8192 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32
  post s s' :=
    match sig s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2)) (State.addr (s.gpr .r3)) with
    | some rs => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
      bytesAt s'.mem (State.addr (s.gpr .r0)) 56 = encode Spec.P224.curve rs
    | none => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
      bytesAt s'.mem (State.addr (s.gpr .r0)) 56 = List.replicate 56 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

end VG.Proof.Ecdsa.Arm.P224

end

end

/-!
# ECDSA over P-224 on 32-bit ARM: `Verified`

P-224 is a curve the proof supports (`p224_ok`, and `Law` for its group law,
which the registration file supplies: `Proof.P224.law`), so `sign_ok` gives
the contract's postcondition; `r4`–`r11` and `lr` are restored and `sp`
kept. Constant time by taint tracking: the only branches are on loop
counters, and every address is `r12` (the working space, from the stack
argument) or `lr` (`out`) plus a constant or a counter.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm.P224

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass

theorem p224_nBits : Spec.Ecdsa.nBits p224.C = 224 := by
  show Spec.P224.curve.n.log2 + 1 = 224
  have h1 : 223 ≤ Spec.P224.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h2 : Spec.P224.curve.n.log2 < 224 :=
    (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega_using [h1, h2]

/-- No bit of a hash of `28` bytes is dropped. -/
theorem p224_sh : p224.sh = 0 := by
  unfold Cfg.sh
  rw [p224_nBits]
  rfl

theorem p224_ok : CfgOk p224 where
  n0 := by decide
  n10 := by decide
  onG := Proof.P224.onCurve_G
  p_odd := by decide +kernel
  n_odd := by decide +kernel
  p_lt := by decide +kernel
  n_lt := by decide +kernel
  n_enc := by decide +kernel
  p_ge := by decide +kernel
  n_ge := by decide +kernel
  p_lt_2n := by decide +kernel
  minv_p := by decide +kernel
  minv_n := by decide +kernel
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  sh := by rw [p224_sh]; decide
  fp := ⟨rfl, rfl, Mont.p224p_ok, rfl⟩
  fn := ⟨rfl, rfl, Mont.p224n_ok, rfl⟩
  mulNf := fun _ _ => Impl.Ecdsa.Arm.mulP224_noFrames
  pubNf := fun _ _ => Impl.Ecdsa.Arm.mulPubP224_noFrames

theorem pre_of {s : State} (h : signArm.pre s) : Pre p224 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem sign_arm (hL : Weierstrass.Law Spec.P224.curve) (s : State) (hs : signArm.pre s) :
    ∃ t s', Exec isa signP224 s t s' ∧ abiPreserved s s' ∧ signArm.post s s' := by
  have hp := pre_of hs
  obtain ⟨t, s', he, K, hpost⟩ := sign_ok p224_ok hL hp
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
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [56, 8192], argLen := 4,
    argBases := [(0, 1)] }

theorem wf₀_pre {u : Bool} {s : State} {extra : List Region} (hp : Pre (p224With u) s extra) :
    VG.Arm.Taint.Wf τ₀ s := by
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀, p224With, show Spec.P224.curve.len = 28 from rfl], ?_, ?_⟩,
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
    (hs : Pre (p224With u) s extraS) (ht : Pre (p224With u) t extraT) (pub : signArm.pub s t) :
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

theorem sign_ct : ConstantTime isa signArm.pre signArm.pub signP224 :=
  VG.Taint.constantTime (A := taint) τ₁
    (fun _ _ hs ht pub => agree₁ (agree₀ (pre_of hs) (pre_of ht) pub)) (by native_taint_decide)

end VG.Proof.Ecdsa.Arm.P224

end

end

/-!
# P-224 on 32-bit ARM with `umaal`: the configuration

`p224With true`, P-224 with its field multiplications by
`vg_p224_mul_mod_<p|n>_umaal`, is a configuration the code supports
(`p224u_ok`: what `p224_ok` states, but that its `vg_p224_mul_umaal` has no
frame).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm.P224

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm VG.Proof

theorem p224u_ok : CfgOk (p224With true) where
  n0 := p224_ok.n0
  n10 := p224_ok.n10
  onG := p224_ok.onG
  p_odd := p224_ok.p_odd
  n_odd := p224_ok.n_odd
  p_lt := p224_ok.p_lt
  n_lt := p224_ok.n_lt
  n_enc := p224_ok.n_enc
  p_ge := p224_ok.p_ge
  n_ge := p224_ok.n_ge
  p_lt_2n := p224_ok.p_lt_2n
  minv_p := p224_ok.minv_p
  minv_n := p224_ok.minv_n
  len8 := p224_ok.len8
  len_lo := p224_ok.len_lo
  len_hi := p224_ok.len_hi
  sh := p224_ok.sh
  fp := p224_ok.fp
  fn := p224_ok.fn
  mulNf := fun _ _ => Impl.Ecdsa.Arm.mulP224U_noFrames
  pubNf := fun _ _ => Impl.Ecdsa.Arm.mulPubP224U_noFrames

/-- Either configuration. -/
theorem p224With_ok (u : Bool) : CfgOk (p224With u) := by
  cases u
  · exact p224_ok
  · exact p224u_ok

end VG.Proof.Ecdsa.Arm.P224
