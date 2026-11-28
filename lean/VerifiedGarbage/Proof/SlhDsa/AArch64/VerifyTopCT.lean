module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.KeyGenCT
public import VerifiedGarbage.Impl.SlhDsa.AArch64.Verify
public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.SlhDsa.AArch64.TopShared
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public meta import VerifiedGarbage.Proof.SlhDsa.AArch64.KeyGenCT
public meta import VerifiedGarbage.Impl.SlhDsa.AArch64.Verify
public meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint

/-!
# SLH-DSA (SHAKE) on AArch64, `verify`: the blocks in constant time

Each block of `verify` by the taint analysis, from the registers that hold
the same public values in both runs; and a state of `verifyContract`'s
precondition (`verifySat_pre`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.VerifyTop

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Impl.SlhDsa.AArch64.Thash4 (mov)
open VG.Proof.SlhDsa.AArch64.KeyGen (Shake6 taintR)

section
variable {P : State → State → Prop}

/-- The test of `ctx_len` and `sig_len`. -/
theorem ct_chk {p : Params} (hp : Shake6 p)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ [Reg.x4, .x6], x.gpr r = y.gpr r) :
    RelCT isa P (.block (([.lsr .x .x9 .x4 8] : List Instr) ++ Impl.SlhDsa.AArch64.movV .x10 p.sigLen ++
      ([.sub .x .x10 .x6 .x10, .logic .orr .x .x9 .x9 .x10] : List Instr))) fun _ _ => True := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_ret0 (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ ([] : List Reg), x.gpr r = y.gpr r) :
    RelCT isa P (.block [.movz .x .x0 0 0]) fun _ _ => True :=
  taintR _ hr (by taint_decide)

/-- The prologue: the registers saved, the arguments kept, the header, the keys. -/
theorem ct_pro {p : Params} (hp : Shake6 p)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Impl.SlhDsa.AArch64.saveRegsAt Layout.oTop .x7 Impl.SlhDsa.AArch64.Shake.topSaved ++
      ([mov .x19 .x7, mov .x20 .x1, mov .x21 .x2, mov .x22 .x3, mov .x23 .x4, mov .x24 .x5,
        .movz .x .x9 0 0, .strb .x9 .x19 Layout.oHdr, .strb .x23 .x19 (Layout.oHdr + 1)] : List Instr) ++
      (List.range 2).flatMap (fun c => Impl.SlhDsa.AArch64.copyWords .x19 (Layout.oPkSeed + 32 * c) .x0 (p.n * c)
        (p.n / 8)))) fun _ _ => True := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

/-- The lanes, the indices, and `forsPk`'s arguments. -/
theorem ct_fblock {p : Params} (hp : Shake6 p)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ [Reg.x19, .x24], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Impl.SlhDsa.AArch64.Shake.seedLanes p ++ Impl.SlhDsa.AArch64.Shake.parseIdx p ++
      ([.movz .x .x10 0 0] : List Instr) ++ Impl.SlhDsa.AArch64.Shake.treeLanes p .x10 .x22 ++
      ([mov .x0 .x19, .addImm .x .x1 .x24 p.n, mov .x2 .x23] : List Instr))) fun _ _ => True := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

/-- Before the layers. -/
theorem ct_init {p : Params} (hp : Shake6 p)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ [Reg.x24], x.gpr r = y.gpr r) :
    RelCT isa P (.block (([.movz .x .x21 0 0] : List Instr) ++ Impl.SlhDsa.AArch64.lea .x20 .x24 (p.n + p.forsSigLen)))
      fun _ _ => True := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

/-- A layer's lanes and `xmssPk`'s arguments. -/
theorem ct_lblock {p : Params} (hp : Shake6 p)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ [Reg.x19, .x20, .x21], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Impl.SlhDsa.AArch64.Shake.treeLanes p .x21 .x22 ++
      ([mov .x0 .x19, mov .x1 .x23, mov .x2 .x20] : List Instr))) fun _ _ => True := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

/-- After a layer's call. -/
theorem ct_next {p : Params} (hp : Shake6 p)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ [Reg.x20, .x21], x.gpr r = y.gpr r) :
    RelCT isa P (.block (([.addImm .x .x20 .x20 p.xmssSigLen] : List Instr) ++
      Impl.SlhDsa.AArch64.movV .x11 (2 ^ p.hp - 1) ++
      ([.logic .and .x .x23 .x22 .x11, .lsr .x .x22 .x22 p.hp, .addImm .x .x21 .x21 1, .subImm .x .x9 .x21 p.d] :
        List Instr))) fun _ _ => True := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

/-- The comparison of the root and the epilogue. -/
theorem ct_tail {p : Params} (hp : Shake6 p)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ [Reg.x19], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Impl.SlhDsa.AArch64.Verify.compareRoot p ++
      Impl.SlhDsa.AArch64.restoreRegsAt Layout.oTop Impl.SlhDsa.AArch64.Shake.topSaved ++
      ([mov .x0 .x9] : List Instr))) fun _ _ => True := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

end

/-! ## A state of the precondition -/

def verifySat (p : Params) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | .x5 => 0x4000 | .x7 => 0x100000000 | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩]
  wr := [⟨0x100000000, scratchWords * 8⟩]

theorem verifySat_pre {p : Params} (hz : Sz p) :
    (Spec.SlhDsa.verifyContract p AArch64.abi 16).pre (verifySat p) := by
  have hn := hz.n32
  have hpk : p.pkLen ≤ 64 := by simp only [Params.pkLen]; omega
  sig_pre [Spec.SlhDsa.verifyContract, Spec.SlhDsa.verifySig, AArch64.abi, VG.AArch64.argRegs, verifySat]
  sig_and_intros
  all_goals first
    | rfl
    | omega
    | (simp only [BitVec.reduceToNat]; omega)
    | (simp only [scratchWords, BitVec.reduceToNat]; omega)
    | (apply Offset.disjoint_of_le <;> dsimp only <;> simp only [BitVec.reduceToNat, BitVec.reduceSub] <;> omega)
    | (apply Region.Disjoint.symm; apply Offset.disjoint_of_le <;> dsimp only <;>
        simp only [BitVec.reduceToNat, BitVec.reduceSub] <;> omega)
    | (apply Offset.disjoint_of_le <;> dsimp only <;>
        simp only [scratchWords, BitVec.reduceToNat, BitVec.reduceSub] <;> omega)
    | (apply Region.Disjoint.symm; apply Offset.disjoint_of_le <;> dsimp only <;>
        simp only [scratchWords, BitVec.reduceToNat, BitVec.reduceSub] <;> omega)

/-! ## The contract's public data -/

open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.AArch64 (Only)

theorem vleak_inj : ∀ {a b : List Byte}, leakBytes a = leakBytes b → a = b
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
    simp only [leakBytes, List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, vleak_inj h.2]
  | [], _ :: _, h => by simp [leakBytes] at h
  | _ :: _, [], h => by simp [leakBytes] at h

/-- What two runs of `verify` share: the pointers, the lengths, `sp`, and
the bytes of the public key, the message, the context string and the
signature. -/
structure VPub (p : Params) (σ₁ σ₂ : State) : Prop where
  regs : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], σ₁.gpr r = σ₂.gpr r
  sp : σ₁.sp = σ₂.sp
  pk : bytesAt σ₁.mem (σ₁.gpr .x0) p.pkLen = bytesAt σ₂.mem (σ₁.gpr .x0) p.pkLen
  msg : bytesAt σ₁.mem (σ₁.gpr .x1) (σ₁.gpr .x2).toNat = bytesAt σ₂.mem (σ₁.gpr .x1) (σ₁.gpr .x2).toNat
  ctx : bytesAt σ₁.mem (σ₁.gpr .x3) (σ₁.gpr .x4).toNat = bytesAt σ₂.mem (σ₁.gpr .x3) (σ₁.gpr .x4).toNat
  sig : bytesAt σ₁.mem (σ₁.gpr .x5) (σ₁.gpr .x6).toNat = bytesAt σ₂.mem (σ₁.gpr .x5) (σ₁.gpr .x6).toNat

theorem vpub_of {p : Params} {s₁ s₂ : State}
    (h : (Spec.SlhDsa.verifyContract p AArch64.abi 16).pub s₁ s₂) : VPub p s₁ s₂ := by
  sig_pub [Spec.SlhDsa.verifyContract, Spec.SlhDsa.verifySig, AArch64.abi, VG.AArch64.argRegs] at h
  obtain ⟨hsp, elk, h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  have e := vleak_inj elk
  rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6] at e
  obtain ⟨e3, eSig⟩ := List.append_inj e (by simp [bytesAt])
  obtain ⟨e2, eCtx⟩ := List.append_inj e3 (by simp [bytesAt])
  obtain ⟨ePk, eMsg⟩ := List.append_inj e2 (by simp [bytesAt])
  refine ⟨fun r hr => ?_, hsp, ePk, eMsg, eCtx, eSig⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-! ## The test of the lengths -/

/-- The first block: `x9 = (ctx_len ≫ 8) ∨ (sig_len - sigLen)`. -/
theorem chk_wp {p : Params} (hsl : p.sigLen < 2 ^ 64) (σ : State) :
    WP isa (.block (([.lsr .x .x9 .x4 8] : List Instr) ++ Impl.SlhDsa.AArch64.movV .x10 p.sigLen ++
      ([.sub .x .x10 .x6 .x10, .logic .orr .x .x9 .x9 .x10] : List Instr))) σ fun s =>
      Only [.x9, .x10] σ s ∧ s.gpr .x9 = (σ.gpr .x4 >>> 8 ||| (σ.gpr .x6 - BitVec.ofNat 64 p.sigLen)) := by
  rw [List.cons_append]
  refine MlKem.AArch64.wp_lsr (by decide) fun s₁ o₁ e₁ => ?_
  show WP isa (.block (Impl.SlhDsa.AArch64.movV .x10 p.sigLen ++
    ([.sub .x .x10 .x6 .x10, .logic .orr .x .x9 .x9 .x10] : List Instr))) s₁ _
  refine movV_ok hsl fun s₂ o₂ e₂ => MlKem.AArch64.wp_sub fun s₃ o₃ e₃ =>
    MlKem.AArch64.wp_orr fun s₄ o₄ e₄ => MlKem.AArch64.wp_nil ⟨((o₁.trans o₂).trans (o₃.trans o₄)).mono, ?_⟩
  rw [e₄, o₃.get .x9, e₃, e₂, o₂.get .x9, e₁, o₂.get .x6, o₁.get .x6]

theorem chk_zero {x4 x6 : BitVec 64} {L : Nat} (h : (x4 >>> 8 ||| (x6 - BitVec.ofNat 64 L)) = 0) :
    x4.toNat < 256 ∧ x6 = BitVec.ofNat 64 L := by
  obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h
  refine ⟨?_, ?_⟩
  · have := congrArg BitVec.toNat h1
    rw [MlKem.AArch64.toNat_lsr, BitVec.toNat_zero] at this
    omega
  · have := BitVec.sub_add_cancel x6 (BitVec.ofNat 64 L)
    rw [h2, BitVec.zero_add] at this
    exact this.symm

end VG.Proof.SlhDsa.AArch64.VerifyTop
