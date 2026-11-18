module

import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineCTRounds
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineBase
public import VerifiedGarbage.Impl.MillerRabin.Arm.Arithmetic
import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
import VerifiedGarbage.Proof.Bignum.Arm.SquareOpCT
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineCTFnBody
import VerifiedGarbage.Proof.Bignum.Arm.FiosFastRound
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.MontOpArgs
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Impl.Bignum.Arm.MontOp
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.Bignum.Arm.FiosFast
public import VerifiedGarbage.Proof.Bignum.Arm.RoundCT
import VerifiedGarbage.Proof.Bignum.Arm.FiosArgs
import VerifiedGarbage.Proof.Bignum.Arm.FiosCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Bignum.Arm.FiosFast
meta import VerifiedGarbage.Proof.Bignum.Arm.FiosCT

/-! ### `Bignum.Arm.FiosFastCT`, which only this module used -/

section

/-! The fused scan's addresses and branches depend only on public pointers and counts. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosFast
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont VG.Proof.Bignum.Arm.Fios
open VG.Proof.X25519.Arm (wp_ldr)

private theorem keeping_r0 {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hp : ∀ s t, P s t → ∀ r ∈ rs, s.gpr r = t.gpr r)
    {hint : VG.Taint.Hint VG.Arm.Taint.T}
    (hc : ((FiosTaint.analysis.check (Taint.ofRegs rs) c hint).map
      fun τ => (RegSet.ofList [.r0]).subset τ.regs) = some true) :
    RelCT isa P c (fun s t => s.gpr .r0 = t.gpr .r0) := by
  intro s t tr₁ tr₂ u v h ex ey
  obtain ⟨τ, ht, ho⟩ := Option.map_eq_some_iff.mp hc
  obtain ⟨trace, final⟩ := VG.Taint.check_sound ht (Taint.agree_ofRegs (hp s t h)) ex ey
  exact ⟨trace, final.rf.1 .r0 (RegSet.mem_of_subset ho (RegSet.mem_ofList.mpr (by simp)))⟩

theorem code_relCT : RelCT isa
    (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r12 = t.gpr .r12 ∧
      s.gpr .r4 = t.gpr .r4 ∧ s.gpr .lr = t.gpr .lr)
    VG.Impl.Bignum.Arm.FiosFast.code (fun s t => s.gpr .r0 = t.gpr .r0) := by
  apply keeping_r0 [.r0,.r12,.r4,.lr] ?_ (by taint_decide)
  intro s t h r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

theorem round_ct {base : BitVec 32} {size tmp a b mod acc n i : Nat} (hi : i < n) :
    RelCT isa (fun s t => RoundReady base size tmp a b mod acc n i s ∧
      RoundReady base size tmp a b mod acc n i t)
      VG.Impl.Bignum.Arm.FiosFast.round (fun _ _ => True) := by
  let P := RoundReady base size tmp a b mod acc n i
  let Q := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 acc ∧
    s.gpr .r12 = base + BitVec.ofNat 32 b ∧ s.gpr .r4 = base + BitVec.ofNat 32 mod ∧
    s.gpr .lr = BitVec.ofNat 32 n
  have ct : RelCT isa (fun s t => P s ∧ P t) (.block VG.Impl.Bignum.Arm.Fios.args)
      (fun _ _ => True) := args_ct.mono
    (fun _ _ h => ⟨h.1.stage,h.2.stage⟩) (fun _ _ h => h)
  have wp (s : State) (h : P s) : WP isa (.block VG.Impl.Bignum.Arm.Fios.args) s Q := by
    obtain ⟨inv,hdr,_⟩ := h.secret
    refine WP.mono (args_ok s h.ctx hdr hi h.ptr) ?_
    rintro t ⟨_,p0,p12,p4,_,count,_⟩
    exact ⟨p0,p12,p4,count⟩
  have scan : RelCT isa (fun s t => Q s ∧ Q t) VG.Impl.Bignum.Arm.FiosFast.code
      (fun s t => s.gpr .r0 = t.gpr .r0) := code_relCT.mono
    (fun _ _ h => ⟨h.1.1.trans h.2.1.symm,h.1.2.1.trans h.2.2.1.symm,
      h.1.2.2.1.trans h.2.2.2.1.symm,h.1.2.2.2.trans h.2.2.2.2.symm⟩)
    (fun _ _ h => h)
  have finish : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0)
      (.block roundFinish) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    exact Taint.agree_ofRegs (by simpa using h)
  exact (pair_posts ct wp).seq (scan.seq finish)

end VG.Proof.Bignum.Arm.FiosFast

end

end

/-! # Fixed-index Montgomery operations have public traces -/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm.Arithmetic
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Impl.MillerRabin.Arm.Arithmetic
open VG.Proof.Rsa.Mont (Operand numAt arrAt)

private theorem product_fios_ct {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b) (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t =>
      (ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0) ∧
      (ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w b < numAt t.mem (State.addr base) w 0) ∧ s.sp = t.sp)
      (product true o a b) (fun _ _ => True) := by
  let P := fun (s t : State) =>
    (ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0) ∧
    (ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w b < numAt t.mem (State.addr base) w 0) ∧ s.sp = t.sp
  have args : RelCT isa P (.block (montOpArgs o a b)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (hc := .block []) (by rfl)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have ready := (relCT_keep_sp args (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨montOpArgs_ready s h.1.1 ho ha hb h.1.2, montOpArgs_ready t h.2.1.1 ho ha hb h.2.1.2⟩)
  have body := relCT_keep_sp ((MontPipeline.fnBody_ct FiosFast.round (MontPipeline.RoundLaw.loop FiosFast.round_law)
    (MontPipeline.RoundCTLaw.loop FiosFast.round_law (by intro _ _ _ _ _ _ _ _ _ _ hi; exact FiosFast.round_ct hi)) ho ha hb fit).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ FnBodyReady base len w o a b s ∧ FnBodyReady base len w o a b t)
    (fun _ _ h => h.2) (fun _ _ h => h)) (fun _ _ h => h.1)
  simp only [product, ↓reduceIte]
  exact (ready.seq (body.seq (loadStack_ct .r0 0))).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem product_ct (fios : Bool) {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b) (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t =>
      (ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0) ∧
      (ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w b < numAt t.mem (State.addr base) w 0) ∧ s.sp = t.sp)
      (product fios o a b) (fun _ _ => True) := by
  cases fios with
  | false => exact montOp_ct ho ha hb fit
  | true => exact product_fios_ct ho ha hb fit

theorem square_ct (fios : Bool) {base : BitVec 32} {len w o a : Nat}
    (ho : Operand o) (ha : Operand a) (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t =>
      (ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w a < numAt s.mem (State.addr base) w 0) ∧
      (ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w a < numAt t.mem (State.addr base) w 0) ∧ s.sp = t.sp)
      (square fios o a) (fun _ _ => True) := by
  cases fios with
  | false => exact squareOp_ct ho ha
  | true => exact product_fios_ct ho ha ha fit

end VG.Proof.MillerRabin.Arm.Arithmetic
