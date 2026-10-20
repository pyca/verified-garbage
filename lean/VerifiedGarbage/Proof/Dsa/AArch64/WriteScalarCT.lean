module

public import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalarHead
public import VerifiedGarbage.Proof.Dsa.AArch64.FailureCT
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalarHead
meta import VerifiedGarbage.Proof.Dsa.AArch64.FailureCT
meta import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Dsa.AArch64.Operands
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Constant-time signature output, including rejection masks -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def ScalarOutRegs (offset : Nat) (second : Bool) (p : FailurePublic) (s : State) : Prop :=
  s.gpr .x1 = off p.base offset ∧
  s.gpr .x2 = (if second then p.output + BitVec.ofNat 64 p.width else p.output) ∧
  s.gpr .x9 = BitVec.ofNat 64 p.width

theorem writeScalar_ct (offset : Nat) (second : Bool) (ho : offset < 2 ^ 16)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (scalarHead offset second)) hc).isSome = true) :
    RelCT isa (Two FailurePre) (SignVerify.writeScalar offset second) (fun _ _ => True) := by
  unfold SignVerify.writeScalar seqs
  refine RelCT.seq (two_piece (Ψ := ScalarOutRegs offset second) [.x0]
    (pins_of (fun p _ => p.base) (by
      intro p s h r hr
      obtain ⟨_, _, _, hdi, _⟩ := h
      simp only [List.mem_singleton] at hr
      subst r
      exact hdi)) hT ?_) ?_
  · intro p s ⟨Z, hs, hZ, hdi, hout, hq⟩
    have hoff : (BitVec.ofNat 16 offset).setWidth 64 = BitVec.ofNat 64 offset := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega
    change WP isa (.block (scalarHead offset second)) s (ScalarOutRegs offset second p)
    unfold scalarHead
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [.x3, .x1, .x2, .x9, .x8] (Q := fun t =>
      t.gpr .x1 = off p.base offset ∧ t.gpr .x2 = p.output ∧ t.gpr .x9 = BitVec.ofNat 64 p.width)
      ?_ rfl rfl rfl) fun t ⟨⟨h1, h2, h9⟩, hk⟩ => ?_
    · brun [Core.field, field_enc .out, field_enc .qLen, field_enc .mask, fieldAddress,
        hdi, hout, hq, hoff,
        hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .out).2 hZ),
        hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .qLen).2 hZ),
        hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .mask).2 hZ)]
    cases second
    · exact WP.block_nil ⟨h1, h2, h9⟩
    · brun [ScalarOutRegs, h1, h2, h9]
  · exact two_taint [.x1, .x2, .x9]
      (pins_of (fun p r => if r = .x1 then off p.base offset else if r = .x2 then
          (if second then p.output + BitVec.ofNat 64 p.width else p.output) else BitVec.ofNat 64 p.width)
        (by
          intro p s h r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact h.1
          · exact h.2.1
          · exact h.2.2)) (by taint_decide)

theorem writeR_ct : RelCT isa (Two FailurePre) (SignVerify.writeScalar r false) (fun _ _ => True) :=
  writeScalar_ct r false (by decide) (by taint_decide)

theorem writeS_ct : RelCT isa (Two FailurePre) (SignVerify.writeScalar s true) (fun _ _ => True) :=
  writeScalar_ct s true (by decide) (by taint_decide)

end VG.Proof.Dsa.AArch64
