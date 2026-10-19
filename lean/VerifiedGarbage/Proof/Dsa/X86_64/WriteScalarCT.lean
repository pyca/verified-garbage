module

public import VerifiedGarbage.Proof.Dsa.X86_64.WriteScalarHead
public import VerifiedGarbage.Proof.Dsa.X86_64.FailureCT
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.WriteScalarHead
meta import VerifiedGarbage.Proof.Dsa.X86_64.FailureCT
meta import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Dsa.X86_64.Operands
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Constant-time signature output, including rejection masks -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def ScalarOutRegs (offset : Nat) (second : Bool) (p : FailurePublic) (s : State) : Prop :=
  s.gpr .rsi = off p.base offset ∧
  s.gpr .rdx = (if second then p.output + BitVec.ofNat 64 p.width else p.output) ∧
  s.gpr .rcx = BitVec.ofNat 64 p.width

theorem writeScalar_ct (offset : Nat) (second : Bool) (ho : offset < 2 ^ 31)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (scalarHead offset second)) hc).isSome = true) :
    RelCT isa (Two FailurePre) (SignVerify.writeScalar offset second) (fun _ _ => True) := by
  unfold SignVerify.writeScalar seqs
  refine RelCT.seq (two_piece (Ψ := ScalarOutRegs offset second) [.rdi]
    (pins_of (fun p _ => p.base) (by
      intro p s h r hr
      obtain ⟨_, _, _, hdi, _⟩ := h
      simp only [List.mem_singleton] at hr
      subst r
      exact hdi)) hT ?_) ?_
  · intro p s ⟨Z, hs, hZ, hdi, hout, hq⟩
    refine WP.mono (WP.keep [.rsi, .rdx, .rcx, .r8]
      (Q := ScalarOutRegs offset second p) ?_ (by cases second <;> rfl)) fun t ht => ht.1
    change WP isa (.block (scalarHead offset second)) s (ScalarOutRegs offset second p)
    unfold ScalarOutRegs
    cases second <;> unfold scalarHead <;>
      simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil, List.cons_append, List.nil_append]
    all_goals
      xrun [State.ea, Core.field, fieldAddress, hdi, hout, hq, sx_ofNat ho,
        hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .out).2 hZ),
        hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .qLen).2 hZ),
        hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .mask).2 hZ)]
  · exact two_taint [.rsi, .rdx, .rcx]
      (pins_of (fun p r => if r = .rsi then off p.base offset else if r = .rdx then
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

end VG.Proof.Dsa.X86_64
