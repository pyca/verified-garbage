module

public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Public pointer and counter updates for one- and two-limb integrated steps. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest wp_dp wp_subs op2_imm dpVal)

theorem advance_ok (s : State) (k : Nat) (hk : k=1 ∨ k=2) :
    WP isa (.block [.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 (4*k))),
      .dp .add .r12 .r12 (.imm (BitVec.ofNat 32 (4*k))),
      .dp .add .r4 .r4 (.imm (BitVec.ofNat 32 (4*k))),
      .subs .lr .lr (.imm (BitVec.ofNat 32 k))]) s fun t =>
      t.gpr .r0=s.gpr .r0+BitVec.ofNat 32 (4*k) ∧
      t.gpr .r12=s.gpr .r12+BitVec.ofNat 32 (4*k) ∧
      t.gpr .r4=s.gpr .r4+BitVec.ofNat 32 (4*k) ∧
      t.gpr .lr=s.gpr .lr-BitVec.ofNat 32 k ∧
      t.z=(s.gpr .lr-BitVec.ofNat 32 k==0) ∧
      t.mem=s.mem ∧ Rest [.r0,.r12,.r4,.lr] s t := by
  have h4 : encodable (BitVec.ofNat 32 (4*k))=true := by rcases hk with rfl|rfl <;> decide
  have h1 : encodable (BitVec.ofNat 32 k)=true := by rcases hk with rfl|rfl <;> decide
  refine wp_dp (op2_imm h4) fun a ha => ?_
  refine wp_dp (op2_imm h4) fun b hb => ?_
  refine wp_dp (op2_imm h4) fun c hc => ?_
  refine wp_subs (op2_imm h1) fun t ht hz => WP.block_nil ?_
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [ht.other .r0 (by decide),hc.other .r0 (by decide),hb.other .r0 (by decide),ha.gpr,dpVal]
  · rw [ht.other .r12 (by decide),hc.other .r12 (by decide),hb.gpr,dpVal,ha.other .r12 (by decide)]
  · rw [ht.other .r4 (by decide),hc.gpr,dpVal,hb.other .r4 (by decide),ha.other .r4 (by decide)]
  · rw [ht.gpr,hc.other .lr (by decide),hb.other .lr (by decide),ha.other .lr (by decide)]
  · rw [hz,hc.other .lr (by decide),hb.other .lr (by decide),ha.other .lr (by decide)]
  · rw [ht.mem,hc.mem,hb.mem,ha.mem]
  · exact (ha.rest (by simp)).trans ((hb.rest (by simp)).trans ((hc.rest (by simp)).trans (ht.rest (by simp))))

end VG.Proof.Bignum.Arm.Fios
