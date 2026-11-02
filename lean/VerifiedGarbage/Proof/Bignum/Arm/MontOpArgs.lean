module

public import VerifiedGarbage.Impl.Bignum.Arm.MontOp
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Bignum.Arm.MontFnBodyCT

/-! # Select public array indices for a verified Montgomery operation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (Operand numAt)
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

theorem montOpArgs_ok (s : State) {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) :
    WP isa (.block (montOpArgs o a b)) s fun t =>
      t.gpr .r2 = BitVec.ofNat 32 o ∧ t.gpr .r3 = BitVec.ofNat 32 a ∧ t.gpr .r12 = BitVec.ofNat 32 b ∧
      t.mem = s.mem ∧ Rest [.r2, .r3, .r12] s t := by
  have enc : ∀ i : Fin 8, encodable (BitVec.ofNat 32 i.val) = true := by decide
  unfold montOpArgs
  refine wp_mov (op2_imm (enc ⟨o, ho⟩)) fun u h => ?_
  refine wp_mov (op2_imm (enc ⟨a, ha⟩)) fun v j => ?_
  refine wp_mov (op2_imm (enc ⟨b, hb⟩)) fun t l => WP.block_nil ?_
  exact ⟨(l.other .r2 (by decide)).trans ((j.other .r2 (by decide)).trans h.gpr),
    (l.other .r3 (by decide)).trans j.gpr, l.gpr, l.mem.trans (j.mem.trans h.mem),
    (h.rest (by simp)).trans ((j.rest (by simp)).trans (l.rest (by simp)))⟩

theorem montOpArgs_ready (s : State) {base : BitVec 32} {len w o a b : Nat}
    (h : ArithmeticReady base len w s) (ho : Operand o) (ha : Operand a) (hb : Operand b)
    (operand : numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0) :
    WP isa (.block (montOpArgs o a b)) s (FnBodyReady base len w o a b) := by
  refine WP.mono (montOpArgs_ok s ho.1 ha.1 hb.1) ?_
  rintro t ⟨po, pa, pb, mem, rest⟩
  refine ⟨h.workspace.congr rest.wr, ?_, ?_, (rest.gpr .r0 (by simp)).trans h.ptr, po, pa, pb, ?_, ?_⟩
  · rw [mem]; exact h.layout
  · rw [mem]; exact h.width
  · rw [mem]; exact h.inverse
  · rw [mem]; exact operand

end VG.Proof.Bignum.Arm
