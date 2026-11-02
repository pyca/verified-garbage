module
public import VerifiedGarbage.Impl.Bignum.Arm.Exp
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Bignum.Arm.Exp
meta import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StageCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Loading an exponent byte reveals only its public pointer -/

@[expose] public section

namespace VG.Proof.Bignum.Arm.ConditionalExp

variable {ok : Prop}
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)
open VG.Proof.X25519.Arm (wp_ldr)

theorem expByteHead_ct {base ep : BitVec 32} {len w : Nat} :
    RelCT isa (fun s t =>
      (ArithmeticReady base len w s ∧ s.mem.readW (VG.Proof.Mont.off (State.addr base) 128) 32 = ep) ∧
      (ArithmeticReady base len w t ∧ t.mem.readW (VG.Proof.Mont.off (State.addr base) 128) 32 = ep))
      expByteHead (fun _ _ => True) := by
  let P := fun s : State => ArithmeticReady base len w s ∧
    s.mem.readW (VG.Proof.Mont.off (State.addr base) 128) 32 = ep
  let Q := fun s : State => s.gpr .r0 = base ∧ s.gpr .r2 = ep
  have first : RelCT isa (fun s t => P s ∧ P t) (.block [.ldr .r2 .r0 128]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.1.ptr.trans h.2.1.ptr.symm
  have wp (s : State) (h : P s) : WP isa (.block [.ldr .r2 .r0 128]) s Q := by
    have size : 132 ≤ 8 * len := by
      have := h.1.layout.2.2.1
      simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at this
      omega
    refine wp_ldr (a := VG.Proof.Mont.off (State.addr base) 128) (by decide)
      (by rw [h.1.ptr]; exact addr_add (by have := h.1.workspace.nowrap; omega))
      (h.1.workspace.read (by omega)) fun t j => WP.block_nil ?_
    exact ⟨(j.other .r0 (by decide)).trans h.1.ptr, j.gpr.trans h.2⟩
  have tail : RelCT isa (fun s t => Q s ∧ Q t) (.block ([.ldrb .r1 .r2 0] ++ expByteSave)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r2]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.trans h.2.1.symm
    · exact h.1.2.trans h.2.2.symm
  exact RelCT.block_append (M := isa) (l₁ := [.ldr .r2 .r0 128]) (l₂ := [.ldrb .r1 .r2 0] ++ expByteSave)
    ((pair_posts first wp).seq tail)

end VG.Proof.Bignum.Arm.ConditionalExp
