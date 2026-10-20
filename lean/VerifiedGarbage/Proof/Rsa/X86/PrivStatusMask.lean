module
public import VerifiedGarbage.Impl.Rsa.X86.PrivChecked
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Accepted results are released only when public re-exponentiation matches -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Rsa.X86.PrivChecked

theorem statusMask_ok (s : State) (accepted equal : Bool)
    (good : s.gpr .ebx = BitVec.ofNat 32 accepted.toNat)
    (eq : s.gpr .eax = BitVec.ofNat 32 equal.toNat) :
    WP isa (.block statusMask) s fun t =>
      t.gpr .edx = -BitVec.ofNat 32 (accepted && equal).toNat ∧
      t.gpr .ebx = (if accepted then if equal then 1 else 2 else 0) ∧
      t.mem = s.mem ∧ Keeps [.edx, .ebp, .ebx] s t := by
  unfold statusMask
  refine wp_movS rfl fun a A _ => ?_
  refine wp_logicS (.inl rfl) rfl fun b B => ?_
  have bit : b.gpr .edx = BitVec.ofNat 32 (accepted && equal).toNat := by
    rw [B.gpr, A.gpr, A.other .eax (by decide), good, eq, ite_eq_left rfl]
    cases accepted <;> cases equal <;> rfl
  refine wp_movS rfl fun c C _ => ?_
  refine wp_subS rfl fun d D _ => ?_
  refine wp_movS rfl fun e E _ => ?_
  have mask : e.gpr .edx = -BitVec.ofNat 32 (accepted && equal).toNat := by
    rw [E.gpr, D.gpr, C.gpr, C.other .edx (by decide), bit]
    exact BitVec.zero_sub _
  refine wp_movS rfl fun f F _ => ?_
  refine wp_subS rfl fun g G _ => ?_
  have acceptedMask : g.gpr .ebp = -BitVec.ofNat 32 accepted.toNat := by
    rw [G.gpr, F.gpr, F.other .ebx (by decide), E.other .ebx (by decide), D.other .ebx (by decide),
      C.other .ebx (by decide), B.other .ebx (by decide), A.other .ebx (by decide), good]
    exact BitVec.zero_sub _
  have equalBit : g.gpr .eax = BitVec.ofNat 32 equal.toNat := by
    rw [G.other .eax (by decide), F.other .eax (by decide), E.other .eax (by decide),
      D.other .eax (by decide), C.other .eax (by decide), B.other .eax (by decide), A.other .eax (by decide), eq]
  refine wp_movS rfl fun h H _ => ?_
  refine wp_subS rfl fun i I _ => ?_
  refine wp_logicS (.inl rfl) rfl fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [T.other .edx (by decide), I.other .edx (by decide), H.other .edx (by decide),
      G.other .edx (by decide), F.other .edx (by decide), mask]
  · rw [T.gpr, I.gpr, H.gpr, H.other .eax (by decide), equalBit,
      I.other .ebp (by decide), H.other .ebp (by decide), acceptedMask, ite_eq_left rfl]
    cases accepted <;> cases equal <;> rfl
  · exact T.mem.trans (I.mem.trans (H.mem.trans (G.mem.trans (F.mem.trans (E.mem.trans
      (D.mem.trans (C.mem.trans (B.mem.trans A.mem))))))))
  · exact (A.keeps.mono (by decide)).trans ((B.keeps.mono (by decide)).trans ((C.keeps.mono (by decide)).trans ((D.keeps.mono (by decide)).trans ((E.keeps.mono (by decide)).trans ((F.keeps.mono (by decide)).trans ((G.keeps.mono (by decide)).trans ((H.keeps.mono (by decide)).trans ((I.keeps.mono (by decide)).trans ((T.keeps.mono (by decide)))))))))))

end VG.Proof.Rsa.X86.PrivChecked
