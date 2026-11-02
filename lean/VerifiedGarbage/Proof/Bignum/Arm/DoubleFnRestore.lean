module

import VerifiedGarbage.Proof.Bignum.Arm.DoubleFnBody
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleFnBodyCT
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Compose modular doubling inside the outer RSA stack frame -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem doubleFnRestore_ok (s : State) {base : BitVec 32} {len w o a b : Nat}
    (ready : DoubleFnReady base len w o a b s) (ho : Operand o) (ha : Operand a) (hb : Operand b)
    (read : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (sep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩)
    (saved : s.mem.readW (State.addr s.sp) 32 = base) :
    WP isa doubleFnRestore s fun t =>
      numAt t.mem (State.addr base) w o < numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o =
        (2 * numAt s.mem (State.addr base) w b) % numAt s.mem (State.addr base) w 0 ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t ∧ t.gpr .r0 = base := by
  have h := ready.1
  have body := doubleFnBody_ok s h.workspace h.layout ho ha hb h.ptr h.outIndex h.aIndex h.bIndex
    (by rw [h.width]; exact ready.2) (by rw [h.width]; exact h.inverse) (by rw [h.width]; exact h.operand)
  simp only [h.width] at body
  rw [doubleFnRestore, WP.seq_iff]
  refine WP.mono body ?_
  rintro u ⟨bound, value, keeps, frame, rest⟩
  have savedU := saved_base_kept frame sep saved rest.sp
  have readU : InRegions (u.rd ++ u.wr) (State.addr u.sp) 4 := by
    rw [rest.rd, rest.wr, rest.sp]; exact read
  refine WP.mono (restoreBase_ok u readU savedU) ?_
  rintro t ⟨ptr, mem, keep⟩
  rw [← mem] at bound value keeps frame
  exact ⟨bound, value, keeps, frame, rest.trans (keep.mono (by decide)), ptr⟩

theorem doubleFnRestore_ct {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b)
    (fit : arrAt w 3 + 32 ≤ 8 * len) (hn : 0 < 2 * w) :
    RelCT isa (fun s t => DoubleFnReady base len w o a b s ∧
      DoubleFnReady base len w o a b t ∧ s.sp = t.sp) doubleFnRestore (fun _ _ => True) := by
  have body := relCT_keep_sp
    ((doubleFnBody_ct ho ha hb fit hn).mono
      (P' := fun (s t : State) => DoubleFnReady base len w o a b s ∧
        DoubleFnReady base len w o a b t ∧ s.sp = t.sp)
      (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)) (fun _ _ h => h.2.2)
  exact (body.seq (loadStack_ct .r0 0)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm
