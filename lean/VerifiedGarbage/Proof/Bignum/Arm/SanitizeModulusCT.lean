module

public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulus
public import VerifiedGarbage.Proof.Bignum.Arm.SmallConstLayoutCT
meta import VerifiedGarbage.Impl.Bignum.Arm.SanitizeModulus
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Factor sanitization conceals the validation bit and the original modulus -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (arrAt)

structure LayoutFrameReady (base : BitVec 32) (len w : Nat) (s : State) : Prop
    extends SelectArrayReady base len w s where
  stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4
  stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩
  saved : s.mem.readW (State.addr s.sp) 32 = base

theorem sanitizeModulus_ct {base : BitVec 32} {len w : Nat} :
    RelCT isa (fun s t => LayoutFrameReady base len w s ∧ LayoutFrameReady base len w t ∧ s.sp = t.sp)
      sanitizeModulus (fun _ _ => True) := by
  let P := LayoutFrameReady base len w
  let Q := SelectArrayReady base len w
  have init := (smallConstLayout_ct (base := base) (len := len) (w := w) (o := 7) 3
    (by decide) (by decide) (by decide)).mono
    (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.toSelectArrayReady, h.2.1.toSelectArrayReady, h.2.2⟩) (fun _ _ _ => trivial)
  have wp (s : State) (h : P s) : WP isa (smallConst 7 3) s Q := by
    refine WP.mono (smallConstLayout_ok s 3 h.workspace h.layout h.width h.ptr
      (by decide : 7 < 8) (by decide) (by decide) h.stackRead h.stackSep h.saved) ?_
    rintro t ⟨layout, width, _, _, _, rest, ptr⟩
    exact ⟨h.workspace.congr rest.wr, layout, width, ptr⟩
  have first := (relCT_keep_sp init (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  have load : RelCT isa (fun s t => Q s ∧ Q t ∧ s.sp = t.sp) (.block sanitizeBit) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.ptr.trans h.2.1.ptr.symm
  have loadWP (s : State) (h : Q s) : WP isa (.block sanitizeBit) s Q := by
    have fits := h.layout.2.2.1
    have size : 216 ≤ 8 * len := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at fits; omega
    refine WP.mono (sanitizeBit_ok s h.workspace size h.ptr) ?_
    rintro t ⟨_, mem, rest⟩
    exact ⟨h.workspace.congr rest.wr, by rw [mem]; exact h.layout,
      by rw [mem]; exact h.width, (rest.gpr .r0 (by simp)).trans h.ptr⟩
  have second := (relCT_keep_sp load (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨loadWP s h.1, loadWP t h.2.1⟩)
  have select := selectArray_ct (base := base) (len := len) (w := w)
    (by decide : 0 < 8) (by decide : 7 < 8) (by decide : 0 < 8)
  exact (first.mono (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩)).seq
    ((second.mono (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩)).seq select)

end VG.Proof.Bignum.Arm
