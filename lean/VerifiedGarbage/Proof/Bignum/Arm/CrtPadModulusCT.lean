module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtPadModulus
public import VerifiedGarbage.Proof.Bignum.Arm.CrtClearWideCT
public import VerifiedGarbage.Proof.Bignum.Arm.ExportArrayCT
public import VerifiedGarbage.Proof.Framework.Arm.TaintErase
meta import VerifiedGarbage.Impl.Bignum.Arm.CrtPadModulus
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Padding the modulus uses only public addresses and lengths -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_padModulus_ct {base : BitVec 32} {size len w d : Nat}
    (fit : 244 ≤ size) (operand : Fin 8 := 0) :
    RelCT isa (fun s t => CrtPadInput base size len w d s ∧
      CrtPadInput base size len w d t ∧ s.sp = t.sp) (padModulus operand) (fun _ _ => True) := by
  let P := CrtPadInput base size len w d
  let Q := fun s : State => SmallFnReady base len w operand.val s ∧ s.gpr .r4 = base + BitVec.ofNat 32 d
  have clear : RelCT isa (fun s t => P s ∧ P t ∧ s.sp = t.sp) (clearWide 240)
      (fun s t => P s ∧ P t) := by
    have ct : RelCT isa (fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp) (clearWide 240)
        (fun _ _ => True) := (crt_clearWide_ct (base := base) (dst := base + BitVec.ofNat 32 d)
      (size := size) (slot := 240) (w := w) (by omega) fit (by decide)).mono
      (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
      (fun _ _ h => ⟨⟨h.1.workspace, h.1.ptr, h.1.layout.nativeCount h.1.main, h.1.link⟩,
        ⟨h.2.1.workspace, h.2.1.ptr, h.2.1.layout.nativeCount h.2.1.main, h.2.1.link⟩, h.2.2⟩)
      (fun _ _ _ => trivial)
    exact (ct.wp (fun s t h => ⟨(crt_padClear_ready s h.1).mono (fun _ j => j.1),
      (crt_padClear_ready t h.2.1).mono (fun _ j => j.1)⟩)).mono
      (fun _ _ h => h) (fun _ _ h => h.2)
  have args : RelCT isa (fun s t => P s ∧ P t) (.block (padModulusArgs operand)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (hc := .block []) (by
      rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs [.r0])]
      rfl)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.ptr.trans h.2.ptr.symm
  have wp (s : State) (h : P s) : WP isa (.block (padModulusArgs operand)) s Q := by
    refine WP.mono (crt_padModulusArgs_ok s h.workspace fit h.ptr h.link operand) ?_
    rintro t ⟨out, index, mem, rest⟩
    exact ⟨⟨h.main.congr rest.wr, by rw [mem]; exact h.layout.layout,
      by rw [mem]; exact h.layout.width, (rest.gpr .r0 (by simp)).trans h.ptr, index⟩, out⟩
  have copy : RelCT isa (fun s t => Q s ∧ Q t) exportArray (fun _ _ => True) :=
    (exportArray_ct (base := base) (dst := base + BitVec.ofNat 32 d) (len := len) (w := w)
      operand.isLt).mono (fun _ _ h => ⟨h.1.1, h.2.1, h.1.2, h.2.2⟩) (fun _ _ h => h)
  exact clear.seq ((pair_posts args wp).seq copy)

end VG.Proof.Bignum.Arm
