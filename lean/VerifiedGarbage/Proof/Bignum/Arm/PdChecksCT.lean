module

public import VerifiedGarbage.Proof.Bignum.Arm.PdChecks
public import VerifiedGarbage.Proof.Bignum.Arm.PdOddCT
public import VerifiedGarbage.Proof.Bignum.Arm.ArrayCompareCT
public import VerifiedGarbage.Proof.Bignum.Arm.SmallConstLayoutCT
public import VerifiedGarbage.Proof.Bignum.Arm.SaveAcceptanceCT
public import VerifiedGarbage.Proof.Bignum.Arm.MergeAcceptanceCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Precomputation validation performs the same checks for every public key -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

theorem pdSmall_ready (s : State) {base : BitVec 32} {len w N R : Nat}
    (h : PdCheckState base len w N R s) : WP isa (smallConst 7 1) s (PdCheckState base len w N R) := by
  refine WP.mono (smallConstLayout_ok s 1 h.ready.workspace h.ready.layout h.ready.width h.ready.ptr
    (by decide : 7 < 8) (by decide) (by decide) h.ready.stackRead h.ready.stackSep h.ready.saved) ?_
  rintro t ⟨_, _, _, outside, frame, rest, ptr⟩
  have keeps := outside_array_keeps outside (len := len) (by have := h.ready.workspace.nowrap; omega)
  exact h.after_array (h.ready.after_array keeps frame rest ptr) rest keeps (by decide) (by decide)

theorem pdSave_ready (s : State) {base : BitVec 32} {len w N R : Nat}
    (h : PdCheckState base len w N R s) : WP isa (.block saveAcceptance) s (PdCheckState base len w N R) := by
  refine WP.mono (saveAcceptanceLayout_ready s h.ready h.stackFit h.write h.separate) ?_
  rintro t ⟨ready, _, eq, _, rest, _⟩
  exact h.after_flag ready rest eq

theorem pdCompare_ready (s : State) {base : BitVec 32} {len w N R a : Nat}
    (h : PdCheckState base len w N R s) (ha : a < 8) (ne : a ≠ 3) :
    WP isa (arrayCompare a 0) s (PdCheckState base len w N R) := by
  refine WP.mono (arrayCompare_ok s h.ready ha (by decide) ne (by decide)) ?_
  rintro t ⟨ready, _, keeps, _, rest⟩
  exact h.after_array ready rest keeps (by decide) (by decide)

theorem pdMerge_ready (s : State) {base : BitVec 32} {len w N R : Nat}
    (h : PdCheckState base len w N R s) : WP isa (.block mergeAcceptance) s (PdCheckState base len w N R) := by
  refine WP.mono (mergeAcceptanceLayout_ready s h.ready h.stackFit h.write h.separate) ?_
  rintro t ⟨ready, _, eq, _, rest, _⟩
  exact h.after_flag ready rest eq

theorem pdChecks_ct {base : BitVec 32} {len w N R : Nat} :
    RelCT isa (fun s t => PdCheckState base len w N R s ∧ PdCheckState base len w N R t ∧ s.sp = t.sp)
      pdChecks (fun _ _ => True) := by
  let P := PdCheckState base len w N R
  have small : RelCT isa (fun s t => P s ∧ P t ∧ s.sp = t.sp) (smallConst 7 1) (fun _ _ => True) :=
    (smallConstLayout_ct (base := base) (len := len) (w := w) (o := 7) 1 (by decide) (by decide) (by decide)).mono
      (fun _ _ h => ⟨h.1.ready.toSelectArrayReady, h.2.1.ready.toSelectArrayReady, h.2.2⟩) (fun _ _ h => h)
  have compare (a : Nat) (ha : a < 8) :
      RelCT isa (fun s t => P s ∧ P t ∧ s.sp = t.sp) (arrayCompare a 0) (fun _ _ => True) :=
    (arrayCompare_ct (base := base) (len := len) (w := w) ha (by decide : 0 < 8)).mono
      (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.2.2⟩) (fun _ _ h => h)
  have save : RelCT isa (fun s t => P s ∧ P t ∧ s.sp = t.sp) (.block saveAcceptance) (fun _ _ => True) :=
    saveAcceptance_ct.mono (fun _ _ h => h.2.2) (fun _ _ h => h)
  have merge : RelCT isa (fun s t => P s ∧ P t ∧ s.sp = t.sp) (.block mergeAcceptance) (fun _ _ => True) :=
    mergeAcceptance_ct.mono (fun _ _ h => h.2.2) (fun _ _ h => h)
  have odd : RelCT isa (fun s t => P s ∧ P t ∧ s.sp = t.sp) pdOdd (fun _ _ => True) :=
    pdOdd_ct.mono (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.2.2⟩) (fun _ _ h => h)
  exact crt_seq_ct small (fun s h => pdSmall_ready s h) (fun s h => pdSmall_ready s h)
    (crt_seq_ct (compare 7 (by decide)) (fun s h => pdCompare_ready s h (by decide) (by decide))
      (fun s h => pdCompare_ready s h (by decide) (by decide))
      (crt_seq_ct save (fun s h => pdSave_ready s h) (fun s h => pdSave_ready s h)
        (crt_seq_ct (compare 4 (by decide)) (fun s h => pdCompare_ready s h (by decide) (by decide))
          (fun s h => pdCompare_ready s h (by decide) (by decide))
          (crt_seq_ct merge (fun s h => pdMerge_ready s h) (fun s h => pdMerge_ready s h) odd))))

end VG.Proof.Bignum.Arm
