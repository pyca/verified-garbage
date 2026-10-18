module

public import VerifiedGarbage.Proof.Rsa.X86.CvPair

/-! # Selecting and exporting a CRT value does not reveal its acceptance mask -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86 VG.Proof.Dsa.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Rsa.X86.CrtValues
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Proof.Rsa.X86.Keys

theorem select_relCT (g : CallGeometry) (j : Nat) (hj : j < nArr) :
    RelCT isa (fun s t => Pair g s t ∧ slot s.mem g.base sMask ≤ 1 ∧ slot t.mem g.base sMask ≤ 1)
      (sel (2 * g.n) j aZero j sMask) (Pair g) := by
  have trace : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (sel (2 * g.n) j aZero j sMask) (VG.X86.Taint.Agree (workspaceTaint false)) := by
    apply erased_relCT (τ := workspaceTaint false) (σ := workspaceTaint false) (sel (2 * g.n) j aZero j sMask) (sel 1 0 1 0 100)
      (VG.Taint.hintOf taint (workspaceTaint false) (sel 1 0 1 0 100)) (by rfl) (by rfl) (by decide +kernel)
    rfl
  intro s t tr ur sf tf ⟨h, bs, bt⟩ es et
  have eq := (trace _ _ _ _ _ _ h.workspace es et).1
  obtain ⟨_, fs, _, ks⟩ := wp_result (sel_ok h.left.ws hj (by decide) hj (by decide) bs) es
  obtain ⟨_, ft, _, kt⟩ := wp_result (sel_ok h.right.ws hj (by decide) hj (by decide) bt) et
  have os := h.left.keepOutside fs (by simp_all) (by simp)
  have ot := h.right.keepOutside ft (by simp_all) (by simp)
  have hs := h.left.after ks (by decide) (by decide) (h.left.scratchFrame os)
  have ht := h.right.after kt (by decide) (by decide) (h.right.scratchFrame ot)
  exact ⟨eq, h.after hs ht ks kt (by decide)⟩

theorem export_relCT (g : CallGeometry) (i : Fin 3) (j : Nat) :
    RelCT isa (Pair g)
      (.seq (.block [.mov .ebx (.mem (VG.Impl.Bignum.X86.PublicFn.argument (2 * i.val))),
        .mov .ecx (.mem (VG.Impl.Bignum.X86.PublicFn.argument (2 * i.val + 1)))])
        (VG.Impl.Bignum.X86.storeBE (VG.Impl.Rsa.X86.Keys.slot (2 * g.n) j)))
      (fun _ _ => True) := by
  apply (VG.RelCT.seq (storeArguments_relCT (2 * i.val) (2 * i.val + 1)
    (g.args (2 * i.val)) (g.args (2 * i.val + 1)))
    (storeBE_relCT (VG.Impl.Rsa.X86.Keys.slot (2 * g.n) j))).mono
  · intro s t h
    exact ⟨h.agree, (h.left.arguments _ (by omega)).readSrc, (h.right.arguments _ (by omega)).readSrc,
      (h.left.arguments _ (by omega)).readSrc, (h.right.arguments _ (by omega)).readSrc⟩
  · intro _ _ _; trivial

theorem store_trace (g : CallGeometry) (i : Fin 3) (j : Nat) (hj : j < nArr) :
    RelCT isa (fun s t => Pair g s t ∧ slot s.mem g.base sMask ≤ 1 ∧ slot t.mem g.base sMask ≤ 1)
      (store g.n (2 * i.val) j) (fun _ _ => True) :=
  VG.RelCT.seq (select_relCT g j hj) (export_relCT g i j)

end VG.Proof.Rsa.X86.CrtValues
