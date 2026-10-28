module

public import VerifiedGarbage.Proof.RsaPss.AArch64.SignPre
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS on AArch64: the epilogue

The restores and the frame's release, for any of the functions with the
frame of `frameBytes` bytes at `fb s` (`restore_frame_ok`): the caller's
registers are back, and `x0` and memory are kept.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp)
open VG.Proof.RsaPss.AArch64.Sgn (fb saved_offs saved_ho)

theorem preserved_saved : ∀ r ∈ preserved, r ∈ saved.map Prod.fst := by decide

theorem restore_frame_ok {s w : State} (hsp : w.sp = fb s) (hwr : w.wr = ⟨fb s, frameBytes⟩ :: s.wr)
    (hv : ∀ r ∈ preservedV, (w.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64)
    (hsv : Spill.Saved (fb s) s.gpr saved w.mem) :
    WP isa (.block restore) w fun w' =>
      abiPreserved s (freed frameBytes w') ∧ (freed frameBytes w').gpr .x0 = w.gpr .x0 ∧
        (freed frameBytes w').mem = w.mem := by
  unfold restore
  refine wp_addSp (by decide) fun w₁ o₁ e₁ => ?_
  rw [hsp, BitVec.add_zero] at e₁
  refine WP.mono (Spill.restore_wp (b := .x16) (l := saved) (B := fb s) e₁ saved_ho (by decide)
    (fun p hp' => by
      rw [o₁.rd, o₁.wr, hwr]
      exact InRegions_append_cons (xs := w.rd) |>.mpr (.inl (Offset.contains_base _
        (by have := saved_offs p hp'; unfold frameBytes; omega) (by have := saved_offs p hp'; omega))))
    (by rw [o₁.mem]; exact hsv)) fun w' hr => ⟨⟨fun r hr' => ?_, ?_, fun r hr' => ?_⟩, ?_, ?_⟩
  · simp only [freed]
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp (preserved_saved r hr')
    exact hr.gpr p hp'
  · simp only [freed]
    rw [hr.sp, o₁.sp, hsp, BitVec.sub_add_cancel]
  · simp only [freed]
    rw [hr.v, o₁.vcs r hr', hv r hr']
  · simp only [freed]
    rw [hr.other .x0 (by decide), o₁.get .x0]
  · simp only [freed]
    rw [hr.mem, o₁.mem]

end VG.Proof.RsaPss.AArch64
