module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FrameCopy
import VerifiedGarbage.Proof.Framework.Omega

/-! # Copy incoming argument words without modifying unread stack arguments -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64


def copiedWords (slots : List (Nat × Nat)) (values W : Nat → BitVec 64) : Nat → BitVec 64 :=
  slots.foldl (fun words slot => upd words slot.2 (values slot.1)) W

theorem copiedWords_congr (slots : List (Nat × Nat)) (values values' : Nat → BitVec 64)
    (he : ∀ x ∈ slots, values x.1 = values' x.1) (W : Nat → BitVec 64) :
    copiedWords slots values W = copiedWords slots values' W := by
  induction slots generalizing W with
  | nil => rfl
  | cons x xs ih =>
    change copiedWords xs values (upd W x.2 (values x.1)) = copiedWords xs values' (upd W x.2 (values' x.1))
    rw [he x (by simp)]
    exact ih (fun y hy => he y (by simp [hy])) _

theorem frame_input_word {F : Addr} {m m' : Mem} {src : Nat}
    (hf : Frame [⟨F, frameBytes⟩] m m') (hlo : frameBytes ≤ src) (hhi : src + 8 ≤ 2 ^ 64) :
    VG.Proof.Bignum.word m' F src = VG.Proof.Bignum.word m F src := by
  unfold VG.Proof.Bignum.word
  exact hf.readW (r := ⟨VG.Proof.Bignum.off F src, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    rcases List.mem_singleton.mp hr with rfl
    exact (Offset.base_disjoint F hlo hhi).symm) (by decide)

theorem frameCopies_ok (slots : List (Nat × Nat))
    (bounds : ∀ slot ∈ slots, slot.2 < nW ∧ frameBytes ≤ slot.1 ∧ slot.1 + 8 ≤ 2 ^ 64 ∧ slot.1 % 8 = 0 ∧ slot.1 < 32768)
    {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.sp = F)
    (hfr : Covers [⟨F, frameBytes⟩] s.wr)
    (hr : ∀ slot ∈ slots, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.off F slot.1) 8) :
    WP isa (.block (slots.flatMap fun slot => [.ldrSp .x3 slot.1, .strSp .x3 (8 * slot.2)])) s fun t =>
      Rep t.mem F S V (copiedWords slots (VG.Proof.Bignum.word s.mem F) W) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  induction slots generalizing s W with
  | nil => exact WP.block_nil ⟨R, Frame.refl _ _, Keep.refl _ _⟩
  | cons slot slots ih =>
    change WP isa (.block (_ ++ _)) s _
    apply WP.block_append
    refine WP.mono (frameCopy_ok G R hsp hfr (bounds slot (by simp)).1 (bounds slot (by simp)).2.2.2 (hr slot (by simp))) fun u ⟨Ru, fu, ku⟩ => ?_
    refine WP.mono (ih (fun x hx => bounds x (by simp [hx])) Ru
      (ku.sp.trans hsp) (by rw [ku.wr]; exact hfr)
      (fun x hx => by rw [ku.rd, ku.wr]; exact hr x (by simp [hx]))) fun t ⟨Rt, ft, kt⟩ => ?_
    refine ⟨?_, fu.trans ft, (ku.trans kt).mono (by decide)⟩
    have same : ∀ x ∈ slots, VG.Proof.Bignum.word u.mem F x.1 = VG.Proof.Bignum.word s.mem F x.1 := by
      intro x hx
      exact frame_input_word fu (bounds x (by simp [hx])).2.1 (bounds x (by simp [hx])).2.2.1
    have eq := copiedWords_congr slots (VG.Proof.Bignum.word u.mem F) (VG.Proof.Bignum.word s.mem F) same (upd W slot.2 (VG.Proof.Bignum.word s.mem F slot.1))
    rw [eq] at Rt
    exact Rt

end VG.Proof.Dsa.AArch64.Generation
