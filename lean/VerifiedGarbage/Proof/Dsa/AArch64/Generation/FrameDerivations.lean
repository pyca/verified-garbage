module
public import VerifiedGarbage.Impl.Bignum.AArch64.Core
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FrameDerived
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.Layout

/-! # Derive several arena pointers from the preserved scratch base -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64


def derivedWords (slots : List (Nat × Nat)) (B : Addr) (W : Nat → BitVec 64) : Nat → BitVec 64 :=
  slots.foldl (fun words slot => upd words slot.1 (VG.Proof.Bignum.off B slot.2)) W

theorem frameDerivations_ok (slots : List (Nat × Nat))
    (bounds : ∀ slot ∈ slots, slot.1 < nW ∧ slot.1 ≠ 5 ∧ slot.2 < 65536)
    {s : State} {F S B : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.sp = F)
    (hfr : Covers [⟨F, frameBytes⟩] s.wr) (hbase : W 5 = B) :
    WP isa (.block (slots.flatMap fun slot => [.ldrSp .x3 40, VG.Impl.Bignum.AArch64.movi .x4 slot.2,
      .add .x .x3 .x3 .x4, .strSp .x3 (8 * slot.1)])) s fun t =>
      Rep t.mem F S V (derivedWords slots B W) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  induction slots generalizing s W with
  | nil => exact WP.block_nil ⟨R, Frame.refl _ _, Keep.refl _ _⟩
  | cons slot slots ih =>
    change WP isa (.block (_ ++ _)) s _
    apply WP.block_append
    have bound := bounds slot (by simp)
    refine WP.mono (frameDerived_ok G R hsp hfr hbase bound.1 bound.2.2) fun u ⟨Ru, fu, ku⟩ => ?_
    refine WP.mono (ih (fun x hx => bounds x (by simp [hx])) Ru
      (ku.sp.trans hsp) (by rw [ku.wr]; exact hfr)
      (by simpa [upd, Ne.symm bound.2.1] using hbase)) fun t ⟨Rt, ft, kt⟩ => ?_
    exact ⟨Rt, fu.trans ft, (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.Generation
