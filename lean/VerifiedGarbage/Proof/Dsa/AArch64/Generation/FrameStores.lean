module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FrameStore

/-! # Save a list of argument registers into the persistent frame -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64


def registerWords (slots : List (Nat × Reg)) (regs : Reg → BitVec 64) (W : Nat → BitVec 64) : Nat → BitVec 64 :=
  slots.foldl (fun words slot => upd words slot.1 (regs slot.2)) W

theorem frameStores_ok (slots : List (Nat × Reg)) (bounds : ∀ slot ∈ slots, slot.1 < nW)
    {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.sp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr) :
    WP isa (.block (slots.map fun slot => .strSp slot.2 (8 * slot.1))) s fun t =>
      Rep t.mem F S V (registerWords slots s.gpr W) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [] s t := by
  induction slots generalizing s W with
  | nil => exact WP.block_nil ⟨R, Frame.refl _ _, Keep.refl _ _⟩
  | cons slot slots ih =>
    change WP isa (.block ([_] ++ _)) s _
    apply WP.block_append
    refine WP.mono (frameStore_ok G R hsp hfr (bounds slot (by simp)) slot.2) fun u ⟨Ru, fu, ku⟩ => ?_
    have regs : u.gpr = s.gpr := funext fun r => ku.gpr r (by simp)
    refine WP.mono (ih (fun x hx => bounds x (by simp [hx])) Ru
      (ku.sp.trans hsp) (by rw [ku.wr]; exact hfr)) fun t ⟨Rt, ft, kt⟩ => ?_
    refine ⟨?_, fu.trans ft, (ku.trans kt).mono (by simp)⟩
    simpa only [registerWords, List.foldl_cons, regs] using Rt

end VG.Proof.Dsa.AArch64.Generation
