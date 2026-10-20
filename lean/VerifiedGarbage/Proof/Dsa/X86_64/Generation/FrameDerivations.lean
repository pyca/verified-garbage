module
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.FrameDerived
import VerifiedGarbage.Proof.Bignum.Layout

/-! # Derive several arena pointers from the preserved scratch base -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

def derivedWords (slots : List (Nat × Nat)) (B : Addr) (W : Nat → BitVec 64) : Nat → BitVec 64 :=
  slots.foldl (fun words slot => upd words slot.1 (off B slot.2)) W

theorem frameDerivations_ok (slots : List (Nat × Nat))
    (bounds : ∀ slot ∈ slots, slot.1 < nW ∧ slot.1 ≠ 5 ∧ slot.2 < 2 ^ 31)
    {s : State} {F S B : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.gpr .rsp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr) (hbase : W 5 = B) :
    WP isa (.block (slots.flatMap fun slot => [.mov .rax (.mem (sp 40)),
      .alu .add .rax (.imm (BitVec.ofNat 32 slot.2)), .store (sp (8 * slot.1)) .rax])) s fun t =>
      Rep t.mem F S V (derivedWords slots B W) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.rax] s t := by
  induction slots generalizing s W with
  | nil => exact WP.block_nil ⟨R, Frame.refl _ _, Keep.refl _ _⟩
  | cons slot slots ih =>
    change WP isa (.block (_ ++ _)) s _
    apply WP.block_append
    have bound := bounds slot (by simp)
    refine WP.mono (frameDerived_ok G R hsp hfr hbase bound.1 bound.2.2) fun u ⟨Ru, fu, ku⟩ => ?_
    refine WP.mono (ih (fun x hx => bounds x (by simp [hx])) Ru
      ((ku.gpr (by decide)).trans hsp) (by rw [ku.2.2]; exact hfr)
      (by simpa [upd, Ne.symm bound.2.1] using hbase)) fun t ⟨Rt, ft, kt⟩ => ?_
    exact ⟨Rt, fu.trans ft, (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation
