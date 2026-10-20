module
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.FrameStore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Impl.Sha256.X86_64

/-! # Save a list of argument registers into the persistent frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

def registerWords (slots : List (Nat × Reg)) (regs : Reg → BitVec 64) (W : Nat → BitVec 64) : Nat → BitVec 64 :=
  slots.foldl (fun words slot => upd words slot.1 (regs slot.2)) W

theorem frameStores_ok (slots : List (Nat × Reg)) (bounds : ∀ slot ∈ slots, slot.1 < nW)
    {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.gpr .rsp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr) :
    WP isa (.block (slots.map fun slot => .store (sp (8 * slot.1)) slot.2)) s fun t =>
      Rep t.mem F S V (registerWords slots s.gpr W) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [] s t := by
  induction slots generalizing s W with
  | nil => exact WP.block_nil ⟨R, Frame.refl _ _, Keep.refl _ _⟩
  | cons slot slots ih =>
    change WP isa (.block ([_] ++ _)) s _
    apply WP.block_append
    refine WP.mono (frameStore_ok G R hsp hfr (bounds slot (by simp)) slot.2) fun u ⟨Ru, fu, ku⟩ => ?_
    have regs : u.gpr = s.gpr := funext fun r => ku.gpr (by simp)
    refine WP.mono (ih (fun x hx => bounds x (by simp [hx])) Ru
      ((ku.gpr (by simp)).trans hsp) (by rw [ku.2.2]; exact hfr)) fun t ⟨Rt, ft, kt⟩ => ?_
    refine ⟨?_, fu.trans ft, (ku.trans kt).mono (by simp)⟩
    simpa only [registerWords, List.foldl_cons, regs] using Rt

end VG.Proof.Dsa.X86_64.Generation
