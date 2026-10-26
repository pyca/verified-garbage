module

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ValidateArgs
public import VerifiedGarbage.Proof.Dsa.AArch64.Parameters
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Validate
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
public import Mathlib.Algebra.Group.Nat.Defs

/-! # Reuse the complete verified domain checker inside parameter generation -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem validateCore_ok (M : Mont) {s : State} {F S : Addr}
    {V : Nat → Byte} {W : Nat → BitVec 64} (p : ParametersInput)
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (hbase : p.base = VG.Proof.Bignum.off (W 5) domainCheck)
    (hp : p.pLen < 2 ^ 16) (hq : p.qLen < 2 ^ 16)
    (hs : Scr s p.base Impl.Dsa.Layout.usedBytes)
    (src : Src s p.base Impl.Dsa.Layout.usedBytes (VG.Proof.Bignum.off (W 5) packed) p.params)
    (hF : (⟨F, frameBytes⟩ : Region).Disjoint ⟨p.base, Impl.Dsa.Layout.usedBytes⟩)
    (hS : (⟨S, oRsa⟩ : Region).Disjoint ⟨p.base, Impl.Dsa.Layout.usedBytes⟩) :
    WP isa (.seq (.block (Impl.Dsa.AArch64.Generation.validateArgs p.pLen p.qLen))
      (Impl.Dsa.AArch64.Generate.checkParameters M.mm)) s fun t =>
      t.gpr .x0 = BitVec.ofNat 64 (if Spec.Dsa.checkParametersBytes p.pLen p.qLen p.params then 1 else 0) ∧
      Lay t F S ∧ Rep t.mem F S V W ∧
      Frame [⟨p.base, Impl.Dsa.Layout.usedBytes⟩] s.mem t.mem ∧ Keep coreRegs s t := by
  refine WP.seq (WP.mono (validateArgs_ok L R hp hq) fun u ⟨hdi, h8, hdx, hcx, hm, ku⟩ => ?_)
  have pre : ParametersPre p u := ⟨hs.congr ku.wr, h8.trans hbase.symm, hdx, hcx,
    hdi ▸ src.congrK (fun a _ => by rw [hm]) ku⟩
  refine WP.mono (parametersMain_ok M pre) fun t ⟨result, ft, kt⟩ => ?_
  have frame : Frame [⟨p.base, Impl.Dsa.Layout.usedBytes⟩] s.mem t.mem := by
    intro a ha
    have hn := ha ⟨p.base, Impl.Dsa.Layout.usedBytes⟩ (by simp)
    change ¬ ofs p.base a < Impl.Dsa.Layout.usedBytes at hn
    rw [ft a (by omega), hm]
  have Rt := rep_of_disjoint_frame R frame
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact hF)
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact hS)
  have keep := ku.trans kt
  exact ⟨result, lay_of_rep L R Rt rfl keep.sp keep.wr, Rt, frame, keep.mono (by decide)⟩

theorem validateTest_ok {s : State} {valid : Bool}
    (hr : s.gpr .x0 = BitVec.ofNat 64 (if valid then 1 else 0)) :
    eval (.zero .x .x0) s = some (!valid) := by
  cases valid <;> simp only [eval, State.read, hr, Size.bits, BitVec.setWidth_eq] <;> rfl

end VG.Proof.Dsa.AArch64.Generation
