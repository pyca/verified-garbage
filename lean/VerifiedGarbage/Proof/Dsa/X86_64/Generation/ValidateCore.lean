module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ValidateArgs
public import VerifiedGarbage.Proof.Dsa.X86_64.Parameters
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Framework.Omega

/-! # Reuse the complete verified domain checker inside parameter generation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem validateCore_ok (M : Mont) (Sq : MontS) {s : State} {F S : Addr}
    {V : Nat → Byte} {W : Nat → BitVec 64} (p : ParametersInput)
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (hbase : p.base = off (W 5) domainCheck)
    (hp : p.pLen < 2 ^ 32) (hq : p.qLen < 2 ^ 32)
    (hs : Scr s p.base Impl.Dsa.Layout.usedBytes)
    (src : Src s p.base Impl.Dsa.Layout.usedBytes (off (W 5) packed) p.params)
    (hF : (⟨F, frameBytes⟩ : Region).Disjoint ⟨p.base, Impl.Dsa.Layout.usedBytes⟩)
    (hS : (⟨S, oRsa⟩ : Region).Disjoint ⟨p.base, Impl.Dsa.Layout.usedBytes⟩) :
    WP isa (.seq (.block (Impl.Dsa.X86_64.Generation.validateArgs p.pLen p.qLen))
      (Impl.Dsa.X86_64.Generate.checkParameters Sq.mm M.mm)) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (if Spec.Dsa.checkParametersBytes p.pLen p.qLen p.params then 1 else 0) ∧
      Lay t F S ∧ Rep t.mem F S V W ∧
      Frame [⟨p.base, Impl.Dsa.Layout.usedBytes⟩] s.mem t.mem ∧ Keep coreRegs s t := by
  refine WP.seq (WP.mono (validateArgs_ok L R hp hq) fun u ⟨hdi, h8, hdx, hcx, hm, ku⟩ => ?_)
  have pre : ParametersPre p u := ⟨hs.congr ku.2.2, h8.trans hbase.symm, hdx, hcx,
    hdi ▸ src.congrK (fun a _ => by rw [hm]) ku⟩
  refine WP.mono (parametersMain_ok M Sq pre) fun t ⟨result, _, ft, kt⟩ => ?_
  have frame : Frame [⟨p.base, Impl.Dsa.Layout.usedBytes⟩] s.mem t.mem := by
    intro a ha
    have hn := ha ⟨p.base, Impl.Dsa.Layout.usedBytes⟩ (by simp)
    change ¬ ofs p.base a < Impl.Dsa.Layout.usedBytes at hn
    rw [ft a (by omega), hm]
  have Rt := rep_of_disjoint_frame R frame
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact hF)
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact hS)
  have keep := ku.trans kt
  exact ⟨result, lay_of_rep L R Rt rfl (keep.gpr (by decide)) keep.2.2, Rt, frame, keep.mono (by decide)⟩

theorem validateTest_ok {s : State} {valid : Bool}
    (hr : s.gpr .rax = BitVec.ofNat 64 (if valid then 1 else 0)) :
    WP isa (.block [.alu .test .rax (.reg .rax)]) s fun t =>
      t.zf = some (!valid) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (!valid) ∧ t.mem = s.mem) (by
    xrun [hr]
    cases valid <;> decide) rfl) fun t ⟨⟨hz, hm⟩, hk⟩ => ⟨hz, hm, hk⟩

end VG.Proof.Dsa.X86_64.Generation
