import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout

/-! A curve's facts hold with any `pubVerify`, which only verification reads
(its final check), so a verification config `{ c with pubVerify := true }`
has those of the signing config `c`. -/
namespace VG.Proof.Ecdsa.Verify.X86_64
open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64

/-- `pubVerify` is none of `CfgOk`'s business. -/
theorem cfgOk_pubVerify {c : Cfg} (h : CfgOk c) (b : Bool) : CfgOk { c with pubVerify := b } :=
  { h with comb := fun d hd => ⟨(h.comb d hd).w,(h.comb d hd).cover,(h.comb d hd).w9⟩ }

end VG.Proof.Ecdsa.Verify.X86_64
