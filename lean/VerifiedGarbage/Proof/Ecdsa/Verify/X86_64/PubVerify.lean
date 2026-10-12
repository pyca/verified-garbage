import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout

/-! A curve's facts hold with any `pubVerify`, which only verification reads
(its final check), so a verification config `{ c with pubVerify := true }`
has those of the signing config `c`. -/
namespace VG.Proof.Ecdsa.Verify.X86_64
open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64

/-- `pubVerify` is none of `CfgOk`'s business. -/
theorem cfgOk_pubVerify {c : Cfg} (h : CfgOk c) (b : Bool) : CfgOk { c with pubVerify := b } :=
  { h with comb := fun d hd => ⟨(h.comb d hd).w,(h.comb d hd).cover,(h.comb d hd).w9⟩ }

/-- `CfgOk` with `nCalls` set, if the modulus `n` is then one a function
computes (`MN'`'s `fnN`). -/
theorem cfgOk_nCalls {c : Cfg} (h : CfgOk c) (b : Bool) (hn : { c with nCalls := b }.MN'.ok c.C.n = true) :
    CfgOk { c with nCalls := b } :=
  { h with
    red_n := hn
    comb := fun d hd => ⟨(h.comb d hd).w,(h.comb d hd).cover,(h.comb d hd).w9⟩
    inv_n := fun hf h9 => ⟨(h.inv_n hf h9).1, ⟨(h.inv_n hf h9).2.B1, (h.inv_n hf h9).2.B16, (h.inv_n hf h9).2.C,
      (h.inv_n hf h9).2.Cpos, (h.inv_n hf h9).2.Cn, (h.inv_n hf h9).2.bound⟩⟩ }

end VG.Proof.Ecdsa.Verify.X86_64
