module

public import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout

/-! A curve's facts hold with any `pubVerify`, which only verification reads
(its final check), so a verification config `{ c with pubVerify := true }`
has those of the signing config `c`. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64

/-- `pubVerify` is none of `CfgOk`'s business. -/
theorem cfgOk_pubVerify {c : Cfg} (h : CfgOk c) (b : Bool) : CfgOk { c with pubVerify := b } :=
  { h with comb := fun d hd => ⟨(h.comb d hd).w,(h.comb d hd).cover,(h.comb d hd).w9⟩ }

/-- A curve's facts hold without its comb, with a table for verification's
generator digits (`Cfg.gtab`) in its place: no fact reads the latter. -/
theorem cfgOk_gtab {c : Cfg} (h : CfgOk c) (g : Option CombData) :
    CfgOk { c with comb := none, gtab := g } :=
  { h with comb := fun _ hd => (by cases hd), comb_am3 := fun _ hd => (by cases hd) }

/-- `cfgOk_pubVerify` and `cfgOk_gtab` for a curve without a comb, of the
facts that do not need `a = -3` (`BaseCfgOk`). -/
theorem baseCfgOk_pubVerify_gtab {c : Cfg} (h : BaseCfgOk c) (hc : c.comb = none) (b : Bool)
    (g : Option CombData) : BaseCfgOk { c with pubVerify := b, gtab := g } :=
  { h with comb := fun d hd => absurd (hc.symm.trans hd) (by simp) }

end VG.Proof.Ecdsa.Verify.X86_64
