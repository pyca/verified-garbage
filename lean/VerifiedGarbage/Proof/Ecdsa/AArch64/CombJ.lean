module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
public import VerifiedGarbage.Proof.Weierstrass.Booth
public import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombJ
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJ

/-!
# ECDSA on AArch64: the comb by Jacobian mixed additions

`combJ_correct`: for any curve the proof of the code supports, the comb with Booth digits and
Jacobian mixed additions (`TCombCfg.combJ`) gives what the signing's and the public key's stages
need of `[k]G` (`CombCorrect`), given the bound on Booth digits (`BoothOk`) for scalars below
`kmax`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64

open VG VG.AArch64 VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

theorem combJ_correct (hc : CfgOk c) (hC : Law c.C)
    (hT : CombOkW c.C Cfg.combW (Cfg.combJ c.n) c.tbl c.start) (hJ : c.combCfg.J < 4096)
    (hb : 1 ≤ c.combCfg.bits) {kmax : Nat} (hB : BoothOk c.C c.combCfg.w c.combCfg.J kmax)
    (hk : 2 ^ c.combCfg.kbytes ≤ kmax) :
    CombCorrect c c.combCfg.combJ := by
  intro base k T s hs hm hf
  exact WP.mono (tcombJWith_ok (tcombLay hc.toBaseCfgOk) (combA hc.toBaseCfgOk) (fprogB_correct _) hJ hC
    hc.am3 hc.onG
    (tcombVals hc.toBaseCfgOk hC hT) hc.p_lt hb hB (Nat.lt_of_lt_of_le hf.k_lt hk) hs hm hf)
    fun _ ⟨K, U, M, L, R⟩ => ⟨K, U.mono fun w hw => List.mem_append_left _ hw, M, L, R⟩

end VG.Proof.Ecdsa.AArch64
