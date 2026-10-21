module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
public import VerifiedGarbage.Proof.Weierstrass.Booth
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJP2

/-!
# ECDSA on AArch64: the comb pipelined in two passes

`combJP2_correct`: for any curve the proof of the code supports, the comb
with Booth digits, Jacobian mixed additions in a straight line `mc` (of a
field compiler for its modulus), and each window's addition woven with the
next one's selection in two passes (`TCombCfg.combJP2`), gives what the
signing's and the public key's stages need of `[k]G` (`CombCorrect`), given
the bound on Booth digits (`BoothOk`) for scalars below `kmax` and the checks
on its code (`JPChecks2`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

theorem combJP2_correct (hc : CfgOk c) (hC : Law c.C)
    (hT : CombOkW c.C Cfg.combW (Cfg.combJ c.n) c.tbl c.start) {arithmetic : Mod → List FOp → Prog isa}
    {X : List Reg} (hcomp : FieldCompilerOn c.combCfg.M c.C X arithmetic size)
    (hX : ∀ r ∈ X, r ∈ tcombClob c.combCfg.M.n ∧ r ≠ .x19) (hJ : c.combCfg.J < 4096)
    (hb : 1 ≤ c.combCfg.bits) {kmax : Nat} (hB : BoothOk c.C c.combCfg.w c.combCfg.J kmax)
    (hk : 2 ^ c.combCfg.kbytes ≤ kmax) {mc : List Instr}
    (hblk : arithmetic c.combCfg.M (maddJ c.combCfg.S c.combCfg.A c.combCfg.E c.combCfg.D) = .block mc)
    (hck : JPChecks2 c.combCfg size mc) :
    CombCorrect c (c.combCfg.combJP2 arithmetic mc) := by
  intro base k T s hs hm hf
  exact WP.mono (tcombJP2_ok (tcombLay hc.toBaseCfgOk) (combA hc.toBaseCfgOk) hcomp hX hJ hC
    hc.am3 hc.onG (tcombVals hc.toBaseCfgOk hC hT) hc.p_lt hb hB (Nat.lt_of_lt_of_le hf.k_lt hk) hblk hck
    hs hm hf)
    fun _ ⟨K, U, M, L, R⟩ => ⟨K, U.mono fun w hw => List.mem_append_left _ hw, M, L, R⟩

end VG.Proof.Ecdsa.AArch64
