module

-- separate module: isolate the comb correctness proof from the signing wrapper and its literal checks

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.AArch64.Comb
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP512r1.Config
import VerifiedGarbage.Proof.BrainpoolP512r1.Comb7
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombGeneral

/-! # brainpoolP512r1 signing: the general-curve comb computes [k]G -/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.BrainpoolP512r1.Comb

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64.BrainpoolP512r1
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass

private theorem with_tables_ok (c : Cfg) (h : BaseCfgOk c)
    (tbl : List (List (Nat × Nat))) (start : Nat × Nat) (tsym : String) :
    BaseCfgOk { c with tbl := tbl, start := start, tsym := tsym } where
  n0 := h.n0
  n10 := h.n10
  onG := h.onG
  p_odd := h.p_odd
  n_odd := h.n_odd
  p_lt := h.p_lt
  n_lt := h.n_lt
  p_ge := h.p_ge
  n_ge := h.n_ge
  p_lt_2n := h.p_lt_2n
  minv_p := h.minv_p
  minv_n := h.minv_n
  red_p := h.red_p
  red_n := h.red_n
  n2 := h.n2
  len8 := h.len8
  len_lo := h.len_lo
  len_hi := h.len_hi
  sh := h.sh
  n4 := h.n4
  sound_p := h.sound_p
  inv_p := h.inv_p
  inv_n := h.inv_n
  chain_n := h.chain_n
  call_p := h.call_p
  call_n := h.call_n
  inv_at := h.inv_at
  inv_fn := h.inv_fn
  check_fn := h.check_fn
  padd := fun hn => ⟨(h.padd hn).n4, (h.padd hn).pres, (h.padd hn).vec, (h.padd hn).nf⟩

theorem cfg_ok (hI : InvSounds) : BaseCfgOk combCfg :=
  with_tables_ok brainpoolp512r1 (brainpoolp512r1_ok hI) _ _ _

private theorem correct_of (c : Cfg) (hc : BaseCfgOk c) (hC : Law c.C)
    (hT : CombOkW c.C Cfg.combW (Cfg.combJ c.n) c.tbl c.start) :
    CombCorrect c (c.combCfg.generalComb (c.mont (3 * c.C.b))) := by
  intro base k T s hs hm hf
  exact WP.mono (generalComb_ok (tcombLay hc) (combA hc) hC (c.mont (3 * c.C.b)) (mont_lt hc _)
    (by
      show toM c.C.p (2 ^ (64 * c.n)) (c.mont (3 * c.C.b)) = _
      rw [toM_cmont hc]) hc.onG
    (tcombVals hc hC hT) hc.p_lt hs hm hf)
    fun s' ⟨K,U,M,L,R⟩ => ⟨K,U.mono fun w hw => List.mem_append_left _ hw,M,L,R⟩

theorem correct (hC : Law Spec.BrainpoolP512r1.curve) (hI : InvSounds) :
    CombCorrect combCfg comb :=
  correct_of combCfg (cfg_ok hI) hC (Proof.BrainpoolP512r1.combOk7 hC)

end VG.Proof.Ecdsa.AArch64.BrainpoolP512r1.Comb
