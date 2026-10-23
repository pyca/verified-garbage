module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.AArch64.Comb
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Config
import VerifiedGarbage.Proof.BrainpoolP256r1.Comb7
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombGeneral

/-! # brainpoolP256r1 signing: the general-curve comb computes [k]G -/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64.BrainpoolP256r1
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass

theorem cfg_ok (hI : InvSounds) : BaseCfgOk combCfg where
  n0 := (brainpoolp256r1_ok hI).n0
  n10 := (brainpoolp256r1_ok hI).n10
  onG := (brainpoolp256r1_ok hI).onG
  p_odd := (brainpoolp256r1_ok hI).p_odd
  n_odd := (brainpoolp256r1_ok hI).n_odd
  p_lt := (brainpoolp256r1_ok hI).p_lt
  n_lt := (brainpoolp256r1_ok hI).n_lt
  p_ge := (brainpoolp256r1_ok hI).p_ge
  n_ge := (brainpoolp256r1_ok hI).n_ge
  p_lt_2n := (brainpoolp256r1_ok hI).p_lt_2n
  minv_p := (brainpoolp256r1_ok hI).minv_p
  minv_n := (brainpoolp256r1_ok hI).minv_n
  red_p := (brainpoolp256r1_ok hI).red_p
  red_n := (brainpoolp256r1_ok hI).red_n
  n2 := (brainpoolp256r1_ok hI).n2
  len8 := (brainpoolp256r1_ok hI).len8
  len_lo := (brainpoolp256r1_ok hI).len_lo
  len_hi := (brainpoolp256r1_ok hI).len_hi
  sh := (brainpoolp256r1_ok hI).sh
  n4 := (brainpoolp256r1_ok hI).n4
  sound_p := (brainpoolp256r1_ok hI).sound_p
  inv_p := (brainpoolp256r1_ok hI).inv_p
  inv_n := (brainpoolp256r1_ok hI).inv_n
  chain_n := (brainpoolp256r1_ok hI).chain_n
  call_p := (brainpoolp256r1_ok hI).call_p
  call_n := (brainpoolp256r1_ok hI).call_n
  inv_at := (brainpoolp256r1_ok hI).inv_at
  inv_fn := (brainpoolp256r1_ok hI).inv_fn
  check_fn := (brainpoolp256r1_ok hI).check_fn
  padd := fun h => absurd rfl h

theorem correct (hC : Law Spec.BrainpoolP256r1.curve) (hI : InvSounds) :
    CombCorrect combCfg comb := by
  have hc := cfg_ok hI
  intro base k T s hs hm hf
  exact WP.mono (generalComb_ok (tcombLay hc) (combA hc) hC b3 (mont_lt hc _)
    (by
      show toM combCfg.C.p (2 ^ (64 * combCfg.n)) (combCfg.mont (3 * combCfg.C.b)) = _
      rw [toM_cmont hc]; rfl) hc.onG
    (tcombVals hc hC (Proof.BrainpoolP256r1.combOk7 hC)) hc.p_lt hs hm hf)
    fun s' ⟨K,U,M,L,R⟩ => ⟨K,U.mono fun w hw => List.mem_append_left _ hw,M,L,R⟩

end VG.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb
