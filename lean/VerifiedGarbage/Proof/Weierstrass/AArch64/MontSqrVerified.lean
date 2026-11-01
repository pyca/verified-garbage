module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontVerified
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontModuli
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontVerified
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontModuli
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# P-384's Montgomery square modulo `p`, as a function, on AArch64: verified

`vg_p384_sqr_mod_p` (`sqrFn384`) meets `sqrContract`: the proof against
`sqrA`, which it implies (`sqrFn384_ok`), constant time by `ct_zext` and taint
tracking (only the pointer and the offsets are public), and a state
satisfying it (`sat`).
-/

@[expose] public section

-- `p`, below `2^384`, is evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.Weierstrass.AArch64.Mont

open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.Mont Impl.Weierstrass.Mont
open VG.Proof.Mont

/-- `vg_<curve>_sqr_mod_<p|n>(ws = x0, o = w1, a = w2, b = w3)`. -/
def sqrA (M : Modulus) : Contract isa where
  pre s := aPre M s ∧ argNum M s .x2 < M.m
  post s s' :=
    numAt s'.mem (s.gpr .x0) ((s.gpr .x1).setWidth 32) M.k < M.m ∧
    numAt s'.mem (s.gpr .x0) ((s.gpr .x1).setWidth 32) M.k * M.R % M.m =
      argNum M s .x2 * argNum M s .x2 % M.m ∧
    Keeps M.k (s.gpr .x0) ((s.gpr .x1).setWidth 32) s.mem s'.mem
  pub := aPub

theorem p384p_m : p384p.m = p384 := by decide +kernel

theorem sqr_a (s : State) (hs : (sqrA p384p).pre s) :
    ∃ t s', Exec isa sqrFn384 s t s' ∧ abiPreserved s s' ∧ (sqrA p384p).post s s' := by
  have hm := p384p_m
  obtain ⟨t, s', he, A, K, ⟨V, C⟩, -, -, -, -⟩ := sqrFn384_ok (pre_of (M := p384p) (by decide) hs.1)
    (by rw [← hm]; rw [← numAt_eq]; exact hs.2)
  refine ⟨t, s', he, A, ?_, ?_, keeps_of_kept (k := 6) (by decide) K⟩
  · rw [numAt_eq, hm]; exact V
  · simp only [argNum, numAt_eq, hm, Modulus.R]; exact C

theorem p384p_sqr_ct : ConstantTime isa (sqrA p384p).pre (sqrA p384p).pub sqrFn384 := by
  exact ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem sqr_sat (M : Modulus) (hk : M.k ≤ 9) (hm : 0 < M.m) : (M.sqrContract AArch64.abi).pre sat :=
  Sig.contract_pre_of_check (by decide +kernel) (by
    sig_reduce [Sig.wfPre, sig, AArch64.abi, AArch64.argRegs, sat]
    exact ⟨by decide, mul_zero M hk hm _⟩)

theorem p384p_sqr_verified : Verified AArch64.target sqrFn384 (p384p.sqrContract AArch64.abi) :=
  Verified.of_correct sqr_a p384p_sqr_ct
    { pre := by sig_implies_pre [Modulus.sqrContract, sig, argNum, sqrA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      post := by sig_implies_post [Modulus.sqrContract, sig, argNum, sqrA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      pub := by sig_implies_pub [Modulus.sqrContract, sig, argNum, sqrA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      sat := ⟨sat, sqr_sat p384p (by decide) (m_pos_of_inv p384p_ok.inv)⟩ }

end VG.Proof.Weierstrass.AArch64.Mont
