module

public import VerifiedGarbage.Impl.Ecdsa.X86_64
public import VerifiedGarbage.Impl.P521.CombTable7

/-! # ECDSA over P-521 on x86-64: nine-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86_64

open VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass

/-- P-521 as the code has it. `[k]G` for the signature and the public key is
a call of `vg_p521_mul_base` (`Cfg.mulBase`), which calls the products, and
`Z^(p-2)` and `k^(n-2)` are calls of `vg_p521_inv_mod_p` and `_n`
(`Cfg.inverse`). -/
def p521 : Cfg where
  n := 9
  C := Spec.P521.curve
  comb := some ⟨7, Impl.P521.p521Comb7, Impl.P521.p521Comb7Start, "VG_P521_COMB", false, false⟩
  fastN := true
  pubVerify := true
  nbits := 521
  mulBase := some Impl.Weierstrass.MulBase.p521
  inverse := some Impl.Weierstrass.Inverse.p521
  checkPoint := some Impl.Weierstrass.CheckPoint.p521

/-- `Cfg.middle` for nine words (`affineOn` is false), but its steps modulo `n`
(`r`, `k R`, and the checks), which do not depend on BMI2 and ADX, are a call
of `vg_ecdsa_p521_sign_r`. Inlined, it is `Cfg.middle`. -/
def Cfg.middleP521 (c : Cfg) : Prog isa :=
  progs [c.mulPF (c.sl XM) (c.sl RX) (c.sl ACC),
    c.mulPF (c.sl X) (c.sl XM) (c.sl ONE),
    .call "vg_ecdsa_p521_sign_r" (progs [
      .block (Mont.X86_64.add c.MN' (c.sl RR) (c.sl X) (c.sl ZERO)),
      opProg c.MN' (.mul (c.sl KM) (c.sl K) (c.sl R2N)),
      .block (c.checkRange (c.sl D) ++ c.checkRange (c.sl K) ++ c.checkNonzero (c.sl RR))])]

/-- `Cfg.sign` for P-521, but its setup, its steps modulo `n` (`middleP521`)
and its last steps (`k^(n-2)` and `s`), which do not depend on BMI2 and ADX,
are calls of `vg_ecdsa_p521_sign_setup`, `_r` and `_scalar`, so that both
configurations share them. Inlined, it is `Cfg.sign`. -/
def Cfg.signP521With (c : Cfg) : Prog isa :=
  .seq (.call "vg_ecdsa_p521_sign_setup" (.block c.setup)) <|
  .seq c.kBits <|
  .seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) <|
  .seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) <|
  .seq c.gMulKC <|
  .seq c.pPow <|
  .seq c.middleP521 <|
  .call "vg_ecdsa_p521_sign_scalar" (.seq c.nPow c.scalar)

/-- `vg_ecdsa_p521_sign`. -/
def signP521 : Prog isa := p521.signP521With

/-- P-521 multiplying modulo `p` with BMI2 and ADX (`Mod.adx`), and selecting
the comb's entries with AVX2 (`TCombCfg.avx2`). -/
def p521x : Cfg := { p521 with adx := true, avx2 := true }

/-- `vg_ecdsa_p521_sign_adx`. -/
def signP521Adx : Prog isa := p521x.signP521With

end VG.Impl.Ecdsa.X86_64
