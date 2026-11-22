module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Table
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.PPC64LE.Fn
public import VerifiedGarbage.Proof.HmacTable.PPC64LE.Vars
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P192.Verified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.BrainpoolP256r1
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.BrainpoolP320r1
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.BrainpoolP384r1
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.BrainpoolP512r1
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P192
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P224
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P256
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P384
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P521
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Secp256k1
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP256r1
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP320r1
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP384r1
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
public import VerifiedGarbage.Spec.Ecdsa.P192
public import VerifiedGarbage.Spec.Ecdsa.P224
public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.Spec.Ecdsa.P384
public import VerifiedGarbage.Spec.Ecdsa.P521
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP256r1.CombLit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP320r1.CombLit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP384r1.CombLit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP512r1.CombLit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P192.Lit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224.CombLit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P256CombLit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384.CombLit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P521.CombLit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Secp256k1.CombLit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Deterministic ECDSA on PPC64LE, without secret residue

For every curve, `vg_ecdsa_<curve>_sign` as emitted
(`Impl.Ecdsa.Rfc6979.PPC64LE.Fn.<curve>`), generic over the HMAC
implementations its table holds, which it calls indirectly: its code, then
`Impl.Scrub.PPC64LE.scrubAll` (`PPC64LE.Scrub.verifiedScrubbedAll`). It calls
indirectly only the functions of its table (`PPC64LE.Scrub.tablesCall`), and
returns with the volatile registers cleared and the 784 bytes of stack its
frames and its callees' use zeroed. Its postcondition reads the memory on return only within
`out` (`signOut`), as on RISC-V (`Proof/Ecdsa/Rfc6979/RISCV64/Scrub.lean`).
Each theorem takes the curve's group law (`Weierstrass.Law`), which its
registration file gives; the code does not depend on the law, and the side
condition of `verifiedScrubbedAll` is proved of the code written without it.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub
open VG.Proof.HmacTable.PPC64LE (HVar tables names vars fnsOf)
open VG.Proof.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.Weierstrass (Law)

/-! ## The postcondition -/

/-- The `n` bytes at `q` read the memory only within a region at `q` of at
least `n` bytes. -/
theorem bytesAt_of {m₁ m₂ : Mem} {q : Addr} {N n : Nat} (hn : n ≤ N)
    (h : ∀ a, Region.Contains ⟨q, N⟩ a 1 → m₁ a = m₂ a) :
    Spec.Sha3.bytesAt m₂ q n = Spec.Sha3.bytesAt m₁ q n := by
  simp only [Spec.Sha3.bytesAt]
  refine List.map_congr_left fun i hi => (h _ ?_).symm
  have hi := List.mem_range.mp hi
  simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  have := Nat.mod_le i (2 ^ 64)
  omega_using [hn, hi]

/-- The postcondition reads the memory on return only within `out`. -/
theorem signOut (T : Spec.Ecdsa.Rfc6979.TableInstance) (cs : List (String × List (BitVec 64)))
    (vs : List HVar) :
    PostOut (specK T cs vs) (T.signSig.retBits 64) :=
  postOut_of_local ((ScrubAbi.consts cs).tables _ _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [out, d, dg, dl, sc, hm], _ =>
      simp only [Spec.Ecdsa.Rfc6979.TableInstance.signSig, Sig.bufs, List.mem_cons,
        forall_eq_or_imp, Elem.size, Nat.mul_one] at hb
      have e := bytesAt_of (n := 2 * T.ecdsa.curve.len) (Nat.le_refl _) hb.1
      intro H F h1 h2
      have h' := h H F h1 h2
      revert h'
      split
      · exact fun h' => ⟨h'.1, e.trans h'.2⟩
      · exact fun h' => ⟨h'.1, e.trans h'.2⟩

/-! ## The functions -/

/-- `vg_ecdsa_p192_sign` as emitted (`Impl.Ecdsa.Rfc6979.PPC64LE.Fn.p192`), with the
HMAC implementations of `HmacTable.PPC64LE.vars`, meets its contract in constant
time and returns without secret residue. -/
theorem p192Sign_scrubbed (hL : Law Spec.P192.curve) (hv : OK vars) :
    VerifiedScrubbed PPC64LE.target (Impl.Ecdsa.Rfc6979.PPC64LE.Fn.p192 (fnsOf vars))
      (specK Spec.Ecdsa.Rfc6979.Curves.p192 [] vars) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdsa.Rfc6979.Curves.p192SignApi) {
      tables := [("hmac", tables vars)]
      code := signCodeT (p192R hL) Spec.Ecdsa.Rfc6979.Curves.p192.tries vars
      verified := p192T_verified hL vars hv }
    784 .all
    (signOut Spec.Ecdsa.Rfc6979.Curves.p192 [] vars)
    (by dsimp only [signCodeT, cfgT, p192R, p192Core, RfcCurve.Q]; lit_decide)

/-- `vg_ecdsa_p224_sign` as emitted (`Impl.Ecdsa.Rfc6979.PPC64LE.Fn.p224`), with the
HMAC implementations of `HmacTable.PPC64LE.vars`, meets its contract in constant
time and returns without secret residue. -/
theorem p224Sign_scrubbed (hL : Law Spec.P224.curve) (hv : OK vars ∧ "VG_P224_COMB" ∉ names vars) :
    VerifiedScrubbed PPC64LE.target (Impl.Ecdsa.Rfc6979.PPC64LE.Fn.p224 (fnsOf vars))
      (specK Spec.Ecdsa.Rfc6979.Curves.p224 Impl.Weierstrass.PPC64LE.p224CombConsts vars) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdsa.Rfc6979.Curves.p224SignApi) {
      tables := [("hmac", tables vars)]
      code := signCodeT (p224R hL) Spec.Ecdsa.Rfc6979.Curves.p224.tries vars
      verified := p224T_verified hL vars hv }
    784 .all
    (signOut Spec.Ecdsa.Rfc6979.Curves.p224 Impl.Weierstrass.PPC64LE.p224CombConsts vars)
    (by dsimp only [signCodeT, cfgT, p224R, p224Core, RfcCurve.Q]; lit_decide)

/-- `vg_ecdsa_p256_sign` as emitted (`Impl.Ecdsa.Rfc6979.PPC64LE.Fn.p256`), with the
HMAC implementations of `HmacTable.PPC64LE.vars`, meets its contract in constant
time and returns without secret residue. -/
theorem p256Sign_scrubbed (hL : Law Spec.P256.curve) (hv : OK vars ∧ "VG_P256_COMB" ∉ names vars) :
    VerifiedScrubbed PPC64LE.target (Impl.Ecdsa.Rfc6979.PPC64LE.Fn.p256 (fnsOf vars))
      (specK Spec.Ecdsa.Rfc6979.Curves.p256 Impl.Weierstrass.PPC64LE.p256CombConsts vars) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdsa.Rfc6979.Curves.p256SignApi) {
      tables := [("hmac", tables vars)]
      code := signCodeT (p256R hL) Spec.Ecdsa.Rfc6979.Curves.p256.tries vars
      verified := p256T_verified hL vars hv }
    784 .all
    (signOut Spec.Ecdsa.Rfc6979.Curves.p256 Impl.Weierstrass.PPC64LE.p256CombConsts vars)
    (by dsimp only [signCodeT, cfgT, p256R, p256Core, RfcCurve.Q]; lit_decide)

/-- `vg_ecdsa_p384_sign` as emitted (`Impl.Ecdsa.Rfc6979.PPC64LE.Fn.p384`), with the
HMAC implementations of `HmacTable.PPC64LE.vars`, meets its contract in constant
time and returns without secret residue. -/
theorem p384Sign_scrubbed (hL : Law Spec.P384.curve) (hv : OK vars ∧ "VG_P384_COMB" ∉ names vars) :
    VerifiedScrubbed PPC64LE.target (Impl.Ecdsa.Rfc6979.PPC64LE.Fn.p384 (fnsOf vars))
      (specK Spec.Ecdsa.Rfc6979.Curves.p384 Impl.Weierstrass.PPC64LE.p384CombConsts vars) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdsa.Rfc6979.Curves.p384SignApi) {
      tables := [("hmac", tables vars)]
      code := signCodeT (p384R hL) Spec.Ecdsa.Rfc6979.Curves.p384.tries vars
      verified := p384T_verified hL vars hv }
    784 .all
    (signOut Spec.Ecdsa.Rfc6979.Curves.p384 Impl.Weierstrass.PPC64LE.p384CombConsts vars)
    (by dsimp only [signCodeT, cfgT, p384R, p384Core, RfcCurve.Q]; lit_decide)

/-- `vg_ecdsa_p521_sign` as emitted (`Impl.Ecdsa.Rfc6979.PPC64LE.Fn.p521`), with the
HMAC implementations of `HmacTable.PPC64LE.vars`, meets its contract in constant
time and returns without secret residue. -/
theorem p521Sign_scrubbed (hL : Law Spec.P521.curve) (hv : OK vars ∧ "VG_P521_COMB" ∉ names vars) :
    VerifiedScrubbed PPC64LE.target (Impl.Ecdsa.Rfc6979.PPC64LE.Fn.p521 (fnsOf vars))
      (specK Spec.Ecdsa.Rfc6979.Curves.p521 Impl.Weierstrass.PPC64LE.p521CombConsts vars) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdsa.Rfc6979.Curves.p521SignApi) {
      tables := [("hmac", tables vars)]
      code := signCodeT (p521R hL) Spec.Ecdsa.Rfc6979.Curves.p521.tries vars
      verified := p521T_verified hL vars hv }
    784 .all
    (signOut Spec.Ecdsa.Rfc6979.Curves.p521 Impl.Weierstrass.PPC64LE.p521CombConsts vars)
    (by dsimp only [signCodeT, cfgT, p521R, p521Core, RfcCurve.Q]; lit_decide)

/-- `vg_ecdsa_secp256k1_sign` as emitted (`Impl.Ecdsa.Rfc6979.PPC64LE.Fn.secp256k1`), with the
HMAC implementations of `HmacTable.PPC64LE.vars`, meets its contract in constant
time and returns without secret residue. -/
theorem secp256k1Sign_scrubbed (hL : Law Spec.Secp256k1.curve) (hv : OK vars ∧ "VG_SECP256K1_COMB" ∉ names vars) :
    VerifiedScrubbed PPC64LE.target (Impl.Ecdsa.Rfc6979.PPC64LE.Fn.secp256k1 (fnsOf vars))
      (specK Spec.Ecdsa.Rfc6979.Curves.secp256k1 Impl.Weierstrass.PPC64LE.secp256k1CombConsts vars) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdsa.Rfc6979.Curves.secp256k1SignApi) {
      tables := [("hmac", tables vars)]
      code := signCodeT (secp256k1R hL) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries vars
      verified := secp256k1T_verified hL vars hv }
    784 .all
    (signOut Spec.Ecdsa.Rfc6979.Curves.secp256k1 Impl.Weierstrass.PPC64LE.secp256k1CombConsts vars)
    (by dsimp only [signCodeT, cfgT, secp256k1R, secp256k1Core, RfcCurve.Q]; lit_decide)

/-- `vg_ecdsa_brainpoolp256r1_sign` as emitted (`Impl.Ecdsa.Rfc6979.PPC64LE.Fn.brainpoolp256r1`), with the
HMAC implementations of `HmacTable.PPC64LE.vars`, meets its contract in constant
time and returns without secret residue. -/
theorem brainpoolp256r1Sign_scrubbed (hL : Law Spec.BrainpoolP256r1.curve) (hv : OK vars ∧ "VG_BRAINPOOLP256R1_COMB" ∉ names vars) :
    VerifiedScrubbed PPC64LE.target (Impl.Ecdsa.Rfc6979.PPC64LE.Fn.brainpoolp256r1 (fnsOf vars))
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1 Impl.Weierstrass.PPC64LE.brainpoolp256r1CombConsts vars) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1SignApi) {
      tables := [("hmac", tables vars)]
      code := signCodeT (brainpoolp256r1R hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1.tries vars
      verified := brainpoolp256r1T_verified hL vars hv }
    784 .all
    (signOut Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1 Impl.Weierstrass.PPC64LE.brainpoolp256r1CombConsts vars)
    (by dsimp only [signCodeT, cfgT, brainpoolp256r1R, brainpoolp256r1Core, RfcCurve.Q]; lit_decide)

/-- `vg_ecdsa_brainpoolp320r1_sign` as emitted (`Impl.Ecdsa.Rfc6979.PPC64LE.Fn.brainpoolp320r1`), with the
HMAC implementations of `HmacTable.PPC64LE.vars`, meets its contract in constant
time and returns without secret residue. -/
theorem brainpoolp320r1Sign_scrubbed (hL : Law Spec.BrainpoolP320r1.curve) (hv : OK vars ∧ "VG_BRAINPOOLP320R1_COMB" ∉ names vars) :
    VerifiedScrubbed PPC64LE.target (Impl.Ecdsa.Rfc6979.PPC64LE.Fn.brainpoolp320r1 (fnsOf vars))
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1 Impl.Weierstrass.PPC64LE.brainpoolp320r1CombConsts vars) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1SignApi) {
      tables := [("hmac", tables vars)]
      code := signCodeT (brainpoolp320r1R hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1.tries vars
      verified := brainpoolp320r1T_verified hL vars hv }
    784 .all
    (signOut Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1 Impl.Weierstrass.PPC64LE.brainpoolp320r1CombConsts vars)
    (by dsimp only [signCodeT, cfgT, brainpoolp320r1R, brainpoolp320r1Core, RfcCurve.Q]; lit_decide)

/-- `vg_ecdsa_brainpoolp384r1_sign` as emitted (`Impl.Ecdsa.Rfc6979.PPC64LE.Fn.brainpoolp384r1`), with the
HMAC implementations of `HmacTable.PPC64LE.vars`, meets its contract in constant
time and returns without secret residue. -/
theorem brainpoolp384r1Sign_scrubbed (hL : Law Spec.BrainpoolP384r1.curve) (hv : OK vars ∧ "VG_BRAINPOOLP384R1_COMB" ∉ names vars) :
    VerifiedScrubbed PPC64LE.target (Impl.Ecdsa.Rfc6979.PPC64LE.Fn.brainpoolp384r1 (fnsOf vars))
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1 Impl.Weierstrass.PPC64LE.brainpoolp384r1CombConsts vars) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1SignApi) {
      tables := [("hmac", tables vars)]
      code := signCodeT (brainpoolp384r1R hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1.tries vars
      verified := brainpoolp384r1T_verified hL vars hv }
    784 .all
    (signOut Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1 Impl.Weierstrass.PPC64LE.brainpoolp384r1CombConsts vars)
    (by dsimp only [signCodeT, cfgT, brainpoolp384r1R, brainpoolp384r1Core, RfcCurve.Q]; lit_decide)

/-- `vg_ecdsa_brainpoolp512r1_sign` as emitted (`Impl.Ecdsa.Rfc6979.PPC64LE.Fn.brainpoolp512r1`), with the
HMAC implementations of `HmacTable.PPC64LE.vars`, meets its contract in constant
time and returns without secret residue. -/
theorem brainpoolp512r1Sign_scrubbed (hL : Law Spec.BrainpoolP512r1.curve) (hv : OK vars ∧ "VG_BRAINPOOLP512R1_COMB" ∉ names vars) :
    VerifiedScrubbed PPC64LE.target (Impl.Ecdsa.Rfc6979.PPC64LE.Fn.brainpoolp512r1 (fnsOf vars))
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1 Impl.Weierstrass.PPC64LE.brainpoolp512r1CombConsts vars) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1SignApi) {
      tables := [("hmac", tables vars)]
      code := signCodeT (brainpoolp512r1R hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries vars
      verified := brainpoolp512r1T_verified hL vars hv }
    784 .all
    (signOut Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1 Impl.Weierstrass.PPC64LE.brainpoolp512r1CombConsts vars)
    (by dsimp only [signCodeT, cfgT, brainpoolp512r1R, brainpoolp512r1Core, RfcCurve.Q]; lit_decide)

end VG.Proof.Ecdsa.Rfc6979.PPC64LE.Scrub
