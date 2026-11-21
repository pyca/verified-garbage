module

public import VerifiedGarbage.Impl.Dsa.PPC64LE.Derive
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Generate
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Generation
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Params
public import VerifiedGarbage.Impl.Dsa.PPC64LE.ProbablePrime
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Prevalidated
public import VerifiedGarbage.Impl.Dsa.PPC64LE.PrevalidatedSign
public import VerifiedGarbage.Impl.Dsa.PPC64LE.RandomSign
public import VerifiedGarbage.Impl.Scrub.PPC64LE

/-!
# Dsa on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/Dsa/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.Dsa.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)

/-- `vg_dsa_derive_key`, as emitted. -/
def deriveKey : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (Impl.Dsa.PPC64LE.Derive.derive)

/-- `vg_dsa_sign_random_prevalidated`, as emitted. -/
def randomSignPrevalidated : Prog isa :=
  scrubAll 32 304 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (Impl.Dsa.PPC64LE.RandomSign.code)

/-- `vg_dsa_generate_key`, as emitted. -/
def generateKey : Prog isa :=
  scrubAll 32 304 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (Impl.Dsa.PPC64LE.Generate.code)

/-- `vg_dsa_validate_public_key`, as emitted. -/
def validatePublicKey : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (Impl.Dsa.PPC64LE.Prevalidated.validate)

/-- `vg_dsa_validate_private_key`, as emitted. -/
def validatePrivateKey : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (Impl.Dsa.PPC64LE.PrevalidatedSign.validate)

/-- `vg_dsa_verify_prevalidated`, as emitted. -/
def verifyPrevalidated : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (Impl.Dsa.PPC64LE.Prevalidated.verify)

/-- The search's geometry for `(pLen, qLen)`, hashing with `G`, testing with
the Miller-Rabin round `round` (`vg_miller_rabin_round<suffix>`), checking
with `vg_dsa_check_parameters`. -/
def searchGeo (pLen qLen : Nat) (G : Impl.Dsa.PPC64LE.Generation.Hash) (suffix : String) (round : Prog isa) :
    Impl.Dsa.PPC64LE.Generation.Geo where
  pLen := pLen
  qLen := qLen
  G := G
  qCand := 0
  qName := s!"vg_dsa_probable_prime_{(Impl.Dsa.PPC64LE.ProbablePrime.layout (8 * qLen)).bits}" ++ suffix
  qCode := Impl.Dsa.PPC64LE.ProbablePrime.code (8 * qLen) ("vg_miller_rabin_round" ++ suffix) round
  pCand := 0
  pName := s!"vg_dsa_probable_prime_{(Impl.Dsa.PPC64LE.ProbablePrime.layout (8 * pLen)).bits}" ++ suffix
  pCode := Impl.Dsa.PPC64LE.ProbablePrime.code (8 * pLen) ("vg_miller_rabin_round" ++ suffix) round
  checkName := "vg_dsa_check_parameters"
  checkCode := Impl.Dsa.PPC64LE.Params.checkParameters

/-- `vg_dsa_parameter_search<suffix>`, as emitted, with the Miller-Rabin
round `round`: the search for (1024, 160), (2048, 224) and (2048, 256)
parameters, then the clearing of the 176 bytes of stack its frames use. -/
def parameterSearch (suffix : String) (round : Prog isa) : Prog isa :=
  scrubAll 32 176 .all
    (Impl.Dsa.PPC64LE.Generation.code
      (searchGeo 128 20 Impl.Dsa.PPC64LE.Generation.sha1 suffix round)
      (searchGeo 256 32 Impl.Dsa.PPC64LE.Generation.sha256 suffix round)
      (searchGeo 384 32 Impl.Dsa.PPC64LE.Generation.sha256 suffix round))

end VG.Impl.Dsa.PPC64LE.Fn
