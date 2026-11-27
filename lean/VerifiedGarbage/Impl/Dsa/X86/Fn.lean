module

public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.Dsa.X86.CombKey
public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Impl.Dsa.X86.PrevalidatedSign
public import VerifiedGarbage.Impl.Dsa.X86.RandomSign
public import VerifiedGarbage.Impl.Dsa.X86.Prevalidated
public import VerifiedGarbage.Impl.Dsa.X86.Generation

/-! # DSA's functions on x86 (32-bit), as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrub rb`, or
`Impl.Scrub.X86.scrubAll rb W` for one with frames or calls: the `W` bytes of
stack below `esp` that it and its callees use zeroed), the registers a
callee may change cleared but the `rb` bits of the result, so that it
returns without secret residue. -/

@[expose] public section

namespace VG.Impl.Dsa.X86.Fn

open VG.X86

/-- `vg_dsa_generate_key`, as emitted. -/
def generateKey : Prog isa := Impl.Scrub.X86.scrubAll 32 232 Comb.generateKey

/-- `vg_dsa_derive_key`, as emitted. -/
def deriveKey : Prog isa := Impl.Scrub.X86.scrubAll 32 108 Generate.deriveKey

/-- `vg_dsa_validate_private_key`, as emitted. -/
def validatePrivateKey : Prog isa := Impl.Scrub.X86.scrubAll 32 108 PrevalidatedSign.validate

/-- `vg_dsa_sign_random_prevalidated`, calling the signer for a validated
private key, `vg_dsa_sign_prevalidated`, as emitted. -/
def randomSignPrevalidated : Prog isa :=
  Impl.Scrub.X86.scrubAll 32 232 (RandomSign.code "vg_dsa_sign_prevalidated" PrevalidatedSign.sign)

/-- `vg_dsa_validate_public_key`, as emitted. -/
def validatePublicKey : Prog isa := Impl.Scrub.X86.scrubAll 32 108 Prevalidated.validate

/-- `vg_dsa_verify_prevalidated`, as emitted. -/
def verifyPrevalidated : Prog isa := Impl.Scrub.X86.scrubAll 32 108 Prevalidated.verify

/-- `vg_dsa_parameter_search_init`, which calls nothing and has no frame, as
emitted. -/
def parameterInit : Prog isa := Impl.Scrub.X86.scrub 32 Generation.init

/-- `vg_dsa_parameter_search`, with the geometries `g1` (1024/160), `g2`
(2048/256) and `g3` (3072/256), as emitted. -/
def parameterSearch (g1 g2 g3 : Generation.Geo) : Prog isa :=
  Impl.Scrub.X86.scrubAll 32 216 (Generation.code g1 g2 g3)

end VG.Impl.Dsa.X86.Fn
