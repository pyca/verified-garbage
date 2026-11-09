module

public import VerifiedGarbage.Spec.Rsa.Contract

/-!
# RSASSA-PSS: what its contracts share

**Trusted** (as every file in `Spec/`). The working space of signing
(`scratchWords`) and of verification (`publicScratchWords`), with their
`# Safety` items, the salt length verification expects
(`expectedSaltLen`), and the `# Safety` items of verification but for what
the signature gives (`verifySafety`), which the contracts of
`Spec/RsaPss/Table.lean` (and those of RSAES-OAEP) share.
-/

@[expose] public section

namespace VG.Spec.RsaPss

/-- The least working space, in `u64`s, for a modulus of `nLen` octets: the
RSA primitives' (`Rsa.scratchWords`), and 1024 more. -/
def scratchWords (nLen : Nat) : Nat := Rsa.scratchWords nLen + 1024

/-- The least working space, in `u64`s, of verification (and of OAEP
encryption) for a modulus of `nLen` octets: the public-key operation's
(`Rsa.publicScratchWords`), and the 1024 words the encoding and the hash
functions use. -/
def publicScratchWords (nLen : Nat) : Nat := Rsa.publicScratchWords nLen + 1024

/-- The `# Safety` items on the working space. -/
def scratchSafety : List String :=
  ["`scratch_len` must be at least `16 * n_len + 1056`.",
    "The contents of `scratch` on return are unspecified and may contain secrets; the caller \
      must destroy them after use."]

/-- The `# Safety` items on the working space of verification (and of OAEP
encryption). -/
def publicScratchSafety : List String :=
  ["`scratch_len` must be at least `8 * ⌈n_len / 8⌉ + 1072`.",
    "The contents of `scratch` on return are unspecified and may contain secrets; the caller \
      must destroy them after use."]

/-- The salt length verification expects, from the arguments `salt_len` and
`any_salt_len`: any if `any_salt_len` is not zero, otherwise `salt_len`. -/
def expectedSaltLen {w : Nat} (saltLen : BitVec w) (anySaltLen : BitVec 32) : Option Nat :=
  if anySaltLen = 0 then some saltLen.toNat else none

/-- The `# Safety` items of `verify` but for what the signature gives. -/
def verifySafety : List String :=
  ["`n_len` must be in 64..=1024.", "`sig_len` must be `n_len`.",
    "`e_len` must be in 1..=`n_len`."] ++ publicScratchSafety

end VG.Spec.RsaPss
