module

public import VerifiedGarbage.Spec.Dsa.ProbablePrime

/-!
# DSA's probable-prime test on PPC64LE

`vg_dsa_probable_prime_{bits}(ws = r3, ws_len = r4, rand = r5, rand_len = r6,
used = r7)`, for `bits` in 160, 256, 1024, 2048 and 3072. The candidate is
the `bits / 8` big-endian bytes at byte 0 of `ws`; from byte `keyOff`, `ws`
holds the Montgomery working space of RSA's functions (a header of 32 words,
then arrays of `w + 2` words, `Spec.Rsa.Mont.Layout`), as the shared
Miller–Rabin round takes it (`Spec.MillerRabin.compact`, whose arrays reach
27), with the prime search's state in its header (`Impl/MillerRabin/PPC64LE/
Search.lean`). That working space is the only part of `ws` the test changes.
-/

@[expose] public section

namespace VG.Impl.Dsa.PPC64LE.ProbablePrime

/-! ## Widths -/

/-- The bytes of the candidate. -/
def len (bits : Nat) : Nat := bits / 8

/-- The 64-bit words of the arithmetic: the candidate's, at least 4 (the
round's least width). -/
def words (bits : Nat) : Nat := max 4 ((bits + 63) / 64)

/-- The octets a witness draws: whole 64-bit words, as many as the candidate
has (`Spec.RsaKeyGen.witnessBytes`). -/
def draw (bits : Nat) : Nat := 8 * ((bits + 63) / 64)

/-- The uniform witnesses needed: DSA's `primeChecks`. -/
def checks (bits : Nat) : Nat := if bits ≤ 2048 then 64 else 128

/-- The working space's byte offset in `ws`, above every candidate. -/
def keyOff : Nat := 384

/-- The working space's bytes: the header's 32 words and the round's 28
arrays of `w + 2` words. -/
def keyBytes (bits : Nat) : Nat := 8 * 32 + 28 * 8 * (words bits + 2)

/-- The candidate at byte 0 of `ws`, and the working space the only bytes
the test changes. -/
def layout (bits : Nat) : Spec.Dsa.ProbablePrime.Layout where
  bits := bits
  candidate := 0
  scratch := [(keyOff, keyBytes bits)]
  size := keyOff + keyBytes bits

end VG.Impl.Dsa.PPC64LE.ProbablePrime
