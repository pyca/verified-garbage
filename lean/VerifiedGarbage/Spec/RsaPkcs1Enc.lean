module

public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Spec.Hmac

/-!
# RSAES-PKCS1-v1_5 with implicit rejection (RFC 8017 §7.2, draft-irtf-cfrg-rsa-guidance-10 §7)

**Trusted** (as every file in `Spec/`). The encryption scheme
RSAES-PKCS1-v1_5 of PKCS #1 v2.2 (RFC 8017 §7.2), whose decryption is done
with *implicit rejection*, transcribed from draft-irtf-cfrg-rsa-guidance-10,
*Implementation Guidance for the PKCS #1 RSA Cryptography Specification*
(11 September 2026), §7 ("the algorithm MUST be implemented as stated"):

* `encrypt`: RSAES-PKCS1-V1_5-ENCRYPT (RFC 8017 §7.2.1), with its padding
  string `PS` of nonzero random octets given as an input (the caller draws
  it), and the public-key operation within BoringSSL's limits on the public
  key, `Rsa.publicOpChecked` (RSAEP).
* `decrypt`: RSAES-PKCS1-V1_5-DECRYPT as the draft's §7.2 implements it,
  with the private-key operation checked against `e`, `Rsa.privateChecked`
  (RSADP; `decryptWith` for any private-key operation): it gives an error
  only if the ciphertext is not `k` octets long or the private-key operation
  gives one (`invalid` for an input not below `n` or a key it refuses, or the
  internal error `fault`). When the padding of the encoded message `EM` is
  not valid, it returns, rather than an error, a message derived from the
  private exponent `d` and the ciphertext (`implicitDecode`): the last `AL`
  octets of `AM`, both derived with the draft's PRF `irprf` (§7.1) from a key
  `kdk` (§7.2 step 3.1).

The private exponent `d` keys the derivation: it is used as given with the
key, and never recomputed from the other values of a private key (step
3.1.a's note), so that every implementation holding the same key returns
the same message for the same invalid ciphertext.

Octet strings are lists of bytes; integers are converted from and to them by
`Rsa.os2ip` and `Rsa.i2osp`, most significant octet first.
-/

@[expose] public section

namespace VG.Spec.RsaPkcs1Enc

open Rsa (os2ip i2osp)

/-- The last `n` octets of `xs` (all of them if it has fewer). -/
def lastN (n : Nat) (xs : List Byte) : List Byte := xs.drop (xs.length - n)

/-- A string of ASCII characters as octets (the draft's labels, UTF-8). -/
def ascii (s : String) : List Byte := s.toList.map fun c => BitVec.ofNat 8 c.toNat

/-! ## Encryption (RFC 8017 §7.2.1) -/

/-- EME-PKCS1-v1_5 encoding (§7.2.1 step 2.b): `EM = 0x00 ‖ 0x02 ‖ PS ‖ 0x00 ‖ M`. -/
def encode (M PS : List Byte) : List Byte := [0x00, 0x02] ++ PS ++ [0x00] ++ M

/-- RSAES-PKCS1-V1_5-ENCRYPT ((n, e), M) (§7.2.1), with the public key
`(nB, eB)` (`k = nB.length` octets of `n`) and the padding string `PS`:

1. Length checking: an error ("message too long") if `mLen > k - 11`.
2. EME-PKCS1-v1_5 encoding: `PS` is `k - mLen - 3` pseudo-randomly
   generated nonzero octets, here given by the caller: an error if it has
   another length or a zero octet. `EM = 0x00 ‖ 0x02 ‖ PS ‖ 0x00 ‖ M`.
3. RSA encryption: `C = I2OSP(RSAEP((n, e), OS2IP(EM)), k)`, which is
   `Rsa.publicOpChecked` (an error if the modulus or the exponent is not one
   it takes).
-/
def encrypt (nB eB M PS : List Byte) : Option (List Byte) :=
  let k := nB.length
  if M.length + 11 ≤ k ∧ PS.length = k - M.length - 3 ∧ PS.all (· != 0) then
    Rsa.publicOpChecked nB eB (encode M PS)
  else none

/-! ## The implicit-rejection PRF (draft §7.1) -/

/-- IRPRF (KDK, label, length) (§7.1): the `length` left-most octets of the
concatenation of `HMAC-SHA256(KDK, P_i)` for `i = 0, 1, …`, as many as make
it at least `length` octets long (steps 2–5), with
`P_i = I ‖ label ‖ bitLength`, the iterator `I = i` and
`bitLength = 8 · length` each as a two-octet big-endian integer.

Step 1 gives an error if `KDK` is not 32 octets or `length` is more than
8192. Here `KDK` is always an HMAC-SHA-256 output (32 octets, `kdk`) and
`length` is 256 or `k ≤ 1024` (the modulus is at most 8192 bits,
`Rsa.modulusValid`), so the error never occurs and is left out. -/
def irprf (kdk label : List Byte) (length : Nat) : List Byte :=
  ((List.range ((length + 31) / 32)).flatMap fun i =>
    Hmac.hmac Hmac.sha256 kdk (i2osp i 2 ++ label ++ i2osp (8 * length) 2)).take length

/-! ## Implicit rejection (draft §7.2) -/

/-- Step 3.1, the key derivation key for the ciphertext `C` (of `k` octets)
and the private exponent `d` (the octets `dB`, most significant first):
`D = I2OSP(d, k)` (3.1.a), `DH = SHA256(D)` (3.1.b) and
`KDK = HMAC(DH, C, SHA256)` (3.1.c). `C` is always `k` octets here (step 1),
so it needs no padding with zeros. -/
def kdk (k : Nat) (dB C : List Byte) : List Byte :=
  Hmac.hmac Hmac.sha256 (Sha256.hash (i2osp (os2ip dB) k)) C

/-- The number of bits of `x`: 0 for 0, else `⌊log₂ x⌋ + 1`. -/
def bitLength (x : Nat) : Nat := if x = 0 then 0 else Nat.log2 x + 1

/-- Step 3.3, the alternative length `AL` for a modulus of `k` octets, from
the 256 octets `CL` of step 3.2.a, read as 128 two-octet big-endian
candidates: each candidate with its high-order bits zeroed, so that it has
the bit length of the maximum valid message size `k - 11` (3.3.a); `AL` is
the last of them not larger than `k - 11`, or 0 if none is (3.3.b). -/
def altLength (k : Nat) (CL : List Byte) : Nat :=
  (List.range 128).foldl (fun al i =>
    let c := os2ip [CL.getD (2 * i) 0, CL.getD (2 * i + 1) 0] % 2 ^ bitLength (k - 11)
    if c ≤ k - 11 then c else al) 0

/-- Step 4's separator: the index in `EM` of the first octet `0x00` after
`0x00 ‖ 0x02` (the first two octets), which separates `PS` from `M`, if there
is one. -/
def separator (EM : List Byte) : Option Nat :=
  ((EM.drop 2).findIdx? (· == 0)).map (· + 2)

/-- Step 4's checks: the padding is valid if the first octet of `EM` is
`0x00`, the second is `0x02`, there is an octet `0x00` separating `PS` from
`M`, and `PS` (the octets between the second and the separator) is at least
8 octets long. -/
def valid (EM : List Byte) : Bool :=
  EM.getD 0 1 == 0x00 && EM.getD 1 0 == 0x02 &&
    match separator EM with
    | some i => 10 ≤ i
    | none => false

/-- Step 4's message length `L`: the number of octets after the separator, or
0 if there is none, whatever the checks found. -/
def msgLength (EM : List Byte) : Nat :=
  match separator EM with
  | some i => EM.length - i - 1
  | none => 0

/-- Step 3 and the second case of step 5, for a modulus of `k` octets, the
private exponent `d` (`dB`) and the ciphertext `C`: the key derivation key
(3.1), the candidate lengths `CL = IRPRF(KDK, "length", 256)` and the
alternative message `AM = IRPRF(KDK, "message", k)` (3.2), the alternative
length `AL` (3.3); and the last `AL` octets of `AM`, which decryption returns
if the padding is not valid. -/
def alternative (k : Nat) (dB C : List Byte) : List Byte :=
  let key := kdk k dB C
  let CL := irprf key (ascii "length") 256
  let AM := irprf key (ascii "message") k
  let AL := altLength k CL
  lastN AL AM

/-- Steps 3–5, from the encoded message `EM` (`k` octets), the ciphertext
`C` and the private exponent `d` (`dB`): the checks and the message length
`L` of EME-PKCS1-v1_5 decoding (4); if the padding is valid, the last `L`
octets of `EM` (its message `M`), otherwise the alternative message
(`alternative`, step 3) (5). -/
def implicitDecode (dB C EM : List Byte) : List Byte :=
  if valid EM then lastN (msgLength EM) EM else alternative EM.length dB C

/-- RSAES-PKCS1-V1_5-DECRYPT (K, C) with implicit rejection (§7.2), for a
modulus of `k` octets, the private exponent `d` (`dB`) and the private-key
operation `rsadp` (RSADP, step 2.b, on and to `k`-octet strings):

1. Length checking: `invalid` if `C` is not `k` octets long (or `k < 11`).
2. RSA decryption: `EM = rsadp C`, or its error: `invalid` ("ciphertext
   representative out of range" if `OS2IP(C) ≥ n`, or a key it refuses) or
   `fault` (the internal error).
3–5. `implicitDecode`.

It never gives an error for an invalid padding. -/
def decryptWith (rsadp : List Byte → Rsa.Outcome) (k : Nat) (dB C : List Byte) : Rsa.Outcome :=
  if C.length = k ∧ 11 ≤ k then
    match rsadp C with
    | .ok EM => .ok (implicitDecode dB C EM)
    | .invalid => .invalid
    | .fault => .fault
  else .invalid

/-- RSAES-PKCS1-V1_5-DECRYPT with implicit rejection (`decryptWith`) of the
ciphertext `C` with the private key `(n, e, d, p, q, dP, dQ, qInv)`, the
modulus of `k = nB.length` octets: RSADP is `Rsa.privateChecked` (with the
CRT, checked against `e`), and `d` keys the implicit rejection, as given. -/
def decrypt (nB eB dB pB qB dPB dQB qInvB C : List Byte) : Rsa.Outcome :=
  decryptWith (fun C => Rsa.privateChecked nB eB C pB qB dPB dQB qInvB) nB.length dB C

end VG.Spec.RsaPkcs1Enc
