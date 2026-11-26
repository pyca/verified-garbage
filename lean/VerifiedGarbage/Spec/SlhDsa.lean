module

public import VerifiedGarbage.Spec.Sha3
public import VerifiedGarbage.Spec.Sha256
public import VerifiedGarbage.Spec.Sha512
public import VerifiedGarbage.Spec.Hmac
public import VerifiedGarbage.Spec.Mgf1

/-!
# SLH-DSA (FIPS 205)

**Trusted** (as every file in `Spec/`). The stateless hash-based digital
signature algorithm SLH-DSA, transcribed from FIPS 205, *Stateless
Hash-Based Digital Signature Standard* (August 2024); section, algorithm and
table numbers below refer to it. The algorithms are written for any
parameter set (`Params`), and the twelve of Table 2 are `sha2_128s` …
`shake_256f`. HashSLH-DSA (§10.2.2, Algorithms 23 and 25) is not specified.

Byte strings are lists of bytes, and the standard's integers are `Nat`s.
Messages are byte strings: the standard allows any bit string, and this
library signs only whole bytes, as the hash functions take them. A string of
`ℓ` `n`-byte strings (a WOTS⁺ signature, an authentication path, the roots
`T_ℓ` hashes) is their concatenation, of `ℓn` bytes, as the standard writes
it into the signature (§9.2), and `chunk X n i` is its string `i`.

An address `ADRS` is its 32-byte string (§4.2, Figure 2), and its member
functions (Table 1) write and read its byte ranges as the table says. The
standard's algorithms change the `ADRS` they are given; here each takes it
by value, which gives the same results: every algorithm sets each field of
`ADRS` that it, or what it calls, uses, from the fields its caller set
(the layer and tree addresses, and for FORS the key pair address), before
using it.

The hash functions are those of §11: SHAKE256 (`Spec/Sha3.lean`) for the
SHAKE parameter sets, and SHA-256, SHA-512 (`Spec/Sha256.lean`,
`Spec/Sha512.lean`), HMAC (`Spec/Hmac.lean`) and MGF1 (`Spec/Mgf1.lean`)
for the SHA2 parameter sets. The contracts of the functions the Rust code
calls are in `Spec/SlhDsa/Contract.lean`.
-/

@[expose] public section

namespace VG.Spec.SlhDsa

/-! ## Functions on integers and byte strings (§4.1) -/

/-- Algorithm 2, `toInt(X, n)`: the first `n` bytes of `X` as a big-endian
integer (`total ← 256·total + X[i]` for `i` from 0 to `n - 1`). -/
def toInt (X : List Byte) (n : Nat) : Nat :=
  (X.take n).foldl (fun total x => 256 * total + x.toNat) 0

/-- Algorithm 3, `toByte(x, n)`: the `n`-byte big-endian representation of
`x mod 256ⁿ` (byte `n - 1 - i` is `⌊x / 256ⁱ⌋ mod 256`). -/
def toByte (x n : Nat) : List Byte :=
  (List.range n).map fun i => BitVec.ofNat 8 (x / 256 ^ (n - 1 - i))

/-- Lines 6–10 of Algorithm 4: while `bits < b`, append the next byte
`X[in]` to `total` (`total ← (total ≪ 8) + X[in]`, `in ← in + 1`,
`bits ← bits + 8`). The loop runs at most `⌈b / 8⌉` times; `fuel` bounds it. -/
def base2bFill (X : List Byte) (b : Nat) : (fuel i bits total : Nat) → Nat × Nat × Nat
  | 0, i, bits, total => (i, bits, total)
  | fuel + 1, i, bits, total =>
    if bits < b then base2bFill X b fuel (i + 1) (bits + 8) (256 * total + (X.getD i 0).toNat)
    else (i, bits, total)

/-- Algorithm 4, `base_2b(X, b, out_len)`: the first `out_len` `b`-bit
integers of `X`, most significant bit first: for each output, read bytes
until `bits ≥ b` (`base2bFill`), then `bits ← bits - b` and
`baseb[out] ← (total ≫ bits) mod 2ᵇ`. -/
def base2b (X : List Byte) (b outLen : Nat) : List Nat :=
  ((List.range outLen).foldl (fun (st : Nat × Nat × Nat × List Nat) _ =>
      let (i, bits, total, out) := st
      let (i, bits, total) := base2bFill X b (b / 8 + 1) i bits total
      let bits := bits - b
      (i, bits, total, out ++ [total / 2 ^ bits % 2 ^ b]))
    (0, 0, 0, [])).2.2.2

/-- String `i` of the string of `n`-byte strings `X`: bytes `ni … ni + n - 1`. -/
def chunk (X : List Byte) (n i : Nat) : List Byte := (X.drop (n * i)).take n

/-! ## Parameter sets (§11, Table 2) -/

/-- The family of hash functions a parameter set uses (§11.1, §11.2). -/
inductive Family | sha2 | shake
  deriving DecidableEq

/-- A parameter set (Table 2): the security parameter `n` (in bytes), the
total height `h` of the hypertree, its number `d` of layers, the height
`h′ = h/d` of each XMSS tree (`hp`), the height `a` of each FORS tree, the
number `k` of FORS trees, `lg_w` (`lgw`, 4 for every parameter set), the
length `m` in bytes of the message digest, the security category, and the
hash functions. -/
structure Params where
  n : Nat
  h : Nat
  d : Nat
  hp : Nat
  a : Nat
  k : Nat
  lgw : Nat
  m : Nat
  category : Nat
  family : Family

/-- SLH-DSA-SHA2-128s (Table 2). -/
def sha2_128s : Params :=
  { n := 16, h := 63, d := 7, hp := 9, a := 12, k := 14, lgw := 4, m := 30, category := 1, family := .sha2 }
/-- SLH-DSA-SHAKE-128s (Table 2). -/
def shake_128s : Params := { sha2_128s with family := .shake }
/-- SLH-DSA-SHA2-128f (Table 2). -/
def sha2_128f : Params :=
  { n := 16, h := 66, d := 22, hp := 3, a := 6, k := 33, lgw := 4, m := 34, category := 1, family := .sha2 }
/-- SLH-DSA-SHAKE-128f (Table 2). -/
def shake_128f : Params := { sha2_128f with family := .shake }
/-- SLH-DSA-SHA2-192s (Table 2). -/
def sha2_192s : Params :=
  { n := 24, h := 63, d := 7, hp := 9, a := 14, k := 17, lgw := 4, m := 39, category := 3, family := .sha2 }
/-- SLH-DSA-SHAKE-192s (Table 2). -/
def shake_192s : Params := { sha2_192s with family := .shake }
/-- SLH-DSA-SHA2-192f (Table 2). -/
def sha2_192f : Params :=
  { n := 24, h := 66, d := 22, hp := 3, a := 8, k := 33, lgw := 4, m := 42, category := 3, family := .sha2 }
/-- SLH-DSA-SHAKE-192f (Table 2). -/
def shake_192f : Params := { sha2_192f with family := .shake }
/-- SLH-DSA-SHA2-256s (Table 2). -/
def sha2_256s : Params :=
  { n := 32, h := 64, d := 8, hp := 8, a := 14, k := 22, lgw := 4, m := 47, category := 5, family := .sha2 }
/-- SLH-DSA-SHAKE-256s (Table 2). -/
def shake_256s : Params := { sha2_256s with family := .shake }
/-- SLH-DSA-SHA2-256f (Table 2). -/
def sha2_256f : Params :=
  { n := 32, h := 68, d := 17, hp := 4, a := 9, k := 35, lgw := 4, m := 49, category := 5, family := .sha2 }
/-- SLH-DSA-SHAKE-256f (Table 2). -/
def shake_256f : Params := { sha2_256f with family := .shake }

namespace Params

variable (p : Params)

/-- `w = 2^lg_w` (§5, equation 5.1). -/
def w : Nat := 2 ^ p.lgw

/-- `len₁ = ⌈8n / lg_w⌉` (equation 5.2). -/
def len1 : Nat := (8 * p.n + p.lgw - 1) / p.lgw

/-- The loop of Algorithm 1 from `len₂` and `capacity`: while
`capacity ≤ max_checksum`, `len₂ ← len₂ + 1` and `capacity ← capacity·w`. Each
iteration multiplies `capacity` by `w ≥ 2`, so `max_checksum` iterations
(`fuel`) are more than it takes. -/
def genLen2Loop (maxChecksum : Nat) : (fuel len2 capacity : Nat) → Nat
  | 0, len2, _ => len2
  | fuel + 1, len2, capacity =>
    if capacity ≤ maxChecksum then genLen2Loop maxChecksum fuel (len2 + 1) (capacity * p.w)
    else len2

/-- Algorithm 1, `gen_len2(n, lg_w)` (equation 5.3): the number of base-`w`
digits of the largest checksum `max_checksum = len₁·(w - 1)`, starting from
`len₂ = 1` and `capacity = w`. (3 for every parameter set of Table 2.) -/
def len2 : Nat :=
  let maxChecksum := p.len1 * (p.w - 1)
  p.genLen2Loop maxChecksum maxChecksum 1 p.w

/-- `len = len₁ + len₂` (equation 5.4): the number of `n`-byte strings of a
WOTS⁺ private key, public key and signature. -/
def len : Nat := p.len1 + p.len2

/-- The length of a public key, `PK.seed ‖ PK.root` (§9.1, Figure 16): `2n`
bytes. -/
def pkLen : Nat := 2 * p.n

/-- The length of a private key, `SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root`
(§9.1, Figure 15): `4n` bytes. -/
def skLen : Nat := 4 * p.n

/-- The length of a FORS signature: `k(1 + a)` `n`-byte strings (§8.3,
Figure 14). -/
def forsSigLen : Nat := p.k * (1 + p.a) * p.n

/-- The length of an XMSS signature: `len + h′` `n`-byte strings (§6.2,
Figure 10). -/
def xmssSigLen : Nat := (p.len + p.hp) * p.n

/-- The length of a signature, `(1 + k(1 + a) + h + d·len)·n` bytes
(Algorithm 20, line 1; §9.2, Figure 17). -/
def sigLen : Nat := (1 + p.k * (1 + p.a) + p.h + p.d * p.len) * p.n

/-- `⌈k·a / 8⌉`, the length of `md` (Algorithm 19, line 7). -/
def mdLen : Nat := (p.k * p.a + 7) / 8

/-- `⌈(h - h/d) / 8⌉`, the length of `tmp_idx_tree` (Algorithm 19, line 8). -/
def treeIdxLen : Nat := (p.h - p.h / p.d + 7) / 8

/-- `⌈h / 8d⌉`, the length of `tmp_idx_leaf` (Algorithm 19, line 9). -/
def leafIdxLen : Nat := (p.h + 8 * p.d - 1) / (8 * p.d)

end Params

/-! ## Addresses (§4.2, §4.3)

An address is its 32 bytes: the layer address (bytes 0–3), the tree address
(4–15), the type (16–19) and three words whose meaning depends on the type
(20–31). -/

/-- An address. -/
abbrev Adrs := List Byte

/-- `ADRS ← toByte(0, 32)`. -/
def adrsZero : Adrs := toByte 0 32

/-- `ADRS[i : i + |bs|] ← bs`. -/
def setBytes (adrs : Adrs) (i : Nat) (bs : List Byte) : Adrs :=
  adrs.take i ++ bs ++ adrs.drop (i + bs.length)

/-- The address types (§4.2): `WOTS_HASH`. -/
def WOTS_HASH : Nat := 0
/-- `WOTS_PK`. -/
def WOTS_PK : Nat := 1
/-- `TREE`. -/
def TREE : Nat := 2
/-- `FORS_TREE`. -/
def FORS_TREE : Nat := 3
/-- `FORS_ROOTS`. -/
def FORS_ROOTS : Nat := 4
/-- `WOTS_PRF`. -/
def WOTS_PRF : Nat := 5
/-- `FORS_PRF`. -/
def FORS_PRF : Nat := 6

/-- `ADRS.setLayerAddress(l)`: `ADRS[0 : 4] ← toByte(l, 4)` (Table 1). -/
def setLayerAddress (adrs : Adrs) (l : Nat) : Adrs := setBytes adrs 0 (toByte l 4)

/-- `ADRS.setTreeAddress(t)`: `ADRS[4 : 16] ← toByte(t, 12)`. -/
def setTreeAddress (adrs : Adrs) (t : Nat) : Adrs := setBytes adrs 4 (toByte t 12)

/-- `ADRS.setTypeAndClear(Y)`: `ADRS[16 : 20] ← toByte(Y, 4)`,
`ADRS[20 : 32] ← toByte(0, 12)`. -/
def setTypeAndClear (adrs : Adrs) (Y : Nat) : Adrs := setBytes adrs 16 (toByte Y 4 ++ toByte 0 12)

/-- `ADRS.setKeyPairAddress(i)`: `ADRS[20 : 24] ← toByte(i, 4)`. -/
def setKeyPairAddress (adrs : Adrs) (i : Nat) : Adrs := setBytes adrs 20 (toByte i 4)

/-- `ADRS.setChainAddress(i)`: `ADRS[24 : 28] ← toByte(i, 4)`. -/
def setChainAddress (adrs : Adrs) (i : Nat) : Adrs := setBytes adrs 24 (toByte i 4)

/-- `ADRS.setTreeHeight(z)`: `ADRS[24 : 28] ← toByte(z, 4)`. -/
def setTreeHeight (adrs : Adrs) (z : Nat) : Adrs := setBytes adrs 24 (toByte z 4)

/-- `ADRS.setHashAddress(i)`: `ADRS[28 : 32] ← toByte(i, 4)`. -/
def setHashAddress (adrs : Adrs) (i : Nat) : Adrs := setBytes adrs 28 (toByte i 4)

/-- `ADRS.setTreeIndex(i)`: `ADRS[28 : 32] ← toByte(i, 4)`. -/
def setTreeIndex (adrs : Adrs) (i : Nat) : Adrs := setBytes adrs 28 (toByte i 4)

/-- `ADRS.getKeyPairAddress()`: `toInt(ADRS[20 : 24], 4)`. -/
def getKeyPairAddress (adrs : Adrs) : Nat := toInt (adrs.drop 20) 4

/-- `ADRS.getTreeIndex()`: `toInt(ADRS[28 : 32], 4)`. -/
def getTreeIndex (adrs : Adrs) : Nat := toInt (adrs.drop 28) 4

/-- The compressed address `ADRSᶜ = ADRS[3] ‖ ADRS[8 : 16] ‖ ADRS[19] ‖ ADRS[20 : 32]`
of 22 bytes (§11.2), which the SHA2 parameter sets hash. -/
def compress (adrs : Adrs) : List Byte :=
  (adrs.drop 3).take 1 ++ (adrs.drop 8).take 8 ++ (adrs.drop 19).take 1 ++ (adrs.drop 20).take 12

/-! ## The hash functions (§11)

`PRF`, `F`, `H` and `T_ℓ` output `n` bytes and `H_msg` `m` bytes; SHAKE256
outputs `8n` and `8m` bits. In security category 1 (`n = 16`), the SHA2
parameter sets use SHA-256 throughout (§11.2.1); in categories 3 and 5, SHA-512
for `H_msg`, `PRF_msg`, `H` and `T_ℓ` (§11.2.2). -/

/-- `SHA-256(PK.seed ‖ toByte(0, 64 - n) ‖ ADRSᶜ ‖ M)`, truncated to `n` bytes. -/
def sha256Adrs (p : Params) (pkSeed : List Byte) (adrs : Adrs) (M : List Byte) : List Byte :=
  (Sha256.hash (pkSeed ++ toByte 0 (64 - p.n) ++ compress adrs ++ M)).take p.n

/-- `SHA-512(PK.seed ‖ toByte(0, 128 - n) ‖ ADRSᶜ ‖ M)`, truncated to `n` bytes. -/
def sha512Adrs (p : Params) (pkSeed : List Byte) (adrs : Adrs) (M : List Byte) : List Byte :=
  (Sha512.sha512 (pkSeed ++ toByte 0 (128 - p.n) ++ compress adrs ++ M)).take p.n

/-- `SHAKE256(PK.seed ‖ ADRS ‖ M, 8n)`. -/
def shakeAdrs (p : Params) (pkSeed : List Byte) (adrs : Adrs) (M : List Byte) : List Byte :=
  Sha3.shake256 (pkSeed ++ adrs ++ M) p.n

/-- `H_msg(R, PK.seed, PK.root, M)`: `SHAKE256(R ‖ PK.seed ‖ PK.root ‖ M, 8m)`
(§11.1); `MGF1-SHA-256(R ‖ PK.seed ‖ SHA-256(R ‖ PK.seed ‖ PK.root ‖ M), m)`
(§11.2.1); `MGF1-SHA-512(R ‖ PK.seed ‖ SHA-512(R ‖ PK.seed ‖ PK.root ‖ M), m)`
(§11.2.2). -/
def hMsg (p : Params) (R pkSeed pkRoot M : List Byte) : List Byte :=
  match p.family with
  | .shake => Sha3.shake256 (R ++ pkSeed ++ pkRoot ++ M) p.m
  | .sha2 =>
    if p.category = 1 then Mgf1.mgf1 Mgf1.sha256 (R ++ pkSeed ++ Sha256.hash (R ++ pkSeed ++ pkRoot ++ M)) p.m
    else Mgf1.mgf1 Mgf1.sha512 (R ++ pkSeed ++ Sha512.sha512 (R ++ pkSeed ++ pkRoot ++ M)) p.m

/-- `PRF(PK.seed, SK.seed, ADRS)`: `SHAKE256(PK.seed ‖ ADRS ‖ SK.seed, 8n)`
(§11.1); `Trunc_n(SHA-256(PK.seed ‖ toByte(0, 64 - n) ‖ ADRSᶜ ‖ SK.seed))`
(§11.2.1, §11.2.2). -/
def prf (p : Params) (pkSeed skSeed : List Byte) (adrs : Adrs) : List Byte :=
  match p.family with
  | .shake => shakeAdrs p pkSeed adrs skSeed
  | .sha2 => sha256Adrs p pkSeed adrs skSeed

/-- `PRF_msg(SK.prf, opt_rand, M)`: `SHAKE256(SK.prf ‖ opt_rand ‖ M, 8n)`
(§11.1); `Trunc_n(HMAC-SHA-256(SK.prf, opt_rand ‖ M))` (§11.2.1);
`Trunc_n(HMAC-SHA-512(SK.prf, opt_rand ‖ M))` (§11.2.2). -/
def prfMsg (p : Params) (skPrf optRand M : List Byte) : List Byte :=
  match p.family with
  | .shake => Sha3.shake256 (skPrf ++ optRand ++ M) p.n
  | .sha2 =>
    if p.category = 1 then (Hmac.hmac Hmac.sha256 skPrf (optRand ++ M)).take p.n
    else (Hmac.hmac Hmac.sha512 skPrf (optRand ++ M)).take p.n

/-- `F(PK.seed, ADRS, M₁)`: `SHAKE256(PK.seed ‖ ADRS ‖ M₁, 8n)` (§11.1);
`Trunc_n(SHA-256(PK.seed ‖ toByte(0, 64 - n) ‖ ADRSᶜ ‖ M₁))` (§11.2.1,
§11.2.2). -/
def F (p : Params) (pkSeed : List Byte) (adrs : Adrs) (M₁ : List Byte) : List Byte :=
  match p.family with
  | .shake => shakeAdrs p pkSeed adrs M₁
  | .sha2 => sha256Adrs p pkSeed adrs M₁

/-- `H(PK.seed, ADRS, M₂)`: `SHAKE256(PK.seed ‖ ADRS ‖ M₂, 8n)` (§11.1);
`Trunc_n(SHA-256(PK.seed ‖ toByte(0, 64 - n) ‖ ADRSᶜ ‖ M₂))` (§11.2.1);
`Trunc_n(SHA-512(PK.seed ‖ toByte(0, 128 - n) ‖ ADRSᶜ ‖ M₂))` (§11.2.2). -/
def H (p : Params) (pkSeed : List Byte) (adrs : Adrs) (M₂ : List Byte) : List Byte :=
  match p.family with
  | .shake => shakeAdrs p pkSeed adrs M₂
  | .sha2 => if p.category = 1 then sha256Adrs p pkSeed adrs M₂ else sha512Adrs p pkSeed adrs M₂

/-- `T_ℓ(PK.seed, ADRS, M_ℓ)`, for `M_ℓ` the concatenation of `ℓ` `n`-byte
strings: as `H` (§11.1, §11.2.1, §11.2.2). -/
def T (p : Params) (pkSeed : List Byte) (adrs : Adrs) (Mℓ : List Byte) : List Byte :=
  match p.family with
  | .shake => shakeAdrs p pkSeed adrs Mℓ
  | .sha2 => if p.category = 1 then sha256Adrs p pkSeed adrs Mℓ else sha512Adrs p pkSeed adrs Mℓ

/-! ## WOTS⁺ (§5) -/

variable (p : Params)

/-- Algorithm 5, `chain(X, i, s, PK.seed, ADRS)`: `s` iterations of `F` on
`X`, the `j`-th (from `j = i`) with the hash address `j`. -/
def chain (X : List Byte) (i s : Nat) (pkSeed : List Byte) (adrs : Adrs) : List Byte :=
  (List.range s).foldl (fun tmp j => F p pkSeed (setHashAddress adrs (i + j)) tmp) X

/-- `skADRS` of Algorithms 6 and 7 (lines 1–3): `ADRS` with the type
`WOTS_PRF` and its key pair address. -/
def wotsSkAdrs (adrs : Adrs) : Adrs :=
  setKeyPairAddress (setTypeAndClear adrs WOTS_PRF) (getKeyPairAddress adrs)

/-- `wotspkADRS` of Algorithms 6 and 8: `ADRS` with the type `WOTS_PK` and
its key pair address. -/
def wotsPkAdrs (adrs : Adrs) : Adrs :=
  setKeyPairAddress (setTypeAndClear adrs WOTS_PK) (getKeyPairAddress adrs)

/-- Algorithm 6, `wots_pkGen(SK.seed, PK.seed, ADRS)`: the WOTS⁺ public key,
`T_len` of the ends of the `len` chains from the private key's strings
`PRF(PK.seed, SK.seed, skADRS)`. -/
def wotsPkGen (skSeed pkSeed : List Byte) (adrs : Adrs) : List Byte :=
  let tmp := (List.range p.len).flatMap fun i =>
    let sk := prf p pkSeed skSeed (setChainAddress (wotsSkAdrs adrs) i)
    chain p sk 0 (p.w - 1) pkSeed (setChainAddress adrs i)
  T p pkSeed (wotsPkAdrs adrs) tmp

/-- Lines 1–7 of Algorithms 7 and 8: the `len` base-`w` digits of the
message `M` and of its checksum. -/
def wotsDigits (M : List Byte) : List Nat :=
  let msg := base2b M p.lgw p.len1
  let csum := msg.foldl (fun csum mi => csum + p.w - 1 - mi) 0
  let csum := csum <<< ((8 - p.len2 * p.lgw % 8) % 8)
  msg ++ base2b (toByte csum ((p.len2 * p.lgw + 7) / 8)) p.lgw p.len2

/-- Algorithm 7, `wots_sign(M, SK.seed, PK.seed, ADRS)`: chain `i` of the
private key run for `msg[i]` steps. -/
def wotsSign (M skSeed pkSeed : List Byte) (adrs : Adrs) : List Byte :=
  let msg := wotsDigits p M
  (List.range p.len).flatMap fun i =>
    let sk := prf p pkSeed skSeed (setChainAddress (wotsSkAdrs adrs) i)
    chain p sk 0 (msg.getD i 0) pkSeed (setChainAddress adrs i)

/-- Algorithm 8, `wots_pkFromSig(sig, M, PK.seed, ADRS)`: the public key the
signature `sig` of `M` gives, chain `i` run on from step `msg[i]`. -/
def wotsPkFromSig (sig M pkSeed : List Byte) (adrs : Adrs) : List Byte :=
  let msg := wotsDigits p M
  let tmp := (List.range p.len).flatMap fun i =>
    chain p (chunk sig p.n i) (msg.getD i 0) (p.w - 1 - msg.getD i 0) pkSeed (setChainAddress adrs i)
  T p pkSeed (wotsPkAdrs adrs) tmp

/-! ## XMSS (§6) -/

/-- Algorithm 9, `xmss_node(SK.seed, i, z, PK.seed, ADRS)`: node `i` at
height `z` of the XMSS tree. -/
def xmssNode (skSeed : List Byte) : (i z : Nat) → (pkSeed : List Byte) → (adrs : Adrs) → List Byte
  | i, 0, pkSeed, adrs =>
    wotsPkGen p skSeed pkSeed (setKeyPairAddress (setTypeAndClear adrs WOTS_HASH) i)
  | i, z + 1, pkSeed, adrs =>
    let lnode := xmssNode skSeed (2 * i) z pkSeed adrs
    let rnode := xmssNode skSeed (2 * i + 1) z pkSeed adrs
    H p pkSeed (setTreeIndex (setTreeHeight (setTypeAndClear adrs TREE) (z + 1)) i) (lnode ++ rnode)

/-- Algorithm 10, `xmss_sign(M, SK.seed, idx, PK.seed, ADRS)`: the WOTS⁺
signature of `M` by leaf `idx`, then the authentication path, the sibling
`⌊idx / 2ʲ⌋ ⊕ 1` at each height `j`. -/
def xmssSign (M skSeed : List Byte) (idx : Nat) (pkSeed : List Byte) (adrs : Adrs) : List Byte :=
  let auth := (List.range p.hp).flatMap fun j => xmssNode p skSeed (idx / 2 ^ j ^^^ 1) j pkSeed adrs
  let sig := wotsSign p M skSeed pkSeed (setKeyPairAddress (setTypeAndClear adrs WOTS_HASH) idx)
  sig ++ auth

/-- Algorithm 11, `xmss_pkFromSig(idx, SIG_XMSS, M, PK.seed, ADRS)`: the root
the XMSS signature `SIG_XMSS` of `M` by leaf `idx` gives. Its WOTS⁺
signature is its first `len` strings (`getWOTSSig`), and its authentication
path the `h′` after them (`getXMSSAUTH`). -/
def xmssPkFromSig (idx : Nat) (sigXmss M pkSeed : List Byte) (adrs : Adrs) : List Byte :=
  let adrs := setKeyPairAddress (setTypeAndClear adrs WOTS_HASH) idx
  let sig := sigXmss.take (p.len * p.n)
  let auth := sigXmss.drop (p.len * p.n)
  let node := wotsPkFromSig p sig M pkSeed adrs
  let adrs := setTreeIndex (setTypeAndClear adrs TREE) idx
  ((List.range p.hp).foldl (fun (st : List Byte × Adrs) k =>
      let (node, adrs) := st
      let adrs := setTreeHeight adrs (k + 1)
      if idx / 2 ^ k % 2 = 0 then
        let adrs := setTreeIndex adrs (getTreeIndex adrs / 2)
        (H p pkSeed adrs (node ++ chunk auth p.n k), adrs)
      else
        let adrs := setTreeIndex adrs ((getTreeIndex adrs - 1) / 2)
        (H p pkSeed adrs (chunk auth p.n k ++ node), adrs))
    (node, adrs)).1

/-! ## The hypertree (§7) -/

/-- Algorithm 12, `ht_sign(M, SK.seed, PK.seed, idx_tree, idx_leaf)`: the
`d` XMSS signatures, from layer 0 up, each of the root of the tree below
(lines 1–15). -/
def htSign (M skSeed pkSeed : List Byte) (idxTree idxLeaf : Nat) : List Byte :=
  let adrs := setTreeAddress adrsZero idxTree
  let sigTmp := xmssSign p M skSeed idxLeaf pkSeed adrs
  let root := xmssPkFromSig p idxLeaf sigTmp M pkSeed adrs
  let (sigHt, _, _, _) := (List.range (p.d - 1)).foldl
    (fun (st : List Byte × List Byte × Nat × Adrs) j' =>
      let (sigHt, root, idxTree, adrs) := st
      let j := j' + 1
      let idxLeaf := idxTree % 2 ^ p.hp
      let idxTree := idxTree >>> p.hp
      let adrs := setTreeAddress (setLayerAddress adrs j) idxTree
      let sigTmp := xmssSign p root skSeed idxLeaf pkSeed adrs
      let sigHt := sigHt ++ sigTmp
      let root := if j < p.d - 1 then xmssPkFromSig p idxLeaf sigTmp root pkSeed adrs else root
      (sigHt, root, idxTree, adrs))
    (sigTmp, root, idxTree, adrs)
  sigHt

/-- Algorithm 13, `ht_verify(M, SIG_HT, PK.seed, idx_tree, idx_leaf, PK.root)`:
whether the root the `d` XMSS signatures of `SIG_HT` give (the `j`-th,
`getXMSSSignature(j)`, of `len + h′` strings) is `PK.root`. -/
def htVerify (M sigHt pkSeed : List Byte) (idxTree idxLeaf : Nat) (pkRoot : List Byte) : Bool :=
  let adrs := setTreeAddress adrsZero idxTree
  let sigTmp := chunk sigHt p.xmssSigLen 0
  let node := xmssPkFromSig p idxLeaf sigTmp M pkSeed adrs
  let (node, _, _) := (List.range (p.d - 1)).foldl
    (fun (st : List Byte × Nat × Adrs) j' =>
      let (node, idxTree, adrs) := st
      let j := j' + 1
      let idxLeaf := idxTree % 2 ^ p.hp
      let idxTree := idxTree >>> p.hp
      let adrs := setTreeAddress (setLayerAddress adrs j) idxTree
      let sigTmp := chunk sigHt p.xmssSigLen j
      (xmssPkFromSig p idxLeaf sigTmp node pkSeed adrs, idxTree, adrs))
    (node, idxTree, adrs)
  node == pkRoot

/-! ## FORS (§8) -/

/-- Algorithm 14, `fors_skGen(SK.seed, PK.seed, ADRS, idx)`: the FORS private
key value `idx`. -/
def forsSkGen (skSeed pkSeed : List Byte) (adrs : Adrs) (idx : Nat) : List Byte :=
  let skAdrs := setTreeIndex (setKeyPairAddress (setTypeAndClear adrs FORS_PRF) (getKeyPairAddress adrs)) idx
  prf p pkSeed skSeed skAdrs

/-- Algorithm 15, `fors_node(SK.seed, i, z, PK.seed, ADRS)`: node `i` at
height `z` of the FORS trees (their nodes at height `z` numbered from the
first tree's). -/
def forsNode (skSeed : List Byte) : (i z : Nat) → (pkSeed : List Byte) → (adrs : Adrs) → List Byte
  | i, 0, pkSeed, adrs =>
    let sk := forsSkGen p skSeed pkSeed adrs i
    F p pkSeed (setTreeIndex (setTreeHeight adrs 0) i) sk
  | i, z + 1, pkSeed, adrs =>
    let lnode := forsNode skSeed (2 * i) z pkSeed adrs
    let rnode := forsNode skSeed (2 * i + 1) z pkSeed adrs
    H p pkSeed (setTreeIndex (setTreeHeight adrs (z + 1)) i) (lnode ++ rnode)

/-- Algorithm 16, `fors_sign(md, SK.seed, PK.seed, ADRS)`: for each of the
`k` trees, the private key value its index `indices[i]` selects, then its
authentication path. -/
def forsSign (md skSeed pkSeed : List Byte) (adrs : Adrs) : List Byte :=
  let indices := base2b md p.a p.k
  (List.range p.k).flatMap fun i =>
    let idx := indices.getD i 0
    forsSkGen p skSeed pkSeed adrs (i * 2 ^ p.a + idx) ++
      (List.range p.a).flatMap fun j =>
        forsNode p skSeed (i * 2 ^ (p.a - j) + (idx / 2 ^ j ^^^ 1)) j pkSeed adrs

/-- Algorithm 17, `fors_pkFromSig(SIG_FORS, md, PK.seed, ADRS)`: the FORS
public key the signature `SIG_FORS` of `md` gives, `T_k` of the `k` roots.
Tree `i`'s private key value is its string `i(a + 1)` (`getSK(i)`), and its
authentication path the `a` strings after it (`getAUTH(i)`). -/
def forsPkFromSig (sigFors md pkSeed : List Byte) (adrs : Adrs) : List Byte :=
  let indices := base2b md p.a p.k
  let root := (List.range p.k).flatMap fun i =>
    let idx := indices.getD i 0
    let sk := chunk sigFors p.n (i * (p.a + 1))
    let auth := ((sigFors.drop (p.n * (i * (p.a + 1) + 1))).take (p.a * p.n))
    let adrs := setTreeIndex (setTreeHeight adrs 0) (i * 2 ^ p.a + idx)
    let node := F p pkSeed adrs sk
    ((List.range p.a).foldl (fun (st : List Byte × Adrs) j =>
        let (node, adrs) := st
        let adrs := setTreeHeight adrs (j + 1)
        if idx / 2 ^ j % 2 = 0 then
          let adrs := setTreeIndex adrs (getTreeIndex adrs / 2)
          (H p pkSeed adrs (node ++ chunk auth p.n j), adrs)
        else
          let adrs := setTreeIndex adrs ((getTreeIndex adrs - 1) / 2)
          (H p pkSeed adrs (chunk auth p.n j ++ node), adrs))
      (node, adrs)).1
  let forspkAdrs := setKeyPairAddress (setTypeAndClear adrs FORS_ROOTS) (getKeyPairAddress adrs)
  T p pkSeed forspkAdrs root

/-! ## SLH-DSA (§9, §10) -/

/-- Algorithm 18, `slh_keygen_internal(SK.seed, SK.prf, PK.seed)`: the
private key `SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root` and the public key
`PK.seed ‖ PK.root`, `PK.root` the root of the XMSS tree of the top layer. -/
def keyGenInternal (skSeed skPrf pkSeed : List Byte) : List Byte × List Byte :=
  let adrs := setLayerAddress adrsZero (p.d - 1)
  let pkRoot := xmssNode p skSeed 0 p.hp pkSeed adrs
  (skSeed ++ skPrf ++ pkSeed ++ pkRoot, pkSeed ++ pkRoot)

/-- Lines 7–12 of Algorithm 19 (lines 6–11 of Algorithm 20): the message
digest `md`, and the indices `idx_tree` (mod `2^(h - h/d)`) and `idx_leaf`
(mod `2^(h/d)`) of the digest. -/
def splitDigest (digest : List Byte) : List Byte × Nat × Nat :=
  let md := digest.take p.mdLen
  let tmpIdxTree := (digest.drop p.mdLen).take p.treeIdxLen
  let tmpIdxLeaf := (digest.drop (p.mdLen + p.treeIdxLen)).take p.leafIdxLen
  let idxTree := toInt tmpIdxTree p.treeIdxLen % 2 ^ (p.h - p.h / p.d)
  let idxLeaf := toInt tmpIdxLeaf p.leafIdxLen % 2 ^ (p.h / p.d)
  (md, idxTree, idxLeaf)

/-- The digest of Algorithm 19, line 6, for the private key `sk` and the
randomness `opt_rand`: `H_msg(R, PK.seed, PK.root, M)` with
`R = PRF_msg(SK.prf, opt_rand, M)` (line 3). -/
def signDigest (M sk optRand : List Byte) : List Byte :=
  let R := prfMsg p (chunk sk p.n 1) optRand M
  hMsg p R (chunk sk p.n 2) (chunk sk p.n 3) M

/-- Algorithm 19, `slh_sign_internal(M, SK, addrnd)`, with `opt_rand`
(line 2): `addrnd`, or `PK.seed` for the deterministic variant. The private
key `SK` is `SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root`. The signature is
`R ‖ SIG_FORS ‖ SIG_HT`. -/
def signInternal (M sk optRand : List Byte) : List Byte :=
  let skSeed := chunk sk p.n 0
  let skPrf := chunk sk p.n 1
  let pkSeed := chunk sk p.n 2
  let pkRoot := chunk sk p.n 3
  let R := prfMsg p skPrf optRand M
  let digest := hMsg p R pkSeed pkRoot M
  let (md, idxTree, idxLeaf) := splitDigest p digest
  let adrs := setKeyPairAddress (setTypeAndClear (setTreeAddress adrsZero idxTree) FORS_TREE) idxLeaf
  let sigFors := forsSign p md skSeed pkSeed adrs
  let pkFors := forsPkFromSig p sigFors md pkSeed adrs
  let sigHt := htSign p pkFors skSeed pkSeed idxTree idxLeaf
  R ++ sigFors ++ sigHt

/-- Algorithm 20, `slh_verify_internal(M, SIG, PK)`: false if `SIG` is not
of `sigLen` bytes (line 1); otherwise whether the hypertree signature
`SIG_HT` (its last `(h + d·len)n` bytes) of the FORS public key that
`SIG_FORS` (the `k(1 + a)n` bytes after `R`, its first `n`) gives is valid
for `PK.root`. The public key `PK` is `PK.seed ‖ PK.root`. -/
def verifyInternal (M sig pk : List Byte) : Bool :=
  if sig.length ≠ p.sigLen then false else
  let pkSeed := chunk pk p.n 0
  let pkRoot := chunk pk p.n 1
  let R := sig.take p.n
  let sigFors := (sig.drop p.n).take p.forsSigLen
  let sigHt := sig.drop (p.n + p.forsSigLen)
  let digest := hMsg p R pkSeed pkRoot M
  let (md, idxTree, idxLeaf) := splitDigest p digest
  let adrs := setKeyPairAddress (setTypeAndClear (setTreeAddress adrsZero idxTree) FORS_TREE) idxLeaf
  let pkFors := forsPkFromSig p sigFors md pkSeed adrs
  htVerify p pkFors sigHt pkSeed idxTree idxLeaf pkRoot

/-- The message `M′ = toByte(0, 1) ‖ toByte(|ctx|, 1) ‖ ctx ‖ M` of a pure
signature (Algorithm 22, line 8; Algorithm 24, line 4), or `none` (the
error indication `⊥` of Algorithm 22, lines 1–3, and `false` of
Algorithm 24) if the context string `ctx` is longer than 255 bytes. -/
def formatMessage (ctx M : List Byte) : Option (List Byte) :=
  if ctx.length > 255 then none
  else some (toByte 0 1 ++ toByte ctx.length 1 ++ ctx ++ M)

/-- Algorithm 22, `slh_sign(M, ctx, SK)`, on the randomness `addrnd`
(line 5; `PK.seed` for the deterministic variant, line 6): the signature
of the formatted message, or `none` (`⊥`) if `ctx` is too long. -/
def sign (M ctx sk addrnd : List Byte) : Option (List Byte) :=
  (formatMessage ctx M).map fun M' => signInternal p M' sk addrnd

/-- Algorithm 24, `slh_verify(M, SIG, ctx, PK)`: false if `ctx` is too long;
otherwise `slh_verify_internal` of the formatted message. -/
def verify (M sig ctx pk : List Byte) : Bool :=
  match formatMessage ctx M with
  | none => false
  | some M' => verifyInternal p M' sig pk

end VG.Spec.SlhDsa
