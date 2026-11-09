module

public import VerifiedGarbage.Impl.RsaOaep.PPC64LE
public import VerifiedGarbage.Impl.Md5.PPC64LE.Stream
public import VerifiedGarbage.Impl.Sha1.PPC64LE.Stream
public import VerifiedGarbage.Impl.Sha256.PPC64LE.Md
public import VerifiedGarbage.Impl.Sha512.PPC64LE.Md

/-!
# RSASSA-PSS verification (RFC 8017 §8.1.2) with a precomputed public key on PPC64LE

`vg_rsa_pss_verify_precomputed(n = r3, n_len = r4, e = r5, e_len = r6,
digest = r7, digest_len = r8, sig = r9, sig_len = r10, salt_len,
any_salt_len, scratch, scratch_len, pre, pre_len, hash, mgf1)`, the last
eight on the stack, with the hash function of the table `hash` (of the
interface `MdHash`, `Spec/MdHashTable.lean`) and MGF1 over that of the table
`mgf1` (of the interface `Hash`, `Spec/HashTable.lean`), which it calls
through the tables (`tcall`), with `vg_rsa_public_precomputed_checked`. The
index of `hash`'s hash function (its word 5) selects the code for that hash
function's sizes (`byIdx`, among `idxs`), which is all that code uses of it
(`shapeOf`): its digest length and its block, hash value and length field,
with the code that writes the length field.

It runs in the frame of RSAES-OAEP encryption (`Impl/RsaOaep/PPC64LE.lean`)
and uses its MGF1 with a table (`mgfXorT`) and its part of `scratch` (`oEm`,
`oSt`, `oDig`, `oW`), and more of it: `M'` at `oY`, the length field at
`oLen` and the hash value selected at `oSel`. The public operation gets the
rest of `scratch` from `oRsa`, `scratch_len - 1024` words, and writes RSAVP1
of the signature (or zeros) to `EM`'s place, `k = n_len` bytes at `scratch`.

The values the code keeps across the calls are in `r14`–`r23`: `r14` =
`scratch`, `r15` = `k`, `r16` = `digest`, `r17` = `lo` (1 if
`emLen = k - 1`, else 0), `r18` = `c`, the mask `0xFF >> (8 emLen - emBits)`
of `maskedDB`'s first byte, `r19` = `salt_len`, `r20` = `any_salt_len`
(zero-extended), `r21` = `dbLen = emLen - hLen - 1`, `r22` = `pre`, `r23` =
`pre_len`. Until the public operation, `r24`–`r27` hold `e`, `e_len`, `sig`
and `scratch_len`, and `r9` the modulus' first byte `n₀`; after it, MGF1 uses
`r24`–`r29`, and then `r24` holds the accumulator of failed checks and
`r25` the salt's length.

If `n₀ = 0`, `emLen < hLen + 2` or, for a given salt length, `salt_len >
emLen - hLen - 2` (all public), it returns 0. Otherwise it computes `EM`,
whose bytes are secret from here on: `EM`'s last byte becomes the OR of the
checks of `0xbc`, of the leading byte if `lo = 1` and of the top bits of
`maskedDB`; `DB` is unmasked in place and its top bits cleared; a scan finds
the first nonzero byte of `DB` (its index `pos` and value) without branching
on it, whose value must be 1, and the salt's length `dbLen - pos - 1`, which
must be `salt_len` if one is given. Then `H' = Hash(0⁸ ‖ mHash ‖ salt)`:

* for a given salt length, the last `salt_len` bytes of `DB` follow `mHash`
  in `M'`, which is hashed with the streaming functions;
* for any salt length, `DB` follows `mHash` in `M'` and is shifted left by
  `pos + 1` bytes in ten passes (one per bit of `pos + 1`, each moving every
  byte or none), so that the salt follows `mHash`, then zeros; `M'`, whose
  length `ℓ = 8 + hLen + sLen` is secret, is hashed by `ctHash`, which
  depends only on `nbm = ⌊(8 + hLen + dbLen - 1 + L) / B⌋ + 1`, the blocks
  of the longest: `init` sets the hash value, `0x80` is ORed into byte `i`
  of `M'` under the mask of `i = ℓ` for every `i < nbm B`, the length field
  of `ℓ` (written at `oLen` by the hash function's code for it) is ORed into
  the end of block `b` under the mask of `b = ⌊(ℓ + L) / B⌋`, the last block
  of the padded message, for every `b < nbm`; every block `b < nbm` is
  compressed (the table's function 3), and the hash value copied to `oSel`
  under the mask of `b = ⌊(ℓ + L) / B⌋`; and the digest of that hash value
  is written to `oDig` (the table's function 4).

The result is 1 if the accumulator, ORed with `H' ⊕ H`, is zero. A
comparison of values below `2⁶³` is the top bit of their difference, and
every selection a mask: every branch and address depends only on the
pointers, the lengths, `salt_len`, `any_salt_len`, `n₀` and which tables
`hash` and `mgf1` are.
-/

@[expose] public section

namespace VG.Impl.RsaPss.PPC64LE

open VG VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Impl.MdStream.PPC64LE (Params lg)
open VG.Impl.RsaOaep.PPC64LE (arg copyLoop zeroLoop oEm oSt oDig oW oRsa Fns tcall tword mgfXorT)

/-! ## More of our part of `scratch` -/

/-- `M' = 0⁸ ‖ mHash ‖ salt`, and room for `DB`'s shift and the padding:
2048 bytes. -/
def oY : Nat := 2560
/-- The length field of `ctHash` (at most 16 bytes). -/
def oLen : Nat := 4608
/-- The hash value selected by `ctHash` (at most 64 bytes). -/
def oSel : Nat := 4800

/-! ## The tables

The hash function's table, of `MdHash`, and MGF1's, of `Hash`, are stack
arguments (`hArg`, `gArg` for verification); each call of one of their
functions is indirect (`tcall`: the table's word through the stack
argument, into `r12`, then `bctrl`, of whichever of the functions the list
names is at that address). -/

/-- The functions an indirect call of each of the functions of a table of
`MdHash` may reach: for each of `init`, `update`, `finalize`, the
compression function and the digest, that function of every table of the
interface. -/
structure MdFns where
  init : List (String × Prog isa)
  upd : List (String × Prog isa)
  fin : List (String × Prog isa)
  comp : List (String × Prog isa)
  dig : List (String × Prog isa)

/-- Verification's stack arguments `hash` and `mgf1`. -/
def hArg : Nat := 6
def gArg : Nat := 7

/-! ## The hash function's sizes -/

/-- The indices in `Spec.Mgf1.hashes` of the hash functions whose tables the
functions take: MD5, SHA-1, SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224
and SHA-512/256. -/
def idxs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]

/-- A hash function with only the sizes `B`, `N` and `D`, which is all the
code with the hash function's calls through a table uses of it. -/
def ofSizes (B N D : Nat) : Hash := ⟨B, N, D, 0, 0, "", .block [], "", .block [], "", .block [], ""⟩

/-- The sizes and the Merkle–Damgård code's parameters of the hash function
of index `i` in `Spec.Mgf1.hashes`: those of MD5, SHA-1, SHA-256 (for SHA-224
too) and SHA-512 (for the SHA-512 family), with the digest length. -/
def shapeOf : Nat → Hash × Params
  | 0 => (ofSizes 64 16 16, Impl.Md5.PPC64LE.Stream.params)
  | 1 => (ofSizes 64 20 20, Impl.Sha1.PPC64LE.Stream.params)
  | 2 => (ofSizes 64 32 28, Impl.Sha256.PPC64LE.mdParams)
  | 3 => (ofSizes 64 32 32, Impl.Sha256.PPC64LE.mdParams)
  | 4 => (ofSizes 128 64 48, Impl.Sha512.PPC64LE.mdParams)
  | 5 => (ofSizes 128 64 64, Impl.Sha512.PPC64LE.mdParams)
  | 6 => (ofSizes 128 64 28, Impl.Sha512.PPC64LE.mdParams)
  | _ => (ofSizes 128 64 32, Impl.Sha512.PPC64LE.mdParams)

/-- `b i` for the index `i` in `r11` (`r12` is written), among `is`: the last
if it is none of the others. -/
def byIdx (b : Nat → Prog isa) : List Nat → Prog isa
  | [] => .block []
  | [i] => b i
  | i :: is => .seq (.block [.subi .r12 .r11 i]) (.ite (.zero .d .r12) (b i) (byIdx b is))

variable (H : Hash) (P : Params) (f : MdFns) (g : Fns)

/-! ## The entry -/

/-- The arguments into the registers that keep them, with `r12 = r1`; then
`n₀` into `r9`, and `lo`, `c` and `dbLen` from it: with `x` the bits of
`n₀ >> 1` smeared down (`2^b - 1` for the top bit `b` of `n₀`), `lo = (x = 0)`
and `c = x ∨ (0xFF ∧ -lo)`. -/
def prologue : List Instr :=
  [.load .d .r20 .r12 (arg 1), .lsr .w .r20 .r20 0, .load .d .r14 .r12 (arg 2), .load .d .r27 .r12 (arg 3),
    .load .d .r22 .r12 (arg 4), .load .d .r23 .r12 (arg 5), mov .r15 .r4, mov .r16 .r7, .load .d .r19 .r12 (arg 0),
    mov .r24 .r5, mov .r25 .r6, mov .r26 .r9, .lbz .r9 .r3 0,
    .lsr .d .r10 .r9 1, .lsr .d .r11 .r10 1, .logic .or .r10 .r10 .r11, .lsr .d .r11 .r10 2,
    .logic .or .r10 .r10 .r11, .lsr .d .r11 .r10 4, .logic .or .r10 .r10 .r11,
    .subi .r11 .r10 1, .lsr .d .r17 .r11 63, .li .r11 0, .sub .r11 .r11 .r17, .li .r8 0xFF,
    .logic .and .r11 .r11 .r8, .logic .or .r18 .r10 .r11, .sub .r21 .r15 .r17, .subi .r21 .r21 (H.D + 1)]

/-- 0. -/
def fail : Prog isa := .block [.li .r3 0]

/-! ## The checks -/

/-- In `r3`, 1 if `emLen < hLen + 2`, 0 if not. -/
def chkEm : List Instr := [.sub .r3 .r15 .r17, .subi .r3 .r3 (H.D + 2), .lsr .d .r3 .r3 63]

/-- `r4 :=` the salt length expected, 0 for any. -/
def expLen : Prog isa := .ite (.zero .d .r20) (.block [mov .r4 .r19]) (.block [.li .r4 0])

/-- In `r3`, nonzero exactly when the salt length expected (`r4`) is more
than `emLen - hLen - 2`, for `emLen ≥ hLen + 2`: the top bit of `r4`, or of
`(emLen - hLen - 2) - r4`. -/
def chkSalt : List Instr :=
  [.sub .r3 .r15 .r17, .subi .r3 .r3 (H.D + 2), .sub .r3 .r3 .r4, .lsr .d .r3 .r3 63, .lsr .d .r5 .r4 63,
    .logic .or .r3 .r3 .r5]

/-! ## The public operation -/

/-- The arguments of `vg_rsa_public_precomputed_checked`: `EM`'s place (`k`
bytes), `pre`, `e`, the signature (`k` bytes), and the rest of `scratch` on
the stack. -/
def pubArgs : List Instr :=
  [.addSp .r12 0, .li .r4 oRsa, .add .r4 .r14 .r4, .store .d .r4 .r12 96, .subi .r5 .r27 1024,
    .store .d .r5 .r12 104, .addi .r3 .r14 oEm, mov .r4 .r15, mov .r5 .r22, mov .r6 .r23, mov .r7 .r24,
    mov .r8 .r25, mov .r9 .r26, mov .r10 .r15]

/-! ## `EM` -/

/-- `EM`'s last byte replaced by `(EM[k-1] ⊕ 0xbc) ∨ (EM[lo] ∧ ¬c) ∨
(EM[0] ∧ -lo)`: zero exactly when it is `0xbc`, the top bits of `maskedDB`
are zero and, if `lo = 1`, the leading byte is zero. -/
def acc0 : List Instr :=
  [.add .r4 .r14 .r15, .subi .r4 .r4 1, .lbz .r5 .r4 0, .li .r6 0xbc, .logic .xor .r5 .r5 .r6,
    .add .r7 .r14 .r17, .lbz .r6 .r7 0, .li .r8 0xFF, .logic .xor .r8 .r8 .r18, .logic .and .r6 .r6 .r8,
    .logic .or .r5 .r5 .r6, .lbz .r6 .r14 0, .li .r8 0, .sub .r8 .r8 .r17, .logic .and .r6 .r6 .r8,
    .logic .or .r5 .r5 .r6, .stb .r5 .r4 0]

/-- MGF1's registers for unmasking `DB` (`dbLen` bytes at `EM + lo`) with `H`
(`hLen` bytes after it). -/
def dbArgs : List Instr := [.add .r26 .r14 .r17, mov .r27 .r21, .add .r24 .r26 .r21, .li .r25 H.D]

/-- `DB`'s first byte ANDed with `c`. -/
def clearTop : List Instr := [.add .r4 .r14 .r17, .lbz .r5 .r4 0, .logic .and .r5 .r5 .r18, .stb .r5 .r4 0]

/-! ## The scan -/

/-- `r4` = the byte's address, `r5` = the bytes left, `r6` = its index,
`r7` = all ones while no nonzero byte was seen, `r8` = `pos`, `r9` = the
value there. -/
def scanArgs : List Instr :=
  [.add .r4 .r14 .r17, mov .r5 .r21, .li .r6 0, .li .r7 0, .subi .r7 .r7 1, .li .r8 0, .li .r9 0]

/-- A byte: `z = (b = 0)`, `take = r7 ∧ (z - 1)`; `pos ∨= i ∧ take`,
`val ∨= b ∧ take`, `r7 ∧= -z`. -/
def scanBody : List Instr :=
  [.lbz .r10 .r4 0, .subi .r11 .r10 1, .lsr .d .r11 .r11 63, .subi .r12 .r11 1, .logic .and .r12 .r12 .r7,
    .logic .and .r3 .r6 .r12, .logic .or .r8 .r8 .r3, .logic .and .r3 .r10 .r12, .logic .or .r9 .r9 .r3,
    .li .r3 0, .sub .r3 .r3 .r11, .logic .and .r7 .r7 .r3, .addi .r4 .r4 1, .addi .r6 .r6 1, .subi .r5 .r5 1]

/-- The first nonzero byte of `DB`: its index in `r8`, its value in `r9`
(both 0 if there is none). -/
def scan : Prog isa := .seq (.block scanArgs) (.loop (.block scanBody) (.nonzero .d .r5))

/-- The accumulator (`r24`): `EM`'s last byte, ORed with `val ⊕ 1`; the salt's
length `dbLen - pos - 1` into `r25`. -/
def posCheck : List Instr :=
  [.add .r4 .r14 .r15, .subi .r4 .r4 1, .lbz .r24 .r4 0, .li .r3 1, .logic .xor .r9 .r9 .r3,
    .logic .or .r24 .r24 .r9, .sub .r25 .r21 .r8, .subi .r25 .r25 1]

/-- For a given salt length, the accumulator ORed with its difference from
the salt's. -/
def lenCheck : Prog isa :=
  .ite (.zero .d .r20) (.block [.logic .xor .r3 .r25 .r19, .logic .or .r24 .r24 .r3]) (.block [])

/-! ## `M'` -/

/-- `0⁸ ‖ mHash` at `scratch + oY`, after `n` bytes of `scratch + oY`
cleared. -/
def mPrefix (n : Nat) : Prog isa :=
  .seq (.seq (.block [.addi .r4 .r14 oY, .li .r5 n, .li .r6 0]) zeroLoop)
    (.seq (.block [mov .r4 .r16, .addi .r5 .r14 (oY + 8), .li .r6 H.D]) copyLoop)

/-- The last `salt_len` bytes of `DB` after `mHash`. -/
def copySalt : Prog isa :=
  .seq (.block [.add .r4 .r14 .r17, .add .r4 .r4 .r21, .sub .r4 .r4 .r19, .addi .r5 .r14 (oY + 8 + H.D),
      mov .r6 .r19])
    (.ite (.nonzero .d .r6) copyLoop (.block []))

/-- `DB` after `mHash`. -/
def copyDb : Prog isa := .seq (.block [.add .r4 .r14 .r17, .addi .r5 .r14 (oY + 8 + H.D), mov .r6 .r21]) copyLoop

/-! ## The shift -/

/-- A pass: every byte of `DB`'s place in `M'` replaced by the one `d` (`r9`)
bytes after it if bit 0 of `a` (`r8`) is set. -/
def shiftPass : Prog isa :=
  .seq (.block [.addi .r4 .r14 (oY + 8 + H.D), .add .r5 .r4 .r9, .li .r6 1, .logic .and .r6 .r8 .r6, .li .r7 0,
      .sub .r6 .r7 .r6, mov .r7 .r21])
    (.loop (.block [.lbz .r11 .r4 0, .lbz .r3 .r5 0, .logic .xor .r3 .r3 .r11, .logic .and .r3 .r3 .r6,
      .logic .xor .r11 .r11 .r3, .stb .r11 .r4 0, .addi .r4 .r4 1, .addi .r5 .r5 1, .subi .r7 .r7 1])
      (.nonzero .d .r7))

/-- `DB`'s place in `M'` shifted left by `pos + 1` (`a`, from `r8`) bytes, in
ten passes, the `j`-th by `d = 2^j`. -/
def shift : Prog isa :=
  .seq (.block [.addi .r8 .r8 1, .li .r9 1, .li .r10 10])
    (.loop (.seq (shiftPass H) (.block [.lsr .d .r8 .r8 1, .add .r9 .r9 .r9, .subi .r10 .r10 1]))
      (.nonzero .d .r10))

/-! ## Hashing with the streaming functions -/

variable (j : Nat)

/-- `init` on the state at `scratch + oSt`, through the table that is our
stack argument `j`. -/
def hInit : Prog isa := .seq (.block [.addi .r3 .r14 oSt]) (tcall j 0 f.init)

/-- `update` of the state, after `r4` bytes, with the `r6` bytes of `M'` at
`r5`. -/
def hUpd : Prog isa := .seq (.block [.addi .r3 .r14 oSt, .addi .r7 .r14 oW]) (tcall j 1 f.upd)

/-- `finalize` of the state, after `r4` bytes, to `scratch + oDig`. -/
def hFin : Prog isa := .seq (.block [.addi .r3 .r14 oSt, .addi .r5 .r14 oDig, .addi .r6 .r14 oW]) (tcall j 2 f.fin)

/-- For a given salt length: `H' = Hash(M')`, `8 + hLen + salt_len` bytes, to
`scratch + oDig`. -/
def hashFixed : Prog isa :=
  .seq (hInit f j) (.seq (.block [.li .r4 0, .addi .r5 .r14 oY, .addi .r6 .r19 (8 + H.D)]) (.seq (hUpd f j)
    (.seq (.block [.addi .r4 .r19 (8 + H.D)]) (hFin f j))))

/-! ## `ctHash`: hashing `M'` of a secret length -/

/-- `ℓ = 8 + hLen + sLen` into `r29`, and `nbm = ⌊(8 + hLen + dbLen - 1 +
L) / B⌋ + 1` into `r28`. -/
def ctLens : List Instr :=
  [.addi .r29 .r25 (8 + H.D), .addi .r28 .r21 (8 + H.D - 1 + P.L), .lsr .d .r28 .r28 (lg P), .addi .r28 .r28 1]

/-- In `d`, all ones if `a = b`, zero if not (`r12` is written). -/
def eqMask (d a b : Reg) : List Instr :=
  [.logic .xor d a b, .subi d d 1, .lsr .d d d 63, .li .r12 0, .sub d .r12 d]

/-- `0x80` ORed into byte `i` of `M'` under the mask of `i = ℓ`, for each of
its `nbm B` bytes. -/
def pad80 : Prog isa :=
  .seq (.block [.addi .r4 .r14 oY, .lsl .r5 .r28 (lg P), .li .r6 0])
    (.loop (.block (eqMask .r7 .r6 .r29 ++ [.li .r8 0x80, .logic .and .r7 .r7 .r8, .lbz .r8 .r4 0,
      .logic .or .r8 .r8 .r7, .stb .r8 .r4 0, .addi .r4 .r4 1, .addi .r6 .r6 1, .subi .r5 .r5 1]))
      (.nonzero .d .r5))

/-- The length field of `ℓ` to `scratch + oLen` (`P.len` with `r26` placed so
that it writes there), and the last block's index `⌊(ℓ + L) / B⌋` to
`r27`. -/
def lenField : List Instr :=
  [.addi .r26 .r14 (oLen - (P.N + P.B - P.L))] ++ P.len ++ [.addi .r27 .r29 P.L, .lsr .d .r27 .r27 (lg P)]

/-- The length field ORed into the last `L` bytes of block `b` (`r6`) under
the mask of `b = ⌊(ℓ + L) / B⌋`, for every block. -/
def lenLoop : Prog isa :=
  .seq (.block [.addi .r4 .r14 (oY + P.B - P.L), .li .r6 0, mov .r9 .r28])
    (.loop (.seq (.block (eqMask .r7 .r6 .r27 ++ [.addi .r5 .r14 oLen, .li .r10 P.L]))
      (.seq (.loop (.block [.lbz .r8 .r5 0, .logic .and .r8 .r8 .r7, .lbz .r11 .r4 0, .logic .or .r11 .r11 .r8,
          .stb .r11 .r4 0, .addi .r4 .r4 1, .addi .r5 .r5 1, .subi .r10 .r10 1]) (.nonzero .d .r10))
        (.block [.addi .r4 .r4 (P.B - P.L), .addi .r6 .r6 1, .subi .r9 .r9 1])))
      (.nonzero .d .r9))

/-- The arguments of the compression function: the hash value at
`scratch + oSt`, block `b` (`r26`) of `M'`, one block, the working space. -/
def compArgs : List Instr :=
  [.addi .r3 .r14 oSt, .lsl .r4 .r26 (lg P), .add .r4 .r4 .r14, .addi .r4 .r4 oY, .li .r5 1, .addi .r6 .r14 oW]

/-- The hash value copied from `scratch + oSt` to `scratch + oSel` under the
mask of `b = ⌊(ℓ + L) / B⌋` (`r26`, `r27`). -/
def selHash : Prog isa :=
  .seq (.block (eqMask .r3 .r26 .r27 ++ [.addi .r4 .r14 oSt, .addi .r5 .r14 oSel, .li .r6 P.N]))
    (.loop (.block [.lbz .r7 .r4 0, .lbz .r8 .r5 0, .logic .xor .r7 .r7 .r8, .logic .and .r7 .r7 .r3,
      .logic .xor .r8 .r8 .r7, .stb .r8 .r5 0, .addi .r4 .r4 1, .addi .r5 .r5 1, .subi .r6 .r6 1])
      (.nonzero .d .r6))

/-- Every block compressed (`r26` the block, `r28` the blocks left), the last
one's hash value selected. -/
def compLoop : Prog isa :=
  .seq (.block [.li .r26 0])
    (.loop (.seq (.block (compArgs P)) (.seq (tcall j 3 f.comp)
      (.seq (selHash P) (.block [.addi .r26 .r26 1, .subi .r28 .r28 1])))) (.nonzero .d .r28))

/-- The digest of the selected hash value to `scratch + oDig`, by the
table's function 4 (`digest(value = r3, out = r4)`). -/
def digestOut : Prog isa := .seq (.block [.addi .r3 .r14 oSel, .addi .r4 .r14 oDig]) (tcall j 4 f.dig)

/-- The digest of the first `ℓ` bytes of `M'`, padded in `nbm` blocks, to
`scratch + oDig`, without revealing `ℓ`. -/
def ctHash : Prog isa :=
  .seq (.block (ctLens H P)) (.seq (hInit f j) (.seq (pad80 P) (.seq (.block (lenField P)) (.seq (lenLoop P)
    (.seq (compLoop P f j) (digestOut f j))))))

/-! ## The result -/

/-- The accumulator ORed with `H' ⊕ H` (`H'` at `scratch + o`), and 1 if it
is zero. -/
def cmpH (o : Nat) : Prog isa :=
  .seq (.block [.add .r4 .r14 .r17, .add .r4 .r4 .r21, .addi .r5 .r14 o, .li .r6 H.D])
    (.seq (.loop (.block [.lbz .r7 .r4 0, .lbz .r8 .r5 0, .logic .xor .r7 .r7 .r8, .logic .or .r24 .r24 .r7,
        .addi .r4 .r4 1, .addi .r5 .r5 1, .subi .r6 .r6 1]) (.nonzero .d .r6))
      (.block [.subi .r3 .r24 1, .lsr .d .r3 .r3 63]))

/-- The salt's hash and the result: by the public salt-length mode. -/
def finish : Prog isa :=
  .ite (.zero .d .r20)
    (.seq (mPrefix H 8) (.seq (copySalt H) (.seq (hashFixed H f hArg) (cmpH H oDig))))
    (.seq (mPrefix H 2048) (.seq (copyDb H) (.seq (shift H) (.seq (ctHash H P f hArg) (cmpH H oDig)))))

/-! ## The function -/

/-- After the checks. -/
def verifyMain : Prog isa :=
  .seq (.block pubArgs) (.seq Impl.RsaPkcs1Sig.PPC64LE.pubCall (.seq (.block acc0)
  (.seq (.block (dbArgs H)) (.seq (mgfXorT g gArg) (.seq (.block clearTop) (.seq scan
  (.seq (.block posCheck) (.seq lenCheck (finish H P f)))))))))

/-- The checks, then `verifyMain`. -/
def checks : Prog isa :=
  .ite (.zero .d .r9) fail
    (.seq (.block (chkEm H)) (.ite (.nonzero .d .r3) fail
      (.seq expLen (.seq (.block (chkSalt H)) (.ite (.nonzero .d .r3) fail (verifyMain H P f g))))))

/-- The frame's body, for the hash function's sizes. -/
def body : Prog isa :=
  .seq (.block (Impl.RsaOaep.PPC64LE.save ++ prologue H)) (.seq (checks H P f g) (.block Impl.RsaOaep.PPC64LE.restore))

/-- The index of the table `hash`'s hash function (its word 5) to `r11`,
then the frame's body for its sizes. -/
def verifyBody : Prog isa :=
  .seq (.block (tword .r11 hArg 5)) (byIdx (fun i => body (shapeOf i).1 (shapeOf i).2 f g) idxs)

/-- `vg_rsa_pss_verify_precomputed`, with the hash function the table that
is its stack argument 6 (`hash`) and MGF1's the table that is its stack
argument 7 (`mgf1`). -/
def verifyPrecomputed : Prog isa :=
  .frame (.alloc Impl.RsaOaep.PPC64LE.frameBytes) (verifyBody f g) (.free Impl.RsaOaep.PPC64LE.frameBytes)

end VG.Impl.RsaPss.PPC64LE
