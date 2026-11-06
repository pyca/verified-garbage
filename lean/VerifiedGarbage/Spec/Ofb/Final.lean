module

public import VerifiedGarbage.Spec.Ofb.Contract

/-!
# OFB of a message of any length, and AES-OFB's final function

**Trusted** (as every file in `Spec/`). OFB (`Spec/Ofb.lean`) of a message
whose length need not be a multiple of the block size `b`, and the contract
of `vg_aes_ofb_final`, which takes a message's last piece, of any length,
and handles its partial last block itself; those of the other block ciphers
are in `Spec/<Cipher>/OfbFinal.lean`. Existing contracts are unchanged.

NIST SP 800-38A §6.4 defines OFB for a message of `(n − 1) b + u` bytes,
`1 ≤ u ≤ b` (§5.2): the last block, of `u` bytes, is XORed with the most
significant `u` bytes of the last output block,
```
Cₙ* = Pₙ* ⊕ MSB_u(Oₙ)       (decryption: Pₙ* = Cₙ* ⊕ MSB_u(Oₙ)),
```
"the remaining b-u bits of the last output block are discarded". So the
message is XORed with the first bytes of `O₁ ‖ … ‖ Oₙ` (`cryptFinal`, as
`aesOfb` for AES).

A final function leaves in `iv` the last output block used, `Oₙ` (`Ofb.next`
after `n` blocks, whole or partial): the block a further call continues from
when the piece is whole blocks, as the whole-block functions do. After a
partial last block the message must end, since the rest of `Oₙ` is
discarded; `Oₙ` is keystream, which the caller wipes.
-/

@[expose] public section

namespace VG.Spec.Ofb

open Cbc (Cipher xor)

/-- The number `n` of blocks, the last possibly partial, of a message of
`len` bytes in blocks of `b` bytes: `⌈len / b⌉`. -/
def blockCount (b len : Nat) : Nat := (len + b - 1) / b

/-- §6.4, OFB Encryption (and Decryption, which is the same) of `x`, of any
length, in blocks of `b` bytes, from `IV`: `x` XORed with the output blocks
`O₁ … Oₙ`, the last truncated to what is left of `x` (`xor` stops at the
shorter operand), `Cₙ* = Pₙ* ⊕ MSB_u(Oₙ)`. -/
def cryptFinal (ciph : Cipher) (b : Nat) (iv x : List Byte) : List Byte :=
  xor x (outputs ciph iv (blockCount b x.length)).flatten

/-- The final function's postcondition, for `CIPH_K` `ciph` on blocks of
`b` bytes: the `len` bytes at `data` replaced by their OFB encryption or
decryption (`cryptFinal`) from the block at `iv`, and that block by the
last output block used (`next` after `⌈len / b⌉` blocks; unchanged if
`len = 0`). -/
def CryptFinal (ciph : Cipher) (b : Nat) (m m' : Mem) (iv data : Addr) (len : Nat) :
    Prop :=
  let v := Aes.bytesAt m iv b
  Aes.bytesAt m' data len = cryptFinal ciph b v (Aes.bytesAt m data len) ∧
    Aes.bytesAt m' iv b = next ciph v (blockCount b len)

/-! ## With AES -/

/-- `vg_aes_ofb_final(schedule: *const [u8; 240], rounds: usize, iv: *mut [u8; 16], data: *mut u8, len: usize, scratch: *mut [u64; 272])`:
the whole-block function's signature (`aesSig`), with the data `len` bytes.
`rounds` is public; `scratch` is working space. -/
def aesFinalSig : Sig where
  params := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
    ("iv", .array true .u8 16), ("data", .slice true .u8 "len"),
    ("scratch", .array true .u64 272)]

/-- For `rounds` of 10, 12 or 14, and every AES key `K` whose key schedule
is at `schedule` with `rounds` rounds (`Aes.KeySchedule`): replaces the
`len` bytes at `data` with their OFB encryption or decryption by AES with
`K`, a partial last block included, from the block at `iv`, and that block
with the last output block used (`CryptFinal`). -/
def aesFinalContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesFinalSig.contract A
    (pre := fun _schedule rounds _iv _data _len _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds iv data len _scratch m m' _ =>
      ∀ key, Aes.KeySchedule m schedule rounds.toNat key →
        CryptFinal (Cbc.aes key) 16 m m' iv data len.toNat)
    (stack := stack)

/-- `vg_aes_ofb_final` on every target. -/
def aesFinalApi : Api where
  module := "aes_ofb"
  name := "vg_aes_ofb_final"
  sig := aesFinalSig
  contracts := some fun A stack => aesFinalContract A stack
  summary := "AES-OFB encryption or decryption (NIST SP 800-38A §6.4) of the last piece of a \
    message, of any length, in place: XORs the `len` bytes at `data` with the output blocks \
    `Oⱼ = CIPH_K(Oⱼ₋₁)`, where `O₀` is the block at `*iv`, a partial last block `Pₙ*` of `u` \
    bytes with `MSB_u(Oₙ)`, and replaces `*iv` with the last output block used, `Oₙ` \
    (leaving it unchanged if `len = 0`): so that a further call continues the message if \
    `len` is a multiple of 16, and otherwise keystream, to be wiped, after which the message \
    must end. `CIPH_K` is AES (FIPS 197) with `rounds` rounds and the key schedule in the \
    first `16 * (rounds + 1)` bytes of `*schedule`, as `vg_aes_expand_key` writes it.\n\n\
    Contract: `VG.Spec.Ofb.aesFinalContract`. Constant time: only the pointers, `rounds` and \
    `len` may affect timing, not the key schedule, the chaining value or the data."
  safety := Cbc.aesSafety

end VG.Spec.Ofb
