module

public import VerifiedGarbage.Spec.Ctr.Contract

/-!
# CTR of a message of any length, and AES-CTR's final function

**Trusted** (as every file in `Spec/`). CTR (`Spec/Ctr.lean`) of a message
whose length need not be a multiple of 16 bytes, and the contract of
`vg_aes_ctr_final`, which takes a message's last piece, of any length, and
handles its partial last block itself; those of Camellia and SM4 are in
`Spec/<Cipher>/CtrFinal.lean`. Existing contracts are unchanged.

NIST SP 800-38A §6.5 defines CTR for a message of `(n − 1) b + u` bytes,
`1 ≤ u ≤ b` (§5.2): the last block, of `u` bytes, is XORed with the most
significant `u` bytes of the last output block,
```
Cₙ* = Pₙ* ⊕ MSB_u(Oₙ)       (decryption: Pₙ* = Cₙ* ⊕ MSB_u(Oₙ)),
```
"the remaining b-u bits of the last output block are discarded". So the
message is XORed with the first bytes of `O₁ ‖ … ‖ Oₙ`, `Oⱼ = CIPH_K(Tⱼ)`
(`cryptFinal`, as `aesCtr` for AES).

A final function leaves in `ctr` the counter block after the last one used,
`Tₙ₊₁` (`Ctr.next` after `n` blocks, whole or partial): the block a further
call continues from when the piece is whole blocks, as the whole-block
functions do. After a partial last block the message must end, since the
rest of `Oₙ` is discarded.
-/

@[expose] public section

namespace VG.Spec.Ctr

open Cbc (Cipher xor)

/-- The number `n` of 16-byte blocks, the last possibly partial, of a
message of `len` bytes: `⌈len / 16⌉`. -/
def blockCount (len : Nat) : Nat := (len + 15) / 16

/-- §6.5, CTR Encryption (and Decryption, which is the same) of `x`, of any
length, from the counter block `T₁ = t`: `x` XORed with the output blocks
`Oⱼ = CIPH_K(Tⱼ)`, the last truncated to what is left of `x` (`xor` stops
at the shorter operand), `Cₙ* = Pₙ* ⊕ MSB_u(Oₙ)`. -/
def cryptFinal (ciph : Cipher) (t x : List Byte) : List Byte :=
  xor x ((counters t (blockCount x.length)).map ciph).flatten

/-- The final function's postcondition, for `CIPH_K` `ciph`: the `len`
bytes at `data` replaced by their CTR encryption or decryption
(`cryptFinal`) from the counter block at `ctr`, and that block by the one
after the last used, `Tₙ₊₁` (`next` after `⌈len / 16⌉` blocks; unchanged
if `len = 0`). -/
def CryptFinal (ciph : Cipher) (m m' : Mem) (ctr data : Addr) (len : Nat) : Prop :=
  let t := Aes.bytesAt m ctr 16
  Aes.bytesAt m' data len = cryptFinal ciph t (Aes.bytesAt m data len) ∧
    Aes.bytesAt m' ctr 16 = next t (blockCount len)

/-! ## With AES -/

/-- `vg_aes_ctr_final(schedule: *const [u8; 240], rounds: usize, ctr: *mut [u8; 16], data: *mut u8, len: usize, scratch: *mut [u64; 272])`:
the whole-block function's signature (`aesSig`), with the data `len` bytes.
`rounds` is public; `scratch` is working space. -/
def aesFinalSig : Sig where
  params := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
    ("ctr", .array true .u8 16), ("data", .slice true .u8 "len"),
    ("scratch", .array true .u64 272)]

/-- For `rounds` of 10, 12 or 14, and every AES key `K` whose key schedule
is at `schedule` with `rounds` rounds (`Aes.KeySchedule`): replaces the
`len` bytes at `data` with their CTR encryption or decryption by AES with
`K`, a partial last block included, from the counter block at `ctr`, and
that block with `Tₙ₊₁` (`CryptFinal`). Its timing may depend on the
counter block's last four bytes, as `vg_aes_ctr`'s (`ctrLeak`). -/
def aesFinalContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesFinalSig.contract A
    (pre := fun _schedule rounds _ctr _data _len _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds ctr data len _scratch m m' _ =>
      ∀ key, Aes.KeySchedule m schedule rounds.toNat key →
        CryptFinal (Cbc.aes key) m m' ctr data len.toNat)
    (leak := some fun _schedule _rounds ctr _data _len _scratch m => ctrLeak m ctr)
    (stack := stack)

/-- `vg_aes_ctr_final` on every target. -/
def aesFinalApi : Api where
  module := "aes_ctr"
  name := "vg_aes_ctr_final"
  sig := aesFinalSig
  contracts := some fun A stack => aesFinalContract A stack
  summary := "AES-CTR encryption or decryption (NIST SP 800-38A §6.5) of the last piece of a \
    message, of any length, in place: XORs the `len` bytes at `data` with the output blocks \
    `Oⱼ = CIPH_K(Tⱼ)`, where `T₁` is the block at `*ctr` and `Tⱼ₊₁ = Tⱼ + 1 mod 2¹²⁸` \
    (Appendix B.1's standard incrementing function on the whole block, read as a big-endian \
    integer), a partial last block `Pₙ*` of `u` bytes with `MSB_u(Oₙ)`, and replaces `*ctr` \
    with `Tₙ₊₁` (leaving it unchanged if `len = 0`), so that a further call continues the \
    message if `len` is a multiple of 16; after a partial last block the message must end. \
    `CIPH_K` is AES (FIPS 197) with `rounds` rounds and the key schedule in the first \
    `16 * (rounds + 1)` bytes of `*schedule`, as `vg_aes_expand_key` writes it.\n\n\
    Contract: `VG.Spec.Ctr.aesFinalContract`. Constant time: only the pointers, `rounds`, \
    `len` and the last four bytes of `*ctr` (the 32-bit counter, public in OpenSSL, BoringSSL \
    and AWS-LC, which split the blocks where it wraps) may affect timing, not the key \
    schedule, the rest of the counter block or the data."
  safety := Cbc.aesSafety

end VG.Spec.Ctr
