module

public import VerifiedGarbage.Impl.Sm4.AArch64.Fb
public import VerifiedGarbage.Impl.Sm4.AArch64.Serial.Core
public import VerifiedGarbage.Impl.Modes.AArch64.CbcChained

/-!
# SM4-CBC on AArch64

`cbcEncryptChained` and `cbcDecryptChained(schedule = x0, iv = x1,
data = x2, n = x3, scratch = x4)`: `vg_sm4_cbc_encrypt_chained` and
`vg_sm4_cbc_decrypt_chained`, the modes' generic CBC that updates the
chaining value (`Impl/Modes/AArch64/CbcChained.lean`). Decryption uses the
bitsliced core and transforms sixteen blocks at a time, but for a few
blocks, which go one at a time through `Serial.decCore`. Encryption uses
`Serial.Core`: one block under the raw schedule, with the S-box held in
vector registers. Both keep the IV address in `x19`.
-/

@[expose] public section

namespace VG.Impl.Sm4.AArch64

open VG.AArch64

/-- `vg_sm4_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := Serial.cbcEncryptChained

/-- `short` for fewer than seven blocks (`n`, which is public), `long`
otherwise: `(n + 1) / 8` is zero. (`n + 1` wraps only for an `n` no buffer
has; the two are the same function of every `n`.) A block through the
one-block core costs about a quarter of a batch of sixteen, after a fixed
cost of about a third. -/
def few7 (n : Reg) (short long : Prog isa) : Prog isa :=
  .seq (.block [.addImm .x .x13 n 1, .lsr .x .x13 .x13 3]) (.ite (.zero .x .x13) short long)

/-- `vg_sm4_cbc_decrypt_chained`: fewer than seven blocks one at a time,
otherwise sixteen at a time. -/
def cbcDecryptChained : Prog isa :=
  few7 .x3 (Serial.decCore.cbcDecryptChained ⟨.x1, .x2, .x3, .x4⟩)
    ((dirCore .decrypt).cbcDecryptChained ⟨.x1, .x2, .x3, .x4⟩)

end VG.Impl.Sm4.AArch64
