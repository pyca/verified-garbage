module

public import VerifiedGarbage.Impl.Camellia.AArch64.Serial.Core
public import VerifiedGarbage.Spec.Camellia.Prepared

/-!
# The serial Camellia core as two functions, and the modes' calls of them

`vg_camellia_prepare_encrypt_keys` and `vg_camellia_encrypt_prepared`
(`Proof/Camellia/PreparedEncrypt.lean`): the serial core's two halves
(`Core.lean`) as functions of the working space, which the feedback modes
and CBC encryption call (`Fb.lean`) rather than each inlining the core.

* `prepareEncrypt(schedule = x0, rounds = x1, ws = x2, ws_len = x3)` writes
  the S-box's table (bytes 0–255) and copies the schedule's 272 bytes
  after it (256–527), keeping `x21`, which both write, in `x9`.
* `encryptPrepared(rounds = x0, ws = x1, ws_len = x2)` encrypts the block
  at byte 768 under them, with the S-box in vector registers and the
  Feistel halves in scalar registers.

Neither writes a register the AAPCS64 preserves, so the modes keep their
own state across the calls in those registers: the IV's address (`x19`),
the data's address and the blocks left (`x23`, `x24`), the return address
(`x20`), `sb` (`x22`) and the number of rounds (`x26`). The working space
is the serial core's 418 slots (`layout`).
-/

@[expose] public section

namespace VG.Impl.Camellia.AArch64.Serial

open VG.AArch64 VG.Impl.Aes.AArch64

/-- `vg_camellia_prepare_encrypt_keys`. -/
def prepareEncrypt : Prog isa :=
  .seq (.block [movR sb .x2, movR .x9 .x21]) (.seq core.prepare (.block [movR .x21 .x9]))

/-- `vg_camellia_encrypt_prepared`. -/
def encryptPrepared : Prog isa :=
  .seq (.block [movR sb .x1, movR .x1 .x0]) core.crypt

/-! ## The layout -/

/-- The S-box's table, then the schedule's words as stored (the most
significant byte first), then the block at byte 768. -/
def layout : Spec.Camellia.Prepared.Layout where
  table rounds := [(0, 256), (256, 8 * Spec.Camellia.scheduleLength rounds)]
  encode _ w _ i :=
    if i < 256 then Spec.Camellia.sbox1Table.getD i 0
    else (Spec.Camellia.wordBytes (w.getD ((i - 256) / 8) 0)).getD ((i - 256) % 8) 0
  buf := 768
  blocks := 1
  prepScratch := [(0, 528)]
  cryptScratch := [(768, 16)]
  size := 8 * core.total

/-! ## The calls -/

/-- A call of `vg_camellia_prepare_encrypt_keys` with the schedule in `x0`
and the number of rounds in `x1` (and in `x26` after it), on the working
space at `sb`, of `core.total` words; `sb` stays in `x22`. -/
def prepareCall : Prog isa :=
  .seq (.block [movR .x20 .x30, movR .x22 sb, movR .x26 .x1, movR .x2 sb,
      .movz .x .x3 (BitVec.ofNat 16 core.total) 0])
    (.seq (.call "vg_camellia_prepare_encrypt_keys" prepareEncrypt)
      (.block [movR sb .x22, movR .x30 .x20]))

/-- A call of `vg_camellia_encrypt_prepared` for the number of rounds in
`x26`, on the working space at `sb`. -/
def cryptCall : Prog isa :=
  .seq (.block [movR .x20 .x30, movR .x0 .x26, movR .x1 sb, .movz .x .x2 (BitVec.ofNat 16 core.total) 0])
    (.seq (.call "vg_camellia_encrypt_prepared" encryptPrepared)
      (.block [movR sb .x22, movR .x30 .x20]))

/-- The serial core for the modes, calling the two functions. -/
def callCore : VG.Impl.Modes.AArch64.Core := { core with prepare := prepareCall, crypt := cryptCall }

end VG.Impl.Camellia.AArch64.Serial
