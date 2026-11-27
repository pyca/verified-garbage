module

public import VerifiedGarbage.Impl.AesCbc.Arm.Groups

/-!
# XTS-AES: ARMv7 implementation

`vg_aes_xts_encrypt(schedule = r0, rounds = r1, tweak = r2, data = r3, n, scratch)`
and `vg_aes_xts_decrypt` with the same arguments (the last two on the stack), composed of
calls of the verified `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks`, in
place: on groups of 4 and of 2 blocks (`xtsG`, `Impl/AesCbc/Arm/Groups.lean`),
whose tweaks are computed before the call, then on the blocks left one at a
time.

They are built from AES-CBC's pieces (`Impl/AesCbc/Arm.lean`), whose
arguments are the same: the registers saved in the scratch buffer and the
arguments kept in `r4` (schedule), `r5` (rounds), `r6` (the tweak), `r7`
(the next block), `r8` (blocks left) and `r10` (scratch). Each block left,
the tweak is XORed into the data block, which is enciphered (or deciphered)
in place, the tweak is XORed in again, and the tweak is multiplied by `α`
(`mulA`).

Only the pointers, `rounds` and `n` can affect timing: the only branches are
on `n`.
-/

@[expose] public section

namespace VG.Impl.AesXts.Arm

open VG.Arm
open VG.Impl.CmacAes.Arm (advance xor4)
open VG.Impl.AesCbc.Arm (wholeG xtsG groupLevels mulA encFrame decFrame callArgs)

/-- The tweak XORed into the data block, and the arguments of the call. -/
def pre : List Instr := xor4 .r7 .r6 .r7 0 0 0 ++ callArgs

/-- The tweak XORed in again, the tweak times `α`, and on to the next block. -/
def post : List Instr := xor4 .r7 .r6 .r7 0 0 0 ++ mulA ++ advance

def encrypt : Prog isa := wholeG encFrame xtsG groupLevels (.seq (.block pre) (.seq encFrame (.block post)))

def decrypt : Prog isa := wholeG decFrame xtsG groupLevels (.seq (.block pre) (.seq decFrame (.block post)))

end VG.Impl.AesXts.Arm
