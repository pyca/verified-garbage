module

public import VerifiedGarbage.Impl.Camellia.X86_64.Ecb
public import VerifiedGarbage.Impl.Camellia.KeyOrder
public import VerifiedGarbage.Spec.Camellia

/-!
# Camellia's batches under prepared subkeys, on x86-64

`vg_camellia_crypt_prepared` (`Proof/Camellia/Prepared.lean`): ECB's eight
blocks (`Ecb.lean`) as a function of the working space, for the modes,
which call it (`Ctr.lean`).

`cryptPrepared(rounds = rdi, ws = rsi, ws_len = rdx)` moves `ws` to `sb`,
saves the callee-saved registers in their slots (371–376), stores the
address of the postwhitening's entry for that many rounds in its slot
(368), and transforms the eight blocks of the tail buffer (`crypt8`) under
the table and the masks, then restores the registers.

The working space is ECB's 401 slots (`slots`). The masks and the table are
what `vg_camellia_crypt_prepared` reads (`layout`): each plane of a subkey
is a 64-bit word, bit `8 c + b` of plane `j` being bit `j` of byte
`bytePos c` of the subkey (`keyPlane`), for every block `b`.

The modes build the table themselves, ECB's key setup inline in their
core's `prepare`: its loop stores through a pointer that the analysis of
constant time cannot place, which would leave it nothing known of the
working space after a call.
-/

@[expose] public section

namespace VG.Impl.Camellia.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64

/-- `vg_camellia_crypt_prepared`: the eight blocks of the tail buffer. -/
def cryptPrepared : Prog isa :=
  .seq (.block ([movR sb .rsi] ++ saveRegs ++ ([.alu .cmp .rdi (.imm 18)] : List Instr)))
    (.seq (.ite .e (.block (endAddr 3)) (.block (endAddr 4)))
      (.seq (.block ([st endSlot .rdi] ++ tailAddr .rdx)) (.seq crypt8 (.block restoreRegs))))

/-! ## The layout -/

/-- The direction of the specification. -/
def ofSpecDir : Spec.Camellia.Direction → Dir
  | .encrypt => .encrypt
  | .decrypt => .decrypt

/-- The schedule's word in the table's entry `e`, for `g` groups of six
rounds and the words `w` in the order encryption uses them: the stored
order for encryption; for decryption `kw3, kw4`, the words between `kw2`
and `kw3` from the last back to the first, then `kw1, kw2` (as `keys`). -/
def keyEntry (w : List (BitVec 64)) (g : Nat) : Dir → Nat → BitVec 64
  | .encrypt, e => w.getD e 0
  | .decrypt, e => w.getD (if e < 2 then 8 * g + e else if e < 8 * g then 8 * g + 1 - e else e - 8 * g) 0

/-- The word of slot `k` of the working space that the key setup writes
for `rounds` rounds: a mask of the layers, or plane `(k - keySlot) % 8` of
the table's entry. -/
def preparedWord (rounds : Nat) (w : List (BitVec 64)) (d : Dir) (k : Nat) : BitVec 64 :=
  if k < keySlot then (layerMasks.find? (·.1 = k)).elim 0 (·.2)
  else keyPlane (keyEntry w (rounds / 6) d ((k - keySlot) / 8)) ((k - keySlot) % 8)

/-! ## The call -/

/-- A call of `vg_camellia_crypt_prepared` on the working space at `sb`, of
`slots` words, for the number of rounds in `rdi`. The modes' data pointer
and blocks left (`rdx`, `r8`) and the number of rounds are kept in
`r12`–`r14`, which the function restores; it leaves the working space's
address in `sb`. -/
def cryptCall : Prog isa :=
  .seq (.block [movR .r12 .rdx, movR .r13 .r8, movR .r14 .rdi, movR .rsi sb,
      .movImm64 .rdx (BitVec.ofNat 64 slots)])
    (.seq (.call "vg_camellia_crypt_prepared" cryptPrepared)
      (.block [movR .rdx .r12, movR .r8 .r13, movR .rdi .r14]))

end VG.Impl.Camellia.X86_64
