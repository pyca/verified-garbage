module

public import VerifiedGarbage.Impl.AesGcmSiv.AArch64
public import VerifiedGarbage.Impl.Gcm.AArch64.Stitch
public import VerifiedGarbage.Impl.Gcm.AArch64.Pmull

/-!
# AES-GCM-SIV on AArch64: counter mode and POLYVAL eight blocks at a time

`vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open` (`Impl.AesGcmSiv.AArch64`)
for CPUs with FEAT_AES, FEAT_PMULL and FEAT_SHA3, with the loops of AES-GCM
(`Impl.Gcm.AArch64.Stitch`) on the whole batches of eight blocks of the data,
`128 ⌊len / 128⌋` bytes; the additional data and the rest of the data go as
in `Impl.AesGcmSiv.AArch64`.

* POLYVAL is GHASH on the blocks with their bytes reversed
  (`Proof.GcmSiv.Polyval`), and a block with its bytes reversed, as AES-GCM's
  loops load it (`ldr q` and `rev64`), is the block as it is in memory with its
  halves swapped: `ghPart` loads it with `ldr q` and `ext #8` (`ld`) and
  multiplies it as AES-GCM's does. The table of keys is computed from GHASH's
  key at `W + 64` as `vg_ghash_aes` computes its powers (`tblBuild`), into
  `W + tblO`.
* Counter mode increments the first 4 bytes of the counter block at `W + 96`
  as a little-endian number: `aesPart`'s counter blocks put `w10 + j` in its
  first lane (`ctr1`), without `rev32`, and the counter is stored back after
  the loops. The rounds read the encryption key's schedule from `x21`, set to
  `W + 240` (the key-generating key's, which `x21` held, is no longer needed).
* `seal` hashes the batches (`ghLoop`), then encrypts them (`ctrLoop`) once
  the tag is known; `open` decrypts batch `i + 1` while it hashes batch `i`,
  decrypted the iteration before (`openLoop`, AES-GCM's `encLoop`): POLYVAL is
  of the plaintext.

`W` is that of `Impl.AesGcmSiv.AArch64`, 192 bytes longer for the table: 4000
bytes.
-/

@[expose] public section

namespace VG.Impl.AesGcmSiv.AArch64.Stitch

open VG.AArch64
open VG.Impl.AesGcmSiv.AArch64
open VG.Impl.Gcm.AArch64.Stitch (K P Y C HI LO MID A₁ A₂ S₁ S₂ KP T U X₁ X₂ breg rnd lastRnd pa pk pb pl
  addFirst addNext reduce fuse stores byRounds)
open VG.Impl.AesGcm.AArch64 (Callees mov ptr imm restore)

/-- Where the table of keys is in `W`. -/
def tblO : Nat := 3808

/-- The size of `W`. -/
def wSize : Nat := 4000

/-! ## The table of keys

At `W + tblO`, as AES-GCM's at `W + 512` (`Impl.Gcm.AArch64.Stitch.tbl`):
`H'ᵏ` with its halves swapped for `k = 1 … 8`, then the sums of the halves
of the powers of each pair of `ghPart`. -/

/-- Where `H'ᵏ`, its halves swapped, is in the table. -/
def sOff (k : Nat) : Nat := tblO + 16 * (k - 1)

/-- Where the keys of pair `p` are in the table. -/
def kOff (p : Nat) : Nat := tblO + 128 + 16 * p

open VG.Impl.Gcm.AArch64.Pmull (tReg sReg powers loadRev consts mul) in
/-- `H'` from GHASH's key at `W + 64` (as `vg_ghash_aes`'s prologue computes
it), `H'²` to `H'⁸`, and the table. -/
def tblBuild : List Instr :=
  loadRev Impl.Gcm.AArch64.Pmull.A .x19 hO ++ consts ++
    mul (sReg 1) Impl.Gcm.AArch64.Pmull.A (sReg 2) (tReg 2) ++
    ([.vop (.ext (tReg 1) (sReg 1) (sReg 1) 8)] : List Instr) ++ powers ++
  (List.range 8).flatMap (fun k => [.strq (sReg (k + 1)) .x19 (sOff (k + 1))]) ++
  (List.range 4).flatMap fun p =>
    [.vop (.logic .eor .v2 (sReg (pk p)) (tReg (pk p))),
     .vop (.logic .eor .v3 (sReg (pl p)) (tReg (pl p))),
     .vop (.ext .v4 .v2 .v3 8), .strq .v4 .x19 (kOff p)]

/-! ## Counter mode -/

/-- Counter block `j` into its register: the counter block at `W + 96` with
`w10 + j` in its first 4 bytes. -/
def ctr1 (j : Nat) : List Instr :=
  [.addImm .w .x12 .x10 j, .ldrq (breg j) .x19 cbO, .vop (.ins .s4 (breg j) 0 .x12)]

/-- Eight blocks of counter mode, of the data at `x9 + o`, into `v0`–`v7`. -/
def aesPart (nr o : Nat) : List Instr :=
  (List.range 8).flatMap ctr1 ++ (List.range (nr - 1)).flatMap rnd ++ lastRnd nr o ++
    ([.addImm .w .x10 .x10 8] : List Instr)

/-! ## POLYVAL -/

/-- Block `j` of the eight at `x9` into `a`, its halves swapped. -/
def ld (a : VReg) (j : Nat) : List Instr := [.ldrq a .x9 (16 * j), .vop (.ext a a a 8)]

/-- Pair `p`'s products (`Impl.Gcm.AArch64.Stitch.pair`, with `ld`). -/
def pair (p : Nat) (a k b l : Nat) (y : Bool) : List Instr :=
  ld A₁ a ++ ld A₂ b ++ (if y then [.vop (.logic .eor A₂ A₂ Y)] else []) ++
  [.ldrq S₁ .x19 (sOff k), .ldrq S₂ .x19 (sOff l), .ldrq KP .x19 (kOff p),
   .vop (.perm .trn1 .d2 T A₁ A₂), .vop (.perm .trn2 .d2 U A₁ A₂), .vop (.logic .eor T T U),
   .vop (.pmull false X₁ A₁ S₁), .vop (.pmull true A₁ A₁ S₁),
   .vop (.pmull false X₂ A₂ S₂), .vop (.pmull true A₂ A₂ S₂),
   .vop (.pmull false U T KP), .vop (.pmull true T T KP)]

/-- POLYVAL of the eight blocks at `x9`, into `Y`. -/
def ghPart : List Instr :=
  pair 0 1 7 2 6 false ++ addFirst ++ pair 1 3 5 4 4 false ++ addNext ++ pair 2 5 3 6 2 false ++ addNext ++
    pair 3 7 1 0 8 true ++ addNext ++ reduce

/-! ## The loops -/

/-- `aesPart nr o` woven with `ghPart`, each `aese` next to its `aesmc`. -/
def parts (nr o : Nat) : List Instr :=
  VG.Impl.Weave.weaveG (fuse (aesPart nr o)) (ghPart.map fun x => [x])

/-- Past a batch: the pointer and the count. -/
def adv : List Instr := [.addImm .x .x9 .x9 128, .subImm .x .x11 .x11 1]

/-- POLYVAL of the `x11 ≥ 1` batches at `x9`. -/
def ghLoop : Prog isa := .loop (.block (ghPart ++ adv)) (.nonzero .x .x11)

/-- Counter mode of the `x11 ≥ 1` batches at `x9`. -/
def ctrLoop (nr : Nat) : Prog isa := .loop (.block (aesPart nr 0 ++ stores 0 ++ adv)) (.nonzero .x .x11)

/-- `open`'s loop over the `x11 ≥ 1` batches at `x9`: the first decrypted,
then each next one decrypted while the one before is hashed, then the last
hashed. -/
def openLoop (nr : Nat) : Prog isa :=
  .seq (.block (aesPart nr 0 ++ stores 0 ++ ([.subImm .x .x11 .x11 1] : List Instr)))
    (.seq (.ite (.zero .x .x11) (.block [])
        (.loop (.block (parts nr 128 ++ stores 128 ++ adv)) (.nonzero .x .x11)))
      (.block (ghPart ++ ([.addImm .x .x9 .x9 128] : List Instr))))

/-- The batches at `x25`: `x9` the pointer, `x11` their number. -/
def batches : List Instr := [mov .x9 .x25, .lsr .x .x11 .x26 7]

/-- The reduction constant in `C` and `Y` from `W + 80`, as loaded. -/
def ghSetup : List Instr :=
  [.movz .x .x12 0xc200 3, .vop (.dup .d2 C .x12), .ldrq Y .x19 yO, .vop (.rev .rev64b Y Y)]

/-- `Y` stored back to `W + 80`. -/
def ghFinish : List Instr := [.vop (.rev .rev64b Y Y), .strq Y .x19 yO]

/-- The counter (`w10`) from the counter block at `W + 96`, and the
encryption key's schedule in `x21`. -/
def ctrSetup : List Instr := [.ldr .w .x10 .x19 cbO, ptr .x21 .x19 skO]

/-- The counter stored back to `W + 96`. -/
def ctrFinish : List Instr := [.str .w .x10 .x19 cbO]

/-- `x27` and `x28` the data past its batches. -/
def rest : List Instr := [.lsr .x .x9 .x26 7, .lsl .x .x9 .x9 7, .add .x .x27 .x25 .x9, .sub .x .x28 .x26 .x9]

/-- `b` if the data has a batch. -/
def ifBatch (b : Prog isa) : Prog isa :=
  .seq (.block [.lsr .x .x9 .x26 7]) (.ite (.zero .x .x9) (.block []) b)

variable (c : Callees)

/-- POLYVAL of the data: its batches by `ghLoop`, the rest by `absorb`. -/
def polyData : Prog isa :=
  .seq (ifBatch (.seq (.block (tblBuild ++ batches ++ ghSetup)) (.seq ghLoop (.block ghFinish))))
  (.seq (.block rest) (absorb c))

/-- POLYVAL of the additional data, the data and the lengths, and the tag
input (`Impl.AesGcmSiv.AArch64.polyval`, with `polyData`). -/
def polyval : Prog isa :=
  .seq (.block [mov .x27 .x23, mov .x28 .x24])
  (.seq (absorb c)
  (.seq (polyData c)
  (.seq (lens c) (.block tagIn))))

/-- The rest of the data, past its batches, from the counter block, by
`crypt`'s blocks. -/
def cryptRest : Prog isa :=
  .seq (.block (rest ++ [.lsr .x .x9 .x28 4]))
  (.seq (.ite (.zero .x .x9) (.block []) (.loop (cryptBlock c) (.nonzero .x .x9)))
    (.ite (.zero .x .x28) (.block []) (cryptTail c)))

/-- The data encrypted in place: the batches by `ctrLoop`, the rest by
`crypt`'s blocks. -/
def crypt : Prog isa :=
  .seq (.block cryptHead)
  (.seq (ifBatch (.seq (.block (ctrSetup ++ batches)) (.seq (byRounds ctrLoop) (.block ctrFinish))))
    (cryptRest c))

/-- The data decrypted in place and its POLYVAL: the batches by `openLoop`,
the rest decrypted by `crypt`'s blocks and absorbed. -/
def openData : Prog isa :=
  .seq (.block cryptHead)
  (.seq (ifBatch (.seq (.block (tblBuild ++ ctrSetup ++ batches ++ ghSetup))
      (.seq (byRounds openLoop) (.block (ctrFinish ++ ghFinish)))))
  (.seq (cryptRest c) (.seq (.block rest) (absorb c))))

/-- `vg_aes_gcm_siv_seal`. -/
def «seal» : Prog isa :=
  .seq (.block entry) (.seq (keys c) (.seq (polyval c) (.seq (tag c tagO) (.seq (crypt c)
    (.block (tagOut ++ restore))))))

/-- `vg_aes_gcm_siv_open`: the additional data absorbed before the data is
decrypted and absorbed. -/
def «open» : Prog isa :=
  .seq (.block entry) (.seq (.block recv) (.seq (keys c)
  (.seq (.block [mov .x27 .x23, mov .x28 .x24]) (.seq (absorb c)
  (.seq (openData c)
  (.seq (lens c) (.seq (.block tagIn) (.seq (tag c bO)
    (.seq (.block cmp) (.seq mask (.block ([mov .x0 .x27] ++ restore))))))))))))

end VG.Impl.AesGcmSiv.AArch64.Stitch
