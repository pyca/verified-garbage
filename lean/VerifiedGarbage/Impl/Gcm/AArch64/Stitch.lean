module

public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.Impl.Weave

/-!
# AES-GCM on AArch64: counter mode and GHASH interleaved

The loops that encrypt (or decrypt) and hash the text of AES-GCM eight
blocks at a time, inline in `seal` and `open` (`Impl/AesGcm/AArch64/Stitch.lean`),
for CPUs with FEAT_AES, FEAT_PMULL and FEAT_SHA3. They follow the structure
of the "unroll8" loops of OpenSSL and AWS-LC
(`aesv8-gcm-armv8-unroll8.pl`): the AES rounds of eight blocks woven with
the GHASH of eight others, so that the AES instructions (which Neoverse N2
issues to either vector pipe) fill the slots the `pmull` and `eor3`
instructions (which issue to one) leave.

* `aesPart nr o`: eight counter blocks (as `vg_aes_ctr32_aes` builds them,
  the counter in `w10`, from the counter block at `x20 + 48`) through the
  `nr` rounds, the round keys loaded from `x21` as they are used, and the
  last round `eor3`'d with the text blocks at `x9 + o`: the eight results in
  `v0`–`v7`. It uses `v30` (the round key) and `v31` (a text block).
* `ghPart`: GHASH of the eight blocks at `x9`, as `vg_ghash_aes` multiplies
  (`Impl.Gcm.AArch64.Pmull`), with Karatsuba's three `pmull`s a block: two
  blocks at a time, their sums `a₀ + a₁` packed into one register by
  `trn1`/`trn2` and multiplied by the matching sums of the keys' halves,
  packed the same way; the eight products added with `eor3` and reduced
  once. The keys are read from the table at `x19 + 512` (`tbl`), `Y` is in
  `v16` (as loaded) and the reduction constant in `v17`. It uses `v16`–`v29`.

The two parts use different registers and only read memory, so woven they
run as one and then the other (`Proof/Framework/Interleave.lean`). `seal`
encrypts batch `i + 1` while it hashes batch `i` (stored by the previous
iteration); `open` decrypts and hashes the same batch.
-/

@[expose] public section

namespace VG.Impl.Gcm.AArch64.Stitch

open VG.AArch64

/-! ## Registers -/

abbrev K : VReg := .v30
abbrev P : VReg := .v31
abbrev Y : VReg := .v16
abbrev C : VReg := .v17
abbrev HI : VReg := .v18
abbrev LO : VReg := .v19
abbrev MID : VReg := .v20
abbrev A₁ : VReg := .v21
abbrev A₂ : VReg := .v22
abbrev S₁ : VReg := .v23
abbrev S₂ : VReg := .v24
abbrev KP : VReg := .v25
abbrev T : VReg := .v26
abbrev U : VReg := .v27
abbrev X₁ : VReg := .v28
abbrev X₂ : VReg := .v29

/-- The register of block `j` of the eight AES states. -/
def breg : Nat → VReg
  | 0 => .v0 | 1 => .v1 | 2 => .v2 | 3 => .v3 | 4 => .v4 | 5 => .v5 | 6 => .v6 | _ => .v7

/-! ## The table of keys

At `x19 + 512`: `H'ᵏ` with its halves swapped for `k = 1 … 8` (`sOff k`),
then four registers' worth of the sums of the halves of the powers, two to a
register, in the order the pairs of `ghPart` use them (`kOff p`). -/

def tbl : Nat := 512

/-- Where `H'ᵏ`, its halves swapped, is in the table. -/
def sOff (k : Nat) : Nat := tbl + 16 * (k - 1)

/-- Where the keys of pair `p` are in the table. -/
def kOff (p : Nat) : Nat := tbl + 128 + 16 * p

/-! ## Counter mode -/

/-- Counter block `j` into its register (`vg_aes_ctr32_aes`'s `ctr1`). -/
def ctr1 (j : Nat) : List Instr :=
  [.addImm .w .x12 .x10 j, .rev32 .x12 .x12, .ldrq (breg j) .x20 48, .vop (.ins .s4 (breg j) 3 .x12)]

/-- A full round of the eight states with round key `r`. -/
def rnd (r : Nat) : List Instr :=
  .ldrq K .x21 (16 * r) :: (List.range 8).flatMap fun j => [.vop (.aese (breg j) K), .vop (.aesmc (breg j) (breg j))]

/-- The last two rounds, with round keys `nr − 1` and `nr`, and the text
blocks at `x9 + o` added. -/
def lastRnd (nr o : Nat) : List Instr :=
  .ldrq K .x21 (16 * (nr - 1)) :: (List.range 8).flatMap (fun j => [.vop (.aese (breg j) K)]) ++
  .ldrq K .x21 (16 * nr) ::
    (List.range 8).flatMap fun j => [.ldrq P .x9 (o + 16 * j), .vop (.eor3 (breg j) (breg j) P K)]

/-- Eight blocks of counter mode, of the text at `x9 + o`, into `v0`–`v7`. -/
def aesPart (nr o : Nat) : List Instr :=
  (List.range 8).flatMap ctr1 ++ (List.range (nr - 1)).flatMap rnd ++ lastRnd nr o ++
    ([.addImm .w .x10 .x10 8] : List Instr)

/-! ## GHASH -/

/-- The pairs of blocks of `ghPart`: pair `p` is block `pa p` by `H'^(pk p)`
and block `pb p` by `H'^(pl p)`. The first block, which `Y` is added to, is in
the last pair. -/
def pa : Nat → Nat | 0 => 1 | 1 => 3 | 2 => 5 | _ => 7
def pk : Nat → Nat | 0 => 7 | 1 => 5 | 2 => 3 | _ => 1
def pb : Nat → Nat | 0 => 2 | 1 => 4 | 2 => 6 | _ => 0
def pl : Nat → Nat | 0 => 6 | 1 => 4 | 2 => 2 | _ => 8

/-- Block `j` of the eight at `x9` into `a`, as loaded. -/
def ld (a : VReg) (j : Nat) : List Instr := [.ldrq a .x9 (16 * j), .vop (.rev .rev64b a a)]

/-- Pair `p`'s products: `X₁ ⊕ X₂` (`hi`), `A₁ ⊕ A₂` (`lo`) and `T ⊕ U`
(`mid`), `Y` added to its second block if `y`. -/
def pair (p : Nat) (a k b l : Nat) (y : Bool) : List Instr :=
  ld A₁ a ++ ld A₂ b ++ (if y then [.vop (.logic .eor A₂ A₂ Y)] else []) ++
  [.ldrq S₁ .x19 (sOff k), .ldrq S₂ .x19 (sOff l), .ldrq KP .x19 (kOff p),
   .vop (.perm .trn1 .d2 T A₁ A₂), .vop (.perm .trn2 .d2 U A₁ A₂), .vop (.logic .eor T T U),
   .vop (.pmull false X₁ A₁ S₁), .vop (.pmull true A₁ A₁ S₁),
   .vop (.pmull false X₂ A₂ S₂), .vop (.pmull true A₂ A₂ S₂),
   .vop (.pmull false U T KP), .vop (.pmull true T T KP)]

/-- The first pair's products, the sums. -/
def addFirst : List Instr :=
  [.vop (.logic .eor HI X₁ X₂), .vop (.logic .eor LO A₁ A₂), .vop (.logic .eor MID U T)]

/-- A pair's products added. -/
def addNext : List Instr :=
  [.vop (.eor3 HI HI X₁ X₂), .vop (.eor3 LO LO A₁ A₂), .vop (.eor3 MID MID U T)]

/-- The product `hi : mid ⊕ hi ⊕ lo : lo`, reduced into `Y` (`PmullK.reduceK`). -/
def reduce : List Instr :=
  [.vop (.pmull false T LO C), .vop (.ext U LO LO 8), .vop (.eor3 U U LO HI),
   .vop (.eor3 MID MID U T), .vop (.pmull false T MID C), .vop (.ext HI HI HI 8),
   .vop (.ext T T T 8), .vop (.eor3 Y HI MID T)]

/-- GHASH of the eight blocks at `x9`. -/
def ghPart : List Instr :=
  pair 0 1 7 2 6 false ++ addFirst ++ pair 1 3 5 4 4 false ++ addNext ++ pair 2 5 3 6 2 false ++ addNext ++
    pair 3 7 1 0 8 true ++ addNext ++ reduce

/-! ## The loops -/

/-- Store `v0`–`v7` to the eight blocks at `x9 + o`. -/
def stores (o : Nat) : List Instr := (List.range 8).flatMap fun j => [.strq (breg j) .x9 (o + 16 * j)]

/-- The counter (`w10`), the reduction constant, `Y` (at `x20 + 16`) and the
pointer to the text (`x23`) set up; `x11 = x26 / 128` batches. -/
def setup : List Instr :=
  [.ldr .w .x10 .x20 60, .rev32 .x10 .x10, .movz .x .x12 0xc200 3, .vop (.dup .d2 C .x12),
   .ldrq Y .x20 16, .vop (.rev .rev64b Y Y), .addImm .x .x9 .x23 0, .lsr .x .x11 .x26 7]

/-- `Y` and the counter stored back. -/
def finish : List Instr :=
  [.vop (.rev .rev64b Y Y), .strq Y .x20 16, .rev32 .x12 .x10, .str .w .x12 .x20 60]

/-- One iteration of `seal`'s loop: batch `i + 1` (at `x9 + 128`) encrypted
while batch `i` (at `x9`) is hashed. -/
def encBody (nr : Nat) : List Instr :=
  VG.Impl.Weave.weave (aesPart nr 128) ghPart ++ stores 128 ++
    ([.addImm .x .x9 .x9 128, .subImm .x .x11 .x11 1] : List Instr)

/-- `seal`'s loop over `x11 ≥ 1` batches: the first encrypted, then each
next one encrypted while the one before is hashed, then the last hashed. -/
def encLoop (nr : Nat) : Prog isa :=
  .seq (.block (aesPart nr 0 ++ stores 0 ++ ([.subImm .x .x11 .x11 1] : List Instr)))
    (.seq (.ite (.zero .x .x11) (.block []) (.loop (.block (encBody nr)) (.nonzero .x .x11)))
      (.block (ghPart ++ ([.addImm .x .x9 .x9 128] : List Instr))))

/-- One iteration of `open`'s loop: the batch at `x9` decrypted and hashed. -/
def decBody (nr : Nat) : List Instr :=
  VG.Impl.Weave.weave (aesPart nr 0) ghPart ++ stores 0 ++
    ([.addImm .x .x9 .x9 128, .subImm .x .x11 .x11 1] : List Instr)

/-- `open`'s loop over `x11 ≥ 1` batches. -/
def decLoop (nr : Nat) : Prog isa := .loop (.block (decBody nr)) (.nonzero .x .x11)

/-- The loop for the number of rounds in `x22` (10, 12 or 14). -/
def byRounds (f : Nat → Prog isa) : Prog isa :=
  .seq (.block [.subImm .x .x13 .x22 10, .subImm .x .x14 .x22 12])
    (.ite (.zero .x .x13) (f 10) (.ite (.zero .x .x14) (f 12) (f 14)))

/-- Encrypt and hash the first `128 ⌊x26 / 128⌋` bytes of the text at `x23`
(at least 128), with the table of keys set up. -/
def enc : Prog isa := .seq (.block setup) (.seq (byRounds encLoop) (.block finish))

/-- Decrypt and hash them. -/
def dec : Prog isa := .seq (.block setup) (.seq (byRounds decLoop) (.block finish))

end VG.Impl.Gcm.AArch64.Stitch
