module

public import VerifiedGarbage.Spec.Sha512
public import VerifiedGarbage.Impl.Sha2.PPC64LE

/-!
# SHA-512 compression function: PPC64LE implementation

`vg_sha512_compress(state = r3, blocks = r4, n = r5, scratch = r6)`.

The POWER8 vector crypto instructions operate on 64-bit words:
* The working variables `a … h` stay in `v4`–`v11`; round `t` names
  variable `k` with `vvar t k`. The high doubleword carries each word.
  The unused low doubleword never influences the result.
* The sixteen-word message window occupies eight more vector registers.
  Two schedule words are generated together; the input pairs use big-endian
  `ldbrx` loads indexed by `r0`.
* Round constants come from a static table addressed by `r18` and `r19`.
  The last working word includes the next round constant.
* The first sixteen rounds load the input. A sixteen-round loop handles
  the remaining sixty-four rounds, with `r14` as its public counter.
* The five nonvolatile core registers are saved in `scratch[128..168)`;
  the table base `r18` is saved separately in `scratch[8..16)`.
* `r3`–`r6` (the pointers and the block count) are public; no address and
  no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Sha512.PPC64LE

open VG.PPC64LE
open VG.Spec.Sha512 (K)

/-- The registers holding the working variables. -/
def work : List Reg := [.r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15]

/-- The register holding working variable `k` (`a = 0, …, h = 7`) at the start of round `t`. -/
def var (t k : Nat) : Reg := work.getD ((k + 8 - t % 8) % 8) .r7

/-- Volatile vector registers hold the working state throughout the rounds. -/
def vwork : List VReg := [.v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11]

def vvar (t k : Nat) : VReg := vwork.getD ((k + 8 - t % 8) % 8) .v4

/-- General-purpose temporaries for input loads and output updates. -/
def T0 : Reg := .r16
def T1 : Reg := .r17
def T2 : Reg := .r0
def T3 : Reg := .r19

/-- The nonvolatile registers used, in the order they are saved. -/
def saved (i : Nat) : Reg := [.r14, .r15, .r16, .r17, .r19].getD i .r14

/-- Save them in `scratch[128..168)`. -/
def save : List Instr := (List.range 5).flatMap fun i => [.store .d (saved i) .r6 (128 + 8 * i)]

/-- Restore them. -/
def restore : List Instr := (List.range 5).flatMap fun i => [.load .d (saved i) .r6 (128 + 8 * i)]

/-- The offset of `W[i mod 16]` in the scratch buffer. -/
def slot (i : Nat) : Nat := 8 * (i % 16)

/-- `d := v` for a 64-bit constant: the high word with `lis` and `ori`,
shifted up by `sldi`, then the low word with `oris` and `ori`. -/
def movImm64 (d : Reg) (v : BitVec 64) : List Instr :=
  [.lis d (v.extractLsb' 48 16), .ori d d (v.extractLsb' 32 16), .lsl d d 32,
   .oris d d (v.extractLsb' 16 16), .ori d d (v.extractLsb' 0 16)]

export VG.Impl.Sha2.PPC64LE (pairs preg)

def schedulePair (n : Nat) : List Instr := VG.Impl.Sha2.PPC64LE.schedulePair true n

/-- The odd word was computed with its predecessor. -/
def schedule (t : Nat) : List Instr :=
  if t % 2 = 0 then schedulePair (t/2) ++ [.vop (.logic .or .v15 (preg (t/2)) (preg (t/2)))]
  else [.vop (.sldoi .v15 (preg (t/2)) (preg (t/2)) 8)]

/-- Bias the final working variable only while another round remains. -/
def roundBias (t : Nat) : Spec.Sha512.Word := if t < 80 then K t else 0

/-- Round constants, with two zero words for the last doubleword-pair load. -/
def kWords : List Spec.Sha512.Word := Spec.Sha512.Ks ++ [0, 0]
def kSym : String := "VG_SHA512_PPC64LE_K"

/-- Byte offset of the next round constant. -/
def kIndex (t : Nat) : BitVec 64 := BitVec.ofNat 64 (8*(t+1))

/-- Round `t` starts with `h + Kₜ`. After choice consumes `g`, prepare it
as the next round's `h + Kₜ₊₁`, off the current round's sum chain. -/
def round (t : Nat) : List Instr :=
  Impl.Sha2.PPC64LE.round true (vvar t) kSym kWords

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ round n))

def roundRange (start : Nat) : Nat → Prog isa
  | 0 => .block []
  | n+1 => .seq (roundRange start n) (.block (schedule (start+n) ++ round (start+n)))

def computedChunk : Prog isa := roundRange 16 16

def roundsLoop : Prog isa := .seq (rounds 16) (.seq (.block [.li .r14 4])
  (.loop (.seq computedChunk (.block [.subi .r14 .r14 1])) (.nonzero .d .r14)))

/-- Load the hash value (`80 % 8 = 0`, so the variables are in the same
registers after the 80 rounds). -/
def loadState : List Instr := (List.range 8).flatMap fun k =>
  [.load .d T1 .r3 (8 * k), .mtvsrd (vvar 0 k) T1]

/-- Start the first round with its constant already in `h`. -/
def load : List Instr := loadState ++ movImm64 T0 (roundBias 0) ++
  [.mtvsrd .v12 T0, .vop (.add true .v11 .v11 .v12), .li .r19 8]

/-- Add the hash value into the working variables (loading all of it before
storing any of it), and store the result. -/
def update : List Instr :=
  (List.range 8).map (fun k => .mfvsrd (var 0 k) (vvar 0 k)) ++
  (List.range 4).map (fun k => .load .d ([T0, T1, T2, T3].getD k T0) .r3 (8 * k)) ++
  (List.range 4).map (fun k => .add (var 0 k) (var 0 k) ([T0, T1, T2, T3].getD k T0)) ++
  (List.range 4).map (fun k => .load .d ([T0, T1, T2, T3].getD k T0) .r3 (8 * (k + 4))) ++
  (List.range 4).map (fun k => .add (var 0 (k + 4)) (var 0 (k + 4)) ([T0, T1, T2, T3].getD k T0)) ++
  (List.range 8).map (fun k => .store .d (var 0 k) .r3 (8 * k))

/-- Advance to the next block and decrement the count. -/
def advance : List Instr := [.addi .r4 .r4 128, .subi .r5 .r5 1]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq roundsLoop (.block (update ++ advance)))

/-- The blocks. -/
def blocks : Prog isa := .ite (.zero .d .r5) (.block []) (.loop body (.nonzero .d .r5))

def compressCore : Prog isa := .seq (.block save) (.seq blocks (.block restore))

/-- Keep the caller's LR in a volatile register while resolving the table.
The complete save/address/restore sequence forms one block. -/
def tableSetup : Prog isa := .seq (.block [.store .d .r18 .r6 8])
  (.block [.mflr .r0, .adrSym .r18 kSym, .mtlr .r0])

def tableRestore : List Instr := [.load .d .r18 .r6 8]

def compress : Prog isa := .seq tableSetup (.seq compressCore (.block tableRestore))

end VG.Impl.Sha512.PPC64LE
