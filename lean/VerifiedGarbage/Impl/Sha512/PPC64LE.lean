module

public import VerifiedGarbage.Spec.Sha512
public import VerifiedGarbage.Impl.Sha2.PPC64LE

/-!
# SHA-512 compression function: PPC64LE implementation

`vg_sha512_compress(state = r3, blocks = r4, n = r5, scratch = r6)`.

The same structure as the SHA-256 implementation (`VG.Impl.Sha256.PPC64LE`),
on whole 64-bit registers:
* The working variables `a … h` stay in `v4`–`v11`; round `t` names
  variable `k` with `vvar t k`. The high doubleword carries each word.
  The unused low doubleword never influences the result.
* The sixteen-word message window occupies eight more vector registers.
  Two schedule words are generated together; the input pairs use big-endian
  `ldbrx` loads indexed by `r0`.
* `Kₜ` is built with `lis`, `ori`, `sldi`, `oris` and `ori` (`movImm64`).
* `r14`–`r19` are nonvolatile: they are saved in `scratch[128..176)` first
  and restored last.
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

/-- Temporaries; `T0` holds `Wₜ` at the start of each round. -/
def T0 : Reg := .r16
def T1 : Reg := .r17
def T2 : Reg := .r18
def T3 : Reg := .r19

/-- The nonvolatile registers used, in the order they are saved. -/
def saved (i : Nat) : Reg := [.r14, .r15, .r16, .r17, .r18, .r19].getD i .r14

/-- Save them in `scratch[128..176)`. -/
def save : List Instr := (List.range 6).flatMap fun i => [.store .d (saved i) .r6 (128 + 8 * i)]

/-- Restore them. -/
def restore : List Instr := (List.range 6).flatMap fun i => [.load .d (saved i) .r6 (128 + 8 * i)]

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

/-- Round `t`, with `Wₜ` in the high doubleword of `v15`. Only the round
constant crosses from scalar to vector registers. -/
def round (t : Nat) : List Instr :=
  let a := vvar t 0; let b := vvar t 1; let c := vvar t 2; let d := vvar t 3
  let e := vvar t 4; let f := vvar t 5; let g := vvar t 6; let h := vvar t 7
  movImm64 T1 (K t) ++
  [.mtvsrd .v12 T1, .vop (.add true .v15 .v12 .v15),
   .vop (.sha512 .v12 e true 8), .vop (.sha512 .v14 a true 0),
   .vop (.logic .xor .v13 f g), .vop (.logic .and .v13 .v13 e), .vop (.logic .xor .v13 .v13 g),
   .vop (.add true .v15 h .v15), .vop (.add true .v15 .v15 .v12), .vop (.add true .v15 .v15 .v13),
   .vop (.add true d d .v15),
   .vop (.logic .or .v12 a b), .vop (.logic .and .v12 .v12 c),
   .vop (.logic .and .v13 a b), .vop (.logic .or .v12 .v12 .v13),
   .vop (.add true .v14 .v14 .v12), .vop (.add true h .v15 .v14)]

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ round n))

/-- Load the hash value (`80 % 8 = 0`, so the variables are in the same
registers after the 80 rounds). -/
def load : List Instr := (List.range 8).flatMap fun k =>
  [.load .d T1 .r3 (8 * k), .mtvsrd (vvar 0 k) T1]

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
def body : Prog isa := .seq (.block load) (.seq (rounds 80) (.block (update ++ advance)))

/-- The blocks. -/
def blocks : Prog isa := .ite (.zero .d .r5) (.block []) (.loop body (.nonzero .d .r5))

def compress : Prog isa := .seq (.block save) (.seq blocks (.block restore))

end VG.Impl.Sha512.PPC64LE
