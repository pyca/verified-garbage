module

public import VerifiedGarbage.Spec.Sha256
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# SHA-256 compression function: PPC64LE implementation

`vg_sha256_compress(state = r3, blocks = r4, n = r5, scratch = r6)`.

The same structure as the AArch64 implementation:
* The working variables `a … h` stay in `v4`–`v11`; round `t` names
  variable `k` with `vvar t k`. Architectural word one carries each word.
  The other lanes never influence the result.
* The message schedule is a 16-word window in `scratch[0..64)`. The words
  of a block are loaded big-endian with `lwbrx`, indexed by `r0`.
* `r14`–`r19` are nonvolatile: they are saved in `scratch[64..112)` first and
  restored last.
* `r3`–`r6` (the pointers and the block count) are public; no address and
  no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Sha256.PPC64LE

open VG.PPC64LE
open VG.Spec.Sha256 (K)

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

/-- Save them in `scratch[64..112)`. -/
def save : List Instr := (List.range 6).flatMap fun i => [.store .d (saved i) .r6 (64 + 8 * i)]

/-- Restore them. -/
def restore : List Instr := (List.range 6).flatMap fun i => [.load .d (saved i) .r6 (64 + 8 * i)]

/-- The offset of `W[i mod 16]` in the scratch buffer. -/
def slot (i : Nat) : Nat := 4 * (i % 16)

/-- Leave `Wₜ` in the low word of `T0` and in its slot. The additions are in
the order of the specification. -/
def schedule (t : Nat) : List Instr :=
  if t < 16 then [
    .li .r0 (4 * t),
    .loadRev .w T0 .r4 .r0,
    .store .w T0 .r6 (slot t)]
  else [
    .load .w T1 .r6 (slot (t + 14)), .mtvsrd .v0 T1,
    .load .w T2 .r6 (slot (t + 1)), .mtvsrd .v1 T2,
    .vop (.sha256 .v0 .v0 false 4), .vop (.sha256 .v1 .v1 false 0),
    .load .w T0 .r6 (slot (t + 9)), .mfvsrd T1 .v0, .add T0 T1 T0,
    .mfvsrd T2 .v1, .add T0 T0 T2,
    .load .w T2 .r6 (slot t), .add T0 T0 T2, .store .w T0 .r6 (slot t)]

/-- Round `t`, with `Wₜ` in `T0`. Only `Kₜ + Wₜ` crosses from scalar
into vector registers; the round state and arithmetic stay in vectors. -/
def round (t : Nat) : List Instr :=
  let a := vvar t 0; let b := vvar t 1; let c := vvar t 2; let d := vvar t 3
  let e := vvar t 4; let f := vvar t 5; let g := vvar t 6; let h := vvar t 7
  [.lis T1 ((K t).extractLsb' 16 16), .ori T1 T1 ((K t).extractLsb' 0 16),
   .add T1 T1 T0, .mtvsrd .v15 T1,
   .vop (.sha256 .v12 e true 4), .vop (.sha256 .v14 a true 0),
   .vop (.logic .xor .v13 f g), .vop (.logic .and .v13 .v13 e), .vop (.logic .xor .v13 .v13 g),
   .vop (.add false .v15 h .v15), .vop (.add false .v15 .v15 .v12), .vop (.add false .v15 .v15 .v13),
   .vop (.add false d d .v15),
   .vop (.logic .or .v12 a b), .vop (.logic .and .v12 .v12 c),
   .vop (.logic .and .v13 a b), .vop (.logic .or .v12 .v12 .v13),
   .vop (.add false .v14 .v14 .v12), .vop (.add false h .v15 .v14)]

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ round n))

/-- Load the hash value (`64 % 8 = 0`, so the variables are in the same
registers after the 64 rounds). -/
def load : List Instr := (List.range 8).flatMap fun k =>
  [.load .w T1 .r3 (4 * k), .mtvsrd (vvar 0 k) T1]

/-- Add the hash value into the working variables (loading all of it before
storing any of it), and store the result. -/
def update : List Instr :=
  (List.range 8).map (fun k => .mfvsrd (var 0 k) (vvar 0 k)) ++
  (List.range 4).map (fun k => .load .w ([T0, T1, T2, T3].getD k T0) .r3 (4 * k)) ++
  (List.range 4).map (fun k => .add (var 0 k) (var 0 k) ([T0, T1, T2, T3].getD k T0)) ++
  (List.range 4).map (fun k => .load .w ([T0, T1, T2, T3].getD k T0) .r3 (4 * (k + 4))) ++
  (List.range 4).map (fun k => .add (var 0 (k + 4)) (var 0 (k + 4)) ([T0, T1, T2, T3].getD k T0)) ++
  (List.range 8).map (fun k => .store .w (var 0 k) .r3 (4 * k))

/-- Advance to the next block and decrement the count. -/
def advance : List Instr := [.addi .r4 .r4 64, .subi .r5 .r5 1]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (rounds 64) (.block (update ++ advance)))

/-- The blocks. -/
def blocks : Prog isa := .ite (.zero .d .r5) (.block []) (.loop body (.nonzero .d .r5))

def compress : Prog isa := .seq (.block save) (.seq blocks (.block restore))

end VG.Impl.Sha256.PPC64LE
