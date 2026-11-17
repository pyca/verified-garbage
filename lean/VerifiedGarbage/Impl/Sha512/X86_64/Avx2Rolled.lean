module

public import VerifiedGarbage.Impl.Sha512.X86_64.Avx2
public import VerifiedGarbage.Impl.Weave

/-!
# SHA-512 compression function: x86-64 implementation with AVX2 and BMI, rolled

The technique of `Impl.Sha512.X86_64.Avx2` (two blocks at a time, their
message schedules computed together in the two lanes of the `ymm`
registers), with the rounds rolled into loops of sixteen: `Kₜ` is added
from a table of constants (`aluTbl`, which carries the table, `Spec.Sha512.Ks`)
rather than loaded with `movabs`.

* Sixteen rounds rename the working variables back to the registers they
  started in (`16 % 8 = 0`) and use the same `carry` registers
  (`16 % 2 = 0`), so iteration `j` of a loop is the same code for every `j`:
  it addresses `Kₜ` through an index, `rdx = 128 j`, which steps through
  the table eight bytes per round (`rsi + rdx + 8 t'`), and the second
  block's `Wₜ` through the same index (`rcx + rdx + …`).
* The first block's 80 rounds are a loop of five iterations, each also
  computing sixteen words of the schedule of both blocks (eight `schedule`
  steps; the last iteration's are never read): one loop rather than one
  and sixteen rounds after it, so that the function's code is small enough
  to stay in the decoded-instruction caches of the cores that have the
  smallest (AMD Zen 3: 4096 µops), with both paths below. The second
  block's 80 rounds are a loop of five iterations.
* The first block's words are in the upper lane of the `ymm` registers and
  the second block's in the lower one, so that the second block's are
  stored as an `xmm` register. The scratch space keeps few of the words:
  the first block's rounds read theirs from a ring of the sixteen current
  words of both blocks (`ringSlot`, 256 bytes at `rcx`), which each schedule
  step overwrites, a register at a time, once the two rounds it is woven
  into have read them; the second block's 80 words are kept after it
  (`hi`), sixteen at the start of each iteration (`keepWords`), as its
  rounds run once the first block's are done.
* If the count is odd, the first block is compressed alone first (`lone`),
  by the same code without keeping words (`first false`), with the block in
  both lanes; the rest are compressed two at a time (`pair`), and the
  second blocks' words are zeroed after the last pair (`wipe`). So on
  every path the 640 bytes after the ring are left as they were or zeroed,
  which the residue analysis (`X86_64.RTaint`) sees: what the function
  leaves in the scratch space of the data is the ring.
* `rsi` (the blocks' address) and `rdx` (the block count) are kept in
  the scratch space while the rounds use them, at `1312` and `1320`, and
  the callee-saved registers around them (`saved`).
-/

@[expose] public section

namespace VG.Impl.Sha512.X86_64.Avx2Rolled

open VG.X86_64
open VG.Impl.Sha512.X86_64.Avx2 (at_ var carry T round initCarry msg mBswap tmp bswapMask const load
  schedule loadState addState vb vs t0 t1 t2 t3)

/-- The name of the table of round constants. -/
def kSym : String := "VG_SHA512_K"

/-- Where round `t'` of an iteration reads `Kₜ`: `t = 16 j + t'` with
`rdx = 128 j` and the table at `rsi`. -/
def kSlot (t' : Nat) : MemOp := { base := .rsi, index := some .rdx, scale := 1, disp := ((8 * t' : Nat) : Int) }

/-- Where the second block's schedule starts in the scratch space, after
the ring of the sixteen current words of both blocks. -/
def hi : Nat := 256

/-- Where round `t'` of an iteration of block `j` reads `Wₜ`: the first
block's from the ring, the second's from its schedule, through the index. -/
def wSlotR (j t' : Nat) : MemOp :=
  if j = 0 then at_ .rcx (32 * (t' / 2) + 16 + 8 * (t' % 2))
  else { base := .rcx, index := some .rdx, scale := 1, disp := ((hi + 8 * t' : Nat) : Int) }

/-- Where the ring keeps words `2i` and `2i+1` of both blocks' current sixteen:
the second block's, then the first's. -/
def ringSlot (i : Nat) : MemOp := at_ .rcx (32 * i)

/-- Where the words `2i` and `2i+1` of the second block's sixteen of an
iteration are kept: through `r14`, the iteration's index. -/
def hiSlot (i : Nat) : MemOp :=
  { base := .rcx, index := some .r14, scale := 1, disp := ((hi + 16 * i : Nat) : Int) }

/-- Round `t'` of block `j`: `Impl.Sha512.X86_64.Avx2.round`, with `Kₜ` read
from the table. -/
def roundR (j t' : Nat) : List Instr :=
  let a := var t' 0; let b := var t' 1; let d := var t' 3
  let e := var t' 4; let f := var t' 5; let g := var t' 6; let h := var t' 7
  let x := carry t'; let y := carry (t' + 1)
  [ -- h := h + Kₜ + Wₜ
    .aluTbl .add h (kSlot t') kSym Spec.Sha512.Ks,
    .alu .add h (.mem (wSlotR j t')),
    -- h := h + Ch(e, f, g), as (e ∧ f) + (¬e ∧ g)
    .mov y (.reg e), .alu .and y (.reg f), .andn T e g, .alu .add y (.reg T),
    .alu .add h (.reg y),
    -- h := h + Σ₁(e), which is T₁
    .rorx y e 14, .rorx T e 18, .alu .xor y (.reg T), .rorx T e 41, .alu .xor y (.reg T),
    .alu .add h (.reg y),
    -- e' := d + T₁
    .alu .add d (.reg h),
    -- h := h + Σ₀(a)
    .rorx y a 28, .rorx T a 34, .alu .xor y (.reg T), .rorx T a 39, .alu .xor y (.reg T),
    .alu .add h (.reg y),
    -- h := h + Maj(a, b, c), as ((a ⊕ b) ∧ (b ⊕ c)) ⊕ b, with b ⊕ c in x;
    -- a ⊕ b, in y, is the next round's b ⊕ c
    .mov y (.reg a), .alu .xor y (.reg b), .alu .and x (.reg y), .alu .xor x (.reg b),
    .alu .add h (.reg x)]

/-- `Impl.Sha512.X86_64.Avx2.schedule i`, without its store: its words stay in `msg i`. -/
def scheduleR (i : Nat) : List Instr := (schedule i).dropLast

/-- The words of `msg (i + 8)` stored, over those the ring held. -/
def storeR (i : Nat) : List Instr := [.vmovdquStore .l256 (ringSlot i) (msg (i + 8))]

/-- Group `i'` (`< 8`) of an iteration of the first block: words `2i'+16`
and `2i'+17` of the iteration's schedule, woven into rounds `2i'` and
`2i'+1` (`Impl.Weave.weave`, as OpenSSL spreads its schedule across its
rounds), so that the vector and integer units both have work throughout,
and stored once those rounds have read the words the ring held. -/
def groupR (i' : Nat) : List Instr :=
  VG.Impl.Weave.weave (scheduleR (i' + 8)) (roundR 0 (2 * i') ++ roundR 0 (2 * i' + 1)) ++ storeR i'

/-- Groups `0 … n-1` of an iteration. -/
def groupsR : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (groupsR n) (.block (groupR n))

/-- Rounds `0 … n-1` of an iteration of block `j`. -/
def roundsR (j : Nat) : Prog isa → Nat → Prog isa
  | p, 0 => p
  | p, n + 1 => .seq (roundsR j p n) (.block (roundR j n))

/-- Sixteen rounds of block `j`, without the schedule. -/
def rounds16 (j : Nat) : Prog isa := roundsR j (.block []) 16

/-- The next iteration: `rdx` steps by 128, up to `stop`. -/
def step (stop : Nat) : List Instr := [.alu .add .rdx (.imm 128), .alu .cmp .rdx (.imm stop)]

/-- The sixteen words of the second block that an iteration of the first
block's loop starts from, the lower lanes of `msg 0 … msg 7`, kept. They are
stored through `r14`, which is free there: the index, as the minimum of it
and 512 (`cmovb`), which changes nothing but tells the residue analysis
(`X86_64.RTaint`) where the stores may write. -/
def keepWords : List Instr :=
  [.mov .r14 (.imm 512), .alu .cmp .rdx (.reg .r14), .cmov .b .r14 (.reg .rdx)] ++
    (List.range 8).map fun i => .vmovdquStore .l128 (hiSlot i) (msg i)

/-- Keep `rsi` and `rdx` in the scratch space, and point `rsi` at the table
and `rdx` at its start. -/
def enter : List Instr :=
  [.store (at_ .rcx 1312) .rsi, .store (at_ .rcx 1320) .rdx, .leaSym .rsi kSym, .mov .rdx (.imm 0)]

/-- Get back `rsi` and `rdx`. -/
def leave : List Instr := [.mov .rsi (.mem (at_ .rcx 1312)), .mov .rdx (.mem (at_ .rcx 1320))]

/-- `W₂ᵢ` and `W₂ᵢ₊₁` (`i < 8`) of the blocks at `r15` and `rsi` into the
lanes of `msg i`, and stored in the ring. -/
def loadR (i : Nat) : List Instr :=
  [.vmovdquLoad .l128 (msg i) (at_ T (16 * i)), .vmovdquLoad .l128 tmp (at_ .rsi (16 * i)),
   .vop (.vinserti128 (msg i) (msg i) tmp 1), vb .vpshufb (msg i) (msg i) mBswap,
   .vmovdquStore .l256 (ringSlot i) (msg i)]

/-- The words an iteration of the first block's loop keeps: the second
block's, if `keep`. -/
def keepIf (keep : Bool) : List Instr := if keep then keepWords else []

/-- The first block of an iteration (as in `Avx2.body`), up to getting back
`rsi` and `rdx`: its 80 rounds, a loop of five iterations of sixteen, which
also compute the schedule of both blocks, sixteen words each (the last
iteration's are never read). If `keep`, the lower lane holds the second
block, at `rsi + 128`, whose words are kept for its rounds; otherwise it
holds the first block again, whose words in that lane no round reads, and
nothing is stored after the ring. `r15` points at the lower lane's block
while the words are loaded. -/
def first (keep : Bool) : Prog isa :=
  .seq (.block ((.mov T (.reg .rsi) :: if keep then [.alu .add T (.imm 128)] else []) ++
    loadR 0 ++ loadR 1 ++ loadR 2 ++ loadR 3 ++ loadR 4 ++ loadR 5 ++
    loadR 6 ++ loadR 7 ++ loadState ++ initCarry ++ enter))
  (.seq (.loop (.seq (.block (keepIf keep)) (.seq (groupsR 8) (.block (step 640)))) .ne) (.block leave))

/-- The rest of a lone block: its hash value, and the next block. -/
def loneRest : List Instr := addState ++ [.alu .add .rsi (.imm 128), .alu .sub .rdx (.imm 1)]

/-- One block, which never writes the second block's schedule. -/
def lone : Prog isa := .seq (first false) (.block loneRest)

/-- The rest of two blocks: the first's hash value, then the second's
rounds, from its words kept in the scratch space, and its hash value. -/
def pairRest : Prog isa :=
  .seq (.block (addState ++ initCarry ++ enter))
  (.seq (.loop (.seq (rounds16 1) (.block (step 640))) .ne)
    (.block (leave ++ addState ++ ([.alu .add .rsi (.imm 256), .alu .sub .rdx (.imm 2)] : List Instr))))

/-- Two blocks. -/
def pair : Prog isa := .seq (first true) pairRest

/-- The callee-saved registers saved in the scratch space, and where. -/
def saved : List (Reg × Nat) :=
  [(.rbx, 1280), (.rbp, 1288), (.r12, 1296), (.r13, 1304), (.r14, 1256), (.r15, 1264)]

def save : List Instr := saved.map fun (r, d) => .store (at_ .rcx d) r

def restore : List Instr := saved.map (fun (r, d) => .mov r (.mem (at_ .rcx d))) ++ [.vop .vzeroupper]

/-- The second block's schedule zeroed, with `xmm0`, by SSE instructions
(after `vzeroupper`, so that they cost no transition between AVX and SSE),
which the residue analysis knows store zero (`pxor x, x`, `movdqu`). -/
def wipe : List Instr :=
  .vop .vzeroupper :: .xop (.bin .pxor (msg 0) (msg 0)) ::
    (List.range 40).map fun k => .movdquStore (at_ .rcx (hi + 16 * k)) (msg 0)

/-- A lone block first, if the count is odd, then the blocks two at a time;
after those, the second blocks' schedule is zeroed. So whatever the count,
what the function leaves in the scratch space of the data is the ring. -/
def compress : Prog isa :=
  .seq (.block (save ++ const mBswap bswapMask ++ ([.alu .test .rdx (.imm 1)] : List Instr)))
  (.seq (.ite .ne lone (.block []))
  (.seq (.block [.alu .test .rdx (.reg .rdx)])
  (.seq (.ite .e (.block []) (.seq (.loop pair .ne) (.block wipe)))
  (.block restore))))

end VG.Impl.Sha512.X86_64.Avx2Rolled
