module

public import VerifiedGarbage.Spec.Sha512
public import VerifiedGarbage.TCB.X86_64.Isa
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
  it addresses `Kₜ` and `Wₜ` through an index, `rdx = 128 j`, which steps
  through the table eight bytes per round (`rsi + rdx + 8 t'`) and through
  the scratch space sixteen (`rcx + 2 rdx + …`).
* The first block's rounds 0–63 are a loop of four iterations, each also
  computing sixteen words of the schedule of both blocks (eight `schedule`
  steps); rounds 64–79 follow once, from `rdx = 512`. The second block's 80
  rounds are a loop of five iterations.
* `rsi` (the blocks' address) and `rdx` (the block count) are kept in
  the scratch space while the rounds use them, at `1312` and `1320`; `r14`
  and `r15`, whose slots those were, are saved in `xmm14` and `xmm15`
  (`vmovq`) and restored after `vzeroupper` (`movq`), when no `ymm` register
  has a dirty upper half, so that the legacy-SSE `movq` costs no transition.
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

/-- Where round `t'` of an iteration of block `j` reads `Wₜ`. -/
def wSlotR (j t' : Nat) : MemOp :=
  { base := .rcx, index := some .rdx, scale := 2, disp := ((32 * (t' / 2) + 16 * j + 8 * (t' % 2) : Nat) : Int) }

/-- Where the `schedule` step `i` (`8 ≤ i < 16`) of an iteration stores its words. -/
def sSlot (i : Nat) : MemOp := { base := .rcx, index := some .rdx, scale := 2, disp := ((32 * i : Nat) : Int) }

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

/-- `Impl.Sha512.X86_64.Avx2.schedule i`, storing its words through the index. -/
def scheduleR (i : Nat) : List Instr :=
  (schedule i).dropLast ++ [.vmovdquStore .l256 (sSlot i) (msg i)]

/-- Group `i'` (`< 8`) of an iteration of the first block: words `2i'+16`
and `2i'+17` of the iteration's schedule, woven into rounds `2i'` and
`2i'+1` (`Impl.Weave.weave`, as OpenSSL spreads its schedule across its
rounds), so that the vector and integer units both have work throughout. -/
def groupR (i' : Nat) : List Instr :=
  VG.Impl.Weave.weave (scheduleR (i' + 8)) (roundR 0 (2 * i') ++ roundR 0 (2 * i' + 1))

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

/-- Keep `rsi` and `rdx` in the scratch space, and point `rsi` at the table
and `rdx` at its start. -/
def enter : List Instr :=
  [.store (at_ .rcx 1312) .rsi, .store (at_ .rcx 1320) .rdx, .leaSym .rsi kSym, .mov .rdx (.imm 0)]

/-- Get back `rsi` and `rdx`. -/
def leave : List Instr := [.mov .rsi (.mem (at_ .rcx 1312)), .mov .rdx (.mem (at_ .rcx 1320))]

/-- The first block of an iteration (as in `Avx2.body`), up to getting back
`rsi` and `rdx`. The second block is at `rsi + 128` if there is one
(`rdx ≥ 2`), and otherwise the first is loaded twice; `r15` points at it
while the words are loaded. -/
def first : Prog isa :=
  .seq (.block [.mov T (.reg .rsi), .alu .cmp .rdx (.imm 1)])
  (.seq (.ite .e (.block []) (.block [.alu .add T (.imm 128)]))
  (.seq (.block (load 0 ++ load 1 ++ load 2 ++ load 3 ++ load 4 ++ load 5 ++ load 6 ++ load 7 ++
    loadState ++ initCarry ++ enter))
  (.seq (.loop (.seq (groupsR 8) (.block (step 512))) .ne)
  (.seq (rounds16 0) (.block leave)))))

/-- The rest of an iteration: the first block's hash value, and the second
block if there is one. -/
def rest : Prog isa :=
  .seq (.block (addState ++ ([.alu .cmp .rdx (.imm 1)] : List Instr)))
  (.ite .e
    (.block [.alu .add .rsi (.imm 128), .alu .sub .rdx (.imm 1)])
    (.seq (.block (initCarry ++ enter))
    (.seq (.loop (.seq (rounds16 1) (.block (step 640))) .ne)
      (.block (leave ++ addState ++ ([.alu .add .rsi (.imm 256), .alu .sub .rdx (.imm 2)] : List Instr))))))

/-- One iteration: two blocks, or the last one. -/
def body : Prog isa := .seq first rest

/-- The callee-saved registers saved in the scratch space, and where; `r14`
and `r15` are saved in `xmm14` and `xmm15`. -/
def saved : List (Reg × Nat) := [(.rbx, 1280), (.rbp, 1288), (.r12, 1296), (.r13, 1304)]

def save : List Instr :=
  saved.map (fun (r, d) => .store (at_ .rcx d) r) ++ [.vop (.vmovq .xmm14 .r14), .vop (.vmovq .xmm15 .r15)]

def restore : List Instr :=
  saved.map (fun (r, d) => .mov r (.mem (at_ .rcx d))) ++
    [.vop .vzeroupper, .movqR .r14 .xmm14, .movqR .r15 .xmm15]

def compress : Prog isa :=
  .seq (.block (save ++ const mBswap bswapMask ++ ([.alu .test .rdx (.reg .rdx)] : List Instr)))
    (.seq (.ite .e (.block []) (.loop body .ne)) (.block restore))

end VG.Impl.Sha512.X86_64.Avx2Rolled
