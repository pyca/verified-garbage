module

public import VerifiedGarbage.Impl.Modes.X86_64.CbcChained

/-!
# Triple DES-CBC and -CFB64 decryption on x86-64, many blocks at a time

`decrypt cfb name code` (schedule = rdi, iv = rsi, data = rdx, n = rcx,
scratch = r8): CBC decryption (`cfb = false`) or CFB64 decryption, whose
blocks need no block's result for the next, in groups of up to `G = 256`
blocks, each by one call of an ECB function (`name`, whose code is `code`:
`vg_triple_des_ecb_decrypt` for CBC, `vg_triple_des_ecb_encrypt` for CFB, or a
variant of it) on the group in place.

The scratch buffer (`G + 9` words, at `sb` = `r9` between the calls): word 0
the chaining value `Cⱼ₋₁` (the IV before the first block), words `1 … G` a
copy of the group's ciphertext blocks, words `G + 1 … G + 6` our caller's
callee-saved registers. Across the calls, which keep them, `r15` holds the
schedule's address, `r13` the scratch buffer's, `r12` the group's and `r14`
the blocks left.

* Entry: the callee-saved registers to the scratch buffer, the IV to word 0,
  and the last ciphertext block `Cₙ₋₁`, the block to continue from, to the IV
  (`Core.cbcLastToIv`), before any block is decrypted.
* Each group of `c = min(G, left)` blocks at `D`: the blocks to words
  `1 … c`; for CFB, words `0 … c - 1` (`Cⱼ₋₁`) to the data; the ECB function
  on the `c` blocks at `D` (CBC: `CIPH⁻¹_K(Cⱼ)`; CFB: `CIPH_K(Cⱼ₋₁)`); then
  each block XORed with word `j` (CBC: `Cⱼ₋₁`) or `j + 1` (CFB: `Cⱼ`); and
  word `c`, the group's last ciphertext block, to word 0.

Only the pointers and `n` (and what is computed from them) are public; no
address or branch depends on the key, the IV or the data.
-/

@[expose] public section

namespace VG.Impl.TripleDes.X86_64.Batch

open VG.X86_64
open VG.Impl.Aes.X86_64 (sb movR)
open VG.Impl.Modes.X86_64 (copyW xorW Core CtrRegs)

/-- The blocks of a group. -/
def G : Nat := 256

/-- The layout, for the modes' pieces (`groupCount`, `copyBlocks`, …): blocks
of one word, the copies at word 1, the saved registers after them. Its
`prepare` and `crypt` are unused. -/
def core : Core where
  prepare := .block []
  crypt := .block []
  slots := G + 1
  total := G + 9
  buf := 1
  G := G
  bw := 1
  keyRegs := []
  dataReg := .r12
  leftReg := .r14

/-- The registers of the arguments. -/
def regs : CtrRegs := ⟨.rsi, .rdx, .rcx, .r8⟩

/-- The callee-saved registers to the scratch buffer (at `sb`), and the IV to
word 0. -/
def entry : List Instr :=
  core.ctrEntry regs ++ copyW .rax sb .rsi 0 0 0

/-- The arguments to the registers the calls keep; ZF is set if there are no
blocks. -/
def setup : List Instr :=
  [movR .r15 .rdi, movR .r13 sb, movR .r12 .rdx, movR .r14 .rcx, .alu .test .r14 (.reg .r14)]

/-- For CFB: words `0 … c - 1` to the data (`c` in `r10`). -/
def shiftIn : Prog isa :=
  .seq (.block [movR .rax .r12, movR .rbx sb, movR .rcx .r10]) core.copyBlocks

/-- The ECB function's arguments: the schedule, the group, `c`. -/
def callArgs : List Instr := [movR .rdi .r15, movR .rsi .r12, movR .rdx .r10]

/-- Before the call: `c` to `rcx` and `r10`, the blocks to words `1 … c`, and
for CFB the words before them to the data. -/
def before (cfb : Bool) : Prog isa :=
  .seq core.groupCount (.seq (.block core.xorArgs) (.seq core.copyBlocks
    (.seq (if cfb then shiftIn else .block []) (.block callArgs))))

/-- `rcx` blocks: the word at `rax` XORed into the block at `rbx`. -/
def xorBlocks : Prog isa := .loop (.block (xorW .rbp .rbx .rax 0 0 0 ++ core.nextBlock)) .ne

/-- The XOR's arguments: the group to `rbx`, `c` to `r10`, word `0` (CBC)
or `1` (CFB) to `rax`. -/
def xorArgs (cfb : Bool) : List Instr :=
  [movR .rbx .r12, movR .r10 .rcx, movR .rax sb] ++
    (if cfb then [.alu .add .rax (.imm 8)] else [])

/-- Word `c` to word 0, and on past the group; ZF is set when no blocks are
left. -/
def finish : List Instr :=
  [movR .rax .r10, .shift .shl .rax 3, .alu .add .rax (.reg sb)] ++ copyW .rbp sb .rax 0 0 0 ++ core.advance

/-- After the call: the scratch buffer back to `sb`, `c` again, the XOR and
the next group. -/
def after (cfb : Bool) : Prog isa :=
  .seq (.block [movR sb .r13]) (.seq core.groupCount (.seq (.block (xorArgs cfb))
    (.seq xorBlocks (.block finish))))

/-- One group. -/
def group (cfb : Bool) (name : String) (code : Prog isa) : Prog isa :=
  .seq (before cfb) (.seq (.call name code) (after cfb))

/-- The entry, the IV and the registers the calls keep. -/
def prologue : Prog isa := .seq (.block entry) (.seq (core.cbcLastToIv regs) (.block setup))

/-- The whole function. -/
def decrypt (cfb : Bool) (name : String) (code : Prog isa) : Prog isa :=
  .seq prologue (.seq (.ite .e (.block []) (.loop (group cfb name code) .ne)) (.block core.restoreRegs))

end VG.Impl.TripleDes.X86_64.Batch
