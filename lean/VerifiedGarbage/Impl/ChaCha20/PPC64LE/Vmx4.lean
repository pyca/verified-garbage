module

public import VerifiedGarbage.Impl.ChaCha20.PPC64LE.Xor

/-!
# Four-block ChaCha20 keystream XOR with VMX on PPC64LE

`vg_chacha20_xor(state = r3, src = r4, len = r5, buf = r6, dst = r7)`, as
`Xor.xor`: while at least 256 bytes remain, four blocks at once in vector
registers; then `Xor.xor` (one block at a time) on the rest.

* Word `k` of the four blocks is in `vreg k` (`v0`–`v15`), word `j` of the
  register (most significant first) for block `j`, whose counter is the
  state's plus `j`. The rounds rotate with `vrlw` by the counts in `v16`–`v19`
  (16, 12, 8 and 7 in every word); additions and XORs are in place, so the
  rounds need no other register.
* Every input word is splatted from its row of the state (`lxvd2x`, which
  puts the row's words in the order 1, 0, 3, 2) with `vperm`, using `v16`
  and `v17`: before the rounds into `vreg k`, after them into `v18` to add
  it.
* Each row of four words is then transposed by `vperm`s through `v16`–`v19`
  into one register per block, holding its 16 bytes in the order a
  `stxvd2x` stores them; the source's row (`lxvd2x` from `r4`, into `v19`) is
  XORed with it and stored to the destination (`r7`), each row of the
  source loaded before the same row of the destination is stored.
* The constants (the `vperm` controls, the counter offsets and the rotation
  counts) are one table, `VG_CHACHA20_VMX4_CONSTS`, read by `lxvd2xTbl`
  from its address in `r10` at the offset in `r8`. Putting its address in
  `r10` changes the link register, which `r11` keeps meanwhile.
* After each chunk the counter in memory advances by four, the pointers by
  256 bytes and the length by 256. `r12` counts the double rounds.

The branches are on the length and the round count only, and every address
is a pointer plus a constant, so only the pointers and the length can
affect timing.
-/

@[expose] public section

namespace VG.Impl.ChaCha20.PPC64LE.Vmx4

open VG.PPC64LE

/-- The register holding word `k` of the four blocks. -/
def vreg (k : Fin 16) : VReg :=
  #[.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15][k]

/-- The name of the table of constants. -/
def tblName : String := "VG_CHACHA20_VMX4_CONSTS"

/-- The `vperm` control that splats word `p` of its first operand. -/
def splatCtl (p : Nat) : BitVec 128 :=
  #[0x00010203000102030001020300010203, 0x04050607040506070405060704050607,
    0x08090a0b08090a0b08090a0b08090a0b, 0x0c0d0e0f0c0d0e0f0c0d0e0f0c0d0e0f].getD p 0

/-- The table: the four splat controls (vectors 0–3); the counter offsets
0, 1, 2, 3 (4); the rotation counts 16, 12, 8, 7 (5–8); and the transposing
controls (9–12): `[b₀, a₀, b₁, a₁]` and `[b₂, a₂, b₃, a₃]` from words `a`
and `b`, and the high or the low halves of two vectors. -/
def tblVecs : List (BitVec 128) :=
  [splatCtl 0, splatCtl 1, splatCtl 2, splatCtl 3,
   0x00000000000000010000000200000003,
   0x00000010000000100000001000000010, 0x0000000c0000000c0000000c0000000c,
   0x00000008000000080000000800000008, 0x00000007000000070000000700000007,
   0x10111213000102031415161704050607, 0x18191a1b08090a0b1c1d1e1f0c0d0e0f,
   0x00010203040506071011121314151617, 0x08090a0b0c0d0e0f18191a1b1c1d1e1f]

/-- The table's doublewords, each vector's high one first, as `lxvd2xTbl`
reads them. -/
def tblWords : List (BitVec 64) := tblVecs.flatMap fun v => [v.extractLsb' 64 64, v.extractLsb' 0 64]

/-- Vector `i` of the table into `d`. -/
def ldc (d : VReg) (i : Nat) : List Instr := [.li .r8 (16 * i), .lxvd2xTbl d .r10 .r8 tblName tblWords]

/-- Where word `k` of the state is in its row as `lxvd2x` loads it. -/
def pos (k : Fin 16) : Nat := k.val % 4 ^^^ 1

/-- Word `k` of the state, in every word of `d` (through `v16` and `v17`). -/
def splat (k : Fin 16) (d : VReg) : List Instr :=
  ([.li .r8 (16 * (k.val / 4)), .lxvd2x .v16 .r3 .r8] : List Instr) ++ ldc .v17 (pos k) ++
    [.vop (.perm d .v16 .v16 .v17)]

/-- The four blocks' input: the state's words, with counters plus 0, 1, 2
and 3; then the rotation counts. -/
def setup : List Instr :=
  (List.finRange 16).flatMap (fun k => splat k (vreg k)) ++ ldc .v16 4 ++
    ([.vop (.add false (vreg 12) (vreg 12) .v16)] : List Instr) ++
    ldc .v16 5 ++ ldc .v17 6 ++ ldc .v18 7 ++ ldc .v19 8

/-- The register of the rotation count `n` (16, 12, 8 or 7). -/
def rotReg (n : Nat) : VReg := if n = 16 then .v16 else if n = 12 then .v17 else if n = 8 then .v18 else .v19

/-- The operations of the rounds, each on all four blocks. -/
inductive Op
  | add (d a b : Fin 16)
  | xorRol (d a b : Fin 16) (n : Nat)

def Op.code : Op → List Instr
  | .add d a b => [.vop (.add false (vreg d) (vreg a) (vreg b))]
  | .xorRol d a b n =>
    [.vop (.logic .xor (vreg d) (vreg a) (vreg b)), .vop (.rlw (vreg d) (vreg d) (rotReg n))]

def cols : List (Fin 16 × Fin 16 × Fin 16 × Fin 16) :=
  [(0,4,8,12), (1,5,9,13), (2,6,10,14), (3,7,11,15)]
def diags : List (Fin 16 × Fin 16 × Fin 16 × Fin 16) :=
  [(0,5,10,15), (1,6,11,12), (2,7,8,13), (3,4,9,14)]

def half (qs : List (Fin 16 × Fin 16 × Fin 16 × Fin 16)) (r₁ r₂ : Nat) : List Op :=
  qs.map (fun (a,b,_,_) => .add a a b) ++
  qs.map (fun (a,_,_,d) => .xorRol d d a r₁) ++
  qs.map (fun (_,_,c,d) => .add c c d) ++
  qs.map (fun (_,b,c,_) => .xorRol b b c r₂)

def quarters (qs : List (Fin 16 × Fin 16 × Fin 16 × Fin 16)) : List Op :=
  half qs 16 12 ++ half qs 8 7

/-- A double round: the four column quarter rounds together, then the four
diagonal ones. -/
def doubleRound : List Instr := (quarters cols ++ quarters diags).flatMap Op.code

/-- Ten double rounds, counted in `r12`. -/
def roundLoop : Prog isa :=
  .seq (.block [.li .r12 10])
    (.loop (.block (doubleRound ++ [.subi .r12 .r12 1])) (.nonzero .d .r12))

/-- Add input word `k` (and the counter offsets to word 12). -/
def feedWord (k : Fin 16) : List Instr :=
  splat k .v18 ++ ([.vop (.add false (vreg k) (vreg k) .v18)] : List Instr) ++
    if k = 12 then ldc .v17 4 ++ [.vop (.add false (vreg k) (vreg k) .v17)] else []

def feed : List Instr := (List.finRange 16).flatMap feedWord

/-- Four words of the four blocks, `a`, `b`, `c` and `d`, transposed: block
0's into `b`, 1's into `d`, 2's into `c` and 3's into `v16`, each as the
words `b, a, d, c` (most significant first). -/
def transpose4 (a b c d : VReg) : List Instr :=
  ldc .v19 9 ++ ([.vop (.perm .v16 a b .v19), .vop (.perm .v17 c d .v19)] : List Instr) ++
  ldc .v19 10 ++ ([.vop (.perm .v18 a b .v19), .vop (.perm a c d .v19)] : List Instr) ++
  ldc .v19 11 ++ ([.vop (.perm b .v16 .v17 .v19), .vop (.perm c .v18 a .v19)] : List Instr) ++
  ldc .v19 12 ++ ([.vop (.perm d .v16 .v17 .v19), .vop (.perm .v16 .v18 a .v19)] : List Instr)

/-- The register of word `i` of row `r`. -/
def rowReg (r i : Fin 4) : VReg := vreg ⟨4 * r + i, by omega⟩

/-- Row `r` (words `4r` to `4r + 3`) of the four blocks, transposed. -/
def transpose (r : Fin 4) : List Instr := transpose4 (rowReg r 0) (rowReg r 1) (rowReg r 2) (rowReg r 3)

/-- The register holding row `r` of block `j` after `transpose r`. -/
def outReg (r j : Fin 4) : VReg :=
  if j.val = 0 then rowReg r 1 else if j.val = 1 then rowReg r 3 else if j.val = 2 then rowReg r 2 else .v16

/-- Row `r` of block `j` of the source XORed with the keystream into the
destination. -/
def xorRow (r j : Fin 4) : List Instr :=
  [.li .r8 (64 * j + 16 * r), .lxvd2x .v19 .r4 .r8, .vop (.logic .xor .v19 .v19 (outReg r j)),
   .stxvd2x .v19 .r7 .r8]

def finishRow (r : Fin 4) : List Instr := transpose r ++ (List.finRange 4).flatMap (xorRow r)

/-- The keystream of the four blocks, XORed with 256 bytes of the source
into the destination. -/
def chunk : Prog isa :=
  .seq (.block setup) (.seq roundLoop (.block (feed ++ (List.finRange 4).flatMap finishRow)))

/-- Advance the counter by four, and the source, the destination and the
length by 256 bytes; `r9` tests for another chunk. -/
def next : List Instr :=
  [.load .w .r8 .r3 48, .addi .r8 .r8 4, .store .w .r8 .r3 48,
   .addi .r4 .r4 256, .addi .r7 .r7 256, .subi .r5 .r5 256, .lsr .d .r9 .r5 8]

def body : Prog isa := .seq chunk (.block next)

/-- The chunks, with the table's address in `r10` and the link register kept
in `r11`. -/
def bulk : Prog isa :=
  .seq (.block [.mflr .r11, .adrSym .r10 tblName])
    (.seq (.loop body (.nonzero .d .r9)) (.block [.mtlr .r11]))

def xor : Prog isa :=
  .seq (.block [.lsr .d .r9 .r5 8])
    (.seq (.ite (.zero .d .r9) (.block []) bulk) VG.Impl.ChaCha20.PPC64LE.Xor.xor)

end VG.Impl.ChaCha20.PPC64LE.Vmx4
