module

public import VerifiedGarbage.Impl.Cast5.Tables
public import VerifiedGarbage.Impl.Cast5.Lines
public import VerifiedGarbage.Impl.Words.RISCV64

/-!
# CAST5 on RISC-V

A lookup in an S-box never uses a secret as an address: the four lookups a
round function (or a line of key expansion) makes are made at once by a
*scan* of the static table `VG_CAST5_S1234` (or `VG_CAST5_S5678` in key
expansion, `Impl/Cast5/Tables.lean`), 256 entries of four words, two
quadwords: quadword `q` of entry `e` holds word `2q` (the low word) and
`2q + 1` (the high word). The scan is two passes, pass `q` reading quadword
`q` of every entry, for the indices `2q` (low word) and `2q + 1` (high
word), in 16 blocks of 16 entries, from the last. A block's 16 quadwords
are reduced to one by a tree of selections `a XOR ((a XOR b) AND m)`, the
mask `m` of level `c` all ones in each word whose index has bit `c` set
(made once a pass): in each word, the entry of the block whose number is
the index's low four bits. The block's selection is then kept where the
block's mask is set, all ones in each word whose index's block (its high
four bits) is at most the block's number, so that the last block to set a
word is the index's. No secret is an address or a branch condition. The
table is 64-byte aligned (`Abi.withConsts`), so its quadwords take aligned
loads.

Each function has the scan once: encryption and decryption run their rounds
in a loop whose body is one round, choosing the round's type (its number
modulo 3, as `Spec.Cast5.f` does) by a branch; key expansion runs each half
of §2.4 as a loop of 40 steps, each one scan, choosing the step's bytes and
what it does with the four values by a chain of branches on the step's
number. The rotation by the secret amount `Kr` (§2.2) is five rotations by
1, 2, 4, 8 and 16 (each two word shifts and an `or`: RV64I has no
rotation), each kept or not by a mask made from a bit of `Kr`.

The model faults on misaligned accesses, and the contracts state no
alignment for the buffers, so the subkeys, the blocks and the key are read
and written a byte at a time; the
working space `scratch` is rounded up to a multiple of 8 (it has room to
spare), and words kept there take aligned accesses. It holds the caller's
`s0`–`s10` (at `savedOff`) and, in key expansion, `x`, `z` and a group's
extra lookups. Every public value (pointers, counts, the round's type, the
step's number, the table's address) stays in a register; `ra` is never
written.
-/

@[expose] public section

namespace VG.Impl.Cast5.RISCV64

open VG.RISCV64
open VG.Impl.Words.RISCV64 (loadBE32 loadLE32 storeBE storeLE32)

/-! ## Registers -/

/-- The table's address. -/
abbrev tbl : Reg := .t4
/-- The address of the scan's block. -/
abbrev ep : Reg := .t3
/-- Temporaries. -/
abbrev tmp : Reg := .t0
abbrev wd : Reg := .t1
/-- `I`, then `f`, of a round, or the value of a line of key expansion. -/
abbrev vI : Reg := .t5
/-- `Kr` of a round and the rotation's mask. -/
abbrev vKr : Reg := .t6
abbrev msk : Reg := .a5

/-- `mv d, n` (`addi d, n, 0`). -/
def mov (d n : Reg) : Instr := .addi d n 0

/-! ## The scan -/

/-- The register of index `k` (0–3) of a scan. -/
def idxReg : Nat → Reg
  | 0 => .s0 | 1 => .s1 | 2 => .s2 | _ => .s3

/-- The register of value `k` (0–3) of a scan. -/
def accReg : Nat → Reg
  | 0 => .s4 | 1 => .s5 | 2 => .s6 | _ => .s7

/-- The mask of level `c` (0–3) of a pass's selections. -/
def maskReg : Nat → Reg
  | 0 => .t0 | 1 => .t1 | 2 => .t2 | _ => .t5

/-- The register a block's selection ends in, in pass `q`. -/
def selReg (q : Nat) : Reg := if q = 0 then .s5 else .s0

/-- The register of a block's mask, in pass `q`. -/
def blkReg (q : Nat) : Reg := if q = 0 then .s6 else .s1

/-- The registers of a pass's selections, pass `q`. -/
def treeRegs (q : Nat) : List Reg := [selReg q, blkReg q, .a5, .t6, .s7]

/-- `a := a XOR ((a XOR b) AND m)`: `b`'s bits where `m`'s are set, `a`'s
elsewhere. Clobbers `b`. -/
def pick (a b m : Reg) : List Instr := [.logic .xor b b a, .logic .and b b m, .logic .xor a a b]

/-- The selection among the `2 ^ L` quadwords at `ep + o + 16 e` (`e < 2 ^
L`) by the masks of levels `0 … L - 1`, into the first of the registers
`rs` (`L + 1` of them, all clobbered): the two halves' selections, of
`2 ^ (L - 1)` quadwords each, then the second where level `L - 1`'s mask is
set. -/
def tree : Nat → Nat → List Reg → List Instr
  | 0, o, a :: _ => [.load .d a ep o]
  | L + 1, o, a :: b :: rs =>
    tree L o (a :: b :: rs) ++ tree L (o + 16 * 2 ^ L) (b :: rs) ++ pick a b (maskReg L)
  | _, _, _ => []

/-- The mask of level `c` of pass `q`: bit `c` of index `2q` spread over the
low word, of index `2q + 1` over the high word (each shifted to the top,
arithmetically down, then to its word). Clobbers `a5`. -/
def maskSetup (q c : Nat) : List Instr :=
  [.shift .sll .d (maskReg c) (idxReg (2 * q)) (63 - c), .shift .sra .d (maskReg c) (maskReg c) 63,
   .shift .srl .d (maskReg c) (maskReg c) 32, .shift .sll .d .a5 (idxReg (2 * q + 1)) (63 - c),
   .shift .sra .d .a5 .a5 63, .shift .sll .d .a5 .a5 32, .logic .or (maskReg c) (maskReg c) .a5]

/-- The start of pass `q`: the masks of levels 0–3; the indices' blocks
less 17 (`h - 17`, for an index's block `h`, its number shifted right by
4), in place; `ep` past the table's end. -/
def passStart (q : Nat) : List Instr :=
  (List.range 4).flatMap (maskSetup q) ++
  [.shift .srl .d (idxReg (2 * q)) (idxReg (2 * q)) 4, .addi (idxReg (2 * q)) (idxReg (2 * q)) (-17),
   .shift .srl .d (idxReg (2 * q + 1)) (idxReg (2 * q + 1)) 4,
   .addi (idxReg (2 * q + 1)) (idxReg (2 * q + 1)) (-17),
   .addi ep tbl 2047, .addi ep ep 2047, .addi ep ep 2]

/-- Block `J` of pass `q`, the blocks `J + 1 … 15` done: `ep` at the block
(`tbl + 256 J`), the indices' registers to `h - J - 1`, negative exactly if
`J ≥ h`; the block's quadwords `q` of its 16 entries selected by the
indices' low bits (each word by its own index); the block's mask, all ones
in each word whose index's block `h` is at most `J` (the low word's from
its register shifted right by 32, the high word's arithmetically by 63
then left by 32); and the selection kept in value `2q` where the mask is
set. The last block a word's mask is set at is the index's. -/
def passBody (q : Nat) : List Instr :=
  [.addi ep ep (-256), .addi (idxReg (2 * q)) (idxReg (2 * q)) 1,
   .addi (idxReg (2 * q + 1)) (idxReg (2 * q + 1)) 1] ++
  tree 4 (8 * q) (treeRegs q) ++
  [.shift .srl .d (blkReg q) (idxReg (2 * q)) 32, .shift .sra .d .a5 (idxReg (2 * q + 1)) 63,
   .shift .sll .d .a5 .a5 32, .logic .or (blkReg q) (blkReg q) .a5] ++
  pick (accReg (2 * q)) (selReg q) (blkReg q)

/-- The words of value `2q`: its high word to value `2q + 1`, its low word
kept. -/
def passEnd (q : Nat) : List Instr :=
  [.shift .srl .d (accReg (2 * q + 1)) (accReg (2 * q)) 32, .shift .sll .d (accReg (2 * q)) (accReg (2 * q)) 32,
   .shift .srl .d (accReg (2 * q)) (accReg (2 * q)) 32]

/-- Pass `q` of a scan: lookups `2q` and `2q + 1`, from quadword `q` of
each entry, its 16 blocks of 16 entries from the last. -/
def pass (q : Nat) : Prog isa :=
  .seq (.block (passStart q)) (.seq (.loop (.block (passBody q)) (.ne ep tbl)) (.block (passEnd q)))

/-- The scan of the table at `tbl` (256 entries of four words) at the
indices in `s0`–`s3` (each below 256), into `s4`–`s7`: lookups 0 and 1,
then 2 and 3. Clobbers `s0`–`s3`, `t0`–`t3`, `t5`, `t6` and `a5`. -/
def scan : Prog isa := .seq (pass 0) (pass 1)

/-! ## The working space -/

/-- Where the callee-saved registers are saved. -/
def savedOff : Nat := 64

/-- The callee-saved registers the code uses. -/
def saved : List Reg := [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10]

/-- The saved registers and their offsets. -/
def savedSlots : List (Reg × Nat) := saved.zipIdx.map fun (r, i) => (r, savedOff + 8 * i)

/-- The working space at `b` rounded up to a multiple of 8, the callee-saved
registers saved there, then the table's address in `tbl`. -/
def prologue (b : Reg) (sym : String) : List Instr :=
  ([.addi b b 7, .logicImm .and b b (-8)] : List Instr) ++ savedSlots.map (fun (r, d) => .store .d r b d) ++
  ([.lla tbl sym] : List Instr)

/-- The callee-saved registers restored from the working space at `b`. -/
def epilogue (b : Reg) : List Instr := savedSlots.map fun (r, d) => .load .d r b d

/-! ## Encryption and decryption

`vg_cast5_ecb_encrypt(schedule = a0, rounds = a1, data = a2, n = a3,
scratch = a4)`. During the rounds `(L, R)` are in `(a6, a7)` (their low
words), the next round's `Kmᵢ` at `s8` (`Krᵢ` at `s8 + 64`), the rounds
left of the block in `s9` and the next round's number modulo 3 in `s10`. -/

abbrev sch : Reg := .a0
abbrev rnd : Reg := .a1
abbrev dat : Reg := .a2
abbrev cnt : Reg := .a3
abbrev wkE : Reg := .a4
abbrev xL : Reg := .a6
abbrev xR : Reg := .a7
abbrev km : Reg := .s8
abbrev left : Reg := .s9
abbrev typ : Reg := .s10

/-- `I` before the rotation, into `vI`: `Kmᵢ - D`, `Kmᵢ + D` or `Kmᵢ ^ D`
for a round number 0, 1 or 2 modulo 3 (Type 3, 1, 2). -/
def mix : Nat → List Instr
  | 1 => loadLE32 vI tmp km 0 ++ [.add vI vI xR]
  | 2 => loadLE32 vI tmp km 0 ++ [.logic .xor vI vI xR]
  | _ => loadLE32 vI tmp km 0 ++ [.sub vI vI xR]

/-- `f` into `vI` from `S1[Ia], S2[Ib], S3[Ic], S4[Id]` in `s7`, `s6`,
`s5`, `s4`. -/
def comb : Nat → List Instr
  | 1 => [.logic .xor vI (accReg 3) (accReg 2), .sub vI vI (accReg 1), .add vI vI (accReg 0)]
  | 2 => [.sub vI (accReg 3) (accReg 2), .add vI vI (accReg 1), .logic .xor vI vI (accReg 0)]
  | _ => [.add vI (accReg 3) (accReg 2), .logic .xor vI vI (accReg 1), .sub vI vI (accReg 0)]

/-- The code for the round number modulo 3 in `typ`. -/
def byType (f : Nat → List Instr) : Prog isa :=
  .ite (.zero typ) (.block (f 0))
    (.seq (.block [.addi tmp typ (-1)]) (.ite (.zero tmp) (.block (f 1)) (.block (f 2))))

/-- One of the five steps of the rotation of `vI` left by the low 5 bits of
`vKr`: `msk` := 0 if bit `b` of `vKr` is set, all ones if not; the rotation
by `2 ^ b` is in `tmp`. -/
def rotateStep (b : Nat) : List Instr :=
  [.shift .sll .d msk vKr (63 - b), .shift .srl .d msk msk 63, .addi msk msk (-1),
   .shift .srl .w wd vI (32 - 2 ^ b), .shift .sll .w tmp vI (2 ^ b), .logic .or tmp tmp wd,
   .logic .xor wd vI tmp, .logic .and wd wd msk, .logic .xor vI tmp wd]

/-- `vI` rotated left by the low 5 bits of `Krᵢ` (of its low byte). -/
def rotate : List Instr := [.load .b vKr km 64] ++ (List.range 5).flatMap rotateStep

/-- The bytes `Id, Ic, Ib, Ia` of `I` in `vI` into `s0`–`s3`. -/
def spread : List Instr :=
  [.logicImm .and (idxReg 0) vI 255, .shift .srl .w (idxReg 1) vI 8,
   .logicImm .and (idxReg 1) (idxReg 1) 255, .shift .srl .w (idxReg 2) vI 16,
   .logicImm .and (idxReg 2) (idxReg 2) 255, .shift .srl .w (idxReg 3) vI 24]

/-- `(L, R)` := `(R, L ^ f)`, then `km` to the next round's subkeys: up for
encryption, down for decryption. -/
def feistel (up : Bool) : List Instr :=
  [.logic .xor vI vI xL, mov xL xR, mov xR vI, .addi km km (if up then 4 else -4)]

/-- The next round's number modulo 3: 1, 2, 0, 1, … for encryption, 1, 0,
2, 1, … (or 0, 2, 1, …) for decryption; then the rounds left down. -/
def next (up : Bool) : Prog isa :=
  .seq (if up then .seq (.block [.addi tmp typ (-2)]) (.ite (.zero tmp) (.block [.li typ 0])
      (.block [.addi typ typ 1]))
    else .ite (.zero typ) (.block [.li typ 2]) (.block [.addi typ typ (-1)]))
    (.block [.addi left left (-1)])

/-- A round. -/
def round (up : Bool) : Prog isa :=
  .seq (byType mix) (.seq (.block (rotate ++ spread)) (.seq scan
    (.seq (byType comb) (.seq (.block (feistel up)) (next up)))))

/-- The block at `p` into `(L₀, R₀)` (big-endian, a byte at a time). -/
def loadBlock (p : Reg) : List Instr := loadBE32 xL tmp p 0 ++ loadBE32 xR tmp p 4

/-- The block into `(L₀, R₀)`; `km` at `Km₁`, the count of rounds and the
number of the first, 1. -/
def startEnc (p : Reg) : List Instr := loadBlock p ++ [mov km sch, mov left rnd, .li typ 1]

/-- The same for decryption: `km` at `Kmₙ`, the number of round `n` modulo
3 (`n / 4 - 3`: 1 for 16 rounds, 0 for 12). -/
def startDec (p : Reg) : List Instr :=
  loadBlock p ++ [.shift .sll .d tmp rnd 2, .add km sch tmp, .addi km km (-4), mov left rnd,
    .shift .srl .d tmp rnd 2, .addi typ tmp (-3)]

/-- `(Rₙ, Lₙ)` to the block at `p`, big-endian, a byte at a time. -/
def finish (p : Reg) : List Instr := storeBE 4 xR tmp p 0 ++ storeBE 4 xL tmp p 4

/-- Encrypting (`up`) or decrypting the block at `p` with the schedule at
`sch` and the number of rounds in `rnd`, in place. This is the block
function a mode reuses. -/
def crypt (up : Bool) (p : Reg) : Prog isa :=
  .seq (.block (if up then startEnc p else startDec p)) (.seq (.loop (round up) (.nonzero left))
    (.block (finish p)))

/-- `vg_cast5_ecb_encrypt(schedule = a0, rounds = a1, data = a2, n = a3,
scratch = a4)`, or decrypt: each block in turn. -/
def ecb (up : Bool) : Prog isa :=
  .seq (.block (prologue wkE s1234Sym))
    (.seq (.ite (.zero cnt) (.block [])
      (.loop (.seq (crypt up dat) (.block [.addi dat dat 8, .addi cnt cnt (-1)])) (.nonzero cnt)))
      (.block (epilogue wkE)))

def ecbEncrypt : Prog isa := ecb true
def ecbDecrypt : Prog isa := ecb false

/-! ## Key expansion

`vg_cast5_expand_key(key = a0, key_len = a1, schedule = a2, scratch =
a3)`. `x0 … xF` and `z0 … zF` are kept in the working space at `xOff` and
`zOff` (`Impl.Cast5.off`), a byte each; a group's four extra lookups at
`extraOff`. Each half of §2.4 is 40 steps: for each of its eight groups of
lines, the group's extra lookups, then its four lines. The step's number is
in `stp`, the halves left in `hlv`, and the next half's subkeys at
`out`. -/

abbrev key : Reg := .a0
abbrev klen : Reg := .a1
abbrev out : Reg := .a2
abbrev wkK : Reg := .a3
abbrev dst : Reg := .a4
abbrev stp : Reg := .a6
abbrev hlv : Reg := .a7

/-- Where a group's extra lookups are kept: `S8, S7, S6, S5` of its extra bytes. -/
def extraOff : Nat := 48

/-- Where a line's value goes: quadruple `q` of an array, or subkey `k` of the half. -/
inductive Store
  | quad (a : Arr) (q : Nat)
  | key (k : Nat)
  deriving Inhabited

/-- A step: the extra lookups of a group, at the bytes `a, b, c, d`
(`S5[a], S6[b], S7[c], S8[d]`), or a line and its store. -/
inductive Step
  | extras (a b c d : Pos)
  | line (l : Line) (st : Store)
  deriving Inhabited

/-- A group of lines: its extra lookups, then its lines. -/
def groupSteps (ls : List Line) (st : Nat → Store) : List Step :=
  .extras (extraOf ls 5) (extraOf ls 6) (extraOf ls 7) (extraOf ls 8) ::
    (List.range 4).map fun k => .line (ls.getD k default) (st k)

/-- The 40 steps of a half (`Spec.Cast5.half`). -/
def halfSteps : List Step :=
  groupSteps zLines (.quad .z) ++ groupSteps aLines .key ++ groupSteps xLines (.quad .x) ++
  groupSteps bLines (fun k => .key (4 + k)) ++ groupSteps zLines (.quad .z) ++
  groupSteps cLines (fun k => .key (8 + k)) ++ groupSteps xLines (.quad .x) ++
  groupSteps dLines (fun k => .key (12 + k))

/-- The bytes at `d, c, b, a` into `s0`–`s3`, the indices of a scan of
`VG_CAST5_S5678` (`S8, S7, S6, S5`). -/
def gather (a b c d : Pos) : List Instr :=
  [.load .b (idxReg 0) wkK (srcOff d), .load .b (idxReg 1) wkK (srcOff c),
   .load .b (idxReg 2) wkK (srcOff b), .load .b (idxReg 3) wkK (srcOff a)]

/-- The bytes a step looks up. -/
def Step.gather : Step → List Instr
  | .extras a b c d => Impl.Cast5.RISCV64.gather a b c d
  | .line l _ => Impl.Cast5.RISCV64.gather l.main.1 l.main.2.1 l.main.2.2.1 l.main.2.2.2

/-- What a step does with the four values in `s4`–`s7`: keep them as the
group's extra lookups, or XOR them, the line's extra lookup and quadruple
(if any, big-endian) into `vI` and store it (a quadruple big-endian, a
subkey little-endian, a byte at a time). -/
def Step.post : Step → List Instr
  | .extras .. => [.store .w (accReg 0) wkK extraOff, .store .w (accReg 1) wkK (extraOff + 4),
      .store .w (accReg 2) wkK (extraOff + 8), .store .w (accReg 3) wkK (extraOff + 12)]
  | .line l st =>
    ([.logic .xor vI (accReg 0) (accReg 1), .logic .xor vI vI (accReg 2), .logic .xor vI vI (accReg 3),
      .load .w tmp wkK (extraOff + 4 * (8 - l.extra.1)), .logic .xor vI vI tmp] : List Instr) ++
    (match l.word with
      | some (a, q) => loadBE32 tmp wd wkK (off a + 4 * q) ++ [.logic .xor vI vI tmp]
      | none => []) ++
    (match st with
      | .quad a q => storeBE 4 vI wd wkK (off a + 4 * q)
      | .key k => storeLE32 vI tmp out (4 * k))

/-- The code `cs[k]` for the step number `k` in `stp` (from `i`), by a chain
of comparisons. -/
def sel : List (List Instr) → Nat → Prog isa
  | [], _ => .block []
  | c :: cs, i => .seq (.block [.addi tmp stp (-(i : Int))]) (.ite (.zero tmp) (.block c) (sel cs (i + 1)))

/-- A step, then the next step's number (`tmp` zero after the last). -/
def step : Prog isa :=
  .seq (sel (halfSteps.map Step.gather) 0) (.seq scan
    (.seq (sel (halfSteps.map Step.post) 0) (.block [.addi stp stp 1, .addi tmp stp (-40)])))

/-- A half: its 40 steps, then `out` on 64 bytes and the halves left down. -/
def half : Prog isa :=
  .seq (.block [.li stp 0]) (.seq (.loop step (.nonzero tmp))
    (.block [.addi out out 64, .addi hlv hlv (-1)]))

/-- Copy a key byte to `x`: `key` at the next key byte, `dst` at its place in
`x`, `klen` the count left. -/
def copyStep : List Instr :=
  [.load .b tmp key 0, .store .b tmp dst 0, .addi key key 1, .addi dst dst 1, .addi klen klen (-1)]

/-- `vg_cast5_expand_key(key = a0, key_len = a1, schedule = a2, scratch =
a3)`: `x` := the key padded with zeros (§2.5), then both halves. -/
def expandKey : Prog isa :=
  .seq (.block (prologue wkK s5678Sym ++
      ([.li tmp 0, .store .d tmp wkK xOff, .store .d tmp wkK (xOff + 8), .addi dst wkK xOff] : List Instr)))
    (.seq (.loop (.block copyStep) (.nonzero klen))
      (.seq (.block [.li hlv 2]) (.seq (.loop half (.nonzero hlv)) (.block (epilogue wkK)))))

end VG.Impl.Cast5.RISCV64
