module

public import VerifiedGarbage.Impl.Cast5.Tables
public import VerifiedGarbage.Impl.Cast5.Lines
public import VerifiedGarbage.TCB.Arm.Isa

/-!
# CAST5 on baseline ARMv7

A lookup in an S-box never uses a secret as an address: the four lookups a
round function (or a line of key expansion) makes are made at once by a
*scan* of the static table `VG_CAST5_S1234` (or `VG_CAST5_S5678` in key
expansion, `Impl/Cast5/Tables.lean`), 256 entries of four words: a loop over
the entries `j`, in order, whose address it forms with `adrSym`, loading each
of the entry's words `k` and keeping it under a mask that is all ones exactly
if the index in `r4 + k` is `j` (`eor`, then `(x - 1) >> 8` widened), ORed
into `r8 + k`. No secret is an address or a branch condition.

Each function has the scan once: encryption and decryption run their rounds
in a loop whose body is one round, choosing the round's type (1, 2 or 3, a
public count kept in the working space) by a branch; key expansion runs each
half of §2.4 as a loop of 40 steps, each one scan, choosing the step's bytes
and what it does with the four values by a chain of branches on the step's
number (public).

The rotation by the secret amount `Kr` (§2.2) is five rotations by 1, 2, 4,
8 and 16, each kept or not by a mask made from a bit of `Kr` (`rotate`).

The working space `scratch` (`r3` for key expansion, the stack argument for
ECB) is in `r12` throughout; the
callee-saved registers `r4`–`r11` and `lr` are saved in it at `savedOff`, and
`r2` and `r3` during a scan at `spillEcb` or `spillKey`.
-/

@[expose] public section

namespace VG.Impl.Cast5.Arm

open VG.Arm

/-! ## The scan -/

/-- The register of index `k` (0–3) of a scan. -/
def idxReg : Nat → Reg
  | 0 => .r4 | 1 => .r5 | 2 => .r6 | _ => .r7

/-- The register of value `k` (0–3) of a scan. -/
def accReg : Nat → Reg
  | 0 => .r8 | 1 => .r9 | 2 => .r10 | _ => .r11

/-- Lookup `k` at the entry whose number is in `r2` and whose words are at
`r3`: `r1` := word `k` of the entry, `r0` := the mask (all ones iff index `k`
is the entry's number), and `r1` under it ORed into value `k`. -/
def look (k : Nat) : List Instr :=
  [.ldr .r1 .r3 (4 * k), .dp .eor .r0 (idxReg k) (.reg .r2), .dp .sub .r0 .r0 (.imm 1),
   .mov .r0 (.shifted .r0 .lsr 8), .dp .orr .r0 .r0 (.shifted .r0 .lsl 8), .dp .and .r1 .r1 (.reg .r0),
   .dp .orr (accReg k) (accReg k) (.reg .r1)]

/-- The four lookups at an entry. -/
def scanEntry : List Instr := (List.range 4).flatMap look

/-- An entry, then on to the next (Z set after the last, number 255). -/
def scanBody : List Instr :=
  scanEntry ++ ([.dp .add .r3 .r3 (.imm 16), .cmp .r2 (.imm 255), .dp .add .r2 .r2 (.imm 1)] : List Instr)

/-- The scan of the table `sym` (256 entries of four words) at the indices
in `r4`–`r7` (each below 256), into `r8`–`r11`: every entry in turn, its
number in `r2` and its address in `r3`, which are saved at `o` and `o + 4`
in the working space at `r12` meanwhile. Clobbers `r0` and `r1`. -/
def scan (sym : String) (o : Nat) : Prog isa :=
  .seq (.block [.str .r2 .r12 o, .str .r3 .r12 (o + 4), .adrSym .r3 sym, .mov .r2 (.imm 0),
      .mov .r8 (.imm 0), .mov .r9 (.imm 0), .mov .r10 (.imm 0), .mov .r11 (.imm 0)])
    (.seq (.loop (.block scanBody) .ne) (.block [.ldr .r2 .r12 o, .ldr .r3 .r12 (o + 4)]))

/-- Where encryption and decryption save `r2` and `r3` during a scan. -/
def spillEcb : Nat := 24

/-- Where key expansion saves `r2` and `r3` during a scan. -/
def spillKey : Nat := 0

/-- The scan of encryption and decryption: `VG_CAST5_S1234`. -/
def scan1234 : Prog isa := scan s1234Sym spillEcb

/-- The scan of key expansion: `VG_CAST5_S5678`. -/
def scan5678 : Prog isa := scan s5678Sym spillKey

/-! ## The working space -/

/-- Where the callee-saved registers are saved. -/
def savedOff : Nat := 64

def saved : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]

def save : List Instr := saved.zipIdx.map fun (r, i) => .str r .r12 (savedOff + 4 * i)
def restore : List Instr := saved.zipIdx.map fun (r, i) => .ldr r .r12 (savedOff + 4 * i)

/-! ## Encryption and decryption

The slots of the working space: the data pointer, the blocks left, the
schedule, the number of rounds, the rounds left of the current block and the
type of the next round. During the rounds `(L, R)` are in `(r2, r3)` and the
next round's `Kmᵢ` at `lr` (`Krᵢ` at `lr + 64`). -/

def dataOff : Nat := 0
def nOff : Nat := 4
def schedOff : Nat := 8
def roundsOff : Nat := 12
def cntOff : Nat := 16
def typeOff : Nat := 20

/-- `r1` := `I` before the rotation, `Kmᵢ + D`, `Kmᵢ ^ D` or `Kmᵢ - D` for
Type 1, 2 or 3. -/
def mix : Nat → List Instr
  | 1 => [.ldr .r1 .lr 0, .dp .add .r1 .r1 (.reg .r3)]
  | 2 => [.ldr .r1 .lr 0, .dp .eor .r1 .r1 (.reg .r3)]
  | _ => [.ldr .r1 .lr 0, .dp .sub .r1 .r1 (.reg .r3)]

/-- `f` into `r1` from `S1[Ia], S2[Ib], S3[Ic], S4[Id]` in `r11`, `r10`,
`r9`, `r8`. -/
def comb : Nat → List Instr
  | 1 => [.dp .eor .r1 .r11 (.reg .r10), .dp .sub .r1 .r1 (.reg .r9), .dp .add .r1 .r1 (.reg .r8)]
  | 2 => [.dp .sub .r1 .r11 (.reg .r10), .dp .add .r1 .r1 (.reg .r9), .dp .eor .r1 .r1 (.reg .r8)]
  | _ => [.dp .add .r1 .r11 (.reg .r10), .dp .eor .r1 .r1 (.reg .r9), .dp .sub .r1 .r1 (.reg .r8)]

/-- The code of Type 1, 2 or 3 chosen by the type in its slot. -/
def byType (f : Nat → List Instr) : Prog isa :=
  .seq (.block [.ldr .r0 .r12 typeOff, .cmp .r0 (.imm 1)])
    (.ite .eq (.block (f 1)) (.seq (.block [.cmp .r0 (.imm 2)]) (.ite .eq (.block (f 2)) (.block (f 3)))))

/-- One of the five steps of the rotation of `r1` left by the low 5 bits of
`r0` (shifted right by `b` so far): `r4` := 0 if bit 0 of `r0` is set, all
ones if not; the rotation by `2 ^ b` is in `r5`. -/
def rotateStep (b : Nat) : List Instr :=
  ([.dp .and .r4 .r0 (.imm 1), .dp .sub .r4 .r4 (.imm 1), .mov .r5 (.shifted .r1 .ror (32 - 2 ^ b)),
    .dp .eor .r1 .r1 (.reg .r5), .dp .and .r1 .r1 (.reg .r4), .dp .eor .r1 .r1 (.reg .r5)] : List Instr) ++
  (if b < 4 then [.mov .r0 (.shifted .r0 .lsr 1)] else [])

/-- `r1` rotated left by the low 5 bits of `Krᵢ`. Clobbers `r0`, `r4`, `r5`. -/
def rotate : List Instr := [.ldr .r0 .lr 64] ++ (List.range 5).flatMap rotateStep

/-- The bytes `Id, Ic, Ib, Ia` of `I` in `r1` into `r4`–`r7`. -/
def spread : List Instr :=
  [.dp .and .r4 .r1 (.imm 255), .mov .r5 (.shifted .r1 .lsr 8), .dp .and .r5 .r5 (.imm 255),
   .mov .r6 (.shifted .r1 .lsr 16), .dp .and .r6 .r6 (.imm 255), .mov .r7 (.shifted .r1 .lsr 24)]

/-- `(L, R)` := `(R, L ^ f)`, then `lr` to the next round's subkeys: up for
encryption, down for decryption. -/
def feistel (up : Bool) : List Instr :=
  [.dp .eor .r1 .r1 (.reg .r2), .mov .r2 (.reg .r3), .mov .r3 (.reg .r1),
   if up then .dp .add .lr .lr (.imm 4) else .dp .sub .lr .lr (.imm 4)]

/-- The next round's type: 1, 2, 3, 1, … for encryption, 3, 2, 1, 3, … for
decryption; then the rounds left down (Z set at 0). -/
def next (up : Bool) : Prog isa :=
  .seq (.block [.ldr .r0 .r12 typeOff, .cmp .r0 (.imm (if up then 3 else 1))])
    (.seq (.ite .eq (.block [.mov .r0 (.imm (if up then 1 else 3))])
        (.block [if up then .dp .add .r0 .r0 (.imm 1) else .dp .sub .r0 .r0 (.imm 1)]))
      (.block [.str .r0 .r12 typeOff, .ldr .r0 .r12 cntOff, .subs .r0 .r0 (.imm 1), .str .r0 .r12 cntOff]))

/-- A round. -/
def round (up : Bool) : Prog isa :=
  .seq (byType mix) (.seq (.block (rotate ++ spread)) (.seq scan1234
    (.seq (byType comb) (.seq (.block (feistel up)) (next up)))))

/-- The block at the data pointer into `(L₀, R₀)`; `lr` at `Km₁`, the count
and type of encryption's rounds. -/
def startEnc : List Instr :=
  [.ldr .r0 .r12 dataOff, .ldr .r2 .r0 0, .rev .r2 .r2, .ldr .r3 .r0 4, .rev .r3 .r3,
   .ldr .lr .r12 schedOff, .ldr .r1 .r12 roundsOff, .str .r1 .r12 cntOff, .mov .r1 (.imm 1),
   .str .r1 .r12 typeOff]

/-- The same for decryption: `lr` at `Kmₙ`, the type of round `n` (`9 - n / 2`:
1 for 16 rounds, 3 for 12). -/
def startDec : List Instr :=
  [.ldr .r0 .r12 dataOff, .ldr .r2 .r0 0, .rev .r2 .r2, .ldr .r3 .r0 4, .rev .r3 .r3,
   .ldr .lr .r12 schedOff, .ldr .r1 .r12 roundsOff, .str .r1 .r12 cntOff,
   .dp .add .lr .lr (.shifted .r1 .lsl 2), .dp .sub .lr .lr (.imm 4),
   .mov .r0 (.shifted .r1 .lsr 1), .movw .r1 9, .dp .sub .r1 .r1 (.reg .r0), .str .r1 .r12 typeOff]

/-- `(Rₙ, Lₙ)` to the block at the data pointer. The slots of the data
pointer, the blocks left, the schedule and the number of rounds are stored
again afterwards, with the values they hold: the constant-time analysis
forgets what it knows of memory at a store of a secret through a pointer
that is not the base of a buffer, and this keeps them public for the next
block. -/
def finish : List Instr :=
  [.ldr .r0 .r12 dataOff, .ldr .r1 .r12 nOff, .ldr .r4 .r12 schedOff, .ldr .r5 .r12 roundsOff,
   .rev .r3 .r3, .str .r3 .r0 0, .rev .r2 .r2, .str .r2 .r0 4,
   .str .r0 .r12 dataOff, .str .r1 .r12 nOff, .str .r4 .r12 schedOff, .str .r5 .r12 roundsOff]

/-- Encrypting or decrypting the block at the data pointer (slot `dataOff`)
with the schedule and number of rounds in their slots, in place. This is the
block function a mode reuses. -/
def crypt (up : Bool) : Prog isa :=
  .seq (.block (if up then startEnc else startDec)) (.seq (.loop (round up) .ne) (.block finish))

/-- On to the next block (Z set when none are left). -/
def advance : List Instr :=
  [.ldr .r0 .r12 dataOff, .dp .add .r0 .r0 (.imm 8), .str .r0 .r12 dataOff,
   .ldr .r0 .r12 nOff, .subs .r0 .r0 (.imm 1), .str .r0 .r12 nOff]

/-- `vg_cast5_ecb_encrypt(schedule = r0, rounds = r1, data = r2, n = r3,
scratch = [sp])`, or decrypt: each block in turn. -/
def ecb (up : Bool) : Prog isa :=
  .seq (.block ([.ldrSp .r12 0] ++ save ++
      [.str .r2 .r12 dataOff, .str .r3 .r12 nOff, .str .r0 .r12 schedOff, .str .r1 .r12 roundsOff,
       .cmp .r3 (.imm 0)]))
    (.seq (.ite .eq (.block []) (.loop (.seq (crypt up) (.block advance)) .ne)) (.block restore))

def ecbEncrypt : Prog isa := ecb true
def ecbDecrypt : Prog isa := ecb false

/-! ## Key expansion

`x0 … xF` and `z0 … zF` are kept in the working space at `xOff` and `zOff`
(`Impl.Cast5.off`), a byte each; a group's four extra lookups at `extraOff`.
Each half of §2.4 is 40 steps: for each of its eight groups of lines, the
group's extra lookups, then its four lines. The step's number is in `r2`,
the halves left in `r3`, and the next half's subkeys at `lr`. -/

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

/-- The bytes at `d, c, b, a` into `r4`–`r7`, the indices of a scan of
`VG_CAST5_S5678` (`S8, S7, S6, S5`). -/
def gather (a b c d : Pos) : List Instr :=
  [.ldrb .r4 .r12 (srcOff d), .ldrb .r5 .r12 (srcOff c), .ldrb .r6 .r12 (srcOff b),
   .ldrb .r7 .r12 (srcOff a)]

/-- The bytes a step looks up. -/
def Step.gather : Step → List Instr
  | .extras a b c d => Impl.Cast5.Arm.gather a b c d
  | .line l _ => Impl.Cast5.Arm.gather l.main.1 l.main.2.1 l.main.2.2.1 l.main.2.2.2

/-- What a step does with the four values in `r8`–`r11`: keep them as the
group's extra lookups, or XOR them, the line's extra lookup and quadruple
(if any) into `r0` and store it. -/
def Step.post : Step → List Instr
  | .extras .. => [.str .r8 .r12 extraOff, .str .r9 .r12 (extraOff + 4), .str .r10 .r12 (extraOff + 8),
      .str .r11 .r12 (extraOff + 12)]
  | .line l st =>
    ([.dp .eor .r0 .r8 (.reg .r9), .dp .eor .r0 .r0 (.reg .r10), .dp .eor .r0 .r0 (.reg .r11),
      .ldr .r1 .r12 (extraOff + 4 * (8 - l.extra.1)), .dp .eor .r0 .r0 (.reg .r1)] : List Instr) ++
    (match l.word with
      | some (a, q) => [.ldr .r1 .r12 (off a + 4 * q), .rev .r1 .r1, .dp .eor .r0 .r0 (.reg .r1)]
      | none => []) ++
    (match st with
      | .quad a q => [.rev .r0 .r0, .str .r0 .r12 (off a + 4 * q)]
      | .key k => [.str .r0 .lr (4 * k)])

/-- The code `cs[k]` for the step number `k` in `r2` (from `i`), by a chain of
comparisons. -/
def sel : List (List Instr) → Nat → Prog isa
  | [], _ => .block []
  | c :: cs, i => .seq (.block [.cmp .r2 (.imm (BitVec.ofNat 32 i))]) (.ite .eq (.block c) (sel cs (i + 1)))

/-- A step, then the next step's number (Z set after the last). -/
def step : Prog isa :=
  .seq (sel (halfSteps.map Step.gather) 0) (.seq scan5678
    (.seq (sel (halfSteps.map Step.post) 0) (.block [.dp .add .r2 .r2 (.imm 1), .cmp .r2 (.imm 40)])))

/-- A half: its 40 steps, then `lr` on 64 bytes and the halves left down. -/
def half : Prog isa :=
  .seq (.block [.mov .r2 (.imm 0)]) (.seq (.loop step .ne)
    (.block [.dp .add .lr .lr (.imm 64), .subs .r3 .r3 (.imm 1)]))

/-- Copy a key byte to `x`: `r0` at the next key byte, `r3` at its place in
`x`, `r1` the count left. -/
def copyStep : List Instr :=
  [.ldrb .r4 .r0 0, .strb .r4 .r3 0, .dp .add .r0 .r0 (.imm 1), .dp .add .r3 .r3 (.imm 1),
   .subs .r1 .r1 (.imm 1)]

/-- `vg_cast5_expand_key(key = r0, key_len = r1, schedule = r2, scratch =
r3)`: `x` := the key padded with zeros (§2.5), then both halves. -/
def expandKey : Prog isa :=
  .seq (.block ([.mov .r12 (.reg .r3)] ++ save ++
      [.mov .r3 (.imm 0), .str .r3 .r12 xOff, .str .r3 .r12 (xOff + 4), .str .r3 .r12 (xOff + 8),
       .str .r3 .r12 (xOff + 12), .dp .add .r3 .r12 (.imm (BitVec.ofNat 32 xOff))]))
    (.seq (.loop (.block copyStep) .ne)
      (.seq (.block [.mov .lr (.reg .r2), .mov .r3 (.imm 2)]) (.seq (.loop half .ne) (.block restore))))

end VG.Impl.Cast5.Arm
