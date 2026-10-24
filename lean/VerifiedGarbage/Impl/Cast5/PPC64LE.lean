module

public import VerifiedGarbage.Impl.Cast5.Tables
public import VerifiedGarbage.Impl.Cast5.Lines
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# CAST5 on PPC64LE

The design of ARMv7's (`Impl/Cast5/Arm.lean`). A lookup in an S-box never
uses a secret as an address: the four lookups a round function (or a line of
key expansion) makes are made at once by a *scan* of the static table
`VG_CAST5_S1234` (or `VG_CAST5_S5678` in key expansion,
`Impl/Cast5/Tables.lean`), 256 entries of four words: a loop over the
entries `j`, in order, loading each of the entry's words `k` and keeping it
under a mask that is all ones exactly if the index in `r14 + k` is `j`
(`xor`, then `0 - ((x - 1) >> 63)`), ORed into `r18 + k`. No secret is an
address or a branch condition.

Each function has the scan once: encryption and decryption run their rounds
in a loop whose body is one round, choosing the round's type (its number
modulo 3, as `Spec.Cast5.f` does) by a branch; key expansion runs each half
of §2.4 as a loop of 40 steps, each one scan, choosing the step's bytes and
what it does with the four values by a chain of branches on the step's
number. The rotation by the secret amount `Kr` (§2.2) is five rotations by
1, 2, 4, 8 and 16, each kept or not by a mask made from a bit of `Kr`.

Every public value (pointers, counts, the round's type, the step's number,
the table's address) stays in a register: the working space `scratch`
(`r7` for ECB, `r6` for key expansion) holds the caller's `r14`–`r30` and
`LR` (at `savedOff`, which `adrSym` changes) and, in key expansion, `x`,
`z` and a group's extra lookups. `r0` is zero once the prologue has run.
-/

@[expose] public section

namespace VG.Impl.Cast5.PPC64LE

open VG.PPC64LE

/-! ## Registers -/

abbrev zero : Reg := .r0
/-- The table's address. -/
abbrev tbl : Reg := .r27
/-- The constant 255. -/
abbrev c255 : Reg := .r26
/-- The scan's entry number and its address. -/
abbrev num : Reg := .r22
abbrev ep : Reg := .r23
/-- Temporaries. -/
abbrev tmp : Reg := .r24
abbrev wd : Reg := .r25
/-- `I`, then `f`, of a round, or the value of a line of key expansion. -/
abbrev vI : Reg := .r28
/-- `Kr` of a round and the rotation's mask. -/
abbrev vKr : Reg := .r29
abbrev msk : Reg := .r30

/-- `mr d, n` (`or d, n, n`). -/
def mov (d n : Reg) : Instr := .logic .or d n n

/-! ## The scan -/

/-- The register of index `k` (0–3) of a scan. -/
def idxReg : Nat → Reg
  | 0 => .r14 | 1 => .r15 | 2 => .r16 | _ => .r17

/-- The register of value `k` (0–3) of a scan. -/
def accReg : Nat → Reg
  | 0 => .r18 | 1 => .r19 | 2 => .r20 | _ => .r21

/-- Lookup `k` at the entry whose number is in `num` and whose words are at
`ep`: `wd` := word `k` of the entry, `tmp` := the mask (all ones iff index
`k` is the entry's number), and `wd` under it ORed into value `k`. -/
def look (k : Nat) : List Instr :=
  [.load .w wd ep (4 * k), .logic .xor tmp (idxReg k) num, .subi tmp tmp 1, .lsr .d tmp tmp 63,
   .sub tmp zero tmp, .logic .and wd wd tmp, .logic .or (accReg k) (accReg k) wd]

/-- The four lookups at an entry. -/
def scanEntry : List Instr := (List.range 4).flatMap look

/-- An entry, then on to the next (`tmp` zero after the last, number 255). -/
def scanBody : List Instr :=
  scanEntry ++ ([.addi ep ep 16, .addi num num 1, .subi tmp num 256] : List Instr)

/-- The scan of the table at `tbl` (256 entries of four words) at the
indices in `r14`–`r17` (each below 256), into `r18`–`r21`: every entry in
turn, its number in `num` and its address in `ep`. Clobbers `tmp` and
`wd`. -/
def scan : Prog isa :=
  .seq (.block [mov ep tbl, .li num 0, .li (accReg 0) 0, .li (accReg 1) 0, .li (accReg 2) 0,
      .li (accReg 3) 0])
    (.loop (.block scanBody) (.nonzero .d tmp))

/-! ## The working space -/

/-- Where the callee-saved registers and `LR` are saved. -/
def savedOff : Nat := 64

/-- The callee-saved registers the code uses. -/
def saved : List Reg := [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25,
  .r26, .r27, .r28, .r29, .r30]

/-- Where `LR` is saved. -/
def lrOff : Nat := savedOff + 8 * saved.length

/-- The saved registers and their offsets. -/
def savedSlots : List (Reg × Nat) := saved.zipIdx.map fun (r, i) => (r, savedOff + 8 * i)

/-- `LR` and the callee-saved registers saved in the working space at `b`,
then the table's address in `tbl`, 255 in `c255` and zero in `r0`. -/
def prologue (b : Reg) (sym : String) : List Instr :=
  ([.mflr .r0, .store .d .r0 b lrOff] : List Instr) ++ savedSlots.map (fun (r, d) => .store .d r b d) ++
  ([.adrSym tbl sym, .li c255 255, .li zero 0] : List Instr)

/-- The callee-saved registers and `LR` restored from the working space at `b`. -/
def epilogue (b : Reg) : List Instr :=
  savedSlots.map (fun (r, d) => .load .d r b d) ++ ([.load .d .r0 b lrOff, .mtlr .r0] : List Instr)

/-! ## Encryption and decryption

`vg_cast5_ecb_encrypt(schedule = r3, rounds = r4, data = r5, n = r6,
scratch = r7)`. During the rounds `(L, R)` are in `(r8, r9)` (their low
words), the next round's `Kmᵢ` at `r10` (`Krᵢ` at `r10 + 64`), the rounds
left of the block in `r11` and the next round's number modulo 3 in `r12`. -/

abbrev sch : Reg := .r3
abbrev rnd : Reg := .r4
abbrev dat : Reg := .r5
abbrev cnt : Reg := .r6
abbrev wkE : Reg := .r7
abbrev xL : Reg := .r8
abbrev xR : Reg := .r9
abbrev km : Reg := .r10
abbrev left : Reg := .r11
abbrev typ : Reg := .r12

/-- `I` before the rotation, into `vI`: `Kmᵢ - D`, `Kmᵢ + D` or `Kmᵢ ^ D`
for a round number 0, 1 or 2 modulo 3 (Type 3, 1, 2). -/
def mix : Nat → List Instr
  | 1 => [.load .w vI km 0, .add vI vI xR]
  | 2 => [.load .w vI km 0, .logic .xor vI vI xR]
  | _ => [.load .w vI km 0, .sub vI vI xR]

/-- `f` into `vI` from `S1[Ia], S2[Ib], S3[Ic], S4[Id]` in `r21`, `r20`,
`r19`, `r18`. -/
def comb : Nat → List Instr
  | 1 => [.logic .xor vI (accReg 3) (accReg 2), .sub vI vI (accReg 1), .add vI vI (accReg 0)]
  | 2 => [.sub vI (accReg 3) (accReg 2), .add vI vI (accReg 1), .logic .xor vI vI (accReg 0)]
  | _ => [.add vI (accReg 3) (accReg 2), .logic .xor vI vI (accReg 1), .sub vI vI (accReg 0)]

/-- The code for the round number modulo 3 in `typ`. -/
def byType (f : Nat → List Instr) : Prog isa :=
  .ite (.zero .d typ) (.block (f 0))
    (.seq (.block [.subi tmp typ 1]) (.ite (.zero .d tmp) (.block (f 1)) (.block (f 2))))

/-- One of the five steps of the rotation of `vI` left by the low 5 bits of
`vKr`: `msk` := 0 if bit `b` of `vKr` is set, all ones if not; the rotation
by `2 ^ b` is in `tmp`. -/
def rotateStep (b : Nat) : List Instr :=
  [.lsl msk vKr (63 - b), .lsr .d msk msk 63, .subi msk msk 1, .rotr .w tmp vI (32 - 2 ^ b),
   .logic .xor wd vI tmp, .logic .and wd wd msk, .logic .xor vI tmp wd]

/-- `vI` rotated left by the low 5 bits of `Krᵢ`. -/
def rotate : List Instr := [.load .w vKr km 64] ++ (List.range 5).flatMap rotateStep

/-- The bytes `Id, Ic, Ib, Ia` of `I` in `vI` into `r14`–`r17`. -/
def spread : List Instr :=
  [.logic .and (idxReg 0) vI c255, .lsr .w (idxReg 1) vI 8, .logic .and (idxReg 1) (idxReg 1) c255,
   .lsr .w (idxReg 2) vI 16, .logic .and (idxReg 2) (idxReg 2) c255, .lsr .w (idxReg 3) vI 24]

/-- `(L, R)` := `(R, L ^ f)`, then `km` to the next round's subkeys: up for
encryption, down for decryption. -/
def feistel (up : Bool) : List Instr :=
  [.logic .xor vI vI xL, mov xL xR, mov xR vI, if up then .addi km km 4 else .subi km km 4]

/-- The next round's number modulo 3: 1, 2, 0, 1, … for encryption, 1, 0,
2, 1, … (or 0, 2, 1, …) for decryption; then the rounds left down. -/
def next (up : Bool) : Prog isa :=
  .seq (if up then .seq (.block [.subi tmp typ 2]) (.ite (.zero .d tmp) (.block [.li typ 0])
      (.block [.addi typ typ 1]))
    else .ite (.zero .d typ) (.block [.li typ 2]) (.block [.subi typ typ 1]))
    (.block [.subi left left 1])

/-- A round. -/
def round (up : Bool) : Prog isa :=
  .seq (byType mix) (.seq (.block (rotate ++ spread)) (.seq scan
    (.seq (byType comb) (.seq (.block (feistel up)) (next up)))))

/-- The block at `p` into `(L₀, R₀)` (big-endian); `km` at `Km₁`, the
count of rounds and the number of the first, 1. -/
def startEnc (p : Reg) : List Instr :=
  [.loadRev .w xL p zero, .addi tmp p 4, .loadRev .w xR tmp zero, mov km sch, mov left rnd, .li typ 1]

/-- The same for decryption: `km` at `Kmₙ`, the number of round `n` modulo
3 (`n / 4 - 3`: 1 for 16 rounds, 0 for 12). -/
def startDec (p : Reg) : List Instr :=
  [.loadRev .w xL p zero, .addi tmp p 4, .loadRev .w xR tmp zero, .lsl tmp rnd 2, .add km sch tmp,
   .subi km km 4, mov left rnd, .lsr .d tmp rnd 2, .subi typ tmp 3]

/-- `(Rₙ, Lₙ)` to the block at `p`, big-endian. -/
def finish (p : Reg) : List Instr :=
  [.storeRev .w xR p zero, .addi tmp p 4, .storeRev .w xL tmp zero]

/-- Encrypting (`up`) or decrypting the block at `p` with the schedule at
`sch` and the number of rounds in `rnd`, in place. This is the block
function a mode reuses. -/
def crypt (up : Bool) (p : Reg) : Prog isa :=
  .seq (.block (if up then startEnc p else startDec p)) (.seq (.loop (round up) (.nonzero .d left))
    (.block (finish p)))

/-- `vg_cast5_ecb_encrypt(schedule = r3, rounds = r4, data = r5, n = r6,
scratch = r7)`, or decrypt: each block in turn. -/
def ecb (up : Bool) : Prog isa :=
  .seq (.block (prologue wkE s1234Sym))
    (.seq (.ite (.zero .d cnt) (.block [])
      (.loop (.seq (crypt up dat) (.block [.addi dat dat 8, .subi cnt cnt 1])) (.nonzero .d cnt)))
      (.block (epilogue wkE)))

def ecbEncrypt : Prog isa := ecb true
def ecbDecrypt : Prog isa := ecb false

/-! ## Key expansion

`vg_cast5_expand_key(key = r3, key_len = r4, schedule = r5, scratch =
r6)`. `x0 … xF` and `z0 … zF` are kept in the working space at `xOff` and
`zOff` (`Impl.Cast5.off`), a byte each; a group's four extra lookups at
`extraOff`. Each half of §2.4 is 40 steps: for each of its eight groups of
lines, the group's extra lookups, then its four lines. The step's number is
in `stp`, the halves left in `halves`, and the next half's subkeys at
`out`. -/

abbrev key : Reg := .r3
abbrev klen : Reg := .r4
abbrev out : Reg := .r5
abbrev wkK : Reg := .r6
abbrev dst : Reg := .r7
abbrev stp : Reg := .r11
abbrev halves : Reg := .r12

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

/-- The bytes at `d, c, b, a` into `r14`–`r17`, the indices of a scan of
`VG_CAST5_S5678` (`S8, S7, S6, S5`). -/
def gather (a b c d : Pos) : List Instr :=
  [.lbz (idxReg 0) wkK (srcOff d), .lbz (idxReg 1) wkK (srcOff c), .lbz (idxReg 2) wkK (srcOff b),
   .lbz (idxReg 3) wkK (srcOff a)]

/-- The bytes a step looks up. -/
def Step.gather : Step → List Instr
  | .extras a b c d => Impl.Cast5.PPC64LE.gather a b c d
  | .line l _ => Impl.Cast5.PPC64LE.gather l.main.1 l.main.2.1 l.main.2.2.1 l.main.2.2.2

/-- What a step does with the four values in `r18`–`r21`: keep them as the
group's extra lookups, or XOR them, the line's extra lookup and quadruple
(if any, big-endian) into `vI` and store it. -/
def Step.post : Step → List Instr
  | .extras .. => [.store .w (accReg 0) wkK extraOff, .store .w (accReg 1) wkK (extraOff + 4),
      .store .w (accReg 2) wkK (extraOff + 8), .store .w (accReg 3) wkK (extraOff + 12)]
  | .line l st =>
    ([.logic .xor vI (accReg 0) (accReg 1), .logic .xor vI vI (accReg 2), .logic .xor vI vI (accReg 3),
      .load .w tmp wkK (extraOff + 4 * (8 - l.extra.1)), .logic .xor vI vI tmp] : List Instr) ++
    (match l.word with
      | some (a, q) => [.li wd (off a + 4 * q), .loadRev .w tmp wkK wd, .logic .xor vI vI tmp]
      | none => []) ++
    (match st with
      | .quad a q => [.li wd (off a + 4 * q), .storeRev .w vI wkK wd]
      | .key k => [.store .w vI out (4 * k)])

/-- The code `cs[k]` for the step number `k` in `stp` (from `i`), by a chain
of comparisons. -/
def sel : List (List Instr) → Nat → Prog isa
  | [], _ => .block []
  | c :: cs, i => .seq (.block [.subi tmp stp i]) (.ite (.zero .d tmp) (.block c) (sel cs (i + 1)))

/-- A step, then the next step's number (`tmp` zero after the last). -/
def step : Prog isa :=
  .seq (sel (halfSteps.map Step.gather) 0) (.seq scan
    (.seq (sel (halfSteps.map Step.post) 0) (.block [.addi stp stp 1, .subi tmp stp 40])))

/-- A half: its 40 steps, then `out` on 64 bytes and the halves left down. -/
def half : Prog isa :=
  .seq (.block [.li stp 0]) (.seq (.loop step (.nonzero .d tmp))
    (.block [.addi out out 64, .subi halves halves 1]))

/-- Copy a key byte to `x`: `key` at the next key byte, `dst` at its place in
`x`, `klen` the count left. -/
def copyStep : List Instr :=
  [.lbz tmp key 0, .stb tmp dst 0, .addi key key 1, .addi dst dst 1, .subi klen klen 1]

/-- `vg_cast5_expand_key(key = r3, key_len = r4, schedule = r5, scratch =
r6)`: `x` := the key padded with zeros (§2.5), then both halves. -/
def expandKey : Prog isa :=
  .seq (.block (prologue wkK s5678Sym ++
      ([.store .d zero wkK xOff, .store .d zero wkK (xOff + 8), .addi dst wkK xOff] : List Instr)))
    (.seq (.loop (.block copyStep) (.nonzero .d klen))
      (.seq (.block [.li halves 2]) (.seq (.loop half (.nonzero .d halves)) (.block (epilogue wkK)))))

end VG.Impl.Cast5.PPC64LE
