module

public import VerifiedGarbage.Impl.Weierstrass.Arm.TComb

/-!
# A table of points past the working space's first 4096 bytes, on 32-bit ARM

What the windows of a point's multiplication (`Cfg.mulBody`,
`Impl/Ecdsa/Arm.lean`) keep their table of multiples with. A load or store
reaches 4096 bytes from `r12`, where the slots are, and the table is past
them, so it is reached from a register that is `r12` plus a constant, or
plus a multiple of a public counter:

* `farPtr r d`: `r = r12 + d`;
* `entryPtr tbl bytes`: `r5 = r12 + tbl + bytes · r11`, where entry `r11` of
  a table at `tbl` is;
* `storePt n d p`: the point `p` of the slots to the `24 n` bytes at
  `r5 + d`;
* `scan o k cnt tbl`: entry `r9` of the `cnt` entries of `k` 32-bit words at
  `tbl`, into the slots at `o`, reading every entry and keeping the one whose
  number is `r9` under a mask (the comb's `TCombCfg.eqMask`), so that the
  addresses are those of the counter alone.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.Arm

open VG.Arm VG.Impl.Mont.Arm VG.Impl.Weierstrass

/-- `r = r12 + d`, for `d < 2¹⁶`. -/
def farPtr (r : Reg) (d : Nat) : List Instr := [.movw r (BitVec.ofNat 16 d), .dp .add r wb (.reg r)]

/-- `r5 = r12 + tbl + bytes · r11`, through `r4`. -/
def entryPtr (tbl bytes : Nat) : List Instr :=
  [.mov .r4 (.imm (BitVec.ofNat 32 bytes)), .mul .r4 .r4 .r11] ++ farPtr .r5 tbl ++
    [.dp .add .r5 .r5 (.reg .r4)]

/-- `[r5 + d] = [r12 + a]`, `k` 32-bit words, through `r4`. -/
def storeFar : Nat → Nat → Nat → List Instr
  | 0, _, _ => []
  | k + 1, d, a => [.ldr .r4 wb a, .str .r4 .r5 d] ++ storeFar k (d + 4) (a + 4)

/-- The point `p`, of `n`-word coordinates, to the `24 n` bytes at `r5 + d`. -/
def storePt (n d : Nat) (p : Pt) : List Instr :=
  storeFar (2 * n) d p.x ++ storeFar (2 * n) (d + 8 * n) p.y ++ storeFar (2 * n) (d + 16 * n) p.z

/-- `[r12 + o + 4 i] = [r8 + 4 i]` if the mask `r10` is all ones, through
`r4` and `r5`. -/
def scanWord (o i : Nat) : List Instr :=
  [.ldr .r4 wb (o + 4 * i), .ldr .r5 .r8 (4 * i), .dp .eor .r5 .r5 (.reg .r4), .dp .and .r5 .r5 (.reg .r10),
    .dp .eor .r4 .r4 (.reg .r5), .str .r4 wb (o + 4 * i)]

/-- The scan of entry `r7`, at `r8`: its `k` words to `[r12 + o]` if `r7` is
`r9`, then `r8` at the next entry and `r7` its number, `Z` set once it is
`cnt`. -/
def scanBody (o k cnt : Nat) : List Instr :=
  TCombCfg.eqMask (.reg .r7) ++ (List.range k).flatMap (scanWord o) ++
    [.dp .add .r8 .r8 (.imm (BitVec.ofNat 32 (4 * k))), .dp .add .r7 .r7 (.imm 1),
      .cmp .r7 (.imm (BitVec.ofNat 32 cnt))]

/-- `[r12 + o]` = entry `r9` of the `cnt` entries of `k` 32-bit words at
`r12 + tbl`, for `r9 < cnt`. -/
def scan (o k cnt tbl : Nat) : Prog isa :=
  .seq (.block (farPtr .r8 tbl ++ [.mov .r7 (.imm 0)])) (.loop (.block (scanBody o k cnt)) .ne)

/-! ## A public number's sliding digits, and a table read by a digit

What the multiplication of a point by a public number (`Cfg.pubBody`,
`Impl/Ecdsa/Arm.lean`) adds to the above: its table's entries are read at
the address of a digit, and its branches are on the digits. -/

/-- `[r12 + a] = [r5 + d]`, `k` 32-bit words, through `r4`. -/
def loadFar : Nat → Nat → Nat → List Instr
  | 0, _, _ => []
  | k + 1, d, a => [.ldr .r4 .r5 d, .str .r4 wb a] ++ loadFar k (d + 4) (a + 4)

/-- The point `p`, of `n`-word coordinates, from the `24 n` bytes at `r5 + d`. -/
def loadPt (n d : Nat) (p : Pt) : List Instr :=
  loadFar (2 * n) d p.x ++ loadFar (2 * n) (d + 8 * n) p.y ++ loadFar (2 * n) (d + 16 * n) p.z

/-- The recoding's start: `r6` the table of bits at `r12 + tb`, no bit read
(`r9`), no window in hand (its next bit's weight `r8`, its digit `r7`), and
an address of a window's byte that is in the table (`r3`). -/
def recInit (tb : Nat) : List Instr :=
  farPtr .r6 tb ++ [.mov .r9 (.imm 0), .mov .r8 (.imm 0), .mov .r7 (.imm 0), .mov .r3 (.reg .r6)]

/-- The address of byte `r9` of the table into `r2`, the bit there into
`r1`, and `Z` set with no window in hand. -/
def recHead : List Instr := [.dp .add .r2 .r6 (.reg .r9), .ldrb .r1 .r2 0, .cmp .r8 (.imm 0)]

/-- No window in hand: the bit is the digit, which its byte holds already,
and a window's first if it is set. -/
def recOpen : List Instr := [.mov .r7 (.reg .r1), .mov .r8 (.shifted .r1 .lsl 1), .mov .r3 (.reg .r2)]

/-- A window in hand: the digit is zero, and the bit is added to the window's
digit at the weight `r8`, which doubles, and is none after 8. -/
def recGrow : List Instr :=
  [.mov .r4 (.imm 0), .strb .r4 .r2 0, .dp .sub .r4 .r4 (.reg .r1), .dp .and .r4 .r4 (.reg .r8),
    .dp .add .r7 .r7 (.reg .r4), .strb .r7 .r3 0, .mov .r8 (.shifted .r8 .lsl 1), .dp .and .r8 .r8 (.imm 15)]

/-- The next bit, `Z` set after bit `nb - 1`. -/
def recNext (nb : Nat) : List Instr :=
  [.dp .add .r9 .r9 (.imm 1), .movw .r4 (BitVec.ofNat 16 nb), .cmp .r9 (.reg .r4)]

/-- The `nb` bytes at `r12 + tb`, each a bit of a number from its lowest,
recoded in place into the number's sliding digits, each zero or odd and
below 16 (`Proof/Ed25519/SlidingDigits.lean`): a set bit that no window
covers opens a window of four bits there, whose digit is those bits' value,
and the window's other three digits are zero. -/
def recode (tb nb : Nat) : Prog isa :=
  .seq (.block (recInit tb)) <| .loop (.seq (.block recHead) <|
    .seq (.ite .eq (.block recOpen) (.block recGrow)) (.block (recNext nb))) .ne

/-- Digit `r11` of the digits at `r12 + tb` into `r9`, `Z` set if it is
zero. -/
def digitLoad (tb : Nat) : List Instr :=
  farPtr .r4 tb ++ [.dp .add .r4 .r4 (.reg .r11), .ldrb .r9 .r4 0, .cmp .r9 (.imm 0)]

/-- `r5` = the address of the entry of the odd digit `r9` in a table at
`r12 + tbl` of entries of `2 half` bytes: entry `(r9 - 1) / 2`. -/
def digitEntry (tbl half : Nat) : List Instr :=
  [.dp .sub .r4 .r9 (.imm 1), .mov .r5 (.imm (BitVec.ofNat 32 half)), .mul .r4 .r4 .r5] ++ farPtr .r5 tbl ++
    [.dp .add .r5 .r5 (.reg .r4)]

end VG.Impl.Weierstrass.Arm
