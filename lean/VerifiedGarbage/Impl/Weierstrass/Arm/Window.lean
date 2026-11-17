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

end VG.Impl.Weierstrass.Arm
