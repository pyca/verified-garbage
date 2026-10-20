module

public import VerifiedGarbage.Impl.P384.EcdhDouble
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Comb
import VerifiedGarbage.Impl.Weierstrass.AArch64.WindowJ

/-!
# P-384's entry selection for ECDH's window on AArch64

`sel` selects digit `x19`'s entry of the window's table into `E` as
s2n-bignum's `p384_montjscalarmul_alt` selects: from the digit's magnitude
`|d|` (in `x2`), every candidate `m` of the table is compared with `|d|` once
(`subs`), its 18 words loaded in pairs (`ldp`) and kept in the accumulators
where they are equal (`csel`), starting from `(0 : R : 0)` for `|d| = 0`; the
accumulators are stored to `E` once. The window negates `y` after it
(`WinCfg.entry`).
-/

@[expose] public section

namespace VG.Impl.P384.EcdhSelect
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.P384.EcdhDouble

/-- The accumulators of coordinate `c` (`X`, `Y`, `Z`). -/
def acc : Nat → List Reg
  | 0 => [.x1, .x3, .x4, .x5, .x6, .x7]
  | 1 => [.x8, .x10, .x11, .x12, .x13, .x14]
  | _ => [.x15, .x21, .x22, .x23, .x24, .x25]

/-- The accumulator of word `w` of coordinate `c`. -/
def accReg (c w : Nat) : Reg := (acc c).getD w .x1

/-- The entry of magnitude zero, `(0 : R : 0)`, in the accumulators. -/
def init : List Instr :=
  zeros (acc 0 ++ acc 2) ++
    (List.range 6).flatMap fun w => const64 (accReg 1 w) (wordOf K.one w)

/-- `x9` = the address of the table's first entry. -/
def tblBase : List Instr := [.movz .x .x9 (BitVec.ofNat 16 K.tbl) 0, .add .x .x9 .x0 .x9]

/-- Candidate `m + 1`, at `x9` (moved on to it from candidate `m`'s), kept where
`|d| = m + 1`. -/
def cand (m : Nat) : List Instr :=
  (if m = 0 then [] else [.addImm .x .x9 .x9 (24 * K.M.n)]) ++
  [.movz .x .x16 (BitVec.ofNat 16 (m + 1)) 0, .subs .x .x16 .x2 .x16] ++
  (List.range 9).flatMap fun p =>
    [.ldp .x16 .x17 .x9 (16 * p), .cselc .x (accReg (p / 3) (2 * (p % 3))) .x16 (accReg (p / 3) (2 * (p % 3))) .eq,
      .cselc .x (accReg (p / 3) (2 * (p % 3) + 1)) .x17 (accReg (p / 3) (2 * (p % 3) + 1)) .eq]

/-- Digit `x19`'s entry into `E`: its magnitude (`nibble`, `magnitude`), the
candidates, and the accumulators stored. -/
def sel : List Instr :=
  nibble K.bits ++ magnitude ++ tblBase ++ init ++ (List.range 8).flatMap cand ++
    stores (acc 0) K.E.x ++ stores (acc 1) K.E.y ++ stores (acc 2) K.E.z

end VG.Impl.P384.EcdhSelect
