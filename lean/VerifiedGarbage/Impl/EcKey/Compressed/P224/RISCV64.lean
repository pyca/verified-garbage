module

public import VerifiedGarbage.Impl.EcKey.Compressed.RISCV64
public import VerifiedGarbage.Impl.Ecdh.P224.RISCV64
public import VerifiedGarbage.Impl.EcKey.Compressed.RootTable
public import VerifiedGarbage.Impl.Weierstrass.TCombWords

/-!
# P-224's point compression and decompression on RISC-V

As P-256's (`Impl/EcKey/Compressed/RISCV64.lean`), with P-224's numbers of
28 bytes (`loadNum4`, `storeNum4`), and, as `p ≡ 1 (mod 4)`, the square root
by a table of `Impl/EcKey/Compressed/RootTable.lean` (`root224`, with
`p - 1 = q 16^24` and `c = 11^q`): in Montgomery's form,

1. `w = rhs^((q-1)/2) = rhs^(2^127 - 1)` by its chain (`chainPow`), `r = w rhs`
   and `t = w r = rhs^q`;
2. `s_m = t^(16^m)` for `m < 24`, by four squarings each, in the slots `SS m`;
   the last row of the table, `g^e = c^(e 16^23)`, in the slots `GS e`;
3. digit `j` of `k`, for `j` from 0 to 23 (`digit`): `y = s_(23-j)` times
   the table's entry `T (23 - j + i) dᵢ` for each digit `dᵢ` already found,
   `i < j` (`muls`: each entry read from the table's address plus `512 m +
   32 dᵢ`, `dᵢ` from `s4` for `i < 16`, else `s5`), then
   `dⱼ = Σ_e (16 - e) mod 16` over the `e` with `y - g^e = 0` (`cmps`, by
   masks, into `s6`), or'ed into `s4` or `s5` at `4 (j mod 16)`;
4. `k / 2` (the shift of `s5:s4`), and `y = r Π_i T i eᵢ` for its digits
   (`rootMul`);
5. as P-256's: `y² - rhs`, `y` or `p - y`.

The table `VG_P224_SQRT` (`sqrtWords`) holds `c^(d 16^m)` in Montgomery's
form, 4 words each, entry `16 m + d`. The digits, and so the addresses of
the table's entries read, depend on `rhs`, which the public key determines:
the contract lets timing depend on it. `s4`–`s6` are kept in the working
space's bytes 40–63.
-/

@[expose] public section

namespace VG.Impl.EcKey.Compressed.RISCV64

open VG.RISCV64 VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg VG.Impl.EcKey.Compressed.RISCV64.Cfg

/-! ## The table -/

/-- The table's symbol. -/
def sqrtSym : String := "VG_P224_SQRT"

/-- The table's words: entry `16 m + d` is `c^(d 16^m)` in Montgomery's form,
4 words little-endian. -/
@[irreducible] def sqrtWords : List (BitVec 64) :=
  (List.range 1536).map fun i => wordOf (mont p224 (Impl.EcKey.Compressed.tbl224 (i / 64) (i / 4 % 16)).val) (i % 4)

def sqrtConsts : List (String × List (BitVec 64)) := [(sqrtSym, sqrtWords)]

/-! ## Slots -/

/-- `r`, `y`, an entry of the table, `y - g^e`. -/
def TR := 13
def YS := 15
def XS := 17
def TD := 22

/-- The slot of `s_m = t^(16^m)`, `m < 24`. -/
def SS (m : Nat) : Nat := 55 + m

/-- The slot of `g^e`, `e < 16`. -/
def GS (e : Nat) : Nat := 79 + e

/-- `vg_ec_p224_compress_public_key`. -/
def compressP224 : Prog isa :=
  .seq (.block (saveCode .a2 ++ loadNum4 3 (p224.sl CX) .a1 1 ++ loadNum4 3 (p224.sl CY) .a1 29 ++
    leadMask .a1 ++ sdAt .a7 wb (p224.sl FLAG) ++ constCode p224)) <|
  .seq (wsCall "vg_p224_check_point" checkP224) <|
  .block (ldAt .a7 wb (p224.sl FLAG) ++ [.load .d .t0 wb (p224.sl CY), .logicImm .and .t0 .t0 1, .addi .t0 .t0 2,
      .logic .and .t0 .t0 .a7, .store .b .t0 .s2 0] ++ storeNum4 3 (p224.sl CX) .s2 1 ++ retCode p224)

/-! ## The pieces -/

/-- The chain of `w = rhs^((q-1)/2)`, into `ACC`. -/
def wChain : ChainCfg :=
  ChainCfg.ofExp p224.MP' (p224.sl ACC) (p224.sl RHS) (p224.sl TB) ((Impl.EcKey.Compressed.q224 - 1) / 2)

/-- `r = w rhs` and `t = w r`, for `w` in `ACC`, `t` to `s_0`'s slot. -/
def tonOps : List FOp :=
  [.mul (p224.sl TR) (p224.sl ACC) (p224.sl RHS), .mul (p224.sl (SS 0)) (p224.sl ACC) (p224.sl TR)]

/-- `s_(m+1) = s_m^16`. -/
def sq4 (m : Nat) : List FOp :=
  [.mul (p224.sl (SS (m + 1))) (p224.sl (SS m)) (p224.sl (SS m)),
    .mul (p224.sl (SS (m + 1))) (p224.sl (SS (m + 1))) (p224.sl (SS (m + 1))),
    .mul (p224.sl (SS (m + 1))) (p224.sl (SS (m + 1))) (p224.sl (SS (m + 1))),
    .mul (p224.sl (SS (m + 1))) (p224.sl (SS (m + 1))) (p224.sl (SS (m + 1)))]

/-- `s_1 … s_m`. -/
def schain : Nat → Prog isa
  | 0 => .block []
  | m + 1 => .seq (schain m) (fprog p224Field (sq4 m))

/-- `t0 =` the address of row `m` of the table (`512 m` bytes in), through `t1`. -/
def rowAddr (m : Nat) : List Instr := [.lla .t0 sqrtSym, .li .t1 m, .shift .sll .d .t1 .t1 9, .add .t0 .t0 .t1]

/-- The entry at `t0 + off` to slot `o`, through `t3`. -/
def entCopy (o off : Nat) : List Instr :=
  [.load .d .t3 .t0 off] ++ sdAt .t3 wb (p224.sl o) ++ [.load .d .t3 .t0 (off + 8)] ++ sdAt .t3 wb (p224.sl o + 8) ++
    [.load .d .t3 .t0 (off + 16)] ++ sdAt .t3 wb (p224.sl o + 16) ++
    [.load .d .t3 .t0 (off + 24)] ++ sdAt .t3 wb (p224.sl o + 24)

/-- The entries `g^e`, `e < n`, of the row at `t0`, to their slots. -/
def gcopies : Nat → List Instr
  | 0 => []
  | e + 1 => gcopies e ++ entCopy (GS e) (32 * e)

/-- `s4`–`s6` kept, the last row to `GS`, and no digits yet. -/
def gload : List Instr :=
  [.store .d .s4 wb 40, .store .d .s5 wb 48, .store .d .s6 wb 56] ++ rowAddr 23 ++ gcopies 16 ++ [.li .s4 0, .li .s5 0]

/-- The register of digit `i`: `s4` for `i < 16`, else `s5`. -/
def dreg (i : Nat) : Reg := if i < 16 then .s4 else .s5

/-- The entry of row `m` at digit `i` to `XS`. -/
def lookup (m i : Nat) : List Instr :=
  rowAddr m ++ [.shift .srl .d .t2 (dreg i) (4 * (i % 16)), .logicImm .and .t2 .t2 15, .shift .sll .d .t2 .t2 5,
    .add .t0 .t0 .t2] ++ entCopy XS 0

/-- `[y] = [y] T (m) dᵢ`. -/
def mulStep (y m i : Nat) : Prog isa :=
  .seq (.block (lookup m i)) (mulCall p224Field (p224.sl y) (p224.sl y) (p224.sl XS))

/-- `[y] = [y] Π_(i<n) T (o + i) dᵢ`. -/
def muls (y o : Nat) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (muls y o n) (mulStep y (o + n) n)

/-- `s6 += (16 - e) mod 16` if `y = g^e`. -/
def cmpStep (e : Nat) : Prog isa :=
  .seq (subCall p224Field (p224.sl TD) (p224.sl YS) (p224.sl (GS e)))
    (.block (zeroMask 4 (p224.sl TD) ++ [.logicImm .and .a7 .a7 (((16 - e) % 16 : Nat) : Int), .add .s6 .s6 .a7]))

/-- The comparisons with `g^e`, `e < n`. -/
def cmps : Nat → Prog isa
  | 0 => .block []
  | e + 1 => .seq (cmps e) (cmpStep e)

/-- Digit `j`: `y`, its products, its comparisons, and the digit into its register. -/
def digit (j : Nat) : Prog isa :=
  .seq (.block (copy 4 (p224.sl YS) (p224.sl (SS (23 - j))) ++ [.li .s6 0])) <|
  .seq (muls YS (23 - j) j) <|
  .seq (cmps 16) <|
  .block [.logicImm .and .s6 .s6 15, .shift .sll .d .s6 .s6 (4 * (j % 16)), .logic .or (dreg j) (dreg j) .s6]

/-- Digits `0 … j - 1`. -/
def digits : Nat → Prog isa
  | 0 => .block []
  | j + 1 => .seq (digits j) (digit j)

/-- `s5:s4 >>= 1`, through `t0` and `t1`. -/
def halve : List Instr :=
  [.shift .srl .d .t0 .s4 1, .shift .sll .d .t1 .s5 63, .logic .or .s4 .t0 .t1, .shift .srl .d .s5 .s5 1]

/-- `[ACC] = r Π_i T i eᵢ` for the digits of `k / 2`. -/
def rootMul : Prog isa := .seq (.block (copy 4 (p224.sl ACC) (p224.sl TR) ++ halve)) (muls ACC 0 24)

/-- `s4`–`s6` restored. -/
def restore456 : List Instr := [.load .d .s4 wb 40, .load .d .s5 wb 48, .load .d .s6 wb 56]

/-- Up to the digits: the setup, `rhs`, `w`, `r`, `t`, its powers and the last row. -/
def front224 : Prog isa :=
  .seq (.block (saveCode .a2 ++ loadNum4 3 (p224.sl CX) .a1 1 ++ parCode p224 .a1 ++ tagMask .a1 ++
    sdAt .a7 wb (p224.sl FLAG) ++ constCode p224 ++ ltMask 4 (p224.sl CX) (p224.sl MP) ++ andFlag p224)) <|
  .seq (fprog p224Field (rhsOps p224)) <|
  .seq (chainPow wChain (p224.sl ONEP) p224Field) <|
  .seq (fprog p224Field tonOps) <|
  .seq (schain 23) <|
  .block gload

/-- After the digits: the root, the checks and the output. -/
def tail224 : Prog isa :=
  .seq rootMul <|
  .seq (.block restore456) <|
  .seq (fprog p224Field (rootOps p224)) <|
  .block (zeroMask 4 (p224.sl DIF) ++ andFlag p224 ++ parMask p224 Y1 ++
    sel 4 (p224.sl YF) (p224.sl Y1) (p224.sl Y2) ++ sameMask p224 YF ++ andFlag p224 ++
    ldAt .a7 wb (p224.sl FLAG) ++ pointOut224 CX YF)

/-- `vg_ec_p224_decompress_public_key`. -/
def decompressP224 : Prog isa := .seq front224 (.seq (digits 24) tail224)

end VG.Impl.EcKey.Compressed.RISCV64
