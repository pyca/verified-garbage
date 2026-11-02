module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Comb

/-!
# `[k]Q` by four-bit windows on RISC-V

`vg_<curve>_mul(ws)` for a curve with `a = -3`, on the layout of
`Impl/Ecdsa/RISCV64.lean` (`Q` affine in `R`'s first two slots, `k` at
`K`'s slot, the result in `R`), in place of the ladder over every bit:

1. `b` in Montgomery's form to slot 40 (`BP`), which the complete addition
   for `a = -3` reads (`rcb3`);
2. the table of `[e]Q` for `e < 16` from byte 2048 (`entry e`, `24 n` bytes
   each): `O = (0 : 1 : 0)` and `Q = (x : y : 1)` copied in, then
   `[e]Q = [e - 1]Q + Q` by fourteen complete additions;
3. from `R = O`, for the windows `j` from `16 n - 1` down to `0` (the
   counter `s1 = j + 1`, then `j`), `R = 16 R + [k_j]Q` for the nibble
   `k_j` of `k`:
   * the nibble (`nibble`: the word `j >>> 4` shifted right by `4 j`,
     which `srl` takes modulo 64) and the masks of its four bits (the
     comb's `maskOfBit`), then the entry by the comb's tree of selections
     over the sixteen entries at `a0 = s0 + 2048` (`scanWord`), into `E`;
   * `R = 16 R` (`quad`): `R` in Jacobian coordinates (`toJ`), four
     doublings (`dblJ`, dbl-2001-b), back in projective coordinates
     (`fromJ`), and `Y = 1` where `Z = 0` (the double of `O`);
   * `T = R + E` by the complete addition, copied to `R`.

The only branch is on the counter, and every address is `s0` plus a
constant, plus `8 (j >>> 4)` for the nibble's word: only the pointer may
affect timing.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64.Window

open VG.RISCV64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Impl.Ecdsa.RISCV64.Comb (treeAt treeRegs)

/-- The slots of the selected entry `E`. -/
def EX := 58
def EY := 59
def EZ := 60

/-- The number of windows of `k`. -/
def windows (c : Cfg) : Nat := 16 * c.n

namespace Cfg

variable (c : Cfg)

/-- The bytes of an entry. -/
def eb : Nat := 24 * c.n

/-- Entry `e` of the table. -/
def entry (e : Nat) : Pt := ⟨2048 + eb c * e, 2048 + eb c * e + 8 * c.n, 2048 + eb c * e + 16 * c.n⟩

/-- Zero, as a point (`toJ` and `fromJ` add zero to copy). -/
def zeroPt : Pt := c.pt ZERO ZERO ZERO

/-- `o = p + q` by the complete addition for `a = -3`. -/
def addPt (p q o : Pt) : Prog isa := fprog c.FP (rcb3 c.rcb3Slots p q o)

/-- `o = p`. -/
def copyPt (o p : Pt) : List Instr := copy c.n o.x p.x ++ copy c.n o.y p.y ++ copy c.n o.z p.z

/-- `[e]Q = [e - 1]Q + Q`, for `e` from 2 up to `e + 1`. -/
def adds : Nat → Prog isa
  | 0 => .block []
  | e + 1 => .seq (adds e) (addPt c (entry c (e + 1)) (entry c 1) (entry c (e + 2)))

/-- `b R mod p` to slot 40, then the table: `O`, `Q`, and `[e]Q` for
`e = 2 … 15`. -/
def build : Prog isa :=
  .seq (.block (Ecdh.RISCV64.setConst c.n (c.sl 40) (Ecdh.RISCV64.Cfg.mont c c.C.b) ++
    copyPt c (entry c 0) (c.pt ZERO ONEP ZERO) ++ copyPt c (entry c 1) (c.pt RX RY ONEP)))
    (adds c 14)

/-- The nibble `k_j` of `k` into `t2`, for `j` in `s1`: the word `j >>> 4`
shifted right by `4 j` (modulo 64), and four bits of it. -/
def nibble : List Instr :=
  [.shift .srl .d .t0 ctr 4, .shift .sll .d .t0 .t0 3, .add .t0 .t0 wb, .load .d .t2 .t0 (c.sl K),
    .shift .sll .d .t1 ctr 2, .shiftReg .srl .d .t2 .t2 .t1, .logicImm .and .t2 .t2 15]

/-- Quadword `q` of the entry selected into `t0`, then to `E` at `8 q`. -/
def scanWord (q : Nat) : List Instr :=
  treeAt .a0 (eb c) 4 (8 * q) treeRegs ++ sdAt .t0 wb (c.sl EX + 8 * q)

/-- The entry of the nibble to `E`: the nibble, its bits' masks, `a0` at the
table, and its `3 n` quadwords. -/
def select : List Instr :=
  nibble c ++ (List.range 4).flatMap Comb.Cfg.maskOfBit ++ [.addi .a0 wb 2047, .addi .a0 .a0 1] ++
    (List.range (3 * c.n)).flatMap (scanWord c)

/-- `R = 16 R`: to Jacobian coordinates in `D`, four doublings between `D`
and `T`, back to `R`, then `Y = 1` where `Z` is zero. -/
def quad : Prog isa :=
  let S := c.rcb3Slots
  let R := c.pt RX RY RZ
  let D := c.pt DX DY DZ
  let T := c.pt TX TY TZ
  progs [fprog c.FP (toJ S R (zeroPt c) D), fprog c.FP (dblJ S D T), fprog c.FP (dblJ S T D),
    fprog c.FP (dblJ S D T), fprog c.FP (dblJ S T D), fprog c.FP (fromJ S D (zeroPt c) R),
    .block (Ecdh.RISCV64.zeroMask c.n (c.sl RZ) ++ sel c.n (c.sl RY) (c.sl RY) (c.sl ONEP))]

/-- One window: `s1 -= 1`, the entry `E` of the nibble, `R = 16 R`, and
`R = R + E`. -/
def step : Prog isa :=
  .seq (.block (decCounter :: select c)) <|
  .seq (quad c) <|
  .seq (addPt c (c.pt RX RY RZ) (c.pt EX EY EZ) (c.pt TX TY TZ))
    (.block (copyPt c (c.pt RX RY RZ) (c.pt TX TY TZ)))

/-- The body: the table, `R = O`, then the windows. -/
def body : Prog isa :=
  .seq (build c) <|
  .seq (.block (copyPt c (c.pt RX RY RZ) (c.pt ZERO ONEP ZERO) ++ [.li ctr (windows c)]))
    (.loop (step c) more)

/-- `vg_<curve>_mul(ws = a0)`: `s0`, `s1` and `ra` kept around the body, as
`Cfg.mulFn` does, with the working space's base in `s0`. -/
def mulFn : Prog isa :=
  .seq (.block (sdAt .s0 .a0 c.mulSave ++ sdAt .s1 .a0 (c.mulSave + 8) ++ sdAt .ra .a0 (c.mulSave + 16) ++
    [.addi .s0 .a0 0])) <|
  .seq (body c) (.block (ldAt .ra .s0 (c.mulSave + 16) ++ ldAt .s1 .s0 (c.mulSave + 8) ++
    ldAt .s0 .s0 c.mulSave))

end Cfg

/-- `vg_p256_mul` by windows. -/
def mulP256 : Prog isa := Cfg.mulFn p256

end VG.Impl.Ecdsa.RISCV64.Window
