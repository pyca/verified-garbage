import VerifiedGarbage.Impl.Weierstrass.AArch64.Comb

/-!
# Short Weierstrass curves on AArch64: a fixed-base comb from tables in memory

`[k]G` for the fixed point `G` and a scalar `k < 2^(w J)` whose bits are a
table of bytes (byte `t` is bit `t`, as `bits` writes it), from `J` tables of
constants in memory (the `static` `tsym`, `Artifact.consts`, whose address
the code forms with `adrSym`): table `j` holds `[m 2^(wj)]G` for `m = 1 … H` (`H = 2^(w-1)`),
affine and in Montgomery form, entry `m` at `16 n (m - 1)` bytes into the
table (`x` then `y`, `n` words each), the tables `16 n H` bytes apart
(`tcombWords`). With the windows `k_j` of `w` bits of `k` and the digits
`d_j = k_j - H ∈ [-H, H)`, `k = c + Σ d_j 2^(wj)` for `c = H Σ_{j<J} 2^(wj)`:
the accumulator `A` starts at `[c]G` (a constant), and iteration `j` adds the
entry of table `j` for `|d_j|` (or the point at infinity for `d_j = 0`),
negated if `d_j < 0`, by the complete addition for `a = -3`, for
`j = J - 1` down to `0`: `J` additions, and no doublings.

The digits are secret, so their entries are selected in constant time: every
pair of words of every entry of the table is loaded into a vector register,
at an address that depends only on `j` (public), and `bit` inserts it under
a mask that is all ones exactly when its entry's index equals the magnitude
(`selEntry`: `cmeq` of the index, counted in both lanes, with the magnitude
in both lanes). Two groups of registers take the odd and the even entries,
so that the loads of one overlap the masks of the other, and are combined by
`orr` (`selPass`). Each group accumulates at most four pairs: an entry's
`n` pairs in one pass over the table if `n ≤ 4`, else `x`'s and then `y`'s
`n / 2` in two for even `n`, else three at a time (`n` a multiple of 3),
stored at `E.x`, which `E.y` continues. The entry's `Z` is `1`
(Montgomery's, `R mod p`) unless the magnitude is zero, when the entry is
`(0 : 1 : 0)`. The negation computes `0 - y` and selects it by the mask of the
digit's sign.
-/

namespace VG.Impl.Weierstrass.AArch64

open VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass

/-- What the comb needs: the field, the complete addition's slots, the
accumulator `A`, the selected entry `E`, the sum `D`, a slot for `-y` and one
holding zero, the table of the scalar's bits, the slot holding the tables'
address, the digits' width `w` and number `J`, the start `[c]G` and
`R mod p`, both in Montgomery form. -/
structure TCombCfg where
  M : Mod
  S : RcbSlots
  A : Pt
  E : Pt
  D : Pt
  neg : Nat
  zero : Nat
  bits : Nat
  /-- The bytes of the table of bits the scalar's bits fill; the code clears
  those up to `w J`. -/
  kbytes : Nat
  tsym : String
  w : Nat
  J : Nat
  start : Nat × Nat
  one : Nat

/-- The bytes of the window, `x2 = Σ_{i<k} b_i 2^i` for the bytes `b_i` at
`x16 + d + i`, by Horner's rule from the top, through `x4`. -/
def hornerBits : Nat → Nat → List Instr
  | _, 0 => [.movz .x .x2 0 0]
  | d, k + 1 => hornerBits (d + 1) k ++ [.add .x .x2 .x2 .x2, .ldrb .x4 .x16 d, .add .x .x2 .x2 .x4]

/-- `x16 = x0 + w x19`, through `x16`. -/
def winIndex (w : Nat) : List Instr :=
  [.movz .x .x16 (BitVec.ofNat 16 w) 0, .mul .x .x16 .x19 .x16, .add .x .x16 .x0 .x16]

/-- From the window `k` in `x2`: `|k - H|` into `x2`, through `x3`, `x4` and `x9`. -/
def magnitudeH (H : Nat) : List Instr :=
  [.subImm .x .x3 .x2 H, .lsr .x .x4 .x3 63, .movz .x .x9 0 0, .sub .x .x4 .x9 .x4,
    .logic .eor .x .x2 .x3 .x4, .sub .x .x2 .x2 .x4]

/-- `x3` all ones if digit `x19` is negative, that is if the top bit of its
window is clear: `x3 = b_{w-1} - 1`, through `x16`. -/
def signMaskW (w bits : Nat) : List Instr :=
  winIndex w ++ [.ldrb .x3 .x16 (bits + w - 1), .subImm .x .x3 .x3 1]

/-- `[y] = -[y]` (through `[neg]`, with zero at `z`) if digit `x19` is negative. -/
def negYW (M : Mod) (w neg z y bits : Nat) : List Instr :=
  Mont.AArch64.sub M neg z y ++ signMaskW w bits ++ sel M.n y y neg

/-- The registers of `c ≤ 8` words of the selected entry. -/
def selRegs (c : Nat) : List Reg := [.x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15].take c

/-- The registers of the selected entry's `x` and `y` (`2n ≤ 8` words; else
those of each coordinate in turn are among them). -/
def entryRegs (n : Nat) : List Reg := selRegs (2 * n)

/-- The vector registers of the selection of `c ≤ 4` pairs of words, in two
groups taking the odd and the even entries: each group's accumulators, the
registers it loads an entry into, its entries' index and its mask. -/
structure SelGroup where
  acc : List VReg
  ld : List VReg
  idx : VReg
  mask : VReg

def selA (c : Nat) : SelGroup :=
  ⟨[.v0, .v1, .v2, .v3].take c, [.v20, .v21, .v22, .v23].take c, .v17, .v16⟩
def selB (c : Nat) : SelGroup :=
  ⟨[.v4, .v5, .v6, .v7].take c, [.v24, .v25, .v26, .v27].take c, .v30, .v31⟩

/-- The magnitude in `x2` in both lanes of `v19`, `x5 = 1` in both of `v28`
and `2` in both of `v18`. -/
def selBcast : List Instr :=
  [.vop (.dup .d2 .v19 .x2), .vop (.dup .d2 .v28 .x5), .vop (.add .d2 .v18 .v28 .v28)]

/-- `A`'s accumulators `h … h + k - 1` stored at `o`. -/
def selStore (c h k o : Nat) : List Instr :=
  (List.range k).map fun i => .strq ((selA c).acc.getD (h + i) .v0) .x0 (o + 16 * i)

namespace TCombCfg

variable (K : TCombCfg)

/-- `H = 2^(w-1)`, the entries of a table. -/
def H : Nat := 2 ^ (K.w - 1)

/-- The bytes of a table. -/
def tblBytes : Nat := 16 * K.M.n * K.H

/-- Entry `m` (from 1) of the table at `x16` into group `G`: its index `+= 2`
(`v18`), its mask all ones exactly if the index is the magnitude (`v19`),
and its `c` pairs of words from byte `o` inserted under it. -/
def selEntry (o c : Nat) (G : SelGroup) (m : Nat) : List Instr :=
  [.vop (.add .d2 G.idx G.idx .v18), .vop (.cmeq .d2 G.mask G.idx .v19)] ++
    (List.range c).map (fun i => .ldrq (G.ld.getD i .v20) .x16 (16 * K.M.n * (m - 1) + o + 16 * i)) ++
    (List.range c).map fun i => .vop (.bsel .bit (G.acc.getD i .v0) (G.ld.getD i .v20) G.mask)

/-- Every entry's `c` pairs from byte `o` into `selA c`'s accumulators: the
odd entries into `A`, the even ones into `B` (their indices from `-1` and
`0`), then both combined. -/
def selPass (o c : Nat) : List Instr :=
  ([.vop (.movi0 (selA c).idx), .vop (.sub .d2 (selA c).idx (selA c).idx .v28),
    .vop (.movi0 (selB c).idx)] : List Instr) ++
  (((selA c).acc ++ (selB c).acc).map (fun v => .vop (.movi0 v)) : List Instr) ++
  ((List.range (K.H / 2)).flatMap (fun m =>
    K.selEntry o c (selA c) (2 * m + 1) ++ K.selEntry o c (selB c) (2 * m + 2)) : List Instr) ++
  ((List.range c).map fun i =>
    .vop (.logic .orr ((selA c).acc.getD i .v0) ((selA c).acc.getD i .v0) ((selB c).acc.getD i .v0)) : List Instr)

/-- `x16` = table `x19`'s address, from the static `tsym`'s, with `x7 = 0`,
`x5 = 1` and `x1 = 0`, through `x17`. -/
def selSetup : List Instr :=
  [zero7, .adrSym .x16 K.tsym, .movz .x .x17 (BitVec.ofNat 16 K.tblBytes) 0, .mul .x .x17 .x19 .x17,
    .add .x .x16 .x16 .x17, .movz .x .x5 1 0, .movz .x .x1 0 0]

/-- The mask of a zero magnitude into `v16`, and `A`'s accumulators
`h … h + k - 1` set to the pairs of words of `v` (`R`, for `y`) under it,
through `x6` and `v20`. -/
def selOne (v c h k : Nat) : List Instr :=
  [.vop (.movi0 .v16), .vop (.cmeq .d2 .v16 .v16 .v19)] ++
  (List.range k).flatMap fun i =>
    const64 .x6 (wordOf v (2 * i)) ++ ([.vop (.ins .d2 .v20 0 .x6)] : List Instr) ++
    const64 .x6 (wordOf v (2 * i + 1)) ++ ([.vop (.ins .d2 .v20 1 .x6),
    .vop (.bsel .bit ((selA c).acc.getD (h + i) .v0) .v20 .v16)] : List Instr)

/-- `Z` = `R` (the `n` words of `one`) unless the magnitude in `x2` is zero
(with `x5 = 1` and `x7 = 0`), through `x4` and `x6`. -/
def selZ : List Instr :=
  .subs .x .x4 .x2 .x5 :: (List.range K.M.n).flatMap fun i =>
    const64 .x6 (wordOf K.one i) ++ [.csel .x .x6 .x6 .x7, st .x6 (K.E.z + 8 * i)]

/-- The pairs of an entry of an odd number `n` of words (`n` a multiple of
3): `n / 3` passes of three pairs each, from byte `48 i`, under the mask of
a zero magnitude set to those of `(0, R)` (`R` from word `n`), and stored at
`E.x + 48 i`, which `E.y = E.x + 8 n` continues. -/
def selThirds : List Instr :=
  (List.range (K.M.n / 3)).flatMap fun i =>
    K.selPass (48 * i) 3 ++ selOne ((K.one <<< (64 * K.M.n)) >>> (384 * i)) 3 0 3 ++
    selStore 3 0 3 (K.E.x + 48 * i)

/-- The entry of table `x19` for the magnitude in `x2` into `E`: the table's
address into `x16`, the broadcasts, then the entry's pairs selected (if
`n ≤ 4`, all in one pass; else, for even `n`, `x`'s, stored, then `y`'s;
else by thirds), `y = R` if the magnitude is zero, and `Z = R` unless it
is. -/
def select : List Instr :=
  K.selSetup ++ selBcast ++
  (if 2 * K.M.n ≤ 8 then
    K.selPass 0 K.M.n ++ selOne K.one K.M.n (K.M.n / 2) (K.M.n / 2) ++
    selStore K.M.n 0 (K.M.n / 2) K.E.x ++ selStore K.M.n (K.M.n / 2) (K.M.n / 2) K.E.y
  else if K.M.n % 2 = 0 then
    K.selPass 0 (K.M.n / 2) ++ selStore (K.M.n / 2) 0 (K.M.n / 2) K.E.x ++
    K.selPass (8 * K.M.n) (K.M.n / 2) ++ selOne K.one (K.M.n / 2) 0 (K.M.n / 2) ++
    selStore (K.M.n / 2) 0 (K.M.n / 2) K.E.y
  else K.selThirds) ++
  K.selZ

/-- Copy the selected public entry from `x16`, replacing it by `fallback`
when the carry is clear (the zero digit). Only scalar loads are needed. -/
def directWords (src dst fallback count : Nat) : List Instr :=
  (List.range count).flatMap fun i =>
    [.ldr .x .x4 .x16 (src + 8 * i)] ++ const64 .x6 (wordOf fallback i) ++
    [.csel .x .x4 .x4 .x6, st .x4 (dst + 8 * i)]

/-- Address the public digit's entry, clamping zero to the first entry.
The carry records whether the actual digit is nonzero. -/
def directAddress : List Instr :=
  [.subs .x .x3 .x2 .x5, .csel .x .x3 .x3 .x7,
   .movz .x .x17 (BitVec.ofNat 16 (16 * K.M.n)) 0,
   .mul .x .x3 .x3 .x17, .add .x .x16 .x16 .x3]

/-- Direct selection for public scalars only; signing keeps `select`. -/
def selectPublic : List Instr :=
  K.selSetup ++ K.directAddress ++
  directWords 0 K.E.x 0 K.M.n ++ directWords (8 * K.M.n) K.E.y K.one K.M.n ++ K.selZ

/-- The digit's magnitude into `x2`: its window and `|k - H|`. -/
def digit : List Instr := winIndex K.w ++ hornerBits K.bits K.w ++ magnitudeH K.H

/-- Iteration `j = x19 - 1` (with `x19` counting down from `J`): the entry,
negated for a negative digit, added to `A`. -/
def step (publicLookup : Bool := false) : Prog isa :=
  .seq (.block (decCounter :: K.digit ++ (if publicLookup then K.selectPublic else K.select))) <|
  .seq (.block (negYW K.M K.w K.neg K.zero K.E.y K.bits)) <|
  .seq (fprogB K.M (rcb3 K.S K.A K.E K.D)) <|
  .block (copyPt K.M.n K.A K.D)

/-- `A = [c]G`, the bytes of the table of bits past the scalar's cleared (to
`w J`, in words), and the counter. -/
def init : List Instr :=
  setConst K.M.n K.A.x K.start.1 ++ setConst K.M.n K.A.y K.start.2 ++
    setConst K.M.n K.A.z K.one ++
    zero7 :: (List.range ((K.w * K.J - K.kbytes + 7) / 8)).map (fun i => st .x7 (K.bits + K.kbytes + 8 * i)) ++
    [.movz .x .x19 (BitVec.ofNat 16 K.J) 0]

/-- `[k]G` into `A`. -/
def comb (publicLookup : Bool := false) : Prog isa :=
  .seq (.block K.init) (.loop (K.step publicLookup) (.nonzero .x .x19))

end TCombCfg

end VG.Impl.Weierstrass.AArch64
