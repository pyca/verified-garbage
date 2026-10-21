module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# ML-KEM on AArch64: the NTT halfword by halfword

`St.runP` follows the code of the 16-bit NTT (`Impl/MlKem/AArch64/Ntt16.lean`)
on terms: each of the eight halfwords of every vector register, and of every
16-byte chunk of the regions of memory the code reads and writes, is a term
(`T`): coefficient `p` of the polynomial after `st` layers of `NTT`
(`lv st p`), its reduced value (`out p`), a constant, one of the
intermediate values of a butterfly or of the reduction, or a halfword the
machine does not follow (`junk`). The terms of a butterfly whose halfwords are
`lv st p` and `lv st (p + len)`, with the zeta of their block, become
`lv (st + 1) p` and `lv (st + 1) (p + len)`, and those of the reduction of the
last layer's `lv st p` become `out p`; any other operation gives `junk`.

The kernel evaluates the machine, so its data are numbers: a term is a
number (`T`), and the vector registers, the general registers and each region
of memory are numbers packing their terms (`slot`, `upd`), which the kernel
computes once at each step.

The general registers are followed as pointers into the regions or as
numbers (`G`), so that the machine runs the loops of the code: each
iteration once, until the counter it tests is zero.

`Sound.lean` proves the machine agrees with the code.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64

/-! ## Packed numbers -/

/-- Slot `i` of `w` bits of `n`. -/
def slot (w n i : Nat) : Nat := Nat.mod (Nat.div n (Nat.pow 2 (Nat.mul w i))) (Nat.pow 2 w)

/-- `n` with slot `i` of `w` bits replaced by `x` (`x < 2 ^ w`). -/
def upd (w n i x : Nat) : Nat :=
  Nat.add (Nat.sub n (Nat.mul (slot w n i) (Nat.pow 2 (Nat.mul w i)))) (Nat.mul x (Nat.pow 2 (Nat.mul w i)))

/-! ## Terms -/

/-- A term: `kind + 16 · (st + 16 · (p + 512 · (z + 4096 · t)))`. -/
abbrev T := Nat

/-- The kinds of terms. -/
inductive K
  /-- Not followed. -/
  | junk
  /-- Coefficient `p` after `st` layers. -/
  | lv
  /-- Coefficient `p` after the last layer, reduced. -/
  | out
  /-- The constant `t`. -/
  | c
  /-- `lv st p · z`. -/
  | mulC
  /-- `sqrdmulh(lv st p, t)`. -/
  | qdC
  /-- `sqrdmulh(lv st p, t) · q`. -/
  | mulQ
  /-- `lv st p · z - sqrdmulh(lv st p, t) · q`: `lv st p · z mod q`. -/
  | mm
  /-- `lv st p - sqrdmulh(lv st p, 10) · q`: `lv st p` reduced to `(-q, q)`. -/
  | n1
  /-- `n1 st p >> 15` (arithmetic). -/
  | sraN
  /-- `(n1 st p >> 15) & q`. -/
  | andN
  /-- A Gentleman–Sande difference `lv st p - lv st p₀` (`p₀` in `z`). -/
  | dif
  /-- `dif st p p₀ · z` (`z` in `t`). -/
  | mulD
  /-- `sqrdmulh(dif st p p₀, t)`. -/
  | qdD
  /-- `sqrdmulh(dif st p p₀, t) · q`. -/
  | mulQD
  deriving DecidableEq, Inhabited

def K.code : K → Nat
  | .junk => 0 | .lv => 1 | .out => 2 | .c => 3 | .mulC => 4 | .qdC => 5 | .mulQ => 6 | .mm => 7
  | .n1 => 8 | .sraN => 9 | .andN => 10 | .dif => 11 | .mulD => 12 | .qdD => 13 | .mulQD => 14

def T.kind (a : T) : Nat := Nat.mod a 16
def T.st (a : T) : Nat := Nat.mod (Nat.div a 16) 16
def T.p (a : T) : Nat := Nat.mod (Nat.div a 256) 512
def T.z (a : T) : Nat := Nat.mod (Nat.div a 131072) 4096
def T.t (a : T) : Nat := Nat.mod (Nat.div a 536870912) 65536

/-- The term of kind `k` with its fields. -/
def mk (k : K) (st p z t : Nat) : T :=
  Nat.add k.code (Nat.mul 16 (Nat.add (Nat.mod st 16) (Nat.mul 16 (Nat.add (Nat.mod p 512)
    (Nat.mul 512 (Nat.add (Nat.mod z 4096) (Nat.mul 4096 (Nat.mod t 65536))))))))

def lvT (st p : Nat) : T := mk .lv st p 0 0
def outT (p : Nat) : T := mk .out 0 p 0 0
def cT (v : Nat) : T := mk .c 0 0 0 v
def junkT : T := 0

/-- `q`. -/
def qN : Nat := 3329

/-- `round(z · 2¹⁵ / q)`, as the code computes it. -/
abbrev twN (z : Nat) : Nat := Impl.MlKem.AArch64.Ntt16.tw z

/-! ## The layers -/

/-- The layers of a transform: its number of levels, its zetas by index, and
whether it is `NTT⁻¹`. `NTT` has seven Cooley–Tukey layers (layer `st` at
distance `128 >>> st`); `NTT⁻¹`'s levels are its Gentleman–Sande layers, the
reductions between them (`invRed`) and the multiplication by 3303. -/
structure Rules where
  layers : Nat
  zeta : Nat → Nat
  inv : Bool := false

/-- `ζ_k`, as the code takes it. -/
def zetaN (k : Nat) : Nat := Impl.MlKem.AArch64.Ntt16.zeta k

/-- `NTT`: seven Cooley–Tukey layers. -/
def fwdRules : Rules := { layers := 7, zeta := zetaN }

/-- The distance of `NTT⁻¹`'s layer at level `st`, `0` at the other levels:
the layers with `len = 2, 4, 8`, a reduction, `16, 32, 64`, a reduction, `128`,
then the multiplication by 3303. -/
def invLen (st : Nat) : Nat :=
  bif Nat.blt st 3 then 2 <<< st else bif Nat.beq st 3 then 0 else bif Nat.blt st 7 then 2 <<< (st - 1)
  else bif Nat.beq st 8 then 128 else 0

/-- The levels of `NTT⁻¹` that reduce every coefficient to `(-q, q)`. -/
def invRed (st : Nat) : Bool := Nat.beq st 3 || Nat.beq st 7

/-- The level of `NTT⁻¹`'s multiplication by 3303. -/
def invScale : Nat := 9

/-- `NTT⁻¹`: ten levels. -/
def invRules : Rules := { layers := 10, zeta := zetaN, inv := true }

/-- The Gentleman–Sande pair `p`, `p'` of `NTT⁻¹`'s level `st`. -/
def gsPair (st p p' : Nat) : Bool :=
  let len := invLen st
  Nat.blt 0 len && Nat.beq p' (p + len) && Nat.blt (p % (2 * len)) len && Nat.blt p' 256

/-- The zeta `z` (and its `tw` `t`) of the block of `p'` in `NTT⁻¹`'s level `st`. -/
def gsZeta (st p' z t : Nat) : Bool :=
  let len := invLen st
  Nat.beq z (zetaN (256 / len - 1 - p' / (2 * len))) && Nat.beq t (twN z)

/-- The Cooley–Tukey butterfly of `p` and `p'` in layer `st`, with the zeta
`z` of their block and its `tw` `t`. -/
def bflyOk (R : Rules) (st p p' z t : Nat) : Bool :=
  let len := 128 >>> st
  Nat.blt st R.layers && Nat.beq p' (p + len) && Nat.blt (p % (2 * len)) len && Nat.blt p' 256 &&
    Nat.beq z (R.zeta (128 / len + p / (2 * len))) && Nat.beq t (twN z)

/-- The product of halfwords. -/
def mulT (a b : T) : T :=
  bif Nat.beq a.kind 1 && Nat.beq b.kind 3 && Nat.blt b.t 4096 then mk .mulC a.st a.p b.t 0
  else bif Nat.beq a.kind 5 && Nat.beq b.kind 3 && Nat.beq b.t qN then mk .mulQ a.st a.p 0 a.t
  else bif Nat.beq a.kind 11 && Nat.beq b.kind 3 then mk .mulD a.st a.p a.z b.t
  else bif Nat.beq a.kind 13 && Nat.beq b.kind 3 && Nat.beq b.t qN then mk .mulQD a.st a.p a.z a.t
  else junkT

/-- `SQRDMULH`. -/
def qdT (a b : T) : T :=
  bif Nat.beq a.kind 1 && Nat.beq b.kind 3 then mk .qdC a.st a.p 0 b.t
  else bif Nat.beq a.kind 11 && Nat.beq b.kind 3 then mk .qdD a.st a.p a.z b.t
  else junkT

/-- `a + b`: a butterfly's sum, or the end of a reduction. -/
def addT (R : Rules) (a b : T) : T :=
  bif !R.inv && Nat.beq a.kind 1 && Nat.beq b.kind 7 && Nat.beq b.st a.st && bflyOk R a.st a.p b.p b.z b.t then
    lvT (a.st + 1) a.p
  else bif !R.inv && Nat.beq a.kind 8 && Nat.beq b.kind 10 && Nat.beq b.z 0 && Nat.beq b.st a.st &&
      Nat.beq b.p a.p && Nat.beq a.st R.layers && Nat.blt a.p 256 then outT a.p
  else bif R.inv && Nat.beq a.kind 1 && Nat.beq b.kind 1 && Nat.beq b.st a.st && gsPair a.st a.p b.p then
    lvT (a.st + 1) a.p
  else bif R.inv && Nat.beq a.kind 1 && Nat.beq b.kind 10 && Nat.beq b.z 1 && Nat.beq b.st a.st &&
      Nat.beq b.p a.p && Nat.beq a.st R.layers && Nat.blt a.p 256 then outT a.p
  else junkT

/-- `a - b`: a butterfly's difference, a product modulo `q`, or a reduction. -/
def subT (R : Rules) (a b : T) : T :=
  bif !R.inv && Nat.beq a.kind 1 && Nat.beq b.kind 7 && Nat.beq b.st a.st && bflyOk R a.st a.p b.p b.z b.t then
    lvT (a.st + 1) b.p
  else bif Nat.beq a.kind 4 && Nat.beq b.kind 6 && Nat.beq b.st a.st && Nat.beq b.p a.p then
    bif R.inv && Nat.beq a.st invScale && Nat.beq a.z 3303 && Nat.beq b.t (twN 3303) then lvT (a.st + 1) a.p
    else mk .mm a.st a.p a.z b.t
  else bif Nat.beq a.kind 1 && Nat.beq b.kind 6 && Nat.beq b.st a.st && Nat.beq b.p a.p && Nat.beq b.t 10 then
    bif R.inv && invRed a.st then lvT (a.st + 1) a.p else mk .n1 a.st a.p 0 0
  else bif R.inv && Nat.beq a.kind 1 && Nat.beq b.kind 1 && Nat.beq b.st a.st && gsPair a.st b.p a.p then
    mk .dif a.st a.p b.p 0
  else bif R.inv && Nat.beq a.kind 12 && Nat.beq b.kind 14 && Nat.beq b.st a.st && Nat.beq b.p a.p &&
      Nat.beq b.z a.z && gsPair a.st a.z a.p && gsZeta a.st a.p a.t b.t then
    lvT (a.st + 1) a.p
  else junkT

/-- The arithmetic shift right by 15: of a reduction (`z = 0`), or of a
coefficient (`z = 1`). -/
def sraT (a : T) : T :=
  bif Nat.beq a.kind 8 then mk .sraN a.st a.p 0 0
  else bif Nat.beq a.kind 1 then mk .sraN a.st a.p 1 0
  else junkT

def andT (a b : T) : T :=
  bif Nat.beq a.kind 9 && Nat.beq b.kind 3 && Nat.beq b.t qN then mk .andN a.st a.p a.z 0 else junkT

/-- `SQRDMULH` by `b` is defined: `b` is a constant other than `-2¹⁵`. -/
def qdOk (b : T) : Bool := Nat.beq b.kind 3 && !Nat.beq b.t 32768

/-! ## Vectors of terms -/

/-- The width of a term. -/
abbrev tw : Nat := 48

/-- The width of eight terms. -/
def yw : Nat := 384

/-- Eight halfwords, packed. -/
abbrev Y := Nat

def Y.get (y : Y) (e : Nat) : T := slot tw y e

/-- Eight halfwords from a function of their index. -/
def Y.ofFn (f : Nat → T) : Y :=
  let m := 281474976710656
  Nat.add (Nat.mod (f 0) m) (Nat.mul m (Nat.add (Nat.mod (f 1) m) (Nat.mul m (Nat.add (Nat.mod (f 2) m)
    (Nat.mul m (Nat.add (Nat.mod (f 3) m) (Nat.mul m (Nat.add (Nat.mod (f 4) m) (Nat.mul m
    (Nat.add (Nat.mod (f 5) m) (Nat.mul m (Nat.add (Nat.mod (f 6) m) (Nat.mul m (Nat.mod (f 7) m))))))))))))))

/-- Eight copies of `a`. -/
def Y.dup (a : T) : Y := Y.ofFn fun _ => a

/-- The source of halfword `e` of a permutation of `x` and `y`: whether it
is `y`'s, and its index there. -/
def permSrc (op : VPermOp) (a : VArr) (e : Nat) : Option (Bool × Nat) :=
  match a, op with
  | .h8, .zip1 => some (e % 2 != 0, e / 2)
  | .h8, .zip2 => some (e % 2 != 0, 4 + e / 2)
  | .h8, .trn1 => if e % 2 = 0 then some (false, e) else some (true, e - 1)
  | .h8, .trn2 => if e % 2 = 0 then some (false, e + 1) else some (true, e)
  | .h8, .uzp1 => if e < 4 then some (false, 2 * e) else some (true, 2 * e - 8)
  | .h8, .uzp2 => if e < 4 then some (false, 2 * e + 1) else some (true, 2 * e - 7)
  | .s4, .zip1 => some (e / 2 % 2 != 0, e / 4 * 2 + e % 2)
  | .s4, .zip2 => some (e / 2 % 2 != 0, 4 + e / 4 * 2 + e % 2)
  | .s4, .trn1 => if e / 2 % 2 = 0 then some (false, e) else some (true, e - 2)
  | .s4, .trn2 => if e / 2 % 2 = 0 then some (false, e + 2) else some (true, e)
  | .s4, .uzp1 => if e < 4 then some (false, 2 * (e / 2) * 2 + e % 2) else some (true, 2 * (e / 2) * 2 + e % 2 - 8)
  | .s4, .uzp2 => if e < 4 then some (false, 2 * (e / 2) * 2 + 2 + e % 2) else some (true, 2 * (e / 2) * 2 + e % 2 - 6)
  | .d2, .trn1 => if e < 4 then some (false, e) else some (true, e - 4)
  | .d2, .trn2 => if e < 4 then some (false, e + 4) else some (true, e)
  | _, _ => none

/-! ## General registers -/

/-- A general register: a pointer `o` bytes into region `k`, a number, or
not followed. -/
inductive G
  | ptr (k o : Nat)
  | num (n : Nat)
  | junk
  deriving DecidableEq, Inhabited

/-- The width of a general register: `0` (not followed), `1 + 2 · n` (the
number `n`) or `2 + 2 · (k + 16 · o)` (a pointer). -/
abbrev gw : Nat := 80

def G.code : G → Nat
  | .junk => 0
  | .num n => 1 + 2 * (n % 2 ^ 64)
  | .ptr k o => 2 + 2 * (k % 16 + 16 * (o % 2 ^ 32))

def G.ofCode (n : Nat) : G :=
  if n = 0 then .junk else if n % 2 = 1 then .num (n / 2) else .ptr ((n - 2) / 2 % 16) ((n - 2) / 2 / 16)

/-- Where a region starts: a register's value on entry, or a static's address. -/
inductive Base
  | reg (r : Reg)
  | sym (name : String)
  deriving DecidableEq, Inhabited

/-- A region of memory the code reads or writes: where it starts and its
offset from there (bytes), its number of 16-byte chunks, and whether the
code may write it. -/
structure Rg where
  base : Base
  off : Nat
  chunks : Nat
  wr : Bool
  deriving DecidableEq, Inhabited

/-- The region holding the byte `a` bytes from `b`, and its offset there. -/
def locate (rs : List Rg) (b : Base) (a : Nat) : Option (Nat × Nat) :=
  (rs.findIdx? fun r => r.base == b && r.off ≤ a && a < r.off + 16 * r.chunks).map fun k =>
    (k, a - (rs.getD k default).off)

/-- A pointer, into the region holding its byte if there is one. -/
def norm (rs : List Rg) (k o : Nat) : G :=
  match locate rs (rs.getD k default).base ((rs.getD k default).off + o) with
  | some (k', o') => .ptr k' o'
  | none => .ptr k o

def addG (rs : List Rg) (g : G) (imm : Nat) : G :=
  match g with
  | .ptr k o => if o + imm < 2 ^ 32 then norm rs k (o + imm) else .junk
  | .num n => .num ((n + imm) % 2 ^ 64)
  | .junk => .junk

def subG (rs : List Rg) (g : G) (imm : Nat) : G :=
  match g with
  | .ptr k o => if imm ≤ o then norm rs k (o - imm) else .junk
  | .num n => .num ((n + (2 ^ 64 - imm)) % 2 ^ 64)
  | .junk => .junk

/-! ## The machine -/

/-- The number of a vector register. -/
def vi : VReg → Nat
  | .v0 => 0 | .v1 => 1 | .v2 => 2 | .v3 => 3 | .v4 => 4 | .v5 => 5 | .v6 => 6 | .v7 => 7
  | .v8 => 8 | .v9 => 9 | .v10 => 10 | .v11 => 11 | .v12 => 12 | .v13 => 13 | .v14 => 14
  | .v15 => 15 | .v16 => 16 | .v17 => 17 | .v18 => 18 | .v19 => 19 | .v20 => 20 | .v21 => 21
  | .v22 => 22 | .v23 => 23 | .v24 => 24 | .v25 => 25 | .v26 => 26 | .v27 => 27 | .v28 => 28
  | .v29 => 29 | .v30 => 30 | .v31 => 31

/-- The number of a general register (`x30` is 18). -/
def gi : Reg → Nat
  | .x0 => 0 | .x1 => 1 | .x2 => 2 | .x3 => 3 | .x4 => 4 | .x5 => 5 | .x6 => 6 | .x7 => 7
  | .x8 => 8 | .x9 => 9 | .x10 => 10 | .x11 => 11 | .x12 => 12 | .x13 => 13 | .x14 => 14
  | .x15 => 15 | .x16 => 16 | .x17 => 17 | .x19 => 19 | .x20 => 20 | .x21 => 21
  | .x22 => 22 | .x23 => 23 | .x24 => 24 | .x25 => 25 | .x26 => 26 | .x27 => 27 | .x28 => 28
  | .x30 => 18

structure St where
  /-- The vector registers, by number. -/
  v : Nat
  /-- The general registers, by number. -/
  g : Nat
  /-- Each region, chunk by chunk. -/
  mem : List Nat
  deriving DecidableEq, Inhabited

def St.vreg (σ : St) (r : VReg) : Y := slot yw σ.v (vi r)

def St.greg (σ : St) (r : Reg) : G := G.ofCode (slot gw σ.g (gi r))

def St.setV (σ : St) (d : VReg) (y : Y) : St := { σ with v := upd yw σ.v (vi d) y }

def St.setG (σ : St) (d : Reg) (g : G) : St := { σ with g := upd gw σ.g (gi d) g.code }

def St.chunk (σ : St) (k j : Nat) : Y := slot yw (σ.mem.getD k 0) j

def St.setChunk (σ : St) (k j : Nat) (y : Y) : St :=
  { σ with mem := σ.mem.set k (upd yw (σ.mem.getD k 0) j y) }

/-- The region and chunk of a 16-byte-aligned access `off` bytes from `g`. -/
def chunkAt (rs : List Rg) (g : G) (off : Nat) : Option (Nat × Nat) :=
  match g with
  | .ptr k o =>
    match locate rs (rs.getD k default).base ((rs.getD k default).off + o + off) with
    | some (k', o') => if o' % 16 = 0 then some (k', o' / 16) else none
    | none => none
  | _ => none

/-- The region of the static `name`, at its start. -/
def symRegion (rs : List Rg) (name : String) : G :=
  match rs.findIdx? (fun r => r.base == .sym name && r.off == 0) with
  | some k => .ptr k 0
  | none => .junk

def St.vop (R : Rules) (σ : St) : VOp → Option St
  | .movi0 d => some (σ.setV d (Y.dup (cT 0)))
  | .dup .h8 d n =>
    match σ.greg n with
    | .num v => some (σ.setV d (Y.dup (cT (v % 65536))))
    | _ => none
  | .ins .h8 d i n =>
    match σ.greg n with
    | .num v => if i < 8 then some (σ.setV d (upd tw (σ.vreg d) i (cT (v % 65536)))) else none
    | _ => none
  | .dupE .h8 d n i => if i < 8 then some (σ.setV d (Y.dup ((σ.vreg n).get i))) else none
  | .mulH .mul d n m =>
    let x := σ.vreg n
    let y := σ.vreg m
    some (σ.setV d (Y.ofFn fun e => mulT (x.get e) (y.get e)))
  | .mulH .sqrdmulh d n m =>
    let x := σ.vreg n
    let y := σ.vreg m
    if (List.range 8).all fun e => qdOk (y.get e) then
      some (σ.setV d (Y.ofFn fun e => qdT (x.get e) (y.get e)))
    else none
  | .mulH .mls d n m =>
    let a := σ.vreg d
    let x := σ.vreg n
    let y := σ.vreg m
    some (σ.setV d (Y.ofFn fun e => subT R (a.get e) (mulT (x.get e) (y.get e))))
  | .mulHE .mul d n m i =>
    let x := σ.vreg n
    let z := (σ.vreg m).get i
    if i < 8 ∧ m.index < 16 then some (σ.setV d (Y.ofFn fun e => mulT (x.get e) z)) else none
  | .mulHE .sqrdmulh d n m i =>
    let x := σ.vreg n
    let z := (σ.vreg m).get i
    if i < 8 ∧ m.index < 16 ∧ qdOk z then some (σ.setV d (Y.ofFn fun e => qdT (x.get e) z)) else none
  | .mulHE .mls d n m i =>
    let a := σ.vreg d
    let x := σ.vreg n
    let z := (σ.vreg m).get i
    if i < 8 ∧ m.index < 16 then some (σ.setV d (Y.ofFn fun e => subT R (a.get e) (mulT (x.get e) z)))
    else none
  | .ins .d2 d i _ => if i < 2 then some (σ.setV d 0) else none
  | .add .h8 d n m =>
    let x := σ.vreg n
    let y := σ.vreg m
    some (σ.setV d (Y.ofFn fun e => addT R (x.get e) (y.get e)))
  | .sub .h8 d n m =>
    let x := σ.vreg n
    let y := σ.vreg m
    some (σ.setV d (Y.ofFn fun e => subT R (x.get e) (y.get e)))
  | .shift .sshr .h8 d n sh =>
    let x := σ.vreg n
    if sh = 15 then some (σ.setV d (Y.ofFn fun e => sraT (x.get e))) else none
  | .logic .and d n m =>
    let x := σ.vreg n
    let y := σ.vreg m
    some (σ.setV d (Y.ofFn fun e => andT (x.get e) (y.get e)))
  | .perm op a d n m =>
    let x := σ.vreg n
    let y := σ.vreg m
    if (List.range 8).all fun e => (permSrc op a e).isSome then
      some (σ.setV d (Y.ofFn fun e =>
        match permSrc op a e with
        | some (b, i) => (if b then y else x).get i
        | none => junkT))
    else none
  | _ => none

/-- One instruction, with the regions `rs`. -/
def St.step (R : Rules) (rs : List Rg) (σ : St) : Instr → Option St
  | .vop o => σ.vop R o
  | .addImm .x d n imm => if imm < 4096 then some (σ.setG d (addG rs (σ.greg n) imm)) else none
  | .subImm .x d n imm => if imm < 4096 then some (σ.setG d (subG rs (σ.greg n) imm)) else none
  | .movz .x d imm hw => if hw < 4 then some (σ.setG d (.num (imm.toNat * 2 ^ (16 * hw)))) else none
  | .adrSym d name => some (σ.setG d (symRegion rs name))
  | .umov .x d _ i => if i < 2 then some (σ.setG d .junk) else none
  | .ldrq t n off =>
    if off % 16 = 0 ∧ off < 65536 then (chunkAt rs (σ.greg n) off).map fun (k, j) => σ.setV t (σ.chunk k j)
    else none
  | .strq t n off =>
    if off % 16 = 0 ∧ off < 65536 then
      (chunkAt rs (σ.greg n) off).bind fun (k, j) =>
        if (rs.getD k default).wr then some (σ.setChunk k j (σ.vreg t)) else none
    else none
  | _ => none

def St.run (R : Rules) (rs : List Rg) (σ : St) : List Instr → Option St
  | [] => some σ
  | i :: is => (σ.step R rs i).bind fun σ' => σ'.run R rs is

/-- Iterations of a loop (`f` its body) until `r` is zero, at most `fuel`. -/
def loopRun (f : St → Option St) (r : Reg) : Nat → St → Option St
  | 0, _ => none
  | fuel + 1, σ => (f σ).bind fun σ' =>
    match σ'.greg r with
    | .num 0 => some σ'
    | .num _ => loopRun f r fuel σ'
    | _ => none

/-- Code of blocks, sequences and loops that test a 64-bit register, each
loop for at most `fuel` iterations. -/
def St.runP (R : Rules) (rs : List Rg) (fuel : Nat) : Prog isa → St → Option St
  | .block is, σ => σ.run R rs is
  | .seq a b, σ => (St.runP R rs fuel a σ).bind (St.runP R rs fuel b)
  | .loop b (.nonzero .x r), σ => loopRun (St.runP R rs fuel b) r fuel σ
  | _, _ => none

end VG.Proof.MlKem.AArch64.NttR
