import VerifiedGarbage.Impl.Weierstrass.X86.TComb
import VerifiedGarbage.Impl.Weierstrass.X86
import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Spec.Ecdsa

/-!
# ECDSA signing on x86 (32-bit)

`vg_ecdsa_<curve>_sign(out, d, digest, k, scratch) -> eax` (cdecl: the
arguments at `[esp + 4]` to `[esp + 20]`), for a curve whose field elements
and scalars are `n` 64-bit words (`2n` 32-bit words; `n = 4` for the 256-bit
curves), from the code of `Impl/Weierstrass/X86.lean`, as on x86-64
(`Impl/Ecdsa/X86_64.lean`):

1. the callee-saved registers are saved in the working space, whose base is
   then `edi`; `k`, `d` and the hash are read big-endian into slots, and the
   constants (the moduli, `a`, `3b`, `G` and Montgomery's ones in
   Montgomery form, `R² mod n`, and the exponents `p - 2` and `n - 2`) are
   stored as immediates;
2. the bits of `k`, `p - 2` and `n - 2` are expanded into tables;
3. `R = [k]G` by the ladder from `R = O = (0 : 1 : 0)`, then
   `x = X Z^(p-2)` (Montgomery's form left by a multiplication by 1) and
   `r = x mod n` (a conditional subtraction, as `x < p < 2n`);
4. `s = k^(n-2) (e + r d) mod n`, in Montgomery form modulo `n`, then left;
5. the flag: `d` and `k` in `[1, n-1]`, `r ≠ 0` and `s ≠ 0`, as a mask, which
   selects `r ‖ s` or zeros for `out` (big-endian), and is returned as 0 or 1.

The multiplications accumulate at `wk`, after the tables. `R = O`
(impossible for `k` in `[1, n-1]`) gives `Z = 0`, so `x = 0` and `r = 0`, as
the specification says. Everything is computed whatever the flag, and only
the pointers may affect timing.
-/

namespace VG.Impl.Ecdsa.X86

open VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass

/-- `-m⁻¹ mod 2⁶⁴`, for odd `m`, by Newton's iteration. -/
def minv (m : Nat) : Nat :=
  let inv := (List.range 6).foldl (fun x _ => x * ((2 + 2 ^ 64 - m * x % 2 ^ 64) % 2 ^ 64) % 2 ^ 64) 1
  (2 ^ 64 - inv) % 2 ^ 64

/-- The working space: the saved registers in bytes `[0, 16)`, then
slots of `n` words (`slot n i`) from byte 64, then the tables of bits
(`bitsAt`), then the multiplications' accumulator (`wkAt`). -/
def slot (n i : Nat) : Nat := 64 + 8 * n * i

/-! Slot numbers. -/
def MP := 0
def MN := 1
def TMP := 2
def ZERO := 3
def ONE := 4
def ONEP := 5
def AP := 6
def B3P := 7
def GX := 8
def GY := 9
def R2N := 10
def ONEN := 11
def EXPP := 12
def EXPN := 13
def RX := 14
def RY := 15
def RZ := 16
def DX := 17
def DY := 18
def DZ := 19
def TX := 20
def TY := 21
def TZ := 22
def T0 := 23
def T1 := 24
def T2 := 25
def T3 := 26
def T4 := 27
def T5 := 28
def ACC := 29
def PT := 30
def K := 31
def D := 32
def E := 33
def XM := 34
def X := 35
def RR := 36
def KM := 37
def RM := 38
def DM := 39
def EM := 40
def TT := 41
def SM := 42
def SS := 43
def FLAG := 44
/-- The number of slots. -/
def nslots := 45

/-- The table of the bits of `k` (`j = 0`), `p - 2` (1) and `n - 2` (2). -/
def bitsAt (n j : Nat) : Nat := slot n nslots + (64 * n + 4) * j

/-- The multiplications' accumulator: after the tables. -/
def wkAt (n : Nat) : Nat := bitsAt n 3

/-- The arguments the setup reads: the working space, `k`, `d` and the hash
(the functions built on the signature's code read some of them from the same
argument), and the slot, if any, holding a hash to shift. -/
structure Args where
  sc : Nat
  k : Nat
  d : Nat
  e : Nat
  hs : Option Nat

/-- The signature's: `(out, d, digest, k, scratch)`, shifting the hash in
`E`. -/
abbrev Args.sign : Args := ⟨4, 3, 1, 2, some E⟩

/-- A fixed-base comb's digit width, affine tables, offset point and symbol. -/
structure CombData where
  w : Nat
  tbl : List (List (Nat × Nat))
  start : Nat × Nat
  tsym : String

/-- A curve as the code has it, and an optional fixed-base comb. -/
structure Cfg where
  n : Nat
  C : Spec.Weierstrass.Curve
  comb : Option CombData := none

namespace Cfg

variable (c : Cfg)

/-- `R = 2^(64 n)`. -/
def R : Nat := 2 ^ (64 * c.n)

/-- The bits of the hash's `len` bytes that are not `e`'s: `8 len - N`, for
`N` the bits of `n` (0 but for P-521's 7). -/
def sh : Nat := 8 * c.C.len - Spec.Ecdsa.nBits c.C

/-- `x R mod p`. -/
def mont (x : Nat) : Nat := x * c.R % c.C.p

def sl (i : Nat) : Nat := slot c.n i

def wk : Nat := wkAt c.n

def MP' : Mod where
  n := c.n
  mo := c.sl MP
  tmp := c.sl TMP
  minv := BitVec.ofNat 64 (minv c.C.p)
  red := Mont.X86.p256RedChoice c.n c.C.p
def MN' : Mod := { n := c.n, mo := c.sl MN, tmp := c.sl TMP, minv := BitVec.ofNat 64 (minv c.C.n) }

def pt (x y z : Nat) : Pt := ⟨c.sl x, c.sl y, c.sl z⟩

def rcbSlots : RcbSlots := ⟨c.sl AP, c.sl B3P, c.sl T0, c.sl T1, c.sl T2, c.sl T3, c.sl T4, c.sl T5⟩

def ladderCfg : LadderCfg where
  M := c.MP'
  S := c.rcbSlots
  G := c.pt GX GY ONEP
  R := c.pt RX RY RZ
  D := c.pt DX DY DZ
  T := c.pt TX TY TZ
  bits := bitsAt c.n 0
  nbits := 64 * c.n

/-- The number of signed windows covering the scalar. -/
def combJ (w : Nat) : Nat := (64 * c.n + w - 1) / w

/-- The comb's pointer is in the unused tail of the saved-register header. -/
def combPtr : Nat := 60

def combCfg (d : CombData) : TCombCfg where
  M := c.MP'
  S := { c.rcbSlots with b3 := c.sl EM }
  A := c.pt RX RY RZ
  E := c.pt TX TY TZ
  D := c.pt DX DY DZ
  neg := c.sl PT
  zero := c.sl ZERO
  bits := bitsAt c.n 0
  kbytes := 64 * c.n
  tsym := d.tsym
  w := d.w
  J := c.combJ d.w
  start := (c.mont d.start.1, c.mont d.start.2)
  one := c.mont 1
  wk := c.wk
  ptr := combPtr

def combWords (d : CombData) : List (BitVec 64) := tcombWords c.n c.R c.C.p d.tbl

def combConsts : List (String × List (BitVec 64)) :=
  match c.comb with
  | none => []
  | some d => [(d.tsym, c.combWords d)]

/-- Obtain the table address before setup; restore ESP before reading cdecl
arguments. The saved EIP is popped into the caller-saved ECX. -/
def tableAddr : Prog isa :=
  match c.comb with
  | none => .block []
  | some d => .frame (.symPush .eax d.tsym) (.block []) (.pop .ecx 1)

/-- The fixed-base multiplication, after setup saved the table pointer. -/
def gMul : Prog isa :=
  match c.comb with
  | none => ladder c.ladderCfg c.wk
  | some d => .seq (.block (setConst c.n (c.sl EM) (c.mont c.C.b)))
      (.seq (.block (c.combCfg d).initCore) (.loop (c.combCfg d).step .ne))

def powP : PowCfg := ⟨c.MP', c.sl ACC, c.sl PT, c.sl RZ, c.sl ONEP, bitsAt c.n 1, 64 * c.n⟩
def powN : PowCfg := ⟨c.MN', c.sl ACC, c.sl PT, c.sl KM, c.sl ONEN, bitsAt c.n 2, 64 * c.n⟩

/-- The callee-saved registers, and where they are saved. -/
def saved : List (Reg × Nat) := [(.ebx, 0), (.esi, 4), (.edi, 8), (.ebp, 12)]

/-- The constants, and `R = (0 : 1 : 0)`: slots and values. -/
def consts : List (Nat × Nat) :=
  [(MP, c.C.p), (MN, c.C.n), (ZERO, 0), (ONE, 1), (ONEP, c.mont 1), (AP, c.mont c.C.a),
    (B3P, c.mont (3 * c.C.b)), (GX, c.mont c.C.gx), (GY, c.mont c.C.gy), (R2N, c.R * c.R % c.C.n),
    (ONEN, c.R % c.C.n), (EXPP, c.C.p - 2), (EXPN, c.C.n - 2), (RX, 0), (RY, c.mont 1), (RZ, 0)]

/-- `[esp + 4 + 4 i]`: argument `i`. -/
def argOp (i : Nat) : MemOp := at_ .esp (4 + 4 * i)

/-- Saves them at `[eax]`. -/
def saveCode : List Instr := saved.map fun (r, d) => .store (at_ .eax d) r

/-- The slot `hs` (if any) shifted right by the bits of a hash's `len`
bytes that are not `e`'s (`sh`: none but for P-521's 7). -/
def shiftCode : Option Nat → List Instr
  | none => []
  | some i => if c.sh = 0 then [] else shrWords c.n (c.sl i) c.sh

/-- Save the public table address supplied in EAX before ordinary setup
uses EAX for the scratch pointer. -/
def prepTable (A : Args) : List Instr :=
  match c.comb with
  | none => []
  | some _ => [.mov .edx (.mem (argOp A.sc)), .store (at_ .edx combPtr) .eax]

/-- Saves them through `eax`, with the working space from its argument, which
then goes to `edi`; reads `k`, `d` and the hash (`len` bytes each) through
`ebx` from the arguments `A` names, and shifts the slot `A.hs` holding a hash;
stores the constants; and sets `R = (0 : 1 : 0)` and the flag (a word) to
all ones. -/
def setupWith (A : Args) : List Instr :=
  c.prepTable A ++ [.mov .eax (.mem (argOp A.sc))] ++ saveCode ++
  [.mov .edi (.reg .eax), .mov .ebx (.mem (argOp A.k))] ++ loadBytes c.C.len c.n (c.sl K) .ebx ++
  [.mov .ebx (.mem (argOp A.d))] ++ loadBytes c.C.len c.n (c.sl D) .ebx ++
  [.mov .ebx (.mem (argOp A.e))] ++ loadBytes c.C.len c.n (c.sl E) .ebx ++
  c.shiftCode A.hs ++
  c.consts.flatMap (fun (i, x) => setConst c.n (c.sl i) x) ++
  [.mov .eax (.imm (BitVec.allOnes 32)), .store (sc (c.sl FLAG)) .eax]

/-- The setup of `sign`. -/
def setup : List Instr := c.setupWith .sign

/-- The mask `edx` of `[a] ≠ 0` (all ones if it is not zero), through `ecx`. -/
def nonzero (a : Nat) : List Instr :=
  [.mov .edx (.mem (sc a))] ++
  ((List.range (2 * c.n - 1)).map fun j => .alu .or .edx (.mem (sc (a + 4 * (j + 1))))) ++
  [.mov .ecx (.imm 0), .alu .sub .ecx (.reg .edx), .alu .sbb .edx (.reg .edx)]

/-- The mask `eax` of `[a] < n` (all ones if it is), through `edx`. -/
def ltN (a : Nat) : List Instr :=
  ((List.range (2 * c.n)).flatMap fun j =>
    [.mov .edx (.mem (sc (a + 4 * j))), .alu (if j = 0 then .sub else .sbb) .edx (.mem (sc (c.sl MN + 4 * j)))]) ++
  [.alu .sbb .eax (.reg .eax)]

/-- The flag `&=` the mask `edx`, through `eax`. -/
def andFlag : List Instr :=
  [.mov .eax (.mem (sc (c.sl FLAG))), .alu .and .eax (.reg .edx), .store (sc (c.sl FLAG)) .eax]

/-- `[a]` is in `[1, n-1]`: the flag `&=` both masks (the first kept in `ebx`). -/
def checkRange (a : Nat) : List Instr :=
  c.ltN a ++ [.mov .ebx (.reg .eax)] ++ c.nonzero a ++ [.alu .and .edx (.reg .ebx)] ++ c.andFlag

/-- `[a] ≠ 0`: the flag `&=` its mask. -/
def checkNonzero (a : Nat) : List Instr := c.nonzero a ++ c.andFlag

/-- `x = X Z⁻¹`, `r = x mod n`, `k R mod n`, and the checks of `d`, `k`, `r`. -/
def middle : Prog isa :=
  progs [Mont.X86.mul c.MP' c.wk (c.sl XM) (c.sl RX) (c.sl ACC),
    Mont.X86.mul c.MP' c.wk (c.sl X) (c.sl XM) (c.sl ONE),
    .block (Mont.X86.add c.MN' c.wk (c.sl RR) (c.sl X) (c.sl ZERO)),
    Mont.X86.mul c.MN' c.wk (c.sl KM) (c.sl K) (c.sl R2N),
    .block (c.checkRange (c.sl D) ++ c.checkRange (c.sl K) ++ c.checkNonzero (c.sl RR))]

/-- The callee-saved registers restored, through `edx`, `edi` last. -/
def restore : List Instr :=
  [.mov .edx (.reg .edi), .mov .ebx (.mem (at_ .edx 0)), .mov .esi (.mem (at_ .edx 4)),
    .mov .ebp (.mem (at_ .edx 12)), .mov .edi (.mem (at_ .edx 8))]

/-- `r ‖ s` (or zeros) to `out` (through `ebx`), the flag's low bit to `eax`,
and the callee-saved registers restored. -/
def finish : List Instr :=
  [.mov .ecx (.mem (sc (c.sl FLAG))), .mov .ebx (.mem (argOp 0))] ++
  storeBytes c.C.len c.n .ebx 0 (c.sl RR) ++ storeBytes c.C.len c.n .ebx c.C.len (c.sl SS) ++
  [.mov .eax (.reg .ecx), .alu .and .eax (.imm 1)] ++ restore

/-- `s = k⁻¹ (e + r d) mod n`, with `k⁻¹ R` in `ACC`, and its check. -/
def scalar : Prog isa :=
  progs [Mont.X86.mul c.MN' c.wk (c.sl RM) (c.sl RR) (c.sl R2N),
    Mont.X86.mul c.MN' c.wk (c.sl DM) (c.sl D) (c.sl R2N),
    Mont.X86.mul c.MN' c.wk (c.sl EM) (c.sl E) (c.sl R2N),
    Mont.X86.mul c.MN' c.wk (c.sl TT) (c.sl RM) (c.sl DM),
    .block (Mont.X86.add c.MN' c.wk (c.sl TT) (c.sl TT) (c.sl EM)),
    Mont.X86.mul c.MN' c.wk (c.sl SM) (c.sl ACC) (c.sl TT),
    Mont.X86.mul c.MN' c.wk (c.sl SS) (c.sl SM) (c.sl ONE),
    .block (c.checkNonzero (c.sl SS) ++ c.finish)]

/-- `vg_ecdsa_<curve>_sign`. -/
def prepareWith (A : Args) : Prog isa :=
  .seq (.block (c.setupWith A)) <|
  .seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) <|
  .seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) <|
  .seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) (.block [])

def signPrep : Prog isa := c.prepareWith .sign

def signTail : Prog isa :=
  .seq (pow c.powP c.wk) <|
  .seq c.middle <|
  .seq (pow c.powN c.wk) c.scalar

def signWithMul (fixed : Prog isa) : Prog isa :=
  .seq c.signPrep (.seq fixed c.signTail)

/-- The existing ladder path. -/
def sign : Prog isa :=
  .seq (.block c.setup) <|
  .seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) <|
  .seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) <|
  .seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) <|
  .seq (ladder c.ladderCfg c.wk) c.signTail

/-- The table address is obtained before reading the cdecl arguments. -/
def signComb : Prog isa := .seq c.tableAddr (c.signWithMul c.gMul)

end Cfg

end VG.Impl.Ecdsa.X86
