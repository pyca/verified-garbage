module

public import VerifiedGarbage.Impl.Bignum.X86.CrtRt
public import VerifiedGarbage.Impl.Bignum.X86.ModulusCheck

/-!
# FFDH on i686: domain and key validation and exchange

Every function runs at the width `B = 8 ⌈p_len / 8⌉` bytes, read at run
time, on the operations of private CRT RSA at a run-time width (`CrtRt`,
in its wide context only): imports of big-endian bytes, comparisons by a
mask, Montgomery preparation (the modulus replaced by three unless it is
an odd number above one, its inverse and `R² mod M`), multiplication by
calls of `vg_rsa_mont_mul_at`, and fixed four-bit-window exponentiation
over all `B` bytes of the exponent, scanning the whole table for each
window.

Those operations read the modulus's length, the numbers' pointers and
lengths, and the working space from private CRT's eighteen arguments on the
stack. Each function saves the callee-saved registers in the working
space's header (`CrtRt.save`), then allocates a frame of 76 bytes holding
eighteen such arguments (`fill`), computed from its own: the length `p_len`
(1), p, g and q (2 to 7, each `p_len` bytes of the domain), y (8, 9), x
(10, 11), the domain's length (12), the output (0) and the working space
and its length (16, 17), the rest zero. All of them are public.

The wide slots used: p (9), g (10), q (11), y (12), x (13), one (14),
`p − 1` (15), the scalar's bound (16), zero (17) and the result (19). Only
public values (the domain, a public value, the statuses the contracts
release) choose branches.
-/

@[expose] public section
namespace VG.Impl.Ffdh.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- The positions of a function's arguments: the output (if any), the
domain, its length, `p_len`, y and x (each followed by its length, if
any), and the working space (followed by its length). -/
structure Args where
  out : Option Nat := none
  dom : Nat
  dlen : Nat
  plen : Nat
  y : Option Nat := none
  x : Option Nat := none
  ws : Nat

/-- The bytes of the frame of the synthetic arguments. -/
def argsFrame : Nat := 76

/-- Synthetic argument `i`. -/
def slotOp (i : Nat) : MemOp := at_ .esp (4 + 4 * i)

/-- `eax` the function's argument `j`. -/
def argVal (j : Nat) : List Instr := [.mov .eax (.mem (argAt 19 j))]

/-- `eax` zero. -/
def zeroVal : List Instr := [.mov .eax (.imm 0)]

/-- `eax` the function's argument `j`, or zero. -/
def optVal : Option Nat → List Instr
  | some j => argVal j
  | none => zeroVal

/-- `eax` the domain's `k`-th component, at `domain + k p_len`. -/
def compVal (a : Args) (k : Nat) : List Instr :=
  [.mov .eax (.mem (argAt 19 a.dom)), .mov .ecx (.mem (argAt 19 a.plen))] ++
    List.replicate k (.alu .add .eax (.reg .ecx))

/-- `eax` synthetic argument `i`. -/
def val (a : Args) : Nat → List Instr
  | 0 => optVal a.out
  | 1 => argVal a.plen
  | 2 => compVal a 0
  | 3 => argVal a.plen
  | 4 => compVal a 1
  | 5 => argVal a.plen
  | 6 => compVal a 2
  | 7 => argVal a.plen
  | 8 => optVal a.y
  | 9 => optVal (a.y.map fun _ => a.plen)
  | 10 => optVal a.x
  | 11 => optVal (a.x.map (· + 1))
  | 12 => argVal a.dlen
  | 16 => argVal a.ws
  | 17 => argVal (a.ws + 1)
  | _ => zeroVal

/-- Synthetic argument `i` stored. -/
def piece (a : Args) (i : Nat) : List Instr := val a i ++ [.store (slotOp i) .eax]

/-- The eighteen synthetic arguments. -/
def fill (a : Args) : List Instr := (List.range 18).flatMap (piece a)

/-- `edi` the working space, with the callee-saved registers saved in its header. -/
def entry (a : Args) : List Instr :=
  [.mov .eax (.mem (PublicFn.argument a.ws))] ++ CrtRt.save ++ [.mov .edi (.reg .eax)]

/-- The registers saved and restored around `body`, which runs in the frame of the synthetic
arguments and leaves the status in `eax`. -/
def wrap (a : Args) (body : Prog isa) : Prog isa :=
  .seq (.block (entry a))
    (.seq (.frame (.alloc argsFrame) (.seq (.block (fill a)) body) (.free argsFrame)) (.block CrtRt.restore))

/-! ## The operations, on the wide slots -/

/-- Wide slot `j`. -/
local notation:max "sl " j:max => Loc.slot Ctx.wide j
/-- A number of the wide context. -/
local notation "n1" => one Ctx.wide

/-- p into slot 9, one into slot 14, `p − 1` into slot 15. -/
def pSetup : Prog isa :=
  .seq (load (sl 9) n1 2 3) (.seq (setSmall (sl 14) n1 1) (chain .sbb (sl 15) (sl 9) (sl 14) n1))

/-- The context of p: p in slot 0, one in slot 3, `R² mod p` in slot 4 and the inverse. -/
def ctxP : Prog isa := .seq (copy (sl 9) (sl 0) n1) (prepare .wide)

/-- Slot 6 the number in slot `b` to the power of the number in slot `e`, modulo p. -/
def powP (b e : Nat) : Prog isa :=
  .seq ctxP (.seq (copy (sl b) (sl 5) n1) (.seq (copy (sl e) (sl 8) n1) (windowPower .wide)))

/-- `ecx` all ones if `1 < [a] < p − 1`, else zero, through the mask word. -/
def rangeMask (a : Nat) : Prog isa :=
  .seq (lessThan (sl 14) (sl a) n1) (.seq (.block [.store (sc maskOff) .ecx])
    (.seq (lessThan (sl a) (sl 15) n1) (.block [.alu .and .ecx (.mem (sc maskOff))])))

/-- ZF set if the mask `ecx` is zero. -/
def testMask : Prog isa := .block [.alu .test .ecx (.reg .ecx)]

/-- The status `r`. -/
def ret (r : Nat) : Prog isa := .block [.mov .eax (.imm (BitVec.ofNat 32 r))]

/-- The status of the mask `ecx`: one if it is all ones, else zero. -/
def retMask : Prog isa := .block [.mov .eax (.reg .ecx), .alu .and .eax (.imm 1)]

/-- `domain_len − 2 p_len`: zero exactly when the domain has no q. -/
def qTest : List Instr :=
  [.mov .eax (.mem (argAt 0 12)), .alu .sub .eax (.mem (argAt 0 3)), .alu .sub .eax (.mem (argAt 0 3))]

/-- `ecx` all ones if `[a] = [b]`, and the status of it. -/
def eqStatus (a b : Nat) : Prog isa := .seq (equal (sl a) (sl b) n1) retMask

/-! ## `vg_ffdh_check_domain` -/

namespace CheckDomain

def args : Args := { dom := 0, dlen := 1, plen := 2, ws := 3 }

/-- `ecx` and-ed with all ones if slot 11's low bit is set, else zero. -/
def oddMask : List Instr :=
  ptrTo (sl 11) .eax .edx ++
    [.mov .eax (.mem (at_ .eax 0)), .alu .and .eax (.imm 1), .mov .edx (.imm 0), .alu .sub .edx (.reg .eax),
      .alu .and .ecx (.reg .edx)]

/-- `g^q mod p = 1`. -/
def subgroup : Prog isa := .seq (powP 10 11) (eqStatus 6 3)

/-- q divides `p − 1`: `(p − 1) R⁻¹ mod q` is zero, in the context of q. -/
def divides : Prog isa :=
  .seq (copy (sl 11) (sl 0) n1) <| .seq (prepare .wide) <| .seq (copy (sl 15) (sl 5) n1) <|
  .seq (mul .wide 6 5 3) <| .seq (zero (sl 17) n1) <| .seq (equal (sl 6) (sl 17) n1) <|
  .seq testMask (.ite .e (ret 0) subgroup)

/-- q odd, `2 < q < p − 1`, then `divides`. -/
def withQ : Prog isa :=
  .seq (load (sl 11) n1 6 7) <| .seq (setSmall (sl 16) n1 2) <|
  .seq (lessThan (sl 16) (sl 11) n1) <| .seq (.block [.store (sc maskOff) .ecx]) <|
  .seq (lessThan (sl 11) (sl 15) n1) <|
  .seq (.block ([.alu .and .ecx (.mem (sc maskOff))] ++ oddMask)) <|
  .seq testMask (.ite .e (ret 0) divides)

/-- `1 < g < p − 1`, then q if there is one. -/
def checked : Prog isa :=
  .seq pSetup <| .seq (load (sl 10) n1 4 5) <| .seq (rangeMask 10) <|
  .seq testMask (.ite .e (ret 0) (.seq (.block qTest) (.ite .e (ret 1) withQ)))

/-- RSA's check of a modulus's bytes (`modulusValid`), then `checked`. -/
def body : Prog isa :=
  .seq (.block PublicFn.modulusArgs) (.seq (.block modulusCheck) (.ite .e checked (ret 0)))

def code : Prog isa := wrap args body

end CheckDomain

/-! ## `vg_ffdh_check_public` -/

namespace CheckPublic

def args : Args := { dom := 0, dlen := 1, plen := 2, y := some 3, ws := 5 }

/-- `1 < y < p − 1`, then `y^q mod p = 1` if there is a q. -/
def body : Prog isa :=
  .seq pSetup <| .seq (load (sl 12) n1 8 9) <| .seq (rangeMask 12) <|
  .seq testMask <| .ite .e (ret 0) <| .seq (.block qTest) <| .ite .e (ret 1) <|
  .seq (load (sl 11) n1 6 7) (.seq (powP 12 11) (eqStatus 6 3))

def code : Prog isa := wrap args body

end CheckPublic

/-! ## `vg_ffdh_check_private` -/

namespace CheckPrivate

def args : Args := { dom := 0, dlen := 1, plen := 2, y := some 3, x := some 5, ws := 7 }

/-- The scalar's bound: q, or `p − 1` without q, into slot 16. -/
def bound : Prog isa :=
  .seq (.block qTest) (.ite .e (copy (sl 15) (sl 16) n1) (load (sl 16) n1 6 7))

/-- `ecx` all ones if `0 < x < bound`, else zero. -/
def scalarMask : Prog isa :=
  .seq (zero (sl 17) n1) <| .seq (lessThan (sl 17) (sl 13) n1) <| .seq (.block [.store (sc maskOff) .ecx]) <|
  .seq (lessThan (sl 13) (sl 16) n1) (.block [.alu .and .ecx (.mem (sc maskOff))])

/-- `1 < y < p − 1` and `g^x mod p = y`; a power of the checked generator is in its subgroup. -/
def pair : Prog isa :=
  .seq (rangeMask 12) <| .seq (.block [.store (sc accOff) .ecx]) <| .seq (powP 10 13) <|
  .seq (equal (sl 6) (sl 12) n1) (.seq (.block [.alu .and .ecx (.mem (sc accOff))]) retMask)

def body : Prog isa :=
  .seq pSetup <| .seq (load (sl 10) n1 4 5) <| .seq (load (sl 12) n1 8 9) <| .seq (load (sl 13) n1 10 11) <|
  .seq bound <| .seq scalarMask <| .seq testMask (.ite .e (ret 2) pair)

def code : Prog isa := wrap args body

end CheckPrivate

/-! ## `vg_ffdh_exchange` -/

namespace Exchange

def args : Args := { out := some 0, dom := 2, dlen := 3, plen := 4, y := some 7, x := some 5, ws := 9 }

/-- `z = y^x mod p` in slot 6, its range as the acceptance mask, and `z` or zeros to the output. -/
def body : Prog isa :=
  .seq pSetup <| .seq ctxP <| .seq (load (sl 5) n1 8 9) <| .seq (load (sl 8) n1 10 11) <|
  .seq (windowPower .wide) <| .seq (rangeMask 6) <| .seq (.block [.store (sc accOff) .ecx]) <|
  .seq (copy (sl 6) (sl 19) n1) exportResult

def code : Prog isa := wrap args body

end Exchange

end VG.Impl.Ffdh.X86
