module

public import VerifiedGarbage.Spec.Sha3
public import VerifiedGarbage.Impl.Sha3.Tables
public import VerifiedGarbage.Impl.Sha512.X86

/-!
# Keccak-f[1600]: x86 (32-bit) implementation

`vg_keccak_f1600(state, scratch)`, cdecl: the arguments are at `[esp + 4]`
and `[esp + 8]`.

With only seven usable general registers, the lanes live in memory: `esi`
points to `state` and `edi` to `scratch` throughout, and `ebp` to the
current round's constant. A lane being worked on is the low quadword of an
XMM register (SSE2: `movq` loads and stores it, `pxor`, `pandn`, `por`,
`psllq` and `psrlq` work on it; what they leave in the registers' high
quadwords is not used). `scratch` (512 bytes) is laid out as:

* `[0, 200)`: a second state, which the rounds alternate with `state`: each
  round reads one (`src`) and writes the other (`dst`), so after the 24
  rounds the result is back in `state`;
* `[200, 392)`: the 24 round constants, stored by the prologue;
* `[392, 404)`: the saved `esi`, `edi` and `ebp` (`ebx` is never written);
* `[448, 488)`: the five `D[x]`.

A round computes the five column parities `C[x]` (θ) in registers and from
them the five `D[x]`, which it stores in `scratch`; then, for each plane `y`
of the output, the lanes `B[x]` of `π(ρ(θ(A)))` of that plane in registers
(a lane of `src`, XORed with its `D` from memory, and rotated: two shifts
of it and of a copy), and from them the plane's lanes
`B[x] ⊕ (¬B[x+1] ∧ B[x+2])` (χ, and ι for lane 0), stored to `dst`: three
through a copy of `B[x+1]`, and then two in `B[x+1]` itself.

With eight XMM registers, every register is used again and again in a
round, for a lane and for the temporaries (of a load from memory to XOR, of
a rotation, of a copy in χ). Which one each use takes is not in the code of
`round` but in a table it is given, a *plan*: the registers in the order
the round takes them. The plans here (`planA`, `planB`, of the two rounds
of an iteration) take, for a register that is written whole (by a load or a
copy), the free one whose value is ready first in a model of the
dependencies in which such a write waits for the register's old value, as
it does where the processor keeps the registers' upper halves (Zen 4 after
256-bit code, Zen 5 while they are not zero): the planes of a round then
wait for each other less. A plan that takes a register still in use gives
wrong code, which the proof would refuse: it evaluates the round built from
the plan (`Proof/Sha3/X86/Permute.lean`).

Every address is a pointer plus a constant or the round constant pointer,
which only depends on the pointers, and the only branch is the round loop's,
which depends only on the pointers, so only the pointers can affect timing.
The loop runs two rounds per iteration, so that `esi` and `edi` are the same
source and destination of the same rounds on every iteration.
-/

@[expose] public section

namespace VG.Impl.Sha3.X86

open VG.X86
open VG.Impl.Sha3 (rhoOff piSrc)
open VG.Impl.Sha512.X86 (at_ lo hi)

/-- `++`, grouping to the right. The kernel evaluates the code (for the
constant-time analysis), and `(a ++ b) ++ c` has it copy `a` twice. -/
local infixr:65 " +++ " => HAppend.hAppend

/-- The offset in `scratch` of `D[x]`. -/
def dOff (x : Nat) : Nat := 448 + 8 * x

/-- Entry `i` of a plan. -/
def planAt (p : List XReg) (i : Nat) : XReg := p.getD i .xmm0

/-- `r ^= [b + o]`, loaded into `t`. -/
def xorm (r : XReg) (b : Reg) (o : Nat) (t : XReg) : List Instr :=
  [.movqLoad t (at_ b o), .xop (.bin .pxor r t)]

/-- `r` rotated left by `n < 64` (nothing for `n = 0`), with `t` for its
bits that leave at the top. -/
def rol (r : XReg) (n : Nat) (t : XReg) : List Instr :=
  if n = 0 then [] else
    [.xop (.bin .movdqa t r), .xop (.shift .psllq r (BitVec.ofNat 8 n)),
      .xop (.shift .psrlq t (BitVec.ofNat 8 (64 - n))), .xop (.bin .por r t)]

/-- `C[x]`, the XOR of column `x` of the state at `src`, in entry `5x` of
the plan, through the four entries after it. -/
def column (p : List XReg) (src : Reg) (x : Nat) : List Instr :=
  .movqLoad (planAt p (5 * x)) (at_ src (8 * x)) ::
    (List.range 4).flatMap fun y => xorm (planAt p (5 * x)) src (8 * (x + 5 * (y + 1))) (planAt p (5 * x + y + 1))

/-- `D[x] = ROTL¹(C[x + 1]) ⊕ C[x - 1]` for `x = 2k mod 5`, to `scratch`,
through entries `25 + 2k` and `26 + 2k` of the plan. In this order of `x`,
each `C` is last used early, and its register is free for what follows. -/
def dcol (p : List XReg) (k : Nat) : List Instr :=
  let x := 2 * k % 5
  .xop (.bin .movdqa (planAt p (25 + 2 * k)) (planAt p (5 * ((x + 1) % 5)))) ::
    (rol (planAt p (25 + 2 * k)) 1 (planAt p (26 + 2 * k)) +++
      [.xop (.bin .pxor (planAt p (25 + 2 * k)) (planAt p (5 * ((x + 4) % 5)))),
        .movqStore (at_ .edi (dOff x)) (planAt p (25 + 2 * k))])

/-- Where plane `y`'s entries start in a plan: 19 for each plane, after the
35 of θ. -/
def planeAt (y : Nat) : Nat := 35 + 19 * y

/-- `B[x]` of plane `y`: lane `piSrc x y` of the state at `src`, XORed with
its `D`, and rotated, in entry `3x` of the plane, through the two entries
after it (the second unused for the lane that is not rotated). -/
def laneB (p : List XReg) (src : Reg) (x y : Nat) : List Instr :=
  .movqLoad (planAt p (planeAt y + 3 * x)) (at_ src (8 * piSrc x y)) ::
    (xorm (planAt p (planeAt y + 3 * x)) .edi (dOff ((x + 3 * y) % 5)) (planAt p (planeAt y + 3 * x + 1)) +++
      rol (planAt p (planeAt y + 3 * x)) (rhoOff (piSrc x y)) (planAt p (planeAt y + 3 * x + 2)))

/-- Lane `x` of plane `y` of the output, which `t` holds but for the round
constant, to `dst`: for lane `(0, 0)`, after the round constant (ι),
through entry 18 of the plane. -/
def outB (p : List XReg) (dst : Reg) (x y : Nat) (t : XReg) : List Instr :=
  (if x = 0 ∧ y = 0 then xorm t .ebp 0 (planAt p (planeAt y + 18)) else []) +++
    [.movqStore (at_ dst (8 * (x + 5 * y))) t]

/-- `¬B[x + 1] ∧ B[x + 2] ⊕ B[x]` of plane `y` in a copy of `B[x + 1]`,
entry `15 + i` of the plane; then `outB`. -/
def chiCopy (p : List XReg) (dst : Reg) (y i x : Nat) : List Instr :=
  [.xop (.bin .movdqa (planAt p (planeAt y + 15 + i)) (planAt p (planeAt y + 3 * ((x + 1) % 5)))),
    .xop (.bin .pandn (planAt p (planeAt y + 15 + i)) (planAt p (planeAt y + 3 * ((x + 2) % 5)))),
    .xop (.bin .pxor (planAt p (planeAt y + 15 + i)) (planAt p (planeAt y + 3 * x)))] +++
    outB p dst x y (planAt p (planeAt y + 15 + i))

/-- The same in `B[x + 1]` itself, which is not used after it. -/
def chiLast (p : List XReg) (dst : Reg) (y x : Nat) : List Instr :=
  [.xop (.bin .pandn (planAt p (planeAt y + 3 * (x + 1))) (planAt p (planeAt y + 3 * ((x + 2) % 5)))),
    .xop (.bin .pxor (planAt p (planeAt y + 3 * (x + 1))) (planAt p (planeAt y + 3 * x)))] +++
    outB p dst x y (planAt p (planeAt y + 3 * (x + 1)))

/-- Plane `y` of the output: its five `B`, then lanes 1, 4 and 3 through
copies, and lanes 0 and 2 in `B[1]` and `B[3]`. -/
def plane (p : List XReg) (src dst : Reg) (y : Nat) : List Instr :=
  (List.range 5).flatMap (fun x => laneB p src x y) +++
    chiCopy p dst y 0 1 +++ chiCopy p dst y 1 4 +++ chiCopy p dst y 2 3 +++
    chiLast p dst y 0 +++ chiLast p dst y 2

/-- One round from `src` to `dst` but for the round constant pointer: the
lanes. -/
def lanes (p : List XReg) (src dst : Reg) : List Instr :=
  (List.range 5).flatMap (column p src) +++ (List.range 5).flatMap (dcol p) +++
    (List.range 5).flatMap (plane p src dst)

/-- One round from `src` to `dst` with the plan `p`; then advance to the
next round constant. -/
def round (p : List XReg) (src dst : Reg) : List Instr :=
  lanes p src dst +++ [.alu .add .ebp (.imm 8)]

/-- The plan of an iteration's first round, in the order `round` takes its
entries: five rows of five for the columns (`C[x]`, and the temporaries of
its other four lanes); a row for `D` (the result and the rotation's
temporary, for `x = 0, 2, 4, 1, 3`); and a row for each plane: three for
each `B[x]` (the lane, the temporary of its `D`, the rotation's temporary),
three for χ's copies, and the round constant's temporary. -/
def planA : List XReg :=
  [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4,
   .xmm5, .xmm6, .xmm7, .xmm1, .xmm2,
   .xmm3, .xmm4, .xmm6, .xmm7, .xmm1,
   .xmm2, .xmm4, .xmm6, .xmm7, .xmm1,
   .xmm4, .xmm6, .xmm7, .xmm1, .xmm6,
   .xmm7, .xmm1, .xmm6, .xmm1, .xmm5, .xmm7, .xmm2, .xmm1, .xmm0, .xmm6,
   .xmm3, .xmm4, .xmm0, .xmm7, .xmm1, .xmm5, .xmm2, .xmm6, .xmm0, .xmm4, .xmm6, .xmm1, .xmm0, .xmm6, .xmm5,
   .xmm6, .xmm1, .xmm5, .xmm6,
   .xmm3, .xmm2, .xmm2, .xmm2, .xmm0, .xmm1, .xmm0, .xmm6, .xmm4, .xmm5, .xmm7, .xmm6, .xmm1, .xmm7, .xmm7,
   .xmm4, .xmm6, .xmm7, .xmm0,
   .xmm3, .xmm0, .xmm0, .xmm2, .xmm1, .xmm4, .xmm6, .xmm1, .xmm5, .xmm0, .xmm1, .xmm7, .xmm1, .xmm4, .xmm5,
   .xmm4, .xmm7, .xmm5, .xmm0,
   .xmm3, .xmm6, .xmm6, .xmm2, .xmm4, .xmm1, .xmm7, .xmm6, .xmm4, .xmm0, .xmm6, .xmm5, .xmm6, .xmm1, .xmm4,
   .xmm1, .xmm5, .xmm4, .xmm0,
   .xmm3, .xmm7, .xmm7, .xmm2, .xmm1, .xmm6, .xmm5, .xmm7, .xmm1, .xmm0, .xmm7, .xmm4, .xmm7, .xmm6, .xmm1,
   .xmm6, .xmm4, .xmm1, .xmm0]

/-- The plan of an iteration's second round, whose registers hold what the
first left. -/
def planB : List XReg :=
  [.xmm3, .xmm5, .xmm5, .xmm2, .xmm5,
   .xmm6, .xmm7, .xmm2, .xmm4, .xmm7,
   .xmm2, .xmm0, .xmm4, .xmm1, .xmm0,
   .xmm4, .xmm1, .xmm1, .xmm1, .xmm1,
   .xmm5, .xmm7, .xmm7, .xmm0, .xmm7,
   .xmm1, .xmm0, .xmm7, .xmm0, .xmm6, .xmm1, .xmm4, .xmm0, .xmm3, .xmm7,
   .xmm2, .xmm5, .xmm0, .xmm1, .xmm0, .xmm6, .xmm4, .xmm7, .xmm3, .xmm5, .xmm7, .xmm0, .xmm3, .xmm7, .xmm6,
   .xmm7, .xmm0, .xmm6, .xmm7,
   .xmm2, .xmm4, .xmm4, .xmm4, .xmm3, .xmm0, .xmm3, .xmm7, .xmm5, .xmm6, .xmm1, .xmm7, .xmm0, .xmm1, .xmm1,
   .xmm5, .xmm7, .xmm1, .xmm0,
   .xmm2, .xmm3, .xmm3, .xmm4, .xmm0, .xmm5, .xmm7, .xmm0, .xmm6, .xmm3, .xmm0, .xmm1, .xmm0, .xmm5, .xmm6,
   .xmm5, .xmm1, .xmm6, .xmm0,
   .xmm2, .xmm7, .xmm7, .xmm4, .xmm5, .xmm0, .xmm1, .xmm7, .xmm5, .xmm3, .xmm7, .xmm6, .xmm7, .xmm0, .xmm5,
   .xmm0, .xmm6, .xmm5, .xmm0,
   .xmm2, .xmm1, .xmm1, .xmm4, .xmm0, .xmm7, .xmm6, .xmm1, .xmm0, .xmm3, .xmm1, .xmm5, .xmm1, .xmm7, .xmm0,
   .xmm7, .xmm5, .xmm0, .xmm0]

/-- Two rounds, and set ZF after the last. -/
def body : List Instr :=
  round planA .esi .edi +++ round planB .edi .esi +++
    [.mov .eax (.reg .ebp), .alu .sub .eax (.reg .edi), .alu .cmp .eax (.imm 392)]

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) := [(.esi, 392), (.edi, 396), (.ebp, 400)]

/-- Round constant `k`, stored at `scratch + 200 + 8k`. -/
def rcStore (k : Nat) : List Instr :=
  [.mov .eax (.imm (lo (Spec.Sha3.RC k))), .store (at_ .edi (200 + 8 * k)) .eax,
    .mov .eax (.imm (hi (Spec.Sha3.RC k))), .store (at_ .edi (204 + 8 * k)) .eax]

/-- Save the registers, load the arguments, store the round constants, and
point `ebp` at the first. -/
def prologue : List Instr :=
  [.mov .eax (.mem (at_ .esp 8)), .mov .ecx (.mem (at_ .esp 4))] +++
    saved.map (fun (r, d) => .store (at_ .eax d) r) +++
    [.mov .edi (.reg .eax), .mov .esi (.reg .ecx)] +++ (List.range 24).flatMap rcStore +++
    [.mov .ebp (.reg .edi), .alu .add .ebp (.imm 200)]

/-- Restore the registers (`edi`, the base, last). -/
def restore : List Instr :=
  [.mov .esi (.mem (at_ .edi 392)), .mov .ebp (.mem (at_ .edi 400)), .mov .edi (.mem (at_ .edi 396))]

def permute : Prog isa :=
  .seq (.block prologue) (.seq (.loop (.block body) .ne) (.block restore))

end VG.Impl.Sha3.X86
