import VerifiedGarbage.Impl.Ed25519.X86_64.Field
import VerifiedGarbage.Spec.Ed25519.Point64

/-!
# Ed25519's point doubling and cached addition on x86-64, as functions

`vg_ed25519_r64_double_ext`, `_double_proj`, `_add_cached_ext` and
`_add_cached_proj` (`Spec/Ed25519/Point64.lean`), each with the baseline's
field multiplications and with BMI2 and ADX's (`_adx`): `ws` is in `rdi`,
where the Ed25519 code keeps it. Each keeps the callee-saved registers the
field arithmetic writes (`rbp`, `r12`–`r15`) in `xmm0`–`xmm4`, which are
caller-saved, runs the field program the code inlined (`dblOps`,
`addCachedOps`: slots 0–3 are the point, slots 4–7 the cached operand, slots
8–15 the temporaries), and restores them. It uses no stack and never writes
`rdi`, every address is `rdi` plus a constant, and it has no branch: only the
pointer may affect timing.
-/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64

/-- Doubles slots 0–3 in place with RFC 8032's formula (§5.1.4): `A = X²`, `B = Y²`,
`C = 2Z²`, `H = A + B`, `E = H - (X + Y)²`, `G = A - B`, `F = C + G`, and `X = EF`, `Y = GH`,
`Z = FG`, and `T = EH` if `t` (only an addition reads `T`). -/
def dblOps (t : Bool) : List FieldOp :=
  [.sqr 8 0, .sqr 9 1, .sqr2 10 2, .add 14 8 9, .add 11 0 1, .sqr 11 11, .sub 11 14 11,
    .sub 12 8 9, .add 13 10 12, .mul 0 11 13, .mul 1 12 14, .mul 2 13 12] ++
    if t then [.mul 3 11 14] else []

/-- Adds the point whose cached form `[Y - X, Y + X, 2dT, 2Z]` is in slots 4–7 to slots 0–3,
computing `T` only if `t`: the last addition at a position need not, as a doubling or the final
comparison follows it, and neither reads `T`. -/
def addCachedOps (t : Bool) : List FieldOp :=
  [.sub 8 1 0, .mul 8 8 4, .add 9 1 0, .mul 9 9 5, .mul 10 3 6, .mul 11 2 7,
    .sub 12 9 8, .sub 13 11 10, .add 14 11 10, .add 15 9 8,
    .mul 0 12 13, .mul 1 14 15, .mul 2 13 14] ++
    if t then [.mul 3 12 15] else []

namespace Point64

/-- The callee-saved registers the field arithmetic writes, and the `xmm` register each is
kept in. -/
def kept : List (Reg × XReg) :=
  [(.rbp, .xmm0), (.r12, .xmm1), (.r13, .xmm2), (.r14, .xmm3), (.r15, .xmm4)]

def saves : List Instr := kept.map fun (r, x) => .xop (.movq x r)

def restores : List Instr := kept.map fun (r, x) => .movqR r x

/-- A function running the field program `ops`. -/
def fn (fld : Arith) (ops : List FieldOp) : Prog isa := .block (saves ++ fieldCode fld ops ++ restores)

/-- The doubling, computing `T` if `t`. -/
def doubleFn (fld : Arith) (t : Bool) : Prog isa := fn fld (dblOps t)

/-- The cached addition, computing `T` if `t`. -/
def addFn (fld : Arith) (t : Bool) : Prog isa := fn fld (addCachedOps t)

/-- The doubling's name, with the field multiplications' suffix `fs`. -/
def doubleName (t : Bool) (fs : String) : String :=
  (if t then Spec.Ed25519.Point64.doubleExtApi.name else Spec.Ed25519.Point64.doubleProjApi.name) ++ fs

/-- The cached addition's name, with the field multiplications' suffix `fs`. -/
def addName (t : Bool) (fs : String) : String :=
  (if t then Spec.Ed25519.Point64.addCachedExtApi.name else Spec.Ed25519.Point64.addCachedProjApi.name) ++ fs

/-- A call of the doubling with the field multiplications `fld`. -/
def doubleCall (fld : Arith) (t : Bool) : Prog isa := .call (doubleName t fld.suffix) (doubleFn fld t)

/-- A call of the cached addition with the field multiplications `fld`. -/
def addCall (fld : Arith) (t : Bool) : Prog isa := .call (addName t fld.suffix) (addFn fld t)

/-- The point operations a caller runs: the doubling and the cached addition, computing `T` if
their argument is `true`. -/
structure Ops where
  dbl : Bool → Prog isa
  add : Bool → Prog isa

/-- The operations as calls of the functions. -/
def calls (fld : Arith) : Ops := ⟨doubleCall fld, addCall fld⟩

/-- The operations as the functions' code, as the calls run it (`Code.inline`). -/
def bodies (fld : Arith) : Ops := ⟨doubleFn fld, addFn fld⟩

end Point64

end VG.Impl.Ed25519.X86_64
