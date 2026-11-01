module

public import VerifiedGarbage.Impl.X448.X86_64
public import VerifiedGarbage.Impl.Ed448.Formulas
public import VerifiedGarbage.Spec.Ed448

/-!
# Ed448's point doubling and affine addition on x86-64, as functions

`vg_ed448_r64_point_double(ws)` and `vg_ed448_r64_point_add_affine(ws)`
(`Proof/Ed448/Point64Contract.lean`; `ws` in `rdi`, where the Ed448 code keeps it)
run the field programs that code inlined, with X448's field arithmetic on
seven 64-bit words (`Impl/X448/X86_64.lean`, the baseline's
multiplications): RFC 8032's doubling (`doubleOps`) of slots 0–2, and the
addition of `(x : y : 1)`, `x` and `y` in slots 8 and 9, to slots 0–2, into
slots 3–5 (`addAffineOps`): `addOps` with `A = Z₁` for `Z₁ Z₂`, one product
fewer. The product by `d = -39081` uses X448's seven-by-one-word
multiplier after negation, instead of a full field multiplication. Each keeps the callee-saved registers the field arithmetic writes
(`rbp`, `r12`–`r15`) in `xmm0`–`xmm4`, which are caller-saved, and restores
them. It uses no stack and never writes `rdi`, every address is `rdi` plus a
constant, and it has no branch: only the pointer may affect timing.
-/

@[expose] public section

namespace VG.Impl.Ed448.X86_64

open VG.X86_64
open VG.Impl.X448.X86_64 (slot Field)

/-! ## Field programs on the slots -/

/-- The code of a field operation (`Impl/Ed448/Formulas.lean`), with the field
multiplications `F`. -/
def fopCode (F : Field) : FOp → List Instr
  | .mul o a b => F.mul (slot o) (slot a) (slot b)
  | .sqr o a => F.sqr (slot o) (slot a)
  | .add o a b => Impl.X448.X86_64.add (slot o) (slot a) (slot b)
  | .sub o a b => Impl.X448.X86_64.sub (slot o) (slot a) (slot b)

def fieldCode (F : Field) (ops : List FOp) : List Instr := ops.flatMap (fopCode F)

/-- `T = R + (x : y : 1)` into slots 3–5, for `R` in slots 0–2, `x` and `y` in
slots 8 and 9, and `d` in slot 11: `addOps` with `A = Z₁ Z₂ = Z₁`, so that slot 2
stands for `A` and `B = Z₁²`. -/
def addAffineOps : List FOp := [
  .sqr 13 2, .mul 14 0 8, .mul 15 1 9, .mul 16 11 14, .mul 16 16 15,
  .sub 17 13 16, .add 18 13 16, .add 19 0 1, .add 20 8 9, .mul 19 19 20, .mul 20 2 17,
  .sub 19 19 14, .sub 19 19 15, .mul 3 20 19, .mul 20 2 18, .sub 19 15 14, .mul 4 20 19,
  .mul 5 17 18]

namespace Point64

/-- The callee-saved registers the field arithmetic writes, and the `xmm` register each is
kept in. -/
def kept : List (Reg × XReg) :=
  [(.rbp, .xmm0), (.r12, .xmm1), (.r13, .xmm2), (.r14, .xmm3), (.r15, .xmm4)]

def saves : List Instr := kept.map fun (r, x) => .xop (.movq x r)

def restores : List Instr := kept.map fun (r, x) => .movqR r x

/-- Multiply slot 14 by Ed448's `d = -39081` into slot 16, using the
seven-by-one-word multiplier shared with X448. Only slot 16 is changed. -/
def mulD : List Instr :=
  Impl.X448.X86_64.sub (slot 16) (slot 14) (slot 14) ++
  Impl.X448.X86_64.sub (slot 16) (slot 16) (slot 14) ++
  Impl.X448.X86_64.baseline.a24 (slot 16) (slot 16)

/-- Affine addition with the multiplication by `d` specialized. -/
def addCodeWith (F : Field) : List Instr :=
  fieldCode F (addAffineOps.take 3) ++ mulD ++
  fieldCode F (addAffineOps.drop 4)

/-- A function running the field program `ops`, with the baseline's multiplications. -/
def fnWith (F : Field) (ops : List FOp) : Prog isa :=
  .block (saves ++ fieldCode F ops ++ restores)

def addCode : List Instr := addCodeWith Impl.X448.X86_64.baseline
def fn (ops : List FOp) : Prog isa := fnWith Impl.X448.X86_64.baseline ops

def doubleFnWith (F : Field) : Prog isa := fnWith F doubleOps
def addFnWith (F : Field) : Prog isa := .block (saves ++ addCodeWith F ++ restores)

/-- `vg_ed448_r64_point_double`: slots 0–2 doubled. -/
def doubleFn : Prog isa := fn doubleOps

/-- `vg_ed448_r64_point_add_affine`: slots 0–2 plus `(x : y : 1)` from slots 8–9, into 3–5. -/
def addFn : Prog isa := addFnWith Impl.X448.X86_64.baseline

def doubleCall : Prog isa := .call "vg_ed448_r64_point_double" doubleFn
def addCall : Prog isa := .call "vg_ed448_r64_point_add_affine" addFn

/-- The point operations a caller runs: the doubling and the affine addition. -/
structure Ops where
  dbl : Prog isa
  add : Prog isa

/-- The operations as calls of the functions. -/
def calls : Ops := ⟨doubleCall, addCall⟩

/-- The operations as the functions' code, as the calls run it (`Code.inline`). -/
def bodies : Ops := ⟨doubleFn, addFn⟩

end Point64

end VG.Impl.Ed448.X86_64
