import VerifiedGarbage.Impl.X448.X86_64
import VerifiedGarbage.Impl.Ed448.Formulas
import VerifiedGarbage.Spec.Ed448.Point64

/-!
# Ed448's point doubling and affine addition on x86-64, as functions

`vg_ed448_r64_point_double(ws)` and `vg_ed448_r64_point_add_affine(ws)`
(`Spec/Ed448/Point64.lean`; `ws` in `rdi`, where the Ed448 code keeps it)
run the field programs that code inlined, with X448's field arithmetic on
seven 64-bit words (`Impl/X448/X86_64.lean`, the baseline's
multiplications): RFC 8032's doubling (`doubleOps`) of slots 0–2, and the
addition of `(x : y : 1)`, `x` and `y` in slots 8 and 9, to slots 0–2, into
slots 3–5 (`addAffineOps`): `addOps` with `A = Z₁` for `Z₁ Z₂`, one product
fewer. Each keeps the callee-saved registers the field arithmetic writes
(`rbp`, `r12`–`r15`) in `xmm0`–`xmm4`, which are caller-saved, and restores
them. It uses no stack and never writes `rdi`, every address is `rdi` plus a
constant, and it has no branch: only the pointer may affect timing.
-/

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

/-- A function running the field program `ops`, with the baseline's multiplications. -/
def fn (ops : List FOp) : Prog isa :=
  .block (saves ++ fieldCode Impl.X448.X86_64.baseline ops ++ restores)

/-- `vg_ed448_r64_point_double`: slots 0–2 doubled. -/
def doubleFn : Prog isa := fn doubleOps

/-- `vg_ed448_r64_point_add_affine`: slots 0–2 plus `(x : y : 1)` from slots 8–9, into 3–5. -/
def addFn : Prog isa := fn addAffineOps

def doubleCall : Prog isa := .call Spec.Ed448.Point64.doubleApi.name doubleFn
def addCall : Prog isa := .call Spec.Ed448.Point64.addAffineApi.name addFn

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
