module

public import VerifiedGarbage.Impl.MlKem.X86_64.NttRegs
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.MlKem.X86_64.NttRegs
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.ZmLit
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.ZmLit
meta import Lean.ToExpr

/-!
# ML-KEM on x86-64: the NTT on registers, its passes as literals

The kernel evaluates the passes of `nttR` in `check` (`Run.lean`), in the
constant-time analysis, and in the checks of every instruction of the
functions that contain them; these read the literals rather than running the
register allocation again.

Materialize the shared zeta table before the passes.

The allocator's code is an array, to which it pushes each instruction
(`Alloc.emit`), and the kernel's arrays are lists: asked for the list of a
pass, it rebuilds, for each instruction, the list of those before it, 40,000
steps for the 300 instructions of half a pass. `materialize_pushed` has it
compare the pass with its literal pushed in the same way instead, one
instruction at a time onto an empty array (`of_pushed`): two arrays built by
the same pushes, which the kernel compares push by push, without building
either list.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

/-- The list of the array that `l` is pushed onto, one element at a time. -/
theorem toList_foldl_push {α : Type} (l : List α) (xs : Array α) :
    (l.foldl Array.push xs).toList = xs.toList ++ l := by
  induction l generalizing xs with
  | nil => exact (List.append_nil _).symm
  | cons a l ih => rw [List.foldl_cons, ih, Array.toList_push, List.append_assoc]; rfl

/-- `t` is `l` if it is the list of the array that `l` is pushed onto. -/
theorem of_pushed {α : Type} {t l : List α} (h : t = (l.foldl Array.push #[]).toList) : t = l :=
  h.trans ((toList_foldl_push l #[]).trans (List.nil_append l))

end VG.Proof.MlKem.X86_64.NttR

end

meta section

namespace VG

open Lean Meta Elab Command in
/-- `materialize_pushed N := t`, for a closed list `t` that is the list of an
array built by pushes: `N.lit`, the list as a literal, and
`N.lit_eq : t = N.lit`, as `materialize_value N := t`, which the kernel checks
by evaluating `t` (with the literals it reaches) against `N.lit` pushed onto
an empty array (`of_pushed`). -/
elab "materialize_pushed " id:ident " := " t:term : command => liftTermElabM do
  let e ← instantiateMVars (← Term.elabTermAndSynthesize t none)
  if e.hasMVar || e.hasFVar then throwError "materialize_pushed: {e} is not closed"
  let N := (← getCurrNamespace) ++ id.getId
  let ty ← whnfD (← inferType e)
  unless ty.isAppOfArity ``List 1 do throwError "materialize_pushed: {e} is not a list"
  let inst ← synthInstance (mkApp (mkConst ``ToExpr [0]) ty)
  let l ← unsafe evalExpr Expr (mkConst ``Expr) (mkApp3 (mkConst ``ToExpr.toExpr [0]) ty inst e)
  addDecl (forceExpose := true) <| .defnDecl {
    name := N ++ `lit, levelParams := [], type := ty, value := ShareCommon.shareCommon' l
    hints := .abbrev, safety := .safe }
  let lit := mkConst (N ++ `lit)
  -- `t = t'` with the literals `t` reaches (`unfoldToLits`), and `t' = N.lit` by `of_pushed`.
  let (e', prf) ← match ← Lit.unfoldToLits N e with
    | some r => pure r
    | none => pure (e, mkApp2 (mkConst ``Eq.refl [1]) ty e)
  let prf' := mkApp4 (mkConst ``Proof.MlKem.X86_64.NttR.of_pushed) ty.appArg! e' lit
    (mkApp2 (mkConst ``Eq.refl [1]) ty e')
  addDecl <| .thmDecl {
    name := N ++ `lit_eq, levelParams := [], type := mkApp3 (mkConst ``Eq [1]) ty e lit
    value := ShareCommon.shareCommon' (mkApp6 (mkConst ``Eq.trans [1]) ty e e' lit prf prf') }

end VG

end

@[expose] public section

namespace VG

namespace Impl.MlKem.X86_64.NttR

/-- The halves of pass B, each with a literal of its own, for the runs of
the machine on them (`Run.lean`). -/
def passBR100 : List VG.X86_64.Instr := passB .r10 0
def passBR101 : List VG.X86_64.Instr := passB .r10 1
def passBAccR100 : List VG.X86_64.Instr := passBAcc .r10 0
def passBAccR101 : List VG.X86_64.Instr := passBAcc .r10 1
def passIBAcc0 : List VG.X86_64.Instr := passIB .acc 0
def passIBAcc1 : List VG.X86_64.Instr := passIB .acc 1

end Impl.MlKem.X86_64.NttR

materialize_value Impl.MlKem.X86_64.NttR.zetaTbl

materialize_value Impl.MlKem.X86_64.NttR.passA
materialize_pushed Impl.MlKem.X86_64.NttR.passBR100 :=
  Impl.MlKem.X86_64.NttR.passB .r10 0
materialize_pushed Impl.MlKem.X86_64.NttR.passBR101 :=
  Impl.MlKem.X86_64.NttR.passB .r10 1
materialize_value Impl.MlKem.X86_64.NttR.passBsR10
materialize_pushed Impl.MlKem.X86_64.NttR.passBAccR100 :=
  Impl.MlKem.X86_64.NttR.passBAcc .r10 0
materialize_pushed Impl.MlKem.X86_64.NttR.passBAccR101 :=
  Impl.MlKem.X86_64.NttR.passBAcc .r10 1
materialize_value Impl.MlKem.X86_64.NttR.passBsAccR10
materialize_value Impl.MlKem.X86_64.NttR.passIA
materialize_pushed Impl.MlKem.X86_64.NttR.passIBAcc0 :=
  Impl.MlKem.X86_64.NttR.passIB .acc 0
materialize_pushed Impl.MlKem.X86_64.NttR.passIBAcc1 :=
  Impl.MlKem.X86_64.NttR.passIB .acc 1
materialize_value Impl.MlKem.X86_64.NttR.passIBsAcc
