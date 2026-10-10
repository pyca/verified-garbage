import Lean.Elab.ElabRules

/-!
# Long lists of AArch64 instructions

Untrusted: this only builds terms, which the kernel checks as usual.

`aarch64_instrs% [i₀, i₁, …]` is the list `[i₀, i₁, …] : List VG.AArch64.Instr`,
built directly as the term the elaborator builds for it. Each instruction
written as a constructor applied to arguments (`.ldr .x .x1 .x0 576`) is the
constructor applied to: for an argument `.c`, the constructor `c` of its
type, without arguments; for a numeral of type `Nat`, the numeral
`@OfNat.ofNat Nat n (instOfNatNat n)`; for anything else, the argument
elaborated against its type. Any other instruction is elaborated as a term
of type `Instr`. The allocated code of P-256 (`Impl/P256/*AllocatedCode.lean`,
thousands of instructions) took most of its modules' time in the term
elaborator, an instruction at a time.
-/

namespace VG.Impl.AArch64Instrs
open Lean Elab Term Meta

/-- `@OfNat.ofNat Nat n (instOfNatNat n)`, the numeral `n : Nat`. -/
def natLit (n : Nat) : Expr :=
  mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Nat) (mkRawNatLit n)
    (mkApp (mkConst ``instOfNatNat) (mkRawNatLit n))

/-- The instruction `stx`, built directly where it is a constructor of
`Instr` applied to arguments, else elaborated. -/
def instr (instrTy : Expr) (stx : Syntax) : TermElabM Expr := do
  let slow : TermElabM Expr := do
    instantiateMVars (← elabTermEnsuringType stx instrTy)
  let (fn, args) :=
    if stx.isOfKind ``Lean.Parser.Term.app then (stx[0], stx[1].getArgs) else (stx, #[])
  unless fn.isOfKind ``Lean.Parser.Term.dotIdent do return ← slow
  let ctor := `VG.AArch64.Instr ++ fn[1].getId
  let env ← getEnv
  let some (.ctorInfo ci) := env.find? ctor | return ← slow
  unless ci.numParams == 0 && ci.numFields == args.size do return ← slow
  forallTelescope ci.type fun xs _ => do
    let mut vals := #[]
    for h : i in [0:args.size] do
      let a := args[i]
      let ty ← whnfD (← inferType xs[i]!)
      let v ← (do
        if a.isOfKind ``Lean.Parser.Term.dotIdent then
          if let .const T _ := ty.getAppFn then
            let c := T ++ a[1].getId
            if let some (.ctorInfo cj) := env.find? c then
              if cj.numParams == 0 && cj.numFields == 0 && ty.getAppNumArgs == 0 then
                return some (mkConst c)
          return none
        if let some n := a.isNatLit? then
          if ty.isConstOf ``Nat then return some (natLit n)
        return none : TermElabM (Option Expr))
      match v with
      | some v => vals := vals.push v
      | none =>
        -- The arguments' types do not depend on earlier arguments here.
        if (← inferType xs[i]!).hasLooseBVars || xs[:i].toArray.any (fun x => (ty.containsFVar x.fvarId!)) then
          return ← slow
        vals := vals.push (← instantiateMVars (← elabTermEnsuringType a ty))
    return mkAppN (mkConst ctor) vals

end VG.Impl.AArch64Instrs

/-- `aarch64_instrs% [i, …]`: the list of AArch64 instructions, `List VG.AArch64.Instr`. -/
syntax (name := aarch64Instrs) "aarch64_instrs% " "[" term,* "]" : term

open Lean Elab Term in
elab_rules : term
  | `(aarch64_instrs% [$xs,*]) => do
    let instrTy := Lean.mkConst `VG.AArch64.Instr
    let mut e := mkApp (Lean.mkConst ``List.nil [.zero]) instrTy
    for x in xs.getElems.reverse do
      e := mkApp3 (Lean.mkConst ``List.cons [.zero]) instrTy (← VG.Impl.AArch64Instrs.instr instrTy x) e
    return e
