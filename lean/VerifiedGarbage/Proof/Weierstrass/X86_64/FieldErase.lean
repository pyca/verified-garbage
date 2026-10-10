import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Impl.Weierstrass.X86_64
import VerifiedGarbage.Impl.Weierstrass.X86_64.ForwardField

/-!
# Field arithmetic without its displacements, for constant time

A field operation's code differs from slot to slot only in its displacements
and immediates (`Code.erase`, `Proof/Framework/X86_64/TaintErase.lean`): the
erased code of each kind of operation is one template (`FieldTmpl`), the
same for every slot, which a modulus's templates (`FieldTmpl.Ok`) prove once
for any slots, by the kernel's evaluation of the code with the slots
variables. Straight-line field arithmetic (`fprogB`) without its
displacements is then the templates one after the other
(`FieldTmpl.Ok.fprogB`), which neither the kernel nor the analysis builds
again per operation: a constant-time check of it analyses each template once
from the same taint (`Taint.constantTime_mapBlocks`).
-/

namespace VG.Proof.Weierstrass.X86_64

/-- A modulus whose products are not written out (`Mod.inl`) is itself with
`inl := false`. -/
theorem _root_.VG.Impl.Mont.Mod.with_inl_false {M : Impl.Mont.Mod} (h : M.inl = false) : { M with inl := false } = M := by
  cases M; cases h; rfl


open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Mont

/-- The code of the field operations without displacements and immediates:
a product of two different slots (`mul`) or a square (`sqr`), a sum of two
different slots (`add`) or a double (`dbl`), a difference (`sub`), and a
product by a call (`call`, if the modulus has one). -/
structure FieldTmpl where
  mul : List Instr
  sqr : List Instr
  add : List Instr
  dbl : List Instr
  sub : List Instr
  call : Prog isa
  deriving Lean.ToExpr

open Lean Meta Elab Term Command in
/-- `def_literal N := t` defines `N` as the value of the closed term `t` (of
a type with a `ToExpr` instance), evaluated in compiled code and written out
as a literal, which the kernel unfolds `N` to rather than evaluating `t`
again (and the compiler compiles, for the hints). Nothing relates `N` to `t`:
what is proven of `N` (`FieldTmpl.Ok`) is proven of the literal. -/
elab doc:(docComment)? "def_literal " id:ident " := " t:term : command => do
  let N := (← getCurrNamespace) ++ id.getId
  liftTermElabM do
    let e ← instantiateMVars (← elabTermAndSynthesize t none)
    if e.hasMVar || e.hasFVar then throwError "def_literal: {e} is not closed"
    let ty ← instantiateMVars (← inferType e)
    let inst ← synthInstance (mkApp (mkConst ``ToExpr [0]) ty)
    let l ← unsafe evalExpr Expr (mkConst ``Expr) (mkApp3 (mkConst ``ToExpr.toExpr [0]) ty inst e)
    addAndCompile <| .defnDecl {
      name := N, levelParams := [], type := ty, value := ShareCommon.shareCommon' l
      hints := .abbrev, safety := .safe }
    if let some doc := doc then addDocStringCore N (← getDocStringText doc)

/-- The erased code of a field operation, as the templates give it. -/
def FieldTmpl.op (T : FieldTmpl) (M : Mod) (op : FOp) : Prog isa :=
  match opCall? M op with
  | some _ => T.call
  | none => .block (match op with
    | .mul _ a b => bif Nat.beq a b then T.sqr else T.mul
    | .add _ a b => bif Nat.beq a b then T.dbl else T.add
    | .sub _ _ _ => T.sub)

/-- Straight-line field arithmetic, as the templates give it. (A function
compiled here: the hints of its checks evaluate it, and the compiler fails to
specialize `List.map` to `FieldTmpl.op` in an expression.) -/
def FieldTmpl.prog (T : FieldTmpl) (M : Mod) (ops : List FOp) : Prog isa := progs (ops.map (T.op M))

/-- The templates are the erased code of the operations modulo `M`, for any
slots. -/
structure FieldTmpl.Ok (T : FieldTmpl) (M : Mod) : Prop where
  mul : ∀ o a b, a ≠ b → KList.map Instr.erase (Impl.Mont.X86_64.mul M o a b) = T.mul
  sqr : ∀ o a, KList.map Instr.erase (Impl.Mont.X86_64.mul M o a a) = T.sqr
  add : ∀ o a b, a ≠ b → KList.map Instr.erase (Impl.Mont.X86_64.add M o a b) = T.add
  dbl : ∀ o a, KList.map Instr.erase (Impl.Mont.X86_64.add M o a a) = T.dbl
  sub : ∀ o a b, KList.map Instr.erase (Impl.Mont.X86_64.sub M o a b) = T.sub
  call : ∀ f body, Impl.Weierstrass.X86_64.Mont.callOf M = some (f, body) → ∀ o a b,
    Code.erase (Impl.Weierstrass.X86_64.Mont.mulCall f body o a b) = T.call

/-- The templates at slots `0`, `8` and `16` (or `0` and `8`). -/
def FieldTmpl.ofMod (M : Mod) : FieldTmpl where
  mul := KList.map Instr.erase (Impl.Mont.X86_64.mul M 0 8 16)
  sqr := KList.map Instr.erase (Impl.Mont.X86_64.mul M 0 8 8)
  add := KList.map Instr.erase (Impl.Mont.X86_64.add M 0 8 16)
  dbl := KList.map Instr.erase (Impl.Mont.X86_64.add M 0 8 8)
  sub := KList.map Instr.erase (Impl.Mont.X86_64.sub M 0 8 16)
  call := match Impl.Weierstrass.X86_64.Mont.callOf M with
    | some (f, body) => Code.erase (Impl.Weierstrass.X86_64.Mont.mulCall f body 0 8 16)
    | none => .block []

theorem progs_erase : ∀ ps : List (Prog isa), Code.erase (progs ps) = progs (ps.map Code.erase)
  | [] => rfl
  | [_] => rfl
  | p :: q :: ps => by
    show Code.seq (Code.erase p) (Code.erase (progs (q :: ps))) = _
    rw [progs_erase (q :: ps)]; rfl

theorem progs_inline : ∀ ps : List (Prog isa), (progs ps).inline = progs (ps.map Code.inline)
  | [] => rfl
  | [_] => rfl
  | p :: q :: ps => by
    show Code.seq p.inline (progs (q :: ps)).inline = _
    rw [progs_inline (q :: ps)]; rfl

variable {T : FieldTmpl} {M : Mod}

theorem FieldTmpl.Ok.opProg (hT : T.Ok M) (op : FOp) :
    Code.erase (Impl.Weierstrass.X86_64.opProg M op) = T.op M op := by
  unfold Impl.Weierstrass.X86_64.opProg FieldTmpl.op
  cases hc : opCall? M op with
  | some p =>
    simp only [Option.getD_some]
    obtain ⟨o, a, b, f, body, hf, rfl⟩ : ∃ o a b f body,
        Impl.Weierstrass.X86_64.Mont.callOf M = some (f, body) ∧
          p = Impl.Weierstrass.X86_64.Mont.mulCall f body o a b := by
      cases op with
      | mul o a b =>
        simp only [opCall?] at hc
        cases hf : Impl.Weierstrass.X86_64.Mont.callOf M with
        | none => rw [hf] at hc; cases hc
        | some fb =>
          obtain ⟨f, body⟩ := fb
          rw [hf] at hc
          by_cases hl : Impl.Weierstrass.X86_64.Mont.lowArgs M.n o a b = true
          · simp only [hl, ite_true, Option.some.injEq] at hc
            exact ⟨o, a, b, f, body, rfl, hc.symm⟩
          · simp only [hl] at hc; cases hc
      | _ => cases hc
    exact hT.call f body hf o a b
  | none =>
    simp only [Option.getD_none]
    show Code.block (KList.map Instr.erase (opCode M op)) = _
    have ne : ∀ {a b : Nat}, a ≠ b → Nat.beq a b = false := fun h =>
      Bool.eq_false_iff.mpr fun h' => h (Nat.eq_of_beq_eq_true h')
    cases op with
    | mul o a b =>
      show _ = Code.block (bif Nat.beq a b then T.sqr else T.mul)
      by_cases h : a = b
      · subst h; rw [Nat.beq_refl, Bool.cond_true]; exact congrArg _ (hT.sqr o a)
      · rw [ne h, Bool.cond_false]; exact congrArg _ (hT.mul o a b h)
    | add o a b =>
      show _ = Code.block (bif Nat.beq a b then T.dbl else T.add)
      by_cases h : a = b
      · subst h; rw [Nat.beq_refl, Bool.cond_true]; exact congrArg _ (hT.dbl o a)
      · rw [ne h, Bool.cond_false]; exact congrArg _ (hT.add o a b h)
    | sub o a b => exact congrArg _ (hT.sub o a b)

/-- Straight-line field arithmetic without its displacements is the
templates, one after the other. -/
theorem FieldTmpl.Ok.fprogB (hT : T.Ok M) (ops : List FOp) :
    Code.erase (Impl.Weierstrass.X86_64.fprogB M ops) = T.prog M ops := by
  unfold Impl.Weierstrass.X86_64.fprogB
  rw [progs_erase, List.map_map]
  exact congrArg progs (List.map_congr_left fun op _ => hT.opProg op)

/-- `fprogB`, with its calls inlined. -/
theorem FieldTmpl.Ok.fprogB_inline (hT : T.Ok M) (ops : List FOp) :
    Code.erase (Impl.Weierstrass.X86_64.fprogB M ops).inline = (T.prog M ops).inline := by
  rw [← Code.erase_inline, hT.fprogB]

/-- `fprogB`, with its calls inlined, as `Code.mapBlocks` (for `simp`). -/
theorem FieldTmpl.Ok.fprogB_mapBlocks (hT : T.Ok M) (ops : List FOp) :
    (Impl.Weierstrass.X86_64.fprogB M ops).inline.mapBlocks Instr.erase = (T.prog M ops).inline :=
  hT.fprogB_inline ops

end VG.Proof.Weierstrass.X86_64

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Mont

variable {T : FieldTmpl} {M : Mod}

/-- Constant time of straight-line field arithmetic (with its calls inlined)
from the analysis of its templates (`taint_decide`), from a taint that knows
no region bases. -/
theorem FieldTmpl.Ok.constantTime (hT : T.Ok M) {Pre : State → Prop} {Pub : State → State → Prop}
    (τ : X86_64.Taint.T) (hτ : τ.bases = []) (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → taint.Agree τ s₁ s₂)
    (ops : List FOp) {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : (taint.check τ (T.prog M ops).inline hc).isSome = true) :
    ConstantTime isa Pre Pub (Impl.Weierstrass.X86_64.fprogB M ops).inline :=
  VG.Taint.constantTime_mapBlocks taint_eraseInv τ hτ hpub (hT.fprogB_inline ops) h

/-- `ForwardField.programB` is `fprogB` but for four-word moduli. -/
theorem programB_eq (hn : M.n ≠ 4) (ops : List FOp) :
    ForwardField.programB M ops = Impl.Weierstrass.X86_64.fprogB M ops := by
  unfold ForwardField.programB Impl.Weierstrass.X86_64.fprogB Impl.Weierstrass.X86_64.opProg
  rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hn h.2)]
  refine congrArg progs (List.map_congr_left fun op _ => ?_)
  cases op <;> simp only [ForwardField.code, hn, and_false, ite_false]

/-- `FieldTmpl.Ok.constantTime`, for `ForwardField.programB`. -/
theorem FieldTmpl.Ok.constantTimeB (hT : T.Ok M) (hn : M.n ≠ 4) {Pre : State → Prop}
    {Pub : State → State → Prop} (τ : X86_64.Taint.T) (hτ : τ.bases = [])
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → taint.Agree τ s₁ s₂)
    (ops : List FOp) {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : (taint.check τ (T.prog M ops).inline hc).isSome = true) :
    ConstantTime isa Pre Pub (ForwardField.programB M ops).inline := by
  rw [programB_eq hn]; exact hT.constantTime τ hτ hpub ops h

end VG.Proof.Weierstrass.X86_64
