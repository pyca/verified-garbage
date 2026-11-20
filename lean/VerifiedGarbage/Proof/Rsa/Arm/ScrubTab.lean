module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.ICall
import VerifiedGarbage.Proof.Framework.Arm.CallF
public meta import Lean

/-!
# What the cleanup needs of code that calls the functions of its tables (ARMv7)

`CodeOk` (`Proof/Framework/Arm/ScrubProved.lean`) asks that code make no
indirect call. RSA-OAEP and RSA-PSS call their hash functions through tables
(`Code.icalls`), which ARM's cleanup accepts (`Arm.Scrub.scrubSideF`'s
`tablesCall`, #5682): `CodeOkT c n T` is that `c`'s frames use at most `n`
bytes and that it calls indirectly only functions named in `T`
(`tableFns` of the tables), from which `scrubSideF_ofT` gives `scrubSideF`.

It follows from the code's shape (`CodeOkT.seq`, `.ite`, `.loop`, `.call`,
`.alloc`, `.push`), from `CodeOk` of the pieces that call nothing
indirectly (`CodeOkT.ofOk`), and, for the indirect call of the functions of
every table (`CodeOkT.icalls`), from what each implementation states of its
own code: so a function generic over the hash functions of its tables is
proven once, without evaluating any hash function's code. `code_okT` walks
the code by these rules.

`Verified.stack_leT` is `Arm.Scrub.Verified.stack_le` for a contract with
tables of functions (`Abi.withTables`): code proven with a number of bytes
of stack that is no frame size of the model is registered with the next.
-/

-- separate module: RSA-OAEP's and RSA-PSS's functions on ARMv7 use it, without each other's proofs.

@[expose] public section

namespace VG.Proof.Rsa.Arm.Scrub

open VG.Arm VG.Arm.Scrub VG.Arm.FrameStack

/-- `c`'s frames use at most `n` bytes, and it calls indirectly only
functions named in `T`. -/
def CodeOkT (c : Prog isa) (n : Nat) (T : List String) : Prop :=
  armStack c ≤ n ∧ (inames c).all (fun f => decide (f ∈ T)) = true

theorem CodeOkT.ofOk {c : Prog isa} {n : Nat} {T : List String} (h : CodeOk c n) : CodeOkT c n T :=
  ⟨h.1, by rw [inames_of_noIcall h.2]; rfl⟩

theorem CodeOkT.block {is : List Instr} {n : Nat} {T : List String} : CodeOkT (.block is) n T :=
  ⟨Nat.zero_le n, rfl⟩

theorem CodeOkT.seq {a b : Prog isa} {n : Nat} {T : List String} (ha : CodeOkT a n T)
    (hb : CodeOkT b n T) : CodeOkT (.seq a b) n T :=
  ⟨Nat.max_le.mpr ⟨ha.1, hb.1⟩, by simp only [inames, List.all_append, ha.2, hb.2, Bool.and_self]⟩

theorem CodeOkT.ite {cc : Cond} {t e : Prog isa} {n : Nat} {T : List String} (ht : CodeOkT t n T)
    (he : CodeOkT e n T) : CodeOkT (.ite cc t e) n T :=
  ⟨Nat.max_le.mpr ⟨ht.1, he.1⟩, by simp only [inames, List.all_append, ht.2, he.2, Bool.and_self]⟩

theorem CodeOkT.loop {b : Prog isa} {cc : Cond} {n : Nat} {T : List String} (hb : CodeOkT b n T) :
    CodeOkT (.loop b cc) n T :=
  ⟨hb.1, hb.2⟩

theorem CodeOkT.call {name : String} {b : Prog isa} {n : Nat} {T : List String} (hb : CodeOkT b n T) :
    CodeOkT (.call name b) n T :=
  ⟨hb.1, hb.2⟩

theorem CodeOkT.alloc {b : Prog isa} {k n : Nat} {j : Instr} {T : List String} (hk : k ≤ n)
    (hb : CodeOkT b (n - k) T) : CodeOkT (.frame (.alloc k) b j) n T :=
  ⟨by simp only [armStack]; have := hb.1; omega, hb.2⟩

theorem CodeOkT.push {b : Prog isa} {rs : List Reg} {j : Instr} {n : Nat} {T : List String}
    (hk : 4 * rs.length ≤ n) (hb : CodeOkT b (n - 4 * rs.length) T) : CodeOkT (.frame (.push rs) b j) n T :=
  ⟨by simp only [armStack]; have := hb.1; omega, hb.2⟩

/-- The indirect call by `i` of the functions `ts`, each of which makes no
indirect call, uses no stack, and is named in `T`. -/
theorem CodeOkT.icalls {i : Instr} {n : Nat} {T : List String} :
    ∀ {ts : List (String × Prog isa)}, (∀ p ∈ ts, CodeOk p.2 0 ∧ p.1 ∈ T) → CodeOkT (Code.icalls i ts) n T
  | [], _ => CodeOkT.block
  | (f, b) :: ts, h => by
    obtain ⟨hb, hf⟩ := h (f, b) List.mem_cons_self
    obtain ⟨h1, h2⟩ := CodeOkT.icalls (i := i) (n := n) (T := T) fun p hp => h p (List.mem_cons_of_mem _ hp)
    refine ⟨Nat.max_le.mpr ⟨Nat.le_trans hb.1 (Nat.zero_le n), h1⟩, ?_⟩
    show ((f :: inames b ++ inames (Code.icalls i ts)).all _) = true
    rw [inames_of_noIcall hb.2]
    simp only [List.cons_append, List.nil_append, List.all_cons, h2, decide_eq_true hf, Bool.and_self]

/-- `scrubSideF` of code from `CodeOkT` of it. -/
theorem scrubSideF_ofT {c : Prog isa} {n : Nat} {ts : List (String × List FnTable)}
    (h : CodeOkT c n (tableFns ts)) (hn : FrameOk n) : scrubSideF c n ts = true := by
  simp only [scrubSideF, tablesCall, h.1, h.2, decide_eq_true hn, decide_true, Bool.and_self]

open Lean Meta Elab Tactic in
/-- The code `c` with its definitions unfolded until its head is one of
`Code`'s constructors, `Code.icalls` or a variable. -/
meta partial def codeHead (c : Expr) : MetaM Expr := do
  let c := (← instantiateMVars c).headBeta
  let f := c.getAppFn
  if f.isFVar || c.isAppOf ``Code.icalls then return c
  if let some n := f.constName? then
    if n == ``Code.block || n == ``Code.seq || n == ``Code.ite || n == ``Code.loop ||
        n == ``Code.call || n == ``Code.frame || n == ``Code.icall then return c
  match ← unfoldDefinition? c with
  | some c' => codeHead c'
  | none =>
    let c' ← whnfCore c
    if c' == c then return c else codeHead c'

open Lean Meta Elab Tactic in
/-- One step of `code_okT` on the goal `g`: the goals it leaves. -/
meta def codeOkTStep (g : MVarId) : TacticM (List MVarId) := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let some (c, n, T) := (do
      guard (tgt.isAppOfArity ``CodeOkT 3)
      pure (tgt.getArg! 0, tgt.getArg! 1, tgt.getArg! 2)) | return [g]
  let c ← codeHead c
  let g ← g.replaceTargetDefEq (mkApp3 (mkConst ``CodeOkT) c n T)
  let run (stx : TacticM Syntax) : TacticM (List MVarId) := do
    setGoals [g]; evalTactic (← stx); getGoals
  if c.getAppFn.isFVar then
    return ← run `(tactic| exact CodeOkT.ofOk (CodeOk.mono ‹_› (by decide)))
  if c.isAppOf ``Code.icalls then
    return ← run `(tactic| (apply CodeOkT.icalls; assumption))
  match c.getAppFn.constName? with
  | some ``Code.block => run `(tactic| exact CodeOkT.block)
  | some ``Code.seq => run `(tactic| apply CodeOkT.seq)
  | some ``Code.ite => run `(tactic| apply CodeOkT.ite)
  | some ``Code.loop => run `(tactic| apply CodeOkT.loop)
  | some ``Code.call => run `(tactic| apply CodeOkT.call)
  | some ``Code.frame =>
    let i ← whnfD (c.getArg! 2)
    if i.isAppOf ``VG.Arm.Instr.push then run `(tactic| apply CodeOkT.push (by decide))
    else if i.isAppOf ``VG.Arm.Instr.alloc then run `(tactic| apply CodeOkT.alloc (by decide))
    else throwError "code_okT: a frame of {i}"
  | _ => throwError "code_okT: no rule for {c}"

/-- Walk code by the rules of `CodeOkT`, down to its blocks: each piece is
unfolded until its head is a constructor, then the rule of that constructor
applies; an indirect call of the functions of the tables by a hypothesis in
context of what they state of their code, and a call of code that is a
variable by the hypothesis `CodeOk` of it. Stated of code whose
implementations are variables, it evaluates none of their code. -/
elab "code_okT" : tactic => do
  let mut todo ← Lean.Elab.Tactic.getGoals
  let mut rest := []
  while !todo.isEmpty do
    let g := todo.head!
    todo := todo.tail!
    let gs ← codeOkTStep g
    if gs == [g] then rest := rest ++ [g] else todo := gs ++ todo
  Lean.Elab.Tactic.setGoals rest

/-! ## The stack of a contract with tables -/

/-- `Sig.contract`'s precondition with tables of functions and `n'` bytes of
stack gives it with fewer. -/
theorem contract_pre_stack_leT {sig : Sig} {t : String × List FnTable} {ts : List (String × List FnTable)}
    {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {n n' : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s : State} (hn : n ≤ n')
    (h : (sig.contract (abi.withTables sig (t :: ts)) pre post wa n' leak).pre s) :
    (sig.contract (abi.withTables sig (t :: ts)) pre post wa n leak).pre s := by
  simp only [Sig.contract, Abi.withTables] at h ⊢
  revert h
  cases abi.args ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) with
  | none => exact id
  | some vals =>
    intro h
    simp only at h ⊢
    obtain ⟨⟨hwf, htab⟩, hrd, hwr, hpw, hres, rest⟩ := h
    cases n with
    | zero =>
      refine ⟨⟨?_, htab⟩, hrd, hwr, hpw, fun r hr => absurd hr List.not_mem_nil, rest⟩
      cases n' with
      | zero => exact hwf
      | succ m => exact hwf.2
    | succ k =>
      obtain ⟨m, rfl⟩ : ∃ m, n' = m + 1 := ⟨n' - 1, by omega⟩
      obtain ⟨hsp, hfit⟩ : m + 1 ≤ s.sp.toNat ∧ _ := hwf
      refine ⟨⟨⟨Nat.le_trans hn hsp, hfit⟩, htab⟩, hrd, hwr, hpw, fun r hr a ha => ?_, rest⟩
      obtain rfl : r = ⟨State.addr s.sp - BitVec.ofNat 64 (k + 1), k + 1⟩ := by
        simpa [abi, stackBelow] using hr
      have hsub := belowA_sub hn hsp
      rw [belowA, belowA, addr_sub' (Nat.le_trans hn hsp), addr_sub' hsp] at hsub
      exact (hres _ (by simp [abi, stackBelow]) a ha).sub_left hsub

/-- `Arm.Scrub.Verified.stack_le`, for a contract with tables of functions. -/
theorem Verified.stack_leT {sig : Sig} {t : String × List FnTable} {ts : List (String × List FnTable)}
    {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {n n' : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {c : Prog isa} (hn : n ≤ n')
    (hv : Verified target c (sig.contract (abi.withTables sig (t :: ts)) pre post wa n leak))
    (hsat : ∃ s, (sig.contract (abi.withTables sig (t :: ts)) pre post wa n' leak).pre s) :
    Verified target c (sig.contract (abi.withTables sig (t :: ts)) pre post wa n' leak) :=
  ⟨fun s hs => hv.1 s (contract_pre_stack_leT hn hs),
    fun s₁ s₂ t₁ t₂ u₁ u₂ p₁ p₂ hp e₁ e₂ =>
      hv.2.1 s₁ s₂ t₁ t₂ u₁ u₂ (contract_pre_stack_leT hn p₁) (contract_pre_stack_leT hn p₂) hp e₁ e₂, hsat⟩

end VG.Proof.Rsa.Arm.Scrub
