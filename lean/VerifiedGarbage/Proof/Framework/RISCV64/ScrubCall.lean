module

public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Impl.ICall

/-!
# The cleanup of a function generic over what it calls (64-bit RISC-V)

What the cleanup needs of a function's code, callees included, is one
Boolean (`RISCV64.Scrub.scrubSide`): the depth of its frames
(`Code.riscv64Depth`) and that it calls indirectly only the functions of its
tables (`tablesCall`). A function generic over an implementation it calls (a
variant, `Proof/Variants/<Iface>/RISCV64.lean`) has code that is not a closed
term: it is the function's own code with the implementation's code where it
calls it, and each implementation is evaluated where it is defined, never in
its callers.

`sdepth_eq`: the depth that the proofs of the functions bound their frames by
(`sdepth`, `Proof/Framework/RISCV64/CallAny.lean`) is the cleanup's.

`Fill n N a b`, as on x86 (`Proof/Framework/X86/ScrubCall.lean`), says that
`b` is the code `a` with some of its places for an implementation filled:
an empty block, by code that uses at most `n` bytes of stack and calls
nothing indirectly (`calleeSide`); a stub that uses `k` bytes of stack
(`holeStub k`), by such code within `k`; or an empty block, by an indirect
call (`Code.icalls`) of any number of functions, each named in `N` and
meeting `calleeSide _ n`: the call through a table of the functions of every
implementation. `a` is the function's code with a stub, and `b` its code
with the implementations. A function proves it once of every
implementation, by `fill_calls` (which walks the function's code, not the
implementation's), from what the implementation states of its own code
where it is defined. `scrubSide_of_fill` then gives `scrubSide b W rb ts`
from `scrubSide a m rb ts`, which the kernel evaluates once, of the stub's
code, with `m + n ≤ W` and the names `N` among the tables' functions:

    theorem keySearch_side (v : RoundImpl) :
        scrubSide (Impl.RsaKeyGen.RISCV64.Fn.body v.suffix v.code) 656 32 [] = true :=
      scrubSide_of_fill (W := 656) (by fill_calls) body_stub_side (fun _ h => h) (fun _ h => nomatch h)

and the theorem that the registration binds takes it, with nothing in it that
evaluates an implementation's code.
-/

@[expose] public section

namespace VG.RISCV64

theorem frameBytes_eq (i : Instr) : Instr.frameBytes i = frameBytes i := by
  cases i <;> rfl

/-- The depth the proofs bound a function's frames by (`sdepth`) is the
depth the cleanup zeroes (`Code.riscv64Depth`). -/
theorem sdepth_eq (c : Prog isa) : sdepth c = c.riscv64Depth := by
  induction c with
  | block => rfl
  | seq _ _ iha ihb | ite _ _ _ iha ihb | icall _ _ _ _ iha ihb =>
    simp only [sdepth, Code.riscv64Depth, iha, ihb]
  | loop _ _ ih | call _ _ ih => simp only [sdepth, Code.riscv64Depth, ih]
  | frame i _ _ ih => simp only [sdepth, Code.riscv64Depth, ih, frameBytes_eq, Nat.add_comm]

theorem depth_le_of_sdepth {c : Prog isa} {n : Nat} (h : sdepth c ≤ n) : c.riscv64Depth ≤ n :=
  sdepth_eq c ▸ h

namespace Scrub

/-- What the cleanup of a function that calls `c` needs of it: at most `n`
bytes of stack, and no indirect call. -/
def calleeSide (c : Prog isa) (n : Nat) : Bool :=
  decide (c.riscv64Depth ≤ n) && (inames c).isEmpty

theorem of_calleeSide {c : Prog isa} {n : Nat} (h : calleeSide c n = true) :
    c.riscv64Depth ≤ n ∧ inames c = [] := by
  simp only [calleeSide, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at h
  exact h

theorem calleeSide_of {c : Prog isa} {n : Nat} (hd : c.riscv64Depth ≤ n) (hi : inames c = []) :
    calleeSide c n = true := by
  simp only [calleeSide, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff]
  exact ⟨hd, hi⟩

theorem calleeSide_mono {c : Prog isa} {n m : Nat} (h : calleeSide c n = true) (hm : n ≤ m) :
    calleeSide c m = true :=
  calleeSide_of (Nat.le_trans (of_calleeSide h).1 hm) (of_calleeSide h).2

/-- A stub's place for an implementation that uses at most `k` bytes of
stack: a frame of `k` bytes around nothing. -/
def holeStub (k : Nat) : Prog isa := .frame (.alloc k) (.block []) (.free k)

/-- The indirect call of functions that each use at most `n` bytes of stack
uses at most `n`. -/
theorem icalls_depth (i : Instr) :
    ∀ {ts : List (String × Prog isa)} {n : Nat}, (∀ e ∈ ts, e.2.riscv64Depth ≤ n) →
      (Code.icalls i ts).riscv64Depth ≤ n
  | [], _, _ => Nat.zero_le _
  | e :: ts, _, h => by
    simp only [Code.icalls, Code.riscv64Depth, Nat.max_le]
    exact ⟨h e List.mem_cons_self, icalls_depth i fun e' he' => h e' (List.mem_cons_of_mem _ he')⟩

/-- The functions the indirect call of `ts` may call: theirs, by name, and
those they call indirectly. -/
theorem mem_inames_icalls (i : Instr) :
    ∀ {ts : List (String × Prog isa)} {f : String}, f ∈ inames (Code.icalls i ts) →
      ∃ e ∈ ts, f = e.1 ∨ f ∈ inames e.2
  | [], _, h => absurd (h : _ ∈ ([] : List String)) List.not_mem_nil
  | (nm, c) :: ts, f, h => by
    simp only [Code.icalls, inames, List.cons_append, List.mem_cons, List.mem_append] at h
    rcases h with h | h | h
    · exact ⟨(nm, c), List.mem_cons_self, .inl h⟩
    · exact ⟨(nm, c), List.mem_cons_self, .inr h⟩
    · obtain ⟨e', he', h'⟩ := mem_inames_icalls i h
      exact ⟨e', List.mem_cons_of_mem _ he', h'⟩

/-- `b` is `a` with some of its places for an implementation filled: an
empty block by code that meets `calleeSide _ n` (`hole`), a stub of `k`
bytes (`holeStub k`) by code that meets `calleeSide _ k` (`budget`), or an
empty block by the indirect call of functions named in `N` that each meet
`calleeSide _ n` (`icalls`); and the names of its calls changed. Code the
two share is matched as it is (`refl`); its blocks, conditions, frames and
indirect calls are otherwise `a`'s. -/
inductive Fill (n : Nat) (N : List String) : Prog isa → Prog isa → Prop
  | refl (a : Prog isa) : Fill n N a a
  | block (is : List Instr) : Fill n N (.block is) (.block is)
  | hole {d : Prog isa} : calleeSide d n = true → Fill n N (.block []) d
  | budget {k : Nat} {d : Prog isa} : calleeSide d k = true → Fill n N (holeStub k) d
  | icalls (i : Instr) {ts : List (String × Prog isa)} :
      (∀ e ∈ ts, e.1 ∈ N ∧ calleeSide e.2 n = true) → Fill n N (.block []) (Code.icalls i ts)
  | seq {a b a' b' : Prog isa} : Fill n N a a' → Fill n N b b' → Fill n N (.seq a b) (.seq a' b')
  | ite {t e t' e' : Prog isa} (c : Cond) :
      Fill n N t t' → Fill n N e e' → Fill n N (.ite c t e) (.ite c t' e')
  | loop {b b' : Prog isa} (c : Cond) : Fill n N b b' → Fill n N (.loop b c) (.loop b' c)
  | call {b b' : Prog isa} (f g : String) : Fill n N b b' → Fill n N (.call f b) (.call g b')
  | frame {b b' : Prog isa} (i j : Instr) : Fill n N b b' → Fill n N (.frame i b j) (.frame i b' j)
  | icall {b x b' x' : Prog isa} (i : Instr) (f : String) :
      Fill n N b b' → Fill n N x x' → Fill n N (.icall i f b x) (.icall i f b' x')

namespace Fill

variable {n : Nat} {N : List String} {a b : Prog isa}

theorem depth_le (h : Fill n N a b) : b.riscv64Depth ≤ a.riscv64Depth + n := by
  induction h with
  | refl | block => exact Nat.le_add_right _ _
  | hole hd => simp only [Code.riscv64Depth, Nat.zero_add]; exact (of_calleeSide hd).1
  | budget hd =>
    simp only [holeStub, Code.riscv64Depth, frameBytes, Nat.zero_add]
    exact Nat.le_trans (of_calleeSide hd).1 (Nat.le_add_right _ _)
  | icalls i hts =>
    simp only [Code.riscv64Depth, Nat.zero_add]
    exact icalls_depth i fun e he => (of_calleeSide (hts e he).2).1
  | seq _ _ iha ihb | ite _ _ _ iha ihb | icall _ _ _ _ iha ihb =>
    simp only [Code.riscv64Depth]; omega
  | loop _ _ ih | call _ _ _ ih => simp only [Code.riscv64Depth]; exact ih
  | frame _ _ _ ih => simp only [Code.riscv64Depth]; omega

/-- The functions `b` may call indirectly are `a`'s and those of `N`. -/
theorem inames_sub (h : Fill n N a b) : ∀ f ∈ inames b, f ∈ inames a ∨ f ∈ N := by
  induction h with
  | refl | block => exact fun f hf => .inl hf
  | hole hd => intro f hf; rw [(of_calleeSide hd).2] at hf; exact absurd hf List.not_mem_nil
  | budget hd => intro f hf; rw [(of_calleeSide hd).2] at hf; exact absurd hf List.not_mem_nil
  | icalls i hts =>
    intro f hf
    obtain ⟨e, he, h | h⟩ := mem_inames_icalls i hf
    · exact .inr (h ▸ (hts e he).1)
    · rw [(of_calleeSide (hts e he).2).2] at h; exact absurd h List.not_mem_nil
  | seq _ _ iha ihb | ite _ _ _ iha ihb =>
    intro f hf
    simp only [inames, List.mem_append] at hf ⊢
    rcases hf with hf | hf
    · exact (iha f hf).imp_left .inl
    · exact (ihb f hf).imp_left .inr
  | loop _ _ ih | call _ _ _ ih | frame _ _ _ ih => simpa only [inames] using ih
  | icall _ g _ _ ihb ihx =>
    intro f hf
    simp only [inames, List.cons_append, List.mem_cons, List.mem_append] at hf
    rcases hf with hf | hf | hf
    · exact .inl (by simp [inames, hf])
    · exact (ihb f hf).imp_left fun h => by simp [inames, h]
    · exact (ihx f hf).imp_left fun h => by simp [inames, h]

theorem mono {m : Nat} (hm : n ≤ m) (h : Fill n N a b) : Fill m N a b := by
  induction h with
  | refl a => exact .refl a
  | block is => exact .block is
  | hole hd => exact .hole (calleeSide_mono hd hm)
  | budget hd => exact .budget hd
  | icalls i hts => exact .icalls i fun e he => ⟨(hts e he).1, calleeSide_mono (hts e he).2 hm⟩
  | seq _ _ iha ihb => exact .seq iha ihb
  | ite c _ _ iht ihe => exact .ite c iht ihe
  | loop c _ ih => exact .loop c ih
  | call f g _ ih => exact .call f g ih
  | frame i j _ ih => exact .frame i j ih
  | icall i f _ _ ihb ihx => exact .icall i f ihb ihx

/-- `Fill` into code that the implementation chooses (`if p then x else y`),
where it chooses `x`. -/
theorem if_pos {p : Prop} [Decidable p] {x y : Prog isa} (h : Fill n N a x) (hp : p) :
    Fill n N a (if p then x else y) := by
  rw [ite_eq_left hp]; exact h

/-- `Fill` into code that the implementation chooses, where it chooses `y`. -/
theorem if_neg {p : Prop} [Decidable p] {x y : Prog isa} (h : Fill n N a y) (hp : ¬p) :
    Fill n N a (if p then x else y) := by
  rw [ite_eq_right hp]; exact h

/-- `Fill` of code that both choose by the same `if p`, the function's own
choice (`if c.big`): of each branch, given its condition. -/
theorem ite_same {p : Prop} [Decidable p] {x y x' y' : Prog isa} (hx : p → Fill n N x x')
    (hy : ¬p → Fill n N y y') : Fill n N (if p then x else y) (if p then x' else y') := by
  by_cases hp : p
  · rw [ite_eq_left hp, ite_eq_left hp]; exact hx hp
  · rw [ite_eq_right hp, ite_eq_right hp]; exact hy hp

end Fill

/-- `scrubSide` of a function's code `b` over `W` bytes, with a result of
`rb` bits and the tables `ts`, whatever the implementations it calls
(`Fill n N a b`), from `scrubSide` of its code `a` with a stub, which the
kernel evaluates once, over `m` bytes and with tables `ts₀` (none, where the
stub calls nothing indirectly) whose functions are among `ts`'s, `m + n ≤ W`
a multiple of 16, and the names `N` among the tables' functions. -/
theorem scrubSide_of_fill {n m W rb : Nat} {N : List String} {ts₀ ts : List (String × List FnTable)}
    {a b : Prog isa} (hf : Fill n N a b) (ha : scrubSide a m rb ts₀ = true)
    (h₀ : ∀ f ∈ tableFns ts₀, f ∈ tableFns ts) (hN : ∀ f ∈ N, f ∈ tableFns ts)
    (hW : m + n ≤ W ∧ W < 2 ^ 64 ∧ W % 16 = 0 := by decide) :
    scrubSide b W rb ts = true := by
  obtain ⟨hd, -, -, ht, hrb⟩ := of_scrubSide ha
  have hdb := hf.depth_le
  have ht' : tablesCall b ts = true := by
    simp only [tablesCall, List.all_eq_true, decide_eq_true_eq] at ht ⊢
    intro f hf'
    rcases hf.inames_sub f hf' with h | h
    · exact h₀ f (ht f h)
    · exact hN f h
  simp only [scrubSide, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨⟨⟨by omega, hW.2.1⟩, hW.2.2⟩, ht'⟩, hrb⟩

/-- Proves `Fill n N a b` of a function's code with a stub (`a`) and with
implementations (`b`), from hypotheses `calleeSide c k = true` of each
implementation's code `c`, and, for an indirect call of the functions of
every implementation, `∀ e ∈ ts, e.1 ∈ N ∧ calleeSide e.2 n = true`: it
walks the function's code, unfolding its definitions, and closes each place
it calls an implementation by its hypothesis. Code the two share is matched
as one term (`Fill.refl`, at reducible transparency, so it is not unfolded),
and a block of the same instructions as one (`Fill.block`); a part filled by
a hypothesis `Fill n N a b` is closed by it. Where the
function's code depends on the implementation otherwise, by an `if p`
(`Fill.if_pos`, `Fill.if_neg`), a hypothesis `p` or `¬p` chooses the branch;
where both choose by the same `if`, each branch is walked (`Fill.ite_same`). -/
macro "fill_calls" : tactic => `(tactic| repeat' (first
  | with_reducible exact Fill.refl _
  | with_reducible assumption
  | exact Fill.block _
  | exact Fill.hole (by assumption)
  | exact Fill.budget (by assumption)
  | exact Fill.icalls _ (by assumption)
  | refine Fill.seq ?_ ?_
  | refine Fill.ite _ ?_ ?_
  | refine Fill.loop _ ?_
  | refine Fill.call _ _ ?_
  | refine Fill.frame _ _ ?_
  | refine Fill.icall _ _ ?_ ?_
  | refine Fill.ite_same (fun _ => ?_) (fun _ => ?_)
  | refine Fill.if_pos ?_ (by assumption)
  | refine Fill.if_neg ?_ (by assumption)))

end Scrub

end VG.RISCV64
