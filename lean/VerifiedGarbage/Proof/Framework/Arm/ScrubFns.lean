module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Framework.Arm.ViaReg

/-!
# Scrubbed code that calls functions of public address (ARMv7)

`verifiedScrubbedAll` (`ScrubProved.lean`) asks that code call indirectly
only the functions of its tables. Code under a calling convention with
functions of public address (`Abi.withFns`, e.g. a body that calls one
function by the address its caller leaves it, `Code.icalls i [(n, b)]`) may
call those too (`fnsCall`): two runs that agree on what is public agree on
their addresses (`fnsCall_pub`), which is what `Verified.scrubAllS` needs of
the functions code calls indirectly. `verifiedScrubbedAllFns` is
`verifiedScrubbedAll` for such a contract, stated of the contract itself, as
the registration of a function with `fns` binds it.
-/

@[expose] public section

namespace VG.Arm.Scrub

open VG.Arm.FrameStack VG.Impl.Scrub.Arm

/-- A calling convention with functions of public address is one the cleanup
works under, as the one it strengthens is. -/
theorem ScrubAbi.withFns {A : Abi isa} (hA : ScrubAbi A) (fns : List String) : ScrubAbi (A.withFns fns) := by
  cases fns with
  | nil => exact hA
  | cons f fs =>
    exact ⟨hA.ptrBits, hA.mem, hA.ret, hA.reserved, hA.wr, hA.wf, fun s₁ s₂ h => hA.pub s₁ s₂ h.1, hA.rdSub,
      hA.argsLen⟩

/-- `c` calls indirectly only the functions `fns` and those of the tables `ts`. -/
def fnsCall (c : Prog isa) (fns : List String) (ts : List (String × List FnTable)) : Bool :=
  (inames c).all fun f => decide (f ∈ fns ∨ f ∈ tableFns ts)

/-- The functions of public address have the same addresses in two runs that
agree on what is public. -/
theorem fns_pub_syms {A : Abi isa} {fns : List String} {s₁ s₂ : State} (h : (A.withFns fns).pub s₁ s₂) :
    ∀ f ∈ fns, isa.fnAddr s₁ f = isa.fnAddr s₂ f := by
  intro f hf
  cases fns with
  | nil => simp at hf
  | cons g gs => exact h.2 f hf

/-- What is public under the tables `ts` is public without them. -/
theorem withTables_pub {A : Abi isa} {sig : Sig} {ts : List (String × List FnTable)} {s₁ s₂ : State}
    (h : (A.withTables sig ts).pub s₁ s₂) : A.pub s₁ s₂ := by
  cases ts with
  | nil => exact h
  | cons t ts => exact h.1

/-- Code that calls indirectly only the functions `fns` and those of the
tables `ts` calls functions whose addresses two runs that agree on what is
public agree on. -/
theorem fnsCall_pub {A : Abi isa} {fns : List String} {sig : Sig} {ts : List (String × List FnTable)}
    {pre : Curry (sig.words ((A.withFns fns).withTables sig ts).ptrBits) (Mem → Prop)}
    {post : sig.Post ((A.withFns fns).withTables sig ts).ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words ((A.withFns fns).withTables sig ts).ptrBits) (Mem → List Nat))}
    {c : Prog isa} (htc : fnsCall c fns ts = true) (s₁ s₂ : State)
    (hp : (sig.contract ((A.withFns fns).withTables sig ts) pre post wa stack leak).pub s₁ s₂) :
    ∀ n ∈ inames c, isa.fnAddr s₁ n = isa.fnAddr s₂ n := by
  intro n hn
  have hp' := contract_pub hp
  simp only [fnsCall, List.all_eq_true, decide_eq_true_eq] at htc
  rcases htc n hn with h | h
  · exact fns_pub_syms (withTables_pub hp') n h
  · exact tables_pub_syms hp' n h

/-- `verifiedScrubbedAll` under a calling convention with functions of public
address: code whose frames use at most the `stack` bytes its contract
reserves, a frame size of the model, and that calls indirectly only the
functions `fns` and those of its tables, with its cleanup (`scrubAll`) meets
its contract in constant time and returns without secret residue, if its
postcondition reads the memory on return only within the buffers. -/
theorem verifiedScrubbedAllFns {A : Abi isa} (hA : ScrubAbi A) {fns : List String} {sig : Sig}
    {ts : List (String × List FnTable)}
    {pre : Curry (sig.words ((A.withFns fns).withTables sig ts).ptrBits) (Mem → Prop)}
    {post : sig.Post ((A.withFns fns).withTables sig ts).ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words ((A.withFns fns).withTables sig ts).ptrBits) (Mem → List Nat))}
    {c : Prog isa} {rb : Nat}
    (hv : Verified target c (sig.contract ((A.withFns fns).withTables sig ts) pre post wa stack leak))
    (hpost : PostOut (sig.contract ((A.withFns fns).withTables sig ts) pre post wa stack leak) rb)
    (hd : armStack c ≤ stack) (hn : FrameOk stack) (hc : fnsCall c fns ts = true)
    (e : rb = sig.retBits ((A.withFns fns).withTables sig ts).ptrBits) :
    VerifiedScrubbed target (scrubAll rb stack c)
      (sig.contract ((A.withFns fns).withTables sig ts) pre post wa stack leak) rb := by
  obtain ⟨h₁, h₂⟩ := Verified.scrubAllS ((hA.withFns fns).tables sig ts) hv hd (fnsCall_pub hc) hn e hpost
  exact ⟨h₁, h₂, fun ty _ h => by cases ty <;> cases h⟩

/-- Code without indirect calls, made to call `n` by its address in a
register, calls indirectly only `n`. -/
theorem inames_viaRegAt {n : String} {r : Reg} {c : Prog isa} (hc : VG.Proof.Arm.Code.icallFree c = true) :
    ∀ m ∈ inames (Impl.Arm.Code.viaRegAt n r c), m = n := by
  induction c with
  | block is => intro m hm; cases hm
  | seq a b iha ihb | ite _ a b iha ihb =>
    simp only [VG.Proof.Arm.Code.icallFree, Bool.and_eq_true] at hc
    intro m hm
    simp only [Impl.Arm.Code.viaRegAt, inames, List.mem_append] at hm
    exact hm.elim (iha hc.1 m) (ihb hc.2 m)
  | loop b _ ih | frame _ b _ ih => exact ih hc
  | call m' b ih =>
    intro m hm
    simp only [Impl.Arm.Code.viaRegAt] at hm
    split at hm
    · simp only [Impl.Arm.callReg, Code.icalls, inames, List.append_nil, List.mem_cons] at hm
      exact hm.elim id (ih hc m)
    · exact ih hc m hm
  | icall _ _ _ _ _ _ => simp only [VG.Proof.Arm.Code.icallFree, Bool.false_eq_true] at hc

end VG.Arm.Scrub
