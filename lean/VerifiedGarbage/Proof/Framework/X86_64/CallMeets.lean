module

public import VerifiedGarbage.Proof.Framework.X86_64.CallIndirect
public import VerifiedGarbage.Proof.Framework.X86_64.Funs
public import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.TCB.X86_64.Target

/-!
# Calling a function that a contract's `FnMeets` describes (x86-64)

A contract with `fns` (`Sig.contract`) states `FnMeets` of the functions its
arguments point to, in the state on entry `s₀`. The function calls one
indirectly (`Code.icall`) later, from a state `s` of its run, which keeps
what `World` says of `s₀`: the same functions at every address and the same
statics, and the memory outside the writable regions and the stack of `s₀`.
`WP.icallMeets` runs the call from the function's `FnMeets`: given the
regions `rd` and `wr` it passes the function, within its own (`Abi.within`),
and that the function's contract holds of the state it enters with those
regions and the tables of constants it reads (whatever they are, as
`FnMeets` leaves them), the call returns in a state satisfying the
contract's postcondition, which keeps `World`. `RelCT.icallMeets` is its
constant time, from `FnMeets`'s.
-/

@[expose] public section

namespace VG.X86_64

/-- What the state `s` of a run from the entry `s₀` keeps, for a function
whose calls and frames use `stack` bytes of stack: the functions at every
address, the addresses of the statics, and every byte outside the writable
regions and the stack of `s₀`. -/
structure World (stack : Nat) (s₀ s : State) : Prop where
  funs : s.funs = s₀.funs
  syms : s.syms = s₀.syms
  mem : ∀ x, (∀ r ∈ s₀.wr ++ abi.reserved stack s₀, ¬ r.Contains x 1) → s.mem x = s₀.mem x

theorem World.refl (stack : Nat) (s₀ : State) : World stack s₀ s₀ := ⟨rfl, rfl, fun _ _ => rfl⟩

/-- Each byte of the regions `ws` is in a writable region or the stack of `s₀`. -/
def Owned (stack : Nat) (s₀ : State) (ws : List Region) : Prop :=
  ∀ r ∈ ws, ∀ x, r.Contains x 1 → InRegions (s₀.wr ++ abi.reserved stack s₀) x 1

theorem Owned.sub {stack : Nat} {e : State} {r r' : Region} (h : Owned stack e [r']) (hs : Region.Sub r r') :
    Owned stack e [r] := fun q hq x hx => by
  rw [List.mem_singleton] at hq; subst hq
  exact h _ (List.mem_singleton_self _) x (hs x hx)

theorem Owned.pair {stack : Nat} {e : State} {r r' : Region} (h : Owned stack e [r]) (h' : Owned stack e [r']) :
    Owned stack e [r, r'] := fun q hq => by
  rcases List.mem_cons.mp hq with rfl | hq
  · exact h _ (List.mem_singleton_self _)
  · exact h' q hq

theorem Owned.cons {stack : Nat} {e : State} {r : Region} {rs : List Region} (h : Owned stack e [r])
    (h' : Owned stack e rs) : Owned stack e (r :: rs) := fun q hq => by
  rcases List.mem_cons.mp hq with rfl | hq
  · exact h _ (List.mem_singleton_self _)
  · exact h' q hq

/-- Regions each within one of the regions `ws` of `s₀`'s own. -/
theorem Owned.of_sub {stack : Nat} {e : State} {ws ws' : List Region} (h : Owned stack e ws)
    (hs : ∀ r ∈ ws', ∃ r' ∈ ws, Region.Sub r r') : Owned stack e ws' := fun r hr x hx => by
  obtain ⟨r', hr', hsub⟩ := hs r hr
  exact h r' hr' x (hsub x hx)

/-- After code that keeps the functions and statics and changes memory only
within regions of `s₀`'s own. -/
theorem World.step {stack : Nat} {s₀ s s' : State} (h : World stack s₀ s) (hf : s'.funs = s.funs)
    (hs : s'.syms = s.syms) {ws : List Region} (hF : Frame ws s.mem s'.mem) (hws : Owned stack s₀ ws) :
    World stack s₀ s' :=
  ⟨hf.trans h.funs, hs.trans h.syms, fun x hx => by
    rw [hF x fun r hr hc => by obtain ⟨r', hr', hc'⟩ := hws r hr x hc; exact hx r' hr' hc', h.mem x hx]⟩

theorem disjoint_of_covered {t r : Region} {L : List Region} (hL : ∀ R ∈ L, t.Disjoint R)
    (hr : ∀ x, r.Contains x 1 → InRegions L x 1) : t.Disjoint r := fun x ht hrx => by
  obtain ⟨R, hR, hc⟩ := hr x hrx
  exact hL R hR x ht hc

/-- A table of constants, held in `m`, is held in a memory that agrees with
`m` on its bytes. -/
theorem constsHeld_congr {m m' : Mem} {f : String → BitVec 64} {cs : List (String × List (BitVec 64))}
    (h : Abi.constsHeld m f cs)
    (hb : ∀ t ∈ Abi.constRegions f cs, t.base.toNat + t.len ≤ 2 ^ 64)
    (he : ∀ t ∈ Abi.constRegions f cs, ∀ x, t.Contains x 1 → m' x = m x) : Abi.constsHeld m' f cs := by
  intro c hc i hi
  rw [← h c hc i hi]
  have hm : (⟨f c.1, 8 * c.2.length⟩ : Region) ∈ Abi.constRegions f cs := List.mem_map.mpr ⟨c, hc, rfl⟩
  have hl := hb _ hm
  refine Mem.readW_congr fun j hj => he _ hm _ ?_
  simp only [Region.Contains]
  rw [show f c.1 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - f c.1 = BitVec.ofNat 64 (8 * i + j) by
    rw [BitVec.add_assoc, Offset.add_sub_cancel_left, BitVec.ofNat_add]]
  simp only [BitVec.toNat_ofNat]
  simp only at hl
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- The stack a function called from `s` with `n` bytes of stack may use,
its return address included, is the `n + 8` bytes below `rsp`. -/
theorem reserved_callEntry_sub {s : State} {n : Nat} (hn : n + 8 < 2 ^ 64) :
    ∀ r ∈ abi.reserved n s.callEntry, ∀ x, r.Contains x 1 → (below (s.gpr .rsp) (n + 8)).Contains x 1 := by
  intro r hr x hx
  simp only [abi, State.callEntry_rsp, List.mem_cons] at hr
  rcases hr with rfl | hr
  · have := below_call (s.gpr .rsp) (n := n + 8) (by omega) hn
    simp only [Region.Contains] at this hx ⊢
    have e : x - (s.gpr .rsp - BitVec.ofNat 64 (n + 8)) = (x - (s.gpr .rsp - 8)) + BitVec.ofNat 64 n := by
      rw [← Offset.sub_add_sub_cancel x (s.gpr .rsp - 8),
        show s.gpr .rsp - 8 - (s.gpr .rsp - BitVec.ofNat 64 (n + 8)) = BitVec.ofNat 64 (n + 8 - 8) from
          Offset.sub_ofNat_sub_sub_ofNat (s.gpr .rsp) (a := 8) (by omega), Nat.add_sub_cancel]
    rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := n) (by omega)]
    omega
  · cases n with
    | zero => simp [stackBelow] at hr
    | succ n =>
      simp only [stackBelow, List.mem_singleton] at hr
      subst hr
      exact below_callee (s.gpr .rsp) (n + 1) x hx

/-- The state an indirect call from `s` enters, with the regions `rd`, the
tables of constants `cs` where the statics are, and `wr`. -/
abbrev narrowed (s : State) (rd wr : List Region) (cs : List (String × List (BitVec 64))) : State :=
  s.callEntry.withRegions (rd ++ Abi.constRegions s.syms cs) wr

/-- What a call from `s`, in a run from the entry `e` with `stack` bytes of
stack, of a function using `n` bytes of stack, passes it: the regions `rd`
and `wr`, of `e`'s own (`wr` of what `s` may write), and the stack below
`rsp` the call uses, of `e`'s. -/
structure Passes (stack n : Nat) (e s : State) (rd wr : List Region) : Prop where
  hw : Covers wr s.wr
  hn : n + 8 < 2 ^ 64
  rd : ∀ r ∈ rd, ∀ x, r.Contains x 1 → InRegions (e.rd ++ e.wr ++ abi.reserved stack e) x 1
  wr : Owned stack e wr
  stk : Owned stack e [below (s.gpr .rsp) (n + 8)]

/-- The tables of constants of the function at `a`, as `FnMeets` holds them
in the entry `e`, from a state `s` keeping `World` of it: in memory, and
apart from what the call passes or uses. -/
theorem consts_ok {K : Abi isa → Nat → Contract isa} {n stack : Nat} {e s : State} {a : Addr}
    (hm : FnMeets abi K n stack e a) (hW : World stack e s) {rd wr : List Region}
    (hp : Passes stack n e s rd wr) :
    Abi.constsHeld s.mem s.syms (fnConsts e a) ∧
      ∀ t ∈ Abi.constRegions s.syms (fnConsts e a), t.base.toNat + t.len ≤ 2 ^ 64 ∧
        (∀ r ∈ wr, t.Disjoint r) ∧ ∀ r ∈ abi.reserved n s.callEntry, t.Disjoint r := by
  obtain ⟨f, cs, -, hc, hcs, -, -⟩ := hm
  subst hc
  simp only [abi] at hcs
  obtain ⟨held, hregs⟩ := hcs
  rw [← hW.syms] at held hregs
  have hdis : ∀ t ∈ Abi.constRegions s.syms (fnConsts e a), ∀ r, (∀ x, r.Contains x 1 →
      InRegions (e.wr ++ abi.reserved stack e) x 1) → t.Disjoint r := fun t ht r hr =>
    disjoint_of_covered (L := e.wr ++ abi.reserved stack e) (fun R hR => by
      rcases List.mem_append.mp hR with hR | hR
      · exact (hregs t ht).2.1 R hR
      · exact (hregs t ht).2.2 R hR) hr
  refine ⟨constsHeld_congr held (fun t ht => (hregs t ht).1) fun t ht x hx => hW.mem x fun r hr hc => ?_,
    fun t ht => ⟨(hregs t ht).1, fun r hr => hdis t ht r (hp.wr r hr),
      fun r hr => hdis t ht r fun x hx => hp.stk _ (List.mem_singleton_self _) x
        (reserved_callEntry_sub hp.hn r hr x hx)⟩⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact (hregs t ht).2.1 r hr x hx hc
  · exact (hregs t ht).2.2 r hr x hx hc

/-- The state a call passes its function is of `e`'s program. -/
theorem narrowed_sameWorld {stack : Nat} {e s : State} (hW : World stack e s) (rd wr : List Region)
    (cs : List (String × List (BitVec 64))) : abi.sameWorld (narrowed s rd wr cs) e := by
  refine ⟨?_, ?_, ?_⟩
  · show fnAt (narrowed s rd wr cs) = fnAt e
    funext a; simp only [fnAt, show (narrowed s rd wr cs).funs = e.funs from hW.funs]
  · show fnConsts (narrowed s rd wr cs) = fnConsts e
    funext a; simp only [fnConsts, show (narrowed s rd wr cs).funs = e.funs from hW.funs]
  · show (fun name => (narrowed s rd wr cs).syms name) = fun name => e.syms name
    funext name
    exact congrFun hW.syms name

/-- The regions a call passes its function are within `e`'s. -/
theorem narrowed_within {stack n : Nat} {e s : State} (hW : World stack e s) {rd wr : List Region}
    (hp : Passes stack n e s rd wr) (cs : List (String × List (BitVec 64))) :
    abi.within stack e cs (narrowed s rd wr cs) := by
  show ∀ r ∈ (narrowed s rd wr cs).rd ++ (narrowed s rd wr cs).wr, ∀ x, r.Contains x 1 →
    InRegions (e.rd ++ e.wr ++ abi.reserved stack e ++ Abi.constRegions e.syms cs) x 1
  intro r hr x hx
  simp only [show (narrowed s rd wr cs).rd = rd ++ Abi.constRegions s.syms cs from rfl,
    show (narrowed s rd wr cs).wr = wr from rfl, List.mem_append] at hr
  rcases hr with (hr | hr) | hr
  · obtain ⟨R, hR, hc⟩ := hp.rd r hr x hx
    exact ⟨R, List.mem_append_left _ hR, hc⟩
  · rw [hW.syms] at hr
    exact ⟨r, List.mem_append_right _ hr, hx⟩
  · obtain ⟨R, hR, hc⟩ := hp.wr r hr x hx
    rcases List.mem_append.mp hR with hR | hR
    · exact ⟨R, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hR)), hc⟩
    · exact ⟨R, List.mem_append_left _ (List.mem_append_right _ hR), hc⟩

theorem fnAt_world {stack : Nat} {e s : State} (hW : World stack e s) : fnAt s = fnAt e := by
  funext a; simp only [fnAt, hW.funs]

/-- A call, of the function at the address in `r11`, which meets `K` with
`n` bytes of stack as `FnMeets` says of it in the entry state `e`, from a
state `s` keeping `World` of it, passing it the regions `rd` and `wr`
(`Passes`). If `K` holds of the state it enters with those regions and the
tables of constants the function reads where the statics are (`hpre`, of
those tables in memory and apart from what the call passes or uses), the
call returns in a state that keeps `World`, the regions, the callee-saved
registers and memory outside `wr` and the `n + 8` bytes below `rsp`, and
whose memory and registers (`rsp` aside) are those of a state satisfying
`K`'s postcondition. -/
theorem WP.icallMeets {K : Abi isa → Nat → Contract isa} {n stack : Nat} {e s : State}
    (hm : FnMeets abi K n stack e (s.gpr .r11)) (hW : World stack e s) {rd wr : List Region}
    (hp : Passes stack n e s rd wr)
    (hpre : let cs := fnConsts e (s.gpr .r11); Abi.constsHeld s.mem s.syms cs →
      (∀ t ∈ Abi.constRegions s.syms cs, t.base.toNat + t.len ≤ 2 ^ 64 ∧ (∀ r ∈ wr, t.Disjoint r) ∧
        ∀ r ∈ abi.reserved n s.callEntry, t.Disjoint r) →
      (K (abi.withConsts cs) n).pre (narrowed s rd wr cs))
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .rsp) (n + 8)]) s.mem s'.mem → World stack e s' →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        (K (abi.withConsts (fnConsts e (s.gpr .r11))) n).post
          (narrowed s rd wr (fnConsts e (s.gpr .r11))) s₂) →
      Q s') :
    WP isa (.icall n) s Q := by
  obtain ⟨held, hregs⟩ := consts_ok hm hW hp
  have hpr := hpre held hregs
  obtain ⟨f, cs, hfa, hc, -, hrun, -⟩ := hm
  subst hc
  have hfs : fnAt s (s.gpr .r11) = some f := by rw [fnAt_world hW]; exact hfa
  obtain ⟨s₂, t, hf₂, hok, hpost⟩ :=
    hrun _ (narrowed_sameWorld hW rd wr _) (narrowed_within hW hp _) hpr
  refine WP.of_funs (WP.of_syms (WP.icall (rd := rd ++ Abi.constRegions s.syms _) (wr := wr)
    (P := fun s₁ s₂ => (K (abi.withConsts (fnConsts e (s.gpr .r11))) n).post s₁ s₂) hfs
    ⟨s₂, t, hf₂, hok, hpost⟩ hp.hw hp.hn fun s' hrd' hwr' hcs' hF hex hsy hfu => ?_))
  refine hQ s' hrd' hwr' hcs' hF (hW.step hfu hsy hF fun r hr => ?_) hex
  rcases List.mem_append.mp hr with hr | hr
  · exact hp.wr r hr
  · exact hp.stk r hr

/-- `Abi.within` depends on the entry only through its regions, stack
pointer and statics. -/
theorem within_congr {stack : Nat} {e e' s : State} {cs : List (String × List (BitVec 64))}
    (hrd : e'.rd = e.rd) (hwr : e'.wr = e.wr) (hsp : e'.gpr .rsp = e.gpr .rsp) (hsy : e'.syms = e.syms)
    (h : abi.within stack e' cs s) : abi.within stack e cs s := by
  intro r hr x hx
  have := h r hr x hx
  simp only [abi, Option.elim] at this ⊢
  rw [hrd, hwr, hsy, hsp] at this
  exact this

/-- What two runs of a call of the function at the address in `r11`, from
the states `s₁` and `s₂`, keep of their entries `e₁` and `e₂`: the
function meets `K` as `FnMeets` says in both, the entries are of the same
program and have the same regions and stack pointer, the states keep
`World` of them, and call the same address from the same `rsp`. -/
structure TwoRuns (K : Abi isa → Nat → Contract isa) (n stack : Nat) (e₁ e₂ s₁ s₂ : State) : Prop where
  m₁ : FnMeets abi K n stack e₁ (s₁.gpr .r11)
  m₂ : FnMeets abi K n stack e₂ (s₂.gpr .r11)
  w₁ : World stack e₁ s₁
  w₂ : World stack e₂ s₂
  same : abi.sameWorld e₂ e₁
  rd : e₂.rd = e₁.rd
  wr : e₂.wr = e₁.wr
  sp : e₂.gpr .rsp = e₁.gpr .rsp
  r11 : s₂.gpr .r11 = s₁.gpr .r11
  rsp : s₂.gpr .rsp = s₁.gpr .rsp

/-- Two runs of an indirect call leak the same trace when they call the
same function from the same `rsp`, as `TwoRuns` says, each passes it
regions of its entry's own (`Passes`), and `K`'s precondition holds in both
of the states the function enters, which agree on `K`'s public data (`hK`,
of the tables of constants the function reads, in memory in both and apart
from what each call passes or uses). -/
theorem RelCT.icallMeets {K : Abi isa → Nat → Contract isa} {n stack : Nat} {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → ∃ (e₁ e₂ : State) (rd₁ wr₁ rd₂ wr₂ : List Region),
      TwoRuns K n stack e₁ e₂ s₁ s₂ ∧ Passes stack n e₁ s₁ rd₁ wr₁ ∧ Passes stack n e₂ s₂ rd₂ wr₂ ∧
      (let cs := fnConsts e₁ (s₁.gpr .r11);
        Abi.constsHeld s₁.mem s₁.syms cs → Abi.constsHeld s₂.mem s₂.syms cs →
        (∀ t ∈ Abi.constRegions s₁.syms cs, t.base.toNat + t.len ≤ 2 ^ 64 ∧
          (∀ r ∈ wr₁, t.Disjoint r) ∧ ∀ r ∈ abi.reserved n s₁.callEntry, t.Disjoint r) →
        (∀ t ∈ Abi.constRegions s₂.syms cs, t.base.toNat + t.len ≤ 2 ^ 64 ∧
          (∀ r ∈ wr₂, t.Disjoint r) ∧ ∀ r ∈ abi.reserved n s₂.callEntry, t.Disjoint r) →
        (K (abi.withConsts cs) n).pre (narrowed s₁ rd₁ wr₁ cs) ∧
          (K (abi.withConsts cs) n).pre (narrowed s₂ rd₂ wr₂ cs) ∧
          (K (abi.withConsts cs) n).pub (narrowed s₁ rd₁ wr₁ cs) (narrowed s₂ rd₂ wr₂ cs))) :
    RelCT isa P (.icall n) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hPs ex₁ ex₂
  obtain ⟨e₁, e₂, rd₁, wr₁, rd₂, wr₂, ⟨hm₁, hm₂, hW₁, hW₂, hsw, hrd, hwr, hsp, h11, hrsp⟩, hp₁, hp₂, hK⟩ :=
    hP _ _ hPs
  have hcs : fnConsts e₂ (s₂.gpr .r11) = fnConsts e₁ (s₁.gpr .r11) := by
    rw [h11]; exact congrFun (show fnConsts e₂ = fnConsts e₁ from hsw.2.1) _
  obtain ⟨held₁, hregs₁⟩ := consts_ok hm₁ hW₁ hp₁
  obtain ⟨held₂, hregs₂⟩ := consts_ok hm₂ hW₂ hp₂
  rw [hcs] at held₂ hregs₂
  obtain ⟨pre₁, pre₂, hpub⟩ := hK held₁ held₂ hregs₁ hregs₂
  obtain ⟨f, cs, hfa, hc, -, hrun, hct⟩ := hm₁
  subst hc
  replace hfa : fnAt e₁ (s₁.gpr .r11) = some f := hfa
  have hsy : e₂.syms = e₁.syms := by
    have := hsw.2.2; simp only [abi, Option.elim] at this; exact funext fun x => congrFun this x
  -- The function each run calls, from the state its call instruction leaves.
  cases ex₁ with
  | icall hf₁ hc₁ hr₁ hk₁ hq₁ =>
  cases ex₂ with
  | icall hf₂ hc₂ hr₂ hk₂ hq₂ =>
  rw [call_callEntry, Option.some.injEq] at hc₁ hc₂
  subst hc₁ hc₂
  simp only [isa] at hf₁ hf₂
  rw [fnAt_world hW₁, hfa, Option.some.injEq] at hf₁
  rw [fnAt_world hW₂, h11, ← fnAt_world hW₂, fnAt_world hW₂,
    show fnAt e₂ = fnAt e₁ from hsw.1, hfa, Option.some.injEq] at hf₂
  subst hf₁ hf₂
  -- Their runs from the states narrowed to what the calls pass.
  have w₁ := narrowed_within hW₁ hp₁ (fnConsts e₁ (s₁.gpr .r11))
  have w₂ : abi.within stack e₁ (fnConsts e₁ (s₁.gpr .r11)) (narrowed s₂ rd₂ wr₂ _) :=
    within_congr hrd hwr hsp hsy (narrowed_within hW₂ hp₂ _)
  have sw₂ : abi.sameWorld (narrowed s₂ rd₂ wr₂ (fnConsts e₁ (s₁.gpr .r11))) e₁ := by
    obtain ⟨a, b, c⟩ := narrowed_sameWorld hW₂ rd₂ wr₂ (fnConsts e₁ (s₁.gpr .r11))
    exact ⟨a.trans hsw.1, b.trans hsw.2.1, c.trans hsw.2.2⟩
  obtain ⟨u₁, v₁, hu₁, -, -⟩ := hrun _ (narrowed_sameWorld hW₁ rd₁ wr₁ _) w₁ pre₁
  obtain ⟨u₂, v₂, hu₂, -, -⟩ := hrun _ sw₂ w₂ pre₂
  have hv := hct _ _ _ _ _ _ (narrowed_sameWorld hW₁ rd₁ wr₁ _) sw₂ w₁ w₂ pre₁ pre₂ hpub hu₁ hu₂
  -- The actual runs are those, with more permissions.
  have hfs₁ : fnAt s₁ (s₁.gpr .r11) = some f := by rw [fnAt_world hW₁]; exact hfa
  obtain ⟨-, -, hw₁⟩ := regionModel.fn_widen hfs₁ hu₁
  have e₁' := hw₁ s₁.rd s₁.wr
  rw [show regionModel.withRegions (narrowed s₁ rd₁ wr₁ _) s₁.rd s₁.wr = s₁.callEntry from rfl] at e₁'
  have hfs₂ : fnAt s₂ (s₂.gpr .r11) = some f := by
    rw [fnAt_world hW₂, h11, show fnAt e₂ = fnAt e₁ from hsw.1]; exact hfa
  obtain ⟨-, -, hw₂⟩ := regionModel.fn_widen hfs₂ hu₂
  have e₂' := hw₂ s₂.rd s₂.wr
  rw [show regionModel.withRegions (narrowed s₂ rd₂ wr₂ _) s₂.rd s₂.wr = s₂.callEntry from rfl] at e₂'
  rw [hr₁, Option.some.injEq, Prod.mk.injEq] at e₁'
  rw [hr₂, Option.some.injEq, Prod.mk.injEq] at e₂'
  obtain ⟨-, rfl⟩ := e₁'
  obtain ⟨-, rfl⟩ := e₂'
  -- The call and return addresses agree with `rsp`, which the functions keep.
  have r₁ := ret_rsp hq₁
  have r₂ := ret_rsp hq₂
  simp only [State.callEntry_rsp] at r₁ r₂
  refine ⟨?_, trivial⟩
  simp only [r₁, r₂, hrsp, h11, hv]

end VG.X86_64
