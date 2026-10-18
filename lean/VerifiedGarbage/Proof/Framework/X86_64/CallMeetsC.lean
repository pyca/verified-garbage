module

public import VerifiedGarbage.Proof.Framework.X86_64.CallMeets
public import VerifiedGarbage.Proof.Framework.X86_64.WithConsts

/-!
# Calling a function that `FnMeets` describes, from a caller with tables (x86-64)

A function that reads tables of constants `cs₀` (`Artifact.consts`) has its
contract under `abi.withConsts cs₀`, and so does the `FnMeets` its contract
states of the functions its arguments point to: such a function, reading
tables `cs` of its own, meets its contract under
`(abi.withConsts cs₀).withConsts cs`, which is `abi.withConsts (cs ++ cs₀)`
(`withConsts_withConsts`): its entry has both its tables and the caller's
after the regions it is passed, and both held in memory. `wp_icall` and
`relCT_icall` are `WP.icallMeets` and `RelCT.icallMeets` for such a caller:
the call passes the function the caller's tables too, which its entry `e`
holds apart from its writable regions and stack (`ConstsAt`), and the
regions it passes are within `e`'s own but for those tables (`PassesC`).
With `cs₀ = []` they are the plain ones (`passesC_nil`, `constsAt_nil`).

That a function verified under `abi.withConsts cs` meets `FnMeets` under
`abi.withConsts cs₀` is not proven here: its run, from an entry that also
lets it read the caller's tables, is the run from the entry without them.
-/

@[expose] public section

namespace VG.X86_64.CallC

/-- The tables `cs` at the statics of the entry `e`: held in its memory, not
wrapping around, and apart from its writable regions and the `stack` bytes
of stack its calls and frames use. -/
def ConstsAt (stack : Nat) (e : State) (cs : List (String × List (BitVec 64))) : Prop :=
  Abi.constsHeld e.mem e.syms cs ∧ ∀ t ∈ Abi.constRegions e.syms cs, t.base.toNat + t.len ≤ 2 ^ 64 ∧
    (∀ r ∈ e.wr, t.Disjoint r) ∧ ∀ r ∈ abi.reserved stack e, t.Disjoint r

theorem constsAt_nil (stack : Nat) (e : State) : ConstsAt stack e [] :=
  ⟨fun _ h => by simp at h, fun _ h => by simp [Abi.constRegions] at h⟩

theorem constRegions_append (f : String → BitVec 64) (cs cs' : List (String × List (BitVec 64))) :
    Abi.constRegions f (cs ++ cs') = Abi.constRegions f cs ++ Abi.constRegions f cs' := List.map_append

theorem constsHeld_append {m : Mem} {f : String → BitVec 64} {cs cs' : List (String × List (BitVec 64))} :
    Abi.constsHeld m f (cs ++ cs') ↔ Abi.constsHeld m f cs ∧ Abi.constsHeld m f cs' := by
  simp only [Abi.constsHeld, List.mem_append]
  exact ⟨fun h => ⟨fun c hc => h c (.inl hc), fun c hc => h c (.inr hc)⟩,
    fun h c hc => hc.elim (h.1 c) (h.2 c)⟩

/-- `L` ends with `S` exactly when it is something followed by `S`. -/
theorem drop_eq_iff {α : Type} {L S : List α} : L.drop (L.length - S.length) = S ↔ ∃ P, L = P ++ S := by
  constructor
  · intro h; exact ⟨_, (List.take_append_drop _ L).symm.trans (congrArg _ h)⟩
  · rintro ⟨P, rfl⟩; rw [List.length_append, Nat.add_sub_cancel, List.drop_left]

theorem withConsts_nil : abi.withConsts [] = abi := rfl

theorem withConsts_rd (cs₀ : List (String × List (BitVec 64))) (s : State) :
    (abi.withConsts cs₀).rd s = s.rd.take (s.rd.length - cs₀.length) := by
  cases cs₀ with
  | nil => show s.rd = s.rd.take (s.rd.length - 0); simp
  | cons c cs => rfl

theorem withConsts_wr' (cs₀ : List (String × List (BitVec 64))) : (abi.withConsts cs₀).wr = abi.wr := by
  cases cs₀ <;> rfl

theorem withConsts_reserved' (cs₀ : List (String × List (BitVec 64))) :
    (abi.withConsts cs₀).reserved = abi.reserved := by
  cases cs₀ <;> rfl

theorem withConsts_sym (cs₀ : List (String × List (BitVec 64))) : (abi.withConsts cs₀).sym = abi.sym := by
  cases cs₀ <;> rfl

theorem withConsts_sameWorld (cs₀ : List (String × List (BitVec 64))) :
    (abi.withConsts cs₀).sameWorld = abi.sameWorld := by
  cases cs₀ <;> rfl

/-- `L` ends with `R₀`, and before it with `R`, exactly when it ends with `R ++ R₀`. -/
theorem drop_two {α : Type} {L R R₀ : List α} {a b n : Nat} (ha : R.length = a) (hb : R₀.length = b)
    (hn : n = a + b) :
    (L.drop (L.length - b) = R₀ ∧ (L.take (L.length - b)).drop ((L.take (L.length - b)).length - a) = R) ↔
      L.drop (L.length - n) = R ++ R₀ := by
  subst ha hb hn
  rw [← List.length_append]
  constructor
  · rintro ⟨h₁, h₂⟩
    obtain ⟨Q, hQ⟩ := drop_eq_iff.mp h₁
    have hq : L.take (L.length - R₀.length) = Q := by
      rw [hQ, List.length_append, Nat.add_sub_cancel, List.take_left]
    rw [hq] at h₂
    obtain ⟨P, hP⟩ := drop_eq_iff.mp h₂
    exact drop_eq_iff.mpr ⟨P, by rw [hQ, hP, List.append_assoc]⟩
  · intro h
    obtain ⟨P, hP⟩ := drop_eq_iff.mp h
    have hq : L.take (L.length - R₀.length) = P ++ R := by
      rw [hP, ← List.append_assoc, List.length_append, Nat.add_sub_cancel, List.take_left]
    refine ⟨drop_eq_iff.mpr ⟨P ++ R, by rw [hP, List.append_assoc]⟩, ?_⟩
    rw [hq]
    exact drop_eq_iff.mpr ⟨P, rfl⟩

/-- The tables `cs` of a function that the caller's contract, under
`abi.withConsts cs₀`, describes: `abi.withConsts (cs ++ cs₀)`. -/
theorem withConsts_withConsts (cs₀ cs : List (String × List (BitVec 64))) :
    (abi.withConsts cs₀).withConsts cs = abi.withConsts (cs ++ cs₀) := by
  cases cs₀ with
  | nil => rw [withConsts_nil, List.append_nil]
  | cons c₀ cs₀ =>
  cases cs with
  | nil => rfl
  | cons c cs =>
  unfold Abi.withConsts
  simp only [abi]
  congr 1
  · funext ws n s
    apply propext
    have h₂ := drop_two (L := s.rd) (R := Abi.constRegions s.syms (c :: cs))
      (R₀ := Abi.constRegions s.syms (c₀ :: cs₀)) (WithConsts.constRegions_length _ _) (WithConsts.constRegions_length _ _)
      (List.length_append (as := c :: cs) (bs := c₀ :: cs₀))
    constructor
    · rintro ⟨⟨hwf, hd₀, hh₀, hr₀⟩, hd, hh, hr⟩
      refine ⟨hwf, ?_, constsHeld_append.mpr ⟨hh, hh₀⟩, fun t ht => ?_⟩
      · rw [constRegions_append]; exact h₂.mp ⟨hd₀, hd⟩
      · rw [constRegions_append, List.mem_append] at ht
        exact ht.elim (hr t) (hr₀ t)
    · rintro ⟨hwf, hd, hh, hr⟩
      rw [constRegions_append] at hd
      obtain ⟨hd₀, hd'⟩ := h₂.mpr hd
      obtain ⟨hh', hh₀⟩ := constsHeld_append.mp hh
      exact ⟨⟨hwf, hd₀, hh₀, fun t ht => hr t (by rw [constRegions_append]; exact List.mem_append_right _ ht)⟩,
        hd', hh', fun t ht => hr t (by rw [constRegions_append]; exact List.mem_append_left _ ht)⟩
  · funext s₁ s₂
    apply propext
    simp only [List.mem_append]
    exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, fun x hx => hx.elim (c x) (b x)⟩,
      fun ⟨a, d⟩ => ⟨⟨a, fun x hx => d x (.inr hx)⟩, fun x hx => d x (.inl hx)⟩⟩
  · funext s
    rw [List.take_take, List.length_take, List.length_append]
    congr 1; omega

/-! ## Contracts under `abi.withConsts`, back to the plain ones -/

/-- The reverse of `WithConsts.withConsts_pre`: the precondition of a contract under
`abi.withConsts cs` is the plain contract's on the state without the tables'
regions, which end its readable ones (and whose facts the plain contract
leaves out). -/
theorem withConsts_pre_inv {sig : Sig} {pre : ∀ pb, Curry (sig.words pb) (Mem → Prop)}
    {post : ∀ pb, sig.Post pb} {wa : Bool} {n : Nat} {cs : List (String × List (BitVec 64))} {s : State}
    (h : (sig.contract (abi.withConsts cs) (pre (abi.withConsts cs).ptrBits) (post (abi.withConsts cs).ptrBits)
      wa n).pre s) :
    (sig.contract abi (pre abi.ptrBits) (post abi.ptrBits) wa n).pre
      (s.withRegions (s.rd.take (s.rd.length - cs.length)) s.wr) := by
  cases cs with
  | nil =>
    rw [show s.rd.length - ([] : List (String × List (BitVec 64))).length = s.rd.length from rfl,
      List.take_length, State.withRegions_self]
    exact h
  | cons c cs =>
    obtain ⟨vals, hv, hvw⟩ := WithConsts.abi_args ((sig.words 64).map (·.bits 64))
    simp only [Sig.contract, WithConsts.withConsts_args, VG.X86_64.WithConsts.withConsts_rd, VG.X86_64.WithConsts.withConsts_wf,
      VG.X86_64.WithConsts.withConsts_wr, WithConsts.withConsts_mem, VG.X86_64.WithConsts.withConsts_argArea, VG.X86_64.WithConsts.withConsts_reserved] at h ⊢
    rw [show abi.ptrBits = 64 from rfl]
    rw [show (abi.withConsts (c :: cs)).ptrBits = 64 from rfl] at h
    simp only [hv] at h ⊢
    simp only [hvw, WithConsts.wf_withRegions, WithConsts.argArea_withRegions, WithConsts.reserved_withRegions]
    obtain ⟨⟨hwf, -, -, -⟩, hr, hw, hp, hres, hb, hpre⟩ := h
    exact ⟨hwf, hr, hw, hp, hres, hb, hpre⟩

/-- The reverse of `WithConsts.withConsts_post`. -/
theorem withConsts_post_inv {sig : Sig} {pre : ∀ pb, Curry (sig.words pb) (Mem → Prop)}
    {post : ∀ pb, sig.Post pb} {wa : Bool} {n : Nat} {cs : List (String × List (BitVec 64))} {s s' : State}
    (h : (sig.contract abi (pre abi.ptrBits) (post abi.ptrBits) wa n).post s s') :
    (sig.contract (abi.withConsts cs) (pre (abi.withConsts cs).ptrBits) (post (abi.withConsts cs).ptrBits)
      wa n).post s s' := by
  cases cs with
  | nil => exact h
  | cons c cs => exact h

/-! ## A call -/

/-- What `FnMeets` under `abi.withConsts cs₀` says of the function at `a`:
its tables are at the statics of `e` (`ConstsAt`), and it meets `K` under
`abi.withConsts` of its tables and then the caller's. -/
theorem fnMeets_c {K : Abi isa → Nat → Contract isa} {n stack : Nat} {e : State} {a : Addr}
    {cs₀ : List (String × List (BitVec 64))} (h : FnMeets (abi.withConsts cs₀) K n stack e a) :
    ∃ f, fnAt e a = some f ∧ ConstsAt stack e (fnConsts e a) ∧
      (∀ s₁, abi.sameWorld s₁ e → (abi.withConsts cs₀).within stack e (fnConsts e a) s₁ →
        (K (abi.withConsts (fnConsts e a ++ cs₀)) n).pre s₁ →
        ∃ s₂ t, f s₁ = some (s₂, t) ∧ callOk n s₁ s₂ ∧ (K (abi.withConsts (fnConsts e a ++ cs₀)) n).post s₁ s₂) ∧
      ∀ s₁ s₂ t₁ t₂ s₁' s₂', abi.sameWorld s₁ e → abi.sameWorld s₂ e →
        (abi.withConsts cs₀).within stack e (fnConsts e a) s₁ →
        (abi.withConsts cs₀).within stack e (fnConsts e a) s₂ →
        (K (abi.withConsts (fnConsts e a ++ cs₀)) n).pre s₁ → (K (abi.withConsts (fnConsts e a ++ cs₀)) n).pre s₂ →
        (K (abi.withConsts (fnConsts e a ++ cs₀)) n).pub s₁ s₂ → f s₁ = some (s₁', t₁) → f s₂ = some (s₂', t₂) →
        t₁ = t₂ := by
  obtain ⟨f, cs, hf, hc, hcs, hr, ht⟩ := h
  subst hc
  rw [← withConsts_withConsts]
  rw [withConsts_sameWorld] at hr ht
  refine ⟨f, hf, ?_, hr, ht⟩
  cases cs₀ <;> exact hcs

/-- The tables of the entry `e`, at a call from a state `s` keeping `World`
of it: in memory, and apart from what the call writes (`wr`, of `e`'s own)
and the stack it uses. -/
theorem constsAt_call {stack n : Nat} {e s : State} {cs : List (String × List (BitVec 64))}
    (hc : ConstsAt stack e cs) (hW : World stack e s) {wr : List Region} (hwr : Owned stack e wr)
    (hstk : Owned stack e [below (s.gpr .rsp) (n + 8)]) (hn : n + 8 < 2 ^ 64) :
    Abi.constsHeld s.mem s.syms cs ∧
      ∀ t ∈ Abi.constRegions s.syms cs, t.base.toNat + t.len ≤ 2 ^ 64 ∧
        (∀ r ∈ wr, t.Disjoint r) ∧ ∀ r ∈ abi.reserved n s.callEntry, t.Disjoint r := by
  obtain ⟨held, hregs⟩ := hc
  rw [← hW.syms] at held hregs
  have hdis : ∀ t ∈ Abi.constRegions s.syms cs, ∀ r, (∀ x, r.Contains x 1 →
      InRegions (e.wr ++ abi.reserved stack e) x 1) → t.Disjoint r := fun t ht r hr =>
    disjoint_of_covered (L := e.wr ++ abi.reserved stack e) (fun R hR => by
      rcases List.mem_append.mp hR with hR | hR
      · exact (hregs t ht).2.1 R hR
      · exact (hregs t ht).2.2 R hR) hr
  refine ⟨constsHeld_congr held (fun t ht => (hregs t ht).1) fun t ht x hx => hW.mem x fun r hr hc => ?_,
    fun t ht => ⟨(hregs t ht).1, fun r hr => hdis t ht r (hwr r hr),
      fun r hr => hdis t ht r fun x hx => hstk _ (List.mem_singleton_self _) x
        (reserved_callEntry_sub hn r hr x hx)⟩⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact (hregs t ht).2.1 r hr x hx hc
  · exact (hregs t ht).2.2 r hr x hx hc

/-- What a call from `s`, in a run from the entry `e` of a function under
`abi.withConsts cs₀`, passes the function it calls: as `Passes`, with the
regions `rd` within `e`'s own but for the tables `cs₀`. -/
structure PassesC (cs₀ : List (String × List (BitVec 64))) (stack n : Nat) (e s : State)
    (rd wr : List Region) : Prop where
  hw : Covers wr s.wr
  hn : n + 8 < 2 ^ 64
  rd : ∀ r ∈ rd, ∀ x, r.Contains x 1 →
    InRegions (e.rd.take (e.rd.length - cs₀.length) ++ e.wr ++ abi.reserved stack e) x 1
  wr : Owned stack e wr
  stk : Owned stack e [below (s.gpr .rsp) (n + 8)]

theorem passesC_nil {stack n : Nat} {e s : State} {rd wr : List Region} (h : Passes stack n e s rd wr) :
    PassesC [] stack n e s rd wr :=
  ⟨h.hw, h.hn, fun r hr x hx => by simpa using h.rd r hr x hx, h.wr, h.stk⟩

/-- A call that reads only what the caller may write or its stack. -/
theorem passesC_of_owned {cs₀ : List (String × List (BitVec 64))} {stack n : Nat} {e s : State}
    {rd wr : List Region} (h : Passes stack n e s rd wr) (hrd : Owned stack e rd) :
    PassesC cs₀ stack n e s rd wr :=
  ⟨h.hw, h.hn, fun r hr x hx => by
    obtain ⟨R, hR, hc⟩ := hrd r hr x hx
    refine ⟨R, ?_, hc⟩
    rcases List.mem_append.mp hR with h | h
    · exact List.mem_append_left _ (List.mem_append_right _ h)
    · exact List.mem_append_right _ h, h.wr, h.stk⟩

theorem take_consts {X : List Region} {cs : List (String × List (BitVec 64))} {f : String → BitVec 64} :
    (X ++ Abi.constRegions f cs).take ((X ++ Abi.constRegions f cs).length - cs.length) = X := by
  rw [List.length_append, WithConsts.constRegions_length, Nat.add_sub_cancel, List.take_left]

/-- The regions a call passes its function, with its tables and then the
caller's, are within `e`'s, as `FnMeets` under `abi.withConsts cs₀` has it. -/
theorem narrowedC_within {cs₀ : List (String × List (BitVec 64))} {stack n : Nat} {e s : State}
    (hW : World stack e s) {rd wr : List Region} (hp : PassesC cs₀ stack n e s rd wr)
    (cs : List (String × List (BitVec 64))) :
    (abi.withConsts cs₀).within stack e cs (narrowed s rd wr (cs ++ cs₀)) := by
  unfold Abi.within
  rw [withConsts_rd, withConsts_rd, withConsts_wr', withConsts_reserved', withConsts_sym]
  show ∀ r ∈ (narrowed s rd wr (cs ++ cs₀)).rd.take ((narrowed s rd wr (cs ++ cs₀)).rd.length - cs₀.length) ++
      wr, ∀ x, r.Contains x 1 → InRegions (e.rd.take (e.rd.length - cs₀.length) ++ e.wr ++ abi.reserved stack e ++
        Abi.constRegions e.syms cs) x 1
  rw [show (narrowed s rd wr (cs ++ cs₀)).rd = (rd ++ Abi.constRegions s.syms cs) ++ Abi.constRegions s.syms cs₀
    by rw [List.append_assoc, ← constRegions_append]; rfl, take_consts]
  intro r hr x hx
  simp only [List.mem_append] at hr
  rcases hr with (hr | hr) | hr
  · obtain ⟨R, hR, hc⟩ := hp.rd r hr x hx
    exact ⟨R, List.mem_append_left _ hR, hc⟩
  · rw [hW.syms] at hr
    exact ⟨r, List.mem_append_right _ hr, hx⟩
  · obtain ⟨R, hR, hc⟩ := hp.wr r hr x hx
    rcases List.mem_append.mp hR with hR | hR
    · exact ⟨R, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hR)), hc⟩
    · exact ⟨R, List.mem_append_left _ (List.mem_append_right _ hR), hc⟩

/-- The facts of the tables of a call, its function's and then the caller's. -/
theorem consts_two {stack n : Nat} {e s : State} {cs cs₀ : List (String × List (BitVec 64))}
    (hc : ConstsAt stack e cs) (h₀ : ConstsAt stack e cs₀) (hW : World stack e s) {wr : List Region}
    (hwr : Owned stack e wr) (hstk : Owned stack e [below (s.gpr .rsp) (n + 8)]) (hn : n + 8 < 2 ^ 64) :
    Abi.constsHeld s.mem s.syms (cs ++ cs₀) ∧
      ∀ t ∈ Abi.constRegions s.syms (cs ++ cs₀), t.base.toNat + t.len ≤ 2 ^ 64 ∧
        (∀ r ∈ wr, t.Disjoint r) ∧ ∀ r ∈ abi.reserved n s.callEntry, t.Disjoint r := by
  obtain ⟨held, hregs⟩ := constsAt_call hc hW hwr hstk hn
  obtain ⟨held₀, hregs₀⟩ := constsAt_call h₀ hW hwr hstk hn
  refine ⟨constsHeld_append.mpr ⟨held, held₀⟩, fun t ht => ?_⟩
  rw [constRegions_append, List.mem_append] at ht
  exact ht.elim (hregs t) (hregs₀ t)

/-- `WP.icallMeets`, for a caller under `abi.withConsts cs₀`, whose entry
`e` holds its tables (`h₀`): the function enters with its tables and then
the caller's. -/
theorem wp_icall {K : Abi isa → Nat → Contract isa} {n stack : Nat} {e s : State}
    {cs₀ : List (String × List (BitVec 64))} (h₀ : ConstsAt stack e cs₀)
    (hm : FnMeets (abi.withConsts cs₀) K n stack e (s.gpr .r11)) (hW : World stack e s) {rd wr : List Region}
    (hp : PassesC cs₀ stack n e s rd wr)
    (hpre : let cs := fnConsts e (s.gpr .r11) ++ cs₀; Abi.constsHeld s.mem s.syms cs →
      (∀ t ∈ Abi.constRegions s.syms cs, t.base.toNat + t.len ≤ 2 ^ 64 ∧ (∀ r ∈ wr, t.Disjoint r) ∧
        ∀ r ∈ abi.reserved n s.callEntry, t.Disjoint r) →
      (K (abi.withConsts cs) n).pre (narrowed s rd wr cs))
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .rsp) (n + 8)]) s.mem s'.mem → World stack e s' →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        (K (abi.withConsts (fnConsts e (s.gpr .r11) ++ cs₀)) n).post
          (narrowed s rd wr (fnConsts e (s.gpr .r11) ++ cs₀)) s₂) →
      Q s') :
    WP isa (.icall n) s Q := by
  obtain ⟨f, hfa, hc, hrun, -⟩ := fnMeets_c hm
  obtain ⟨held, hregs⟩ := consts_two hc h₀ hW hp.wr hp.stk hp.hn
  have hpr := hpre held hregs
  have hfs : fnAt s (s.gpr .r11) = some f := by rw [fnAt_world hW]; exact hfa
  obtain ⟨s₂, t, hf₂, hok, hpost⟩ :=
    hrun _ (narrowed_sameWorld hW rd wr _) (narrowedC_within hW hp _) hpr
  refine WP.of_funs (WP.of_syms (WP.icall (rd := rd ++ Abi.constRegions s.syms _) (wr := wr)
    (P := fun s₁ s₂ => (K (abi.withConsts (fnConsts e (s.gpr .r11) ++ cs₀)) n).post s₁ s₂) hfs
    ⟨s₂, t, hf₂, hok, hpost⟩ hp.hw hp.hn fun s' hrd' hwr' hcs' hF hex hsy hfu => ?_))
  refine hQ s' hrd' hwr' hcs' hF (hW.step hfu hsy hF fun r hr => ?_) hex
  rcases List.mem_append.mp hr with hr | hr
  · exact hp.wr r hr
  · exact hp.stk r hr

/-! ## Two runs of a call -/

theorem withinC_congr {cs₀ : List (String × List (BitVec 64))} {stack : Nat} {e e' s : State}
    {cs : List (String × List (BitVec 64))}
    (hrd : e'.rd = e.rd) (hwr : e'.wr = e.wr) (hsp : e'.gpr .rsp = e.gpr .rsp) (hsy : e'.syms = e.syms)
    (h : (abi.withConsts cs₀).within stack e' cs s) : (abi.withConsts cs₀).within stack e cs s := by
  unfold Abi.within at h ⊢
  rw [withConsts_rd, withConsts_rd, withConsts_wr', withConsts_reserved', withConsts_sym] at h ⊢
  simp only [abi, Option.elim] at h ⊢
  rw [hrd, hwr, hsy, hsp] at h
  exact h

/-- `TwoRuns`, for a caller under `abi.withConsts cs₀`. -/
structure TwoRunsC (cs₀ : List (String × List (BitVec 64))) (K : Abi isa → Nat → Contract isa)
    (n stack : Nat) (e₁ e₂ s₁ s₂ : State) : Prop where
  m₁ : FnMeets (abi.withConsts cs₀) K n stack e₁ (s₁.gpr .r11)
  m₂ : FnMeets (abi.withConsts cs₀) K n stack e₂ (s₂.gpr .r11)
  c₁ : ConstsAt stack e₁ cs₀
  c₂ : ConstsAt stack e₂ cs₀
  w₁ : World stack e₁ s₁
  w₂ : World stack e₂ s₂
  same : abi.sameWorld e₂ e₁
  rd : e₂.rd = e₁.rd
  wr : e₂.wr = e₁.wr
  sp : e₂.gpr .rsp = e₁.gpr .rsp
  r11 : s₂.gpr .r11 = s₁.gpr .r11
  rsp : s₂.gpr .rsp = s₁.gpr .rsp

theorem twoRunsC_nil {K : Abi isa → Nat → Contract isa} {n stack : Nat} {e₁ e₂ s₁ s₂ : State}
    (h : TwoRuns K n stack e₁ e₂ s₁ s₂) : TwoRunsC [] K n stack e₁ e₂ s₁ s₂ :=
  ⟨h.m₁, h.m₂, constsAt_nil _ _, constsAt_nil _ _, h.w₁, h.w₂, h.same, h.rd, h.wr, h.sp, h.r11, h.rsp⟩

/-- `RelCT.icallMeets`, for a caller under `abi.withConsts cs₀`. -/
theorem relCT_icall {cs₀ : List (String × List (BitVec 64))} {K : Abi isa → Nat → Contract isa}
    {n stack : Nat} {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → ∃ (e₁ e₂ : State) (rd₁ wr₁ rd₂ wr₂ : List Region),
      TwoRunsC cs₀ K n stack e₁ e₂ s₁ s₂ ∧ PassesC cs₀ stack n e₁ s₁ rd₁ wr₁ ∧
      PassesC cs₀ stack n e₂ s₂ rd₂ wr₂ ∧
      (let cs := fnConsts e₁ (s₁.gpr .r11) ++ cs₀;
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
  obtain ⟨e₁, e₂, rd₁, wr₁, rd₂, wr₂, ⟨hm₁, hm₂, c₁, c₂, hW₁, hW₂, hsw, hrd, hwr, hsp, h11, hrsp⟩, hp₁, hp₂, hK⟩ :=
    hP _ _ hPs
  have hcs : fnConsts e₂ (s₂.gpr .r11) = fnConsts e₁ (s₁.gpr .r11) := by
    rw [h11]; exact congrFun (show fnConsts e₂ = fnConsts e₁ from hsw.2.1) _
  obtain ⟨f, hfa, hc₁, hrun, hct⟩ := fnMeets_c hm₁
  obtain ⟨-, -, hc₂, -, -⟩ := fnMeets_c hm₂
  obtain ⟨held₁, hregs₁⟩ := consts_two hc₁ c₁ hW₁ hp₁.wr hp₁.stk hp₁.hn
  obtain ⟨held₂, hregs₂⟩ := consts_two hc₂ c₂ hW₂ hp₂.wr hp₂.stk hp₂.hn
  rw [hcs] at held₂ hregs₂
  obtain ⟨pre₁, pre₂, hpub⟩ := hK held₁ held₂ hregs₁ hregs₂
  have hsy : e₂.syms = e₁.syms := by
    have := hsw.2.2; simp only [abi, Option.elim] at this; exact funext fun x => congrFun this x
  cases ex₁ with
  | icall hf₁ hc₁' hr₁ hk₁ hq₁ =>
  cases ex₂ with
  | icall hf₂ hc₂' hr₂ hk₂ hq₂ =>
  rw [call_callEntry, Option.some.injEq] at hc₁' hc₂'
  subst hc₁' hc₂'
  simp only [isa] at hf₁ hf₂
  rw [fnAt_world hW₁, hfa, Option.some.injEq] at hf₁
  rw [fnAt_world hW₂, h11, ← fnAt_world hW₂, fnAt_world hW₂,
    show fnAt e₂ = fnAt e₁ from hsw.1, hfa, Option.some.injEq] at hf₂
  subst hf₁ hf₂
  have w₁ := narrowedC_within hW₁ hp₁ (fnConsts e₁ (s₁.gpr .r11))
  have w₂ : (abi.withConsts cs₀).within stack e₁ (fnConsts e₁ (s₁.gpr .r11))
      (narrowed s₂ rd₂ wr₂ (fnConsts e₁ (s₁.gpr .r11) ++ cs₀)) :=
    withinC_congr hrd hwr hsp hsy (narrowedC_within hW₂ hp₂ _)
  have sw₂ : abi.sameWorld (narrowed s₂ rd₂ wr₂ (fnConsts e₁ (s₁.gpr .r11) ++ cs₀)) e₁ := by
    obtain ⟨a, b, c⟩ := narrowed_sameWorld hW₂ rd₂ wr₂ (fnConsts e₁ (s₁.gpr .r11) ++ cs₀)
    exact ⟨a.trans hsw.1, b.trans hsw.2.1, c.trans hsw.2.2⟩
  obtain ⟨u₁, v₁, hu₁, -, -⟩ := hrun _ (narrowed_sameWorld hW₁ rd₁ wr₁ _) w₁ pre₁
  obtain ⟨u₂, v₂, hu₂, -, -⟩ := hrun _ sw₂ w₂ pre₂
  have hv := hct _ _ _ _ _ _ (narrowed_sameWorld hW₁ rd₁ wr₁ _) sw₂ w₁ w₂ pre₁ pre₂ hpub hu₁ hu₂
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
  have r₁ := ret_rsp hq₁
  have r₂ := ret_rsp hq₂
  simp only [State.callEntry_rsp] at r₁ r₂
  refine ⟨?_, trivial⟩
  simp only [r₁, r₂, hrsp, h11, hv]

end VG.X86_64.CallC
