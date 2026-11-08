module

public import VerifiedGarbage.Proof.Framework.AArch64.CallWipe
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratchConsts
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Mem

/-!
# A call that wipes part of a buffer afterwards, for code that reads tables of constants (AArch64)

`Verified.callWipeC'` and `Verified.callWipeC`: `Verified.callWipe'` and
`Verified.callWipe` (`CallWipe.lean`) for contracts under `abi.withConsts K`,
whose readable regions end with the tables `K`
(`StackScratchConsts.lean`), with the same hypotheses. Without its tables
(`stripConsts`), a state satisfying the caller's contract satisfies it under
`abi` (`pre_consts`), and `cw_wp` and `cw_ct` run `callWipe` from it with the
readable regions it has. The first function runs with them, tables
included: the frame, within the stack the caller's contract reserves, lies
apart from the tables and leaves them as they are, and the stack the first
function's contract reserves lies within the caller's
(`constsOk_cwEntry`).
-/

@[expose] public section

namespace VG.AArch64

open VG.Impl.CallWipe.AArch64

section
variable {sig : Sig} {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

theorem stripConsts_cwEntry (K : List (String × List (BitVec 64))) (r : Reg) (s : State) :
    stripConsts K (cwEntry r s) = cwEntry r (stripConsts K s) := rfl

/-- What `abi.withConsts` says of the tables holds at the first function's
entry: the frame's writes lie apart from them, and the stack its contract
reserves within the caller's. -/
theorem constsOk_cwEntry (r : Reg) {s : State} (hsb : stack + 32 ≤ s.sp.toNat)
    (hc : ConstsOk (c₀ :: cs) (stack + 32) s) : ConstsOk (c₀ :: cs) stack (cwEntry r s) := by
  obtain ⟨hd, hh, ht, hal⟩ := hc
  have hR : below s.sp (stack + 32) ∈ abi.reserved (stack + 32) s := reserved_below (by omega_using []) s
  refine ⟨hd, ?_, fun t ht' => ⟨(ht t ht').1, (ht t ht').2.1, fun q hq => ?_⟩, hal⟩
  · intro c hc i hi
    have htc : (⟨s.syms c.1, 8 * c.2.length⟩ : Region) ∈ constRegs (c₀ :: cs) s :=
      List.mem_map.mpr ⟨c, hc, rfl⟩
    have hfr : Frame [below s.sp 32] s.mem (cwEntry r s).mem := cwSave_frame r s
    have hb : (s.syms c.1).toNat + 8 * c.2.length ≤ 2 ^ 64 := (ht _ htc).1
    show (cwEntry r s).mem.readW (s.syms c.1 + BitVec.ofNat 64 (8 * i)) 64 = c.2.getD i 0
    rw [hfr.readW (r := ⟨s.syms c.1, 8 * c.2.length⟩)
      (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hb]))
      (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact ((ht _ htc).2.2 _ hR).sub_right (below_sub (by omega_using []) (by omega_using [hsb])))
      (by decide)]
    exact hh c hc i hi
  · have hq' : q ∈ stackBelow (s.sp - BitVec.ofNat 64 32) stack := hq
    rcases Nat.eq_zero_or_pos stack with h0 | h0
    · subst h0; simp [stackBelow] at hq'
    · rw [stackBelow_pos _ h0, List.mem_singleton] at hq'; subst hq'
      exact ((ht t ht').2.2 _ hR).sub_right (below_below _ 32 stack)

/-- The caller's precondition gives the first function's at its entry. -/
theorem cw_bodyPreK (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    {r : Reg} (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + 32) leak).pre s) :
    (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa stack leak).pre (cwEntry r s) := by
  obtain ⟨hs₀, hc⟩ := pre_consts.mp hs
  have hsb : stack + 32 ≤ s.sp.toNat := cw_sp (s := stripConsts (c₀ :: cs) s) hk hl hs₀
  refine pre_consts.mpr ⟨?_, constsOk_cwEntry r hsb hc⟩
  rw [stripConsts_cwEntry]
  exact cw_bodyPre hk hl hpre hs₀

/-- The caller's public data is the first function's at its entry. -/
theorem cw_bodyPubK (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    (r : Reg) {s₁ s₂ : State}
    (h₁ : (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + 32) leak).pre s₁)
    (h₂ : (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + 32) leak).pre s₂)
    (hp : (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + 32) leak).pub s₁ s₂)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak) :
    (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa stack leak).pub (cwEntry r s₁) (cwEntry r s₂) := by
  obtain ⟨hp₀, hsy⟩ := pub_consts.mp hp
  exact pub_consts.mpr ⟨cw_bodyPub hk hl r (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 hp₀ hleak, hsy⟩

/-- `Verified.callWipe'` for code that reads the tables `c₀ :: cs`, under
`abi.withConsts (c₀ :: cs)`. -/
theorem Verified.callWipeC' {post' : sig.Post abi.ptrBits} {name zname : String}
    {body zcode : Prog isa} {zst : Nat} {ps₁ ps₂ : List (String × Param)} {nm : String} {e : Elem}
    {k n i : Nat}
    (h : Verified target body (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa stack leak))
    (hz : Verified target zcode (Spec.Zeroize.zeroizeContract abi zst))
    (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    (hps : sig.params = ps₁ ++ (nm, .array true e k) :: ps₂)
    (hi : i = (ps₁.flatMap fun p => p.2.words 64).length)
    (hn : n ≤ k * e.size) (hn16 : n < 2 ^ 16)
    (hd : 16 * body.aarch64Depth ≤ stack) (hzd : 16 * zcode.aarch64Depth ≤ zst) (hzs : zst ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' x →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' x)
    (hpostOut : ∀ vs m m₁ m₂ x, vs.length = (sig.words abi.ptrBits).length →
      (Sig.bufs sig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs sig.params vs, b.1.Disjoint ⟨vs.getD i 0, k * e.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ x →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ x)
    (hwiped : ∀ vs m m' x, vs.length = (sig.words abi.ptrBits).length →
      Curry.apply (sig.words abi.ptrBits) post vs m m' x →
      Spec.Zeroize.bytesAt m' (vs.getD i 0) n = Spec.Zeroize.zeros n →
        Curry.apply (sig.words abi.ptrBits) post' vs m m' x)
    (hsat : ∃ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post' wa (stack + 32) leak).pre s)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) :
    Verified target (Impl.CallWipe.AArch64.callWipe (argRegs.getD i .x0) n name body zname zcode)
      (sig.contract (abi.withConsts (c₀ :: cs)) pre post' wa (stack + 32) leak) := by
  subst hi
  generalize hr' : argRegs.getD (ps₁.flatMap fun p => p.2.words 64).length .x0 = r
  have hget := cw_get hk hps hr'
  have harr : ∀ s : State, (⟨s.gpr r, k * e.size⟩, true) ∈ Sig.bufs sig.params (regArgs sig s) :=
    cw_arr hk hps hr'
  -- The postcondition reads the memory on return only within the buffers apart from the array.
  have hout : ∀ s, (sig.contract abi pre post wa (stack + 32) leak).pre (stripConsts (c₀ :: cs) s) →
      ∀ m₁ m₂ x, (∀ b ∈ Sig.bufs sig.params (regArgs sig s), b.1.Disjoint ⟨s.gpr r, k * e.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem m₁ x →
        Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem m₂ x := by
    intro s hs m₁ m₂ x hag hq
    have hpw : (Sig.bufs sig.params (regArgs sig s)).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) :=
      ((pre_regs' hk hl).mp hs).2.2.2.1
    exact hpostOut _ _ _ _ _ (regArgs_length sig s hk) hpw (by rw [hget]; exact hag) hq
  -- The first function's run, from the caller's state.
  have hbody : ∀ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + 32) leak).pre s →
      WP isa (.call name body) (cwSave r s) (AfterBody sig post r stack s) := fun s hs =>
    cw_body_wpOf (rd := (stripConsts (c₀ :: cs) s).rd) h.1 (fun _ _ h => post_consts.mp h) hk hl hd hpost
      (pre_consts.mp hs).1 (cw_bodyPreK hk hl hpre hs)
  refine ⟨fun s hs => ?_, ?_, hsat⟩
  · have hs' : (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + 32) leak).pre s := hs
    have hs₀ := (pre_consts.mp hs').1
    obtain ⟨t, g, he, habi, hq, hz0⟩ :=
      cw_wp (r := r) (post := post) (leak := leak) (rd := (stripConsts (c₀ :: cs) s).rd) hz hk hl hzd hzs
        hn hn16 hs₀ (harr s) (hbody s hs') (hout s hs₀)
    refine ⟨t, g, he, habi, post_consts.mpr ?_⟩
    rw [post_regs hk] at hq ⊢
    exact hwiped _ _ _ _ (regArgs_length sig s hk) hq (by rw [hget]; exact hz0)
  · refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.alloc (R := fun _ _ => True) ?_)
    refine RelCT.exists_ fun σ₁ => RelCT.exists_ fun σ₂ => ?_
    by_cases hP0 : (sig.contract (abi.withConsts (c₀ :: cs)) pre post' wa (stack + 32) leak).pre σ₁ ∧
        (sig.contract (abi.withConsts (c₀ :: cs)) pre post' wa (stack + 32) leak).pre σ₂ ∧
        (sig.contract (abi.withConsts (c₀ :: cs)) pre post' wa (stack + 32) leak).pub σ₁ σ₂
    swap
    · exact RelCT.of_false fun a b hab => hP0 hab.1
    obtain ⟨h₁, h₂, hp⟩ := hP0
    have h₁' : (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + 32) leak).pre σ₁ := h₁
    have h₂' : (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + 32) leak).pre σ₂ := h₂
    have hp' : (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + 32) leak).pub σ₁ σ₂ := hp
    have hp₀ := (pub_consts.mp hp').1
    have hsp12 : σ₁.sp = σ₂.sp := ((pub_regs hk).mp hp₀).1.1
    have hpp : σ₁.gpr r = σ₂.gpr r := cw_pubArr hk hps hr' hp₀
    refine RelCT.mono (P := fun a b => a = allocated 32 σ₁ ∧ b = allocated 32 σ₂)
      (cw_ct (post := post) (leak := leak) (rd₁ := (stripConsts (c₀ :: cs) σ₁).rd)
        (rd₂ := (stripConsts (c₀ :: cs) σ₂).rd) hz hk hl hzd hzs hn hn16 (pre_consts.mp h₁').1
        (pre_consts.mp h₂').1 (harr σ₁) (harr σ₂) hsp12 hpp ?_)
      (fun a b hab => hab.2) (fun _ _ h => h)
    -- The first function.
    have hcov : ∀ σ : State, Covers (σ.rd ++ σ.wr) ((cwSave r σ).rd ++ (cwSave r σ).wr) ∧
        Covers σ.wr (cwSave r σ).wr := fun σ =>
      ⟨Covers.append (Covers.refl _) (Covers.of_mem fun x hx => List.mem_cons_of_mem _ hx),
        Covers.of_mem fun x hx => List.mem_cons_of_mem _ hx⟩
    refine RelCT.mono (RelCT.wp (F₁ := AfterBody sig post r stack σ₁) (F₂ := AfterBody sig post r stack σ₂)
      (RelCT.callEx h.1 h.2.1 fun a b hab => ?_) fun a b hab => ?_) (fun _ _ h => h) (fun _ _ h => h.2)
    · obtain ⟨rfl, rfl⟩ := hab
      exact ⟨σ₁.rd, σ₁.wr, σ₂.rd, σ₂.wr, cw_bodyPreK hk hl hpre h₁', cw_bodyPreK hk hl hpre h₂',
        cw_bodyPubK hk hl r h₁' h₂' hp' hleak, (hcov σ₁).1, (hcov σ₁).2, (hcov σ₂).1, (hcov σ₂).2⟩
    · obtain ⟨rfl, rfl⟩ := hab
      exact ⟨hbody σ₁ h₁', hbody σ₂ h₂'⟩

/-- `Verified.callWipeC'`, with the function's postcondition. -/
theorem Verified.callWipeC {name zname : String} {body zcode : Prog isa} {zst : Nat}
    {ps₁ ps₂ : List (String × Param)} {nm : String} {e : Elem} {k n i : Nat}
    (h : Verified target body (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa stack leak))
    (hz : Verified target zcode (Spec.Zeroize.zeroizeContract abi zst))
    (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    (hps : sig.params = ps₁ ++ (nm, .array true e k) :: ps₂)
    (hi : i = (ps₁.flatMap fun p => p.2.words 64).length)
    (hn : n ≤ k * e.size) (hn16 : n < 2 ^ 16)
    (hd : 16 * body.aarch64Depth ≤ stack) (hzd : 16 * zcode.aarch64Depth ≤ zst) (hzs : zst ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' x →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' x)
    (hpostOut : ∀ vs m m₁ m₂ x, vs.length = (sig.words abi.ptrBits).length →
      (Sig.bufs sig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs sig.params vs, b.1.Disjoint ⟨vs.getD i 0, k * e.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ x →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ x)
    (hsat : ∃ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + 32) leak).pre s)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) :
    Verified target (Impl.CallWipe.AArch64.callWipe (argRegs.getD i .x0) n name body zname zcode)
      (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + 32) leak) :=
  Verified.callWipeC' h hz hk hl hps hi hn hn16 hd hzd hzs hpre hpost hpostOut
    (fun _ _ _ _ _ hq _ => hq) hsat hleak

end

end VG.AArch64
