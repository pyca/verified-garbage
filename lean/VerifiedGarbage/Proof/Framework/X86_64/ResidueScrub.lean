module

public import VerifiedGarbage.Proof.Framework.X86_64.ResidueTaintSound
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public meta import Lean.Meta.Eval
public meta import Lean.Elab.Term
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The residue analysis decides what `scrub` wipes (x86-64)

`init sig stack` is where the residue analysis (`RTaint.rtaint`) starts on
a function of signature `sig`: everything in the registers is the same in
both runs (`Outside 0`), the writable regions are its writable buffers (of
their lengths, if fixed, and their addresses in the argument registers),
and its window is the `stack` bytes below the stack pointer, which hold the
same bytes in both runs (`init_agree`). If the analysis of its code ends
with the window as it started, the window's bytes the analysis cannot show
equal in both runs are those `sec` lists; `scrub` then need wipe only the
16-byte granules that hold them (`keepOf`), and `resOk_of_check` gives
`Verified.scrub` the rest (`Scrub.ResOk`).
-/

@[expose] public section

namespace VG.X86_64.RScrub

open VG.X86_64 VG.X86_64.Taint VG.X86_64.RTaint VG.X86_64.Scrub VG.Impl.Scrub.X86_64

/-! ## Where the analysis starts -/

/-- The word index and length (`0` if not fixed) of each writable buffer of
the parameters, the first at word `w`. -/
def wrInfo : List (String × Param) → Nat → List (Nat × Nat)
  | [], _ => []
  | (_, .int ..) :: ps, w => wrInfo ps (w + 1)
  | (_, .array m e n) :: ps, w => (if m then [(w, n * e.size)] else []) ++ wrInfo ps (w + 1)
  | (_, .slice m _ _) :: ps, w => (if m then [(w, 0)] else []) ++ wrInfo ps (w + 2)
  | (_, .slices ..) :: ps, w => wrInfo ps (w + 2)
  | (_, .table _) :: ps, w => wrInfo ps (w + 1)

/-- The argument registers holding the address of writable buffer `i`, `i + 1`, …. -/
def basesAux : List (Nat × Nat) → Nat → List (Reg × Nat × Nat)
  | [], _ => []
  | q :: qs, i => (match argRegs[q.1]? with | some r => [(r, i, 0)] | none => []) ++ basesAux qs (i + 1)

def allRegs : RegSet Reg := RegSet.ofList
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

def allX : RegSet XReg := RegSet.ofList
  [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7,
   .xmm8, .xmm9, .xmm10, .xmm11, .xmm12, .xmm13, .xmm14, .xmm15]

/-- Where the analysis of a function of signature `sig` starts. -/
def init (sig : Sig) (stack : Nat) (pubs : List (Nat × Nat × Nat) := []) : FT :=
  let ws := wrInfo sig.params 0
  let t : Taint.T := ⟨allRegs, true, ws.map (·.2), basesAux ws 0, pubs, .empty, allX⟩
  ⟨true, t, 0, 0, stack, [], [], [], none, []⟩

/-- The writable buffers. -/
def wrOf (ps : List (String × Param)) (vs : List (BitVec 64)) : List Region :=
  ((Sig.bufs ps vs).filter (·.2)).map (·.1)

theorem wr_info : ∀ (ps : List (String × Param)) (vs : List (BitVec 64)) (w : Nat),
    vs.length = (ps.flatMap (·.2.words 64)).length →
    List.Forall₂ (fun r l => l ≤ r.len) (wrOf ps vs) ((wrInfo ps w).map (·.2)) ∧
    ∀ i (h : i < (wrInfo ps w).length), w ≤ ((wrInfo ps w)[i]).1 ∧ ((wrInfo ps w)[i].1 - w) < vs.length ∧
      ((wrOf ps vs).getD i ⟨0, 0⟩).base = vs.getD ((wrInfo ps w)[i].1 - w) 0
  | [], vs, w, _ => ⟨by simp [wrOf, Sig.bufs, wrInfo], fun i h => by simp [wrInfo] at h⟩
  | (_, p) :: ps, vs, w, hl => by
    cases p with
    | int ty pb =>
      obtain ⟨v, vs, rfl⟩ : ∃ v vs', vs = v :: vs' := by
        cases vs with
        | nil => simp [Param.words] at hl
        | cons v vs => exact ⟨v, vs, rfl⟩
      replace hl : vs.length = (ps.flatMap (·.2.words 64)).length := by
        simp only [List.flatMap_cons, Param.words, List.length_append, List.length_cons, List.length_nil] at hl ⊢
        omega
      obtain ⟨h1, h2⟩ := wr_info ps vs (w + 1) (by omega)
      refine ⟨by simpa [wrOf, Sig.bufs, wrInfo] using h1, fun i h => ?_⟩
      simp only [wrInfo] at h ⊢
      obtain ⟨a, b, c⟩ := h2 i h
      refine ⟨by omega, by simp; omega, ?_⟩
      simp only [wrOf, Sig.bufs] at c ⊢
      rw [c, show (wrInfo ps (w + 1))[i].1 - w = (wrInfo ps (w + 1))[i].1 - (w + 1) + 1 by omega]
      simp
    | array m e n =>
      obtain ⟨v, vs, rfl⟩ : ∃ v vs', vs = v :: vs' := by
        cases vs with
        | nil => simp [Param.words] at hl
        | cons v vs => exact ⟨v, vs, rfl⟩
      replace hl : vs.length = (ps.flatMap (·.2.words 64)).length := by
        simp only [List.flatMap_cons, Param.words, List.length_append, List.length_cons, List.length_nil] at hl ⊢
        omega
      obtain ⟨h1, h2⟩ := wr_info ps vs (w + 1) (by omega)
      cases m with
      | false =>
        refine ⟨by simpa [wrOf, Sig.bufs, wrInfo] using h1, fun i h => ?_⟩
        simp only [wrInfo, Bool.false_eq_true, ↓reduceIte, List.nil_append] at h ⊢
        obtain ⟨a, b, c⟩ := h2 i h
        refine ⟨by omega, by simp; omega, ?_⟩
        simp only [wrOf, Sig.bufs, List.filter_cons, Bool.false_eq_true, ↓reduceIte] at c ⊢
        rw [c, show (wrInfo ps (w + 1))[i].1 - w = (wrInfo ps (w + 1))[i].1 - (w + 1) + 1 by omega]
        simp
      | true =>
        refine ⟨by simpa [wrOf, Sig.bufs, wrInfo] using h1, fun i h => ?_⟩
        simp only [wrInfo, ↓reduceIte, List.singleton_append, List.length_cons] at h ⊢
        cases i with
        | zero => simp [wrOf, Sig.bufs]
        | succ i =>
          obtain ⟨a, b, c⟩ := h2 i (by omega)
          refine ⟨by simp; omega, by simp; omega, ?_⟩
          simp only [wrOf, Sig.bufs, List.filter_cons, ↓reduceIte, List.map_cons, List.getD_cons_succ,
            List.getElem_cons_succ] at c ⊢
          rw [c, show (wrInfo ps (w + 1))[i].1 - w = (wrInfo ps (w + 1))[i].1 - (w + 1) + 1 by omega]
          simp
    | slice m e len =>
      obtain ⟨v, l, vs, rfl⟩ : ∃ v l vs', vs = v :: l :: vs' := by
        match vs with
        | [] => simp [Param.words] at hl
        | [_] => simp [Param.words] at hl
        | v :: l :: vs => exact ⟨v, l, vs, rfl⟩
      replace hl : vs.length = (ps.flatMap (·.2.words 64)).length := by
        simp only [List.flatMap_cons, Param.words, List.length_append, List.length_cons, List.length_nil] at hl ⊢
        omega
      obtain ⟨h1, h2⟩ := wr_info ps vs (w + 2) (by omega)
      cases m with
      | false =>
        refine ⟨by simpa [wrOf, Sig.bufs, wrInfo] using h1, fun i h => ?_⟩
        simp only [wrInfo, Bool.false_eq_true, ↓reduceIte, List.nil_append] at h ⊢
        obtain ⟨a, b, c⟩ := h2 i h
        refine ⟨by omega, by simp; omega, ?_⟩
        simp only [wrOf, Sig.bufs, List.filter_cons, Bool.false_eq_true, ↓reduceIte] at c ⊢
        rw [c, show (wrInfo ps (w + 2))[i].1 - w = (wrInfo ps (w + 2))[i].1 - (w + 2) + 1 + 1 by omega]
        simp
      | true =>
        refine ⟨by simpa [wrOf, Sig.bufs, wrInfo] using h1, fun i h => ?_⟩
        simp only [wrInfo, ↓reduceIte, List.singleton_append, List.length_cons] at h ⊢
        cases i with
        | zero => simp [wrOf, Sig.bufs]
        | succ i =>
          obtain ⟨a, b, c⟩ := h2 i (by omega)
          refine ⟨by simp; omega, by simp; omega, ?_⟩
          simp only [wrOf, Sig.bufs, List.filter_cons, ↓reduceIte, List.map_cons, List.getD_cons_succ,
            List.getElem_cons_succ] at c ⊢
          rw [c, show (wrInfo ps (w + 2))[i].1 - w = (wrInfo ps (w + 2))[i].1 - (w + 2) + 1 + 1 by omega]
          simp
    | slices e count =>
      obtain ⟨v, l, vs, rfl⟩ : ∃ v l vs', vs = v :: l :: vs' := by
        match vs with
        | [] => simp [Param.words] at hl
        | [_] => simp [Param.words] at hl
        | v :: l :: vs => exact ⟨v, l, vs, rfl⟩
      replace hl : vs.length = (ps.flatMap (·.2.words 64)).length := by
        simp only [List.flatMap_cons, Param.words, List.length_append, List.length_cons, List.length_nil] at hl ⊢
        omega
      obtain ⟨h1, h2⟩ := wr_info ps vs (w + 2) (by omega)
      refine ⟨by simpa [wrOf, Sig.bufs, wrInfo] using h1, fun i h => ?_⟩
      simp only [wrInfo] at h ⊢
      obtain ⟨a, b, c⟩ := h2 i h
      refine ⟨by omega, by simp; omega, ?_⟩
      simp only [wrOf, Sig.bufs] at c ⊢
      rw [c, show (wrInfo ps (w + 2))[i].1 - w = (wrInfo ps (w + 2))[i].1 - (w + 2) + 1 + 1 by omega]
      simp
    | table n =>
      obtain ⟨v, vs, rfl⟩ : ∃ v vs', vs = v :: vs' := by
        cases vs with
        | nil => simp [Param.words] at hl
        | cons v vs => exact ⟨v, vs, rfl⟩
      replace hl : vs.length = (ps.flatMap (·.2.words 64)).length := by
        simp only [List.flatMap_cons, Param.words, List.length_append, List.length_cons, List.length_nil] at hl ⊢
        omega
      obtain ⟨h1, h2⟩ := wr_info ps vs (w + 1) (by omega)
      refine ⟨by simpa [wrOf, Sig.bufs, wrInfo] using h1, fun i h => ?_⟩
      simp only [wrInfo] at h ⊢
      obtain ⟨a, b, c⟩ := h2 i h
      refine ⟨by omega, by simp; omega, ?_⟩
      simp only [wrOf, Sig.bufs] at c ⊢
      rw [c, show (wrInfo ps (w + 1))[i].1 - w = (wrInfo ps (w + 1))[i].1 - (w + 1) + 1 by omega]
      simp

theorem basesAux_mem : ∀ {qs : List (Nat × Nat)} {i : Nat} {p : Reg × Nat × Nat}, p ∈ basesAux qs i →
    ∃ j, ∃ h : j < qs.length, argRegs[qs[j].1]? = some p.1 ∧ p.2 = (i + j, 0)
  | [], _, _, h => by simp [basesAux] at h
  | q :: qs, i, p, h => by
    simp only [basesAux, List.mem_append] at h
    rcases h with h | h
    · split at h
      · rename_i r hr
        simp only [List.mem_singleton] at h; subst h
        exact ⟨0, by simp, by simpa using hr, by simp⟩
      · cases h
    · obtain ⟨j, hj, h1, h2⟩ := basesAux_mem h
      exact ⟨j + 1, by simp; omega, by simpa using h1, by rw [h2]; congr 1; omega⟩

theorem abi_vals {ws : List Nat} {f : State → List (BitVec 64)} (h : abi.args ws = some f) {w : Nat}
    (hw : w < ws.length) {r : Reg} (hr : argRegs[w]? = some r) (s : State) : (f s).getD w 0 = s.gpr r := by
  have h6 : w < 6 := by
    have : w < argRegs.length := by
      rcases Nat.lt_or_ge w argRegs.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hr; cases hr
    exact this
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hr
  simp only [abi] at h
  split at h <;> cases h
  · simp [List.getD_eq_getElem?_getD, hw, List.getElem?_eq_getElem hlt]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, hlt]

section
variable {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
  {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
  {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}

/-- What the precondition gives of the writable regions. -/
theorem init_wf (hA : ScrubAbi A) {pubs : List (Nat × Nat × Nat)} {s : State} (h : (sig.contract A pre post wa stack leak).pre s) :
    Wf (init sig stack pubs).t s ∧ List.Forall₂ (fun r l => l ≤ r.len) s.wr (init sig stack pubs).t.lens := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  rename_i vals hvals
  obtain ⟨-, -, hwr, hpw, -, hbnd, -⟩ := h
  have hl : (vals s).length = (sig.params.flatMap (·.2.words 64)).length := by
    rw [hA.argsLen _ _ hvals s, List.length_map]
    show (sig.params.flatMap (·.2.words A.ptrBits)).length = _
    rw [hA.ptrBits]
  -- The writable regions are the writable buffers.
  have hw : s.wr = wrOf sig.params (vals s) := by
    rw [← hA.wr, hwr]
    simp only [List.filter_append, List.map_append, wrOf]
    have e1 : (List.map (fun r => (r, false)) (Sig.lists A.ptrBits (A.mem s) sig.params (vals s))).filter (·.2) = [] := by
      simp
    have e2 : ((A.argArea ((sig.words A.ptrBits).map (·.bits A.ptrBits)) s).map
        (fun (r, w) => (r, w && wa))).filter (·.2) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      simp [hA.argRo _ _ b hb]
    rw [e1, e2]; simp
  obtain ⟨hF, hI⟩ := wr_info sig.params (vals s) 0 hl
  refine ⟨⟨fun _ => ⟨hw ▸ hF, ?_, ?_⟩, fun p hp => ?_⟩, hw ▸ hF⟩
  · rw [hw]
    have h1 := (hpw.sublist (List.sublist_append_left _ _)).sublist
      (List.sublist_append_left (Sig.bufs sig.params (vals s)) _)
    have h2 := h1.sublist (List.filter_sublist (p := (·.2)))
    exact List.pairwise_map.mpr (h2.imp_of_mem fun ha _ h => h (by simp [(List.mem_filter.mp ha).2]))
  · intro r hr
    rw [hw] at hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    have := hbnd a (List.mem_append_left _ (List.mem_filter.mp ha).1)
    rw [hA.ptrBits] at this
    omega
  · obtain ⟨j, hj, hr, hp2⟩ := basesAux_mem hp
    obtain ⟨-, hlt, hb⟩ := hI j hj
    rw [hp2]
    simp only [Nat.zero_add, Nat.sub_zero] at hb hlt ⊢
    have hv : (vals s).getD (wrInfo sig.params 0)[j].1 0 = s.gpr p.1 := by
      have := hA.args ((sig.words A.ptrBits).map (·.bits A.ptrBits))
      rw [hvals] at this
      exact abi_vals this.symm (by rw [← hA.argsLen _ _ hvals s]; exact hlt) hr s
    rw [← hv, ← hb]
    simp [region, hw, BitVec.add_zero]

/-- The bytes `pubs` lists (`(i, o, n)`: the `n` bytes at offset `o` of writable buffer `i`) are
the same in two runs whose entry states agree on what the contract says is public. -/
def PubOk (k : Contract isa) (pubs : List (Nat × Nat × Nat)) : Prop :=
  ∀ s₁ s₂, k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ → Outside 0 s₁ s₂ →
    ∀ sl ∈ pubs, ∀ j, sl.2.1 ≤ j → j < sl.2.1 + sl.2.2 → s₁.mem (byteAddr s₁ sl.1 j) = s₂.mem (byteAddr s₂ sl.1 j)

/-- Every range of `pubs` lies in its buffer, as the signature gives its length. -/
def pubsFit (sig : Sig) (pubs : List (Nat × Nat × Nat)) : Bool :=
  pubs.all fun sl => sl.2.1 + sl.2.2 ≤ ((wrInfo sig.params 0).map (·.2)).getD sl.1 0

theorem init_agree (hA : ScrubAbi A) {pubs : List (Nat × Nat × Nat)} (hfit : pubsFit sig pubs = true)
    (hpub : PubOk (sig.contract A pre post wa stack leak) pubs)
    {s₁ s₂ : State} (h₁ : (sig.contract A pre post wa stack leak).pre s₁)
    (h₂ : (sig.contract A pre post wa stack leak).pre s₂) (ho : Outside 0 s₁ s₂)
    (hp : (sig.contract A pre post wa stack leak).pub s₁ s₂)
    (hu : s₁.unknowns = s₂.unknowns) : Agree (init sig stack pubs) s₁ s₂ := by
  intro _
  have hag := hpub s₁ s₂ h₁ h₂ hp ho
  obtain ⟨hrd, hwr, hg, hrax, hcf, hzf, hsf, hof, hx, -, -, -, -, -, hm⟩ := ho
  have hgr : ∀ r, s₁.gpr r = s₂.gpr r := fun r => by
    by_cases h : r = .rax
    · subst h; simpa using hrax
    · exact hg r h
  obtain ⟨wf₁, hF⟩ := init_wf (stack := stack) (pubs := pubs) hA h₁
  have wf₂ := (init_wf (stack := stack) (pubs := pubs) hA h₂).1
  obtain ⟨hst, hdis⟩ := contract_pre_scrub hA h₁
  have hne : ∀ r ∈ s₁.rd ++ s₁.wr, (⟨s₁.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Disjoint r := by
    intro r hr
    by_cases h0 : stack = 0
    · intro a ha; subst h0; simp [Region.Contains] at ha
    · exact (hdis r hr).2 h0
  have hrsp := (s₁.gpr .rsp).isLt
  refine ⟨⟨⟨fun r _ => hgr r, fun _ => ⟨hcf, hzf, hsf, hof⟩⟩, fun _ => hwr, wf₁, wf₂,
      fun sl h => by simp only [pubsFit, List.all_eq_true, decide_eq_true_eq] at hfit; exact hfit sl h,
      fun sl h k h1 h2 => hag sl h k h1 h2, noLo, fun r _ => (by rw [hx])⟩,
    hgr .rsp, hu, hwr, ?_, Nat.zero_le _, ?_, (by simp [init]; omega), fun _ h => absurd h (Nat.not_lt_zero _), ?_,
    fun _ h => (by cases h), List.Pairwise.nil, fun _ h => (by cases h), ?_, fun _ h => (by cases h),
    ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩,
    ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩⟩
  · intro h
    rw [h] at hF
    exact List.eq_nil_of_length_eq_zero (forall₂_length hF)
  · simp only [init]; rcases hst with h | h <;> omega
  · intro i _ hi
    simp only [init, wb, Nat.add_zero]
    rw [region_getElem hi]
    exact Region.Disjoint.symm (hne _ (List.mem_append_right _ (List.getElem_mem _)))
  · intro j hj _ hw
    simp only [init, Nat.add_zero] at hj
    rw [← wa_eq (hgr .rsp)]
    apply hm
    intro r hr hc
    simp only [RTaint.wa, wb, init] at hc
    exact hne r hr _ (Offset.contains_base _ (by omega) (by omega)) hc

/-- What `resOk_of_check` checks of the analysis's last taint: the window as
it started, and every byte of it `sec` lists in a granule `ks` lists. -/
def resOkB (τ : FT) (stack : Nat) (ks cs : List Nat) : Bool :=
  τ.ok && τ.room == stack && τ.depth == 0 &&
    (List.range stack).all fun j => cov ks cs j || !τ.sec.any fun p => decide (p.1 ≤ j ∧ j < p.1 + p.2)

/-- The analysis of the code, from `init`, proves the bytes of the window
outside the granules `ks` the same in both runs. -/
theorem resOk_of_check {c : Prog isa} {ks cs : List Nat} {pubs : List (Nat × Nat × Nat)} (hA : ScrubAbi A)
    (hv : Verified target c (sig.contract A pre post wa stack leak)) (hcs : cs.sum = stack)
    {h : VG.Taint.Hint FT}
    (hfit : pubsFit sig pubs = true) (hpub : PubOk (sig.contract A pre post wa stack leak) pubs)
    (hc : (VG.Taint.check rtaint (init sig stack pubs) c h).any (resOkB · stack ks cs) = true) :
    ResOk c (sig.contract A pre post wa stack leak) stack ks cs := by
  obtain ⟨τf, hτ, hb⟩ : ∃ τf, VG.Taint.check rtaint (init sig stack pubs) c h = some τf ∧
      resOkB τf stack ks cs = true := by
    cases h' : VG.Taint.check rtaint (init sig stack pubs) c h with
    | none => rw [h'] at hc; cases hc
    | some τf => rw [h'] at hc; exact ⟨τf, rfl, hc⟩
  simp only [resOkB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', List.any_eq_false, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨hok, hroom⟩, hdep⟩, hcov⟩ := hb
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp ho hu e₁ e₂ x hx hw
  obtain ⟨-, ha⟩ := VG.Taint.check_sound (A := rtaint) hτ (init_agree hA hfit hpub h₁ h₂ ho hp hu) e₁ e₂
  have inv := ha hok
  obtain ⟨hcor, -, -⟩ := hv
  have hsp : u₁.gpr .rsp = s₁.gpr .rsp := by
    obtain ⟨t', u', he', hab, -⟩ := hcor s₁ h₁
    obtain ⟨-, rfl⟩ := Exec.det e₁ he'
    exact hab.1 .rsp (by decide)
  have hwr : u₁.wr = s₁.wr := (Exec.rdwr e₁).2
  obtain ⟨hst, hdis⟩ := contract_pre_scrub hA h₁
  have hj : (x - (s₁.gpr .rsp - BitVec.ofNat 64 stack)).toNat < stack := by
    simp only [Region.Contains] at hx; omega
  generalize hJ : (x - (s₁.gpr .rsp - BitVec.ofNat 64 stack)).toNat = j at hj
  have hxe : x = RTaint.wa u₁ τf j := by
    simp only [RTaint.wa, wb, hroom, hsp, ← hJ, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [BitVec.add_comm, BitVec.sub_add_cancel]
  have hcj : cov ks cs j = false := by
    cases h' : cov ks cs j
    · rfl
    · exact absurd ⟨hcs ▸ hx, by rw [hcs, hJ]; exact h'⟩ hw
  have hns : ¬ InSec τf.sec j := by
    rintro ⟨p, hp, h1, h2⟩
    rcases hcov j hj with h | h
    · rw [hcj] at h; cases h
    · exact h p hp ⟨h1, h2⟩
  have hfree : ∀ r ∈ u₁.wr, ¬ r.Contains (RTaint.wa u₁ τf j) 1 := by
    intro r hr hc
    rw [hwr] at hr
    rw [← hxe] at hc
    exact (hdis r (List.mem_append_right _ hr)).2 (by omega) x hx hc
  have := inv.dead j (by rw [hroom, hdep]; omega) hns hfree
  have e2 : RTaint.wa u₂ τf j = RTaint.wa u₁ τf j := by simp only [RTaint.wa, wb, inv.rsp]
  rw [e2, ← hxe] at this
  exact this

end

/-! ## The granules to wipe -/

/-- The granules `wipe ks cs` may zero, as offsets from the bottom of the
`cs.sum` bytes and widths. -/
def granules : List Nat → List (Nat × Nat)
  | [] => []
  | b :: bs => ((List.range (b / 16)).map fun t => (bs.sum + b % 16 + 16 * t, 16)) ++
    (if b % 16 = 8 then [(bs.sum, 8)] else []) ++ granules bs

/-- The granules of `wipe _ cs` that hold a byte `sec` lists. -/
def keepOf (sec : List (Nat × Nat)) (cs : List Nat) : List Nat :=
  (granules cs).filterMap fun g =>
    if (List.range g.2).any (fun k => sec.any fun p => decide (p.1 ≤ g.1 + k ∧ g.1 + k < p.1 + p.2)) then
      some g.1 else none

/-! ## Registrations -/

/-- `resOk_of_check` for a registration. -/
theorem resOk_reg {api : Api} (r : Registration api target) (ks : List Nat) {pubs : List (Nat × Nat × Nat)}
    (hfit : pubsFit api.sig pubs = true) (hpub : PubOk r.contract pubs) {h : VG.Taint.Hint FT}
    (hc : (VG.Taint.check rtaint (init api.sig r.stack pubs) r.code h).any (resOkB · r.stack ks (chunks r.stack)) = true) :
    ResOk r.code r.contract r.stack ks (chunks r.stack) := by
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  have hp := hpub
  rw [e] at hv hp ⊢
  exact resOk_of_check (ScrubAbi.of r.consts api.sig r.tables api.pubMode) hv (chunks_sum r.stack) hfit hp hc

theorem pubOk_nil (k : Contract isa) : PubOk k [] := fun _ _ _ _ _ _ _ h => absurd h List.not_mem_nil

/-- `resOk_reg`, with no bytes of the buffers known public. -/
theorem resOk_reg0 {api : Api} (r : Registration api target) (ks : List Nat) {h : VG.Taint.Hint FT}
    (hc : (VG.Taint.check rtaint (init api.sig r.stack) r.code h).any (resOkB · r.stack ks (chunks r.stack)) = true) :
    ResOk r.code r.contract r.stack ks (chunks r.stack) :=
  resOk_reg r ks (pubs := []) rfl (pubOk_nil _) hc

/-- The granules of `r.stack` bytes of stack that `scrub` must wipe after
the code `code` of signature `sig`, from the analysis (none if it fails,
which the check then rejects). -/
def keepFor (sig : Sig) (stack : Nat) (code : Prog isa) (pubs : List (Nat × Nat × Nat) := []) : List Nat :=
  match VG.Taint.hint rtaint 256 (init sig stack pubs) code with
  | some (τ, _) => keepOf τ.sec (chunks stack)
  | none => []

/-- The level `scrub` clears the vector registers at for `code`: `pxor` if
nothing in it writes bits 511:128 of a vector register, else `vpxor`. -/
def levelFor (code : Prog isa) : VecLevel :=
  if code.all (fun i => decide (i.vecLevel ≤ VecLevel.sse.level)) then .sse else .avx

/-- The residue analysis of the code `code` of signature `sig`, whose frames
and calls use `stack` bytes, from `init` with the bytes `pubs` of its buffers
public: the granules `ks` that `scrub` wipes, and the analysis's success
(`resOk_of_check`), which the kernel checks (`taint_decide`). -/
structure Analysed (sig : Sig) (stack : Nat) (pubs : List (Nat × Nat × Nat)) (code : Prog isa) where
  ks : List Nat
  ok : ∃ h : VG.Taint.Hint FT,
    (VG.Taint.check rtaint (init sig stack pubs) code h).any (resOkB · stack ks (chunks stack)) = true

/-- `Analysed.ok`, from the analysis with a hint `taint_decide` finds. -/
theorem Analysed.ok_of {sig : Sig} {stack : Nat} {pubs : List (Nat × Nat × Nat)} {code : Prog isa}
    (ks : List Nat) {h : VG.Taint.Hint FT}
    (hc : (VG.Taint.check rtaint (init sig stack pubs) code h).any (resOkB · stack ks (chunks stack)) = true) :
    ∃ h : VG.Taint.Hint FT,
      (VG.Taint.check rtaint (init sig stack pubs) code h).any (resOkB · stack ks (chunks stack)) = true :=
  ⟨h, hc⟩

/-- `r`, returning without secret residue (`scrubReg`), given the residue
analysis of its code (`Analysed`) and if `scrub`'s side conditions hold;
otherwise `r` itself, which then has no proof (`Registration.residue`), as
the emitter allows only of what `ci/residue_allowlist.txt` lists. A caller
generic over the implementations of a function (`Generic/`) takes the
analysis of each of its instances from the implementation, `none` for one
the analysis does not handle. -/
def withScrub {api : Api} (r : Registration api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (pubs : List (Nat × Nat × Nat)) (hpub : PubOk r.contract pubs)
    (a : Option (Analysed api.sig r.stack pubs r.code)) : Registration api target :=
  match a with
  | none => r
  | some a =>
    let v := levelFor r.code
    if hfit : pubsFit api.sig pubs = true then
    if hd : r.code.x86_64Depth ≤ r.stack then
    if hst : r.stack + 8 < 2 ^ 64 then
    if h8 : r.stack % 8 = 0 then
    if hlv : r.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true then
    if hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨
        api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64 then
    if hw : r.written = [] then
      scrubReg r v a.ks hd hst h8 hlv hrb hpost
        (by obtain ⟨_, hc⟩ := a.ok; exact resOk_reg r a.ks hfit hpub hc) hw
    else r else r else r else r else r else r else r

end VG.X86_64.RScrub

/-- `keep_for% sig stack code`: `RScrub.keepFor sig stack code`, computed in
compiled code, as a literal (for the kernel, which then checks it with the
analysis, `RScrub.resOk_reg`, rather than computing it too). -/
syntax "keep_for% " term:max term:max term:max (term:max)? : term

open Lean Elab Term Meta in
elab_rules : term
  | `(keep_for% $sig $stack $code $[$pubs]?) => do
  let e ← match pubs with
    | some p => elabTerm (← `(VG.X86_64.RScrub.keepFor $sig $stack $code $p)) none
    | none => elabTerm (← `(VG.X86_64.RScrub.keepFor $sig $stack $code)) none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let v ← unsafe evalExpr (List Nat) (← inferType e) e
  return toExpr v

