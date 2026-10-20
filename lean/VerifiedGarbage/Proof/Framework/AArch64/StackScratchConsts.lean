module
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratch

import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Offset

/-!
# A scratch buffer on the stack, for code that reads tables of constants (AArch64)

As on x86-64 (`Proof/Framework/X86_64/StackScratchConsts.lean`).
`Verified.stackScratchWipedC`: `Verified.stackScratchWiped` for contracts
under `abi.withConsts K`, whose readable regions end with the tables `K`.
The frame and the state the code runs from (`narrow`) are those of
`Verified.stackScratchWiped`. Without its tables, a state satisfying the
contract under `abi.withConsts K` satisfies it under `abi` (`pre_consts`),
so the lemmas of `StackScratch.lean` apply to it; `narrow` keeps the
readable regions, the memory and the statics' addresses, and the tables lie
outside the frame, which is within the stack the contract reserves
(`narrowK_pre`). The run of the frame (`withStackScratchK_run`) is
`withStackScratch_run`'s, which needs of the entry state only that the
contract reserves the frame's stack.
-/

@[expose] public section

namespace VG.AArch64

open VG.Impl.StackScratch.AArch64

/-- The regions of the tables `K` in `s`. -/
abbrev constRegs (K : List (String × List (BitVec 64))) (s : State) : List Region :=
  Abi.constRegions (fun name => s.syms name) K

/-- `s` without the regions of the tables `K` at the end of its readable regions. -/
def stripConsts (K : List (String × List (BitVec 64))) (s : State) : State :=
  s.withRegions (s.rd.take (s.rd.length - K.length)) s.wr

/-- What `abi.withConsts K` adds to the calling convention's well-formedness. -/
def ConstsOk (K : List (String × List (BitVec 64))) (st : Nat) (s : State) : Prop :=
  s.rd.drop (s.rd.length - K.length) = constRegs K s ∧ Abi.constsHeld s.mem (fun name => s.syms name) K ∧
    ∀ t ∈ constRegs K s, t.base.toNat + t.len ≤ 2 ^ abi.ptrBits ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧
      ∀ r ∈ abi.reserved st s, t.Disjoint r

@[simp] theorem stripConsts_gpr (K : List (String × List (BitVec 64))) (s : State) :
    (stripConsts K s).gpr = s.gpr := rfl
@[simp] theorem stripConsts_sp (K : List (String × List (BitVec 64))) (s : State) :
    (stripConsts K s).sp = s.sp := rfl
@[simp] theorem stripConsts_mem (K : List (String × List (BitVec 64))) (s : State) :
    (stripConsts K s).mem = s.mem := rfl
@[simp] theorem stripConsts_wr (K : List (String × List (BitVec 64))) (s : State) :
    (stripConsts K s).wr = s.wr := rfl

section
variable {sig : Sig} {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {st : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- The arguments do not depend on the readable regions. -/
theorem args_stripConsts {K : List (String × List (BitVec 64))} {ws : List Nat} {vals : State → List (BitVec 64)}
    (h : abi.args ws = some vals) (s : State) : vals (stripConsts K s) = vals s := by
  simp only [abi] at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · split at h
      · cases h; rfl
      · cases h

theorem withConsts_ptrBits : (abi.withConsts (c₀ :: cs)).ptrBits = abi.ptrBits := rfl
theorem withConsts_args : (abi.withConsts (c₀ :: cs)).args = abi.args := rfl
theorem withConsts_argArea : (abi.withConsts (c₀ :: cs)).argArea = abi.argArea := rfl
theorem withConsts_reserved : (abi.withConsts (c₀ :: cs)).reserved = abi.reserved := rfl
theorem withConsts_mem : (abi.withConsts (c₀ :: cs)).mem = abi.mem := rfl
theorem withConsts_wr : (abi.withConsts (c₀ :: cs)).wr = abi.wr := rfl
theorem withConsts_rd :
    (abi.withConsts (c₀ :: cs)).rd = fun s => s.rd.take (s.rd.length - (c₀ :: cs).length) := rfl
theorem withConsts_wf :
    (abi.withConsts (c₀ :: cs)).wf = fun ws n s => abi.wf ws n s ∧ ConstsOk (c₀ :: cs) n s := rfl
theorem withConsts_pub : (abi.withConsts (c₀ :: cs)).pub = fun s₁ s₂ =>
    abi.pub s₁ s₂ ∧ ∀ c ∈ c₀ :: cs, s₁.syms c.1 = s₂.syms c.1 := rfl

/-- A precondition under `abi.withConsts`: the one under `abi` without the
tables' regions, and what the tables add. -/
theorem pre_consts {s : State} :
    (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa st leak).pre s ↔
      (sig.contract abi pre post wa st leak).pre (stripConsts (c₀ :: cs) s) ∧ ConstsOk (c₀ :: cs) st s := by
  dsimp only [Sig.contract, withConsts_args, withConsts_rd, withConsts_wr, withConsts_wf, withConsts_mem,
    withConsts_argArea, withConsts_reserved, withConsts_ptrBits]
  cases h : abi.args ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) with
  | none => simp
  | some vals =>
    dsimp only
    rw [args_stripConsts h]
    constructor
    · rintro ⟨⟨hw, hd, hh, ht⟩, hrd, hwr, hpw, hres, hnw, hpr⟩
      exact ⟨⟨hw, hrd, hwr, hpw, hres, hnw, hpr⟩, hd, hh, ht⟩
    · rintro ⟨⟨hw, hrd, hwr, hpw, hres, hnw, hpr⟩, hd, hh, ht⟩
      exact ⟨⟨hw, hd, hh, ht⟩, hrd, hwr, hpw, hres, hnw, hpr⟩

/-- A postcondition under `abi.withConsts` is the one under `abi`. -/
theorem post_consts {s s' : State} :
    (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa st leak).post s s' ↔
      (sig.contract abi pre post wa st leak).post s s' := Iff.rfl

/-- The public data under `abi.withConsts`: that under `abi`, and the tables'
addresses. -/
theorem pub_consts {s₁ s₂ : State} :
    (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa st leak).pub s₁ s₂ ↔
      (sig.contract abi pre post wa st leak).pub s₁ s₂ ∧ ∀ c ∈ c₀ :: cs, s₁.syms c.1 = s₂.syms c.1 := by
  dsimp only [Sig.contract, withConsts_args, withConsts_pub, withConsts_mem, withConsts_ptrBits]
  generalize abi.args ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) = o
  cases o with
  | none => simp
  | some vals =>
    cases leak with
    | none =>
      constructor
      · rintro ⟨⟨hp, hs⟩, ha, hd⟩; exact ⟨⟨hp, ha, hd⟩, hs⟩
      · rintro ⟨⟨hp, ha, hd⟩, hs⟩; exact ⟨⟨hp, hs⟩, ha, hd⟩
    | some f =>
      constructor
      · rintro ⟨⟨⟨hp, hs⟩, hl⟩, ha, hd⟩; exact ⟨⟨⟨hp, hl⟩, ha, hd⟩, hs⟩
      · rintro ⟨⟨⟨hp, hl⟩, ha, hd⟩, hs⟩; exact ⟨⟨⟨hp, hs⟩, hl⟩, ha, hd⟩

end

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes words : Nat}

@[simp] theorem narrow_syms (s : State) : (narrow sig e n bytes s).syms = s.syms := rfl

/-- `narrow` of `s` without the tables' regions is `narrow s` without them. -/
theorem stripConsts_narrow (K : List (String × List (BitVec 64))) (s : State) :
    stripConsts K (narrow sig e n bytes s) = narrow sig e n bytes (stripConsts K s) := rfl

/-- The stack the contract reserves below `sp`, which holds the frame. -/
theorem reserved_below (hS : 0 < stack + bytes) (s : State) :
    below s.sp (stack + bytes) ∈ abi.reserved (stack + bytes) s := by
  show _ ∈ stackBelow s.sp (stack + bytes)
  rw [stackBelow_pos _ hS]; simp

/-- What the precondition under `abi.withConsts` says of the stack pointer. -/
theorem sp_of_preK (hk : (sig.words abi.ptrBits).length < 8) (hb : 0 < bytes) {s : State}
    (hs : (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)).pre s) :
    stack + bytes ≤ s.sp.toNat := by
  have hwf := ((pre_regs (by omega)).mp (pre_consts.mp hs).1).1
  simp only [stripConsts_sp] at hwf
  rcases hwf with h | h <;> omega

/-- The precondition under `abi.withConsts` gives the one with the buffer in
`narrow`. -/
theorem narrowK_pre (hk : (sig.words abi.ptrBits).length < 8)
    (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0 ∧ n * e.size ≤ bytes) {s : State}
    (hs : (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)).pre s) :
    (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack).pre (narrow sig e n bytes s) := by
  have hsb := sp_of_preK hk hb.1 hs
  obtain ⟨hs', hd, hh, ht⟩ := pre_consts.mp hs
  have hn := narrow_pre (nm := nm) hk hb hs'
  have hR := reserved_below (stack := stack) (bytes := bytes) (by omega) s
  refine pre_consts.mpr ⟨by rw [stripConsts_narrow]; exact hn, hd, hh, fun t ht' => ⟨(ht t ht').1, ?_, ?_⟩⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact (ht t ht').2.1 r hr
    · simp only [List.mem_singleton] at hr; subst hr
      exact ((ht t ht').2.2 _ hR).sub_right (Offset.sub_below _ (by omega) (by have := hb.2.2.2; omega))
  · intro r hr
    have hr' : r ∈ stackBelow (s.sp - BitVec.ofNat 64 bytes) stack := hr
    rcases Nat.eq_zero_or_pos stack with h0 | h0
    · subst h0; simp [stackBelow] at hr'
    · rw [stackBelow_pos _ h0, List.mem_singleton] at hr'; subst hr'
      exact ((ht t ht').2.2 _ hR).sub_right (below_below _ bytes stack)

/-- `withStackScratch_run`, from the fact about the entry state it needs: the
stack the contract reserves. -/
theorem withStackScratchK_run {c : Prog isa} (hk : (sig.words abi.ptrBits).length < 8)
    (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0 ∧ n * e.size ≤ bytes) {s : State}
    (hsb : stack + bytes ≤ s.sp.toNat) {t : List Leak} {s₃ : State}
    (he : Exec isa c (narrow sig e n bytes s) t s₃) (ha : abiPreserved (narrow sig e n bytes s) s₃) :
    Exec isa (withStackScratch bytes (argRegs.getD (sig.words abi.ptrBits).length .x0) c) s t
        (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr = s₃.gpr := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := hb
  obtain ⟨hr2, -⟩ := argRegs_scratch _ hk
  have hpush : isa.push (.alloc bytes) s = some (allocated bytes s) := by
    simp only [isa, push, allocated]
    exact ite_eq_left ⟨hb0, hb1, hb2, by omega⟩
  have hblk : Exec isa (.block [.addSp (argRegs.getD (sig.words abi.ptrBits).length .x0) 0])
      (allocated bytes s) [] (scratchState sig bytes s) :=
    .block (by simp only [execBlock, isa, exec, show (0 : Nat) < 4096 by decide, ite_true,
      Option.map_some, addrs, List.map_nil, List.append_nil, scratchState])
  have hcov : Covers (s.wr ++ [⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩])
      (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) :=
    Covers.append_left (Covers.of_mem fun r hr => List.mem_cons_of_mem _ hr)
      (Covers.one ⟨_, List.mem_cons_self .., Region.contains_self' (by omega)⟩)
  have hw := Exec.widen he (rd := s.rd) (wr := ⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)
    (by simpa using Covers.append (Covers.refl s.rd) hcov) (by simpa using hcov)
  rw [show (narrow sig e n bytes s).withRegions s.rd (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) =
      scratchState sig bytes s from rfl] at hw
  have hsp₃ : s₃.sp = s.sp - BitVec.ofNat 64 bytes := ha.2.1.trans (narrow_sp s)
  have hpop : isa.pop (.free bytes) (allocated bytes s)
      (s₃.withRegions s.rd (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)) =
      some (popState bytes s s₃) := by
    simp only [isa, pop, State.withRegions, allocated, hsp₃, List.head?_cons, List.tail_cons, hb0,
      hb1, hb2, and_self, ite_true, BitVec.sub_add_cancel]
    rfl
  have hex := Exec.frame hpush (Exec.seq hblk hw) hpop
  simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] at hex
  refine ⟨hex, ⟨fun q hq => ?_, ?_, fun q hq => ?_⟩, rfl, rfl⟩
  · have hqr : q ≠ argRegs.getD (sig.words abi.ptrBits).length .x0 := fun h => hr2 (h ▸ hq)
    show s₃.gpr q = s.gpr q
    rw [ha.1 q hq, narrow_gpr]
    simp only [hqr, ↓reduceIte]
  · rfl
  · show (s₃.v q).extractLsb' 0 64 = (s.v q).extractLsb' 0 64
    exact ha.2.2 q hq

/-- Code verified for a function whose last argument, in a register, is a
scratch buffer, and which reads the tables `c₀ :: cs`, is verified for the
function without it (`Verified.stackScratchWiped`, under
`abi.withConsts (c₀ :: cs)`). -/
theorem Verified.stackScratchWipedC {c : Prog isa}
    (h : Verified target c (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack))
    (hk : (sig.words abi.ptrBits).length < 8)
    (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0 ∧ n * e.size ≤ bytes)
    (hw : 8 * words ≤ n * e.size)
    (hpost : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r)
    (hsat : ∃ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)).pre s) :
    Verified target
      (withStackScratchWiped bytes (argRegs.getD (sig.words abi.ptrBits).length .x0) words c)
      (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hlen := regArgs_length sig
  -- The buffer, below the stack the contract without it reserves, so apart
  -- from its buffers.
  have hdisj : ∀ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)).pre s →
      ∀ b ∈ Sig.bufs sig.params (regArgs sig s),
        b.1.Disjoint ⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩ := by
    intro s hs b hb'
    have h0 := sp_of_preK hk hb.1 hs
    have hs' := (pre_regs (by omega)).mp (pre_consts.mp hs).1
    obtain ⟨-, -, -, -, hres, -, -⟩ := hs'
    simp only [stripConsts_sp] at hres
    have hbelow : below s.sp (stack + bytes) ∈ stackBelow s.sp (stack + bytes) := by
      rw [stackBelow_pos _ (by omega)]; simp
    have hscrSub : Region.Sub ⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩ (below s.sp (stack + bytes)) :=
      Offset.sub_below _ (by omega) (by have := hb.2.2.2; omega)
    exact (Region.Disjoint.symm (hres _ hbelow b (List.mem_append_left _ hb'))).sub_right hscrSub
  -- Every run is the code's run from `narrow`, then the wipe.
  have hrun : ∀ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)).pre s → ∃ t s₃ s₄,
      Exec isa c (narrow sig e n bytes s) t s₃ ∧
      (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack).post
        (narrow sig e n bytes s) s₃ ∧
      Frame [⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩] s₃.mem s₄.mem ∧
      s₃.sp = s.sp - BitVec.ofNat 64 bytes ∧
      Exec isa (withStackScratchWiped bytes (argRegs.getD (sig.words abi.ptrBits).length .x0) words c) s
        (t ++ wipeTrace s₃.sp words) (popState bytes s s₄) ∧
      abiPreserved s (popState bytes s s₄) ∧ (popState bytes s s₄).mem = s₄.mem ∧
      (popState bytes s s₄).gpr .x0 = s₃.gpr .x0 := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrowK_pre hk hb hs)
    have hsp₃ : s₃.sp = s.sp - BitVec.ofNat 64 bytes := ha.2.1.trans (narrow_sp s)
    have hwr₃ : s₃.wr = (narrow sig e n bytes s).wr := (Exec.rdwr he).2.1
    have h0 := sp_of_preK hk hb.1 hs
    obtain ⟨m', hblk, hfr⟩ := wipe_run ⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩ s₃ words
      (by rw [hwr₃, narrow_wr]; simp) (by have := hb.2.2.2; omega)
      (fun k hk' => by
        rw [hsp₃]; exact Offset.contains_base _ (by omega) (by have := hb.2.2.2; omega))
    have he' := Exec.seq he (Exec.block hblk)
    have ha' : abiPreserved (narrow sig e n bytes s) { ((s₃.write .x .x16 (s₃.sp + BitVec.ofNat 64 0)).write
        .x .x17 ((0 : BitVec 16).setWidth 64 <<< (16 * 0))) with mem := m' } := by
      refine ⟨fun q hq => ?_, ha.2.1, ha.2.2⟩
      have h16 : q ≠ .x16 := by rintro rfl; simp [preserved] at hq
      have h17 : q ≠ .x17 := by rintro rfl; simp [preserved] at hq
      simp only [State.write, h16, h17, ↓reduceIte]
      exact ha.1 q hq
    obtain ⟨hex, habi, hm, hg⟩ := withStackScratchK_run hk hb h0 he' ha'
    refine ⟨t, s₃, _, he, hq, hfr, hsp₃, hex, habi, hm, ?_⟩
    rw [hg]; simp [State.write]
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, s₄, -, hq, hfr, -, hex, ha, hm, hx0⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    refine post_consts.mpr ((post_regs (by omega)).mpr ?_)
    have hq' := (post_regs (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
      (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega)).mp (post_consts.mp hq)
    rw [narrow_regArgs hk] at hq'
    rw [hm, hx0]
    have h₃ := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params
      post _ _ (hlen s (by omega))) s.mem) s₃.mem) _) hq'
    refine hpost _ _ _ _ _ (hlen s (by omega)) (fun b hb' a ha' => ?_) h₃
    exact (hfr a fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdisj s hs b hb' a ha').symm
  · obtain ⟨u₁, _, _, f₁, _, _, p₁, x₁, _⟩ := hrun s₁ h₁
    obtain ⟨u₂, _, _, f₂, _, _, p₂, x₂, _⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, p₁, p₂]
    obtain ⟨hp', hsy⟩ := pub_consts.mp hp
    have hsp₁₂ : s₁.sp = s₂.sp := ((pub_regs (by omega)).mp hp').1.1
    rw [hct _ _ _ _ _ _ (narrowK_pre hk hb h₁) (narrowK_pre hk hb h₂)
      (pub_consts.mpr ⟨narrow_pub hk hp', fun c hc => hsy c hc⟩) f₁ f₂, hsp₁₂]

end

end VG.AArch64
