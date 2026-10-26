module

import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch

/-!
# A scratch buffer on the stack, for code that reads tables of constants (PPC64LE)

As on AArch64 (`Proof/Framework/AArch64/StackScratchConsts.lean`).
`Verified.stackScratchWipedC`: `Verified.stackScratchWiped` for contracts
under `abi.withConsts K`, whose readable regions end with the tables `K`.
The frame and the state the code runs from (`narrow`) are those of
`Verified.stackScratchWiped`. Without its tables, a state satisfying the
contract under `abi.withConsts K` satisfies it under `abi` (`pre_consts`),
so the lemmas of `StackScratch.lean` apply to it; `narrow` keeps the
readable regions and the statics' addresses, and the tables lie outside the
frame, which is within the stack the contract reserves, so the push of the
frame's back chain leaves them as they were (`narrowK_pre`). The run of the
frame (`withStackScratchK_run`) is `withStackScratch_run`'s, which needs of
the entry state only that the contract reserves the frame's stack.
-/

@[expose] public section

namespace VG.PPC64LE

open VG.Impl.StackScratch.PPC64LE

section
variable {K : List (String × List (BitVec 64))} {sig : Sig}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {st : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- A postcondition under `abi` does not read the readable regions. -/
theorem post_stripConsts {s s' : State} :
    (sig.contract abi pre post wa st leak).post (stripConsts K s) s' ↔
      (sig.contract abi pre post wa st leak).post s s' := by
  dsimp only [Sig.contract]
  cases h : abi.args ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) with
  | none => simp
  | some vals => dsimp only; rw [args_stripConsts h]; exact Iff.rfl

/-- Nor does what is public. -/
theorem pub_stripConsts {s₁ s₂ : State} :
    (sig.contract abi pre post wa st leak).pub (stripConsts K s₁) (stripConsts K s₂) ↔
      (sig.contract abi pre post wa st leak).pub s₁ s₂ := by
  dsimp only [Sig.contract]
  cases h : abi.args ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) with
  | none => simp
  | some vals => dsimp only; rw [args_stripConsts h, args_stripConsts h]; exact Iff.rfl

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
theorem sp_of_preK (hk : (sig.words abi.ptrBits).length < 8) (hl : Sig.noLists sig.params = true)
    {s : State} (hs : (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)).pre s) :
    stack + bytes ≤ s.sp.toNat := by
  have hwf := ((pre_regs (by omega_using [hk]) hl).mp (pre_consts.mp hs).1).1
  simp only [stripConsts_sp] at hwf
  rcases hwf with h | h <;> omega_using [h]

/-- The precondition under `abi.withConsts` gives the one with the buffer in
`narrow`: the tables, apart from the frame, still hold after its push. -/
theorem narrowK_pre (hk : (sig.words abi.ptrBits).length < 8)
    (hb : 32 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0 ∧ n * e.size + 32 ≤ bytes)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)).pre s) :
    (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack).pre
      (narrow sig e n bytes s) := by
  obtain ⟨hs', hdr, hd, ht, hal⟩ := pre_consts.mp hs
  have hn := narrow_pre (nm := nm) hk hb hpre hs' hl
  have hR := reserved_below (stack := stack) (bytes := bytes) (by omega_using [hb]) s
  refine pre_consts.mpr ⟨by rw [stripConsts_narrow]; exact hn, hdr, ?_, fun t ht' => ⟨(ht t ht').1, ?_, ?_⟩, hal⟩
  · -- The push writes only the back chain, in the reserved stack.
    intro c hc i hi
    rw [narrow_mem, narrow_syms, ← hd c hc i hi]
    refine Mem.readW_congr fun j hj => ?_
    have hT : (⟨s.syms c.1, 8 * c.2.length⟩ : Region) ∈ constRegs (c₀ :: cs) s :=
      List.mem_map_of_mem (f := fun c => (⟨s.syms c.1, 8 * c.2.length⟩ : Region)) hc
    have hfit := (ht _ hT).1
    have hD := ((ht _ hT).2.2 _ hR).sub_right (frame_sub (stack := stack) s hb.1)
    have hf : Frame [⟨s.sp - BitVec.ofNat 64 bytes, 8⟩] s.mem
        (s.mem.write (s.sp - BitVec.ofNat 64 bytes) 8 s.sp) :=
      Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
    refine hf _ fun r hr hc' => ?_
    simp only [List.mem_singleton] at hr; subst hr
    refine hD _ ?_ hc'
    rw [Offset.add_add]
    exact Offset.contains_base _ (by omega_using [hi, hj]) (by simp only [abi] at hfit; omega_using [hi, hj, hfit])
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact (ht t ht').2.1 r hr
    · simp only [List.mem_singleton] at hr; subst hr
      exact ((ht t ht').2.2 _ hR).sub_right (buf_sub (stack := stack) s hb.2.2.2)
  · intro r hr
    have hr' : r ∈ stackBelow (s.sp - BitVec.ofNat 64 bytes) stack := hr
    rcases Nat.eq_zero_or_pos stack with h0 | h0
    · subst h0; simp [stackBelow] at hr'
    · rw [stackBelow_pos _ h0, List.mem_singleton] at hr'; subst hr'
      exact ((ht t ht').2.2 _ hR).sub_right (below_below _ bytes stack)

/-- `withStackScratch_run`, from the fact about the entry state it needs: the
stack the contract reserves. -/
theorem withStackScratchK_run {c : Prog isa} (hk : (sig.words abi.ptrBits).length < 8)
    (hb : 32 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0 ∧ n * e.size + 32 ≤ bytes) {s : State}
    (hsb : stack + bytes ≤ s.sp.toNat) {t : List Leak} {s₃ : State}
    (he : Exec isa c (narrow sig e n bytes s) t s₃) (ha : abiPreserved (narrow sig e n bytes s) s₃) :
    Exec isa (withStackScratch bytes (argRegs.getD (sig.words abi.ptrBits).length .r3) c) s
        (.addr (s.sp - BitVec.ofNat 64 bytes) :: t) (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr = s₃.gpr := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := hb
  obtain ⟨hr2, -⟩ := argRegs_scratch _ hk
  have hpush : isa.push (.alloc bytes) s = some (allocated bytes s) := by
    simp only [isa, push, allocated]
    exact ite_eq_left ⟨hb0, hb1, hb2, by omega⟩
  have hblk : Exec isa (.block [.addSp (argRegs.getD (sig.words abi.ptrBits).length .r3) 32])
      (allocated bytes s) [] (scratchState sig bytes s) :=
    .block (by simp only [execBlock, isa, exec, show (32 : Nat) < 2 ^ 15 by decide, ite_true,
      Option.map_some, addrs, List.map_nil, List.append_nil, scratchState]; rfl)
  have hcov : Covers (s.wr ++ [⟨s.sp - BitVec.ofNat 64 bytes + 32, n * e.size⟩])
      (frameR bytes s :: s.wr) :=
    Covers.append_left (Covers.of_mem fun r hr => List.mem_cons_of_mem _ hr)
      (Covers.one ⟨_, List.mem_cons_self .., Region.contains_self' (by omega)⟩)
  have hw := Exec.widen he (rd := s.rd) (wr := frameR bytes s :: s.wr)
    (by simpa using Covers.append (Covers.refl s.rd) hcov) (by simpa using hcov)
  rw [show (narrow sig e n bytes s).withRegions s.rd (frameR bytes s :: s.wr) =
      scratchState sig bytes s from rfl] at hw
  have hsp₃ : s₃.sp = s.sp - BitVec.ofNat 64 bytes := ha.2.1.trans (narrow_sp s)
  have hpop : isa.pop (.free bytes) (allocated bytes s)
      (s₃.withRegions s.rd (frameR bytes s :: s.wr)) = some (popState bytes s s₃) := by
    simp only [isa, pop, State.withRegions, allocated, hsp₃, List.head?_cons, List.tail_cons, hb0,
      hb1, hb2, and_self, ite_true, BitVec.sub_add_cancel]
    rfl
  have hex := Exec.frame hpush (Exec.seq hblk hw) hpop
  simp only [isa, addrs, List.map_cons, List.map_nil, List.nil_append, List.append_nil,
    List.cons_append] at hex
  refine ⟨hex, ⟨fun q hq => ?_, rfl, ?_⟩, rfl, rfl⟩
  · have hqr : q ≠ argRegs.getD (sig.words abi.ptrBits).length .r3 := fun h => hr2 (h ▸ hq)
    show s₃.gpr q = s.gpr q
    rw [ha.1 q hq, narrow_gpr]
    simp only [hqr, ↓reduceIte]
  · show s₃.lr = s.lr
    rw [ha.2.2, narrow_lr]

/-- Code verified for a function whose last argument, in a register, is a
scratch buffer, and which reads the tables `c₀ :: cs`, is verified for the
function without it (`Verified.stackScratchWiped`, under
`abi.withConsts (c₀ :: cs)`). -/
theorem Verified.stackScratchWipedC {c : Prog isa}
    (h : Verified target c (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack))
    (hk : (sig.words abi.ptrBits).length < 8)
    (hb : 32 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0 ∧ n * e.size + 32 ≤ bytes)
    (hw : 8 * words ≤ n * e.size)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hpostOut : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r)
    (hsat : ∃ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true := by decide) :
    Verified target
      (withStackScratchWiped bytes (argRegs.getD (sig.words abi.ptrBits).length .r3) words c)
      (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hlen := regArgs_length sig
  -- The buffer, below the stack the contract without it reserves, so apart
  -- from the function's buffers.
  have hdisj : ∀ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)).pre s →
      ∀ b ∈ Sig.bufs sig.params (regArgs sig s),
        b.1.Disjoint ⟨s.sp - BitVec.ofNat 64 bytes + 32, n * e.size⟩ := by
    intro s hs b hb'
    have hs' := (pre_regs (by omega_using [hk]) hl).mp (pre_consts.mp hs).1
    obtain ⟨-, -, -, -, hres, -, -⟩ := hs'
    simp only [stripConsts_sp] at hres
    have hbelow : below s.sp (stack + bytes) ∈ stackBelow s.sp (stack + bytes) := by
      rw [stackBelow_pos _ (by omega_using [hb])]; simp
    exact ((hres _ hbelow b hb').sub_left (buf_sub (stack := stack) s hb.2.2.2)).symm
  -- Every run is the code's run from `narrow`, then the wipe.
  have hrun : ∀ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)).pre s →
      ∃ t s₃ s₄, Exec isa c (narrow sig e n bytes s) t s₃ ∧
      (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack).post
        (narrow sig e n bytes s) s₃ ∧
      Frame [⟨s.sp - BitVec.ofNat 64 bytes + 32, n * e.size⟩] s₃.mem s₄.mem ∧
      s₃.sp = s.sp - BitVec.ofNat 64 bytes ∧
      Exec isa (withStackScratchWiped bytes (argRegs.getD (sig.words abi.ptrBits).length .r3) words c) s
        (.addr (s.sp - BitVec.ofNat 64 bytes) :: (t ++ wipeTrace (s₃.sp + 32) words))
        (popState bytes s s₄) ∧
      abiPreserved s (popState bytes s s₄) ∧ (popState bytes s s₄).mem = s₄.mem ∧
      (popState bytes s s₄).gpr .r3 = s₃.gpr .r3 := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrowK_pre hk hb hpre hl hs)
    have hsp₃ : s₃.sp = s.sp - BitVec.ofNat 64 bytes := ha.2.1.trans (narrow_sp s)
    have hwr₃ : s₃.wr = (narrow sig e n bytes s).wr := (Exec.rdwr he).2.1
    obtain ⟨m', hblk, hfr⟩ := wipe_run ⟨s.sp - BitVec.ofNat 64 bytes + 32, n * e.size⟩ s₃ words
      (by rw [hwr₃, narrow_wr]; simp) (by omega_using [hb, hw])
      (fun k hk' => by
        rw [hsp₃]; exact Offset.contains_base _ (by omega_using [hw, hk']) (by omega_using [hb, hw, hk']))
    have he' := Exec.seq he (Exec.block hblk)
    have ha' : abiPreserved (narrow sig e n bytes s)
        { ((s₃.write .r12 (s₃.sp + BitVec.ofNat 64 32)).write .r11 (BitVec.ofNat 64 0)) with mem := m' } := by
      refine ⟨fun q hq => ?_, ha.2.1, ha.2.2⟩
      have h12 : q ≠ .r12 := by rintro rfl; simp [preserved] at hq
      have h11 : q ≠ .r11 := by rintro rfl; simp [preserved] at hq
      simp only [State.write, h12, h11, ↓reduceIte]
      exact ha.1 q hq
    obtain ⟨hex, habi, hm, hg⟩ := withStackScratchK_run hk hb (sp_of_preK hk hl hs) he' ha'
    refine ⟨t, s₃, _, he, hq, hfr, hsp₃, hex, habi, hm, ?_⟩
    rw [hg]; simp [State.write]
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, s₄, -, hq, hfr, -, hex, ha, hm, hr3⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    refine post_consts.mpr ((post_regs (by omega_using [hk])).mpr ?_)
    have hq' := (post_regs (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
      (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega_using [hk])).mp
      (post_consts.mp hq)
    rw [narrow_regArgs hk] at hq'
    rw [hm, hr3]
    have h₃ := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params
      post _ _ (hlen s (by omega_using [hk]))) _) s₃.mem) _) hq'
    -- The memory on entry: `narrow`'s, which differs from `s`'s only in the frame's header.
    have h₄ := hpost _ _ _ _ _ (hlen s (by omega_using [hk]))
      (fun b hb' a ha' => (narrow_agree (e := e) (n := n) hk hb.1 (pre_consts.mp hs).1 hl b hb' a ha').symm) h₃
    -- The memory on return: after the wipe, which writes only the buffer.
    refine hpostOut _ _ _ _ _ (hlen s (by omega_using [hk])) (fun b hb' a ha' => ?_) h₄
    exact (hfr a fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdisj s hs b hb' a ha').symm
  · obtain ⟨u₁, _, _, f₁, _, _, p₁, x₁, _⟩ := hrun s₁ h₁
    obtain ⟨u₂, _, _, f₂, _, _, p₂, x₂, _⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, p₁, p₂]
    obtain ⟨hp', hsy⟩ := pub_consts.mp hp
    have hsp₁₂ : s₁.sp = s₂.sp := ((pub_regs (by omega_using [hk]) hl).mp hp').1
    rw [hct _ _ _ _ _ _ (narrowK_pre hk hb hpre hl h₁) (narrowK_pre hk hb hpre hl h₂)
      (pub_consts.mpr ⟨narrow_pub hk hp' hl, fun c hc => hsy c hc⟩) f₁ f₂, hsp₁₂]

end

end VG.PPC64LE
