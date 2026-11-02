module

public import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A scratch buffer on the stack, for code that reads tables of constants (RISC-V)

As on PPC64LE (`Proof/Framework/PPC64LE/StackScratchConsts.lean`).
`Verified.stackScratchWipedC`: `Verified.stackScratchWiped` for contracts
under `abi.withConsts K`, whose readable regions end with the tables `K`.
The frame and the state the code runs from (`narrow`) are those of
`Verified.stackScratchWiped`. Without its tables, a state satisfying the
contract under `abi.withConsts K` satisfies it under `abi` (`pre_consts`),
so the lemmas of `StackScratch.lean` apply to it; `narrow` keeps the
readable regions, the memory and the statics' addresses, and the tables lie
outside the buffer, which is within the stack the contract reserves
(`narrowK_pre`). The run of the frame is `withStackScratch_runSp`, which
needs of the entry state only that the frame fits below its stack pointer.
-/

@[expose] public section

namespace VG.RISCV64

open VG.Impl.StackScratch.RISCV64

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

/-- The precondition under `abi.withConsts` gives the one with the buffer in
`narrow`: the tables, apart from the buffer, are as they were. -/
theorem narrowK_pre (hk : (sig.words abi.ptrBits).length < 8)
    (hb : 0 < bytes ∧ bytes ≤ 4064 ∧ bytes % 16 = 0 ∧ n * e.size ≤ bytes)
    (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)).pre s) :
    (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack).pre
      (narrow sig e n bytes s) := by
  obtain ⟨hs', hdr, hd, ht, hal⟩ := pre_consts.mp hs
  have hn := narrow_pre (nm := nm) hk hb hs' hl
  have hR := reserved_below (stack := stack) (bytes := bytes) (by omega_using [hb]) s
  refine pre_consts.mpr ⟨by rw [stripConsts_narrow]; exact hn, hdr, hd,
    fun t ht' => ⟨(ht t ht').1, ?_, ?_⟩, hal⟩
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

/-- Code verified for a function whose last argument, in a register, is a
scratch buffer, and which reads the tables `c₀ :: cs`, is verified for the
function without it (`Verified.stackScratchWiped`, under
`abi.withConsts (c₀ :: cs)`). -/
theorem Verified.stackScratchWipedC {c : Prog isa}
    (h : Verified target c (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack))
    (hk : (sig.words abi.ptrBits).length < 8)
    (hb : 0 < bytes ∧ bytes ≤ 4064 ∧ bytes % 16 = 0 ∧ n * e.size ≤ bytes)
    (hw : 8 * words ≤ n * e.size)
    (hpostOut : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r)
    (hsat : ∃ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true := by decide) :
    Verified target (withStackScratchWiped bytes (scratchReg sig) words c)
      (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hlen := regArgs_length sig
  -- The buffer, below the stack the contract without it reserves, so apart
  -- from the function's buffers.
  have hdisj : ∀ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)).pre s →
      ∀ b ∈ Sig.bufs sig.params (regArgs sig s),
        b.1.Disjoint ⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩ := by
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
      Frame [⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩] s₃.mem s₄.mem ∧
      s₃.sp = s.sp - BitVec.ofNat 64 bytes ∧
      Exec isa (withStackScratchWiped bytes (scratchReg sig) words c) s
        (t ++ wipeTrace s₃.sp words) (popState bytes s s₄) ∧
      abiPreserved s (popState bytes s s₄) ∧ (popState bytes s s₄).mem = s₄.mem ∧
      (popState bytes s s₄).gpr .a0 = s₃.gpr .a0 := by
    intro s hs
    have hs' := (pre_regs (by omega_using [hk]) hl).mp (pre_consts.mp hs).1
    have hal : s.sp.toNat % 16 = 0 := hs'.1.1
    have hwf : stack + bytes = 0 ∨ stack + bytes ≤ s.sp.toNat := hs'.1.2
    have hsb : bytes ≤ s.sp.toNat := by rcases hwf with h | h <;> omega_using [h, hb]
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrowK_pre hk hb hl hs)
    have hsp₃ : s₃.sp = s.sp - BitVec.ofNat 64 bytes := ha.2.1.trans (narrow_sp s)
    have hwr₃ : s₃.wr = (narrow sig e n bytes s).wr := (Exec.rdwr he).2.1
    obtain ⟨u', hblk, hfr, hu', hsp', -⟩ := wipe_run ⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩ s₃ words
      (by rw [hwr₃, narrow_wr]; simp)
      (by rw [hsp₃, toNat_sub_ofNat' hsb]; omega_using [hal, hb])
      (fun k hk' => by
        rw [hsp₃]; exact Offset.contains_base _ (by omega_using [hw, hk']) (by omega_using [hb, hw, hk']))
    have he' := Exec.seq he (Exec.block hblk)
    have ha' : abiPreserved (narrow sig e n bytes s) u' := by
      refine ⟨fun q hq => ?_, hsp'.trans ha.2.1, ?_⟩
      · have h5 : q ≠ .t5 := by rintro rfl; simp [preserved] at hq
        have h6 : q ≠ .t6 := by rintro rfl; simp [preserved] at hq
        rw [hu' q h5 h6]
        exact ha.1 q hq
      · rw [hu' _ (by decide) (by decide)]
        exact ha.2.2
    obtain ⟨hex, habi, hm, hg⟩ := withStackScratch_runSp hk hb hsb he' ha'
    refine ⟨t, s₃, _, he, hq, hfr, hsp₃, hex, habi, hm, ?_⟩
    rw [hg]; exact hu' _ (by decide) (by decide)
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, s₄, -, hq, hfr, -, hex, ha, hm, hr0⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    refine post_consts.mpr ((post_regs (by omega_using [hk])).mpr ?_)
    have hq' := (post_regs (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
      (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega_using [hk])).mp
      (post_consts.mp hq)
    rw [narrow_regArgs hk] at hq'
    rw [hm, hr0]
    have h₃ := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params
      post _ _ (hlen s (by omega_using [hk]))) _) s₃.mem) _) hq'
    -- The memory on return: after the wipe, which writes only the buffer.
    refine hpostOut _ _ _ _ _ (hlen s (by omega_using [hk])) (fun b hb' a ha' => ?_) h₃
    exact (hfr a fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdisj s hs b hb' a ha').symm
  · obtain ⟨u₁, _, _, f₁, _, _, p₁, x₁, _⟩ := hrun s₁ h₁
    obtain ⟨u₂, _, _, f₂, _, _, p₂, x₂, _⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, p₁, p₂]
    obtain ⟨hp', hsy⟩ := pub_consts.mp hp
    have hsp₁₂ : s₁.sp = s₂.sp := ((pub_regs (by omega_using [hk]) hl).mp hp').1
    rw [hct _ _ _ _ _ _ (narrowK_pre hk hb hl h₁) (narrowK_pre hk hb hl h₂)
      (pub_consts.mpr ⟨narrow_pub hk hp' hl, fun c hc => hsy c hc⟩) f₁ f₂, hsp₁₂]

end

end VG.RISCV64
