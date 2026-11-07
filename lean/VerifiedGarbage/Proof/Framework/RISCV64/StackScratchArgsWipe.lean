module

public import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchArgs
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Offset

/-!
# A scratch buffer on the stack, for a function with stack arguments, wiped after use (RISC-V)

`Verified.stackScratchArgsWiped`: `Verified.stackScratchArgs` for
`withStackScratchArgsWiped`, which zeroes the first `words` doublewords of
the buffer after the code, as `Verified.stackScratchWiped` is
`Verified.stackScratchL` for `withStackScratchWiped`. The wipe runs with the
permissions of the contract with the buffer (`narrowA`), which may write the
buffer, so `withStackScratchArgs_run` gives the run of the code followed by
the wipe; the wipe writes only the buffer, which is in the frame, apart from
the function's buffers, so the postcondition holds after it if it reads the
memory on return only within them (`hpostOut`, which may assume the precondition).
-/

@[expose] public section

namespace VG.RISCV64

open VG.Impl.StackScratch.RISCV64

/-- `wipeFrom off words` from `u`, with the `words` doublewords at
`sp + off` in the region `R`, which `u` may write: `wipe_run` from an
offset. -/
theorem wipeFrom_run (R : Region) (u : State) (off words : Nat) (hoff : off < 2048) (hR : R ∈ u.wr)
    (hal : (u.sp + BitVec.ofNat 64 off).toNat % 8 = 0)
    (hc : ∀ k < words, R.Contains (u.sp + BitVec.ofNat 64 off + BitVec.ofNat 64 (8 * k)) 8) :
    ∃ u', execBlock isa (wipeFrom off words) u =
        some (u', wipeTrace (u.sp + BitVec.ofNat 64 off) words) ∧
      Frame [R] u.mem u'.mem ∧ (∀ r, r ≠ .t5 → r ≠ .t6 → u'.gpr r = u.gpr r) ∧ u'.sp = u.sp ∧
      u'.rd = u.rd ∧ u'.wr = u.wr := by
  have h5 : ((u.write .t5 (u.sp + BitVec.ofNat 64 off)).write .t6 (BitVec.ofInt 64 0)).gpr .t5 =
      u.sp + BitVec.ofNat 64 off := by
    simp [State.write]
  obtain ⟨u', he, hf, ho, sp', rd', wr'⟩ := wipeChunks_run R (words / 256) words
    ((u.write .t5 (u.sp + BitVec.ofNat 64 off)).write .t6 (BitVec.ofInt 64 0))
    (by simpa [State.write]) (by rw [h5]; exact hal) (by omega) (by rw [h5]; exact hc)
  refine ⟨u', ?_, by simpa [State.write] using hf, fun r h5' h6 => ?_, by rw [sp']; rfl,
    by rw [rd']; rfl, by rw [wr']; rfl⟩
  · simp only [wipeFrom, execBlock, isa, exec, hoff, ↓reduceIte]
    simp only [show imm12 (0 : Int) = true by decide, ↓reduceIte, Option.map_some, he, h5, addrs,
      List.map_nil, List.nil_append]
  · rw [ho r h5']; simp [State.write, h5', h6]

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes m : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- The buffer in the frame. -/
abbrev bufA (e : Elem) (n bytes m : Nat) (s : State) : Region :=
  ⟨s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 + 8 * m), n * e.size⟩

/-- The function's buffers are apart from the frame's buffer. -/
theorem bufs_disj_bufA (hk : (sig.words abi.ptrBits).length = 8 + m)
    (hl : Sig.noLists sig.params = true) (hb : FitsA m bytes e n) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) :
    ∀ b ∈ Sig.bufs sig.params (stkArgs m s), b.1.Disjoint (bufA e n bytes m s) := by
  rw [pre_stk hk hl] at hs
  obtain ⟨⟨-, hst, -⟩, -, -, -, hres, -, -⟩ := hs
  have hbelow : below s.sp (stack + bytes) ∈ stackBelow s.sp (stack + bytes) := by
    rw [stackBelow_pos _ (by omega_using [hb.1])]; simp
  intro b hb'
  exact ((Region.Disjoint.symm (hres _ hbelow b (List.mem_append_left _ hb'))).sub_right
    (Offset.sub_below _ (a := bytes) (n := bytes) (by omega_using []) (by omega_using []))).sub_right
    (Offset.sub_base _ (by omega_using [hb.1]))

/-- `Verified.stackScratchArgs` for `withStackScratchArgsWiped`, which
zeroes the first `words` doublewords of the buffer after the code, if the
postcondition reads the memory on return only within the function's buffers
when the precondition holds (`hpostOut`). -/
theorem Verified.stackScratchArgsWiped {c : Prog isa} {words : Nat}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack leak))
    (hk : (sig.words abi.ptrBits).length = 8 + m) (hb : FitsA m bytes e n)
    (hoff : 8 + 8 * m < 2048) (hw : 8 * words ≤ n * e.size)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hpostOut : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      Curry.apply (sig.words abi.ptrBits) pre vs m →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true := by decide)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) :
    Verified target (withStackScratchArgsWiped bytes m words c)
      (sig.contract abi pre post wa (stack + bytes) leak) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hk' : ((sig.withScratch nm e n).words abi.ptrBits).length = 8 + (m + 1) := by
    rw [Sig.words_withScratch, List.length_append, List.length_singleton, hk]; omega_using []
  have hlen : ∀ s, (stkArgs m s).length = (sig.words abi.ptrBits).length := fun s => by
    rw [stkArgs_length, hk]
  -- Every run is the `alloc` and `setArgs`, the code's run from `narrowA`, then the wipe.
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s → ∃ t s₃ s₄,
      Exec isa c (narrowA sig e n bytes m s) t s₃ ∧
      (Sig.scratchContract abi sig nm e n pre post wa stack leak).post (narrowA sig e n bytes m s) s₃ ∧
      Frame [bufA e n bytes m s] s₃.mem s₄.mem ∧
      Exec isa (withStackScratchArgsWiped bytes m words c) s
        (setArgsTrace bytes (s.sp - BitVec.ofNat 64 bytes) m ++
          (t ++ wipeTrace (s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 + 8 * m)) words))
        (popState bytes s s₄) ∧
      abiPreserved s (popState bytes s s₄) ∧ (popState bytes s s₄).mem = s₄.mem ∧
      (popState bytes s s₄).gpr .a0 = s₃.gpr .a0 := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrowA_pre hk hl hb hpre hs)
    obtain ⟨hspA, -, -, -⟩ := narrowA_facts (e := e) (n := n) hk hl hb hs
    have hsp₃ : s₃.sp = s.sp - BitVec.ofNat 64 bytes := ha.2.1.trans hspA
    have hwr₃ : s₃.wr = (narrowA sig e n bytes m s).wr := (Exec.rdwr he).2.1
    have hs' := hs
    rw [pre_stk hk hl] at hs'
    obtain ⟨⟨hal, hst, -⟩, -⟩ := hs'
    have hsb : stack + bytes ≤ s.sp.toNat := by rcases hst with h | h <;> omega_using [h, hb.1]
    have hEal : (s.sp - BitVec.ofNat 64 bytes).toNat % 8 = 0 := by
      rw [toNat_sub_ofNat' (by omega_using [hsb])]; omega_using [hal, hb.2.2]
    obtain ⟨u', hblk, hfr, hu', hsp', -⟩ := wipeFrom_run (bufA e n bytes m s) s₃ (8 + 8 * m) words hoff
      (by rw [hwr₃]; simp [narrowA, oldRegions, State.withRegions])
      (by rw [hsp₃]; exact Spill.al8 hEal (by omega_using []))
      (fun k hk'' => by
        rw [hsp₃]
        exact Offset.contains_base _ (by omega_using [hw, hk'']) (by omega_using [hb.1, hw, hk'', hsb]))
    have he' := Exec.seq he (Exec.block hblk)
    have ha' : abiPreserved (narrowA sig e n bytes m s) u' := by
      refine ⟨fun q hq => ?_, hsp'.trans ha.2.1, ?_⟩
      · have h5 : q ≠ .t5 := by rintro rfl; simp [preserved] at hq
        have h6 : q ≠ .t6 := by rintro rfl; simp [preserved] at hq
        rw [hu' q h5 h6]
        exact ha.1 q hq
      · rw [hu' _ (by decide) (by decide)]
        exact ha.2.2
    obtain ⟨hex, habi, hm, hg⟩ := withStackScratchArgs_run hk hl hb hs he' ha'
    refine ⟨t, s₃, u', he, hq, hfr, ?_, habi, hm, ?_⟩
    · rw [hsp₃] at hex; exact hex
    · rw [hg]; exact hu' _ (by decide) (by decide)
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, s₄, -, hq, hfr, hex, ha, hm, hr0⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_stk hk]
    have hq' := (post_stk (sig := sig.withScratch nm e n) (m := m + 1)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post) hk').mp hq
    obtain ⟨-, -, hargs, -⟩ := narrowA_facts (e := e) (n := n) hk hl hb hs
    rw [hargs] at hq'
    rw [hm, hr0]
    have hq'' := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n
      sig.params post _ _ (hlen s)) _) s₃.mem) _) hq'
    have h₃ := hpost _ _ _ _ _ (hlen s) (narrowA_agree hk hl hb hs) hq''
    have hpr : Curry.apply (sig.words abi.ptrBits) pre (stkArgs m s) s.mem := by
      have hs' := hs
      rw [pre_stk hk hl] at hs'
      exact hs'.2.2.2.2.2.2.1
    refine hpostOut _ _ _ _ _ (hlen s) hpr (fun b hb' a ha' => ?_) h₃
    exact (hfr a fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact bufs_disj_bufA hk hl hb hs b hb' a ha').symm
  · obtain ⟨u₁, r₁, _, f₁, -, -, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨u₂, r₂, _, f₂, -, -, x₂, -⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, ((pubL_stk hk hl).mp hp).1.1,
      hct _ _ _ _ _ _ (narrowA_pre hk hl hb hpre h₁) (narrowA_pre hk hl hb hpre h₂)
        (narrowA_pub hk hl hb h₁ h₂ hp hleak) f₁ f₂]

end

end VG.RISCV64
