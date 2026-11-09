module

public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchArgs
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# A scratch buffer on the stack, for a function with stack arguments, wiped after use (PPC64LE)

`Verified.stackScratchArgsWiped`: `Verified.stackScratchArgs` for
`withStackScratchArgsWiped`, which zeroes the first `words` doublewords of
the buffer after the code, as `Verified.stackScratchWiped` is
`Verified.stackScratch` for `withStackScratchWiped`. The wipe runs with the
permissions of the contract with the buffer (`narrowA`), which may write the
buffer, so `withStackScratchArgs_run` gives the run of the code followed by
the wipe; the wipe writes only the buffer, which is in the frame, apart from
the function's buffers, so the postcondition holds after it if it reads the
memory on return only within them (`hpostOut`, which may assume the
precondition). The same structure as RISC-V's
(`Proof/Framework/RISCV64/StackScratchArgsWipe.lean`).
-/

@[expose] public section

namespace VG.PPC64LE

open VG.Impl.StackScratch.PPC64LE

/-- `wipeFrom off words` from `u`, with the `words` doublewords at
`r1 + off` in the region `R`, which `u` may write: `wipe_run` from an
offset. -/
theorem wipeFrom_run (R : Region) (u : State) (off words : Nat) (hoff : off < 2 ^ 15) (hR : R ∈ u.wr)
    (hwb : 8 * words ≤ 4096)
    (hc : ∀ k < words, R.Contains (u.sp + BitVec.ofNat 64 off + BitVec.ofNat 64 (8 * k)) 8) :
    ∃ u', execBlock isa (wipeFrom off words) u = some (u', wipeTrace (u.sp + BitVec.ofNat 64 off) words) ∧
      Frame [R] u.mem u'.mem ∧ (∀ r, r ≠ .r12 → r ≠ .r11 → u'.gpr r = u.gpr r) ∧ u'.sp = u.sp ∧
      u'.lr = u.lr ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  have h12 : ((u.write .r12 (u.sp + BitVec.ofNat 64 off)).write .r11 (BitVec.ofNat 64 0)).gpr .r12 =
      u.sp + BitVec.ofNat 64 off := by
    simp [State.write]
  obtain ⟨m', he, hf⟩ := wipeStores_run R ((u.write .r12 (u.sp + BitVec.ofNat 64 off)).write .r11
      (BitVec.ofNat 64 0)) (by simpa [State.write]) words hwb (by rw [h12]; exact hc)
  refine ⟨{ ((u.write .r12 (u.sp + BitVec.ofNat 64 off)).write .r11 (BitVec.ofNat 64 0)) with mem := m' },
    ?_, by simpa [State.write] using hf, fun r h₁ h₂ => by simp [State.write, h₁, h₂], rfl, rfl, rfl, rfl⟩
  simp only [wipeFrom, execBlock, isa, exec, hoff, show (0 : Nat) < 2 ^ 15 by decide, ↓reduceIte]
  simp only [Option.map_some, he, h12, addrs, List.map_nil, List.nil_append]

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes m : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- The buffer in the frame. -/
abbrev bufA (e : Elem) (n bytes m : Nat) (s : State) : Region :=
  ⟨s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (104 + 8 * m), n * e.size⟩

/-- The function's buffers are apart from the frame's buffer. -/
theorem bufs_disj_bufA (hk : (sig.words abi.ptrBits).length = 8 + m)
    (hl : Sig.noLists sig.params = true) (hb : FitsA m bytes e n) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) :
    ∀ b ∈ Sig.bufs sig.params (stkArgs m s), b.1.Disjoint (bufA e n bytes m s) := by
  rw [pre_stk hk hl] at hs
  obtain ⟨⟨hst, -⟩, -, -, -, hres, -, -⟩ := hs
  have hsb : stack + bytes ≤ s.sp.toNat := by rcases hst with h | h <;> omega_using [h, hb.1]
  have hbelow : below s.sp (stack + bytes) ∈ stackBelow s.sp (stack + bytes) := by
    rw [stackBelow_pos _ (by omega_using [hb.1])]; simp
  intro b hb'
  have e₁ : s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (104 + 8 * m) =
      s.sp - BitVec.ofNat 64 (bytes - (104 + 8 * m)) := sub_add_ofNat _ (by omega_using [hb.1])
  show b.1.Disjoint ⟨s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (104 + 8 * m), n * e.size⟩
  rw [e₁]
  exact (Region.Disjoint.symm (hres _ hbelow b (List.mem_append_left _ hb'))).sub_right
    (Offset.sub_below _ (by omega_using []) (by omega_using [hb.1]))

/-- `Verified.stackScratchArgs` for `withStackScratchArgsWiped`, which
zeroes the first `words` doublewords of the buffer after the code, if the
postcondition reads the memory on return only within the function's buffers
when the precondition holds (`hpostOut`). -/
theorem Verified.stackScratchArgsWiped {c : Prog isa} {words : Nat}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack leak))
    (hk : (sig.words abi.ptrBits).length = 8 + m) (hb : FitsA m bytes e n)
    (hw : 8 * words ≤ n * e.size)
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
  -- Every run is the push and `setArgs`, the code's run from `narrowA`, then the wipe.
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s → ∃ t s₃ s₄,
      Exec isa c (narrowA sig e n bytes m s) t s₃ ∧
      (Sig.scratchContract abi sig nm e n pre post wa stack leak).post (narrowA sig e n bytes m s) s₃ ∧
      Frame [bufA e n bytes m s] s₃.mem s₄.mem ∧
      Exec isa (withStackScratchArgsWiped bytes m words c) s
        (.addr (s.sp - BitVec.ofNat 64 bytes) :: (setArgsTrace bytes (s.sp - BitVec.ofNat 64 bytes) m ++
          (t ++ wipeTrace (s.sp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (104 + 8 * m)) words)))
        (popState bytes s s₄) ∧
      abiPreserved s (popState bytes s s₄) ∧ (popState bytes s s₄).mem = s₄.mem ∧
      (popState bytes s s₄).gpr .r3 = s₃.gpr .r3 := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrowA_pre hk hl hb hpre hs)
    obtain ⟨hspA, -, -, -, -⟩ := narrowA_facts (e := e) (n := n) hk hl hb hs
    have hsp₃ : s₃.sp = s.sp - BitVec.ofNat 64 bytes := ha.2.1.trans hspA
    have hwr₃ : s₃.wr = (narrowA sig e n bytes m s).wr := (Exec.rdwr he).2.1
    have hs' := hs
    rw [pre_stk hk hl] at hs'
    obtain ⟨⟨hst, -⟩, -⟩ := hs'
    have hsb : stack + bytes ≤ s.sp.toNat := by rcases hst with h | h <;> omega_using [h, hb.1]
    obtain ⟨u', hblk, hfr, hu', hsp', hlr', -⟩ := wipeFrom_run (bufA e n bytes m s) s₃ (104 + 8 * m) words
      (by omega_using [hb.1, hb.2.1])
      (by rw [hwr₃]; simp [narrowA, oldRegions, State.withRegions])
      (by omega_using [hw, hb.1, hb.2.1])
      (fun k hk'' => by
        rw [hsp₃]
        exact Offset.contains_base _ (by omega_using [hw, hk'']) (by omega_using [hb.1, hb.2.1, hw, hk'']))
    have he' := Exec.seq he (Exec.block hblk)
    have ha' : abiPreserved (narrowA sig e n bytes m s) u' := by
      refine ⟨fun q hq => ?_, hsp'.trans ha.2.1, hlr'.trans ha.2.2⟩
      have h12 : q ≠ .r12 := by rintro rfl; simp [preserved] at hq
      have h11 : q ≠ .r11 := by rintro rfl; simp [preserved] at hq
      rw [hu' q h12 h11]
      exact ha.1 q hq
    obtain ⟨hex, habi, hm, hg⟩ := withStackScratchArgs_run hk hl hb hs he' ha'
    refine ⟨t, s₃, u', he, hq, hfr, ?_, habi, hm, ?_⟩
    · rw [hsp₃] at hex; exact hex
    · rw [hg]; exact hu' _ (by decide) (by decide)
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, s₄, -, hq, hfr, hex, ha, hm, hr3⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_stk hk]
    have hq' := (post_stk (sig := sig.withScratch nm e n) (m := m + 1)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post) hk').mp hq
    obtain ⟨-, -, -, hargs, -⟩ := narrowA_facts (e := e) (n := n) hk hl hb hs
    rw [hargs] at hq'
    rw [hm, hr3]
    have hq'' := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n
      sig.params post _ _ (hlen s)) _) s₃.mem) _) hq'
    have h₃ := hpost _ _ _ _ _ (hlen s) (narrowA_agree hk hl hb hs) hq''
    have hpr : Curry.apply (sig.words abi.ptrBits) pre (stkArgs m s) s.mem := by
      have hs' := hs
      rw [pre_stk hk hl] at hs'
      exact hs'.2.2.2.2.2.2
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

end VG.PPC64LE
