module

public import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
public import VerifiedGarbage.Impl.StackScratch.X86.Wiped2

/-!
# A scratch buffer on the stack, zeroed in two places after use (x86)

`Verified.stackScratchWiped2`: as `Verified.stackScratchWiped`, for
`withStackScratchWiped2`, which zeroes the first `a` doublewords of the
buffer and the `b` at its byte `d` after the code (`wipe2_run`): the wipe
stores only into the buffer, within the frame, so the run of the code
followed by the wipe keeps what the calling convention requires and the
return value, and its trace depends only on the stack pointer.
-/

@[expose] public section

namespace VG.X86

open VG.Impl.StackScratch.X86

/-- `wipe2 off a d b` from `u`, with the `a` doublewords at `esp + off` and
the `b` at `esp + off + d` in the region `R`, which `u` may write: it sets
`ecx` to zero and changes memory only in `R`, with a trace of the addresses
alone. -/
theorem wipe2_run (R : Region) (u : State) (off a d b : Nat) (hR : R ∈ u.wr)
    (hc : ∀ k < a, R.Contains ((u.gpr .esp + BitVec.ofNat 32 (off + 4 * k)).setWidth 64) 4)
    (hc' : ∀ k < b, R.Contains ((u.gpr .esp + BitVec.ofNat 32 (off + d + 4 * k)).setWidth 64) 4) :
    ∃ m', execBlock isa (wipe2 off a d b) u =
        some ({ u.setReg .ecx 0 with mem := m' }, wipeTrace (u.gpr .esp) off a ++ wipeTrace (u.gpr .esp) (off + d) b) ∧
      Frame [R] u.mem m' := by
  obtain ⟨m₁, he₁, hf₁⟩ := wipe_run R u off a hR hc
  have hsp : ({ u.setReg .ecx 0 with mem := m₁ } : State).gpr .esp = u.gpr .esp := by simp [State.setReg]
  obtain ⟨m₂, he₂, hf₂⟩ := wipeStores_run R { u.setReg .ecx 0 with mem := m₁ } (by simpa [State.setReg] using hR)
    (off + d) b (by rw [hsp]; exact hc')
  refine ⟨m₂, ?_, hf₁.trans hf₂⟩
  rw [wipe2, execBlock_append, he₁]
  simp only [Option.bind_some]
  rw [he₂, hsp]
  rfl

theorem wipe2_noSp (off a d b : Nat) : NoSp (.block (wipe2 off a d b) : Prog isa) := by
  intro i hi
  simp only [instrs, wipe2, wipe, wipeStores, List.cons_append, List.mem_cons, List.mem_append, List.mem_map,
    List.mem_range] at hi
  rcases hi with rfl | ⟨k, -, rfl⟩ | ⟨k, -, rfl⟩ <;> rfl

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes a d b : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- `Verified.stackScratchWiped`, for `withStackScratchWiped2`, which zeroes
the first `a` doublewords of the buffer and the `b` at its byte `d` after
the code. -/
theorem Verified.stackScratchWiped2 {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack leak))
    (hb : 8 + 4 * slots sig + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 4 = 0)
    (hsp : c.allInstrs (fun i => !Taint.clobbers i .esp) = true) (hd : stackUse c ≤ stack)
    (hw : 4 * a ≤ n * e.size) (hw' : d + 4 * b ≤ n * e.size)
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
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true := by decide)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) :
    Verified target (withStackScratchWiped2 bytes (slots sig) a d b c)
      (sig.contract abi pre post wa (stack + bytes) leak) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hpreL : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂ :=
    fun vs m₁ m₂ hl hb _ => hpre vs m₁ m₂ hl hb
  have hnsp : NoSp c := fun i hi => by
    rw [Code.allInstrs_eq, List.all_eq_true] at hsp
    simpa using hsp i hi
  have hnsp' : NoSp (.seq c (.block (wipe2 (8 + 4 * slots sig) a d b)) : Prog isa) := fun i hi => by
    simp only [instrs, List.mem_append] at hi
    rcases hi with hi | hi
    · exact hnsp i hi
    · exact wipe2_noSp _ _ _ _ i hi
  have hd' : stackUse (.seq c (.block (wipe2 (8 + 4 * slots sig) a d b)) : Prog isa) ≤ stack := by
    simp only [stackUse]; omega_using [hd]
  -- The buffer, in 64 bits, from the frame's base `E - bytes`.
  have hR : ∀ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s →
      (s.gpr .esp - BitVec.ofNat 32 bytes + BitVec.ofNat 32 (8 + 4 * slots sig)).setWidth 64 =
        (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - (8 + 4 * slots sig)) ∧
      stack + bytes ≤ (s.gpr .esp).toNat := fun s hs => by
    have hs' := hs
    rw [pre_stack hl] at hs'
    obtain ⟨⟨hst, -⟩, -⟩ := hs'
    exact ⟨sub_add_setWidth (by omega_using [hb]) (by omega_using [hst]), by omega_using [hst]⟩
  -- The buffer is below the stack the contract without it reserves, so apart
  -- from its buffers.
  have hdisj : ∀ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s →
      ∀ b ∈ Sig.bufs sig.params (stackArgs sig s),
        b.1.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - (8 + 4 * slots sig)),
          n * e.size⟩ := by
    intro s hs b hb'
    have h0 := (hR s hs).2
    rw [pre_stack hl] at hs
    obtain ⟨⟨hst, -⟩, -, -, -, hres, -, -⟩ := hs
    have hbelow : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (stack + bytes), stack + bytes⟩ :
        Region) ∈ (⟨(s.gpr .esp).setWidth 64, 4⟩ :: stackBelow ((s.gpr .esp).setWidth 64)
          (stack + bytes) : List Region) := by
      rw [show stack + bytes = (stack + bytes - 1) + 1 by omega_using [hb]]; simp [stackBelow]
    exact (Region.Disjoint.symm (hres _ hbelow b (List.mem_append_left _ hb'))).sub_right
      (below_sub' _ (by omega_using []) (by omega_using [hb]))
  -- Every run is `setArgs`, then the code's run from `narrow`, then the wipe.
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s → ∃ t s₃ s₄,
      Exec isa c (narrow sig e n bytes wa s) t s₃ ∧
      (Sig.scratchContract abi sig nm e n pre post wa stack leak).post (narrow sig e n bytes wa s) s₃ ∧
      Frame [⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - (8 + 4 * slots sig)), n * e.size⟩]
        s₃.mem s₄.mem ∧
      s₃.gpr .esp = s.gpr .esp - BitVec.ofNat 32 bytes ∧
      Exec isa (withStackScratchWiped2 bytes (slots sig) a d b c) s
        (setArgsTrace bytes (s.gpr .esp - BitVec.ofNat 32 bytes) (slots sig) ++
          (t ++ (wipeTrace (s₃.gpr .esp) (8 + 4 * slots sig) a ++
            wipeTrace (s₃.gpr .esp) (8 + 4 * slots sig + d) b)))
        (popState bytes s s₄) ∧
      abiPreserved s (popState bytes s s₄) ∧ (popState bytes s s₄).mem = s₄.mem ∧
      (popState bytes s s₄).gpr .eax = s₃.gpr .eax ∧ (popState bytes s s₄).gpr .edx = s₃.gpr .edx := by
    intro s hs
    obtain ⟨hR64, h0⟩ := hR s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrow_pre hb.1 hpreL hs)
    obtain ⟨hesp, -, -, -⟩ := narrow_facts (nm := "") (e := e) (n := n) hb.1 hs
    have hesp₃ : s₃.gpr .esp = s.gpr .esp - BitVec.ofNat 32 bytes :=
      (ha.1 .esp (by simp [calleeSaved])).trans hesp
    have hwr₃ : s₃.wr = (narrow sig e n bytes wa s).wr := (Exec.rdwr he).2
    have hmem : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - (8 + 4 * slots sig)),
        n * e.size⟩ : Region) ∈ s₃.wr := by
      rw [hwr₃, ← hR64]
      simp [narrow, oldRegions]
    obtain ⟨m', hblk, hfr⟩ := wipe2_run _ s₃ (8 + 4 * slots sig) a d b hmem (fun k hk => by
      rw [hesp₃, sub_add_setWidth (by omega_using [hb, hw, hk]) (by omega_using [h0])]
      exact Offset.contains_below _ (by omega_using []) (by omega_using [hw, hk]) (by omega_using [h0]))
      (fun k hk => by
        rw [hesp₃, show 8 + 4 * slots sig + d + 4 * k = 8 + 4 * slots sig + (d + 4 * k) by omega_using [],
          sub_add_setWidth (by omega_using [hb, hw', hk]) (by omega_using [h0])]
        exact Offset.contains_below _ (by omega_using []) (by omega_using [hw', hk]) (by omega_using [h0]))
    have he' := Exec.seq he (Exec.block hblk)
    have ha' : abiPreserved (narrow sig e n bytes wa s) { s₃.setReg .ecx 0 with mem := m' } := by
      refine ⟨fun q hq => ?_, ?_⟩
      · have hq' : q ≠ .ecx := by rintro rfl; simp [calleeSaved] at hq
        simp only [State.setReg, hq', ↓reduceIte]
        exact ha.1 q hq
      · show m'.readW _ 32 = _
        rw [hesp, Taint.sub_setWidth (by omega_using [h0])]
        rw [hfr.readW (r := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 bytes, 4⟩)
          (Region.contains_self _ _) (fun r' hr' => by
            simp only [List.mem_singleton] at hr'; subst hr'
            exact below_disjoint _ bytes (a := bytes) (b := bytes - (8 + 4 * slots sig))
              (by omega_using []) (by omega_using []) (.inl (by omega_using [hb])) (by omega_using []) (by omega_using [hb]))
          (by decide)]
        have h2 := ha.2
        rwa [hesp, Taint.sub_setWidth (by omega_using [h0])] at h2
    obtain ⟨hex, habi, hm, heax, hedx⟩ := withStackScratch_run hb hnsp' hd' hs he' ha'
    refine ⟨t, s₃, _, he, hq, hfr, hesp₃, hex, habi, hm, ?_, ?_⟩
    · rw [heax]; simp [State.setReg]
    · rw [hedx]; simp [State.setReg]
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, s₄, -, hq, hfr, -, hex, ha, hm, heax, hedx⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_stack]
    have hq' := (post_stack (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)).mp hq
    obtain ⟨-, -, hargs, -⟩ := narrow_facts (nm := nm) (e := e) (n := n) hb.1 hs
    rw [hargs] at hq'
    rw [hm, heax, hedx]
    have hq'' := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params
      post _ _ (stackArgs_length sig s)) _) s₃.mem) _) hq'
    have h₃ := hpost _ _ _ _ _ (stackArgs_length sig s) (narrow_agree hb.1 hs) hq''
    refine hpostOut _ _ _ _ _ (stackArgs_length sig s) (fun b hb' a ha' => ?_) h₃
    exact (hfr a fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdisj s hs b hb' a ha').symm
  · obtain ⟨u₁, _, _, f₁, _, _, p₁, x₁, _⟩ := hrun s₁ h₁
    obtain ⟨u₂, _, _, f₂, _, _, p₂, x₂, _⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, p₁, p₂, ((pubL_stack hl).mp hp).1.1,
      hct _ _ _ _ _ _ (narrow_pre hb.1 hpreL h₁) (narrow_pre hb.1 hpreL h₂)
        (narrow_pub hb.1 h₁ h₂ hp hleak.toL) f₁ f₂]

end

end VG.X86
