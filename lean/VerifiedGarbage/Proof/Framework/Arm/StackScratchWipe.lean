import VerifiedGarbage.Proof.Framework.Arm.StackScratch
import VerifiedGarbage.Proof.Framework.Arm.RegScratchWipe

/-!
# A scratch buffer on the stack, after stack arguments, wiped after use (ARMv7)

`Verified.stackScratchWiped`: as `Verified.stackScratch`, for
`withStackScratchWiped`, which zeroes the first `words` words of the buffer
after the code. The wipe stores only into the buffer, within the frame
(`wipeAt_run`), so the run of the code followed by the wipe keeps what the
calling convention requires and the return value, and its trace depends only
on the stack pointer. The postcondition holds of the memory after the wipe
if it reads the memory on return only within the function's buffers
(`hpostOut`), which are disjoint from the frame.
-/

namespace VG.Arm

open VG.Impl.StackScratch.Arm VG.Arm.FrameStack

/-- `wipeAt off words` from `u`, with the `words` words at `sp + off` in the
region `R`, which `u` may write: it sets `r12` to `sp + off` and `r2` to
zero, and changes memory only in `R`, with a trace of the addresses alone. -/
theorem wipeAt_run (R : Region) (u : State) (off words : Nat) (hR : R ∈ u.wr)
    (hoff : off < 256) (hwb : 4 * words ≤ 4096)
    (hc : ∀ k < words, R.Contains (State.addr (u.sp + BitVec.ofNat 32 off + BitVec.ofNat 32 (4 * k))) 4) :
    ∃ m', execBlock isa (wipeAt off words) u =
        some ({ (u.setReg .r12 (u.sp + BitVec.ofNat 32 off)).setReg .r2 0 with mem := m' },
          wipeTrace (u.sp + BitVec.ofNat 32 off) words) ∧
      Frame [R] u.mem m' := by
  have h12 : ((u.setReg .r12 (u.sp + BitVec.ofNat 32 off)).setReg .r2 0).gpr .r12 =
      u.sp + BitVec.ofNat 32 off := by
    simp [State.setReg]
  obtain ⟨m', he, hf⟩ := wipeStores_run R ((u.setReg .r12 (u.sp + BitVec.ofNat 32 off)).setReg .r2 0)
    (by simpa [State.setReg]) words hwb (by rw [h12]; exact hc)
  refine ⟨m', ?_, by simpa [State.setReg] using hf⟩
  simp only [wipeAt, execBlock, isa, exec, hoff, ↓reduceIte, Op2.eval,
    show encodable (0 : BitVec 32) = true by decide, Option.map_some]
  rw [he, h12]
  simp [addrs]

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes m words : Nat}

/-- Code verified for a function whose last argument, on the stack after `m`
words of other stack arguments, is a scratch buffer of `n` elements `e`, with
`stack` bytes of stack, is verified for the function without it, which
allocates the buffer in a frame of `bytes` more bytes of stack and zeroes
its first `words` words after the code (`withStackScratchWiped`), if its
precondition reads memory only within the function's buffers (`hpre`), and
its postcondition both the memory on entry and the memory on return
(`hpost`, `hpostOut`). -/
theorem Verified.stackScratchWiped {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack))
    (hcl : ScratchOnStack sig) (hN : nsaa sig = 4 * m)
    (hloc : (locs sig).all (Loc.ok (4 * m)) = true) (hb : Fits m bytes e n)
    (hw : 4 * words ≤ n * e.size)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hpostOut : ∀ vs mm m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs mm m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs mm m₂ r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true := by decide) :
    Verified target (withStackScratchWiped bytes m words c)
      (sig.contract abi pre post wa (stack + bytes)) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hpreL : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂ :=
    fun vs m₁ m₂ hl hb _ => hpre vs m₁ m₂ hl hb
  have hlen := armArgs_length sig
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ := hb
  have hsb : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s → stack + bytes ≤ s.sp.toNat :=
    fun s hs => by
      rw [pre_arm hl] at hs
      obtain ⟨⟨hst, -⟩, -⟩ := hs
      omega
  -- The buffer is below the stack the contract without it reserves, so apart
  -- from its buffers.
  have hdisj : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s →
      ∀ b ∈ Sig.bufs sig.params (armArgs sig s),
        b.1.Disjoint ⟨sa (s.sp - BitVec.ofNat 32 bytes) (4 * m + 8), n * e.size⟩ := by
    intro s hs b hb'
    have h0 := hsb s hs
    rw [pre_arm hl] at hs
    obtain ⟨-, -, -, -, hres, -, -⟩ := hs
    have hbelow : (⟨State.addr s.sp - BitVec.ofNat 64 (stack + bytes), stack + bytes⟩ : Region) ∈
        stackBelow (State.addr s.sp) (stack + bytes) := by
      rw [show stack + bytes = (stack + bytes - 1) + 1 by omega]; simp [stackBelow]
    rw [sa_sub (by omega) (by omega)]
    exact (Region.Disjoint.symm (hres _ hbelow b (List.mem_append_left _ hb'))).sub_right
      (Offset.sub_below _ (by omega) (by omega))
  -- Every run is `setArgs`, then the code's run from `narrow`, then the wipe.
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s → ∃ t s₃ s₄,
      Exec isa c (narrow sig e n bytes m s) t s₃ ∧
      (Sig.scratchContract abi sig nm e n pre post wa stack).post (narrow sig e n bytes m s) s₃ ∧
      Frame [⟨sa (s.sp - BitVec.ofNat 32 bytes) (4 * m + 8), n * e.size⟩] s₃.mem s₄.mem ∧
      s₃.sp = s.sp - BitVec.ofNat 32 bytes ∧
      Exec isa (withStackScratchWiped bytes m words c) s
        (setArgsTrace bytes (s.sp - BitVec.ofNat 32 bytes) m ++
          (t ++ wipeTrace (s₃.sp + BitVec.ofNat 32 (4 * m + 8)) words))
        (popState bytes s s₄) ∧
      abiPreserved s (popState bytes s s₄) ∧ (popState bytes s s₄).mem = s₄.mem ∧
      (popState bytes s s₄).gpr .r0 = s₃.gpr .r0 ∧ (popState bytes s s₄).gpr .r1 = s₃.gpr .r1 := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrow_pre hcl hN hloc ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ hpreL hs)
    obtain ⟨hsp₂, -, -, -⟩ := narrow_facts (nm := nm) hcl hN hloc ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ hs
    have hsp₃ : s₃.sp = s.sp - BitVec.ofNat 32 bytes := ha.2.trans hsp₂
    have hwr₃ : s₃.wr = (narrow sig e n bytes m s).wr := (Exec.rdwr he).2.1
    have h0 := hsb s hs
    have hbuf : (⟨sa (s.sp - BitVec.ofNat 32 bytes) (4 * m + 8), n * e.size⟩ : Region) ∈ s₃.wr := by
      rw [hwr₃]
      simp [narrow, oldRegions, List.filter_append]
    have hF : (s.sp - BitVec.ofNat 32 bytes).toNat = s.sp.toNat - bytes := sub_toNat' (by omega)
    obtain ⟨m', hblk, hfr⟩ := wipeAt_run _ s₃ (4 * m + 8) words hbuf (by omega) (by omega)
      (fun k hk' => by
        have hlt := s.sp.isLt
        rw [hsp₃, BitVec.add_assoc, BitVec.ofNat_add_ofNat, sa,
          addr_add (by rw [hF]; omega), addr_add (by rw [hF]; omega)]
        exact Offset.contains _ (by omega) (by omega) (by omega))
    have he' := Exec.seq he (Exec.block hblk)
    have ha' : abiPreserved (narrow sig e n bytes m s)
        { (s₃.setReg .r12 (s₃.sp + BitVec.ofNat 32 (4 * m + 8))).setReg .r2 0 with mem := m' } := by
      refine ⟨fun q hq => ?_, ha.2⟩
      have h12 : q ≠ .r12 := by rintro rfl; simp [preserved] at hq
      have h2 : q ≠ .r2 := by rintro rfl; simp [preserved] at hq
      simp only [State.setReg, h12, h2, ↓reduceIte]
      exact ha.1 q hq
    obtain ⟨hex, habi, hm, hg⟩ :=
      withStackScratch_run hcl hN hloc ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ hs he' ha'
    refine ⟨t, s₃, _, he, hq, hfr, hsp₃, hex, habi, hm, ?_, ?_⟩
    · rw [hg]; simp [State.setReg]
    · rw [hg]; simp [State.setReg]
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, s₄, -, hq, hfr, -, hex, ha, hm, hr0, hr1⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_arm]
    have hq' := (post_arm (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)).mp hq
    obtain ⟨-, -, hargs, -⟩ := narrow_facts (nm := nm) hcl hN hloc ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ hs
    rw [hargs] at hq'
    rw [hm, hr0, hr1]
    have h₃ := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n
      sig.params post _ _ (hlen s)) _) s₃.mem) _) hq'
    have h₄ := hpost _ _ _ _ _ (hlen s)
      (narrow_agree hcl hN hloc ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ hs) h₃
    refine hpostOut _ _ _ _ _ (hlen s) (fun b hb' a ha' => ?_) h₄
    exact (hfr a fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdisj s hs b hb' a ha').symm
  · obtain ⟨u₁, _, _, f₁, _, _, p₁, x₁, _⟩ := hrun s₁ h₁
    obtain ⟨u₂, _, _, f₂, _, _, p₂, x₂, _⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, p₁, p₂, ((pub_arm hl).mp hp).1,
      hct _ _ _ _ _ _ (narrow_pre hcl hN hloc ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ hpreL h₁)
        (narrow_pre hcl hN hloc ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ hpreL h₂)
        (narrow_pub hcl hN hloc ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ h₁ h₂ hp) f₁ f₂]

end

end VG.Arm
