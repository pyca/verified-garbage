import VerifiedGarbage.Proof.Framework.AArch64.StackScratch

/-!
# A scratch buffer on the stack, wiped after use (AArch64)

`Verified.stackScratchWiped`: as `Verified.stackScratch`, for
`withStackScratchWiped`, which zeroes the first `words` doublewords of the
buffer after the code. The wipe stores only into the buffer, within the
frame (`wipe_run`), so the run of the code followed by the wipe keeps what the
calling convention requires and the return value, and its trace depends only
on the stack pointer. The postcondition holds of the memory after the wipe
if it reads the memory on return only within the function's buffers
(`hpost`), which are disjoint from the frame.
-/

namespace VG.AArch64

open VG.Impl.StackScratch.AArch64

/-- The trace of `wipeStores words` from a state whose `x16` is `p`. -/
def wipeTrace (p : Addr) (words : Nat) : List Leak :=
  (List.range words).map fun k => .addr (p + BitVec.ofNat 64 (8 * k))

theorem wipeStores_succ (w : Nat) :
    wipeStores (w + 1) = wipeStores w ++ ([.str .x .x17 .x16 (8 * w)] : List Instr) := by
  simp only [wipeStores, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- The stores of `wipeStores` change memory only in the region `R`, which
holds each of them and which `u` may write. -/
theorem wipeStores_run (R : Region) (u : State) (hR : R ∈ u.wr) : ∀ words, 8 * words ≤ 4096 →
    (∀ k < words, R.Contains (u.gpr .x16 + BitVec.ofNat 64 (8 * k)) 8) →
    ∃ m', execBlock isa (wipeStores words) u =
        some ({ u with mem := m' }, wipeTrace (u.gpr .x16) words) ∧ Frame [R] u.mem m'
  | 0, _, _ => ⟨u.mem, rfl, Frame.refl _ _⟩
  | w + 1, hwb, hc => by
    obtain ⟨m', he, hf⟩ := wipeStores_run R u hR w (by omega) fun k hk => hc k (by omega)
    have hin : InRegions u.wr (u.gpr .x16 + BitVec.ofNat 64 (8 * w)) 8 := ⟨R, hR, hc w (by omega)⟩
    have hoff : 8 * w % 8 = 0 ∧ 8 * w < 4096 * 8 := ⟨by omega, by omega⟩
    refine ⟨m'.write (u.gpr .x16 + BitVec.ofNat 64 (8 * w)) 8
      (((u.gpr .x17).setWidth 64).setWidth (8 * 8)), ?_,
      hf.write (List.mem_singleton_self _) _ (hc w (by omega))⟩
    rw [wipeStores_succ, execBlock_append, he]
    simp only [Option.bind_some, execBlock, isa, exec, addr, hoff, and_self, ↓reduceIte,
      State.store, hin, Option.map_some, addrs, List.map_cons, List.map_nil, List.append_nil,
      wipeTrace, List.range_succ, List.map_append, State.read, Size.bytes, Size.bits]

/-- `wipe words` from `u`, with the `words` doublewords at `sp` in the region
`R`, which `u` may write: it sets `x16` to `sp` and `x17` to zero, and changes
memory only in `R`, with a trace of the addresses alone. -/
theorem wipe_run (R : Region) (u : State) (words : Nat) (hR : R ∈ u.wr) (hwb : 8 * words ≤ 4096)
    (hc : ∀ k < words, R.Contains (u.sp + BitVec.ofNat 64 (8 * k)) 8) :
    ∃ m', execBlock isa (wipe words) u =
        some ({ ((u.write .x .x16 (u.sp + BitVec.ofNat 64 0)).write .x .x17
            ((0 : BitVec 16).setWidth 64 <<< (16 * 0))) with mem := m' }, wipeTrace u.sp words) ∧
      Frame [R] u.mem m' := by
  have h16 : ((u.write .x .x16 (u.sp + BitVec.ofNat 64 0)).write .x .x17
      ((0 : BitVec 16).setWidth 64 <<< (16 * 0))).gpr .x16 = u.sp := by
    simp [State.write]
  obtain ⟨m', he, hf⟩ := wipeStores_run R ((u.write .x .x16 (u.sp + BitVec.ofNat 64 0)).write .x .x17
      ((0 : BitVec 16).setWidth 64 <<< (16 * 0))) (by simpa [State.write]) words hwb
    (by rw [h16]; exact hc)
  refine ⟨m', ?_, by simpa [State.write] using hf⟩
  simp only [wipe, execBlock, isa, exec, show (0 : Nat) < 4096 by decide, ↓reduceIte,
    show 16 * 0 < Size.bits .x by decide]
  rw [he, h16]
  simp [addrs]

theorem wipe_spSafe (words : Nat) : (wipe words).all (fun i => !isa.writesSp i) = true := by
  simp [wipe, wipeStores]

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes words : Nat}

/-- Code verified for a function whose last argument, in a register, is a
scratch buffer of `n` elements `e`, with `stack` bytes of stack, is verified
for the function without it, which allocates the buffer in a frame of
`bytes` more bytes of stack and zeroes its first `words` doublewords after
the code (`withStackScratchWiped`), if the postcondition reads the memory on
return only within the function's buffers (`hpost`). -/
theorem Verified.stackScratchWiped {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack))
    (hk : (sig.words abi.ptrBits).length < 8)
    (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0 ∧ n * e.size ≤ bytes)
    (hw : 8 * words ≤ n * e.size)
    (hpost : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true := by decide) :
    Verified target
      (withStackScratchWiped bytes (argRegs.getD (sig.words abi.ptrBits).length .x0) words c)
      (sig.contract abi pre post wa (stack + bytes)) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hlen := regArgs_length sig
  have hsb : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s → stack + bytes ≤ s.sp.toNat :=
    fun s hs => by
      rw [pre_regs (by omega) hl] at hs
      rcases hs.1 with h | h <;> omega
  -- The buffer, below the stack the contract without it reserves, so apart
  -- from its buffers.
  have hdisj : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s →
      ∀ b ∈ Sig.bufs sig.params (regArgs sig s),
        b.1.Disjoint ⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩ := by
    intro s hs b hb'
    have h0 := hsb s hs
    rw [pre_regs (by omega) hl] at hs
    obtain ⟨-, -, -, -, hres, -, -⟩ := hs
    have hbelow : below s.sp (stack + bytes) ∈ stackBelow s.sp (stack + bytes) := by
      rw [stackBelow_pos _ (by omega)]; simp
    have hscrSub : Region.Sub ⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩ (below s.sp (stack + bytes)) :=
      Offset.sub_below _ (by omega) (by omega)
    exact (Region.Disjoint.symm (hres _ hbelow b hb')).sub_right hscrSub
  -- Every run is the code's run from `narrow`, then the wipe.
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s → ∃ t s₃ s₄,
      Exec isa c (narrow sig e n bytes s) t s₃ ∧
      (Sig.scratchContract abi sig nm e n pre post wa stack).post (narrow sig e n bytes s) s₃ ∧
      Frame [⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩] s₃.mem s₄.mem ∧
      s₃.sp = s.sp - BitVec.ofNat 64 bytes ∧
      Exec isa (withStackScratchWiped bytes (argRegs.getD (sig.words abi.ptrBits).length .x0) words c) s
        (t ++ wipeTrace s₃.sp words) (popState bytes s s₄) ∧
      abiPreserved s (popState bytes s s₄) ∧ (popState bytes s s₄).mem = s₄.mem ∧
      (popState bytes s s₄).gpr .x0 = s₃.gpr .x0 := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrow_pre hk hb hs hl)
    have hsp₃ : s₃.sp = s.sp - BitVec.ofNat 64 bytes := ha.2.1.trans (narrow_sp s)
    have hwr₃ : s₃.wr = (narrow sig e n bytes s).wr := (Exec.rdwr he).2.1
    have h0 := hsb s hs
    obtain ⟨m', hblk, hfr⟩ := wipe_run ⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩ s₃ words
      (by rw [hwr₃, narrow_wr]; simp) (by have := hb.2.2.2; omega)
      (fun k hk' => by
        rw [hsp₃]; exact Offset.contains_base _ (by omega) (by omega))
    have he' := Exec.seq he (Exec.block hblk)
    have ha' : abiPreserved (narrow sig e n bytes s) { ((s₃.write .x .x16 (s₃.sp + BitVec.ofNat 64 0)).write
        .x .x17 ((0 : BitVec 16).setWidth 64 <<< (16 * 0))) with mem := m' } := by
      refine ⟨fun q hq => ?_, ha.2.1, ha.2.2⟩
      have h16 : q ≠ .x16 := by rintro rfl; simp [preserved] at hq
      have h17 : q ≠ .x17 := by rintro rfl; simp [preserved] at hq
      simp only [State.write, h16, h17, ↓reduceIte]
      exact ha.1 q hq
    obtain ⟨hex, habi, hm, hg⟩ := withStackScratch_run hk hb hs he' ha' hl
    refine ⟨t, s₃, _, he, hq, hfr, hsp₃, hex, habi, hm, ?_⟩
    rw [hg]; simp [State.write]
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, s₄, -, hq, hfr, -, hex, ha, hm, hx0⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_regs (by omega)]
    have hq' := (post_regs (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
      (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega)).mp hq
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
    have hsp₁₂ : s₁.sp = s₂.sp := ((pub_regs (by omega) hl).mp hp).1
    rw [hct _ _ _ _ _ _ (narrow_pre hk hb h₁ hl) (narrow_pre hk hb h₂ hl) (narrow_pub hk hp hl) f₁ f₂,
      hsp₁₂]

end

end VG.AArch64
