import VerifiedGarbage.Proof.Framework.Arm.RegScratch
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-!
# A scratch buffer in a register, on the stack, wiped after use (ARMv7)

`Verified.regScratchWiped`: as `Verified.regScratch`, for
`withRegScratchWiped`, which zeroes the first `words` words of the buffer
after the code. The wipe stores only into the buffer, within the frame
(`wipe_run`), so the run of the code followed by the wipe keeps what the
calling convention requires and the return value, and its trace depends only
on the stack pointer. The postcondition holds of the memory after the wipe
if it reads the memory on return only within the function's buffers
(`hpost`), which are disjoint from the frame.
-/

namespace VG.Arm

open VG.Impl.StackScratch.Arm VG.Arm.FrameStack

/-- The trace of `wipeStores words` from a state whose `r12` is `p`. -/
def wipeTrace (p : BitVec 32) (words : Nat) : List Leak :=
  (List.range words).map fun k => .addr (State.addr (p + BitVec.ofNat 32 (4 * k)))

theorem wipeStores_succ (w : Nat) :
    wipeStores (w + 1) = wipeStores w ++ ([.str .r2 .r12 (4 * w)] : List Instr) := by
  simp only [wipeStores, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- The stores of `wipeStores` change memory only in the region `R`, which
holds each of them and which `u` may write. -/
theorem wipeStores_run (R : Region) (u : State) (hR : R ∈ u.wr) : ∀ words, 4 * words ≤ 4096 →
    (∀ k < words, R.Contains (State.addr (u.gpr .r12 + BitVec.ofNat 32 (4 * k))) 4) →
    ∃ m', execBlock isa (wipeStores words) u =
        some ({ u with mem := m' }, wipeTrace (u.gpr .r12) words) ∧ Frame [R] u.mem m'
  | 0, _, _ => ⟨u.mem, rfl, Frame.refl _ _⟩
  | w + 1, hwb, hc => by
    obtain ⟨m', he, hf⟩ := wipeStores_run R u hR w (by omega) fun k hk => hc k (by omega)
    have hin : InRegions u.wr (State.addr (u.gpr .r12 + BitVec.ofNat 32 (4 * w))) 4 :=
      ⟨R, hR, hc w (by omega)⟩
    have hoff : 4 * w < 4096 := by omega
    refine ⟨m'.writeW (State.addr (u.gpr .r12 + BitVec.ofNat 32 (4 * w))) (u.gpr .r2), ?_,
      hf.writeW (List.mem_singleton_self _) _ (hc w (by omega))⟩
    rw [wipeStores_succ, execBlock_append, he]
    simp only [Option.bind_some, execBlock, isa, exec, hoff, ↓reduceIte, State.store32, hin,
      Option.map_some, addrs, List.map_cons, List.map_nil, List.append_nil, wipeTrace,
      List.range_succ, List.map_append]

/-- `wipe words` from `u`, with the `words` words at `sp` in the region `R`,
which `u` may write: it sets `r12` to `sp` and `r2` to zero, and changes
memory only in `R`, with a trace of the addresses alone. -/
theorem wipe_run (R : Region) (u : State) (words : Nat) (hR : R ∈ u.wr) (hwb : 4 * words ≤ 4096)
    (hc : ∀ k < words, R.Contains (State.addr (u.sp + BitVec.ofNat 32 (4 * k))) 4) :
    ∃ m', execBlock isa (wipe words) u =
        some ({ (u.setReg .r12 (u.sp + BitVec.ofNat 32 0)).setReg .r2 0 with mem := m' },
          wipeTrace u.sp words) ∧
      Frame [R] u.mem m' := by
  have h12 : ((u.setReg .r12 (u.sp + BitVec.ofNat 32 0)).setReg .r2 0).gpr .r12 = u.sp := by
    simp [State.setReg]
  obtain ⟨m', he, hf⟩ := wipeStores_run R ((u.setReg .r12 (u.sp + BitVec.ofNat 32 0)).setReg .r2 0)
    (by simpa [State.setReg]) words hwb (by rw [h12]; exact hc)
  refine ⟨m', ?_, by simpa [State.setReg] using hf⟩
  simp only [wipe, execBlock, isa, exec, show (0 : Nat) < 256 by decide, ↓reduceIte, Op2.eval,
    show encodable (0 : BitVec 32) = true by decide, Option.map_some]
  rw [he, h12]
  simp [addrs]

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes words : Nat} {r : Reg}

/-- Code verified for a function whose last argument, in a register `r`, is a
scratch buffer of `n` elements `e`, with `stack` bytes of stack, is verified
for the function without it, which allocates the buffer in a frame of
`bytes` more bytes of stack and zeroes its first `words` words after the code
(`withRegScratchWiped`), if the postcondition reads the memory on return only
within the function's buffers (`hpost`). The other arguments are in
registers too (`hcl`, `hloc`), but neither `r2` nor `r12` is the buffer's. -/
theorem Verified.regScratchWiped {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack))
    (hcl : ScratchInReg sig r) (hloc : (locs sig).all (Loc.avoids r) = true) (hb : FitsR bytes e n)
    (hw : 4 * words ≤ n * e.size)
    (hpost : ∀ vs m m₁ m₂ ret, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ ret →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ ret)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true := by decide) :
    Verified target (withRegScratchWiped bytes r words c)
      (sig.contract abi pre post wa (stack + bytes)) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hlen := armArgs_length sig
  have hsb : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s → stack + bytes ≤ s.sp.toNat :=
    fun s hs => by
      rw [pre_arm hl] at hs
      obtain ⟨⟨hst, -⟩, -⟩ := hs
      omega
  -- The buffer is below the stack the contract without it reserves, so apart
  -- from its buffers.
  have hdisj : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s →
      ∀ b ∈ Sig.bufs sig.params (armArgs sig s),
        b.1.Disjoint ⟨State.addr (s.sp - BitVec.ofNat 32 bytes), n * e.size⟩ := by
    intro s hs b hb'
    have h0 := hsb s hs
    rw [pre_arm hl] at hs
    obtain ⟨-, -, -, -, hres, -, -⟩ := hs
    rw [allRegions, argArea_eq_nil hcl.2.1 s, List.append_nil] at hres
    have hbelow : (⟨State.addr s.sp - BitVec.ofNat 64 (stack + bytes), stack + bytes⟩ : Region) ∈
        stackBelow (State.addr s.sp) (stack + bytes) := by
      rw [show stack + bytes = (stack + bytes - 1) + 1 by omega]; simp [stackBelow]
    rw [addr_sub' (by omega)]
    exact (Region.Disjoint.symm (hres _ hbelow b hb')).sub_right
      (Offset.sub_below _ (by omega) (by have := hb.2.2.2.2; omega))
  -- Every run is the code's run from `narrowR`, then the wipe.
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s → ∃ t s₃ s₄,
      Exec isa c (narrowR e n bytes r s) t s₃ ∧
      (Sig.scratchContract abi sig nm e n pre post wa stack).post (narrowR e n bytes r s) s₃ ∧
      Frame [⟨State.addr (s.sp - BitVec.ofNat 32 bytes), n * e.size⟩] s₃.mem s₄.mem ∧
      s₃.sp = s.sp - BitVec.ofNat 32 bytes ∧
      Exec isa (withRegScratchWiped bytes r words c) s (t ++ wipeTrace s₃.sp words)
        (popState bytes s s₄) ∧
      abiPreserved s (popState bytes s s₄) ∧ (popState bytes s s₄).mem = s₄.mem ∧
      (popState bytes s s₄).gpr .r0 = s₃.gpr .r0 ∧ (popState bytes s s₄).gpr .r1 = s₃.gpr .r1 := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrowR_pre hcl hloc hb hs hl)
    have hsp₃ : s₃.sp = s.sp - BitVec.ofNat 32 bytes := ha.2.trans (narrowR_sp s)
    have hwr₃ : s₃.wr = (narrowR e n bytes r s).wr := (Exec.rdwr he).2.1
    have h0 := hsb s hs
    have hn := hb.2.2.2.2
    obtain ⟨m', hblk, hfr⟩ := wipe_run ⟨State.addr (s.sp - BitVec.ofNat 32 bytes), n * e.size⟩ s₃ words
      (by rw [hwr₃, narrowR_wr]; simp) (by have := hb.2.1; omega)
      (fun k hk' => by
        rw [hsp₃, addr_add (by rw [sub_toNat' (by omega)]; have := s.sp.isLt; omega)]
        exact Offset.contains_base _ (by omega) (by omega))
    have he' := Exec.seq he (Exec.block hblk)
    have ha' : abiPreserved (narrowR e n bytes r s)
        { (s₃.setReg .r12 (s₃.sp + BitVec.ofNat 32 0)).setReg .r2 0 with mem := m' } := by
      refine ⟨fun q hq => ?_, ha.2⟩
      have h12 : q ≠ .r12 := by rintro rfl; simp [preserved] at hq
      have h2 : q ≠ .r2 := by rintro rfl; simp [preserved] at hq
      simp only [State.setReg, h12, h2, ↓reduceIte]
      exact ha.1 q hq
    obtain ⟨hex, habi, hm, hg⟩ := withRegScratch_run hcl hb hs he' ha' hl
    refine ⟨t, s₃, _, he, hq, hfr, hsp₃, hex, habi, hm, ?_, ?_⟩
    · rw [hg]; simp [State.setReg]
    · rw [hg]; simp [State.setReg]
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, s₄, -, hq, hfr, -, hex, ha, hm, hr0, hr1⟩ := hrun s hs
    refine ⟨t ++ _, _, hex, ha, ?_⟩
    rw [post_arm]
    have hq' := (post_arm (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)).mp hq
    rw [narrowR_armArgs hcl hloc] at hq'
    rw [hm, hr0, hr1]
    have h₃ := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params
      post _ _ (hlen s)) s.mem) s₃.mem) _) hq'
    refine hpost _ _ _ _ _ (hlen s) (fun b hb' a ha' => ?_) h₃
    exact (hfr a fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdisj s hs b hb' a ha').symm
  · obtain ⟨u₁, _, _, f₁, _, _, p₁, x₁, _⟩ := hrun s₁ h₁
    obtain ⟨u₂, _, _, f₂, _, _, p₂, x₂, _⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, p₁, p₂, ((pub_arm hl).mp hp).1,
      hct _ _ _ _ _ _ (narrowR_pre hcl hloc hb h₁ hl) (narrowR_pre hcl hloc hb h₂ hl)
        (narrowR_pub hcl hloc hp hl) f₁ f₂]

end

end VG.Arm
