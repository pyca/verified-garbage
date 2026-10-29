module

public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# A scratch buffer on the stack, wiped after use (PPC64LE)

`Verified.stackScratchWiped`: as `Verified.stackScratch`, for
`withStackScratchWiped`, which zeroes the first `words` doublewords of the
buffer after the code. The wipe stores only into the buffer, within the
frame (`wipe_run`), so the run of the code followed by the wipe keeps what the
calling convention requires, and its trace depends only on the stack pointer.
The postcondition holds of the memory after the wipe if it reads the memory
on return only within the function's buffers (`hpost`), which are disjoint
from the frame. The same structure as `VG.AArch64.Verified.stackScratchWiped`.
-/

@[expose] public section

namespace VG.PPC64LE

open VG.Impl.StackScratch.PPC64LE

/-- The trace of `wipeStores words` from a state whose `r12` is `p`. -/
def wipeTrace (p : Addr) (words : Nat) : List Leak :=
  (List.range words).map fun k => .addr (p + BitVec.ofNat 64 (8 * k))

theorem wipeStores_succ (w : Nat) :
    wipeStores (w + 1) = wipeStores w ++ ([.store .d .r11 .r12 (8 * w)] : List Instr) := by
  simp only [wipeStores, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- The stores of `wipeStores` change memory only in the region `R`, which
holds each of them and which `u` may write. -/
theorem wipeStores_run (R : Region) (u : State) (hR : R ∈ u.wr) : ∀ words, 8 * words ≤ 4096 →
    (∀ k < words, R.Contains (u.gpr .r12 + BitVec.ofNat 64 (8 * k)) 8) →
    ∃ m', execBlock isa (wipeStores words) u =
        some ({ u with mem := m' }, wipeTrace (u.gpr .r12) words) ∧ Frame [R] u.mem m'
  | 0, _, _ => ⟨u.mem, rfl, Frame.refl _ _⟩
  | w + 1, hwb, hc => by
    obtain ⟨m', he, hf⟩ := wipeStores_run R u hR w (by omega_using [hwb]) fun k hk => hc k (by omega_using [hk])
    have hin : InRegions ({ u with mem := m' } : State).wr (u.gpr .r12 + BitVec.ofNat 64 (8 * w)) 8 :=
      ⟨R, hR, hc w (by omega_using [])⟩
    refine ⟨m'.writeW (u.gpr .r12 + BitVec.ofNat 64 (8 * w)) (u.gpr .r11), ?_,
      hf.writeW (List.mem_singleton_self _) _ (hc w (by omega_using []))⟩
    rw [wipeStores_succ, execBlock_append, he]
    simp only [Option.bind_some, execBlock, isa,
      exec_store_d (s := { u with mem := m' }) (by decide)
        ⟨by omega_using [hwb], by omega_using []⟩ hin,
      Option.map_some, addrs, List.map_cons, List.map_nil, List.append_nil, wipeTrace, List.range_succ,
      List.map_append]

/-- `wipe words` from `u`, with the `words` doublewords at `r1 + 32` in the
region `R`, which `u` may write: it sets `r12` to `r1 + 32` and `r11` to
zero, and changes memory only in `R`, with a trace of the addresses alone. -/
theorem wipe_run (R : Region) (u : State) (words : Nat) (hR : R ∈ u.wr) (hwb : 8 * words ≤ 4096)
    (hc : ∀ k < words, R.Contains (u.sp + 32 + BitVec.ofNat 64 (8 * k)) 8) :
    ∃ m', execBlock isa (wipe words) u =
        some ({ ((u.write .r12 (u.sp + BitVec.ofNat 64 32)).write .r11 (BitVec.ofNat 64 0)) with
          mem := m' }, wipeTrace (u.sp + 32) words) ∧
      Frame [R] u.mem m' := by
  have h12 : ((u.write .r12 (u.sp + BitVec.ofNat 64 32)).write .r11 (BitVec.ofNat 64 0)).gpr .r12 =
      u.sp + 32 := by
    simp [State.write]
  obtain ⟨m', he, hf⟩ := wipeStores_run R ((u.write .r12 (u.sp + BitVec.ofNat 64 32)).write .r11
      (BitVec.ofNat 64 0)) (by simpa [State.write]) words hwb (by rw [h12]; exact hc)
  refine ⟨m', ?_, by simpa [State.write] using hf⟩
  simp only [wipe, execBlock, isa, exec, show (32 : Nat) < 2 ^ 15 by decide,
    show (0 : Nat) < 2 ^ 15 by decide, ↓reduceIte]
  rw [show ((u.write .r12 (u.sp + BitVec.ofNat 64 32)).write .r11 (BitVec.ofNat 64 0 : BitVec 64)) =
      ((u.write .r12 (u.sp + BitVec.ofNat 64 32)).write .r11 (BitVec.ofNat 64 0)) from rfl]
  simp only [Option.map_some, he, h12, addrs, List.map_nil, List.nil_append]

theorem wipe_spSafe (words : Nat) : (wipe words).all (fun i => !isa.writesSp i) = true := by
  simp [wipe, wipeStores, List.all_cons, List.all_map]

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes words : Nat}

/-- Code verified for a function whose last argument, in a register, is a
scratch buffer of `n` elements `e`, with `stack` bytes of stack, is verified
for the function without it, which allocates the buffer in a frame of
`bytes` more bytes of stack and zeroes its first `words` doublewords after
the code (`withStackScratchWiped`), if its precondition reads memory only
within the function's buffers (`hpre`) and its postcondition reads the
memory on entry and on return only within them (`hpost`, `hpostOut`). -/
theorem Verified.stackScratchWiped {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack))
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
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true := by decide) :
    Verified target
      (withStackScratchWiped bytes (argRegs.getD (sig.words abi.ptrBits).length .r3) words c)
      (sig.contract abi pre post wa (stack + bytes)) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hlen := regArgs_length sig
  -- The buffer, below the stack the contract without it reserves, so apart
  -- from the function's buffers.
  have hdisj : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s →
      ∀ b ∈ Sig.bufs sig.params (regArgs sig s),
        b.1.Disjoint ⟨s.sp - BitVec.ofNat 64 bytes + 32, n * e.size⟩ := by
    intro s hs b hb'
    rw [pre_regs (by omega_using [hk]) hl] at hs
    obtain ⟨-, -, -, -, hres, -, -⟩ := hs
    have hbelow : below s.sp (stack + bytes) ∈ stackBelow s.sp (stack + bytes) := by
      rw [stackBelow_pos _ (by omega_using [hb])]; simp
    exact ((hres _ hbelow b hb').sub_left (buf_sub (stack := stack) s hb.2.2.2)).symm
  -- Every run is the code's run from `narrow`, then the wipe.
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s → ∃ t s₃ s₄,
      Exec isa c (narrow sig e n bytes s) t s₃ ∧
      (Sig.scratchContract abi sig nm e n pre post wa stack).post (narrow sig e n bytes s) s₃ ∧
      Frame [⟨s.sp - BitVec.ofNat 64 bytes + 32, n * e.size⟩] s₃.mem s₄.mem ∧
      s₃.sp = s.sp - BitVec.ofNat 64 bytes ∧
      Exec isa (withStackScratchWiped bytes (argRegs.getD (sig.words abi.ptrBits).length .r3) words c) s
        (.addr (s.sp - BitVec.ofNat 64 bytes) :: (t ++ wipeTrace (s₃.sp + 32) words))
        (popState bytes s s₄) ∧
      abiPreserved s (popState bytes s s₄) ∧ (popState bytes s s₄).mem = s₄.mem ∧
      (popState bytes s s₄).gpr .r3 = s₃.gpr .r3 := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrow_pre hk hb hpre hs hl)
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
    obtain ⟨hex, habi, hm, hg⟩ := withStackScratch_run hk hb hs he' ha' hl
    refine ⟨t, s₃, _, he, hq, hfr, hsp₃, hex, habi, hm, ?_⟩
    rw [hg]; simp [State.write]
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, s₄, -, hq, hfr, -, hex, ha, hm, hr3⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_regs (by omega_using [hk])]
    have hq' := (post_regs (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
      (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega_using [hk])).mp hq
    rw [narrow_regArgs hk] at hq'
    rw [hm, hr3]
    have h₃ := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params
      post _ _ (hlen s (by omega_using [hk]))) _) s₃.mem) _) hq'
    -- The memory on entry: `narrow`'s, which differs from `s`'s only in the frame's header.
    have h₄ := hpost _ _ _ _ _ (hlen s (by omega_using [hk]))
      (fun b hb' a ha' => (narrow_agree (e := e) (n := n) hk hb.1 hs hl b hb' a ha').symm) h₃
    -- The memory on return: after the wipe, which writes only the buffer.
    refine hpostOut _ _ _ _ _ (hlen s (by omega_using [hk])) (fun b hb' a ha' => ?_) h₄
    exact (hfr a fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdisj s hs b hb' a ha').symm
  · obtain ⟨u₁, _, _, f₁, _, _, p₁, x₁, _⟩ := hrun s₁ h₁
    obtain ⟨u₂, _, _, f₂, _, _, p₂, x₂, _⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, p₁, p₂]
    have hsp₁₂ : s₁.sp = s₂.sp := ((pub_regs (by omega_using [hk]) hl).mp hp).1
    rw [hct _ _ _ _ _ _ (narrow_pre hk hb hpre h₁ hl) (narrow_pre hk hb hpre h₂ hl)
        (narrow_pub hk hp hl) f₁ f₂, hsp₁₂]

end

end VG.PPC64LE
