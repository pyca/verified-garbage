module

public import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe
public import VerifiedGarbage.Impl.StackScratch.X86_64.WipedX

/-!
# A scratch buffer on the stack, wiped after use by any wipe (x86-64)

`Verified.stackScratchWipedBy`: as `Verified.stackScratchWiped`, for a
scratch buffer passed in a register and any wipe (`Wiper`) of the start of
the buffer, at `rsp + 8`; and `Verified.stackScratchWipedX`, for
`withStackScratchWipedX`, which zeroes the first `n` 16-byte words of the
buffer (`Wiper.x`). The wipe stores only into the buffer, within the frame,
and writes no callee-saved register, `rax` or MXCSR, so the run of the code
followed by the wipe keeps what the calling convention requires and the
return value, and its trace depends only on the stack pointer.
-/

@[expose] public section

namespace VG.X86_64

open VG.Impl.StackScratch.X86_64

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes : Nat}

/-- Code verified for a function whose last argument, in a register, is a
scratch buffer of `n` elements `e`, with `stack` bytes of stack, is verified
for the function without it, which allocates the buffer in a frame of
`bytes` more bytes of stack and zeroes its first `w.len` bytes after the code
with the wipe `w`, if the postcondition reads the memory on return only
within the function's buffers (`hpost`). -/
theorem Verified.stackScratchWipedBy (w : Wiper) {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack))
    (hk : (sig.words abi.ptrBits).length < 6)
    (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 8 = 0 ∧ 8 + n * e.size ≤ bytes)
    (hst : stack + bytes + 8 ≤ 2 ^ 64)
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ stack)
    (hw : w.len ≤ n * e.size)
    (hpost : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true := by decide) :
    Verified target
      (withStackScratch bytes (argRegs.getD (sig.words abi.ptrBits).length .rax) (.seq c (.block (w.code 8))))
      (sig.contract abi pre post wa (stack + bytes)) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hsafe : SpSafe (.seq c (.block (w.code 8)) : Prog isa) :=
    SpSafe.of_all (by simp only [Code.all, hsp, w.spSafe, Bool.and_self])
  have hdep : (Code.seq c (.block (w.code 8)) : Prog isa).x86_64Depth ≤ stack := by
    simp only [Code.x86_64Depth]; omega_using [hd]
  have hlen := regArgs_length sig
  -- The buffer, below the stack the contract without it reserves, so apart
  -- from its buffers.
  have hdisj : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s →
      ∀ b ∈ Sig.bufs sig.params (regArgs sig s),
        b.1.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, n * e.size⟩ := by
    intro s hs b hb'
    rw [pre_regs (by omega_using [hk]) hl] at hs
    obtain ⟨hwf, -, -, -, hres, -, -⟩ := hs
    have hsb : stack + bytes ≤ (s.gpr .rsp).toNat := by rcases hwf with h | h <;> omega_using [h]
    have hbelow : below (s.gpr .rsp) (stack + bytes) ∈
        (⟨s.gpr .rsp, 8⟩ :: stackBelow (s.gpr .rsp) (stack + bytes) : List Region) := by
      rw [stackBelow_pos _ (by omega_using [hb])]; simp
    have hscrSub : Region.Sub ⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, n * e.size⟩
        (below (s.gpr .rsp) (stack + bytes)) := by
      rw [sub_add_eight _ (by omega_using [hb])]; exact Offset.sub_below _ (by omega_using []) (by omega_using [hb])
    exact (Region.Disjoint.symm (hres _ hbelow b hb')).sub_right hscrSub
  -- Every run is the code's run from `narrow`, then the wipe.
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s → ∃ t s₃ u,
      Exec isa c (narrow sig e n bytes s) t s₃ ∧
      (Sig.scratchContract abi sig nm e n pre post wa stack).post (narrow sig e n bytes s) s₃ ∧
      Frame [⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, n * e.size⟩] s₃.mem u.mem ∧
      Exec isa (withStackScratch bytes (argRegs.getD (sig.words abi.ptrBits).length .rax)
          (.seq c (.block (w.code 8)))) s
        (t ++ w.trace (s.gpr .rsp - BitVec.ofNat 64 bytes) 8) (popState bytes s u) ∧
      abiPreserved s (popState bytes s u) ∧ (popState bytes s u).mem = u.mem ∧
      (popState bytes s u).gpr .rax = s₃.gpr .rax := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrow_pre hk hb hst hs hl)
    have hrsp₃ : s₃.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes :=
      (ha.1 .rsp (by simp [calleeSaved])).trans (narrow_rsp hk s)
    have hwr₃ : s₃.wr = (narrow sig e n bytes s).wr := (Exec.rdwr he).2
    have hb3 := hb.2.2.2
    have hsb : stack + bytes ≤ (s.gpr .rsp).toNat := by
      have hs' := hs
      rw [pre_regs (by omega_using [hk]) hl] at hs'
      rcases hs'.1 with h | h <;> omega_using [h]
    obtain ⟨u, hblk, hfr, hg, hmx, -, -⟩ := w.run ⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, n * e.size⟩ s₃ 8
      (by rw [hwr₃, narrow_wr]; simp)
      (fun a k hak => by
        have h8 := Offset.contains_base (s.gpr .rsp - BitVec.ofNat 64 bytes + 8) (d := a) (n := k)
          (k := n * e.size) (by omega_using [hw, hak]) (by omega_using [hw, hb3, hsb, hak])
        rwa [hrsp₃, show s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 + a) =
            s.gpr .rsp - BitVec.ofNat 64 bytes + 8 + BitVec.ofNat 64 a by
          rw [BitVec.add_assoc]; congr 1; exact (BitVec.ofNat_add_ofNat ..).symm])
    have he' := Exec.seq he (Exec.block hblk)
    rw [hrsp₃] at he'
    have ha' : abiPreserved (narrow sig e n bytes s) u := by
      refine ⟨fun q hq => ?_, ?_, by rw [hmx]; exact ha.2.2⟩
      · rw [hg q (.inl hq)]
        exact ha.1 q hq
      · rw [narrow_rsp hk]
        rw [hfr.readW (r := ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, 8⟩) (Region.contains_self _ _)
          (fun r' hr' => by
            simp only [List.mem_singleton] at hr'; subst hr'
            exact Offset.base_disjoint _ (e := 8) (k := 8) (Nat.le_refl _) (by omega_using [hb3, hsb]))
          (by decide)]
        have h2 := ha.2.1
        rwa [narrow_rsp hk] at h2
    obtain ⟨hex, habi, hm, hrax⟩ := withStackScratch_run hk hb hst hsafe hdep hs he' ha' hl
    exact ⟨t, s₃, u, he, hq, hfr, hex, habi, hm, by rw [hrax, hg .rax (.inr rfl)]⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, u, -, hq, hfr, hex, ha, hm, hrax⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_regs (by omega_using [hk])]
    have hq' := (post_regs (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
      (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega_using [hk])).mp hq
    rw [narrow_regArgs hk] at hq'
    rw [hm, hrax]
    have h₃ := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params
      post _ _ (hlen s (by omega_using [hk]))) s.mem) s₃.mem) _) hq'
    refine hpost _ _ _ _ _ (hlen s (by omega_using [hk])) (fun b hb' a ha' => ?_) h₃
    exact (hfr a fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdisj s hs b hb' a ha').symm
  · obtain ⟨u₁, _, _, f₁, _, _, x₁, _⟩ := hrun s₁ h₁
    obtain ⟨u₂, _, _, f₂, _, _, x₂, _⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1]
    have hsp₁₂ : s₁.gpr .rsp = s₂.gpr .rsp := ((pub_regs (by omega_using [hk]) hl).mp hp).1
    rw [hct _ _ _ _ _ _ (narrow_pre hk hb hst h₁ hl) (narrow_pre hk hb hst h₂ hl)
      (narrow_pub hk hp hl) f₁ f₂, hsp₁₂]

/-- `Verified.stackScratchWipedBy`, for `withStackScratchWipedX`, which
zeroes the first `k` 16-byte words of the buffer. -/
theorem Verified.stackScratchWipedX {c : Prog isa} {k : Nat}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack))
    (hk : (sig.words abi.ptrBits).length < 6)
    (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 8 = 0 ∧ 8 + n * e.size ≤ bytes)
    (hst : stack + bytes + 8 ≤ 2 ^ 64)
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ stack)
    (hw : 16 * k ≤ n * e.size)
    (hpost : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true := by decide) :
    Verified target
      (withStackScratchWipedX bytes (argRegs.getD (sig.words abi.ptrBits).length .rax) k c)
      (sig.contract abi pre post wa (stack + bytes)) :=
  Verified.stackScratchWipedBy (.x k) h hk hb hst hsp hd hw hpost hsat hl

/-- `withStackScratchWipedX` writes `rsp` only in its frame if its code does. -/
theorem withStackScratchWipedX_spSafe_of {bytes : Nat} {r : Reg} {k : Nat} {c : Prog isa}
    (h : c.all (fun i => !isa.writesSp i) = true) (hr : r ≠ .rsp := by decide) :
    (withStackScratchWipedX bytes r k c).all (fun i => !isa.writesSp i) = true :=
  withStackScratch_spSafe hr (by simp only [Code.all, h, wipeAtX_spSafe, Bool.and_self])

end

end VG.X86_64
