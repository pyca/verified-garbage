module
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Framework.X86_64.Depth

import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-!
# A scratch buffer on the stack, wiped after use (x86-64)

`Verified.stackScratchWiped`: as `Verified.stackScratch`, for
`withStackScratchWiped`, which zeroes the first `words` quadwords of the
buffer after the code. The wipe stores only into the buffer, within the
frame (`wipe_run`), so the run of the code followed by the wipe keeps what the
calling convention requires and the return value, and its trace depends only
on the stack pointer. The postcondition holds of the memory after the wipe
if it reads the memory on return only within the function's buffers
(`hpost`), which are disjoint from the frame.
-/

@[expose] public section

namespace VG.X86_64

open VG.Impl.StackScratch.X86_64

/-- The trace of `wipe words` from a state whose `rsp` is `sp`: the
addresses of its 16-byte stores, then of its last quadword's. -/
def wipeTrace (sp : Addr) (words : Nat) : List Leak :=
  (List.range (words / 2)).map (fun k => .addr (sp + BitVec.ofNat 64 (8 + 16 * k))) ++
    (List.range (words % 2)).map fun k => .addr (sp + BitVec.ofNat 64 (8 + 16 * (words / 2) + 8 * k))

/-- The registers once `wipe` has run: `xmm0` and `r11` zeroed. -/
def wipedRegs (u : State) : State := (XOp.exec (.bin .pxor .xmm0 .xmm0) u).setReg32 .r11 0

theorem wipedRegs_gpr (u : State) {r : Reg} (h : r ≠ .r11) : (wipedRegs u).gpr r = u.gpr r := by
  simp [wipedRegs, XOp.exec, State.setXmm, State.setReg32, State.setReg, h]

theorem wipedRegs_wr (u : State) : (wipedRegs u).wr = u.wr := rfl

theorem wipeStores16_succ (w : Nat) :
    wipeStores16 (w + 1) =
      wipeStores16 w ++ ([.movdquStore { base := .rsp, disp := ((8 + 16 * w : Nat) : Int) } .xmm0] : List Instr) := by
  simp only [wipeStores16, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- The stores of `wipeStores16` change memory only in the region `R`, which
holds each of them and which `u` may write. -/
theorem wipeStores16_run (R : Region) (u : State) (hR : R ∈ u.wr) : ∀ n,
    (∀ k < n, R.Contains (u.gpr .rsp + BitVec.ofNat 64 (8 + 16 * k)) 16) →
    ∃ m', execBlock isa (wipeStores16 n) u =
        some ({ u with mem := m' },
          (List.range n).map fun k => .addr (u.gpr .rsp + BitVec.ofNat 64 (8 + 16 * k))) ∧
        Frame [R] u.mem m'
  | 0, _ => ⟨u.mem, rfl, Frame.refl _ _⟩
  | w + 1, hc => by
    obtain ⟨m', he, hf⟩ := wipeStores16_run R u hR w fun k hk => hc k (by omega_using [hk])
    have hin : InRegions u.wr (u.gpr .rsp + BitVec.ofNat 64 (8 + 16 * w)) 16 :=
      ⟨R, hR, hc w (by omega_using [])⟩
    refine ⟨m'.writeW (u.gpr .rsp + BitVec.ofNat 64 (8 + 16 * w)) (u.xmm .xmm0), ?_,
      hf.writeW (List.mem_singleton_self _) _ (hc w (by omega_using []))⟩
    rw [wipeStores16_succ, execBlock_append, he]
    simp only [Option.bind_some, execBlock, isa, exec, State.store128, State.ea, BitVec.ofInt_natCast,
      hin, ↓reduceIte, Option.map_some, addrs, List.map_cons, List.map_nil, List.append_nil,
      List.range_succ, List.map_append]

/-- `wipe words` from `u`, with the `words` quadwords at `rsp + 8` in the
region `R`, which `u` may write (`hc`, of every access within them): it
zeroes `xmm0` and `r11` (`wipedRegs`) and changes memory only in `R`, with a
trace of the addresses alone. -/
theorem wipe_run (R : Region) (u : State) (words : Nat) (hR : R ∈ u.wr)
    (hc : ∀ d n, d + n ≤ 8 * words → R.Contains (u.gpr .rsp + BitVec.ofNat 64 (8 + d)) n) :
    ∃ m', execBlock isa (wipe words) u =
        some ({ wipedRegs u with mem := m' }, wipeTrace (u.gpr .rsp) words) ∧
      Frame [R] u.mem m' := by
  have hsp : (wipedRegs u).gpr .rsp = u.gpr .rsp := wipedRegs_gpr u (by decide)
  have hR' : R ∈ (wipedRegs u).wr := by rw [wipedRegs_wr]; exact hR
  obtain ⟨m₁, he₁, hf₁⟩ := wipeStores16_run R (wipedRegs u) hR' (words / 2) fun k hk => by
    rw [hsp, show 8 + 16 * k = 8 + 16 * k from rfl]
    exact hc (16 * k) 16 (by omega_using [hk])
  have hR₁ : R ∈ ({ wipedRegs u with mem := m₁ } : State).wr := hR'
  obtain ⟨m₂, he₂, hf₂⟩ := wipeStoresAt_run R { wipedRegs u with mem := m₁ } (8 + 16 * (words / 2)) hR₁
    (words % 2) fun k hk => by
      show R.Contains ((wipedRegs u).gpr .rsp + _) 8
      rw [hsp, show 8 + 16 * (words / 2) + 8 * k = 8 + (16 * (words / 2) + 8 * k) by omega_using []]
      exact hc _ 8 (by omega_using [hk])
  refine ⟨m₂, ?_, fun a ha => (hf₂ a ha).trans (hf₁ a ha)⟩
  simp only [wipedRegs] at he₁ he₂ hsp
  simp only [wipe, execBlock, isa, exec, readSrc32, Option.map_some, addrs, srcAddrs, List.map_nil,
    List.nil_append]
  rw [execBlock_append, he₁, Option.bind_some, he₂]
  simp [wipeTrace, wipeAtTrace, wipedRegs, XOp.exec, State.setXmm, State.setReg32, State.setReg]

theorem wipe_spSafe (words : Nat) : (wipe words).all (fun i => !isa.writesSp i) = true := by
  simp [wipe, wipeStores16, wipeStoresAt, reduceInstrDst]

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes words : Nat}

/-- Code verified for a function whose last argument, in a register, is a
scratch buffer of `n` elements `e`, with `stack` bytes of stack, is verified
for the function without it, which allocates the buffer in a frame of
`bytes` more bytes of stack and zeroes its first `words` quadwords after the
code (`withStackScratchWiped`), if the postcondition reads the memory on
return only within the function's buffers (`hpost`). -/
theorem Verified.stackScratchWiped {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack))
    (hk : (sig.words abi.ptrBits).length < 6)
    (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 8 = 0 ∧ 8 + n * e.size ≤ bytes)
    (hst : stack + bytes + 8 ≤ 2 ^ 64)
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ stack)
    (hw : 8 * words ≤ n * e.size)
    (hpost : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true := by decide) :
    Verified target
      (withStackScratchWiped bytes (argRegs.getD (sig.words abi.ptrBits).length .rax) words c)
      (sig.contract abi pre post wa (stack + bytes)) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hsafe : SpSafe (.seq c (.block (wipe words)) : Prog isa) :=
    SpSafe.of_all (by simp only [Code.all, hsp, wipe_spSafe, Bool.and_self])
  have hdep : (Code.seq c (.block (wipe words)) : Prog isa).x86_64Depth ≤ stack := by
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
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s → ∃ t s₃ m',
      Exec isa c (narrow sig e n bytes s) t s₃ ∧
      (Sig.scratchContract abi sig nm e n pre post wa stack).post (narrow sig e n bytes s) s₃ ∧
      Frame [⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, n * e.size⟩] s₃.mem m' ∧
      Exec isa (withStackScratchWiped bytes (argRegs.getD (sig.words abi.ptrBits).length .rax) words c) s
        (t ++ wipeTrace (s.gpr .rsp - BitVec.ofNat 64 bytes) words)
        (popState bytes s { wipedRegs s₃ with mem := m' }) ∧
      abiPreserved s (popState bytes s { wipedRegs s₃ with mem := m' }) ∧
      Frame [⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩] m'
        (popState bytes s { wipedRegs s₃ with mem := m' }).mem ∧
      (popState bytes s { wipedRegs s₃ with mem := m' }).gpr .rax = s₃.gpr .rax := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrow_pre hk hb hst hs hl)
    have hrsp₃ : s₃.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes :=
      (ha.1 .rsp (by simp [calleeSaved])).trans (narrow_rsp hk s)
    have hwr₃ : s₃.wr = (narrow sig e n bytes s).wr := (Exec.rdwr he).2
    have hb0 := hb.1
    have hb3 := hb.2.2.2
    have hsb : stack + bytes ≤ (s.gpr .rsp).toNat := by
      have hs' := hs
      rw [pre_regs (by omega_using [hk]) hl] at hs'
      rcases hs'.1 with h | h <;> omega_using [h]
    obtain ⟨m', hblk, hfr⟩ := wipe_run ⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, n * e.size⟩ s₃ words
      (by rw [hwr₃, narrow_wr]; simp)
      (fun d m hdm => by
        have h8 := Offset.contains_base (s.gpr .rsp - BitVec.ofNat 64 bytes + 8) (d := d) (n := m)
          (k := n * e.size) (by omega_using [hw, hdm]) (by omega_using [hw, hb3, hsb, hdm])
        rwa [hrsp₃, show s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 + d) =
            s.gpr .rsp - BitVec.ofNat 64 bytes + 8 + BitVec.ofNat 64 d by
          rw [BitVec.add_assoc]; congr 1; exact (BitVec.ofNat_add_ofNat ..).symm])
    have he' := Exec.seq he (Exec.block hblk)
    rw [hrsp₃] at he'
    have ha' : abiPreserved (narrow sig e n bytes s) { wipedRegs s₃ with mem := m' } := by
      refine ⟨fun q hq => ?_, ?_, ha.2.2⟩
      · have hq' : q ≠ .r11 := by rintro rfl; simp [calleeSaved] at hq
        exact (wipedRegs_gpr s₃ hq').trans (ha.1 q hq)
      · rw [narrow_rsp hk]
        show m'.readW _ 64 = _
        rw [hfr.readW (r := ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, 8⟩) (Region.contains_self _ _)
          (fun r' hr' => by
            simp only [List.mem_singleton] at hr'; subst hr'
            exact Offset.base_disjoint _ (e := 8) (k := 8) (Nat.le_refl _) (by omega_using [hb3, hsb]))
          (by decide)]
        have h2 := ha.2.1
        rwa [narrow_rsp hk] at h2
    obtain ⟨hex, habi, hm, hrax⟩ := withStackScratch_run hk hb hst hsafe hdep hs he' ha' hl
    exact ⟨t, s₃, m', he, hq, hfr, hex, habi, hm, by rw [hrax]; exact wipedRegs_gpr s₃ (r := .rax) (by decide)⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, m', -, hq, hfr, hex, ha, hm, hrax⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_regs (by omega_using [hk])]
    have hq' := (post_regs (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
      (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega_using [hk])).mp hq
    rw [narrow_regArgs hk] at hq'
    rw [hrax]
    have h₃ := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params
      post _ _ (hlen s (by omega_using [hk]))) s.mem) s₃.mem) _) hq'
    refine hpost _ _ _ _ _ (hlen s (by omega_using [hk])) (fun b hb' a ha' => ?_) h₃
    -- The memory on return: after the wipe, which writes only the buffer,
    -- and the `free`, which loses only the frame.
    exact ((hm a fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact frame_disjoint (post := post) hk hb.1 hl hs b hb' a ha').trans (hfr a fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdisj s hs b hb' a ha')).symm
  · obtain ⟨u₁, _, _, f₁, _, _, x₁, _⟩ := hrun s₁ h₁
    obtain ⟨u₂, _, _, f₂, _, _, x₂, _⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1]
    have hsp₁₂ : s₁.gpr .rsp = s₂.gpr .rsp := ((pub_regs (by omega_using [hk]) hl).mp hp).1.1
    rw [hct _ _ _ _ _ _ (narrow_pre hk hb hst h₁ hl) (narrow_pre hk hb hst h₂ hl)
      (narrow_pub hk hp hl) f₁ f₂, hsp₁₂]

end

end VG.X86_64
