module
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.TCB.AArch64.Target

import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Mem

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

@[expose] public section

namespace VG.AArch64

open VG.Impl.StackScratch.AArch64

/-- The trace of `wipePairStores pairs` from a state whose `x16` is `p`. -/
def pairTrace (p : Addr) (pairs : Nat) : List Leak :=
  (List.range pairs).flatMap fun k =>
    [.addr (p + BitVec.ofNat 64 (16 * k)), .addr (p + BitVec.ofNat 64 (16 * k) + 8)]

/-- The trace of `wipePairChunks pairs` from a state whose stack pointer is `sp`. -/
def chunksTrace (sp : Addr) (pairs : Nat) : List Leak :=
  (List.range (pairs / 32)).flatMap (fun j => pairTrace (sp + BitVec.ofNat 64 (512 * j)) 32) ++
    if pairs % 32 = 0 then [] else pairTrace (sp + BitVec.ofNat 64 (512 * (pairs / 32))) (pairs % 32)

theorem wipePairStores_succ (w : Nat) :
    wipePairStores (w + 1) = wipePairStores w ++ ([.stp .x17 .x17 .x16 (16 * w)] : List Instr) := by
  simp only [wipePairStores, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- The doubleword `i` of the `2 * pairs` at `p` is in the region. -/
abbrev PairsIn (R : Region) (p : Addr) (words : Nat) : Prop :=
  ∀ i < words, R.Contains (p + BitVec.ofNat 64 (8 * i)) 8

/-- The stores of `wipePairStores` change memory only in the region `R`,
which holds each of them and which `u` may write. -/
theorem wipePairStores_run (R : Region) (u : State) (hR : R ∈ u.wr) : ∀ pairs, pairs ≤ 32 →
    PairsIn R (u.gpr .x16) (2 * pairs) →
    ∃ m', execBlock isa (wipePairStores pairs) u =
        some ({ u with mem := m' }, pairTrace (u.gpr .x16) pairs) ∧ Frame [R] u.mem m'
  | 0, _, _ => ⟨u.mem, rfl, Frame.refl _ _⟩
  | w + 1, hwb, hc => by
    obtain ⟨m', he, hf⟩ := wipePairStores_run R u hR w (by omega_using [hwb])
      fun i hi => hc i (by omega_using [hi])
    have hc₁ : R.Contains (u.gpr .x16 + BitVec.ofNat 64 (16 * w)) 8 := by
      have := hc (2 * w) (by omega_using []); rwa [show 8 * (2 * w) = 16 * w by omega_using []] at this
    have hc₂ : R.Contains (u.gpr .x16 + BitVec.ofNat 64 (16 * w) + 8) 8 := by
      have := hc (2 * w + 1) (by omega_using [])
      rwa [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, Offset.add_add_eq _ (c := 8 * (2 * w + 1))
        (by omega_using [])]
    have hin₁ : InRegions u.wr (u.gpr .x16 + BitVec.ofNat 64 (16 * w)) 8 := ⟨R, hR, hc₁⟩
    have hin₂ : InRegions u.wr (u.gpr .x16 + BitVec.ofNat 64 (16 * w) + 8) 8 := ⟨R, hR, hc₂⟩
    have hoff : 16 * w % 8 = 0 ∧ 16 * w ≤ 504 := ⟨by omega_using [], by omega_using [hwb]⟩
    refine ⟨(m'.write (u.gpr .x16 + BitVec.ofNat 64 (16 * w)) 8 ((u.read .x .x17).setWidth 64)).write
      (u.gpr .x16 + BitVec.ofNat 64 (16 * w) + 8) 8 ((u.read .x .x17).setWidth 64), ?_,
      (hf.write (List.mem_singleton_self _) _ hc₁).write (List.mem_singleton_self _) _ hc₂⟩
    rw [wipePairStores_succ, execBlock_append, he]
    simp only [Option.bind_some, execBlock, isa, exec, hoff, and_self, ↓reduceIte,
      State.store, hin₁, hin₂, Option.map_some, addrs, List.map_cons, List.map_nil, List.append_nil,
      pairTrace, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      State.read, Size.bits]

/-- Chunk `j` of the wipe from `u`: `x16` set to `sp + 512 j`, and memory
changed only in `R`. -/
theorem wipePairChunk_run (R : Region) (u : State) (hR : R ∈ u.wr) (j pairs : Nat)
    (hj : 512 * j < 4096) (hp : pairs ≤ 32) (hc : PairsIn R (u.sp + BitVec.ofNat 64 (512 * j)) (2 * pairs)) :
    ∃ m', execBlock isa (wipePairChunk j pairs) u =
        some ({ u.write .x .x16 (u.sp + BitVec.ofNat 64 (512 * j)) with mem := m' },
          pairTrace (u.sp + BitVec.ofNat 64 (512 * j)) pairs) ∧ Frame [R] u.mem m' := by
  have h16 : (u.write .x .x16 (u.sp + BitVec.ofNat 64 (512 * j))).gpr .x16 = u.sp + BitVec.ofNat 64 (512 * j) := by
    simp [State.write]
  obtain ⟨m', he, hf⟩ := wipePairStores_run R (u.write .x .x16 (u.sp + BitVec.ofNat 64 (512 * j)))
    (by simpa [State.write]) pairs hp (by rw [h16]; exact hc)
  refine ⟨m', ?_, by simpa [State.write] using hf⟩
  simp only [wipePairChunk, execBlock, isa, exec, hj, ↓reduceIte]
  rw [he, h16]
  simp [addrs]

/-- A state `u` with its registers but `x16` and `x17` and its memory changed. -/
def Wiped (u u' : State) : Prop :=
  ∃ g m', u' = { u with gpr := g, mem := m' } ∧ ∀ q, q ≠ .x16 → q ≠ .x17 → g q = u.gpr q

theorem Wiped.refl (u : State) : Wiped u u := ⟨u.gpr, u.mem, rfl, fun _ _ _ => rfl⟩

/-- The chunks of the wipe from a state `u` that may write `R`, which holds
the `2 * pairs` doublewords at `sp`: memory changes only in `R`, and the
trace is that of the stack pointer. -/
theorem wipePairChunks_run (R : Region) (u : State) (hR : R ∈ u.wr) (pairs : Nat) (hp : pairs ≤ 256)
    (hc : PairsIn R u.sp (2 * pairs)) :
    ∃ u', execBlock isa (wipePairChunks pairs) u = some (u', chunksTrace u.sp pairs) ∧
      Wiped u u' ∧ Frame [R] u.mem u'.mem := by
  -- The pairs of chunk `j`, of `q` pairs, are among those at `sp`.
  have hchunk : ∀ j q, 32 * j + q ≤ pairs → PairsIn R (u.sp + BitVec.ofNat 64 (512 * j)) (2 * q) :=
    fun j q hq i hi => by
      rw [Offset.add_add_eq _ (c := 8 * (64 * j + i)) (by omega_using [])]
      exact hc _ (by omega_using [hq, hi])
  -- Any state with `u`'s stack pointer and regions runs chunk `j` the same way.
  have hstep : ∀ (v : State) (j q : Nat), Wiped u v → Frame [R] u.mem v.mem → 32 * j + q ≤ pairs → 0 < q →
      q ≤ 32 →
      ∃ v', execBlock isa (wipePairChunk j q) v = some (v', pairTrace (u.sp + BitVec.ofNat 64 (512 * j)) q) ∧
        Wiped u v' ∧ Frame [R] u.mem v'.mem := by
    rintro v j q ⟨g, m, rfl, hg⟩ hf hq hq0 hq32
    obtain ⟨m', he, hf'⟩ := wipePairChunk_run R { u with gpr := g, mem := m } hR j q
      (by omega_using [hq, hp, hq0]) hq32 (hchunk j q hq)
    refine ⟨_, he, ⟨_, m', rfl, fun r h₁ h₂ => ?_⟩, fun a ha => (hf' a ha).trans (hf a ha)⟩
    simp only [State.write, h₁, ↓reduceIte]
    exact hg r h₁ h₂
  -- The full chunks, by induction.
  have hfull : ∀ n, n ≤ pairs / 32 →
      ∃ v, execBlock isa ((List.range n).flatMap fun j => wipePairChunk j 32) u =
          some (v, (List.range n).flatMap fun j => pairTrace (u.sp + BitVec.ofNat 64 (512 * j)) 32) ∧
        Wiped u v ∧ Frame [R] u.mem v.mem := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨u, rfl, Wiped.refl u, Frame.refl _ _⟩
    | succ n ih =>
      intro hn
      obtain ⟨v, he, hw, hf⟩ := ih (by omega_using [hn])
      obtain ⟨v', he', hw', hf'⟩ := hstep v n 32 hw hf (by omega_using [hn]) (by omega_using [])
        (by omega_using [])
      refine ⟨v', ?_, hw', hf'⟩
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        execBlock_append, he]
      simp only [Option.bind_some, he', Option.map_some, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
  obtain ⟨v, he, hw, hf⟩ := hfull (pairs / 32) (Nat.le_refl _)
  unfold wipePairChunks chunksTrace
  rw [execBlock_append, he]
  by_cases h0 : pairs % 32 = 0
  · simp only [h0, ↓reduceIte, Option.bind_some, execBlock, Option.map_some, List.append_nil]
    exact ⟨v, rfl, hw, hf⟩
  · obtain ⟨v', he', hw', hf'⟩ := hstep v (pairs / 32) (pairs % 32) hw hf (by omega_using [])
      (by omega_using [h0]) (by omega_using [])
    simp only [h0, ↓reduceIte, Option.bind_some, he', Option.map_some]
    exact ⟨v', rfl, hw', hf'⟩

/-- The trace of `wipe words` from a state whose stack pointer is `sp`. -/
def wipeTrace (sp : Addr) (words : Nat) : List Leak :=
  chunksTrace sp (words / 2) ++
    if words % 2 = 0 then [] else [.addr (sp + BitVec.ofNat 64 (8 * (words - 1)))]

/-- `wipe words` from `u`, with the `words` doublewords at `sp` in the region
`R`, which `u` may write: it writes only `x16` and `x17`, changes memory only
in `R`, and leaves a trace of the stack pointer alone. -/
theorem wipe_run (R : Region) (u : State) (words : Nat) (hR : R ∈ u.wr) (hwb : 8 * words ≤ 4096)
    (hc : ∀ k < words, R.Contains (u.sp + BitVec.ofNat 64 (8 * k)) 8) :
    ∃ u', execBlock isa (wipe words) u = some (u', wipeTrace u.sp words) ∧
      Wiped u u' ∧ Frame [R] u.mem u'.mem := by
  obtain ⟨u', he, ⟨g, m', rfl, hg⟩, hf⟩ := wipePairChunks_run R
    (u.write .x .x17 ((0 : BitVec 16).setWidth 64 <<< (16 * 0))) (by simpa [State.write]) (words / 2)
    (by omega_using [hwb]) (by simpa [State.write] using fun i hi => hc i (by omega_using [hi]))
  by_cases h0 : words % 2 = 0
  · refine ⟨_, ?_, ⟨g, m', rfl, fun q h₁ h₂ => ?_⟩, hf⟩
    · simp only [wipe, h0, ↓reduceIte, List.append_nil, execBlock, isa, exec,
        show 16 * 0 < Size.bits .x by decide]
      rw [he]
      simp [addrs, State.write, wipeTrace, h0]
    · rw [hg q h₁ h₂]; simp [State.write, h₂]
  · have hk : R.Contains (u.sp + BitVec.ofNat 64 (8 * (words - 1))) 8 := hc _ (by omega_using [h0])
    have hin : InRegions u.wr (u.sp + BitVec.ofNat 64 (8 * (words - 1))) 8 := ⟨R, hR, hk⟩
    have hoff : 8 * (words - 1) % 8 = 0 ∧ 8 * (words - 1) < 32768 :=
      ⟨by omega_using [], by omega_using [hwb]⟩
    refine ⟨_, ?_, ⟨g, m'.write (u.sp + BitVec.ofNat 64 (8 * (words - 1))) 8 ((g .x17).setWidth 64), rfl,
      fun q h₁ h₂ => ?_⟩, hf.write (List.mem_singleton_self _) _ hk⟩
    · have hm : isa.exec (.movz .x .x17 0 0) u = some (u.write .x .x17 ((0 : BitVec 16).setWidth 64 <<< (16 * 0))) := by
        simp [isa, exec]
      rw [show wipe words = .movz .x .x17 0 0 ::
          (wipePairChunks (words / 2) ++ ([.strSp .x17 (8 * (words - 1))] : List Instr)) by simp [wipe, h0],
        execBlock, hm]
      simp only []
      rw [execBlock_append, he]
      simp only [Option.bind_some, execBlock]
      simp [exec, addrs, State.write, State.store, State.read, wipeTrace, h0, hoff, hin]
    · rw [hg q h₁ h₂]; simp [State.write, h₂]

theorem wipe_spSafe (words : Nat) : (wipe words).all (fun i => !isa.writesSp i) = true := by
  simp only [wipe, wipePairChunks]
  split <;> split <;> simp [wipePairChunk, wipePairStores]

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
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s) :
    Verified target
      (withStackScratchWiped bytes (argRegs.getD (sig.words abi.ptrBits).length .x0) words c)
      (sig.contract abi pre post wa (stack + bytes)) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hlen := regArgs_length sig
  have hsb : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s → stack + bytes ≤ s.sp.toNat :=
    fun s hs => by
      rw [pre_regs (by omega_using [hk])] at hs
      rcases hs.1 with h | h <;> omega_using [h]
  -- The buffer, below the stack the contract without it reserves, so apart
  -- from its buffers.
  have hdisj : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s →
      ∀ b ∈ Sig.bufs sig.params (regArgs sig s),
        b.1.Disjoint ⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩ := by
    intro s hs b hb'
    have h0 := hsb s hs
    rw [pre_regs (by omega_using [hk])] at hs
    obtain ⟨-, -, -, -, hres, -, -⟩ := hs
    have hbelow : below s.sp (stack + bytes) ∈ stackBelow s.sp (stack + bytes) := by
      rw [stackBelow_pos _ (by omega_using [hb])]; simp
    have hscrSub : Region.Sub ⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩ (below s.sp (stack + bytes)) :=
      Offset.sub_below _ (by omega_using []) (by omega_using [hb])
    exact (Region.Disjoint.symm (hres _ hbelow b (List.mem_append_left _ hb'))).sub_right hscrSub
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
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrow_pre hk hb hs)
    have hsp₃ : s₃.sp = s.sp - BitVec.ofNat 64 bytes := ha.2.1.trans (narrow_sp s)
    have hwr₃ : s₃.wr = (narrow sig e n bytes s).wr := (Exec.rdwr he).2.1
    have h0 := hsb s hs
    obtain ⟨u', hblk, ⟨g, m', rfl, hg⟩, hfr⟩ := wipe_run ⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩ s₃ words
      (by rw [hwr₃, narrow_wr]; simp) (by have := hb.2.2.2; omega_using [hb, hw])
      (fun k hk' => by
        rw [hsp₃]; exact Offset.contains_base _ (by omega_using [hw, hk']) (by omega_using [hb, hw, hk']))
    have he' := Exec.seq he (Exec.block hblk)
    have ha' : abiPreserved (narrow sig e n bytes s) { s₃ with gpr := g, mem := m' } := by
      refine ⟨fun q hq => ?_, ha.2.1, ha.2.2⟩
      have h16 : q ≠ .x16 := by rintro rfl; simp [preserved] at hq
      have h17 : q ≠ .x17 := by rintro rfl; simp [preserved] at hq
      exact (hg q h16 h17).trans (ha.1 q hq)
    obtain ⟨hex, habi, hm, hgp⟩ := withStackScratch_run hk hb hs he' ha'
    refine ⟨t, s₃, _, he, hq, hfr, hsp₃, hex, habi, hm, ?_⟩
    rw [hgp]; exact hg .x0 (by decide) (by decide)
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, s₄, -, hq, hfr, -, hex, ha, hm, hx0⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_regs (by omega_using [hk])]
    have hq' := (post_regs (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
      (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega_using [hk])).mp hq
    rw [narrow_regArgs hk] at hq'
    rw [hm, hx0]
    have h₃ := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params
      post _ _ (hlen s (by omega_using [hk]))) s.mem) s₃.mem) _) hq'
    refine hpost _ _ _ _ _ (hlen s (by omega_using [hk])) (fun b hb' a ha' => ?_) h₃
    exact (hfr a fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdisj s hs b hb' a ha').symm
  · obtain ⟨u₁, _, _, f₁, _, _, p₁, x₁, _⟩ := hrun s₁ h₁
    obtain ⟨u₂, _, _, f₂, _, _, p₂, x₂, _⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, p₁, p₂]
    have hsp₁₂ : s₁.sp = s₂.sp := ((pub_regs (by omega_using [hk])).mp hp).1.1
    rw [hct _ _ _ _ _ _ (narrow_pre hk hb h₁) (narrow_pre hk hb h₂) (narrow_pub hk hp) f₁ f₂,
      hsp₁₂]

end

end VG.AArch64
