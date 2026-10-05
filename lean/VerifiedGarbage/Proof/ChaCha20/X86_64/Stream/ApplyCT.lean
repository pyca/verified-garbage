import VerifiedGarbage.Proof.ChaCha20.X86_64.Stream.Init
import VerifiedGarbage.Proof.ChaCha20.X86_64.Xor
import VerifiedGarbage.Proof.ChaCha20.X86_64.Variant
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.X86_64.Stream.Bytes`. -/
section

/-!
# Streaming ChaCha20 on x86-64: XORing bytes

Untrusted: everything here is checked by Lean. `xorBytes` XORs the `rdx`
bytes at `rsi` into those at `rbp`, one at a time.
-/

namespace VG.Proof.ChaCha20.X86_64.Stream

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Stream
open VG.Impl.ChaCha20.X86_64.Xor (xorLoop dataByte ksByte)
open VG.Proof.ChaCha20.X86_64 (toNat_ofNat_lt)
open VG.Proof.ChaCha20.X86_64.Xor (xorBody xorLoop_eq writeW8_apply xor_setWidth se1)

/-- What `xorBytes` needs: `c` bytes at `D` to write and at `K` to read, not
overlapping. -/
structure BPre (s : State) (D K : Addr) (c : Nat) : Prop where
  rbp : s.gpr .rbp = D
  rsi : s.gpr .rsi = K
  rdx : s.gpr .rdx = BitVec.ofNat 64 c
  c_lt : c ≤ 2 ^ 32
  wD : ∀ k < c, InRegions s.wr (D + BitVec.ofNat 64 k) 1
  rK : ∀ k < c, InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 k) 1
  sep : ∀ j < c, ∀ k < c, D + BitVec.ofNat 64 j ≠ K + BitVec.ofNat 64 k

/-- What `xorBytes` leaves: the bytes XORed, `rbp` past them and `r12`
less their number; only `rax`, `r8`, `rcx`, `rbp`, `r12` and the flags are
written. -/
structure BPost (s : State) (D K : Addr) (c : Nat) (s' : State) : Prop where
  rbp : s'.gpr .rbp = D + BitVec.ofNat 64 c
  r12 : s'.gpr .r12 = s.gpr .r12 - BitVec.ofNat 64 c
  keep : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .rcx → r ≠ .rbp → r ≠ .r12 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  data : ∀ k < c, s'.mem (D + BitVec.ofNat 64 k) = s.mem (D + BitVec.ofNat 64 k) ^^^ s.mem (K + BitVec.ofNat 64 k)
  frame : Frame [⟨D, c⟩] s.mem s'.mem

/-- Before byte `i`. -/
structure LInv (s : State) (D K : Addr) (c i : Nat) (s' : State) : Prop where
  rcx : s'.gpr .rcx = BitVec.ofNat 64 i
  keep : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .rcx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  data : ∀ k < c, s'.mem (D + BitVec.ofNat 64 k) =
    if k < i then s.mem (D + BitVec.ofNat 64 k) ^^^ s.mem (K + BitVec.ofNat 64 k) else s.mem (D + BitVec.ofNat 64 k)
  frame : Frame [⟨D, c⟩] s.mem s'.mem

theorem D_ne {D : Addr} {c j k : Nat} (hc : c ≤ 2 ^ 32) (hj : j < c) (hk : k < c) (h : j ≠ k) :
    D + BitVec.ofNat 64 j ≠ D + BitVec.ofNat 64 k := by
  intro he
  have e : BitVec.ofNat 64 j = BitVec.ofNat 64 k := by
    have e := congrArg (· - D) he; simpa using e
  have := congrArg BitVec.toNat e
  rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at this
  exact h this

theorem contains_byte {D : Addr} {c k : Nat} (hk : k < c) (hc : c ≤ 2 ^ 32) :
    (⟨D, c⟩ : Region).Contains (D + BitVec.ofNat 64 k) 1 :=
  Offset.contains_base D (by omega) (by omega)

/-- A byte read is outside the bytes written. -/
theorem not_contains {D K : Addr} {c i : Nat}
    (hs : ∀ j < c, ∀ k < c, D + BitVec.ofNat 64 j ≠ K + BitVec.ofNat 64 k) (hi : i < c)
    (h : (⟨D, c⟩ : Region).Contains (K + BitVec.ofNat 64 i) 1) : False := by
  simp only [Region.Contains] at h
  refine hs (K + BitVec.ofNat 64 i - D).toNat (by omega) i hi ?_
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

set_option simprocs false in
theorem byte_step {s : State} {D K : Addr} {c i : Nat} (hp : VG.Proof.ChaCha20.X86_64.Stream.BPre s D K c) (hi : i < c) {s₁ : State}
    (h : VG.Proof.ChaCha20.X86_64.Stream.LInv s D K c i s₁) :
    WP isa (.block xorBody) s₁ fun s' =>
      VG.Proof.ChaCha20.X86_64.Stream.LInv s D K c (i + 1) s' ∧ s'.zf = some (decide (i + 1 = c)) := by
  have hc := hp.c_lt
  have ea₁ : D + BitVec.ofNat 64 i * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = D + BitVec.ofNat 64 i := by simp
  have ea₂ : K + BitVec.ofNat 64 i * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = K + BitVec.ofNat 64 i := by simp
  have i₁ : InRegions (s₁.rd ++ s₁.wr) (D + BitVec.ofNat 64 i) 1 := by
    obtain ⟨r, hr, hc⟩ := hp.wD i hi; exact ⟨r, by rw [h.rd, h.wr]; exact List.mem_append_right _ hr, hc⟩
  have i₂ : InRegions (s₁.rd ++ s₁.wr) (K + BitVec.ofNat 64 i) 1 := by rw [h.rd, h.wr]; exact hp.rK i hi
  have o₁ : InRegions s₁.wr (D + BitVec.ofNat 64 i) 1 := by rw [h.wr]; exact hp.wD i hi
  have hrbp : s₁.gpr .rbp = D := by rw [h.keep _ (by decide) (by decide) (by decide), hp.rbp]
  have hrsi : s₁.gpr .rsi = K := by rw [h.keep _ (by decide) (by decide) (by decide), hp.rsi]
  have hrdx : s₁.gpr .rdx = BitVec.ofNat 64 c := by rw [h.keep _ (by decide) (by decide) (by decide), hp.rdx]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [xorBody, dataByte, ksByte, runBlock_cons, runStep_some,
    runBlock_nil, exec, State.ea, readSrc, execAlu, arithFlags, State.load8, State.store8,
    State.setReg, State.setFlags, hrbp, hrsi, h.rcx, ea₁, ea₂, i₁, i₂, o₁, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', se1]
  have hd : s₁.mem (D + BitVec.ofNat 64 i) = s.mem (D + BitVec.ofNat 64 i) := by
    rw [h.data _ hi]; simp
  have hk : s₁.mem (K + BitVec.ofNat 64 i) = s.mem (K + BitVec.ofNat 64 i) :=
    h.frame _ fun r hr hcont => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Proof.ChaCha20.X86_64.Stream.not_contains hp.sep hi hcont
  rw [hd, hk, xor_setWidth]
  refine ⟨⟨by simp [BitVec.ofNat_add], fun r h₁ h₂ h₃ => ?_, h.rd, h.wr, fun k hk' => ?_,
    h.frame.writeW (List.mem_singleton_self _) _ (VG.Proof.ChaCha20.X86_64.Stream.contains_byte hi hc)⟩, ?_⟩
  · simp only [h₁, h₂, h₃, ite_false]; exact h.keep r h₁ h₂ h₃
  · dsimp only; rw [writeW8_apply]
    by_cases he : k = i
    · subst he; simp
    · simp only [VG.Proof.ChaCha20.X86_64.Stream.D_ne hc hk' hi he, ite_false]
      rw [h.data k hk']
      by_cases h₁ : k < i
      · simp [h₁, show k < i + 1 by omega]
      · simp [h₁, show ¬ k < i + 1 by omega]
  · rw [hrdx, ← Offset.ofNat_sub_ofNat_beq (x := i + 1) (y := c) (by omega) (by omega), BitVec.ofNat_add]
    rfl


theorem loop_ok {s : State} {D K : Addr} {c : Nat} (hp : VG.Proof.ChaCha20.X86_64.Stream.BPre s D K c) (hc0 : 0 < c) {s₁ : State}
    (h : VG.Proof.ChaCha20.X86_64.Stream.LInv s D K c 0 s₁) : WP isa xorLoop s₁ (VG.Proof.ChaCha20.X86_64.Stream.LInv s D K c c) := by
  rw [xorLoop_eq]
  let Inv : Nat → State → Prop := fun n s' => ∃ i, n = c - i ∧ i < c ∧ VG.Proof.ChaCha20.X86_64.Stream.LInv s D K c i s'
  have hstep : ∀ n s', Inv n s' → WP isa (.block xorBody) s' (fun s'' =>
      (VG.X86_64.eval .ne s'' = some false ∧ VG.Proof.ChaCha20.X86_64.Stream.LInv s D K c c s'') ∨ (VG.X86_64.eval .ne s'' = some true ∧ ∃ n' < n, Inv n' s'')) := by
    rintro n s' ⟨i, rfl, hi, hI⟩
    refine WP.mono (VG.Proof.ChaCha20.X86_64.Stream.byte_step hp hi hI) fun s'' ⟨h', hz⟩ => ?_
    by_cases hl : i + 1 = c
    · exact .inl ⟨by simp [VG.X86_64.eval, hz, hl], hl ▸ h'⟩
    · exact .inr ⟨by simp [VG.X86_64.eval, hz, hl], c - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
  exact WP.loop (M := isa) Inv hstep c s₁ ⟨0, by simp, hc0, h⟩

theorem xorBytes_eq : xorBytes =
    .seq (.block [.mov32 .rcx (.imm 0), .alu .test .rdx (.reg .rdx)])
      (.seq (.ite .e (.block []) xorLoop) (.block [.alu .add .rbp (.reg .rdx), .alu .sub .r12 (.reg .rdx)])) :=
  rfl

set_option simprocs false in
theorem xorBytes_ok {s : State} {D K : Addr} {c : Nat} (hp : VG.Proof.ChaCha20.X86_64.Stream.BPre s D K c) :
    WP isa xorBytes s (VG.Proof.ChaCha20.X86_64.Stream.BPost s D K c) := by
  have hc := hp.c_lt
  have h₁ : WP isa (.block [.mov32 .rcx (.imm 0), .alu .test .rdx (.reg .rdx)]) s fun s₁ =>
      VG.Proof.ChaCha20.X86_64.Stream.LInv s D K c 0 s₁ ∧ s₁.zf = some (decide (c = 0)) := by
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      readSrc32, execAlu, arithFlags, State.setReg, State.setReg32, State.setFlags, Option.map_some,
      Option.bind_some, Option.some.injEq, exists_eq_left', ite_false]
    refine ⟨⟨by simp, fun r h₁ h₂ h₃ => by simp [h₃], rfl, rfl, fun k hk => by simp, Frame.refl _ _⟩, ?_⟩
    rw [BitVec.and_self, hp.rdx, ← Offset.ofNat_sub_ofNat_beq (x := c) (y := 0) (by omega) (by omega)]
    simp
  rw [VG.Proof.ChaCha20.X86_64.Stream.xorBytes_eq]
  refine WP.seq (WP.mono h₁ fun s₁ ⟨hI, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.ChaCha20.X86_64.Stream.LInv s D K c c) ?_ fun s₂ h₂ => ?_)
  · refine WP.ite (decide (c = 0)) (by simp [VG.X86_64.eval, hz]) (fun h0 => WP.block_nil (M := isa) ?_) (fun h0 => VG.Proof.ChaCha20.X86_64.Stream.loop_ok hp ?_ hI)
    · simp only [decide_eq_true_eq] at h0; subst h0; exact hI
    · simp only [decide_eq_false_iff_not] at h0; omega
  · have hrdx : s₂.gpr .rdx = BitVec.ofNat 64 c := by rw [h₂.keep _ (by decide) (by decide) (by decide), hp.rdx]
    have hrbp : s₂.gpr .rbp = D := by rw [h₂.keep _ (by decide) (by decide) (by decide), hp.rbp]
    have hr12 : s₂.gpr .r12 = s.gpr .r12 := h₂.keep _ (by decide) (by decide) (by decide)
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, arithFlags, State.setReg, State.setFlags, Option.bind_some,
      Option.some.injEq, exists_eq_left', ite_false, hrdx, hrbp, hr12]
    refine ⟨by simp (config := {decide := true}), by simp (config := {decide := true}),
      fun r e₁ e₂ e₃ e₄ e₅ => ?_, h₂.rd, h₂.wr, fun k hk => ?_, h₂.frame⟩
    · simp only [e₄, e₅, ite_false]; exact h₂.keep r e₁ e₂ e₃
    · rw [h₂.data k hk, ite_pos hk]

end VG.Proof.ChaCha20.X86_64.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.X86_64.Stream.Calls`. -/
section

/-!
# Streaming ChaCha20 on x86-64: the calls

Untrusted: everything here is checked by Lean. The calls of
`vg_chacha20_block` and of an implementation of `vg_chacha20_xor`, from their
proofs of correctness (with `WP.call`), as ChaCha20-Poly1305 makes them.
-/

namespace VG.Proof.ChaCha20.X86_64.Stream

open VG VG.X86_64
open VG.Spec.ChaCha20 (stateAt keystream bytesAt)
open VG.Proof.ChaCha20.X86_64.Xor (stateAt_frame)

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- The return address a call stores. -/
theorem callEntry_frame (s : State) : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

theorem callEntry_gpr' (s : State) {r : Reg} (h : r ≠ .rsp) : s.callEntry.gpr r = s.gpr r :=
  State.callEntry_gpr s h

theorem block_call {s : State} {S B : Addr} (hrdi : s.gpr .rdi = S) (hrsi : s.gpr .rsi = B)
    (hdj : (⟨B, 256⟩ : Region).Disjoint ⟨S, 64⟩)
    (hsB : (below (s.gpr .rsp) 8).Disjoint ⟨B, 256⟩) (hsS : (below (s.gpr .rsp) 8).Disjoint ⟨S, 64⟩)
    (hc : Covers ([⟨S, 64⟩] ++ [⟨B, 256⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨B, 256⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨B, 256⟩, below (s.gpr .rsp) 8] s.mem s'.mem → s'.gpr .rsi = B →
      stateAt s'.mem B = Spec.ChaCha20.block (stateAt s.mem S) → Q s') :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.X86_64.block) s Q := by
  refine WP.call (k := Proof.ChaCha20.blockX86_64) Proof.ChaCha20.X86_64.block_correct
    (Proof.ChaCha20.X86_64.Xor.block_keeps_reg (by simp [Proof.ChaCha20.X86_64.Xor.kept]))
    (by rw [Proof.ChaCha20.X86_64.Xor.block_depth]; decide) (rd := [⟨S, 64⟩]) (wr := [⟨B, 256⟩]) ?_ hc hw ?_
  · simp only [Proof.ChaCha20.blockX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, VG.Proof.ChaCha20.X86_64.Stream.callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp),
      VG.Proof.ChaCha20.X86_64.Stream.callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp), hrdi, hrsi]
    exact ⟨trivial, trivial, hdj, hsB⟩
  · intro s' hrd hwr hcs hf hkeep ⟨s₂, hm₂, _, hpost⟩
    rw [Proof.ChaCha20.X86_64.Xor.block_depth] at hf
    refine hQ s' hrd hwr hcs hf (by rw [hkeep .rsi (Proof.ChaCha20.X86_64.Xor.block_keeps_reg
      (by simp [Proof.ChaCha20.X86_64.Xor.kept])), hrsi]) ?_
    simp only [Proof.ChaCha20.blockX86_64, State.withRegions_gpr, State.withRegions_mem,
      VG.Proof.ChaCha20.X86_64.Stream.callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp), VG.Proof.ChaCha20.X86_64.Stream.callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp), hrdi,
      hrsi, hm₂] at hpost
    rwa [stateAt_frame (VG.Proof.ChaCha20.X86_64.Stream.callEntry_frame s) (by simpa using hsS.symm)] at hpost

theorem below8_24 (s : State) : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) 24) :=
  below_sub (by decide) (by decide)

/-- The precondition of the implementation `v` of `vg_chacha20_xor`, called
with 24 bytes of stack below `rsp`: 8 for its return address, and at most 16
for its calls. -/
theorem xor_pre (v : Proof.ChaCha20.X86_64.XorImpl) {s : State} {S D B : Addr} {n : Nat}
    (hrdi : s.gpr .rdi = S) (hrsi : s.gpr .rsi = D)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 n) (hrcx : s.gpr .rcx = B) (hn : n < 2 ^ 64)
    (hSD : (⟨S, 64⟩ : Region).Disjoint ⟨D, n⟩) (hSB : (⟨S, 64⟩ : Region).Disjoint ⟨B, 320⟩)
    (hDB : (⟨D, n⟩ : Region).Disjoint ⟨B, 320⟩) (hwrap : D.toNat + n ≤ 2 ^ 64)
    (hsS : (below (s.gpr .rsp) 24).Disjoint ⟨S, 64⟩) (hsD : (below (s.gpr .rsp) 24).Disjoint ⟨D, n⟩)
    (hsB : (below (s.gpr .rsp) 24).Disjoint ⟨B, 320⟩) :
    (Proof.ChaCha20.xorStack v.stack).pre (s.callEntry.withRegions [] [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  have hk := v.stack_le
  have h8 := VG.Proof.ChaCha20.X86_64.Stream.below8_24 s
  have hk' : Region.Sub ⟨s.gpr .rsp - 8 - BitVec.ofNat 64 v.stack, v.stack⟩ (below (s.gpr .rsp) 24) := by
    rw [show s.gpr .rsp - 8 - BitVec.ofNat 64 v.stack = s.gpr .rsp - BitVec.ofNat 64 (8 + v.stack) by
      rw [BitVec.sub_sub, BitVec.ofNat_add]; rfl]
    exact Offset.sub_below _ (by omega) (by omega)
  simp only [Proof.ChaCha20.xorStack, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, VG.Proof.ChaCha20.X86_64.Stream.callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp),
    VG.Proof.ChaCha20.X86_64.Stream.callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp), VG.Proof.ChaCha20.X86_64.Stream.callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp),
    VG.Proof.ChaCha20.X86_64.Stream.callEntry_gpr' s (by decide : Reg.rcx ≠ .rsp), hrdi, hrsi, hrdx, hrcx, hn']
  exact ⟨trivial, trivial, hSD, hSB, hDB, hsS.sub_left h8, hsD.sub_left h8, hsB.sub_left h8,
    hsS.sub_left hk', hsD.sub_left hk', hsB.sub_left hk', hwrap⟩

/-- A call of the implementation `v` of `vg_chacha20_xor` (see `xor_pre`). -/
theorem xor_call (v : Proof.ChaCha20.X86_64.XorImpl) {s : State} {S D B : Addr} {n : Nat}
    (hrdi : s.gpr .rdi = S) (hrsi : s.gpr .rsi = D)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 n) (hrcx : s.gpr .rcx = B) (hn : n < 2 ^ 64)
    (hSD : (⟨S, 64⟩ : Region).Disjoint ⟨D, n⟩) (hSB : (⟨S, 64⟩ : Region).Disjoint ⟨B, 320⟩)
    (hDB : (⟨D, n⟩ : Region).Disjoint ⟨B, 320⟩) (hwrap : D.toNat + n ≤ 2 ^ 64)
    (hsS : (below (s.gpr .rsp) 24).Disjoint ⟨S, 64⟩) (hsD : (below (s.gpr .rsp) 24).Disjoint ⟨D, n⟩)
    (hsB : (below (s.gpr .rsp) 24).Disjoint ⟨B, 320⟩)
    (hc : Covers ([] ++ [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩, below (s.gpr .rsp) 24] s.mem s'.mem →
      bytesAt s'.mem D n = List.zipWith (· ^^^ ·) (bytesAt s.mem D n) (keystream (stateAt s.mem S) n) →
      Q s') :
    WP isa (.call v.callee.name v.callee.code) s Q := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  have hd := v.depth_le
  have h8 := VG.Proof.ChaCha20.X86_64.Stream.below8_24 s
  refine WP.call (k := Proof.ChaCha20.xorStack v.stack) v.ok v.nosp (by omega)
    (VG.Proof.ChaCha20.X86_64.Stream.xor_pre v hrdi hrsi hrdx hrcx hn hSD hSB hDB hwrap hsS hsD hsB) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost, _⟩
  have hf' : Frame [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩, below (s.gpr .rsp) 24] s.mem s'.mem := by
    refine hf.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨below (s.gpr .rsp) 24, by simp, below_sub (by omega) (by omega)⟩
  refine hQ s' hrd hwr hcs hf' ?_
  simp only [Proof.ChaCha20.xorX86_64, State.withRegions_gpr, State.withRegions_mem,
    VG.Proof.ChaCha20.X86_64.Stream.callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp), VG.Proof.ChaCha20.X86_64.Stream.callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp),
    VG.Proof.ChaCha20.X86_64.Stream.callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp), hrdi, hrsi, hrdx, hn', hm₂] at hpost
  rw [hpost, VG.Proof.ChaCha20.X86_64.Stream.bytesAt_frame (VG.Proof.ChaCha20.X86_64.Stream.callEntry_frame s) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hsD.sub_left h8).symm) (by omega),
    stateAt_frame (VG.Proof.ChaCha20.X86_64.Stream.callEntry_frame s) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hsS.sub_left h8).symm)]

end VG.Proof.ChaCha20.X86_64.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.X86_64.Stream.Apply`. -/
section

/-!
# Streaming ChaCha20 on x86-64: `apply`, correctness

Untrusted: everything here is checked by Lean. The pieces of `apply`
(`Impl/ChaCha20/X86_64/Stream.lean`), each from what holds before it
(`Q0` … `Q3`), and the whole function, for any implementation `v` of
`vg_chacha20_xor`. The pieces are those that the proof of constant time
(`ApplyCT.lean`) relates in two runs.
-/

namespace VG.Proof.ChaCha20

open VG.X86_64
open VG.Spec.ChaCha20 (keyAt restAt leftAt bytesAt)

/-- x86-64 contract for `vg_chacha20_apply(state = rdi, data = rsi, len = rdx) -> eax`,
with 24 bytes of stack below the return address (8 for the return address
of a call, and 16 for the calls of any implementation of `vg_chacha20_xor`). -/
def applyX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 768⟩
    let data : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 24, 24⟩
    s.rd = [] ∧ s.wr = [state, data] ∧ state.Disjoint data ∧
    ret.Disjoint state ∧ ret.Disjoint data ∧ stack.Disjoint state ∧ stack.Disjoint data ∧
    (s.gpr .rdi).toNat + 768 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64
  post s s' :=
    keyAt s'.mem (s.gpr .rdi) = keyAt s.mem (s.gpr .rdi) ∧
      if (s.gpr .rdx).toNat ≤ leftAt s.mem (s.gpr .rdi) then
        (s'.gpr .rax).setWidth 32 = 1 ∧
          bytesAt s'.mem (s.gpr .rsi) (s.gpr .rdx).toNat =
            List.zipWith (· ^^^ ·) (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
              ((restAt s.mem (s.gpr .rdi)).take (s.gpr .rdx).toNat) ∧
          restAt s'.mem (s.gpr .rdi) = (restAt s.mem (s.gpr .rdi)).drop (s.gpr .rdx).toNat
      else
        (s'.gpr .rax).setWidth 32 = 0 ∧
          bytesAt s'.mem (s.gpr .rsi) (s.gpr .rdx).toNat = bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat ∧
          restAt s'.mem (s.gpr .rdi) = restAt s.mem (s.gpr .rdi)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rsp = s₂.gpr .rsp ∧ [leftAt s₁.mem (s₁.gpr .rdi)] = [leftAt s₂.mem (s₂.gpr .rdi)]

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.X86_64.Stream

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Stream
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Proof.ChaCha20.X86_64 (toNat_ofNat_lt contains_off ea_at ofInt_natCast off_sep)
open VG.Spec.ChaCha20 (keyAt restAt leftAt bytesAt stateAt serialize block)

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev st : Addr := s₀.gpr .rdi
abbrev dp : Addr := s₀.gpr .rsi
abbrev L : Nat := (s₀.gpr .rdx).toNat
/-- The number of bytes of keystream left, and those in the buffered block. -/
abbrev N : Nat := leftAt s₀.mem (VG.Proof.ChaCha20.X86_64.Stream.st s₀)
abbrev O : Nat := VG.Proof.ChaCha20.X86_64.Stream.N s₀ % 64
/-- The bytes from the buffered block, the whole blocks and the bytes of the
next block that `apply` uses. -/
abbrev H : Nat := headLen s₀.mem (VG.Proof.ChaCha20.X86_64.Stream.st s₀) (VG.Proof.ChaCha20.X86_64.Stream.L s₀)
abbrev NB : Nat := blocksOf s₀.mem (VG.Proof.ChaCha20.X86_64.Stream.st s₀) (VG.Proof.ChaCha20.X86_64.Stream.L s₀)
abbrev T : Nat := tailLen s₀.mem (VG.Proof.ChaCha20.X86_64.Stream.st s₀) (VG.Proof.ChaCha20.X86_64.Stream.L s₀)
abbrev S0 : CState := stateAt s₀.mem (VG.Proof.ChaCha20.X86_64.Stream.st s₀)
abbrev D0 (k : Nat) : Byte := s₀.mem (VG.Proof.ChaCha20.X86_64.Stream.dp s₀ + BitVec.ofNat 64 k)
abbrev stR : Region := ⟨VG.Proof.ChaCha20.X86_64.Stream.st s₀, 768⟩
abbrev dR : Region := ⟨VG.Proof.ChaCha20.X86_64.Stream.dp s₀, VG.Proof.ChaCha20.X86_64.Stream.L s₀⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := ⟨s₀.gpr .rsp - 24, 24⟩
/-- The keystream byte XORed into byte `k` of the data. -/
abbrev KS (k : Nat) : Byte :=
  if k < VG.Proof.ChaCha20.X86_64.Stream.H s₀ then s₀.mem (VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 (128 - VG.Proof.ChaCha20.X86_64.Stream.O s₀ + k))
  else (serialize (block (ctr (VG.Proof.ChaCha20.X86_64.Stream.S0 s₀) ((k - VG.Proof.ChaCha20.X86_64.Stream.H s₀) / 64)))).getD ((k - VG.Proof.ChaCha20.X86_64.Stream.H s₀) % 64) 0
/-- The data with its first `j` bytes XORed. -/
abbrev Done (j : Nat) (m : Mem) : Prop :=
  ∀ k < VG.Proof.ChaCha20.X86_64.Stream.L s₀, m (VG.Proof.ChaCha20.X86_64.Stream.dp s₀ + BitVec.ofNat 64 k) = if k < j then VG.Proof.ChaCha20.X86_64.Stream.D0 s₀ k ^^^ VG.Proof.ChaCha20.X86_64.Stream.KS s₀ k else VG.Proof.ChaCha20.X86_64.Stream.D0 s₀ k
end

theorem L_lt (s₀ : State) : VG.Proof.ChaCha20.X86_64.Stream.L s₀ < 2 ^ 64 := (s₀.gpr .rdx).isLt
theorem N_lt (s₀ : State) : VG.Proof.ChaCha20.X86_64.Stream.N s₀ < 2 ^ 64 := (s₀.mem.readW (VG.Proof.ChaCha20.X86_64.Stream.st s₀ + 128) 64).isLt

structure APre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [VG.Proof.ChaCha20.X86_64.Stream.stR s₀, VG.Proof.ChaCha20.X86_64.Stream.dR s₀]
  st_d : (VG.Proof.ChaCha20.X86_64.Stream.stR s₀).Disjoint (VG.Proof.ChaCha20.X86_64.Stream.dR s₀)
  ret_st : (VG.Proof.ChaCha20.X86_64.Stream.retR s₀).Disjoint (VG.Proof.ChaCha20.X86_64.Stream.stR s₀)
  ret_d : (VG.Proof.ChaCha20.X86_64.Stream.retR s₀).Disjoint (VG.Proof.ChaCha20.X86_64.Stream.dR s₀)
  stk_st : (VG.Proof.ChaCha20.X86_64.Stream.stkR s₀).Disjoint (VG.Proof.ChaCha20.X86_64.Stream.stR s₀)
  stk_d : (VG.Proof.ChaCha20.X86_64.Stream.stkR s₀).Disjoint (VG.Proof.ChaCha20.X86_64.Stream.dR s₀)
  wrap_st : (VG.Proof.ChaCha20.X86_64.Stream.st s₀).toNat + 768 ≤ 2 ^ 64
  wrap_d : (VG.Proof.ChaCha20.X86_64.Stream.dp s₀).toNat + VG.Proof.ChaCha20.X86_64.Stream.L s₀ ≤ 2 ^ 64

theorem APre.of (s₀ : State) (h : Proof.ChaCha20.applyX86_64.pre s₀) : VG.Proof.ChaCha20.X86_64.Stream.APre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- Our caller's `rbx, rbp, r12`, and the bytes left after `apply`. -/
structure Saved (s₀ : State) (m : Mem) : Prop where
  rbx : m.readW (off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 576) 64 = s₀.gpr .rbx
  rbp : m.readW (off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 584) 64 = s₀.gpr .rbp
  r12 : m.readW (off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 592) 64 = s₀.gpr .r12
  left : m.readW (off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 600) 64 = BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.N s₀ - VG.Proof.ChaCha20.X86_64.Stream.L s₀)

/-! ## Regions -/

theorem APre.w_st {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Stream.APre s₀) {d n : Nat} (h : d + n ≤ 768) :
    InRegions s₀.wr (off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) d) n :=
  ⟨VG.Proof.ChaCha20.X86_64.Stream.stR s₀, by rw [hp.wr]; exact List.mem_cons_self .., contains_off h (by omega)⟩

theorem APre.r_st {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Stream.APre s₀) {d n : Nat} (h : d + n ≤ 768) :
    InRegions (s₀.rd ++ s₀.wr) (off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) d) n := by
  rw [hp.rd, List.nil_append]; exact hp.w_st h

/-! ## The check -/

/-- After the check: `rax` holds the bytes left, and the carry whether they
are fewer than `len`. -/
structure Q0 (s₀ s : State) : Prop where
  rax : s.gpr .rax = BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.N s₀)
  cf : s.cf = some (decide (VG.Proof.ChaCha20.X86_64.Stream.N s₀ < VG.Proof.ChaCha20.X86_64.Stream.L s₀))
  keep : ∀ r, r ≠ .rax → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

set_option simprocs false in
theorem check_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Stream.APre s₀) : WP isa (.block check) s₀ (VG.Proof.ChaCha20.X86_64.Stream.Q0 s₀) := by
  have i₁ := hp.r_st (d := 128) (n := 8) (by decide)
  simp only [off] at i₁
  apply WP.of_runBlock
  simp only [check, runBlock_cons, runStep_some, runBlock_nil, exec,
    ea_at, readSrc, execAlu, arithFlags, State.load64, State.setReg, State.setFlags, i₁, ite_true,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  have hn : s₀.mem.readW (VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofInt 64 ((128 : Nat) : Int)) 64 = BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.N s₀) := by
    rw [ofInt_natCast]; simp [VG.Proof.ChaCha20.X86_64.Stream.N, leftAt]
  have hn' : s₀.mem.readW (s₀.gpr .rdi + 128) 64 = BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.N s₀) := by simp [VG.Proof.ChaCha20.X86_64.Stream.N, leftAt]
  refine ⟨hn', ?_, fun r hr => by simp [hr], rfl, rfl, rfl⟩
  simp only [hn, toNat_ofNat_lt (VG.Proof.ChaCha20.X86_64.Stream.N_lt s₀)]
  rfl


/-! ## The bytes left in the buffered block -/

/-- `and` with `-64` rounds down to a multiple of 64. -/
theorem and_mask (x : BitVec 64) :
    x &&& BitVec.signExtend 64 (0xffffffc0 : BitVec 32) = BitVec.ofNat 64 (x.toNat / 64 * 64) := by
  have : BitVec.signExtend 64 (0xffffffc0 : BitVec 32) = BitVec.ofNat 64 ((2 ^ 58 - 1) <<< 6) := by decide
  rw [this]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hx := x.isLt
  generalize x.toNat = n at *
  rw [Nat.mod_eq_of_lt (by decide), Nat.mod_eq_of_lt (by omega),
    show n / 64 * 64 = (n >>> 6) <<< 6 by rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : 6 ≤ i
  · by_cases h2 : i - 6 < 58
    · simp [hi, h2, show 6 + (i - 6) = i by omega]
    · have : n.testBit i = false := Nat.testBit_lt_two_pow (by
        calc n < 2 ^ 64 := hx
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega))
      simp [hi, h2, this, show 6 + (i - 6) = i by omega]
  · simp [hi]

/-- `and` with 63: the remainder modulo 64. -/
theorem and_63 (x : BitVec 64) : x &&& BitVec.signExtend 64 (63 : BitVec 32) = BitVec.ofNat 64 (x.toNat % 64) := by
  have : BitVec.signExtend 64 (63 : BitVec 32) = BitVec.ofNat 64 (2 ^ 6 - 1) := by decide
  rw [this]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 2 ^ 6 - 1 < 2 ^ 64 by decide), Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- The state of memory before the data is touched. -/
structure Mid (s₀ : State) (m : Mem) : Prop where
  keep : ∀ i < 136, m (VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 i) = s₀.mem (VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 i)
  saved : VG.Proof.ChaCha20.X86_64.Stream.Saved s₀ m

/-- Where our caller's registers and the bytes left after `apply` are. -/
abbrev savR (s₀ : State) : Region := ⟨off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 576, 32⟩

theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : VG.Proof.ChaCha20.X86_64.Stream.Saved s₀ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (VG.Proof.ChaCha20.X86_64.Stream.savR s₀).Disjoint r) : VG.Proof.ChaCha20.X86_64.Stream.Saved s₀ m' := by
  have c : ∀ d, 576 ≤ d → d + 8 ≤ 608 → (VG.Proof.ChaCha20.X86_64.Stream.savR s₀).Contains (off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) d) (64 / 8) := by
    intro d h₁ h₂
    simp only [VG.Proof.ChaCha20.X86_64.Stream.savR, off_eq]
    exact Offset.contains _ h₁ (by omega) (by omega)
  exact ⟨by rw [hf.readW (c 576 (by decide) (by decide)) hd (by decide), h.rbx],
    by rw [hf.readW (c 584 (by decide) (by decide)) hd (by decide), h.rbp],
    by rw [hf.readW (c 592 (by decide) (by decide)) hd (by decide), h.r12],
    by rw [hf.readW (c 600 (by decide) (by decide)) hd (by decide), h.left]⟩

theorem savR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.X86_64.Stream.savR s₀) (VG.Proof.ChaCha20.X86_64.Stream.stR s₀) := by
  simp only [VG.Proof.ChaCha20.X86_64.Stream.savR, off_eq]; exact Offset.sub_base _ (by omega)

/-- After `start`, with `x` in `rdx`. -/
structure R1 (s₀ : State) (x : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = VG.Proof.ChaCha20.X86_64.Stream.st s₀
  rbp : s.gpr .rbp = VG.Proof.ChaCha20.X86_64.Stream.dp s₀
  r12 : s.gpr .r12 = BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.L s₀)
  rdx : s.gpr .rdx = BitVec.ofNat 64 x
  rax : s.gpr .rax = BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.O s₀)
  keep : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mid : VG.Proof.ChaCha20.X86_64.Stream.Mid s₀ s.mem
  done : VG.Proof.ChaCha20.X86_64.Stream.Done s₀ 0 s.mem
  frame : Frame [VG.Proof.ChaCha20.X86_64.Stream.stR s₀] s₀.mem s.mem

theorem readW64_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 64 = m.readW (off p d) 64 := readW64_writeW_off m p v hd he h

/-- A byte outside a write of at most 8 bytes is unchanged. -/
theorem byte_writeW_off (m : Mem) (p : Addr) {w : Nat} (v : BitVec w) {i e : Nat} (hw : w / 8 ≤ 8)
    (hi : i < 2 ^ 32) (he : e < 2 ^ 32) (h : i + 1 ≤ e ∨ e + w / 8 ≤ i) :
    (m.writeW (off p e) v) (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) := by
  have hs := off_sep p (d := i) (n := 1) (e := e) (k := w / 8) hi he (by decide) hw h
  rw [← off_eq]
  exact Mem.write_apply (hs _ (by simp))

set_option simprocs false in
theorem start_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Stream.APre s₀) (hle : VG.Proof.ChaCha20.X86_64.Stream.L s₀ ≤ VG.Proof.ChaCha20.X86_64.Stream.N s₀) {s : State} (h : VG.Proof.ChaCha20.X86_64.Stream.Q0 s₀ s) :
    WP isa (.block start) s fun s' => VG.Proof.ChaCha20.X86_64.Stream.R1 s₀ (VG.Proof.ChaCha20.X86_64.Stream.L s₀) s' ∧ s'.cf = some (decide (VG.Proof.ChaCha20.X86_64.Stream.O s₀ < VG.Proof.ChaCha20.X86_64.Stream.L s₀)) := by
  have o576 := hp.w_st (d := 576) (n := 8) (by decide)
  have o584 := hp.w_st (d := 584) (n := 8) (by decide)
  have o592 := hp.w_st (d := 592) (n := 8) (by decide)
  have o600 := hp.w_st (d := 600) (n := 8) (by decide)
  rw [← h.wr] at o576 o584 o592 o600
  simp only [off] at o576 o584 o592 o600
  have hrdi := h.keep .rdi (by decide); have hrsi := h.keep .rsi (by decide)
  have hrdx := h.keep .rdx (by decide)
  have hrbx := h.keep .rbx (by decide); have hrbp := h.keep .rbp (by decide)
  have hr12 := h.keep .r12 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [start, runBlock_cons, runStep_some, runBlock_nil, exec,
    ea_at, readSrc, execAlu, arithFlags, State.store64, State.setReg, State.setFlags, hrdi, hrsi, hrdx,
    hrbx, hrbp, hr12, h.rax, o576, o584, o592, o600, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have hL := VG.Proof.ChaCha20.X86_64.Stream.L_lt s₀
  have hN := VG.Proof.ChaCha20.X86_64.Stream.N_lt s₀
  have hsub : BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.N s₀) - s₀.gpr .rdx = BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.N s₀ - VG.Proof.ChaCha20.X86_64.Stream.L s₀) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, toNat_ofNat_lt hN]; exact hle),
      toNat_ofNat_lt hN, toNat_ofNat_lt (by omega)]
  have hf : Frame [VG.Proof.ChaCha20.X86_64.Stream.stR s₀] s₀.mem ((((s₀.mem.writeW (off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 576) (s₀.gpr .rbx)).writeW (off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 584)
      (s₀.gpr .rbp)).writeW (off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 592) (s₀.gpr .r12)).writeW (off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 600)
      (BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.N s₀ - VG.Proof.ChaCha20.X86_64.Stream.L s₀))) := by
    have c : ∀ d, d + 8 ≤ 768 → (VG.Proof.ChaCha20.X86_64.Stream.stR s₀).Contains (off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) d) (64 / 8) :=
      fun d hd => contains_off hd (by omega)
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 576 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 584 (by decide))).writeW (List.mem_singleton_self _) _
      (c 592 (by decide))).writeW (List.mem_singleton_self _) _ (c 600 (by decide))
  rw [hsub, h.mem]
  refine ⟨⟨by simp (config := {decide := true}), by simp (config := {decide := true}),
    by simp (config := {decide := true}) [VG.Proof.ChaCha20.X86_64.Stream.L], by simp (config := {decide := true}) [VG.Proof.ChaCha20.X86_64.Stream.L, hrdx], ?_,
    fun r hr => ?_, h.rd, h.wr, ⟨fun i hi => ?_, ?_⟩,
    fun k hk => ?_, hf⟩, ?_⟩
  · simp (config := {decide := true}) only [ite_true, ite_false, VG.Proof.ChaCha20.X86_64.Stream.and_63, toNat_ofNat_lt hN]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) <;>
      exact h.keep _ (by decide)
  · simp only [VG.Proof.ChaCha20.X86_64.Stream.byte_writeW_off _ _ _ (show 64 / 8 ≤ 8 by decide) (show i < 2 ^ 32 by omega)
      (show 576 < 2 ^ 32 by decide) (by omega), VG.Proof.ChaCha20.X86_64.Stream.byte_writeW_off _ _ _ (show 64 / 8 ≤ 8 by decide)
      (show i < 2 ^ 32 by omega) (show 584 < 2 ^ 32 by decide) (by omega),
      VG.Proof.ChaCha20.X86_64.Stream.byte_writeW_off _ _ _ (show 64 / 8 ≤ 8 by decide) (show i < 2 ^ 32 by omega)
      (show 592 < 2 ^ 32 by decide) (by omega), VG.Proof.ChaCha20.X86_64.Stream.byte_writeW_off _ _ _ (show 64 / 8 ≤ 8 by decide)
      (show i < 2 ^ 32 by omega) (show 600 < 2 ^ 32 by decide) (by omega)]
  · exact ⟨by simp (config := {decide := true}) only [VG.Proof.ChaCha20.X86_64.Stream.readW64_off, Mem.readW_writeW_self64],
      by simp (config := {decide := true}) only [VG.Proof.ChaCha20.X86_64.Stream.readW64_off, Mem.readW_writeW_self64],
      by simp (config := {decide := true}) only [VG.Proof.ChaCha20.X86_64.Stream.readW64_off, Mem.readW_writeW_self64],
      by simp (config := {decide := true}) only [Mem.readW_writeW_self64]⟩
  · dsimp only
    rw [hf.bytes (R := VG.Proof.ChaCha20.X86_64.Stream.dR s₀) (by simpa using hp.st_d.symm) (show VG.Proof.ChaCha20.X86_64.Stream.L s₀ ≤ 2 ^ 64 by have := VG.Proof.ChaCha20.X86_64.Stream.L_lt s₀; omega) hk]
    simp
  · simp (config := {decide := true}) only [VG.Proof.ChaCha20.X86_64.Stream.and_63, toNat_ofNat_lt hN,
      toNat_ofNat_lt (show VG.Proof.ChaCha20.X86_64.Stream.N s₀ % 64 < 2 ^ 64 by omega)]


theorem H_le (s₀ : State) : VG.Proof.ChaCha20.X86_64.Stream.H s₀ ≤ VG.Proof.ChaCha20.X86_64.Stream.L s₀ := Nat.min_le_right _ _
theorem H_le_O (s₀ : State) : VG.Proof.ChaCha20.X86_64.Stream.H s₀ ≤ VG.Proof.ChaCha20.X86_64.Stream.O s₀ := Nat.min_le_left _ _
theorem O_lt (s₀ : State) : VG.Proof.ChaCha20.X86_64.Stream.O s₀ < 64 := Nat.mod_lt _ (by decide)

set_option simprocs false in
theorem sel_ok {s₀ : State} {s : State} (h : VG.Proof.ChaCha20.X86_64.Stream.R1 s₀ (VG.Proof.ChaCha20.X86_64.Stream.L s₀) s) (hc : s.cf = some (decide (VG.Proof.ChaCha20.X86_64.Stream.O s₀ < VG.Proof.ChaCha20.X86_64.Stream.L s₀))) :
    WP isa (.ite .b (.block [.mov .rdx (.reg .rax)]) (.block [])) s (VG.Proof.ChaCha20.X86_64.Stream.R1 s₀ (VG.Proof.ChaCha20.X86_64.Stream.H s₀)) := by
  refine WP.ite (decide (VG.Proof.ChaCha20.X86_64.Stream.O s₀ < VG.Proof.ChaCha20.X86_64.Stream.L s₀)) (by simp only [eval, hc]) (fun hlt => ?_) (fun hge => ?_)
  · simp only [decide_eq_true_eq] at hlt
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
      Option.some.injEq, exists_eq_left']
    have g : ∀ r, r ≠ .rdx → (s.setReg .rdx (s.gpr .rax)).gpr r = s.gpr r := fun r hr => by
      simp [State.setReg, hr]
    exact ⟨by rw [g _ (by decide), h.rbx], by rw [g _ (by decide), h.rbp], by rw [g _ (by decide), h.r12],
      by simp [State.setReg, h.rax, VG.Proof.ChaCha20.X86_64.Stream.H, headLen, bufLeft, Nat.min_eq_left (Nat.le_of_lt hlt)],
      by rw [g _ (by decide), h.rax],
      fun r hr => by rw [g r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide)]; exact h.keep r hr,
      h.rd, h.wr, h.mid, h.done, h.frame⟩
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hge
    refine WP.block_nil (M := isa) ⟨h.rbx, h.rbp, h.r12, ?_, h.rax, h.keep, h.rd, h.wr, h.mid, h.done, h.frame⟩
    rw [h.rdx, VG.Proof.ChaCha20.X86_64.Stream.H, headLen, bufLeft, Nat.min_eq_right hge]


/-- After `part1`: the bytes from the buffered block XORed, and `rdx` the
bytes of the whole blocks. -/
structure Q1 (s₀ s : State) : Prop where
  rbx : s.gpr .rbx = VG.Proof.ChaCha20.X86_64.Stream.st s₀
  rbp : s.gpr .rbp = VG.Proof.ChaCha20.X86_64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.H s₀)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.L s₀ - VG.Proof.ChaCha20.X86_64.Stream.H s₀)
  rdx : s.gpr .rdx = BitVec.ofNat 64 (64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀)
  zf : s.zf = some (decide (64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀ = 0))
  keep : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mid : VG.Proof.ChaCha20.X86_64.Stream.Mid s₀ s.mem
  done : VG.Proof.ChaCha20.X86_64.Stream.Done s₀ (VG.Proof.ChaCha20.X86_64.Stream.H s₀) s.mem
  frame : Frame [VG.Proof.ChaCha20.X86_64.Stream.stR s₀, VG.Proof.ChaCha20.X86_64.Stream.dR s₀] s₀.mem s.mem

theorem dR_byte {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Stream.APre s₀) {k : Nat} (hk : k < VG.Proof.ChaCha20.X86_64.Stream.L s₀) : InRegions s₀.wr (VG.Proof.ChaCha20.X86_64.Stream.dp s₀ + BitVec.ofNat 64 k) 1 :=
  ⟨VG.Proof.ChaCha20.X86_64.Stream.dR s₀, by rw [hp.wr]; simp, Offset.contains_base _ (by omega) (by have := VG.Proof.ChaCha20.X86_64.Stream.L_lt s₀; omega)⟩

theorem stR_byte {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Stream.APre s₀) {k : Nat} (hk : k < 768) : InRegions s₀.wr (VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 k) 1 :=
  ⟨VG.Proof.ChaCha20.X86_64.Stream.stR s₀, by rw [hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩

theorem d_ne_st {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Stream.APre s₀) {j k : Nat} (hj : j < VG.Proof.ChaCha20.X86_64.Stream.L s₀) (hk : k < 768) :
    VG.Proof.ChaCha20.X86_64.Stream.dp s₀ + BitVec.ofNat 64 j ≠ VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 k := by
  intro he
  have c₁ : (VG.Proof.ChaCha20.X86_64.Stream.dR s₀).Contains (VG.Proof.ChaCha20.X86_64.Stream.dp s₀ + BitVec.ofNat 64 j) 1 :=
    Offset.contains_base _ (by omega) (by have := VG.Proof.ChaCha20.X86_64.Stream.L_lt s₀; omega)
  have c₂ : (VG.Proof.ChaCha20.X86_64.Stream.stR s₀).Contains (VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega) (by omega)
  rw [he] at c₁
  exact hp.st_d _ c₂ c₁

theorem not_in_prefix (p : Addr) {k c : Nat} (hk : c ≤ k) (hk' : k < 2 ^ 64) :
    ¬ (⟨p, c⟩ : Region).Contains (p + BitVec.ofNat 64 k) 1 := by
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat p hk']
  omega

theorem prefix_sub (p : Addr) {c n : Nat} (h : c ≤ n) : Region.Sub ⟨p, c⟩ ⟨p, n⟩ := Region.sub_prefix h

theorem ptr_eq (p : Addr) {o : Nat} (ho : o < 64) :
    p + BitVec.signExtend 64 (128 : BitVec 32) - BitVec.ofNat 64 o = p + BitVec.ofNat 64 (128 - o) := by
  rw [show BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 (128 - o) + BitVec.ofNat 64 o by
      rw [BitVec.ofNat_add_ofNat, show 128 - o + o = 128 by omega]; decide,
    ← BitVec.add_assoc, BitVec.add_sub_cancel]

set_option simprocs false in
theorem part1_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Stream.APre s₀) (hle : VG.Proof.ChaCha20.X86_64.Stream.L s₀ ≤ VG.Proof.ChaCha20.X86_64.Stream.N s₀) {s : State} (h : VG.Proof.ChaCha20.X86_64.Stream.Q0 s₀ s) :
    WP isa part1 s (VG.Proof.ChaCha20.X86_64.Stream.Q1 s₀) := by
  have hL := VG.Proof.ChaCha20.X86_64.Stream.L_lt s₀
  have hH := VG.Proof.ChaCha20.X86_64.Stream.H_le s₀
  have hHO := VG.Proof.ChaCha20.X86_64.Stream.H_le_O s₀
  have hO := VG.Proof.ChaCha20.X86_64.Stream.O_lt s₀
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.Stream.start_ok hp hle h) fun s₁ ⟨h₁, hc₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.Stream.sel_ok h₁ hc₁) fun s₂ h₂ => ?_)
  -- The pointer to the bytes left in the buffered block.
  have h₃ : WP isa (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm 128), .alu .sub .rsi (.reg .rax)]) s₂
      fun s₃ => VG.Proof.ChaCha20.X86_64.Stream.R1 s₀ (VG.Proof.ChaCha20.X86_64.Stream.H s₀) s₃ ∧ s₃.gpr .rsi = VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 (128 - VG.Proof.ChaCha20.X86_64.Stream.O s₀) := by
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
      Option.some.injEq, exists_eq_left', ite_true, ite_false, h₂.rbx, h₂.rax]
    refine ⟨⟨h₂.rbx, h₂.rbp, h₂.r12, h₂.rdx, h₂.rax, fun r hr => ?_, h₂.rd, h₂.wr, h₂.mid, h₂.done,
      h₂.frame⟩, VG.Proof.ChaCha20.X86_64.Stream.ptr_eq _ hO⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) <;>
      exact h₂.keep _ (by simp)
  refine WP.seq (WP.mono h₃ fun s₃ ⟨h₃, hrsi⟩ => ?_)
  have hb : VG.Proof.ChaCha20.X86_64.Stream.BPre s₃ (VG.Proof.ChaCha20.X86_64.Stream.dp s₀) (VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 (128 - VG.Proof.ChaCha20.X86_64.Stream.O s₀)) (VG.Proof.ChaCha20.X86_64.Stream.H s₀) :=
    ⟨h₃.rbp, hrsi, h₃.rdx, by omega, fun k hk => by rw [h₃.wr]; exact VG.Proof.ChaCha20.X86_64.Stream.dR_byte hp (by omega),
      fun k hk => by
        rw [h₃.wr, Offset.add_add]
        obtain ⟨r, hr, hc⟩ := VG.Proof.ChaCha20.X86_64.Stream.stR_byte hp (k := 128 - VG.Proof.ChaCha20.X86_64.Stream.O s₀ + k) (by omega)
        exact ⟨r, List.mem_append_right _ hr, hc⟩,
      fun j hj k hk => by rw [Offset.add_add]; exact VG.Proof.ChaCha20.X86_64.Stream.d_ne_st hp (by omega) (by omega)⟩
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.Stream.xorBytes_ok hb) fun s₄ h₄ => ?_)
  have hr12 : s₄.gpr .r12 = BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.L s₀ - VG.Proof.ChaCha20.X86_64.Stream.H s₀) := by
    rw [h₄.r12, h₃.r12, Offset.ofNat_sub_ofNat hH]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true, hr12, VG.Proof.ChaCha20.X86_64.Stream.and_mask,
    toNat_ofNat_lt (show VG.Proof.ChaCha20.X86_64.Stream.L s₀ - VG.Proof.ChaCha20.X86_64.Stream.H s₀ < 2 ^ 64 by omega)]
  have hnb : (VG.Proof.ChaCha20.X86_64.Stream.L s₀ - VG.Proof.ChaCha20.X86_64.Stream.H s₀) / 64 * 64 = 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀ := by simp only [VG.Proof.ChaCha20.X86_64.Stream.NB, blocksOf, VG.Proof.ChaCha20.X86_64.Stream.H]; omega
  rw [hnb]
  have hrbx : s₄.gpr .rbx = VG.Proof.ChaCha20.X86_64.Stream.st s₀ := by
    rw [h₄.keep _ (by decide) (by decide) (by decide) (by decide) (by decide), h₃.rbx]
  have hk4 : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s₄.gpr r = s₀.gpr r := fun r hr => by
    have := h₃.keep r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      (rw [← this]; exact h₄.keep _ (by decide) (by decide) (by decide) (by decide) (by decide))
  refine ⟨by simp (config := {decide := true}) [hrbx],
    by simp (config := {decide := true}) [h₄.rbp], by simp (config := {decide := true}) [hr12],
    by simp (config := {decide := true}), ?_, fun r hr => ?_, by rw [h₄.rd, h₃.rd],
    by rw [h₄.wr, h₃.wr], ⟨fun i hi => ?_, ?_⟩, fun k hk => ?_, ?_⟩
  · rw [← Offset.ofNat_sub_ofNat_beq (x := 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀) (y := 0) (by omega) (by omega)]
    simp
  · have := hk4 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simpa (config := {decide := true}) using this
  · rw [h₄.frame _ fun r hr hc => ?_]
    · exact h₃.mid.keep i hi
    · simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_d _ (Offset.contains_base (VG.Proof.ChaCha20.X86_64.Stream.st s₀) (d := i) (n := 1) (k := 768) (by omega) (by omega))
        (Offset.sub_base (VG.Proof.ChaCha20.X86_64.Stream.dp s₀) (d := 0) (n := VG.Proof.ChaCha20.X86_64.Stream.H s₀) (k := VG.Proof.ChaCha20.X86_64.Stream.L s₀) (by omega) _ (by simpa using hc))
  · exact h₃.mid.saved.frame h₄.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.st_d.sub_left (VG.Proof.ChaCha20.X86_64.Stream.savR_sub s₀)).sub_right fun x hx => by
        simpa using Offset.sub_base (VG.Proof.ChaCha20.X86_64.Stream.dp s₀) (d := 0) (n := VG.Proof.ChaCha20.X86_64.Stream.H s₀) (k := VG.Proof.ChaCha20.X86_64.Stream.L s₀) (by omega) x (by simpa using hx)
  · by_cases hk' : k < VG.Proof.ChaCha20.X86_64.Stream.H s₀
    · rw [h₄.data k hk', h₃.done k hk, Offset.add_add, h₃.mid.keep _ (by omega)]
      simp [hk', VG.Proof.ChaCha20.X86_64.Stream.KS]
    · rw [h₄.frame _ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.ChaCha20.X86_64.Stream.not_in_prefix _ (by omega) (by omega),
        h₃.done k hk]
      simp [hk']
  · exact (h₃.frame.mono (by simp)).trans (h₄.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.ChaCha20.X86_64.Stream.dR s₀, by simp, VG.Proof.ChaCha20.X86_64.Stream.prefix_sub _ hH⟩)


/-! ## The whole blocks -/

/-- The memory after the arguments of `vg_chacha20_xor` are set up: the
state copied to `p + 192`, and its counter advanced by `c`. -/
def copyMem (m : Mem) (p : Addr) (c : BitVec 32) : Mem :=
  ((((((((m.writeW (off p 192) (m.readW (off p 0) 64)).writeW (off p 200) (m.readW (off p 8) 64)).writeW
    (off p 208) (m.readW (off p 16) 64)).writeW (off p 216) (m.readW (off p 24) 64)).writeW
    (off p 224) (m.readW (off p 32) 64)).writeW (off p 232) (m.readW (off p 40) 64)).writeW
    (off p 240) (m.readW (off p 48) 64)).writeW (off p 248) (m.readW (off p 56) 64)).writeW
    (off p 48) ((m.readW (off p 48) 64).setWidth 32 + c)

set_option simprocs false in
theorem args_exec {s : State} {p : Addr} (hrbx : s.gpr .rbx = p)
    (hw : ∀ d, d + 8 ≤ 768 → InRegions s.wr (off p d) 8) (hrd : s.rd = []) :
    WP isa (.block blocksArgs) s fun s' => s'.mem = VG.Proof.ChaCha20.X86_64.Stream.copyMem s.mem p ((s.gpr .rdx >>> 6).setWidth 32) ∧
      s'.gpr .rdi = p + BitVec.ofNat 64 192 ∧ s'.gpr .rsi = s.gpr .rbp ∧ s'.gpr .rcx = p + BitVec.ofNat 64 256 ∧
      s'.gpr .rdx = s.gpr .rdx ∧ s'.gpr .rbp = s.gpr .rbp + s.gpr .rdx ∧
      s'.gpr .r12 = s.gpr .r12 - s.gpr .rdx ∧
      (∀ r ∈ [Reg.rbx, .r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i : ∀ d, d + 8 ≤ 768 → InRegions (s.rd ++ s.wr) (off p d) 8 := fun d hd => by
    rw [hrd, List.nil_append]; exact hw d hd
  have o4 : InRegions s.wr (off p 48) 4 := by
    obtain ⟨r, hr, hc⟩ := hw 48 (by decide); exact ⟨r, hr, by simp only [Region.Contains] at hc ⊢; omega⟩
  have i0 := i 0 (by decide); have i8 := i 8 (by decide); have i16 := i 16 (by decide)
  have i24 := i 24 (by decide); have i32 := i 32 (by decide); have i40 := i 40 (by decide)
  have i48 := i 48 (by decide); have i56 := i 56 (by decide)
  have o192 := hw 192 (by decide); have o200 := hw 200 (by decide); have o208 := hw 208 (by decide)
  have o216 := hw 216 (by decide); have o224 := hw 224 (by decide); have o232 := hw 232 (by decide)
  have o240 := hw 240 (by decide); have o248 := hw 248 (by decide)
  simp only [off] at i0 i8 i16 i24 i32 i40 i48 i56 o4 o192 o200 o208 o216 o224 o232 o240 o248
  apply WP.of_runBlock
  simp (config := {decide := true}) only [blocksArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
    ea_at, readSrc, readSrc32, execAlu, execAlu32, execShift, arithFlags, State.store64, State.store32,
    State.load64, State.setReg, State.setReg32, State.setFlags, hrbx, i0, i8, i16, i24, i32,
    i40, i48, i56, o4, o192, o200, o208, o216, o224, o232, o240, o248, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.setWidth_setWidth_32]
  refine ⟨rfl, rfl, trivial, rfl, trivial, trivial, trivial, fun r hr => ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [hrbx]


/-- The memory before the counter is advanced. -/
def copyMem8 (m : Mem) (p : Addr) : Mem :=
  (((((((m.writeW (off p 192) (m.readW (off p 0) 64)).writeW (off p 200) (m.readW (off p 8) 64)).writeW
    (off p 208) (m.readW (off p 16) 64)).writeW (off p 216) (m.readW (off p 24) 64)).writeW
    (off p 224) (m.readW (off p 32) 64)).writeW (off p 232) (m.readW (off p 40) 64)).writeW
    (off p 240) (m.readW (off p 48) 64)).writeW (off p 248) (m.readW (off p 56) 64)

theorem copyMem_eq (m : Mem) (p : Addr) (c : BitVec 32) :
    VG.Proof.ChaCha20.X86_64.Stream.copyMem m p c = (VG.Proof.ChaCha20.X86_64.Stream.copyMem8 m p).writeW (off p 48) ((m.readW (off p 48) 64).setWidth 32 + c) := rfl

theorem copyMem8_frame (m : Mem) (p : Addr) : Frame [⟨off p 192, 64⟩] m (VG.Proof.ChaCha20.X86_64.Stream.copyMem8 m p) := by
  have c : ∀ d, 192 ≤ d → d + 8 ≤ 256 → (⟨off p 192, 64⟩ : Region).Contains (off p d) (64 / 8) := by
    intro d h₁ h₂; simp only [off_eq]; exact Offset.contains _ h₁ (by omega) (by omega)
  simp only [VG.Proof.ChaCha20.X86_64.Stream.copyMem8]
  have w : ∀ {m' : Mem} (_ : Frame [⟨off p 192, 64⟩] m m') (d : Nat), 192 ≤ d → d + 8 ≤ 256 →
      ∀ v : BitVec 64, Frame [⟨off p 192, 64⟩] m (m'.writeW (off p d) v) :=
    fun hf d h₁ h₂ v => hf.writeW (List.mem_singleton_self _) v (c d h₁ h₂)
  exact w (w (w (w (w (w (w (w (Frame.refl _ _) 192 (by decide) (by decide) _) 200 (by decide) (by decide) _)
    208 (by decide) (by decide) _) 216 (by decide) (by decide) _) 224 (by decide) (by decide) _) 232 (by decide)
    (by decide) _) 240 (by decide) (by decide) _) 248 (by decide) (by decide) _

theorem copyMem_frame (m : Mem) (p : Addr) (c : BitVec 32) :
    Frame [⟨p, 64⟩, ⟨off p 192, 64⟩] m (VG.Proof.ChaCha20.X86_64.Stream.copyMem m p c) := by
  rw [VG.Proof.ChaCha20.X86_64.Stream.copyMem_eq]
  refine ((VG.Proof.ChaCha20.X86_64.Stream.copyMem8_frame m p).mono (by simp)).writeW (List.mem_cons_self ..) _ ?_
  simp only [off_eq]; exact Offset.contains_base _ (by omega) (by omega)

/-- The copy of the state. -/
theorem copyMem_copy (m : Mem) (p : Addr) (c : BitVec 32) :
    stateAt (VG.Proof.ChaCha20.X86_64.Stream.copyMem m p c) (p + BitVec.ofNat 64 192) = stateAt m p := by
  refine stateAt_congr fun i hi => ?_
  rw [VG.Proof.ChaCha20.X86_64.Stream.copyMem_eq, Offset.add_add, VG.Proof.ChaCha20.X86_64.Stream.byte_writeW_off _ _ _ (show 32 / 8 ≤ 8 by decide) (by omega) (by omega)
    (by omega)]
  have hw : ∀ k, 24 ≤ k → k < 32 → (VG.Proof.ChaCha20.X86_64.Stream.copyMem8 m p).readW (p + BitVec.ofNat 64 (8 * k)) 64 =
      m.readW (p + BitVec.ofNat 64 (8 * (k - 24))) 64 := by
    intro k h₁ h₂
    rw [word_off, word_off]
    simp only [VG.Proof.ChaCha20.X86_64.Stream.copyMem8]
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨ k = 30 ∨ k = 31 := by omega
    all_goals simp (config := {decide := true}) only [Mem.readW_writeW_self64, VG.Proof.ChaCha20.X86_64.Stream.readW64_off]
  have hm : ∀ k, 0 ≤ k → k < 8 → m.readW (p + BitVec.ofNat 64 (8 * k)) 64 = m.readW (p + BitVec.ofNat 64 (8 * k)) 64 :=
    fun _ _ _ => rfl
  rw [byte_of_words64 hw (by omega) (by omega), byte_of_words64 hm (i := i) (Nat.zero_le _) (by omega),
    show (192 + i) / 8 - 24 = i / 8 by omega, show (192 + i) % 8 = i % 8 by omega]


/-- The state, with its counter advanced. -/
theorem copyMem_state (m : Mem) (p : Addr) (c : BitVec 32) :
    stateAt (VG.Proof.ChaCha20.X86_64.Stream.copyMem m p c) p = (stateAt m p).set 12 ((stateAt m p)[12] + c) := by
  rw [VG.Proof.ChaCha20.X86_64.Stream.copyMem_eq, Proof.ChaCha20.X86_64.Xor.stateAt_writeW_counter,
    Proof.ChaCha20.X86_64.Xor.stateAt_frame (VG.Proof.ChaCha20.X86_64.Stream.copyMem8_frame m p) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only [off_eq]
      exact Offset.base_disjoint _ (by omega) (by omega)),
    readW64_setWidth]
  simp [stateAt, off_eq]


theorem shr_eq {nb : Nat} (h : 64 * nb < 2 ^ 64) :
    (BitVec.ofNat 64 (64 * nb) >>> 6).setWidth 32 = BitVec.ofNat 32 nb := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, toNat_ofNat_lt h, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  omega

/-- After `part2`: the whole blocks XORed, and the counter advanced past
them. -/
structure Q2 (s₀ s : State) : Prop where
  rbx : s.gpr .rbx = VG.Proof.ChaCha20.X86_64.Stream.st s₀
  rbp : s.gpr .rbp = VG.Proof.ChaCha20.X86_64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.T s₀)
  keep : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : stateAt s.mem (VG.Proof.ChaCha20.X86_64.Stream.st s₀) = ctr (VG.Proof.ChaCha20.X86_64.Stream.S0 s₀) (VG.Proof.ChaCha20.X86_64.Stream.NB s₀)
  buf : ∀ i < 64, s.mem (VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 (64 + i)) = s₀.mem (VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 (64 + i))
  saved : VG.Proof.ChaCha20.X86_64.Stream.Saved s₀ s.mem
  done : VG.Proof.ChaCha20.X86_64.Stream.Done s₀ (VG.Proof.ChaCha20.X86_64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀) s.mem
  frame : Frame [VG.Proof.ChaCha20.X86_64.Stream.stR s₀, VG.Proof.ChaCha20.X86_64.Stream.dR s₀, VG.Proof.ChaCha20.X86_64.Stream.stkR s₀] s₀.mem s.mem

theorem T_eq (s₀ : State) : VG.Proof.ChaCha20.X86_64.Stream.T s₀ = VG.Proof.ChaCha20.X86_64.Stream.L s₀ - VG.Proof.ChaCha20.X86_64.Stream.H s₀ - 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀ := by simp only [VG.Proof.ChaCha20.X86_64.Stream.T, VG.Proof.ChaCha20.X86_64.Stream.NB, tailLen, blocksOf, VG.Proof.ChaCha20.X86_64.Stream.H]; omega
theorem HNB_le (s₀ : State) : VG.Proof.ChaCha20.X86_64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀ ≤ VG.Proof.ChaCha20.X86_64.Stream.L s₀ := by
  have := VG.Proof.ChaCha20.X86_64.Stream.H_le s₀; simp only [VG.Proof.ChaCha20.X86_64.Stream.NB, blocksOf, VG.Proof.ChaCha20.X86_64.Stream.H] at *; omega

theorem Mid.state {s₀ : State} {m : Mem} (h : VG.Proof.ChaCha20.X86_64.Stream.Mid s₀ m) : stateAt m (VG.Proof.ChaCha20.X86_64.Stream.st s₀) = VG.Proof.ChaCha20.X86_64.Stream.S0 s₀ :=
  stateAt_congr fun i hi => h.keep i (by omega)

theorem nb_zero_ok {s₀ : State} {s : State} (h : VG.Proof.ChaCha20.X86_64.Stream.Q1 s₀ s) (h0 : 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀ = 0) : VG.Proof.ChaCha20.X86_64.Stream.Q2 s₀ s := by
  have hT := VG.Proof.ChaCha20.X86_64.Stream.T_eq s₀
  refine ⟨h.rbx, by rw [h.rbp, h0, Nat.add_zero], by rw [h.r12, hT, h0, Nat.sub_zero], h.keep, h.rd, h.wr,
    by rw [h.mid.state, show VG.Proof.ChaCha20.X86_64.Stream.NB s₀ = 0 by omega, ctr_zero], fun i hi => h.mid.keep _ (by omega), h.mid.saved,
    by rw [h0, Nat.add_zero]; exact h.done, h.frame.mono (by simp)⟩

theorem Q1.w {s₀ s : State} (hp : VG.Proof.ChaCha20.X86_64.Stream.APre s₀) (h : VG.Proof.ChaCha20.X86_64.Stream.Q1 s₀ s) :
    ∀ d, d + 8 ≤ 768 → InRegions s.wr (off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) d) 8 := fun d hd => by rw [h.wr]; exact hp.w_st hd

/-- The regions of the call of `vg_chacha20_xor`: the copy of the state,
the data and the working space. -/
abbrev cpR (s₀ : State) : Region := ⟨VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 192, 64⟩
abbrev blR (s₀ : State) : Region := ⟨VG.Proof.ChaCha20.X86_64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.H s₀), 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀⟩
abbrev wkR (s₀ : State) : Region := ⟨VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 256, 320⟩

theorem cpR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.X86_64.Stream.cpR s₀) (VG.Proof.ChaCha20.X86_64.Stream.stR s₀) := Offset.sub_base _ (by omega)
theorem wkR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.X86_64.Stream.wkR s₀) (VG.Proof.ChaCha20.X86_64.Stream.stR s₀) := Offset.sub_base _ (by omega)
theorem blR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.X86_64.Stream.blR s₀) (VG.Proof.ChaCha20.X86_64.Stream.dR s₀) := Offset.sub_base _ (VG.Proof.ChaCha20.X86_64.Stream.HNB_le s₀)


theorem part2_eq (x : Impl.ChaCha20.X86_64.Callee) :
    part2 x = .ite .e (.block []) (.seq (.block blocksArgs) (.call x.name x.code)) := rfl

theorem blocks_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Stream.APre s₀) {s : State} (h : VG.Proof.ChaCha20.X86_64.Stream.Q1 s₀ s)
    (hnb : 0 < VG.Proof.ChaCha20.X86_64.Stream.NB s₀) : WP isa (.seq (.block blocksArgs) (.call v.callee.name v.callee.code)) s (VG.Proof.ChaCha20.X86_64.Stream.Q2 s₀) := by
  have hL := VG.Proof.ChaCha20.X86_64.Stream.L_lt s₀
  have hH := VG.Proof.ChaCha20.X86_64.Stream.H_le s₀
  have hHNB := VG.Proof.ChaCha20.X86_64.Stream.HNB_le s₀
  have hT := VG.Proof.ChaCha20.X86_64.Stream.T_eq s₀
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.Stream.args_exec h.rbx (h.w hp) (by rw [h.rd, hp.rd])) fun s₁ ⟨m₁, rdi₁, rsi₁, rcx₁, rdx₁,
    rbp₁, r12₁, k₁, rd₁, wr₁⟩ => ?_)
  rw [h.rdx, VG.Proof.ChaCha20.X86_64.Stream.shr_eq (by omega)] at m₁
  rw [h.rdx] at rdx₁
  rw [h.rbp] at rsi₁
  have hsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [k₁ .rsp (by simp), h.keep .rsp (by simp)]
  have hstk : below (s₁.gpr .rsp) 24 = VG.Proof.ChaCha20.X86_64.Stream.stkR s₀ := by rw [hsp₁]; rfl
  have hwr₁ : s₁.wr = [VG.Proof.ChaCha20.X86_64.Stream.stR s₀, VG.Proof.ChaCha20.X86_64.Stream.dR s₀] := by rw [wr₁, h.wr, hp.wr]
  have hrd₁ : s₁.rd = [] := by rw [rd₁, h.rd, hp.rd]
  have dSB : (VG.Proof.ChaCha20.X86_64.Stream.cpR s₀).Disjoint (VG.Proof.ChaCha20.X86_64.Stream.wkR s₀) := Offset.disjoint _ (by omega) (by omega) (by omega)
  have dSD : (VG.Proof.ChaCha20.X86_64.Stream.cpR s₀).Disjoint (VG.Proof.ChaCha20.X86_64.Stream.blR s₀) := (hp.st_d.sub_left (VG.Proof.ChaCha20.X86_64.Stream.cpR_sub s₀)).sub_right (VG.Proof.ChaCha20.X86_64.Stream.blR_sub s₀)
  have dDB : (VG.Proof.ChaCha20.X86_64.Stream.blR s₀).Disjoint (VG.Proof.ChaCha20.X86_64.Stream.wkR s₀) := (hp.st_d.sub_left (VG.Proof.ChaCha20.X86_64.Stream.wkR_sub s₀)).symm.sub_left (VG.Proof.ChaCha20.X86_64.Stream.blR_sub s₀)
  have hcov : ∀ r ∈ [VG.Proof.ChaCha20.X86_64.Stream.cpR s₀, VG.Proof.ChaCha20.X86_64.Stream.blR s₀, VG.Proof.ChaCha20.X86_64.Stream.wkR s₀], ∃ r' ∈ [VG.Proof.ChaCha20.X86_64.Stream.stR s₀, VG.Proof.ChaCha20.X86_64.Stream.dR s₀], ∃ o,
      r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.ChaCha20.X86_64.Stream.stR s₀, by simp, 192, rfl, by simp⟩
    · exact ⟨VG.Proof.ChaCha20.X86_64.Stream.dR s₀, by simp, VG.Proof.ChaCha20.X86_64.Stream.H s₀, rfl, hHNB⟩
    · exact ⟨VG.Proof.ChaCha20.X86_64.Stream.stR s₀, by simp, 256, rfl, by simp⟩
  have hwrap : (VG.Proof.ChaCha20.X86_64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.H s₀)).toNat + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀ ≤ 2 ^ 64 := by
    have := hp.wrap_d
    rw [BitVec.toNat_add, toNat_ofNat_lt (by omega)]
    omega
  refine VG.Proof.ChaCha20.X86_64.Stream.xor_call v (S := VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 192) (D := VG.Proof.ChaCha20.X86_64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.H s₀))
    (B := VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 256) (n := 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀) rdi₁ rsi₁ rdx₁ rcx₁ (by omega) dSD dSB dDB hwrap
    (by rw [hstk]; exact hp.stk_st.sub_right (VG.Proof.ChaCha20.X86_64.Stream.cpR_sub s₀)) (by rw [hstk]; exact hp.stk_d.sub_right (VG.Proof.ChaCha20.X86_64.Stream.blR_sub s₀))
    (by rw [hstk]; exact hp.stk_st.sub_right (VG.Proof.ChaCha20.X86_64.Stream.wkR_sub s₀))
    (by rw [hrd₁, hwr₁, List.nil_append, List.nil_append]; exact Covers.of_sub hcov)
    (by rw [hwr₁]; exact Covers.of_sub hcov) ?_
  intro s₂ rd₂ wr₂ cs₂ f₂ x₂
  rw [hstk] at f₂
  have g : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], s₂.gpr r = s₁.gpr r :=
    fun r hr => cs₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])
  -- Regions the call does not write.
  have nd : ∀ R : Region, R.Disjoint (VG.Proof.ChaCha20.X86_64.Stream.cpR s₀) → R.Disjoint (VG.Proof.ChaCha20.X86_64.Stream.blR s₀) → R.Disjoint (VG.Proof.ChaCha20.X86_64.Stream.wkR s₀) →
      R.Disjoint (VG.Proof.ChaCha20.X86_64.Stream.stkR s₀) → ∀ r ∈ [VG.Proof.ChaCha20.X86_64.Stream.cpR s₀, VG.Proof.ChaCha20.X86_64.Stream.blR s₀, VG.Proof.ChaCha20.X86_64.Stream.wkR s₀, VG.Proof.ChaCha20.X86_64.Stream.stkR s₀], R.Disjoint r := by
    intro R h₁ h₂ h₃ h₄ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  have nc : ∀ R : Region, R.Disjoint ⟨VG.Proof.ChaCha20.X86_64.Stream.st s₀, 64⟩ → R.Disjoint ⟨off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 192, 64⟩ →
      ∀ r ∈ [⟨VG.Proof.ChaCha20.X86_64.Stream.st s₀, 64⟩, ⟨off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 192, 64⟩], R.Disjoint r := by
    intro R h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption
  have fc := VG.Proof.ChaCha20.X86_64.Stream.copyMem_frame s.mem (VG.Proof.ChaCha20.X86_64.Stream.st s₀) (BitVec.ofNat 32 (VG.Proof.ChaCha20.X86_64.Stream.NB s₀))
  rw [← m₁] at fc
  have stS : Region.Sub ⟨VG.Proof.ChaCha20.X86_64.Stream.st s₀, 64⟩ (VG.Proof.ChaCha20.X86_64.Stream.stR s₀) := VG.Proof.ChaCha20.X86_64.Stream.prefix_sub _ (by omega)
  have cpS : Region.Sub ⟨off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 192, 64⟩ (VG.Proof.ChaCha20.X86_64.Stream.stR s₀) := by rw [off_eq]; exact VG.Proof.ChaCha20.X86_64.Stream.cpR_sub s₀
  have bufS : Region.Sub ⟨VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 64, 64⟩ (VG.Proof.ChaCha20.X86_64.Stream.stR s₀) := Offset.sub_base _ (by omega)
  have svS := VG.Proof.ChaCha20.X86_64.Stream.savR_sub s₀
  -- Anything in the state is apart from the data and the stack.
  have sd : ∀ R, Region.Sub R (VG.Proof.ChaCha20.X86_64.Stream.stR s₀) → R.Disjoint (VG.Proof.ChaCha20.X86_64.Stream.blR s₀) := fun R hR =>
    (hp.st_d.sub_left hR).sub_right (VG.Proof.ChaCha20.X86_64.Stream.blR_sub s₀)
  have sk : ∀ R, Region.Sub R (VG.Proof.ChaCha20.X86_64.Stream.stR s₀) → R.Disjoint (VG.Proof.ChaCha20.X86_64.Stream.stkR s₀) := fun R hR => hp.stk_st.symm.sub_left hR
  have ds : ∀ R R', Region.Sub R (VG.Proof.ChaCha20.X86_64.Stream.dR s₀) → Region.Sub R' (VG.Proof.ChaCha20.X86_64.Stream.stR s₀) → R.Disjoint R' := fun R R' h₁ h₂ =>
    (hp.st_d.symm.sub_left h₁).sub_right h₂
  have dk : ∀ R, Region.Sub R (VG.Proof.ChaCha20.X86_64.Stream.dR s₀) → R.Disjoint (VG.Proof.ChaCha20.X86_64.Stream.stkR s₀) := fun R hR => hp.stk_d.symm.sub_left hR
  refine ⟨by rw [g .rbx (by simp), k₁ .rbx (by simp), h.rbx], ?_, ?_, fun r hr => ?_, by rw [rd₂, rd₁, h.rd],
    by rw [wr₂, wr₁, h.wr], ?_, fun i hi => ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [g .rbp (by simp), rbp₁, h.rbp, h.rdx, Offset.add_add]
  · rw [g .r12 (by simp), r12₁, h.r12, h.rdx, Offset.ofNat_sub_ofNat (by omega), hT, Nat.sub_sub]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [g r (by rcases hr with rfl | rfl | rfl | rfl <;> simp), k₁ r (by rcases hr with rfl | rfl | rfl | rfl <;> simp)]
    exact h.keep r (by rcases hr with rfl | rfl | rfl | rfl <;> simp)
  · rw [Proof.ChaCha20.X86_64.Xor.stateAt_frame f₂ (nd _
        (Offset.base_disjoint _ (by omega) (by omega)) (sd _ stS)
        (Offset.base_disjoint _ (by omega) (by omega)) (sk _ stS)),
      m₁, VG.Proof.ChaCha20.X86_64.Stream.copyMem_state, h.mid.state]
    rfl
  · rw [← Offset.add_add, f₂.bytes (R := ⟨VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 64, 64⟩) (nd _
        (Offset.disjoint _ (by omega) (by omega) (by omega)) (sd _ bufS)
        (Offset.disjoint _ (by omega) (by omega) (by omega)) (sk _ bufS)) (show 64 ≤ 2 ^ 64 by decide) hi,
      fc.bytes (R := ⟨VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 64, 64⟩) (nc _ (Offset.disjoint_base _ (by omega) (by omega))
        (by rw [off_eq]; exact Offset.disjoint _ (by omega) (by omega) (by omega))) (show 64 ≤ 2 ^ 64 by decide) hi,
      Offset.add_add]
    exact h.mid.keep _ (by omega)
  · refine (h.mid.saved.frame fc (nc _ ?_ ?_)).frame f₂ (nd _ ?_ (sd _ svS) ?_ (sk _ svS))
    · simp only [VG.Proof.ChaCha20.X86_64.Stream.savR, off_eq]; exact Offset.disjoint_base _ (by omega) (by omega)
    · simp only [VG.Proof.ChaCha20.X86_64.Stream.savR, off_eq]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · simp only [VG.Proof.ChaCha20.X86_64.Stream.savR, off_eq]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · simp only [VG.Proof.ChaCha20.X86_64.Stream.savR, off_eq]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · have fcd : s₁.mem (VG.Proof.ChaCha20.X86_64.Stream.dp s₀ + BitVec.ofNat 64 k) = s.mem (VG.Proof.ChaCha20.X86_64.Stream.dp s₀ + BitVec.ofNat 64 k) :=
      fc.bytes (R := VG.Proof.ChaCha20.X86_64.Stream.dR s₀) (nc _ (ds _ _ (fun _ h => h) stS) (ds _ _ (fun _ h => h) cpS))
        (show VG.Proof.ChaCha20.X86_64.Stream.L s₀ ≤ 2 ^ 64 by omega) hk
    by_cases hk₁ : k < VG.Proof.ChaCha20.X86_64.Stream.H s₀
    · have hpre : Region.Sub ⟨VG.Proof.ChaCha20.X86_64.Stream.dp s₀, VG.Proof.ChaCha20.X86_64.Stream.H s₀⟩ (VG.Proof.ChaCha20.X86_64.Stream.dR s₀) := VG.Proof.ChaCha20.X86_64.Stream.prefix_sub _ hH
      rw [f₂.bytes (R := ⟨VG.Proof.ChaCha20.X86_64.Stream.dp s₀, VG.Proof.ChaCha20.X86_64.Stream.H s₀⟩) (nd _ (ds _ _ hpre (VG.Proof.ChaCha20.X86_64.Stream.cpR_sub s₀))
          (Offset.base_disjoint _ (by omega) (by omega)) (ds _ _ hpre (VG.Proof.ChaCha20.X86_64.Stream.wkR_sub s₀)) (dk _ hpre))
          (show VG.Proof.ChaCha20.X86_64.Stream.H s₀ ≤ 2 ^ 64 by omega) hk₁]
      rw [fcd, h.done k hk, ite_pos hk₁, ite_pos (by omega)]
    by_cases hk₂ : k < VG.Proof.ChaCha20.X86_64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀
    · have e := xor_getD (length_keystream _ _) x₂ (j := k - VG.Proof.ChaCha20.X86_64.Stream.H s₀) (by omega)
      rw [Offset.add_add, show VG.Proof.ChaCha20.X86_64.Stream.H s₀ + (k - VG.Proof.ChaCha20.X86_64.Stream.H s₀) = k by omega, fcd, h.done k hk, ite_neg hk₁, m₁,
        VG.Proof.ChaCha20.X86_64.Stream.copyMem_copy, h.mid.state, keystream_getD _ (by omega)] at e
      rw [e, ite_pos hk₂]
      simp only [VG.Proof.ChaCha20.X86_64.Stream.KS, ite_neg hk₁]
    · have hR : Region.Sub ⟨VG.Proof.ChaCha20.X86_64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀), VG.Proof.ChaCha20.X86_64.Stream.L s₀ - (VG.Proof.ChaCha20.X86_64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀)⟩ (VG.Proof.ChaCha20.X86_64.Stream.dR s₀) :=
        Offset.sub_base _ (by omega)
      have := f₂.bytes (R := ⟨VG.Proof.ChaCha20.X86_64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀), VG.Proof.ChaCha20.X86_64.Stream.L s₀ - (VG.Proof.ChaCha20.X86_64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀)⟩)
        (nd _ (ds _ _ hR (VG.Proof.ChaCha20.X86_64.Stream.cpR_sub s₀)) (Offset.disjoint _ (by omega) (by omega) (by omega))
          (ds _ _ hR (VG.Proof.ChaCha20.X86_64.Stream.wkR_sub s₀)) (dk _ hR)) (show VG.Proof.ChaCha20.X86_64.Stream.L s₀ - (VG.Proof.ChaCha20.X86_64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀) ≤ 2 ^ 64 by omega)
          (i := k - (VG.Proof.ChaCha20.X86_64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀)) (by simp only; omega)
      rw [Offset.add_add, show VG.Proof.ChaCha20.X86_64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀ + (k - (VG.Proof.ChaCha20.X86_64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀)) = k by omega] at this
      rw [this, fcd, h.done k hk, ite_neg hk₁, ite_neg hk₂]
  · refine ((h.frame.mono (by simp)).trans (fc.sub fun r hr => ?_)).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.ChaCha20.X86_64.Stream.stR s₀, by simp, stS⟩
      · exact ⟨VG.Proof.ChaCha20.X86_64.Stream.stR s₀, by simp, cpS⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨VG.Proof.ChaCha20.X86_64.Stream.stR s₀, by simp, VG.Proof.ChaCha20.X86_64.Stream.cpR_sub s₀⟩
      · exact ⟨VG.Proof.ChaCha20.X86_64.Stream.dR s₀, by simp, VG.Proof.ChaCha20.X86_64.Stream.blR_sub s₀⟩
      · exact ⟨VG.Proof.ChaCha20.X86_64.Stream.stR s₀, by simp, VG.Proof.ChaCha20.X86_64.Stream.wkR_sub s₀⟩
      · exact ⟨VG.Proof.ChaCha20.X86_64.Stream.stkR s₀, by simp, fun _ h => h⟩


theorem part2_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Stream.APre s₀) {s : State} (h : VG.Proof.ChaCha20.X86_64.Stream.Q1 s₀ s) :
    WP isa (part2 v.callee) s (VG.Proof.ChaCha20.X86_64.Stream.Q2 s₀) := by
  rw [VG.Proof.ChaCha20.X86_64.Stream.part2_eq]
  refine WP.ite (decide (64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀ = 0)) (by simp [eval, h.zf])
    (fun h0 => WP.block_nil (M := isa) (VG.Proof.ChaCha20.X86_64.Stream.nb_zero_ok h (by simpa using h0)))
    (fun h0 => VG.Proof.ChaCha20.X86_64.Stream.blocks_ok v hp h (by simp at h0; omega))

/-! ## The last bytes -/

/-- After `part3`: all the data XORed; the counter advanced past the block
started, if any, which is buffered. -/
structure Q3 (s₀ s : State) : Prop where
  rbx : s.gpr .rbx = VG.Proof.ChaCha20.X86_64.Stream.st s₀
  keep : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : stateAt s.mem (VG.Proof.ChaCha20.X86_64.Stream.st s₀) = ctr (VG.Proof.ChaCha20.X86_64.Stream.S0 s₀) (VG.Proof.ChaCha20.X86_64.Stream.NB s₀ + if VG.Proof.ChaCha20.X86_64.Stream.T s₀ = 0 then 0 else 1)
  buf : ∀ i < 64, s.mem (VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 (64 + i)) =
    if VG.Proof.ChaCha20.X86_64.Stream.T s₀ = 0 then s₀.mem (VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 (64 + i))
    else (serialize (block (ctr (VG.Proof.ChaCha20.X86_64.Stream.S0 s₀) (VG.Proof.ChaCha20.X86_64.Stream.NB s₀)))).getD i 0
  saved : VG.Proof.ChaCha20.X86_64.Stream.Saved s₀ s.mem
  done : VG.Proof.ChaCha20.X86_64.Stream.Done s₀ (VG.Proof.ChaCha20.X86_64.Stream.L s₀) s.mem
  frame : Frame [VG.Proof.ChaCha20.X86_64.Stream.stR s₀, VG.Proof.ChaCha20.X86_64.Stream.dR s₀, VG.Proof.ChaCha20.X86_64.Stream.stkR s₀] s₀.mem s.mem

theorem t_zero_ok {s₀ : State} {s : State} (h : VG.Proof.ChaCha20.X86_64.Stream.Q2 s₀ s) (h0 : VG.Proof.ChaCha20.X86_64.Stream.T s₀ = 0) : VG.Proof.ChaCha20.X86_64.Stream.Q3 s₀ s := by
  have hT := VG.Proof.ChaCha20.X86_64.Stream.T_eq s₀
  have hHNB := VG.Proof.ChaCha20.X86_64.Stream.HNB_le s₀
  refine ⟨h.rbx, h.keep, h.rd, h.wr, by rw [h.state, h0]; rfl, fun i hi => by rw [h.buf i hi, h0]; rfl, h.saved,
    by rw [show VG.Proof.ChaCha20.X86_64.Stream.L s₀ = VG.Proof.ChaCha20.X86_64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀ by omega]; exact h.done, h.frame⟩


/-- The buffered block. -/
abbrev bufR (s₀ : State) : Region := ⟨VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 64, 256⟩

theorem bufR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.X86_64.Stream.bufR s₀) (VG.Proof.ChaCha20.X86_64.Stream.stR s₀) := Offset.sub_base _ (by omega)

theorem below8_stk (s₀ : State) : Region.Sub (below (s₀.gpr .rsp) 8) (VG.Proof.ChaCha20.X86_64.Stream.stkR s₀) :=
  below_sub (by decide) (by decide)

set_option simprocs false in
/-- The counter advanced, and the arguments of `xorBytes` for the buffered
block. -/
theorem ctr_exec {s : State} {p : Addr} (hrbx : s.gpr .rbx = p) (hw : InRegions s.wr (off p 48) 4)
    (hr : InRegions (s.rd ++ s.wr) (off p 48) 4) :
    WP isa (.block [.mov32 .rax (.mem (at_ .rbx 48)), .alu32 .add .rax (.imm 1),
      .store32 (at_ .rbx 48) .rax, .mov .rsi (.reg .rbx), .alu .add .rsi (.imm 64),
      .mov .rdx (.reg .r12)]) s fun s' =>
      s'.mem = s.mem.writeW (off p 48) (s.mem.readW (off p 48) 32 + 1) ∧
      s'.gpr .rsi = p + BitVec.ofNat 64 64 ∧ s'.gpr .rdx = s.gpr .r12 ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [off] at hw hr
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, readSrc,
    readSrc32, execAlu, execAlu32, arithFlags, State.load32, State.store32, State.setReg, State.setReg32,
    State.setFlags, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', ite_true,
    ite_false, hrbx, hw, hr, RegUpd.setWidth_setWidth_32]
  exact ⟨trivial, rfl, trivial, fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃], trivial⟩

set_option simprocs false in
theorem tail_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Stream.APre s₀) {s : State} (h : VG.Proof.ChaCha20.X86_64.Stream.Q2 s₀ s) (ht : VG.Proof.ChaCha20.X86_64.Stream.T s₀ ≠ 0) :
    WP isa (.seq (.block tailArgs) (.seq (.call "vg_chacha20_block" Impl.ChaCha20.X86_64.block) tailXor))
      s (VG.Proof.ChaCha20.X86_64.Stream.Q3 s₀) := by
  have hT := VG.Proof.ChaCha20.X86_64.Stream.T_eq s₀
  have hHNB := VG.Proof.ChaCha20.X86_64.Stream.HNB_le s₀
  have hL := VG.Proof.ChaCha20.X86_64.Stream.L_lt s₀
  have h₁ : WP isa (.block tailArgs) s fun s₁ => s₁.gpr .rdi = VG.Proof.ChaCha20.X86_64.Stream.st s₀ ∧
      s₁.gpr .rsi = VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 64 ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    apply WP.of_runBlock
    simp (config := {decide := true}) only [tailArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
      readSrc, execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
      Option.some.injEq, exists_eq_left', ite_true, ite_false, h.rbx]
    exact ⟨trivial, rfl, fun r h₁ h₂ => by simp [h₁, h₂], trivial⟩
  refine WP.seq (WP.mono h₁ fun s₁ ⟨rdi₁, rsi₁, k₁, m₁, rd₁, wr₁⟩ => ?_)
  have hsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [k₁ _ (by decide) (by decide), h.keep .rsp (by simp)]
  have hwr₁ : s₁.wr = [VG.Proof.ChaCha20.X86_64.Stream.stR s₀, VG.Proof.ChaCha20.X86_64.Stream.dR s₀] := by rw [wr₁, h.wr, hp.wr]
  have hrd₁ : s₁.rd = [] := by rw [rd₁, h.rd, hp.rd]
  have hb8 : below (s₁.gpr .rsp) 8 = below (s₀.gpr .rsp) 8 := by rw [hsp₁]
  have stS : Region.Sub ⟨VG.Proof.ChaCha20.X86_64.Stream.st s₀, 64⟩ (VG.Proof.ChaCha20.X86_64.Stream.stR s₀) := VG.Proof.ChaCha20.X86_64.Stream.prefix_sub _ (by omega)
  refine WP.seq (VG.Proof.ChaCha20.X86_64.Stream.block_call rdi₁ rsi₁ (Offset.disjoint_base _ (by omega) (by omega))
    (by rw [hb8]; exact (hp.stk_st.sub_left (VG.Proof.ChaCha20.X86_64.Stream.below8_stk s₀)).sub_right (VG.Proof.ChaCha20.X86_64.Stream.bufR_sub s₀))
    (by rw [hb8]; exact (hp.stk_st.sub_left (VG.Proof.ChaCha20.X86_64.Stream.below8_stk s₀)).sub_right stS)
    (by
      rw [hrd₁, hwr₁]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.ChaCha20.X86_64.Stream.stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 768 by decide⟩
      · exact ⟨VG.Proof.ChaCha20.X86_64.Stream.stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩)
    (by
      rw [hwr₁]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.ChaCha20.X86_64.Stream.stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩) fun s₂ rd₂ wr₂ cs₂ f₂ rsi₂ blk₂ => ?_)
  rw [hb8] at f₂
  have g : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], s₂.gpr r = s.gpr r := fun r hr => by
    rw [cs₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact k₁ r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hw48 : InRegions s₂.wr (off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 48) 4 := by
    rw [wr₂, hwr₁]; exact ⟨VG.Proof.ChaCha20.X86_64.Stream.stR s₀, by simp, contains_off (by omega) (by omega)⟩
  have hr48 : InRegions (s₂.rd ++ s₂.wr) (off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 48) 4 := by
    rw [rd₂, hrd₁, List.nil_append]; exact hw48
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.Stream.ctr_exec (by rw [g .rbx (by simp), h.rbx]) hw48 hr48)
    fun s₃ ⟨m₃, rsi₃, rdx₃, k₃, rd₃, wr₃⟩ => ?_)
  have hT64 : VG.Proof.ChaCha20.X86_64.Stream.T s₀ < 64 := Nat.mod_lt _ (by decide)
  have hrbp₃ : s₃.gpr .rbp = VG.Proof.ChaCha20.X86_64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀) := by
    rw [k₃ .rbp (by decide) (by decide) (by decide), g .rbp (by simp), h.rbp]
  have dS : ∀ R R', Region.Sub R (VG.Proof.ChaCha20.X86_64.Stream.dR s₀) → Region.Sub R' (VG.Proof.ChaCha20.X86_64.Stream.stR s₀) → R.Disjoint R' := fun R R' h₁ h₂ =>
    (hp.st_d.symm.sub_left h₁).sub_right h₂
  have hb : VG.Proof.ChaCha20.X86_64.Stream.BPre s₃ (VG.Proof.ChaCha20.X86_64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀)) (VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 64) (VG.Proof.ChaCha20.X86_64.Stream.T s₀) :=
    ⟨hrbp₃, rsi₃, by rw [rdx₃, g .r12 (by simp), h.r12], by omega,
      fun k hk => by
        rw [wr₃, wr₂, hwr₁, Offset.add_add]
        exact ⟨VG.Proof.ChaCha20.X86_64.Stream.dR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩,
      fun k hk => by
        rw [rd₃, wr₃, rd₂, wr₂, hrd₁, hwr₁, List.nil_append, Offset.add_add]
        exact ⟨VG.Proof.ChaCha20.X86_64.Stream.stR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩,
      fun j hj k hk => by rw [Offset.add_add, Offset.add_add]; exact VG.Proof.ChaCha20.X86_64.Stream.d_ne_st hp (by omega) (by omega)⟩
  refine WP.mono (VG.Proof.ChaCha20.X86_64.Stream.xorBytes_ok hb) fun s₄ h₄ => ?_
  have stS : Region.Sub ⟨VG.Proof.ChaCha20.X86_64.Stream.st s₀, 64⟩ (VG.Proof.ChaCha20.X86_64.Stream.stR s₀) := VG.Proof.ChaCha20.X86_64.Stream.prefix_sub _ (by omega)
  have b8S := VG.Proof.ChaCha20.X86_64.Stream.below8_stk s₀
  have f₃ : Frame [⟨off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 48, 4⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have tR : Region.Sub ⟨VG.Proof.ChaCha20.X86_64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀), VG.Proof.ChaCha20.X86_64.Stream.T s₀⟩ (VG.Proof.ChaCha20.X86_64.Stream.dR s₀) := Offset.sub_base _ (by omega)
  have c48 : Region.Sub ⟨off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 48, 4⟩ (VG.Proof.ChaCha20.X86_64.Stream.stR s₀) := by rw [off_eq]; exact Offset.sub_base _ (by omega)
  have st₂ : stateAt s₂.mem (VG.Proof.ChaCha20.X86_64.Stream.st s₀) = ctr (VG.Proof.ChaCha20.X86_64.Stream.S0 s₀) (VG.Proof.ChaCha20.X86_64.Stream.NB s₀) := by
    rw [Proof.ChaCha20.X86_64.Xor.stateAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.base_disjoint _ (by omega) (by omega)
        · exact (hp.stk_st.sub_left b8S).symm.sub_left stS),
      m₁, h.state]
  have bb : ∀ i < 64, s₂.mem (VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 (64 + i)) = (serialize (block (ctr (VG.Proof.ChaCha20.X86_64.Stream.S0 s₀) (VG.Proof.ChaCha20.X86_64.Stream.NB s₀)))).getD i 0 := by
    intro i hi
    rw [← Offset.add_add, ← serialize_stateAt s₂.mem _ hi, blk₂, m₁, h.state]
  have b3 : ∀ i < 64, s₃.mem (VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 (64 + i)) = s₂.mem (VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 (64 + i)) := by
    intro i hi
    rw [m₃]; exact VG.Proof.ChaCha20.X86_64.Stream.byte_writeW_off _ _ _ (show 32 / 8 ≤ 8 by decide) (by omega) (by omega) (by omega)
  have b4 : ∀ i < 64, s₄.mem (VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 (64 + i)) = s₃.mem (VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 (64 + i)) := by
    intro i hi
    rw [← Offset.add_add]
    exact h₄.frame.bytes (R := ⟨VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 64, 64⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dS _ _ tR (Offset.sub_base _ (by omega))).symm) (show 64 ≤ 2 ^ 64 by decide) hi
  refine ⟨?_, fun r hr => ?_, by rw [h₄.rd, rd₃, rd₂, rd₁, h.rd], by rw [h₄.wr, wr₃, wr₂, wr₁, h.wr], ?_,
    fun i hi => ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [h₄.keep _ (by decide) (by decide) (by decide) (by decide) (by decide),
      k₃ .rbx (by decide) (by decide) (by decide), g .rbx (by simp), h.rbx]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [h₄.keep r (by rcases hr with rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
      k₃ r (by rcases hr with rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl <;> decide), g r (by rcases hr with rfl | rfl | rfl | rfl <;> simp)]
    exact h.keep r (by rcases hr with rfl | rfl | rfl | rfl <;> simp)
  · have e12 : s₂.mem.readW (off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 48) 32 = (ctr (VG.Proof.ChaCha20.X86_64.Stream.S0 s₀) (VG.Proof.ChaCha20.X86_64.Stream.NB s₀))[12] := by
      rw [← st₂]; simp [stateAt, off_eq]
    rw [Proof.ChaCha20.X86_64.Xor.stateAt_frame h₄.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dS _ _ tR stS).symm),
      m₃, Proof.ChaCha20.X86_64.Xor.stateAt_writeW_counter, st₂, e12, ctr_succ, ite_neg ht]
  · rw [b4 i hi, b3 i hi, bb i hi, ite_neg ht]
  · have svS := VG.Proof.ChaCha20.X86_64.Stream.savR_sub s₀
    rw [m₁] at f₂
    refine ((h.saved.frame f₂ fun r hr => ?_).frame f₃ fun r hr => ?_).frame h₄.frame fun r hr => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [VG.Proof.ChaCha20.X86_64.Stream.savR, off_eq]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · exact (hp.stk_st.sub_left b8S).symm.sub_left svS
    · simp only [List.mem_singleton] at hr; subst hr
      simp only [VG.Proof.ChaCha20.X86_64.Stream.savR, off_eq]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact (dS _ _ tR svS).symm
  · have dS48 : (VG.Proof.ChaCha20.X86_64.Stream.dR s₀).Disjoint ⟨off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 48, 4⟩ := dS _ _ (fun _ h => h) c48
    have back : s₃.mem (VG.Proof.ChaCha20.X86_64.Stream.dp s₀ + BitVec.ofNat 64 k) = s.mem (VG.Proof.ChaCha20.X86_64.Stream.dp s₀ + BitVec.ofNat 64 k) := by
      rw [f₃.bytes (R := VG.Proof.ChaCha20.X86_64.Stream.dR s₀) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dS48)
          (show VG.Proof.ChaCha20.X86_64.Stream.L s₀ ≤ 2 ^ 64 by omega) hk,
        f₂.bytes (R := VG.Proof.ChaCha20.X86_64.Stream.dR s₀) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact dS _ _ (fun _ h => h) (VG.Proof.ChaCha20.X86_64.Stream.bufR_sub s₀)
          · exact (hp.stk_d.sub_left b8S).symm) (show VG.Proof.ChaCha20.X86_64.Stream.L s₀ ≤ 2 ^ 64 by omega) hk, m₁]
    by_cases hk₁ : k < VG.Proof.ChaCha20.X86_64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀
    · rw [h₄.frame.bytes (R := ⟨VG.Proof.ChaCha20.X86_64.Stream.dp s₀, VG.Proof.ChaCha20.X86_64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint _ (by omega) (by omega)) (show VG.Proof.ChaCha20.X86_64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀ ≤ 2 ^ 64 by omega) hk₁,
        back, h.done k hk, ite_pos hk₁, ite_pos hk]
    · have e := h₄.data (k - (VG.Proof.ChaCha20.X86_64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀)) (by omega)
      rw [Offset.add_add, Offset.add_add, show VG.Proof.ChaCha20.X86_64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀ + (k - (VG.Proof.ChaCha20.X86_64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀)) = k by omega,
        back, b3 _ (by omega), bb _ (by omega), h.done k hk, ite_neg hk₁] at e
      rw [e, ite_pos hk]
      simp only [VG.Proof.ChaCha20.X86_64.Stream.KS, ite_neg (show ¬ k < VG.Proof.ChaCha20.X86_64.Stream.H s₀ by omega)]
      rw [show (k - VG.Proof.ChaCha20.X86_64.Stream.H s₀) / 64 = VG.Proof.ChaCha20.X86_64.Stream.NB s₀ by omega, show (k - VG.Proof.ChaCha20.X86_64.Stream.H s₀) % 64 = k - (VG.Proof.ChaCha20.X86_64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀) by omega]
  · rw [m₁] at f₂
    refine ((h.frame.trans (f₂.sub fun r hr => ?_)).trans (f₃.sub fun r hr => ?_)).trans
      (h₄.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.ChaCha20.X86_64.Stream.stR s₀, by simp, VG.Proof.ChaCha20.X86_64.Stream.bufR_sub s₀⟩
      · exact ⟨VG.Proof.ChaCha20.X86_64.Stream.stkR s₀, by simp, b8S⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.ChaCha20.X86_64.Stream.stR s₀, by simp, c48⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.ChaCha20.X86_64.Stream.dR s₀, by simp, tR⟩


theorem part3_eq : part3 = .seq (.block [.alu .test .r12 (.reg .r12)])
    (.ite .e (.block []) (.seq (.block tailArgs) (.seq (.call "vg_chacha20_block" Impl.ChaCha20.X86_64.block)
      tailXor))) := rfl

set_option simprocs false in
theorem part3_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Stream.APre s₀) {s : State} (h : VG.Proof.ChaCha20.X86_64.Stream.Q2 s₀ s) : WP isa part3 s (VG.Proof.ChaCha20.X86_64.Stream.Q3 s₀) := by
  have hT64 : VG.Proof.ChaCha20.X86_64.Stream.T s₀ < 64 := Nat.mod_lt _ (by decide)
  have h₁ : WP isa (.block [.alu .test .r12 (.reg .r12)]) s fun s₁ =>
      VG.Proof.ChaCha20.X86_64.Stream.Q2 s₀ s₁ ∧ s₁.zf = some (decide (VG.Proof.ChaCha20.X86_64.Stream.T s₀ = 0)) := by
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, arithFlags, State.setFlags, Option.bind_some, Option.some.injEq,
      exists_eq_left']
    refine ⟨⟨h.rbx, h.rbp, h.r12, h.keep, h.rd, h.wr, h.state, h.buf, h.saved, h.done, h.frame⟩, ?_⟩
    rw [BitVec.and_self, h.r12, ← Offset.ofNat_sub_ofNat_beq (x := VG.Proof.ChaCha20.X86_64.Stream.T s₀) (y := 0) (by omega) (by omega)]
    simp
  rw [VG.Proof.ChaCha20.X86_64.Stream.part3_eq]
  refine WP.seq (WP.mono h₁ fun s₁ ⟨h₁, hz⟩ => ?_)
  refine WP.ite (decide (VG.Proof.ChaCha20.X86_64.Stream.T s₀ = 0)) (by simp [eval, hz])
    (fun h0 => WP.block_nil (M := isa) (VG.Proof.ChaCha20.X86_64.Stream.t_zero_ok h₁ (by simpa using h0)))
    (fun h0 => VG.Proof.ChaCha20.X86_64.Stream.tail_ok hp h₁ (by simpa using h0))

/-! ## The end -/

/-- What `apply` guarantees (`applyX86_64`), and the registers it keeps. -/
def Final (s₀ s : State) : Prop := gprPreserved s₀ s ∧ Proof.ChaCha20.applyX86_64.post s₀ s

theorem retR_stkR (s₀ : State) : (VG.Proof.ChaCha20.X86_64.Stream.retR s₀).Disjoint (VG.Proof.ChaCha20.X86_64.Stream.stkR s₀) :=
  Offset.base_disjoint_below (s₀.gpr .rsp) (n := 24) (k := 8) (by decide)

set_option simprocs false in
theorem finish_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Stream.APre s₀) (hle : VG.Proof.ChaCha20.X86_64.Stream.L s₀ ≤ VG.Proof.ChaCha20.X86_64.Stream.N s₀) {s : State} (h : VG.Proof.ChaCha20.X86_64.Stream.Q3 s₀ s) :
    WP isa (.block finish) s (VG.Proof.ChaCha20.X86_64.Stream.Final s₀) := by
  have hL := VG.Proof.ChaCha20.X86_64.Stream.L_lt s₀
  have hN := VG.Proof.ChaCha20.X86_64.Stream.N_lt s₀
  have w : ∀ d, d + 8 ≤ 768 → InRegions s.wr (off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) d) 8 := fun d hd => by rw [h.wr]; exact hp.w_st hd
  have r : ∀ d, d + 8 ≤ 768 → InRegions (s.rd ++ s.wr) (off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) d) 8 := fun d hd => by
    rw [h.rd, hp.rd, List.nil_append]; exact w d hd
  have o128 := w 128 (by decide)
  have i600 := r 600 (by decide); have i584 := r 584 (by decide); have i592 := r 592 (by decide)
  have i576 := r 576 (by decide)
  simp only [off] at o128 i600 i584 i592 i576
  apply WP.of_runBlock
  simp (config := {decide := true}) only [finish, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    readSrc, readSrc32, State.load64, State.store64, State.setReg, State.setReg32, Option.map_some,
    Option.some.injEq, exists_eq_left', ite_true, ite_false, h.rbx, o128, i600, i584,
    i592, i576]
  have hl : s.mem.readW (off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 600) 64 = BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.N s₀ - VG.Proof.ChaCha20.X86_64.Stream.L s₀) := h.saved.left
  have sv : ∀ d, 576 ≤ d → d + 8 ≤ 600 →
      (s.mem.writeW (off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 128) (BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.N s₀ - VG.Proof.ChaCha20.X86_64.Stream.L s₀))).readW (off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) d) 64 =
        s.mem.readW (off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) d) 64 := fun d h₁ h₂ => VG.Proof.ChaCha20.X86_64.Stream.readW64_off _ _ _ (by omega) (by omega) (by omega)
  simp only [off] at hl sv
  rw [hl]
  have hfw : Frame [⟨off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 128, 8⟩] s.mem (s.mem.writeW (off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 128) (BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.N s₀ - VG.Proof.ChaCha20.X86_64.Stream.L s₀))) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have c128 : Region.Sub ⟨off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 128, 8⟩ (VG.Proof.ChaCha20.X86_64.Stream.stR s₀) := by rw [off_eq]; exact Offset.sub_base _ (by omega)
  have hF : Frame [VG.Proof.ChaCha20.X86_64.Stream.stR s₀, VG.Proof.ChaCha20.X86_64.Stream.dR s₀, VG.Proof.ChaCha20.X86_64.Stream.stkR s₀] s₀.mem
      (s.mem.writeW (off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 128) (BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.N s₀ - VG.Proof.ChaCha20.X86_64.Stream.L s₀))) :=
    h.frame.trans (hfw.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.ChaCha20.X86_64.Stream.stR s₀, by simp, c128⟩)
  have hS : stateAt (s.mem.writeW (off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 128) (BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.N s₀ - VG.Proof.ChaCha20.X86_64.Stream.L s₀))) (VG.Proof.ChaCha20.X86_64.Stream.st s₀) =
      ctr (VG.Proof.ChaCha20.X86_64.Stream.S0 s₀) (VG.Proof.ChaCha20.X86_64.Stream.NB s₀ + if VG.Proof.ChaCha20.X86_64.Stream.T s₀ = 0 then 0 else 1) := by
    rw [Proof.ChaCha20.X86_64.Xor.stateAt_frame hfw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [off_eq]
      exact Offset.base_disjoint _ (by omega) (by omega)), h.state]
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp (config := {decide := true}) only [ite_true, ite_false]
      rw [sv 576 (by decide) (by decide)]; exact h.saved.rbx
    · simp (config := {decide := true}) only [ite_true, ite_false]
      rw [sv 584 (by decide) (by decide)]; exact h.saved.rbp
    · simp (config := {decide := true}) only [ite_false]; exact h.keep .rsp (by simp)
    · simp (config := {decide := true}) only [ite_true, ite_false]
      rw [sv 592 (by decide) (by decide)]; exact h.saved.r12
    · simp (config := {decide := true}) only [ite_false]; exact h.keep .r13 (by simp)
    · simp (config := {decide := true}) only [ite_false]; exact h.keep .r14 (by simp)
    · simp (config := {decide := true}) only [ite_false]; exact h.keep .r15 (by simp)
  · dsimp only
    exact hF.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.ret_st
      · exact hp.ret_d
      · exact VG.Proof.ChaCha20.X86_64.Stream.retR_stkR s₀) (by decide)
  · have hd : ∀ k < VG.Proof.ChaCha20.X86_64.Stream.L s₀, (s.mem.writeW (off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 128) (BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.N s₀ - VG.Proof.ChaCha20.X86_64.Stream.L s₀)))
        (VG.Proof.ChaCha20.X86_64.Stream.dp s₀ + BitVec.ofNat 64 k) = s.mem (VG.Proof.ChaCha20.X86_64.Stream.dp s₀ + BitVec.ofNat 64 k) := fun k hk =>
      hfw.bytes (R := VG.Proof.ChaCha20.X86_64.Stream.dR s₀) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.st_d.symm.sub_right c128)) (show VG.Proof.ChaCha20.X86_64.Stream.L s₀ ≤ 2 ^ 64 by omega) hk
    show keyAt _ _ = _ ∧ _
    refine ⟨Proof.ChaCha20.keyAt_of_ctr hS, ?_⟩
    rw [ite_pos hle]
    refine ⟨by simp (config := {decide := true}), apply_data hle fun k hk => ?_,
      apply_rest hle ?_ hS fun i hi => ?_⟩
    · dsimp only
      rw [hd k hk, h.done k hk, ite_pos hk]
    · dsimp only
      simp only [leftAt]
      rw [show (VG.Proof.ChaCha20.X86_64.Stream.st s₀ + 128 : Addr) = off (VG.Proof.ChaCha20.X86_64.Stream.st s₀) 128 by rw [off_eq]; rfl, Mem.readW_writeW_self64,
        toNat_ofNat_lt (by omega)]
    · dsimp only
      rw [VG.Proof.ChaCha20.X86_64.Stream.byte_writeW_off _ _ _ (show 64 / 8 ≤ 8 by decide) (by omega) (by omega) (by omega), h.buf i hi]


set_option simprocs false in
theorem fail_ok {s₀ : State} (hlt : VG.Proof.ChaCha20.X86_64.Stream.N s₀ < VG.Proof.ChaCha20.X86_64.Stream.L s₀) {s : State} (h : VG.Proof.ChaCha20.X86_64.Stream.Q0 s₀ s) :
    WP isa (.block [.mov32 .rax (.imm 0)]) s (VG.Proof.ChaCha20.X86_64.Stream.Final s₀) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32,
    State.setReg, State.setReg32, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r hr => ?_, by dsimp only; rw [h.mem]⟩, ?_⟩
  · have : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp only [this, ite_false]; exact h.keep r this
  · show keyAt _ _ = _ ∧ _
    rw [ite_neg (show ¬ VG.Proof.ChaCha20.X86_64.Stream.L s₀ ≤ VG.Proof.ChaCha20.X86_64.Stream.N s₀ by omega)]
    dsimp only
    rw [h.mem]
    exact ⟨rfl, by simp, rfl, rfl⟩

theorem apply_eq (x : Impl.ChaCha20.X86_64.Callee) : apply x = .seq (.block check)
    (.ite .b (.block [.mov32 .rax (.imm 0)]) (.seq part1 (.seq (part2 x) (.seq part3 (.block finish))))) := rfl

theorem apply_correct (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Stream.APre s₀) :
    WP isa (apply v.callee) s₀ (VG.Proof.ChaCha20.X86_64.Stream.Final s₀) := by
  rw [VG.Proof.ChaCha20.X86_64.Stream.apply_eq]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.Stream.check_ok hp) fun s h => ?_)
  refine WP.ite (decide (VG.Proof.ChaCha20.X86_64.Stream.N s₀ < VG.Proof.ChaCha20.X86_64.Stream.L s₀)) (by simp [eval, h.cf]) (fun hlt => VG.Proof.ChaCha20.X86_64.Stream.fail_ok (by simpa using hlt) h)
    (fun hge => ?_)
  have hle : VG.Proof.ChaCha20.X86_64.Stream.L s₀ ≤ VG.Proof.ChaCha20.X86_64.Stream.N s₀ := by simp at hge; omega
  exact WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.Stream.part1_ok hp hle h) fun s₁ h₁ => WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.Stream.part2_ok v hp h₁) fun s₂ h₂ =>
    WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.Stream.part3_ok hp h₂) fun s₃ h₃ => VG.Proof.ChaCha20.X86_64.Stream.finish_ok hp hle h₃)))

end VG.Proof.ChaCha20.X86_64.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.X86_64.Stream.ApplyCT`. -/
section

/-!
# Streaming ChaCha20 on x86-64: `apply`, constant time

Untrusted: everything here is checked by Lean. Two runs from states that
agree on the pointers, the length and the number of bytes of keystream left
(which the contract lets `apply` leak) are related piece by piece (`RelCT`):
the taint analysis proves each piece without calls constant time from the
registers that hold public values (`taintRegs`), which correctness determines
in each run (`Apply.lean`) from those public values; the calls of the block
function and of the implementation `v` of `vg_chacha20_xor` are constant time
by their own proofs (`RelCT.callEx`), their arguments agreeing; and the
branches are on public values (`RelCT.ite`).
-/

namespace VG.Proof.ChaCha20.X86_64.Stream

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Stream
open VG.Spec.ChaCha20 (stateAt)

/-- Code the taint analysis proves constant time from the registers `rs`. -/
theorem taintRegs {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, P x y → ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs) (fun x y hp => Taint.agree_ofRegs (hr x y hp)) h

/-- What each run satisfies by correctness holds of the final states. -/
theorem RelCT.post {P : State → State → Prop} {c : Prog isa} {F₁ F₂ : State → Prop}
    (h : RelCT isa P c fun _ _ => True) (hw : ∀ x y, P x y → WP isa c x F₁ ∧ WP isa c y F₂) :
    RelCT isa P c fun x y => F₁ x ∧ F₂ y :=
  RelCT.mono (RelCT.wp h hw) (fun _ _ h => h) fun _ _ h => h.2

/-- Two entry states that agree on what is public. -/
structure Two (a b : State) : Prop where
  pa : VG.Proof.ChaCha20.X86_64.Stream.APre a
  pb : VG.Proof.ChaCha20.X86_64.Stream.APre b
  hst : VG.Proof.ChaCha20.X86_64.Stream.st a = VG.Proof.ChaCha20.X86_64.Stream.st b
  hdp : VG.Proof.ChaCha20.X86_64.Stream.dp a = VG.Proof.ChaCha20.X86_64.Stream.dp b
  hrdx : a.gpr .rdx = b.gpr .rdx
  hrsp : a.gpr .rsp = b.gpr .rsp
  hleft : VG.Proof.ChaCha20.X86_64.Stream.N a = VG.Proof.ChaCha20.X86_64.Stream.N b

theorem Two.eqL {a b : State} (h : VG.Proof.ChaCha20.X86_64.Stream.Two a b) : VG.Proof.ChaCha20.X86_64.Stream.L a = VG.Proof.ChaCha20.X86_64.Stream.L b := by
  show (a.gpr .rdx).toNat = (b.gpr .rdx).toNat; rw [h.hrdx]
theorem Two.eqH {a b : State} (h : VG.Proof.ChaCha20.X86_64.Stream.Two a b) : VG.Proof.ChaCha20.X86_64.Stream.H a = VG.Proof.ChaCha20.X86_64.Stream.H b := by
  show min (VG.Proof.ChaCha20.X86_64.Stream.N a % 64) (VG.Proof.ChaCha20.X86_64.Stream.L a) = min (VG.Proof.ChaCha20.X86_64.Stream.N b % 64) (VG.Proof.ChaCha20.X86_64.Stream.L b); rw [h.hleft, h.eqL]
theorem Two.eqNB {a b : State} (h : VG.Proof.ChaCha20.X86_64.Stream.Two a b) : VG.Proof.ChaCha20.X86_64.Stream.NB a = VG.Proof.ChaCha20.X86_64.Stream.NB b := by
  show (VG.Proof.ChaCha20.X86_64.Stream.L a - VG.Proof.ChaCha20.X86_64.Stream.H a) / 64 = (VG.Proof.ChaCha20.X86_64.Stream.L b - VG.Proof.ChaCha20.X86_64.Stream.H b) / 64; rw [h.eqH, h.eqL]
theorem Two.eqT {a b : State} (h : VG.Proof.ChaCha20.X86_64.Stream.Two a b) : VG.Proof.ChaCha20.X86_64.Stream.T a = VG.Proof.ChaCha20.X86_64.Stream.T b := by
  show (VG.Proof.ChaCha20.X86_64.Stream.L a - VG.Proof.ChaCha20.X86_64.Stream.H a) % 64 = (VG.Proof.ChaCha20.X86_64.Stream.L b - VG.Proof.ChaCha20.X86_64.Stream.H b) % 64; rw [h.eqH, h.eqL]


/-- The arguments of the call of `vg_chacha20_xor`. -/
structure Args (s₀ s : State) : Prop where
  rdi : s.gpr .rdi = VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 192
  rsi : s.gpr .rsi = VG.Proof.ChaCha20.X86_64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.H s₀)
  rdx : s.gpr .rdx = BitVec.ofNat 64 (64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀)
  rcx : s.gpr .rcx = VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 256
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = []
  wr : s.wr = [VG.Proof.ChaCha20.X86_64.Stream.stR s₀, VG.Proof.ChaCha20.X86_64.Stream.dR s₀]

theorem args_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Stream.APre s₀) {s : State} (h : VG.Proof.ChaCha20.X86_64.Stream.Q1 s₀ s) :
    WP isa (.block blocksArgs) s (VG.Proof.ChaCha20.X86_64.Stream.Args s₀) :=
  WP.mono (VG.Proof.ChaCha20.X86_64.Stream.args_exec h.rbx (h.w hp) (by rw [h.rd, hp.rd])) fun _ ⟨_, rdi₁, rsi₁, rcx₁, rdx₁, _, _, k₁, rd₁, wr₁⟩ =>
    ⟨rdi₁, by rw [rsi₁, h.rbp], by rw [rdx₁, h.rdx], rcx₁, by rw [k₁ .rsp (by simp), h.keep .rsp (by simp)],
      by rw [rd₁, h.rd, hp.rd], by rw [wr₁, h.wr, hp.wr]⟩

theorem Args.covers {s₀ s : State} (h : VG.Proof.ChaCha20.X86_64.Stream.Args s₀ s) :
    Covers [VG.Proof.ChaCha20.X86_64.Stream.cpR s₀, VG.Proof.ChaCha20.X86_64.Stream.blR s₀, VG.Proof.ChaCha20.X86_64.Stream.wkR s₀] s.wr ∧ Covers ([] ++ [VG.Proof.ChaCha20.X86_64.Stream.cpR s₀, VG.Proof.ChaCha20.X86_64.Stream.blR s₀, VG.Proof.ChaCha20.X86_64.Stream.wkR s₀]) (s.rd ++ s.wr) := by
  have hcov : ∀ r ∈ [VG.Proof.ChaCha20.X86_64.Stream.cpR s₀, VG.Proof.ChaCha20.X86_64.Stream.blR s₀, VG.Proof.ChaCha20.X86_64.Stream.wkR s₀], ∃ r' ∈ [VG.Proof.ChaCha20.X86_64.Stream.stR s₀, VG.Proof.ChaCha20.X86_64.Stream.dR s₀], ∃ o,
      r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.ChaCha20.X86_64.Stream.stR s₀, by simp, 192, rfl, by simp⟩
    · exact ⟨VG.Proof.ChaCha20.X86_64.Stream.dR s₀, by simp, VG.Proof.ChaCha20.X86_64.Stream.H s₀, rfl, VG.Proof.ChaCha20.X86_64.Stream.HNB_le s₀⟩
    · exact ⟨VG.Proof.ChaCha20.X86_64.Stream.stR s₀, by simp, 256, rfl, by simp⟩
  exact ⟨by rw [h.wr]; exact Covers.of_sub hcov,
    by rw [h.rd, h.wr, List.nil_append, List.nil_append]; exact Covers.of_sub hcov⟩

theorem Args.pre (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ s : State} (hp : VG.Proof.ChaCha20.X86_64.Stream.APre s₀) (h : VG.Proof.ChaCha20.X86_64.Stream.Args s₀ s) :
    (Proof.ChaCha20.xorStack v.stack).pre (s.callEntry.withRegions [] [VG.Proof.ChaCha20.X86_64.Stream.cpR s₀, VG.Proof.ChaCha20.X86_64.Stream.blR s₀, VG.Proof.ChaCha20.X86_64.Stream.wkR s₀]) := by
  have hL := VG.Proof.ChaCha20.X86_64.Stream.L_lt s₀
  have hH := VG.Proof.ChaCha20.X86_64.Stream.H_le s₀
  have hHNB := VG.Proof.ChaCha20.X86_64.Stream.HNB_le s₀
  have hstk : below (s.gpr .rsp) 24 = VG.Proof.ChaCha20.X86_64.Stream.stkR s₀ := by rw [h.rsp]; rfl
  have hwrap : (VG.Proof.ChaCha20.X86_64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.H s₀)).toNat + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀ ≤ 2 ^ 64 := by
    have := hp.wrap_d
    rw [BitVec.toNat_add, Proof.ChaCha20.X86_64.toNat_ofNat_lt (by omega)]
    omega
  exact VG.Proof.ChaCha20.X86_64.Stream.xor_pre v h.rdi h.rsi h.rdx h.rcx (by omega)
    ((hp.st_d.sub_left (VG.Proof.ChaCha20.X86_64.Stream.cpR_sub s₀)).sub_right (VG.Proof.ChaCha20.X86_64.Stream.blR_sub s₀))
    (Offset.disjoint _ (by omega) (by omega) (by omega))
    ((hp.st_d.sub_left (VG.Proof.ChaCha20.X86_64.Stream.wkR_sub s₀)).symm.sub_left (VG.Proof.ChaCha20.X86_64.Stream.blR_sub s₀)) hwrap
    (by rw [hstk]; exact hp.stk_st.sub_right (VG.Proof.ChaCha20.X86_64.Stream.cpR_sub s₀)) (by rw [hstk]; exact hp.stk_d.sub_right (VG.Proof.ChaCha20.X86_64.Stream.blR_sub s₀))
    (by rw [hstk]; exact hp.stk_st.sub_right (VG.Proof.ChaCha20.X86_64.Stream.wkR_sub s₀))

set_option simprocs false in
theorem test_ok {s₀ : State} {s : State} (h : VG.Proof.ChaCha20.X86_64.Stream.Q2 s₀ s) :
    WP isa (.block [.alu .test .r12 (.reg .r12)]) s fun s₁ => VG.Proof.ChaCha20.X86_64.Stream.Q2 s₀ s₁ ∧ s₁.zf = some (decide (VG.Proof.ChaCha20.X86_64.Stream.T s₀ = 0)) := by
  have hT64 : VG.Proof.ChaCha20.X86_64.Stream.T s₀ < 64 := Nat.mod_lt _ (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨h.rbx, h.rbp, h.r12, h.keep, h.rd, h.wr, h.state, h.buf, h.saved, h.done, h.frame⟩, ?_⟩
  rw [BitVec.and_self, h.r12, ← Offset.ofNat_sub_ofNat_beq (x := VG.Proof.ChaCha20.X86_64.Stream.T s₀) (y := 0) (by omega) (by omega)]
  simp

/-- The arguments of the call of the block function, and the registers the
rest uses. -/
structure TArgs (s₀ s : State) : Prop where
  rdi : s.gpr .rdi = VG.Proof.ChaCha20.X86_64.Stream.st s₀
  rsi : s.gpr .rsi = VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 64
  rbx : s.gpr .rbx = VG.Proof.ChaCha20.X86_64.Stream.st s₀
  rbp : s.gpr .rbp = VG.Proof.ChaCha20.X86_64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.T s₀)
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = []
  wr : s.wr = [VG.Proof.ChaCha20.X86_64.Stream.stR s₀, VG.Proof.ChaCha20.X86_64.Stream.dR s₀]

set_option simprocs false in
theorem tailArgs_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Stream.APre s₀) {s : State} (h : VG.Proof.ChaCha20.X86_64.Stream.Q2 s₀ s) :
    WP isa (.block tailArgs) s (VG.Proof.ChaCha20.X86_64.Stream.TArgs s₀) := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [tailArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true, ite_false, h.rbx]
  exact ⟨rfl, rfl, by simp (config := {decide := true}) [h.rbx], by simp (config := {decide := true}) [h.rbp],
    by simp (config := {decide := true}) [h.r12], by simp (config := {decide := true}) [h.keep .rsp (by simp)],
    by simp [h.rd, hp.rd], by simp [h.wr, hp.wr]⟩

/-- After the block function: the registers the rest uses. -/
structure TAfter (s₀ s : State) : Prop where
  rbx : s.gpr .rbx = VG.Proof.ChaCha20.X86_64.Stream.st s₀
  rbp : s.gpr .rbp = VG.Proof.ChaCha20.X86_64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86_64.Stream.NB s₀)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Stream.T s₀)
  rsp : s.gpr .rsp = s₀.gpr .rsp

theorem TArgs.pre {s₀ s : State} (hp : VG.Proof.ChaCha20.X86_64.Stream.APre s₀) (h : VG.Proof.ChaCha20.X86_64.Stream.TArgs s₀ s) :
    Proof.ChaCha20.blockX86_64.pre (s.callEntry.withRegions [⟨VG.Proof.ChaCha20.X86_64.Stream.st s₀, 64⟩] [⟨VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 64, 256⟩]) := by
  simp only [Proof.ChaCha20.blockX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, VG.Proof.ChaCha20.X86_64.Stream.callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp), VG.Proof.ChaCha20.X86_64.Stream.callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp),
    h.rdi, h.rsi, h.rsp]
  exact ⟨trivial, trivial, Offset.disjoint_base _ (by omega) (by omega),
    (hp.stk_st.sub_left (VG.Proof.ChaCha20.X86_64.Stream.below8_stk s₀)).sub_right (VG.Proof.ChaCha20.X86_64.Stream.bufR_sub s₀)⟩

theorem TArgs.covers {s₀ s : State} (h : VG.Proof.ChaCha20.X86_64.Stream.TArgs s₀ s) :
    Covers ([⟨VG.Proof.ChaCha20.X86_64.Stream.st s₀, 64⟩] ++ [⟨VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 64, 256⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨VG.Proof.ChaCha20.X86_64.Stream.st s₀ + BitVec.ofNat 64 64, 256⟩] s.wr := by
  refine ⟨?_, ?_⟩
  · rw [h.rd, h.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.ChaCha20.X86_64.Stream.stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 768 by decide⟩
    · exact ⟨VG.Proof.ChaCha20.X86_64.Stream.stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩
  · rw [h.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.ChaCha20.X86_64.Stream.stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩

theorem TArgs.call {s₀ s : State} (hp : VG.Proof.ChaCha20.X86_64.Stream.APre s₀) (h : VG.Proof.ChaCha20.X86_64.Stream.TArgs s₀ s) :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.X86_64.block) s (VG.Proof.ChaCha20.X86_64.Stream.TAfter s₀) := by
  have stS : Region.Sub ⟨VG.Proof.ChaCha20.X86_64.Stream.st s₀, 64⟩ (VG.Proof.ChaCha20.X86_64.Stream.stR s₀) := VG.Proof.ChaCha20.X86_64.Stream.prefix_sub _ (by omega)
  have hb8 : below (s.gpr .rsp) 8 = below (s₀.gpr .rsp) 8 := by rw [h.rsp]
  refine VG.Proof.ChaCha20.X86_64.Stream.block_call h.rdi h.rsi (Offset.disjoint_base _ (by omega) (by omega))
    (by rw [hb8]; exact (hp.stk_st.sub_left (VG.Proof.ChaCha20.X86_64.Stream.below8_stk s₀)).sub_right (VG.Proof.ChaCha20.X86_64.Stream.bufR_sub s₀))
    (by rw [hb8]; exact (hp.stk_st.sub_left (VG.Proof.ChaCha20.X86_64.Stream.below8_stk s₀)).sub_right stS) h.covers.1 h.covers.2
    fun s' _ _ cs _ _ _ => ⟨by rw [cs .rbx (by simp [calleeSaved]), h.rbx],
      by rw [cs .rbp (by simp [calleeSaved]), h.rbp], by rw [cs .r12 (by simp [calleeSaved]), h.r12],
      by rw [cs .rsp (by simp [calleeSaved]), h.rsp]⟩

section
variable {a b : State} (h : VG.Proof.ChaCha20.X86_64.Stream.Two a b)
include h

theorem check_rel : RelCT isa (fun x y => x = a ∧ y = b) (.block check) fun x y => VG.Proof.ChaCha20.X86_64.Stream.Q0 a x ∧ VG.Proof.ChaCha20.X86_64.Stream.Q0 b y :=
  RelCT.post (VG.Proof.ChaCha20.X86_64.Stream.taintRegs [.rdi, .rsp] (fun x y ⟨hx, hy⟩ r hr => by
      subst hx hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.hst
      · exact h.hrsp) (by taint_decide))
    fun x y ⟨hx, hy⟩ => ⟨by subst hx; exact VG.Proof.ChaCha20.X86_64.Stream.check_ok h.pa, by subst hy; exact VG.Proof.ChaCha20.X86_64.Stream.check_ok h.pb⟩

theorem part1_rel (hle : VG.Proof.ChaCha20.X86_64.Stream.L a ≤ VG.Proof.ChaCha20.X86_64.Stream.N a) :
    RelCT isa (fun x y => VG.Proof.ChaCha20.X86_64.Stream.Q0 a x ∧ VG.Proof.ChaCha20.X86_64.Stream.Q0 b y) part1 fun x y => VG.Proof.ChaCha20.X86_64.Stream.Q1 a x ∧ VG.Proof.ChaCha20.X86_64.Stream.Q1 b y :=
  RelCT.post (VG.Proof.ChaCha20.X86_64.Stream.taintRegs [.rdi, .rsi, .rdx, .rax, .rsp] (fun x y ⟨hx, hy⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [hx.keep _ (by decide), hy.keep _ (by decide)]; exact h.hst
      · rw [hx.keep _ (by decide), hy.keep _ (by decide)]; exact h.hdp
      · rw [hx.keep _ (by decide), hy.keep _ (by decide)]; exact h.hrdx
      · rw [hx.rax, hy.rax, h.hleft]
      · rw [hx.keep _ (by decide), hy.keep _ (by decide)]; exact h.hrsp) (by taint_decide))
    fun x y ⟨hx, hy⟩ => ⟨VG.Proof.ChaCha20.X86_64.Stream.part1_ok h.pa hle hx, VG.Proof.ChaCha20.X86_64.Stream.part1_ok h.pb (by rw [← h.eqL, ← h.hleft]; exact hle) hy⟩

theorem xor_rel (v : Proof.ChaCha20.X86_64.XorImpl) :
    RelCT isa (fun x y => VG.Proof.ChaCha20.X86_64.Stream.Args a x ∧ VG.Proof.ChaCha20.X86_64.Stream.Args b y) (.call v.callee.name v.callee.code) fun _ _ => True :=
  RelCT.callEx v.ok v.ct fun x y ⟨hx, hy⟩ =>
    ⟨[], _, [], _, hx.pre v h.pa, hy.pre v h.pb, by
      simp only [Proof.ChaCha20.xorStack, Proof.ChaCha20.xorX86_64, State.withRegions_gpr,
        State.callEntry_rsp, VG.Proof.ChaCha20.X86_64.Stream.callEntry_gpr' x (by decide : Reg.rdi ≠ .rsp),
        VG.Proof.ChaCha20.X86_64.Stream.callEntry_gpr' x (by decide : Reg.rsi ≠ .rsp), VG.Proof.ChaCha20.X86_64.Stream.callEntry_gpr' x (by decide : Reg.rdx ≠ .rsp),
        VG.Proof.ChaCha20.X86_64.Stream.callEntry_gpr' x (by decide : Reg.rcx ≠ .rsp), VG.Proof.ChaCha20.X86_64.Stream.callEntry_gpr' y (by decide : Reg.rdi ≠ .rsp),
        VG.Proof.ChaCha20.X86_64.Stream.callEntry_gpr' y (by decide : Reg.rsi ≠ .rsp), VG.Proof.ChaCha20.X86_64.Stream.callEntry_gpr' y (by decide : Reg.rdx ≠ .rsp),
        VG.Proof.ChaCha20.X86_64.Stream.callEntry_gpr' y (by decide : Reg.rcx ≠ .rsp), hx.rdi, hx.rsi, hx.rdx, hx.rcx, hx.rsp, hy.rdi,
        hy.rsi, hy.rdx, hy.rcx, hy.rsp, h.hst, h.hdp, h.eqH, h.eqNB, h.hrsp]
      exact ⟨trivial, trivial, trivial, trivial, trivial⟩,
      hx.covers.2, hx.covers.1, hy.covers.2, hy.covers.1, by rw [hx.rsp, hy.rsp, h.hrsp]⟩

theorem part2_rel (v : Proof.ChaCha20.X86_64.XorImpl) :
    RelCT isa (fun x y => VG.Proof.ChaCha20.X86_64.Stream.Q1 a x ∧ VG.Proof.ChaCha20.X86_64.Stream.Q1 b y) (part2 v.callee) fun x y => VG.Proof.ChaCha20.X86_64.Stream.Q2 a x ∧ VG.Proof.ChaCha20.X86_64.Stream.Q2 b y := by
  refine RelCT.post ?_ fun x y ⟨hx, hy⟩ => ⟨VG.Proof.ChaCha20.X86_64.Stream.part2_ok v h.pa hx, VG.Proof.ChaCha20.X86_64.Stream.part2_ok v h.pb hy⟩
  rw [VG.Proof.ChaCha20.X86_64.Stream.part2_eq]
  refine RelCT.ite (fun x y ⟨hx, hy⟩ => by simp only [eval, hx.zf, hy.zf, h.eqNB])
    (VG.Proof.ChaCha20.X86_64.Stream.taintRegs [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)) ?_
  refine RelCT.seq (R := fun x y => VG.Proof.ChaCha20.X86_64.Stream.Args a x ∧ VG.Proof.ChaCha20.X86_64.Stream.Args b y) ?_ (VG.Proof.ChaCha20.X86_64.Stream.xor_rel h v)
  refine RelCT.post (VG.Proof.ChaCha20.X86_64.Stream.taintRegs [.rbx, .rbp, .r12, .rdx, .rsp] (fun x y ⟨⟨hx, hy⟩, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [hx.rbx, hy.rbx, h.hst]
      · rw [hx.rbp, hy.rbp, h.hdp, h.eqH]
      · rw [hx.r12, hy.r12, h.eqL, h.eqH]
      · rw [hx.rdx, hy.rdx, h.eqNB]
      · rw [hx.keep .rsp (by simp), hy.keep .rsp (by simp), h.hrsp]) (by taint_decide))
    fun x y ⟨⟨hx, hy⟩, _⟩ => ⟨VG.Proof.ChaCha20.X86_64.Stream.args_ok h.pa hx, VG.Proof.ChaCha20.X86_64.Stream.args_ok h.pb hy⟩

theorem part3_rel : RelCT isa (fun x y => VG.Proof.ChaCha20.X86_64.Stream.Q2 a x ∧ VG.Proof.ChaCha20.X86_64.Stream.Q2 b y) part3 fun x y => VG.Proof.ChaCha20.X86_64.Stream.Q3 a x ∧ VG.Proof.ChaCha20.X86_64.Stream.Q3 b y := by
  refine RelCT.post ?_ fun x y ⟨hx, hy⟩ => ⟨VG.Proof.ChaCha20.X86_64.Stream.part3_ok h.pa hx, VG.Proof.ChaCha20.X86_64.Stream.part3_ok h.pb hy⟩
  rw [VG.Proof.ChaCha20.X86_64.Stream.part3_eq]
  refine RelCT.seq (R := fun (x y : State) => (VG.Proof.ChaCha20.X86_64.Stream.Q2 a x ∧ x.zf = some (decide (VG.Proof.ChaCha20.X86_64.Stream.T a = 0))) ∧
      (VG.Proof.ChaCha20.X86_64.Stream.Q2 b y ∧ y.zf = some (decide (VG.Proof.ChaCha20.X86_64.Stream.T b = 0))))
    (RelCT.post (VG.Proof.ChaCha20.X86_64.Stream.taintRegs [] (fun _ _ _ r hr => by simp at hr) (by taint_decide))
      fun x y ⟨hx, hy⟩ => ⟨VG.Proof.ChaCha20.X86_64.Stream.test_ok hx, VG.Proof.ChaCha20.X86_64.Stream.test_ok hy⟩) ?_
  refine RelCT.ite (fun x y ⟨hx, hy⟩ => by simp only [eval, hx.2, hy.2, h.eqT])
    (VG.Proof.ChaCha20.X86_64.Stream.taintRegs [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)) ?_
  refine RelCT.seq (R := fun x y => VG.Proof.ChaCha20.X86_64.Stream.TArgs a x ∧ VG.Proof.ChaCha20.X86_64.Stream.TArgs b y)
    (RelCT.post (VG.Proof.ChaCha20.X86_64.Stream.taintRegs [.rbx] (fun x y ⟨⟨hx, hy⟩, _⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hx.1.rbx, hy.1.rbx, h.hst]) (by taint_decide))
      fun x y ⟨⟨hx, hy⟩, _⟩ => ⟨VG.Proof.ChaCha20.X86_64.Stream.tailArgs_ok h.pa hx.1, VG.Proof.ChaCha20.X86_64.Stream.tailArgs_ok h.pb hy.1⟩) ?_
  refine RelCT.seq (R := fun x y => VG.Proof.ChaCha20.X86_64.Stream.TAfter a x ∧ VG.Proof.ChaCha20.X86_64.Stream.TAfter b y) ?_
    (VG.Proof.ChaCha20.X86_64.Stream.taintRegs [.rbx, .rbp, .r12, .rsp] (fun x y ⟨hx, hy⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [hx.rbx, hy.rbx, h.hst]
      · rw [hx.rbp, hy.rbp, h.hdp, h.eqH, h.eqNB]
      · rw [hx.r12, hy.r12, h.eqT]
      · rw [hx.rsp, hy.rsp, h.hrsp]) (by taint_decide))
  have hP : ∀ x y : State, VG.Proof.ChaCha20.X86_64.Stream.TArgs a x ∧ VG.Proof.ChaCha20.X86_64.Stream.TArgs b y → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      Proof.ChaCha20.blockX86_64.pre (x.callEntry.withRegions rd₁ wr₁) ∧
      Proof.ChaCha20.blockX86_64.pre (y.callEntry.withRegions rd₂ wr₂) ∧
      Proof.ChaCha20.blockX86_64.pub (x.callEntry.withRegions rd₁ wr₁) (y.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (x.rd ++ x.wr) ∧ Covers wr₁ x.wr ∧
      Covers (rd₂ ++ wr₂) (y.rd ++ y.wr) ∧ Covers wr₂ y.wr ∧ x.gpr .rsp = y.gpr .rsp := by
    intro x y ⟨hx, hy⟩
    refine ⟨_, _, _, _, hx.pre h.pa, hy.pre h.pb, ?_, hx.covers.1, hx.covers.2, hy.covers.1,
      hy.covers.2, by rw [hx.rsp, hy.rsp, h.hrsp]⟩
    simp only [Proof.ChaCha20.blockX86_64, State.withRegions_gpr, VG.Proof.ChaCha20.X86_64.Stream.callEntry_gpr' x (by decide : Reg.rdi ≠ .rsp),
      VG.Proof.ChaCha20.X86_64.Stream.callEntry_gpr' x (by decide : Reg.rsi ≠ .rsp), VG.Proof.ChaCha20.X86_64.Stream.callEntry_gpr' y (by decide : Reg.rdi ≠ .rsp),
      VG.Proof.ChaCha20.X86_64.Stream.callEntry_gpr' y (by decide : Reg.rsi ≠ .rsp), hx.rdi, hx.rsi, hy.rdi, hy.rsi, h.hst]
    exact ⟨trivial, trivial⟩
  exact RelCT.post (RelCT.callEx Proof.ChaCha20.X86_64.block_correct Proof.ChaCha20.X86_64.block_ct hP)
    fun x y ⟨hx, hy⟩ => ⟨hx.call h.pa, hy.call h.pb⟩

theorem apply_rel (v : Proof.ChaCha20.X86_64.XorImpl) :
    RelCT isa (fun x y => x = a ∧ y = b) (apply v.callee) fun _ _ => True := by
  rw [VG.Proof.ChaCha20.X86_64.Stream.apply_eq]
  refine RelCT.seq (VG.Proof.ChaCha20.X86_64.Stream.check_rel h) (RelCT.ite (fun x y ⟨hx, hy⟩ => by simp only [eval, hx.cf, hy.cf, h.hleft, h.eqL])
    (VG.Proof.ChaCha20.X86_64.Stream.taintRegs [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)) ?_)
  by_cases hlt : VG.Proof.ChaCha20.X86_64.Stream.N a < VG.Proof.ChaCha20.X86_64.Stream.L a
  · exact RelCT.of_false fun x y ⟨⟨hx, _⟩, he⟩ => by simp [eval, hx.cf, hlt] at he
  have hle : VG.Proof.ChaCha20.X86_64.Stream.L a ≤ VG.Proof.ChaCha20.X86_64.Stream.N a := by omega
  refine RelCT.seq (RelCT.mono (VG.Proof.ChaCha20.X86_64.Stream.part1_rel h hle) (fun _ _ hp => hp.1) fun _ _ hq => hq)
    (RelCT.seq (VG.Proof.ChaCha20.X86_64.Stream.part2_rel h v) (RelCT.seq (VG.Proof.ChaCha20.X86_64.Stream.part3_rel h) ?_))
  exact VG.Proof.ChaCha20.X86_64.Stream.taintRegs [.rbx, .rsp] (fun x y ⟨hx, hy⟩ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hx.rbx, hy.rbx, h.hst]
    · rw [hx.keep .rsp (by simp), hy.keep .rsp (by simp), h.hrsp]) (by taint_decide)

end

theorem Two.of {a b : State} (ha : Proof.ChaCha20.applyX86_64.pre a) (hb : Proof.ChaCha20.applyX86_64.pre b)
    (hq : Proof.ChaCha20.applyX86_64.pub a b) : VG.Proof.ChaCha20.X86_64.Stream.Two a b := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hq
  exact ⟨APre.of a ha, APre.of b hb, p1, p2, p3, p4, (List.cons.inj p5).1⟩

theorem apply_ct (v : Proof.ChaCha20.X86_64.XorImpl) :
    ConstantTime isa Proof.ChaCha20.applyX86_64.pre Proof.ChaCha20.applyX86_64.pub (apply v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.ChaCha20.X86_64.Stream.apply_rel (Two.of h₁ h₂ hq) v _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem apply_mxcsr (v : Proof.ChaCha20.X86_64.XorImpl) :
    (apply v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [apply, part2, Code.allInstrs, v.mxcsr, Bool.and_true, Bool.true_and]
  lit_decide

theorem apply_spSafe (v : Proof.ChaCha20.X86_64.XorImpl) :
    (apply v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [apply, part2, Code.all, v.spSafe, Bool.and_true]
  lit_decide

theorem apply_ok (v : Proof.ChaCha20.X86_64.XorImpl) (s : State) (hs : Proof.ChaCha20.applyX86_64.pre s) :
    ∃ t s', Exec isa (apply v.callee) s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.applyX86_64.post s s' := by
  obtain ⟨t, s', he, hf⟩ := VG.Proof.ChaCha20.X86_64.Stream.apply_correct v (APre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (VG.Proof.ChaCha20.X86_64.Stream.apply_mxcsr v) he hf.1, hf.2⟩

/-- A state satisfying the precondition of `apply` (with no data). -/
def applySat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 768⟩, ⟨0x2000, 0⟩]

theorem apply_verified (v : Proof.ChaCha20.X86_64.XorImpl) :
    Verified X86_64.target (apply v.callee) (Spec.ChaCha20.applyContract X86_64.abi 24) :=
  Verified.of_correct (VG.Proof.ChaCha20.X86_64.Stream.apply_ok v) (VG.Proof.ChaCha20.X86_64.Stream.apply_ct v) (by
    sig_implies [Spec.ChaCha20.applyContract, Spec.ChaCha20.applySig, Proof.ChaCha20.applyX86_64,
      X86_64.abi, X86_64.argRegs] [applySat] using VG.Proof.ChaCha20.X86_64.Stream.applySat)

end VG.Proof.ChaCha20.X86_64.Stream

end
