import VerifiedGarbage.Proof.ChaCha20.AArch64.Stream.Init
import VerifiedGarbage.Proof.ChaCha20.AArch64.XorVariant
import VerifiedGarbage.Proof.Framework.AArch64.RelCT

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Stream.Bytes`. -/
section

/-!
# Streaming ChaCha20 on AArch64: XORing bytes

Untrusted: everything here is checked by Lean. `xorBytes` XORs the `x2`
bytes at `x1` into those at `x22`, one at a time, advancing both and
counting them off `x2` and `x23`.
-/

namespace VG.Proof.ChaCha20.AArch64.Stream

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Stream
open VG.Proof.ChaCha20.AArch64.Xor (wp_ldrb wp_strb wp_eor32 wp_addImm wp_subImm xor_setWidth writeW8_apply
  eval_nonzero_ofNat sub_ofNat add_ofNat)
open VG.Proof.ChaCha20.AArch64 (toNat_ofNat_lt)

/-- What `xorBytes` needs: `c` bytes at `D` to write and at `K` to read, not
overlapping. -/
structure BPre (s : State) (D K : Addr) (c : Nat) : Prop where
  x22 : s.gpr .x22 = D
  x1 : s.gpr .x1 = K
  x2 : s.gpr .x2 = BitVec.ofNat 64 c
  c_lt : c ≤ 2 ^ 32
  wD : ∀ k < c, InRegions s.wr (D + BitVec.ofNat 64 k) 1
  rK : ∀ k < c, InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 k) 1
  sep : ∀ j < c, ∀ k < c, D + BitVec.ofNat 64 j ≠ K + BitVec.ofNat 64 k

/-- What `xorBytes` leaves: the bytes XORed, `x22` past them and `x23` less
their number; only `x1`, `x2`, `x9`, `x10`, `x22` and `x23` are written. -/
structure BPost (s : State) (D K : Addr) (c : Nat) (s' : State) : Prop where
  x22 : s'.gpr .x22 = D + BitVec.ofNat 64 c
  x23 : s'.gpr .x23 = s.gpr .x23 - BitVec.ofNat 64 c
  keep : ∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x9 → r ≠ .x10 → r ≠ .x22 → r ≠ .x23 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  data : ∀ k < c, s'.mem (D + BitVec.ofNat 64 k) = s.mem (D + BitVec.ofNat 64 k) ^^^ s.mem (K + BitVec.ofNat 64 k)
  frame : Frame [⟨D, c⟩] s.mem s'.mem

/-- Before byte `i`. -/
structure LInv (s : State) (D K : Addr) (c i : Nat) (s' : State) : Prop where
  x22 : s'.gpr .x22 = D + BitVec.ofNat 64 i
  x1 : s'.gpr .x1 = K + BitVec.ofNat 64 i
  x2 : s'.gpr .x2 = BitVec.ofNat 64 (c - i)
  x23 : s'.gpr .x23 = s.gpr .x23 - BitVec.ofNat 64 i
  keep : ∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x9 → r ≠ .x10 → r ≠ .x22 → r ≠ .x23 → s'.gpr r = s.gpr r
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
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  exact h this

/-- A byte read is outside the bytes written. -/
theorem not_contains {D K : Addr} {c i : Nat}
    (hs : ∀ j < c, ∀ k < c, D + BitVec.ofNat 64 j ≠ K + BitVec.ofNat 64 k) (hi : i < c)
    (h : (⟨D, c⟩ : Region).Contains (K + BitVec.ofNat 64 i) 1) : False := by
  simp only [Region.Contains] at h
  refine hs (K + BitVec.ofNat 64 i - D).toNat (by omega) i hi ?_
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

/-- The loop's body. -/
def body : List Instr :=
  [.ldrb .x9 .x22 0, .ldrb .x10 .x1 0, .logic .eor .w .x9 .x9 .x10, .strb .x9 .x22 0,
    .addImm .x .x22 .x22 1, .addImm .x .x1 .x1 1, .subImm .x .x2 .x2 1, .subImm .x .x23 .x23 1]

theorem byte_step {s : State} {D K : Addr} {c i : Nat} (hp : VG.Proof.ChaCha20.AArch64.Stream.BPre s D K c) (hi : i < c) {s₁ : State}
    (h : VG.Proof.ChaCha20.AArch64.Stream.LInv s D K c i s₁) : WP isa (.block VG.Proof.ChaCha20.AArch64.Stream.body) s₁ (VG.Proof.ChaCha20.AArch64.Stream.LInv s D K c (i + 1)) := by
  have hc := hp.c_lt
  have i₁ : InRegions (s₁.rd ++ s₁.wr) (D + BitVec.ofNat 64 i) 1 := by
    obtain ⟨r, hr, hc⟩ := hp.wD i hi; exact ⟨r, by rw [h.rd, h.wr]; exact List.mem_append_right _ hr, hc⟩
  have i₂ : InRegions (s₁.rd ++ s₁.wr) (K + BitVec.ofNat 64 i) 1 := by rw [h.rd, h.wr]; exact hp.rK i hi
  have o₁ : InRegions s₁.wr (D + BitVec.ofNat 64 i) 1 := by rw [h.wr]; exact hp.wD i hi
  have cd : (⟨D, c⟩ : Region).Contains (D + BitVec.ofNat 64 i) 1 := Offset.contains_base D (by omega) (by omega)
  unfold VG.Proof.ChaCha20.AArch64.Stream.body
  refine wp_ldrb (a := D + BitVec.ofNat 64 i) (by decide) (by rw [h.x22]; exact BitVec.add_zero _) i₁
    fun s₂ u₂ => ?_
  refine wp_ldrb (a := K + BitVec.ofNat 64 i) (by decide)
    (by rw [u₂.other _ (by decide), h.x1]; exact BitVec.add_zero _) (by rw [u₂.rd, u₂.wr]; exact i₂)
    fun s₃ u₃ => ?_
  refine wp_eor32 fun s₄ u₄ => ?_
  refine wp_strb (a := D + BitVec.ofNat 64 i) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h.x22]
        exact BitVec.add_zero _)
    (by rw [u₄.wr, u₃.wr, u₂.wr]; exact o₁) fun s₅ g₅ => ?_
  refine wp_addImm (by decide) fun s₆ u₆ => wp_addImm (by decide) fun s₇ u₇ =>
    wp_subImm (by decide) fun s₈ u₈ => wp_subImm (by decide) fun s₉ u₉ => WP.block_nil ?_
  have hk : s₁.mem (K + BitVec.ofNat 64 i) = s.mem (K + BitVec.ofNat 64 i) :=
    h.frame _ fun r hr hcont => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Proof.ChaCha20.AArch64.Stream.not_contains hp.sep hi hcont
  have hv : (s₄.gpr .x9).setWidth 8 = s.mem (D + BitVec.ofNat 64 i) ^^^ s.mem (K + BitVec.ofNat 64 i) := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₃.gpr, u₂.mem, xor_setWidth, h.data _ hi, hk]
    simp
  have hm : s₉.mem = s₁.mem.writeW (D + BitVec.ofNat 64 i)
      (s.mem (D + BitVec.ofNat 64 i) ^^^ s.mem (K + BitVec.ofNat 64 i)) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, g₅.mem, hv, u₄.mem, u₃.mem, u₂.mem]
  have g : ∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x9 → r ≠ .x10 → r ≠ .x22 → r ≠ .x23 → s₉.gpr r = s₁.gpr r :=
    fun r h₁ h₂ h₃ h₄ h₅ h₆ => by
      rw [u₉.other r h₆, u₈.other r h₂, u₇.other r h₁, u₆.other r h₅, g₅.gpr, u₄.other r h₃, u₃.other r h₄,
        u₂.other r h₃]
  have hfd : Frame [⟨D, c⟩] s₁.mem s₉.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cd
  refine ⟨?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ h₅ h₆ => by rw [g r h₁ h₂ h₃ h₄ h₅ h₆]; exact h.keep r h₁ h₂ h₃ h₄ h₅ h₆,
    by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, g₅.rd, u₄.rd, u₃.rd, u₂.rd, h.rd],
    by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, g₅.wr, u₄.wr, u₃.wr, u₂.wr, h.wr], fun k hk' => ?_, h.frame.trans hfd⟩
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h.x22, add_ofNat]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h.x1, add_ofNat]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h.x2, sub_ofNat (by omega),
      Nat.sub_sub]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h.x23, BitVec.sub_sub,
      BitVec.ofNat_add]
  · rw [hm, writeW8_apply]
    by_cases he : k = i
    · subst he; simp
    · simp only [VG.Proof.ChaCha20.AArch64.Stream.D_ne hc hk' hi he, ite_false]
      rw [h.data k hk']
      by_cases h₁ : k < i
      · simp [h₁, show k < i + 1 by omega]
      · simp [h₁, show ¬ k < i + 1 by omega]


theorem xorBytes_eq : xorBytes = .ite (.zero .x .x2) (.block []) (.loop (.block VG.Proof.ChaCha20.AArch64.Stream.body) (.nonzero .x .x2)) := rfl

theorem LInv.zero {s : State} {D K : Addr} {c : Nat} (hp : VG.Proof.ChaCha20.AArch64.Stream.BPre s D K c) : VG.Proof.ChaCha20.AArch64.Stream.LInv s D K c 0 s :=
  ⟨by rw [hp.x22]; simp, by rw [hp.x1]; simp, by rw [hp.x2, Nat.sub_zero], by simp,
    fun _ _ _ _ _ _ _ => rfl, rfl, rfl, fun k _ => by simp, Frame.refl _ _⟩

theorem LInv.post {s : State} {D K : Addr} {c : Nat} {s' : State} (h : VG.Proof.ChaCha20.AArch64.Stream.LInv s D K c c s') : VG.Proof.ChaCha20.AArch64.Stream.BPost s D K c s' :=
  ⟨h.x22, h.x23, h.keep, h.rd, h.wr, fun k hk => by rw [h.data k hk, ite_pos hk], h.frame⟩

theorem xorBytes_ok {s : State} {D K : Addr} {c : Nat} (hp : VG.Proof.ChaCha20.AArch64.Stream.BPre s D K c) :
    WP isa xorBytes s (VG.Proof.ChaCha20.AArch64.Stream.BPost s D K c) := by
  have hc := hp.c_lt
  rw [VG.Proof.ChaCha20.AArch64.Stream.xorBytes_eq]
  refine WP.ite (decide (c = 0)) (by
      have e : isa.eval (.zero .x .x2) s = some (s.gpr .x2 == 0) := Proof.ChaCha20.AArch64.Xor.eval_zero s .x2
      rw [e, hp.x2, Proof.ChaCha20.AArch64.Xor.ofNat_beq_zero (by omega)])
    (fun h0 => WP.block_nil (M := isa) ?_) (fun h0 => ?_)
  · simp only [decide_eq_true_eq] at h0; subst h0; exact (LInv.zero hp).post
  · simp only [decide_eq_false_iff_not] at h0
    let Inv : Nat → State → Prop := fun n s' => ∃ i, n = c - i ∧ i < c ∧ VG.Proof.ChaCha20.AArch64.Stream.LInv s D K c i s'
    have hstep : ∀ n s', Inv n s' → WP isa (.block VG.Proof.ChaCha20.AArch64.Stream.body) s' (fun s'' =>
        (isa.eval (.nonzero .x .x2) s'' = some false ∧ VG.Proof.ChaCha20.AArch64.Stream.BPost s D K c s'') ∨
        (isa.eval (.nonzero .x .x2) s'' = some true ∧ ∃ n' < n, Inv n' s'')) := by
      rintro n s' ⟨i, rfl, hi, hI⟩
      refine WP.mono (VG.Proof.ChaCha20.AArch64.Stream.byte_step hp hi hI) fun s'' h' => ?_
      have hz := eval_nonzero_ofNat s'' .x2 (by omega) h'.x2
      by_cases hl : i + 1 = c
      · exact .inl ⟨by rw [hz]; simp; omega, LInv.post (hl ▸ h')⟩
      · exact .inr ⟨by rw [hz]; simp; omega, c - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) Inv hstep c s ⟨0, by simp, by omega, LInv.zero hp⟩

end VG.Proof.ChaCha20.AArch64.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Stream.Calls`. -/
section

/-!
# Streaming ChaCha20 on AArch64: the calls

Untrusted: everything here is checked by Lean. The calls of
`vg_chacha20_block` and of an implementation of `vg_chacha20_xor`, from their
proofs of correctness (with `WP.call`), as ChaCha20-Poly1305 makes them. A
call stores nothing in memory, so the callee changes memory only within the
regions it may write.
-/

namespace VG.Proof.ChaCha20.AArch64.Stream

open VG VG.AArch64
open VG.Spec.ChaCha20 (stateAt keystream bytesAt)

/-- `s'` differs from `s` only in memory within `rs` and in registers that
are not callee-saved (or are `x30`). -/
structure Kept (rs : List Region) (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame rs s.mem s'.mem
  vec : ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem callEntry_gpr' (s : State) {r : Reg} (h : r ∉ linkRegs) : s.callEntry.gpr r = s.gpr r :=
  State.callEntry_gpr _ h

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem block_call {s : State} {S B : Addr} (hx0 : s.gpr .x0 = S) (hx1 : s.gpr .x1 = B)
    (hdj : (⟨B, 256⟩ : Region).Disjoint ⟨S, 64⟩)
    (hc : Covers ([⟨S, 64⟩] ++ [⟨B, 256⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨B, 256⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.ChaCha20.AArch64.Stream.Kept [⟨B, 256⟩] s s' → stateAt s'.mem B = Spec.ChaCha20.block (stateAt s.mem S) → Q s') :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.AArch64.block) s Q := by
  refine WP.callV (k := Proof.ChaCha20.blockAArch64) Proof.ChaCha20.AArch64.block_correct
    (rd := [⟨S, 64⟩]) (wr := [⟨B, 256⟩]) ?_ hc hw ?_ (by lit_decide)
  · simp only [Proof.ChaCha20.blockAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' s (by decide : Reg.x0 ∉ linkRegs),
      VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' s (by decide : Reg.x1 ∉ linkRegs), hx0, hx1]
    exact ⟨trivial, trivial, hdj⟩
  · intro s' hrd hwr hsp hf hcs _ hvec hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf, hvec⟩ ?_
    simpa only [Proof.ChaCha20.blockAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' s (by decide : Reg.x0 ∉ linkRegs),
      VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' s (by decide : Reg.x1 ∉ linkRegs), hx0, hx1] using hpost

theorem xor_call (v : Proof.ChaCha20.AArch64.XorImpl) {s : State} {S D B : Addr} {n : Nat}
    (hx0 : s.gpr .x0 = S) (hx1 : s.gpr .x1 = D)
    (hx2 : s.gpr .x2 = BitVec.ofNat 64 n) (hx3 : s.gpr .x3 = B) (hn : n < 2 ^ 64)
    (hSD : (⟨S, 64⟩ : Region).Disjoint ⟨D, n⟩) (hSB : (⟨S, 64⟩ : Region).Disjoint ⟨B, 320⟩)
    (hDB : (⟨D, n⟩ : Region).Disjoint ⟨B, 320⟩) (hwrap : D.toNat + n ≤ 2 ^ 64)
    (hc : Covers ([] ++ [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.ChaCha20.AArch64.Stream.Kept [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s s' →
      bytesAt s'.mem D n = List.zipWith (· ^^^ ·) (bytesAt s.mem D n) (keystream (stateAt s.mem S) n) →
      Q s') :
    WP isa (.call v.callee.name v.callee.code) s Q := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  refine WP.callV (k := Proof.ChaCha20.xorAArch64) v.ok
    (rd := []) (wr := [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) ?_ hc hw ?_ v.noFrames
  · simp only [Proof.ChaCha20.xorAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' s (by decide : Reg.x0 ∉ linkRegs),
      VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' s (by decide : Reg.x1 ∉ linkRegs), VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' s (by decide : Reg.x2 ∉ linkRegs),
      VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' s (by decide : Reg.x3 ∉ linkRegs), hx0, hx1, hx2, hx3, hn']
    exact ⟨trivial, trivial, hSD, hSB, hDB, hwrap⟩
  · intro s' hrd hwr hsp hf hcs _ hvec hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf, hvec⟩ ?_
    simpa only [Proof.ChaCha20.xorAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' s (by decide : Reg.x0 ∉ linkRegs),
      VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' s (by decide : Reg.x1 ∉ linkRegs), VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' s (by decide : Reg.x2 ∉ linkRegs),
      hx0, hx1, hx2, hn'] using hpost

end VG.Proof.ChaCha20.AArch64.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Stream.Apply`. -/
section

/-!
# Streaming ChaCha20 on AArch64: `apply`, correctness

Untrusted: everything here is checked by Lean. The pieces of `apply`
(`Impl/ChaCha20/AArch64/Stream.lean`), each from what holds before it
(`Q0` … `Q3`), and the whole function, for any implementation `v` of
`vg_chacha20_xor`. The pieces are those that the proof of constant time
(`ApplyCT.lean`) relates in two runs.
-/

namespace VG.Proof.ChaCha20

open VG.AArch64
open VG.Spec.ChaCha20 (keyAt restAt leftAt bytesAt)

/-- AArch64 contract for `vg_chacha20_apply(state = x0, data = x1, len = x2) -> w0`.
The return address is in `x30`, which the code saves in the state, so no
stack is used. -/
def applyAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 768⟩
    let data : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
    s.rd = [] ∧ s.wr = [state, data] ∧ state.Disjoint data ∧
    (s.gpr .x0).toNat + 768 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64
  post s s' :=
    keyAt s'.mem (s.gpr .x0) = keyAt s.mem (s.gpr .x0) ∧
      if (s.gpr .x2).toNat ≤ leftAt s.mem (s.gpr .x0) then
        (s'.gpr .x0).setWidth 32 = 1 ∧
          bytesAt s'.mem (s.gpr .x1) (s.gpr .x2).toNat =
            List.zipWith (· ^^^ ·) (bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
              ((restAt s.mem (s.gpr .x0)).take (s.gpr .x2).toNat) ∧
          restAt s'.mem (s.gpr .x0) = (restAt s.mem (s.gpr .x0)).drop (s.gpr .x2).toNat
      else
        (s'.gpr .x0).setWidth 32 = 0 ∧
          bytesAt s'.mem (s.gpr .x1) (s.gpr .x2).toNat = bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat ∧
          restAt s'.mem (s.gpr .x0) = restAt s.mem (s.gpr .x0)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.sp = s₂.sp ∧ [leftAt s₁.mem (s₁.gpr .x0)] = [leftAt s₂.mem (s₂.gpr .x0)]

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.AArch64.Stream

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Stream
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Spec.ChaCha20 (keyAt restAt leftAt bytesAt stateAt serialize block)
open VG.Proof.ChaCha20.AArch64.Xor (wp_ldr32 wp_addImm32 wp_str32 wp_addImm wp_mov wp_ldr wp_str wp_movz)
open VG.Proof.ChaCha20.AArch64 (toNat_ofNat_lt)

/-! ## Memory as the model writes it -/

theorem write64_eq (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp [Mem.writeW]
theorem write32_eq (m : Mem) (a : Addr) (v : BitVec 32) : m.write a 4 v = m.writeW a v := by
  simp [Mem.writeW]
theorem read64_eq (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by simp [Mem.readW]
theorem read32_eq (m : Mem) (a : Addr) : m.read a 4 = m.readW a 32 := by simp [Mem.readW]

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev st : Addr := s₀.gpr .x0
abbrev dp : Addr := s₀.gpr .x1
abbrev L : Nat := (s₀.gpr .x2).toNat
/-- The number of bytes of keystream left, and those in the buffered block. -/
abbrev N : Nat := leftAt s₀.mem (VG.Proof.ChaCha20.AArch64.Stream.st s₀)
abbrev O : Nat := VG.Proof.ChaCha20.AArch64.Stream.N s₀ % 64
/-- The bytes from the buffered block, the whole blocks and the bytes of the
next block that `apply` uses. -/
abbrev H : Nat := headLen s₀.mem (VG.Proof.ChaCha20.AArch64.Stream.st s₀) (VG.Proof.ChaCha20.AArch64.Stream.L s₀)
abbrev NB : Nat := blocksOf s₀.mem (VG.Proof.ChaCha20.AArch64.Stream.st s₀) (VG.Proof.ChaCha20.AArch64.Stream.L s₀)
abbrev T : Nat := tailLen s₀.mem (VG.Proof.ChaCha20.AArch64.Stream.st s₀) (VG.Proof.ChaCha20.AArch64.Stream.L s₀)
abbrev S0 : CState := stateAt s₀.mem (VG.Proof.ChaCha20.AArch64.Stream.st s₀)
abbrev D0 (k : Nat) : Byte := s₀.mem (VG.Proof.ChaCha20.AArch64.Stream.dp s₀ + BitVec.ofNat 64 k)
abbrev stR : Region := ⟨VG.Proof.ChaCha20.AArch64.Stream.st s₀, 768⟩
abbrev dR : Region := ⟨VG.Proof.ChaCha20.AArch64.Stream.dp s₀, VG.Proof.ChaCha20.AArch64.Stream.L s₀⟩
/-- The keystream byte XORed into byte `k` of the data. -/
abbrev KS (k : Nat) : Byte :=
  if k < VG.Proof.ChaCha20.AArch64.Stream.H s₀ then s₀.mem (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 (128 - VG.Proof.ChaCha20.AArch64.Stream.O s₀ + k))
  else (serialize (block (ctr (VG.Proof.ChaCha20.AArch64.Stream.S0 s₀) ((k - VG.Proof.ChaCha20.AArch64.Stream.H s₀) / 64)))).getD ((k - VG.Proof.ChaCha20.AArch64.Stream.H s₀) % 64) 0
/-- The data with its first `j` bytes XORed. -/
abbrev Done (j : Nat) (m : Mem) : Prop :=
  ∀ k < VG.Proof.ChaCha20.AArch64.Stream.L s₀, m (VG.Proof.ChaCha20.AArch64.Stream.dp s₀ + BitVec.ofNat 64 k) = if k < j then VG.Proof.ChaCha20.AArch64.Stream.D0 s₀ k ^^^ VG.Proof.ChaCha20.AArch64.Stream.KS s₀ k else VG.Proof.ChaCha20.AArch64.Stream.D0 s₀ k
end

theorem L_lt (s₀ : State) : VG.Proof.ChaCha20.AArch64.Stream.L s₀ < 2 ^ 64 := (s₀.gpr .x2).isLt
theorem N_lt (s₀ : State) : VG.Proof.ChaCha20.AArch64.Stream.N s₀ < 2 ^ 64 := (s₀.mem.readW (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + 128) 64).isLt
theorem H_le (s₀ : State) : VG.Proof.ChaCha20.AArch64.Stream.H s₀ ≤ VG.Proof.ChaCha20.AArch64.Stream.L s₀ := Nat.min_le_right _ _
theorem H_le_O (s₀ : State) : VG.Proof.ChaCha20.AArch64.Stream.H s₀ ≤ VG.Proof.ChaCha20.AArch64.Stream.O s₀ := Nat.min_le_left _ _
theorem O_lt (s₀ : State) : VG.Proof.ChaCha20.AArch64.Stream.O s₀ < 64 := Nat.mod_lt _ (by decide)
theorem T_eq (s₀ : State) : VG.Proof.ChaCha20.AArch64.Stream.T s₀ = VG.Proof.ChaCha20.AArch64.Stream.L s₀ - VG.Proof.ChaCha20.AArch64.Stream.H s₀ - 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀ := by simp only [VG.Proof.ChaCha20.AArch64.Stream.T, VG.Proof.ChaCha20.AArch64.Stream.NB, tailLen, blocksOf, VG.Proof.ChaCha20.AArch64.Stream.H]; omega
theorem HNB_le (s₀ : State) : VG.Proof.ChaCha20.AArch64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀ ≤ VG.Proof.ChaCha20.AArch64.Stream.L s₀ := by
  have := VG.Proof.ChaCha20.AArch64.Stream.H_le s₀; simp only [VG.Proof.ChaCha20.AArch64.Stream.NB, blocksOf, VG.Proof.ChaCha20.AArch64.Stream.H] at *; omega

structure APre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [VG.Proof.ChaCha20.AArch64.Stream.stR s₀, VG.Proof.ChaCha20.AArch64.Stream.dR s₀]
  st_d : (VG.Proof.ChaCha20.AArch64.Stream.stR s₀).Disjoint (VG.Proof.ChaCha20.AArch64.Stream.dR s₀)
  wrap_st : (VG.Proof.ChaCha20.AArch64.Stream.st s₀).toNat + 768 ≤ 2 ^ 64
  wrap_d : (VG.Proof.ChaCha20.AArch64.Stream.dp s₀).toNat + VG.Proof.ChaCha20.AArch64.Stream.L s₀ ≤ 2 ^ 64

theorem APre.of (s₀ : State) (h : Proof.ChaCha20.applyAArch64.pre s₀) : VG.Proof.ChaCha20.AArch64.Stream.APre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem APre.w_st {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Stream.APre s₀) {d n : Nat} (h : d + n ≤ 768) :
    InRegions s₀.wr (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 d) n :=
  ⟨VG.Proof.ChaCha20.AArch64.Stream.stR s₀, by rw [hp.wr]; exact List.mem_cons_self .., Offset.contains_base _ h (by omega)⟩

theorem APre.r_st {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Stream.APre s₀) {d n : Nat} (h : d + n ≤ 768) :
    InRegions (s₀.rd ++ s₀.wr) (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 d) n := by
  rw [hp.rd, List.nil_append]; exact hp.w_st h

/-- Our caller's `x21`–`x23`, our return address, and the bytes left after
`apply`. -/
structure Saved (s₀ : State) (m : Mem) : Prop where
  x21 : m.readW (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 576) 64 = s₀.gpr .x21
  x22 : m.readW (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 584) 64 = s₀.gpr .x22
  x23 : m.readW (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 592) 64 = s₀.gpr .x23
  x30 : m.readW (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 600) 64 = s₀.gpr .x30
  left : m.readW (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 608) 64 = BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.N s₀ - VG.Proof.ChaCha20.AArch64.Stream.L s₀)

/-- Where they are. -/
abbrev savR (s₀ : State) : Region := ⟨VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 576, 40⟩

theorem savR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.AArch64.Stream.savR s₀) (VG.Proof.ChaCha20.AArch64.Stream.stR s₀) := Offset.sub_base _ (by omega)

theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : VG.Proof.ChaCha20.AArch64.Stream.Saved s₀ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (VG.Proof.ChaCha20.AArch64.Stream.savR s₀).Disjoint r) : VG.Proof.ChaCha20.AArch64.Stream.Saved s₀ m' := by
  have c : ∀ d, 576 ≤ d → d + 8 ≤ 616 → (VG.Proof.ChaCha20.AArch64.Stream.savR s₀).Contains (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 d) (64 / 8) :=
    fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
  exact ⟨by rw [hf.readW (c 576 (by decide) (by decide)) hd (by decide), h.x21],
    by rw [hf.readW (c 584 (by decide) (by decide)) hd (by decide), h.x22],
    by rw [hf.readW (c 592 (by decide) (by decide)) hd (by decide), h.x23],
    by rw [hf.readW (c 600 (by decide) (by decide)) hd (by decide), h.x30],
    by rw [hf.readW (c 608 (by decide) (by decide)) hd (by decide), h.left]⟩

/-! ## The check -/

/-- `(x <<< 58) >>> 58` keeps the low 6 bits. -/
theorem low6 (x : BitVec 64) : (x <<< 58) >>> 58 = BitVec.ofNat 64 (x.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

/-- The carry of `subs`, moved into a register by `adcs` of zeros. -/
theorem carry_ge (x : Nat) (b : BitVec 64) :
    BitVec.setWidth 64 (0 : BitVec 16) <<< (16 * 0) + BitVec.setWidth 64 (0 : BitVec 16) <<< (16 * 0) +
      BitVec.ofNat 64 (decide (2 ^ 64 ≤ x + (~~~b).toNat + true.toNat)).toNat =
      BitVec.ofNat 64 (decide (b.toNat ≤ x)).toNat := by
  have e : (2 ^ 64 ≤ x + (~~~b).toNat + true.toNat) ↔ b.toNat ≤ x := by
    rw [BitVec.toNat_not]; have := b.isLt; simp only [Bool.toNat_true]; omega
  rw [show BitVec.setWidth 64 (0 : BitVec 16) <<< (16 * 0) = 0 by decide]
  simp only [e]
  simp

/-- After the check. -/
structure Q0 (s₀ s : State) : Prop where
  x9 : s.gpr .x9 = BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.N s₀)
  x10 : s.gpr .x10 = BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.O s₀)
  x11 : s.gpr .x11 = BitVec.ofNat 64 (decide (VG.Proof.ChaCha20.AArch64.Stream.L s₀ ≤ VG.Proof.ChaCha20.AArch64.Stream.N s₀)).toNat
  x12 : s.gpr .x12 = BitVec.ofNat 64 (decide (VG.Proof.ChaCha20.AArch64.Stream.L s₀ ≤ VG.Proof.ChaCha20.AArch64.Stream.O s₀)).toNat
  keep : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  v : s.v = s₀.v
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

set_option simprocs false in
theorem check_ok {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Stream.APre s₀) : WP isa (.block check) s₀ (VG.Proof.ChaCha20.AArch64.Stream.Q0 s₀) := by
  have i₁ := hp.r_st (d := 128) (n := 8) (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [check, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
    Size.bytes, State.load, State.read, State.write, State.addWithCarry, Size.bits, BitVec.setWidth_eq,
    Option.bind_some, Option.map_some, i₁, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  have hn : s₀.mem.read (s₀.gpr .x0 + 128#64) 8 = BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.N s₀) := by
    rw [VG.Proof.ChaCha20.AArch64.Stream.read64_eq]; simp [VG.Proof.ChaCha20.AArch64.Stream.N, leftAt]
  have hO : VG.Proof.ChaCha20.AArch64.Stream.N s₀ % 64 < 2 ^ 64 := by omega
  simp only [hn, VG.Proof.ChaCha20.AArch64.Stream.low6, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (VG.Proof.ChaCha20.AArch64.Stream.N_lt s₀), Nat.mod_eq_of_lt hO,
    VG.Proof.ChaCha20.AArch64.Stream.carry_ge]
  refine ⟨by simp (config := {decide := true}), by simp (config := {decide := true}),
    by simp (config := {decide := true}), by simp (config := {decide := true}),
    fun r h₁ h₂ h₃ h₄ h₅ => by simp [h₁, h₂, h₃, h₄, h₅], rfl, rfl, rfl, rfl, rfl⟩


/-- The callee-saved registers our code never writes. -/
def kept : List Reg := [.x19, .x20, .x24, .x25, .x26, .x27, .x28]

theorem kept_ne {r : Reg} (hr : r ∈ VG.Proof.ChaCha20.AArch64.Stream.kept) {r' : Reg} (h : r' ∉ VG.Proof.ChaCha20.AArch64.Stream.kept := by decide) : r ≠ r' :=
  fun e => h (e ▸ hr)

/-- What `apply` guarantees (`applyAArch64`), and the registers it keeps. -/
def Final (s₀ s : State) : Prop :=
  (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ Proof.ChaCha20.applyAArch64.post s₀ s

/-- The low halves of v8–v15 are those on entry. -/
abbrev VKeep (s₀ s : State) : Prop :=
  ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64

theorem fail_ok {s₀ : State} (hlt : VG.Proof.ChaCha20.AArch64.Stream.N s₀ < VG.Proof.ChaCha20.AArch64.Stream.L s₀) {s : State} (h : VG.Proof.ChaCha20.AArch64.Stream.Q0 s₀ s) :
    WP isa (.block [.movz .x .x0 0 0]) s (VG.Proof.ChaCha20.AArch64.Stream.Final s₀) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.write,
    Size.bits, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left', ↓reduceIte, Nat.reduceMul, Nat.reduceLT]
  unfold VG.Proof.ChaCha20.AArch64.Stream.Final
  refine ⟨fun r hr => ?_, ?_⟩
  · have : r ≠ .x0 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp only [this.1, ite_false]
    exact h.keep r this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2.1 this.2.2.2.2.2
  · show keyAt _ _ = _ ∧ _
    rw [ite_neg (show ¬ VG.Proof.ChaCha20.AArch64.Stream.L s₀ ≤ VG.Proof.ChaCha20.AArch64.Stream.N s₀ by omega)]
    dsimp only
    rw [h.mem]
    exact ⟨rfl, by simp, rfl, rfl⟩


/-! ## The bytes left in the buffered block -/

/-- The state of memory before the data is touched. -/
structure Mid (s₀ : State) (m : Mem) : Prop where
  keep : ∀ i < 136, m (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 i) = s₀.mem (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 i)
  saved : VG.Proof.ChaCha20.AArch64.Stream.Saved s₀ m

theorem Mid.state {s₀ : State} {m : Mem} (h : VG.Proof.ChaCha20.AArch64.Stream.Mid s₀ m) : stateAt m (VG.Proof.ChaCha20.AArch64.Stream.st s₀) = VG.Proof.ChaCha20.AArch64.Stream.S0 s₀ :=
  stateAt_congr fun i hi => h.keep i (by omega)

/-- After `start`, with `x` in `x2`. -/
structure R1 (s₀ : State) (x : Nat) (s : State) : Prop where
  x21 : s.gpr .x21 = VG.Proof.ChaCha20.AArch64.Stream.st s₀
  x22 : s.gpr .x22 = VG.Proof.ChaCha20.AArch64.Stream.dp s₀
  x23 : s.gpr .x23 = BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.L s₀)
  x2 : s.gpr .x2 = BitVec.ofNat 64 x
  x10 : s.gpr .x10 = BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.O s₀)
  keep : ∀ r ∈ VG.Proof.ChaCha20.AArch64.Stream.kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mid : VG.Proof.ChaCha20.AArch64.Stream.Mid s₀ s.mem
  done : VG.Proof.ChaCha20.AArch64.Stream.Done s₀ 0 s.mem
  frame : Frame [VG.Proof.ChaCha20.AArch64.Stream.stR s₀] s₀.mem s.mem

/-- The memory after `start`. -/
def startMem (s₀ : State) : Mem :=
  ((((s₀.mem.writeW (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 576) (s₀.gpr .x21)).writeW (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 584)
    (s₀.gpr .x22)).writeW (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 592) (s₀.gpr .x23)).writeW (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 600)
    (s₀.gpr .x30)).writeW (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 608) (BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.N s₀ - VG.Proof.ChaCha20.AArch64.Stream.L s₀))

theorem startMem_frame (s₀ : State) : Frame [VG.Proof.ChaCha20.AArch64.Stream.stR s₀] s₀.mem (VG.Proof.ChaCha20.AArch64.Stream.startMem s₀) := by
  simp only [VG.Proof.ChaCha20.AArch64.Stream.startMem]
  exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_st _ (d := 576) (by decide))).writeW
    (List.mem_singleton_self _) _ (contains_st _ (d := 584) (by decide))).writeW (List.mem_singleton_self _) _
    (contains_st _ (d := 592) (by decide))).writeW (List.mem_singleton_self _) _
    (contains_st _ (d := 600) (by decide))).writeW (List.mem_singleton_self _) _
    (contains_st _ (d := 608) (by decide))

theorem startMem_mid (s₀ : State) : VG.Proof.ChaCha20.AArch64.Stream.Mid s₀ (VG.Proof.ChaCha20.AArch64.Stream.startMem s₀) := by
  refine ⟨fun i hi => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [VG.Proof.ChaCha20.AArch64.Stream.startMem]
    rw [byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
      byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
      byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
      byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
      byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega)]
  all_goals simp (disch := decide) only [VG.Proof.ChaCha20.AArch64.Stream.startMem, Mem.readW_writeW_self64, readW_writeW_ofNat]

theorem start_ok {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Stream.APre s₀) (hle : VG.Proof.ChaCha20.AArch64.Stream.L s₀ ≤ VG.Proof.ChaCha20.AArch64.Stream.N s₀) {s : State} (h : VG.Proof.ChaCha20.AArch64.Stream.Q0 s₀ s) :
    WP isa (.block start) s fun s' => VG.Proof.ChaCha20.AArch64.Stream.R1 s₀ (VG.Proof.ChaCha20.AArch64.Stream.L s₀) s' ∧ s'.gpr .x12 = s.gpr .x12 := by
  have o576 := hp.w_st (d := 576) (n := 8) (by decide)
  have o584 := hp.w_st (d := 584) (n := 8) (by decide)
  have o592 := hp.w_st (d := 592) (n := 8) (by decide)
  have o600 := hp.w_st (d := 600) (n := 8) (by decide)
  have o608 := hp.w_st (d := 608) (n := 8) (by decide)
  rw [← h.wr] at o576 o584 o592 o600 o608
  have hx0 := h.keep .x0 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx1 := h.keep .x1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx2 := h.keep .x2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx21 := h.keep .x21 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx22 := h.keep .x22 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx23 := h.keep .x23 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx30 := h.keep .x30 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsub : BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.N s₀) - s₀.gpr .x2 = BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.N s₀ - VG.Proof.ChaCha20.AArch64.Stream.L s₀) := by
    rw [show s₀.gpr .x2 = BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.L s₀) by simp [VG.Proof.ChaCha20.AArch64.Stream.L]]
    exact Proof.ChaCha20.AArch64.Xor.sub_ofNat hle
  apply WP.of_runBlock
  simp only [start, mov, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
    Size.bytes, State.store, State.read, State.write, Size.bits, BitVec.setWidth_eq, Option.bind_some,
    hx0, hx1, hx2, hx21, hx22, hx23, hx30, h.x9, hsub, o576, o584, o592, o600, o608,
    Option.some.injEq, exists_eq_left', VG.Proof.ChaCha20.AArch64.Stream.write64_eq, BitVec.add_zero, ↓reduceIte, reduceCtorEq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self]
  rw [h.mem]
  refine ⟨⟨by simp, by simp,
    by simp [VG.Proof.ChaCha20.AArch64.Stream.L], by simp [VG.Proof.ChaCha20.AArch64.Stream.L, hx2],
    by simp [h.x10], fun r hr => ?_, h.rd, h.wr, VG.Proof.ChaCha20.AArch64.Stream.startMem_mid s₀, fun k hk => ?_,
    VG.Proof.ChaCha20.AArch64.Stream.startMem_frame s₀⟩, by simp⟩
  · simp only [VG.Proof.ChaCha20.AArch64.Stream.kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;>
      exact h.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
  · have e := (VG.Proof.ChaCha20.AArch64.Stream.startMem_frame s₀).bytes (R := VG.Proof.ChaCha20.AArch64.Stream.dR s₀) (by simpa using hp.st_d.symm)
      (show VG.Proof.ChaCha20.AArch64.Stream.L s₀ ≤ 2 ^ 64 by have := VG.Proof.ChaCha20.AArch64.Stream.L_lt s₀; omega) hk
    simp only [VG.Proof.ChaCha20.AArch64.Stream.startMem] at e
    dsimp only
    rw [e]
    simp


theorem sel_ok {s₀ : State} {s : State} (h : VG.Proof.ChaCha20.AArch64.Stream.R1 s₀ (VG.Proof.ChaCha20.AArch64.Stream.L s₀) s)
    (hc : s.gpr .x12 = BitVec.ofNat 64 (decide (VG.Proof.ChaCha20.AArch64.Stream.L s₀ ≤ VG.Proof.ChaCha20.AArch64.Stream.O s₀)).toNat) :
    WP isa (.ite (.zero .x .x12) (.block [mov .x2 .x10]) (.block [])) s (VG.Proof.ChaCha20.AArch64.Stream.R1 s₀ (VG.Proof.ChaCha20.AArch64.Stream.H s₀)) := by
  refine WP.ite (decide (VG.Proof.ChaCha20.AArch64.Stream.O s₀ < VG.Proof.ChaCha20.AArch64.Stream.L s₀)) (by
      have e : isa.eval (.zero .x .x12) s = some (s.gpr .x12 == 0) := Proof.ChaCha20.AArch64.Xor.eval_zero s .x12
      rw [e, hc]; by_cases hh : VG.Proof.ChaCha20.AArch64.Stream.L s₀ ≤ VG.Proof.ChaCha20.AArch64.Stream.O s₀ <;> simp [hh] <;> omega) (fun hlt => ?_) (fun hge => ?_)
  · simp only [decide_eq_true_eq] at hlt
    refine Proof.ChaCha20.AArch64.Xor.wp_mov fun s' u => WP.block_nil ?_
    exact ⟨by rw [u.other _ (by decide), h.x21], by rw [u.other _ (by decide), h.x22],
      by rw [u.other _ (by decide), h.x23],
      by rw [u.gpr, h.x10, VG.Proof.ChaCha20.AArch64.Stream.H, headLen, bufLeft, Nat.min_eq_left (Nat.le_of_lt hlt)],
      by rw [u.other _ (by decide), h.x10],
      fun r hr => by rw [u.other r (VG.Proof.ChaCha20.AArch64.Stream.kept_ne hr)]; exact h.keep r hr,
      by rw [u.rd, h.rd], by rw [u.wr, h.wr], u.mem ▸ h.mid, u.mem ▸ h.done, u.mem ▸ h.frame⟩
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hge
    refine WP.block_nil (M := isa) ⟨h.x21, h.x22, h.x23, ?_, h.x10, h.keep, h.rd, h.wr, h.mid, h.done, h.frame⟩
    rw [h.x2, VG.Proof.ChaCha20.AArch64.Stream.H, headLen, bufLeft, Nat.min_eq_right hge]

/-- After `part1`: the bytes from the buffered block XORed, and `x2` the
bytes of the whole blocks. -/
structure Q1 (s₀ s : State) : Prop where
  x21 : s.gpr .x21 = VG.Proof.ChaCha20.AArch64.Stream.st s₀
  x22 : s.gpr .x22 = VG.Proof.ChaCha20.AArch64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.H s₀)
  x23 : s.gpr .x23 = BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.L s₀ - VG.Proof.ChaCha20.AArch64.Stream.H s₀)
  x2 : s.gpr .x2 = BitVec.ofNat 64 (64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀)
  keep : ∀ r ∈ VG.Proof.ChaCha20.AArch64.Stream.kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mid : VG.Proof.ChaCha20.AArch64.Stream.Mid s₀ s.mem
  done : VG.Proof.ChaCha20.AArch64.Stream.Done s₀ (VG.Proof.ChaCha20.AArch64.Stream.H s₀) s.mem
  frame : Frame [VG.Proof.ChaCha20.AArch64.Stream.stR s₀, VG.Proof.ChaCha20.AArch64.Stream.dR s₀] s₀.mem s.mem

theorem d_ne_st {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Stream.APre s₀) {j k : Nat} (hj : j < VG.Proof.ChaCha20.AArch64.Stream.L s₀) (hk : k < 768) :
    VG.Proof.ChaCha20.AArch64.Stream.dp s₀ + BitVec.ofNat 64 j ≠ VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 k := by
  intro he
  have c₁ : (VG.Proof.ChaCha20.AArch64.Stream.dR s₀).Contains (VG.Proof.ChaCha20.AArch64.Stream.dp s₀ + BitVec.ofNat 64 j) 1 :=
    Offset.contains_base _ (by omega) (by have := VG.Proof.ChaCha20.AArch64.Stream.L_lt s₀; omega)
  have c₂ : (VG.Proof.ChaCha20.AArch64.Stream.stR s₀).Contains (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega) (by omega)
  rw [he] at c₁
  exact hp.st_d _ c₂ c₁

theorem dR_byte {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Stream.APre s₀) {k : Nat} (hk : k < VG.Proof.ChaCha20.AArch64.Stream.L s₀) : InRegions s₀.wr (VG.Proof.ChaCha20.AArch64.Stream.dp s₀ + BitVec.ofNat 64 k) 1 :=
  ⟨VG.Proof.ChaCha20.AArch64.Stream.dR s₀, by rw [hp.wr]; simp, Offset.contains_base _ (by omega) (by have := VG.Proof.ChaCha20.AArch64.Stream.L_lt s₀; omega)⟩

theorem stR_byte {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Stream.APre s₀) {k : Nat} (hk : k < 768) : InRegions s₀.wr (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 k) 1 :=
  ⟨VG.Proof.ChaCha20.AArch64.Stream.stR s₀, by rw [hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩

theorem not_in_prefix (p : Addr) {k c : Nat} (hk : c ≤ k) (hk' : k < 2 ^ 64) :
    ¬ (⟨p, c⟩ : Region).Contains (p + BitVec.ofNat 64 k) 1 := by
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat p hk']
  omega

theorem prefix_sub (p : Addr) {c n : Nat} (h : c ≤ n) : Region.Sub ⟨p, c⟩ ⟨p, n⟩ := Region.sub_prefix h

/-- `(x >>> 6) <<< 6` rounds down to a multiple of 64. -/
theorem round64 {x : Nat} (hx : x < 2 ^ 64) :
    (BitVec.ofNat 64 x >>> 6) <<< 6 = BitVec.ofNat 64 (64 * (x / 64)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem wp_lsl {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Proof.ChaCha20.AArch64.Xor.Upd s s' d (s.gpr n <<< sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsl .x d n sh :: is)) s Q :=
  Proof.ChaCha20.AArch64.Xor.WP.cons (s' := s.write .x d (s.gpr n <<< sh)) (by simp [exec, h, State.read])
    (k _ (Proof.ChaCha20.AArch64.Xor.Upd.write64 _ _ _))

set_option simprocs false in
theorem part1_ok {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Stream.APre s₀) (hle : VG.Proof.ChaCha20.AArch64.Stream.L s₀ ≤ VG.Proof.ChaCha20.AArch64.Stream.N s₀) {s : State} (h : VG.Proof.ChaCha20.AArch64.Stream.Q0 s₀ s) :
    WP isa part1 s (VG.Proof.ChaCha20.AArch64.Stream.Q1 s₀) := by
  have hL := VG.Proof.ChaCha20.AArch64.Stream.L_lt s₀
  have hH := VG.Proof.ChaCha20.AArch64.Stream.H_le s₀
  have hHO := VG.Proof.ChaCha20.AArch64.Stream.H_le_O s₀
  have hO := VG.Proof.ChaCha20.AArch64.Stream.O_lt s₀
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.AArch64.Stream.start_ok hp hle h) fun s₁ ⟨h₁, hc₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.AArch64.Stream.sel_ok h₁ (by rw [hc₁, h.x12])) fun s₂ h₂ => ?_)
  -- The pointer to the bytes left in the buffered block.
  have h₃ : WP isa (.block [.addImm .x .x1 .x21 128, .sub .x .x1 .x1 .x10]) s₂
      fun s₃ => VG.Proof.ChaCha20.AArch64.Stream.R1 s₀ (VG.Proof.ChaCha20.AArch64.Stream.H s₀) s₃ ∧ s₃.gpr .x1 = VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 (128 - VG.Proof.ChaCha20.AArch64.Stream.O s₀) := by
    refine Proof.ChaCha20.AArch64.Xor.wp_addImm (by decide) fun s' u => ?_
    refine Proof.ChaCha20.AArch64.Xor.wp_sub fun s'' u' => WP.block_nil ?_
    have g : ∀ r, r ≠ .x1 → s''.gpr r = s₂.gpr r := fun r hr => by rw [u'.other r hr, u.other r hr]
    refine ⟨⟨by rw [g _ (by decide), h₂.x21], by rw [g _ (by decide), h₂.x22], by rw [g _ (by decide), h₂.x23],
      by rw [g _ (by decide), h₂.x2], by rw [g _ (by decide), h₂.x10],
      fun r hr => by rw [g r (VG.Proof.ChaCha20.AArch64.Stream.kept_ne hr)]; exact h₂.keep r hr,
      by rw [u'.rd, u.rd, h₂.rd], by rw [u'.wr, u.wr, h₂.wr], by rw [u'.mem, u.mem]; exact h₂.mid,
      by rw [u'.mem, u.mem]; exact h₂.done, by rw [u'.mem, u.mem]; exact h₂.frame⟩, ?_⟩
    rw [u'.gpr, u.gpr, u.other .x10 (by decide), h₂.x21, h₂.x10,
      show (128#64 : BitVec 64) = BitVec.ofNat 64 (128 - VG.Proof.ChaCha20.AArch64.Stream.O s₀) + BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.O s₀) by
        rw [BitVec.ofNat_add_ofNat, show 128 - VG.Proof.ChaCha20.AArch64.Stream.O s₀ + VG.Proof.ChaCha20.AArch64.Stream.O s₀ = 128 by omega],
      ← BitVec.add_assoc, BitVec.add_sub_cancel]
  refine WP.seq (WP.mono h₃ fun s₃ ⟨h₃, hx1⟩ => ?_)
  have hb : VG.Proof.ChaCha20.AArch64.Stream.BPre s₃ (VG.Proof.ChaCha20.AArch64.Stream.dp s₀) (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 (128 - VG.Proof.ChaCha20.AArch64.Stream.O s₀)) (VG.Proof.ChaCha20.AArch64.Stream.H s₀) :=
    ⟨h₃.x22, hx1, h₃.x2, by omega, fun k hk => by rw [h₃.wr]; exact VG.Proof.ChaCha20.AArch64.Stream.dR_byte hp (by omega),
      fun k hk => by
        rw [h₃.wr, Offset.add_add]
        obtain ⟨r, hr, hc⟩ := VG.Proof.ChaCha20.AArch64.Stream.stR_byte hp (k := 128 - VG.Proof.ChaCha20.AArch64.Stream.O s₀ + k) (by omega)
        exact ⟨r, List.mem_append_right _ hr, hc⟩,
      fun j hj k hk => by rw [Offset.add_add]; exact VG.Proof.ChaCha20.AArch64.Stream.d_ne_st hp (by omega) (by omega)⟩
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.AArch64.Stream.xorBytes_ok hb) fun s₄ h₄ => ?_)
  have hx23 : s₄.gpr .x23 = BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.L s₀ - VG.Proof.ChaCha20.AArch64.Stream.H s₀) := by
    rw [h₄.x23, h₃.x23, Proof.ChaCha20.AArch64.Xor.sub_ofNat hH]
  refine Proof.ChaCha20.AArch64.Xor.wp_lsr (by decide) fun s₅ u₅ => VG.Proof.ChaCha20.AArch64.Stream.wp_lsl (by decide) fun s₆ u₆ =>
    WP.block_nil ?_
  have g : ∀ r, r ≠ .x2 → s₆.gpr r = s₄.gpr r := fun r hr => by rw [u₆.other r hr, u₅.other r hr]
  have hm : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  have hnb : 64 * ((VG.Proof.ChaCha20.AArch64.Stream.L s₀ - VG.Proof.ChaCha20.AArch64.Stream.H s₀) / 64) = 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀ := by simp only [VG.Proof.ChaCha20.AArch64.Stream.NB, blocksOf, VG.Proof.ChaCha20.AArch64.Stream.H]
  refine ⟨by rw [g _ (by decide), h₄.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h₃.x21],
    by rw [g _ (by decide), h₄.x22], by rw [g _ (by decide), hx23],
    by rw [u₆.gpr, u₅.gpr, hx23, VG.Proof.ChaCha20.AArch64.Stream.round64 (by omega), hnb],
    fun r hr => by
      rw [g r (VG.Proof.ChaCha20.AArch64.Stream.kept_ne hr), h₄.keep r (VG.Proof.ChaCha20.AArch64.Stream.kept_ne hr) (VG.Proof.ChaCha20.AArch64.Stream.kept_ne hr) (VG.Proof.ChaCha20.AArch64.Stream.kept_ne hr) (VG.Proof.ChaCha20.AArch64.Stream.kept_ne hr) (VG.Proof.ChaCha20.AArch64.Stream.kept_ne hr)
        (VG.Proof.ChaCha20.AArch64.Stream.kept_ne hr)]
      exact h₃.keep r hr,
    by rw [u₆.rd, u₅.rd, h₄.rd, h₃.rd], by rw [u₆.wr, u₅.wr, h₄.wr, h₃.wr], ⟨fun i hi => ?_, ?_⟩,
    fun k hk => ?_, ?_⟩
  · rw [hm, h₄.frame _ fun r hr hc => ?_]
    · exact h₃.mid.keep i hi
    · simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_d _ (Offset.contains_base (VG.Proof.ChaCha20.AArch64.Stream.st s₀) (d := i) (n := 1) (k := 768) (by omega) (by omega))
        (Offset.sub_base (VG.Proof.ChaCha20.AArch64.Stream.dp s₀) (d := 0) (n := VG.Proof.ChaCha20.AArch64.Stream.H s₀) (k := VG.Proof.ChaCha20.AArch64.Stream.L s₀) (by omega) _ (by simpa using hc))
  · rw [hm]
    exact h₃.mid.saved.frame h₄.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.st_d.sub_left (VG.Proof.ChaCha20.AArch64.Stream.savR_sub s₀)).sub_right fun x hx => by
        simpa using Offset.sub_base (VG.Proof.ChaCha20.AArch64.Stream.dp s₀) (d := 0) (n := VG.Proof.ChaCha20.AArch64.Stream.H s₀) (k := VG.Proof.ChaCha20.AArch64.Stream.L s₀) (by omega) x (by simpa using hx)
  · rw [hm]
    by_cases hk' : k < VG.Proof.ChaCha20.AArch64.Stream.H s₀
    · rw [h₄.data k hk', h₃.done k hk, Offset.add_add, h₃.mid.keep _ (by omega)]
      simp [hk', VG.Proof.ChaCha20.AArch64.Stream.KS]
    · rw [h₄.frame _ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.ChaCha20.AArch64.Stream.not_in_prefix _ (by omega) (by omega),
        h₃.done k hk]
      simp [hk']
  · rw [hm]
    exact (h₃.frame.mono (by simp)).trans (h₄.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.ChaCha20.AArch64.Stream.dR s₀, by simp, VG.Proof.ChaCha20.AArch64.Stream.prefix_sub _ hH⟩)

/-! ## The whole blocks -/

/-- The memory before the counter is advanced: the state copied to
`p + 192`. -/
def copyMem8 (m : Mem) (p : Addr) : Mem :=
  (((((((m.writeW (p + BitVec.ofNat 64 192) (m.readW p 64)).writeW (p + BitVec.ofNat 64 200)
    (m.readW (p + BitVec.ofNat 64 8) 64)).writeW (p + BitVec.ofNat 64 208) (m.readW (p + BitVec.ofNat 64 16) 64)).writeW
    (p + BitVec.ofNat 64 216) (m.readW (p + BitVec.ofNat 64 24) 64)).writeW (p + BitVec.ofNat 64 224)
    (m.readW (p + BitVec.ofNat 64 32) 64)).writeW (p + BitVec.ofNat 64 232) (m.readW (p + BitVec.ofNat 64 40) 64)).writeW
    (p + BitVec.ofNat 64 240) (m.readW (p + BitVec.ofNat 64 48) 64)).writeW (p + BitVec.ofNat 64 248)
    (m.readW (p + BitVec.ofNat 64 56) 64)

/-- And its counter advanced by `c`. -/
def copyMem (m : Mem) (p : Addr) (c : BitVec 32) : Mem :=
  (VG.Proof.ChaCha20.AArch64.Stream.copyMem8 m p).writeW (p + BitVec.ofNat 64 48) ((m.readW (p + BitVec.ofNat 64 48) 64).setWidth 32 + c)

theorem args_exec {s : State} {p : Addr} (hx21 : s.gpr .x21 = p)
    (hw : ∀ d, d + 8 ≤ 768 → InRegions s.wr (p + BitVec.ofNat 64 d) 8) (hrd : s.rd = []) :
    WP isa (.block blocksArgs) s fun s' => s'.mem = VG.Proof.ChaCha20.AArch64.Stream.copyMem s.mem p ((s.gpr .x2 >>> 6).setWidth 32) ∧
      s'.gpr .x0 = p + BitVec.ofNat 64 192 ∧ s'.gpr .x1 = s.gpr .x22 ∧ s'.gpr .x3 = p + BitVec.ofNat 64 256 ∧
      s'.gpr .x2 = s.gpr .x2 ∧ s'.gpr .x22 = s.gpr .x22 + s.gpr .x2 ∧
      s'.gpr .x23 = s.gpr .x23 - s.gpr .x2 ∧ s'.gpr .x21 = p ∧
      (∀ r ∈ VG.Proof.ChaCha20.AArch64.Stream.kept, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i : ∀ d, d + 8 ≤ 768 → InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [hrd, List.nil_append]; exact hw d hd
  have o4 : InRegions s.wr (p + BitVec.ofNat 64 48) 4 := by
    obtain ⟨r, hr, hc⟩ := hw 48 (by decide); exact ⟨r, hr, by simp only [Region.Contains] at hc ⊢; omega⟩
  have i0 := i 0 (by decide); have i8 := i 8 (by decide); have i16 := i 16 (by decide)
  have i24 := i 24 (by decide); have i32 := i 32 (by decide); have i40 := i 40 (by decide)
  have i48 := i 48 (by decide); have i56 := i 56 (by decide)
  have o192 := hw 192 (by decide); have o200 := hw 200 (by decide); have o208 := hw 208 (by decide)
  have o216 := hw 216 (by decide); have o224 := hw 224 (by decide); have o232 := hw 232 (by decide)
  have o240 := hw 240 (by decide); have o248 := hw 248 (by decide)
  simp only [BitVec.add_zero] at i0
  apply WP.of_runBlock
  simp only [blocksArgs, mov, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
    Size.bytes, State.load, State.store, State.read, State.write, Size.bits, BitVec.setWidth_eq,
    Option.bind_some, Option.map_some, hx21, i0, i8, i16, i24, i32, i40, i48, i56, o4, o192, o200, o208, o216,
    o224, o232, o240, o248, Option.some.injEq, exists_eq_left', VG.Proof.ChaCha20.AArch64.Stream.write64_eq, VG.Proof.ChaCha20.AArch64.Stream.read64_eq,
    BitVec.add_zero, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, ↓reduceIte, reduceCtorEq, and_self]
  have e : ∀ v : BitVec 32, BitVec.setWidth 32 (BitVec.setWidth 64 v) = v := fun v => BitVec.setWidth_setWidth_of_le _ (by decide)
  refine ⟨by rw [VG.Proof.ChaCha20.AArch64.Stream.write32_eq, e]; rfl, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    fun r hr => ?_, trivial⟩
  simp only [VG.Proof.ChaCha20.AArch64.Stream.kept, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- Reading a word after writing a 64-bit word elsewhere, at offsets from `p`. -/
theorem readW64_ofNat (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d < 2 ^ 32) (he : e < 2 ^ 32) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 64 = m.readW (p + BitVec.ofNat 64 d) 64 :=
  readW_writeW_ofNat m p v h (by omega) (by omega) (by decide)

theorem copyMem8_frame (m : Mem) (p : Addr) : Frame [⟨p + BitVec.ofNat 64 192, 64⟩] m (VG.Proof.ChaCha20.AArch64.Stream.copyMem8 m p) := by
  have c : ∀ d, 192 ≤ d → d + 8 ≤ 256 →
      (⟨p + BitVec.ofNat 64 192, 64⟩ : Region).Contains (p + BitVec.ofNat 64 d) (64 / 8) :=
    fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
  simp only [VG.Proof.ChaCha20.AArch64.Stream.copyMem8]
  have w : ∀ {m' : Mem} (_ : Frame [⟨p + BitVec.ofNat 64 192, 64⟩] m m') (d : Nat), 192 ≤ d → d + 8 ≤ 256 →
      ∀ v : BitVec 64, Frame [⟨p + BitVec.ofNat 64 192, 64⟩] m (m'.writeW (p + BitVec.ofNat 64 d) v) :=
    fun hf d h₁ h₂ v => hf.writeW (List.mem_singleton_self _) v (c d h₁ h₂)
  exact w (w (w (w (w (w (w (w (Frame.refl _ _) 192 (by decide) (by decide) _) 200 (by decide) (by decide) _)
    208 (by decide) (by decide) _) 216 (by decide) (by decide) _) 224 (by decide) (by decide) _) 232 (by decide)
    (by decide) _) 240 (by decide) (by decide) _) 248 (by decide) (by decide) _

theorem copyMem_frame (m : Mem) (p : Addr) (c : BitVec 32) :
    Frame [⟨p, 64⟩, ⟨p + BitVec.ofNat 64 192, 64⟩] m (VG.Proof.ChaCha20.AArch64.Stream.copyMem m p c) := by
  refine ((VG.Proof.ChaCha20.AArch64.Stream.copyMem8_frame m p).mono (by simp)).writeW (List.mem_cons_self ..) _ ?_
  exact Offset.contains_base _ (by omega) (by omega)

/-- The copy of the state. -/
theorem copyMem_copy (m : Mem) (p : Addr) (c : BitVec 32) :
    stateAt (VG.Proof.ChaCha20.AArch64.Stream.copyMem m p c) (p + BitVec.ofNat 64 192) = stateAt m p := by
  refine stateAt_congr fun i hi => ?_
  rw [VG.Proof.ChaCha20.AArch64.Stream.copyMem, Offset.add_add, byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega)]
  have hw : ∀ k, 24 ≤ k → k < 32 → (VG.Proof.ChaCha20.AArch64.Stream.copyMem8 m p).readW (p + BitVec.ofNat 64 (8 * k)) 64 =
      m.readW (p + BitVec.ofNat 64 (8 * (k - 24))) 64 := by
    intro k h₁ h₂
    simp only [VG.Proof.ChaCha20.AArch64.Stream.copyMem8]
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨ k = 30 ∨ k = 31 := by omega
    all_goals simp only [Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceAdd, Nat.reducePow, or_false, Nat.reduceMul, Nat.reduceSub, Mem.readW_writeW_self64,
      VG.Proof.ChaCha20.AArch64.Stream.readW64_ofNat, BitVec.add_zero]
  have hm : ∀ k, 0 ≤ k → k < 8 → m.readW (p + BitVec.ofNat 64 (8 * k)) 64 = m.readW (p + BitVec.ofNat 64 (8 * k)) 64 :=
    fun _ _ _ => rfl
  rw [byte_of_words64 hw (by omega) (by omega), byte_of_words64 hm (i := i) (Nat.zero_le _) (by omega),
    show (192 + i) / 8 - 24 = i / 8 by omega, show (192 + i) % 8 = i % 8 by omega]

/-- The state, with its counter advanced. -/
theorem copyMem_state (m : Mem) (p : Addr) (c : BitVec 32) :
    stateAt (VG.Proof.ChaCha20.AArch64.Stream.copyMem m p c) p = (stateAt m p).set 12 ((stateAt m p)[12] + c) := by
  rw [VG.Proof.ChaCha20.AArch64.Stream.copyMem, Proof.ChaCha20.AArch64.Xor.stateAt_writeW_counter,
    Proof.ChaCha20.AArch64.Xor.stateAt_frame (VG.Proof.ChaCha20.AArch64.Stream.copyMem8_frame m p) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint _ (by omega) (by omega)),
    readW64_setWidth]
  simp [stateAt]

theorem shr_eq {nb : Nat} (h : 64 * nb < 2 ^ 64) :
    (BitVec.ofNat 64 (64 * nb) >>> 6).setWidth 32 = BitVec.ofNat 32 nb := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h, Nat.shiftRight_eq_div_pow]
  omega

/-- After `part2`: the whole blocks XORed, and the counter advanced past
them. -/
structure Q2 (s₀ s : State) : Prop where
  x21 : s.gpr .x21 = VG.Proof.ChaCha20.AArch64.Stream.st s₀
  x22 : s.gpr .x22 = VG.Proof.ChaCha20.AArch64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀)
  x23 : s.gpr .x23 = BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.T s₀)
  keep : ∀ r ∈ VG.Proof.ChaCha20.AArch64.Stream.kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : stateAt s.mem (VG.Proof.ChaCha20.AArch64.Stream.st s₀) = ctr (VG.Proof.ChaCha20.AArch64.Stream.S0 s₀) (VG.Proof.ChaCha20.AArch64.Stream.NB s₀)
  buf : ∀ i < 64, s.mem (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 (64 + i)) = s₀.mem (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 (64 + i))
  saved : VG.Proof.ChaCha20.AArch64.Stream.Saved s₀ s.mem
  done : VG.Proof.ChaCha20.AArch64.Stream.Done s₀ (VG.Proof.ChaCha20.AArch64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀) s.mem
  frame : Frame [VG.Proof.ChaCha20.AArch64.Stream.stR s₀, VG.Proof.ChaCha20.AArch64.Stream.dR s₀] s₀.mem s.mem

theorem nb_zero_ok {s₀ : State} {s : State} (h : VG.Proof.ChaCha20.AArch64.Stream.Q1 s₀ s) (h0 : 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀ = 0) : VG.Proof.ChaCha20.AArch64.Stream.Q2 s₀ s := by
  have hT := VG.Proof.ChaCha20.AArch64.Stream.T_eq s₀
  refine ⟨h.x21, by rw [h.x22, h0, Nat.add_zero], by rw [h.x23, hT, h0, Nat.sub_zero], h.keep, h.rd, h.wr,
    by rw [h.mid.state, show VG.Proof.ChaCha20.AArch64.Stream.NB s₀ = 0 by omega, ctr_zero], fun i hi => h.mid.keep _ (by omega), h.mid.saved,
    by rw [h0, Nat.add_zero]; exact h.done, h.frame⟩

theorem Q1.w {s₀ s : State} (hp : VG.Proof.ChaCha20.AArch64.Stream.APre s₀) (h : VG.Proof.ChaCha20.AArch64.Stream.Q1 s₀ s) :
    ∀ d, d + 8 ≤ 768 → InRegions s.wr (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 d) 8 := fun d hd => by
  rw [h.wr]; exact hp.w_st hd

/-- The regions of the call of `vg_chacha20_xor`: the copy of the state,
the data and the working space. -/
abbrev cpR (s₀ : State) : Region := ⟨VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 192, 64⟩
abbrev blR (s₀ : State) : Region := ⟨VG.Proof.ChaCha20.AArch64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.H s₀), 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀⟩
abbrev wkR (s₀ : State) : Region := ⟨VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 256, 320⟩

theorem cpR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.AArch64.Stream.cpR s₀) (VG.Proof.ChaCha20.AArch64.Stream.stR s₀) := Offset.sub_base _ (by omega)
theorem wkR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.AArch64.Stream.wkR s₀) (VG.Proof.ChaCha20.AArch64.Stream.stR s₀) := Offset.sub_base _ (by omega)
theorem blR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.AArch64.Stream.blR s₀) (VG.Proof.ChaCha20.AArch64.Stream.dR s₀) := Offset.sub_base _ (VG.Proof.ChaCha20.AArch64.Stream.HNB_le s₀)

/-- The registers kept are callee-saved, and not the return address. -/
theorem kept_preserved : ∀ r ∈ VG.Proof.ChaCha20.AArch64.Stream.kept, r ∈ preserved ∧ r ≠ .x30 := by decide

theorem blocks_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Stream.APre s₀) {s : State} (h : VG.Proof.ChaCha20.AArch64.Stream.Q1 s₀ s)
    (hnb : 0 < VG.Proof.ChaCha20.AArch64.Stream.NB s₀) : WP isa (.seq (.block blocksArgs) (.call v.callee.name v.callee.code)) s (fun u => VG.Proof.ChaCha20.AArch64.Stream.Q2 s₀ u ∧
      ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) := by
  have hL := VG.Proof.ChaCha20.AArch64.Stream.L_lt s₀
  have hH := VG.Proof.ChaCha20.AArch64.Stream.H_le s₀
  have hHNB := VG.Proof.ChaCha20.AArch64.Stream.HNB_le s₀
  have hT := VG.Proof.ChaCha20.AArch64.Stream.T_eq s₀
  refine WP.seq (WP.mono (WP.preservedV (VG.Proof.ChaCha20.AArch64.Stream.args_exec h.x21 (h.w hp) (by rw [h.rd, hp.rd])) (by lit_decide)) fun s₁ ⟨⟨m₁, x0₁, x1₁, x3₁, x2₁,
    x22₁, x23₁, x21₁, k₁, rd₁, wr₁⟩,v₁⟩ => ?_)
  rw [h.x2, VG.Proof.ChaCha20.AArch64.Stream.shr_eq (by omega)] at m₁
  rw [h.x2] at x2₁
  rw [h.x22] at x1₁
  have hwr₁ : s₁.wr = [VG.Proof.ChaCha20.AArch64.Stream.stR s₀, VG.Proof.ChaCha20.AArch64.Stream.dR s₀] := by rw [wr₁, h.wr, hp.wr]
  have hrd₁ : s₁.rd = [] := by rw [rd₁, h.rd, hp.rd]
  have dSB : (VG.Proof.ChaCha20.AArch64.Stream.cpR s₀).Disjoint (VG.Proof.ChaCha20.AArch64.Stream.wkR s₀) := Offset.disjoint _ (by omega) (by omega) (by omega)
  have dSD : (VG.Proof.ChaCha20.AArch64.Stream.cpR s₀).Disjoint (VG.Proof.ChaCha20.AArch64.Stream.blR s₀) := (hp.st_d.sub_left (VG.Proof.ChaCha20.AArch64.Stream.cpR_sub s₀)).sub_right (VG.Proof.ChaCha20.AArch64.Stream.blR_sub s₀)
  have dDB : (VG.Proof.ChaCha20.AArch64.Stream.blR s₀).Disjoint (VG.Proof.ChaCha20.AArch64.Stream.wkR s₀) := (hp.st_d.sub_left (VG.Proof.ChaCha20.AArch64.Stream.wkR_sub s₀)).symm.sub_left (VG.Proof.ChaCha20.AArch64.Stream.blR_sub s₀)
  have hcov : ∀ r ∈ [VG.Proof.ChaCha20.AArch64.Stream.cpR s₀, VG.Proof.ChaCha20.AArch64.Stream.blR s₀, VG.Proof.ChaCha20.AArch64.Stream.wkR s₀], ∃ r' ∈ [VG.Proof.ChaCha20.AArch64.Stream.stR s₀, VG.Proof.ChaCha20.AArch64.Stream.dR s₀], ∃ o,
      r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.ChaCha20.AArch64.Stream.stR s₀, by simp, 192, rfl, by simp⟩
    · exact ⟨VG.Proof.ChaCha20.AArch64.Stream.dR s₀, by simp, VG.Proof.ChaCha20.AArch64.Stream.H s₀, rfl, hHNB⟩
    · exact ⟨VG.Proof.ChaCha20.AArch64.Stream.stR s₀, by simp, 256, rfl, by simp⟩
  have hwrap : (VG.Proof.ChaCha20.AArch64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.H s₀)).toNat + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀ ≤ 2 ^ 64 := by
    have := hp.wrap_d
    rw [BitVec.toNat_add, toNat_ofNat_lt (by omega)]
    omega
  refine VG.Proof.ChaCha20.AArch64.Stream.xor_call v (S := VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 192) (D := VG.Proof.ChaCha20.AArch64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.H s₀))
    (B := VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 256) (n := 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀) x0₁ x1₁ x2₁ x3₁ (by omega) dSD dSB dDB hwrap
    (by rw [hrd₁, hwr₁, List.nil_append, List.nil_append]; exact Covers.of_sub hcov)
    (by rw [hwr₁]; exact Covers.of_sub hcov) ?_
  intro s₂ k₂ x₂
  refine ⟨?_,fun r hr => (k₂.vec r hr).trans (v₁ r hr)⟩
  have g : ∀ r ∈ preserved, r ≠ .x30 → s₂.gpr r = s₁.gpr r := k₂.cs
  -- Regions the call does not write.
  have nd : ∀ R : Region, R.Disjoint (VG.Proof.ChaCha20.AArch64.Stream.cpR s₀) → R.Disjoint (VG.Proof.ChaCha20.AArch64.Stream.blR s₀) → R.Disjoint (VG.Proof.ChaCha20.AArch64.Stream.wkR s₀) →
      ∀ r ∈ [VG.Proof.ChaCha20.AArch64.Stream.cpR s₀, VG.Proof.ChaCha20.AArch64.Stream.blR s₀, VG.Proof.ChaCha20.AArch64.Stream.wkR s₀], R.Disjoint r := by
    intro R h₁ h₂ h₃ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption
  have nc : ∀ R : Region, R.Disjoint ⟨VG.Proof.ChaCha20.AArch64.Stream.st s₀, 64⟩ → R.Disjoint ⟨VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 192, 64⟩ →
      ∀ r ∈ [⟨VG.Proof.ChaCha20.AArch64.Stream.st s₀, 64⟩, ⟨VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 192, 64⟩], R.Disjoint r := by
    intro R h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption
  have fc := VG.Proof.ChaCha20.AArch64.Stream.copyMem_frame s.mem (VG.Proof.ChaCha20.AArch64.Stream.st s₀) (BitVec.ofNat 32 (VG.Proof.ChaCha20.AArch64.Stream.NB s₀))
  rw [← m₁] at fc
  have stS : Region.Sub ⟨VG.Proof.ChaCha20.AArch64.Stream.st s₀, 64⟩ (VG.Proof.ChaCha20.AArch64.Stream.stR s₀) := VG.Proof.ChaCha20.AArch64.Stream.prefix_sub _ (by omega)
  have bufS : Region.Sub ⟨VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 64, 64⟩ (VG.Proof.ChaCha20.AArch64.Stream.stR s₀) := Offset.sub_base _ (by omega)
  have svS := VG.Proof.ChaCha20.AArch64.Stream.savR_sub s₀
  -- Anything in the state is apart from the data.
  have sd : ∀ R, Region.Sub R (VG.Proof.ChaCha20.AArch64.Stream.stR s₀) → R.Disjoint (VG.Proof.ChaCha20.AArch64.Stream.blR s₀) := fun R hR =>
    (hp.st_d.sub_left hR).sub_right (VG.Proof.ChaCha20.AArch64.Stream.blR_sub s₀)
  have ds : ∀ R R', Region.Sub R (VG.Proof.ChaCha20.AArch64.Stream.dR s₀) → Region.Sub R' (VG.Proof.ChaCha20.AArch64.Stream.stR s₀) → R.Disjoint R' := fun R R' h₁ h₂ =>
    (hp.st_d.symm.sub_left h₁).sub_right h₂
  refine ⟨by rw [g .x21 (by decide) (by decide), x21₁], ?_, ?_, fun r hr => ?_,
    by rw [k₂.rd, rd₁, h.rd], by rw [k₂.wr, wr₁, h.wr], ?_, fun i hi => ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [g .x22 (by decide) (by decide), x22₁, h.x22, h.x2, Offset.add_add]
  · rw [g .x23 (by decide) (by decide), x23₁, h.x23, h.x2, Proof.ChaCha20.AArch64.Xor.sub_ofNat (by omega), hT,
      Nat.sub_sub]
  · rw [g r (VG.Proof.ChaCha20.AArch64.Stream.kept_preserved r hr).1 (VG.Proof.ChaCha20.AArch64.Stream.kept_preserved r hr).2, k₁ r hr]
    exact h.keep r hr
  · rw [Proof.ChaCha20.AArch64.Xor.stateAt_frame k₂.frame (nd _
        (Offset.base_disjoint _ (by omega) (by omega)) (sd _ stS)
        (Offset.base_disjoint _ (by omega) (by omega))),
      m₁, VG.Proof.ChaCha20.AArch64.Stream.copyMem_state, h.mid.state]
    rfl
  · rw [← Offset.add_add, k₂.frame.bytes (R := ⟨VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 64, 64⟩) (nd _
        (Offset.disjoint _ (by omega) (by omega) (by omega)) (sd _ bufS)
        (Offset.disjoint _ (by omega) (by omega) (by omega))) (show 64 ≤ 2 ^ 64 by decide) hi,
      fc.bytes (R := ⟨VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 64, 64⟩) (nc _ (Offset.disjoint_base _ (by omega) (by omega))
        (Offset.disjoint _ (by omega) (by omega) (by omega))) (show 64 ≤ 2 ^ 64 by decide) hi,
      Offset.add_add]
    exact h.mid.keep _ (by omega)
  · refine (h.mid.saved.frame fc (nc _ ?_ ?_)).frame k₂.frame (nd _ ?_ (sd _ svS) ?_)
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · have fcd : s₁.mem (VG.Proof.ChaCha20.AArch64.Stream.dp s₀ + BitVec.ofNat 64 k) = s.mem (VG.Proof.ChaCha20.AArch64.Stream.dp s₀ + BitVec.ofNat 64 k) :=
      fc.bytes (R := VG.Proof.ChaCha20.AArch64.Stream.dR s₀) (nc _ (ds _ _ (fun _ h => h) stS) (ds _ _ (fun _ h => h) (VG.Proof.ChaCha20.AArch64.Stream.cpR_sub s₀)))
        (show VG.Proof.ChaCha20.AArch64.Stream.L s₀ ≤ 2 ^ 64 by omega) hk
    by_cases hk₁ : k < VG.Proof.ChaCha20.AArch64.Stream.H s₀
    · have hpre : Region.Sub ⟨VG.Proof.ChaCha20.AArch64.Stream.dp s₀, VG.Proof.ChaCha20.AArch64.Stream.H s₀⟩ (VG.Proof.ChaCha20.AArch64.Stream.dR s₀) := VG.Proof.ChaCha20.AArch64.Stream.prefix_sub _ hH
      rw [k₂.frame.bytes (R := ⟨VG.Proof.ChaCha20.AArch64.Stream.dp s₀, VG.Proof.ChaCha20.AArch64.Stream.H s₀⟩) (nd _ (ds _ _ hpre (VG.Proof.ChaCha20.AArch64.Stream.cpR_sub s₀))
          (Offset.base_disjoint _ (by omega) (by omega)) (ds _ _ hpre (VG.Proof.ChaCha20.AArch64.Stream.wkR_sub s₀)))
          (show VG.Proof.ChaCha20.AArch64.Stream.H s₀ ≤ 2 ^ 64 by omega) hk₁]
      rw [fcd, h.done k hk, ite_pos hk₁, ite_pos (by omega)]
    by_cases hk₂ : k < VG.Proof.ChaCha20.AArch64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀
    · have e := xor_getD (length_keystream _ _) x₂ (j := k - VG.Proof.ChaCha20.AArch64.Stream.H s₀) (by omega)
      rw [Offset.add_add, show VG.Proof.ChaCha20.AArch64.Stream.H s₀ + (k - VG.Proof.ChaCha20.AArch64.Stream.H s₀) = k by omega, fcd, h.done k hk, ite_neg hk₁, m₁,
        VG.Proof.ChaCha20.AArch64.Stream.copyMem_copy, h.mid.state, keystream_getD _ (by omega)] at e
      rw [e, ite_pos hk₂]
      simp only [VG.Proof.ChaCha20.AArch64.Stream.KS, ite_neg hk₁]
    · have hR : Region.Sub ⟨VG.Proof.ChaCha20.AArch64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀), VG.Proof.ChaCha20.AArch64.Stream.L s₀ - (VG.Proof.ChaCha20.AArch64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀)⟩ (VG.Proof.ChaCha20.AArch64.Stream.dR s₀) :=
        Offset.sub_base _ (by omega)
      have := k₂.frame.bytes (R := ⟨VG.Proof.ChaCha20.AArch64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀), VG.Proof.ChaCha20.AArch64.Stream.L s₀ - (VG.Proof.ChaCha20.AArch64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀)⟩)
        (nd _ (ds _ _ hR (VG.Proof.ChaCha20.AArch64.Stream.cpR_sub s₀)) (Offset.disjoint _ (by omega) (by omega) (by omega))
          (ds _ _ hR (VG.Proof.ChaCha20.AArch64.Stream.wkR_sub s₀))) (show VG.Proof.ChaCha20.AArch64.Stream.L s₀ - (VG.Proof.ChaCha20.AArch64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀) ≤ 2 ^ 64 by omega)
          (i := k - (VG.Proof.ChaCha20.AArch64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀)) (by simp only; omega)
      rw [Offset.add_add, show VG.Proof.ChaCha20.AArch64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀ + (k - (VG.Proof.ChaCha20.AArch64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀)) = k by omega] at this
      rw [this, fcd, h.done k hk, ite_neg hk₁, ite_neg hk₂]
  · refine (h.frame.trans (fc.sub fun r hr => ?_)).trans (k₂.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.ChaCha20.AArch64.Stream.stR s₀, by simp, stS⟩
      · exact ⟨VG.Proof.ChaCha20.AArch64.Stream.stR s₀, by simp, VG.Proof.ChaCha20.AArch64.Stream.cpR_sub s₀⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨VG.Proof.ChaCha20.AArch64.Stream.stR s₀, by simp, VG.Proof.ChaCha20.AArch64.Stream.cpR_sub s₀⟩
      · exact ⟨VG.Proof.ChaCha20.AArch64.Stream.dR s₀, by simp, VG.Proof.ChaCha20.AArch64.Stream.blR_sub s₀⟩
      · exact ⟨VG.Proof.ChaCha20.AArch64.Stream.stR s₀, by simp, VG.Proof.ChaCha20.AArch64.Stream.wkR_sub s₀⟩

theorem part2_withV (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Stream.APre s₀) {s : State} (h : VG.Proof.ChaCha20.AArch64.Stream.Q1 s₀ s) :
    WP isa (part2 v.callee) s (fun u => VG.Proof.ChaCha20.AArch64.Stream.Q2 s₀ u ∧
      ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) := by
  have hL := VG.Proof.ChaCha20.AArch64.Stream.L_lt s₀
  have hHNB := VG.Proof.ChaCha20.AArch64.Stream.HNB_le s₀
  refine WP.ite (decide (64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀ = 0)) (by
      have e : isa.eval (.zero .x .x2) s = some (s.gpr .x2 == 0) := Proof.ChaCha20.AArch64.Xor.eval_zero s .x2
      rw [e, h.x2, Proof.ChaCha20.AArch64.Xor.ofNat_beq_zero (by omega)])
    (fun h0 => WP.block_nil (M := isa) ⟨VG.Proof.ChaCha20.AArch64.Stream.nb_zero_ok h (by simpa using h0),fun _ _ => rfl⟩)
    (fun h0 => VG.Proof.ChaCha20.AArch64.Stream.blocks_ok v hp h (by simp at h0; omega))

theorem part2_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Stream.APre s₀)
    {s : State} (h : VG.Proof.ChaCha20.AArch64.Stream.Q1 s₀ s) : WP isa (part2 v.callee) s (VG.Proof.ChaCha20.AArch64.Stream.Q2 s₀) :=
  (VG.Proof.ChaCha20.AArch64.Stream.part2_withV v hp h).mono fun _ h => h.1

/-! ## The last bytes -/

/-- After `part3`: all the data XORed; the counter advanced past the block
started, if any, which is buffered. -/
structure Q3 (s₀ s : State) : Prop where
  x21 : s.gpr .x21 = VG.Proof.ChaCha20.AArch64.Stream.st s₀
  keep : ∀ r ∈ VG.Proof.ChaCha20.AArch64.Stream.kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : stateAt s.mem (VG.Proof.ChaCha20.AArch64.Stream.st s₀) = ctr (VG.Proof.ChaCha20.AArch64.Stream.S0 s₀) (VG.Proof.ChaCha20.AArch64.Stream.NB s₀ + if VG.Proof.ChaCha20.AArch64.Stream.T s₀ = 0 then 0 else 1)
  buf : ∀ i < 64, s.mem (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 (64 + i)) =
    if VG.Proof.ChaCha20.AArch64.Stream.T s₀ = 0 then s₀.mem (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 (64 + i))
    else (serialize (block (ctr (VG.Proof.ChaCha20.AArch64.Stream.S0 s₀) (VG.Proof.ChaCha20.AArch64.Stream.NB s₀)))).getD i 0
  saved : VG.Proof.ChaCha20.AArch64.Stream.Saved s₀ s.mem
  done : VG.Proof.ChaCha20.AArch64.Stream.Done s₀ (VG.Proof.ChaCha20.AArch64.Stream.L s₀) s.mem
  frame : Frame [VG.Proof.ChaCha20.AArch64.Stream.stR s₀, VG.Proof.ChaCha20.AArch64.Stream.dR s₀] s₀.mem s.mem

theorem t_zero_ok {s₀ : State} {s : State} (h : VG.Proof.ChaCha20.AArch64.Stream.Q2 s₀ s) (h0 : VG.Proof.ChaCha20.AArch64.Stream.T s₀ = 0) : VG.Proof.ChaCha20.AArch64.Stream.Q3 s₀ s := by
  have hT := VG.Proof.ChaCha20.AArch64.Stream.T_eq s₀
  have hHNB := VG.Proof.ChaCha20.AArch64.Stream.HNB_le s₀
  refine ⟨h.x21, h.keep, h.rd, h.wr, by rw [h.state, h0]; rfl, fun i hi => by rw [h.buf i hi, h0]; rfl, h.saved,
    by rw [show VG.Proof.ChaCha20.AArch64.Stream.L s₀ = VG.Proof.ChaCha20.AArch64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀ by omega]; exact h.done, h.frame⟩

/-- The buffered block, and the bytes the block function may write. -/
abbrev bufR (s₀ : State) : Region := ⟨VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 64, 256⟩

theorem bufR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.AArch64.Stream.bufR s₀) (VG.Proof.ChaCha20.AArch64.Stream.stR s₀) := Offset.sub_base _ (by omega)

/-- The counter advanced, and the arguments of `xorBytes` for the buffered
block. -/
theorem ctr_exec {s : State} {p : Addr} (hx21 : s.gpr .x21 = p) (hw : InRegions s.wr (p + BitVec.ofNat 64 48) 4)
    (hr : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 48) 4) :
    WP isa (.block [.ldr .w .x9 .x21 48, .addImm .w .x9 .x9 1, .str .w .x9 .x21 48, .addImm .x .x1 .x21 64,
      mov .x2 .x23]) s fun s' =>
      s'.mem = s.mem.writeW (p + BitVec.ofNat 64 48) (s.mem.readW (p + BitVec.ofNat 64 48) 32 + 1) ∧
      s'.gpr .x1 = p + BitVec.ofNat 64 64 ∧ s'.gpr .x2 = s.gpr .x23 ∧
      (∀ r, r ≠ .x9 → r ≠ .x1 → r ≠ .x2 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine wp_ldr32 (a := p + BitVec.ofNat 64 48) (by decide) (by rw [hx21]) hr fun s₁ u₁ => ?_
  refine wp_addImm32 (by decide) fun s₂ u₂ => ?_
  refine wp_str32 (a := p + BitVec.ofNat 64 48) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hx21]) (by rw [u₂.wr, u₁.wr]; exact hw)
    fun s₃ g₃ => ?_
  refine wp_addImm (by decide) fun s₄ u₄ => wp_mov fun s₅ u₅ => WP.block_nil ?_
  have e : ∀ v : BitVec 32, BitVec.setWidth 32 (BitVec.setWidth 64 v) = v := fun v =>
    BitVec.setWidth_setWidth_of_le _ (by decide)
  refine ⟨?_, ?_, ?_, fun r h₁ h₂ h₃ => ?_, ?_, ?_⟩
  · rw [u₅.mem, u₄.mem, g₃.mem, u₂.gpr, u₁.gpr, e, e, u₂.mem, u₁.mem, show (1#32 : BitVec 32) = 1 from rfl]
  · rw [u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hx21]
  · rw [u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₅.other r h₃, u₄.other r h₂, g₃.gpr, u₂.other r h₁, u₁.other r h₁]
  · rw [u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr]

theorem tail_ok {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Stream.APre s₀) {s : State} (h : VG.Proof.ChaCha20.AArch64.Stream.Q2 s₀ s) (ht : VG.Proof.ChaCha20.AArch64.Stream.T s₀ ≠ 0) :
    WP isa (.seq (.block tailArgs) (.seq (.call "vg_chacha20_block" Impl.ChaCha20.AArch64.block) tailXor))
      s (VG.Proof.ChaCha20.AArch64.Stream.Q3 s₀) := by
  have hT := VG.Proof.ChaCha20.AArch64.Stream.T_eq s₀
  have hHNB := VG.Proof.ChaCha20.AArch64.Stream.HNB_le s₀
  have hL := VG.Proof.ChaCha20.AArch64.Stream.L_lt s₀
  have h₁ : WP isa (.block tailArgs) s fun s₁ => s₁.gpr .x0 = VG.Proof.ChaCha20.AArch64.Stream.st s₀ ∧
      s₁.gpr .x1 = VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 64 ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine Proof.ChaCha20.AArch64.Xor.wp_mov fun s' u => Proof.ChaCha20.AArch64.Xor.wp_addImm (by decide)
      fun s'' u' => WP.block_nil ?_
    exact ⟨by rw [u'.other _ (by decide), u.gpr, h.x21], by rw [u'.gpr, u.other _ (by decide), h.x21],
      fun r h₁ h₂ => by rw [u'.other r h₂, u.other r h₁], by rw [u'.mem, u.mem], by rw [u'.rd, u.rd],
      by rw [u'.wr, u.wr]⟩
  refine WP.seq (WP.mono h₁ fun s₁ ⟨x0₁, x1₁, k₁, m₁, rd₁, wr₁⟩ => ?_)
  have hwr₁ : s₁.wr = [VG.Proof.ChaCha20.AArch64.Stream.stR s₀, VG.Proof.ChaCha20.AArch64.Stream.dR s₀] := by rw [wr₁, h.wr, hp.wr]
  have hrd₁ : s₁.rd = [] := by rw [rd₁, h.rd, hp.rd]
  have stS : Region.Sub ⟨VG.Proof.ChaCha20.AArch64.Stream.st s₀, 64⟩ (VG.Proof.ChaCha20.AArch64.Stream.stR s₀) := VG.Proof.ChaCha20.AArch64.Stream.prefix_sub _ (by omega)
  refine WP.seq (VG.Proof.ChaCha20.AArch64.Stream.block_call x0₁ x1₁ (Offset.disjoint_base _ (by omega) (by omega))
    (by
      rw [hrd₁, hwr₁]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.ChaCha20.AArch64.Stream.stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 768 by decide⟩
      · exact ⟨VG.Proof.ChaCha20.AArch64.Stream.stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩)
    (by
      rw [hwr₁]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.ChaCha20.AArch64.Stream.stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩) fun s₂ k₂ blk₂ => ?_)
  have g : ∀ r ∈ [Reg.x21, .x22, .x23, .x19, .x20, .x24, .x25, .x26, .x27, .x28], s₂.gpr r = s.gpr r :=
    fun r hr => by
      have hp' : r ∈ preserved ∧ r ≠ .x30 ∧ r ≠ .x0 ∧ r ≠ .x1 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [k₂.cs r hp'.1 hp'.2.1, k₁ r hp'.2.2.1 hp'.2.2.2]
  have hw48 : InRegions s₂.wr (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 48) 4 := by
    rw [k₂.wr, hwr₁]; exact ⟨VG.Proof.ChaCha20.AArch64.Stream.stR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hr48 : InRegions (s₂.rd ++ s₂.wr) (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 48) 4 := by
    rw [k₂.rd, hrd₁, List.nil_append]; exact hw48
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.AArch64.Stream.ctr_exec (by rw [g .x21 (by simp), h.x21]) hw48 hr48)
    fun s₃ ⟨m₃, x1₃, x2₃, k₃, rd₃, wr₃⟩ => ?_)
  have hT64 : VG.Proof.ChaCha20.AArch64.Stream.T s₀ < 64 := Nat.mod_lt _ (by decide)
  have hx22₃ : s₃.gpr .x22 = VG.Proof.ChaCha20.AArch64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀) := by
    rw [k₃ .x22 (by decide) (by decide) (by decide), g .x22 (by simp), h.x22]
  have dS : ∀ R R', Region.Sub R (VG.Proof.ChaCha20.AArch64.Stream.dR s₀) → Region.Sub R' (VG.Proof.ChaCha20.AArch64.Stream.stR s₀) → R.Disjoint R' := fun R R' h₁ h₂ =>
    (hp.st_d.symm.sub_left h₁).sub_right h₂
  have hb : VG.Proof.ChaCha20.AArch64.Stream.BPre s₃ (VG.Proof.ChaCha20.AArch64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀)) (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 64) (VG.Proof.ChaCha20.AArch64.Stream.T s₀) :=
    ⟨hx22₃, x1₃, by rw [x2₃, g .x23 (by simp), h.x23], by omega,
      fun k hk => by
        rw [wr₃, k₂.wr, hwr₁, Offset.add_add]
        exact ⟨VG.Proof.ChaCha20.AArch64.Stream.dR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩,
      fun k hk => by
        rw [rd₃, wr₃, k₂.rd, k₂.wr, hrd₁, hwr₁, List.nil_append, Offset.add_add]
        exact ⟨VG.Proof.ChaCha20.AArch64.Stream.stR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩,
      fun j hj k hk => by rw [Offset.add_add, Offset.add_add]; exact VG.Proof.ChaCha20.AArch64.Stream.d_ne_st hp (by omega) (by omega)⟩
  refine WP.mono (VG.Proof.ChaCha20.AArch64.Stream.xorBytes_ok hb) fun s₄ h₄ => ?_
  have f₂ := k₂.frame
  have f₃ : Frame [⟨VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 48, 4⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have tR : Region.Sub ⟨VG.Proof.ChaCha20.AArch64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀), VG.Proof.ChaCha20.AArch64.Stream.T s₀⟩ (VG.Proof.ChaCha20.AArch64.Stream.dR s₀) :=
    Offset.sub_base _ (by omega)
  have c48 : Region.Sub ⟨VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 48, 4⟩ (VG.Proof.ChaCha20.AArch64.Stream.stR s₀) := Offset.sub_base _ (by omega)
  have st₂ : stateAt s₂.mem (VG.Proof.ChaCha20.AArch64.Stream.st s₀) = ctr (VG.Proof.ChaCha20.AArch64.Stream.S0 s₀) (VG.Proof.ChaCha20.AArch64.Stream.NB s₀) := by
    rw [Proof.ChaCha20.AArch64.Xor.stateAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by omega) (by omega)),
      m₁, h.state]
  have bb : ∀ i < 64, s₂.mem (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 (64 + i)) =
      (serialize (block (ctr (VG.Proof.ChaCha20.AArch64.Stream.S0 s₀) (VG.Proof.ChaCha20.AArch64.Stream.NB s₀)))).getD i 0 := by
    intro i hi
    rw [← Offset.add_add, ← serialize_stateAt s₂.mem _ hi, blk₂, m₁, h.state]
  have b3 : ∀ i < 64, s₃.mem (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 (64 + i)) = s₂.mem (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 (64 + i)) := by
    intro i hi
    rw [m₃]; exact byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega)
  have b4 : ∀ i < 64, s₄.mem (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 (64 + i)) = s₃.mem (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 (64 + i)) := by
    intro i hi
    rw [← Offset.add_add]
    exact h₄.frame.bytes (R := ⟨VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 64, 64⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dS _ _ tR (Offset.sub_base _ (by omega))).symm) (show 64 ≤ 2 ^ 64 by decide) hi
  refine ⟨?_, fun r hr => ?_, by rw [h₄.rd, rd₃, k₂.rd, rd₁, h.rd], by rw [h₄.wr, wr₃, k₂.wr, wr₁, h.wr], ?_,
    fun i hi => ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [h₄.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k₃ .x21 (by decide) (by decide) (by decide), g .x21 (by simp), h.x21]
  · rw [h₄.keep r (VG.Proof.ChaCha20.AArch64.Stream.kept_ne hr) (VG.Proof.ChaCha20.AArch64.Stream.kept_ne hr) (VG.Proof.ChaCha20.AArch64.Stream.kept_ne hr) (VG.Proof.ChaCha20.AArch64.Stream.kept_ne hr) (VG.Proof.ChaCha20.AArch64.Stream.kept_ne hr) (VG.Proof.ChaCha20.AArch64.Stream.kept_ne hr),
      k₃ r (VG.Proof.ChaCha20.AArch64.Stream.kept_ne hr) (VG.Proof.ChaCha20.AArch64.Stream.kept_ne hr) (VG.Proof.ChaCha20.AArch64.Stream.kept_ne hr),
      g r (by simp only [VG.Proof.ChaCha20.AArch64.Stream.kept, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
              rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)]
    exact h.keep r hr
  · have e12 : s₂.mem.readW (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 48) 32 = (ctr (VG.Proof.ChaCha20.AArch64.Stream.S0 s₀) (VG.Proof.ChaCha20.AArch64.Stream.NB s₀))[12] := by
      rw [← st₂]; simp [stateAt]
    rw [Proof.ChaCha20.AArch64.Xor.stateAt_frame h₄.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dS _ _ tR stS).symm),
      m₃, Proof.ChaCha20.AArch64.Xor.stateAt_writeW_counter, st₂, e12, ctr_succ, ite_neg ht]
  · rw [b4 i hi, b3 i hi, bb i hi, ite_neg ht]
  · have svS := VG.Proof.ChaCha20.AArch64.Stream.savR_sub s₀
    rw [m₁] at f₂
    refine ((h.saved.frame f₂ fun r hr => ?_).frame f₃ fun r hr => ?_).frame h₄.frame fun r hr => ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact (dS _ _ tR svS).symm
  · have dS48 : (VG.Proof.ChaCha20.AArch64.Stream.dR s₀).Disjoint ⟨VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 48, 4⟩ := dS _ _ (fun _ h => h) c48
    have back : s₃.mem (VG.Proof.ChaCha20.AArch64.Stream.dp s₀ + BitVec.ofNat 64 k) = s.mem (VG.Proof.ChaCha20.AArch64.Stream.dp s₀ + BitVec.ofNat 64 k) := by
      rw [f₃.bytes (R := VG.Proof.ChaCha20.AArch64.Stream.dR s₀) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dS48)
          (show VG.Proof.ChaCha20.AArch64.Stream.L s₀ ≤ 2 ^ 64 by omega) hk,
        f₂.bytes (R := VG.Proof.ChaCha20.AArch64.Stream.dR s₀) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact dS _ _ (fun _ h => h) (VG.Proof.ChaCha20.AArch64.Stream.bufR_sub s₀)) (show VG.Proof.ChaCha20.AArch64.Stream.L s₀ ≤ 2 ^ 64 by omega) hk, m₁]
    by_cases hk₁ : k < VG.Proof.ChaCha20.AArch64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀
    · rw [h₄.frame.bytes (R := ⟨VG.Proof.ChaCha20.AArch64.Stream.dp s₀, VG.Proof.ChaCha20.AArch64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint _ (by omega) (by omega)) (show VG.Proof.ChaCha20.AArch64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀ ≤ 2 ^ 64 by omega) hk₁,
        back, h.done k hk, ite_pos hk₁, ite_pos hk]
    · have e := h₄.data (k - (VG.Proof.ChaCha20.AArch64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀)) (by omega)
      rw [Offset.add_add, Offset.add_add, show VG.Proof.ChaCha20.AArch64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀ + (k - (VG.Proof.ChaCha20.AArch64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀)) = k by omega,
        back, b3 _ (by omega), bb _ (by omega), h.done k hk, ite_neg hk₁] at e
      rw [e, ite_pos hk]
      simp only [VG.Proof.ChaCha20.AArch64.Stream.KS, ite_neg (show ¬ k < VG.Proof.ChaCha20.AArch64.Stream.H s₀ by omega)]
      rw [show (k - VG.Proof.ChaCha20.AArch64.Stream.H s₀) / 64 = VG.Proof.ChaCha20.AArch64.Stream.NB s₀ by omega, show (k - VG.Proof.ChaCha20.AArch64.Stream.H s₀) % 64 = k - (VG.Proof.ChaCha20.AArch64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀) by omega]
  · rw [m₁] at f₂
    refine ((h.frame.trans (f₂.sub fun r hr => ?_)).trans (f₃.sub fun r hr => ?_)).trans
      (h₄.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.ChaCha20.AArch64.Stream.stR s₀, by simp, VG.Proof.ChaCha20.AArch64.Stream.bufR_sub s₀⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.ChaCha20.AArch64.Stream.stR s₀, by simp, c48⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.ChaCha20.AArch64.Stream.dR s₀, by simp, tR⟩

theorem part3_ok {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Stream.APre s₀) {s : State} (h : VG.Proof.ChaCha20.AArch64.Stream.Q2 s₀ s) : WP isa part3 s (VG.Proof.ChaCha20.AArch64.Stream.Q3 s₀) := by
  have hT64 : VG.Proof.ChaCha20.AArch64.Stream.T s₀ < 64 := Nat.mod_lt _ (by decide)
  refine WP.ite (decide (VG.Proof.ChaCha20.AArch64.Stream.T s₀ = 0)) (by
      have e : isa.eval (.zero .x .x23) s = some (s.gpr .x23 == 0) := Proof.ChaCha20.AArch64.Xor.eval_zero s .x23
      rw [e, h.x23, Proof.ChaCha20.AArch64.Xor.ofNat_beq_zero (by omega)])
    (fun h0 => WP.block_nil (M := isa) (VG.Proof.ChaCha20.AArch64.Stream.t_zero_ok h (by simpa using h0)))
    (fun h0 => VG.Proof.ChaCha20.AArch64.Stream.tail_ok hp h (by simpa using h0))

/-! ## The end -/

theorem finish_ok {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Stream.APre s₀) (hle : VG.Proof.ChaCha20.AArch64.Stream.L s₀ ≤ VG.Proof.ChaCha20.AArch64.Stream.N s₀) {s : State} (h : VG.Proof.ChaCha20.AArch64.Stream.Q3 s₀ s) :
    WP isa (.block finish) s (VG.Proof.ChaCha20.AArch64.Stream.Final s₀) := by
  have hL := VG.Proof.ChaCha20.AArch64.Stream.L_lt s₀
  have hN := VG.Proof.ChaCha20.AArch64.Stream.N_lt s₀
  have w : ∀ d, d + 8 ≤ 768 → InRegions s.wr (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [h.wr]; exact hp.w_st hd
  have r : ∀ d, d + 8 ≤ 768 → InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [h.rd, hp.rd, List.nil_append]; exact w d hd
  refine wp_ldr (a := VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 608) ⟨by decide, by decide⟩ (by rw [h.x21]) (r 608 (by decide))
    fun s₁ u₁ => ?_
  refine wp_str (a := VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 128) ⟨by decide, by decide⟩ (by rw [u₁.other _ (by decide), h.x21])
    (by rw [u₁.wr]; exact w 128 (by decide)) fun s₂ g₂ => ?_
  have rr : ∀ d, d + 8 ≤ 768 → InRegions (s₂.rd ++ s₂.wr) (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [g₂.rd, g₂.wr, u₁.rd, u₁.wr]; exact r d hd
  have x21₂ : s₂.gpr .x21 = VG.Proof.ChaCha20.AArch64.Stream.st s₀ := by rw [g₂.gpr, u₁.other _ (by decide), h.x21]
  refine wp_ldr (a := VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 600) ⟨by decide, by decide⟩ (by rw [x21₂]) (rr 600 (by decide))
    fun s₃ u₃ => ?_
  refine wp_ldr (a := VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 584) ⟨by decide, by decide⟩ (by rw [u₃.other _ (by decide), x21₂])
    (by rw [u₃.rd, u₃.wr]; exact rr 584 (by decide)) fun s₄ u₄ => ?_
  refine wp_ldr (a := VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 592) ⟨by decide, by decide⟩
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), x21₂])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact rr 592 (by decide)) fun s₅ u₅ => ?_
  refine wp_ldr (a := VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 576) ⟨by decide, by decide⟩
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), x21₂])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact rr 576 (by decide)) fun s₆ u₆ => ?_
  refine wp_movz fun s₇ u₇ => WP.block_nil ?_
  -- The memory, from the bytes left stored.
  have hm₂ : s₂.mem = s.mem.writeW (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.N s₀ - VG.Proof.ChaCha20.AArch64.Stream.L s₀)) := by
    rw [g₂.mem, u₁.gpr, u₁.mem, h.saved.left]
  have hm : s₇.mem = s.mem.writeW (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.N s₀ - VG.Proof.ChaCha20.AArch64.Stream.L s₀)) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂]
  have sv : ∀ d, 576 ≤ d → d + 8 ≤ 616 →
      (s.mem.writeW (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.N s₀ - VG.Proof.ChaCha20.AArch64.Stream.L s₀))).readW
        (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 d) 64 = s.mem.readW (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => VG.Proof.ChaCha20.AArch64.Stream.readW64_ofNat _ _ _ (by omega) (by omega) (by omega)
  have g : ∀ r, r ≠ .x0 → r ≠ .x9 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x30 → s₇.gpr r = s.gpr r :=
    fun r h₀ h₉ h₂₁ h₂₂ h₂₃ h₃₀ => by
      rw [u₇.other r h₀, u₆.other r h₂₁, u₅.other r h₂₃, u₄.other r h₂₂, u₃.other r h₃₀, g₂.gpr, u₁.other r h₉]
  have hfw : Frame [⟨VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 128, 8⟩] s.mem
      (s.mem.writeW (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.N s₀ - VG.Proof.ChaCha20.AArch64.Stream.L s₀))) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have c128 : Region.Sub ⟨VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 128, 8⟩ (VG.Proof.ChaCha20.AArch64.Stream.stR s₀) := Offset.sub_base _ (by omega)
  have hS : stateAt (s.mem.writeW (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.N s₀ - VG.Proof.ChaCha20.AArch64.Stream.L s₀))) (VG.Proof.ChaCha20.AArch64.Stream.st s₀) =
      ctr (VG.Proof.ChaCha20.AArch64.Stream.S0 s₀) (VG.Proof.ChaCha20.AArch64.Stream.NB s₀ + if VG.Proof.ChaCha20.AArch64.Stream.T s₀ = 0 then 0 else 1) := by
    rw [Proof.ChaCha20.AArch64.Xor.stateAt_frame hfw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint _ (by omega) (by omega)), h.state]
  refine ⟨fun r hr => ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h.keep _ (by decide)
    · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h.keep _ (by decide)
    · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem, u₃.mem, hm₂, sv 576 (by decide) (by decide)]
      exact h.saved.x21
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, hm₂,
        sv 584 (by decide) (by decide)]
      exact h.saved.x22
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, hm₂,
        sv 592 (by decide) (by decide)]
      exact h.saved.x23
    · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h.keep _ (by decide)
    · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h.keep _ (by decide)
    · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h.keep _ (by decide)
    · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h.keep _ (by decide)
    · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h.keep _ (by decide)
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.gpr, hm₂, sv 600 (by decide) (by decide)]
      exact h.saved.x30
  · have hd : ∀ k < VG.Proof.ChaCha20.AArch64.Stream.L s₀, (s.mem.writeW (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.N s₀ - VG.Proof.ChaCha20.AArch64.Stream.L s₀)))
        (VG.Proof.ChaCha20.AArch64.Stream.dp s₀ + BitVec.ofNat 64 k) = s.mem (VG.Proof.ChaCha20.AArch64.Stream.dp s₀ + BitVec.ofNat 64 k) := fun k hk =>
      hfw.bytes (R := VG.Proof.ChaCha20.AArch64.Stream.dR s₀) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.st_d.symm.sub_right c128)) (show VG.Proof.ChaCha20.AArch64.Stream.L s₀ ≤ 2 ^ 64 by omega) hk
    show keyAt _ _ = _ ∧ _
    rw [hm]
    refine ⟨Proof.ChaCha20.keyAt_of_ctr hS, ?_⟩
    rw [ite_pos hle]
    refine ⟨by rw [u₇.gpr]; decide, apply_data hle fun k hk => ?_, apply_rest hle ?_ hS fun i hi => ?_⟩
    · rw [hd k hk, h.done k hk, ite_pos hk]
    · simp only [leftAt]
      rw [show (VG.Proof.ChaCha20.AArch64.Stream.st s₀ + 128 : Addr) = VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 128 from rfl, Mem.readW_writeW_self64,
        toNat_ofNat_lt (by omega)]
    · rw [byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), h.buf i hi]

theorem apply_eq (x : Impl.ChaCha20.AArch64.XorCallee) : apply x = .seq (.block check)
    (.ite (.zero .x .x11) (.block [.movz .x .x0 0 0]) (.seq part1 (.seq (part2 x) (.seq part3 (.block finish))))) :=
  rfl

theorem apply_correct (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Stream.APre s₀) :
    WP isa (apply v.callee) s₀ (fun u => VG.Proof.ChaCha20.AArch64.Stream.Final s₀ u ∧
      ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64) := by
  rw [VG.Proof.ChaCha20.AArch64.Stream.apply_eq]
  refine WP.seq (WP.mono (WP.preservedV (VG.Proof.ChaCha20.AArch64.Stream.check_ok hp) (by lit_decide)) fun s ⟨h,v₀⟩ => ?_)
  refine WP.ite (decide (VG.Proof.ChaCha20.AArch64.Stream.N s₀ < VG.Proof.ChaCha20.AArch64.Stream.L s₀)) (by
      have e : isa.eval (.zero .x .x11) s = some (s.gpr .x11 == 0) := Proof.ChaCha20.AArch64.Xor.eval_zero s .x11
      rw [e, h.x11]; by_cases hh : VG.Proof.ChaCha20.AArch64.Stream.L s₀ ≤ VG.Proof.ChaCha20.AArch64.Stream.N s₀ <;> simp [hh] <;> omega)
    (fun hlt => (WP.preservedV (VG.Proof.ChaCha20.AArch64.Stream.fail_ok (by simpa using hlt) h) (by lit_decide)).mono
      fun u ⟨hu,vu⟩ => ⟨hu,fun r hr => (vu r hr).trans (v₀ r hr)⟩) (fun hge => ?_)
  have hle : VG.Proof.ChaCha20.AArch64.Stream.L s₀ ≤ VG.Proof.ChaCha20.AArch64.Stream.N s₀ := by simp at hge; omega
  refine WP.seq (WP.mono (WP.preservedV (VG.Proof.ChaCha20.AArch64.Stream.part1_ok hp hle h) (by lit_decide)) fun s₁ ⟨h₁,v₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.AArch64.Stream.part2_withV v hp h₁) fun s₂ ⟨h₂,v₂⟩ => ?_)
  refine WP.seq (WP.mono (WP.preservedV (VG.Proof.ChaCha20.AArch64.Stream.part3_ok hp h₂) (by lit_decide)) fun s₃ ⟨h₃,v₃⟩ => ?_)
  exact (WP.preservedV (VG.Proof.ChaCha20.AArch64.Stream.finish_ok hp hle h₃) (by lit_decide)).mono fun u ⟨hu,vu⟩ =>
    ⟨hu,fun r hr => (((vu r hr).trans (v₃ r hr)).trans (v₂ r hr)).trans
      ((v₁ r hr).trans (v₀ r hr))⟩

end VG.Proof.ChaCha20.AArch64.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Stream.ApplyCT`. -/
section

/-!
# Streaming ChaCha20 on AArch64: `apply`, constant time

Untrusted: everything here is checked by Lean. Two runs from states that
agree on the pointers, the length, the stack pointer and the number of bytes
of keystream left (which the contract lets `apply` leak) are related piece by
piece (`RelCT`): the taint analysis proves each piece without calls constant
time from the registers that hold public values (`taintRegs`), which
correctness determines in each run (`Apply.lean`) from those public values;
the calls of the block function and of the implementation `v` of
`vg_chacha20_xor` are constant time by their own proofs (`RelCT.call`), their
arguments agreeing; and the branches are on public values (`RelCT.ite`).
-/

namespace VG.Proof.ChaCha20.AArch64.Stream

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Stream
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (wp_addImm wp_mov eval_zero ofNat_beq_zero)

/-- Code the taint analysis proves constant time from the registers `rs`
(and the stack pointer). -/
theorem taintRegs {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun x y hp => ⟨(hr x y hp).1, fun r h' => (hr x y hp).2 r (Taint.mem_ofRegs.mp h')⟩) h

/-- What each run satisfies by correctness holds of the final states. -/
theorem RelCT.post {P : State → State → Prop} {c : Prog isa} {F₁ F₂ : State → Prop}
    (h : RelCT isa P c fun _ _ => True) (hw : ∀ x y, P x y → WP isa c x F₁ ∧ WP isa c y F₂) :
    RelCT isa P c fun x y => F₁ x ∧ F₂ y :=
  RelCT.mono (RelCT.wp h hw) (fun _ _ h => h) fun _ _ h => h.2

/-- `F` of the entry state `a`, with the stack pointer of `a`. -/
abbrev Sp (F : State → State → Prop) (a x : State) : Prop := F a x ∧ x.sp = a.sp

/-- Code keeps the stack pointer. -/
theorem wp_sp {c : Prog isa} {s a : State} {F : State → State → Prop} (h : WP isa c s (F a))
    (hs : s.sp = a.sp) : WP isa c s (VG.Proof.ChaCha20.AArch64.Stream.Sp F a) := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, (Exec.sp he).trans hs⟩

/-- Two entry states that agree on what is public. -/
structure Two (a b : State) : Prop where
  pa : VG.Proof.ChaCha20.AArch64.Stream.APre a
  pb : VG.Proof.ChaCha20.AArch64.Stream.APre b
  hst : VG.Proof.ChaCha20.AArch64.Stream.st a = VG.Proof.ChaCha20.AArch64.Stream.st b
  hdp : VG.Proof.ChaCha20.AArch64.Stream.dp a = VG.Proof.ChaCha20.AArch64.Stream.dp b
  hx2 : a.gpr .x2 = b.gpr .x2
  hsp : a.sp = b.sp
  hleft : VG.Proof.ChaCha20.AArch64.Stream.N a = VG.Proof.ChaCha20.AArch64.Stream.N b

theorem Two.eqL {a b : State} (h : VG.Proof.ChaCha20.AArch64.Stream.Two a b) : VG.Proof.ChaCha20.AArch64.Stream.L a = VG.Proof.ChaCha20.AArch64.Stream.L b := by
  show (a.gpr .x2).toNat = (b.gpr .x2).toNat; rw [h.hx2]
theorem Two.eqO {a b : State} (h : VG.Proof.ChaCha20.AArch64.Stream.Two a b) : VG.Proof.ChaCha20.AArch64.Stream.O a = VG.Proof.ChaCha20.AArch64.Stream.O b := by
  show VG.Proof.ChaCha20.AArch64.Stream.N a % 64 = VG.Proof.ChaCha20.AArch64.Stream.N b % 64; rw [h.hleft]
theorem Two.eqH {a b : State} (h : VG.Proof.ChaCha20.AArch64.Stream.Two a b) : VG.Proof.ChaCha20.AArch64.Stream.H a = VG.Proof.ChaCha20.AArch64.Stream.H b := by
  show min (VG.Proof.ChaCha20.AArch64.Stream.N a % 64) (VG.Proof.ChaCha20.AArch64.Stream.L a) = min (VG.Proof.ChaCha20.AArch64.Stream.N b % 64) (VG.Proof.ChaCha20.AArch64.Stream.L b); rw [h.hleft, h.eqL]
theorem Two.eqNB {a b : State} (h : VG.Proof.ChaCha20.AArch64.Stream.Two a b) : VG.Proof.ChaCha20.AArch64.Stream.NB a = VG.Proof.ChaCha20.AArch64.Stream.NB b := by
  show (VG.Proof.ChaCha20.AArch64.Stream.L a - VG.Proof.ChaCha20.AArch64.Stream.H a) / 64 = (VG.Proof.ChaCha20.AArch64.Stream.L b - VG.Proof.ChaCha20.AArch64.Stream.H b) / 64; rw [h.eqH, h.eqL]
theorem Two.eqT {a b : State} (h : VG.Proof.ChaCha20.AArch64.Stream.Two a b) : VG.Proof.ChaCha20.AArch64.Stream.T a = VG.Proof.ChaCha20.AArch64.Stream.T b := by
  show (VG.Proof.ChaCha20.AArch64.Stream.L a - VG.Proof.ChaCha20.AArch64.Stream.H a) % 64 = (VG.Proof.ChaCha20.AArch64.Stream.L b - VG.Proof.ChaCha20.AArch64.Stream.H b) % 64; rw [h.eqH, h.eqL]

/-! ## The call of `vg_chacha20_xor` -/

/-- The arguments of the call of `vg_chacha20_xor`. -/
structure Args (s₀ s : State) : Prop where
  x0 : s.gpr .x0 = VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 192
  x1 : s.gpr .x1 = VG.Proof.ChaCha20.AArch64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.H s₀)
  x2 : s.gpr .x2 = BitVec.ofNat 64 (64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀)
  x3 : s.gpr .x3 = VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 256
  rd : s.rd = []
  wr : s.wr = [VG.Proof.ChaCha20.AArch64.Stream.stR s₀, VG.Proof.ChaCha20.AArch64.Stream.dR s₀]

theorem args_ok {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Stream.APre s₀) {s : State} (h : VG.Proof.ChaCha20.AArch64.Stream.Q1 s₀ s) :
    WP isa (.block blocksArgs) s (VG.Proof.ChaCha20.AArch64.Stream.Args s₀) :=
  WP.mono (VG.Proof.ChaCha20.AArch64.Stream.args_exec h.x21 (h.w hp) (by rw [h.rd, hp.rd])) fun _ ⟨_, x0₁, x1₁, x3₁, x2₁, _, _, _, _, rd₁, wr₁⟩ =>
    ⟨x0₁, by rw [x1₁, h.x22], by rw [x2₁, h.x2], x3₁, by rw [rd₁, h.rd, hp.rd], by rw [wr₁, h.wr, hp.wr]⟩

theorem Args.covers {s₀ s : State} (h : VG.Proof.ChaCha20.AArch64.Stream.Args s₀ s) :
    Covers ([] ++ [VG.Proof.ChaCha20.AArch64.Stream.cpR s₀, VG.Proof.ChaCha20.AArch64.Stream.blR s₀, VG.Proof.ChaCha20.AArch64.Stream.wkR s₀]) (s.rd ++ s.wr) ∧ Covers [VG.Proof.ChaCha20.AArch64.Stream.cpR s₀, VG.Proof.ChaCha20.AArch64.Stream.blR s₀, VG.Proof.ChaCha20.AArch64.Stream.wkR s₀] s.wr := by
  have hcov : ∀ r ∈ [VG.Proof.ChaCha20.AArch64.Stream.cpR s₀, VG.Proof.ChaCha20.AArch64.Stream.blR s₀, VG.Proof.ChaCha20.AArch64.Stream.wkR s₀], ∃ r' ∈ [VG.Proof.ChaCha20.AArch64.Stream.stR s₀, VG.Proof.ChaCha20.AArch64.Stream.dR s₀], ∃ o,
      r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.ChaCha20.AArch64.Stream.stR s₀, by simp, 192, rfl, by simp⟩
    · exact ⟨VG.Proof.ChaCha20.AArch64.Stream.dR s₀, by simp, VG.Proof.ChaCha20.AArch64.Stream.H s₀, rfl, VG.Proof.ChaCha20.AArch64.Stream.HNB_le s₀⟩
    · exact ⟨VG.Proof.ChaCha20.AArch64.Stream.stR s₀, by simp, 256, rfl, by simp⟩
  exact ⟨by rw [h.rd, h.wr, List.nil_append, List.nil_append]; exact Covers.of_sub hcov,
    by rw [h.wr]; exact Covers.of_sub hcov⟩

theorem Args.pre {s₀ s : State} (hp : VG.Proof.ChaCha20.AArch64.Stream.APre s₀) (h : VG.Proof.ChaCha20.AArch64.Stream.Args s₀ s) :
    Proof.ChaCha20.xorAArch64.pre (s.callEntry.withRegions [] [VG.Proof.ChaCha20.AArch64.Stream.cpR s₀, VG.Proof.ChaCha20.AArch64.Stream.blR s₀, VG.Proof.ChaCha20.AArch64.Stream.wkR s₀]) := by
  have hL := VG.Proof.ChaCha20.AArch64.Stream.L_lt s₀
  have hH := VG.Proof.ChaCha20.AArch64.Stream.H_le s₀
  have hHNB := VG.Proof.ChaCha20.AArch64.Stream.HNB_le s₀
  have hwrap : (VG.Proof.ChaCha20.AArch64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.H s₀)).toNat + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀ ≤ 2 ^ 64 := by
    have := hp.wrap_d
    rw [BitVec.toNat_add, Proof.ChaCha20.AArch64.toNat_ofNat_lt (by omega)]
    omega
  have hn : (BitVec.ofNat 64 (64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀)).toNat = 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀ := Proof.ChaCha20.AArch64.toNat_ofNat_lt (by omega)
  simp only [Proof.ChaCha20.xorAArch64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' s (by decide : Reg.x0 ∉ linkRegs),
    VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' s (by decide : Reg.x1 ∉ linkRegs), VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' s (by decide : Reg.x2 ∉ linkRegs),
    VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' s (by decide : Reg.x3 ∉ linkRegs), h.x0, h.x1, h.x2, h.x3, hn]
  exact ⟨trivial, trivial, (hp.st_d.sub_left (VG.Proof.ChaCha20.AArch64.Stream.cpR_sub s₀)).sub_right (VG.Proof.ChaCha20.AArch64.Stream.blR_sub s₀),
    Offset.disjoint _ (by omega) (by omega) (by omega),
    (hp.st_d.sub_left (VG.Proof.ChaCha20.AArch64.Stream.wkR_sub s₀)).symm.sub_left (VG.Proof.ChaCha20.AArch64.Stream.blR_sub s₀), hwrap⟩

/-! ## The call of the block function -/

/-- The arguments of the call of the block function, and the registers the
rest uses. -/
structure TArgs (s₀ s : State) : Prop where
  x0 : s.gpr .x0 = VG.Proof.ChaCha20.AArch64.Stream.st s₀
  x1 : s.gpr .x1 = VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 64
  x21 : s.gpr .x21 = VG.Proof.ChaCha20.AArch64.Stream.st s₀
  x22 : s.gpr .x22 = VG.Proof.ChaCha20.AArch64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀)
  x23 : s.gpr .x23 = BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.T s₀)
  rd : s.rd = []
  wr : s.wr = [VG.Proof.ChaCha20.AArch64.Stream.stR s₀, VG.Proof.ChaCha20.AArch64.Stream.dR s₀]

theorem tailArgs_ok {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Stream.APre s₀) {s : State} (h : VG.Proof.ChaCha20.AArch64.Stream.Q2 s₀ s) :
    WP isa (.block tailArgs) s (VG.Proof.ChaCha20.AArch64.Stream.TArgs s₀) :=
  wp_mov fun s' u => wp_addImm (by decide) fun s'' u' => WP.block_nil
    ⟨by rw [u'.other _ (by decide), u.gpr, h.x21], by rw [u'.gpr, u.other _ (by decide), h.x21],
      by rw [u'.other _ (by decide), u.other _ (by decide), h.x21],
      by rw [u'.other _ (by decide), u.other _ (by decide), h.x22],
      by rw [u'.other _ (by decide), u.other _ (by decide), h.x23],
      by rw [u'.rd, u.rd, h.rd, hp.rd], by rw [u'.wr, u.wr, h.wr, hp.wr]⟩

/-- After the block function: the registers the rest uses. -/
structure TAfter (s₀ s : State) : Prop where
  x21 : s.gpr .x21 = VG.Proof.ChaCha20.AArch64.Stream.st s₀
  x22 : s.gpr .x22 = VG.Proof.ChaCha20.AArch64.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.H s₀ + 64 * VG.Proof.ChaCha20.AArch64.Stream.NB s₀)
  x23 : s.gpr .x23 = BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Stream.T s₀)

theorem TArgs.covers {s₀ s : State} (h : VG.Proof.ChaCha20.AArch64.Stream.TArgs s₀ s) :
    Covers ([⟨VG.Proof.ChaCha20.AArch64.Stream.st s₀, 64⟩] ++ [⟨VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 64, 256⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 64, 256⟩] s.wr := by
  refine ⟨?_, ?_⟩
  · rw [h.rd, h.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.ChaCha20.AArch64.Stream.stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 768 by decide⟩
    · exact ⟨VG.Proof.ChaCha20.AArch64.Stream.stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩
  · rw [h.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.ChaCha20.AArch64.Stream.stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩

theorem TArgs.pre {s₀ s : State} (h : VG.Proof.ChaCha20.AArch64.Stream.TArgs s₀ s) :
    Proof.ChaCha20.blockAArch64.pre
      (s.callEntry.withRegions [⟨VG.Proof.ChaCha20.AArch64.Stream.st s₀, 64⟩] [⟨VG.Proof.ChaCha20.AArch64.Stream.st s₀ + BitVec.ofNat 64 64, 256⟩]) := by
  simp only [Proof.ChaCha20.blockAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' s (by decide : Reg.x0 ∉ linkRegs), VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' s (by decide : Reg.x1 ∉ linkRegs),
    h.x0, h.x1]
  exact ⟨trivial, trivial, Offset.disjoint_base _ (by omega) (by omega)⟩

theorem TArgs.call {s₀ s : State} (h : VG.Proof.ChaCha20.AArch64.Stream.TArgs s₀ s) :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.AArch64.block) s (VG.Proof.ChaCha20.AArch64.Stream.TAfter s₀) :=
  VG.Proof.ChaCha20.AArch64.Stream.block_call h.x0 h.x1 (Offset.disjoint_base _ (by omega) (by omega)) h.covers.1 h.covers.2
    fun _ k _ => ⟨by rw [k.cs .x21 (by decide) (by decide), h.x21], by rw [k.cs .x22 (by decide) (by decide), h.x22],
      by rw [k.cs .x23 (by decide) (by decide), h.x23]⟩

/-! ## The pieces, related -/

section
variable {a b : State} (h : VG.Proof.ChaCha20.AArch64.Stream.Two a b)
include h

theorem check_rel :
    RelCT isa (fun x y => x = a ∧ y = b) (.block check) fun x y => VG.Proof.ChaCha20.AArch64.Stream.Sp VG.Proof.ChaCha20.AArch64.Stream.Q0 a x ∧ VG.Proof.ChaCha20.AArch64.Stream.Sp VG.Proof.ChaCha20.AArch64.Stream.Q0 b y :=
  RelCT.post (VG.Proof.ChaCha20.AArch64.Stream.taintRegs [.x0] (fun x y ⟨hx, hy⟩ => by
      subst hx hy
      refine ⟨h.hsp, fun r hr => ?_⟩
      simp only [List.mem_singleton] at hr; subst hr; exact h.hst) (by taint_decide))
    fun x y ⟨hx, hy⟩ => ⟨by subst hx; exact VG.Proof.ChaCha20.AArch64.Stream.wp_sp (VG.Proof.ChaCha20.AArch64.Stream.check_ok h.pa) rfl, by subst hy; exact VG.Proof.ChaCha20.AArch64.Stream.wp_sp (VG.Proof.ChaCha20.AArch64.Stream.check_ok h.pb) rfl⟩

theorem part1_rel (hle : VG.Proof.ChaCha20.AArch64.Stream.L a ≤ VG.Proof.ChaCha20.AArch64.Stream.N a) :
    RelCT isa (fun x y => VG.Proof.ChaCha20.AArch64.Stream.Sp VG.Proof.ChaCha20.AArch64.Stream.Q0 a x ∧ VG.Proof.ChaCha20.AArch64.Stream.Sp VG.Proof.ChaCha20.AArch64.Stream.Q0 b y) part1 fun x y => VG.Proof.ChaCha20.AArch64.Stream.Sp VG.Proof.ChaCha20.AArch64.Stream.Q1 a x ∧ VG.Proof.ChaCha20.AArch64.Stream.Sp VG.Proof.ChaCha20.AArch64.Stream.Q1 b y :=
  RelCT.post (VG.Proof.ChaCha20.AArch64.Stream.taintRegs [.x0, .x1, .x2, .x10, .x12] (fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => by
      refine ⟨by rw [sx, sy, h.hsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [hx.keep _ (by decide) (by decide) (by decide) (by decide) (by decide),
          hy.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.hst
      · rw [hx.keep _ (by decide) (by decide) (by decide) (by decide) (by decide),
          hy.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.hdp
      · rw [hx.keep _ (by decide) (by decide) (by decide) (by decide) (by decide),
          hy.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.hx2
      · rw [hx.x10, hy.x10, h.eqO]
      · rw [hx.x12, hy.x12, h.eqO, h.eqL]) (by taint_decide))
    fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => ⟨VG.Proof.ChaCha20.AArch64.Stream.wp_sp (VG.Proof.ChaCha20.AArch64.Stream.part1_ok h.pa hle hx) sx,
      VG.Proof.ChaCha20.AArch64.Stream.wp_sp (VG.Proof.ChaCha20.AArch64.Stream.part1_ok h.pb (by rw [← h.eqL, ← h.hleft]; exact hle) hy) sy⟩

theorem xor_rel (v : Proof.ChaCha20.AArch64.XorImpl) :
    RelCT isa (fun x y => VG.Proof.ChaCha20.AArch64.Stream.Sp VG.Proof.ChaCha20.AArch64.Stream.Args a x ∧ VG.Proof.ChaCha20.AArch64.Stream.Sp VG.Proof.ChaCha20.AArch64.Stream.Args b y) (.call v.callee.name v.callee.code) fun _ _ => True := by
  have ecp : VG.Proof.ChaCha20.AArch64.Stream.cpR b = VG.Proof.ChaCha20.AArch64.Stream.cpR a := by simp only [VG.Proof.ChaCha20.AArch64.Stream.cpR, h.hst]
  have ebl : VG.Proof.ChaCha20.AArch64.Stream.blR b = VG.Proof.ChaCha20.AArch64.Stream.blR a := by simp only [VG.Proof.ChaCha20.AArch64.Stream.blR, h.hdp, h.eqH, h.eqNB]
  have ewk : VG.Proof.ChaCha20.AArch64.Stream.wkR b = VG.Proof.ChaCha20.AArch64.Stream.wkR a := by simp only [VG.Proof.ChaCha20.AArch64.Stream.wkR, h.hst]
  refine RelCT.call v.ok v.ct [] [VG.Proof.ChaCha20.AArch64.Stream.cpR a, VG.Proof.ChaCha20.AArch64.Stream.blR a, VG.Proof.ChaCha20.AArch64.Stream.wkR a] fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => ?_
  have py := hy.pre h.pb
  have cy := hy.covers
  rw [ecp, ebl, ewk] at py cy
  refine ⟨hx.pre h.pa, py, ?_, hx.covers.1, hx.covers.2, cy.1, cy.2⟩
  simp only [Proof.ChaCha20.xorAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' x (by decide : Reg.x0 ∉ linkRegs), VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' x (by decide : Reg.x1 ∉ linkRegs),
    VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' x (by decide : Reg.x2 ∉ linkRegs), VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' x (by decide : Reg.x3 ∉ linkRegs),
    VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' y (by decide : Reg.x0 ∉ linkRegs), VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' y (by decide : Reg.x1 ∉ linkRegs),
    VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' y (by decide : Reg.x2 ∉ linkRegs), VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' y (by decide : Reg.x3 ∉ linkRegs),
    hx.x0, hx.x1, hx.x2, hx.x3, hy.x0, hy.x1, hy.x2, hy.x3, h.hst, h.hdp, h.eqH, h.eqNB, sx, sy, h.hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem part2_rel (v : Proof.ChaCha20.AArch64.XorImpl) :
    RelCT isa (fun x y => VG.Proof.ChaCha20.AArch64.Stream.Sp VG.Proof.ChaCha20.AArch64.Stream.Q1 a x ∧ VG.Proof.ChaCha20.AArch64.Stream.Sp VG.Proof.ChaCha20.AArch64.Stream.Q1 b y) (part2 v.callee) fun x y => VG.Proof.ChaCha20.AArch64.Stream.Sp VG.Proof.ChaCha20.AArch64.Stream.Q2 a x ∧ VG.Proof.ChaCha20.AArch64.Stream.Sp VG.Proof.ChaCha20.AArch64.Stream.Q2 b y := by
  refine RelCT.post ?_ fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => ⟨VG.Proof.ChaCha20.AArch64.Stream.wp_sp (VG.Proof.ChaCha20.AArch64.Stream.part2_ok v h.pa hx) sx, VG.Proof.ChaCha20.AArch64.Stream.wp_sp (VG.Proof.ChaCha20.AArch64.Stream.part2_ok v h.pb hy) sy⟩
  refine RelCT.ite (fun x y ⟨⟨hx, _⟩, ⟨hy, _⟩⟩ => by
      have ex : isa.eval (.zero .x .x2) x = some (x.gpr .x2 == 0) := eval_zero x .x2
      have ey : isa.eval (.zero .x .x2) y = some (y.gpr .x2 == 0) := eval_zero y .x2
      rw [ex, ey, hx.x2, hy.x2, h.eqNB])
    (VG.Proof.ChaCha20.AArch64.Stream.taintRegs [] (fun x y ⟨⟨⟨_, sx⟩, ⟨_, sy⟩⟩, _⟩ => ⟨by rw [sx, sy, h.hsp], fun r hr => by simp at hr⟩)
      (by taint_decide)) ?_
  refine RelCT.seq (R := fun x y => VG.Proof.ChaCha20.AArch64.Stream.Sp VG.Proof.ChaCha20.AArch64.Stream.Args a x ∧ VG.Proof.ChaCha20.AArch64.Stream.Sp VG.Proof.ChaCha20.AArch64.Stream.Args b y) ?_ (VG.Proof.ChaCha20.AArch64.Stream.xor_rel h v)
  refine RelCT.post (VG.Proof.ChaCha20.AArch64.Stream.taintRegs [.x21, .x22, .x2] (fun x y ⟨⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩, _⟩ => by
      refine ⟨by rw [sx, sy, h.hsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hx.x21, hy.x21, h.hst]
      · rw [hx.x22, hy.x22, h.hdp, h.eqH]
      · rw [hx.x2, hy.x2, h.eqNB]) (by taint_decide))
    fun x y ⟨⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩, _⟩ => ⟨VG.Proof.ChaCha20.AArch64.Stream.wp_sp (VG.Proof.ChaCha20.AArch64.Stream.args_ok h.pa hx) sx, VG.Proof.ChaCha20.AArch64.Stream.wp_sp (VG.Proof.ChaCha20.AArch64.Stream.args_ok h.pb hy) sy⟩

theorem part3_rel : RelCT isa (fun x y => VG.Proof.ChaCha20.AArch64.Stream.Sp VG.Proof.ChaCha20.AArch64.Stream.Q2 a x ∧ VG.Proof.ChaCha20.AArch64.Stream.Sp VG.Proof.ChaCha20.AArch64.Stream.Q2 b y) part3 fun x y => VG.Proof.ChaCha20.AArch64.Stream.Sp VG.Proof.ChaCha20.AArch64.Stream.Q3 a x ∧ VG.Proof.ChaCha20.AArch64.Stream.Sp VG.Proof.ChaCha20.AArch64.Stream.Q3 b y := by
  refine RelCT.post ?_ fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => ⟨VG.Proof.ChaCha20.AArch64.Stream.wp_sp (VG.Proof.ChaCha20.AArch64.Stream.part3_ok h.pa hx) sx, VG.Proof.ChaCha20.AArch64.Stream.wp_sp (VG.Proof.ChaCha20.AArch64.Stream.part3_ok h.pb hy) sy⟩
  refine RelCT.ite (fun x y ⟨⟨hx, _⟩, ⟨hy, _⟩⟩ => by
      have ex : isa.eval (.zero .x .x23) x = some (x.gpr .x23 == 0) := eval_zero x .x23
      have ey : isa.eval (.zero .x .x23) y = some (y.gpr .x23 == 0) := eval_zero y .x23
      rw [ex, ey, hx.x23, hy.x23, h.eqT])
    (VG.Proof.ChaCha20.AArch64.Stream.taintRegs [] (fun x y ⟨⟨⟨_, sx⟩, ⟨_, sy⟩⟩, _⟩ => ⟨by rw [sx, sy, h.hsp], fun r hr => by simp at hr⟩)
      (by taint_decide)) ?_
  refine RelCT.seq (R := fun x y => VG.Proof.ChaCha20.AArch64.Stream.Sp VG.Proof.ChaCha20.AArch64.Stream.TArgs a x ∧ VG.Proof.ChaCha20.AArch64.Stream.Sp VG.Proof.ChaCha20.AArch64.Stream.TArgs b y)
    (RelCT.post (VG.Proof.ChaCha20.AArch64.Stream.taintRegs [.x21] (fun x y ⟨⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩, _⟩ => by
        refine ⟨by rw [sx, sy, h.hsp], fun r hr => ?_⟩
        simp only [List.mem_singleton] at hr; subst hr; rw [hx.x21, hy.x21, h.hst]) (by taint_decide))
      fun x y ⟨⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩, _⟩ => ⟨VG.Proof.ChaCha20.AArch64.Stream.wp_sp (VG.Proof.ChaCha20.AArch64.Stream.tailArgs_ok h.pa hx) sx, VG.Proof.ChaCha20.AArch64.Stream.wp_sp (VG.Proof.ChaCha20.AArch64.Stream.tailArgs_ok h.pb hy) sy⟩) ?_
  refine RelCT.seq (R := fun x y => VG.Proof.ChaCha20.AArch64.Stream.Sp VG.Proof.ChaCha20.AArch64.Stream.TAfter a x ∧ VG.Proof.ChaCha20.AArch64.Stream.Sp VG.Proof.ChaCha20.AArch64.Stream.TAfter b y) ?_
    (VG.Proof.ChaCha20.AArch64.Stream.taintRegs [.x21, .x22, .x23] (fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => by
      refine ⟨by rw [sx, sy, h.hsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hx.x21, hy.x21, h.hst]
      · rw [hx.x22, hy.x22, h.hdp, h.eqH, h.eqNB]
      · rw [hx.x23, hy.x23, h.eqT]) (by taint_decide))
  have est : VG.Proof.ChaCha20.AArch64.Stream.st b = VG.Proof.ChaCha20.AArch64.Stream.st a := h.hst.symm
  refine RelCT.post (RelCT.call Proof.ChaCha20.AArch64.block_correct Proof.ChaCha20.AArch64.block_ct
    [⟨VG.Proof.ChaCha20.AArch64.Stream.st a, 64⟩] [⟨VG.Proof.ChaCha20.AArch64.Stream.st a + BitVec.ofNat 64 64, 256⟩] fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => ?_)
    fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => ⟨VG.Proof.ChaCha20.AArch64.Stream.wp_sp hx.call sx, VG.Proof.ChaCha20.AArch64.Stream.wp_sp hy.call sy⟩
  have py := hy.pre
  have cy := hy.covers
  rw [est] at py cy
  refine ⟨hx.pre, py, ?_, hx.covers.1, hx.covers.2, cy.1, cy.2⟩
  simp only [Proof.ChaCha20.blockAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' x (by decide : Reg.x0 ∉ linkRegs), VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' x (by decide : Reg.x1 ∉ linkRegs),
    VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' y (by decide : Reg.x0 ∉ linkRegs), VG.Proof.ChaCha20.AArch64.Stream.callEntry_gpr' y (by decide : Reg.x1 ∉ linkRegs),
    hx.x0, hx.x1, hy.x0, hy.x1, h.hst, sx, sy, h.hsp]
  exact ⟨trivial, trivial, trivial⟩

theorem apply_rel (v : Proof.ChaCha20.AArch64.XorImpl) :
    RelCT isa (fun x y => x = a ∧ y = b) (apply v.callee) fun _ _ => True := by
  rw [VG.Proof.ChaCha20.AArch64.Stream.apply_eq]
  have e11 : ∀ {s₀ x : State}, VG.Proof.ChaCha20.AArch64.Stream.Q0 s₀ x →
      isa.eval (.zero .x .x11) x = some (decide (VG.Proof.ChaCha20.AArch64.Stream.N s₀ < VG.Proof.ChaCha20.AArch64.Stream.L s₀)) := fun {s₀ x} hx => by
    have e : isa.eval (.zero .x .x11) x = some (x.gpr .x11 == 0) := eval_zero x .x11
    rw [e, hx.x11]; by_cases hh : VG.Proof.ChaCha20.AArch64.Stream.L s₀ ≤ VG.Proof.ChaCha20.AArch64.Stream.N s₀ <;> simp [hh] <;> omega
  refine RelCT.seq (VG.Proof.ChaCha20.AArch64.Stream.check_rel h) (RelCT.ite (fun x y ⟨⟨hx, _⟩, ⟨hy, _⟩⟩ => by
      rw [e11 hx, e11 hy, h.hleft, h.eqL])
    (VG.Proof.ChaCha20.AArch64.Stream.taintRegs [] (fun x y ⟨⟨⟨_, sx⟩, ⟨_, sy⟩⟩, _⟩ => ⟨by rw [sx, sy, h.hsp], fun r hr => by simp at hr⟩)
      (by taint_decide)) ?_)
  by_cases hlt : VG.Proof.ChaCha20.AArch64.Stream.N a < VG.Proof.ChaCha20.AArch64.Stream.L a
  · refine RelCT.of_false fun x y hp => ?_
    have he := hp.2
    rw [e11 hp.1.1.1] at he
    simp [hlt] at he
  have hle : VG.Proof.ChaCha20.AArch64.Stream.L a ≤ VG.Proof.ChaCha20.AArch64.Stream.N a := by omega
  refine RelCT.seq (RelCT.mono (VG.Proof.ChaCha20.AArch64.Stream.part1_rel h hle) (fun _ _ hp => hp.1) fun _ _ hq => hq)
    (RelCT.seq (VG.Proof.ChaCha20.AArch64.Stream.part2_rel h v) (RelCT.seq (VG.Proof.ChaCha20.AArch64.Stream.part3_rel h) ?_))
  exact VG.Proof.ChaCha20.AArch64.Stream.taintRegs [.x21] (fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => by
    refine ⟨by rw [sx, sy, h.hsp], fun r hr => ?_⟩
    simp only [List.mem_singleton] at hr; subst hr; rw [hx.x21, hy.x21, h.hst]) (by taint_decide)

end

theorem Two.of {a b : State} (ha : Proof.ChaCha20.applyAArch64.pre a) (hb : Proof.ChaCha20.applyAArch64.pre b)
    (hq : Proof.ChaCha20.applyAArch64.pub a b) : VG.Proof.ChaCha20.AArch64.Stream.Two a b := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hq
  exact ⟨APre.of a ha, APre.of b hb, p1, p2, p3, p4, (List.cons.inj p5).1⟩

theorem apply_ct (v : Proof.ChaCha20.AArch64.XorImpl) :
    ConstantTime isa Proof.ChaCha20.applyAArch64.pre Proof.ChaCha20.applyAArch64.pub (apply v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.ChaCha20.AArch64.Stream.apply_rel (Two.of h₁ h₂ hq) v _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem apply_ok (v : Proof.ChaCha20.AArch64.XorImpl) (s : State) (hs : Proof.ChaCha20.applyAArch64.pre s) :
    ∃ t s', Exec isa (apply v.callee) s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.applyAArch64.post s s' := by
  obtain ⟨t, s', he, hf, hv⟩ := VG.Proof.ChaCha20.AArch64.Stream.apply_correct v (APre.of s hs)
  exact ⟨t, s', he, ⟨hf.1, Exec.sp he, hv⟩, hf.2⟩

/-- A state satisfying the precondition of `apply` (with no data). -/
def applySat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 768⟩, ⟨0x2000, 0⟩]

theorem apply_verified (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target (apply v.callee) (Spec.ChaCha20.applyContract AArch64.abi 0) :=
  Verified.of_correct (VG.Proof.ChaCha20.AArch64.Stream.apply_ok v) (VG.Proof.ChaCha20.AArch64.Stream.apply_ct v) (by
    sig_implies [Spec.ChaCha20.applyContract, Spec.ChaCha20.applySig, Proof.ChaCha20.applyAArch64,
      AArch64.abi, AArch64.argRegs] [applySat] using VG.Proof.ChaCha20.AArch64.Stream.applySat)

end VG.Proof.ChaCha20.AArch64.Stream

end
