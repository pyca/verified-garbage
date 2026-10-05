import VerifiedGarbage.Proof.ChaCha20.Arm.Stream.Init
import VerifiedGarbage.Proof.ChaCha20.Arm.Xor
import VerifiedGarbage.Proof.ChaCha20.StreamBytes
import VerifiedGarbage.Proof.Framework.Arm.RelCT

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.Arm.Stream.Bytes`. -/
section

/-!
# Streaming ChaCha20 on ARMv7: XORing bytes

Untrusted: everything here is checked by Lean. `xorBytes` XORs the `r2`
bytes at `r3` into those at `r5`, one at a time, advancing both (the loop of
`vg_chacha20_xor`, `Xor.xorLoop`).
-/

namespace VG.Proof.ChaCha20.Arm.Stream

open VG VG.Arm VG.Impl.ChaCha20.Arm.Stream
open VG.Impl.ChaCha20.Arm.Xor (xorLoop)
open VG.Proof.ChaCha20.Arm.Xor (xorBody xorLoop_eq wp_eor imm0 imm1 ea0 xor_setWidth writeW8_apply add_one'
  sub_one' sub_zero' eval_ne_ofNat)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_add wp_subs wp_cmp wp_ldrb wp_strb eval_eq
  ofNat_beq_zero)

/-- What `xorBytes` needs: `c` bytes at `D` to write and at `K` to read, not
overlapping. -/
structure BPre (s : State) (D K : BitVec 32) (c : Nat) : Prop where
  r5 : s.gpr .r5 = D
  r3 : s.gpr .r3 = K
  r2 : s.gpr .r2 = BitVec.ofNat 32 c
  d_fit : D.toNat + c ≤ 2 ^ 32
  k_fit : K.toNat + c < 2 ^ 32
  wD : ∀ k < c, InRegions s.wr (State.addr D + BitVec.ofNat 64 k) 1
  rK : ∀ k < c, InRegions (s.rd ++ s.wr) (State.addr K + BitVec.ofNat 64 k) 1
  sep : ∀ j < c, ∀ k < c, State.addr D + BitVec.ofNat 64 j ≠ State.addr K + BitVec.ofNat 64 k

/-- What `xorBytes` leaves: the bytes XORed, and `r5` past them; only `r0`,
`r2`, `r3`, `r5` and `r12` are written. -/
structure BPost (s : State) (D K : BitVec 32) (c : Nat) (s' : State) : Prop where
  r5 : s'.gpr .r5 = D + BitVec.ofNat 32 c
  keep : ∀ r, r ≠ .r0 → r ≠ .r2 → r ≠ .r3 → r ≠ .r5 → r ≠ .r12 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  data : ∀ k < c, s'.mem (State.addr D + BitVec.ofNat 64 k) =
    s.mem (State.addr D + BitVec.ofNat 64 k) ^^^ s.mem (State.addr K + BitVec.ofNat 64 k)
  frame : Frame [⟨State.addr D, c⟩] s.mem s'.mem

/-- Before byte `i`. -/
structure LInv (s : State) (D K : BitVec 32) (c i : Nat) (s' : State) : Prop where
  r5 : s'.gpr .r5 = D + BitVec.ofNat 32 i
  r3 : s'.gpr .r3 = K + BitVec.ofNat 32 i
  r2 : s'.gpr .r2 = BitVec.ofNat 32 (c - i)
  keep : ∀ r, r ≠ .r0 → r ≠ .r2 → r ≠ .r3 → r ≠ .r5 → r ≠ .r12 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  data : ∀ k < c, s'.mem (State.addr D + BitVec.ofNat 64 k) =
    if k < i then s.mem (State.addr D + BitVec.ofNat 64 k) ^^^ s.mem (State.addr K + BitVec.ofNat 64 k)
    else s.mem (State.addr D + BitVec.ofNat 64 k)
  frame : Frame [⟨State.addr D, c⟩] s.mem s'.mem

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

theorem byte_step {s : State} {D K : BitVec 32} {c i : Nat} (hp : VG.Proof.ChaCha20.Arm.Stream.BPre s D K c) (hi : i < c) {s₁ : State}
    (h : VG.Proof.ChaCha20.Arm.Stream.LInv s D K c i s₁) :
    WP isa (.block xorBody) s₁ fun s' => VG.Proof.ChaCha20.Arm.Stream.LInv s D K c (i + 1) s' ∧ s'.z = (s'.gpr .r2 - 0 == 0) := by
  have hc := hp.d_fit
  have hk := hp.k_fit
  have cd : (⟨State.addr D, c⟩ : Region).Contains (State.addr D + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  have i₁ : InRegions (s₁.rd ++ s₁.wr) (State.addr D + BitVec.ofNat 64 i) 1 := by
    obtain ⟨r, hr, hc⟩ := hp.wD i hi; exact ⟨r, by rw [h.rd, h.wr]; exact List.mem_append_right _ hr, hc⟩
  have i₂ : InRegions (s₁.rd ++ s₁.wr) (State.addr K + BitVec.ofNat 64 i) 1 := by
    rw [h.rd, h.wr]; exact hp.rK i hi
  have o₁ : InRegions s₁.wr (State.addr D + BitVec.ofNat 64 i) 1 := by rw [h.wr]; exact hp.wD i hi
  have ed : ∀ x : State, x.gpr .r5 = s₁.gpr .r5 →
      State.addr (x.gpr .r5 + BitVec.ofNat 32 0) = State.addr D + BitVec.ofNat 64 i :=
    fun x hx => by rw [hx, h.r5]; exact ea0 (by omega)
  unfold xorBody
  refine wp_ldrb (by decide) (ed s₁ rfl) i₁ fun s₂ u₂ => ?_
  refine wp_ldrb (a := State.addr K + BitVec.ofNat 64 i) (by decide)
    (by rw [u₂.other _ (by decide), h.r3]; exact ea0 (by omega))
    (by rw [u₂.rd, u₂.wr]; exact i₂) fun s₃ u₃ => ?_
  refine wp_eor (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_strb (by decide) (ed s₄ (by rw [u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide)]))
    (by rw [u₄.wr, u₃.wr, u₂.wr]; exact o₁) fun s₅ g₅ => ?_
  refine wp_add (op2_imm imm1) fun s₆ u₆ => wp_add (op2_imm imm1) fun s₇ u₇ =>
    wp_subs (op2_imm imm1) fun s₈ u₈ hz => WP.block_nil ?_
  have hk' : s₁.mem (State.addr K + BitVec.ofNat 64 i) = s.mem (State.addr K + BitVec.ofNat 64 i) :=
    h.frame _ fun r hr hcont => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Proof.ChaCha20.Arm.Stream.not_contains hp.sep hi hcont
  have hv : (s₄.gpr .r0).setWidth 8 =
      s.mem (State.addr D + BitVec.ofNat 64 i) ^^^ s.mem (State.addr K + BitVec.ofNat 64 i) := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₃.gpr, u₂.mem, xor_setWidth, h.data _ hi, hk']
    simp
  have hm : s₈.mem = s₁.mem.writeW (State.addr D + BitVec.ofNat 64 i)
      (s.mem (State.addr D + BitVec.ofNat 64 i) ^^^ s.mem (State.addr K + BitVec.ofNat 64 i)) := by
    rw [u₈.mem, u₇.mem, u₆.mem, g₅.mem, hv, u₄.mem, u₃.mem, u₂.mem]
  have hfd : Frame [⟨State.addr D, c⟩] s₁.mem s₈.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cd
  have g : ∀ r, r ≠ .r0 → r ≠ .r2 → r ≠ .r3 → r ≠ .r5 → r ≠ .r12 → s₈.gpr r = s₁.gpr r :=
    fun r h₁ h₂ h₃ h₄ h₅ => by
      rw [u₈.other r h₂, u₇.other r h₃, u₆.other r h₄, g₅.gpr, u₄.other r h₁, u₃.other r h₅,
        u₂.other r h₁]
  have h7 : s₇.gpr .r2 = BitVec.ofNat 32 (c - i) := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), g₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), h.r2]
  have hr2 : s₈.gpr .r2 = BitVec.ofNat 32 (c - (i + 1)) := by
    rw [u₈.gpr, h7, sub_one' (by omega), Nat.sub_sub]
  refine ⟨⟨?_, ?_, hr2, fun r h₁ h₂ h₃ h₄ h₅ => by rw [g r h₁ h₂ h₃ h₄ h₅]; exact h.keep r h₁ h₂ h₃ h₄ h₅,
    by rw [u₈.rd, u₇.rd, u₆.rd, g₅.rd, u₄.rd, u₃.rd, u₂.rd, h.rd],
    by rw [u₈.wr, u₇.wr, u₆.wr, g₅.wr, u₄.wr, u₃.wr, u₂.wr, h.wr],
    by rw [u₈.sp, u₇.sp, u₆.sp, g₅.sp, u₄.sp, u₃.sp, u₂.sp, h.sp], fun k hk' => ?_, h.frame.trans hfd⟩, ?_⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), h.r5, add_one']
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), g₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), h.r3, add_one']
  · rw [hm, VG.Proof.ChaCha20.Arm.Xor.writeW8_apply]
    by_cases he : k = i
    · subst he; simp
    · simp only [VG.Proof.ChaCha20.Arm.Stream.D_ne (D := State.addr D) (by omega) hk' hi he, ite_false]
      rw [h.data k hk']
      by_cases h₁ : k < i
      · simp [h₁, show k < i + 1 by omega]
      · simp [h₁, show ¬ k < i + 1 by omega]
  · rw [hz, hr2, h7, sub_one' (by omega), sub_zero', Nat.sub_sub]

theorem LInv.zero {s : State} {D K : BitVec 32} {c : Nat} (hp : VG.Proof.ChaCha20.Arm.Stream.BPre s D K c) : VG.Proof.ChaCha20.Arm.Stream.LInv s D K c 0 s :=
  ⟨by rw [hp.r5]; simp, by rw [hp.r3]; simp, by rw [hp.r2, Nat.sub_zero], fun _ _ _ _ _ _ => rfl, rfl, rfl,
    rfl, fun k _ => by simp, Frame.refl _ _⟩

theorem LInv.post {s : State} {D K : BitVec 32} {c : Nat} {s' : State} (h : VG.Proof.ChaCha20.Arm.Stream.LInv s D K c c s') :
    VG.Proof.ChaCha20.Arm.Stream.BPost s D K c s' :=
  ⟨h.r5, h.keep, h.rd, h.wr, h.sp, fun k hk => by rw [h.data k hk, ite_pos hk], h.frame⟩

theorem loop_ok {s : State} {D K : BitVec 32} {c : Nat} (hp : VG.Proof.ChaCha20.Arm.Stream.BPre s D K c) (hc0 : c ≠ 0) :
    WP isa xorLoop s (VG.Proof.ChaCha20.Arm.Stream.BPost s D K c) := by
  have hc := hp.d_fit
  rw [xorLoop_eq]
  let Inv : Nat → State → Prop := fun n s' => ∃ i, n = c - i ∧ i < c ∧ VG.Proof.ChaCha20.Arm.Stream.LInv s D K c i s'
  have hstep : ∀ n s', Inv n s' → WP isa (.block xorBody) s' (fun s'' =>
      (isa.eval .ne s'' = some false ∧ VG.Proof.ChaCha20.Arm.Stream.BPost s D K c s'') ∨
      (isa.eval .ne s'' = some true ∧ ∃ n' < n, Inv n' s'')) := by
    rintro n s' ⟨i, rfl, hi, hI⟩
    refine WP.mono (VG.Proof.ChaCha20.Arm.Stream.byte_step hp hi hI) fun s'' ⟨h', hz'⟩ => ?_
    have hz := eval_ne_ofNat s'' (show c - (i + 1) < 2 ^ 32 by omega) hz' h'.r2
    by_cases hl : i + 1 = c
    · exact .inl ⟨by rw [hz]; simp; omega, LInv.post (hl ▸ h')⟩
    · exact .inr ⟨by rw [hz]; simp; omega, c - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
  exact WP.loop (M := isa) Inv hstep c s ⟨0, by simp, by omega, LInv.zero hp⟩

theorem xorBytes_eq : xorBytes = .seq (.block [.cmp .r2 (.imm 0)]) (.ite .eq (.block []) xorLoop) := rfl

theorem xorBytes_ok {s : State} {D K : BitVec 32} {c : Nat} (hp : VG.Proof.ChaCha20.Arm.Stream.BPre s D K c) :
    WP isa xorBytes s (VG.Proof.ChaCha20.Arm.Stream.BPost s D K c) := by
  have hc := hp.k_fit
  rw [VG.Proof.ChaCha20.Arm.Stream.xorBytes_eq]
  refine WP.seq (wp_cmp (n := .r2) (op2_imm imm0) fun s₁ f₁ hz => WP.block_nil ?_)
  have hp₁ : VG.Proof.ChaCha20.Arm.Stream.BPre s₁ D K c := ⟨by rw [f₁.gpr, hp.r5], by rw [f₁.gpr, hp.r3], by rw [f₁.gpr, hp.r2], hp.d_fit,
    hp.k_fit, fun k hk => by rw [f₁.wr]; exact hp.wD k hk, fun k hk => by rw [f₁.rd, f₁.wr]; exact hp.rK k hk,
    hp.sep⟩
  have conv : ∀ s', VG.Proof.ChaCha20.Arm.Stream.BPost s₁ D K c s' → VG.Proof.ChaCha20.Arm.Stream.BPost s D K c s' := fun s' h =>
    ⟨h.r5, fun r a b d e f => by rw [h.keep r a b d e f, f₁.gpr], by rw [h.rd, f₁.rd], by rw [h.wr, f₁.wr],
      by rw [h.sp, f₁.sp], fun k hk => by rw [h.data k hk, f₁.mem], f₁.mem ▸ h.frame⟩
  refine WP.ite (decide (c = 0)) (by
      have e : isa.eval .eq s₁ = some s₁.z := eval_eq s₁
      rw [e, hz, hp.r2, sub_zero', ofNat_beq_zero (by omega)])
    (fun h0 => WP.block_nil (M := isa) (conv _ ?_)) (fun h0 => WP.mono (VG.Proof.ChaCha20.Arm.Stream.loop_ok hp₁ (by simpa using h0)) conv)
  simp only [decide_eq_true_eq] at h0; subst h0; exact (LInv.zero hp₁).post

end VG.Proof.ChaCha20.Arm.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.Arm.Stream.Calls`. -/
section

/-!
# Streaming ChaCha20 on ARMv7: the entry state and the calls

Untrusted: everything here is checked by Lean. The contract of `apply`, what
its precondition gives, and the calls of `vg_chacha20_block` and
`vg_chacha20_xor`, from their proofs of correctness (with `WP.call` and
`WP.callCalls`), as ChaCha20-Poly1305 makes them. A call (`bl`) stores
nothing in memory, so the callee changes memory only within the regions it
may write.
-/

namespace VG.Proof.ChaCha20

open VG.Arm
open VG.Spec.ChaCha20 (keyAt restAt leftAt bytesAt)

/-- ARMv7 contract for `vg_chacha20_apply(state = r0, data = r1, len = r2) -> r0`.
The return address is in `lr`, which the code saves in the state, so no
stack is used. -/
def applyArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 768⟩
    let data : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
    s.rd = [] ∧ s.wr = [state, data] ∧ state.Disjoint data ∧
    (s.gpr .r0).toNat + 768 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32
  post s s' :=
    keyAt s'.mem (State.addr (s.gpr .r0)) = keyAt s.mem (State.addr (s.gpr .r0)) ∧
      if (s.gpr .r2).toNat ≤ leftAt s.mem (State.addr (s.gpr .r0)) then
        s'.gpr .r0 = 1 ∧
          bytesAt s'.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
            List.zipWith (· ^^^ ·) (bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
              ((restAt s.mem (State.addr (s.gpr .r0))).take (s.gpr .r2).toNat) ∧
          restAt s'.mem (State.addr (s.gpr .r0)) = (restAt s.mem (State.addr (s.gpr .r0))).drop (s.gpr .r2).toNat
      else
        s'.gpr .r0 = 0 ∧
          bytesAt s'.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
            bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat ∧
          restAt s'.mem (State.addr (s.gpr .r0)) = restAt s.mem (State.addr (s.gpr .r0))
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.sp = s₂.sp ∧ [leftAt s₁.mem (State.addr (s₁.gpr .r0))] = [leftAt s₂.mem (State.addr (s₂.gpr .r0))]

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.Arm.Stream

open VG VG.Arm VG.Impl.ChaCha20.Arm.Stream
open VG.Proof.MdStream.Arm (addr_off)
open VG.Spec.ChaCha20 (keyAt restAt leftAt bytesAt stateAt keystream serialize block)

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev ST : BitVec 32 := s₀.gpr .r0
abbrev DP : BitVec 32 := s₀.gpr .r1
abbrev L : Nat := (s₀.gpr .r2).toNat
abbrev st : Addr := State.addr (VG.Proof.ChaCha20.Arm.Stream.ST s₀)
abbrev dp : Addr := State.addr (VG.Proof.ChaCha20.Arm.Stream.DP s₀)
/-- The number of bytes of keystream left, and those in the buffered block. -/
abbrev N : Nat := leftAt s₀.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀)
abbrev O : Nat := VG.Proof.ChaCha20.Arm.Stream.N s₀ % 64
/-- The bytes from the buffered block, the whole blocks and the bytes of the
next block that `apply` uses. -/
abbrev H : Nat := headLen s₀.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀) (VG.Proof.ChaCha20.Arm.Stream.L s₀)
abbrev NB : Nat := blocksOf s₀.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀) (VG.Proof.ChaCha20.Arm.Stream.L s₀)
abbrev T : Nat := tailLen s₀.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀) (VG.Proof.ChaCha20.Arm.Stream.L s₀)
abbrev S0 : CState := stateAt s₀.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀)
abbrev D0 (k : Nat) : Byte := s₀.mem (VG.Proof.ChaCha20.Arm.Stream.dp s₀ + BitVec.ofNat 64 k)
abbrev stR : Region := ⟨VG.Proof.ChaCha20.Arm.Stream.st s₀, 768⟩
abbrev dR : Region := ⟨VG.Proof.ChaCha20.Arm.Stream.dp s₀, VG.Proof.ChaCha20.Arm.Stream.L s₀⟩
/-- The keystream byte XORed into byte `k` of the data. -/
abbrev KS (k : Nat) : Byte :=
  if k < VG.Proof.ChaCha20.Arm.Stream.H s₀ then s₀.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 (128 - VG.Proof.ChaCha20.Arm.Stream.O s₀ + k))
  else (serialize (block (ctr (VG.Proof.ChaCha20.Arm.Stream.S0 s₀) ((k - VG.Proof.ChaCha20.Arm.Stream.H s₀) / 64)))).getD ((k - VG.Proof.ChaCha20.Arm.Stream.H s₀) % 64) 0
/-- The data with its first `j` bytes XORed. -/
abbrev Done (j : Nat) (m : Mem) : Prop :=
  ∀ k < VG.Proof.ChaCha20.Arm.Stream.L s₀, m (VG.Proof.ChaCha20.Arm.Stream.dp s₀ + BitVec.ofNat 64 k) = if k < j then VG.Proof.ChaCha20.Arm.Stream.D0 s₀ k ^^^ VG.Proof.ChaCha20.Arm.Stream.KS s₀ k else VG.Proof.ChaCha20.Arm.Stream.D0 s₀ k
end

theorem L_lt (s₀ : State) : VG.Proof.ChaCha20.Arm.Stream.L s₀ < 2 ^ 32 := (s₀.gpr .r2).isLt
theorem N_lt (s₀ : State) : VG.Proof.ChaCha20.Arm.Stream.N s₀ < 2 ^ 64 := (s₀.mem.readW (VG.Proof.ChaCha20.Arm.Stream.st s₀ + 128) 64).isLt
theorem H_le (s₀ : State) : VG.Proof.ChaCha20.Arm.Stream.H s₀ ≤ VG.Proof.ChaCha20.Arm.Stream.L s₀ := Nat.min_le_right _ _
theorem H_le_O (s₀ : State) : VG.Proof.ChaCha20.Arm.Stream.H s₀ ≤ VG.Proof.ChaCha20.Arm.Stream.O s₀ := Nat.min_le_left _ _
theorem O_lt (s₀ : State) : VG.Proof.ChaCha20.Arm.Stream.O s₀ < 64 := Nat.mod_lt _ (by decide)
theorem T_eq (s₀ : State) : VG.Proof.ChaCha20.Arm.Stream.T s₀ = VG.Proof.ChaCha20.Arm.Stream.L s₀ - VG.Proof.ChaCha20.Arm.Stream.H s₀ - 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀ := by simp only [VG.Proof.ChaCha20.Arm.Stream.T, VG.Proof.ChaCha20.Arm.Stream.NB, tailLen, blocksOf, VG.Proof.ChaCha20.Arm.Stream.H]; omega
theorem HNB_le (s₀ : State) : VG.Proof.ChaCha20.Arm.Stream.H s₀ + 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀ ≤ VG.Proof.ChaCha20.Arm.Stream.L s₀ := by
  have := VG.Proof.ChaCha20.Arm.Stream.H_le s₀; simp only [VG.Proof.ChaCha20.Arm.Stream.NB, blocksOf, VG.Proof.ChaCha20.Arm.Stream.H] at *; omega

structure APre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [VG.Proof.ChaCha20.Arm.Stream.stR s₀, VG.Proof.ChaCha20.Arm.Stream.dR s₀]
  st_d : (VG.Proof.ChaCha20.Arm.Stream.stR s₀).Disjoint (VG.Proof.ChaCha20.Arm.Stream.dR s₀)
  st_fit : (VG.Proof.ChaCha20.Arm.Stream.ST s₀).toNat + 768 ≤ 2 ^ 32
  d_fit : (VG.Proof.ChaCha20.Arm.Stream.DP s₀).toNat + VG.Proof.ChaCha20.Arm.Stream.L s₀ ≤ 2 ^ 32

theorem APre.of (s₀ : State) (h : Proof.ChaCha20.applyArm.pre s₀) : VG.Proof.ChaCha20.Arm.Stream.APre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

namespace APre
variable {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Stream.APre s₀)
include hp

theorem eaS {d : Nat} (hd : d < 768) : State.addr (VG.Proof.ChaCha20.Arm.Stream.ST s₀ + BitVec.ofNat 32 d) = VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 d :=
  addr_off (by have := hp.st_fit; omega)

theorem sNat {d : Nat} (hd : d < 768) : (VG.Proof.ChaCha20.Arm.Stream.ST s₀ + BitVec.ofNat 32 d).toNat = (VG.Proof.ChaCha20.Arm.Stream.ST s₀).toNat + d := by
  have := hp.st_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show d < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem eaD {d : Nat} (hd : d < VG.Proof.ChaCha20.Arm.Stream.L s₀) : State.addr (VG.Proof.ChaCha20.Arm.Stream.DP s₀ + BitVec.ofNat 32 d) = VG.Proof.ChaCha20.Arm.Stream.dp s₀ + BitVec.ofNat 64 d :=
  addr_off (by have := hp.d_fit; omega)

theorem dNat {d : Nat} (hd : d < VG.Proof.ChaCha20.Arm.Stream.L s₀) : (VG.Proof.ChaCha20.Arm.Stream.DP s₀ + BitVec.ofNat 32 d).toNat = (VG.Proof.ChaCha20.Arm.Stream.DP s₀).toNat + d := by
  have := hp.d_fit
  have := VG.Proof.ChaCha20.Arm.Stream.L_lt s₀
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show d < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem w_st {d n : Nat} (h : d + n ≤ 768) : InRegions s₀.wr (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 d) n :=
  ⟨VG.Proof.ChaCha20.Arm.Stream.stR s₀, by rw [hp.wr]; exact List.mem_cons_self .., Offset.contains_base _ h (by omega)⟩

theorem r_st {d n : Nat} (h : d + n ≤ 768) : InRegions (s₀.rd ++ s₀.wr) (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 d) n := by
  rw [hp.rd, List.nil_append]; exact hp.w_st h

end APre

theorem d_ne_st {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Stream.APre s₀) {j k : Nat} (hj : j < VG.Proof.ChaCha20.Arm.Stream.L s₀) (hk : k < 768) :
    VG.Proof.ChaCha20.Arm.Stream.dp s₀ + BitVec.ofNat 64 j ≠ VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 k := by
  intro he
  have c₁ : (VG.Proof.ChaCha20.Arm.Stream.dR s₀).Contains (VG.Proof.ChaCha20.Arm.Stream.dp s₀ + BitVec.ofNat 64 j) 1 :=
    Offset.contains_base _ (by omega) (by have := VG.Proof.ChaCha20.Arm.Stream.L_lt s₀; omega)
  have c₂ : (VG.Proof.ChaCha20.Arm.Stream.stR s₀).Contains (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega) (by omega)
  rw [he] at c₁
  exact hp.st_d _ c₂ c₁

theorem dR_byte {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Stream.APre s₀) {k : Nat} (hk : k < VG.Proof.ChaCha20.Arm.Stream.L s₀) :
    InRegions s₀.wr (VG.Proof.ChaCha20.Arm.Stream.dp s₀ + BitVec.ofNat 64 k) 1 :=
  ⟨VG.Proof.ChaCha20.Arm.Stream.dR s₀, by rw [hp.wr]; simp, Offset.contains_base _ (by omega) (by have := VG.Proof.ChaCha20.Arm.Stream.L_lt s₀; omega)⟩

theorem not_in_prefix (p : Addr) {k c : Nat} (hk : c ≤ k) (hk' : k < 2 ^ 64) :
    ¬ (⟨p, c⟩ : Region).Contains (p + BitVec.ofNat 64 k) 1 := by
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat p hk']
  omega

theorem prefix_sub (p : Addr) {c n : Nat} (h : c ≤ n) : Region.Sub ⟨p, c⟩ ⟨p, n⟩ := Region.sub_prefix h

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-! ## The calls -/

/-- `s'` differs from `s` only in memory within `rs` and in registers that
are not callee-saved (or are `lr`). -/
structure Kept (rs : List Region) (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame rs s.mem s'.mem

theorem block_noCalls : Impl.ChaCha20.Arm.block.noCalls = true := by lit_decide
theorem xor_noFrames : Impl.ChaCha20.Arm.Xor.xor.noFrames = true := by lit_decide

theorem block_call {s : State} {S B : BitVec 32} (h0 : s.gpr .r0 = S) (h1 : s.gpr .r1 = B)
    (hdj : (⟨State.addr B, 256⟩ : Region).Disjoint ⟨State.addr S, 64⟩)
    (hS : S.toNat + 64 ≤ 2 ^ 32) (hB : B.toNat + 256 ≤ 2 ^ 32)
    (hc : Covers ([⟨State.addr S, 64⟩] ++ [⟨State.addr B, 256⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨State.addr B, 256⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.ChaCha20.Arm.Stream.Kept [⟨State.addr B, 256⟩] s s' →
      stateAt s'.mem (State.addr B) = Spec.ChaCha20.block (stateAt s.mem (State.addr S)) → Q s') :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.Arm.block) s Q := by
  refine WP.call (k := Proof.ChaCha20.blockArm) Proof.ChaCha20.Arm.block_correct
    (rd := [⟨State.addr S, 64⟩]) (wr := [⟨State.addr B, 256⟩]) ?_ hc hw ?_ VG.Proof.ChaCha20.Arm.Stream.block_noCalls
  · simp only [Proof.ChaCha20.blockArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), h0, h1]
    exact ⟨trivial, trivial, hdj, hS, hB⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ ?_
    simpa only [Proof.ChaCha20.blockArm, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), h0, h1] using hpost

/-- `vg_chacha20_xor`'s contract, with what its proof shows of `r0` and `r1`
on return. -/
def xorK : Contract isa :=
  { Proof.ChaCha20.xorArm with
    post := fun s s' => Proof.ChaCha20.xorArm.post s s' ∧ s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r3 }

theorem xor_call {s : State} {S D B : BitVec 32} {n : Nat} (h0 : s.gpr .r0 = S) (h1 : s.gpr .r1 = D)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 n) (h3 : s.gpr .r3 = B) (hn : n < 2 ^ 32)
    (hSD : (⟨State.addr S, 64⟩ : Region).Disjoint ⟨State.addr D, n⟩)
    (hSB : (⟨State.addr S, 64⟩ : Region).Disjoint ⟨State.addr B, 320⟩)
    (hDB : (⟨State.addr D, n⟩ : Region).Disjoint ⟨State.addr B, 320⟩)
    (hS : S.toNat + 64 ≤ 2 ^ 32) (hD : D.toNat + n ≤ 2 ^ 32) (hB : B.toNat + 320 ≤ 2 ^ 32)
    (hc : Covers ([] ++ [⟨State.addr S, 64⟩, ⟨State.addr D, n⟩, ⟨State.addr B, 320⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨State.addr S, 64⟩, ⟨State.addr D, n⟩, ⟨State.addr B, 320⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.ChaCha20.Arm.Stream.Kept [⟨State.addr S, 64⟩, ⟨State.addr D, n⟩, ⟨State.addr B, 320⟩] s s' →
      bytesAt s'.mem (State.addr D) n =
        List.zipWith (· ^^^ ·) (bytesAt s.mem (State.addr D) n) (keystream (stateAt s.mem (State.addr S)) n) →
      Q s') :
    WP isa (.call "vg_chacha20_xor" Impl.ChaCha20.Arm.Xor.xor) s Q := by
  have hn' : (BitVec.ofNat 32 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  refine WP.callCalls (k := VG.Proof.ChaCha20.Arm.Stream.xorK) (fun s hs => Proof.ChaCha20.Arm.Xor.xor_regs s hs)
    (rd := []) (wr := [⟨State.addr S, 64⟩, ⟨State.addr D, n⟩, ⟨State.addr B, 320⟩]) ?_ hc hw ?_
    VG.Proof.ChaCha20.Arm.Stream.xor_noFrames
  · simp only [VG.Proof.ChaCha20.Arm.Stream.xorK, Proof.ChaCha20.xorArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.r2 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs), h0, h1, h2, h3, hn']
    exact ⟨trivial, trivial, hSD, hSB, hDB, hS, hD, hB⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [VG.Proof.ChaCha20.Arm.Stream.xorK, Proof.ChaCha20.xorArm, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.r2 ∉ linkRegs),
      h0, h1, h2, hn'] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ hpost.1

/-- The regions of the call of `vg_chacha20_xor`: the copy of the state,
the data and the working space. -/
abbrev cpR (s₀ : State) : Region := ⟨VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 192, 64⟩
abbrev blR (s₀ : State) : Region := ⟨VG.Proof.ChaCha20.Arm.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.Arm.Stream.H s₀), 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀⟩
abbrev wkR (s₀ : State) : Region := ⟨VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 256, 320⟩

theorem cpR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.Arm.Stream.cpR s₀) (VG.Proof.ChaCha20.Arm.Stream.stR s₀) := Offset.sub_base _ (by omega)
theorem wkR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.Arm.Stream.wkR s₀) (VG.Proof.ChaCha20.Arm.Stream.stR s₀) := Offset.sub_base _ (by omega)
theorem blR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.Arm.Stream.blR s₀) (VG.Proof.ChaCha20.Arm.Stream.dR s₀) := Offset.sub_base _ (VG.Proof.ChaCha20.Arm.Stream.HNB_le s₀)

end VG.Proof.ChaCha20.Arm.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.Arm.Stream.Apply`. -/
section

/-!
# Streaming ChaCha20 on ARMv7: `apply`, correctness

Untrusted: everything here is checked by Lean. The pieces of `apply`
(`Impl/ChaCha20/Arm/Stream.lean`), each from what holds before it
(`Q0` … `Q3`), and the whole function. The pieces are those that the proof
of constant time (`ApplyCT.lean`) relates in two runs.
-/

namespace VG.Proof.ChaCha20.Arm.Stream

open VG VG.Arm VG.Impl.ChaCha20.Arm.Stream
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr op2_lsl wp_mov wp_add wp_sub wp_and wp_cmp
  wp_ldr wp_str eval_eq ofNat_beq_zero sub_ofNat)
open VG.Proof.ChaCha20.Arm.Xor (imm0 imm1 imm64 sub_zero')
open VG.Spec.ChaCha20 (keyAt restAt leftAt bytesAt stateAt serialize block)

/-! ## The check -/

/-- After the check: Z is whether fewer than `len` bytes are left. -/
structure Q0 (s₀ s : State) : Prop where
  z : s.z = decide (VG.Proof.ChaCha20.Arm.Stream.N s₀ < VG.Proof.ChaCha20.Arm.Stream.L s₀)
  keep : ∀ r, r ≠ .r3 → r ≠ .r12 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem N_eq (s₀ : State) : VG.Proof.ChaCha20.Arm.Stream.N s₀ = (s₀.mem.readW (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 128) 32).toNat +
    2 ^ 32 * (s₀.mem.readW (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 132) 32).toNat := by
  simp only [VG.Proof.ChaCha20.Arm.Stream.N, leftAt]
  rw [show (VG.Proof.ChaCha20.Arm.Stream.st s₀ + 128 : Addr) = VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 128 from rfl, readW64_toNat, Offset.add_add]

/-- The flag the check leaves: whether `a + 2³² b < l`, from the carries of
`a - l` and `b - 1`. -/
theorem check_z (a b l : BitVec 32) :
    (((0 + 0 + if decide (l.toNat ≤ a.toNat) = true then (1 : BitVec 32) else 0) + 0 +
      if decide (BitVec.toNat (1 : BitVec 32) ≤ b.toNat) = true then 1 else 0) - 0 == 0) =
      decide (a.toNat + 2 ^ 32 * b.toNat < l.toNat) := by
  have := l.isLt
  have e : (1 : BitVec 32).toNat = 1 := rfl
  by_cases h₁ : l.toNat ≤ a.toNat <;> by_cases h₂ : BitVec.toNat (1 : BitVec 32) ≤ b.toNat <;>
    simp only [h₁, h₂, decide_true, decide_false, ite_true] <;>
    first | (rw [decide_eq_false (by omega)]; decide) | (rw [decide_eq_true (by omega)]; decide)

set_option simprocs false in
theorem check_ok {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Stream.APre s₀) : WP isa (.block check) s₀ (VG.Proof.ChaCha20.Arm.Stream.Q0 s₀) := by
  have e₁ := hp.eaS (d := 128) (by decide); have e₂ := hp.eaS (d := 132) (by decide)
  have j₁ := hp.r_st (d := 128) (n := 4) (by decide); have j₂ := hp.r_st (d := 132) (n := 4) (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [check, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval,
    State.load32, State.setReg, subFlags, e₁, e₂, j₁, j₂, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r h₁ h₂ => by simp [h₁, h₂], rfl, rfl, rfl, rfl⟩
  refine (VG.Proof.ChaCha20.Arm.Stream.check_z (s₀.mem.readW (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 128) 32) (s₀.mem.readW (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 132) 32)
    (s₀.gpr .r2)).trans ?_
  rw [VG.Proof.ChaCha20.Arm.Stream.N_eq]

/-- What `apply` guarantees (`applyArm`), and the registers it keeps. -/
def Final (s₀ s : State) : Prop := abiPreserved s₀ s ∧ Proof.ChaCha20.applyArm.post s₀ s

theorem fail_ok {s₀ : State} (hlt : VG.Proof.ChaCha20.Arm.Stream.N s₀ < VG.Proof.ChaCha20.Arm.Stream.L s₀) {s : State} (h : VG.Proof.ChaCha20.Arm.Stream.Q0 s₀ s) :
    WP isa (.block [.mov .r0 (.imm 0)]) s (VG.Proof.ChaCha20.Arm.Stream.Final s₀) := by
  refine wp_mov (op2_imm imm0) fun s' u => WP.block_nil ⟨⟨fun r hr => ?_, by rw [u.sp, h.sp]⟩, ?_⟩
  · rw [u.other r (preserved_ne hr).1, h.keep r (preserved_ne hr).2.2.2.1 (preserved_ne hr).2.2.2.2]
  · show keyAt _ _ = _ ∧ _
    rw [ite_neg (show ¬ VG.Proof.ChaCha20.Arm.Stream.L s₀ ≤ VG.Proof.ChaCha20.Arm.Stream.N s₀ by omega), u.mem, h.mem]
    exact ⟨rfl, u.gpr, rfl, rfl⟩

/-! ## The bytes left in the buffered block -/

/-- `and` with 63: the remainder modulo 64. -/
theorem and_63 (x : BitVec 32) : x &&& (63 : BitVec 32) = BitVec.ofNat 32 (x.toNat % 64) := by
  have : (63 : BitVec 32) = BitVec.ofNat 32 (2 ^ 6 - 1) := by decide
  rw [this]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 2 ^ 6 - 1 < 2 ^ 32 by decide), Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- Our caller's `r4`–`r7`, our return address, and the bytes left after
`apply`. -/
structure Saved (s₀ : State) (m : Mem) : Prop where
  r4 : m.readW (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 576) 32 = s₀.gpr .r4
  r5 : m.readW (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 580) 32 = s₀.gpr .r5
  r6 : m.readW (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 584) 32 = s₀.gpr .r6
  r7 : m.readW (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 588) 32 = s₀.gpr .r7
  lr : m.readW (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 592) 32 = s₀.gpr .lr
  lo : m.readW (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 600) 32 = BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Stream.N s₀ - VG.Proof.ChaCha20.Arm.Stream.L s₀)
  hi : m.readW (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 604) 32 = BitVec.ofNat 32 ((VG.Proof.ChaCha20.Arm.Stream.N s₀ - VG.Proof.ChaCha20.Arm.Stream.L s₀) / 2 ^ 32)

/-- Where they are. -/
abbrev savR (s₀ : State) : Region := ⟨VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 576, 32⟩

theorem savR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.Arm.Stream.savR s₀) (VG.Proof.ChaCha20.Arm.Stream.stR s₀) := Offset.sub_base _ (by omega)

theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : VG.Proof.ChaCha20.Arm.Stream.Saved s₀ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (VG.Proof.ChaCha20.Arm.Stream.savR s₀).Disjoint r) : VG.Proof.ChaCha20.Arm.Stream.Saved s₀ m' := by
  have c : ∀ d, 576 ≤ d → d + 4 ≤ 608 → (VG.Proof.ChaCha20.Arm.Stream.savR s₀).Contains (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 d) (32 / 8) :=
    fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
  exact ⟨by rw [hf.readW (c 576 (by decide) (by decide)) hd (by decide), h.r4],
    by rw [hf.readW (c 580 (by decide) (by decide)) hd (by decide), h.r5],
    by rw [hf.readW (c 584 (by decide) (by decide)) hd (by decide), h.r6],
    by rw [hf.readW (c 588 (by decide) (by decide)) hd (by decide), h.r7],
    by rw [hf.readW (c 592 (by decide) (by decide)) hd (by decide), h.lr],
    by rw [hf.readW (c 600 (by decide) (by decide)) hd (by decide), h.lo],
    by rw [hf.readW (c 604 (by decide) (by decide)) hd (by decide), h.hi]⟩

/-- The state of memory before the data is touched. -/
structure Mid (s₀ : State) (m : Mem) : Prop where
  keep : ∀ i < 136, m (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 i) = s₀.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 i)
  saved : VG.Proof.ChaCha20.Arm.Stream.Saved s₀ m

theorem Mid.state {s₀ : State} {m : Mem} (h : VG.Proof.ChaCha20.Arm.Stream.Mid s₀ m) : stateAt m (VG.Proof.ChaCha20.Arm.Stream.st s₀) = VG.Proof.ChaCha20.Arm.Stream.S0 s₀ :=
  stateAt_congr fun i hi => h.keep i (by omega)

/-- The memory after `start`'s stores. -/
def startMem (m : Mem) (st : Addr) (a b c d e lo hi : BitVec 32) : Mem :=
  ((((((m.writeW (st + BitVec.ofNat 64 576) a).writeW (st + BitVec.ofNat 64 580) b).writeW
    (st + BitVec.ofNat 64 584) c).writeW (st + BitVec.ofNat 64 588) d).writeW (st + BitVec.ofNat 64 592) e).writeW
    (st + BitVec.ofNat 64 600) lo).writeW (st + BitVec.ofNat 64 604) hi

theorem startMem_frame (m : Mem) (st : Addr) (a b c d e lo hi : BitVec 32) :
    Frame [⟨st, 768⟩] m (VG.Proof.ChaCha20.Arm.Stream.startMem m st a b c d e lo hi) := by
  have c : ∀ d, d + 4 ≤ 768 → (⟨st, 768⟩ : Region).Contains (st + BitVec.ofNat 64 d) (32 / 8) :=
    fun d hd => Offset.contains_base _ hd (by omega)
  exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 576 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 580 (by decide))).writeW (List.mem_singleton_self _) _
    (c 584 (by decide))).writeW (List.mem_singleton_self _) _ (c 588 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 592 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 600 (by decide))).writeW (List.mem_singleton_self _) _ (c 604 (by decide))

theorem startMem_byte (m : Mem) (st : Addr) (a b c d e lo hi : BitVec 32) {i : Nat} (hi' : i < 576) :
    (VG.Proof.ChaCha20.Arm.Stream.startMem m st a b c d e lo hi) (st + BitVec.ofNat 64 i) = m (st + BitVec.ofNat 64 i) := by
  simp only [VG.Proof.ChaCha20.Arm.Stream.startMem]
  rw [byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
    byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
    byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
    byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega)]

theorem startMem_read (m : Mem) (st : Addr) (a b c d e lo hi : BitVec 32) {k : Nat} (hk : k + 4 ≤ 576) :
    (VG.Proof.ChaCha20.Arm.Stream.startMem m st a b c d e lo hi).readW (st + BitVec.ofNat 64 k) 32 = m.readW (st + BitVec.ofNat 64 k) 32 := by
  simp only [VG.Proof.ChaCha20.Arm.Stream.startMem]
  rw [readW_writeW_ofNat _ _ _ (by omega) (by omega) (by omega) (by omega),
    readW_writeW_ofNat _ _ _ (by omega) (by omega) (by omega) (by omega),
    readW_writeW_ofNat _ _ _ (by omega) (by omega) (by omega) (by omega),
    readW_writeW_ofNat _ _ _ (by omega) (by omega) (by omega) (by omega),
    readW_writeW_ofNat _ _ _ (by omega) (by omega) (by omega) (by omega),
    readW_writeW_ofNat _ _ _ (by omega) (by omega) (by omega) (by omega),
    readW_writeW_ofNat _ _ _ (by omega) (by omega) (by omega) (by omega)]

set_option simprocs false in
theorem startMem_saved (s₀ : State) :
    VG.Proof.ChaCha20.Arm.Stream.Saved s₀ (VG.Proof.ChaCha20.Arm.Stream.startMem s₀.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀) (s₀.gpr .r4) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r7) (s₀.gpr .lr)
      (BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Stream.N s₀ - VG.Proof.ChaCha20.Arm.Stream.L s₀)) (BitVec.ofNat 32 ((VG.Proof.ChaCha20.Arm.Stream.N s₀ - VG.Proof.ChaCha20.Arm.Stream.L s₀) / 2 ^ 32))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp (config := {decide := true}) only [VG.Proof.ChaCha20.Arm.Stream.startMem, Mem.readW_writeW_self32, readW_writeW_ofNat]

/-- The low word of the bytes left after `apply`. -/
theorem left_lo {a b l : BitVec 32} {n : Nat} (hn : n = a.toNat + 2 ^ 32 * b.toNat) (h : l.toNat ≤ n) :
    a - l = BitVec.ofNat 32 (n - l.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt; have := l.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- And its high word, from the borrow of the low word. -/
theorem left_hi {a b l : BitVec 32} {n : Nat} (hn : n = a.toNat + 2 ^ 32 * b.toNat) (h : l.toNat ≤ n) :
    b + ((65535 : BitVec 16) ++ BitVec.extractLsb' 0 16 (BitVec.setWidth 32 (65535 : BitVec 16))) +
      (if decide (l.toNat ≤ a.toNat) = true then 1 else 0) = BitVec.ofNat 32 ((n - l.toNat) / 2 ^ 32) := by
  rw [show ((65535 : BitVec 16) ++ BitVec.extractLsb' 0 16 (BitVec.setWidth 32 (65535 : BitVec 16)) : BitVec 32) =
    BitVec.ofNat 32 (2 ^ 32 - 1) by apply BitVec.eq_of_toNat_eq; simp]
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt; have hb := b.isLt; have hl := l.isLt
  have e1 : (BitVec.ofNat 32 (2 ^ 32 - 1)).toNat = 2 ^ 32 - 1 := rfl
  have e2 : (BitVec.ofNat 32 ((n - l.toNat) / 2 ^ 32)).toNat = (n - l.toNat) / 2 ^ 32 % 2 ^ 32 :=
    BitVec.toNat_ofNat _ _
  rw [BitVec.toNat_add, BitVec.toNat_add, e1, e2]
  by_cases hc : l.toNat ≤ a.toNat
  · rw [show (if decide (l.toNat ≤ a.toNat) = true then (1 : BitVec 32) else 0).toNat = 1 by simp [hc]]
    omega
  · rw [show (if decide (l.toNat ≤ a.toNat) = true then (1 : BitVec 32) else 0).toNat = 0 by simp [hc]]
    omega

def startA : List Instr :=
  [.str .r4 .r0 576, .str .r5 .r0 580, .str .r6 .r0 584, .str .r7 .r0 588, .str .lr .r0 592,
   .ldr .r3 .r0 128, .ldr .r12 .r0 132, .subs .r3 .r3 (.reg .r2), .movw .r4 0xffff, .movt .r4 0xffff,
   .adc .r12 .r12 (.reg .r4), .str .r3 .r0 600, .str .r12 .r0 604]

def startB : List Instr :=
  [.mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2),
   .ldr .r12 .r4 128, .dp .and .r12 .r12 (.imm 63), .cmp .r12 (.reg .r6), .mov .r0 (.imm 0),
   .adc .r0 .r0 (.imm 0), .cmp .r0 (.imm 0), .mov .r2 (.reg .r6)]

theorem start_eq : start = VG.Proof.ChaCha20.Arm.Stream.startA ++ VG.Proof.ChaCha20.Arm.Stream.startB := rfl

set_option simprocs false in
theorem startA_ok {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Stream.APre s₀) (hle : VG.Proof.ChaCha20.Arm.Stream.L s₀ ≤ VG.Proof.ChaCha20.Arm.Stream.N s₀) {s : State} (h : VG.Proof.ChaCha20.Arm.Stream.Q0 s₀ s) :
    WP isa (.block VG.Proof.ChaCha20.Arm.Stream.startA) s fun s' =>
      s'.mem = VG.Proof.ChaCha20.Arm.Stream.startMem s₀.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀) (s₀.gpr .r4) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r7) (s₀.gpr .lr)
        (BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Stream.N s₀ - VG.Proof.ChaCha20.Arm.Stream.L s₀)) (BitVec.ofNat 32 ((VG.Proof.ChaCha20.Arm.Stream.N s₀ - VG.Proof.ChaCha20.Arm.Stream.L s₀) / 2 ^ 32)) ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → s'.gpr r = s₀.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have e : ∀ d, d < 768 → State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 d :=
    fun d hd => by rw [h.keep .r0 (by decide) (by decide)]; exact hp.eaS hd
  have o : ∀ d, d + 4 ≤ 768 → InRegions s.wr (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [h.wr]; exact hp.w_st hd
  have i : ∀ d, d + 4 ≤ 768 → InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [h.rd, h.wr]; exact hp.r_st hd
  have e576 := e 576 (by decide); have e580 := e 580 (by decide); have e584 := e 584 (by decide)
  have e588 := e 588 (by decide); have e592 := e 592 (by decide); have e600 := e 600 (by decide)
  have e604 := e 604 (by decide); have e128 := e 128 (by decide); have e132 := e 132 (by decide)
  have o576 := o 576 (by decide); have o580 := o 580 (by decide); have o584 := o 584 (by decide)
  have o588 := o 588 (by decide); have o592 := o 592 (by decide); have o600 := o 600 (by decide)
  have o604 := o 604 (by decide); have i128 := i 128 (by decide); have i132 := i 132 (by decide)
  have k4 := h.keep .r4 (by decide) (by decide); have k5 := h.keep .r5 (by decide) (by decide)
  have k6 := h.keep .r6 (by decide) (by decide); have k7 := h.keep .r7 (by decide) (by decide)
  have kl := h.keep .lr (by decide) (by decide); have k2 := h.keep .r2 (by decide) (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [VG.Proof.ChaCha20.Arm.Stream.startA, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval,
    State.load32, State.store32, State.setReg, subFlags, e576, e580, e584, e588, e592, e600, e604, e128, e132,
    o576, o580, o584, o588, o592, o600, o604, i128, i132, k4, k5, k6, k7, kl, k2, h.mem, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left', readW_writeW_ofNat]
  refine ⟨?_, fun r h₁ h₂ h₃ => ?_, trivial⟩
  · rw [VG.Proof.ChaCha20.Arm.Stream.left_lo (VG.Proof.ChaCha20.Arm.Stream.N_eq s₀) hle, VG.Proof.ChaCha20.Arm.Stream.left_hi (VG.Proof.ChaCha20.Arm.Stream.N_eq s₀) hle]
    rfl
  · simp only [h₁, h₂, h₃, ite_false]
    exact h.keep r h₁ h₃

/-- The callee-saved registers our code never writes. -/
def kept : List Reg := [.r8, .r9, .r10, .r11]

theorem kept_ne {r : Reg} (hr : r ∈ VG.Proof.ChaCha20.Arm.Stream.kept) {r' : Reg} (h : r' ∉ VG.Proof.ChaCha20.Arm.Stream.kept := by decide) : r ≠ r' :=
  fun e => h (e ▸ hr)

/-- After `start`, with `x` in `r2`. -/
structure R1 (s₀ : State) (x : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = VG.Proof.ChaCha20.Arm.Stream.ST s₀
  r5 : s.gpr .r5 = VG.Proof.ChaCha20.Arm.Stream.DP s₀
  r6 : s.gpr .r6 = BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Stream.L s₀)
  r2 : s.gpr .r2 = BitVec.ofNat 32 x
  r12 : s.gpr .r12 = BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Stream.O s₀)
  keep : ∀ r ∈ VG.Proof.ChaCha20.Arm.Stream.kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mid : VG.Proof.ChaCha20.Arm.Stream.Mid s₀ s.mem
  done : VG.Proof.ChaCha20.Arm.Stream.Done s₀ 0 s.mem
  frame : Frame [VG.Proof.ChaCha20.Arm.Stream.stR s₀] s₀.mem s.mem

theorem lo_mod (s₀ : State) : (s₀.mem.readW (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 128) 32).toNat % 64 = VG.Proof.ChaCha20.Arm.Stream.O s₀ := by
  simp only [VG.Proof.ChaCha20.Arm.Stream.O]
  rw [VG.Proof.ChaCha20.Arm.Stream.N_eq]
  omega

/-- The carry of `cmp`, moved into a register by `adc` of zeros, compared
with zero. -/
theorem carry_z (x y : Nat) : ((0 + 0 + if decide (x ≤ y) = true then (1 : BitVec 32) else 0) - 0 == 0) =
    decide (y < x) := by
  by_cases h : x ≤ y
  · simp only [h, decide_true, ite_true]; rw [decide_eq_false (by omega)]; decide
  · simp only [h, decide_false]; rw [decide_eq_true (by omega)]; decide

set_option simprocs false in
theorem startB_ok {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Stream.APre s₀) {s : State} (h0 : s.gpr .r0 = VG.Proof.ChaCha20.Arm.Stream.ST s₀) (h1 : s.gpr .r1 = VG.Proof.ChaCha20.Arm.Stream.DP s₀)
    (h2 : s.gpr .r2 = s₀.gpr .r2) (hk : ∀ r ∈ VG.Proof.ChaCha20.Arm.Stream.kept, s.gpr r = s₀.gpr r)
    (hm : s.mem = VG.Proof.ChaCha20.Arm.Stream.startMem s₀.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀) (s₀.gpr .r4) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r7) (s₀.gpr .lr)
        (BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Stream.N s₀ - VG.Proof.ChaCha20.Arm.Stream.L s₀)) (BitVec.ofNat 32 ((VG.Proof.ChaCha20.Arm.Stream.N s₀ - VG.Proof.ChaCha20.Arm.Stream.L s₀) / 2 ^ 32)))
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hsp : s.sp = s₀.sp) :
    WP isa (.block VG.Proof.ChaCha20.Arm.Stream.startB) s fun s' => VG.Proof.ChaCha20.Arm.Stream.R1 s₀ (VG.Proof.ChaCha20.Arm.Stream.L s₀) s' ∧ s'.z = decide (VG.Proof.ChaCha20.Arm.Stream.O s₀ < VG.Proof.ChaCha20.Arm.Stream.L s₀) := by
  have hf := VG.Proof.ChaCha20.Arm.Stream.startMem_frame s₀.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀) (s₀.gpr .r4) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r7) (s₀.gpr .lr)
    (BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Stream.N s₀ - VG.Proof.ChaCha20.Arm.Stream.L s₀)) (BitVec.ofNat 32 ((VG.Proof.ChaCha20.Arm.Stream.N s₀ - VG.Proof.ChaCha20.Arm.Stream.L s₀) / 2 ^ 32))
  have e₁ := hp.eaS (d := 128) (by decide)
  have i₁ : InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 128) 4 := by
    rw [hrd, hwr]; exact hp.r_st (by decide)
  have v₁ := VG.Proof.ChaCha20.Arm.Stream.startMem_read s₀.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀) (s₀.gpr .r4) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r7) (s₀.gpr .lr)
    (BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Stream.N s₀ - VG.Proof.ChaCha20.Arm.Stream.L s₀)) (BitVec.ofNat 32 ((VG.Proof.ChaCha20.Arm.Stream.N s₀ - VG.Proof.ChaCha20.Arm.Stream.L s₀) / 2 ^ 32)) (k := 128) (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [VG.Proof.ChaCha20.Arm.Stream.startB, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval,
    State.load32, State.setReg, subFlags, h0, h1, h2, e₁, i₁, hm, v₁, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left', VG.Proof.ChaCha20.Arm.Stream.and_63, VG.Proof.ChaCha20.Arm.Stream.lo_mod]
  have hO : VG.Proof.ChaCha20.Arm.Stream.O s₀ < 2 ^ 32 := by have := VG.Proof.ChaCha20.Arm.Stream.O_lt s₀; omega
  have hL : s₀.gpr .r2 = BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Stream.L s₀) := by simp [VG.Proof.ChaCha20.Arm.Stream.L]
  refine ⟨⟨rfl, rfl, hL, hL, rfl, fun r hr => ?_, hrd, hwr, hsp,
    ⟨fun i hi => VG.Proof.ChaCha20.Arm.Stream.startMem_byte _ _ _ _ _ _ _ _ _ (by omega), VG.Proof.ChaCha20.Arm.Stream.startMem_saved s₀⟩, fun k hk => ?_, hm ▸ hf⟩, ?_⟩
  · simp only [VG.Proof.ChaCha20.Arm.Stream.kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) only [ite_false] <;>
      exact hk _ (by simp [VG.Proof.ChaCha20.Arm.Stream.kept])
  · dsimp only
    rw [hf.bytes (R := VG.Proof.ChaCha20.Arm.Stream.dR s₀) (by simpa using hp.st_d.symm) (show VG.Proof.ChaCha20.Arm.Stream.L s₀ ≤ 2 ^ 64 by have := VG.Proof.ChaCha20.Arm.Stream.L_lt s₀; omega) hk]
    simp
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hO, VG.Proof.ChaCha20.Arm.Stream.carry_z]

theorem start_ok {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Stream.APre s₀) (hle : VG.Proof.ChaCha20.Arm.Stream.L s₀ ≤ VG.Proof.ChaCha20.Arm.Stream.N s₀) {s : State} (h : VG.Proof.ChaCha20.Arm.Stream.Q0 s₀ s) :
    WP isa (.block start) s fun s' => VG.Proof.ChaCha20.Arm.Stream.R1 s₀ (VG.Proof.ChaCha20.Arm.Stream.L s₀) s' ∧ s'.z = decide (VG.Proof.ChaCha20.Arm.Stream.O s₀ < VG.Proof.ChaCha20.Arm.Stream.L s₀) := by
  rw [VG.Proof.ChaCha20.Arm.Stream.start_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.ChaCha20.Arm.Stream.startA_ok hp hle h) fun s₁ ⟨m₁, g₁, r₁, w₁, p₁⟩ => VG.Proof.ChaCha20.Arm.Stream.startB_ok hp
    (by rw [g₁ _ (by decide) (by decide) (by decide)]) (by rw [g₁ _ (by decide) (by decide) (by decide)])
    (by rw [g₁ _ (by decide) (by decide) (by decide)])
    (fun r hr => g₁ r (VG.Proof.ChaCha20.Arm.Stream.kept_ne hr) (VG.Proof.ChaCha20.Arm.Stream.kept_ne hr) (VG.Proof.ChaCha20.Arm.Stream.kept_ne hr)) m₁ (by rw [r₁, h.rd]) (by rw [w₁, h.wr])
    (by rw [p₁, h.sp])

theorem sel_ok {s₀ : State} {s : State} (h : VG.Proof.ChaCha20.Arm.Stream.R1 s₀ (VG.Proof.ChaCha20.Arm.Stream.L s₀) s) (hz : s.z = decide (VG.Proof.ChaCha20.Arm.Stream.O s₀ < VG.Proof.ChaCha20.Arm.Stream.L s₀)) :
    WP isa (.ite .eq (.block [.mov .r2 (.reg .r12)]) (.block [])) s (VG.Proof.ChaCha20.Arm.Stream.R1 s₀ (VG.Proof.ChaCha20.Arm.Stream.H s₀)) := by
  refine WP.ite (decide (VG.Proof.ChaCha20.Arm.Stream.O s₀ < VG.Proof.ChaCha20.Arm.Stream.L s₀)) (by have e : isa.eval .eq s = some s.z := eval_eq s; rw [e, hz]) (fun hlt => ?_) (fun hge => ?_)
  · simp only [decide_eq_true_eq] at hlt
    refine wp_mov (op2_reg _ _) fun s' u => WP.block_nil ?_
    exact ⟨by rw [u.other _ (by decide), h.r4], by rw [u.other _ (by decide), h.r5],
      by rw [u.other _ (by decide), h.r6],
      by rw [u.gpr, h.r12, VG.Proof.ChaCha20.Arm.Stream.H, headLen, bufLeft, Nat.min_eq_left (Nat.le_of_lt hlt)],
      by rw [u.other _ (by decide), h.r12],
      fun r hr => by rw [u.other r (VG.Proof.ChaCha20.Arm.Stream.kept_ne hr)]; exact h.keep r hr,
      by rw [u.rd, h.rd], by rw [u.wr, h.wr], by rw [u.sp, h.sp], u.mem ▸ h.mid, u.mem ▸ h.done,
      u.mem ▸ h.frame⟩
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hge
    refine WP.block_nil (M := isa) ⟨h.r4, h.r5, h.r6, ?_, h.r12, h.keep, h.rd, h.wr, h.sp, h.mid, h.done,
      h.frame⟩
    rw [h.r2, VG.Proof.ChaCha20.Arm.Stream.H, headLen, bufLeft, Nat.min_eq_right hge]

/-- After `part1`: the bytes from the buffered block XORed, and `r2` the
bytes of the whole blocks, Z whether there are none. -/
structure Q1 (s₀ s : State) : Prop where
  r4 : s.gpr .r4 = VG.Proof.ChaCha20.Arm.Stream.ST s₀
  r5 : s.gpr .r5 = VG.Proof.ChaCha20.Arm.Stream.DP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Stream.H s₀)
  r6 : s.gpr .r6 = BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Stream.L s₀ - VG.Proof.ChaCha20.Arm.Stream.H s₀)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀)
  z : s.z = decide (64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀ = 0)
  keep : ∀ r ∈ VG.Proof.ChaCha20.Arm.Stream.kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mid : VG.Proof.ChaCha20.Arm.Stream.Mid s₀ s.mem
  done : VG.Proof.ChaCha20.Arm.Stream.Done s₀ (VG.Proof.ChaCha20.Arm.Stream.H s₀) s.mem
  frame : Frame [VG.Proof.ChaCha20.Arm.Stream.stR s₀, VG.Proof.ChaCha20.Arm.Stream.dR s₀] s₀.mem s.mem

/-- `(x >>> 6) <<< 6` rounds down to a multiple of 64. -/
theorem round64 {x : Nat} (hx : x < 2 ^ 32) :
    (BitVec.ofNat 32 x >>> 6) <<< 6 = BitVec.ofNat 32 (64 * (x / 64)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem part1_eq : part1 = .seq (.block start)
    (.seq (.ite .eq (.block [.mov .r2 (.reg .r12)]) (.block []))
    (.seq (.block [.dp .add .r3 .r4 (.imm 128), .dp .sub .r3 .r3 (.reg .r12), .dp .sub .r6 .r6 (.reg .r2)])
    (.seq xorBytes (.block [.mov .r2 (.shifted .r6 .lsr 6), .mov .r2 (.shifted .r2 .lsl 6), .cmp .r2 (.imm 0)])))) :=
  rfl

/-- After the bytes left in the buffered block to use are chosen. -/
def rest1 : Prog isa :=
  .seq (.block [.dp .add .r3 .r4 (.imm 128), .dp .sub .r3 .r3 (.reg .r12), .dp .sub .r6 .r6 (.reg .r2)])
    (.seq xorBytes (.block [.mov .r2 (.shifted .r6 .lsr 6), .mov .r2 (.shifted .r2 .lsl 6), .cmp .r2 (.imm 0)]))

theorem rest1_ok {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Stream.APre s₀) {s₂ : State} (h₂ : VG.Proof.ChaCha20.Arm.Stream.R1 s₀ (VG.Proof.ChaCha20.Arm.Stream.H s₀) s₂) :
    WP isa VG.Proof.ChaCha20.Arm.Stream.rest1 s₂ (VG.Proof.ChaCha20.Arm.Stream.Q1 s₀) := by
  have hL := VG.Proof.ChaCha20.Arm.Stream.L_lt s₀
  have hH := VG.Proof.ChaCha20.Arm.Stream.H_le s₀
  have hHO := VG.Proof.ChaCha20.Arm.Stream.H_le_O s₀
  have hO := VG.Proof.ChaCha20.Arm.Stream.O_lt s₀
  have hst := hp.st_fit
  have hd := hp.d_fit
  -- The pointer to the bytes left in the buffered block, and the length left.
  refine WP.seq (wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_sub (op2_reg _ _) fun s₄ u₄ =>
    wp_sub (op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_)
  have hK : s₅.gpr .r3 = VG.Proof.ChaCha20.Arm.Stream.ST s₀ + BitVec.ofNat 32 (128 - VG.Proof.ChaCha20.Arm.Stream.O s₀) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₃.other .r12 (by decide), h₂.r4, h₂.r12,
      show (128 : BitVec 32) = BitVec.ofNat 32 (128 - VG.Proof.ChaCha20.Arm.Stream.O s₀) + BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Stream.O s₀) by
        rw [BitVec.ofNat_add_ofNat, show 128 - VG.Proof.ChaCha20.Arm.Stream.O s₀ + VG.Proof.ChaCha20.Arm.Stream.O s₀ = 128 by omega]; rfl,
      ← BitVec.add_assoc, BitVec.add_sub_cancel]
  have g : ∀ r, r ≠ .r3 → r ≠ .r6 → s₅.gpr r = s₂.gpr r := fun r h₁ h₂ => by
    rw [u₅.other r h₂, u₄.other r h₁, u₃.other r h₁]
  have hm₅ : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  have hr6 : s₅.gpr .r6 = BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Stream.L s₀ - VG.Proof.ChaCha20.Arm.Stream.H s₀) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), h₂.r6, u₄.other _ (by decide),
      u₃.other _ (by decide), h₂.r2, sub_ofNat hH]
  have eK : State.addr (VG.Proof.ChaCha20.Arm.Stream.ST s₀ + BitVec.ofNat 32 (128 - VG.Proof.ChaCha20.Arm.Stream.O s₀)) = VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 (128 - VG.Proof.ChaCha20.Arm.Stream.O s₀) :=
    hp.eaS (by omega)
  have hb : VG.Proof.ChaCha20.Arm.Stream.BPre s₅ (VG.Proof.ChaCha20.Arm.Stream.DP s₀) (VG.Proof.ChaCha20.Arm.Stream.ST s₀ + BitVec.ofNat 32 (128 - VG.Proof.ChaCha20.Arm.Stream.O s₀)) (VG.Proof.ChaCha20.Arm.Stream.H s₀) :=
    ⟨by rw [g _ (by decide) (by decide), h₂.r5], hK, by rw [g _ (by decide) (by decide), h₂.r2],
      by omega, by rw [hp.sNat (by omega)]; omega,
      fun k hk => by rw [u₅.wr, u₄.wr, u₃.wr, h₂.wr]; exact VG.Proof.ChaCha20.Arm.Stream.dR_byte hp (by omega),
      fun k hk => by
        rw [u₅.rd, u₄.rd, u₃.rd, u₅.wr, u₄.wr, u₃.wr, h₂.rd, h₂.wr, eK, Offset.add_add]
        exact hp.r_st (by omega),
      fun j hj k hk => by rw [eK, Offset.add_add]; exact VG.Proof.ChaCha20.Arm.Stream.d_ne_st hp (by omega) (by omega)⟩
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.Stream.xorBytes_ok hb) fun s₆ h₆ => ?_)
  refine wp_mov (op2_lsr (by decide)) fun s₇ u₇ => wp_mov (op2_lsl (by decide)) fun s₈ u₈ =>
    wp_cmp (n := .r2) (op2_imm imm0) fun s₉ f₉ hz => WP.block_nil ?_
  have g' : ∀ r, r ≠ .r2 → s₉.gpr r = s₆.gpr r := fun r hr => by
    rw [f₉.gpr, u₈.other r hr, u₇.other r hr]
  have hm : s₉.mem = s₆.mem := by rw [f₉.mem, u₈.mem, u₇.mem]
  have hnb : 64 * ((VG.Proof.ChaCha20.Arm.Stream.L s₀ - VG.Proof.ChaCha20.Arm.Stream.H s₀) / 64) = 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀ := by simp only [VG.Proof.ChaCha20.Arm.Stream.NB, blocksOf, VG.Proof.ChaCha20.Arm.Stream.H]
  have hr2 : s₉.gpr .r2 = BitVec.ofNat 32 (64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀) := by
    rw [f₉.gpr, u₈.gpr, u₇.gpr, h₆.keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hr6,
      VG.Proof.ChaCha20.Arm.Stream.round64 (by omega), hnb]
  have kp : ∀ r ∈ VG.Proof.ChaCha20.Arm.Stream.kept, s₉.gpr r = s₀.gpr r := fun r hr => by
    rw [g' r (VG.Proof.ChaCha20.Arm.Stream.kept_ne hr), h₆.keep r (VG.Proof.ChaCha20.Arm.Stream.kept_ne hr) (VG.Proof.ChaCha20.Arm.Stream.kept_ne hr) (VG.Proof.ChaCha20.Arm.Stream.kept_ne hr) (VG.Proof.ChaCha20.Arm.Stream.kept_ne hr) (VG.Proof.ChaCha20.Arm.Stream.kept_ne hr),
      g r (VG.Proof.ChaCha20.Arm.Stream.kept_ne hr) (VG.Proof.ChaCha20.Arm.Stream.kept_ne hr)]
    exact h₂.keep r hr
  refine ⟨by rw [g' _ (by decide), h₆.keep _ (by decide) (by decide) (by decide) (by decide) (by decide),
      g _ (by decide) (by decide), h₂.r4],
    by rw [g' _ (by decide), h₆.r5], by rw [g' _ (by decide), h₆.keep _ (by decide) (by decide) (by decide)
      (by decide) (by decide), hr6], hr2,
    by rw [hz, ← congrFun f₉.gpr .r2, hr2, sub_zero', ofNat_beq_zero (by omega)], kp,
    by rw [f₉.rd, u₈.rd, u₇.rd, h₆.rd, u₅.rd, u₄.rd, u₃.rd, h₂.rd],
    by rw [f₉.wr, u₈.wr, u₇.wr, h₆.wr, u₅.wr, u₄.wr, u₃.wr, h₂.wr],
    by rw [f₉.sp, u₈.sp, u₇.sp, h₆.sp, u₅.sp, u₄.sp, u₃.sp, h₂.sp], ⟨fun i hi => ?_, ?_⟩, fun k hk => ?_, ?_⟩
  · rw [hm, h₆.frame _ fun r hr hc => ?_, hm₅]
    · exact h₂.mid.keep i hi
    · simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_d _ (Offset.contains_base (VG.Proof.ChaCha20.Arm.Stream.st s₀) (d := i) (n := 1) (k := 768) (by omega) (by omega))
        (Offset.sub_base (VG.Proof.ChaCha20.Arm.Stream.dp s₀) (d := 0) (n := VG.Proof.ChaCha20.Arm.Stream.H s₀) (k := VG.Proof.ChaCha20.Arm.Stream.L s₀) (by omega) _ (by simpa using hc))
  · rw [hm]
    refine (hm₅ ▸ h₂.mid.saved).frame h₆.frame fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.st_d.sub_left (VG.Proof.ChaCha20.Arm.Stream.savR_sub s₀)).sub_right fun x hx => by
      simpa using Offset.sub_base (VG.Proof.ChaCha20.Arm.Stream.dp s₀) (d := 0) (n := VG.Proof.ChaCha20.Arm.Stream.H s₀) (k := VG.Proof.ChaCha20.Arm.Stream.L s₀) (by omega) x (by simpa using hx)
  · rw [hm]
    by_cases hk' : k < VG.Proof.ChaCha20.Arm.Stream.H s₀
    · rw [h₆.data k hk', hm₅, h₂.done k hk, eK, Offset.add_add, h₂.mid.keep _ (by omega)]
      simp [hk', VG.Proof.ChaCha20.Arm.Stream.KS]
    · rw [h₆.frame _ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.ChaCha20.Arm.Stream.not_in_prefix _ (by omega) (by omega),
        hm₅, h₂.done k hk]
      simp [hk']
  · rw [hm]
    exact (hm₅ ▸ h₂.frame.mono (by simp)).trans (h₆.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.ChaCha20.Arm.Stream.dR s₀, by simp, VG.Proof.ChaCha20.Arm.Stream.prefix_sub _ hH⟩)

theorem part1_ok {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Stream.APre s₀) (hle : VG.Proof.ChaCha20.Arm.Stream.L s₀ ≤ VG.Proof.ChaCha20.Arm.Stream.N s₀) {s : State} (h : VG.Proof.ChaCha20.Arm.Stream.Q0 s₀ s) :
    WP isa part1 s (VG.Proof.ChaCha20.Arm.Stream.Q1 s₀) := by
  rw [VG.Proof.ChaCha20.Arm.Stream.part1_eq]
  exact WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.Stream.start_ok hp hle h) fun s₁ ⟨h₁, hz₁⟩ =>
    WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.Stream.sel_ok h₁ hz₁) fun s₂ h₂ => VG.Proof.ChaCha20.Arm.Stream.rest1_ok hp h₂))

/-! ## The whole blocks -/

/-- After `part2`: the whole blocks XORed, and the counter advanced past
them. -/
structure Q2 (s₀ s : State) : Prop where
  r4 : s.gpr .r4 = VG.Proof.ChaCha20.Arm.Stream.ST s₀
  r5 : s.gpr .r5 = VG.Proof.ChaCha20.Arm.Stream.DP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Stream.H s₀ + 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀)
  r6 : s.gpr .r6 = BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Stream.T s₀)
  keep : ∀ r ∈ VG.Proof.ChaCha20.Arm.Stream.kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  state : stateAt s.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀) = ctr (VG.Proof.ChaCha20.Arm.Stream.S0 s₀) (VG.Proof.ChaCha20.Arm.Stream.NB s₀)
  buf : ∀ i < 64, s.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 (64 + i)) = s₀.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 (64 + i))
  saved : VG.Proof.ChaCha20.Arm.Stream.Saved s₀ s.mem
  done : VG.Proof.ChaCha20.Arm.Stream.Done s₀ (VG.Proof.ChaCha20.Arm.Stream.H s₀ + 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀) s.mem
  frame : Frame [VG.Proof.ChaCha20.Arm.Stream.stR s₀, VG.Proof.ChaCha20.Arm.Stream.dR s₀] s₀.mem s.mem

theorem nb_zero_ok {s₀ : State} {s : State} (h : VG.Proof.ChaCha20.Arm.Stream.Q1 s₀ s) (h0 : 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀ = 0) : VG.Proof.ChaCha20.Arm.Stream.Q2 s₀ s := by
  have hT := VG.Proof.ChaCha20.Arm.Stream.T_eq s₀
  refine ⟨h.r4, by rw [h.r5, h0, Nat.add_zero], by rw [h.r6, hT, h0, Nat.sub_zero], h.keep, h.rd, h.wr, h.sp,
    by rw [h.mid.state, show VG.Proof.ChaCha20.Arm.Stream.NB s₀ = 0 by omega, ctr_zero], fun i hi => h.mid.keep _ (by omega), h.mid.saved,
    by rw [h0, Nat.add_zero]; exact h.done, h.frame⟩

/-- The callee-saved registers are kept by the calls, but for `lr`. -/
theorem kept_cs : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11], r ∈ preserved ∧ r ≠ .lr := by decide

def ctrInstrs : List Instr :=
  [.ldr .r0 .r4 48, .mov .r1 (.shifted .r2 .lsr 6), .dp .add .r0 .r0 (.reg .r1), .str .r0 .r4 48,
   .mov .r7 (.reg .r2), .dp .add .r0 .r4 (.imm 192), .mov .r1 (.reg .r5), .dp .add .r3 .r4 (.imm 256)]

theorem blocksArgs_eq : blocksArgs = copyWords .r0 .r4 .r4 0 192 16 ++ VG.Proof.ChaCha20.Arm.Stream.ctrInstrs := rfl

theorem shr_nb {nb : Nat} (h : 64 * nb < 2 ^ 32) : BitVec.ofNat 32 (64 * nb) >>> 6 = BitVec.ofNat 32 nb := by
  rw [VG.Proof.MdStream.Arm.shr6 h, show 64 * nb / 64 = nb by omega]

/-- The arguments of the call of `vg_chacha20_xor`. -/
structure Args (s₀ s : State) : Prop where
  r0 : s.gpr .r0 = VG.Proof.ChaCha20.Arm.Stream.ST s₀ + BitVec.ofNat 32 192
  r1 : s.gpr .r1 = VG.Proof.ChaCha20.Arm.Stream.DP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Stream.H s₀)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀)
  r3 : s.gpr .r3 = VG.Proof.ChaCha20.Arm.Stream.ST s₀ + BitVec.ofNat 32 256
  r7 : s.gpr .r7 = BitVec.ofNat 32 (64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀)
  rd : s.rd = []
  wr : s.wr = [VG.Proof.ChaCha20.Arm.Stream.stR s₀, VG.Proof.ChaCha20.Arm.Stream.dR s₀]

theorem args_ok {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Stream.APre s₀) {s : State} (h : VG.Proof.ChaCha20.Arm.Stream.Q1 s₀ s) :
    WP isa (.block blocksArgs) s fun s₉ => VG.Proof.ChaCha20.Arm.Stream.Args s₀ s₉ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r3 → r ≠ .r7 → s₉.gpr r = s.gpr r) ∧ s₉.sp = s₀.sp ∧
      stateAt s₉.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀) = ctr (VG.Proof.ChaCha20.Arm.Stream.S0 s₀) (VG.Proof.ChaCha20.Arm.Stream.NB s₀) ∧ stateAt s₉.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 192) = VG.Proof.ChaCha20.Arm.Stream.S0 s₀ ∧
      Frame [VG.Proof.ChaCha20.Arm.Stream.cpR s₀, ⟨VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 48, 4⟩] s.mem s₉.mem := by
  have hL := VG.Proof.ChaCha20.Arm.Stream.L_lt s₀
  have hH := VG.Proof.ChaCha20.Arm.Stream.H_le s₀
  have hHNB := VG.Proof.ChaCha20.Arm.Stream.HNB_le s₀
  have hT := VG.Proof.ChaCha20.Arm.Stream.T_eq s₀
  have hst := hp.st_fit
  have hd := hp.d_fit
  have hrw : s.rd ++ s.wr = [VG.Proof.ChaCha20.Arm.Stream.stR s₀, VG.Proof.ChaCha20.Arm.Stream.dR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr, List.nil_append]
  have hc : CPre s .r0 .r4 .r4 (VG.Proof.ChaCha20.Arm.Stream.ST s₀) (VG.Proof.ChaCha20.Arm.Stream.ST s₀) 0 192 16 :=
    ⟨h.r4, h.r4, by decide, by decide, by omega, by omega, by decide, by decide,
      fun i n' hi => by rw [hrw]; exact ⟨VG.Proof.ChaCha20.Arm.Stream.stR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩,
      fun i n' hi => by rw [h.wr]; exact hp.w_st (by omega),
      Offset.disjoint _ (by omega) (by omega) (by omega)⟩
  rw [VG.Proof.ChaCha20.Arm.Stream.blocksArgs_eq, WP.block_append_iff]
  refine WP.mono (copy_ok hc) fun s₁ h₁ => ?_
  have r4₁ : s₁.gpr .r4 = VG.Proof.ChaCha20.Arm.Stream.ST s₀ := by rw [h₁.gpr _ (by decide), h.r4]
  have rd₁ : s₁.rd ++ s₁.wr = [VG.Proof.ChaCha20.Arm.Stream.stR s₀, VG.Proof.ChaCha20.Arm.Stream.dR s₀] := by rw [h₁.rd, h₁.wr, hrw]
  have c48 : (VG.Proof.ChaCha20.Arm.Stream.stR s₀).Contains (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 48) 4 := Offset.contains_base _ (by omega) (by omega)
  unfold VG.Proof.ChaCha20.Arm.Stream.ctrInstrs
  refine wp_ldr (a := VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 48) (by decide) (by rw [r4₁]; exact hp.eaS (by decide))
    (by rw [rd₁]; exact ⟨VG.Proof.ChaCha20.Arm.Stream.stR s₀, by simp, c48⟩) fun s₂ u₂ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₃ u₃ => wp_add (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_str (a := VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 48) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), r4₁]; exact hp.eaS (by decide))
    (by rw [u₄.wr, u₃.wr, u₂.wr, h₁.wr, h.wr]; exact hp.w_st (by decide)) fun s₅ g₅ => ?_
  refine wp_mov (op2_reg _ _) fun s₆ u₆ => wp_add (op2_imm (by decide)) fun s₇ u₇ =>
    wp_mov (op2_reg _ _) fun s₈ u₈ => wp_add (op2_imm (by decide)) fun s₉ u₉ => WP.block_nil ?_
  -- What the registers and memory are before the call.
  have g : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r3 → r ≠ .r7 → s₉.gpr r = s.gpr r := fun r a b c d => by
    rw [u₉.other r c, u₈.other r b, u₇.other r a, u₆.other r d, g₅.gpr, u₄.other r a, u₃.other r b,
      u₂.other r a, h₁.gpr r a]
  have r4₉ : s₉.gpr .r4 = VG.Proof.ChaCha20.Arm.Stream.ST s₀ := by rw [g _ (by decide) (by decide) (by decide) (by decide), h.r4]
  have r2₉ : s₉.gpr .r2 = BitVec.ofNat 32 (64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀) := by
    rw [g _ (by decide) (by decide) (by decide) (by decide), h.r2]
  have hm₉ : s₉.mem = s₁.mem.writeW (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 48)
      (s₁.mem.readW (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 48) 32 + BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Stream.NB s₀)) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, g₅.mem, u₄.gpr, u₃.gpr, u₃.other .r0 (by decide), u₂.gpr,
      u₂.other .r2 (by decide), h₁.gpr .r2 (by decide), h.r2, VG.Proof.ChaCha20.Arm.Stream.shr_nb (by omega), u₄.mem, u₃.mem, u₂.mem]
  have x0 : s₉.gpr .r0 = VG.Proof.ChaCha20.Arm.Stream.ST s₀ + BitVec.ofNat 32 192 := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), r4₁]; rfl
  have x1 : s₉.gpr .r1 = VG.Proof.ChaCha20.Arm.Stream.DP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Stream.H s₀) := by
    rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h₁.gpr _ (by decide), h.r5]
  have x3 : s₉.gpr .r3 = VG.Proof.ChaCha20.Arm.Stream.ST s₀ + BitVec.ofNat 32 256 := by
    rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), r4₁]; rfl
  have x7 : s₉.gpr .r7 = BitVec.ofNat 32 (64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀) := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h₁.gpr _ (by decide), h.r2]
  have hrd₉ : s₉.rd = [] := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, g₅.rd, u₄.rd, u₃.rd, u₂.rd, h₁.rd, h.rd, hp.rd]
  have hwr₉ : s₉.wr = [VG.Proof.ChaCha20.Arm.Stream.stR s₀, VG.Proof.ChaCha20.Arm.Stream.dR s₀] := by
    rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, g₅.wr, u₄.wr, u₃.wr, u₂.wr, h₁.wr, h.wr, hp.wr]
  have hsp₉ : s₉.sp = s₀.sp := by rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, g₅.sp, u₄.sp, u₃.sp, u₂.sp, h₁.sp, h.sp]
  have f₁ : Frame [VG.Proof.ChaCha20.Arm.Stream.cpR s₀] s.mem s₁.mem := h₁.frame
  have f₉ : Frame [⟨VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 48, 4⟩] s₁.mem s₉.mem := by
    rw [hm₉]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have st₁ : stateAt s₁.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀) = VG.Proof.ChaCha20.Arm.Stream.S0 s₀ := by
    rw [Proof.ChaCha20.Arm.Xor.stateAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.base_disjoint _ (by omega) (by omega)),
      h.mid.state]
  have e12 : s₁.mem.readW (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 48) 32 = (VG.Proof.ChaCha20.Arm.Stream.S0 s₀)[12] := by
    rw [← st₁]; simp [stateAt]
  have st₉ : stateAt s₉.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀) = ctr (VG.Proof.ChaCha20.Arm.Stream.S0 s₀) (VG.Proof.ChaCha20.Arm.Stream.NB s₀) := by
    rw [hm₉, Proof.ChaCha20.Arm.Xor.stateAt_writeW_counter, st₁, e12]; rfl
  have cp₉ : stateAt s₉.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 192) = VG.Proof.ChaCha20.Arm.Stream.S0 s₀ := by
    refine stateAt_congr fun i hi => ?_
    rw [Offset.add_add, hm₉, byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega)]
    have := h₁.copied i (by omega)
    rw [Nat.zero_add] at this
    rw [this]
    exact h.mid.keep i (by omega)
  have fc : Frame [VG.Proof.ChaCha20.Arm.Stream.cpR s₀, ⟨VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 48, 4⟩] s.mem s₉.mem :=
    (f₁.mono (by simp)).trans (f₉.mono (by simp))
  exact ⟨⟨x0, x1, r2₉, x3, x7, hrd₉, hwr₉⟩, g, hsp₉, st₉, cp₉, fc⟩

theorem blocks_ok {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Stream.APre s₀) {s : State} (h : VG.Proof.ChaCha20.Arm.Stream.Q1 s₀ s) (hnb : 0 < VG.Proof.ChaCha20.Arm.Stream.NB s₀) :
    WP isa (.seq (.block blocksArgs) (.seq (.call "vg_chacha20_xor" Impl.ChaCha20.Arm.Xor.xor)
      (.block [.dp .add .r5 .r5 (.reg .r7), .dp .sub .r6 .r6 (.reg .r7)]))) s (VG.Proof.ChaCha20.Arm.Stream.Q2 s₀) := by
  have hL := VG.Proof.ChaCha20.Arm.Stream.L_lt s₀
  have hH := VG.Proof.ChaCha20.Arm.Stream.H_le s₀
  have hHNB := VG.Proof.ChaCha20.Arm.Stream.HNB_le s₀
  have hT := VG.Proof.ChaCha20.Arm.Stream.T_eq s₀
  have hst := hp.st_fit
  have hd := hp.d_fit
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.Stream.args_ok hp h) fun s₉ ⟨⟨x0, x1, r2₉, x3, x7, hrd₉, hwr₉⟩, g, hsp₉, st₉, cp₉, fc⟩ =>
    ?_)
  have r4₉ : s₉.gpr .r4 = VG.Proof.ChaCha20.Arm.Stream.ST s₀ := by rw [g _ (by decide) (by decide) (by decide) (by decide), h.r4]
  have e192 := hp.eaS (d := 192) (by decide)
  have e256 := hp.eaS (d := 256) (by decide)
  have eH := hp.eaD (d := VG.Proof.ChaCha20.Arm.Stream.H s₀) (by omega)
  have dSD : (VG.Proof.ChaCha20.Arm.Stream.cpR s₀).Disjoint (VG.Proof.ChaCha20.Arm.Stream.blR s₀) := (hp.st_d.sub_left (VG.Proof.ChaCha20.Arm.Stream.cpR_sub s₀)).sub_right (VG.Proof.ChaCha20.Arm.Stream.blR_sub s₀)
  have dSB : (VG.Proof.ChaCha20.Arm.Stream.cpR s₀).Disjoint (VG.Proof.ChaCha20.Arm.Stream.wkR s₀) := Offset.disjoint _ (by omega) (by omega) (by omega)
  have dDB : (VG.Proof.ChaCha20.Arm.Stream.blR s₀).Disjoint (VG.Proof.ChaCha20.Arm.Stream.wkR s₀) := (hp.st_d.sub_left (VG.Proof.ChaCha20.Arm.Stream.wkR_sub s₀)).symm.sub_left (VG.Proof.ChaCha20.Arm.Stream.blR_sub s₀)
  have hcov : ∀ r ∈ [VG.Proof.ChaCha20.Arm.Stream.cpR s₀, VG.Proof.ChaCha20.Arm.Stream.blR s₀, VG.Proof.ChaCha20.Arm.Stream.wkR s₀], ∃ r' ∈ [VG.Proof.ChaCha20.Arm.Stream.stR s₀, VG.Proof.ChaCha20.Arm.Stream.dR s₀], ∃ o,
      r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.ChaCha20.Arm.Stream.stR s₀, by simp, 192, rfl, by simp⟩
    · exact ⟨VG.Proof.ChaCha20.Arm.Stream.dR s₀, by simp, VG.Proof.ChaCha20.Arm.Stream.H s₀, rfl, hHNB⟩
    · exact ⟨VG.Proof.ChaCha20.Arm.Stream.stR s₀, by simp, 256, rfl, by simp⟩
  refine WP.seq (VG.Proof.ChaCha20.Arm.Stream.xor_call (n := 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀) x0 x1 r2₉ x3 (by omega)
    (by rw [e192, eH]; exact dSD) (by rw [e192, e256]; exact dSB) (by rw [eH, e256]; exact dDB)
    (by rw [hp.sNat (by decide)]; omega) (by rw [hp.dNat (by omega)]; omega) (by rw [hp.sNat (by decide)]; omega)
    (by rw [hrd₉, hwr₉, List.nil_append, List.nil_append, e192, eH, e256]; exact Covers.of_sub hcov)
    (by rw [hwr₉, e192, eH, e256]; exact Covers.of_sub hcov) fun s₁₀ k₁₀ x₁₀ => ?_)
  rw [e192, eH, e256] at k₁₀
  rw [e192, eH] at x₁₀
  refine wp_add (op2_reg _ _) fun s₁₁ u₁₁ => wp_sub (op2_reg _ _) fun s₁₂ u₁₂ => WP.block_nil ?_
  have gc : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11], s₁₀.gpr r = s₉.gpr r := fun r hr =>
    k₁₀.cs r (VG.Proof.ChaCha20.Arm.Stream.kept_cs r hr).1 (VG.Proof.ChaCha20.Arm.Stream.kept_cs r hr).2
  have g₁₂ : ∀ r, r ≠ .r5 → r ≠ .r6 → s₁₂.gpr r = s₁₀.gpr r := fun r a b => by
    rw [u₁₂.other r b, u₁₁.other r a]
  have hm : s₁₂.mem = s₁₀.mem := by rw [u₁₂.mem, u₁₁.mem]
  -- Regions the call does not write.
  have nd : ∀ R : Region, R.Disjoint (VG.Proof.ChaCha20.Arm.Stream.cpR s₀) → R.Disjoint (VG.Proof.ChaCha20.Arm.Stream.blR s₀) → R.Disjoint (VG.Proof.ChaCha20.Arm.Stream.wkR s₀) →
      ∀ r ∈ [VG.Proof.ChaCha20.Arm.Stream.cpR s₀, VG.Proof.ChaCha20.Arm.Stream.blR s₀, VG.Proof.ChaCha20.Arm.Stream.wkR s₀], R.Disjoint r := by
    intro R h₁ h₂ h₃ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [h₁, h₂, h₃]
  have c48s : Region.Sub ⟨VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 48, 4⟩ (VG.Proof.ChaCha20.Arm.Stream.stR s₀) := Offset.sub_base _ (by omega)
  have stS : Region.Sub ⟨VG.Proof.ChaCha20.Arm.Stream.st s₀, 64⟩ (VG.Proof.ChaCha20.Arm.Stream.stR s₀) := VG.Proof.ChaCha20.Arm.Stream.prefix_sub _ (by omega)
  have bufS : Region.Sub ⟨VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 64, 64⟩ (VG.Proof.ChaCha20.Arm.Stream.stR s₀) := Offset.sub_base _ (by omega)
  have svS := VG.Proof.ChaCha20.Arm.Stream.savR_sub s₀
  have sd : ∀ R, Region.Sub R (VG.Proof.ChaCha20.Arm.Stream.stR s₀) → R.Disjoint (VG.Proof.ChaCha20.Arm.Stream.blR s₀) := fun R hR =>
    (hp.st_d.sub_left hR).sub_right (VG.Proof.ChaCha20.Arm.Stream.blR_sub s₀)
  have ds : ∀ R R', Region.Sub R (VG.Proof.ChaCha20.Arm.Stream.dR s₀) → Region.Sub R' (VG.Proof.ChaCha20.Arm.Stream.stR s₀) → R.Disjoint R' := fun R R' h₁ h₂ =>
    (hp.st_d.symm.sub_left h₁).sub_right h₂
  refine ⟨by rw [g₁₂ _ (by decide) (by decide), gc .r4 (by simp), r4₉], ?_, ?_, fun r hr => ?_,
    by rw [u₁₂.rd, u₁₁.rd, k₁₀.rd, hrd₉, hp.rd], by rw [u₁₂.wr, u₁₁.wr, k₁₀.wr, hwr₉, hp.wr],
    by rw [u₁₂.sp, u₁₁.sp, k₁₀.sp, hsp₉], ?_, fun i hi => ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [u₁₂.other _ (by decide), u₁₁.gpr, gc .r5 (by simp), gc .r7 (by simp), x7,
      g _ (by decide) (by decide) (by decide) (by decide), h.r5, BitVec.add_assoc, BitVec.ofNat_add]
  · rw [u₁₂.gpr, u₁₁.other _ (by decide), gc .r6 (by simp), u₁₁.other _ (by decide), gc .r7 (by simp), x7,
      g _ (by decide) (by decide) (by decide) (by decide), h.r6, sub_ofNat (by omega), hT, Nat.sub_sub]
  · rw [g₁₂ r (VG.Proof.ChaCha20.Arm.Stream.kept_ne hr) (VG.Proof.ChaCha20.Arm.Stream.kept_ne hr),
      gc r (by
        simp only [VG.Proof.ChaCha20.Arm.Stream.kept, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl <;> simp),
      g r (VG.Proof.ChaCha20.Arm.Stream.kept_ne hr) (VG.Proof.ChaCha20.Arm.Stream.kept_ne hr) (VG.Proof.ChaCha20.Arm.Stream.kept_ne hr) (VG.Proof.ChaCha20.Arm.Stream.kept_ne hr)]
    exact h.keep r hr
  · rw [hm, Proof.ChaCha20.Arm.Xor.stateAt_frame k₁₀.frame (nd _
        (Offset.base_disjoint _ (by omega) (by omega)) (sd _ stS)
        (Offset.base_disjoint _ (by omega) (by omega))), st₉]
  · rw [hm, ← Offset.add_add, k₁₀.frame.bytes (R := ⟨VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 64, 64⟩) (nd _
        (Offset.disjoint _ (by omega) (by omega) (by omega)) (sd _ bufS)
        (Offset.disjoint _ (by omega) (by omega) (by omega))) (show 64 ≤ 2 ^ 64 by decide) hi,
      fc.bytes (R := ⟨VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 64, 64⟩) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.disjoint _ (by omega) (by omega) (by omega)
        · exact Offset.disjoint _ (by omega) (by omega) (by omega)) (show 64 ≤ 2 ^ 64 by decide) hi,
      Offset.add_add]
    exact h.mid.keep _ (by omega)
  · rw [hm]
    refine (h.mid.saved.frame fc fun r hr => ?_).frame k₁₀.frame (nd _ ?_ (sd _ svS) ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · rw [hm]
    have fcd : s₉.mem (VG.Proof.ChaCha20.Arm.Stream.dp s₀ + BitVec.ofNat 64 k) = s.mem (VG.Proof.ChaCha20.Arm.Stream.dp s₀ + BitVec.ofNat 64 k) :=
      fc.bytes (R := VG.Proof.ChaCha20.Arm.Stream.dR s₀) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ds _ _ (fun _ h => h) (VG.Proof.ChaCha20.Arm.Stream.cpR_sub s₀)
        · exact ds _ _ (fun _ h => h) c48s) (show VG.Proof.ChaCha20.Arm.Stream.L s₀ ≤ 2 ^ 64 by omega) hk
    by_cases hk₁ : k < VG.Proof.ChaCha20.Arm.Stream.H s₀
    · have hpre : Region.Sub ⟨VG.Proof.ChaCha20.Arm.Stream.dp s₀, VG.Proof.ChaCha20.Arm.Stream.H s₀⟩ (VG.Proof.ChaCha20.Arm.Stream.dR s₀) := VG.Proof.ChaCha20.Arm.Stream.prefix_sub _ hH
      rw [k₁₀.frame.bytes (R := ⟨VG.Proof.ChaCha20.Arm.Stream.dp s₀, VG.Proof.ChaCha20.Arm.Stream.H s₀⟩) (nd _ (ds _ _ hpre (VG.Proof.ChaCha20.Arm.Stream.cpR_sub s₀))
          (Offset.base_disjoint _ (by omega) (by omega)) (ds _ _ hpre (VG.Proof.ChaCha20.Arm.Stream.wkR_sub s₀)))
          (show VG.Proof.ChaCha20.Arm.Stream.H s₀ ≤ 2 ^ 64 by omega) hk₁]
      rw [fcd, h.done k hk, ite_pos hk₁, ite_pos (by omega)]
    by_cases hk₂ : k < VG.Proof.ChaCha20.Arm.Stream.H s₀ + 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀
    · have e := xor_getD (length_keystream _ _) x₁₀ (j := k - VG.Proof.ChaCha20.Arm.Stream.H s₀) (by omega)
      rw [Offset.add_add, show VG.Proof.ChaCha20.Arm.Stream.H s₀ + (k - VG.Proof.ChaCha20.Arm.Stream.H s₀) = k by omega, fcd, h.done k hk, ite_neg hk₁, cp₉,
        keystream_getD _ (by omega)] at e
      rw [e, ite_pos hk₂]
      simp only [VG.Proof.ChaCha20.Arm.Stream.KS, ite_neg hk₁]
    · have hR : Region.Sub ⟨VG.Proof.ChaCha20.Arm.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.Arm.Stream.H s₀ + 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀), VG.Proof.ChaCha20.Arm.Stream.L s₀ - (VG.Proof.ChaCha20.Arm.Stream.H s₀ + 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀)⟩ (VG.Proof.ChaCha20.Arm.Stream.dR s₀) :=
        Offset.sub_base _ (by omega)
      have := k₁₀.frame.bytes (R := ⟨VG.Proof.ChaCha20.Arm.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.Arm.Stream.H s₀ + 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀), VG.Proof.ChaCha20.Arm.Stream.L s₀ - (VG.Proof.ChaCha20.Arm.Stream.H s₀ + 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀)⟩)
        (nd _ (ds _ _ hR (VG.Proof.ChaCha20.Arm.Stream.cpR_sub s₀)) (Offset.disjoint _ (by omega) (by omega) (by omega))
          (ds _ _ hR (VG.Proof.ChaCha20.Arm.Stream.wkR_sub s₀))) (show VG.Proof.ChaCha20.Arm.Stream.L s₀ - (VG.Proof.ChaCha20.Arm.Stream.H s₀ + 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀) ≤ 2 ^ 64 by omega)
          (i := k - (VG.Proof.ChaCha20.Arm.Stream.H s₀ + 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀)) (by simp only; omega)
      rw [Offset.add_add, show VG.Proof.ChaCha20.Arm.Stream.H s₀ + 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀ + (k - (VG.Proof.ChaCha20.Arm.Stream.H s₀ + 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀)) = k by omega] at this
      rw [this, fcd, h.done k hk, ite_neg hk₁, ite_neg hk₂]
  · rw [hm]
    refine (h.frame.trans (fc.sub fun r hr => ?_)).trans (k₁₀.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.ChaCha20.Arm.Stream.stR s₀, by simp, VG.Proof.ChaCha20.Arm.Stream.cpR_sub s₀⟩
      · exact ⟨VG.Proof.ChaCha20.Arm.Stream.stR s₀, by simp, c48s⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨VG.Proof.ChaCha20.Arm.Stream.stR s₀, by simp, VG.Proof.ChaCha20.Arm.Stream.cpR_sub s₀⟩
      · exact ⟨VG.Proof.ChaCha20.Arm.Stream.dR s₀, by simp, VG.Proof.ChaCha20.Arm.Stream.blR_sub s₀⟩
      · exact ⟨VG.Proof.ChaCha20.Arm.Stream.stR s₀, by simp, VG.Proof.ChaCha20.Arm.Stream.wkR_sub s₀⟩

theorem part2_ok {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Stream.APre s₀) {s : State} (h : VG.Proof.ChaCha20.Arm.Stream.Q1 s₀ s) : WP isa part2 s (VG.Proof.ChaCha20.Arm.Stream.Q2 s₀) := by
  have hL := VG.Proof.ChaCha20.Arm.Stream.L_lt s₀
  have hHNB := VG.Proof.ChaCha20.Arm.Stream.HNB_le s₀
  refine WP.ite (decide (64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀ = 0)) (by have e : isa.eval .eq s = some s.z := eval_eq s; rw [e, h.z])
    (fun h0 => WP.block_nil (M := isa) (VG.Proof.ChaCha20.Arm.Stream.nb_zero_ok h (by simpa using h0)))
    (fun h0 => VG.Proof.ChaCha20.Arm.Stream.blocks_ok hp h (by simp at h0; omega))

/-! ## The last bytes -/

/-- After `part3`: all the data XORed; the counter advanced past the block
started, if any, which is buffered. -/
structure Q3 (s₀ s : State) : Prop where
  r4 : s.gpr .r4 = VG.Proof.ChaCha20.Arm.Stream.ST s₀
  keep : ∀ r ∈ VG.Proof.ChaCha20.Arm.Stream.kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  state : stateAt s.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀) = ctr (VG.Proof.ChaCha20.Arm.Stream.S0 s₀) (VG.Proof.ChaCha20.Arm.Stream.NB s₀ + if VG.Proof.ChaCha20.Arm.Stream.T s₀ = 0 then 0 else 1)
  buf : ∀ i < 64, s.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 (64 + i)) =
    if VG.Proof.ChaCha20.Arm.Stream.T s₀ = 0 then s₀.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 (64 + i))
    else (serialize (block (ctr (VG.Proof.ChaCha20.Arm.Stream.S0 s₀) (VG.Proof.ChaCha20.Arm.Stream.NB s₀)))).getD i 0
  saved : VG.Proof.ChaCha20.Arm.Stream.Saved s₀ s.mem
  done : VG.Proof.ChaCha20.Arm.Stream.Done s₀ (VG.Proof.ChaCha20.Arm.Stream.L s₀) s.mem
  frame : Frame [VG.Proof.ChaCha20.Arm.Stream.stR s₀, VG.Proof.ChaCha20.Arm.Stream.dR s₀] s₀.mem s.mem

theorem t_zero_ok {s₀ : State} {s : State} (h : VG.Proof.ChaCha20.Arm.Stream.Q2 s₀ s) (h0 : VG.Proof.ChaCha20.Arm.Stream.T s₀ = 0) : VG.Proof.ChaCha20.Arm.Stream.Q3 s₀ s := by
  have hT := VG.Proof.ChaCha20.Arm.Stream.T_eq s₀
  have hHNB := VG.Proof.ChaCha20.Arm.Stream.HNB_le s₀
  refine ⟨h.r4, h.keep, h.rd, h.wr, h.sp, by rw [h.state, h0]; rfl, fun i hi => by rw [h.buf i hi, h0]; rfl,
    h.saved, by rw [show VG.Proof.ChaCha20.Arm.Stream.L s₀ = VG.Proof.ChaCha20.Arm.Stream.H s₀ + 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀ by omega]; exact h.done, h.frame⟩

/-- The buffered block, and the bytes the block function may write. -/
abbrev bufR (s₀ : State) : Region := ⟨VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 64, 256⟩

theorem bufR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.Arm.Stream.bufR s₀) (VG.Proof.ChaCha20.Arm.Stream.stR s₀) := Offset.sub_base _ (by omega)

theorem tailXor_eq : tailXor = .seq (.block [.ldr .r0 .r4 48, .dp .add .r0 .r0 (.imm 1), .str .r0 .r4 48,
    .dp .add .r3 .r4 (.imm 64), .mov .r2 (.reg .r6)]) xorBytes := rfl

theorem tail_ok {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Stream.APre s₀) {s : State} (h : VG.Proof.ChaCha20.Arm.Stream.Q2 s₀ s) (ht : VG.Proof.ChaCha20.Arm.Stream.T s₀ ≠ 0) :
    WP isa (.seq (.block [.mov .r0 (.reg .r4), .dp .add .r1 .r4 (.imm 64)])
      (.seq (.call "vg_chacha20_block" Impl.ChaCha20.Arm.block) tailXor)) s (VG.Proof.ChaCha20.Arm.Stream.Q3 s₀) := by
  have hT := VG.Proof.ChaCha20.Arm.Stream.T_eq s₀
  have hHNB := VG.Proof.ChaCha20.Arm.Stream.HNB_le s₀
  have hL := VG.Proof.ChaCha20.Arm.Stream.L_lt s₀
  have hT64 : VG.Proof.ChaCha20.Arm.Stream.T s₀ < 64 := Nat.mod_lt _ (by decide)
  have hst := hp.st_fit
  have hd := hp.d_fit
  refine WP.seq (wp_mov (op2_reg _ _) fun s' u => wp_add (op2_imm (by decide)) fun s₁ u₁ => WP.block_nil ?_)
  have x0₁ : s₁.gpr .r0 = VG.Proof.ChaCha20.Arm.Stream.ST s₀ := by rw [u₁.other _ (by decide), u.gpr, h.r4]
  have x1₁ : s₁.gpr .r1 = VG.Proof.ChaCha20.Arm.Stream.ST s₀ + BitVec.ofNat 32 64 := by rw [u₁.gpr, u.other _ (by decide), h.r4]; rfl
  have k₁ : ∀ r, r ≠ .r0 → r ≠ .r1 → s₁.gpr r = s.gpr r := fun r a b => by rw [u₁.other r b, u.other r a]
  have hwr₁ : s₁.wr = [VG.Proof.ChaCha20.Arm.Stream.stR s₀, VG.Proof.ChaCha20.Arm.Stream.dR s₀] := by rw [u₁.wr, u.wr, h.wr, hp.wr]
  have hrd₁ : s₁.rd = [] := by rw [u₁.rd, u.rd, h.rd, hp.rd]
  have e64 := hp.eaS (d := 64) (by decide)
  refine WP.seq (VG.Proof.ChaCha20.Arm.Stream.block_call x0₁ x1₁ (by rw [e64]; exact Offset.disjoint_base _ (by omega) (by omega))
    (by omega) (by rw [hp.sNat (by decide)]; omega)
    (by
      rw [hrd₁, hwr₁, e64]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.ChaCha20.Arm.Stream.stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 768 by decide⟩
      · exact ⟨VG.Proof.ChaCha20.Arm.Stream.stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩)
    (by
      rw [hwr₁, e64]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.ChaCha20.Arm.Stream.stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩) fun s₂ k₂ blk₂ => ?_)
  rw [e64] at k₂ blk₂
  have g : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11], s₂.gpr r = s.gpr r := fun r hr => by
    rw [k₂.cs r (VG.Proof.ChaCha20.Arm.Stream.kept_cs r hr).1 (VG.Proof.ChaCha20.Arm.Stream.kept_cs r hr).2, k₁ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  have r4₂ : s₂.gpr .r4 = VG.Proof.ChaCha20.Arm.Stream.ST s₀ := by rw [g .r4 (by simp), h.r4]
  have hw48 : InRegions s₂.wr (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 48) 4 := by
    rw [k₂.wr, hwr₁]; exact ⟨VG.Proof.ChaCha20.Arm.Stream.stR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hr48 : InRegions (s₂.rd ++ s₂.wr) (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 48) 4 := by
    rw [k₂.rd, hrd₁, List.nil_append]; exact hw48
  rw [VG.Proof.ChaCha20.Arm.Stream.tailXor_eq]
  refine WP.seq (wp_ldr (a := VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 48) (by decide) (by rw [r4₂]; exact hp.eaS (by decide))
    hr48 fun s₃ u₃ => wp_add (op2_imm imm1) fun s₄ u₄ => ?_)
  refine wp_str (a := VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 48) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), r4₂]; exact hp.eaS (by decide))
    (by rw [u₄.wr, u₃.wr]; exact hw48) fun s₅ g₅ => ?_
  refine wp_add (op2_imm (by decide)) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ => WP.block_nil ?_
  have g₇ : ∀ r, r ≠ .r0 → r ≠ .r2 → r ≠ .r3 → s₇.gpr r = s₂.gpr r := fun r a b c => by
    rw [u₇.other r b, u₆.other r c, g₅.gpr, u₄.other r a, u₃.other r a]
  have m₇ : s₇.mem = s₂.mem.writeW (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 48)
      (s₂.mem.readW (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 48) 32 + 1) := by
    rw [u₇.mem, u₆.mem, g₅.mem, u₄.gpr, u₃.gpr, u₄.mem, u₃.mem]
  have rd₇ : s₇.rd = s₂.rd := by rw [u₇.rd, u₆.rd, g₅.rd, u₄.rd, u₃.rd]
  have wr₇ : s₇.wr = s₂.wr := by rw [u₇.wr, u₆.wr, g₅.wr, u₄.wr, u₃.wr]
  have sp₇ : s₇.sp = s₂.sp := by rw [u₇.sp, u₆.sp, g₅.sp, u₄.sp, u₃.sp]
  have eD := hp.eaD (d := VG.Proof.ChaCha20.Arm.Stream.H s₀ + 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀) (by omega)
  have dS : ∀ R R', Region.Sub R (VG.Proof.ChaCha20.Arm.Stream.dR s₀) → Region.Sub R' (VG.Proof.ChaCha20.Arm.Stream.stR s₀) → R.Disjoint R' := fun R R' h₁ h₂ =>
    (hp.st_d.symm.sub_left h₁).sub_right h₂
  have hb : VG.Proof.ChaCha20.Arm.Stream.BPre s₇ (VG.Proof.ChaCha20.Arm.Stream.DP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Stream.H s₀ + 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀)) (VG.Proof.ChaCha20.Arm.Stream.ST s₀ + BitVec.ofNat 32 64) (VG.Proof.ChaCha20.Arm.Stream.T s₀) :=
    ⟨by rw [g₇ _ (by decide) (by decide) (by decide), g .r5 (by simp), h.r5],
      by rw [u₇.other _ (by decide), u₆.gpr, g₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), r4₂]; rfl,
      by rw [u₇.gpr, u₆.other _ (by decide), g₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
        g .r6 (by simp), h.r6],
      by rw [hp.dNat (by omega)]; omega, by rw [hp.sNat (by decide)]; omega,
      fun k hk => by
        rw [wr₇, k₂.wr, hwr₁, eD, Offset.add_add]
        exact ⟨VG.Proof.ChaCha20.Arm.Stream.dR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩,
      fun k hk => by
        rw [rd₇, wr₇, k₂.rd, k₂.wr, hrd₁, hwr₁, List.nil_append, e64, Offset.add_add]
        exact ⟨VG.Proof.ChaCha20.Arm.Stream.stR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩,
      fun j hj k hk => by rw [eD, e64, Offset.add_add, Offset.add_add]; exact VG.Proof.ChaCha20.Arm.Stream.d_ne_st hp (by omega) (by omega)⟩
  refine WP.mono (VG.Proof.ChaCha20.Arm.Stream.xorBytes_ok hb) fun s₈ h₈ => ?_
  have f₂ := k₂.frame
  have f₃ : Frame [⟨VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 48, 4⟩] s₂.mem s₇.mem := by
    rw [m₇]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have f₄ := h₈.frame
  rw [eD] at f₄
  have tR : Region.Sub ⟨VG.Proof.ChaCha20.Arm.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.Arm.Stream.H s₀ + 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀), VG.Proof.ChaCha20.Arm.Stream.T s₀⟩ (VG.Proof.ChaCha20.Arm.Stream.dR s₀) :=
    Offset.sub_base _ (by omega)
  have c48 : Region.Sub ⟨VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 48, 4⟩ (VG.Proof.ChaCha20.Arm.Stream.stR s₀) := Offset.sub_base _ (by omega)
  have stS : Region.Sub ⟨VG.Proof.ChaCha20.Arm.Stream.st s₀, 64⟩ (VG.Proof.ChaCha20.Arm.Stream.stR s₀) := VG.Proof.ChaCha20.Arm.Stream.prefix_sub _ (by omega)
  have hm₁ : s₁.mem = s.mem := by rw [u₁.mem, u.mem]
  rw [hm₁] at f₂ blk₂
  have st₂ : stateAt s₂.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀) = ctr (VG.Proof.ChaCha20.Arm.Stream.S0 s₀) (VG.Proof.ChaCha20.Arm.Stream.NB s₀) := by
    rw [Proof.ChaCha20.Arm.Xor.stateAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by omega) (by omega)), h.state]
  have bb : ∀ i < 64, s₂.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 (64 + i)) =
      (serialize (block (ctr (VG.Proof.ChaCha20.Arm.Stream.S0 s₀) (VG.Proof.ChaCha20.Arm.Stream.NB s₀)))).getD i 0 := by
    intro i hi
    rw [← Offset.add_add, ← serialize_stateAt s₂.mem _ hi, blk₂, h.state]
  have b3 : ∀ i < 64, s₇.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 (64 + i)) = s₂.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 (64 + i)) := by
    intro i hi
    rw [m₇]; exact byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega)
  have b4 : ∀ i < 64, s₈.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 (64 + i)) = s₇.mem (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 (64 + i)) := by
    intro i hi
    rw [← Offset.add_add]
    exact f₄.bytes (R := ⟨VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 64, 64⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dS _ _ tR (Offset.sub_base _ (by omega))).symm) (show 64 ≤ 2 ^ 64 by decide) hi
  refine ⟨?_, fun r hr => ?_, by rw [h₈.rd, rd₇, k₂.rd, hrd₁, hp.rd], by rw [h₈.wr, wr₇, k₂.wr, hwr₁, hp.wr],
    by rw [h₈.sp, sp₇, k₂.sp, u₁.sp, u.sp, h.sp], ?_, fun i hi => ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [h₈.keep _ (by decide) (by decide) (by decide) (by decide) (by decide),
      g₇ _ (by decide) (by decide) (by decide), r4₂]
  · rw [h₈.keep r (VG.Proof.ChaCha20.Arm.Stream.kept_ne hr) (VG.Proof.ChaCha20.Arm.Stream.kept_ne hr) (VG.Proof.ChaCha20.Arm.Stream.kept_ne hr) (VG.Proof.ChaCha20.Arm.Stream.kept_ne hr) (VG.Proof.ChaCha20.Arm.Stream.kept_ne hr),
      g₇ r (VG.Proof.ChaCha20.Arm.Stream.kept_ne hr) (VG.Proof.ChaCha20.Arm.Stream.kept_ne hr) (VG.Proof.ChaCha20.Arm.Stream.kept_ne hr),
      g r (by
        simp only [VG.Proof.ChaCha20.Arm.Stream.kept, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl <;> simp)]
    exact h.keep r hr
  · have e12 : s₂.mem.readW (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 48) 32 = (ctr (VG.Proof.ChaCha20.Arm.Stream.S0 s₀) (VG.Proof.ChaCha20.Arm.Stream.NB s₀))[12] := by
      rw [← st₂]; simp [stateAt]
    rw [Proof.ChaCha20.Arm.Xor.stateAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dS _ _ tR stS).symm),
      m₇, Proof.ChaCha20.Arm.Xor.stateAt_writeW_counter, st₂, e12, ctr_succ, ite_neg ht]
  · rw [b4 i hi, b3 i hi, bb i hi, ite_neg ht]
  · have svS := VG.Proof.ChaCha20.Arm.Stream.savR_sub s₀
    refine ((h.saved.frame f₂ fun r hr => ?_).frame f₃ fun r hr => ?_).frame f₄ fun r hr => ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact (dS _ _ tR svS).symm
  · have dS48 : (VG.Proof.ChaCha20.Arm.Stream.dR s₀).Disjoint ⟨VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 48, 4⟩ := dS _ _ (fun _ h => h) c48
    have back : s₇.mem (VG.Proof.ChaCha20.Arm.Stream.dp s₀ + BitVec.ofNat 64 k) = s.mem (VG.Proof.ChaCha20.Arm.Stream.dp s₀ + BitVec.ofNat 64 k) := by
      rw [f₃.bytes (R := VG.Proof.ChaCha20.Arm.Stream.dR s₀) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dS48)
          (show VG.Proof.ChaCha20.Arm.Stream.L s₀ ≤ 2 ^ 64 by omega) hk,
        f₂.bytes (R := VG.Proof.ChaCha20.Arm.Stream.dR s₀) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact dS _ _ (fun _ h => h) (VG.Proof.ChaCha20.Arm.Stream.bufR_sub s₀)) (show VG.Proof.ChaCha20.Arm.Stream.L s₀ ≤ 2 ^ 64 by omega) hk]
    by_cases hk₁ : k < VG.Proof.ChaCha20.Arm.Stream.H s₀ + 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀
    · rw [f₄.bytes (R := ⟨VG.Proof.ChaCha20.Arm.Stream.dp s₀, VG.Proof.ChaCha20.Arm.Stream.H s₀ + 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint _ (by omega) (by omega)) (show VG.Proof.ChaCha20.Arm.Stream.H s₀ + 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀ ≤ 2 ^ 64 by omega) hk₁,
        back, h.done k hk, ite_pos hk₁, ite_pos hk]
    · have e := h₈.data (k - (VG.Proof.ChaCha20.Arm.Stream.H s₀ + 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀)) (by omega)
      rw [eD, e64, Offset.add_add, Offset.add_add, show VG.Proof.ChaCha20.Arm.Stream.H s₀ + 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀ + (k - (VG.Proof.ChaCha20.Arm.Stream.H s₀ + 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀)) = k by omega,
        back, b3 _ (by omega), bb _ (by omega), h.done k hk, ite_neg hk₁] at e
      rw [e, ite_pos hk]
      simp only [VG.Proof.ChaCha20.Arm.Stream.KS, ite_neg (show ¬ k < VG.Proof.ChaCha20.Arm.Stream.H s₀ by omega)]
      rw [show (k - VG.Proof.ChaCha20.Arm.Stream.H s₀) / 64 = VG.Proof.ChaCha20.Arm.Stream.NB s₀ by omega, show (k - VG.Proof.ChaCha20.Arm.Stream.H s₀) % 64 = k - (VG.Proof.ChaCha20.Arm.Stream.H s₀ + 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀) by omega]
  · refine ((h.frame.trans (f₂.sub fun r hr => ?_)).trans (f₃.sub fun r hr => ?_)).trans
      (f₄.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.ChaCha20.Arm.Stream.stR s₀, by simp, VG.Proof.ChaCha20.Arm.Stream.bufR_sub s₀⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.ChaCha20.Arm.Stream.stR s₀, by simp, c48⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.ChaCha20.Arm.Stream.dR s₀, by simp, tR⟩

theorem cmp6_ok {s₀ : State} {s : State} (h : VG.Proof.ChaCha20.Arm.Stream.Q2 s₀ s) :
    WP isa (.block [.cmp .r6 (.imm 0)]) s fun s₁ => VG.Proof.ChaCha20.Arm.Stream.Q2 s₀ s₁ ∧ s₁.z = decide (VG.Proof.ChaCha20.Arm.Stream.T s₀ = 0) := by
  have hT64 : VG.Proof.ChaCha20.Arm.Stream.T s₀ < 64 := Nat.mod_lt _ (by decide)
  refine wp_cmp (n := .r6) (op2_imm imm0) fun s₁ f₁ hz => WP.block_nil ?_
  exact ⟨⟨by rw [f₁.gpr, h.r4], by rw [f₁.gpr, h.r5], by rw [f₁.gpr, h.r6],
    fun r hr => by rw [f₁.gpr, h.keep r hr], by rw [f₁.rd, h.rd], by rw [f₁.wr, h.wr], by rw [f₁.sp, h.sp],
    by rw [f₁.mem, h.state], fun i hi => by rw [f₁.mem, h.buf i hi], f₁.mem ▸ h.saved, f₁.mem ▸ h.done,
    f₁.mem ▸ h.frame⟩, by rw [hz, h.r6, sub_zero', ofNat_beq_zero (by omega)]⟩

theorem part3_eq : part3 = .seq (.block [.cmp .r6 (.imm 0)]) (.ite .eq (.block [])
    (.seq (.block [.mov .r0 (.reg .r4), .dp .add .r1 .r4 (.imm 64)])
      (.seq (.call "vg_chacha20_block" Impl.ChaCha20.Arm.block) tailXor))) := rfl

theorem part3_ok {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Stream.APre s₀) {s : State} (h : VG.Proof.ChaCha20.Arm.Stream.Q2 s₀ s) : WP isa part3 s (VG.Proof.ChaCha20.Arm.Stream.Q3 s₀) := by
  have hT64 : VG.Proof.ChaCha20.Arm.Stream.T s₀ < 64 := Nat.mod_lt _ (by decide)
  rw [VG.Proof.ChaCha20.Arm.Stream.part3_eq]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.Stream.cmp6_ok h) fun s₁ ⟨h₁, hz⟩ => ?_)
  refine WP.ite (decide (VG.Proof.ChaCha20.Arm.Stream.T s₀ = 0)) (by
      have e : isa.eval .eq s₁ = some s₁.z := eval_eq s₁
      rw [e, hz])
    (fun h0 => WP.block_nil (M := isa) (VG.Proof.ChaCha20.Arm.Stream.t_zero_ok h₁ (by simpa using h0)))
    (fun h0 => VG.Proof.ChaCha20.Arm.Stream.tail_ok hp h₁ (by simpa using h0))

/-! ## The end -/

set_option simprocs false in
theorem finish_ok {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Stream.APre s₀) (hle : VG.Proof.ChaCha20.Arm.Stream.L s₀ ≤ VG.Proof.ChaCha20.Arm.Stream.N s₀) {s : State} (h : VG.Proof.ChaCha20.Arm.Stream.Q3 s₀ s) :
    WP isa (.block finish) s (VG.Proof.ChaCha20.Arm.Stream.Final s₀) := by
  have hL := VG.Proof.ChaCha20.Arm.Stream.L_lt s₀
  have hN := VG.Proof.ChaCha20.Arm.Stream.N_lt s₀
  have e : ∀ d, d < 768 → State.addr (s.gpr .r4 + BitVec.ofNat 32 d) = VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 d :=
    fun d hd => by rw [h.r4]; exact hp.eaS hd
  have w : ∀ d, d + 4 ≤ 768 → InRegions s.wr (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [h.wr]; exact hp.w_st hd
  have r : ∀ d, d + 4 ≤ 768 → InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [h.rd, h.wr]; exact hp.r_st hd
  have e128 := e 128 (by decide); have e132 := e 132 (by decide); have e576 := e 576 (by decide)
  have e580 := e 580 (by decide); have e584 := e 584 (by decide); have e588 := e 588 (by decide)
  have e592 := e 592 (by decide); have e600 := e 600 (by decide); have e604 := e 604 (by decide)
  have o128 := w 128 (by decide); have o132 := w 132 (by decide)
  have i576 := r 576 (by decide); have i580 := r 580 (by decide); have i584 := r 584 (by decide)
  have i588 := r 588 (by decide); have i592 := r 592 (by decide); have i600 := r 600 (by decide)
  have i604 := r 604 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [finish, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval,
    State.load32, State.store32, State.setReg, Option.map_some, Option.some.injEq, exists_eq_left', ite_true,
    ite_false, e128, e132, e576, e580, e584, e588, e592, e600, e604, o128, o132, i576, i580, i584, i588, i592,
    i600, i604, readW_writeW_ofNat, h.saved.lo, h.saved.hi, h.saved.r4, h.saved.r5, h.saved.r6, h.saved.r7,
    h.saved.lr]
  have hfw : Frame [⟨VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 128, 8⟩] s.mem
      ((s.mem.writeW (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Stream.N s₀ - VG.Proof.ChaCha20.Arm.Stream.L s₀))).writeW
        (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 132) (BitVec.ofNat 32 ((VG.Proof.ChaCha20.Arm.Stream.N s₀ - VG.Proof.ChaCha20.Arm.Stream.L s₀) / 2 ^ 32))) :=
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (VG.Proof.ChaCha20.Arm.Stream.st s₀) (e := 128) (d := 128) (k := 8) (by omega) (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains (VG.Proof.ChaCha20.Arm.Stream.st s₀) (e := 128) (d := 132) (k := 8) (by omega) (by omega) (by omega))
  have c128 : Region.Sub ⟨VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 128, 8⟩ (VG.Proof.ChaCha20.Arm.Stream.stR s₀) := Offset.sub_base _ (by omega)
  have hS : stateAt ((s.mem.writeW (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Stream.N s₀ - VG.Proof.ChaCha20.Arm.Stream.L s₀))).writeW
      (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 132) (BitVec.ofNat 32 ((VG.Proof.ChaCha20.Arm.Stream.N s₀ - VG.Proof.ChaCha20.Arm.Stream.L s₀) / 2 ^ 32))) (VG.Proof.ChaCha20.Arm.Stream.st s₀) =
      ctr (VG.Proof.ChaCha20.Arm.Stream.S0 s₀) (VG.Proof.ChaCha20.Arm.Stream.NB s₀ + if VG.Proof.ChaCha20.Arm.Stream.T s₀ = 0 then 0 else 1) := by
    rw [Proof.ChaCha20.Arm.Xor.stateAt_frame hfw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint _ (by omega) (by omega)), h.state]
  refine ⟨⟨fun r hr => ?_, h.sp⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp (config := {decide := true}) only [ite_true, ite_false]
    all_goals exact h.keep _ (by simp [VG.Proof.ChaCha20.Arm.Stream.kept])
  · have hd : ∀ k < VG.Proof.ChaCha20.Arm.Stream.L s₀, ((s.mem.writeW (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Stream.N s₀ - VG.Proof.ChaCha20.Arm.Stream.L s₀))).writeW
        (VG.Proof.ChaCha20.Arm.Stream.st s₀ + BitVec.ofNat 64 132) (BitVec.ofNat 32 ((VG.Proof.ChaCha20.Arm.Stream.N s₀ - VG.Proof.ChaCha20.Arm.Stream.L s₀) / 2 ^ 32)))
        (VG.Proof.ChaCha20.Arm.Stream.dp s₀ + BitVec.ofNat 64 k) = s.mem (VG.Proof.ChaCha20.Arm.Stream.dp s₀ + BitVec.ofNat 64 k) := fun k hk =>
      hfw.bytes (R := VG.Proof.ChaCha20.Arm.Stream.dR s₀) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.st_d.symm.sub_right c128)) (show VG.Proof.ChaCha20.Arm.Stream.L s₀ ≤ 2 ^ 64 by omega) hk
    show keyAt _ _ = _ ∧ _
    refine ⟨Proof.ChaCha20.keyAt_of_ctr hS, ?_⟩
    rw [ite_pos hle]
    refine ⟨by simp (config := {decide := true}), apply_data hle fun k hk => ?_,
      apply_rest hle ?_ hS fun i hi => ?_⟩
    · dsimp only
      rw [hd k hk, h.done k hk, ite_pos hk]
    · dsimp only
      rw [leftAt_halves _ _ (by omega)]
    · dsimp only
      rw [byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
        byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), h.buf i hi]

theorem apply_eq : apply = .seq (.block check)
    (.ite .eq (.block [.mov .r0 (.imm 0)]) (.seq part1 (.seq part2 (.seq part3 (.block finish))))) := rfl

theorem apply_correct {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Stream.APre s₀) : WP isa apply s₀ (VG.Proof.ChaCha20.Arm.Stream.Final s₀) := by
  rw [VG.Proof.ChaCha20.Arm.Stream.apply_eq]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.Stream.check_ok hp) fun s h => ?_)
  refine WP.ite (decide (VG.Proof.ChaCha20.Arm.Stream.N s₀ < VG.Proof.ChaCha20.Arm.Stream.L s₀)) (by
      have e : isa.eval .eq s = some s.z := eval_eq s
      rw [e, h.z])
    (fun hlt => VG.Proof.ChaCha20.Arm.Stream.fail_ok (by simpa using hlt) h) (fun hge => ?_)
  have hle : VG.Proof.ChaCha20.Arm.Stream.L s₀ ≤ VG.Proof.ChaCha20.Arm.Stream.N s₀ := by simp at hge; omega
  exact WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.Stream.part1_ok hp hle h) fun s₁ h₁ => WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.Stream.part2_ok hp h₁) fun s₂ h₂ =>
    WP.seq (WP.mono (VG.Proof.ChaCha20.Arm.Stream.part3_ok hp h₂) fun s₃ h₃ => VG.Proof.ChaCha20.Arm.Stream.finish_ok hp hle h₃)))

end VG.Proof.ChaCha20.Arm.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.Arm.Stream.ApplyCT`. -/
section

/-!
# Streaming ChaCha20 on ARMv7: `apply`, constant time

Untrusted: everything here is checked by Lean. Two runs from states that
agree on the pointers, the length and the number of bytes of keystream left
(which the contract lets `apply` leak) are related piece by piece (`RelCT`):
the taint analysis proves each piece without calls or branches on loaded
values constant time from the registers that hold public values
(`taintRegs`), which correctness determines in each run (`Apply.lean`) from
those public values; the calls of the block function and of
`vg_chacha20_xor` are constant time by their own proofs (`RelCT.call`), their
arguments agreeing; and the branches on Z after the check and in `start`,
`part2` and `part3` are on public values (`RelCT.ite`), as correctness shows.
-/

namespace VG.Proof.ChaCha20.Arm.Stream

open VG VG.Arm VG.Impl.ChaCha20.Arm.Stream
open VG.Proof.MdStream.Arm (op2_imm op2_reg wp_mov wp_add eval_eq)

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
  pa : VG.Proof.ChaCha20.Arm.Stream.APre a
  pb : VG.Proof.ChaCha20.Arm.Stream.APre b
  hst : VG.Proof.ChaCha20.Arm.Stream.ST a = VG.Proof.ChaCha20.Arm.Stream.ST b
  hdp : VG.Proof.ChaCha20.Arm.Stream.DP a = VG.Proof.ChaCha20.Arm.Stream.DP b
  hr2 : a.gpr .r2 = b.gpr .r2
  hleft : VG.Proof.ChaCha20.Arm.Stream.N a = VG.Proof.ChaCha20.Arm.Stream.N b

theorem Two.eqL {a b : State} (h : VG.Proof.ChaCha20.Arm.Stream.Two a b) : VG.Proof.ChaCha20.Arm.Stream.L a = VG.Proof.ChaCha20.Arm.Stream.L b := by
  show (a.gpr .r2).toNat = (b.gpr .r2).toNat; rw [h.hr2]
theorem Two.eqO {a b : State} (h : VG.Proof.ChaCha20.Arm.Stream.Two a b) : VG.Proof.ChaCha20.Arm.Stream.O a = VG.Proof.ChaCha20.Arm.Stream.O b := by
  show VG.Proof.ChaCha20.Arm.Stream.N a % 64 = VG.Proof.ChaCha20.Arm.Stream.N b % 64; rw [h.hleft]
theorem Two.eqH {a b : State} (h : VG.Proof.ChaCha20.Arm.Stream.Two a b) : VG.Proof.ChaCha20.Arm.Stream.H a = VG.Proof.ChaCha20.Arm.Stream.H b := by
  show min (VG.Proof.ChaCha20.Arm.Stream.N a % 64) (VG.Proof.ChaCha20.Arm.Stream.L a) = min (VG.Proof.ChaCha20.Arm.Stream.N b % 64) (VG.Proof.ChaCha20.Arm.Stream.L b); rw [h.hleft, h.eqL]
theorem Two.eqNB {a b : State} (h : VG.Proof.ChaCha20.Arm.Stream.Two a b) : VG.Proof.ChaCha20.Arm.Stream.NB a = VG.Proof.ChaCha20.Arm.Stream.NB b := by
  show (VG.Proof.ChaCha20.Arm.Stream.L a - VG.Proof.ChaCha20.Arm.Stream.H a) / 64 = (VG.Proof.ChaCha20.Arm.Stream.L b - VG.Proof.ChaCha20.Arm.Stream.H b) / 64; rw [h.eqH, h.eqL]
theorem Two.eqT {a b : State} (h : VG.Proof.ChaCha20.Arm.Stream.Two a b) : VG.Proof.ChaCha20.Arm.Stream.T a = VG.Proof.ChaCha20.Arm.Stream.T b := by
  show (VG.Proof.ChaCha20.Arm.Stream.L a - VG.Proof.ChaCha20.Arm.Stream.H a) % 64 = (VG.Proof.ChaCha20.Arm.Stream.L b - VG.Proof.ChaCha20.Arm.Stream.H b) % 64; rw [h.eqH, h.eqL]
theorem Two.eqst {a b : State} (h : VG.Proof.ChaCha20.Arm.Stream.Two a b) : VG.Proof.ChaCha20.Arm.Stream.st a = VG.Proof.ChaCha20.Arm.Stream.st b := by
  show State.addr (VG.Proof.ChaCha20.Arm.Stream.ST a) = State.addr (VG.Proof.ChaCha20.Arm.Stream.ST b); rw [h.hst]
theorem Two.eqdp {a b : State} (h : VG.Proof.ChaCha20.Arm.Stream.Two a b) : VG.Proof.ChaCha20.Arm.Stream.dp a = VG.Proof.ChaCha20.Arm.Stream.dp b := by
  show State.addr (VG.Proof.ChaCha20.Arm.Stream.DP a) = State.addr (VG.Proof.ChaCha20.Arm.Stream.DP b); rw [h.hdp]

/-- A branch on Z, which agrees in both runs. -/
theorem z_eq {x y : State} {p q : Bool} (hx : x.z = p) (hy : y.z = q) (hab : p = q) :
    isa.eval .eq x = isa.eval .eq y := by
  have ex : isa.eval .eq x = some x.z := eval_eq x
  have ey : isa.eval .eq y = some y.z := eval_eq y
  rw [ex, ey, hx, hy, hab]

/-! ## The call of `vg_chacha20_xor` -/

theorem Args.covers {s₀ s : State} (h : VG.Proof.ChaCha20.Arm.Stream.Args s₀ s) :
    Covers ([] ++ [VG.Proof.ChaCha20.Arm.Stream.cpR s₀, VG.Proof.ChaCha20.Arm.Stream.blR s₀, VG.Proof.ChaCha20.Arm.Stream.wkR s₀]) (s.rd ++ s.wr) ∧ Covers [VG.Proof.ChaCha20.Arm.Stream.cpR s₀, VG.Proof.ChaCha20.Arm.Stream.blR s₀, VG.Proof.ChaCha20.Arm.Stream.wkR s₀] s.wr := by
  have hcov : ∀ r ∈ [VG.Proof.ChaCha20.Arm.Stream.cpR s₀, VG.Proof.ChaCha20.Arm.Stream.blR s₀, VG.Proof.ChaCha20.Arm.Stream.wkR s₀], ∃ r' ∈ [VG.Proof.ChaCha20.Arm.Stream.stR s₀, VG.Proof.ChaCha20.Arm.Stream.dR s₀], ∃ o,
      r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.ChaCha20.Arm.Stream.stR s₀, by simp, 192, rfl, by simp⟩
    · exact ⟨VG.Proof.ChaCha20.Arm.Stream.dR s₀, by simp, VG.Proof.ChaCha20.Arm.Stream.H s₀, rfl, VG.Proof.ChaCha20.Arm.Stream.HNB_le s₀⟩
    · exact ⟨VG.Proof.ChaCha20.Arm.Stream.stR s₀, by simp, 256, rfl, by simp⟩
  exact ⟨by rw [h.rd, h.wr, List.nil_append, List.nil_append]; exact Covers.of_sub hcov,
    by rw [h.wr]; exact Covers.of_sub hcov⟩

theorem Args.pre {s₀ s : State} (hp : VG.Proof.ChaCha20.Arm.Stream.APre s₀) (h : VG.Proof.ChaCha20.Arm.Stream.Args s₀ s) (hnb : 0 < VG.Proof.ChaCha20.Arm.Stream.NB s₀) :
    Proof.ChaCha20.xorArm.pre (s.callEntry.withRegions [] [VG.Proof.ChaCha20.Arm.Stream.cpR s₀, VG.Proof.ChaCha20.Arm.Stream.blR s₀, VG.Proof.ChaCha20.Arm.Stream.wkR s₀]) := by
  have hL := VG.Proof.ChaCha20.Arm.Stream.L_lt s₀
  have hHNB := VG.Proof.ChaCha20.Arm.Stream.HNB_le s₀
  have hst := hp.st_fit
  have hd := hp.d_fit
  have hn : (BitVec.ofNat 32 (64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀)).toNat = 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀ := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  simp only [Proof.ChaCha20.xorArm, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs), h.r0, h.r1, h.r2, h.r3, hn,
    hp.eaS (d := 192) (by decide), hp.eaS (d := 256) (by decide), hp.eaD (d := VG.Proof.ChaCha20.Arm.Stream.H s₀) (by omega),
    hp.sNat (d := 192) (by decide), hp.sNat (d := 256) (by decide), hp.dNat (d := VG.Proof.ChaCha20.Arm.Stream.H s₀) (by omega)]
  exact ⟨trivial, trivial, (hp.st_d.sub_left (VG.Proof.ChaCha20.Arm.Stream.cpR_sub s₀)).sub_right (VG.Proof.ChaCha20.Arm.Stream.blR_sub s₀),
    Offset.disjoint _ (by omega) (by omega) (by omega),
    (hp.st_d.sub_left (VG.Proof.ChaCha20.Arm.Stream.wkR_sub s₀)).symm.sub_left (VG.Proof.ChaCha20.Arm.Stream.blR_sub s₀), by omega, by omega, by omega⟩

/-! ## The call of the block function -/

/-- The arguments of the call of the block function, and the registers the
rest uses. -/
structure TArgs (s₀ s : State) : Prop where
  r0 : s.gpr .r0 = VG.Proof.ChaCha20.Arm.Stream.ST s₀
  r1 : s.gpr .r1 = VG.Proof.ChaCha20.Arm.Stream.ST s₀ + BitVec.ofNat 32 64
  r4 : s.gpr .r4 = VG.Proof.ChaCha20.Arm.Stream.ST s₀
  r5 : s.gpr .r5 = VG.Proof.ChaCha20.Arm.Stream.DP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Stream.H s₀ + 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀)
  r6 : s.gpr .r6 = BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Stream.T s₀)
  rd : s.rd = []
  wr : s.wr = [VG.Proof.ChaCha20.Arm.Stream.stR s₀, VG.Proof.ChaCha20.Arm.Stream.dR s₀]

theorem tailArgs_ok {s₀ : State} (hp : VG.Proof.ChaCha20.Arm.Stream.APre s₀) {s : State} (h : VG.Proof.ChaCha20.Arm.Stream.Q2 s₀ s) :
    WP isa (.block [.mov .r0 (.reg .r4), .dp .add .r1 .r4 (.imm 64)]) s (VG.Proof.ChaCha20.Arm.Stream.TArgs s₀) :=
  wp_mov (op2_reg _ _) fun s' u => wp_add (op2_imm (by decide)) fun s'' u' => WP.block_nil
    ⟨by rw [u'.other _ (by decide), u.gpr, h.r4], by rw [u'.gpr, u.other _ (by decide), h.r4]; rfl,
      by rw [u'.other _ (by decide), u.other _ (by decide), h.r4],
      by rw [u'.other _ (by decide), u.other _ (by decide), h.r5],
      by rw [u'.other _ (by decide), u.other _ (by decide), h.r6],
      by rw [u'.rd, u.rd, h.rd, hp.rd], by rw [u'.wr, u.wr, h.wr, hp.wr]⟩

/-- After the block function: the registers the rest uses. -/
structure TAfter (s₀ s : State) : Prop where
  r4 : s.gpr .r4 = VG.Proof.ChaCha20.Arm.Stream.ST s₀
  r5 : s.gpr .r5 = VG.Proof.ChaCha20.Arm.Stream.DP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Stream.H s₀ + 64 * VG.Proof.ChaCha20.Arm.Stream.NB s₀)
  r6 : s.gpr .r6 = BitVec.ofNat 32 (VG.Proof.ChaCha20.Arm.Stream.T s₀)

theorem TArgs.covers {s₀ s : State} (hp : VG.Proof.ChaCha20.Arm.Stream.APre s₀) (h : VG.Proof.ChaCha20.Arm.Stream.TArgs s₀ s) :
    Covers ([⟨VG.Proof.ChaCha20.Arm.Stream.st s₀, 64⟩] ++ [⟨State.addr (VG.Proof.ChaCha20.Arm.Stream.ST s₀ + BitVec.ofNat 32 64), 256⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨State.addr (VG.Proof.ChaCha20.Arm.Stream.ST s₀ + BitVec.ofNat 32 64), 256⟩] s.wr := by
  rw [hp.eaS (d := 64) (by decide)]
  refine ⟨?_, ?_⟩
  · rw [h.rd, h.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.ChaCha20.Arm.Stream.stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 768 by decide⟩
    · exact ⟨VG.Proof.ChaCha20.Arm.Stream.stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩
  · rw [h.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.ChaCha20.Arm.Stream.stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩

theorem TArgs.pre {s₀ s : State} (hp : VG.Proof.ChaCha20.Arm.Stream.APre s₀) (h : VG.Proof.ChaCha20.Arm.Stream.TArgs s₀ s) :
    Proof.ChaCha20.blockArm.pre
      (s.callEntry.withRegions [⟨VG.Proof.ChaCha20.Arm.Stream.st s₀, 64⟩] [⟨State.addr (VG.Proof.ChaCha20.Arm.Stream.ST s₀ + BitVec.ofNat 32 64), 256⟩]) := by
  have hst := hp.st_fit
  simp only [Proof.ChaCha20.blockArm, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs),
    h.r0, h.r1, hp.eaS (d := 64) (by decide), hp.sNat (d := 64) (by decide)]
  exact ⟨trivial, trivial, Offset.disjoint_base _ (by omega) (by omega), by omega, by omega⟩

theorem TArgs.call {s₀ s : State} (hp : VG.Proof.ChaCha20.Arm.Stream.APre s₀) (h : VG.Proof.ChaCha20.Arm.Stream.TArgs s₀ s) :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.Arm.block) s (VG.Proof.ChaCha20.Arm.Stream.TAfter s₀) := by
  have hst := hp.st_fit
  have c := h.covers hp
  exact VG.Proof.ChaCha20.Arm.Stream.block_call h.r0 h.r1 (by rw [hp.eaS (d := 64) (by decide)]; exact Offset.disjoint_base _ (by omega) (by omega))
    (by omega) (by rw [hp.sNat (d := 64) (by decide)]; omega) c.1 c.2
    fun _ k _ => ⟨by rw [k.cs .r4 (by decide) (by decide), h.r4], by rw [k.cs .r5 (by decide) (by decide), h.r5],
      by rw [k.cs .r6 (by decide) (by decide), h.r6]⟩

/-! ## The pieces, related -/

section
variable {a b : State} (h : VG.Proof.ChaCha20.Arm.Stream.Two a b)
include h

theorem check_rel :
    RelCT isa (fun x y => x = a ∧ y = b) (.block check) fun x y => VG.Proof.ChaCha20.Arm.Stream.Q0 a x ∧ VG.Proof.ChaCha20.Arm.Stream.Q0 b y :=
  RelCT.post (VG.Proof.ChaCha20.Arm.Stream.taintRegs [.r0] (fun x y ⟨hx, hy⟩ r hr => by
      subst hx hy
      simp only [List.mem_singleton] at hr; subst hr; exact h.hst) (by taint_decide))
    fun x y ⟨hx, hy⟩ => ⟨by subst hx; exact VG.Proof.ChaCha20.Arm.Stream.check_ok h.pa, by subst hy; exact VG.Proof.ChaCha20.Arm.Stream.check_ok h.pb⟩

theorem part1_rel (hle : VG.Proof.ChaCha20.Arm.Stream.L a ≤ VG.Proof.ChaCha20.Arm.Stream.N a) :
    RelCT isa (fun x y => VG.Proof.ChaCha20.Arm.Stream.Q0 a x ∧ VG.Proof.ChaCha20.Arm.Stream.Q0 b y) part1 fun x y => VG.Proof.ChaCha20.Arm.Stream.Q1 a x ∧ VG.Proof.ChaCha20.Arm.Stream.Q1 b y := by
  have hle' : VG.Proof.ChaCha20.Arm.Stream.L b ≤ VG.Proof.ChaCha20.Arm.Stream.N b := by rw [← h.eqL, ← h.hleft]; exact hle
  rw [VG.Proof.ChaCha20.Arm.Stream.part1_eq]
  refine RelCT.seq (R := fun (x y : State) => (VG.Proof.ChaCha20.Arm.Stream.R1 a (VG.Proof.ChaCha20.Arm.Stream.L a) x ∧ x.z = decide (VG.Proof.ChaCha20.Arm.Stream.O a < VG.Proof.ChaCha20.Arm.Stream.L a)) ∧
      (VG.Proof.ChaCha20.Arm.Stream.R1 b (VG.Proof.ChaCha20.Arm.Stream.L b) y ∧ y.z = decide (VG.Proof.ChaCha20.Arm.Stream.O b < VG.Proof.ChaCha20.Arm.Stream.L b)))
    (RelCT.post (VG.Proof.ChaCha20.Arm.Stream.taintRegs [.r0, .r1, .r2] (fun x y ⟨hx, hy⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [hx.keep _ (by decide) (by decide), hy.keep _ (by decide) (by decide)]; exact h.hst
        · rw [hx.keep _ (by decide) (by decide), hy.keep _ (by decide) (by decide)]; exact h.hdp
        · rw [hx.keep _ (by decide) (by decide), hy.keep _ (by decide) (by decide)]; exact h.hr2)
        (by taint_decide))
      fun x y ⟨hx, hy⟩ => ⟨VG.Proof.ChaCha20.Arm.Stream.start_ok h.pa hle hx, VG.Proof.ChaCha20.Arm.Stream.start_ok h.pb hle' hy⟩) ?_
  refine RelCT.seq (R := fun x y => VG.Proof.ChaCha20.Arm.Stream.R1 a (VG.Proof.ChaCha20.Arm.Stream.H a) x ∧ VG.Proof.ChaCha20.Arm.Stream.R1 b (VG.Proof.ChaCha20.Arm.Stream.H b) y)
    (RelCT.post (RelCT.ite (fun x y ⟨⟨_, zx⟩, ⟨_, zy⟩⟩ => VG.Proof.ChaCha20.Arm.Stream.z_eq zx zy (by rw [h.eqO, h.eqL]))
        (VG.Proof.ChaCha20.Arm.Stream.taintRegs [] (fun _ _ _ r hr => by simp at hr) (by taint_decide))
        (VG.Proof.ChaCha20.Arm.Stream.taintRegs [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)))
      fun x y ⟨⟨hx, zx⟩, ⟨hy, zy⟩⟩ => ⟨VG.Proof.ChaCha20.Arm.Stream.sel_ok hx zx, VG.Proof.ChaCha20.Arm.Stream.sel_ok hy zy⟩) ?_
  refine RelCT.post (c := VG.Proof.ChaCha20.Arm.Stream.rest1) (VG.Proof.ChaCha20.Arm.Stream.taintRegs [.r4, .r5, .r6, .r2, .r12] (fun x y ⟨hx, hy⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [hx.r4, hy.r4, h.hst]
      · rw [hx.r5, hy.r5, h.hdp]
      · rw [hx.r6, hy.r6, h.eqL]
      · rw [hx.r2, hy.r2, h.eqH]
      · rw [hx.r12, hy.r12, h.eqO]) (by taint_decide))
    fun x y ⟨hx, hy⟩ => ⟨VG.Proof.ChaCha20.Arm.Stream.rest1_ok h.pa hx, VG.Proof.ChaCha20.Arm.Stream.rest1_ok h.pb hy⟩

theorem xor_rel :
    RelCT isa (fun x y => (VG.Proof.ChaCha20.Arm.Stream.Args a x ∧ 0 < VG.Proof.ChaCha20.Arm.Stream.NB a) ∧ VG.Proof.ChaCha20.Arm.Stream.Args b y)
      (.call "vg_chacha20_xor" Impl.ChaCha20.Arm.Xor.xor) fun _ _ => True := by
  have ecp : VG.Proof.ChaCha20.Arm.Stream.cpR b = VG.Proof.ChaCha20.Arm.Stream.cpR a := by simp only [VG.Proof.ChaCha20.Arm.Stream.cpR, h.eqst]
  have ebl : VG.Proof.ChaCha20.Arm.Stream.blR b = VG.Proof.ChaCha20.Arm.Stream.blR a := by simp only [VG.Proof.ChaCha20.Arm.Stream.blR, h.eqdp, h.eqH, h.eqNB]
  have ewk : VG.Proof.ChaCha20.Arm.Stream.wkR b = VG.Proof.ChaCha20.Arm.Stream.wkR a := by simp only [VG.Proof.ChaCha20.Arm.Stream.wkR, h.eqst]
  refine RelCT.call Proof.ChaCha20.Arm.Xor.xor_correct Proof.ChaCha20.Arm.Xor.xor_ct [] [VG.Proof.ChaCha20.Arm.Stream.cpR a, VG.Proof.ChaCha20.Arm.Stream.blR a, VG.Proof.ChaCha20.Arm.Stream.wkR a]
    fun x y ⟨⟨hx, hnb⟩, hy⟩ => ?_
  have py := hy.pre h.pb (by rw [← h.eqNB]; exact hnb)
  have cy := hy.covers
  rw [ecp, ebl, ewk] at py cy
  refine ⟨hx.pre h.pa hnb, py, ?_, hx.covers.1, hx.covers.2, cy.1, cy.2⟩
  simp only [Proof.ChaCha20.xorArm, State.withRegions_gpr,
    State.callEntry_gpr x (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr x (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr x (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr x (by decide : Reg.r3 ∉ linkRegs),
    State.callEntry_gpr y (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr y (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr y (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr y (by decide : Reg.r3 ∉ linkRegs),
    hx.r0, hx.r1, hx.r2, hx.r3, hy.r0, hy.r1, hy.r2, hy.r3, h.hst, h.hdp, h.eqH, h.eqNB]
  exact ⟨trivial, trivial, trivial, trivial⟩

theorem part2_rel :
    RelCT isa (fun x y => VG.Proof.ChaCha20.Arm.Stream.Q1 a x ∧ VG.Proof.ChaCha20.Arm.Stream.Q1 b y) part2 fun x y => VG.Proof.ChaCha20.Arm.Stream.Q2 a x ∧ VG.Proof.ChaCha20.Arm.Stream.Q2 b y := by
  refine RelCT.post ?_ fun x y ⟨hx, hy⟩ => ⟨VG.Proof.ChaCha20.Arm.Stream.part2_ok h.pa hx, VG.Proof.ChaCha20.Arm.Stream.part2_ok h.pb hy⟩
  refine RelCT.ite (fun x y ⟨hx, hy⟩ => VG.Proof.ChaCha20.Arm.Stream.z_eq hx.z hy.z (by rw [h.eqNB]))
    (VG.Proof.ChaCha20.Arm.Stream.taintRegs [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)) ?_
  refine RelCT.seq (R := fun x y => (VG.Proof.ChaCha20.Arm.Stream.Args a x ∧ 0 < VG.Proof.ChaCha20.Arm.Stream.NB a) ∧ VG.Proof.ChaCha20.Arm.Stream.Args b y) ?_
    (RelCT.seq (VG.Proof.ChaCha20.Arm.Stream.xor_rel h) (VG.Proof.ChaCha20.Arm.Stream.taintRegs [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)))
  refine RelCT.mono (P := fun x y => (VG.Proof.ChaCha20.Arm.Stream.Q1 a x ∧ VG.Proof.ChaCha20.Arm.Stream.Q1 b y) ∧ 0 < VG.Proof.ChaCha20.Arm.Stream.NB a)
    (RelCT.post (VG.Proof.ChaCha20.Arm.Stream.taintRegs [.r4, .r2, .r5] (fun x y ⟨⟨hx, hy⟩, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [hx.r4, hy.r4, h.hst]
        · rw [hx.r2, hy.r2, h.eqNB]
        · rw [hx.r5, hy.r5, h.hdp, h.eqH]) (by taint_decide))
      fun x y ⟨⟨hx, hy⟩, hnb⟩ => ⟨WP.mono (VG.Proof.ChaCha20.Arm.Stream.args_ok h.pa hx) fun _ h' => ⟨h'.1, hnb⟩,
        WP.mono (VG.Proof.ChaCha20.Arm.Stream.args_ok h.pb hy) fun _ h' => h'.1⟩)
    (fun x y ⟨⟨hx, hy⟩, he⟩ => ⟨⟨hx, hy⟩, by
      have e : isa.eval .eq x = some x.z := eval_eq x
      rw [e, hx.z] at he
      simp at he
      omega⟩) fun _ _ hq => hq

theorem part3_rel : RelCT isa (fun x y => VG.Proof.ChaCha20.Arm.Stream.Q2 a x ∧ VG.Proof.ChaCha20.Arm.Stream.Q2 b y) part3 fun x y => VG.Proof.ChaCha20.Arm.Stream.Q3 a x ∧ VG.Proof.ChaCha20.Arm.Stream.Q3 b y := by
  refine RelCT.post ?_ fun x y ⟨hx, hy⟩ => ⟨VG.Proof.ChaCha20.Arm.Stream.part3_ok h.pa hx, VG.Proof.ChaCha20.Arm.Stream.part3_ok h.pb hy⟩
  rw [VG.Proof.ChaCha20.Arm.Stream.part3_eq]
  refine RelCT.seq (R := fun (x y : State) => (VG.Proof.ChaCha20.Arm.Stream.Q2 a x ∧ x.z = decide (VG.Proof.ChaCha20.Arm.Stream.T a = 0)) ∧ (VG.Proof.ChaCha20.Arm.Stream.Q2 b y ∧ y.z = decide (VG.Proof.ChaCha20.Arm.Stream.T b = 0)))
    (RelCT.post (VG.Proof.ChaCha20.Arm.Stream.taintRegs [] (fun _ _ _ r hr => by simp at hr) (by taint_decide))
      fun x y ⟨hx, hy⟩ => ⟨VG.Proof.ChaCha20.Arm.Stream.cmp6_ok hx, VG.Proof.ChaCha20.Arm.Stream.cmp6_ok hy⟩) ?_
  refine RelCT.ite (fun x y ⟨⟨_, zx⟩, ⟨_, zy⟩⟩ => VG.Proof.ChaCha20.Arm.Stream.z_eq zx zy (by rw [h.eqT]))
    (VG.Proof.ChaCha20.Arm.Stream.taintRegs [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)) ?_
  refine RelCT.seq (R := fun x y => VG.Proof.ChaCha20.Arm.Stream.TArgs a x ∧ VG.Proof.ChaCha20.Arm.Stream.TArgs b y)
    (RelCT.post (VG.Proof.ChaCha20.Arm.Stream.taintRegs [.r4] (fun x y ⟨⟨⟨hx, _⟩, ⟨hy, _⟩⟩, _⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hx.r4, hy.r4, h.hst]) (by taint_decide))
      fun x y ⟨⟨⟨hx, _⟩, ⟨hy, _⟩⟩, _⟩ => ⟨VG.Proof.ChaCha20.Arm.Stream.tailArgs_ok h.pa hx, VG.Proof.ChaCha20.Arm.Stream.tailArgs_ok h.pb hy⟩) ?_
  refine RelCT.seq (R := fun x y => VG.Proof.ChaCha20.Arm.Stream.TAfter a x ∧ VG.Proof.ChaCha20.Arm.Stream.TAfter b y) ?_
    (VG.Proof.ChaCha20.Arm.Stream.taintRegs [.r4, .r5, .r6] (fun x y ⟨hx, hy⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hx.r4, hy.r4, h.hst]
      · rw [hx.r5, hy.r5, h.hdp, h.eqH, h.eqNB]
      · rw [hx.r6, hy.r6, h.eqT]) (by taint_decide))
  have est : VG.Proof.ChaCha20.Arm.Stream.ST b = VG.Proof.ChaCha20.Arm.Stream.ST a := h.hst.symm
  have est' : VG.Proof.ChaCha20.Arm.Stream.st b = VG.Proof.ChaCha20.Arm.Stream.st a := h.eqst.symm
  refine RelCT.post (RelCT.call Proof.ChaCha20.Arm.block_correct Proof.ChaCha20.Arm.block_ct
    [⟨VG.Proof.ChaCha20.Arm.Stream.st a, 64⟩] [⟨State.addr (VG.Proof.ChaCha20.Arm.Stream.ST a + BitVec.ofNat 32 64), 256⟩] fun x y ⟨hx, hy⟩ => ?_)
    fun x y ⟨hx, hy⟩ => ⟨hx.call h.pa, hy.call h.pb⟩
  have py := hy.pre h.pb
  have cy := hy.covers h.pb
  rw [est, est'] at py cy
  refine ⟨hx.pre h.pa, py, ?_, (hx.covers h.pa).1, (hx.covers h.pa).2, cy.1, cy.2⟩
  simp only [Proof.ChaCha20.blockArm, State.withRegions_gpr,
    State.callEntry_gpr x (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr x (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr y (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr y (by decide : Reg.r1 ∉ linkRegs),
    hx.r0, hx.r1, hy.r0, hy.r1, h.hst]
  exact ⟨trivial, trivial⟩

theorem apply_rel : RelCT isa (fun x y => x = a ∧ y = b) apply fun _ _ => True := by
  rw [VG.Proof.ChaCha20.Arm.Stream.apply_eq]
  refine RelCT.seq (VG.Proof.ChaCha20.Arm.Stream.check_rel h) (RelCT.ite (fun x y ⟨hx, hy⟩ => VG.Proof.ChaCha20.Arm.Stream.z_eq hx.z hy.z (by rw [h.hleft, h.eqL]))
    (VG.Proof.ChaCha20.Arm.Stream.taintRegs [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)) ?_)
  by_cases hlt : VG.Proof.ChaCha20.Arm.Stream.N a < VG.Proof.ChaCha20.Arm.Stream.L a
  · refine RelCT.of_false fun x y hp => ?_
    have he := hp.2
    have e : isa.eval .eq x = some x.z := eval_eq x
    rw [e, hp.1.1.z] at he
    simp [hlt] at he
  have hle : VG.Proof.ChaCha20.Arm.Stream.L a ≤ VG.Proof.ChaCha20.Arm.Stream.N a := by omega
  refine RelCT.seq (RelCT.mono (VG.Proof.ChaCha20.Arm.Stream.part1_rel h hle) (fun _ _ hp => hp.1) fun _ _ hq => hq)
    (RelCT.seq (VG.Proof.ChaCha20.Arm.Stream.part2_rel h) (RelCT.seq (VG.Proof.ChaCha20.Arm.Stream.part3_rel h) ?_))
  exact VG.Proof.ChaCha20.Arm.Stream.taintRegs [.r4] (fun x y ⟨hx, hy⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [hx.r4, hy.r4, h.hst]) (by taint_decide)

end

theorem Two.of {a b : State} (ha : Proof.ChaCha20.applyArm.pre a) (hb : Proof.ChaCha20.applyArm.pre b)
    (hq : Proof.ChaCha20.applyArm.pub a b) : VG.Proof.ChaCha20.Arm.Stream.Two a b := by
  obtain ⟨p1, p2, p3, _, p5⟩ := hq
  exact ⟨APre.of a ha, APre.of b hb, p1, p2, p3, (List.cons.inj p5).1⟩

theorem apply_ct : ConstantTime isa Proof.ChaCha20.applyArm.pre Proof.ChaCha20.applyArm.pub apply :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.ChaCha20.Arm.Stream.apply_rel (Two.of h₁ h₂ hq) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem apply_ok (s : State) (hs : Proof.ChaCha20.applyArm.pre s) :
    ∃ t s', Exec isa apply s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.applyArm.post s s' := by
  obtain ⟨t, s', he, hf⟩ := VG.Proof.ChaCha20.Arm.Stream.apply_correct (APre.of s hs)
  exact ⟨t, s', he, hf.1, hf.2⟩

/-- A state satisfying the precondition of `apply` (with no data). -/
def applySat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 768⟩, ⟨0x2000, 0⟩]

theorem ret_eq (x y : BitVec 32) : (x ++ y).setWidth 32 = y := by
  ext i hi
  rw [BitVec.getElem_setWidth, BitVec.getLsbD_append, ite_pos hi, BitVec.getLsbD_eq_getElem hi]

theorem apply_verified : Verified Arm.target apply (Spec.ChaCha20.applyContract Arm.abi 0) :=
  Verified.of_correct VG.Proof.ChaCha20.Arm.Stream.apply_ok VG.Proof.ChaCha20.Arm.Stream.apply_ct (by
    sig_implies [Spec.ChaCha20.applyContract, Spec.ChaCha20.applySig, Proof.ChaCha20.applyArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, State.addr, VG.Proof.ChaCha20.Arm.Stream.ret_eq] [applySat] using VG.Proof.ChaCha20.Arm.Stream.applySat)

end VG.Proof.ChaCha20.Arm.Stream

end
