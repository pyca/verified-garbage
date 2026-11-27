module

public import VerifiedGarbage.Proof.ChaCha20.Stream
public import VerifiedGarbage.Proof.ChaCha20.Arm.Xor
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.ChaCha20.Arm.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.ChaCha20.Arm.Stream

/-! ### `ChaCha20.Arm.Stream.Bytes`, which the modules that import this one used -/

section

/-!
# Streaming ChaCha20 on ARMv7: XORing bytes

Untrusted: everything here is checked by Lean. `xorBytes` XORs the `r2`
bytes at `r3` into those at `r5`, one at a time, advancing both (the loop of
`vg_chacha20_xor`, `Xor.xorLoop`).
-/

@[expose] public section

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
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hc, hj]), Nat.mod_eq_of_lt (by omega_using [hc, hk])] at this
  exact h this

/-- A byte read is outside the bytes written. -/
theorem not_contains {D K : Addr} {c i : Nat}
    (hs : ∀ j < c, ∀ k < c, D + BitVec.ofNat 64 j ≠ K + BitVec.ofNat 64 k) (hi : i < c)
    (h : (⟨D, c⟩ : Region).Contains (K + BitVec.ofNat 64 i) 1) : False := by
  simp only [Region.Contains] at h
  refine hs (K + BitVec.ofNat 64 i - D).toNat (by omega_using [h]) i hi ?_
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

theorem byte_step {s : State} {D K : BitVec 32} {c i : Nat} (hp : BPre s D K c) (hi : i < c) {s₁ : State}
    (h : LInv s D K c i s₁) :
    WP isa (.block xorBody) s₁ fun s' => LInv s D K c (i + 1) s' ∧ s'.z = (s'.gpr .r2 - 0 == 0) := by
  have hc := hp.d_fit
  have hk := hp.k_fit
  have cd : (⟨State.addr D, c⟩ : Region).Contains (State.addr D + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hc])
  have i₁ : InRegions (s₁.rd ++ s₁.wr) (State.addr D + BitVec.ofNat 64 i) 1 := by
    obtain ⟨r, hr, hc⟩ := hp.wD i hi; exact ⟨r, by rw [h.rd, h.wr]; exact List.mem_append_right _ hr, hc⟩
  have i₂ : InRegions (s₁.rd ++ s₁.wr) (State.addr K + BitVec.ofNat 64 i) 1 := by
    rw [h.rd, h.wr]; exact hp.rK i hi
  have o₁ : InRegions s₁.wr (State.addr D + BitVec.ofNat 64 i) 1 := by rw [h.wr]; exact hp.wD i hi
  have ed : ∀ x : State, x.gpr .r5 = s₁.gpr .r5 →
      State.addr (x.gpr .r5 + BitVec.ofNat 32 0) = State.addr D + BitVec.ofNat 64 i :=
    fun x hx => by rw [hx, h.r5]; exact ea0 (by omega_using [hi, hc])
  unfold xorBody
  refine wp_ldrb (by decide) (ed s₁ rfl) i₁ fun s₂ u₂ => ?_
  refine wp_ldrb (a := State.addr K + BitVec.ofNat 64 i) (by decide)
    (by rw [u₂.other _ (by decide), h.r3]; exact ea0 (by omega_using [hi, hk]))
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
      exact not_contains hp.sep hi hcont
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
    rw [u₈.gpr, h7, sub_one' (by omega_using [hi]), Nat.sub_sub]
  refine ⟨⟨?_, ?_, hr2, fun r h₁ h₂ h₃ h₄ h₅ => by rw [g r h₁ h₂ h₃ h₄ h₅]; exact h.keep r h₁ h₂ h₃ h₄ h₅,
    by rw [u₈.rd, u₇.rd, u₆.rd, g₅.rd, u₄.rd, u₃.rd, u₂.rd, h.rd],
    by rw [u₈.wr, u₇.wr, u₆.wr, g₅.wr, u₄.wr, u₃.wr, u₂.wr, h.wr],
    by rw [u₈.sp, u₇.sp, u₆.sp, g₅.sp, u₄.sp, u₃.sp, u₂.sp, h.sp], fun k hk' => ?_, h.frame.trans hfd⟩, ?_⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), h.r5, add_one']
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), g₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), h.r3, add_one']
  · rw [hm, writeW8_apply]
    by_cases he : k = i
    · subst he; simp
    · simp only [D_ne (D := State.addr D) (by omega_using [hc]) hk' hi he, ite_false]
      rw [h.data k hk']
      by_cases h₁ : k < i
      · simp [h₁, show k < i + 1 by omega_using [h₁]]
      · simp [h₁, show ¬ k < i + 1 by omega_using [he, h₁]]
  · rw [hz, hr2, h7, sub_one' (by omega_using [hi]), sub_zero', Nat.sub_sub]

theorem LInv.zero {s : State} {D K : BitVec 32} {c : Nat} (hp : BPre s D K c) : LInv s D K c 0 s :=
  ⟨by rw [hp.r5]; simp, by rw [hp.r3]; simp, by rw [hp.r2, Nat.sub_zero], fun _ _ _ _ _ _ => rfl, rfl, rfl,
    rfl, fun k _ => by simp, Frame.refl _ _⟩

theorem LInv.post {s : State} {D K : BitVec 32} {c : Nat} {s' : State} (h : LInv s D K c c s') :
    BPost s D K c s' :=
  ⟨h.r5, h.keep, h.rd, h.wr, h.sp, fun k hk => by rw [h.data k hk, ite_pos hk], h.frame⟩

theorem loop_ok {s : State} {D K : BitVec 32} {c : Nat} (hp : BPre s D K c) (hc0 : c ≠ 0) :
    WP isa xorLoop s (BPost s D K c) := by
  have hc := hp.d_fit
  rw [xorLoop_eq]
  let Inv : Nat → State → Prop := fun n s' => ∃ i, n = c - i ∧ i < c ∧ LInv s D K c i s'
  have hstep : ∀ n s', Inv n s' → WP isa (.block xorBody) s' (fun s'' =>
      (isa.eval .ne s'' = some false ∧ BPost s D K c s'') ∨
      (isa.eval .ne s'' = some true ∧ ∃ n' < n, Inv n' s'')) := by
    rintro n s' ⟨i, rfl, hi, hI⟩
    refine WP.mono (byte_step hp hi hI) fun s'' ⟨h', hz'⟩ => ?_
    have hz := eval_ne_ofNat s'' (show c - (i + 1) < 2 ^ 32 by omega_using [hc]) hz' h'.r2
    by_cases hl : i + 1 = c
    · exact .inl ⟨by rw [hz]; simp; omega_using [hl], LInv.post (hl ▸ h')⟩
    · exact .inr ⟨by rw [hz]; simp; omega_using [hi, hl], c - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, hl], h'⟩
  exact WP.loop (M := isa) Inv hstep c s ⟨0, by simp, by omega_using [hc0], LInv.zero hp⟩

theorem xorBytes_eq : xorBytes = .seq (.block [.cmp .r2 (.imm 0)]) (.ite .eq (.block []) xorLoop) := rfl

theorem xorBytes_ok {s : State} {D K : BitVec 32} {c : Nat} (hp : BPre s D K c) :
    WP isa xorBytes s (BPost s D K c) := by
  have hc := hp.k_fit
  rw [xorBytes_eq]
  refine WP.seq (wp_cmp (n := .r2) (op2_imm imm0) fun s₁ f₁ hz => WP.block_nil ?_)
  have hp₁ : BPre s₁ D K c := ⟨by rw [f₁.gpr, hp.r5], by rw [f₁.gpr, hp.r3], by rw [f₁.gpr, hp.r2], hp.d_fit,
    hp.k_fit, fun k hk => by rw [f₁.wr]; exact hp.wD k hk, fun k hk => by rw [f₁.rd, f₁.wr]; exact hp.rK k hk,
    hp.sep⟩
  have conv : ∀ s', BPost s₁ D K c s' → BPost s D K c s' := fun s' h =>
    ⟨h.r5, fun r a b d e f => by rw [h.keep r a b d e f, f₁.gpr], by rw [h.rd, f₁.rd], by rw [h.wr, f₁.wr],
      by rw [h.sp, f₁.sp], fun k hk => by rw [h.data k hk, f₁.mem], f₁.mem ▸ h.frame⟩
  refine WP.ite (decide (c = 0)) (by
      have e : isa.eval .eq s₁ = some s₁.z := eval_eq s₁
      rw [e, hz, hp.r2, sub_zero', ofNat_beq_zero (by omega_using [hc])])
    (fun h0 => WP.block_nil (M := isa) (conv _ ?_)) (fun h0 => WP.mono (loop_ok hp₁ (by simpa using h0)) conv)
  simp only [decide_eq_true_eq] at h0; subst h0; exact (LInv.zero hp₁).post

end VG.Proof.ChaCha20.Arm.Stream

end

end

/-!
# Streaming ChaCha20 on ARMv7: the entry state and the calls

Untrusted: everything here is checked by Lean. The contract of `apply`, what
its precondition gives, and the calls of `vg_chacha20_block` and
`vg_chacha20_xor`, from their proofs of correctness (with `WP.call` and
`WP.callCalls`), as ChaCha20-Poly1305 makes them. A call (`bl`) stores
nothing in memory, so the callee changes memory only within the regions it
may write.
-/

@[expose] public section

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
abbrev st : Addr := State.addr (ST s₀)
abbrev dp : Addr := State.addr (DP s₀)
/-- The number of bytes of keystream left, and those in the buffered block. -/
abbrev N : Nat := leftAt s₀.mem (st s₀)
abbrev O : Nat := N s₀ % 64
/-- The bytes from the buffered block, the whole blocks and the bytes of the
next block that `apply` uses. -/
abbrev H : Nat := headLen s₀.mem (st s₀) (L s₀)
abbrev NB : Nat := blocksOf s₀.mem (st s₀) (L s₀)
abbrev T : Nat := tailLen s₀.mem (st s₀) (L s₀)
abbrev S0 : CState := stateAt s₀.mem (st s₀)
abbrev D0 (k : Nat) : Byte := s₀.mem (dp s₀ + BitVec.ofNat 64 k)
abbrev stR : Region := ⟨st s₀, 768⟩
abbrev dR : Region := ⟨dp s₀, L s₀⟩
/-- The keystream byte XORed into byte `k` of the data. -/
abbrev KS (k : Nat) : Byte :=
  if k < H s₀ then s₀.mem (st s₀ + BitVec.ofNat 64 (128 - O s₀ + k))
  else (serialize (block (ctr (S0 s₀) ((k - H s₀) / 64)))).getD ((k - H s₀) % 64) 0
/-- The data with its first `j` bytes XORed. -/
abbrev Done (j : Nat) (m : Mem) : Prop :=
  ∀ k < L s₀, m (dp s₀ + BitVec.ofNat 64 k) = if k < j then D0 s₀ k ^^^ KS s₀ k else D0 s₀ k
end

theorem L_lt (s₀ : State) : L s₀ < 2 ^ 32 := (s₀.gpr .r2).isLt
theorem N_lt (s₀ : State) : N s₀ < 2 ^ 64 := (s₀.mem.readW (st s₀ + 128) 64).isLt
theorem H_le (s₀ : State) : H s₀ ≤ L s₀ := Nat.min_le_right _ _
theorem H_le_O (s₀ : State) : H s₀ ≤ O s₀ := Nat.min_le_left _ _
theorem O_lt (s₀ : State) : O s₀ < 64 := Nat.mod_lt _ (by decide)
theorem T_eq (s₀ : State) : T s₀ = L s₀ - H s₀ - 64 * NB s₀ := by simp only [T, NB, tailLen, blocksOf, H]; omega_using []
theorem HNB_le (s₀ : State) : H s₀ + 64 * NB s₀ ≤ L s₀ := by
  have := H_le s₀; simp only [NB, blocksOf, H] at *; omega_using [this]

structure APre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, dR s₀]
  st_d : (stR s₀).Disjoint (dR s₀)
  st_fit : (ST s₀).toNat + 768 ≤ 2 ^ 32
  d_fit : (DP s₀).toNat + L s₀ ≤ 2 ^ 32

theorem APre.of (s₀ : State) (h : Proof.ChaCha20.applyArm.pre s₀) : APre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

namespace APre
variable {s₀ : State} (hp : APre s₀)
include hp

theorem eaS {d : Nat} (hd : d < 768) : State.addr (ST s₀ + BitVec.ofNat 32 d) = st s₀ + BitVec.ofNat 64 d :=
  addr_off (by have := hp.st_fit; omega_using [hd, this])

theorem sNat {d : Nat} (hd : d < 768) : (ST s₀ + BitVec.ofNat 32 d).toNat = (ST s₀).toNat + d := by
  have := hp.st_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show d < 2 ^ 32 by omega_using [hd]),
    Nat.mod_eq_of_lt (by omega_using [hd, this])]

theorem eaD {d : Nat} (hd : d < L s₀) : State.addr (DP s₀ + BitVec.ofNat 32 d) = dp s₀ + BitVec.ofNat 64 d :=
  addr_off (by have := hp.d_fit; omega_using [hd, this])

theorem dNat {d : Nat} (hd : d < L s₀) : (DP s₀ + BitVec.ofNat 32 d).toNat = (DP s₀).toNat + d := by
  have := hp.d_fit
  have := L_lt s₀
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show d < 2 ^ 32 by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]

theorem w_st {d n : Nat} (h : d + n ≤ 768) : InRegions s₀.wr (st s₀ + BitVec.ofNat 64 d) n :=
  ⟨stR s₀, by rw [hp.wr]; exact List.mem_cons_self .., Offset.contains_base _ h (by omega_using [h])⟩

theorem r_st {d n : Nat} (h : d + n ≤ 768) : InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 d) n := by
  rw [hp.rd, List.nil_append]; exact hp.w_st h

end APre

theorem d_ne_st {s₀ : State} (hp : APre s₀) {j k : Nat} (hj : j < L s₀) (hk : k < 768) :
    dp s₀ + BitVec.ofNat 64 j ≠ st s₀ + BitVec.ofNat 64 k := by
  intro he
  have c₁ : (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 j) 1 :=
    Offset.contains_base _ (by omega_using [hj]) (by have := L_lt s₀; omega_using [hj, this])
  have c₂ : (stR s₀).Contains (st s₀ + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])
  rw [he] at c₁
  exact hp.st_d _ c₂ c₁

theorem dR_byte {s₀ : State} (hp : APre s₀) {k : Nat} (hk : k < L s₀) :
    InRegions s₀.wr (dp s₀ + BitVec.ofNat 64 k) 1 :=
  ⟨dR s₀, by rw [hp.wr]; simp, Offset.contains_base _ (by omega_using [hk]) (by have := L_lt s₀; omega_using [hk, this])⟩

theorem not_in_prefix (p : Addr) {k c : Nat} (hk : c ≤ k) (hk' : k < 2 ^ 64) :
    ¬ (⟨p, c⟩ : Region).Contains (p + BitVec.ofNat 64 k) 1 := by
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat p hk']
  omega_using [hk]

theorem prefix_sub (p : Addr) {c n : Nat} (h : c ≤ n) : Region.Sub ⟨p, c⟩ ⟨p, n⟩ := Region.sub_prefix h

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

theorem block_call {s : State} {S B : BitVec 32} (h0 : s.gpr .r0 = S) (h1 : s.gpr .r1 = B)
    (hdj : (⟨State.addr B, 256⟩ : Region).Disjoint ⟨State.addr S, 64⟩)
    (hS : S.toNat + 64 ≤ 2 ^ 32) (hB : B.toNat + 256 ≤ 2 ^ 32)
    (hc : Covers ([⟨State.addr S, 64⟩] ++ [⟨State.addr B, 256⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨State.addr B, 256⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨State.addr B, 256⟩] s s' →
      stateAt s'.mem (State.addr B) = Spec.ChaCha20.block (stateAt s.mem (State.addr S)) → Q s') :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.Arm.block) s Q := by
  refine WP.call (k := Proof.ChaCha20.blockArm) Proof.ChaCha20.Arm.block_correct
    (rd := [⟨State.addr S, 64⟩]) (wr := [⟨State.addr B, 256⟩]) ?_ hc hw ?_ block_noCalls
  · simp only [Proof.ChaCha20.blockArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), h0, h1]
    exact ⟨trivial, trivial, hdj, hS, hB⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ ?_
    simpa only [Proof.ChaCha20.blockArm, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), h0, h1] using hpost

/-- A call of `vg_chacha20_xor` in place (`dst = src` in `r5`), through
`Xor.xor_call`. -/
theorem xor_call {s : State} {S D B : BitVec 32} {n : Nat} (h0 : s.gpr .r0 = S) (h1 : s.gpr .r1 = D)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 n) (h3 : s.gpr .r3 = B) (h5 : s.gpr .r5 = D) (hn : n < 2 ^ 32)
    (hSD : (⟨State.addr S, 64⟩ : Region).Disjoint ⟨State.addr D, n⟩)
    (hSB : (⟨State.addr S, 64⟩ : Region).Disjoint ⟨State.addr B, 320⟩)
    (hDB : (⟨State.addr D, n⟩ : Region).Disjoint ⟨State.addr B, 320⟩)
    (hS : S.toNat + 64 ≤ 2 ^ 32) (hD : D.toNat + n ≤ 2 ^ 32) (hB : B.toNat + 320 ≤ 2 ^ 32)
    (hc : Covers ([] ++ [⟨State.addr S, 64⟩, ⟨State.addr D, n⟩, ⟨State.addr B, 320⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨State.addr S, 64⟩, ⟨State.addr D, n⟩, ⟨State.addr B, 320⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨State.addr S, 64⟩, ⟨State.addr D, n⟩, ⟨State.addr B, 320⟩] s s' →
      bytesAt s'.mem (State.addr D) n =
        List.zipWith (· ^^^ ·) (bytesAt s.mem (State.addr D) n) (keystream (stateAt s.mem (State.addr S)) n) →
      Q s') :
    WP isa (.call "vg_chacha20_xor" Impl.ChaCha20.Arm.Xor.xor) s Q :=
  Proof.ChaCha20.Arm.Xor.xor_call h0 h1 h2 h3 h5 hn hSD hSB hDB hS hD hB hc hw
    fun s' hrd hwr hsp hf hcs _ hpost => hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ hpost

/-- The regions of the call of `vg_chacha20_xor`: the copy of the state,
the data and the working space. -/
abbrev cpR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 192, 64⟩
abbrev blR (s₀ : State) : Region := ⟨dp s₀ + BitVec.ofNat 64 (H s₀), 64 * NB s₀⟩
abbrev wkR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 256, 320⟩

theorem cpR_sub (s₀ : State) : Region.Sub (cpR s₀) (stR s₀) := Offset.sub_base _ (by omega_using [])
theorem wkR_sub (s₀ : State) : Region.Sub (wkR s₀) (stR s₀) := Offset.sub_base _ (by omega_using [])
theorem blR_sub (s₀ : State) : Region.Sub (blR s₀) (dR s₀) := Offset.sub_base _ (HNB_le s₀)

end VG.Proof.ChaCha20.Arm.Stream
