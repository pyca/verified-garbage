import VerifiedGarbage.Proof.Argon2.Arm.Derive.MemoryInit
import VerifiedGarbage.Proof.Argon2.Arm.Mix

/-!
# Argon2 on ARMv7: the steps of the filling loops

The address computations the filling loops share: `column_ok` (the current
column), `blockAddr_ok` (a block's address from its lane and column) and
`prevPointer_ok` (the previous block's). Register-only steps are described
by `Only` (the registers they may write), which keeps the body's invariant
when `r11` is not among them (`Inv.only`).
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.Sha512.Arm (Only)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_sub wp_cmp op2_imm op2_reg op2_lsl)
open VG.Impl.Argon2.Arm.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff ld)

theorem Inv.only {s₀ s t : State} (h : Inv s₀ s) {ds : List Reg} (o : Only ds s t) (h11 : Reg.r11 ∉ ds) :
    Inv s₀ t :=
  h.step o.sp (o.gpr _ h11) o.rd o.wr (by rw [o.mem]; exact Frame.refl _ _)

theorem Only.of_fupd {s t : State} (f : Fupd s t) : Only [] s t :=
  ⟨fun _ _ => by rw [f.gpr], f.mem, f.rd, f.wr, f.sp⟩

theorem Divide.Keep.only {s t : State} (k : Divide.Keep s t) : Only [.r0, .r1, .r3] s t :=
  ⟨fun r hr => k.other r (fun h => hr (by simp [h])) (fun h => hr (by simp [h])) (fun h => hr (by simp [h])),
    k.mem, k.rd, k.wr, k.sp⟩

/-- `ofNat x << n`, without overflow. -/
theorem ofNat_shl {x n : Nat} (h : x * 2 ^ n < 2 ^ 32) :
    BitVec.ofNat 32 x <<< n = BitVec.ofNat 32 (x * 2 ^ n) := by
  have hx : x < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right x (Nat.two_pow_pos n)) h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]

/-- `ofNat a * ofNat b`, without overflow. -/
theorem ofNat_mul_ofNat {a b : Nat} : BitVec.ofNat 32 a * BitVec.ofNat 32 b = BitVec.ofNat 32 (a * b) :=
  (BitVec.ofNat_mul ..).symm

/-! ## Addresses -/

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem laneLen_ge : 8 ≤ (prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega

/-- A cell of the matrix, and its bytes, fit below 2³². -/
theorem cell_fits {lane col : Nat} (hl : lane < lanesN s₀) (hc : col < (prm s₀).laneLen) :
    lane * (prm s₀).laneLen + col < blocksN s₀ ∧
      (memP s₀).toNat + ((lane * (prm s₀).laneLen + col) * 1024 + 1024) ≤ 2 ^ 32 := by
  have hm := hp.mem_fits
  have : lane * (prm s₀).laneLen + col < blocksN s₀ := by
    have e := hp.blocks_eq
    have := Nat.mul_le_mul_right (prm s₀).laneLen (show lane + 1 ≤ lanesN s₀ by omega)
    rw [Nat.succ_mul] at this
    omega
  have h2 : (lane * (prm s₀).laneLen + col + 1) * 1024 ≤ blocksN s₀ * 1024 := Nat.mul_le_mul_right 1024 this
  rw [Nat.succ_mul] at h2
  exact ⟨this, Nat.le_trans (Nat.add_le_add_left h2 _) hm⟩

/-- `blockAddr`: `r0 :=` the address of block `col` of lane `lane`. -/
theorem blockAddr_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {lane col : Nat} (hl : lane < lanesN s₀)
    (hc : col < (prm s₀).laneLen) (ha : s.gpr .r0 = BitVec.ofNat 32 lane) (hcx : s.gpr .r1 = BitVec.ofNat 32 col)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .r0 = memP s₀ + BitVec.ofNat 32 ((lane * (prm s₀).laneLen + col) * 1024) →
      Only [.r0, .r2] s t → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.Arm.Derive.blockAddr ++ is)) s Q := by
  obtain ⟨cl, cf⟩ := cell_fits hp hl hc
  have hb := hp.blocks_lt
  unfold Impl.Argon2.Arm.Derive.blockAddr
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc hp h (d := laneLenOff) (by decide) fun s₁ u₁ => wp_mul fun s₂ u₂ =>
    wp_add (op2_reg _ _) fun s₃ u₃ => ?_
  have i₃ := ((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)
  have e₃ : s₃.gpr .r0 = BitVec.ofNat 32 (lane * (prm s₀).laneLen + col) := by
    rw [u₃.gpr, u₂.gpr, u₂.other .r1 (by decide), u₁.other .r0 (by decide), u₁.other .r1 (by decide), u₁.gpr,
      ha, hcx, pr.laneLen, ofNat_mul_ofNat, BitVec.ofNat_add_ofNat]
  refine wp_ldarg hp i₃ (i := 13) (by decide) fun s₄ u₄ => wp_add (op2_lsl (by decide)) fun s₅ u₅ => k s₅ ?_ ?_
  · rw [u₅.gpr, u₄.gpr, u₄.other _ (by decide), e₃, ofNat_shl (by omega)]
  · exact ((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans (Only.of_upd u₄)).trans
      (Only.of_upd u₅) |>.mono (by simp)

end

/-- The loop position in the locals. -/
structure Pos (s₀ s : State) (pass slice lane index : Nat) : Prop where
  pass : lw s₀ s Impl.Argon2.Arm.Derive.passOff = BitVec.ofNat 32 pass
  slice : lw s₀ s sliceOff = BitVec.ofNat 32 slice
  lane : lw s₀ s laneOff = BitVec.ofNat 32 lane
  index : lw s₀ s indexOff = BitVec.ofNat 32 index

theorem Pos.of_mem {s₀ s t : State} {pass slice lane index : Nat} (h : Pos s₀ s pass slice lane index)
    (hm : t.mem = s.mem) : Pos s₀ t pass slice lane index :=
  ⟨by rw [lw_mem hm]; exact h.pass, by rw [lw_mem hm]; exact h.slice, by rw [lw_mem hm]; exact h.lane,
    by rw [lw_mem hm]; exact h.index⟩

theorem Pos.of_lw {s₀ s t : State} {pass slice lane index : Nat} (h : Pos s₀ s pass slice lane index)
    (hl : ∀ d ∈ [Impl.Argon2.Arm.Derive.passOff, sliceOff, laneOff, indexOff], lw s₀ t d = lw s₀ s d) :
    Pos s₀ t pass slice lane index :=
  ⟨by rw [hl _ (by simp)]; exact h.pass, by rw [hl _ (by simp)]; exact h.slice,
    by rw [hl _ (by simp)]; exact h.lane, by rw [hl _ (by simp)]; exact h.index⟩

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem segLen_lt : (prm s₀).segmentLen < 2 ^ 30 := by
  have := laneLen_ge hp
  have e := hp.blocks_eq
  have l := hp.laneLen_eq
  have := Nat.le_mul_of_pos_left (prm s₀).laneLen (show 0 < lanesN s₀ from hp.lanes_pos)
  have := hp.blocks_lt
  omega

/-- `column`: `r1 :=` the current column, `slice · segLen + index`. -/
theorem column_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {pass slice lane index : Nat}
    (ps : Pos s₀ s pass slice lane index) (hs : slice < 4) (hi : index < (prm s₀).segmentLen)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .r1 = BitVec.ofNat 32 (slice * (prm s₀).segmentLen + index) → Only [.r0, .r1, .r2] s t →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.Arm.Derive.column ++ is)) s Q := by
  have sl := segLen_lt hp
  have hc := Proof.Argon2.column_lt (prm s₀) hp.lanes_pos hs hi
  have := laneLen_ge hp
  have ll := hp.laneLen_eq
  unfold Impl.Argon2.Arm.Derive.column
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc hp h (d := sliceOff) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁ (by decide)
  refine wp_ldloc hp i₁ (d := segLenOff) (by decide) fun s₂ u₂ => wp_mul fun s₃ u₃ => ?_
  have i₃ := (i₁.upd u₂ (by decide)).upd u₃ (by decide)
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine wp_ldloc hp i₃ (d := indexOff) (by decide) fun s₄ u₄ => wp_add (op2_reg _ _) fun t u => k t ?_ ?_
  · rw [u.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, lw_mem u₁.mem, ps.slice,
      pr.segLen, u₄.gpr, lw_mem m₃, ps.index, ofNat_mul_ofNat, BitVec.ofNat_add_ofNat]
  · exact ((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans (Only.of_upd u₄)).trans
      (Only.of_upd u) |>.mono (by simp)

/-- `prevColumn`: `r1 :=` the column before `r1`, cyclically. -/
theorem prevColumn_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {col : Nat} (hc : col < (prm s₀).laneLen)
    (hx : s.gpr .r1 = BitVec.ofNat 32 col) :
    WP isa Impl.Argon2.Arm.Derive.prevColumn s fun t =>
      t.gpr .r1 = BitVec.ofNat 32 ((col + (prm s₀).laneLen - 1) % (prm s₀).laneLen) ∧ Only [.r1] s t := by
  have sl := segLen_lt hp
  have := laneLen_ge hp
  have ll := hp.laneLen_eq
  unfold Impl.Argon2.Arm.Derive.prevColumn
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun s₁ f₁ z₁ => WP.block_nil ?_)
  have o₁ := Only.of_fupd f₁
  have i₁ := h.only o₁ (by decide)
  refine WP.seq (WP.ite (decide (col = 0)) ?_ ?_ ?_)
  · show VG.Arm.eval .eq s₁ = _
    have z : ∀ y : BitVec 32, y - 0 = y := fun y => by simp
    rw [MdStream.Arm.eval_eq, z₁, hx, z, MdStream.Arm.ofNat_beq_zero (by omega)]
  · intro hz
    refine wp_ldloc hp i₁ (d := laneLenOff) (by decide) fun s₂ u₂ => WP.block_nil ?_
    refine wp_sub (op2_imm (by decide)) fun t u => WP.block_nil ⟨?_, ?_⟩
    · have c0 : col = 0 := of_decide_eq_true hz
      rw [u.gpr, u₂.gpr, lw_mem f₁.mem, pr.laneLen, c0, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        MdStream.Arm.sub_ofNat (by omega), Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    · exact ((o₁.trans (Only.of_upd u₂)).trans (Only.of_upd u)).mono (by simp)
  · intro hz
    refine WP.block_nil (wp_sub (op2_imm (by decide)) fun t u => WP.block_nil ⟨?_, ?_⟩)
    · have c0 : col ≠ 0 := of_decide_eq_false hz
      rw [u.gpr, f₁.gpr, hx, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, MdStream.Arm.sub_ofNat (by omega)]
      congr 1
      rw [show col + (prm s₀).laneLen - 1 = col - 1 + (prm s₀).laneLen by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    · exact (o₁.trans (Only.of_upd u)).mono (by simp)

/-- `prevPointer`: `r0 :=` the address of the previous block. -/
theorem prevPointer_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {pass slice lane index : Nat}
    (ps : Pos s₀ s pass slice lane index) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) :
    WP isa Impl.Argon2.Arm.Derive.prevPointer s fun t =>
      t.gpr .r0 = memP s₀ + BitVec.ofNat 32 ((lane * (prm s₀).laneLen +
        (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) % (prm s₀).laneLen) * 1024) ∧
      Only [.r0, .r1, .r2] s t := by
  have hc := Proof.Argon2.column_lt (prm s₀) hp.lanes_pos hs hi
  have := laneLen_ge hp
  unfold Impl.Argon2.Arm.Derive.prevPointer
  refine WP.seq ?_
  rw [← List.append_nil Impl.Argon2.Arm.Derive.column]
  refine column_ok hp h pr ps hs hi fun s₁ c₁ k₁ => WP.block_nil ?_
  have i₁ := h.only k₁ (by decide)
  refine WP.seq ((prevColumn_ok hp i₁ (pr.of_mem k₁.mem) hc c₁).mono fun s₂ ⟨c₂, k₂⟩ => ?_)
  have i₂ := i₁.only k₂ (by decide)
  have m₂ : s₂.mem = s.mem := by rw [k₂.mem, k₁.mem]
  refine wp_ldloc hp i₂ (d := laneOff) (by decide) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃ (by decide)
  rw [← List.append_nil Impl.Argon2.Arm.Derive.blockAddr]
  refine blockAddr_ok hp i₃ (pr.of_mem (by rw [u₃.mem, m₂])) hl (Nat.mod_lt _ (by omega))
    (by rw [u₃.gpr, lw_mem m₂, ps.lane]) (by rw [u₃.other _ (by decide), c₂]) fun t a k => WP.block_nil ⟨a, ?_⟩
  exact (((k₁.trans k₂).trans (Only.of_upd u₃)).trans k).mono (by simp)

end

end VG.Proof.Argon2.Arm.Derive
