module

public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Parameters
public import VerifiedGarbage.Proof.Argon2.RISCV64.Ops
import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Locals

/-!
# Argon2 on RISC-V: the steps of the filling loops

The address computations the filling loops share: `column_ok` (the current
column), `blockAddr_ok` (a block's address from its lane and column) and
`prevPointer_ok` (the previous block's). Register-only steps are described
by `Only` (the registers they may write), which keeps the body's invariant
when the invariant names none of them (`Inv.only`).
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_subi)
open VG.Impl.Argon2.RISCV64.Derive (sliceOff segLenOff indexOff laneOff laneLenOff passOff ld)

theorem Inv.only {s₀ s t : State} (h : Inv s₀ s) {ds : List Reg} (o : Only ds s t)
    (hd : ∀ r ∈ ds, Free r := by decide) : Inv s₀ t :=
  h.step o.sp (o.gpr _ fun m => (hd _ m).1 rfl) (o.gpr _ fun m => (hd _ m).2.1 rfl)
    (o.gpr _ fun m => (hd _ m).2.2.1 rfl) (fun r hr => o.gpr _ fun m => (hd _ m).2.2.2 hr) o.rd o.wr (by rw [o.mem]; exact Frame.refl _ _)

theorem Divide.KeepD.only {s t : State} (k : Divide.KeepD s t) : Only [.a1, .a3, .a4, .a5, .a6] s t :=
  ⟨fun r hr => k.other r (fun h => hr (by simp [h])) (fun h => hr (by simp [h]))
    (fun h => hr (by simp [h])) (fun h => hr (by simp [h])) (fun h => hr (by simp [h])),
    k.mem, k.rd, k.wr, k.sp⟩

theorem ofNat_mul_ofNat {a b : Nat} : BitVec.ofNat 64 a * BitVec.ofNat 64 b = BitVec.ofNat 64 (a * b) :=
  (BitVec.ofNat_mul ..).symm

/-- `ofNat x << n`, without overflow. -/
theorem ofNat_shl' {x n : Nat} (h : x * 2 ^ n < 2 ^ 64) :
    BitVec.ofNat 64 x <<< n = BitVec.ofNat 64 (x * 2 ^ n) := by
  have hx : x < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right x (Nat.two_pow_pos n)) h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx]

/-! ## Addresses -/

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem laneLen_ge : 8 ≤ (prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega

theorem laneLen_le : (prm s₀).laneLen ≤ blocksN s₀ := by
  rw [hp.blocks_eq]; exact Nat.le_mul_of_pos_left _ hp.lanes_pos

theorem blocks_lt' : blocksN s₀ < 2 ^ 32 := Nat.lt_of_le_of_lt hp.blocks_le (mcost_lt s₀)

/-- A cell of the matrix, and its bytes, fit in the matrix. -/
theorem cell_fits {lane col : Nat} (hl : lane < lanesN s₀) (hc : col < (prm s₀).laneLen) :
    lane * (prm s₀).laneLen + col < blocksN s₀ ∧
      (lane * (prm s₀).laneLen + col) * 1024 + 1024 ≤ blocksN s₀ * 1024 := by
  have : lane * (prm s₀).laneLen + col < blocksN s₀ := by
    have e := hp.blocks_eq
    have := Nat.mul_le_mul_right (prm s₀).laneLen (show lane + 1 ≤ lanesN s₀ by omega)
    rw [Nat.succ_mul] at this
    omega
  have h2 : (lane * (prm s₀).laneLen + col + 1) * 1024 ≤ blocksN s₀ * 1024 :=
    Nat.mul_le_mul_right 1024 this
  rw [Nat.succ_mul] at h2
  exact ⟨this, h2⟩

/-- `blockAddr`: `r3 :=` the address of block `col` of lane `lane`. -/
theorem blockAddr_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {lane col : Nat}
    (hl : lane < lanesN s₀) (hc : col < (prm s₀).laneLen) (ha : s.gpr .a0 = BitVec.ofNat 64 lane)
    (hcx : s.gpr .a1 = BitVec.ofNat 64 col) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .a0 = memP s₀ + BitVec.ofNat 64 ((lane * (prm s₀).laneLen + col) * 1024) →
      Only [.a0, .a2] s t → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.RISCV64.Derive.blockAddr ++ is)) s Q := by
  obtain ⟨cl, cf⟩ := cell_fits hp hl hc
  have hb := blocks_lt' hp
  unfold Impl.Argon2.RISCV64.Derive.blockAddr
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc h (d := laneLenOff) (by decide) fun s₁ u₁ => wp_mul fun s₂ u₂ =>
    wp_add fun s₃ u₃ => wp_sll (by decide) fun s₄ u₄ => ?_
  have i₄ := (((h.upd u₁).upd u₂).upd u₃).upd u₄
  have e₄ : s₄.gpr .a0 = BitVec.ofNat 64 ((lane * (prm s₀).laneLen + col) * 1024) := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₂.other .a1 (by decide), u₁.gpr, u₁.other .a0 (by decide),
      u₁.other .a1 (by decide), ha, hcx, pr.laneLen, ofNat_mul_ofNat, BitVec.ofNat_add_ofNat,
      ofNat_shl' (by omega)]
  refine wp_lda hp i₄ (i := 13) (by decide) fun s₅ u₅ => wp_add fun s₆ u₆ => k s₆ ?_ ?_
  · rw [u₆.gpr, u₅.gpr, u₅.other _ (by decide), e₄]
  · exact (((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans
      (Only.of_upd u₄)).trans (Only.of_upd u₅)).trans (Only.of_upd u₆) |>.mono (by simp)

end

/-- The loop position in the frame. -/
structure Pos (s₀ s : State) (pass slice lane index : Nat) : Prop where
  pass : lw s₀ s passOff = BitVec.ofNat 64 pass
  slice : lw s₀ s sliceOff = BitVec.ofNat 64 slice
  lane : lw s₀ s laneOff = BitVec.ofNat 64 lane
  index : lw s₀ s indexOff = BitVec.ofNat 64 index

theorem Pos.of_mem {s₀ s t : State} {pass slice lane index : Nat} (h : Pos s₀ s pass slice lane index)
    (hm : t.mem = s.mem) : Pos s₀ t pass slice lane index :=
  ⟨by rw [lw_mem hm]; exact h.pass, by rw [lw_mem hm]; exact h.slice, by rw [lw_mem hm]; exact h.lane,
    by rw [lw_mem hm]; exact h.index⟩

theorem Pos.of_lw {s₀ s t : State} {pass slice lane index : Nat} (h : Pos s₀ s pass slice lane index)
    (hl : ∀ d, 184 ≤ d → d + 8 ≤ 216 → lw s₀ t d = lw s₀ s d) :
    Pos s₀ t pass slice lane index :=
  ⟨by rw [hl _ (by decide) (by decide)]; exact h.pass, by rw [hl _ (by decide) (by decide)]; exact h.slice,
    by rw [hl _ (by decide) (by decide)]; exact h.lane, by rw [hl _ (by decide) (by decide)]; exact h.index⟩

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem segLen_lt : (prm s₀).segmentLen < 2 ^ 30 := by
  have := laneLen_ge hp
  have := laneLen_le hp
  have := blocks_lt' hp
  have l := hp.laneLen_eq
  omega

omit hp in
/-- `column`: `r4 :=` the current column, `slice · segLen + index`. -/
theorem column_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {pass slice lane index : Nat}
    (ps : Pos s₀ s pass slice lane index)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .a1 = BitVec.ofNat 64 (slice * (prm s₀).segmentLen + index) →
      Only [.a0, .a1, .a2] s t → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.RISCV64.Derive.column ++ is)) s Q := by
  unfold Impl.Argon2.RISCV64.Derive.column
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc h (d := sliceOff) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁
  refine wp_ldloc i₁ (d := segLenOff) (by decide) fun s₂ u₂ => wp_mul fun s₃ u₃ => ?_
  have i₃ := (i₁.upd u₂).upd u₃
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine wp_ldloc i₃ (d := indexOff) (by decide) fun s₄ u₄ => wp_add fun t u => k t ?_ ?_
  · rw [u.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, lw_mem u₁.mem,
      ps.slice, pr.segLen, u₄.gpr, lw_mem m₃, ps.index, ofNat_mul_ofNat, BitVec.ofNat_add_ofNat]
  · exact ((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans
      (Only.of_upd u₄)).trans (Only.of_upd u) |>.mono (by simp)

/-- `prevColumn`: `r4 :=` the column before `a1`, cyclically. -/
theorem prevColumn_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {col : Nat}
    (hc : col < (prm s₀).laneLen) (hx : s.gpr .a1 = BitVec.ofNat 64 col) :
    WP isa Impl.Argon2.RISCV64.Derive.prevColumn s fun t =>
      t.gpr .a1 = BitVec.ofNat 64 ((col + (prm s₀).laneLen - 1) % (prm s₀).laneLen) ∧
        Only [.a1] s t := by
  have := laneLen_ge hp
  have := laneLen_le hp
  have := blocks_lt' hp
  unfold Impl.Argon2.RISCV64.Derive.prevColumn
  refine WP.seq (WP.ite (decide (col = 0)) ?_ ?_ ?_)
  · rw [show isa.eval _ s = VG.RISCV64.eval _ s from rfl, VG.RISCV64.Wp.eval_zero, hx,
      VG.RISCV64.Steps.ofNat_beq_zero (by omega)]
  · intro hz
    refine wp_ldloc h (d := laneLenOff) (by decide) fun s₂ u₂ => WP.block_nil ?_
    refine wp_subi (by decide) fun t u => WP.block_nil ⟨?_, ?_⟩
    · have c0 : col = 0 := of_decide_eq_true hz
      rw [u.gpr, u₂.gpr, pr.laneLen, c0, sub_ofNat (b := 1) (by omega), Nat.zero_add,
        Nat.mod_eq_of_lt (by omega)]
    · exact ((Only.of_upd u₂).trans (Only.of_upd u)).mono (by simp)
  · intro hz
    refine WP.block_nil (wp_subi (by decide) fun t u => WP.block_nil ⟨?_, ?_⟩)
    · have c0 : col ≠ 0 := of_decide_eq_false hz
      rw [u.gpr, hx, sub_ofNat (b := 1) (by omega)]
      congr 1
      rw [show col + (prm s₀).laneLen - 1 = col - 1 + (prm s₀).laneLen by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    · exact (Only.of_upd u).mono (by simp)

/-- `prevPointer`: `r3 :=` the address of the previous block. -/
theorem prevPointer_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {pass slice lane index : Nat}
    (ps : Pos s₀ s pass slice lane index) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) :
    WP isa Impl.Argon2.RISCV64.Derive.prevPointer s fun t =>
      t.gpr .a0 = memP s₀ + BitVec.ofNat 64 ((lane * (prm s₀).laneLen +
        (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) % (prm s₀).laneLen) * 1024) ∧
      Only [.a0, .a1, .a2] s t := by
  have hc := Proof.Argon2.column_lt (prm s₀) hp.lanes_pos hs hi
  have := laneLen_ge hp
  unfold Impl.Argon2.RISCV64.Derive.prevPointer
  refine WP.seq ?_
  rw [← List.append_nil Impl.Argon2.RISCV64.Derive.column]
  refine column_ok h pr ps fun s₁ c₁ k₁ => WP.block_nil ?_
  have i₁ := h.only k₁
  refine WP.seq ((prevColumn_ok hp i₁ (pr.of_mem k₁.mem) hc c₁).mono fun s₂ ⟨c₂, k₂⟩ => ?_)
  have i₂ := i₁.only k₂
  have m₂ : s₂.mem = s.mem := by rw [k₂.mem, k₁.mem]
  refine wp_ldloc i₂ (d := laneOff) (by decide) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃
  rw [← List.append_nil Impl.Argon2.RISCV64.Derive.blockAddr]
  refine blockAddr_ok hp i₃ (pr.of_mem (by rw [u₃.mem, m₂])) hl (Nat.mod_lt _ (by omega))
    (by rw [u₃.gpr, lw_mem m₂, ps.lane]) (by rw [u₃.other _ (by decide), c₂])
    fun t a k => WP.block_nil ⟨a, ?_⟩
  exact (((k₁.trans k₂).trans (Only.of_upd u₃)).trans k).mono (by simp)

end

end VG.Proof.Argon2.RISCV64.Derive
