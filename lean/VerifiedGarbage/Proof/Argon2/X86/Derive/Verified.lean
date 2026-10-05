import VerifiedGarbage.Proof.Argon2.References
import VerifiedGarbage.Proof.Argon2.Reference
import VerifiedGarbage.Proof.Argon2.X86.Derive.MemoryInit
import VerifiedGarbage.Proof.Argon2.AddressInput
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Argon2.Serialization
import VerifiedGarbage.Proof.Argon2.X86.HPrime.Verified

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.Derive.FillState`. -/
section

section

/-!
# Argon2 on x86 (32-bit): the steps of the filling loops

The instructions the filling loops use beyond `VG.X86.Wp` (`mul`, and ALU
operations with a memory or immediate operand), and the address
computations they share: `column_ok` (the current column), `blockAddr_ok`
(a block's address from its lane and column) and `prevPointer_ok` (the
previous block's).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_addm wp_cmpi)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff)

/-! ## Instructions -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `mul r`: `edx:eax := eax · r`. -/
theorem wp_mul {r : Reg}
    (k : ∀ t, t.gpr .eax = BitVec.ofNat 32 ((s.gpr .eax).toNat * (s.gpr r).toNat) →
      t.gpr .edx = BitVec.ofNat 32 ((s.gpr .eax).toNat * (s.gpr r).toNat / 2 ^ 32) →
      Divide.Keep s t → (∀ q, q ≠ .eax → q ≠ .edx → t.gpr q = s.gpr q) → WP isa (.block is) t Q) :
    WP isa (.block (.mul r :: is)) s Q :=
  Wp.cons (s' := execMul r s) rfl (k _ (by simp [execMul, State.setReg]) (by simp [execMul, State.setReg])
    ⟨fun q h1 _ h3 => by simp [execMul, State.setReg, State.setFlags, h1, h3], rfl, rfl, rfl⟩
    fun q h1 h3 => by simp [execMul, State.setReg, State.setFlags, h1, h3])

/-- `or d, [b + o]`, and ZF. -/
theorem wp_orm {d b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Upd s s' d (s.gpr d ||| s.mem.readW (addr B o) 32) →
      s'.zf = some ((s.gpr d ||| s.mem.readW (addr B o) 32) == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .or d (.mem ⟨b, o⟩) :: is)) s Q :=
  Wp.cons (by simp [exec, execAlu, Wp.readSrc_mem hb hin]; rfl) (k _ (Upd.flags _ _ _ _ _ _) rfl)

/-- `xor d, v` -/
theorem wp_xori {d : Reg} {v : BitVec 32} (k : ∀ s', Upd s s' d (s.gpr d ^^^ v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.imm v) :: is)) s Q :=
  Wp.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

/-- `and d, v`, and ZF. -/
theorem wp_andiz {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d &&& v) → s'.zf = some ((s.gpr d &&& v) == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.imm v) :: is)) s Q :=
  Wp.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

end

/-- `add eax, eax`, `n` times. -/
theorem dblA_ok {s : State} {is : List Instr} {Q : State → Prop} :
    ∀ n, (s.gpr .eax).toNat * 2 ^ n < 2 ^ 32 →
      (∀ t, (t.gpr .eax).toNat = (s.gpr .eax).toNat * 2 ^ n → Divide.Keep s t →
        (∀ q, q ≠ .eax → t.gpr q = s.gpr q) → WP isa (.block is) t Q) →
      WP isa (.block (List.replicate n (.alu .add .eax (.reg .eax)) ++ is)) s Q
  | 0, _, k => k s (by simp) (Divide.Keep.refl s) fun _ _ => rfl
  | n + 1, hn, k => by
    rw [List.replicate_succ, List.cons_append]
    have e : (s.gpr .eax).toNat * 2 ^ (n + 1) = (s.gpr .eax).toNat * 2 * 2 ^ n := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mul_assoc]
    have hx : (s.gpr .eax).toNat ≤ (s.gpr .eax).toNat * 2 ^ n :=
      Nat.le_mul_of_pos_right _ (Nat.two_pow_pos n)
    have two : (s.gpr .eax).toNat * 2 < 2 ^ 32 := by
      have := Nat.mul_le_mul_right 2 hx
      rw [Nat.mul_right_comm] at this
      rw [e] at hn
      omega
    refine wp_add fun s₁ u₁ _ => VG.Proof.Argon2.X86.Derive.dblA_ok (s := s₁) n ?_ fun t ht kt ot => k t ?_
      ((Divide.Keep.of_upd u₁ (by simp)).trans kt) fun q hq => (ot q hq).trans (u₁.other q hq)
    · rw [u₁.gpr, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega), ← Nat.two_mul, Nat.mul_comm 2]
      rw [e] at hn; exact hn
    · rw [ht, u₁.gpr, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega), ← Nat.two_mul, Nat.mul_comm 2, e]

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

/-- `blockAddr`: `eax :=` the address of block `col` of lane `lane`. -/
theorem blockAddr_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) (pr : Prm s₀ s) {lane col : Nat} (hl : lane < lanesN s₀)
    (hc : col < (prm s₀).laneLen) (ha : s.gpr .eax = BitVec.ofNat 32 lane) (hcx : s.gpr .ecx = BitVec.ofNat 32 col)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .eax = memP s₀ + BitVec.ofNat 32 ((lane * (prm s₀).laneLen + col) * 1024) →
      t.gpr .ecx = s.gpr .ecx → Divide.Keep s t → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.X86.Derive.blockAddr ++ is)) s Q := by
  obtain ⟨cl, cf⟩ := VG.Proof.Argon2.X86.Derive.cell_fits hp hl hc
  have hb := hp.blocks_lt
  have lt := hp.lanes_lt
  have hL : (prm s₀).laneLen < 2 ^ 32 := by
    have := Nat.le_mul_of_pos_left (prm s₀).laneLen (show 0 < lanesN s₀ from hp.lanes_pos)
    have e := hp.blocks_eq
    omega
  have lL : lane * (prm s₀).laneLen < 2 ^ 32 := by omega
  unfold Impl.Argon2.X86.Derive.blockAddr
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_ldloc hp h (d := laneLenOff) (by decide) fun s₁ u₁ => VG.Proof.Argon2.X86.Derive.wp_mul fun s₂ a₂ d₂ k₂ o₂ =>
    wp_add fun s₃ u₃ _ => ?_
  have i₃ := ((h.upd u₁ (by decide) (by decide)).keep k₂).upd u₃ (by decide) (by decide)
  have e₃ : (s₃.gpr .eax).toNat = lane * (prm s₀).laneLen + col := by
    rw [u₃.gpr, o₂ .ecx (by decide) (by decide), u₁.other .ecx (by decide), hcx, a₂, u₁.other .eax (by decide), ha,
      u₁.gpr, pr.laneLen, BitVec.toNat_add, Wp.toNat_ofNat_lt (k := lane) (by omega), Wp.toNat_ofNat_lt hL,
      Wp.toNat_ofNat_lt lL, Wp.toNat_ofNat_lt (k := col) (by omega), Nat.mod_eq_of_lt (by omega)]
  refine VG.Proof.Argon2.X86.Derive.dblA_ok 10 (by rw [e₃]; omega) fun s₄ e₄ k₄ o₄ => ?_
  have i₄ := i₃.keep k₄
  refine wp_addm i₄.ebp (i₄.arg_in hp (i := 13) (by decide)) fun s₅ u₅ => k s₅ ?_ ?_ ?_
  · rw [u₅.gpr, i₄.arg hp (by decide), BitVec.add_comm]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [e₄, e₃, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rw [u₅.other _ (by decide), o₄ _ (by decide), u₃.other _ (by decide), o₂ _ (by decide) (by decide),
      u₁.other _ (by decide)]
  · exact (((Divide.Keep.of_upd u₁ (by simp)).trans k₂).trans ((Divide.Keep.of_upd u₃ (by simp)).trans k₄)).trans
      (Divide.Keep.of_upd u₅ (by simp))

end


/-- The loop position in the locals. -/
structure Pos (s₀ s : State) (pass slice lane index : Nat) : Prop where
  pass : lw s₀ s Impl.Argon2.X86.Derive.passOff = BitVec.ofNat 32 pass
  slice : lw s₀ s sliceOff = BitVec.ofNat 32 slice
  lane : lw s₀ s laneOff = BitVec.ofNat 32 lane
  index : lw s₀ s indexOff = BitVec.ofNat 32 index

theorem Pos.of_mem {s₀ s t : State} {pass slice lane index : Nat} (h : VG.Proof.Argon2.X86.Derive.Pos s₀ s pass slice lane index)
    (hm : t.mem = s.mem) : VG.Proof.Argon2.X86.Derive.Pos s₀ t pass slice lane index :=
  ⟨by rw [lw_mem hm]; exact h.pass, by rw [lw_mem hm]; exact h.slice, by rw [lw_mem hm]; exact h.lane,
    by rw [lw_mem hm]; exact h.index⟩

theorem Pos.of_lw {s₀ s t : State} {pass slice lane index : Nat} (h : VG.Proof.Argon2.X86.Derive.Pos s₀ s pass slice lane index)
    (hl : ∀ d ∈ [Impl.Argon2.X86.Derive.passOff, sliceOff, laneOff, indexOff], lw s₀ t d = lw s₀ s d) :
    VG.Proof.Argon2.X86.Derive.Pos s₀ t pass slice lane index :=
  ⟨by rw [hl _ (by simp)]; exact h.pass, by rw [hl _ (by simp)]; exact h.slice,
    by rw [hl _ (by simp)]; exact h.lane, by rw [hl _ (by simp)]; exact h.index⟩

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem segLen_lt : (prm s₀).segmentLen < 2 ^ 30 := by
  have := VG.Proof.Argon2.X86.Derive.laneLen_ge hp
  have e := hp.blocks_eq
  have l := hp.laneLen_eq
  have := Nat.le_mul_of_pos_left (prm s₀).laneLen (show 0 < lanesN s₀ from hp.lanes_pos)
  have := hp.blocks_lt
  omega

/-- `column`: `eax` and `ecx :=` the current column, `slice · segLen + index`. -/
theorem column_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) (pr : Prm s₀ s) {pass slice lane index : Nat}
    (ps : VG.Proof.Argon2.X86.Derive.Pos s₀ s pass slice lane index) (hs : slice < 4) (hi : index < (prm s₀).segmentLen)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .eax = BitVec.ofNat 32 (slice * (prm s₀).segmentLen + index) →
      t.gpr .ecx = BitVec.ofNat 32 (slice * (prm s₀).segmentLen + index) → Divide.Keep s t →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.X86.Derive.column ++ is)) s Q := by
  have sl := VG.Proof.Argon2.X86.Derive.segLen_lt hp
  have hc := Proof.Argon2.column_lt (prm s₀) hp.lanes_pos hs hi
  have := VG.Proof.Argon2.X86.Derive.laneLen_ge hp
  have ll := hp.laneLen_eq
  unfold Impl.Argon2.X86.Derive.column
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc hp h (d := sliceOff) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁ (by decide) (by decide)
  refine wp_ldloc hp i₁ (d := segLenOff) (by decide) fun s₂ u₂ => VG.Proof.Argon2.X86.Derive.wp_mul fun s₃ a₃ _ k₃ _ => ?_
  have i₃ := (i₁.upd u₂ (by decide) (by decide)).keep k₃
  have m₃ : s₃.mem = s.mem := by rw [k₃.mem, u₂.mem, u₁.mem]
  refine wp_addm i₃.ebp (loc_in' hp i₃ (d := indexOff) (by decide)) fun s₄ u₄ => wp_mov fun t u => k t ?_ ?_ ?_
  · have e : s₄.gpr .eax = BitVec.ofNat 32 (slice * (prm s₀).segmentLen + index) := by
      rw [u₄.gpr, a₃, u₂.other _ (by decide), u₁.gpr, u₂.gpr, lw_mem u₁.mem, ps.slice, pr.segLen,
        show s₃.mem.readW (addr (VG.Proof.Argon2.X86.Derive.E s₀) indexOff) 32 = lw s₀ s₃ indexOff from rfl, lw_mem m₃, ps.index,
        Wp.toNat_ofNat_lt (by omega), Wp.toNat_ofNat_lt (by omega), BitVec.ofNat_add_ofNat]
    rw [u.other _ (by decide), e]
  · rw [u.gpr, u₄.gpr, a₃, u₂.other _ (by decide), u₁.gpr, u₂.gpr, lw_mem u₁.mem, ps.slice, pr.segLen,
      show s₃.mem.readW (addr (VG.Proof.Argon2.X86.Derive.E s₀) indexOff) 32 = lw s₀ s₃ indexOff from rfl, lw_mem m₃, ps.index,
      Wp.toNat_ofNat_lt (by omega), Wp.toNat_ofNat_lt (by omega), BitVec.ofNat_add_ofNat]
  · exact (((Divide.Keep.of_upd u₁ (by simp)).trans (Divide.Keep.of_upd u₂ (by simp))).trans
      (k₃.trans (Divide.Keep.of_upd u₄ (by simp)))).trans (Divide.Keep.of_upd u (by simp))

/-- `prevColumn`: `ecx :=` the column before `ecx`, cyclically. -/
theorem prevColumn_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) (pr : Prm s₀ s) {col : Nat} (hc : col < (prm s₀).laneLen)
    (hx : s.gpr .ecx = BitVec.ofNat 32 col) :
    WP isa Impl.Argon2.X86.Derive.prevColumn s fun t =>
      t.gpr .ecx = BitVec.ofNat 32 ((col + (prm s₀).laneLen - 1) % (prm s₀).laneLen) ∧ Divide.Keep s t := by
  have sl := VG.Proof.Argon2.X86.Derive.segLen_lt hp
  have := VG.Proof.Argon2.X86.Derive.laneLen_ge hp
  have ll := hp.laneLen_eq
  unfold Impl.Argon2.X86.Derive.prevColumn
  refine WP.seq (wp_cmpi fun s₁ f₁ _ z₁ => WP.block_nil ?_)
  have k₁ : Divide.Keep s s₁ := ⟨fun r _ _ _ => by rw [f₁.gpr], f₁.mem, f₁.rd, f₁.wr⟩
  have i₁ := h.keep k₁
  refine WP.seq (WP.ite (decide (col = 0)) ?_ ?_ ?_)
  · show s₁.zf = _
    have z : ∀ y : BitVec 32, y - 0 = y := fun y => by simp
    rw [z₁, hx, z, Wp.ofNat_beq_zero (by omega)]
  · intro hz
    refine wp_ldloc hp i₁ (d := laneLenOff) (by decide) fun s₂ u₂ => WP.block_nil ?_
    refine wp_subi fun t u _ _ => WP.block_nil ⟨?_, ?_⟩
    · have c0 : col = 0 := of_decide_eq_true hz
      rw [u.gpr, u₂.gpr, lw_mem f₁.mem, pr.laneLen, c0, Wp.ofNat_pred (by omega), Nat.zero_add,
        Nat.mod_eq_of_lt (by omega)]
    · exact (k₁.trans (Divide.Keep.of_upd u₂ (by simp))).trans (Divide.Keep.of_upd u (by simp))
  · intro hz
    refine WP.block_nil (wp_subi fun t u _ _ => WP.block_nil ⟨?_, ?_⟩)
    · have c0 : col ≠ 0 := of_decide_eq_false hz
      rw [u.gpr, f₁.gpr, hx, Wp.ofNat_pred (by omega)]
      congr 1
      rw [show col + (prm s₀).laneLen - 1 = col - 1 + (prm s₀).laneLen by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    · exact k₁.trans (Divide.Keep.of_upd u (by simp))

/-- `prevPointer`: `eax :=` the address of the previous block. -/
theorem prevPointer_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) (pr : Prm s₀ s) {pass slice lane index : Nat}
    (ps : VG.Proof.Argon2.X86.Derive.Pos s₀ s pass slice lane index) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) :
    WP isa Impl.Argon2.X86.Derive.prevPointer s fun t =>
      t.gpr .eax = memP s₀ + BitVec.ofNat 32 ((lane * (prm s₀).laneLen +
        (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) % (prm s₀).laneLen) * 1024) ∧
      Divide.Keep s t := by
  have hc := Proof.Argon2.column_lt (prm s₀) hp.lanes_pos hs hi
  have := VG.Proof.Argon2.X86.Derive.laneLen_ge hp
  unfold Impl.Argon2.X86.Derive.prevPointer
  refine WP.seq ?_
  rw [← List.append_nil Impl.Argon2.X86.Derive.column]
  refine VG.Proof.Argon2.X86.Derive.column_ok hp h pr ps hs hi fun s₁ _ c₁ k₁ => WP.block_nil ?_
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.prevColumn_ok hp (h.keep k₁) (pr.of_mem k₁.mem) hc c₁).mono fun s₂ ⟨c₂, k₂⟩ => ?_)
  have i₂ := (h.keep k₁).keep k₂
  have m₂ : s₂.mem = s.mem := by rw [k₂.mem, k₁.mem]
  refine wp_ldloc hp i₂ (d := laneOff) (by decide) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃ (by decide) (by decide)
  rw [← List.append_nil Impl.Argon2.X86.Derive.blockAddr]
  refine VG.Proof.Argon2.X86.Derive.blockAddr_ok hp i₃ (pr.of_mem (by rw [u₃.mem, m₂])) hl (Nat.mod_lt _ (by omega))
    (by rw [u₃.gpr, lw_mem m₂, ps.lane]) (by rw [u₃.other _ (by decide), c₂]) fun t a _ k => WP.block_nil ⟨a, ?_⟩
  exact ((k₁.trans k₂).trans (Divide.Keep.of_upd u₃ (by simp))).trans k

end

end VG.Proof.Argon2.X86.Derive

end

/-!
# Argon2 on x86 (32-bit): the state of the filling loops

`FS s₀ pass slice lane index ctr st`: the body at a position of the filling
loops (`Pos`), the memory matrix representing `st`'s, and the address block
cached in `scratch[6144, 7168)` that of the counter in the locals, if it is
not zero (`CacheOk`). `addressMode_ok`: `addressMode` sets ZF for
data-dependent addressing.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_addm wp_cmpi wp_sbb_self wp_and wp_or
  wp_andi)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState addressBlock independent)
open VG.Proof.Argon2.X86 (blk)
open VG.Proof.Sha512.X86 (rd64)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff)

/-- The address block cached at `scratch + 6144`, for the counter in the locals. -/
def CacheOk (s₀ : State) (pass lane slice ctr : Nat) (s : State) : Prop :=
  ctr < 2 ^ 32 ∧ lw s₀ s counterOff = BitVec.ofNat 32 ctr ∧
    (ctr = 0 ∨ 1 ≤ ctr ∧ VG.Proof.Argon2.X86.blk s.mem (scrP s₀) 6144 = addressBlock (prm s₀) pass lane slice ctr)

/-- The counter after a block: the index's group, for data-independent addressing. -/
def ctrNext (p : Spec.Argon2.Params) (pass slice index ctr : Nat) : Nat :=
  if independent p pass slice then index / 128 + 1 else ctr

/-- The filling loops' state at a position, the memory matrix holding `st`'s. -/
structure FS (s₀ : State) (pass slice lane index ctr : Nat) (st : FillState) (s : State) : Prop where
  inv : VG.Proof.Argon2.X86.Derive.Inv s₀ s
  pr : Prm s₀ s
  pos : VG.Proof.Argon2.X86.Derive.Pos s₀ s pass slice lane index
  cache : VG.Proof.Argon2.X86.Derive.CacheOk s₀ pass lane slice ctr s
  mem : Represents s.mem (memB s₀) (prm s₀).blocks st.memory

theorem Divide.Keep.of_fupd {s t : State} (f : Fupd s t) : Divide.Keep s t :=
  ⟨fun _ _ _ _ => by rw [f.gpr], f.mem, f.rd, f.wr⟩

theorem Represents.keep {m m' : Mem} {base : Addr} {n : Nat} {b : Array Block}
    (h : Represents m base n b) (hk : ∀ k < n, blockAt m' (matrixCell base k) = blockAt m (matrixCell base k)) :
    Represents m' base n b :=
  ⟨h.size, fun k hk' => (hk k hk').trans (h.block k hk')⟩

/-- The block at `B + o`, from `B + o` as its base. -/
theorem blk_shift (m : Mem) (B : BitVec 32) (o : Nat) : VG.Proof.Argon2.X86.blk m (B + BitVec.ofNat 32 o) 0 = VG.Proof.Argon2.X86.blk m B o := by
  apply Vector.ext
  intro j hj
  simp only [VG.Proof.Argon2.X86.blk, Vector.getElem_ofFn, rd64, addr, Nat.zero_add, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
    Nat.add_assoc]

/-- The cells of the matrix, as `blk`. -/
theorem cell_blk {s₀ : State} (hp : DPre s₀) (m : Mem) {k : Nat} (hk : k < blocksN s₀) :
    blockAt m (matrixCell (memB s₀) k) = VG.Proof.Argon2.X86.blk m (memP s₀) (k * 1024) := by
  have := hp.mem_fits
  have : k * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega
  rw [← cell_addr hp hk, Proof.Argon2.X86.blockAt_eq (by rw [add_nat (by omega)]; omega), VG.Proof.Argon2.X86.Derive.blk_shift]

/-- The first word of a block. -/
theorem blk_zero (m : Mem) (B : BitVec 32) (o : Nat) :
    (VG.Proof.Argon2.X86.blk m B o)[0] = m.readW (addr B (o + 4)) 32 ++ m.readW (addr B o) 32 := by
  simp only [VG.Proof.Argon2.X86.blk, Vector.getElem_ofFn, rd64, Nat.mul_zero, Nat.add_zero]

/-- Word `j` of a block. -/
theorem blk_get (m : Mem) (B : BitVec 32) (o j : Nat) (hj : j < 128) :
    (VG.Proof.Argon2.X86.blk m B o)[j] = m.readW (addr B (o + 8 * j + 4)) 32 ++ m.readW (addr B (o + 8 * j)) 32 := by
  simp only [VG.Proof.Argon2.X86.blk, Vector.getElem_ofFn, rd64]

/-! ## The addressing mode -/

theorem independent_eq {s₀ : State} (hk : (kindV s₀).toNat ≤ 2) (pass slice : Nat) :
    independent (prm s₀) pass slice = (decide ((kindV s₀).toNat = 1) ||
      (decide ((kindV s₀).toNat = 2) && decide (pass = 0) && decide (slice < 2))) := by
  have hv : (prm s₀).variant = (if (kindV s₀).toNat = 0 then .d else if (kindV s₀).toNat = 1 then .i else .id) :=
    rfl
  have e1 : (Spec.Argon2.Variant.d == .i) = false := rfl
  have e2 : (Spec.Argon2.Variant.d == .id) = false := rfl
  have e3 : (Spec.Argon2.Variant.i == .i) = true := rfl
  have e3' : (Spec.Argon2.Variant.i == .id) = false := rfl
  have e4 : (Spec.Argon2.Variant.id == .i) = false := rfl
  have e5 : (Spec.Argon2.Variant.id == .id) = true := rfl
  rcases (by omega : (kindV s₀).toNat = 0 ∨ (kindV s₀).toNat = 1 ∨ (kindV s₀).toNat = 2) with h | h | h
  · rw [independent, hv, ite_eq_left h, e1, e2, h]; simp
  · rw [independent, hv, ite_eq_right (by omega), ite_eq_left h, e3, e3', h]; simp
  · rw [independent, hv, ite_eq_right (by omega), ite_eq_right (by omega), e4, e5, h]; simp
    cases pass <;> rfl

theorem mode_bits (a b c d : Bool) :
    ((((if a then BitVec.allOnes 32 else 0) ||| ((if b then BitVec.allOnes 32 else 0) &&&
      (if c then BitVec.allOnes 32 else 0) &&& (if d then BitVec.allOnes 32 else 0))) &&& 1) - 0 == 0) =
      !(a || (b && c && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `addressMode`: ZF for data-dependent addressing. -/
theorem addressMode_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) {pass slice lane index : Nat}
    (ps : VG.Proof.Argon2.X86.Derive.Pos s₀ s pass slice lane index) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa (.block Impl.Argon2.X86.Derive.addressMode) s fun t =>
      t.zf = some (!independent (prm s₀) pass slice) ∧ Divide.Keep s t := by
  have hk := hp.kind_le
  unfold Impl.Argon2.X86.Derive.addressMode
  refine wp_ldarg hp h (i := 0) (by decide) fun s₁ u₁ => wp_mov fun s₂ u₂ => VG.Proof.Argon2.X86.Derive.wp_xori fun s₃ u₃ =>
    wp_cmpi fun s₄ f₄ c₄ _ => wp_sbb_self c₄ fun s₅ u₅ => wp_mov fun s₆ u₆ => VG.Proof.Argon2.X86.Derive.wp_xori fun s₇ u₇ =>
    wp_cmpi fun s₈ f₈ c₈ _ => wp_sbb_self c₈ fun s₉ u₉ => ?_
  have K₉ : Divide.Keep s s₉ :=
    ((((((((Divide.Keep.of_upd u₁ (by simp)).trans (Divide.Keep.of_upd u₂ (by simp))).trans
      (Divide.Keep.of_upd u₃ (by simp))).trans (Divide.Keep.of_fupd f₄)).trans (Divide.Keep.of_upd u₅ (by simp))).trans
      (Divide.Keep.of_upd u₆ (by simp))).trans (Divide.Keep.of_upd u₇ (by simp))).trans
      (Divide.Keep.of_fupd f₈)).trans (Divide.Keep.of_upd u₉ (by simp))
  refine wp_ldloc hp (h.keep K₉) (d := passOff) (by decide) fun s₁₀ u₁₀ => wp_cmpi fun s₁₁ f₁₁ c₁₁ _ =>
    wp_sbb_self c₁₁ fun s₁₂ u₁₂ => wp_and fun s₁₃ u₁₃ => ?_
  have K₁₃ : Divide.Keep s s₁₃ :=
    (((K₉.trans (Divide.Keep.of_upd u₁₀ (by simp))).trans (Divide.Keep.of_fupd f₁₁)).trans
      (Divide.Keep.of_upd u₁₂ (by simp))).trans (Divide.Keep.of_upd u₁₃ (by simp))
  refine wp_ldloc hp (h.keep K₁₃) (d := sliceOff) (by decide) fun s₁₄ u₁₄ => wp_cmpi fun s₁₅ f₁₅ c₁₅ _ =>
    wp_sbb_self c₁₅ fun s₁₆ u₁₆ => wp_and fun s₁₇ u₁₇ => wp_or fun s₁₈ u₁₈ => wp_andi fun s₁₉ u₁₉ =>
    wp_cmpi fun t f _ z => WP.block_nil ⟨?_, ?_⟩
  · -- The masks.
    have e₅ : s₅.gpr .ecx = if decide ((kindV s₀ ^^^ 1).toNat < 1) then BitVec.allOnes 32 else 0 := by
      rw [u₅.gpr]; congr 2
      rw [u₃.gpr, u₂.gpr, u₁.gpr]; rfl
    have e₉ : s₉.gpr .edx = if decide ((kindV s₀ ^^^ 2).toNat < 1) then BitVec.allOnes 32 else 0 := by
      rw [u₉.gpr]; congr 2
      rw [u₇.gpr, u₆.gpr, u₅.other _ (by decide), f₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.gpr]; rfl
    have p₁₀ : (s₁₀.gpr .eax).toNat = pass := by
      rw [u₁₀.gpr, lw_mem K₉.mem, ps.pass, Wp.toNat_ofNat_lt hpass]
    have e₁₃ : s₁₃.gpr .edx = s₉.gpr .edx &&& if decide (pass < 1) then BitVec.allOnes 32 else 0 := by
      rw [u₁₃.gpr, u₁₂.other _ (by decide), f₁₁.gpr, u₁₀.other _ (by decide), u₁₂.gpr]
      congr 3
      rw [p₁₀]; rfl
    have p₁₄ : (s₁₄.gpr .eax).toNat = slice := by
      rw [u₁₄.gpr, lw_mem K₁₃.mem, ps.slice, Wp.toNat_ofNat_lt (by omega)]
    have e₁₇ : s₁₇.gpr .edx = s₁₃.gpr .edx &&& if decide (slice < 2) then BitVec.allOnes 32 else 0 := by
      rw [u₁₇.gpr, u₁₆.other _ (by decide), f₁₅.gpr, u₁₄.other _ (by decide), u₁₆.gpr]
      congr 3
      rw [p₁₄]; rfl
    have e₁₈ : s₁₈.gpr .ecx = s₅.gpr .ecx ||| s₁₇.gpr .edx := by
      rw [u₁₈.gpr, u₁₇.other _ (by decide), u₁₆.other _ (by decide), f₁₅.gpr, u₁₄.other _ (by decide),
        u₁₃.other _ (by decide), u₁₂.other _ (by decide), f₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide),
        f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide)]
    rw [z, u₁₉.gpr, e₁₈, e₁₇, e₁₃, e₉, e₅, VG.Proof.Argon2.X86.Derive.independent_eq hk]
    have k3 : decide ((kindV s₀ ^^^ 1).toNat < 1) = decide ((kindV s₀).toNat = 1) ∧
        decide ((kindV s₀ ^^^ 2).toNat < 1) = decide ((kindV s₀).toNat = 2) := by
      rcases (by omega : (kindV s₀).toNat = 0 ∨ (kindV s₀).toNat = 1 ∨ (kindV s₀).toNat = 2) with e | e | e <;>
        · rw [show kindV s₀ = BitVec.ofNat 32 (kindV s₀).toNat by simp, e]; decide
    rw [k3.1, k3.2, show decide (pass < 1) = decide (pass = 0) by simp only [Nat.lt_one_iff],
      VG.Proof.Argon2.X86.Derive.mode_bits]
  · exact (((((((K₁₃.trans (Divide.Keep.of_upd u₁₄ (by simp))).trans (Divide.Keep.of_fupd f₁₅)).trans
      (Divide.Keep.of_upd u₁₆ (by simp))).trans (Divide.Keep.of_upd u₁₇ (by simp))).trans
      (Divide.Keep.of_upd u₁₈ (by simp))).trans (Divide.Keep.of_upd u₁₉ (by simp))).trans (Divide.Keep.of_fupd f))

end

end VG.Proof.Argon2.X86.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.Derive.FillCall`. -/
section

/-!
# Argon2 on x86 (32-bit): calls of G in the filling loops

The filling loops call `vg_argon2_compress` in a frame of its four arguments,
`compress(eax, esi, ecx, edx)`: G of the blocks at `eax` and `esi`, each a
cell of the memory matrix or a block of `scratch` from offset 4096 on
(`GArg`), to `scratch + o`, with `scratch[0, 4096)` as its working space
(`ccall_ok`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.Spec.Argon2 (Block blockAt compress)
open VG.Proof.Argon2.X86 (blk compressX86)

theorem compress_nosp : NoSp Impl.Argon2.X86.compress := NoSp.of_all (by lit_decide)
theorem compress_stack : stackUse Impl.Argon2.X86.compress = 0 := by lit_decide

/-- `scratch`, as an address. -/
abbrev scrB (s₀ : State) : Addr := (scrP s₀).setWidth 64

/-- A block G may read: a cell of the matrix, or a block of `scratch` from 4096
on apart from the output at offset `o`. -/
def GArg (s₀ : State) (o : Nat) (p : BitVec 32) : Prop :=
  (∃ k < blocksN s₀, p = memP s₀ + BitVec.ofNat 32 (k * 1024)) ∨
    ∃ d, 4096 ≤ d ∧ d + 1024 ≤ 16384 ∧ (d + 1024 ≤ o ∨ o + 1024 ≤ d) ∧ p = scrP s₀ + BitVec.ofNat 32 d

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- What a call needs of a block it reads. -/
theorem GArg.facts {o : Nat} (ho : 4096 ≤ o) (ho' : o + 1024 ≤ 16384) {p : BitVec 32} (h : VG.Proof.Argon2.X86.Derive.GArg s₀ o p) :
    (∃ R ∈ [memR s₀, VG.Proof.Argon2.X86.Derive.scrR s₀], ∃ off, p.setWidth 64 = R.base + BitVec.ofNat 64 off ∧ off + 1024 ≤ R.len) ∧
    p.toNat + 1024 ≤ 2 ^ 32 ∧
    Region.Disjoint ⟨p.setWidth 64, 1024⟩ ⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 o, 1024⟩ ∧
    Region.Disjoint ⟨p.setWidth 64, 1024⟩ ⟨VG.Proof.Argon2.X86.Derive.scrB s₀, 4096⟩ ∧
    Region.Disjoint ⟨p.setWidth 64, 1024⟩ (callR s₀) := by
  have hs := hp.scr_fits
  have hm := hp.mem_fits
  rcases h with ⟨k, hk, rfl⟩ | ⟨d, hd, hd', hdo, rfl⟩
  · have hk' : k * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega
    have e := cell_addr hp hk
    have sub : Region.Sub ⟨(memP s₀ + BitVec.ofNat 32 (k * 1024)).setWidth 64, 1024⟩ (memR s₀) := by
      rw [e]; exact cell_in_mem hk
    refine ⟨⟨memR s₀, by simp, k * 1024, e, hk'⟩, by rw [add_nat (by omega)]; omega, ?_, ?_, ?_⟩
    · exact (hp.mem_scr.sub_left sub).sub_right (Offset.sub_base _ ho')
    · exact (hp.mem_scr.sub_left sub).sub_right (Offset.sub_base (d := 0) (n := 4096) (k := 16384) _ (by omega) |> fun h => by
        simpa using h)
    · exact (call_disj hp (R := memR s₀) (by simp)).symm.sub_left sub
  · have e : (scrP s₀ + BitVec.ofNat 32 d).setWidth 64 = VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 d :=
      HPrime.setWidth_add (by omega)
    refine ⟨⟨VG.Proof.Argon2.X86.Derive.scrR s₀, by simp, d, e, hd'⟩, by rw [add_nat (by omega)]; omega, ?_, ?_, ?_⟩
    · rw [e]; exact Offset.disjoint _ hdo (by omega) (by omega)
    · rw [e]; exact Offset.disjoint_base _ hd (by omega)
    · rw [e]; exact (call_disj hp (R := VG.Proof.Argon2.X86.Derive.scrR s₀) (by simp)).symm.sub_left (Offset.sub_base _ hd')

/-- What G needs, from the body: `compress(eax, esi, ecx, edx)`, to `scratch + o`. -/
theorem ccall_pre {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) (hdx : s.gpr .edx = scrP s₀) {o : Nat} (ho : 4096 ≤ o)
    (ho' : o + 1024 ≤ 16384) (hcx : s.gpr .ecx = scrP s₀ + BitVec.ofNat 32 o) (hx : VG.Proof.Argon2.X86.Derive.GArg s₀ o (s.gpr .eax))
    (hy : VG.Proof.Argon2.X86.Derive.GArg s₀ o (s.gpr .esi)) :
    CallPre VG.Proof.Argon2.X86.compressX86 [.edx, .ecx, .esi, .eax]
      [⟨(s.gpr .eax).setWidth 64, 1024⟩, ⟨(s.gpr .esi).setWidth 64, 1024⟩,
        ⟨(s.gpr .esp - BitVec.ofNat 32 16).setWidth 64, 16⟩]
      [⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨VG.Proof.Argon2.X86.Derive.scrB s₀, 4096⟩] s := by
  have hE := E_nat hp
  have hlo := hp.esp_lo
  have hhi := E_hi hp
  have hs := hp.scr_fits
  have esp := h.esp
  have nesp : Reg.esp ∉ [Reg.edx, .ecx, .esi, .eax] := by decide
  have fit : 4 * [Reg.edx, .ecx, .esi, .eax].length + 4 ≤ (s.gpr .esp).toNat := by
    simp only [List.length_cons, List.length_nil]; rw [esp]; omega
  have a0 := callEntry_arg fit nesp (i := 0) (by simp)
  have a1 := callEntry_arg fit nesp (i := 1) (by simp)
  have a2 := callEntry_arg fit nesp (i := 2) (by simp)
  have a3 := callEntry_arg fit nesp (i := 3) (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_succ, List.getElem_cons_zero,
    Nat.reduceAdd, Nat.reduceSub] at a0 a1 a2 a3
  rw [hdx] at a3
  rw [hcx] at a2
  obtain ⟨⟨RX, hRX, oX, bX, lX⟩, fX, X_out, X_scr, X_call⟩ := hx.facts hp ho ho'
  obtain ⟨⟨RY, hRY, oY, bY, lY⟩, fY, Y_out, Y_scr, Y_call⟩ := hy.facts hp ho ho'
  have eO : (scrP s₀ + BitVec.ofNat 32 o).setWidth 64 = VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 o :=
    HPrime.setWidth_add (by omega)
  have memW : ∀ R ∈ [memR s₀, VG.Proof.Argon2.X86.Derive.scrR s₀], R ∈ s.wr := fun R hR => by
    rw [h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact mem_mem hp
    · exact scr_mem hp
  have scrW : VG.Proof.Argon2.X86.Derive.scrR s₀ ∈ s.wr := memW _ (by simp)
  have cX : Covers [⟨(s.gpr .eax).setWidth 64, 1024⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RX, memW _ hRX, oX, bX, lX⟩
  have cY : Covers [⟨(s.gpr .esi).setWidth 64, 1024⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RY, memW _ hRY, oY, bY, lY⟩
  have cO : Covers [⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 o, 1024⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨VG.Proof.Argon2.X86.Derive.scrR s₀, scrW, o, rfl, ho'⟩
  have cW : Covers [⟨VG.Proof.Argon2.X86.Derive.scrB s₀, 4096⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨VG.Proof.Argon2.X86.Derive.scrR s₀, scrW, 0, by simp, by simp⟩
  have O_W : Region.Disjoint ⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 o, 1024⟩ ⟨VG.Proof.Argon2.X86.Derive.scrB s₀, 4096⟩ :=
    Offset.disjoint_base _ ho (by omega)
  have O_call : Region.Disjoint ⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 o, 1024⟩ (callR s₀) :=
    (call_disj hp (R := VG.Proof.Argon2.X86.Derive.scrR s₀) (by simp)).symm.sub_left (Offset.sub_base _ ho')
  have W_call : Region.Disjoint ⟨VG.Proof.Argon2.X86.Derive.scrB s₀, 4096⟩ (callR s₀) :=
    (call_disj hp (R := VG.Proof.Argon2.X86.Derive.scrR s₀) (by simp)).symm.sub_left (Region.sub_prefix (by decide))
  have e16 : (s.gpr .esp - BitVec.ofNat 32 16).toNat = (VG.Proof.Argon2.X86.Derive.E s₀).toNat - 16 := by rw [esp, sub_nat (by omega)]
  have e20 : (s.gpr .esp - BitVec.ofNat 32 20).toNat = (VG.Proof.Argon2.X86.Derive.E s₀).toNat - 20 := by rw [esp, sub_nat (by omega)]
  have cA : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 16).setWidth 64, 16⟩ (callR s₀) :=
    in_call hp (by omega) (by omega)
  have cR : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 20).setWidth 64, 4⟩ (callR s₀) :=
    in_call hp (by omega) (by omega)
  have a16 : argAddr (pushed [Reg.edx, .ecx, .esi, .eax] s).callEntry 0 =
      (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 := callEntry_argAddr0 _ _
  have ce : (pushed [Reg.edx, .ecx, .esi, .eax] s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 20 :=
    callEntry_esp' _ _
  refine ⟨?_, ?_, ?_⟩
  · simp only [VG.Proof.Argon2.X86.compressX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, arg_withRegions,
      argAddr_withRegions, a0, a1, a2, a3, a16, ce, eO]
    refine ⟨trivial, trivial, O_W, X_out, X_scr, Y_out, Y_scr, O_call.symm.sub_left cA,
      W_call.symm.sub_left cA, O_call.symm.sub_left cR, W_call.symm.sub_left cR, fX, fY,
      by rw [add_nat (by omega)]; omega, hs |> fun _ => by omega, by rw [e20]; omega⟩
  · intro a n ⟨q, hq, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨q', hq', hc'⟩ := cX a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
    · obtain ⟨q', hq', hc'⟩ := cY a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl (by simpa using hc))
    · obtain ⟨q', hq', hc'⟩ := cO a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
    · obtain ⟨q', hq', hc'⟩ := cW a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
  · intro a n ⟨q, hq, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · obtain ⟨q', hq', hc'⟩ := cO a n ⟨_, List.mem_singleton_self _, hc⟩
      exact ⟨q', List.mem_cons_of_mem _ hq', hc'⟩
    · obtain ⟨q', hq', hc'⟩ := cW a n ⟨_, List.mem_singleton_self _, hc⟩
      exact ⟨q', List.mem_cons_of_mem _ hq', hc'⟩

/-- A call of G from the body: `compress(eax, esi, ecx, edx)`, to `scratch + o`. -/
theorem ccall_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) (hdx : s.gpr .edx = scrP s₀) {o : Nat} (ho : 4096 ≤ o)
    (ho' : o + 1024 ≤ 16384) (hcx : s.gpr .ecx = scrP s₀ + BitVec.ofNat 32 o) (hx : VG.Proof.Argon2.X86.Derive.GArg s₀ o (s.gpr .eax))
    (hy : VG.Proof.Argon2.X86.Derive.GArg s₀ o (s.gpr .esi)) {Q : State → Prop}
    (k : ∀ t, VG.Proof.Argon2.X86.Derive.Inv s₀ t → (∀ q ∈ calleeSaved, t.gpr q = s.gpr q) →
      Frame [⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨VG.Proof.Argon2.X86.Derive.scrB s₀, 4096⟩, callR s₀] s.mem t.mem →
      VG.Proof.Argon2.X86.blk t.mem (scrP s₀) o =
        compress (blockAt s.mem ((s.gpr .eax).setWidth 64)) (blockAt s.mem ((s.gpr .esi).setWidth 64)) → Q t) :
    WP isa (.frame (.push [.edx, .ecx, .esi, .eax]) (.call Impl.Argon2.X86.Derive.compressName
      Impl.Argon2.X86.compress) (.pop .eax 4)) s Q := by
  have hE := E_nat hp
  have hlo := hp.esp_lo
  have hhi := E_hi hp
  have hs := hp.scr_fits
  have esp := h.esp
  have nesp : Reg.esp ∉ [Reg.edx, .ecx, .esi, .eax] := by decide
  have fit : 4 * [Reg.edx, .ecx, .esi, .eax].length + 4 ≤ (s.gpr .esp).toNat := by
    simp only [List.length_cons, List.length_nil]; rw [esp]; omega
  have a0 := callEntry_arg fit nesp (i := 0) (by simp)
  have a1 := callEntry_arg fit nesp (i := 1) (by simp)
  have a2 := callEntry_arg fit nesp (i := 2) (by simp)
  have a3 := callEntry_arg fit nesp (i := 3) (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_succ, List.getElem_cons_zero,
    Nat.reduceAdd, Nat.reduceSub] at a0 a1 a2 a3
  rw [hdx] at a3
  rw [hcx] at a2
  obtain ⟨⟨RX, hRX, oX, bX, lX⟩, fX, X_out, X_scr, X_call⟩ := hx.facts hp ho ho'
  obtain ⟨⟨RY, hRY, oY, bY, lY⟩, fY, Y_out, Y_scr, Y_call⟩ := hy.facts hp ho ho'
  have eO : (scrP s₀ + BitVec.ofNat 32 o).setWidth 64 = VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 o :=
    HPrime.setWidth_add (by omega)
  have memW : ∀ R ∈ [memR s₀, VG.Proof.Argon2.X86.Derive.scrR s₀], R ∈ s.wr := fun R hR => by
    rw [h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact mem_mem hp
    · exact scr_mem hp
  have scrW : VG.Proof.Argon2.X86.Derive.scrR s₀ ∈ s.wr := memW _ (by simp)
  have cX : Covers [⟨(s.gpr .eax).setWidth 64, 1024⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RX, memW _ hRX, oX, bX, lX⟩
  have cY : Covers [⟨(s.gpr .esi).setWidth 64, 1024⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RY, memW _ hRY, oY, bY, lY⟩
  have cO : Covers [⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 o, 1024⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨VG.Proof.Argon2.X86.Derive.scrR s₀, scrW, o, rfl, ho'⟩
  have cW : Covers [⟨VG.Proof.Argon2.X86.Derive.scrB s₀, 4096⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨VG.Proof.Argon2.X86.Derive.scrR s₀, scrW, 0, by simp, by simp⟩
  have O_W : Region.Disjoint ⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 o, 1024⟩ ⟨VG.Proof.Argon2.X86.Derive.scrB s₀, 4096⟩ :=
    Offset.disjoint_base _ ho (by omega)
  have O_call : Region.Disjoint ⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 o, 1024⟩ (callR s₀) :=
    (call_disj hp (R := VG.Proof.Argon2.X86.Derive.scrR s₀) (by simp)).symm.sub_left (Offset.sub_base _ ho')
  have W_call : Region.Disjoint ⟨VG.Proof.Argon2.X86.Derive.scrB s₀, 4096⟩ (callR s₀) :=
    (call_disj hp (R := VG.Proof.Argon2.X86.Derive.scrR s₀) (by simp)).symm.sub_left (Region.sub_prefix (by decide))
  have e16 : (s.gpr .esp - BitVec.ofNat 32 16).toNat = (VG.Proof.Argon2.X86.Derive.E s₀).toNat - 16 := by rw [esp, sub_nat (by omega)]
  have e20 : (s.gpr .esp - BitVec.ofNat 32 20).toNat = (VG.Proof.Argon2.X86.Derive.E s₀).toNat - 20 := by rw [esp, sub_nat (by omega)]
  have cA : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 16).setWidth 64, 16⟩ (callR s₀) :=
    in_call hp (by omega) (by omega)
  have cR : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 20).setWidth 64, 4⟩ (callR s₀) :=
    in_call hp (by omega) (by omega)
  have a16 : argAddr (pushed [Reg.edx, .ecx, .esi, .eax] s).callEntry 0 =
      (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 := callEntry_argAddr0 _ _
  have ce : (pushed [Reg.edx, .ecx, .esi, .eax] s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 20 :=
    callEntry_esp' _ _
  have pre := VG.Proof.Argon2.X86.Derive.ccall_pre hp h hdx ho ho' hcx hx hy
  refine WP.callWith Proof.Argon2.X86.compress_verified.1 VG.Proof.Argon2.X86.Derive.compress_nosp (by simp) nesp
    (by rw [VG.Proof.Argon2.X86.Derive.compress_stack, esp]; simp only [List.length_cons, List.length_nil]; omega) pre
    fun t rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  simp only [VG.Proof.Argon2.X86.compressX86, arg_withRegions, State.withRegions_mem, a0, a1, a2] at post
  have cB : Region.Sub (below (s.gpr .esp) 20) (callR s₀) := in_call hp (by rw [e20]; omega) (by rw [e20]; omega)
  have cf := callEntry_frame fit nesp
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.zero_add] at cf
  rw [VG.Proof.Argon2.X86.Derive.compress_stack] at f'
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.zero_add] at f'
  rw [m₂, blockAt_keep cf (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact X_call.sub_right cB),
    blockAt_keep cf (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact Y_call.sub_right cB),
    Proof.Argon2.X86.blockAt_eq (by rw [add_nat (by omega)]; omega), VG.Proof.Argon2.X86.Derive.blk_shift] at post
  have f₁ : Frame [⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨VG.Proof.Argon2.X86.Derive.scrB s₀, 4096⟩, callR s₀] s.mem t.mem :=
    f'.sub fun q hq => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · exact ⟨callR s₀, by simp, cB⟩
  refine k t (h.step (cs' .esp (by decide)) (cs' .ebp (by decide)) rd' wr' (f₁.sub fun q hq => ?_)) cs' f₁ post
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨VG.Proof.Argon2.X86.Derive.scrR s₀, by simp, Offset.sub_base _ ho'⟩
  · exact ⟨VG.Proof.Argon2.X86.Derive.scrR s₀, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

end

end VG.Proof.Argon2.X86.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.Derive.FillDep`. -/
section

/-!
# Argon2 on x86 (32-bit): what keeps the filling state, and data-dependent addressing

`FS.keep`: the filling state is kept by steps that keep the parameters, the
position and counter in the locals, the cached address block and the
matrix. `dependentWord_ok`: J₁ and J₂ are the first word of the previous
block.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_addm wp_cmpi wp_ldm wp_stm)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState)
open VG.Proof.Argon2.X86 (blk)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  divisorOff strideOff j1Off j2Off)

/-- The offsets of the locals the filling state is about. -/
abbrev fsOffs : List Nat :=
  [divisorOff, segLenOff, laneLenOff, strideOff, passOff, sliceOff, laneOff, indexOff, counterOff]

theorem FS.keep {s₀ s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st s) (it : VG.Proof.Argon2.X86.Derive.Inv s₀ t) (hl : ∀ d ∈ VG.Proof.Argon2.X86.Derive.fsOffs, lw s₀ t d = lw s₀ s d)
    (hc : VG.Proof.Argon2.X86.blk t.mem (scrP s₀) 6144 = VG.Proof.Argon2.X86.blk s.mem (scrP s₀) 6144)
    (hm : ∀ k < (prm s₀).blocks, blockAt t.mem (matrixCell (memB s₀) k) = blockAt s.mem (matrixCell (memB s₀) k)) :
    VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st t := by
  refine ⟨it, Prm.of_lw h.pr fun d hd => hl d (by simp at hd ⊢; omega),
    h.pos.of_lw fun d hd => hl d (by simp at hd ⊢; omega), ?_, Represents.keep h.mem hm⟩
  obtain ⟨c0, c1, c2 | ⟨c3, c4⟩⟩ := h.cache
  · exact ⟨c0, by rw [hl _ (by simp)]; exact c1, .inl c2⟩
  · exact ⟨c0, by rw [hl _ (by simp)]; exact c1, .inr ⟨c3, by rw [hc]; exact c4⟩⟩

theorem FS.of_keep {s₀ s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st s) (k : Divide.Keep s t) : VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st t :=
  h.keep (h.inv.keep k) (fun d _ => lw_mem k.mem d) (by rw [k.mem]) fun _ _ => by rw [k.mem]

/-- `[B + o + d]` -/
theorem addr_shift (B : BitVec 32) (o d : Nat) : addr (B + BitVec.ofNat 32 o) d = addr B (o + d) := by
  simp only [addr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- A block of `scratch`. -/
theorem scr_blk (m : Mem) {o : Nat} (ho : o + 1024 ≤ 16384) :
    VG.Proof.Argon2.X86.blk m (scrP s₀) o = blockAt m (VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 o) := by
  have := hp.scr_fits
  have e : (scrP s₀ + BitVec.ofNat 32 o).setWidth 64 = VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 o := HPrime.setWidth_add (by omega)
  have f : (scrP s₀ + BitVec.ofNat 32 o).toNat + 1024 ≤ 2 ^ 32 := by rw [add_nat (by omega)]; omega
  rw [← e, Proof.Argon2.X86.blockAt_eq f, VG.Proof.Argon2.X86.Derive.blk_shift]

/-- A word of the matrix is kept by a store to the locals. -/
theorem mem_loc_store {m : Mem} {d : Nat} (hd : d + 4 ≤ 144) (v : BitVec 32) {a : Addr}
    (ha : (memR s₀).Contains a 4) :
    (m.writeW (addr (VG.Proof.Argon2.X86.Derive.E s₀) d) v).readW a 32 = m.readW a 32 :=
  ((Frame.refl [⟨addr (VG.Proof.Argon2.X86.Derive.E s₀) d, 4⟩] m).writeW (List.mem_singleton_self _) v (Region.contains_self _ _)).readW
    (r := memR s₀) ha (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (loc_disj hp hd (memR s₀) (by simp)).symm) (by decide)

/-- A store to the locals keeps what the filling state is about, but at the word `d`. -/
theorem FS.store {s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st s) (it : VG.Proof.Argon2.X86.Derive.Inv s₀ t) {d : Nat} (hd : d + 4 ≤ 144) (ha : d % 4 = 0)
    (hd' : d ∉ VG.Proof.Argon2.X86.Derive.fsOffs) {v : BitVec 32} (hm : t.mem = s.mem.writeW (addr (VG.Proof.Argon2.X86.Derive.E s₀) d) v) : VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st t := by
  have f : Frame [⟨addr (VG.Proof.Argon2.X86.Derive.E s₀) d, 4⟩] s.mem t.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) v (Region.contains_self _ _)
  refine h.keep it (fun e he => ?_) ?_ fun k hk => ?_
  · show t.mem.readW (addr (VG.Proof.Argon2.X86.Derive.E s₀) e) 32 = s.mem.readW (addr (VG.Proof.Argon2.X86.Derive.E s₀) e) 32
    rw [hm]
    simp only [VG.Proof.Argon2.X86.Derive.fsOffs, List.mem_cons, List.not_mem_nil, or_false] at he hd'
    have : (e + 4 ≤ d ∨ d + 4 ≤ e) ∧ e + 4 ≤ 236 := by
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [divisorOff, segLenOff, laneLenOff, strideOff, passOff, sliceOff, laneOff, indexOff,
        counterOff] at hd' ⊢ <;> omega
    exact lw_store hp (by omega) this.2 this.1.symm v
  · rw [VG.Proof.Argon2.X86.Derive.scr_blk hp t.mem (by decide), VG.Proof.Argon2.X86.Derive.scr_blk hp s.mem (by decide)]
    refine blockAt_keep f fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact (loc_disj hp hd (VG.Proof.Argon2.X86.Derive.scrR s₀) (by simp)).symm.sub_left (Offset.sub_base _ (by omega))
  · refine blockAt_keep f fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have hk' : k < blocksN s₀ := by rw [hp.blocks]; exact hk
    exact (loc_disj hp hd (memR s₀) (by simp)).symm.sub_left (cell_in_mem hk')

/-- `dependentWord`: J₁ and J₂ are the halves of the previous block's first word. -/
theorem dependentWord_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st s) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) :
    WP isa Impl.Argon2.X86.Derive.dependentWord s fun t => VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st t ∧
      lw s₀ t j2Off ++ lw s₀ t j1Off = (blockAt s.mem (matrixCell (memB s₀) (lane * (prm s₀).laneLen +
        (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) % (prm s₀).laneLen)))[0] := by
  have hm := hp.mem_fits
  have L8 := VG.Proof.Argon2.X86.Derive.laneLen_ge hp
  obtain ⟨cl, cf⟩ := VG.Proof.Argon2.X86.Derive.cell_fits hp hl (col := (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) %
    (prm s₀).laneLen) (Nat.mod_lt _ (by omega))
  unfold Impl.Argon2.X86.Derive.dependentWord
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.prevPointer_ok hp h.inv h.pr h.pos hl hs hi).mono fun s₁ ⟨a₁, k₁⟩ => ?_)
  generalize (lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) %
    (prm s₀).laneLen) = c at cl cf a₁ ⊢
  have h₁ := h.of_keep k₁
  have inP : ∀ o, o + 4 ≤ 1024 → (memR s₀).Contains (addr (memP s₀ + BitVec.ofNat 32 (c * 1024)) o) 4 :=
    fun o ho => by
      rw [VG.Proof.Argon2.X86.Derive.addr_shift, addr_eq (by omega)]
      exact Offset.contains_base _ (by omega) (by omega)
  have mW : memR s₀ ∈ s₁.wr := by rw [h₁.inv.wr]; exact mem_mem hp
  have in0 : InRegions (s₁.rd ++ s₁.wr) (addr (memP s₀ + BitVec.ofNat 32 (c * 1024)) 0) 4 :=
    ⟨_, List.mem_append_right _ mW, inP 0 (by decide)⟩
  refine wp_ldm a₁ in0 fun s₂ u₂ => ?_
  have h₂ := h₁.of_keep (Divide.Keep.of_upd u₂ (by simp))
  refine wp_stloc hp h₂.inv (d := j1Off) (by decide) fun s₃ i₃ v₃ o₃ g₃ m₃ => ?_
  have h₃ := h₂.store hp i₃ (d := j1Off) (by decide) (by decide) (by decide) m₃
  refine wp_ldm (by rw [g₃, u₂.other _ (by decide), a₁]) ⟨_, List.mem_append_right _ (by rw [h₃.inv.wr]; exact mem_mem hp),
    inP 4 (by decide)⟩ fun s₄ u₄ => ?_
  have h₄ := h₃.of_keep (Divide.Keep.of_upd u₄ (by simp))
  refine wp_stloc hp h₄.inv (d := j2Off) (by decide) fun t it vt ot gt mt => WP.block_nil ⟨?_, ?_⟩
  · exact h₄.store hp it (d := j2Off) (by decide) (by decide) (by decide) mt
  · rw [vt, ot j1Off (by decide) (by decide), lw_mem u₄.mem, v₃, u₄.gpr, m₃, VG.Proof.Argon2.X86.Derive.mem_loc_store hp (by decide) _ (inP 4 (by decide)),
      u₂.mem, u₂.gpr, k₁.mem, VG.Proof.Argon2.X86.Derive.cell_blk hp _ cl, Proof.Argon2.X86.Derive.blk_zero, VG.Proof.Argon2.X86.Derive.addr_shift, VG.Proof.Argon2.X86.Derive.addr_shift,
      Nat.add_zero (c * 1024)]

end


/-- Regions a step of the filling loops may write without changing the filling state. -/
def Outside (s₀ : State) (r : Region) : Prop :=
  r.Disjoint (locR s₀) ∧ r.Disjoint ⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 6144, 1024⟩ ∧ r.Disjoint (memR s₀)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem loc_word_sub {d : Nat} (hd : d + 4 ≤ 144) : Region.Sub ⟨addr (VG.Proof.Argon2.X86.Derive.E s₀) d, 4⟩ (locR s₀) := by
  have := E_hi hp
  exact sub32 (by rw [loc_addr hp (by omega)]; omega) (by rw [loc_addr hp (by omega)]; omega)

theorem FS.frame {s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st s) (it : VG.Proof.Argon2.X86.Derive.Inv s₀ t) {rs : List Region} (f : Frame rs s.mem t.mem)
    (ho : ∀ r ∈ rs, VG.Proof.Argon2.X86.Derive.Outside s₀ r) : VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st t := by
  refine h.keep it (fun d hd => ?_) ?_ fun k hk => ?_
  · have hd' : d + 4 ≤ 144 := by
      simp only [VG.Proof.Argon2.X86.Derive.fsOffs, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact f.readW (r := ⟨addr (VG.Proof.Argon2.X86.Derive.E s₀) d, 4⟩) (Region.contains_self _ _)
      (fun r hr => (ho r hr).1.symm.sub_left (VG.Proof.Argon2.X86.Derive.loc_word_sub hp hd')) (by decide)
  · rw [VG.Proof.Argon2.X86.Derive.scr_blk hp t.mem (by decide), VG.Proof.Argon2.X86.Derive.scr_blk hp s.mem (by decide)]
    exact blockAt_keep f fun r hr => (ho r hr).2.1.symm
  · have hk' : k < blocksN s₀ := by rw [hp.blocks]; exact hk
    exact blockAt_keep f fun r hr => (ho r hr).2.2.symm.sub_left (cell_in_mem hk')

theorem outside_scr {o n : Nat} (h : o + n ≤ 6144 ∨ (7168 ≤ o ∧ o + n ≤ 16384)) :
    VG.Proof.Argon2.X86.Derive.Outside s₀ ⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 o, n⟩ := by
  have sub : Region.Sub ⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 o, n⟩ (VG.Proof.Argon2.X86.Derive.scrR s₀) := Offset.sub_base _ (by omega)
  refine ⟨(loc_disj' hp (R := VG.Proof.Argon2.X86.Derive.scrR s₀) (by simp)).symm.sub_left sub, Offset.disjoint _ (by omega) (by omega)
    (by omega), hp.mem_scr.symm.sub_left sub⟩

theorem outside_call : VG.Proof.Argon2.X86.Derive.Outside s₀ (callR s₀) :=
  ⟨(loc_call hp).symm, (call_disj hp (R := VG.Proof.Argon2.X86.Derive.scrR s₀) (by simp)).sub_right (Offset.sub_base _ (by decide)),
    call_disj hp (R := memR s₀) (by simp)⟩

end
end VG.Proof.Argon2.X86.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.Derive.FillInput`. -/
section

/-!
# Argon2 on x86 (32-bit): the input of the address block

`clearAt_ok`: `clearAt d` zeroes `scratch[d, d + 1024)`. `aheader_ok`: the
seven words of the address-generation input block (§3.4.1.2), at
`scratch + 5120`. `input_ok`: after both, the block there is
`addressInput`, and the one at `scratch + 7168` is zero.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_addm wp_cmpi wp_ldm wp_stm)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState)
open VG.Proof.Argon2.X86 (blk ofWords blk_of_words)
open VG.Impl.Sha512.X86 (at_)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff)

/-- Words of `scratch`. -/
abbrev sw (s₀ : State) (m : Mem) (o : Nat) : BitVec 32 := m.readW (addr (scrP s₀) o) 32

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem scr_addr' {o : Nat} (ho : o < 16384) : addr (scrP s₀) o = VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 o :=
  addr_eq (by have := hp.scr_fits; omega)

/-- A word of `scratch` after a store to another, or the same. -/
theorem sw_store (m : Mem) {a b : Nat} (ha : a + 4 ≤ 16384) (hb : b + 4 ≤ 16384)
    (h : a = b ∨ a + 4 ≤ b ∨ b + 4 ≤ a) (v : BitVec 32) :
    VG.Proof.Argon2.X86.Derive.sw s₀ (m.writeW (addr (scrP s₀) a) v) b = if a = b then v else VG.Proof.Argon2.X86.Derive.sw s₀ m b := by
  by_cases e : a = b
  · subst e; rw [ite_eq_left rfl]; exact Mem.readW_writeW_self32 _ _ _
  · rw [ite_eq_right e, VG.Proof.Argon2.X86.Derive.sw, VG.Proof.Argon2.X86.Derive.sw, VG.Proof.Argon2.X86.Derive.scr_addr' hp (by omega), VG.Proof.Argon2.X86.Derive.scr_addr' hp (by omega)]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

/-- `n` stores of `eax = 0` to `[edx + 4k]`, with `edx = scratch + d`. -/
theorem zeros_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) {d : Nat} (hd : d + 1024 ≤ 16384)
    (hx : s.gpr .edx = scrP s₀ + BitVec.ofNat 32 d) (ha : s.gpr .eax = 0) :
    ∀ n ≤ 256, WP isa (.block ((List.range n).map fun k => Instr.store (at_ .edx (4 * k)) .eax)) s fun t =>
      VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ t.gpr = s.gpr ∧ Frame [⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 d, 1024⟩] s.mem t.mem ∧
      ∀ i < n, VG.Proof.Argon2.X86.Derive.sw s₀ t.mem (d + 4 * i) = 0
  | 0, _ => WP.block_nil ⟨h, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    have hs := hp.scr_fits
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append ((VG.Proof.Argon2.X86.Derive.zeros_ok h hd hx ha n (by omega)).mono fun t ⟨it, gt, ft, wt⟩ => ?_)
    have ea : addr (t.gpr .edx) (4 * n) = VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 (d + 4 * n) := by
      rw [gt, hx, VG.Proof.Argon2.X86.Derive.addr_shift, VG.Proof.Argon2.X86.Derive.scr_addr' hp (by omega)]
    have hc : (VG.Proof.Argon2.X86.Derive.scrR s₀).Contains (addr (t.gpr .edx) (4 * n)) 4 := by
      rw [ea]; exact Offset.contains_base _ (by omega) (by omega)
    have hc' : (⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 d, 1024⟩ : Region).Contains (addr (t.gpr .edx) (4 * n)) 4 := by
      rw [ea]; exact Offset.contains _ (by omega) (by omega) (by omega)
    refine Wp.wp_stm rfl ⟨_, by rw [it.wr]; exact scr_mem hp, hc⟩ fun t₁ u₁ => WP.block_nil
      ⟨it.store (R := VG.Proof.Argon2.X86.Derive.scrR s₀) (by simp) hc u₁, by rw [u₁.gpr, gt], ?_, fun i hi => ?_⟩
    · rw [u₁.mem]
      exact ft.writeW (List.mem_singleton_self _) _ hc'
    · rw [u₁.mem, gt, hx, VG.Proof.Argon2.X86.Derive.addr_shift, VG.Proof.Argon2.X86.Derive.sw_store hp _ (by omega) (by omega) (by omega), ha]
      by_cases e : d + 4 * n = d + 4 * i
      · rw [ite_eq_left e]
      · rw [ite_eq_right e]; exact wt i (by omega)

/-- `clearAt d`: zero `scratch[d, d + 1024)`. -/
theorem clearAt_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) {d : Nat} (hd : d + 1024 ≤ 16384) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ t, VG.Proof.Argon2.X86.Derive.Inv s₀ t → (∀ r, r ≠ .eax → r ≠ .edx → t.gpr r = s.gpr r) →
      Frame [⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 d, 1024⟩] s.mem t.mem → (∀ i < 256, VG.Proof.Argon2.X86.Derive.sw s₀ t.mem (d + 4 * i) = 0) →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.X86.Derive.clearAt d ++ is)) s Q := by
  unfold Impl.Argon2.X86.Derive.clearAt Impl.Argon2.X86.Derive.scratchAt
  simp only [List.cons_append, List.nil_append]
  refine wp_ldarg hp h (i := 15) (by decide) fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_movi fun s₃ u₃ => ?_
  have i₃ := ((h.upd u₁ (by decide) (by decide)).upd u₂ (by decide) (by decide)).upd u₃ (by decide) (by decide)
  refine WP.block_append ((VG.Proof.Argon2.X86.Derive.zeros_ok hp i₃ hd (by rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr]) u₃.gpr 256
    (Nat.le_refl _)).mono fun t ⟨it, gt, ft, wt⟩ => k t it (fun r a b => ?_) ?_ wt)
  · rw [gt, u₃.other _ a, u₂.other _ b, u₁.other _ b]
  · rw [show s.mem = s₃.mem by rw [u₃.mem, u₂.mem, u₁.mem]]; exact ft

end


/-- The seven words of the address-generation input block. -/
def hdr (s₀ : State) (pass lane slice c : Nat) : Nat → BitVec 32
  | 0 => BitVec.ofNat 32 pass
  | 1 => BitVec.ofNat 32 lane
  | 2 => BitVec.ofNat 32 slice
  | 3 => VG.X86.arg s₀ 14
  | 4 => VG.X86.arg s₀ 5
  | 5 => VG.X86.arg s₀ 0
  | _ => BitVec.ofNat 32 c

/-- The words of the input block after its first `n` words are written over `m`'s. -/
def HW (s₀ : State) (m : Mem) (pass lane slice c n : Nat) (m' : Mem) : Prop :=
  ∀ i < 256, VG.Proof.Argon2.X86.Derive.sw s₀ m' (5120 + 4 * i) =
    if i % 2 = 0 ∧ i < 2 * n then VG.Proof.Argon2.X86.Derive.hdr s₀ pass lane slice c (i / 2) else VG.Proof.Argon2.X86.Derive.sw s₀ m (5120 + 4 * i)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- One word of the header. -/
theorem hdr_step {m : Mem} {pass lane slice c n : Nat} (hn : n < 7) {u : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ u)
    (hx : u.gpr .edx = scrP s₀) (ha : u.gpr .eax = VG.Proof.Argon2.X86.Derive.hdr s₀ pass lane slice c n)
    (hw : VG.Proof.Argon2.X86.Derive.HW s₀ m pass lane slice c n u.mem) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.Argon2.X86.Derive.Inv s₀ t → t.gpr = u.gpr → Frame [⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] u.mem t.mem →
      VG.Proof.Argon2.X86.Derive.HW s₀ m pass lane slice c (n + 1) t.mem → WP isa (.block is) t Q) :
    WP isa (.block (.store (at_ .edx (5120 + 8 * n)) .eax :: is)) u Q := by
  have hs := hp.scr_fits
  have ea : addr (u.gpr .edx) (5120 + 8 * n) = VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 (5120 + 8 * n) := by
    rw [hx, VG.Proof.Argon2.X86.Derive.scr_addr' hp (by omega)]
  have hc : (VG.Proof.Argon2.X86.Derive.scrR s₀).Contains (addr (u.gpr .edx) (5120 + 8 * n)) 4 := by
    rw [ea]; exact Offset.contains_base _ (by omega) (by omega)
  have hc' : (⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 5120, 1024⟩ : Region).Contains (addr (u.gpr .edx) (5120 + 8 * n)) 4 := by
    rw [ea]; exact Offset.contains _ (by omega) (by omega) (by omega)
  refine Wp.wp_stm rfl ⟨_, by rw [h.wr]; exact scr_mem hp, hc⟩ fun t u₁ =>
    k t (h.store (R := VG.Proof.Argon2.X86.Derive.scrR s₀) (by simp) hc u₁) u₁.gpr ?_ fun i hi => ?_
  · rw [u₁.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc'
  · rw [u₁.mem, hx, VG.Proof.Argon2.X86.Derive.sw_store hp _ (by omega) (by omega) (by omega), ha, hw i hi]
    by_cases e : 5120 + 8 * n = 5120 + 4 * i
    · rw [ite_eq_left e, ite_eq_left (by omega), show i / 2 = n by omega]
    · rw [ite_eq_right e]
      by_cases c₁ : i % 2 = 0 ∧ i < 2 * n
      · rw [ite_eq_left c₁, ite_eq_left (by omega)]
      · rw [ite_eq_right c₁, ite_eq_right (by omega)]

theorem aheader_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) {pass slice lane index c : Nat}
    (ps : VG.Proof.Argon2.X86.Derive.Pos s₀ s pass slice lane index) (hc : lw s₀ s counterOff = BitVec.ofNat 32 c) :
    WP isa (.block Impl.Argon2.X86.Derive.addressHeader) s fun t => VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧
      (∀ r, r ≠ .eax → r ≠ .edx → t.gpr r = s.gpr r) ∧
      Frame [⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] s.mem t.mem ∧ VG.Proof.Argon2.X86.Derive.HW s₀ s.mem pass lane slice c 7 t.mem := by
  have fsub : ∀ r ∈ [(⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 5120, 1024⟩ : Region)],
      ∃ r' ∈ [memR s₀, VG.Proof.Argon2.X86.Derive.scrR s₀, VG.Proof.Argon2.X86.Derive.outR s₀, callR s₀], Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.Argon2.X86.Derive.scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
  unfold Impl.Argon2.X86.Derive.addressHeader
  refine wp_ldarg hp h (i := 15) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁ (by decide) (by decide)
  have w₀ : VG.Proof.Argon2.X86.Derive.HW s₀ s.mem pass lane slice c 0 s₁.mem := fun i _ => by
    rw [ite_eq_right (by omega), u₁.mem]
  -- Word 0: the pass.
  refine wp_ldloc hp i₁ (d := passOff) (by decide) fun s₂ u₂ => ?_
  refine VG.Proof.Argon2.X86.Derive.hdr_step hp (n := 0) (by decide) (i₁.upd u₂ (by decide) (by decide)) (by rw [u₂.other _ (by decide), u₁.gpr])
    (by rw [u₂.gpr, lw_mem u₁.mem, ps.pass]; rfl) (by rw [u₂.mem]; exact w₀) fun t₂ it₂ g₂ f₂ w₂ => ?_
  -- Word 1: the lane.
  refine wp_ldloc hp it₂ (d := laneOff) (by decide) fun s₃ u₃ => ?_
  refine VG.Proof.Argon2.X86.Derive.hdr_step hp (n := 1) (by decide) (it₂.upd u₃ (by decide) (by decide))
    (by rw [u₃.other _ (by decide), g₂, u₂.other _ (by decide), u₁.gpr])
    (by rw [u₃.gpr, lw_keep hp f₂ fsub (by decide), lw_mem u₂.mem, lw_mem u₁.mem, ps.lane]; rfl)
    (by rw [u₃.mem]; exact w₂) fun t₃ it₃ g₃ f₃ w₃ => ?_
  have F₃ : Frame [⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] s.mem t₃.mem := by
    rw [← u₁.mem, ← u₂.mem]; exact f₂.trans (by rw [← u₃.mem]; exact f₃)
  -- Word 2: the slice.
  refine wp_ldloc hp it₃ (d := sliceOff) (by decide) fun s₄ u₄ => ?_
  refine VG.Proof.Argon2.X86.Derive.hdr_step hp (n := 2) (by decide) (it₃.upd u₄ (by decide) (by decide))
    (by rw [u₄.other _ (by decide), g₃, u₃.other _ (by decide), g₂, u₂.other _ (by decide), u₁.gpr])
    (by rw [u₄.gpr, lw_keep hp F₃ fsub (by decide), ps.slice]; rfl)
    (by rw [u₄.mem]; exact w₃) fun t₄ it₄ g₄ f₄ w₄ => ?_
  have F₄ : Frame [⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] s.mem t₄.mem :=
    F₃.trans (by rw [← u₄.mem]; exact f₄)
  -- Words 3 to 5: the arguments.
  refine wp_ldarg hp it₄ (i := 14) (by decide) fun s₅ u₅ => ?_
  refine VG.Proof.Argon2.X86.Derive.hdr_step hp (n := 3) (by decide) (it₄.upd u₅ (by decide) (by decide))
    (by rw [u₅.other _ (by decide), g₄, u₄.other _ (by decide), g₃, u₃.other _ (by decide), g₂,
      u₂.other _ (by decide), u₁.gpr])
    (by rw [u₅.gpr]; rfl) (by rw [u₅.mem]; exact w₄) fun t₅ it₅ g₅ f₅ w₅ => ?_
  have F₅ : Frame [⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] s.mem t₅.mem :=
    F₄.trans (by rw [← u₅.mem]; exact f₅)
  refine wp_ldarg hp it₅ (i := 5) (by decide) fun s₆ u₆ => ?_
  refine VG.Proof.Argon2.X86.Derive.hdr_step hp (n := 4) (by decide) (it₅.upd u₆ (by decide) (by decide))
    (by rw [u₆.other _ (by decide), g₅, u₅.other _ (by decide), g₄, u₄.other _ (by decide), g₃,
      u₃.other _ (by decide), g₂, u₂.other _ (by decide), u₁.gpr])
    (by rw [u₆.gpr]; rfl) (by rw [u₆.mem]; exact w₅) fun t₆ it₆ g₆ f₆ w₆ => ?_
  have F₆ : Frame [⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] s.mem t₆.mem :=
    F₅.trans (by rw [← u₆.mem]; exact f₆)
  refine wp_ldarg hp it₆ (i := 0) (by decide) fun s₇ u₇ => ?_
  refine VG.Proof.Argon2.X86.Derive.hdr_step hp (n := 5) (by decide) (it₆.upd u₇ (by decide) (by decide))
    (by rw [u₇.other _ (by decide), g₆, u₆.other _ (by decide), g₅, u₅.other _ (by decide), g₄,
      u₄.other _ (by decide), g₃, u₃.other _ (by decide), g₂, u₂.other _ (by decide), u₁.gpr])
    (by rw [u₇.gpr]; rfl) (by rw [u₇.mem]; exact w₆) fun t₇ it₇ g₇ f₇ w₇ => ?_
  have F₇ : Frame [⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] s.mem t₇.mem :=
    F₆.trans (by rw [← u₇.mem]; exact f₇)
  -- Word 6: the counter.
  refine wp_ldloc hp it₇ (d := counterOff) (by decide) fun s₈ u₈ => ?_
  refine VG.Proof.Argon2.X86.Derive.hdr_step hp (n := 6) (by decide) (it₇.upd u₈ (by decide) (by decide))
    (by rw [u₈.other _ (by decide), g₇, u₇.other _ (by decide), g₆, u₆.other _ (by decide), g₅,
      u₅.other _ (by decide), g₄, u₄.other _ (by decide), g₃, u₃.other _ (by decide), g₂,
      u₂.other _ (by decide), u₁.gpr])
    (by rw [u₈.gpr, lw_keep hp F₇ fsub (by decide), hc]; rfl)
    (by rw [u₈.mem]; exact w₇) fun t it g f w => WP.block_nil ⟨it, fun r a b => ?_,
      F₇.trans (by rw [← u₈.mem]; exact f), w⟩
  rw [g, u₈.other _ a, g₇, u₇.other _ a, g₆, u₆.other _ a, g₅, u₅.other _ a, g₄, u₄.other _ a, g₃,
    u₃.other _ a, g₂, u₂.other _ a, u₁.other _ b]

end

theorem zero_append32 (x : BitVec 32) : 0#32 ++ x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_ofNat]
  simp
  have := x.isLt
  omega

/-- The input block's words. -/
def inWord (s₀ : State) (pass lane slice c : Nat) (i : Nat) : BitVec 32 :=
  if i % 2 = 0 ∧ i < 14 then VG.Proof.Argon2.X86.Derive.hdr s₀ pass lane slice c (i / 2) else 0

theorem input_words {s₀ : State} (hp : DPre s₀) {pass lane slice c : Nat} (h₁ : pass < 2 ^ 32)
    (h₂ : lane < 2 ^ 32) (h₃ : slice < 2 ^ 32) (h₄ : c < 2 ^ 32) :
    ofWords (VG.Proof.Argon2.X86.Derive.inWord s₀ pass lane slice c) = Proof.Argon2.addressInput (prm s₀) pass lane slice c := by
  have eb : (VG.X86.arg s₀ 14).toNat = (prm s₀).blocks := hp.blocks
  have ep : (VG.X86.arg s₀ 5).toNat = (prm s₀).passes := rfl
  have ek : (VG.X86.arg s₀ 0).toNat = (prm s₀).variant.code := (variant_code hp.kind_le).symm
  apply Vector.ext
  intro j hj
  simp only [ofWords, Vector.getElem_ofFn, Proof.Argon2.addressInput, Vector.getElem_set, zeroBlock,
    Vector.getElem_replicate, VG.Proof.Argon2.X86.Derive.inWord]
  rw [ite_eq_right (by omega)]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ 7 ≤ j) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | hj7
  · simp [VG.Proof.Argon2.X86.Derive.hdr]; rw [VG.Proof.Argon2.X86.Derive.zero_append32, Wp.toNat_ofNat_lt h₁]
  · simp [VG.Proof.Argon2.X86.Derive.hdr]; rw [VG.Proof.Argon2.X86.Derive.zero_append32, Wp.toNat_ofNat_lt h₂]
  · simp [VG.Proof.Argon2.X86.Derive.hdr]; rw [VG.Proof.Argon2.X86.Derive.zero_append32, Wp.toNat_ofNat_lt h₃]
  · simp [VG.Proof.Argon2.X86.Derive.hdr]; rw [VG.Proof.Argon2.X86.Derive.zero_append32, eb]
  · simp [VG.Proof.Argon2.X86.Derive.hdr]; rw [VG.Proof.Argon2.X86.Derive.zero_append32, ep]
  · simp [VG.Proof.Argon2.X86.Derive.hdr]; rw [VG.Proof.Argon2.X86.Derive.zero_append32, ek]
  · simp [VG.Proof.Argon2.X86.Derive.hdr]; rw [VG.Proof.Argon2.X86.Derive.zero_append32, Wp.toNat_ofNat_lt h₄]
  · rw [ite_eq_right (by omega)]
    simp (disch := omega) only [ite_eq_right]
    rfl

theorem ofWords_zero : ofWords (fun _ => 0) = zeroBlock := by
  apply Vector.ext
  intro j hj
  simp only [ofWords, Vector.getElem_ofFn, zeroBlock, Vector.getElem_replicate]
  rfl

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- A word of `scratch` outside a frame's region of `scratch`. -/
theorem sw_frame {m m' : Mem} {a n : Nat} (f : Frame [⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 a, n⟩] m m') {o : Nat}
    (h : o + 4 ≤ a ∨ a + n ≤ o) (ho : o + 4 ≤ 16384) (hn : a + n ≤ 16384) : VG.Proof.Argon2.X86.Derive.sw s₀ m' o = VG.Proof.Argon2.X86.Derive.sw s₀ m o := by
  rw [VG.Proof.Argon2.X86.Derive.sw, VG.Proof.Argon2.X86.Derive.sw, VG.Proof.Argon2.X86.Derive.scr_addr' hp (by omega)]
  refine f.readW (r := ⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint _ h (by omega) (by omega)

/-- The address-generation input block at `scratch + 5120`, and a zero block at `scratch + 7168`. -/
theorem input_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) {pass slice lane index c : Nat}
    (ps : VG.Proof.Argon2.X86.Derive.Pos s₀ s pass slice lane index) (hc : lw s₀ s counterOff = BitVec.ofNat 32 c)
    (h₁ : pass < 2 ^ 32) (h₂ : lane < 2 ^ 32) (h₃ : slice < 2 ^ 32) (h₄ : c < 2 ^ 32) :
    WP isa (.block (Impl.Argon2.X86.Derive.clearAt 5120 ++ (Impl.Argon2.X86.Derive.clearAt 7168 ++
      Impl.Argon2.X86.Derive.addressHeader))) s fun t => VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧
      (∀ r, r ≠ .eax → r ≠ .edx → t.gpr r = s.gpr r) ∧
      Frame [⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 5120, 1024⟩, ⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 7168, 1024⟩] s.mem t.mem ∧
      VG.Proof.Argon2.X86.blk t.mem (scrP s₀) 5120 = Proof.Argon2.addressInput (prm s₀) pass lane slice c ∧
      VG.Proof.Argon2.X86.blk t.mem (scrP s₀) 7168 = zeroBlock := by
  have fsub : ∀ d, d + 1024 ≤ 16384 → ∀ r ∈ [(⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 d, 1024⟩ : Region)],
      ∃ r' ∈ [memR s₀, VG.Proof.Argon2.X86.Derive.scrR s₀, VG.Proof.Argon2.X86.Derive.outR s₀, callR s₀], Region.Sub r r' := fun d hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.Argon2.X86.Derive.scrR s₀, by simp, Offset.sub_base _ hd⟩
  refine VG.Proof.Argon2.X86.Derive.clearAt_ok hp h (d := 5120) (by decide) fun t₁ i₁ g₁ f₁ z₁ => ?_
  refine VG.Proof.Argon2.X86.Derive.clearAt_ok hp i₁ (d := 7168) (by decide) fun t₂ i₂ g₂ f₂ z₂ => ?_
  have L : ∀ d, d + 4 ≤ 144 → lw s₀ t₂ d = lw s₀ s d := fun d hd => by
    rw [lw_keep hp f₂ (fsub _ (by decide)) hd, lw_keep hp f₁ (fsub _ (by decide)) hd]
  refine (VG.Proof.Argon2.X86.Derive.aheader_ok hp i₂ (pass := pass) (slice := slice) (lane := lane) (index := index) (c := c)
    (ps.of_lw fun d hd => L d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide)) (by rw [L _ (by decide)]; exact hc)).mono
    fun t ⟨it, gt, ft, wt⟩ => ⟨it, fun r a b => by rw [gt r a b, g₂ r a b, g₁ r a b], ?_, ?_, ?_⟩
  · refine (Frame.trans (f₁.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩)
      (f₂.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩)).trans
      (ft.sub fun r hr => ⟨⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 5120, 1024⟩, by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩)
  · rw [blk_of_words (f := VG.Proof.Argon2.X86.Derive.inWord s₀ pass lane slice c) fun i hi => ?_, VG.Proof.Argon2.X86.Derive.input_words hp h₁ h₂ h₃ h₄]
    have w := wt i hi
    simp only [VG.Proof.Argon2.X86.Derive.sw] at w
    rw [w, VG.Proof.Argon2.X86.Derive.inWord]
    by_cases e : i % 2 = 0 ∧ i < 2 * 7
    · rw [ite_eq_left e, ite_eq_left (by omega)]
    · rw [ite_eq_right e, ite_eq_right (by omega), ← VG.Proof.Argon2.X86.Derive.sw, VG.Proof.Argon2.X86.Derive.sw_frame hp f₂ (by omega) (by omega) (by decide)]
      exact z₁ i hi
  · rw [blk_of_words (f := fun _ => 0) fun i hi => ?_, VG.Proof.Argon2.X86.Derive.ofWords_zero]
    rw [← VG.Proof.Argon2.X86.Derive.sw, VG.Proof.Argon2.X86.Derive.sw_frame hp ft (by omega) (by omega) (by decide)]
    exact z₂ i hi

end
end VG.Proof.Argon2.X86.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.Derive.FillCache`. -/
section

/-!
# Argon2 on x86 (32-bit): the address block and the random word

`stage_ok`: G of two blocks of `scratch` to a third. `addressCalls_ok`: the
address block for the counter, G(0, G(0, input)), at `scratch + 6144`.
`addressCache_ok`: J₁, J₂ from the cached address block, regenerated when
the index enters a new group of 128. `randomSource_ok`: J₁, J₂ are the
random word of `FillStep.random`.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_addm wp_cmpi wp_ldm wp_stm wp_andi wp_shr)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState compress addressBlock)
open VG.Proof.Argon2.X86 (blk)
open VG.Impl.Sha512.X86 (at_)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem scr_blockAt (m : Mem) {o : Nat} (ho : o + 1024 ≤ 16384) :
    blockAt m ((scrP s₀ + BitVec.ofNat 32 o).setWidth 64) = VG.Proof.Argon2.X86.blk m (scrP s₀) o := by
  have := hp.scr_fits
  rw [Proof.Argon2.X86.blockAt_eq (by rw [add_nat (by omega)]; omega), VG.Proof.Argon2.X86.Derive.blk_shift]

/-- `stage x y out`: G of the blocks at `scratch + x` and `scratch + y` to `scratch + out`. -/
theorem stage_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) {x y o : Nat} (ho : 4096 ≤ o) (ho' : o + 1024 ≤ 16384)
    (hx : 4096 ≤ x) (hx' : x + 1024 ≤ 16384) (hxo : x + 1024 ≤ o ∨ o + 1024 ≤ x)
    (hy : 4096 ≤ y) (hy' : y + 1024 ≤ 16384) (hyo : y + 1024 ≤ o ∨ o + 1024 ≤ y) :
    WP isa (Impl.Argon2.X86.Derive.stage x y o) s fun t => VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧
      (∀ q ∈ [Reg.ebx, .edi, .ebp, .esp], t.gpr q = s.gpr q) ∧
      Frame [⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨VG.Proof.Argon2.X86.Derive.scrB s₀, 4096⟩, callR s₀] s.mem t.mem ∧
      VG.Proof.Argon2.X86.blk t.mem (scrP s₀) o = compress (VG.Proof.Argon2.X86.blk s.mem (scrP s₀) x) (VG.Proof.Argon2.X86.blk s.mem (scrP s₀) y) := by
  unfold Impl.Argon2.X86.Derive.stage Impl.Argon2.X86.Derive.compressCall
  refine WP.seq (wp_ldarg hp h (i := 15) (by decide) fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_addi fun s₃ u₃ =>
    wp_mov fun s₄ u₄ => wp_addi fun s₅ u₅ => wp_mov fun s₆ u₆ => wp_addi fun s₇ u₇ => WP.block_nil ?_)
  have i₇ := ((((((h.upd u₁ (by decide) (by decide)).upd u₂ (by decide) (by decide)).upd u₃ (by decide)
    (by decide)).upd u₄ (by decide) (by decide)).upd u₅ (by decide) (by decide)).upd u₆ (by decide)
    (by decide)).upd u₇ (by decide) (by decide)
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have dx : s₇.gpr .edx = scrP s₀ := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  have ax : s₇.gpr .eax = scrP s₀ + BitVec.ofNat 32 x := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.gpr, u₁.gpr]
  have sx : s₇.gpr .esi = scrP s₀ + BitVec.ofNat 32 y := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  have cx : s₇.gpr .ecx = scrP s₀ + BitVec.ofNat 32 o := by
    rw [u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  refine VG.Proof.Argon2.X86.Derive.ccall_ok hp i₇ dx ho ho' cx (by rw [ax]; exact .inr ⟨x, hx, hx', hxo, rfl⟩)
    (by rw [sx]; exact .inr ⟨y, hy, hy', hyo, rfl⟩) fun t it cs f post => ⟨it, fun q hq => ?_, by rw [← m₇]; exact f,
      by rw [post, ax, sx, VG.Proof.Argon2.X86.Derive.scr_blockAt hp _ hx', VG.Proof.Argon2.X86.Derive.scr_blockAt hp _ hy', m₇]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> rw [cs _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]


/-- A block of `scratch` at `d`, outside the regions G's call at `o` writes. -/
theorem stage_keep {m m' : Mem} {o : Nat} (ho : 4096 ≤ o) (ho' : o + 1024 ≤ 16384)
    (f : Frame [⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨VG.Proof.Argon2.X86.Derive.scrB s₀, 4096⟩, callR s₀] m m') {d : Nat} (hd : 4096 ≤ d)
    (hd' : d + 1024 ≤ 16384) (hdo : d + 1024 ≤ o ∨ o + 1024 ≤ d) :
    VG.Proof.Argon2.X86.blk m' (scrP s₀) d = VG.Proof.Argon2.X86.blk m (scrP s₀) d := by
  rw [VG.Proof.Argon2.X86.Derive.scr_blk hp m' hd', VG.Proof.Argon2.X86.Derive.scr_blk hp m hd']
  refine blockAt_keep f fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint _ hdo (by omega) (by omega)
  · exact Offset.disjoint_base _ hd (by omega)
  · exact (call_disj hp (R := VG.Proof.Argon2.X86.Derive.scrR s₀) (by simp)).symm.sub_left (Offset.sub_base _ hd')

omit hp in
theorem stage_frame {m m' : Mem} {o : Nat} (ho' : o + 1024 ≤ 16384)
    (f : Frame [⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨VG.Proof.Argon2.X86.Derive.scrB s₀, 4096⟩, callR s₀] m m') :
    Frame [VG.Proof.Argon2.X86.Derive.scrR s₀, callR s₀] m m' :=
  f.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.Argon2.X86.Derive.scrR s₀, by simp, Offset.sub_base _ ho'⟩
    · exact ⟨VG.Proof.Argon2.X86.Derive.scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨callR s₀, by simp, fun _ h => h⟩

/-- `addressCalls`: the address block for the counter `c` at `scratch + 6144`. -/
theorem addressCalls_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) {pass slice lane index c : Nat}
    (ps : VG.Proof.Argon2.X86.Derive.Pos s₀ s pass slice lane index) (hc : lw s₀ s counterOff = BitVec.ofNat 32 c)
    (h₁ : pass < 2 ^ 32) (h₂ : lane < 2 ^ 32) (h₃ : slice < 2 ^ 32) (h₄ : c < 2 ^ 32) :
    WP isa Impl.Argon2.X86.Derive.addressCalls s fun t => VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧
      (∀ q ∈ [Reg.ebx, .edi, .ebp, .esp], t.gpr q = s.gpr q) ∧ Frame [VG.Proof.Argon2.X86.Derive.scrR s₀, callR s₀] s.mem t.mem ∧
      VG.Proof.Argon2.X86.blk t.mem (scrP s₀) 6144 = addressBlock (prm s₀) pass lane slice c := by
  unfold Impl.Argon2.X86.Derive.addressCalls
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.input_ok hp h ps hc h₁ h₂ h₃ h₄).mono fun t₁ ⟨i₁, g₁, f₁, b₁, z₁⟩ => ?_)
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.stage_ok hp i₁ (x := 7168) (y := 5120) (o := 4096) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).mono fun t₂ ⟨i₂, g₂, f₂, b₂⟩ => ?_)
  refine (VG.Proof.Argon2.X86.Derive.stage_ok hp i₂ (x := 7168) (y := 4096) (o := 6144) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).mono fun t ⟨it, gt, ft, bt⟩ =>
      ⟨it, fun q hq => ?_, ?_, ?_⟩
  · rw [gt q hq, g₂ q hq]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)
  · refine Frame.trans (f₁.sub fun r hr => ?_) ((VG.Proof.Argon2.X86.Derive.stage_frame (by decide) f₂).trans (VG.Proof.Argon2.X86.Derive.stage_frame (by decide) ft))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.Argon2.X86.Derive.scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨VG.Proof.Argon2.X86.Derive.scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
  · rw [bt, VG.Proof.Argon2.X86.Derive.stage_keep hp (by decide) (by decide) f₂ (d := 7168) (by decide) (by decide) (by decide), b₂, z₁, b₁]
    rfl
end


theorem and127 {n : Nat} (h : n < 2 ^ 32) : BitVec.ofNat 32 n &&& 127 = BitVec.ofNat 32 (n % 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, Wp.toNat_ofNat_lt h, Wp.toNat_ofNat_lt (by omega),
    show (127 : BitVec 32).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem shr7 {n : Nat} (h : n < 2 ^ 32) : BitVec.ofNat 32 n >>> 7 = BitVec.ofNat 32 (n / 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Wp.toNat_ofNat_lt h, Wp.toNat_ofNat_lt (by omega), Nat.shiftRight_eq_div_pow]

theorem dbl32 (n : Nat) : BitVec.ofNat 32 n + BitVec.ofNat 32 n = BitVec.ofNat 32 (2 * n) := by
  rw [BitVec.ofNat_add_ofNat, Nat.two_mul]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `cacheWord`: J₁ and J₂ are word `index mod 128` of the cached address block. -/
theorem cacheWord_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st s) (hi : index < 2 ^ 30) :
    WP isa (.block Impl.Argon2.X86.Derive.cacheWord) s fun t => VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st t ∧
      lw s₀ t j2Off ++ lw s₀ t j1Off = (VG.Proof.Argon2.X86.blk s.mem (scrP s₀) 6144)[index % 128]'(Nat.mod_lt _ (by decide)) := by
  have hs := hp.scr_fits
  have e8 : 8 * (index % 128) < 1024 := by omega
  unfold Impl.Argon2.X86.Derive.cacheWord
  refine wp_ldloc hp h.inv (d := indexOff) (by decide) fun s₁ u₁ => wp_andi fun s₂ u₂ => wp_add fun s₃ u₃ _ =>
    wp_add fun s₄ u₄ _ => wp_add fun s₅ u₅ _ => ?_
  have h₅ := (((((h.of_keep (Divide.Keep.of_upd u₁ (by simp))).of_keep (Divide.Keep.of_upd u₂ (by simp))).of_keep
    (Divide.Keep.of_upd u₃ (by simp))).of_keep (Divide.Keep.of_upd u₄ (by simp))).of_keep
    (Divide.Keep.of_upd u₅ (by simp)))
  have a₅ : s₅.gpr .eax = BitVec.ofNat 32 (8 * (index % 128)) := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, h.pos.index, VG.Proof.Argon2.X86.Derive.and127 (by omega), VG.Proof.Argon2.X86.Derive.dbl32, VG.Proof.Argon2.X86.Derive.dbl32, VG.Proof.Argon2.X86.Derive.dbl32]
    congr 1; omega
  refine wp_addm h₅.inv.ebp (h₅.inv.arg_in hp (i := 15) (by decide)) fun s₆ u₆ => ?_
  have h₆ := h₅.of_keep (Divide.Keep.of_upd u₆ (by simp))
  have a₆ : s₆.gpr .eax = scrP s₀ + BitVec.ofNat 32 (8 * (index % 128)) := by
    rw [u₆.gpr, h₅.inv.arg hp (by decide), a₅, BitVec.add_comm]; rfl
  have inS : ∀ o, o + 4 ≤ 1024 → InRegions (s₆.rd ++ s₆.wr) (addr (s₆.gpr .eax) (6144 + o)) 4 := fun o ho => by
    rw [a₆, VG.Proof.Argon2.X86.Derive.addr_shift, VG.Proof.Argon2.X86.Derive.scr_addr' hp (by omega), h₆.inv.wr]
    exact ⟨VG.Proof.Argon2.X86.Derive.scrR s₀, List.mem_append_right _ (scr_mem hp), Offset.contains_base _ (by omega) (by omega)⟩
  refine wp_ldm rfl (inS 0 (by decide)) fun s₇ u₇ => ?_
  have h₇ := h₆.of_keep (Divide.Keep.of_upd u₇ (by simp))
  refine wp_stloc hp h₇.inv (d := j1Off) (by decide) fun s₈ i₈ v₈ o₈ g₈ m₈ => ?_
  have h₈ := h₇.store hp i₈ (d := j1Off) (by decide) (by decide) (by decide) m₈
  have e₈ : s₈.gpr .eax = s₆.gpr .eax := by rw [g₈, u₇.other _ (by decide)]
  have in₈ : InRegions (s₈.rd ++ s₈.wr) (addr (s₆.gpr .eax) (6144 + 4)) 4 := by
    rw [i₈.rd, i₈.wr, ← h₆.inv.rd, ← h₆.inv.wr]
    exact inS 4 (by decide)
  refine wp_ldm e₈ in₈ fun s₉ u₉ => ?_
  have h₉ := h₈.of_keep (Divide.Keep.of_upd u₉ (by simp))
  refine wp_stloc hp h₉.inv (d := j2Off) (by decide) fun t it vt ot gt mt => WP.block_nil ⟨?_, ?_⟩
  · exact h₉.store hp it (d := j2Off) (by decide) (by decide) (by decide) mt
  · have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    rw [vt, ot j1Off (by decide) (by decide), lw_mem u₉.mem, v₈, u₉.gpr, m₈, a₆, VG.Proof.Argon2.X86.Derive.addr_shift,
      scr_loc hp (by decide) (by omega), u₇.gpr, a₆, VG.Proof.Argon2.X86.Derive.addr_shift, u₇.mem, u₆.mem, m₅,
      VG.Proof.Argon2.X86.Derive.blk_get _ _ _ _ (Nat.mod_lt _ (by decide))]
    rw [show 8 * (index % 128) + 6148 = 6144 + 8 * (index % 128) + 4 by omega,
      show 8 * (index % 128) + 6144 = 6144 + 8 * (index % 128) by omega]

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

omit hp in
/-- The cached address block is that of `c`. -/
theorem cached {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st s) {c : Nat} (hc : 1 ≤ c) (hc' : c < 2 ^ 32)
    (he : lw s₀ s counterOff = BitVec.ofNat 32 c) :
    VG.Proof.Argon2.X86.blk s.mem (scrP s₀) 6144 = addressBlock (prm s₀) pass lane slice c := by
  obtain ⟨c0, c1, c2 | ⟨_, c4⟩⟩ := h.cache
  · rw [he, c2] at c1
    have := congrArg BitVec.toNat c1
    rw [Wp.toNat_ofNat_lt hc'] at this
    exact absurd this (by simp; omega)
  · rw [c4]
    rw [he] at c1
    have := congrArg BitVec.toNat c1
    rw [Wp.toNat_ofNat_lt hc', Wp.toNat_ofNat_lt c0] at this
    rw [this]

/-- `cacheCheck`: `eax :=` the counter of the index's group; ZF if it is cached. -/
theorem cacheCheck_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st s) (hi : index < (prm s₀).segmentLen) :
    WP isa (.block Impl.Argon2.X86.Derive.cacheCheck) s fun t => VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st t ∧
      t.gpr .eax = BitVec.ofNat 32 (index / 128 + 1) ∧
      t.zf = some (BitVec.ofNat 32 (index / 128 + 1) - lw s₀ t counterOff == 0) := by
  have sl := VG.Proof.Argon2.X86.Derive.segLen_lt hp
  unfold Impl.Argon2.X86.Derive.cacheCheck
  refine wp_ldloc hp h.inv (d := indexOff) (by decide) fun s₁ u₁ => wp_shr (n := 7) (by decide)
    fun s₂ u₂ _ => wp_addi fun s₃ u₃ => ?_
  have h₃ := ((h.of_keep (Divide.Keep.of_upd u₁ (by simp))).of_keep (Divide.Keep.of_upd u₂ (by simp))).of_keep
    (Divide.Keep.of_upd u₃ (by simp))
  have a₃ : s₃.gpr .eax = BitVec.ofNat 32 (index / 128 + 1) := by
    rw [u₃.gpr, u₂.gpr, u₁.gpr, h.pos.index, VG.Proof.Argon2.X86.Derive.shr7 (by omega), show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_add_ofNat]
  refine wp_cmpm h₃.inv.ebp (loc_in' hp h₃.inv (d := counterOff) (by decide)) fun s₄ f₄ _ z₄ => WP.block_nil ?_
  exact ⟨h₃.of_keep (Divide.Keep.of_fupd f₄), by rw [f₄.gpr, a₃], by rw [z₄, a₃, lw_mem f₄.mem]⟩

/-- The address block of the index's group, regenerated unless it is cached. -/
theorem cacheFill_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h₄ : VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) (a₃ : s.gpr .eax = BitVec.ofNat 32 (index / 128 + 1))
    (z₄ : s.zf = some (BitVec.ofNat 32 (index / 128 + 1) - lw s₀ s counterOff == 0)) :
    WP isa (.ite .e (.block []) (.seq (.block [Impl.Argon2.X86.Derive.st counterOff .eax])
      Impl.Argon2.X86.Derive.addressCalls)) s fun t => VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index (index / 128 + 1) st t ∧
      VG.Proof.Argon2.X86.blk t.mem (scrP s₀) 6144 = addressBlock (prm s₀) pass lane slice (index / 128 + 1) := by
  have sl := VG.Proof.Argon2.X86.Derive.segLen_lt hp
  have hlt := hp.lanes_lt
  refine WP.ite (BitVec.ofNat 32 (index / 128 + 1) - lw s₀ s counterOff == 0) z₄
    (fun hb => ?_) fun hb => ?_
  · have ce : lw s₀ s counterOff = BitVec.ofNat 32 (index / 128 + 1) := by
      have e := beq_iff_eq.mp hb
      exact ((BitVec.sub_eq_iff_eq_add.mp e).trans (by simp)).symm
    have cb := VG.Proof.Argon2.X86.Derive.cached h₄ (c := index / 128 + 1) (by omega) (by omega) ce
    exact WP.block_nil ⟨⟨h₄.inv, h₄.pr, h₄.pos, ⟨by omega, ce, .inr ⟨by omega, cb⟩⟩, h₄.mem⟩, cb⟩
  · refine WP.seq (wp_stloc hp h₄.inv (d := counterOff) (by decide) fun s₅ i₅ v₅ o₅ g₅ m₅ => WP.block_nil ?_)
    have L₅ : ∀ d ∈ VG.Proof.Argon2.X86.Derive.fsOffs, d ≠ counterOff → lw s₀ s₅ d = lw s₀ s d := fun d hd hd' => by
      simp only [VG.Proof.Argon2.X86.Derive.fsOffs, List.mem_cons, List.not_mem_nil, or_false] at hd
      refine o₅ d ?_ ?_ <;>
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | decide | exact absurd rfl hd'
    refine (VG.Proof.Argon2.X86.Derive.addressCalls_ok hp i₅ (index := index) (c := index / 128 + 1)
      (h₄.pos.of_lw fun d hd => L₅ d (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl <;> decide) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl <;> decide))
      (by rw [v₅, a₃]) hpass (by omega) (by omega) (by omega)).mono
      fun t ⟨it, _, ft, bt⟩ => ⟨?_, bt⟩
    have fsub : ∀ r ∈ [VG.Proof.Argon2.X86.Derive.scrR s₀, callR s₀], ∃ r' ∈ [memR s₀, VG.Proof.Argon2.X86.Derive.scrR s₀, VG.Proof.Argon2.X86.Derive.outR s₀, callR s₀], Region.Sub r r' :=
      fun r hr => ⟨r, by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp,
        fun _ h => h⟩
    have Lt : ∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ s₅ d := fun d hd => lw_keep hp ft fsub hd
    refine ⟨it, Prm.of_lw h₄.pr fun d hd => ?_, h₄.pos.of_lw fun d hd => ?_, ⟨by omega,
      by rw [Lt _ (by decide), v₅, a₃], .inr ⟨by omega, bt⟩⟩, Represents.keep h₄.mem fun k hk => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rw [Lt d (by rcases hd with rfl | rfl | rfl | rfl <;> decide)]
      exact L₅ d (by simp only [VG.Proof.Argon2.X86.Derive.fsOffs]; rcases hd with rfl | rfl | rfl | rfl <;> simp)
        (by rcases hd with rfl | rfl | rfl | rfl <;> decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rw [Lt d (by rcases hd with rfl | rfl | rfl | rfl <;> decide)]
      exact L₅ d (by simp only [VG.Proof.Argon2.X86.Derive.fsOffs]; rcases hd with rfl | rfl | rfl | rfl <;> simp)
        (by rcases hd with rfl | rfl | rfl | rfl <;> decide)
    · have hk' : k < blocksN s₀ := by rw [hp.blocks]; exact hk
      rw [blockAt_keep ft fun r hr => ?_, m₅, blockAt_keep (rs := [⟨addr (VG.Proof.Argon2.X86.Derive.E s₀) counterOff, 4⟩])
        ((Frame.refl _ _).writeW (w := 32) (List.mem_singleton_self _) _ (Region.contains_self _ _)) fun r hr => ?_]
      · simp only [List.mem_singleton] at hr; subst hr
        exact (loc_disj hp (d := counterOff) (by decide) (memR s₀) (by simp)).symm.sub_left (cell_in_mem hk')
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.mem_scr.sub_left (cell_in_mem hk')
        · exact (call_disj hp (R := memR s₀) (by simp)).symm.sub_left (cell_in_mem hk')

/-- `addressCache`: J₁ and J₂ from the address block of the index's group of 128. -/
theorem addressCache_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) :
    WP isa Impl.Argon2.X86.Derive.addressCache s fun t => VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index (index / 128 + 1) st t ∧
      lw s₀ t j2Off ++ lw s₀ t j1Off =
        (addressBlock (prm s₀) pass lane slice (index / 128 + 1))[index % 128]'(Nat.mod_lt _ (by decide)) := by
  have sl := VG.Proof.Argon2.X86.Derive.segLen_lt hp
  unfold Impl.Argon2.X86.Derive.addressCache
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.cacheCheck_ok hp h hi).mono fun s₄ ⟨h₄, a₄, z₄⟩ => ?_)
  have M := VG.Proof.Argon2.X86.Derive.cacheFill_ok hp h₄ hpass hl hs hi a₄ z₄
  refine WP.seq (M.mono fun t ⟨ht, bt⟩ => (VG.Proof.Argon2.X86.Derive.cacheWord_ok hp ht (by omega)).mono fun u ⟨hu, wu⟩ => ⟨hu, ?_⟩)
  rw [wu, bt]

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `randomSource`: J₁ and J₂ are the step's random word. -/
theorem randomSource_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) :
    WP isa Impl.Argon2.X86.Derive.randomSource s fun t =>
      VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index (VG.Proof.Argon2.X86.Derive.ctrNext (prm s₀) pass slice index ctr) st t ∧
      lw s₀ t j2Off ++ lw s₀ t j1Off = Proof.Argon2.FillStep.random (prm s₀) pass lane slice index st.memory := by
  unfold Impl.Argon2.X86.Derive.randomSource
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.addressMode_ok hp h.inv h.pos hpass hs).mono fun s₁ ⟨z₁, k₁⟩ => ?_)
  have h₁ := h.of_keep k₁
  refine WP.ite (!Spec.Argon2.independent (prm s₀) pass slice) z₁ (fun hb => ?_) fun hb => ?_
  · have hind : Spec.Argon2.independent (prm s₀) pass slice = false := by simpa using hb
    refine (VG.Proof.Argon2.X86.Derive.dependentWord_ok hp h₁ hl hs hi).mono fun t ⟨ht, wt⟩ => ⟨by rw [VG.Proof.Argon2.X86.Derive.ctrNext, hind]; exact ht, ?_⟩
    have cl := Proof.Argon2.previous_cell_lt (prm s₀) hp.lanes_pos hp.memory_ge
      (column := slice * (prm s₀).segmentLen + index) hl
    rw [wt, k₁.mem, h.mem.block _ cl]
    unfold Proof.Argon2.FillStep.random
    rw [hind]
    rfl
  · have hind : Spec.Argon2.independent (prm s₀) pass slice = true := by simpa using hb
    refine (VG.Proof.Argon2.X86.Derive.addressCache_ok hp h₁ hpass hl hs hi).mono fun t ⟨ht, wt⟩ => ⟨by rw [VG.Proof.Argon2.X86.Derive.ctrNext, hind]; exact ht, ?_⟩
    rw [wt]
    unfold Proof.Argon2.FillStep.random
    rw [hind]
    rfl

end
end VG.Proof.Argon2.X86.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.Derive.FillPtr`. -/
section

section

section

/-!
# Argon2 on x86 (32-bit): the reference block's lane, start and base

`RS`: the filling state with J₁ and J₂ in the locals. `refLane_ok`: the
reference lane (RFC 9106 §3.4.2); `refStart_ok`: where the window of
eligible blocks starts; `countBase_ok`: the blocks before the current
segment that a reference may use.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_addm wp_cmpi wp_ldm wp_stm wp_andi
  wp_sbb_self wp_and wp_xor)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off refLaneOff startOff countOff tmpOff curOff)

/-- The filling state, with J₁ and J₂ in the locals. -/
structure RS (s₀ : State) (pass slice lane index ctr : Nat) (st : FillState) (J1 J2 : BitVec 32) (s : State) :
    Prop where
  fs : VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st s
  j1 : lw s₀ s j1Off = J1
  j2 : lw s₀ s j2Off = J2

theorem RS.of_keep {s₀ s t : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : VG.Proof.Argon2.X86.Derive.RS s₀ pass slice lane index ctr st J1 J2 s) (k : Divide.Keep s t) : VG.Proof.Argon2.X86.Derive.RS s₀ pass slice lane index ctr st J1 J2 t :=
  ⟨h.fs.of_keep k, by rw [lw_mem k.mem]; exact h.j1, by rw [lw_mem k.mem]; exact h.j2⟩

/-- The reference lane: J₂ mod the lane count, but the current lane in the first slice of the first pass. -/
def refLaneV (lanes pass slice lane j2 : Nat) : Nat := if pass = 0 ∧ slice = 0 then lane else j2 % lanes

/-- Where the window starts. -/
def startV (segLen laneLen pass slice : Nat) : Nat :=
  if pass = 0 then 0 else (slice + 1) * segLen % laneLen

/-- The blocks before the current segment that a reference may use. -/
def baseV (segLen laneLen pass slice : Nat) : Nat := if pass = 0 then slice * segLen else laneLen - segLen

theorem or_zero {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a ||| BitVec.ofNat 32 b == 0) = decide (a = 0 ∧ b = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro e
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_or, Wp.toNat_ofNat_lt ha, Wp.toNat_ofNat_lt hb] at this
    simpa using this
  · rintro ⟨rfl, rfl⟩; rfl

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem RS.store {s t : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : VG.Proof.Argon2.X86.Derive.RS s₀ pass slice lane index ctr st J1 J2 s) (it : VG.Proof.Argon2.X86.Derive.Inv s₀ t) {d : Nat} (hd : d + 4 ≤ 144) (ha : d % 4 = 0)
    (hd' : d ∉ VG.Proof.Argon2.X86.Derive.fsOffs) (h1 : d ≠ j1Off) (h2 : d ≠ j2Off) {v : BitVec 32}
    (hm : t.mem = s.mem.writeW (addr (VG.Proof.Argon2.X86.Derive.E s₀) d) v) : VG.Proof.Argon2.X86.Derive.RS s₀ pass slice lane index ctr st J1 J2 t := by
  refine ⟨h.fs.store hp it hd ha hd' hm, ?_, ?_⟩
  · show t.mem.readW _ 32 = _
    rw [hm, lw_store hp (by omega) (by decide) (by simp [j1Off] at h1 ⊢; omega)]; exact h.j1
  · show t.mem.readW _ 32 = _
    rw [hm, lw_store hp (by omega) (by decide) (by simp [j2Off] at h2 ⊢; omega)]; exact h.j2

/-- The block of `refLane`: J₂ mod lanes, to the locals, and ZF in the first
slice of the first pass. -/
theorem refLaneBlk_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : VG.Proof.Argon2.X86.Derive.RS s₀ pass slice lane index ctr st J1 J2 s) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa (.block (.mov .ecx (Impl.Argon2.X86.Derive.fr j2Off) :: Impl.Argon2.X86.Divide.code (argOff 7) ++
      [Impl.Argon2.X86.Derive.st refLaneOff .eax, .mov .eax (Impl.Argon2.X86.Derive.fr passOff),
        .alu .or .eax (Impl.Argon2.X86.Derive.fr sliceOff)])) s fun t =>
      VG.Proof.Argon2.X86.Derive.RS s₀ pass slice lane index ctr st J1 J2 t ∧ t.zf = some (decide (pass = 0 ∧ slice = 0)) ∧
      lw s₀ t refLaneOff = BitVec.ofNat 32 (J2.toNat % lanesN s₀) := by
  have hlt := hp.lanes_lt
  have hl1 := hp.lanes_pos
  have e7 : lanesN s₀ = (VG.X86.arg s₀ 7).toNat := rfl
  simp only [List.cons_append]
  refine wp_ldloc hp h.fs.inv (d := j2Off) (by decide) fun s₁ u₁ => ?_
  have h₁ := h.of_keep (Divide.Keep.of_upd u₁ (by simp))
  refine Divide.code_ok (D := VG.X86.arg s₀ 7) (by omega) (by omega) h₁.fs.inv.ebp (h₁.fs.inv.arg_in hp (by decide))
    (h₁.fs.inv.arg hp (by decide)) fun s₂ _ r₂ k₂ => ?_
  have h₂ := h₁.of_keep k₂
  refine wp_stloc hp h₂.fs.inv (d := refLaneOff) (by decide) fun s₃ i₃ v₃ _ g₃ m₃ => ?_
  have h₃ := h₂.store hp i₃ (d := refLaneOff) (by decide) (by decide) (by decide) (by decide) (by decide) m₃
  refine wp_ldloc hp h₃.fs.inv (d := passOff) (by decide) fun s₄ u₄ => ?_
  have h₄ := h₃.of_keep (Divide.Keep.of_upd u₄ (by simp))
  refine VG.Proof.Argon2.X86.Derive.wp_orm h₄.fs.inv.ebp (loc_in' hp h₄.fs.inv (d := sliceOff) (by decide)) fun s₅ u₅ z₅ => WP.block_nil ?_
  have h₅ := h₄.of_keep (Divide.Keep.of_upd u₅ (by simp))
  have r : s₂.gpr .eax = BitVec.ofNat 32 (J2.toNat % lanesN s₀) := BitVec.eq_of_toNat_eq (by
    rw [r₂, u₁.gpr, h.j2, Wp.toNat_ofNat_lt (by have := J2.isLt; have := Nat.mod_le J2.toNat (lanesN s₀); omega)])
  refine ⟨h₅, ?_, by rw [lw_mem u₅.mem, lw_mem u₄.mem, v₃, r]⟩
  rw [z₅, u₄.gpr, show s₄.mem.readW (addr (VG.Proof.Argon2.X86.Derive.E s₀) sliceOff) 32 = lw s₀ s₄ sliceOff from rfl, h₄.fs.pos.slice,
    h₃.fs.pos.pass, VG.Proof.Argon2.X86.Derive.or_zero hpass (by omega)]

/-- `refLane`: the reference lane, to the locals. -/
theorem refLane_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : VG.Proof.Argon2.X86.Derive.RS s₀ pass slice lane index ctr st J1 J2 s) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa Impl.Argon2.X86.Derive.refLane s fun t => VG.Proof.Argon2.X86.Derive.RS s₀ pass slice lane index ctr st J1 J2 t ∧
      lw s₀ t refLaneOff = BitVec.ofNat 32 (VG.Proof.Argon2.X86.Derive.refLaneV (lanesN s₀) pass slice lane J2.toNat) := by
  unfold Impl.Argon2.X86.Derive.refLane
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.refLaneBlk_ok hp h hpass hs).mono fun s₅ ⟨h₅, z₅, e₃⟩ => ?_)
  refine WP.ite (decide (pass = 0 ∧ slice = 0)) z₅ (fun hb => ?_) fun hb => ?_
  · have hb' : pass = 0 ∧ slice = 0 := of_decide_eq_true hb
    refine wp_ldloc hp h₅.fs.inv (d := laneOff) (by decide) fun s₆ u₆ => ?_
    have h₆ := h₅.of_keep (Divide.Keep.of_upd u₆ (by simp))
    refine wp_stloc hp h₆.fs.inv (d := refLaneOff) (by decide) fun t it vt _ _ mt => WP.block_nil ⟨?_, ?_⟩
    · exact h₆.store hp it (d := refLaneOff) (by decide) (by decide) (by decide) (by decide) (by decide) mt
    · rw [vt, u₆.gpr, h₅.fs.pos.lane, VG.Proof.Argon2.X86.Derive.refLaneV, ite_eq_left hb']
  · have hb' : ¬(pass = 0 ∧ slice = 0) := of_decide_eq_false hb
    refine WP.block_nil ⟨h₅, ?_⟩
    rw [e₃, VG.Proof.Argon2.X86.Derive.refLaneV, ite_eq_right hb']

end


section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `refStart`: where the window starts, to the locals. -/
theorem refStart_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : VG.Proof.Argon2.X86.Derive.RS s₀ pass slice lane index ctr st J1 J2 s) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa Impl.Argon2.X86.Derive.refStart s fun t => VG.Proof.Argon2.X86.Derive.RS s₀ pass slice lane index ctr st J1 J2 t ∧
      lw s₀ t refLaneOff = lw s₀ s refLaneOff ∧
      lw s₀ t startOff = BitVec.ofNat 32 (VG.Proof.Argon2.X86.Derive.startV (prm s₀).segmentLen (prm s₀).laneLen pass slice) := by
  have sl := VG.Proof.Argon2.X86.Derive.segLen_lt hp
  have ll := hp.laneLen_eq
  have s2 := hp.segLen_two
  unfold Impl.Argon2.X86.Derive.refStart
  refine WP.seq (wp_movi fun s₁ u₁ => ?_)
  have h₁ := h.of_keep (Divide.Keep.of_upd u₁ (by simp))
  refine wp_stloc hp h₁.fs.inv (d := startOff) (by decide) fun s₂ i₂ v₂ o₂ _ m₂ => ?_
  have h₂ := h₁.store hp i₂ (d := startOff) (by decide) (by decide) (by decide) (by decide) (by decide) m₂
  refine wp_ldloc hp h₂.fs.inv (d := passOff) (by decide) fun s₃ u₃ => wp_cmpi fun s₄ f₄ _ z₄ => WP.block_nil ?_
  have h₄ := (h₂.of_keep (Divide.Keep.of_upd u₃ (by simp))).of_keep (Divide.Keep.of_fupd f₄)
  have m₄ : s₄.mem = s₂.mem := by rw [f₄.mem, u₃.mem]
  have r₂ : lw s₀ s₂ refLaneOff = lw s₀ s refLaneOff := by
    rw [o₂ _ (by decide) (by decide), lw_mem u₁.mem]
  have z : ∀ y : BitVec 32, y - 0 = y := fun y => by simp
  refine WP.ite (decide (pass = 0)) (by
    show s₄.zf = _
    rw [z₄, u₃.gpr, h₂.fs.pos.pass, z, Wp.ofNat_beq_zero hpass]) (fun hb => ?_) fun hb => ?_
  · refine WP.block_nil ⟨h₄, by rw [lw_mem m₄, r₂], ?_⟩
    rw [lw_mem m₄, v₂, u₁.gpr, VG.Proof.Argon2.X86.Derive.startV, ite_eq_left (of_decide_eq_true hb)]; rfl
  · have hp0 : pass ≠ 0 := of_decide_eq_false hb
    refine WP.seq (wp_ldloc hp h₄.fs.inv (d := sliceOff) (by decide) fun s₅ u₅ => wp_cmpi fun s₆ f₆ _ z₆ =>
      WP.block_nil ?_)
    have h₆ := (h₄.of_keep (Divide.Keep.of_upd u₅ (by simp))).of_keep (Divide.Keep.of_fupd f₆)
    have m₆ : s₆.mem = s₂.mem := by rw [f₆.mem, u₅.mem, m₄]
    refine WP.ite (decide (slice = 3)) (by
      show s₆.zf = _
      rw [z₆, u₅.gpr, h₄.fs.pos.slice, show (3 : BitVec 32) = BitVec.ofNat 32 3 from rfl,
        Wp.sub_beq (by omega) (by decide)]) (fun hb' => ?_) fun hb' => ?_
    · refine WP.block_nil ⟨h₆, by rw [lw_mem m₆, r₂], ?_⟩
      rw [lw_mem m₆, v₂, u₁.gpr, VG.Proof.Argon2.X86.Derive.startV, ite_eq_right hp0, of_decide_eq_true hb', ll, Nat.mod_self]; rfl
    · have hs3 : slice ≠ 3 := of_decide_eq_false hb'
      refine wp_ldloc hp h₆.fs.inv (d := sliceOff) (by decide) fun s₇ u₇ => wp_addi fun s₈ u₈ =>
        wp_ldloc hp ((h₆.of_keep (Divide.Keep.of_upd u₇ (by simp))).of_keep (Divide.Keep.of_upd u₈ (by simp))).fs.inv
          (d := segLenOff) (by decide) fun s₉ u₉ => VG.Proof.Argon2.X86.Derive.wp_mul fun s₁₀ a₁₀ _ k₁₀ _ => ?_
      have h₁₀ := ((((h₆.of_keep (Divide.Keep.of_upd u₇ (by simp))).of_keep (Divide.Keep.of_upd u₈ (by simp))).of_keep
        (Divide.Keep.of_upd u₉ (by simp))).of_keep k₁₀)
      have m₁₀ : s₁₀.mem = s₂.mem := by rw [k₁₀.mem, u₉.mem, u₈.mem, u₇.mem, m₆]
      refine wp_stloc hp h₁₀.fs.inv (d := startOff) (by decide) fun t it vt ot _ mt => WP.block_nil ⟨?_, ?_, ?_⟩
      · exact h₁₀.store hp it (d := startOff) (by decide) (by decide) (by decide) (by decide) (by decide) mt
      · rw [ot _ (by decide) (by decide), lw_mem m₁₀, r₂]
      · have : (slice + 1) * (prm s₀).segmentLen < (prm s₀).laneLen := by
          rw [ll]; exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
        rw [vt, a₁₀, u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₉.gpr, lw_mem u₈.mem, lw_mem u₇.mem,
          h₆.fs.pr.segLen, lw_mem (show s₆.mem = s₂.mem from m₆), h₂.fs.pos.slice,
          show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat, Wp.toNat_ofNat_lt (by omega),
          Wp.toNat_ofNat_lt (by omega), VG.Proof.Argon2.X86.Derive.startV, ite_eq_right hp0, Nat.mod_eq_of_lt this]

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `countBase`: `eax :=` the blocks before the current segment that a reference may use. -/
theorem countBase_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : VG.Proof.Argon2.X86.Derive.RS s₀ pass slice lane index ctr st J1 J2 s) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa Impl.Argon2.X86.Derive.countBase s fun t => Divide.Keep s t ∧
      t.gpr .eax = BitVec.ofNat 32 (VG.Proof.Argon2.X86.Derive.baseV (prm s₀).segmentLen (prm s₀).laneLen pass slice) := by
  have sl := VG.Proof.Argon2.X86.Derive.segLen_lt hp
  have ll := hp.laneLen_eq
  unfold Impl.Argon2.X86.Derive.countBase
  refine WP.seq (wp_ldloc hp h.fs.inv (d := passOff) (by decide) fun s₁ u₁ => wp_cmpi fun s₂ f₂ _ z₂ =>
    WP.block_nil ?_)
  have k₂ := (Divide.Keep.of_upd u₁ (by simp)).trans (Divide.Keep.of_fupd f₂)
  have h₂ := h.of_keep k₂
  have z : ∀ y : BitVec 32, y - 0 = y := fun y => by simp
  refine WP.ite (decide (pass = 0)) (by
    show s₂.zf = _
    rw [z₂, u₁.gpr, h.fs.pos.pass, z, Wp.ofNat_beq_zero hpass]) (fun hb => ?_) fun hb => ?_
  · refine wp_ldloc hp h₂.fs.inv (d := sliceOff) (by decide) fun s₃ u₃ =>
      wp_ldloc hp (h₂.of_keep (Divide.Keep.of_upd u₃ (by simp))).fs.inv (d := segLenOff) (by decide) fun s₄ u₄ =>
      VG.Proof.Argon2.X86.Derive.wp_mul fun t a _ k _ => WP.block_nil ⟨k₂.trans ((Divide.Keep.of_upd u₃ (by simp)).trans
        ((Divide.Keep.of_upd u₄ (by simp)).trans k)), ?_⟩
    rw [a, u₄.other _ (by decide), u₃.gpr, u₄.gpr, lw_mem u₃.mem, h₂.fs.pos.slice, h₂.fs.pr.segLen,
      Wp.toNat_ofNat_lt (by omega), Wp.toNat_ofNat_lt (by omega), VG.Proof.Argon2.X86.Derive.baseV, ite_eq_left (of_decide_eq_true hb)]
  · refine wp_ldloc hp h₂.fs.inv (d := laneLenOff) (by decide) fun s₃ u₃ =>
      Divide.wp_subm (h₂.of_keep (Divide.Keep.of_upd u₃ (by simp))).fs.inv.ebp
        (loc_in' hp (h₂.of_keep (Divide.Keep.of_upd u₃ (by simp))).fs.inv (d := segLenOff) (by decide))
        fun t u _ => WP.block_nil ⟨k₂.trans ((Divide.Keep.of_upd u₃ (by simp)).trans
          (Divide.Keep.of_upd u (by simp))), ?_⟩
    rw [u.gpr, u₃.gpr, show s₃.mem.readW (addr (VG.Proof.Argon2.X86.Derive.E s₀) segLenOff) 32 = lw s₀ s₃ segLenOff from rfl,
      lw_mem u₃.mem, h₂.fs.pr.laneLen, h₂.fs.pr.segLen, Wp.sub_ofNat (by omega), VG.Proof.Argon2.X86.Derive.baseV,
      ite_eq_right (of_decide_eq_false hb)]

end
end VG.Proof.Argon2.X86.Derive

end

/-!
# Argon2 on x86 (32-bit): the reference window's size

`countSelect_ok`: the number of eligible reference blocks, chosen between
the current lane's and another lane's by a mask (`sel`), to the locals.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_addm wp_cmpi wp_ldm wp_stm wp_andi
  wp_sbb_self wp_and wp_xor wp_xorm)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off refLaneOff startOff countOff tmpOff curOff)

theorem sel (a c : BitVec 32) (b : Bool) :
    a ^^^ ((c ^^^ a) &&& (if b then BitVec.allOnes 32 else 0)) = if b then c else a := by
  cases b
  · simp
  · simp only [ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm c a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem add_allOnes {x : Nat} (h : 1 ≤ x) (h' : x < 2 ^ 32) :
    BitVec.ofNat 32 x + BitVec.allOnes 32 = BitVec.ofNat 32 (x - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, Wp.toNat_ofNat_lt h', Wp.toNat_ofNat_lt (by omega), BitVec.toNat_allOnes]
  omega

theorem xor_lt_one {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    decide ((BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b).toNat < (1 : BitVec 32).toNat) = decide (a = b) := by
  rw [show (1 : BitVec 32).toNat = 1 from rfl, Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  constructor
  · intro h
    have e : BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b = 0#32 :=
      BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; omega)
    have := congrArg (· ^^^ BitVec.ofNat 32 b) e
    simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, BitVec.zero_xor] at this
    have := congrArg BitVec.toNat this
    rwa [Wp.toNat_ofNat_lt ha, Wp.toNat_ofNat_lt hb] at this
  · rintro rfl; simp

theorem lt_one {n : Nat} (h : n < 2 ^ 32) :
    decide ((BitVec.ofNat 32 n).toNat < (1 : BitVec 32).toNat) = decide (n = 0) := by
  rw [Wp.toNat_ofNat_lt h]
  simp only [show (1 : BitVec 32).toNat = 1 from rfl, Nat.lt_one_iff]

/-- The window's size. -/
def countV (base index : Nat) (same : Bool) : Nat :=
  if same then base + index - 1 else base - (if index = 0 then 1 else 0)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `countSelect`: the window's size, to the locals and `eax`. -/
theorem countSelect_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : VG.Proof.Argon2.X86.Derive.RS s₀ pass slice lane index ctr st J1 J2 s) {base rl : Nat} (hb : base < 2 ^ 31)
    (hi : index < (prm s₀).segmentLen) (hl : lane < lanesN s₀) (hrl : rl < lanesN s₀)
    (ha : s.gpr .eax = BitVec.ofNat 32 base) (hr : lw s₀ s refLaneOff = BitVec.ofNat 32 rl)
    (hsame : rl = lane → 1 ≤ base + index) (hother : rl ≠ lane → index = 0 → 1 ≤ base)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.Argon2.X86.Derive.RS s₀ pass slice lane index ctr st J1 J2 t →
      t.gpr .eax = BitVec.ofNat 32 (VG.Proof.Argon2.X86.Derive.countV base index (rl == lane)) →
      lw s₀ t countOff = BitVec.ofNat 32 (VG.Proof.Argon2.X86.Derive.countV base index (rl == lane)) →
      (∀ e, e + 4 ≤ 236 → (countOff + 4 ≤ e ∨ e + 4 ≤ countOff) → lw s₀ t e = lw s₀ s e) →
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.X86.Derive.countSelect ++ is)) s Q := by
  have sl := VG.Proof.Argon2.X86.Derive.segLen_lt hp
  have lt := hp.lanes_lt
  unfold Impl.Argon2.X86.Derive.countSelect
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => ?_
  have h₁ := h.of_keep (Divide.Keep.of_upd u₁ (by simp))
  refine wp_addm h₁.fs.inv.ebp (loc_in' hp h₁.fs.inv (d := indexOff) (by decide)) fun s₂ u₂ =>
    wp_subi fun s₃ u₃ _ _ => ?_
  have K₃ : Divide.Keep s s₃ :=
    ((Divide.Keep.of_upd u₁ (by simp)).trans (Divide.Keep.of_upd u₂ (by simp))).trans (Divide.Keep.of_upd u₃ (by simp))
  refine wp_ldloc hp (h.of_keep K₃).fs.inv (d := indexOff) (by decide) fun s₄ u₄ => wp_subi fun s₅ u₅ c₅ _ =>
    wp_sbb_self c₅ fun s₆ u₆ => wp_add fun s₇ u₇ _ => ?_
  have K₇ : Divide.Keep s s₇ := (((K₃.trans (Divide.Keep.of_upd u₄ (by simp))).trans
    (Divide.Keep.of_upd u₅ (by simp))).trans (Divide.Keep.of_upd u₆ (by simp))).trans (Divide.Keep.of_upd u₇ (by simp))
  refine wp_ldloc hp (h.of_keep K₇).fs.inv (d := refLaneOff) (by decide) fun s₈ u₈ => ?_
  have K₈ := K₇.trans (Divide.Keep.of_upd u₈ (by simp))
  refine wp_xorm (h.of_keep K₈).fs.inv.ebp (loc_in' hp (h.of_keep K₈).fs.inv (d := laneOff) (by decide))
    fun s₉ u₉ => wp_subi fun s₁₀ u₁₀ c₁₀ _ => wp_sbb_self c₁₀ fun s₁₁ u₁₁ => wp_xor fun s₁₂ u₁₂ =>
    wp_and fun s₁₃ u₁₃ => wp_xor fun s₁₄ u₁₄ => ?_
  have K₁₄ : Divide.Keep s s₁₄ := ((((((K₈.trans (Divide.Keep.of_upd u₉ (by simp))).trans
    (Divide.Keep.of_upd u₁₀ (by simp))).trans (Divide.Keep.of_upd u₁₁ (by simp))).trans
    (Divide.Keep.of_upd u₁₂ (by simp))).trans (Divide.Keep.of_upd u₁₃ (by simp))).trans
    (Divide.Keep.of_upd u₁₄ (by simp)))
  have h₁₄ := h.of_keep K₁₄
  -- The value.
  have hix : lw s₀ s indexOff = BitVec.ofNat 32 index := h.fs.pos.index
  have hln : lw s₀ s laneOff = BitVec.ofNat 32 lane := h.fs.pos.lane
  have m : ∀ {t : State}, Divide.Keep s t → ∀ d, lw s₀ t d = lw s₀ s d := fun k d => lw_mem k.mem d
  have e₃ : s₃.gpr .ecx = BitVec.ofNat 32 base + BitVec.ofNat 32 index - 1 := by
    rw [u₃.gpr, u₂.gpr, u₁.gpr, ha, show s₁.mem.readW (addr (VG.Proof.Argon2.X86.Derive.E s₀) indexOff) 32 = lw s₀ s₁ indexOff from rfl,
      m (Divide.Keep.of_upd u₁ (by simp)), hix]
  have e₇ : s₇.gpr .eax = BitVec.ofNat 32 base + (if decide (index = 0) then BitVec.allOnes 32 else 0) := by
    rw [u₇.gpr, u₆.gpr, u₆.other .eax (by decide), u₅.other .eax (by decide), u₄.other .eax (by decide),
      u₃.other .eax (by decide), u₂.other .eax (by decide), u₁.other .eax (by decide), ha, u₄.gpr, m K₃, hix,
      VG.Proof.Argon2.X86.Derive.lt_one (by omega)]
  have e₁₁ : s₁₁.gpr .edx = if decide (rl = lane) then BitVec.allOnes 32 else 0 := by
    rw [u₁₁.gpr, u₉.gpr, u₈.gpr, show s₈.mem.readW (addr (VG.Proof.Argon2.X86.Derive.E s₀) laneOff) 32 = lw s₀ s₈ laneOff from rfl, m K₇, m K₈,
      hr, hln, VG.Proof.Argon2.X86.Derive.xor_lt_one (by omega) (by omega)]
  have e₁₄ : s₁₄.gpr .eax = if decide (rl = lane) then s₃.gpr .ecx else s₇.gpr .eax := by
    rw [u₁₄.gpr, u₁₃.gpr, u₁₃.other .eax (by decide), u₁₂.gpr, u₁₂.other .eax (by decide), u₁₂.other .edx (by decide),
      e₁₁, u₁₁.other .eax (by decide), u₁₁.other .ecx (by decide), u₁₀.other .eax (by decide),
      u₁₀.other .ecx (by decide), u₉.other .eax (by decide), u₉.other .ecx (by decide), u₈.other .eax (by decide),
      u₈.other .ecx (by decide), u₇.other .ecx (by decide), u₆.other .ecx (by decide), u₅.other .ecx (by decide),
      u₄.other .ecx (by decide), VG.Proof.Argon2.X86.Derive.sel]
  have val : s₁₄.gpr .eax = BitVec.ofNat 32 (VG.Proof.Argon2.X86.Derive.countV base index (rl == lane)) := by
    rw [e₁₄, VG.Proof.Argon2.X86.Derive.countV]
    by_cases hs : rl = lane
    · simp only [decide_eq_true hs, show (rl == lane) = true from beq_iff_eq.mpr hs, ↓reduceIte]
      rw [e₃, BitVec.ofNat_add_ofNat, Wp.ofNat_pred (hsame hs)]
    · simp only [decide_eq_false hs, show (rl == lane) = false from beq_eq_false_iff_ne.mpr hs, ↓reduceIte,
        Bool.false_eq_true]
      rw [e₇]
      by_cases hi0 : index = 0
      · rw [decide_eq_true hi0, ite_eq_left (rfl : true = true), ite_eq_left hi0,
          VG.Proof.Argon2.X86.Derive.add_allOnes (hother hs hi0) (by omega)]
      · rw [decide_eq_false hi0, ite_eq_right (by decide : ¬(false = true)), ite_eq_right hi0, Nat.sub_zero]
        simp
  refine wp_stloc hp h₁₄.fs.inv (d := countOff) (by decide) fun t it vt ot gt mt => k t ?_ (by rw [gt, val])
    (by rw [vt, val]) (fun e he hd => by rw [ot e he hd, m K₁₄]) (fun r a b c => by rw [gt, K₁₄.other r a b c])
  exact h₁₄.store hp it (d := countOff) (by decide) (by decide) (by decide) (by decide) (by decide) mt

end

end VG.Proof.Argon2.X86.Derive

end

/-!
# Argon2 on x86 (32-bit): the reference block's column and the block pointers

`relative_ok`: the position in the window that J₁ selects (RFC 9106
§3.4.2); `wrap_ok`: its column, from the window's start, modulo the lane
length; `refPointer_ok` and `curPointer_ok`: the reference and current
blocks' addresses, to the locals.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_sub wp_addm wp_cmpi wp_ldm wp_stm wp_andi
  wp_sbb_self wp_and wp_xor wp_xorm)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off refLaneOff startOff countOff tmpOff curOff)

/-- The position in the window that `j1` selects. -/
def relV (cnt j1 : Nat) : Nat := cnt - 1 - cnt * (j1 * j1 / 2 ^ 32) / 2 ^ 32

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `relative`: `eax :=` the position in the window. -/
theorem relative_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : VG.Proof.Argon2.X86.Derive.RS s₀ pass slice lane index ctr st J1 J2 s) {cnt : Nat} (hc : 1 ≤ cnt) (hc' : cnt < 2 ^ 32)
    (hcnt : lw s₀ s countOff = BitVec.ofNat 32 cnt) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .eax = BitVec.ofNat 32 (VG.Proof.Argon2.X86.Derive.relV cnt J1.toNat) → Divide.Keep s t → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.X86.Derive.relative ++ is)) s Q := by
  have jb := J1.isLt
  have x32 := Proof.Argon2.reference_scaled_bound J1.toNat jb
  have lt := Proof.Argon2.reference_scale_lt_count cnt J1.toNat (by omega) jb
  unfold Impl.Argon2.X86.Derive.relative
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc hp h.fs.inv (d := j1Off) (by decide) fun s₁ u₁ => VG.Proof.Argon2.X86.Derive.wp_mul fun s₂ _ d₂ k₂ _ => wp_mov fun s₃ u₃ => ?_
  have K₃ := ((Divide.Keep.of_upd u₁ (by simp)).trans k₂).trans (Divide.Keep.of_upd u₃ (by simp))
  refine wp_ldloc hp (h.of_keep K₃).fs.inv (d := countOff) (by decide) fun s₄ u₄ => VG.Proof.Argon2.X86.Derive.wp_mul fun s₅ _ d₅ k₅ o₅ =>
    wp_mov fun s₆ u₆ => wp_subi fun s₇ u₇ _ _ => wp_sub fun t u _ => k t ?_ ?_
  · have x₃ : (s₃.gpr .eax).toNat = J1.toNat * J1.toNat / 2 ^ 32 := by
      rw [u₃.gpr, d₂, u₁.gpr, h.j1, Wp.toNat_ofNat_lt x32]
    have c₄ : (s₄.gpr .ecx).toNat = cnt := by
      rw [u₄.gpr, lw_mem K₃.mem, hcnt, Wp.toNat_ofNat_lt hc']
    rw [u.gpr, u₇.gpr, u₇.other .edx (by decide), u₆.gpr, u₆.other .edx (by decide), o₅ .ecx (by decide) (by decide),
      d₅, u₄.other .eax (by decide), x₃, c₄, u₄.gpr, lw_mem K₃.mem, hcnt, Wp.ofNat_pred hc,
      Wp.sub_ofNat (by rw [Nat.mul_comm]; omega), VG.Proof.Argon2.X86.Derive.relV, Nat.mul_comm (J1.toNat * J1.toNat / 2 ^ 32) cnt]
  · exact (((((K₃.trans (Divide.Keep.of_upd u₄ (by simp))).trans k₅).trans (Divide.Keep.of_upd u₆ (by simp))).trans
      (Divide.Keep.of_upd u₇ (by simp))).trans (Divide.Keep.of_upd u (by simp)))


/-- `wrap`: `eax := (start + eax) mod laneLen`. -/
theorem wrap_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : VG.Proof.Argon2.X86.Derive.RS s₀ pass slice lane index ctr st J1 J2 s) {rel stt : Nat} (hr : rel < (prm s₀).laneLen)
    (hs : stt < (prm s₀).laneLen) (ha : s.gpr .eax = BitVec.ofNat 32 rel)
    (hst : lw s₀ s startOff = BitVec.ofNat 32 stt) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .eax = BitVec.ofNat 32 ((stt + rel) % (prm s₀).laneLen) → Divide.Keep s t →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.X86.Derive.wrap ++ is)) s Q := by
  have L22 : (prm s₀).laneLen < 2 ^ 22 := by
    have := Nat.le_mul_of_pos_left (prm s₀).laneLen (show 0 < lanesN s₀ from hp.lanes_pos)
    have e := hp.blocks_eq
    have := hp.blocks_lt
    omega
  unfold Impl.Argon2.X86.Derive.wrap
  simp only [List.cons_append, List.nil_append]
  refine wp_addm h.fs.inv.ebp (loc_in' hp h.fs.inv (d := startOff) (by decide)) fun s₁ u₁ => ?_
  have K₁ := Divide.Keep.of_upd u₁ (by simp)
  refine Divide.wp_subm (h.of_keep K₁).fs.inv.ebp (loc_in' hp (h.of_keep K₁).fs.inv (d := laneLenOff) (by decide))
    fun s₂ u₂ c₂ => wp_sbb_self c₂ fun s₃ u₃ => ?_
  have K₃ := (K₁.trans (Divide.Keep.of_upd u₂ (by simp))).trans (Divide.Keep.of_upd u₃ (by simp))
  refine Divide.wp_andm (h.of_keep K₃).fs.inv.ebp (loc_in' hp (h.of_keep K₃).fs.inv (d := laneLenOff) (by decide))
    fun s₄ u₄ => wp_add fun t u _ => k t ?_ ?_
  · have x₁ : s₁.gpr .eax = BitVec.ofNat 32 (stt + rel) := by
      rw [u₁.gpr, ha, show s.mem.readW (addr (VG.Proof.Argon2.X86.Derive.E s₀) startOff) 32 = lw s₀ s startOff from rfl, hst,
        BitVec.ofNat_add_ofNat, Nat.add_comm]
    have L₁ : s₁.mem.readW (addr (VG.Proof.Argon2.X86.Derive.E s₀) laneLenOff) 32 = BitVec.ofNat 32 (prm s₀).laneLen := by
      show lw s₀ s₁ laneLenOff = _
      rw [lw_mem K₁.mem]; exact h.fs.pr.laneLen
    have L₃ : s₃.mem.readW (addr (VG.Proof.Argon2.X86.Derive.E s₀) laneLenOff) 32 = BitVec.ofNat 32 (prm s₀).laneLen := by
      show lw s₀ s₃ laneLenOff = _
      rw [lw_mem K₃.mem]; exact h.fs.pr.laneLen
    rw [u.gpr, u₄.other _ (by decide), u₄.gpr, L₃, u₃.gpr, u₃.other _ (by decide), u₂.gpr, x₁, L₁,
      Wp.toNat_ofNat_lt (by omega), Wp.toNat_ofNat_lt (by omega),
      Proof.Argon2.reference_wrap (stt + rel) (prm s₀).laneLen (by omega)]
    by_cases c : stt + rel < (prm s₀).laneLen
    · simp only [c, decide_true, ite_true, BitVec.allOnes_and, BitVec.sub_add_cancel]
    · simp only [c, decide_false, ite_false, Bool.false_eq_true]
      rw [Wp.sub_ofNat (by omega)]
      simp
  · exact (K₃.trans (Divide.Keep.of_upd u₄ (by simp))).trans (Divide.Keep.of_upd u (by simp))

/-- `refPointer`: the address of block `eax` of the reference lane, to the locals. -/
theorem refPointer_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : VG.Proof.Argon2.X86.Derive.RS s₀ pass slice lane index ctr st J1 J2 s) {col rl : Nat} (hc : col < (prm s₀).laneLen)
    (hrl : rl < lanesN s₀) (ha : s.gpr .eax = BitVec.ofNat 32 col)
    (hr : lw s₀ s refLaneOff = BitVec.ofNat 32 rl) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.Argon2.X86.Derive.RS s₀ pass slice lane index ctr st J1 J2 t →
      lw s₀ t tmpOff = memP s₀ + BitVec.ofNat 32 ((rl * (prm s₀).laneLen + col) * 1024) →
      (∀ e, e + 4 ≤ 236 → (tmpOff + 4 ≤ e ∨ e + 4 ≤ tmpOff) → lw s₀ t e = lw s₀ s e) →
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.X86.Derive.refPointer ++ is)) s Q := by
  unfold Impl.Argon2.X86.Derive.refPointer
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_mov fun s₁ u₁ => ?_
  have K₁ := Divide.Keep.of_upd u₁ (by simp)
  refine wp_ldloc hp (h.of_keep K₁).fs.inv (d := refLaneOff) (by decide) fun s₂ u₂ => ?_
  have K₂ := K₁.trans (Divide.Keep.of_upd u₂ (by simp))
  refine VG.Proof.Argon2.X86.Derive.blockAddr_ok hp (h.of_keep K₂).fs.inv (h.of_keep K₂).fs.pr hrl hc
    (by rw [u₂.gpr, lw_mem K₁.mem, hr]) (by rw [u₂.other _ (by decide), u₁.gpr, ha]) fun s₃ a₃ _ k₃ => ?_
  have K₃ := K₂.trans k₃
  refine wp_stloc hp (h.of_keep K₃).fs.inv (d := tmpOff) (by decide) fun t it vt ot gt mt =>
    k t ?_ (by rw [vt, a₃]) (fun e he hd => by rw [ot e he hd, lw_mem K₃.mem]) (fun r a b c => by
      rw [gt, K₃.other r a b c])
  exact (h.of_keep K₃).store hp it (d := tmpOff) (by decide) (by decide) (by decide) (by decide) (by decide) mt

/-- `curPointer`: the address of the current block, to the locals. -/
theorem curPointer_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : VG.Proof.Argon2.X86.Derive.RS s₀ pass slice lane index ctr st J1 J2 s) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.Argon2.X86.Derive.RS s₀ pass slice lane index ctr st J1 J2 t →
      lw s₀ t curOff = memP s₀ + BitVec.ofNat 32
        ((lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index)) * 1024) →
      (∀ e, e + 4 ≤ 236 → (curOff + 4 ≤ e ∨ e + 4 ≤ curOff) → lw s₀ t e = lw s₀ s e) →
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.X86.Derive.curPointer ++ is)) s Q := by
  have hc := Proof.Argon2.column_lt (prm s₀) hp.lanes_pos hs hi
  unfold Impl.Argon2.X86.Derive.curPointer
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine VG.Proof.Argon2.X86.Derive.column_ok hp h.fs.inv h.fs.pr h.fs.pos hs hi fun s₁ _ c₁ k₁ => ?_
  refine wp_ldloc hp (h.of_keep k₁).fs.inv (d := laneOff) (by decide) fun s₂ u₂ => ?_
  have K₂ := k₁.trans (Divide.Keep.of_upd u₂ (by simp))
  refine VG.Proof.Argon2.X86.Derive.blockAddr_ok hp (h.of_keep K₂).fs.inv (h.of_keep K₂).fs.pr hl hc
    (by rw [u₂.gpr, lw_mem k₁.mem]; exact h.fs.pos.lane) (by rw [u₂.other _ (by decide), c₁])
    fun s₃ a₃ _ k₃ => ?_
  have K₃ := K₂.trans k₃
  refine wp_stloc hp (h.of_keep K₃).fs.inv (d := curOff) (by decide) fun t it vt ot gt mt =>
    k t ?_ (by rw [vt, a₃]) (fun e he hd => by rw [ot e he hd, lw_mem K₃.mem]) (fun r a b c => by
      rw [gt, K₃.other r a b c])
  exact (h.of_keep K₃).store hp it (d := curOff) (by decide) (by decide) (by decide) (by decide) (by decide) mt
end


theorem j2_eq (J1 J2 : BitVec 32) : ((J2 ++ J1 : BitVec 64) >>> 32).toNat = J2.toNat := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ← Proof.Sha512.Word64.hi_toNat,
    Proof.Sha512.Word64.hi_append]

theorem j1_eq (J1 J2 : BitVec 32) : ((J2 ++ J1 : BitVec 64) &&& 0xffffffff).toNat = J1.toNat := by
  rw [BitVec.toNat_and, show (0xffffffff : BitVec 64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    ← Proof.Sha512.Word64.lo_toNat, Proof.Sha512.Word64.lo_append]

theorem count_eq (p : Spec.Argon2.Params) (pass slice index : Nat) (same : Bool) :
    Spec.Argon2.referenceCount p pass slice index same =
      VG.Proof.Argon2.X86.Derive.countV (VG.Proof.Argon2.X86.Derive.baseV p.segmentLen p.laneLen pass slice) index same := by
  unfold Spec.Argon2.referenceCount VG.Proof.Argon2.X86.Derive.countV VG.Proof.Argon2.X86.Derive.baseV
  by_cases h : pass = 0
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]

theorem ref_eq (p : Spec.Argon2.Params) (pass lane slice index : Nat) (J1 J2 : BitVec 32) :
    Spec.Argon2.reference p pass lane slice index (J2 ++ J1) =
      (VG.Proof.Argon2.X86.Derive.refLaneV p.lanes pass slice lane J2.toNat,
        (VG.Proof.Argon2.X86.Derive.startV p.segmentLen p.laneLen pass slice +
          VG.Proof.Argon2.X86.Derive.relV (VG.Proof.Argon2.X86.Derive.countV (VG.Proof.Argon2.X86.Derive.baseV p.segmentLen p.laneLen pass slice) index
            (VG.Proof.Argon2.X86.Derive.refLaneV p.lanes pass slice lane J2.toNat == lane)) J1.toNat) % p.laneLen) := by
  unfold Spec.Argon2.reference
  simp only [VG.Proof.Argon2.X86.Derive.j1_eq, VG.Proof.Argon2.X86.Derive.j2_eq, VG.Proof.Argon2.X86.Derive.count_eq]
  rfl

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `reference`: the reference and current blocks' addresses, to the locals. -/
theorem reference_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : VG.Proof.Argon2.X86.Derive.RS s₀ pass slice lane index ctr st J1 J2 s) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index) :
    WP isa Impl.Argon2.X86.Derive.reference s fun t => VG.Proof.Argon2.X86.Derive.RS s₀ pass slice lane index ctr st J1 J2 t ∧
      lw s₀ t tmpOff = memP s₀ + BitVec.ofNat 32
        (((Spec.Argon2.reference (prm s₀) pass lane slice index (J2 ++ J1)).1 * (prm s₀).laneLen +
          (Spec.Argon2.reference (prm s₀) pass lane slice index (J2 ++ J1)).2) * 1024) ∧
      lw s₀ t curOff = memP s₀ + BitVec.ofNat 32
        ((lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index)) * 1024) := by
  have L22 : (prm s₀).laneLen < 2 ^ 22 := by
    have := Nat.le_mul_of_pos_left (prm s₀).laneLen (show 0 < lanesN s₀ from hp.lanes_pos)
    have e := hp.blocks_eq
    have := hp.blocks_lt
    omega
  have ll := hp.laneLen_eq
  have s2 := hp.segLen_two
  have hl1 := hp.lanes_pos
  rw [VG.Proof.Argon2.X86.Derive.ref_eq]
  generalize hRL : VG.Proof.Argon2.X86.Derive.refLaneV (prm s₀).lanes pass slice lane J2.toNat = RL
  have hRL' : VG.Proof.Argon2.X86.Derive.refLaneV (lanesN s₀) pass slice lane J2.toNat = RL := hRL
  have rl_lt : RL < lanesN s₀ := by
    rw [← hRL', VG.Proof.Argon2.X86.Derive.refLaneV]; split
    · exact hl
    · exact Nat.mod_lt _ (by omega)
  have first : pass = 0 → slice = 0 → RL = lane := fun a b => by rw [← hRL', VG.Proof.Argon2.X86.Derive.refLaneV, ite_eq_left ⟨a, b⟩]
  generalize hB : VG.Proof.Argon2.X86.Derive.baseV (prm s₀).segmentLen (prm s₀).laneLen pass slice = B
  have b_le : B ≤ (prm s₀).laneLen := by
    rw [← hB, VG.Proof.Argon2.X86.Derive.baseV]; split
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (show slice ≤ 3 by omega)) (by omega))
    · omega
  generalize hST : VG.Proof.Argon2.X86.Derive.startV (prm s₀).segmentLen (prm s₀).laneLen pass slice = ST
  have st_lt : ST < (prm s₀).laneLen := by
    rw [← hST, VG.Proof.Argon2.X86.Derive.startV]; split
    · omega
    · exact Nat.mod_lt _ (by omega)
  have cpos := Proof.Argon2.reference_count_positive (prm s₀) hp.lanes_pos hp.memory_ge pass slice index
    (RL == lane) active fun a b => by simp [first a b]
  have clt := Proof.Argon2.reference_count_lt_lane (prm s₀) hp.lanes_pos hp.memory_ge pass slice index
    (RL == lane) hs hi
  rw [VG.Proof.Argon2.X86.Derive.count_eq, hB] at cpos clt
  unfold Impl.Argon2.X86.Derive.reference
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.refLane_ok hp h hpass hs).mono fun t₁ ⟨h₁, r₁⟩ => ?_)
  rw [hRL'] at r₁
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.refStart_ok hp h₁ hpass hs).mono fun t₂ ⟨h₂, r₂, st₂⟩ => ?_)
  rw [hST] at st₂
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.countBase_ok hp h₂ hpass hs).mono fun t₃ ⟨k₃, a₃⟩ => ?_)
  rw [hB] at a₃
  have h₃ := h₂.of_keep k₃
  rw [← List.append_nil Impl.Argon2.X86.Derive.curPointer]
  refine VG.Proof.Argon2.X86.Derive.countSelect_ok hp h₃ (base := B) (rl := RL) (by omega) hi hl rl_lt a₃
    (by rw [lw_mem k₃.mem, r₂, r₁]) (fun e => ?_) (fun e e0 => ?_) fun t₄ h₄ a₄ c₄ o₄ g₄ => ?_
  · rw [← hB, VG.Proof.Argon2.X86.Derive.baseV]; split
    · rename_i hp0
      by_cases hs0 : slice = 0
      · omega
      · have := Nat.mul_le_mul_right (prm s₀).segmentLen (show 1 ≤ slice by omega); omega
    · omega
  · have : ¬(pass = 0 ∧ slice = 0) := fun ⟨a, b⟩ => e (first a b)
    rw [← hB, VG.Proof.Argon2.X86.Derive.baseV]; split
    · rename_i hp0
      have := Nat.mul_le_mul_right (prm s₀).segmentLen (show 1 ≤ slice by omega); omega
    · omega
  refine VG.Proof.Argon2.X86.Derive.relative_ok hp h₄ (cnt := VG.Proof.Argon2.X86.Derive.countV B index (RL == lane)) cpos (by omega) c₄ fun t₅ a₅ k₅ => ?_
  have h₅ := h₄.of_keep k₅
  have rel_lt : VG.Proof.Argon2.X86.Derive.relV (VG.Proof.Argon2.X86.Derive.countV B index (RL == lane)) J1.toNat < (prm s₀).laneLen := by
    unfold VG.Proof.Argon2.X86.Derive.relV; omega
  refine VG.Proof.Argon2.X86.Derive.wrap_ok hp h₅ rel_lt st_lt a₅ (by
      rw [lw_mem k₅.mem, o₄ _ (by decide) (by decide), lw_mem k₃.mem, st₂]) fun t₆ a₆ k₆ => ?_
  have h₆ := h₅.of_keep k₆
  refine VG.Proof.Argon2.X86.Derive.refPointer_ok hp h₆ (Nat.mod_lt _ (by omega)) rl_lt a₆ (by
      rw [lw_mem k₆.mem, lw_mem k₅.mem, o₄ _ (by decide) (by decide), lw_mem k₃.mem, r₂, r₁])
    fun t₇ h₇ p₇ o₇ _ => ?_
  refine VG.Proof.Argon2.X86.Derive.curPointer_ok hp h₇ hl hs hi fun t h' c' o' _ => WP.block_nil ⟨h', ?_, c'⟩
  rw [o' _ (by decide) (by decide), p₇]

end
end VG.Proof.Argon2.X86.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.Derive.FillBlock`. -/
section

section

/-!
# Argon2 on x86 (32-bit): the new block

`fillCompress_ok`: G of the previous and reference blocks, to
`scratch + 4096`. `writeWords_ok`: its words to the current block, XORed
into the old ones after the first pass; `fillWrite_ok`: the current block
after the step, as `FillStep.update` has it.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_sub wp_addm wp_cmpi wp_ldm wp_stm wp_andi
  wp_sbb_self wp_and wp_xor wp_xorm)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState compress xorBlock)
open VG.Proof.Argon2.X86 (blk ofWords blk_of_words)
open VG.Impl.Sha512.X86 (at_)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off refLaneOff startOff countOff tmpOff curOff writeWord)

/-- Words of the memory matrix. -/
abbrev mw (s₀ : State) (m : Mem) (o : Nat) : BitVec 32 := m.readW (addr (memP s₀) o) 32

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem blocks22 : blocksN s₀ < 2 ^ 22 := by
  have hb := hp.blocks_lt
  omega

theorem mem_addr' {o : Nat} (ho : o < blocksN s₀ * 1024) : addr (memP s₀) o = memB s₀ + BitVec.ofNat 64 o :=
  addr_eq (by have := hp.mem_fits; omega)

/-- A word of the matrix after a store to another, or the same. -/
theorem mw_store (m : Mem) {a b : Nat} (ha : a + 4 ≤ blocksN s₀ * 1024) (hb : b + 4 ≤ blocksN s₀ * 1024)
    (h : a = b ∨ a + 4 ≤ b ∨ b + 4 ≤ a) (v : BitVec 32) :
    VG.Proof.Argon2.X86.Derive.mw s₀ (m.writeW (addr (memP s₀) a) v) b = if a = b then v else VG.Proof.Argon2.X86.Derive.mw s₀ m b := by
  have := VG.Proof.Argon2.X86.Derive.blocks22 hp
  by_cases e : a = b
  · subst e; rw [ite_eq_left rfl]; exact Mem.readW_writeW_self32 _ _ _
  · rw [ite_eq_right e, VG.Proof.Argon2.X86.Derive.mw, VG.Proof.Argon2.X86.Derive.mw, VG.Proof.Argon2.X86.Derive.mem_addr' hp (by omega), VG.Proof.Argon2.X86.Derive.mem_addr' hp (by omega)]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

/-- The words of the current block, `n` of them written. -/
theorem writeWords_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) {cur : Nat} (hc : cur < blocksN s₀) (xo : Bool)
    {P : BitVec 32} (hsi : s.gpr .esi = P) (hPfit : P.toNat + 1024 ≤ 2 ^ 32)
    (hPw : ∃ R ∈ [VG.Proof.Argon2.X86.Derive.scrR s₀, memR s₀], ∃ off, P.setWidth 64 = R.base + BitVec.ofNat 64 off ∧ off + 1024 ≤ R.len)
    (hPC : Region.Disjoint ⟨P.setWidth 64, 1024⟩ ⟨matrixCell (memB s₀) cur, 1024⟩)
    (hdi : s.gpr .edi = memP s₀ + BitVec.ofNat 32 (cur * 1024)) :
    ∀ n ≤ 256, WP isa (.block ((List.range n).flatMap (writeWord xo))) s fun t =>
      VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ (∀ r, r ≠ .eax → t.gpr r = s.gpr r) ∧
      Frame [⟨matrixCell (memB s₀) cur, 1024⟩] s.mem t.mem ∧
      ∀ i < 256, VG.Proof.Argon2.X86.Derive.mw s₀ t.mem (cur * 1024 + 4 * i) = if i < n then
        (if xo then s.mem.readW (addr P (4 * i)) 32 ^^^ VG.Proof.Argon2.X86.Derive.mw s₀ s.mem (cur * 1024 + 4 * i) else s.mem.readW (addr P (4 * i)) 32)
        else VG.Proof.Argon2.X86.Derive.mw s₀ s.mem (cur * 1024 + 4 * i)
  | 0, _ => WP.block_nil ⟨h, fun _ _ => rfl, Frame.refl _ _, fun i _ => by rw [ite_eq_right (by omega)]⟩
  | n + 1, hn => by
    have hs := hp.scr_fits
    have hm := hp.mem_fits
    have hb := VG.Proof.Argon2.X86.Derive.blocks22 hp
    have hc' : cur * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append ((VG.Proof.Argon2.X86.Derive.writeWords_ok h hc xo hsi hPfit hPw hPC hdi n (by omega)).mono
      fun t ⟨it, gt, ft, wt⟩ => ?_)
    have cell : matrixCell (memB s₀) cur = memB s₀ + BitVec.ofNat 64 (cur * 1024) := rfl
    -- The source word is kept: only the current block has been written.
    have eP : addr P (4 * n) = P.setWidth 64 + BitVec.ofNat 64 (4 * n) := addr_eq (by omega_using [hPfit, hn])
    have sw_t : t.mem.readW (addr P (4 * n)) 32 = s.mem.readW (addr P (4 * n)) 32 := by
      rw [eP]
      refine ft.readW (r := ⟨P.setWidth 64 + BitVec.ofNat 64 (4 * n), 4⟩) (Region.contains_self _ _)
        (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact hPC.sub_left (Offset.sub_base _ (by omega_using [hn]))
    have ea : addr (t.gpr .esi) (4 * n) = addr P (4 * n) := by
      rw [gt _ (by decide), hsi]
    have eb : addr (t.gpr .edi) (4 * n) = addr (memP s₀) (cur * 1024 + 4 * n) := by
      rw [gt _ (by decide), hdi, VG.Proof.Argon2.X86.Derive.addr_shift]
    have b1 : cur * 1024 + 4 * n + 4 ≤ blocksN s₀ * 1024 := by omega_using [hc', hn]
    have b2 : cur * 1024 + 1024 < 2 ^ 64 := by omega_using [hc', hb]
    have inS : InRegions (t.rd ++ t.wr) (addr (t.gpr .esi) (4 * n)) 4 := by
      obtain ⟨R, hR, off, bR, lR⟩ := hPw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      have RW : R ∈ t.wr ∧ R.len ≤ 2 ^ 32 := by
        rw [it.wr]
        rcases hR with rfl | rfl
        · exact ⟨scr_mem hp, by show 16384 ≤ 2 ^ 32; decide⟩
        · exact ⟨mem_mem hp, by show blocksN s₀ * 1024 ≤ 2 ^ 32; omega_using [hm]⟩
      rw [ea, eP, bR, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact ⟨R, List.mem_append_right _ RW.1, Offset.contains_base _ (by omega_using [lR, hn])
        (by have := RW.2; omega_using [lR, hn, this])⟩
    have inMc : (memR s₀).Contains (addr (t.gpr .edi) (4 * n)) 4 := by
      rw [eb, VG.Proof.Argon2.X86.Derive.mem_addr' hp (by omega_using [b1])]
      exact Offset.contains_base _ b1 (by omega_using [b1, hb])
    have inC : (⟨matrixCell (memB s₀) cur, 1024⟩ : Region).Contains (addr (t.gpr .edi) (4 * n)) 4 := by
      rw [eb, VG.Proof.Argon2.X86.Derive.mem_addr' hp (by omega_using [b1]), cell]
      exact Offset.contains _ (by omega_using []) (by omega_using [hn]) b2
    have inM : InRegions t.wr (addr (t.gpr .edi) (4 * n)) 4 := ⟨memR s₀, by rw [it.wr]; exact mem_mem hp, inMc⟩
    -- The word.
    have fin : ∀ (v : BitVec 32) (u : State), u.mem = t.mem.writeW (addr (t.gpr .edi) (4 * n)) v →
        u.rd = t.rd → u.wr = t.wr → (∀ r, r ≠ .eax → u.gpr r = s.gpr r) →
        v = (if xo then s.mem.readW (addr P (4 * n)) 32 ^^^ VG.Proof.Argon2.X86.Derive.mw s₀ s.mem (cur * 1024 + 4 * n)
          else s.mem.readW (addr P (4 * n)) 32) →
        VG.Proof.Argon2.X86.Derive.Inv s₀ u ∧ (∀ r, r ≠ .eax → u.gpr r = s.gpr r) ∧
        Frame [⟨matrixCell (memB s₀) cur, 1024⟩] s.mem u.mem ∧
        ∀ i < 256, VG.Proof.Argon2.X86.Derive.mw s₀ u.mem (cur * 1024 + 4 * i) = if i < n + 1 then
          (if xo then s.mem.readW (addr P (4 * i)) 32 ^^^ VG.Proof.Argon2.X86.Derive.mw s₀ s.mem (cur * 1024 + 4 * i)
            else s.mem.readW (addr P (4 * i)) 32)
          else VG.Proof.Argon2.X86.Derive.mw s₀ s.mem (cur * 1024 + 4 * i) := fun v u hm hrd hwr gu ev => by
      have fu : Frame [⟨matrixCell (memB s₀) cur, 1024⟩] s.mem u.mem := by
        rw [hm]; exact ft.writeW (List.mem_singleton_self _) v inC
      have iu : VG.Proof.Argon2.X86.Derive.Inv s₀ u := it.step (by rw [gu _ (by decide), gt _ (by decide)])
        (by rw [gu _ (by decide), gt _ (by decide)]) hrd hwr
        (by rw [hm]; exact (Frame.refl _ _).writeW (r := memR s₀) (by simp) v inMc)
      refine ⟨iu, gu, fu, fun i hi => ?_⟩
      rw [hm, eb, VG.Proof.Argon2.X86.Derive.mw_store hp _ b1 (by omega_using [hi, hc', hb]) (by omega_using []), wt i hi]
      by_cases e : i = n
      · subst e
        rw [ite_eq_left rfl, ite_eq_left (show i < i + 1 by omega_using []), ev]
      · rw [ite_eq_right (show ¬cur * 1024 + 4 * n = cur * 1024 + 4 * i by omega_using [e])]
        by_cases c : i < n
        · rw [ite_eq_left c, ite_eq_left (show i < n + 1 by omega_using [c])]
        · rw [ite_eq_right c, ite_eq_right (show ¬i < n + 1 by omega_using [c, e])]
    cases xo
    · simp only [writeWord, Bool.false_eq_true, ite_false, List.nil_append]
      refine wp_ldm rfl inS fun u₁ v₁ => ?_
      refine wp_stm (b := .edi) (v₁.other .edi (by decide)) (by rw [v₁.wr]; exact inM) fun u mu => WP.block_nil ?_
      refine fin _ u (by rw [mu.mem, v₁.mem]) (by rw [mu.rd, v₁.rd]) (by rw [mu.wr, v₁.wr])
        (fun r hr => by rw [mu.gpr, v₁.other r hr, gt r hr]) ?_
      simp only [Bool.false_eq_true, ite_false]
      rw [v₁.gpr, ea, sw_t]
    · simp only [writeWord, ite_true, List.cons_append, List.nil_append]
      refine wp_ldm rfl inS fun u₁ v₁ => ?_
      refine wp_xorm (b := .edi) (v₁.other .edi (by decide)) (by rw [v₁.rd, v₁.wr]; exact
        ⟨memR s₀, List.mem_append_right _ (by rw [it.wr]; exact mem_mem hp), inMc⟩) fun u₂ v₂ => ?_
      refine wp_stm (b := .edi) (by rw [v₂.other .edi (by decide), v₁.other .edi (by decide)])
        (by rw [v₂.wr, v₁.wr]; exact inM) fun u mu => WP.block_nil ?_
      refine fin _ u (by rw [mu.mem, v₂.mem, v₁.mem]) (by rw [mu.rd, v₂.rd, v₁.rd]) (by rw [mu.wr, v₂.wr, v₁.wr])
        (fun r hr => by rw [mu.gpr, v₂.other r hr, v₁.other r hr, gt r hr]) ?_
      simp only [ite_true]
      rw [v₂.gpr, v₁.gpr, v₁.mem, ea, sw_t, eb, ← VG.Proof.Argon2.X86.Derive.mw, wt n (by omega_using [hn]),
        ite_eq_right (show ¬n < n by omega_using [])]

end

end VG.Proof.Argon2.X86.Derive

end

/-!
# Argon2 on x86 (32-bit): one block of the filling loops

`fillCompress_ok`: G of the previous and reference blocks to
`scratch + 4096`; `fillWrite_ok`: the current block, copied or XORed;
`fillBlock_ok`: the filling state after one block (`Spec.Argon2.fillBlock`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_sub wp_addm wp_cmpi wp_ldm wp_stm wp_andi
  wp_sbb_self wp_and wp_xor wp_xorm)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState compress xorBlock)
open VG.Proof.Argon2.X86 (blk ofWords blk_of_words xor_words)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off refLaneOff startOff countOff tmpOff curOff writeBlock)

theorem FS.of_upd {s₀ s t : State} {pass slice lane index ctr : Nat} {st : FillState} {r : Reg} {v : BitVec 32}
    (h : VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st s) (u : Upd s t r v) (h1 : r ≠ .esp) (h2 : r ≠ .ebp) :
    VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st t :=
  h.keep (h.inv.upd u h1 h2) (fun d _ => lw_mem u.mem d) (by rw [u.mem]) fun _ _ => by rw [u.mem]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem outside_work : VG.Proof.Argon2.X86.Derive.Outside s₀ ⟨VG.Proof.Argon2.X86.Derive.scrB s₀, 4096⟩ := by
  have := VG.Proof.Argon2.X86.Derive.outside_scr hp (o := 0) (n := 4096) (.inl (by decide))
  simpa using this

/-- The locals are kept by writes outside them. -/
theorem lw_outside {s t : State} {rs : List Region} (f : Frame rs s.mem t.mem) (ho : ∀ r ∈ rs, VG.Proof.Argon2.X86.Derive.Outside s₀ r)
    {d : Nat} (hd : d + 4 ≤ 144) : lw s₀ t d = lw s₀ s d :=
  f.readW (r := ⟨addr (VG.Proof.Argon2.X86.Derive.E s₀) d, 4⟩) (Region.contains_self _ _)
    (fun r hr => (ho r hr).1.symm.sub_left (VG.Proof.Argon2.X86.Derive.loc_word_sub hp hd)) (by decide)

/-- `fillCompress`: G of the previous and reference blocks, to `scratch + 4096`. -/
theorem fillCompress_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st s) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) {R : Nat} (hR : R < blocksN s₀)
    (htmp : lw s₀ s tmpOff = memP s₀ + BitVec.ofNat 32 (R * 1024)) :
    WP isa Impl.Argon2.X86.Derive.fillCompress s fun t => VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st t ∧
      (∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ s d) ∧
      VG.Proof.Argon2.X86.blk t.mem (scrP s₀) 4096 = compress (blockAt s.mem (matrixCell (memB s₀) (lane * (prm s₀).laneLen +
        (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) % (prm s₀).laneLen)))
        (blockAt s.mem (matrixCell (memB s₀) R)) := by
  have L8 := VG.Proof.Argon2.X86.Derive.laneLen_ge hp
  obtain ⟨cl, _⟩ := VG.Proof.Argon2.X86.Derive.cell_fits hp hl (col := (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) %
    (prm s₀).laneLen) (Nat.mod_lt _ (by omega))
  unfold Impl.Argon2.X86.Derive.fillCompress Impl.Argon2.X86.Derive.compressCall
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.prevPointer_ok hp h.inv h.pr h.pos hl hs hi).mono fun s₁ ⟨a₁, k₁⟩ => ?_)
  generalize (lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) %
    (prm s₀).laneLen) = P at cl a₁ ⊢
  have h₁ := h.of_keep k₁
  refine WP.seq (wp_ldloc hp h₁.inv (d := tmpOff) (by decide) fun s₂ u₂ => ?_)
  have h₂ := h₁.of_upd u₂ (by decide) (by decide)
  refine wp_ldarg hp h₂.inv (i := 15) (by decide) fun s₃ u₃ => ?_
  have h₃ := h₂.of_upd u₃ (by decide) (by decide)
  refine wp_mov fun s₄ u₄ => ?_
  have h₄ := h₃.of_upd u₄ (by decide) (by decide)
  refine wp_addi fun s₅ u₅ => WP.block_nil ?_
  have h₅ := h₄.of_upd u₅ (by decide) (by decide)
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, k₁.mem]
  have ax : s₅.gpr .eax = memP s₀ + BitVec.ofNat 32 (P * 1024) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), a₁]
  have sx : s₅.gpr .esi = memP s₀ + BitVec.ofNat 32 (R * 1024) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, lw_mem k₁.mem, htmp]
  have dx : s₅.gpr .edx = scrP s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  have cx : s₅.gpr .ecx = scrP s₀ + BitVec.ofNat 32 4096 := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr]; rfl
  refine VG.Proof.Argon2.X86.Derive.ccall_ok hp h₅.inv dx (o := 4096) (by decide) (by decide) cx (by rw [ax]; exact .inl ⟨P, cl, rfl⟩)
    (by rw [sx]; exact .inl ⟨R, hR, rfl⟩) fun t it _ f post => ?_
  have ho : ∀ r ∈ [⟨VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 4096, 1024⟩, ⟨VG.Proof.Argon2.X86.Derive.scrB s₀, 4096⟩, callR s₀], VG.Proof.Argon2.X86.Derive.Outside s₀ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact VG.Proof.Argon2.X86.Derive.outside_scr hp (.inl (by decide))
    · exact VG.Proof.Argon2.X86.Derive.outside_work hp
    · exact VG.Proof.Argon2.X86.Derive.outside_call hp
  refine ⟨h₅.frame hp it f ho, fun d hd => by rw [VG.Proof.Argon2.X86.Derive.lw_outside hp f ho hd, lw_mem m₅], ?_⟩
  rw [post, ax, sx, cell_addr hp cl, cell_addr hp hR, m₅]

end


section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `fillWrite`: G's output to the current block, XORed into it after the first pass. -/
theorem fillWrite_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) {C : Nat} (hC : C < blocksN s₀)
    (hcur : lw s₀ s curOff = memP s₀ + BitVec.ofNat 32 (C * 1024)) :
    WP isa Impl.Argon2.X86.Derive.fillWrite s fun t => VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧
      Frame [⟨matrixCell (memB s₀) C, 1024⟩] s.mem t.mem ∧
      blockAt t.mem (matrixCell (memB s₀) C) = if pass = 0 then VG.Proof.Argon2.X86.blk s.mem (scrP s₀) 4096 else
        xorBlock (VG.Proof.Argon2.X86.blk s.mem (scrP s₀) 4096) (blockAt s.mem (matrixCell (memB s₀) C)) := by
  unfold Impl.Argon2.X86.Derive.fillWrite
  refine WP.seq (wp_ldarg hp h.inv (i := 15) (by decide) fun s₁ u₁ => ?_)
  have h₁ := h.of_upd u₁ (by decide) (by decide)
  refine wp_addi fun s₂ u₂ => ?_
  have h₂ := h₁.of_upd u₂ (by decide) (by decide)
  refine wp_ldloc hp h₂.inv (d := curOff) (by decide) fun s₃ u₃ => ?_
  have h₃ := h₂.of_upd u₃ (by decide) (by decide)
  refine wp_ldloc hp h₃.inv (d := passOff) (by decide) fun s₄ u₄ => wp_cmpi fun s₅ f₅ _ z₅ => WP.block_nil ?_
  have h₅ := (h₃.of_upd u₄ (by decide) (by decide)).of_keep (Divide.Keep.of_fupd f₅)
  have m₅ : s₅.mem = s.mem := by rw [f₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have si : s₅.gpr .esi = scrP s₀ + BitVec.ofNat 32 4096 := by
    rw [f₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr]; rfl
  have di : s₅.gpr .edi = memP s₀ + BitVec.ofNat 32 (C * 1024) := by
    rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, lw_mem u₂.mem, lw_mem u₁.mem, hcur]
  have z : ∀ y : BitVec 32, y - 0 = y := fun y => by simp
  have hsf := hp.scr_fits
  have eP : (scrP s₀ + BitVec.ofNat 32 4096).setWidth 64 = VG.Proof.Argon2.X86.Derive.scrB s₀ + BitVec.ofNat 64 4096 :=
    HPrime.setWidth_add (by omega)
  have Pfit : (scrP s₀ + BitVec.ofNat 32 4096).toNat + 1024 ≤ 2 ^ 32 := by rw [add_nat (by omega)]; omega
  have Pw : ∃ R ∈ [VG.Proof.Argon2.X86.Derive.scrR s₀, memR s₀], ∃ off, (scrP s₀ + BitVec.ofNat 32 4096).setWidth 64 =
      R.base + BitVec.ofNat 64 off ∧ off + 1024 ≤ R.len := ⟨VG.Proof.Argon2.X86.Derive.scrR s₀, by simp, 4096, eP, by show 4096 + 1024 ≤ 16384; decide⟩
  have PC : Region.Disjoint ⟨(scrP s₀ + BitVec.ofNat 32 4096).setWidth 64, 1024⟩ ⟨matrixCell (memB s₀) C, 1024⟩ := by
    rw [eP]
    exact (hp.mem_scr.symm.sub_left (Offset.sub_base _ (by decide))).sub_right (cell_in_mem hC)
  have nxt : VG.Proof.Argon2.X86.blk s.mem (scrP s₀) 4096 = ofWords fun i => VG.Proof.Argon2.X86.Derive.sw s₀ s.mem (4096 + 4 * i) :=
    blk_of_words fun _ _ => rfl
  have old : blockAt s.mem (matrixCell (memB s₀) C) = ofWords fun i => VG.Proof.Argon2.X86.Derive.mw s₀ s.mem (C * 1024 + 4 * i) := by
    rw [VG.Proof.Argon2.X86.Derive.cell_blk hp _ hC]; exact blk_of_words fun _ _ => rfl
  have done : ∀ (xo : Bool) (t : State), (∀ i < 256, VG.Proof.Argon2.X86.Derive.mw s₀ t.mem (C * 1024 + 4 * i) = if i < 256 then
        (if xo then s₅.mem.readW (addr (scrP s₀ + BitVec.ofNat 32 4096) (4 * i)) 32 ^^^ VG.Proof.Argon2.X86.Derive.mw s₀ s₅.mem (C * 1024 + 4 * i)
          else s₅.mem.readW (addr (scrP s₀ + BitVec.ofNat 32 4096) (4 * i)) 32)
        else VG.Proof.Argon2.X86.Derive.mw s₀ s₅.mem (C * 1024 + 4 * i)) →
      blockAt t.mem (matrixCell (memB s₀) C) = if xo then
        xorBlock (VG.Proof.Argon2.X86.blk s.mem (scrP s₀) 4096) (blockAt s.mem (matrixCell (memB s₀) C)) else VG.Proof.Argon2.X86.blk s.mem (scrP s₀) 4096 :=
    fun xo t wt => by
      have e : blockAt t.mem (matrixCell (memB s₀) C) = ofWords fun i => if xo then
          VG.Proof.Argon2.X86.Derive.sw s₀ s.mem (4096 + 4 * i) ^^^ VG.Proof.Argon2.X86.Derive.mw s₀ s.mem (C * 1024 + 4 * i) else VG.Proof.Argon2.X86.Derive.sw s₀ s.mem (4096 + 4 * i) := by
        rw [VG.Proof.Argon2.X86.Derive.cell_blk hp _ hC]
        exact blk_of_words fun i hi => by rw [← VG.Proof.Argon2.X86.Derive.mw, wt i hi, ite_eq_left hi, m₅, VG.Proof.Argon2.X86.Derive.addr_shift]
      rw [e, nxt, old]
      cases xo
      · rfl
      · simp only [ite_true]; rw [xor_words]
  refine WP.ite (decide (pass = 0)) (by
    show s₅.zf = _
    rw [z₅, u₄.gpr, lw_mem u₃.mem, lw_mem u₂.mem, lw_mem u₁.mem, h.pos.pass, z, Wp.ofNat_beq_zero hpass])
    (fun hb => ?_) fun hb => ?_
  · refine ((VG.Proof.Argon2.X86.Derive.writeWords_ok hp h₅.inv hC false si Pfit Pw PC di 256 (Nat.le_refl _)).mono fun t ⟨it, _, ft, wt⟩ =>
      ⟨it, by rw [← m₅]; exact ft, ?_⟩)
    rw [done false t wt, ite_eq_left (of_decide_eq_true hb)]; rfl
  · refine ((VG.Proof.Argon2.X86.Derive.writeWords_ok hp h₅.inv hC true si Pfit Pw PC di 256 (Nat.le_refl _)).mono fun t ⟨it, _, ft, wt⟩ =>
      ⟨it, by rw [← m₅]; exact ft, ?_⟩)
    rw [done true t wt, ite_eq_right (of_decide_eq_false hb)]; rfl

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `fillBlock`: one block of the filling loops. -/
theorem fillBlock_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index) :
    WP isa Impl.Argon2.X86.Derive.fillBlock s fun t =>
      VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index (VG.Proof.Argon2.X86.Derive.ctrNext (prm s₀) pass slice index ctr)
        (Spec.Argon2.fillBlock (prm s₀) pass slice lane index st) t := by
  have hb : blocksN s₀ = (prm s₀).blocks := hp.blocks
  unfold Impl.Argon2.X86.Derive.fillBlock
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.randomSource_ok hp h hpass hl hs hi).mono fun t₁ ⟨h₁, w₁⟩ => ?_)
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.reference_ok hp ⟨h₁, rfl, rfl⟩ hpass hl hs hi active).mono fun t₂ ⟨h₂, tmp₂, cur₂⟩ => ?_)
  rw [w₁] at tmp₂
  have refLt := Proof.Argon2.reference_cell_lt (prm s₀) hp.lanes_pos hp.memory_ge pass lane slice index
    (Proof.Argon2.FillStep.random (prm s₀) pass lane slice index st.memory) hl
  have curLt := Proof.Argon2.current_cell_lt (prm s₀) hp.lanes_pos hl hs hi
  have prevLt := Proof.Argon2.previous_cell_lt (prm s₀) hp.lanes_pos hp.memory_ge
    (column := slice * (prm s₀).segmentLen + index) hl
  simp only at refLt
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.fillCompress_ok hp h₂.fs hl hs hi (by rw [hb]; exact refLt) tmp₂).mono
    fun t₃ ⟨h₃, l₃, c₃⟩ => ?_)
  refine (VG.Proof.Argon2.X86.Derive.fillWrite_ok hp h₃ hpass (C := lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index))
    (by rw [hb]; exact curLt) (by rw [l₃ _ (by decide)]; exact cur₂)).mono
    fun t ⟨it, ft, bt⟩ => ?_
  have kept : ∀ j < (prm s₀).blocks, j ≠ lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index) →
      blockAt t.mem (matrixCell (memB s₀) j) = blockAt t₃.mem (matrixCell (memB s₀) j) := fun j hj ne =>
    blockAt_keep ft fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact cell_other hp (by rw [hb]; exact hj) (by rw [hb]; exact curLt) ne
  have lt : ∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ t₃ d := fun d hd =>
    ft.readW (r := ⟨addr (VG.Proof.Argon2.X86.Derive.E s₀) d, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (loc_disj hp hd (memR s₀) (by simp)).sub_right (cell_in_mem (by rw [hb]; exact curLt))) (by decide)
  refine ⟨it, Prm.of_lw h₃.pr fun d hd => lt d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
    h₃.pos.of_lw fun d hd => lt d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
    ?_, ?_⟩
  · obtain ⟨c0, c1, c2 | ⟨c3, c4⟩⟩ := h₃.cache
    · exact ⟨c0, by rw [lt _ (by decide)]; exact c1, .inl c2⟩
    · refine ⟨c0, by rw [lt _ (by decide)]; exact c1, .inr ⟨c3, ?_⟩⟩
      rw [VG.Proof.Argon2.X86.Derive.scr_blk hp _ (by decide), blockAt_keep ft (fun r hr => ?_), ← VG.Proof.Argon2.X86.Derive.scr_blk hp _ (by decide), c4]
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.mem_scr.symm.sub_left (Offset.sub_base _ (by decide))).sub_right
        (cell_in_mem (by rw [hb]; exact curLt))
  · rw [Proof.Argon2.FillStep.memory _ _ _ _ _ _ active]
    simp only [Proof.Argon2.FillStep.update]
    refine Represents.update h₃.mem _ curLt _ ?_ kept
    rw [bt, c₃, h₂.fs.mem.block _ prevLt, h₂.fs.mem.block _ refLt, h₃.mem.block _ curLt]

end
end VG.Proof.Argon2.X86.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.Derive.FillLoops`. -/
section

/-!
# Argon2 on x86 (32-bit): the filling loops

`FB s₀ st`: the body with the memory matrix holding `st`'s. `segment_ok`:
a segment, from its first index (`Proof.Argon2.segmentStart`), through
`fillBlock_ok`; `lanes_ok`, `slices_ok` and `passes_ok` the loops around
it, and `fill_ok` all passes, from the initialized memory:
`Spec.Argon2.fill` (`Proof.Argon2.iterations_fill`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_sub wp_addm wp_cmpi wp_ldm wp_stm wp_andi
  wp_sbb_self wp_and wp_xor wp_xorm)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState compress xorBlock)
open VG.Proof.Argon2.X86 (blk)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  divisorOff strideOff)

/-- The body, the memory matrix holding `st`'s. -/
structure FB (s₀ : State) (st : FillState) (s : State) : Prop where
  inv : VG.Proof.Argon2.X86.Derive.Inv s₀ s
  pr : Prm s₀ s
  mem : Represents s.mem (memB s₀) (prm s₀).blocks st.memory

/-- `cmp d, src`, for a source of known value. -/
theorem wp_cmpS {s : State} {d : Reg} {src : Src} {v : BitVec 32} (hv : readSrc s src = some v)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Fupd s s' → s'.cf = some (decide ((s.gpr d).toNat < v.toNat)) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d src :: is)) s Q :=
  VG.X86.Wp.cons (s' := arithFlags s (s.gpr d - v) (decide ((s.gpr d).toNat < v.toNat))
      (subOverflow (s.gpr d) v (s.gpr d - v)))
    (by simp only [exec, execAlu, hv, Option.bind_some]) (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- A store to the locals keeps their other words, the cached address block and the matrix. -/
theorem loc_store {s t : State} {d : Nat} (hd : d + 4 ≤ 144) {v : BitVec 32}
    (hm : t.mem = s.mem.writeW (addr (VG.Proof.Argon2.X86.Derive.E s₀) d) v) :
    (∀ e, e + 4 ≤ 236 → (e + 4 ≤ d ∨ d + 4 ≤ e) → lw s₀ t e = lw s₀ s e) ∧
    VG.Proof.Argon2.X86.blk t.mem (scrP s₀) 6144 = VG.Proof.Argon2.X86.blk s.mem (scrP s₀) 6144 ∧
    ∀ k < (prm s₀).blocks, blockAt t.mem (matrixCell (memB s₀) k) = blockAt s.mem (matrixCell (memB s₀) k) := by
  have f : Frame [⟨addr (VG.Proof.Argon2.X86.Derive.E s₀) d, 4⟩] s.mem t.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) v (Region.contains_self _ _)
  refine ⟨fun e he hde => ?_, ?_, fun k hk => ?_⟩
  · show t.mem.readW _ 32 = _
    rw [hm, lw_store hp (by omega) he hde.symm]
  · rw [VG.Proof.Argon2.X86.Derive.scr_blk hp t.mem (by decide), VG.Proof.Argon2.X86.Derive.scr_blk hp s.mem (by decide)]
    refine blockAt_keep f fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact (loc_disj hp hd (VG.Proof.Argon2.X86.Derive.scrR s₀) (by simp)).symm.sub_left (Offset.sub_base _ (by decide))
  · refine blockAt_keep f fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have hk' : k < blocksN s₀ := by rw [hp.blocks]; exact hk
    exact (loc_disj hp hd (memR s₀) (by simp)).symm.sub_left (cell_in_mem hk')

/-- A store to a word of the locals other than the parameters keeps `FB`. -/
theorem FB.store {st : FillState} {s t : State} (h : VG.Proof.Argon2.X86.Derive.FB s₀ st s) (it : VG.Proof.Argon2.X86.Derive.Inv s₀ t) {d : Nat} (hd : d + 4 ≤ 144)
    (hd' : ∀ e ∈ [divisorOff, segLenOff, laneLenOff, strideOff], e + 4 ≤ d ∨ d + 4 ≤ e) {v : BitVec 32}
    (hm : t.mem = s.mem.writeW (addr (VG.Proof.Argon2.X86.Derive.E s₀) d) v) : VG.Proof.Argon2.X86.Derive.FB s₀ st t := by
  obtain ⟨l, _, c⟩ := VG.Proof.Argon2.X86.Derive.loc_store hp hd hm
  exact ⟨it, Prm.of_lw h.pr fun e he => l e (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he; rcases he with rfl | rfl | rfl | rfl <;> decide)
    (hd' e he), Represents.keep h.mem c⟩

omit hp in
theorem FB.of_upd {st : FillState} {s t : State} {r : Reg} {v : BitVec 32} (h : VG.Proof.Argon2.X86.Derive.FB s₀ st s) (u : Upd s t r v)
    (h1 : r ≠ .esp) (h2 : r ≠ .ebp) : VG.Proof.Argon2.X86.Derive.FB s₀ st t :=
  ⟨h.inv.upd u h1 h2, h.pr.of_mem u.mem, by rw [u.mem]; exact h.mem⟩

/-- `advance d src`: `[ebp + d] += 1`, compared with `src`. -/
theorem advance_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) {d n : Nat} (hd : d + 4 ≤ 144) (hn : lw s₀ s d = BitVec.ofNat 32 n)
    (hn' : n + 1 < 2 ^ 32) {src : Src} {B : Nat} (hB : B < 2 ^ 32)
    (hsrc : ∀ t : State, VG.Proof.Argon2.X86.Derive.Inv s₀ t → t.mem = s.mem.writeW (addr (VG.Proof.Argon2.X86.Derive.E s₀) d) (BitVec.ofNat 32 (n + 1)) →
      readSrc t src = some (BitVec.ofNat 32 B)) :
    WP isa (.block (Impl.Argon2.X86.Derive.advance d src)) s fun t => VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧
      t.mem = s.mem.writeW (addr (VG.Proof.Argon2.X86.Derive.E s₀) d) (BitVec.ofNat 32 (n + 1)) ∧ t.cf = some (decide (n + 1 < B)) ∧
      ∀ r, r ≠ .eax → t.gpr r = s.gpr r := by
  unfold Impl.Argon2.X86.Derive.advance
  refine wp_ldloc hp h (d := d) hd fun s₁ u₁ => wp_addi fun s₂ u₂ => ?_
  have i₂ := (h.upd u₁ (by decide) (by decide)).upd u₂ (by decide) (by decide)
  have a₂ : s₂.gpr .eax = BitVec.ofNat 32 (n + 1) := by
    rw [u₂.gpr, u₁.gpr, hn, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat]
  refine wp_stloc hp i₂ (d := d) hd fun s₃ i₃ _ _ g₃ m₃ => ?_
  have m₃' : s₃.mem = s.mem.writeW (addr (VG.Proof.Argon2.X86.Derive.E s₀) d) (BitVec.ofNat 32 (n + 1)) := by
    rw [m₃, a₂, u₂.mem, u₁.mem]
  refine VG.Proof.Argon2.X86.Derive.wp_cmpS (hsrc s₃ i₃ m₃') fun t f c => WP.block_nil ⟨i₃.step (by rw [f.gpr]) (by rw [f.gpr]) f.rd f.wr
    (by rw [f.mem]; exact Frame.refl _ _), by rw [f.mem, m₃'], ?_, fun r hr => ?_⟩
  · rw [c, g₃, a₂, Wp.toNat_ofNat_lt hn', Wp.toNat_ofNat_lt hB]
  · rw [f.gpr, g₃, u₂.other _ hr, u₁.other _ hr]

end


/-- The body at a lane of the filling loops. -/
structure LS (s₀ : State) (st : FillState) (pass slice lane : Nat) (s : State) : Prop where
  fb : VG.Proof.Argon2.X86.Derive.FB s₀ st s
  pass : lw s₀ s passOff = BitVec.ofNat 32 pass
  slice : lw s₀ s sliceOff = BitVec.ofNat 32 slice
  lane : lw s₀ s laneOff = BitVec.ofNat 32 lane

theorem FS.ls {s₀ s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st s) : VG.Proof.Argon2.X86.Derive.LS s₀ st pass slice lane s :=
  ⟨⟨h.inv, h.pr, h.mem⟩, h.pos.pass, h.pos.slice, h.pos.lane⟩

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The index advanced. -/
theorem FS.next {s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st s) (it : VG.Proof.Argon2.X86.Derive.Inv s₀ t)
    (hm : t.mem = s.mem.writeW (addr (VG.Proof.Argon2.X86.Derive.E s₀) indexOff) (BitVec.ofNat 32 (index + 1))) :
    VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane (index + 1) ctr st t := by
  obtain ⟨l, b, c⟩ := VG.Proof.Argon2.X86.Derive.loc_store hp (d := indexOff) (by decide) hm
  refine ⟨it, Prm.of_lw h.pr fun e he => l e (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he; rcases he with rfl | rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at he; rcases he with rfl | rfl | rfl | rfl <;> decide),
    ⟨by rw [l _ (by decide) (by decide)]; exact h.pos.pass, by rw [l _ (by decide) (by decide)]; exact h.pos.slice,
      by rw [l _ (by decide) (by decide)]; exact h.pos.lane, ?_⟩, ?_, Represents.keep h.mem c⟩
  · show t.mem.readW _ 32 = _
    rw [hm, Mem.readW_writeW_self32]
  · obtain ⟨c0, c1, c2 | ⟨c3, c4⟩⟩ := h.cache
    · exact ⟨c0, by rw [l _ (by decide) (by decide)]; exact c1, .inl c2⟩
    · exact ⟨c0, by rw [l _ (by decide) (by decide)]; exact c1, .inr ⟨c3, by rw [b]; exact c4⟩⟩

/-- The block of `segmentStart`: the counter cleared, and ZF in the first slice of the first pass. -/
theorem segStartBlk_ok {s : State} {pass slice lane : Nat} {st : FillState} (h : VG.Proof.Argon2.X86.Derive.LS s₀ st pass slice lane s)
    (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa (.block (Impl.Argon2.X86.Derive.setLocal counterOff 0 ++
      ([.mov .eax (Impl.Argon2.X86.Derive.fr passOff), .alu .or .eax (Impl.Argon2.X86.Derive.fr sliceOff)] :
        List Instr))) s
      fun t => VG.Proof.Argon2.X86.Derive.LS s₀ st pass slice lane t ∧ lw s₀ t counterOff = 0 ∧
        t.zf = some (decide (pass = 0 ∧ slice = 0)) := by
  unfold Impl.Argon2.X86.Derive.setLocal
  simp only [List.cons_append, List.nil_append]
  refine wp_movi fun s₁ u₁ => ?_
  have f₁ := h.fb.of_upd u₁ (by decide) (by decide)
  refine wp_stloc hp f₁.inv (d := counterOff) (by decide) fun s₂ i₂ v₂ o₂ _ m₂ => ?_
  have f₂ := f₁.store hp i₂ (d := counterOff) (by decide) (by decide) m₂
  have L₂ : ∀ d ∈ [passOff, sliceOff, laneOff], lw s₀ s₂ d = lw s₀ s d := fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rw [o₂ d (by rcases hd with rfl | rfl | rfl <;> decide) (by rcases hd with rfl | rfl | rfl <;> decide),
      lw_mem u₁.mem]
  refine wp_ldloc hp f₂.inv (d := passOff) (by decide) fun s₃ u₃ => ?_
  have f₃ := f₂.of_upd u₃ (by decide) (by decide)
  refine VG.Proof.Argon2.X86.Derive.wp_orm f₃.inv.ebp (loc_in' hp f₃.inv (d := sliceOff) (by decide)) fun s₄ u₄ z₄ => WP.block_nil ?_
  have f₄ := f₃.of_upd u₄ (by decide) (by decide)
  have m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  refine ⟨⟨f₄, by rw [lw_mem m₄, L₂ _ (by simp)]; exact h.pass, by rw [lw_mem m₄, L₂ _ (by simp)]; exact h.slice,
    by rw [lw_mem m₄, L₂ _ (by simp)]; exact h.lane⟩, by rw [lw_mem m₄, v₂, u₁.gpr], ?_⟩
  rw [z₄, u₃.gpr, show s₃.mem.readW (addr (VG.Proof.Argon2.X86.Derive.E s₀) sliceOff) 32 = lw s₀ s₃ sliceOff from rfl, lw_mem u₃.mem,
    L₂ _ (by simp), L₂ _ (by simp), h.pass, h.slice, VG.Proof.Argon2.X86.Derive.or_zero hpass (by omega)]

/-- `segmentStart`: the counter cleared, and the segment's first index. -/
theorem segmentStart_ok {s : State} {pass slice lane : Nat} {st : FillState} (h : VG.Proof.Argon2.X86.Derive.LS s₀ st pass slice lane s)
    (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa Impl.Argon2.X86.Derive.segmentStart s
      (VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane (Proof.Argon2.segmentStart pass slice) 0 st) := by
  unfold Impl.Argon2.X86.Derive.segmentStart
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.segStartBlk_ok hp h hpass hs).mono fun s₄ ⟨f₄, c₄, z₄⟩ => ?_)
  refine WP.ite (decide (pass = 0 ∧ slice = 0)) z₄ (fun hb => ?_) fun hb => ?_
  all_goals
    unfold Impl.Argon2.X86.Derive.setLocal
    refine wp_movi fun s₅ u₅ => ?_
    have f₅ := f₄.fb.of_upd u₅ (by decide) (by decide)
    refine wp_stloc hp f₅.inv (d := indexOff) (by decide) fun t it vt ot _ mt => WP.block_nil ?_
    have ft := f₅.store hp it (d := indexOff) (by decide) (by decide) mt
    have Lt : ∀ d ∈ [passOff, sliceOff, laneOff, counterOff], lw s₀ t d = lw s₀ s₄ d := fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rw [ot d (by rcases hd with rfl | rfl | rfl | rfl <;> decide)
        (by rcases hd with rfl | rfl | rfl | rfl <;> decide), lw_mem u₅.mem]
    refine ⟨ft.inv, ft.pr, ⟨by rw [Lt _ (by simp)]; exact f₄.pass, by rw [Lt _ (by simp)]; exact f₄.slice,
      by rw [Lt _ (by simp)]; exact f₄.lane, ?_⟩, ⟨by decide, by rw [Lt _ (by simp), c₄]; rfl, .inl rfl⟩, ft.mem⟩
    rw [vt, u₅.gpr, Proof.Argon2.segmentStart]
  · rw [ite_eq_left (of_decide_eq_true hb)]; rfl
  · rw [ite_eq_right (of_decide_eq_false hb)]; rfl

end

theorem segment_snoc (p : Spec.Argon2.Params) (pass lane slice start k : Nat) (st : FillState) :
    Proof.Argon2.segment p pass lane slice start (k + 1) st =
      Spec.Argon2.fillBlock p pass slice lane (start + k) (Proof.Argon2.segment p pass lane slice start k st) := by
  rw [Proof.Argon2.segment_append, Proof.Argon2.segment_succ, Proof.Argon2.segment_zero]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The comparison of the segment's first index with its length. -/
theorem segCmp_ok {s : State} {pass slice lane S ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane S ctr st s) (hS : S ≤ 2) :
    WP isa (.block [.mov .eax (Impl.Argon2.X86.Derive.fr indexOff),
      .alu .cmp .eax (Impl.Argon2.X86.Derive.fr segLenOff)]) s
      fun t => VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane S ctr st t ∧ t.cf = some (decide (S < (prm s₀).segmentLen)) := by
  have sl := VG.Proof.Argon2.X86.Derive.segLen_lt hp
  refine wp_ldloc hp h.inv (d := indexOff) (by decide) fun t₂ u₂ => ?_
  have h₂ := h.of_upd u₂ (by decide) (by decide)
  refine wp_cmpm h₂.inv.ebp (loc_in' hp h₂.inv (d := segLenOff) (by decide)) fun t₃ f₃ c₃ _ => WP.block_nil ?_
  refine ⟨h₂.of_keep (Divide.Keep.of_fupd f₃), ?_⟩
  rw [c₃, u₂.gpr, show t₂.mem.readW (addr (VG.Proof.Argon2.X86.Derive.E s₀) segLenOff) 32 = lw s₀ t₂ segLenOff from rfl, h₂.pr.segLen,
    h.pos.index, Wp.toNat_ofNat_lt (by omega), Wp.toNat_ofNat_lt (by omega)]

/-- One block of a segment, and the index advanced. -/
theorem segStep_ok {t : State} {pass slice lane i c : Nat} {X : FillState}
    (ht : VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane i c X t) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : i < (prm s₀).segmentLen) (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ i) :
    WP isa (.seq Impl.Argon2.X86.Derive.fillBlock
      (.block (Impl.Argon2.X86.Derive.advance indexOff (Impl.Argon2.X86.Derive.fr segLenOff)))) t
      fun v => VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane (i + 1) (VG.Proof.Argon2.X86.Derive.ctrNext (prm s₀) pass slice i c)
        (Spec.Argon2.fillBlock (prm s₀) pass slice lane i X) v ∧
        v.cf = some (decide (i + 1 < (prm s₀).segmentLen)) := by
  have sl := VG.Proof.Argon2.X86.Derive.segLen_lt hp
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.fillBlock_ok hp ht hpass hl hs hi active).mono fun u hu => ?_)
  refine (VG.Proof.Argon2.X86.Derive.advance_ok hp hu.inv (d := indexOff) (n := i) (by decide) hu.pos.index (by omega)
    (B := (prm s₀).segmentLen) (by omega) fun v iv mv => ?_).mono fun v ⟨iv, mv, cv, _⟩ => ⟨hu.next hp iv mv, cv⟩
  rw [show Impl.Argon2.X86.Derive.fr segLenOff = .mem ⟨.ebp, segLenOff⟩ from rfl,
    Wp.readSrc_mem iv.ebp (loc_in' hp iv (d := segLenOff) (by decide))]
  show some (lw s₀ v segLenOff) = _
  rw [(VG.Proof.Argon2.X86.Derive.loc_store hp (d := indexOff) (by decide) mv).1 _ (by decide) (by decide), hu.pr.segLen]

/-- `segment`: a segment of the filling loops. -/
theorem segment_ok {s : State} {pass slice lane : Nat} {st : FillState} (h : VG.Proof.Argon2.X86.Derive.LS s₀ st pass slice lane s)
    (hpass : pass < 2 ^ 32) (hs : slice < 4) (hl : lane < lanesN s₀) :
    WP isa Impl.Argon2.X86.Derive.segment s
      (VG.Proof.Argon2.X86.Derive.LS s₀ (Proof.Argon2.segment (prm s₀) pass lane slice 0 (prm s₀).segmentLen st) pass slice lane) := by
  have s2 := hp.segLen_two
  have sl := VG.Proof.Argon2.X86.Derive.segLen_lt hp
  have hS : Proof.Argon2.segmentStart pass slice ≤ 2 := by unfold Proof.Argon2.segmentStart; split <;> omega
  have hS2 : pass = 0 → slice = 0 → Proof.Argon2.segmentStart pass slice = 2 := fun a b => by
    unfold Proof.Argon2.segmentStart; rw [ite_eq_left ⟨a, b⟩]
  generalize hSd : Proof.Argon2.segmentStart pass slice = S at hS hS2
  rw [Proof.Argon2.segment_start _ _ _ _ _ s2, hSd]
  unfold Impl.Argon2.X86.Derive.segment
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.segmentStart_ok hp h hpass hs).mono fun t₁ h₁ => ?_)
  rw [hSd] at h₁
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.segCmp_ok hp h₁ hS).mono fun t₃ ⟨h₃, c₃⟩ => ?_)
  refine WP.ite (decide (S < (prm s₀).segmentLen)) c₃ (fun hb => ?_) fun hb => ?_
  · have hb' : S < (prm s₀).segmentLen := of_decide_eq_true hb
    refine WP.loop (M := isa) (fun n t => ∃ i, n = (prm s₀).segmentLen - i ∧ S ≤ i ∧ i < (prm s₀).segmentLen ∧
      ∃ c, VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane i c (Proof.Argon2.segment (prm s₀) pass lane slice S (i - S) st) t) ?_
      ((prm s₀).segmentLen - S) t₃ ⟨S, rfl, Nat.le_refl _, hb', 0, by rw [Nat.sub_self]; exact h₃⟩
    rintro n t ⟨i, rfl, hSi, hi, c, ht⟩
    refine (VG.Proof.Argon2.X86.Derive.segStep_ok hp ht hpass hl hs hi (by
        by_cases a : pass = 0
        · by_cases b : slice = 0
          · have := hS2 a b; omega
          · exact .inr (.inl b)
        · exact .inl a)).mono fun v ⟨hv, cv⟩ => ?_
    have eq : Proof.Argon2.segment (prm s₀) pass lane slice S (i + 1 - S) st =
        Spec.Argon2.fillBlock (prm s₀) pass slice lane i (Proof.Argon2.segment (prm s₀) pass lane slice S (i - S) st) := by
      rw [show i + 1 - S = (i - S) + 1 by omega, VG.Proof.Argon2.X86.Derive.segment_snoc, show S + (i - S) = i by omega]
    rw [← eq] at hv
    by_cases e : i + 1 < (prm s₀).segmentLen
    · exact .inr ⟨by rw [show isa.eval .b v = v.cf from rfl, cv]; simp [e], _, by omega, i + 1, rfl, by omega, e, _, hv⟩
    · refine .inl ⟨by rw [show isa.eval .b v = v.cf from rfl, cv]; simp [e], ?_⟩
      rw [show (prm s₀).segmentLen - S = i + 1 - S by omega]
      exact hv.ls
  · have hb' : ¬S < (prm s₀).segmentLen := of_decide_eq_false hb
    refine WP.block_nil ?_
    rw [show (prm s₀).segmentLen - S = 0 by omega, Proof.Argon2.segment_zero]
    exact h₃.ls

end

theorem foldl_range'_snoc {α : Type} (f : α → Nat → α) (start k : Nat) (x : α) :
    (List.range' start (k + 1)).foldl f x = f ((List.range' start k).foldl f x) (start + k) := by
  rw [List.range'_concat, List.foldl_append]
  simp

/-- The body at a slice of the filling loops. -/
structure SS (s₀ : State) (st : FillState) (pass slice : Nat) (s : State) : Prop where
  fb : VG.Proof.Argon2.X86.Derive.FB s₀ st s
  pass : lw s₀ s passOff = BitVec.ofNat 32 pass
  slice : lw s₀ s sliceOff = BitVec.ofNat 32 slice

/-- The body at a pass of the filling loops. -/
structure PS (s₀ : State) (st : FillState) (pass : Nat) (s : State) : Prop where
  fb : VG.Proof.Argon2.X86.Derive.FB s₀ st s
  pass : lw s₀ s passOff = BitVec.ofNat 32 pass

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `setLocal d v`. -/
theorem setLocal_ok {s : State} {st : FillState} (h : VG.Proof.Argon2.X86.Derive.FB s₀ st s) {d : Nat} (hd : d + 4 ≤ 144)
    (hd' : ∀ e ∈ [divisorOff, segLenOff, laneLenOff, strideOff], e + 4 ≤ d ∨ d + 4 ≤ e) (v : BitVec 32) :
    WP isa (.block (Impl.Argon2.X86.Derive.setLocal d v)) s fun t => VG.Proof.Argon2.X86.Derive.FB s₀ st t ∧ lw s₀ t d = v ∧
      ∀ e, e + 4 ≤ 236 → (d + 4 ≤ e ∨ e + 4 ≤ d) → lw s₀ t e = lw s₀ s e := by
  unfold Impl.Argon2.X86.Derive.setLocal
  refine wp_movi fun s₁ u₁ => ?_
  have f₁ := h.of_upd u₁ (by decide) (by decide)
  refine wp_stloc hp f₁.inv (d := d) hd fun t it vt ot _ mt => WP.block_nil
    ⟨f₁.store hp it hd hd' mt, by rw [vt, u₁.gpr], fun e he hde => by rw [ot e he hde, lw_mem u₁.mem]⟩

/-- A lane's segment of a slice, and the lane advanced. -/
theorem laneStep_ok {t : State} {pass slice l : Nat} {X : FillState} (ht : VG.Proof.Argon2.X86.Derive.LS s₀ X pass slice l t)
    (hpass : pass < 2 ^ 32) (hs : slice < 4) (hl : l < lanesN s₀) :
    WP isa (.seq Impl.Argon2.X86.Derive.segment
      (.block (Impl.Argon2.X86.Derive.advance laneOff (Impl.Argon2.X86.Derive.fr (argOff 7))))) t fun v =>
      VG.Proof.Argon2.X86.Derive.LS s₀ (Proof.Argon2.segment (prm s₀) pass l slice 0 (prm s₀).segmentLen X) pass slice (l + 1) v ∧
      v.cf = some (decide (l + 1 < lanesN s₀)) := by
  have hlt := hp.lanes_lt
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.segment_ok hp ht hpass hs hl).mono fun u hu => ?_)
  refine (VG.Proof.Argon2.X86.Derive.advance_ok hp hu.fb.inv (d := laneOff) (n := l) (by decide) hu.lane (by omega) (B := lanesN s₀)
    (by omega) fun v iv _ => ?_).mono fun v ⟨iv, mv, cv, _⟩ => ⟨?_, cv⟩
  · rw [show Impl.Argon2.X86.Derive.fr (argOff 7) = .mem ⟨.ebp, argOff 7⟩ from rfl,
      Wp.readSrc_mem iv.ebp (iv.arg_in hp (by decide)), iv.arg hp (by decide)]
    simp
  obtain ⟨lv, _, _⟩ := VG.Proof.Argon2.X86.Derive.loc_store hp (d := laneOff) (by decide) mv
  refine ⟨hu.fb.store hp iv (d := laneOff) (by decide) (by decide) mv, ?_, ?_, ?_⟩
  · rw [lv _ (by decide) (by decide)]; exact hu.pass
  · rw [lv _ (by decide) (by decide)]; exact hu.slice
  · show v.mem.readW _ 32 = _
    rw [mv, Mem.readW_writeW_self32]

/-- `lanesLoop`: every lane's segment of a slice. -/
theorem lanes_ok {s : State} {pass slice : Nat} {st : FillState} (h : VG.Proof.Argon2.X86.Derive.SS s₀ st pass slice s)
    (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa Impl.Argon2.X86.Derive.lanesLoop s
      (VG.Proof.Argon2.X86.Derive.SS s₀ (Proof.Argon2.lanes (prm s₀) pass slice 0 (lanesN s₀) st) pass slice) := by
  have hl1 := hp.lanes_pos
  unfold Impl.Argon2.X86.Derive.lanesLoop
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.setLocal_ok hp h.fb (d := laneOff) (by decide) (by decide) 0).mono fun t₁ ⟨f₁, v₁, o₁⟩ => ?_)
  refine WP.loop (M := isa) (fun n t => ∃ l, n = lanesN s₀ - l ∧ l < lanesN s₀ ∧
    VG.Proof.Argon2.X86.Derive.LS s₀ (Proof.Argon2.lanes (prm s₀) pass slice 0 l st) pass slice l t) ?_ (lanesN s₀) t₁
    ⟨0, by omega, hl1, f₁, by rw [o₁ _ (by decide) (by decide)]; exact h.pass,
      by rw [o₁ _ (by decide) (by decide)]; exact h.slice, v₁⟩
  rintro n t ⟨l, rfl, hl, ht⟩
  refine (VG.Proof.Argon2.X86.Derive.laneStep_ok hp ht hpass hs hl).mono fun v ⟨hv, cv⟩ => ?_
  rw [show Proof.Argon2.segment (prm s₀) pass l slice 0 (prm s₀).segmentLen
      (Proof.Argon2.lanes (prm s₀) pass slice 0 l st) = Proof.Argon2.lanes (prm s₀) pass slice 0 (l + 1) st from by
    unfold Proof.Argon2.lanes; rw [VG.Proof.Argon2.X86.Derive.foldl_range'_snoc, Nat.zero_add]] at hv
  by_cases e : l + 1 < lanesN s₀
  · exact .inr ⟨by rw [show isa.eval .b v = v.cf from rfl, cv]; simp [e], _, by omega, l + 1, rfl, e, hv⟩
  · refine .inl ⟨by rw [show isa.eval .b v = v.cf from rfl, cv]; simp [e], ?_⟩
    rw [show lanesN s₀ = l + 1 by omega]
    exact ⟨hv.fb, hv.pass, hv.slice⟩

/-- A slice of a pass, and the slice advanced. -/
theorem sliceStep_ok {t : State} {pass j : Nat} {X : FillState} (ht : VG.Proof.Argon2.X86.Derive.SS s₀ X pass j t)
    (hpass : pass < 2 ^ 32) (hj : j < 4) :
    WP isa (.seq Impl.Argon2.X86.Derive.lanesLoop
      (.block (Impl.Argon2.X86.Derive.advance sliceOff (.imm 4)))) t fun v =>
      VG.Proof.Argon2.X86.Derive.SS s₀ (Proof.Argon2.lanes (prm s₀) pass j 0 (lanesN s₀) X) pass (j + 1) v ∧
      v.cf = some (decide (j + 1 < 4)) := by
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.lanes_ok hp ht hpass hj).mono fun u hu => ?_)
  refine (VG.Proof.Argon2.X86.Derive.advance_ok hp hu.fb.inv (d := sliceOff) (n := j) (by decide) hu.slice (by omega) (B := 4)
    (by decide) fun v iv _ => rfl).mono fun v ⟨iv, mv, cv, _⟩ => ⟨?_, cv⟩
  obtain ⟨lv, _, _⟩ := VG.Proof.Argon2.X86.Derive.loc_store hp (d := sliceOff) (by decide) mv
  refine ⟨hu.fb.store hp iv (d := sliceOff) (by decide) (by decide) mv, ?_, ?_⟩
  · rw [lv _ (by decide) (by decide)]; exact hu.pass
  · show v.mem.readW _ 32 = _
    rw [mv, Mem.readW_writeW_self32]

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `slicesLoop`: one pass. -/
theorem slices_ok {s : State} {pass : Nat} {st : FillState} (h : VG.Proof.Argon2.X86.Derive.PS s₀ st pass s) (hpass : pass < 2 ^ 32) :
    WP isa Impl.Argon2.X86.Derive.slicesLoop s (VG.Proof.Argon2.X86.Derive.PS s₀ (Spec.Argon2.fillPass (prm s₀) st pass) pass) := by
  unfold Impl.Argon2.X86.Derive.slicesLoop
  rw [← Proof.Argon2.slices_pass]
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.setLocal_ok hp h.fb (d := sliceOff) (by decide) (by decide) 0).mono fun t₁ ⟨f₁, v₁, o₁⟩ => ?_)
  refine WP.loop (M := isa) (fun n t => ∃ j, n = 4 - j ∧ j < 4 ∧
    VG.Proof.Argon2.X86.Derive.SS s₀ (Proof.Argon2.slices (prm s₀) pass 0 j st) pass j t) ?_ 4 t₁
    ⟨0, rfl, by decide, f₁, by rw [o₁ _ (by decide) (by decide)]; exact h.pass, v₁⟩
  rintro n t ⟨j, rfl, hj, ht⟩
  refine (VG.Proof.Argon2.X86.Derive.sliceStep_ok hp ht hpass hj).mono fun v ⟨hv, cv⟩ => ?_
  rw [show Proof.Argon2.lanes (prm s₀) pass j 0 (lanesN s₀) (Proof.Argon2.slices (prm s₀) pass 0 j st) =
      Proof.Argon2.slices (prm s₀) pass 0 (j + 1) st from by
    unfold Proof.Argon2.slices; rw [VG.Proof.Argon2.X86.Derive.foldl_range'_snoc, Nat.zero_add]; rfl] at hv
  by_cases e : j + 1 < 4
  · exact .inr ⟨by rw [show isa.eval .b v = v.cf from rfl, cv]; simp [e], _, by omega, j + 1, rfl, e, hv⟩
  · refine .inl ⟨by rw [show isa.eval .b v = v.cf from rfl, cv]; simp [e], ?_⟩
    rw [show (4 : Nat) = j + 1 by omega]
    exact ⟨hv.fb, hv.pass⟩

/-- A pass, and the pass advanced. -/
theorem passStep_ok {t : State} {k : Nat} {X : FillState} (ht : VG.Proof.Argon2.X86.Derive.PS s₀ X k t) (hk : k < itersN s₀) :
    WP isa (.seq Impl.Argon2.X86.Derive.slicesLoop
      (.block (Impl.Argon2.X86.Derive.advance passOff (Impl.Argon2.X86.Derive.fr (argOff 5))))) t fun v =>
      VG.Proof.Argon2.X86.Derive.PS s₀ (Spec.Argon2.fillPass (prm s₀) X k) (k + 1) v ∧ v.cf = some (decide (k + 1 < itersN s₀)) := by
  have hpl : itersN s₀ < 2 ^ 32 := (VG.X86.arg s₀ 5).isLt
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.slices_ok hp ht (by omega)).mono fun u hu => ?_)
  refine (VG.Proof.Argon2.X86.Derive.advance_ok hp hu.fb.inv (d := passOff) (n := k) (by decide) hu.pass (by omega) (B := itersN s₀)
    hpl fun v iv _ => ?_).mono fun v ⟨iv, mv, cv, _⟩ => ⟨?_, cv⟩
  · rw [show Impl.Argon2.X86.Derive.fr (argOff 5) = .mem ⟨.ebp, argOff 5⟩ from rfl,
      Wp.readSrc_mem iv.ebp (iv.arg_in hp (by decide)), iv.arg hp (by decide)]
    simp
  refine ⟨hu.fb.store hp iv (d := passOff) (by decide) (by decide) mv, ?_⟩
  show v.mem.readW _ 32 = _
  rw [mv, Mem.readW_writeW_self32]

/-- `passesLoop`: every pass. -/
theorem passes_ok {s : State} {st : FillState} (h : VG.Proof.Argon2.X86.Derive.FB s₀ st s) :
    WP isa Impl.Argon2.X86.Derive.passesLoop s (VG.Proof.Argon2.X86.Derive.FB s₀ (Proof.Argon2.iterations (prm s₀) 0 (itersN s₀) st)) := by
  have hp1 := hp.passes_pos
  unfold Impl.Argon2.X86.Derive.passesLoop
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.setLocal_ok hp h (d := passOff) (by decide) (by decide) 0).mono fun t₁ ⟨f₁, v₁, _⟩ => ?_)
  refine WP.loop (M := isa) (fun n t => ∃ k, n = itersN s₀ - k ∧ k < itersN s₀ ∧
    VG.Proof.Argon2.X86.Derive.PS s₀ (Proof.Argon2.iterations (prm s₀) 0 k st) k t) ?_ (itersN s₀) t₁ ⟨0, by omega, by omega, f₁, v₁⟩
  rintro n t ⟨k, rfl, hk, ht⟩
  refine (VG.Proof.Argon2.X86.Derive.passStep_ok hp ht hk).mono fun v ⟨hv, cv⟩ => ?_
  rw [show Spec.Argon2.fillPass (prm s₀) (Proof.Argon2.iterations (prm s₀) 0 k st) k =
      Proof.Argon2.iterations (prm s₀) 0 (k + 1) st from by
    unfold Proof.Argon2.iterations; rw [VG.Proof.Argon2.X86.Derive.foldl_range'_snoc, Nat.zero_add]] at hv
  by_cases e : k + 1 < itersN s₀
  · exact .inr ⟨by rw [show isa.eval .b v = v.cf from rfl, cv]; simp [e], _, by omega, k + 1, rfl, e, hv⟩
  · refine .inl ⟨by rw [show isa.eval .b v = v.cf from rfl, cv]; simp [e], ?_⟩
    rw [show itersN s₀ = k + 1 by omega]
    exact hv.fb

end
end VG.Proof.Argon2.X86.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.Derive.Correct`. -/
section

section

/-!
# Argon2 on x86 (32-bit): the final block and the tag

`reduce_ok`: the memory's first block becomes the XOR of every lane's last
block (`Proof.Argon2.reduction`), the other blocks kept; `finalOutput_ok`:
H′ of it to `out`, the tag (`Proof.Argon2.finish_reduction`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_sub wp_addm wp_cmpi wp_ldm wp_stm)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState compress xorBlock)
open VG.Spec.Blake2 (bytesAt)
open VG.Proof.Argon2.X86 (blk ofWords blk_of_words xor_words)
open VG.Impl.Sha512.X86 (at_)
open VG.Impl.Argon2.X86.Derive (laneOff laneLenOff argOff divisorOff segLenOff strideOff)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `n` stores of `eax = 0` to `[edi + 4k]`, `edi` the memory matrix. -/
theorem memZeros_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) (hx : s.gpr .edi = memP s₀) (ha : s.gpr .eax = 0) :
    ∀ n ≤ 256, WP isa (.block ((List.range n).map fun k => Instr.store (at_ .edi (4 * k)) .eax)) s fun t =>
      VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ t.gpr = s.gpr ∧ Frame [⟨matrixCell (memB s₀) 0, 1024⟩] s.mem t.mem ∧
      ∀ i < n, VG.Proof.Argon2.X86.Derive.mw s₀ t.mem (4 * i) = 0
  | 0, _ => WP.block_nil ⟨h, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    have b1 := blocks_pos hp
    have hb := VG.Proof.Argon2.X86.Derive.blocks22 hp
    have hm := hp.mem_fits
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append ((VG.Proof.Argon2.X86.Derive.memZeros_ok h hx ha n (by omega)).mono fun t ⟨it, gt, ft, wt⟩ => ?_)
    have ea : addr (t.gpr .edi) (4 * n) = memB s₀ + BitVec.ofNat 64 (4 * n) := by
      rw [gt, hx, VG.Proof.Argon2.X86.Derive.mem_addr' hp (by omega)]
    have hc : (memR s₀).Contains (addr (t.gpr .edi) (4 * n)) 4 := by
      rw [ea]; exact Offset.contains_base _ (by omega) (by omega)
    have hc' : (⟨matrixCell (memB s₀) 0, 1024⟩ : Region).Contains (addr (t.gpr .edi) (4 * n)) 4 := by
      rw [ea, show matrixCell (memB s₀) 0 = memB s₀ by simp [matrixCell]]
      exact Offset.contains_base _ (by omega) (by omega)
    refine Wp.wp_stm rfl ⟨_, by rw [it.wr]; exact mem_mem hp, hc⟩ fun t₁ u₁ => WP.block_nil
      ⟨it.store (R := memR s₀) (by simp) hc u₁, by rw [u₁.gpr, gt], ?_, fun i hi => ?_⟩
    · rw [u₁.mem]
      exact ft.writeW (List.mem_singleton_self _) _ hc'
    · rw [u₁.mem, gt, hx, show 4 * n = 0 + 4 * n by omega, show 4 * i = 0 + 4 * i by omega,
        VG.Proof.Argon2.X86.Derive.mw_store hp _ (by omega) (by omega) (by omega), ha]
      by_cases e : 0 + 4 * n = 0 + 4 * i
      · rw [ite_eq_left e]
      · rw [ite_eq_right e, show 0 + 4 * i = 4 * i by omega]; exact wt i (by omega)

end


theorem reduction_snoc (p : Spec.Argon2.Params) (M : Array Block) (l : Nat) (acc : Block) :
    Proof.Argon2.reduction p M 0 (l + 1) acc =
      xorBlock (Proof.Argon2.reduction p M 0 l acc) (M[Proof.Argon2.lastIndex p l]?.getD zeroBlock) := by
  unfold Proof.Argon2.reduction
  rw [VG.Proof.Argon2.X86.Derive.foldl_range'_snoc, Nat.zero_add]

/-- The state of the reduction after `l` lanes. -/
structure RI (s₀ : State) (M : Array Block) (l : Nat) (s : State) : Prop where
  inv : VG.Proof.Argon2.X86.Derive.Inv s₀ s
  pr : Prm s₀ s
  lane : lw s₀ s laneOff = BitVec.ofNat 32 l
  first : blockAt s.mem (matrixCell (memB s₀) 0) = Proof.Argon2.reduction (prm s₀) M 0 l zeroBlock
  rest : ∀ k < (prm s₀).blocks, k ≠ 0 → blockAt s.mem (matrixCell (memB s₀) k) = M[k]?.getD zeroBlock

theorem cell0 (s₀ : State) : matrixCell (memB s₀) 0 = memB s₀ := by simp [matrixCell]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- One lane of the reduction. -/
theorem reduceLane_ok {s : State} {M : Array Block} {l : Nat} (h : VG.Proof.Argon2.X86.Derive.RI s₀ M l s) (hl : l < lanesN s₀) :
    WP isa (.block (Impl.Argon2.X86.Derive.reduceLane ++
      Impl.Argon2.X86.Derive.advance laneOff (Impl.Argon2.X86.Derive.fr (argOff Impl.Argon2.X86.Derive.lanesArg))))
      s fun t => VG.Proof.Argon2.X86.Derive.RI s₀ M (l + 1) t ∧ t.cf = some (decide (l + 1 < lanesN s₀)) := by
  have L8 := VG.Proof.Argon2.X86.Derive.laneLen_ge hp
  have hlt := hp.lanes_lt
  have hb : blocksN s₀ = (prm s₀).blocks := hp.blocks
  obtain ⟨cl, _⟩ := VG.Proof.Argon2.X86.Derive.cell_fits hp hl (col := (prm s₀).laneLen - 1) (by omega)
  have last : Proof.Argon2.lastIndex (prm s₀) l = l * (prm s₀).laneLen + ((prm s₀).laneLen - 1) := by
    unfold Proof.Argon2.lastIndex; rw [Nat.succ_mul]; omega
  have ne0 : l * (prm s₀).laneLen + ((prm s₀).laneLen - 1) ≠ 0 := by omega
  unfold Impl.Argon2.X86.Derive.reduceLane Impl.Argon2.X86.Derive.writeBlock
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_ldloc hp h.inv (d := laneOff) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.inv.upd u₁ (by decide) (by decide)
  refine wp_ldloc hp i₁ (d := laneLenOff) (by decide) fun s₂ u₂ => wp_subi fun s₃ u₃ _ _ => ?_
  have i₃ := (i₁.upd u₂ (by decide) (by decide)).upd u₃ (by decide) (by decide)
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine VG.Proof.Argon2.X86.Derive.blockAddr_ok hp i₃ (h.pr.of_mem m₃) hl (col := (prm s₀).laneLen - 1) (by omega)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.lane])
    (by rw [u₃.gpr, u₂.gpr, lw_mem u₁.mem, h.pr.laneLen, Wp.ofNat_pred (by omega)]) fun s₄ a₄ _ k₄ => ?_
  have i₄ := i₃.keep k₄
  refine wp_mov fun s₅ u₅ => ?_
  have i₅ := i₄.upd u₅ (by decide) (by decide)
  refine wp_ldarg hp i₅ (i := 13) (by decide) fun s₆ u₆ => ?_
  have i₆ := i₅.upd u₆ (by decide) (by decide)
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, k₄.mem, m₃]
  have hm := hp.mem_fits
  have b22 := VG.Proof.Argon2.X86.Derive.blocks22 hp
  have b1 := blocks_pos hp
  generalize hc : l * (prm s₀).laneLen + ((prm s₀).laneLen - 1) = c at cl a₄ ne0 last
  have hc' : c * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega_using [cl]
  have sx : s₆.gpr .esi = memP s₀ + BitVec.ofNat 32 (c * 1024) := by
    rw [u₆.other _ (by decide), u₅.gpr, a₄]
  have dx : s₆.gpr .edi = memP s₀ + BitVec.ofNat 32 (0 * 1024) := by
    rw [u₆.gpr]; simp
  refine WP.block_append ((VG.Proof.Argon2.X86.Derive.writeWords_ok hp i₆ (cur := 0) b1 true sx
    (by rw [add_nat (by omega_using [hc', hm])]; omega_using [hc', hm])
    ⟨memR s₀, by simp, c * 1024, cell_addr hp cl, hc'⟩
    (by rw [cell_addr hp cl]; exact cell_other hp cl b1 ne0) dx 256 (Nat.le_refl _)).mono
    fun t₇ ⟨i₇, g₇, f₇, w₇⟩ => ?_)
  have lt₇ : ∀ d, d + 4 ≤ 144 → lw s₀ t₇ d = lw s₀ s d := fun d hd => by
    rw [← lw_mem m₆ d]
    exact f₇.readW (r := ⟨addr (VG.Proof.Argon2.X86.Derive.E s₀) d, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (loc_disj hp hd (memR s₀) (by simp)).sub_right (cell_in_mem b1)) (by decide)
  refine (VG.Proof.Argon2.X86.Derive.advance_ok hp i₇ (d := laneOff) (n := l) (by decide) (by rw [lt₇ _ (by decide)]; exact h.lane)
    (by omega) (B := lanesN s₀) (by omega) fun v iv _ => ?_).mono fun t ⟨it, mt, ct, _⟩ => ⟨?_, ct⟩
  · rw [show Impl.Argon2.X86.Derive.fr (argOff Impl.Argon2.X86.Derive.lanesArg) = .mem ⟨.ebp, argOff 7⟩ from rfl,
      Wp.readSrc_mem iv.ebp (iv.arg_in hp (by decide)), iv.arg hp (by decide)]
    simp
  obtain ⟨lt, _, ct⟩ := VG.Proof.Argon2.X86.Derive.loc_store hp (d := laneOff) (by decide) mt
  have new : blockAt t₇.mem (matrixCell (memB s₀) 0) =
      xorBlock (blockAt s.mem (matrixCell (memB s₀) c)) (blockAt s.mem (matrixCell (memB s₀) 0)) := by
    rw [VG.Proof.Argon2.X86.Derive.cell_blk hp _ b1, VG.Proof.Argon2.X86.Derive.cell_blk hp _ b1, VG.Proof.Argon2.X86.Derive.cell_blk hp _ cl,
      blk_of_words (f := fun i => VG.Proof.Argon2.X86.Derive.mw s₀ s.mem (c * 1024 + 4 * i) ^^^ VG.Proof.Argon2.X86.Derive.mw s₀ s.mem (0 * 1024 + 4 * i)) fun i hi => by
        rw [← VG.Proof.Argon2.X86.Derive.mw, w₇ i hi, ite_eq_left hi, ite_eq_left (rfl : true = true), m₆, VG.Proof.Argon2.X86.Derive.addr_shift],
      blk_of_words (m := s.mem) (B := memP s₀) (o := c * 1024) (f := fun i => VG.Proof.Argon2.X86.Derive.mw s₀ s.mem (c * 1024 + 4 * i))
        fun _ _ => rfl,
      blk_of_words (m := s.mem) (B := memP s₀) (o := 0 * 1024) (f := fun i => VG.Proof.Argon2.X86.Derive.mw s₀ s.mem (0 * 1024 + 4 * i))
        fun _ _ => rfl, xor_words]
  refine ⟨it, Prm.of_lw h.pr fun d hd => ?_, ?_, ?_, fun k hk k0 => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    have hd4 : d + 4 ≤ 144 := by rcases hd with rfl | rfl | rfl | rfl <;> decide
    rw [lt d (by omega) (by rcases hd with rfl | rfl | rfl | rfl <;> decide), lt₇ d hd4]
  · show t.mem.readW _ 32 = _
    rw [mt, Mem.readW_writeW_self32]
  · rw [ct _ (by rw [← hb]; exact b1), new, h.first, h.rest _ (by rw [← hb]; exact cl) ne0, VG.Proof.Argon2.X86.Derive.reduction_snoc,
      Proof.Argon2.xorBlock_comm, last]
  · rw [ct _ hk, blockAt_keep f₇ (fun r hr => ?_), m₆, h.rest k hk k0]
    simp only [List.mem_singleton] at hr; subst hr
    exact cell_other hp (by rw [hb]; exact hk) b1 k0

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The first block of `reduce`: the memory's first block cleared, and the lane `0`. -/
theorem reduceStart_ok {s : State} {M : Array Block} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) (pr : Prm s₀ s)
    (hm : Represents s.mem (memB s₀) (prm s₀).blocks M) :
    WP isa (.block (Impl.Argon2.X86.Derive.reduceClear ++ Impl.Argon2.X86.Derive.setLocal laneOff 0)) s
      (VG.Proof.Argon2.X86.Derive.RI s₀ M 0) := by
  have b1 := blocks_pos hp
  have hb : blocksN s₀ = (prm s₀).blocks := hp.blocks
  unfold Impl.Argon2.X86.Derive.reduceClear Impl.Argon2.X86.Derive.setLocal
  simp only [List.cons_append, List.nil_append]
  refine wp_ldarg hp h (i := 13) (by decide) fun s₁ u₁ => wp_movi fun s₂ u₂ => ?_
  have i₂ := (h.upd u₁ (by decide) (by decide)).upd u₂ (by decide) (by decide)
  refine WP.block_append ((VG.Proof.Argon2.X86.Derive.memZeros_ok hp i₂ (by rw [u₂.other _ (by decide), u₁.gpr]) u₂.gpr 256
    (Nat.le_refl _)).mono fun s₃ ⟨i₃, _, f₃, z₃⟩ => ?_)
  refine wp_movi fun s₄ u₄ => ?_
  have i₄ := i₃.upd u₄ (by decide) (by decide)
  refine wp_stloc hp i₄ (d := laneOff) (by decide) fun s₅ i₅ v₅ _ _ m₅ => WP.block_nil ?_
  obtain ⟨l₅, _, c₅⟩ := VG.Proof.Argon2.X86.Derive.loc_store hp (d := laneOff) (by decide) m₅
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have lt₃ : ∀ d, d + 4 ≤ 144 → lw s₀ s₃ d = lw s₀ s d := fun d hd => by
    rw [← lw_mem m₂ d]
    exact f₃.readW (r := ⟨addr (VG.Proof.Argon2.X86.Derive.E s₀) d, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (loc_disj hp hd (memR s₀) (by simp)).sub_right (cell_in_mem b1)) (by decide)
  refine ⟨i₅, Prm.of_lw pr fun d hd => ?_, by rw [v₅, u₄.gpr]; rfl, ?_, fun k hk k0 => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    have hd4 : d + 4 ≤ 144 := by rcases hd with rfl | rfl | rfl | rfl <;> decide
    rw [l₅ d (by omega) (by rcases hd with rfl | rfl | rfl | rfl <;> decide), lw_mem u₄.mem, lt₃ d hd4]
  · rw [c₅ _ (by rw [← hb]; exact b1), u₄.mem, VG.Proof.Argon2.X86.Derive.cell_blk hp _ b1,
      blk_of_words (f := fun _ => 0) fun i hi => by rw [← VG.Proof.Argon2.X86.Derive.mw, Nat.zero_mul, Nat.zero_add]; exact z₃ i hi,
      VG.Proof.Argon2.X86.Derive.ofWords_zero]
    rfl
  · rw [c₅ _ hk, u₄.mem, blockAt_keep f₃ (fun r hr => ?_), m₂, hm.block k hk]
    simp only [List.mem_singleton] at hr; subst hr
    exact cell_other hp (by rw [hb]; exact hk) b1 k0

/-- `reduce`: the XOR of every lane's last block, to the memory's first block. -/
theorem reduce_ok {s : State} {M : Array Block} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) (pr : Prm s₀ s)
    (hm : Represents s.mem (memB s₀) (prm s₀).blocks M) :
    WP isa Impl.Argon2.X86.Derive.reduce s fun t => VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ Prm s₀ t ∧
      blockAt t.mem (matrixCell (memB s₀) 0) = Proof.Argon2.reduction (prm s₀) M 0 (lanesN s₀) zeroBlock := by
  have hl1 := hp.lanes_pos
  unfold Impl.Argon2.X86.Derive.reduce
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.reduceStart_ok hp h pr hm).mono fun s₅ start => ?_)
  refine WP.loop (M := isa) (fun n t => ∃ l, n = lanesN s₀ - l ∧ l < lanesN s₀ ∧ VG.Proof.Argon2.X86.Derive.RI s₀ M l t) ?_ (lanesN s₀) s₅
    ⟨0, by omega, hl1, start⟩
  rintro n t ⟨l, rfl, hl, ht⟩
  refine (VG.Proof.Argon2.X86.Derive.reduceLane_ok hp ht hl).mono fun u ⟨hu, cu⟩ => ?_
  by_cases e : l + 1 < lanesN s₀
  · exact .inr ⟨by rw [show isa.eval .b u = u.cf from rfl, cu]; simp [e], _, by omega, l + 1, rfl, e, hu⟩
  · refine .inl ⟨by rw [show isa.eval .b u = u.cf from rfl, cu]; simp [e], hu.inv, hu.pr, ?_⟩
    rw [hu.first, show l + 1 = lanesN s₀ by omega]

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `finalOutput`: H′ of the memory's first block, to `out`. -/
theorem finalOutput_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) :
    WP isa Impl.Argon2.X86.Derive.finalOutput s fun t => VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧
      bytesAt t.mem ((outP s₀).setWidth 64) (outL s₀) =
        Spec.Argon2.hPrime (outL s₀) (Spec.Argon2.serialize (blockAt s.mem (matrixCell (memB s₀) 0))) := by
  have b1 := blocks_pos hp
  have hm := hp.mem_fits
  have ho := hp.out_fits
  have tg := hp.tag_ge
  unfold Impl.Argon2.X86.Derive.finalOutput
  refine WP.seq (wp_ldarg hp h (i := 13) (by decide) fun s₁ u₁ => ?_)
  have i₁ := h.upd u₁ (by decide) (by decide)
  refine wp_movi fun s₂ u₂ => ?_
  have i₂ := i₁.upd u₂ (by decide) (by decide)
  refine wp_ldarg hp i₂ (i := 16) (by decide) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃ (by decide) (by decide)
  refine wp_ldarg hp i₃ (i := 17) (by decide) fun s₄ u₄ => ?_
  have i₄ := i₃.upd u₄ (by decide) (by decide)
  refine wp_ldarg hp i₄ (i := 15) (by decide) fun s₅ u₅ => WP.block_nil ?_
  have i₅ := i₄.upd u₅ (by decide) (by decide)
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have si : s₅.gpr .esi = memP s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  have ax : (s₅.gpr .eax).toNat = 1024 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]; rfl
  have di : s₅.gpr .edi = outP s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  have cx : (s₅.gpr .ecx).toNat = outL s₀ := by
    rw [u₅.other _ (by decide), u₄.gpr]
  refine hcall_ok hp i₅ (r := .esi) (by decide) u₅.gpr
    ⟨memR s₀, by simp, 0, by rw [si]; simp, by rw [ax]; show 0 + 1024 ≤ blocksN s₀ * 1024; omega⟩
    (by rw [si, ax]; omega) ⟨VG.Proof.Argon2.X86.Derive.outR s₀, by simp, 0, by rw [di]; simp, by rw [cx]; show 0 + outL s₀ ≤ outL s₀; omega⟩
    (by rw [di, cx]; exact ho) (by rw [cx]; omega) fun t it _ _ post => ⟨it, ?_⟩
  rw [← di, ← cx, post, cx, ax, si, m₅, VG.Proof.Argon2.X86.Derive.cell0, Proof.Argon2.serialize_blockAt]

end
end VG.Proof.Argon2.X86.Derive

end

/-!
# Argon2 on x86 (32-bit): the derivation is correct

`body_ok`: the body computes the parameters and H₀, initializes and fills
the memory, and writes the tag (`Spec.Argon2.derive`) to `out`; `correct`:
the whole function, in its frames, keeps the ABI's registers too.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState)
open VG.Spec.Blake2 (bytesAt)

theorem body_nosp : NoSp Impl.Argon2.X86.Derive.body := NoSp.of_all (by lit_decide)

theorem body_stack : stackUse Impl.Argon2.X86.Derive.body = 84 := by lit_decide

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem body_ok : WP isa Impl.Argon2.X86.Derive.body (entry s₀) fun t => BodyDone s₀ t ∧
    bytesAt t.mem ((outP s₀).setWidth 64) (outL s₀) =
      Spec.Argon2.derive (prm s₀) (pwB s₀) (saltB s₀) (secB s₀) (adB s₀) := by
  unfold Impl.Argon2.X86.Derive.body
  refine WP.seq ?_
  rw [← List.append_nil (Instr.mov .ebp (.reg .esp) :: Impl.Argon2.X86.Derive.parameters)]
  refine parameters_ok hp fun s₁ i₁ p₁ => WP.block_nil ?_
  refine WP.seq ((code_ok hp i₁ p₁).mono fun s₂ ⟨i₂, p₂, b₂⟩ => ?_)
  refine WP.seq ((memoryInit_ok hp i₂ p₂ b₂).mono fun s₃ ⟨i₃, p₃, m₃⟩ => ?_)
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.passes_ok hp (st := Spec.Argon2.initMemory (prm s₀)
    (Spec.Argon2.initialHash (prm s₀) (pwB s₀) (saltB s₀) (secB s₀) (adB s₀))) ⟨i₃, p₃, m₃⟩).mono
    fun s₄ f₄ => ?_)
  rw [show itersN s₀ = (prm s₀).passes from rfl, Proof.Argon2.iterations_fill] at f₄
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.reduce_ok hp f₄.inv f₄.pr f₄.mem).mono fun s₅ ⟨i₅, _, b₅⟩ => ?_)
  refine (VG.Proof.Argon2.X86.Derive.finalOutput_ok hp i₅).mono fun t ⟨it, ot⟩ => ⟨it.done hp, ?_⟩
  rw [ot, b₅, Spec.Argon2.derive, Proof.Argon2.finish_reduction]
  rfl

theorem correct : WP isa Impl.Argon2.X86.Derive.derive s₀ fun t => abiPreserved s₀ t ∧ deriveX86.post s₀ t :=
  frames_ok (by have := hp.esp_lo; omega) VG.Proof.Argon2.X86.Derive.body_nosp (VG.Proof.Argon2.X86.Derive.body_ok hp) fun t u q m => by
    show bytesAt u.mem _ _ = _
    rw [m]; exact q

end

end VG.Proof.Argon2.X86.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.Derive.CTBase`. -/
section

/-!
# Argon2 on x86 (32-bit): the derivation's taint analysis

The body reads its arguments through `ebp`, which the taint analysis only
knows to be public through `esp`. So its pieces are analysed from states
with more permissions (`RelCT.taintW`, by `Exec.widen`): the locals and the
saved registers as one writable region, the memory matrix, `scratch`, the
output, and the arguments (`wide`). `τB sl` makes `esp` and `ebp`, the
arguments and the locals' slots `sl` public, and knows which arguments are
the base addresses of the matrix, `scratch` and the output; `agreeB` gives it
from what two runs of the body are known to share.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.Spec.Blake2 (bytesAt)

/-- Two runs leak the same trace if, from states with more permissions, the
taint analysis proves it. -/
theorem RelCT.taintW {P : State → State → Prop} {c : Prog isa} (τ : VG.X86.Taint.T)
    (hp : ∀ s₁ s₂, P s₁ s₂ → ∃ w₁ w₂, Covers s₁.wr w₁ ∧ Covers s₂.wr w₂ ∧
      VG.X86.Taint.Agree τ (s₁.withRegions s₁.rd w₁) (s₂.withRegions s₂.rd w₂))
    {hc : VG.Taint.Hint VG.X86.Taint.T} (h : (VG.Taint.check taint τ c hc).isSome = true) :
    RelCT isa P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  obtain ⟨w₁, w₂, c₁, c₂, ag⟩ := hp _ _ hP
  have e₁' := Exec.widen e₁ (Covers.append (Covers.refl _) c₁) c₁
  have e₂' := Exec.widen e₂ (Covers.append (Covers.refl _) c₂) c₂
  exact ⟨((VG.RelCT.taint (A := taint) (P := fun a b => a = s₁.withRegions s₁.rd w₁ ∧
    b = s₂.withRegions s₂.rd w₂) τ (fun _ _ ⟨h₁, h₂⟩ => by subst h₁ h₂; exact ag) h) _ _ _ _ _ _
    ⟨rfl, rfl⟩ e₁' e₂').1, trivial⟩

/-- As `RelCT.taintW`, with what each run satisfies by correctness. -/
theorem rel_taintW {F₁ F₂ G₁ G₂ : State → Prop} {R : State → State → Prop} {c : Prog isa} (τ : VG.X86.Taint.T)
    (hp : ∀ s₁ s₂, F₁ s₁ → F₂ s₂ → R s₁ s₂ → ∃ w₁ w₂, Covers s₁.wr w₁ ∧ Covers s₂.wr w₂ ∧
      VG.X86.Taint.Agree τ (s₁.withRegions s₁.rd w₁) (s₂.withRegions s₂.rd w₂))
    (hc : ∃ hc, (VG.Taint.check taint τ c hc).isSome = true)
    (hw₁ : ∀ s, F₁ s → WP isa c s G₁) (hw₂ : ∀ s, F₂ s → WP isa c s G₂) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂ ∧ R s₁ s₂) c fun t₁ t₂ => G₁ t₁ ∧ G₂ t₂ := by
  obtain ⟨_, hc⟩ := hc
  exact ((RelCT.taintW (P := fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂ ∧ R s₁ s₂) τ
    (fun s₁ s₂ h => hp s₁ s₂ h.1 h.2.1 h.2.2) hc).wp fun s₁ s₂ h => ⟨hw₁ s₁ h.1, hw₂ s₂ h.2.1⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-! ## The regions -/

/-- The regions the taint analysis of the body knows: the locals and saved
registers, the memory matrix, `scratch`, the output and the arguments. -/
def wide (s₀ : State) : List Region :=
  [⟨(VG.Proof.Argon2.X86.Derive.E s₀).setWidth 64, 160⟩, memR s₀, VG.Proof.Argon2.X86.Derive.scrR s₀, VG.Proof.Argon2.X86.Derive.outR s₀, VG.Proof.Argon2.X86.Derive.argR s₀]

/-- The taint state of the body, with the locals' slots `sl` and the registers
`rs` public. -/
def τB (sl : List (Nat × Nat × Nat)) (rs : List Reg := []) : VG.X86.Taint.T :=
  { regs := .ofList (.esp :: .ebp :: rs), flags := false, lens := [160, 1024, 16384, 0, 72],
    bases := [(.ebp, 4, 164), (.ebp, 0, 0), (.esp, 4, 164), (.esp, 0, 0)], slots := sl ++ [(4, 0, 72)],
    wbases := [(4, 52, 1), (4, 60, 2), (4, 64, 3)] }


section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The writable regions of the body: frames within the 160 bytes above `E`, and the caller's. -/
theorem entry_wr_cases {r : Region} (hr : r ∈ (entry s₀).wr) : r ∈ s₀.wr ∨
    ∃ x : BitVec 32, ∃ n, r = ⟨x.setWidth 64, n⟩ ∧ (VG.Proof.Argon2.X86.Derive.E s₀).toNat ≤ x.toNat ∧ x.toNat + n ≤ (VG.Proof.Argon2.X86.Derive.E s₀).toNat + 160 := by
  have hlo : 244 ≤ (s₀.gpr .esp).toNat := hp.esp_lo
  have hE0 : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have hE := E_nat hp
  have n₁ := pushed_esp_nat (rs := [.ebp]) (s := s₀) (by simp only [List.length_singleton]; omega)
  have n₂ := pushed_esp_nat (rs := [.edi]) (s := pushed [.ebp] s₀)
    (by simp only [List.length_singleton] at n₁ ⊢; omega)
  have n₃ := pushed_esp_nat (rs := [.esi]) (s := pushed [.edi] (pushed [.ebp] s₀))
    (by simp only [List.length_singleton] at n₁ n₂ ⊢; omega)
  have n₄ := pushed_esp_nat (rs := [.ebx]) (s := pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀)))
    (by simp only [List.length_singleton] at n₁ n₂ n₃ ⊢; omega)
  simp only [List.length_singleton, Nat.mul_one] at n₁ n₂ n₃ n₄
  have w : ∀ (x : BitVec 32) (n : Nat), n ≤ x.toNat → (VG.Proof.Argon2.X86.Derive.E s₀).toNat ≤ x.toNat - n → x.toNat ≤ (VG.Proof.Argon2.X86.Derive.E s₀).toNat + 160 →
      (VG.Proof.Argon2.X86.Derive.E s₀).toNat ≤ (x - BitVec.ofNat 32 n).toNat ∧ (x - BitVec.ofNat 32 n).toNat + n ≤ (VG.Proof.Argon2.X86.Derive.E s₀).toNat + 160 :=
    fun x n h₁ h₂ h₃ => by rw [sub_nat h₁]; omega
  simp only [entry, pushed_wr, List.mem_cons, List.length_singleton, List.length_replicate, Nat.mul_one,
    Nat.reduceMul] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | hr
  · exact .inr ⟨_, _, rfl, w _ _ (by omega) (by omega) (by omega)⟩
  · exact .inr ⟨_, _, rfl, w _ _ (by omega) (by omega) (by omega)⟩
  · exact .inr ⟨_, _, rfl, w _ _ (by omega) (by omega) (by omega)⟩
  · exact .inr ⟨_, _, rfl, w _ _ (by omega) (by omega) (by omega)⟩
  · exact .inr ⟨_, _, rfl, w _ _ (by omega) (by omega) (by omega)⟩
  · exact .inl hr

theorem covers_wide : Covers (entry s₀).wr (VG.Proof.Argon2.X86.Derive.wide s₀) := by
  have hE := E_hi hp
  refine Covers.of_sub fun r hr => ?_
  rcases VG.Proof.Argon2.X86.Derive.entry_wr_cases hp hr with hr | ⟨x, n, rfl, h₁, h₂⟩
  · rw [hp.wr] at hr
    exact ⟨r, by simp only [VG.Proof.Argon2.X86.Derive.wide, List.mem_cons] at hr ⊢; simp at hr; rcases hr with h | h | h <;> simp [h],
      0, by simp, by simp⟩
  · refine ⟨⟨(VG.Proof.Argon2.X86.Derive.E s₀).setWidth 64, 160⟩, by simp [VG.Proof.Argon2.X86.Derive.wide], x.toNat - (VG.Proof.Argon2.X86.Derive.E s₀).toNat, ?_, by simp only; omega⟩
    show x.setWidth 64 = (VG.Proof.Argon2.X86.Derive.E s₀).setWidth 64 + BitVec.ofNat 64 (x.toNat - (VG.Proof.Argon2.X86.Derive.E s₀).toNat)
    rw [← HPrime.setWidth_add (by omega)]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [add_nat (by omega)]; omega

end

/-- What two runs share: the stack pointer and the arguments. -/
def Pub2 (s₀₁ s₀₂ : State) : Prop := E0 s₀₁ = E0 s₀₂ ∧ ∀ i < 18, VG.X86.arg s₀₁ i = VG.X86.arg s₀₂ i

theorem Pub2.E {s₀₁ s₀₂ : State} (h : VG.Proof.Argon2.X86.Derive.Pub2 s₀₁ s₀₂) : VG.Proof.Argon2.X86.Derive.E s₀₁ = VG.Proof.Argon2.X86.Derive.E s₀₂ := by
  show E0 s₀₁ - BitVec.ofNat 32 160 = E0 s₀₂ - BitVec.ofNat 32 160
  rw [h.1]

theorem Pub2.wide_eq {s₀₁ s₀₂ : State} (h : VG.Proof.Argon2.X86.Derive.Pub2 s₀₁ s₀₂) : VG.Proof.Argon2.X86.Derive.wide s₀₁ = VG.Proof.Argon2.X86.Derive.wide s₀₂ := by
  have e : s₀₁.gpr .esp = s₀₂.gpr .esp := h.1
  unfold VG.Proof.Argon2.X86.Derive.wide
  rw [h.E, show memR s₀₁ = memR s₀₂ by simp only [memR, memP, blocksN, h.2 13 (by decide), h.2 14 (by decide)],
    show VG.Proof.Argon2.X86.Derive.scrR s₀₁ = VG.Proof.Argon2.X86.Derive.scrR s₀₂ by simp only [VG.Proof.Argon2.X86.Derive.scrR, scrP, h.2 15 (by decide)],
    show VG.Proof.Argon2.X86.Derive.outR s₀₁ = VG.Proof.Argon2.X86.Derive.outR s₀₂ by simp only [VG.Proof.Argon2.X86.Derive.outR, outP, outL, h.2 16 (by decide), h.2 17 (by decide)],
    show VG.Proof.Argon2.X86.Derive.argR s₀₁ = VG.Proof.Argon2.X86.Derive.argR s₀₂ by simp only [VG.Proof.Argon2.X86.Derive.argR, argAddr, e]]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- Word `i` of the arguments, in the widened regions' terms. -/
theorem arg_byteAddr {i : Nat} (hi : i < 18) :
    argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) = argAddr s₀ i := by
  have := hp.esp_hi
  have := hp.esp_lo
  have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  simp only [argAddr]
  rw [← HPrime.setWidth_add (by rw [add_nat (by omega)]; omega), BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem wf_wide (sl : List (Nat × Nat × Nat)) (rs : List Reg) {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) :
    VG.X86.Taint.Wf (VG.Proof.Argon2.X86.Derive.τB sl rs) (s.withRegions s.rd (VG.Proof.Argon2.X86.Derive.wide s₀)) := by
  have hlo := hp.esp_lo
  have hhi := hp.esp_hi
  have hE := E_nat hp
  have hE0 : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have b1 := blocks_pos hp
  have hm := hp.mem_fits
  have hs := hp.scr_fits
  have ho := hp.out_fits
  have aR : (VG.Proof.Argon2.X86.Derive.argR s₀) = ⟨(E0 s₀ + BitVec.ofNat 32 4).setWidth 64, 72⟩ := rfl
  have a4 : (E0 s₀ + BitVec.ofNat 32 4).toNat = (E0 s₀).toNat + 4 := add_nat (by omega)
  have locS : Region.Sub ⟨(VG.Proof.Argon2.X86.Derive.E s₀).setWidth 64, 160⟩ (VG.Proof.Argon2.X86.Derive.stkR s₀) := by
    simpa using frame_stk hp (d := 0) (n := 160) (by decide)
  refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hp' => ?_, fun p hp' => ?_, fun h0 => absurd h0 (Nat.lt_irrefl 0),
    fun _ h' => (List.not_mem_nil h').elim, by simp; exact (s.gpr .esp).isLt,
    fun _ h' => by simp [VG.Proof.Argon2.X86.Derive.τB, VG.X86.Taint.frameList] at h', fun h0 => absurd h0 (Nat.lt_irrefl 0)⟩
  · simp only [State.withRegions_wr, VG.Proof.Argon2.X86.Derive.wide, VG.Proof.Argon2.X86.Derive.τB]
    refine .cons (by simp) (.cons ?_ (.cons (by simp) (.cons (by simp) (.cons (by simp) .nil))))
    show 1024 ≤ blocksN s₀ * 1024; omega
  · simp only [State.withRegions_wr, VG.Proof.Argon2.X86.Derive.wide]
    have d1 := (hp.stk_all (memR s₀) (by simp)).sub_left locS
    have d2 := (hp.stk_all (VG.Proof.Argon2.X86.Derive.scrR s₀) (by simp)).sub_left locS
    have d3 := (hp.stk_all (VG.Proof.Argon2.X86.Derive.outR s₀) (by simp)).sub_left locS
    have d4 : Region.Disjoint ⟨(VG.Proof.Argon2.X86.Derive.E s₀).setWidth 64, 160⟩ (VG.Proof.Argon2.X86.Derive.argR s₀) := by
      rw [aR]; exact disj32 (.inl (by rw [a4]; omega)) (by omega) (by rw [a4]; omega)
    have r1 := hp.ro_w (VG.Proof.Argon2.X86.Derive.argR s₀) (by simp) (memR s₀) (by simp)
    have r2 := hp.ro_w (VG.Proof.Argon2.X86.Derive.argR s₀) (by simp) (VG.Proof.Argon2.X86.Derive.scrR s₀) (by simp)
    have r3 := hp.ro_w (VG.Proof.Argon2.X86.Derive.argR s₀) (by simp) (VG.Proof.Argon2.X86.Derive.outR s₀) (by simp)
    refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons (fun _ h => (List.not_mem_nil h).elim) .nil))))
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [d1, d2, d3, d4]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hp.mem_scr, hp.mem_out, r1.symm]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [hp.scr_out, r2.symm]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact r3.symm
  · simp only [State.withRegions_wr, VG.Proof.Argon2.X86.Derive.wide, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl) <;> simp only [toNat_w]
    · omega
    · exact hm
    · exact hs
    · exact ho
    · show ((E0 s₀ + BitVec.ofNat 32 4).setWidth 64).toNat + 72 ≤ 2 ^ 32
      rw [toNat_w, a4]; omega
  · simp only [VG.Proof.Argon2.X86.Derive.τB, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl
    · show addr (s.gpr .ebp) 164 = argAddr s₀ 0
      rw [h.ebp]; exact arg_addr hp (i := 0) (by decide)
    · show addr (s.gpr .ebp) 0 = (VG.Proof.Argon2.X86.Derive.E s₀).setWidth 64
      rw [h.ebp]; simp [addr]
    · show addr (s.gpr .esp) 164 = argAddr s₀ 0
      rw [h.esp]; exact arg_addr hp (i := 0) (by decide)
    · show addr (s.gpr .esp) 0 = (VG.Proof.Argon2.X86.Derive.E s₀).setWidth 64
      rw [h.esp]; simp [addr]
  · simp only [VG.Proof.Argon2.X86.Derive.τB, List.mem_cons, List.not_mem_nil, or_false] at hp'
    have wb : ∀ i, i < 18 → (s.withRegions s.rd (VG.Proof.Argon2.X86.Derive.wide s₀)).mem.readW
        (VG.X86.Taint.byteAddr (s.withRegions s.rd (VG.Proof.Argon2.X86.Derive.wide s₀)) 4 (4 * i)) 32 = VG.X86.arg s₀ i := fun i hi => by
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, State.withRegions_wr, State.withRegions_mem, VG.Proof.Argon2.X86.Derive.wide,
        List.getD_cons_succ, List.getD_cons_zero, VG.Proof.Argon2.X86.Derive.argR]
      rw [VG.Proof.Argon2.X86.Derive.arg_byteAddr hp hi, ← arg_addr hp hi]
      exact h.arg hp hi
    rcases hp' with rfl | rfl | rfl
    · refine ⟨by show 52 + 4 ≤ 72; decide, ?_⟩
      show addr ((s.withRegions s.rd (VG.Proof.Argon2.X86.Derive.wide s₀)).mem.readW
        (VG.X86.Taint.byteAddr (s.withRegions s.rd (VG.Proof.Argon2.X86.Derive.wide s₀)) 4 (4 * 13)) 32) 0 = (memP s₀).setWidth 64
      rw [wb 13 (by decide)]; simp [addr]
    · refine ⟨by show 60 + 4 ≤ 72; decide, ?_⟩
      show addr ((s.withRegions s.rd (VG.Proof.Argon2.X86.Derive.wide s₀)).mem.readW
        (VG.X86.Taint.byteAddr (s.withRegions s.rd (VG.Proof.Argon2.X86.Derive.wide s₀)) 4 (4 * 15)) 32) 0 = (scrP s₀).setWidth 64
      rw [wb 15 (by decide)]; simp [addr]
    · refine ⟨by show 64 + 4 ≤ 72; decide, ?_⟩
      show addr ((s.withRegions s.rd (VG.Proof.Argon2.X86.Derive.wide s₀)).mem.readW
        (VG.X86.Taint.byteAddr (s.withRegions s.rd (VG.Proof.Argon2.X86.Derive.wide s₀)) 4 (4 * 16)) 32) 0 = (outP s₀).setWidth 64
      rw [wb 16 (by decide)]; simp [addr]

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- A byte of the locals, from its word. -/
theorem loc_byte (m : Mem) {k : Nat} (hk : k < 160) :
    m ((VG.Proof.Argon2.X86.Derive.E s₀).setWidth 64 + BitVec.ofNat 64 k) =
      (m.readW (addr (VG.Proof.Argon2.X86.Derive.E s₀) (4 * (k / 4))) 32).extractLsb' (8 * (k % 4)) 8 := by
  have := E_hi hp
  rw [addr_eq (by omega), ← Mem.readW_byte m _ (Nat.mod_lt _ (by decide)), BitVec.add_assoc,
    BitVec.ofNat_add_ofNat, Nat.div_add_mod]

/-- A byte of the arguments, from its word. -/
theorem arg_byte {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) {k : Nat} (hk : k < 72) :
    s.mem (argAddr s₀ 0 + BitVec.ofNat 64 k) = (VG.X86.arg s₀ (k / 4)).extractLsb' (8 * (k % 4)) 8 := by
  rw [show argAddr s₀ 0 + BitVec.ofNat 64 k = argAddr s₀ 0 + BitVec.ofNat 64 (4 * (k / 4)) +
      BitVec.ofNat 64 (k % 4) by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.div_add_mod],
    Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), VG.Proof.Argon2.X86.Derive.arg_byteAddr hp (by omega), ← arg_addr hp (by omega),
    h.arg hp (by omega)]

end

/-- The taint analysis's knowledge of the body, from what two runs share and
the values of the locals' slots `sl` in both. -/
theorem agreeB {s₀₁ s₀₂ s₁ s₂ : State} (hp₁ : DPre s₀₁) (hp₂ : DPre s₀₂) (pb : VG.Proof.Argon2.X86.Derive.Pub2 s₀₁ s₀₂)
    (h₁ : VG.Proof.Argon2.X86.Derive.Inv s₀₁ s₁) (h₂ : VG.Proof.Argon2.X86.Derive.Inv s₀₂ s₂) (sl : List (Nat × Nat × Nat)) (rs : List Reg)
    (hrs : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hok : VG.X86.Taint.SlotsOk (VG.Proof.Argon2.X86.Derive.τB sl rs))
    (hsl : ∀ x ∈ sl, x.1 = 0 ∧ ∀ k, x.2.1 ≤ k → k < x.2.1 + x.2.2 →
      lw s₀₁ s₁ (4 * (k / 4)) = lw s₀₂ s₂ (4 * (k / 4))) :
    ∃ w₁ w₂, Covers s₁.wr w₁ ∧ Covers s₂.wr w₂ ∧
      VG.X86.Taint.Agree (VG.Proof.Argon2.X86.Derive.τB sl rs) (s₁.withRegions s₁.rd w₁) (s₂.withRegions s₂.rd w₂) := by
  refine ⟨VG.Proof.Argon2.X86.Derive.wide s₀₁, VG.Proof.Argon2.X86.Derive.wide s₀₂, by rw [h₁.wr]; exact VG.Proof.Argon2.X86.Derive.covers_wide hp₁, by rw [h₂.wr]; exact VG.Proof.Argon2.X86.Derive.covers_wide hp₂,
    ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => pb.wide_eq, VG.Proof.Argon2.X86.Derive.wf_wide hp₁ sl rs h₁, VG.Proof.Argon2.X86.Derive.wf_wide hp₂ sl rs h₂, hok,
      fun x hx k hk₁ hk₂ => ?_, fun h0 => absurd h0 (Nat.lt_irrefl 0),
      fun _ _ h0 => absurd h0 (Nat.not_lt_zero _)⟩⟩
  · simp only [VG.Proof.Argon2.X86.Derive.τB, RegSet.mem_ofList, List.mem_cons] at hr
    rcases hr with rfl | rfl | hr
    · rw [State.withRegions_gpr, State.withRegions_gpr, h₁.esp, h₂.esp, pb.E]
    · rw [State.withRegions_gpr, State.withRegions_gpr, h₁.ebp, h₂.ebp, pb.E]
    · rw [State.withRegions_gpr, State.withRegions_gpr]; exact hrs r hr
  · simp only [VG.Proof.Argon2.X86.Derive.τB, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · obtain ⟨x0, hk⟩ := hsl x hx
      have hlen := hok x (by simp [VG.Proof.Argon2.X86.Derive.τB, hx])
      rw [x0] at hlen
      simp only [VG.Proof.Argon2.X86.Derive.τB, List.getD_cons_zero] at hlen
      have k160 : k < 160 := by omega
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, State.withRegions_wr, State.withRegions_mem, x0,
        VG.Proof.Argon2.X86.Derive.wide, List.getD_cons_zero]
      rw [VG.Proof.Argon2.X86.Derive.loc_byte hp₁ s₁.mem k160, VG.Proof.Argon2.X86.Derive.loc_byte hp₂ s₂.mem k160]
      exact congrArg _ (hk k hk₁ hk₂)
    · simp only at hk₁ hk₂
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, State.withRegions_wr, State.withRegions_mem,
        VG.Proof.Argon2.X86.Derive.wide, List.getD_cons_succ, List.getD_cons_zero]
      rw [VG.Proof.Argon2.X86.Derive.arg_byte hp₁ h₁ (by omega), VG.Proof.Argon2.X86.Derive.arg_byte hp₂ h₂ (by omega), pb.2 _ (by omega)]
end VG.Proof.Argon2.X86.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.Derive.FillCT1`. -/
section

section

/-!
# Argon2 on x86 (32-bit): two runs of the body

`Two s₀₁ s₀₂`: two runs of the derivation with the same public data.
`Two.leaf` relates a piece of the body the taint analysis proves, from the
public words of the locals (`slots_of_words`), and adds what each run
satisfies by correctness; `ccall_rel` and `hcall_rel` relate the calls of G
and H′, from their preconditions in both runs and their public arguments.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.Proof.Argon2.X86 (compressX86)

/-- Two runs of the derivation, with the same public data. -/
structure Two (s₀₁ s₀₂ : State) : Prop where
  hp₁ : DPre s₀₁
  hp₂ : DPre s₀₂
  pb : VG.Proof.Argon2.X86.Derive.Pub2 s₀₁ s₀₂

namespace Pub2
variable {s₀₁ s₀₂ : State} (h : VG.Proof.Argon2.X86.Derive.Pub2 s₀₁ s₀₂)
include h

theorem arg_eq {i : Nat} (hi : i < 18) : VG.X86.arg s₀₁ i = VG.X86.arg s₀₂ i := h.2 i hi
theorem memP_eq : memP s₀₁ = memP s₀₂ := h.2 13 (by decide)
theorem scrP_eq : scrP s₀₁ = scrP s₀₂ := h.2 15 (by decide)
theorem outP_eq : outP s₀₁ = outP s₀₂ := h.2 16 (by decide)
theorem outL_eq : outL s₀₁ = outL s₀₂ := by simp only [outL, h.2 17 (by decide)]
theorem blocksN_eq : blocksN s₀₁ = blocksN s₀₂ := by simp only [blocksN, h.2 14 (by decide)]
theorem lanesN_eq : lanesN s₀₁ = lanesN s₀₂ := by simp only [lanesN, h.2 7 (by decide)]
theorem itersN_eq : itersN s₀₁ = itersN s₀₂ := by simp only [itersN, h.2 5 (by decide)]

theorem prm_eq : prm s₀₁ = prm s₀₂ := by
  simp only [prm, kindV, itersN, mcostN, lanesN, outL, h.2 0 (by decide), h.2 5 (by decide),
    h.2 6 (by decide), h.2 7 (by decide), h.2 17 (by decide)]

theorem esp_eq : s₀₁.gpr .esp = s₀₂.gpr .esp := h.1

end Pub2

/-- The slots `sl` of the locals hold the words `ws`. -/
theorem slots_of_words {s₀₁ s₀₂ s₁ s₂ : State} {ws : List Nat} {sl : List (Nat × Nat × Nat)}
    (hw : ∀ d ∈ ws, lw s₀₁ s₁ d = lw s₀₂ s₂ d)
    (hc : ∀ x ∈ sl, x.1 = 0 ∧ ∀ j < x.2.2, 4 * ((x.2.1 + j) / 4) ∈ ws) :
    ∀ x ∈ sl, x.1 = 0 ∧ ∀ k, x.2.1 ≤ k → k < x.2.1 + x.2.2 →
      lw s₀₁ s₁ (4 * (k / 4)) = lw s₀₂ s₂ (4 * (k / 4)) := by
  intro x hx
  obtain ⟨h0, hj⟩ := hc x hx
  refine ⟨h0, fun k h₁ h₂ => hw _ ?_⟩
  have := hj (k - x.2.1) (by omega)
  rwa [Nat.add_sub_cancel' h₁] at this

/-- A relation proved for each pair of related states. -/
theorem RelCT.of_eq {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ s₁ s₂, P s₁ s₂ → RelCT isa (fun a b => a = s₁ ∧ b = s₂) c Q) : RelCT isa P c Q :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => h s₁ s₂ hp s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

theorem execBlock_append (l₁ l₂ : List Instr) (s : State) :
    execBlock isa (l₁ ++ l₂) s = (execBlock isa l₁ s).bind fun p =>
      (execBlock isa l₂ p.1).map fun q => (q.1, p.2 ++ q.2) := by
  induction l₁ generalizing s with
  | nil => simp [execBlock]
  | cons i is ih =>
    simp only [List.cons_append, execBlock]
    split
    · rfl
    · rw [ih]
      cases execBlock isa is _ with
      | none => rfl
      | some p => simp [Function.comp_def, List.append_assoc]

/-- A block in two parts leaks as their sequence. -/
theorem RelCT.block_split {P Q : State → State → Prop} {l₁ l₂ : List Instr}
    (h : RelCT isa P (.seq (.block l₁) (.block l₂)) Q) : RelCT isa P (.block (l₁ ++ l₂)) Q := by
  have split : ∀ {s t s'}, Exec isa (.block (l₁ ++ l₂)) s t s' →
      Exec isa (.seq (.block l₁) (.block l₂)) s t s' := by
    intro s t s' e
    rw [Exec.block_iff, VG.Proof.Argon2.X86.Derive.execBlock_append, Option.bind_eq_some_iff] at e
    obtain ⟨⟨s₁, t₁⟩, h₁, h₂⟩ := e
    rw [Option.map_eq_some_iff] at h₂
    obtain ⟨⟨s₂, t₂⟩, h₂, he⟩ := h₂
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact .seq (.block h₁) (.block h₂)
  exact fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (split e₁) (split e₂)

namespace Two
variable {s₀₁ s₀₂ : State} (T : VG.Proof.Argon2.X86.Derive.Two s₀₁ s₀₂)
include T

/-- A piece of the body the taint analysis proves, from the slots `sl` of the
locals, which hold the words `ws`, public; with what each run satisfies. -/
theorem leaf {F₁ F₂ G₁ G₂ : State → Prop} {c : Prog isa} (ws : List Nat) (sl : List (Nat × Nat × Nat))
    (rs : List Reg) (hok : VG.X86.Taint.SlotsOk (VG.Proof.Argon2.X86.Derive.τB sl rs))
    (hsl : ∀ x ∈ sl, x.1 = 0 ∧ ∀ j < x.2.2, 4 * ((x.2.1 + j) / 4) ∈ ws)
    (hag : ∀ s₁ s₂, F₁ s₁ → F₂ s₂ → VG.Proof.Argon2.X86.Derive.Inv s₀₁ s₁ ∧ VG.Proof.Argon2.X86.Derive.Inv s₀₂ s₂ ∧ (∀ d ∈ ws, lw s₀₁ s₁ d = lw s₀₂ s₂ d) ∧
      ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (VG.Taint.check taint (VG.Proof.Argon2.X86.Derive.τB sl rs) c hc).isSome = true)
    (hw₁ : ∀ s, F₁ s → WP isa c s G₁) (hw₂ : ∀ s, F₂ s → WP isa c s G₂) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c fun t₁ t₂ => G₁ t₁ ∧ G₂ t₂ :=
  (VG.Proof.Argon2.X86.Derive.rel_taintW (R := fun _ _ => True) (VG.Proof.Argon2.X86.Derive.τB sl rs) (fun s₁ s₂ f₁ f₂ _ => by
      obtain ⟨i₁, i₂, hw, hr⟩ := hag s₁ s₂ f₁ f₂
      exact VG.Proof.Argon2.X86.Derive.agreeB T.hp₁ T.hp₂ T.pb i₁ i₂ sl rs hr hok (VG.Proof.Argon2.X86.Derive.slots_of_words hw hsl)) hc hw₁ hw₂).mono
    (fun _ _ h => ⟨h.1, h.2, trivial⟩) fun _ _ h => h

/-- A call of G: `compress(eax, esi, ecx, edx)` to `scratch + o`, with the
same blocks in both runs. -/
theorem ccall_rel {o : Nat} (ho : 4096 ≤ o) (ho' : o + 1024 ≤ 16384) {F₁ F₂ : State → Prop}
    (h : ∀ s₁ s₂, F₁ s₁ → F₂ s₂ →
      (VG.Proof.Argon2.X86.Derive.Inv s₀₁ s₁ ∧ s₁.gpr .edx = scrP s₀₁ ∧ s₁.gpr .ecx = scrP s₀₁ + BitVec.ofNat 32 o ∧
        VG.Proof.Argon2.X86.Derive.GArg s₀₁ o (s₁.gpr .eax) ∧ VG.Proof.Argon2.X86.Derive.GArg s₀₁ o (s₁.gpr .esi)) ∧
      (VG.Proof.Argon2.X86.Derive.Inv s₀₂ s₂ ∧ s₂.gpr .edx = scrP s₀₂ ∧ s₂.gpr .ecx = scrP s₀₂ + BitVec.ofNat 32 o ∧
        VG.Proof.Argon2.X86.Derive.GArg s₀₂ o (s₂.gpr .eax) ∧ VG.Proof.Argon2.X86.Derive.GArg s₀₂ o (s₂.gpr .esi)) ∧
      s₁.gpr .eax = s₂.gpr .eax ∧ s₁.gpr .esi = s₂.gpr .esi) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) Impl.Argon2.X86.Derive.compressCall fun _ _ => True := by
  refine RelCT.of_eq fun s₁ s₂ ⟨f₁, f₂⟩ => ?_
  obtain ⟨⟨i₁, d₁, c₁, x₁, y₁⟩, ⟨i₂, d₂, c₂, x₂, y₂⟩, ea, es⟩ := h s₁ s₂ f₁ f₂
  have hsp : s₁.gpr .esp = s₂.gpr .esp := by rw [i₁.esp, i₂.esp, T.pb.E]
  have p₁ := VG.Proof.Argon2.X86.Derive.ccall_pre T.hp₁ i₁ d₁ ho ho' c₁ x₁ y₁
  have p₂ := VG.Proof.Argon2.X86.Derive.ccall_pre T.hp₂ i₂ d₂ ho ho' c₂ x₂ y₂
  rw [← ea, ← es, ← hsp, show VG.Proof.Argon2.X86.Derive.scrB s₀₂ = VG.Proof.Argon2.X86.Derive.scrB s₀₁ by rw [VG.Proof.Argon2.X86.Derive.scrB, VG.Proof.Argon2.X86.Derive.scrB, T.pb.scrP_eq]] at p₂
  unfold Impl.Argon2.X86.Derive.compressCall
  refine RelCT.callWith (k := VG.Proof.Argon2.X86.compressX86) Proof.Argon2.X86.compress_verified.1
    Proof.Argon2.X86.compress_verified.2.1
    [⟨(s₁.gpr .eax).setWidth 64, 1024⟩, ⟨(s₁.gpr .esi).setWidth 64, 1024⟩,
      ⟨(s₁.gpr .esp - BitVec.ofNat 32 16).setWidth 64, 16⟩]
    [⟨VG.Proof.Argon2.X86.Derive.scrB s₀₁ + BitVec.ofNat 64 o, 1024⟩, ⟨VG.Proof.Argon2.X86.Derive.scrB s₀₁, 4096⟩] fun a b ⟨ha, hb⟩ => ?_
  subst ha hb
  have fit : 4 * [Reg.edx, .ecx, .esi, .eax].length + 4 ≤ (a.gpr .esp).toNat := by
    have := T.hp₁.esp_lo
    rw [i₁.esp, E_nat T.hp₁]; simp only [List.length_cons, List.length_nil]; omega
  obtain ⟨q₁, q₂⟩ := HPrime.call_pub (by decide) fit hsp (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [d₁, d₂, T.pb.scrP_eq]
    · rw [c₁, c₂, T.pb.scrP_eq]
    · exact es
    · exact ea) _ _
  exact ⟨p₁, p₂, hsp, q₁, q₂⟩

/-- A call of H′: `hprime(r, eax, edi, ecx, edx)`, with the same arguments in
both runs. -/
theorem hcall_rel {r : Reg} (hr : r ≠ .esp) {F₁ F₂ : State → Prop}
    (h : ∀ s₁ s₂, F₁ s₁ → F₂ s₂ →
      (VG.Proof.Argon2.X86.Derive.Inv s₀₁ s₁ ∧ s₁.gpr .edx = scrP s₀₁ ∧
        (∃ R ∈ [memR s₀₁, locR s₀₁], ∃ off, (s₁.gpr r).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
          off + (s₁.gpr .eax).toNat ≤ R.len) ∧ (s₁.gpr r).toNat + (s₁.gpr .eax).toNat ≤ 2 ^ 32 ∧
        (∃ R ∈ [memR s₀₁, VG.Proof.Argon2.X86.Derive.outR s₀₁], ∃ off, (s₁.gpr .edi).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
          off + (s₁.gpr .ecx).toNat ≤ R.len) ∧ (s₁.gpr .edi).toNat + (s₁.gpr .ecx).toNat ≤ 2 ^ 32 ∧
        1 ≤ (s₁.gpr .ecx).toNat) ∧
      (VG.Proof.Argon2.X86.Derive.Inv s₀₂ s₂ ∧ s₂.gpr .edx = scrP s₀₂ ∧
        (∃ R ∈ [memR s₀₂, locR s₀₂], ∃ off, (s₂.gpr r).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
          off + (s₂.gpr .eax).toNat ≤ R.len) ∧ (s₂.gpr r).toNat + (s₂.gpr .eax).toNat ≤ 2 ^ 32 ∧
        (∃ R ∈ [memR s₀₂, VG.Proof.Argon2.X86.Derive.outR s₀₂], ∃ off, (s₂.gpr .edi).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
          off + (s₂.gpr .ecx).toNat ≤ R.len) ∧ (s₂.gpr .edi).toNat + (s₂.gpr .ecx).toNat ≤ 2 ^ 32 ∧
        1 ≤ (s₂.gpr .ecx).toNat) ∧
      s₁.gpr r = s₂.gpr r ∧ s₁.gpr .eax = s₂.gpr .eax ∧ s₁.gpr .edi = s₂.gpr .edi ∧
        s₁.gpr .ecx = s₂.gpr .ecx) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) (.frame (.push [.edx, .ecx, .edi, .eax, r])
      (.call Impl.Argon2.X86.Derive.hPrimeName Impl.Argon2.X86.HPrime.code) (.pop .eax 5)) fun _ _ => True := by
  refine RelCT.of_eq fun s₁ s₂ ⟨f₁, f₂⟩ => ?_
  obtain ⟨⟨i₁, d₁, n₁, nf₁, o₁, of₁, l₁⟩, ⟨i₂, d₂, n₂, nf₂, o₂, of₂, l₂⟩, er, ea, ed, ec⟩ := h s₁ s₂ f₁ f₂
  have hsp : s₁.gpr .esp = s₂.gpr .esp := by rw [i₁.esp, i₂.esp, T.pb.E]
  have p₁ := hcall_pre T.hp₁ i₁ hr d₁ n₁ nf₁ o₁ of₁ l₁
  have p₂ := hcall_pre T.hp₂ i₂ hr d₂ n₂ nf₂ o₂ of₂ l₂
  rw [← er, ← ea, ← ed, ← ec, ← hsp, show VG.Proof.Argon2.X86.Derive.scrR s₀₂ = VG.Proof.Argon2.X86.Derive.scrR s₀₁ by rw [VG.Proof.Argon2.X86.Derive.scrR, VG.Proof.Argon2.X86.Derive.scrR, T.pb.scrP_eq]] at p₂
  refine RelCT.callWith (k := HPrime.hPrimeX86) HPrime.hPrime_verified.1 HPrime.hPrime_verified.2.1
    [⟨(s₁.gpr r).setWidth 64, (s₁.gpr .eax).toNat⟩, ⟨(s₁.gpr .esp - BitVec.ofNat 32 20).setWidth 64, 20⟩]
    [⟨(s₁.gpr .edi).setWidth 64, (s₁.gpr .ecx).toNat⟩, VG.Proof.Argon2.X86.Derive.scrR s₀₁] fun a b ⟨ha, hb⟩ => ?_
  subst ha hb
  have fit : 4 * [Reg.edx, .ecx, .edi, .eax, r].length + 4 ≤ (a.gpr .esp).toNat := by
    have := T.hp₁.esp_lo
    rw [i₁.esp, E_nat T.hp₁]; simp only [List.length_cons, List.length_nil]; omega
  obtain ⟨q₁, q₂⟩ := HPrime.call_pub (by simp [Ne.symm hr]) fit hsp (fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · rw [d₁, d₂, T.pb.scrP_eq]
    · exact ec
    · exact ed
    · exact ea
    · exact er) _ _
  exact ⟨p₁, p₂, hsp, q₁, q₂⟩

end Two

end VG.Proof.Argon2.X86.Derive

end

/-!
# Argon2 on x86 (32-bit): the random word, in two runs

`W`: the public words of the filling loops' locals (the parameters, the
position and the counter), which `Two.leafF` makes public for the taint
analysis, with any registers the runs agree on. The taint analysis forgets
that a sum with a memory operand is public (`column`, `blockAddr`,
`cacheWord`), so the pieces are cut there, and the runs related again from
what correctness says the registers hold. `randomSource_rel`: the random
word's trace depends only on the position.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd wp_mov wp_movi wp_add wp_addi wp_addm wp_andi)
open VG.Spec.Argon2 (FillState)
open VG.Impl.Sha512.X86 (at_)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  divisorOff strideOff)

/-- The public words of the filling loops' locals. -/
structure W (s₀ : State) (pass slice lane index ctr : Nat) (s : State) : Prop where
  inv : VG.Proof.Argon2.X86.Derive.Inv s₀ s
  pr : Prm s₀ s
  pos : VG.Proof.Argon2.X86.Derive.Pos s₀ s pass slice lane index
  ctr : lw s₀ s counterOff = BitVec.ofNat 32 ctr

theorem FS.w {s₀ s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.X86.Derive.FS s₀ pass slice lane index ctr st s) : VG.Proof.Argon2.X86.Derive.W s₀ pass slice lane index ctr s :=
  ⟨h.inv, h.pr, h.pos, h.cache.2.1⟩

theorem W.of_keep {s₀ s t : State} {pass slice lane index ctr : Nat} (h : VG.Proof.Argon2.X86.Derive.W s₀ pass slice lane index ctr s)
    (k : Divide.Keep s t) : VG.Proof.Argon2.X86.Derive.W s₀ pass slice lane index ctr t :=
  ⟨h.inv.keep k, h.pr.of_mem k.mem, h.pos.of_mem k.mem, by rw [lw_mem k.mem]; exact h.ctr⟩

/-- The words `W` is about. -/
abbrev ws0 : List Nat := [72, 76, 80, 84, 88, 92, 96, 100, 132]

/-- Their slots. -/
abbrev sl0 : List (Nat × Nat × Nat) := [(0, 72, 32), (0, 132, 4)]

theorem slotsOk0 (rs : List Reg) : VG.X86.Taint.SlotsOk (VG.Proof.Argon2.X86.Derive.τB VG.Proof.Argon2.X86.Derive.sl0 rs) := by
  intro x hx
  simp only [VG.Proof.Argon2.X86.Derive.τB, VG.Proof.Argon2.X86.Derive.sl0, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> simp [VG.Proof.Argon2.X86.Derive.τB]

theorem slotsOkE (rs : List Reg) : VG.X86.Taint.SlotsOk (VG.Proof.Argon2.X86.Derive.τB [] rs) := by
  intro x hx
  simp only [VG.Proof.Argon2.X86.Derive.τB, List.nil_append, List.mem_singleton] at hx
  subst hx; simp [VG.Proof.Argon2.X86.Derive.τB]

/-- Composition, with what each run satisfies after the first part. -/
theorem RelCT.seqW {F₁ F₂ G₁ G₂ : State → Prop} {c₁ c₂ : Prog isa} {Q : State → State → Prop}
    (h₁ : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c₁ fun _ _ => True)
    (w₁ : ∀ s, F₁ s → WP isa c₁ s G₁) (w₂ : ∀ s, F₂ s → WP isa c₁ s G₂)
    (h₂ : RelCT isa (fun s₁ s₂ => G₁ s₁ ∧ G₂ s₂) c₂ Q) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) (.seq c₁ c₂) Q :=
  RelCT.seq (HPrime.rel_wp h₁ w₁ w₂) h₂

/-- A branch on a condition that agrees in both runs. -/
theorem RelCT.iteF {F₁ F₂ : State → Prop} {c : Cond} {th el : Prog isa} {Q : State → State → Prop}
    (hc : ∀ s₁ s₂, F₁ s₁ → F₂ s₂ → isa.eval c s₁ = isa.eval c s₂)
    (ht : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) th Q) (he : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) el Q) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) (.ite c th el) Q :=
  RelCT.ite (fun s₁ s₂ h => hc s₁ s₂ h.1 h.2) (ht.mono (fun _ _ h => h.1) fun _ _ h => h)
    (he.mono (fun _ _ h => h.1) fun _ _ h => h)

namespace Two
variable {s₀₁ s₀₂ : State} (T : VG.Proof.Argon2.X86.Derive.Two s₀₁ s₀₂)
include T

theorem words {pass slice lane index ctr : Nat} {s₁ s₂ : State} (h₁ : VG.Proof.Argon2.X86.Derive.W s₀₁ pass slice lane index ctr s₁)
    (h₂ : VG.Proof.Argon2.X86.Derive.W s₀₂ pass slice lane index ctr s₂) : ∀ d ∈ VG.Proof.Argon2.X86.Derive.ws0, lw s₀₁ s₁ d = lw s₀₂ s₂ d := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  intro d hd
  simp only [VG.Proof.Argon2.X86.Derive.ws0, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁.pos.pass.trans h₂.pos.pass.symm
  · exact h₁.pos.lane.trans h₂.pos.lane.symm
  · exact h₁.pos.slice.trans h₂.pos.slice.symm
  · exact h₁.pos.index.trans h₂.pos.index.symm
  · exact h₁.ctr.trans h₂.ctr.symm
  · exact (h₁.pr.laneLen.trans (congrArg (fun p : Spec.Argon2.Params => BitVec.ofNat 32 p.laneLen) pe)).trans h₂.pr.laneLen.symm
  · exact (h₁.pr.stride.trans (congrArg (fun p : Spec.Argon2.Params => BitVec.ofNat 32 (p.laneLen * 1024)) pe)).trans
      h₂.pr.stride.symm
  · exact (h₁.pr.segLen.trans (congrArg (fun p : Spec.Argon2.Params => BitVec.ofNat 32 p.segmentLen) pe)).trans h₂.pr.segLen.symm
  · exact (h₁.pr.divisor.trans (congrArg (fun n : Nat => BitVec.ofNat 32 (4 * n)) le)).trans h₂.pr.divisor.symm

/-- A piece the taint analysis proves from the public words `W` and the
registers `rs`, which both runs agree on. -/
theorem leafF {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s₁ s₂, P s₁ s₂ → (∃ pass slice lane index ctr, VG.Proof.Argon2.X86.Derive.W s₀₁ pass slice lane index ctr s₁ ∧
      VG.Proof.Argon2.X86.Derive.W s₀₂ pass slice lane index ctr s₂) ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (VG.Taint.check taint (VG.Proof.Argon2.X86.Derive.τB VG.Proof.Argon2.X86.Derive.sl0 rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  refine RelCT.taintW (VG.Proof.Argon2.X86.Derive.τB VG.Proof.Argon2.X86.Derive.sl0 rs) (fun s₁ s₂ h => ?_) hc
  obtain ⟨⟨_, _, _, _, _, w₁, w₂⟩, hr⟩ := hag s₁ s₂ h
  exact VG.Proof.Argon2.X86.Derive.agreeB T.hp₁ T.hp₂ T.pb w₁.inv w₂.inv VG.Proof.Argon2.X86.Derive.sl0 rs hr (VG.Proof.Argon2.X86.Derive.slotsOk0 rs)
    (VG.Proof.Argon2.X86.Derive.slots_of_words (T.words w₁ w₂) (by decide))

/-- A piece the taint analysis proves from the arguments and the registers
`rs`, which both runs agree on. -/
theorem leafI {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.Argon2.X86.Derive.Inv s₀₁ s₁ ∧ VG.Proof.Argon2.X86.Derive.Inv s₀₂ s₂ ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (VG.Taint.check taint (VG.Proof.Argon2.X86.Derive.τB [] rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  refine RelCT.taintW (VG.Proof.Argon2.X86.Derive.τB [] rs) (fun s₁ s₂ h => ?_) hc
  obtain ⟨i₁, i₂, hr⟩ := hag s₁ s₂ h
  exact VG.Proof.Argon2.X86.Derive.agreeB T.hp₁ T.hp₂ T.pb i₁ i₂ [] rs hr (VG.Proof.Argon2.X86.Derive.slotsOkE rs) (fun _ h => (List.not_mem_nil h).elim)

end Two

/-! ## Pointers -/

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem column_w {s : State} {pass slice lane index ctr : Nat} (h : VG.Proof.Argon2.X86.Derive.W s₀ pass slice lane index ctr s)
    (hs : slice < 4) (hi : index < (prm s₀).segmentLen) :
    WP isa (.block Impl.Argon2.X86.Derive.column) s fun t => VG.Proof.Argon2.X86.Derive.W s₀ pass slice lane index ctr t ∧
      t.gpr .ecx = BitVec.ofNat 32 (slice * (prm s₀).segmentLen + index) := by
  rw [← List.append_nil Impl.Argon2.X86.Derive.column]
  exact VG.Proof.Argon2.X86.Derive.column_ok hp h.inv h.pr h.pos hs hi fun t _ c k => WP.block_nil ⟨h.of_keep k, c⟩

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : VG.Proof.Argon2.X86.Derive.Two s₀₁ s₀₂)
include T

/-- `prevPointer` leaks the same trace in two runs at the same position. -/
theorem prevPointer_rel {pass slice lane index ctr : Nat} (hs : slice < 4)
    (hi : index < (prm s₀₁).segmentLen) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.Derive.W s₀₁ pass slice lane index ctr s₁ ∧ VG.Proof.Argon2.X86.Derive.W s₀₂ pass slice lane index ctr s₂)
      Impl.Argon2.X86.Derive.prevPointer fun _ _ => True := by
  have pe := T.pb.prm_eq
  have hi₂ : index < (prm s₀₂).segmentLen := pe ▸ hi
  have hc := Proof.Argon2.column_lt (prm s₀₁) T.hp₁.lanes_pos hs hi
  have hc₂ := Proof.Argon2.column_lt (prm s₀₂) T.hp₂.lanes_pos hs hi₂
  unfold Impl.Argon2.X86.Derive.prevPointer
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1, h.2⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.X86.Derive.column_w T.hp₁ h hs hi) (fun s h => VG.Proof.Argon2.X86.Derive.column_w T.hp₂ h hs hi₂) ?_
  refine RelCT.seqW (T.leafF [.ecx] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1, h.2.1⟩, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.2, h.2.2, pe]⟩) ⟨_, by taint_decide⟩)
    (fun s h => (VG.Proof.Argon2.X86.Derive.prevColumn_ok T.hp₁ h.1.inv h.1.pr hc h.2).mono fun t ⟨_, k⟩ => h.1.of_keep k)
    (fun s h => (VG.Proof.Argon2.X86.Derive.prevColumn_ok T.hp₂ h.1.inv h.1.pr hc₂ h.2).mono fun t ⟨_, k⟩ => h.1.of_keep k) ?_
  exact T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1, h.2⟩, by simp⟩) ⟨_, by taint_decide⟩

/-- `dependentWord` leaks the same trace in two runs at the same position. -/
theorem dependentWord_rel {pass slice lane index ctr : Nat} (hl : lane < lanesN s₀₁) (hs : slice < 4)
    (hi : index < (prm s₀₁).segmentLen) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.Derive.W s₀₁ pass slice lane index ctr s₁ ∧ VG.Proof.Argon2.X86.Derive.W s₀₂ pass slice lane index ctr s₂)
      Impl.Argon2.X86.Derive.dependentWord fun _ _ => True := by
  have pe := T.pb.prm_eq
  have hi₂ : index < (prm s₀₂).segmentLen := pe ▸ hi
  have hl₂ : lane < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  unfold Impl.Argon2.X86.Derive.dependentWord
  refine RelCT.seq (HPrime.rel_wp (T.prevPointer_rel hs hi)
    (G₁ := fun t => VG.Proof.Argon2.X86.Derive.W s₀₁ pass slice lane index ctr t ∧ t.gpr .eax = memP s₀₁ + BitVec.ofNat 32
      ((lane * (prm s₀₁).laneLen + (slice * (prm s₀₁).segmentLen + index + (prm s₀₁).laneLen - 1) %
        (prm s₀₁).laneLen) * 1024))
    (G₂ := fun t => VG.Proof.Argon2.X86.Derive.W s₀₂ pass slice lane index ctr t ∧ t.gpr .eax = memP s₀₂ + BitVec.ofNat 32
      ((lane * (prm s₀₂).laneLen + (slice * (prm s₀₂).segmentLen + index + (prm s₀₂).laneLen - 1) %
        (prm s₀₂).laneLen) * 1024))
    (fun s h => (VG.Proof.Argon2.X86.Derive.prevPointer_ok T.hp₁ h.inv h.pr h.pos hl hs hi).mono fun t ⟨a, k⟩ => ⟨h.of_keep k, a⟩)
    (fun s h => (VG.Proof.Argon2.X86.Derive.prevPointer_ok T.hp₂ h.inv h.pr h.pos hl₂ hs hi₂).mono fun t ⟨a, k⟩ => ⟨h.of_keep k, a⟩)) ?_
  exact T.leafF [.eax] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1, h.2.1⟩, by
    simp only [List.mem_singleton, forall_eq]; rw [h.1.2, h.2.2, pe, T.pb.memP_eq]⟩) ⟨_, by taint_decide⟩

end Two

theorem W.of_lw {s₀ s t : State} {pass slice lane index ctr : Nat} (h : VG.Proof.Argon2.X86.Derive.W s₀ pass slice lane index ctr s)
    (it : VG.Proof.Argon2.X86.Derive.Inv s₀ t) (hl : ∀ d ∈ VG.Proof.Argon2.X86.Derive.ws0, lw s₀ t d = lw s₀ s d) : VG.Proof.Argon2.X86.Derive.W s₀ pass slice lane index ctr t :=
  ⟨it, Prm.of_lw h.pr fun d hd => hl d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
    h.pos.of_lw fun d hd => hl d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
    (hl 88 (by decide)).trans h.ctr⟩

/-! ## The address block -/

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The instructions before G's call in `stage x y o`. -/
theorem stageBlk_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) (x y o : Nat) :
    WP isa (.block [.mov .edx (Impl.Argon2.X86.Derive.fr (argOff 15)), .mov .eax (.reg .edx),
      .alu .add .eax (.imm (BitVec.ofNat 32 x)), .mov .esi (.reg .edx),
      .alu .add .esi (.imm (BitVec.ofNat 32 y)), .mov .ecx (.reg .edx),
      .alu .add .ecx (.imm (BitVec.ofNat 32 o))]) s fun t => VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ t.gpr .edx = scrP s₀ ∧
      t.gpr .eax = scrP s₀ + BitVec.ofNat 32 x ∧ t.gpr .esi = scrP s₀ + BitVec.ofNat 32 y ∧
      t.gpr .ecx = scrP s₀ + BitVec.ofNat 32 o := by
  refine wp_ldarg hp h (i := 15) (by decide) fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_addi fun s₃ u₃ =>
    wp_mov fun s₄ u₄ => wp_addi fun s₅ u₅ => wp_mov fun s₆ u₆ => wp_addi fun s₇ u₇ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ((((((h.upd u₁ (by decide) (by decide)).upd u₂ (by decide) (by decide)).upd u₃ (by decide)
      (by decide)).upd u₄ (by decide) (by decide)).upd u₅ (by decide) (by decide)).upd u₆ (by decide)
      (by decide)).upd u₇ (by decide) (by decide)
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.gpr, u₁.gpr]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]

/-- The counter, stored. -/
theorem stctr_w {s : State} {pass slice lane index ctr c : Nat} (h : VG.Proof.Argon2.X86.Derive.W s₀ pass slice lane index ctr s)
    (ha : s.gpr .eax = BitVec.ofNat 32 c) :
    WP isa (.block [Impl.Argon2.X86.Derive.st counterOff .eax]) s (VG.Proof.Argon2.X86.Derive.W s₀ pass slice lane index c) :=
  wp_stloc hp h.inv (d := counterOff) (by decide) fun t it vt ot _ _ => WP.block_nil
    ⟨it, Prm.of_lw h.pr fun d hd => ot d (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl | rfl | rfl <;> decide),
    h.pos.of_lw fun d hd => ot d (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl | rfl | rfl <;> decide),
    by rw [vt, ha]⟩

/-- The first part of `cacheWord`: `eax :=` the address of word `index mod 128`'s pair. -/
theorem cacheWord1_ok {s : State} {pass slice lane index ctr : Nat} (h : VG.Proof.Argon2.X86.Derive.W s₀ pass slice lane index ctr s)
    (hi : index < 2 ^ 30) :
    WP isa (.block [.mov .eax (Impl.Argon2.X86.Derive.fr indexOff), .alu .and .eax (.imm 127),
      .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
      .alu .add .eax (Impl.Argon2.X86.Derive.fr (argOff 15))]) s fun t => VG.Proof.Argon2.X86.Derive.W s₀ pass slice lane index ctr t ∧
      t.gpr .eax = scrP s₀ + BitVec.ofNat 32 (8 * (index % 128)) := by
  refine wp_ldloc hp h.inv (d := indexOff) (by decide) fun s₁ u₁ => wp_andi fun s₂ u₂ => wp_add fun s₃ u₃ _ =>
    wp_add fun s₄ u₄ _ => wp_add fun s₅ u₅ _ => ?_
  have h₅ := (((((h.of_keep (Divide.Keep.of_upd u₁ (by simp))).of_keep (Divide.Keep.of_upd u₂ (by simp))).of_keep
    (Divide.Keep.of_upd u₃ (by simp))).of_keep (Divide.Keep.of_upd u₄ (by simp))).of_keep
    (Divide.Keep.of_upd u₅ (by simp)))
  have a₅ : s₅.gpr .eax = BitVec.ofNat 32 (8 * (index % 128)) := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, h.pos.index, VG.Proof.Argon2.X86.Derive.and127 (by omega), VG.Proof.Argon2.X86.Derive.dbl32, VG.Proof.Argon2.X86.Derive.dbl32, VG.Proof.Argon2.X86.Derive.dbl32]
    congr 1; omega
  refine wp_addm h₅.inv.ebp (h₅.inv.arg_in hp (i := 15) (by decide)) fun s₆ u₆ => WP.block_nil
    ⟨h₅.of_keep (Divide.Keep.of_upd u₆ (by simp)), ?_⟩
  rw [u₆.gpr, h₅.inv.arg hp (by decide), a₅, BitVec.add_comm]

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : VG.Proof.Argon2.X86.Derive.Two s₀₁ s₀₂)
include T

/-- `stage x y o` leaks the same trace in two runs. -/
theorem stage_rel {x y o : Nat} (ho : 4096 ≤ o) (ho' : o + 1024 ≤ 16384)
    (hx : 4096 ≤ x) (hx' : x + 1024 ≤ 16384) (hxo : x + 1024 ≤ o ∨ o + 1024 ≤ x)
    (hy : 4096 ≤ y) (hy' : y + 1024 ≤ 16384) (hyo : y + 1024 ≤ o ∨ o + 1024 ≤ y)
    (hc : ∃ hc, (VG.Taint.check taint (VG.Proof.Argon2.X86.Derive.τB [] []) (.block [.mov .edx (Impl.Argon2.X86.Derive.fr (argOff 15)),
      .mov .eax (.reg .edx), .alu .add .eax (.imm (BitVec.ofNat 32 x)), .mov .esi (.reg .edx),
      .alu .add .esi (.imm (BitVec.ofNat 32 y)), .mov .ecx (.reg .edx),
      .alu .add .ecx (.imm (BitVec.ofNat 32 o))]) hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.Derive.Inv s₀₁ s₁ ∧ VG.Proof.Argon2.X86.Derive.Inv s₀₂ s₂) (Impl.Argon2.X86.Derive.stage x y o) fun _ _ => True := by
  unfold Impl.Argon2.X86.Derive.stage
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1, h.2, by simp⟩) hc)
    (fun s h => VG.Proof.Argon2.X86.Derive.stageBlk_ok T.hp₁ h x y o) (fun s h => VG.Proof.Argon2.X86.Derive.stageBlk_ok T.hp₂ h x y o) ?_
  refine T.ccall_rel ho ho' fun s₁ s₂ ⟨i₁, d₁, a₁, e₁, c₁⟩ ⟨i₂, d₂, a₂, e₂, c₂⟩ =>
    ⟨⟨i₁, d₁, c₁, by rw [a₁]; exact .inr ⟨x, hx, hx', hxo, rfl⟩, by rw [e₁]; exact .inr ⟨y, hy, hy', hyo, rfl⟩⟩,
     ⟨i₂, d₂, c₂, by rw [a₂]; exact .inr ⟨x, hx, hx', hxo, rfl⟩, by rw [e₂]; exact .inr ⟨y, hy, hy', hyo, rfl⟩⟩,
     by rw [a₁, a₂, T.pb.scrP_eq], by rw [e₁, e₂, T.pb.scrP_eq]⟩

/-- `addressCalls` leaks the same trace in two runs at the same position. -/
theorem addressCalls_rel {pass slice lane index c : Nat} (h₁ : pass < 2 ^ 32) (h₂ : lane < 2 ^ 32)
    (h₃ : slice < 2 ^ 32) (h₄ : c < 2 ^ 32) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.Derive.W s₀₁ pass slice lane index c s₁ ∧ VG.Proof.Argon2.X86.Derive.W s₀₂ pass slice lane index c s₂)
      Impl.Argon2.X86.Derive.addressCalls fun _ _ => True := by
  unfold Impl.Argon2.X86.Derive.addressCalls
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1, h.2⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => (VG.Proof.Argon2.X86.Derive.input_ok T.hp₁ h.inv h.pos h.ctr h₁ h₂ h₃ h₄).mono fun t ht => ht.1)
    (fun s h => (VG.Proof.Argon2.X86.Derive.input_ok T.hp₂ h.inv h.pos h.ctr h₁ h₂ h₃ h₄).mono fun t ht => ht.1) ?_
  refine RelCT.seqW (T.stage_rel (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) ⟨_, by taint_decide⟩)
    (fun s h => (VG.Proof.Argon2.X86.Derive.stage_ok T.hp₁ h (x := 7168) (y := 5120) (o := 4096) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).mono fun t ht => ht.1)
    (fun s h => (VG.Proof.Argon2.X86.Derive.stage_ok T.hp₂ h (x := 7168) (y := 5120) (o := 4096) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).mono fun t ht => ht.1) ?_
  exact T.stage_rel (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) ⟨_, by taint_decide⟩

/-- `cacheWord` leaks the same trace in two runs at the same position. -/
theorem cacheWord_rel {pass slice lane index c : Nat} (hi : index < 2 ^ 30) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.Derive.W s₀₁ pass slice lane index c s₁ ∧ VG.Proof.Argon2.X86.Derive.W s₀₂ pass slice lane index c s₂)
      (.block Impl.Argon2.X86.Derive.cacheWord) fun _ _ => True := by
  unfold Impl.Argon2.X86.Derive.cacheWord
  refine RelCT.block_split (l₁ := [_, _, _, _, _, _]) (RelCT.seqW
    (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1, h.2⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.X86.Derive.cacheWord1_ok T.hp₁ h hi) (fun s h => VG.Proof.Argon2.X86.Derive.cacheWord1_ok T.hp₂ h hi) ?_)
  exact T.leafF [.eax] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1, h.2.1⟩, by
    simp only [List.mem_singleton, forall_eq]; rw [h.1.2, h.2.2, T.pb.scrP_eq]⟩) ⟨_, by taint_decide⟩

/-- `addressCache` leaks the same trace in two runs at the same position. -/
theorem addressCache_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} (hpass : pass < 2 ^ 32)
    (hl : lane < lanesN s₀₁) (hs : slice < 4) (hi : index < (prm s₀₁).segmentLen) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.Derive.FS s₀₁ pass slice lane index ctr st₁ s₁ ∧ VG.Proof.Argon2.X86.Derive.FS s₀₂ pass slice lane index ctr st₂ s₂)
      Impl.Argon2.X86.Derive.addressCache fun _ _ => True := by
  have pe := T.pb.prm_eq
  have hi₂ : index < (prm s₀₂).segmentLen := pe ▸ hi
  have hl₂ : lane < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  have sl := VG.Proof.Argon2.X86.Derive.segLen_lt T.hp₁
  have hlt := T.hp₁.lanes_lt
  unfold Impl.Argon2.X86.Derive.addressCache
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.w, h.2.w⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.X86.Derive.cacheCheck_ok T.hp₁ h hi) (fun s h => VG.Proof.Argon2.X86.Derive.cacheCheck_ok T.hp₂ h hi₂) ?_
  refine RelCT.seqW (RelCT.iteF (fun s₁ s₂ h₁ h₂ => by
      show s₁.zf = s₂.zf
      rw [h₁.2.2, h₂.2.2, h₁.1.cache.2.1, h₂.1.cache.2.1])
    (RelCT.nil fun _ _ _ => trivial) ?_)
    (fun s h => VG.Proof.Argon2.X86.Derive.cacheFill_ok T.hp₁ h.1 hpass hl hs hi h.2.1 h.2.2)
    (fun s h => VG.Proof.Argon2.X86.Derive.cacheFill_ok T.hp₂ h.1 hpass hl₂ hs hi₂ h.2.1 h.2.2)
    ((T.cacheWord_rel (by omega)).mono (fun _ _ h => ⟨h.1.1.w, h.2.1.w⟩) fun _ _ h => h)
  refine RelCT.seqW (G₁ := VG.Proof.Argon2.X86.Derive.W s₀₁ pass slice lane index (index / 128 + 1))
    (G₂ := VG.Proof.Argon2.X86.Derive.W s₀₂ pass slice lane index (index / 128 + 1))
    (T.leafF [.eax] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1.w, h.2.1.w⟩, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.2.1, h.2.2.1]⟩) ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.X86.Derive.stctr_w T.hp₁ h.1.w h.2.1) (fun s h => VG.Proof.Argon2.X86.Derive.stctr_w T.hp₂ h.1.w h.2.1) ?_
  exact T.addressCalls_rel hpass (by omega) (by omega) (by omega)

end Two

namespace Two
variable {s₀₁ s₀₂ : State} (T : VG.Proof.Argon2.X86.Derive.Two s₀₁ s₀₂)
include T

/-- `randomSource` leaks the same trace in two runs at the same position. -/
theorem randomSource_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} (hpass : pass < 2 ^ 32)
    (hl : lane < lanesN s₀₁) (hs : slice < 4) (hi : index < (prm s₀₁).segmentLen) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.Derive.FS s₀₁ pass slice lane index ctr st₁ s₁ ∧ VG.Proof.Argon2.X86.Derive.FS s₀₂ pass slice lane index ctr st₂ s₂)
      Impl.Argon2.X86.Derive.randomSource fun _ _ => True := by
  have pe := T.pb.prm_eq
  unfold Impl.Argon2.X86.Derive.randomSource
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.w, h.2.w⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (G₁ := fun t => VG.Proof.Argon2.X86.Derive.FS s₀₁ pass slice lane index ctr st₁ t ∧
      t.zf = some (!Spec.Argon2.independent (prm s₀₁) pass slice))
    (G₂ := fun t => VG.Proof.Argon2.X86.Derive.FS s₀₂ pass slice lane index ctr st₂ t ∧
      t.zf = some (!Spec.Argon2.independent (prm s₀₂) pass slice))
    (fun s h => (VG.Proof.Argon2.X86.Derive.addressMode_ok T.hp₁ h.inv h.pos hpass hs).mono fun t ⟨z, k⟩ => ⟨h.of_keep k, z⟩)
    (fun s h => (VG.Proof.Argon2.X86.Derive.addressMode_ok T.hp₂ h.inv h.pos hpass hs).mono fun t ⟨z, k⟩ => ⟨h.of_keep k, z⟩) ?_
  refine RelCT.iteF (fun s₁ s₂ h₁ h₂ => by
      show s₁.zf = s₂.zf
      rw [h₁.2, h₂.2, pe])
    ((T.dependentWord_rel hl hs hi).mono (fun _ _ h => ⟨h.1.1.w, h.2.1.w⟩) fun _ _ h => h)
    ((T.addressCache_rel hpass hl hs hi).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h)

end Two

end VG.Proof.Argon2.X86.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.Derive.FillCT2`. -/
section

/-!
# Argon2 on x86 (32-bit): a block of the filling loops, in two runs

`fillBlock_rel`: one block's trace depends only on its position and on the
reference block's index, which the leakage permits (`Spec.Argon2.references`):
the reference is computed from the random word in the locals (`reference_rel`),
G is called on the previous and the reference blocks (`fillCompress_rel`), and
its output is written to the current block (`fillWrite_rel`), whose address the
runs agree on.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd wp_mov wp_movi wp_add wp_addi)
open VG.Spec.Argon2 (FillState)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  divisorOff strideOff j1Off j2Off refLaneOff tmpOff curOff)

/-- Two runs, from any of a family of states each. -/
theorem RelCT.exists₂ {α β : Sort _} {A : α → State → Prop} {B : β → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (h : ∀ a b, RelCT isa (fun s₁ s₂ => A a s₁ ∧ B b s₂) c Q) :
    RelCT isa (fun s₁ s₂ => (∃ a, A a s₁) ∧ ∃ b, B b s₂) c Q :=
  fun _ _ _ _ _ _ ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ e₁ e₂ => h a b _ _ _ _ _ _ ⟨ha, hb⟩ e₁ e₂

/-- The slots of the words `ws0` and `ex`. -/
abbrev slx (ex : List Nat) : List (Nat × Nat × Nat) := VG.Proof.Argon2.X86.Derive.sl0 ++ ex.map fun d => (0, d, 4)

theorem slotsOkX {ex : List Nat} (hex : ∀ d ∈ ex, d % 4 = 0 ∧ d + 4 ≤ 144) (rs : List Reg) :
    VG.X86.Taint.SlotsOk (VG.Proof.Argon2.X86.Derive.τB (VG.Proof.Argon2.X86.Derive.slx ex) rs) := by
  intro x hx
  simp only [VG.Proof.Argon2.X86.Derive.τB, VG.Proof.Argon2.X86.Derive.slx, List.append_assoc, List.mem_append, List.mem_map] at hx
  rcases hx with hx | ⟨d, hd, rfl⟩ | hx
  · exact VG.Proof.Argon2.X86.Derive.slotsOk0 rs x (by simp only [VG.Proof.Argon2.X86.Derive.τB]; exact List.mem_append_left _ hx)
  · have := hex d hd; simp [VG.Proof.Argon2.X86.Derive.τB]; omega
  · exact VG.Proof.Argon2.X86.Derive.slotsOk0 rs x (by simp only [VG.Proof.Argon2.X86.Derive.τB]; exact List.mem_append_right _ hx)

namespace Two
variable {s₀₁ s₀₂ : State} (T : VG.Proof.Argon2.X86.Derive.Two s₀₁ s₀₂)
include T

/-- As `leafF`, with the words `ex` of the locals public too. -/
theorem leafX {P : State → State → Prop} {c : Prog isa} (rs : List Reg) (ex : List Nat)
    (hex : ∀ d ∈ ex, d % 4 = 0 ∧ d + 4 ≤ 144)
    (hag : ∀ s₁ s₂, P s₁ s₂ → (∃ pass slice lane index ctr, VG.Proof.Argon2.X86.Derive.W s₀₁ pass slice lane index ctr s₁ ∧
      VG.Proof.Argon2.X86.Derive.W s₀₂ pass slice lane index ctr s₂) ∧ (∀ r ∈ rs, s₁.gpr r = s₂.gpr r) ∧
      ∀ d ∈ ex, lw s₀₁ s₁ d = lw s₀₂ s₂ d)
    (hc : ∃ hc, (VG.Taint.check taint (VG.Proof.Argon2.X86.Derive.τB (VG.Proof.Argon2.X86.Derive.slx ex) rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  refine RelCT.taintW (VG.Proof.Argon2.X86.Derive.τB (VG.Proof.Argon2.X86.Derive.slx ex) rs) (fun s₁ s₂ h => ?_) hc
  obtain ⟨⟨_, _, _, _, _, w₁, w₂⟩, hr, he⟩ := hag s₁ s₂ h
  refine VG.Proof.Argon2.X86.Derive.agreeB T.hp₁ T.hp₂ T.pb w₁.inv w₂.inv _ rs hr (VG.Proof.Argon2.X86.Derive.slotsOkX hex rs)
    (VG.Proof.Argon2.X86.Derive.slots_of_words (ws := VG.Proof.Argon2.X86.Derive.ws0 ++ ex) (fun d hd => ?_) fun x hx => ?_)
  · rcases List.mem_append.mp hd with hd | hd
    · exact T.words w₁ w₂ d hd
    · exact he d hd
  · rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨h0, hj⟩ := (show ∀ x ∈ VG.Proof.Argon2.X86.Derive.sl0, x.1 = 0 ∧ ∀ j < x.2.2, 4 * ((x.2.1 + j) / 4) ∈ VG.Proof.Argon2.X86.Derive.ws0 by decide) x hx
      exact ⟨h0, fun j hj' => List.mem_append_left _ (hj j hj')⟩
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
      refine ⟨rfl, fun j hj => List.mem_append_right _ ?_⟩
      have := (hex d hd).1
      rw [show 4 * ((d + j) / 4) = d by simp only at hj; omega]
      exact hd

/-! ## The reference -/

/-- `refLane` leaks the same trace in two runs at the same position. -/
theorem refLane_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} {J1 J2 J1' J2' : BitVec 32}
    (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.Derive.RS s₀₁ pass slice lane index ctr st₁ J1 J2 s₁ ∧
      VG.Proof.Argon2.X86.Derive.RS s₀₂ pass slice lane index ctr st₂ J1' J2' s₂) Impl.Argon2.X86.Derive.refLane fun _ _ => True := by
  unfold Impl.Argon2.X86.Derive.refLane
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.fs.w, h.2.fs.w⟩, by simp⟩)
      ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.X86.Derive.refLaneBlk_ok T.hp₁ h hpass hs) (fun s h => VG.Proof.Argon2.X86.Derive.refLaneBlk_ok T.hp₂ h hpass hs) ?_
  refine RelCT.iteF (fun s₁ s₂ h₁ h₂ => by
      show s₁.zf = s₂.zf
      rw [h₁.2.1, h₂.2.1])
    (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1.fs.w, h.2.1.fs.w⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (RelCT.nil fun _ _ _ => trivial)

/-- `reference` leaks the same trace in two runs at the same position. -/
theorem reference_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} {J1 J2 J1' J2' : BitVec 32}
    (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.Derive.RS s₀₁ pass slice lane index ctr st₁ J1 J2 s₁ ∧
      VG.Proof.Argon2.X86.Derive.RS s₀₂ pass slice lane index ctr st₂ J1' J2' s₂) Impl.Argon2.X86.Derive.reference fun _ _ => True := by
  unfold Impl.Argon2.X86.Derive.reference
  refine RelCT.seqW (T.refLane_rel hpass hs)
    (fun s h => (VG.Proof.Argon2.X86.Derive.refLane_ok T.hp₁ h hpass hs).mono fun t ht => ht.1)
    (fun s h => (VG.Proof.Argon2.X86.Derive.refLane_ok T.hp₂ h hpass hs).mono fun t ht => ht.1) ?_
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.fs.w, h.2.fs.w⟩, by simp⟩)
      ⟨_, by taint_decide⟩)
    (fun s h => (VG.Proof.Argon2.X86.Derive.refStart_ok T.hp₁ h hpass hs).mono fun t ht => ht.1)
    (fun s h => (VG.Proof.Argon2.X86.Derive.refStart_ok T.hp₂ h hpass hs).mono fun t ht => ht.1) ?_
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.fs.w, h.2.fs.w⟩, by simp⟩)
      ⟨_, by taint_decide⟩)
    (fun s h => (VG.Proof.Argon2.X86.Derive.countBase_ok T.hp₁ h hpass hs).mono fun t ht => h.of_keep ht.1)
    (fun s h => (VG.Proof.Argon2.X86.Derive.countBase_ok T.hp₂ h hpass hs).mono fun t ht => h.of_keep ht.1) ?_
  exact T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.fs.w, h.2.fs.w⟩, by simp⟩) ⟨_, by taint_decide⟩

end Two

/-! ## G and the new block -/

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The instructions before `fillCompress`'s call of G. -/
theorem fcBlk_ok {s : State} {pass slice lane index ctr : Nat} (h : VG.Proof.Argon2.X86.Derive.W s₀ pass slice lane index ctr s)
    {P R : Nat} (ha : s.gpr .eax = memP s₀ + BitVec.ofNat 32 (P * 1024))
    (htmp : lw s₀ s tmpOff = memP s₀ + BitVec.ofNat 32 (R * 1024)) :
    WP isa (.block [.mov .esi (Impl.Argon2.X86.Derive.fr tmpOff),
      .mov .edx (Impl.Argon2.X86.Derive.fr (argOff 15)), .mov .ecx (.reg .edx),
      .alu .add .ecx (.imm 4096)]) s fun t => VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ t.gpr .edx = scrP s₀ ∧
      t.gpr .ecx = scrP s₀ + BitVec.ofNat 32 4096 ∧ t.gpr .eax = memP s₀ + BitVec.ofNat 32 (P * 1024) ∧
      t.gpr .esi = memP s₀ + BitVec.ofNat 32 (R * 1024) := by
  refine wp_ldloc hp h.inv (d := tmpOff) (by decide) fun s₂ u₂ => wp_ldarg hp (h.inv.upd u₂ (by decide)
    (by decide)) (i := 15) (by decide) fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_addi fun s₅ u₅ => WP.block_nil
    ⟨(((h.inv.upd u₂ (by decide) (by decide)).upd u₃ (by decide) (by decide)).upd u₄ (by decide)
      (by decide)).upd u₅ (by decide) (by decide), ?_, ?_, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  · rw [u₅.gpr, u₄.gpr, u₃.gpr]; rfl
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), ha]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, htmp]

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : VG.Proof.Argon2.X86.Derive.Two s₀₁ s₀₂)
include T

/-- `fillCompress` leaks the same trace in two runs at the same position and
with the same reference block. -/
theorem fillCompress_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} (hl : lane < lanesN s₀₁)
    (hs : slice < 4) (hi : index < (prm s₀₁).segmentLen) {R : Nat} (hR : R < blocksN s₀₁) :
    RelCT isa (fun s₁ s₂ => (VG.Proof.Argon2.X86.Derive.FS s₀₁ pass slice lane index ctr st₁ s₁ ∧
        lw s₀₁ s₁ tmpOff = memP s₀₁ + BitVec.ofNat 32 (R * 1024)) ∧
      (VG.Proof.Argon2.X86.Derive.FS s₀₂ pass slice lane index ctr st₂ s₂ ∧ lw s₀₂ s₂ tmpOff = memP s₀₂ + BitVec.ofNat 32 (R * 1024)))
      Impl.Argon2.X86.Derive.fillCompress fun _ _ => True := by
  have pe := T.pb.prm_eq
  have hi₂ : index < (prm s₀₂).segmentLen := pe ▸ hi
  have hl₂ : lane < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  have hR₂ : R < blocksN s₀₂ := T.pb.blocksN_eq ▸ hR
  have L8 := VG.Proof.Argon2.X86.Derive.laneLen_ge T.hp₁
  obtain ⟨cl, _⟩ := VG.Proof.Argon2.X86.Derive.cell_fits T.hp₁ hl (col := (slice * (prm s₀₁).segmentLen + index + (prm s₀₁).laneLen - 1) %
    (prm s₀₁).laneLen) (Nat.mod_lt _ (by omega))
  have L8₂ := VG.Proof.Argon2.X86.Derive.laneLen_ge T.hp₂
  obtain ⟨cl₂, _⟩ := VG.Proof.Argon2.X86.Derive.cell_fits T.hp₂ hl₂ (col := (slice * (prm s₀₂).segmentLen + index + (prm s₀₂).laneLen - 1) %
    (prm s₀₂).laneLen) (Nat.mod_lt _ (by omega))
  unfold Impl.Argon2.X86.Derive.fillCompress
  refine RelCT.seq (HPrime.rel_wp ((T.prevPointer_rel hs hi).mono (fun _ _ h => ⟨h.1.1.w, h.2.1.w⟩)
      fun _ _ h => h)
    (G₁ := fun t => VG.Proof.Argon2.X86.Derive.W s₀₁ pass slice lane index ctr t ∧ t.gpr .eax = memP s₀₁ + BitVec.ofNat 32
      ((lane * (prm s₀₁).laneLen + (slice * (prm s₀₁).segmentLen + index + (prm s₀₁).laneLen - 1) %
        (prm s₀₁).laneLen) * 1024) ∧ lw s₀₁ t tmpOff = memP s₀₁ + BitVec.ofNat 32 (R * 1024))
    (G₂ := fun t => VG.Proof.Argon2.X86.Derive.W s₀₂ pass slice lane index ctr t ∧ t.gpr .eax = memP s₀₂ + BitVec.ofNat 32
      ((lane * (prm s₀₂).laneLen + (slice * (prm s₀₂).segmentLen + index + (prm s₀₂).laneLen - 1) %
        (prm s₀₂).laneLen) * 1024) ∧ lw s₀₂ t tmpOff = memP s₀₂ + BitVec.ofNat 32 (R * 1024))
    (fun s h => (VG.Proof.Argon2.X86.Derive.prevPointer_ok T.hp₁ h.1.inv h.1.pr h.1.pos hl hs hi).mono fun t ⟨a, k⟩ =>
      ⟨h.1.w.of_keep k, a, by rw [lw_mem k.mem]; exact h.2⟩)
    (fun s h => (VG.Proof.Argon2.X86.Derive.prevPointer_ok T.hp₂ h.1.inv h.1.pr h.1.pos hl₂ hs hi₂).mono fun t ⟨a, k⟩ =>
      ⟨h.1.w.of_keep k, a, by rw [lw_mem k.mem]; exact h.2⟩)) ?_
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1, h.2.1⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.X86.Derive.fcBlk_ok T.hp₁ h.1 h.2.1 h.2.2) (fun s h => VG.Proof.Argon2.X86.Derive.fcBlk_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  refine T.ccall_rel (o := 4096) (by decide) (by decide) fun s₁ s₂ ⟨i₁, d₁, c₁, a₁, e₁⟩ ⟨i₂, d₂, c₂, a₂, e₂⟩ =>
    ⟨⟨i₁, d₁, c₁, by rw [a₁]; exact .inl ⟨_, cl, rfl⟩, by rw [e₁]; exact .inl ⟨R, hR, rfl⟩⟩,
     ⟨i₂, d₂, c₂, by rw [a₂]; exact .inl ⟨_, cl₂, rfl⟩, by rw [e₂]; exact .inl ⟨R, hR₂, rfl⟩⟩,
     by rw [a₁, a₂, pe, T.pb.memP_eq], by rw [e₁, e₂, T.pb.memP_eq]⟩

/-- `fillWrite` leaks the same trace in two runs at the same position. -/
theorem fillWrite_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} :
    RelCT isa (fun s₁ s₂ => (VG.Proof.Argon2.X86.Derive.FS s₀₁ pass slice lane index ctr st₁ s₁ ∧ VG.Proof.Argon2.X86.Derive.FS s₀₂ pass slice lane index ctr st₂ s₂) ∧
      lw s₀₁ s₁ curOff = lw s₀₂ s₂ curOff) Impl.Argon2.X86.Derive.fillWrite fun _ _ => True :=
  T.leafX [] [curOff] (by decide) (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1.w, h.1.2.w⟩, by simp, by
    simp only [List.mem_singleton, forall_eq]; exact h.2⟩) ⟨_, by taint_decide⟩

end Two

namespace Two
variable {s₀₁ s₀₂ : State} (T : VG.Proof.Argon2.X86.Derive.Two s₀₁ s₀₂)
include T

/-- `fillBlock` leaks the same trace in two runs at the same position whose
reference blocks agree. -/
theorem fillBlock_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} (hpass : pass < 2 ^ 32)
    (hl : lane < lanesN s₀₁) (hs : slice < 4) (hi : index < (prm s₀₁).segmentLen)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index)
    (href : Spec.Argon2.reference (prm s₀₁) pass lane slice index
        (Proof.Argon2.FillStep.random (prm s₀₁) pass lane slice index st₁.memory) =
      Spec.Argon2.reference (prm s₀₂) pass lane slice index
        (Proof.Argon2.FillStep.random (prm s₀₂) pass lane slice index st₂.memory)) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.Derive.FS s₀₁ pass slice lane index ctr st₁ s₁ ∧ VG.Proof.Argon2.X86.Derive.FS s₀₂ pass slice lane index ctr st₂ s₂)
      Impl.Argon2.X86.Derive.fillBlock fun _ _ => True := by
  have pe := T.pb.prm_eq
  have hi₂ : index < (prm s₀₂).segmentLen := pe ▸ hi
  have hl₂ : lane < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  have hb₁ : blocksN s₀₁ = (prm s₀₁).blocks := T.hp₁.blocks
  have refLt := Proof.Argon2.reference_cell_lt (prm s₀₁) T.hp₁.lanes_pos T.hp₁.memory_ge pass lane slice index
    (Proof.Argon2.FillStep.random (prm s₀₁) pass lane slice index st₁.memory) hl
  simp only at refLt
  generalize hR : (Spec.Argon2.reference (prm s₀₁) pass lane slice index
      (Proof.Argon2.FillStep.random (prm s₀₁) pass lane slice index st₁.memory)).1 * (prm s₀₁).laneLen +
    (Spec.Argon2.reference (prm s₀₁) pass lane slice index
      (Proof.Argon2.FillStep.random (prm s₀₁) pass lane slice index st₁.memory)).2 = R at refLt
  have hR₂ : (Spec.Argon2.reference (prm s₀₂) pass lane slice index
      (Proof.Argon2.FillStep.random (prm s₀₂) pass lane slice index st₂.memory)).1 * (prm s₀₂).laneLen +
    (Spec.Argon2.reference (prm s₀₂) pass lane slice index
      (Proof.Argon2.FillStep.random (prm s₀₂) pass lane slice index st₂.memory)).2 = R := by
    rw [← href, ← pe]; exact hR
  generalize hC : lane * (prm s₀₁).laneLen + (slice * (prm s₀₁).segmentLen + index) = C
  have hC₂ : lane * (prm s₀₂).laneLen + (slice * (prm s₀₂).segmentLen + index) = C := by rw [← pe]; exact hC
  unfold Impl.Argon2.X86.Derive.fillBlock
  refine RelCT.seqW (T.randomSource_rel hpass hl hs hi)
    (fun s h => VG.Proof.Argon2.X86.Derive.randomSource_ok T.hp₁ h hpass hl hs hi) (fun s h => VG.Proof.Argon2.X86.Derive.randomSource_ok T.hp₂ h hpass hl₂ hs hi₂) ?_
  refine RelCT.seq (HPrime.rel_wp (G₁ := fun t =>
      VG.Proof.Argon2.X86.Derive.FS s₀₁ pass slice lane index (VG.Proof.Argon2.X86.Derive.ctrNext (prm s₀₁) pass slice index ctr) st₁ t ∧
      lw s₀₁ t tmpOff = memP s₀₁ + BitVec.ofNat 32 (R * 1024) ∧
      lw s₀₁ t curOff = memP s₀₁ + BitVec.ofNat 32 (C * 1024))
    (G₂ := fun t => VG.Proof.Argon2.X86.Derive.FS s₀₂ pass slice lane index (VG.Proof.Argon2.X86.Derive.ctrNext (prm s₀₂) pass slice index ctr) st₂ t ∧
      lw s₀₂ t tmpOff = memP s₀₂ + BitVec.ofNat 32 (R * 1024) ∧
      lw s₀₂ t curOff = memP s₀₂ + BitVec.ofNat 32 (C * 1024))
    (RelCT.of_eq fun s₁ s₂ ⟨g₁, g₂⟩ => (T.reference_rel hpass hs (J1 := lw s₀₁ s₁ j1Off) (J2 := lw s₀₁ s₁ j2Off)
      (J1' := lw s₀₂ s₂ j1Off) (J2' := lw s₀₂ s₂ j2Off)).mono (fun a b ⟨ha, hb⟩ => by
        subst ha hb
        rw [← pe] at g₂
        exact ⟨⟨g₁.1, rfl, rfl⟩, ⟨g₂.1, rfl, rfl⟩⟩) fun _ _ h => h)
    (fun s g => (VG.Proof.Argon2.X86.Derive.reference_ok T.hp₁ ⟨g.1, rfl, rfl⟩ hpass hl hs hi active).mono fun t ⟨r, tmp, cur⟩ =>
      ⟨r.fs, by rw [tmp, g.2, hR], by rw [cur, hC]⟩)
    (fun s g => (VG.Proof.Argon2.X86.Derive.reference_ok T.hp₂ ⟨g.1, rfl, rfl⟩ hpass hl₂ hs hi₂ active).mono fun t ⟨r, tmp, cur⟩ =>
      ⟨r.fs, by rw [tmp, g.2, hR₂], by rw [cur, hC₂]⟩)) ?_
  rw [show VG.Proof.Argon2.X86.Derive.ctrNext (prm s₀₂) pass slice index ctr = VG.Proof.Argon2.X86.Derive.ctrNext (prm s₀₁) pass slice index ctr by rw [pe]]
  refine RelCT.seq (HPrime.rel_wp (G₁ := fun t =>
      VG.Proof.Argon2.X86.Derive.FS s₀₁ pass slice lane index (VG.Proof.Argon2.X86.Derive.ctrNext (prm s₀₁) pass slice index ctr) st₁ t ∧
      lw s₀₁ t curOff = memP s₀₁ + BitVec.ofNat 32 (C * 1024))
    (G₂ := fun t => VG.Proof.Argon2.X86.Derive.FS s₀₂ pass slice lane index (VG.Proof.Argon2.X86.Derive.ctrNext (prm s₀₁) pass slice index ctr) st₂ t ∧
      lw s₀₂ t curOff = memP s₀₂ + BitVec.ofNat 32 (C * 1024))
    ((T.fillCompress_rel hl hs hi (by rw [hb₁]; exact refLt)).mono
      (fun _ _ h => ⟨⟨h.1.1, h.1.2.1⟩, ⟨h.2.1, h.2.2.1⟩⟩) fun _ _ h => h)
    (fun s g => (VG.Proof.Argon2.X86.Derive.fillCompress_ok T.hp₁ g.1 hl hs hi (by rw [hb₁]; exact refLt) g.2.1).mono
      fun t ⟨f, l, _⟩ => ⟨f, by rw [l _ (by decide), g.2.2]⟩)
    (fun s g => (VG.Proof.Argon2.X86.Derive.fillCompress_ok T.hp₂ g.1 hl₂ hs hi₂ (by rw [← T.pb.blocksN_eq, hb₁]; exact refLt) g.2.1).mono
      fun t ⟨f, l, _⟩ => ⟨f, by rw [l _ (by decide), g.2.2]⟩)) ?_
  exact T.fillWrite_rel.mono (fun _ _ h => ⟨⟨h.1.1, h.2.1⟩, by rw [h.1.2, h.2.2, T.pb.memP_eq]⟩) fun _ _ h => h

end Two

end VG.Proof.Argon2.X86.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.Derive.FillCT3`. -/
section

/-!
# Argon2 on x86 (32-bit): the filling loops, in two runs

The loops run in lockstep in two runs with the same public data: their
positions and counters agree, and so do the indices of the data-dependent
references still to be made (the rest of `Spec.Argon2.references`), from
which each block's reference agrees (`ref_same`). `passes_rel`: the filling
loops leak the same trace in two runs whose references agree.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.Spec.Argon2 (FillState)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  divisorOff strideOff)

/-- A block's reference, in two runs whose references from it on agree. -/
theorem ref_same (p : Spec.Argon2.Params) (pass lane slice i count : Nat) (X₁ X₂ : FillState)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ i)
    (h : (Proof.Argon2.segment p pass lane slice i (count + 1) X₁).indices =
      (Proof.Argon2.segment p pass lane slice i (count + 1) X₂).indices) :
    Spec.Argon2.reference p pass lane slice i (Proof.Argon2.FillStep.random p pass lane slice i X₁.memory) =
      Spec.Argon2.reference p pass lane slice i (Proof.Argon2.FillStep.random p pass lane slice i X₂.memory) := by
  cases hind : Spec.Argon2.independent p pass slice
  · exact Proof.Argon2.segment_first_reference p pass lane slice i count X₁ X₂ active h hind
  · unfold Proof.Argon2.FillStep.random
    rw [hind]
    rfl

/-- The words of the locals a lane's state fixes. -/
abbrev wsL : List Nat := [72, 76, 80, 92, 96, 100, 132]

theorem slotsOkL : VG.X86.Taint.SlotsOk (VG.Proof.Argon2.X86.Derive.τB [(0, 72, 12), (0, 92, 12), (0, 132, 4)]) := by
  intro x hx
  simp only [VG.Proof.Argon2.X86.Derive.τB, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp [VG.Proof.Argon2.X86.Derive.τB]

namespace Two
variable {s₀₁ s₀₂ : State} (T : VG.Proof.Argon2.X86.Derive.Two s₀₁ s₀₂)
include T

theorem wordsL {st₁ st₂ : FillState} {pass slice lane : Nat} {s₁ s₂ : State}
    (h₁ : VG.Proof.Argon2.X86.Derive.LS s₀₁ st₁ pass slice lane s₁) (h₂ : VG.Proof.Argon2.X86.Derive.LS s₀₂ st₂ pass slice lane s₂) :
    ∀ d ∈ VG.Proof.Argon2.X86.Derive.wsL, lw s₀₁ s₁ d = lw s₀₂ s₂ d := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  intro d hd
  simp only [VG.Proof.Argon2.X86.Derive.wsL, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁.pass.trans h₂.pass.symm
  · exact h₁.lane.trans h₂.lane.symm
  · exact h₁.slice.trans h₂.slice.symm
  · exact (h₁.fb.pr.laneLen.trans (congrArg (fun p : Spec.Argon2.Params => BitVec.ofNat 32 p.laneLen) pe)).trans
      h₂.fb.pr.laneLen.symm
  · exact (h₁.fb.pr.stride.trans
      (congrArg (fun p : Spec.Argon2.Params => BitVec.ofNat 32 (p.laneLen * 1024)) pe)).trans h₂.fb.pr.stride.symm
  · exact (h₁.fb.pr.segLen.trans
      (congrArg (fun p : Spec.Argon2.Params => BitVec.ofNat 32 p.segmentLen) pe)).trans h₂.fb.pr.segLen.symm
  · exact (h₁.fb.pr.divisor.trans (congrArg (fun n : Nat => BitVec.ofNat 32 (4 * n)) le)).trans
      h₂.fb.pr.divisor.symm

/-- `segmentStart` leaks the same trace in two runs at the same lane. -/
theorem segmentStart_rel {pass slice lane : Nat} {st₁ st₂ : FillState} (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.Derive.LS s₀₁ st₁ pass slice lane s₁ ∧ VG.Proof.Argon2.X86.Derive.LS s₀₂ st₂ pass slice lane s₂)
      Impl.Argon2.X86.Derive.segmentStart fun _ _ => True := by
  unfold Impl.Argon2.X86.Derive.segmentStart
  refine RelCT.seq (T.leaf VG.Proof.Argon2.X86.Derive.wsL [(0, 72, 12), (0, 92, 12), (0, 132, 4)] [] VG.Proof.Argon2.X86.Derive.slotsOkL (by decide)
      (fun s₁ s₂ h₁ h₂ => ⟨h₁.fb.inv, h₂.fb.inv, T.wordsL h₁ h₂, by simp⟩) ⟨_, by taint_decide⟩
      (fun s h => VG.Proof.Argon2.X86.Derive.segStartBlk_ok T.hp₁ h hpass hs) (fun s h => VG.Proof.Argon2.X86.Derive.segStartBlk_ok T.hp₂ h hpass hs)) ?_
  refine RelCT.iteF (fun s₁ s₂ h₁ h₂ => by
      show s₁.zf = s₂.zf
      rw [h₁.2.2, h₂.2.2])
    (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1.fb.inv, h.2.1.fb.inv, by simp⟩) ⟨_, by taint_decide⟩)
    (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1.fb.inv, h.2.1.fb.inv, by simp⟩) ⟨_, by taint_decide⟩)

/-- A block of a segment and the index advanced, in two runs at the same
position whose reference blocks agree. -/
theorem segBody_rel {pass slice lane i c : Nat} {X₁ X₂ : FillState} (hpass : pass < 2 ^ 32)
    (hl : lane < lanesN s₀₁) (hs : slice < 4) (hi : i < (prm s₀₁).segmentLen)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ i)
    (href : Spec.Argon2.reference (prm s₀₁) pass lane slice i
        (Proof.Argon2.FillStep.random (prm s₀₁) pass lane slice i X₁.memory) =
      Spec.Argon2.reference (prm s₀₂) pass lane slice i
        (Proof.Argon2.FillStep.random (prm s₀₂) pass lane slice i X₂.memory)) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.Derive.FS s₀₁ pass slice lane i c X₁ s₁ ∧ VG.Proof.Argon2.X86.Derive.FS s₀₂ pass slice lane i c X₂ s₂)
      (.seq Impl.Argon2.X86.Derive.fillBlock
        (.block (Impl.Argon2.X86.Derive.advance indexOff (Impl.Argon2.X86.Derive.fr segLenOff))))
      fun v₁ v₂ => (VG.Proof.Argon2.X86.Derive.FS s₀₁ pass slice lane (i + 1) (VG.Proof.Argon2.X86.Derive.ctrNext (prm s₀₁) pass slice i c)
          (Spec.Argon2.fillBlock (prm s₀₁) pass slice lane i X₁) v₁ ∧
          v₁.cf = some (decide (i + 1 < (prm s₀₁).segmentLen))) ∧
        (VG.Proof.Argon2.X86.Derive.FS s₀₂ pass slice lane (i + 1) (VG.Proof.Argon2.X86.Derive.ctrNext (prm s₀₂) pass slice i c)
          (Spec.Argon2.fillBlock (prm s₀₂) pass slice lane i X₂) v₂ ∧
          v₂.cf = some (decide (i + 1 < (prm s₀₂).segmentLen))) := by
  have pe := T.pb.prm_eq
  have hi₂ : i < (prm s₀₂).segmentLen := pe ▸ hi
  have hl₂ : lane < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  refine HPrime.rel_wp (RelCT.seqW (T.fillBlock_rel hpass hl hs hi active href)
    (fun s h => VG.Proof.Argon2.X86.Derive.fillBlock_ok T.hp₁ h hpass hl hs hi active)
    (fun s h => VG.Proof.Argon2.X86.Derive.fillBlock_ok T.hp₂ h hpass hl₂ hs hi₂ active)
    (T.leafF [] (fun s₁ s₂ h => by
      have h₂ := h.2
      rw [← pe] at h₂
      exact ⟨⟨_, _, _, _, _, h.1.w, h₂.w⟩, by simp⟩) ⟨_, by taint_decide⟩))
    (fun s h => VG.Proof.Argon2.X86.Derive.segStep_ok T.hp₁ h hpass hl hs hi active) (fun s h => VG.Proof.Argon2.X86.Derive.segStep_ok T.hp₂ h hpass hl₂ hs hi₂ active)

/-- `segment` leaks the same trace in two runs at the same lane whose
references in it agree. -/
theorem segment_rel {pass slice lane : Nat} {st₁ st₂ : FillState} (hpass : pass < 2 ^ 32) (hs : slice < 4)
    (hl : lane < lanesN s₀₁)
    (hind : (Proof.Argon2.segment (prm s₀₁) pass lane slice 0 (prm s₀₁).segmentLen st₁).indices =
      (Proof.Argon2.segment (prm s₀₁) pass lane slice 0 (prm s₀₁).segmentLen st₂).indices) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.Derive.LS s₀₁ st₁ pass slice lane s₁ ∧ VG.Proof.Argon2.X86.Derive.LS s₀₂ st₂ pass slice lane s₂)
      Impl.Argon2.X86.Derive.segment fun _ _ => True := by
  have pe := T.pb.prm_eq
  have hl₂ : lane < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  have s2 := T.hp₁.segLen_two
  have hS : Proof.Argon2.segmentStart pass slice ≤ 2 := by unfold Proof.Argon2.segmentStart; split <;> omega
  have hS2 : pass = 0 → slice = 0 → Proof.Argon2.segmentStart pass slice = 2 := fun a b => by
    unfold Proof.Argon2.segmentStart; rw [ite_eq_left ⟨a, b⟩]
  rw [Proof.Argon2.segment_start _ _ _ _ _ s2, Proof.Argon2.segment_start _ _ _ _ _ s2] at hind
  generalize hSd : Proof.Argon2.segmentStart pass slice = S at hS hS2 hind
  generalize hL : (prm s₀₁).segmentLen = L at hind s2
  have hL₂ : (prm s₀₂).segmentLen = L := by rw [← pe, hL]
  unfold Impl.Argon2.X86.Derive.segment
  refine RelCT.seq (HPrime.rel_wp (T.segmentStart_rel hpass hs)
    (fun s h => VG.Proof.Argon2.X86.Derive.segmentStart_ok T.hp₁ h hpass hs) (fun s h => VG.Proof.Argon2.X86.Derive.segmentStart_ok T.hp₂ h hpass hs)) ?_
  rw [hSd]
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.w, h.2.w⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.X86.Derive.segCmp_ok T.hp₁ h hS) (fun s h => VG.Proof.Argon2.X86.Derive.segCmp_ok T.hp₂ h hS) ?_
  refine RelCT.ite (fun s₁ s₂ h => by
      show s₁.cf = s₂.cf
      rw [h.1.2, h.2.2, hL, hL₂]) ?_ ((RelCT.nil fun _ _ _ => trivial))
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ i, n = L - i ∧ S ≤ i ∧ i < L ∧ ∃ c,
      VG.Proof.Argon2.X86.Derive.FS s₀₁ pass slice lane i c (Proof.Argon2.segment (prm s₀₁) pass lane slice S (i - S) st₁) s₁ ∧
      VG.Proof.Argon2.X86.Derive.FS s₀₂ pass slice lane i c (Proof.Argon2.segment (prm s₀₁) pass lane slice S (i - S) st₂) s₂ ∧
      (Proof.Argon2.segment (prm s₀₁) pass lane slice i (L - i)
          (Proof.Argon2.segment (prm s₀₁) pass lane slice S (i - S) st₁)).indices =
        (Proof.Argon2.segment (prm s₀₁) pass lane slice i (L - i)
          (Proof.Argon2.segment (prm s₀₁) pass lane slice S (i - S) st₂)).indices) ?step (L - S)).mono
    (fun s₁ s₂ ⟨⟨⟨h₁, c₁⟩, ⟨h₂, _⟩⟩, e⟩ => ?init) fun _ _ h => h
  case init =>
    have hb : S < L := by
      rw [show isa.eval .b s₁ = s₁.cf from rfl, c₁, hL] at e
      simpa using e
    exact ⟨S, rfl, Nat.le_refl _, hb, 0, by rw [Nat.sub_self]; exact h₁, by rw [Nat.sub_self]; exact h₂,
      by rw [Nat.sub_self]; exact hind⟩
  case step =>
    intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨i, hn, hSi, hi, c, h₁, h₂, hidx⟩ e₁ e₂
    have active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ i := by
      by_cases a : pass = 0
      · by_cases b : slice = 0
        · have := hS2 a b; omega
        · exact .inr (.inl b)
      · exact .inl a
    rw [show L - i = (L - (i + 1)) + 1 by omega] at hidx
    have href := VG.Proof.Argon2.X86.Derive.ref_same (prm s₀₁) pass lane slice i (L - (i + 1)) _ _ active hidx
    rw [Proof.Argon2.segment_succ, Proof.Argon2.segment_succ] at hidx
    obtain ⟨ht, ⟨g₁, c₁⟩, ⟨g₂, c₂⟩⟩ := T.segBody_rel (c := c) hpass hl hs (by rw [hL]; exact hi) active
      (by rw [← pe]; exact href) s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
    rw [← pe] at g₂ c₂
    have eq₁ : ∀ X, Proof.Argon2.segment (prm s₀₁) pass lane slice S (i + 1 - S) X =
        Spec.Argon2.fillBlock (prm s₀₁) pass slice lane i (Proof.Argon2.segment (prm s₀₁) pass lane slice S (i - S) X) :=
      fun X => by rw [show i + 1 - S = (i - S) + 1 by omega, VG.Proof.Argon2.X86.Derive.segment_snoc, show S + (i - S) = i by omega]
    rw [← eq₁] at g₁ g₂ hidx
    rw [← eq₁] at hidx
    rw [hL] at c₁ c₂
    refine ⟨ht, by show s₁'.cf = s₂'.cf; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
    have e : i + 1 < L := by
      rw [show isa.eval .b s₁' = s₁'.cf from rfl, c₁] at hc
      simpa using hc
    exact ⟨L - (i + 1), by omega, i + 1, rfl, by omega, e, _, g₁, g₂, hidx⟩

end Two

namespace Two
variable {s₀₁ s₀₂ : State} (T : VG.Proof.Argon2.X86.Derive.Two s₀₁ s₀₂)
include T

/-- A lane's segment and the lane advanced, in two runs. -/
theorem laneBody_rel {pass slice l : Nat} {X₁ X₂ : FillState} (hpass : pass < 2 ^ 32) (hs : slice < 4)
    (hl : l < lanesN s₀₁)
    (hind : (Proof.Argon2.segment (prm s₀₁) pass l slice 0 (prm s₀₁).segmentLen X₁).indices =
      (Proof.Argon2.segment (prm s₀₁) pass l slice 0 (prm s₀₁).segmentLen X₂).indices) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.Derive.LS s₀₁ X₁ pass slice l s₁ ∧ VG.Proof.Argon2.X86.Derive.LS s₀₂ X₂ pass slice l s₂)
      (.seq Impl.Argon2.X86.Derive.segment
        (.block (Impl.Argon2.X86.Derive.advance laneOff (Impl.Argon2.X86.Derive.fr (argOff 7)))))
      fun v₁ v₂ => (VG.Proof.Argon2.X86.Derive.LS s₀₁ (Proof.Argon2.segment (prm s₀₁) pass l slice 0 (prm s₀₁).segmentLen X₁) pass slice
          (l + 1) v₁ ∧ v₁.cf = some (decide (l + 1 < lanesN s₀₁))) ∧
        (VG.Proof.Argon2.X86.Derive.LS s₀₂ (Proof.Argon2.segment (prm s₀₂) pass l slice 0 (prm s₀₂).segmentLen X₂) pass slice (l + 1) v₂ ∧
          v₂.cf = some (decide (l + 1 < lanesN s₀₂))) := by
  have hl₂ : l < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  exact HPrime.rel_wp (RelCT.seqW (T.segment_rel hpass hs hl hind)
    (fun s h => VG.Proof.Argon2.X86.Derive.segment_ok T.hp₁ h hpass hs hl) (fun s h => VG.Proof.Argon2.X86.Derive.segment_ok T.hp₂ h hpass hs hl₂)
    (T.leafI [] (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, by simp⟩) ⟨_, by taint_decide⟩))
    (fun s h => VG.Proof.Argon2.X86.Derive.laneStep_ok T.hp₁ h hpass hs hl) (fun s h => VG.Proof.Argon2.X86.Derive.laneStep_ok T.hp₂ h hpass hs hl₂)

/-- `lanesLoop` leaks the same trace in two runs at the same slice whose
references in it agree. -/
theorem lanes_rel {pass slice : Nat} {Y₁ Y₂ : FillState} (hpass : pass < 2 ^ 32) (hs : slice < 4)
    (hind : (Proof.Argon2.lanes (prm s₀₁) pass slice 0 (lanesN s₀₁) Y₁).indices =
      (Proof.Argon2.lanes (prm s₀₁) pass slice 0 (lanesN s₀₁) Y₂).indices) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.Derive.SS s₀₁ Y₁ pass slice s₁ ∧ VG.Proof.Argon2.X86.Derive.SS s₀₂ Y₂ pass slice s₂)
      Impl.Argon2.X86.Derive.lanesLoop fun _ _ => True := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  have hl1 := T.hp₁.lanes_pos
  have s2 := T.hp₁.segLen_two
  unfold Impl.Argon2.X86.Derive.lanesLoop
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => (VG.Proof.Argon2.X86.Derive.setLocal_ok T.hp₁ h.fb (d := laneOff) (by decide) (by decide) 0).mono fun t ⟨f, v, o⟩ =>
      (⟨f, by rw [o _ (by decide) (by decide)]; exact h.pass, by rw [o _ (by decide) (by decide)]; exact h.slice,
        v⟩ : VG.Proof.Argon2.X86.Derive.LS s₀₁ Y₁ pass slice 0 t))
    (fun s h => (VG.Proof.Argon2.X86.Derive.setLocal_ok T.hp₂ h.fb (d := laneOff) (by decide) (by decide) 0).mono fun t ⟨f, v, o⟩ =>
      (⟨f, by rw [o _ (by decide) (by decide)]; exact h.pass, by rw [o _ (by decide) (by decide)]; exact h.slice,
        v⟩ : VG.Proof.Argon2.X86.Derive.LS s₀₂ Y₂ pass slice 0 t)) ?_
  generalize hN : lanesN s₀₁ = N at hind hl1
  have hN₂ : lanesN s₀₂ = N := by rw [← le, hN]
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ l, n = N - l ∧ l < N ∧
      VG.Proof.Argon2.X86.Derive.LS s₀₁ (Proof.Argon2.lanes (prm s₀₁) pass slice 0 l Y₁) pass slice l s₁ ∧
      VG.Proof.Argon2.X86.Derive.LS s₀₂ (Proof.Argon2.lanes (prm s₀₁) pass slice 0 l Y₂) pass slice l s₂ ∧
      (Proof.Argon2.lanes (prm s₀₁) pass slice l (N - l) (Proof.Argon2.lanes (prm s₀₁) pass slice 0 l Y₁)).indices =
        (Proof.Argon2.lanes (prm s₀₁) pass slice l (N - l) (Proof.Argon2.lanes (prm s₀₁) pass slice 0 l Y₂)).indices)
    ?step N).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, by omega, hl1, h.1, h.2, hind⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨l, hn, hl, h₁, h₂, hidx⟩ e₁ e₂
  rw [show N - l = (N - (l + 1)) + 1 by omega] at hidx
  have hseg := Proof.Argon2.lanes_first_segment (prm s₀₁) pass slice l (N - (l + 1)) _ _ s2 hidx
  rw [Proof.Argon2.lanes_succ, Proof.Argon2.lanes_succ] at hidx
  obtain ⟨ht, ⟨g₁, c₁⟩, ⟨g₂, c₂⟩⟩ := T.laneBody_rel hpass hs (by rw [hN]; exact hl) hseg
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
  rw [← pe] at g₂
  have eq : ∀ X, Proof.Argon2.segment (prm s₀₁) pass l slice 0 (prm s₀₁).segmentLen
      (Proof.Argon2.lanes (prm s₀₁) pass slice 0 l X) = Proof.Argon2.lanes (prm s₀₁) pass slice 0 (l + 1) X :=
    fun X => by unfold Proof.Argon2.lanes; rw [VG.Proof.Argon2.X86.Derive.foldl_range'_snoc, Nat.zero_add]
  rw [eq] at g₁ g₂ hidx
  rw [eq] at hidx
  rw [hN] at c₁
  rw [hN₂] at c₂
  refine ⟨ht, by show s₁'.cf = s₂'.cf; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  have e : l + 1 < N := by
    rw [show isa.eval .b s₁' = s₁'.cf from rfl, c₁] at hc
    simpa using hc
  exact ⟨N - (l + 1), by omega, l + 1, rfl, e, g₁, g₂, hidx⟩

/-- A slice's lanes and the slice advanced, in two runs. -/
theorem sliceBody_rel {pass j : Nat} {X₁ X₂ : FillState} (hpass : pass < 2 ^ 32) (hj : j < 4)
    (hind : (Proof.Argon2.lanes (prm s₀₁) pass j 0 (lanesN s₀₁) X₁).indices =
      (Proof.Argon2.lanes (prm s₀₁) pass j 0 (lanesN s₀₁) X₂).indices) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.Derive.SS s₀₁ X₁ pass j s₁ ∧ VG.Proof.Argon2.X86.Derive.SS s₀₂ X₂ pass j s₂)
      (.seq Impl.Argon2.X86.Derive.lanesLoop (.block (Impl.Argon2.X86.Derive.advance sliceOff (.imm 4))))
      fun v₁ v₂ => (VG.Proof.Argon2.X86.Derive.SS s₀₁ (Proof.Argon2.lanes (prm s₀₁) pass j 0 (lanesN s₀₁) X₁) pass (j + 1) v₁ ∧
          v₁.cf = some (decide (j + 1 < 4))) ∧
        (VG.Proof.Argon2.X86.Derive.SS s₀₂ (Proof.Argon2.lanes (prm s₀₂) pass j 0 (lanesN s₀₂) X₂) pass (j + 1) v₂ ∧
          v₂.cf = some (decide (j + 1 < 4))) :=
  HPrime.rel_wp (RelCT.seqW (T.lanes_rel hpass hj hind)
    (fun s h => VG.Proof.Argon2.X86.Derive.lanes_ok T.hp₁ h hpass hj) (fun s h => VG.Proof.Argon2.X86.Derive.lanes_ok T.hp₂ h hpass hj)
    (T.leafI [] (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, by simp⟩) ⟨_, by taint_decide⟩))
    (fun s h => VG.Proof.Argon2.X86.Derive.sliceStep_ok T.hp₁ h hpass hj) (fun s h => VG.Proof.Argon2.X86.Derive.sliceStep_ok T.hp₂ h hpass hj)

/-- `slicesLoop` leaks the same trace in two runs at the same pass whose
references in it agree. -/
theorem slices_rel {pass : Nat} {Z₁ Z₂ : FillState} (hpass : pass < 2 ^ 32)
    (hind : (Proof.Argon2.slices (prm s₀₁) pass 0 4 Z₁).indices =
      (Proof.Argon2.slices (prm s₀₁) pass 0 4 Z₂).indices) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.Derive.PS s₀₁ Z₁ pass s₁ ∧ VG.Proof.Argon2.X86.Derive.PS s₀₂ Z₂ pass s₂)
      Impl.Argon2.X86.Derive.slicesLoop fun _ _ => True := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  have s2 := T.hp₁.segLen_two
  unfold Impl.Argon2.X86.Derive.slicesLoop
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => (VG.Proof.Argon2.X86.Derive.setLocal_ok T.hp₁ h.fb (d := sliceOff) (by decide) (by decide) 0).mono fun t ⟨f, v, o⟩ =>
      (⟨f, by rw [o _ (by decide) (by decide)]; exact h.pass, v⟩ : VG.Proof.Argon2.X86.Derive.SS s₀₁ Z₁ pass 0 t))
    (fun s h => (VG.Proof.Argon2.X86.Derive.setLocal_ok T.hp₂ h.fb (d := sliceOff) (by decide) (by decide) 0).mono fun t ⟨f, v, o⟩ =>
      (⟨f, by rw [o _ (by decide) (by decide)]; exact h.pass, v⟩ : VG.Proof.Argon2.X86.Derive.SS s₀₂ Z₂ pass 0 t)) ?_
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ j, n = 4 - j ∧ j < 4 ∧
      VG.Proof.Argon2.X86.Derive.SS s₀₁ (Proof.Argon2.slices (prm s₀₁) pass 0 j Z₁) pass j s₁ ∧
      VG.Proof.Argon2.X86.Derive.SS s₀₂ (Proof.Argon2.slices (prm s₀₁) pass 0 j Z₂) pass j s₂ ∧
      (Proof.Argon2.slices (prm s₀₁) pass j (4 - j) (Proof.Argon2.slices (prm s₀₁) pass 0 j Z₁)).indices =
        (Proof.Argon2.slices (prm s₀₁) pass j (4 - j) (Proof.Argon2.slices (prm s₀₁) pass 0 j Z₂)).indices)
    ?step 4).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, rfl, by decide, h.1, h.2, hind⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨j, hn, hj, h₁, h₂, hidx⟩ e₁ e₂
  rw [show 4 - j = (3 - j) + 1 by omega] at hidx
  have hl := Proof.Argon2.slices_first_lane_fold (prm s₀₁) pass j (3 - j) _ _ s2 hidx
  rw [Proof.Argon2.slices_succ, Proof.Argon2.slices_succ] at hidx
  obtain ⟨ht, ⟨g₁, c₁⟩, ⟨g₂, c₂⟩⟩ := T.sliceBody_rel hpass hj hl s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
  rw [← pe, ← le] at g₂
  have eq : ∀ X, Proof.Argon2.lanes (prm s₀₁) pass j 0 (lanesN s₀₁) (Proof.Argon2.slices (prm s₀₁) pass 0 j X) =
      Proof.Argon2.slices (prm s₀₁) pass 0 (j + 1) X :=
    fun X => by unfold Proof.Argon2.slices; rw [VG.Proof.Argon2.X86.Derive.foldl_range'_snoc, Nat.zero_add]; rfl
  rw [eq] at g₁ g₂
  rw [show 3 - j = 4 - (j + 1) by omega] at hidx
  refine ⟨ht, by show s₁'.cf = s₂'.cf; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  have e : j + 1 < 4 := by
    rw [show isa.eval .b s₁' = s₁'.cf from rfl, c₁] at hc
    simpa using hc
  refine ⟨4 - (j + 1), by omega, j + 1, rfl, e, g₁, g₂, ?_⟩
  rw [← eq, ← eq]
  exact hidx

/-- A pass and the pass advanced, in two runs. -/
theorem passBody_rel {k : Nat} {X₁ X₂ : FillState} (hk : k < itersN s₀₁)
    (hind : (Spec.Argon2.fillPass (prm s₀₁) X₁ k).indices = (Spec.Argon2.fillPass (prm s₀₁) X₂ k).indices) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.Derive.PS s₀₁ X₁ k s₁ ∧ VG.Proof.Argon2.X86.Derive.PS s₀₂ X₂ k s₂)
      (.seq Impl.Argon2.X86.Derive.slicesLoop
        (.block (Impl.Argon2.X86.Derive.advance passOff (Impl.Argon2.X86.Derive.fr (argOff 5)))))
      fun v₁ v₂ => (VG.Proof.Argon2.X86.Derive.PS s₀₁ (Spec.Argon2.fillPass (prm s₀₁) X₁ k) (k + 1) v₁ ∧
          v₁.cf = some (decide (k + 1 < itersN s₀₁))) ∧
        (VG.Proof.Argon2.X86.Derive.PS s₀₂ (Spec.Argon2.fillPass (prm s₀₂) X₂ k) (k + 1) v₂ ∧ v₂.cf = some (decide (k + 1 < itersN s₀₂))) := by
  have hk₂ : k < itersN s₀₂ := T.pb.itersN_eq ▸ hk
  have hpl : itersN s₀₁ < 2 ^ 32 := (VG.X86.arg s₀₁ 5).isLt
  rw [← Proof.Argon2.slices_pass, ← Proof.Argon2.slices_pass] at hind
  exact HPrime.rel_wp (RelCT.seqW (T.slices_rel (by omega) hind)
    (fun s h => VG.Proof.Argon2.X86.Derive.slices_ok T.hp₁ h (by omega)) (fun s h => VG.Proof.Argon2.X86.Derive.slices_ok T.hp₂ h (by omega))
    (T.leafI [] (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, by simp⟩) ⟨_, by taint_decide⟩))
    (fun s h => VG.Proof.Argon2.X86.Derive.passStep_ok T.hp₁ h hk) (fun s h => VG.Proof.Argon2.X86.Derive.passStep_ok T.hp₂ h hk₂)

/-- `passesLoop` leaks the same trace in two runs whose references agree. -/
theorem passes_rel {W₁ W₂ : FillState}
    (hind : (Proof.Argon2.iterations (prm s₀₁) 0 (itersN s₀₁) W₁).indices =
      (Proof.Argon2.iterations (prm s₀₁) 0 (itersN s₀₁) W₂).indices) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.Derive.FB s₀₁ W₁ s₁ ∧ VG.Proof.Argon2.X86.Derive.FB s₀₂ W₂ s₂) Impl.Argon2.X86.Derive.passesLoop fun _ _ => True := by
  have pe := T.pb.prm_eq
  have ie := T.pb.itersN_eq
  have hp1 := T.hp₁.passes_pos
  have s2 := T.hp₁.segLen_two
  unfold Impl.Argon2.X86.Derive.passesLoop
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => (VG.Proof.Argon2.X86.Derive.setLocal_ok T.hp₁ h (d := passOff) (by decide) (by decide) 0).mono fun t ⟨f, v, _⟩ =>
      (⟨f, v⟩ : VG.Proof.Argon2.X86.Derive.PS s₀₁ W₁ 0 t))
    (fun s h => (VG.Proof.Argon2.X86.Derive.setLocal_ok T.hp₂ h (d := passOff) (by decide) (by decide) 0).mono fun t ⟨f, v, _⟩ =>
      (⟨f, v⟩ : VG.Proof.Argon2.X86.Derive.PS s₀₂ W₂ 0 t)) ?_
  generalize hN : itersN s₀₁ = N at hind hp1
  have hN₂ : itersN s₀₂ = N := by rw [← ie, hN]
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ k, n = N - k ∧ k < N ∧
      VG.Proof.Argon2.X86.Derive.PS s₀₁ (Proof.Argon2.iterations (prm s₀₁) 0 k W₁) k s₁ ∧
      VG.Proof.Argon2.X86.Derive.PS s₀₂ (Proof.Argon2.iterations (prm s₀₁) 0 k W₂) k s₂ ∧
      (Proof.Argon2.iterations (prm s₀₁) k (N - k) (Proof.Argon2.iterations (prm s₀₁) 0 k W₁)).indices =
        (Proof.Argon2.iterations (prm s₀₁) k (N - k) (Proof.Argon2.iterations (prm s₀₁) 0 k W₂)).indices)
    ?step N).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, by omega, by omega, h.1, h.2, hind⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨k, hn, hk, h₁, h₂, hidx⟩ e₁ e₂
  rw [show N - k = (N - (k + 1)) + 1 by omega] at hidx
  have hpass := Proof.Argon2.iterations_first_pass (prm s₀₁) k (N - (k + 1)) _ _ s2 hidx
  rw [Proof.Argon2.iterations_succ, Proof.Argon2.iterations_succ] at hidx
  obtain ⟨ht, ⟨g₁, c₁⟩, ⟨g₂, c₂⟩⟩ := T.passBody_rel (by rw [hN]; exact hk) hpass s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
  rw [← pe] at g₂
  have eq : ∀ X, Spec.Argon2.fillPass (prm s₀₁) (Proof.Argon2.iterations (prm s₀₁) 0 k X) k =
      Proof.Argon2.iterations (prm s₀₁) 0 (k + 1) X :=
    fun X => by unfold Proof.Argon2.iterations; rw [VG.Proof.Argon2.X86.Derive.foldl_range'_snoc, Nat.zero_add]
  rw [eq] at g₁ g₂ hidx
  rw [eq] at hidx
  rw [hN] at c₁
  rw [hN₂] at c₂
  refine ⟨ht, by show s₁'.cf = s₂'.cf; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  have e : k + 1 < N := by
    rw [show isa.eval .b s₁' = s₁'.cf from rfl, c₁] at hc
    simpa using hc
  exact ⟨N - (k + 1), by omega, k + 1, rfl, e, g₁, g₂, hidx⟩

end Two

end VG.Proof.Argon2.X86.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.Derive.InitialCT`. -/
section

/-!
# Argon2 on x86 (32-bit): H₀, in two runs

`code_rel`: H₀'s hash leaks the same trace in two runs with the same public
data. The BLAKE2b calls are related by H′'s macros' relations
(`HPrime.init_rel`, `update_rel`, `finalize_rel`, `absorbFixed_rel`), from
the same arguments: `scratch`, the inputs' places and lengths, and the byte
count, which only the inputs' lengths fix.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.Spec.Blake2 (Repr b bytesAt)
open VG.Proof.Argon2.X86.HPrime (Ctx InitIn UpdateIn FinalizeIn FixedIn)
open VG.Impl.Argon2.X86.Derive (countLoOff countHiOff argOff)

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp only [bytesAt, List.length_map, List.length_range]

namespace Two
variable {s₀₁ s₀₂ : State} (T : VG.Proof.Argon2.X86.Derive.Two s₀₁ s₀₂)
include T

/-- `scratch`'s context in the second run, in the first run's terms. -/
theorem ctx₂ {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀₂ s) (hb : s.gpr .ebx = scrP s₀₂) : VG.Proof.Argon2.X86.HPrime.Ctx (scrP s₀₁) (VG.Proof.Argon2.X86.Derive.E s₀₁) s := by
  rw [T.pb.scrP_eq, T.pb.E]; exact VG.Proof.Argon2.X86.Derive.ctx T.hp₂ h hb

/-- `start` leaks the same trace in two runs. -/
theorem start_rel :
    RelCT isa (fun s₁ s₂ => (VG.Proof.Argon2.X86.Derive.Inv s₀₁ s₁ ∧ Prm s₀₁ s₁) ∧ (VG.Proof.Argon2.X86.Derive.Inv s₀₂ s₂ ∧ Prm s₀₂ s₂))
      Impl.Argon2.X86.Derive.start fun _ _ => True := by
  have hs := T.hp₁.scr_fits
  unfold Impl.Argon2.X86.Derive.start
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => stA_ok T.hp₁ h.1 h.2) (fun s h => stA_ok T.hp₂ h.1 h.2) ?_
  refine RelCT.seqW ((HPrime.init_rel (B := scrP s₀₁) (E := VG.Proof.Argon2.X86.Derive.E s₀₁) (n := 64) (by decide) (by decide)).mono
      (fun s₁ s₂ h => ⟨⟨VG.Proof.Argon2.X86.Derive.ctx T.hp₁ h.1.1 h.1.2.2.1, h.1.2.2.2⟩, ⟨T.ctx₂ h.2.1 h.2.2.2.1, h.2.2.2.2⟩⟩)
      fun _ _ h => h)
    (fun s h => stInit_ok T.hp₁ h) (fun s h => stInit_ok T.hp₂ h) ?_
  refine RelCT.seqW (T.leafI [.ebx] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.2.2.1, h.2.2.2.1, T.pb.scrP_eq]⟩) ⟨_, by taint_decide⟩)
    (G₁ := fun t => VG.Proof.Argon2.X86.Derive.Inv s₀₁ t ∧ Prm s₀₁ t ∧ t.gpr .ebx = scrP s₀₁ ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem ((scrP s₀₁).setWidth 64) [] ∧
      bytesAt t.mem ((scrP s₀₁).setWidth 64 + BitVec.ofNat 64 768) 24 = Proof.Argon2.initialHeader (prm s₀₁))
    (G₂ := fun t => VG.Proof.Argon2.X86.Derive.Inv s₀₂ t ∧ Prm s₀₂ t ∧ t.gpr .ebx = scrP s₀₂ ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem ((scrP s₀₂).setWidth 64) [] ∧
      bytesAt t.mem ((scrP s₀₂).setWidth 64 + BitVec.ofNat 64 768) 24 = Proof.Argon2.initialHeader (prm s₀₂))
    (fun s h => (header_ok T.hp₁ h.1 h.2.1 h.2.2.1 h.2.2.2).mono fun t ⟨i, p, e, r, d, _⟩ => ⟨i, p, e, r, d⟩)
    (fun s h => (header_ok T.hp₂ h.1 h.2.1 h.2.2.1 h.2.2.2).mono fun t ⟨i, p, e, r, d, _⟩ => ⟨i, p, e, r, d⟩) ?_
  refine RelCT.seqW ((HPrime.absorbFixed_rel (B := scrP s₀₁) (E := VG.Proof.Argon2.X86.Derive.E s₀₁) (offset := 768) (size := 24)
      (by omega) (by decide) (by decide) (stk_scr T.hp₁ (by decide) (by decide)) ⟨_, by taint_decide⟩).mono
      (fun s₁ s₂ h => ⟨⟨VG.Proof.Argon2.X86.Derive.ctx T.hp₁ h.1.1 h.1.2.2.1, scr_cov T.hp₁ h.1.1 (by decide)⟩,
        ⟨T.ctx₂ h.2.1 h.2.2.2.1, by rw [T.pb.scrP_eq]; exact scr_cov T.hp₂ h.2.1 (by decide)⟩⟩) fun _ _ h => h)
    (fun s h => stFix_ok T.hp₁ h) (fun s h => stFix_ok T.hp₂ h) ?_
  exact T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩

/-- `absorb ptr len` leaks the same trace in two runs whose absorbed data have
the same length. -/
theorem absorb_rel {ptr len : Nat} (hptr : ptr < 18) (hlen : len < 18)
    (hR₁ : (⟨(VG.X86.arg s₀₁ ptr).setWidth 64, (VG.X86.arg s₀₁ len).toNat⟩ : Region) ∈ [pwR s₀₁, saltR s₀₁, secR s₀₁, adR s₀₁])
    (hR₂ : (⟨(VG.X86.arg s₀₂ ptr).setWidth 64, (VG.X86.arg s₀₂ len).toNat⟩ : Region) ∈ [pwR s₀₂, saltR s₀₂, secR s₀₂, adR s₀₂])
    (hfit₁ : (VG.X86.arg s₀₁ ptr).toNat + (VG.X86.arg s₀₁ len).toNat ≤ 2 ^ 32)
    (hfit₂ : (VG.X86.arg s₀₂ ptr).toNat + (VG.X86.arg s₀₂ len).toNat ≤ 2 ^ 32) {data₁ data₂ : List Byte}
    (hd : data₁.length + 4 + 2 ^ 32 < 2 ^ 36) (heq : data₁.length = data₂.length)
    (hcA : ∃ hc, (VG.Taint.check taint (VG.Proof.Argon2.X86.Derive.τB [] [.ebx]) (.block [.mov .eax (Impl.Argon2.X86.Derive.fr (argOff len)),
      .store ⟨.ebx, 792⟩ .eax, .mov .ecx (Impl.Argon2.X86.Derive.fr countLoOff),
      .mov .edx (Impl.Argon2.X86.Derive.fr countHiOff), .mov .esi (.reg .ebx), .alu .add .esi (.imm 792),
      .mov .edi (.imm 4)]) hc).isSome = true)
    (hcB : ∃ hc, (VG.Taint.check taint (VG.Proof.Argon2.X86.Derive.τB [] []) (.block (Impl.Argon2.X86.Derive.addCount (.imm 4) ++
      ([.mov .esi (Impl.Argon2.X86.Derive.fr (argOff ptr)), .mov .edi (Impl.Argon2.X86.Derive.fr (argOff len))] :
        List Instr)))
      hc).isSome = true)
    (hcC : ∃ hc, (VG.Taint.check taint (VG.Proof.Argon2.X86.Derive.τB [] [])
      (.block (Impl.Argon2.X86.Derive.addCount (Impl.Argon2.X86.Derive.fr (argOff len)))) hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => HI s₀₁ data₁ s₁ ∧ HI s₀₂ data₂ s₂) (Impl.Argon2.X86.Derive.absorb ptr len)
      fun _ _ => True := by
  have hs := T.hp₁.scr_fits
  have ep := T.pb.arg_eq hptr
  have el := T.pb.arg_eq hlen
  have e792 : (scrP s₀₁ + 792).setWidth 64 = (scrP s₀₁).setWidth 64 + BitVec.ofNat 64 792 :=
    HPrime.setWidth_add (d := 792) (by omega)
  have cov792 : ∀ {s₀ s : State}, DPre s₀ → VG.Proof.Argon2.X86.Derive.Inv s₀ s →
      Covers [⟨(scrP s₀ + 792).setWidth 64, 4⟩] (s.rd ++ s.wr) := fun {s₀ s} hp h => by
    have := hp.scr_fits
    have e : (scrP s₀ + 792).setWidth 64 = (scrP s₀).setWidth 64 + BitVec.ofNat 64 792 :=
      HPrime.setWidth_add (d := 792) (by omega)
    rw [e]; exact Covers.right (scr_cov hp h (by decide))
  have covIn : ∀ {s₀ s : State}, DPre s₀ → VG.Proof.Argon2.X86.Derive.Inv s₀ s →
      (⟨(VG.X86.arg s₀ ptr).setWidth 64, (VG.X86.arg s₀ len).toNat⟩ : Region) ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀] →
      Covers [⟨(VG.X86.arg s₀ ptr).setWidth 64, (VG.X86.arg s₀ len).toNat⟩] (s.rd ++ s.wr) := fun {s₀ s} hp h hR => by
    have hR' : (⟨(VG.X86.arg s₀ ptr).setWidth 64, (VG.X86.arg s₀ len).toNat⟩ : Region) ∈
        [pwR s₀, saltR s₀, secR s₀, adR s₀, VG.Proof.Argon2.X86.Derive.argR s₀] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
      rcases hR with h | h | h | h <;> simp [h]
    rw [h.rd, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_left _ hR', 0, by simp, by simp⟩
  have hS : (⟨(VG.X86.arg s₀₁ ptr).setWidth 64, (VG.X86.arg s₀₁ len).toNat⟩ : Region) ∈
      [pwR s₀₁, saltR s₀₁, secR s₀₁, adR s₀₁, memR s₀₁, VG.Proof.Argon2.X86.Derive.scrR s₀₁, VG.Proof.Argon2.X86.Derive.outR s₀₁] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR₁ ⊢
    rcases hR₁ with h | h | h | h <;> simp [h]
  have hR' : (⟨(VG.X86.arg s₀₁ ptr).setWidth 64, (VG.X86.arg s₀₁ len).toNat⟩ : Region) ∈
      [pwR s₀₁, saltR s₀₁, secR s₀₁, adR s₀₁, VG.Proof.Argon2.X86.Derive.argR s₀₁] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR₁ ⊢
    rcases hR₁ with h | h | h | h <;> simp [h]
  unfold Impl.Argon2.X86.Derive.absorb
  refine RelCT.seqW (T.leafI [.ebx] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.ebx, h.2.ebx, T.pb.scrP_eq]⟩) hcA)
    (fun s h => absA_ok T.hp₁ hlen h.hc) (fun s h => absA_ok T.hp₂ hlen h.hc) ?_
  refine RelCT.seqW ((HPrime.update_rel (B := scrP s₀₁) (E := VG.Proof.Argon2.X86.Derive.E s₀₁) (D := scrP s₀₁ + 792) (L := 4)
      (lo := BitVec.ofNat 32 data₁.length) (hi := BitVec.ofNat 32 (data₁.length / 2 ^ 32))
      (by have : (scrP s₀₁ + 792).toNat = (scrP s₀₁).toNat + 792 := add_nat (k := 792) (by omega)
          omega)
      (by rw [e792]; exact Offset.disjoint_base _ (by decide) (by decide))
      (by rw [e792]; exact stk_scr T.hp₁ (by decide) (by decide))).mono
      (fun s₁ s₂ ⟨⟨g₁, e₁, d₁, c₁, x₁, _⟩, ⟨g₂, e₂, d₂, c₂, x₂, _⟩⟩ =>
        ⟨⟨VG.Proof.Argon2.X86.Derive.ctx T.hp₁ g₁.inv g₁.ebx, e₁, d₁, c₁, x₁, cov792 T.hp₁ g₁.inv⟩,
         ⟨T.ctx₂ g₂.inv g₂.ebx, by rw [e₂, T.pb.scrP_eq], d₂, by rw [c₂, heq], by rw [x₂, heq],
           by rw [T.pb.scrP_eq]; exact cov792 T.hp₂ g₂.inv⟩⟩) fun _ _ h => h)
    (fun s h => absU1_ok T.hp₁ h.1 rfl (by omega) h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
    (fun s h => absU1_ok T.hp₂ h.1 rfl (by omega) h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2) ?_
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩) hcB)
    (fun s h => absB_ok T.hp₁ hptr hlen h) (fun s h => absB_ok T.hp₂ hptr hlen h) ?_
  refine RelCT.seqW ((HPrime.update_rel (B := scrP s₀₁) (E := VG.Proof.Argon2.X86.Derive.E s₀₁) (D := VG.X86.arg s₀₁ ptr)
      (L := (VG.X86.arg s₀₁ len).toNat) (lo := BitVec.ofNat 32 (data₁.length + 4))
      (hi := BitVec.ofNat 32 ((data₁.length + 4) / 2 ^ 32))
      hfit₁ ((T.hp₁.ro_w _ hR' (VG.Proof.Argon2.X86.Derive.scrR s₀₁) (by simp)).sub_right (Region.sub_prefix (by decide)))
      ((T.hp₁.stk_all _ hS).sub_left fun a ha => call_stk T.hp₁ a (below60_call T.hp₁ a ha))).mono
      (fun s₁ s₂ ⟨⟨g₁, e₁, d₁, c₁, x₁⟩, ⟨g₂, e₂, d₂, c₂, x₂⟩⟩ =>
        ⟨⟨VG.Proof.Argon2.X86.Derive.ctx T.hp₁ g₁.inv g₁.ebx, e₁, d₁, c₁, x₁, covIn T.hp₁ g₁.inv hR₁⟩,
         ⟨T.ctx₂ g₂.inv g₂.ebx, by rw [e₂, ep], by rw [d₂, el], by rw [c₂, heq], by rw [x₂, heq],
           by rw [ep, el]; exact covIn T.hp₂ g₂.inv hR₂⟩⟩) fun _ _ h => h)
    (fun s h => absU2_ok T.hp₁ hR₁ hfit₁ h.1 (by simp [Proof.Argon2.le32_length]) (by omega)
      h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
    (fun s h => absU2_ok T.hp₂ hR₂ hfit₂ h.1 (by simp [Proof.Argon2.le32_length]) (by omega)
      h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2) ?_
  exact T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩) hcC

/-- `finish` leaks the same trace in two runs whose absorbed data have the same
length. -/
theorem finish_rel {data₁ data₂ : List Byte} (heq : data₁.length = data₂.length) :
    RelCT isa (fun s₁ s₂ => HI s₀₁ data₁ s₁ ∧ HI s₀₂ data₂ s₂) Impl.Argon2.X86.Derive.finish fun _ _ => True := by
  unfold Impl.Argon2.X86.Derive.finish
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => fiA_ok T.hp₁ h) (fun s h => fiA_ok T.hp₂ h) ?_
  refine RelCT.seqW ((HPrime.finalize_rel (B := scrP s₀₁) (E := VG.Proof.Argon2.X86.Derive.E s₀₁) (lo := BitVec.ofNat 32 data₁.length)
      (hi := BitVec.ofNat 32 (data₁.length / 2 ^ 32))).mono
      (fun s₁ s₂ ⟨⟨g₁, c₁, x₁⟩, ⟨g₂, c₂, x₂⟩⟩ =>
        ⟨⟨VG.Proof.Argon2.X86.Derive.ctx T.hp₁ g₁.inv g₁.ebx, c₁, x₁⟩, ⟨T.ctx₂ g₂.inv g₂.ebx, by rw [c₂, heq], by rw [x₂, heq]⟩⟩)
      fun _ _ h => h)
    (fun s h => fiFin_ok T.hp₁ h.1 h.2.1 h.2.2) (fun s h => fiFin_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  exact T.leafI [.ebx] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by
    simp only [List.mem_singleton, forall_eq]; rw [h.1.2.2.1, h.2.2.2.1, T.pb.scrP_eq]⟩) ⟨_, by taint_decide⟩

/-- H₀'s code leaks the same trace in two runs. -/
theorem code_rel :
    RelCT isa (fun s₁ s₂ => (VG.Proof.Argon2.X86.Derive.Inv s₀₁ s₁ ∧ Prm s₀₁ s₁) ∧ (VG.Proof.Argon2.X86.Derive.Inv s₀₂ s₂ ∧ Prm s₀₂ s₂))
      Impl.Argon2.X86.Derive.code fun _ _ => True := by
  have l1 := (VG.X86.arg s₀₁ 2).isLt
  have l2 := (VG.X86.arg s₀₁ 4).isLt
  have l3 := (VG.X86.arg s₀₁ 10).isLt
  have hpp := T.pb
  have a2 : (VG.X86.arg s₀₂ 2).toNat = (VG.X86.arg s₀₁ 2).toNat := by rw [hpp.arg_eq (by decide)]
  have a4 : (VG.X86.arg s₀₂ 4).toNat = (VG.X86.arg s₀₁ 4).toNat := by rw [hpp.arg_eq (by decide)]
  have a10 : (VG.X86.arg s₀₂ 10).toNat = (VG.X86.arg s₀₁ 10).toNat := by rw [hpp.arg_eq (by decide)]
  have a12 : (VG.X86.arg s₀₂ 12).toNat = (VG.X86.arg s₀₁ 12).toNat := by rw [hpp.arg_eq (by decide)]
  unfold Impl.Argon2.X86.Derive.code
  refine RelCT.seqW T.start_rel (fun s h => start_ok T.hp₁ h.1 h.2) (fun s h => start_ok T.hp₂ h.1 h.2) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 1) (len := 2) (by decide) (by decide) (by simp) (by simp)
      T.hp₁.pw_fits T.hp₂.pw_fits (by rw [Proof.Argon2.initialHeader_length]; omega)
      (by rw [Proof.Argon2.initialHeader_length, Proof.Argon2.initialHeader_length])
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => absorb_ok T.hp₁ (ptr := 1) (len := 2) (by decide) (by decide) (by simp) T.hp₁.pw_fits
      (by rw [Proof.Argon2.initialHeader_length]; omega) h)
    (fun s h => absorb_ok T.hp₂ (ptr := 1) (len := 2) (by decide) (by decide) (by simp) T.hp₂.pw_fits
      (by rw [Proof.Argon2.initialHeader_length]; omega) h) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 3) (len := 4) (by decide) (by decide) (by simp) (by simp)
      T.hp₁.salt_fits T.hp₂.salt_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, VG.Proof.Argon2.X86.Derive.bytesAt_length]; omega)
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, VG.Proof.Argon2.X86.Derive.bytesAt_length, a2])
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => absorb_ok T.hp₁ (ptr := 3) (len := 4) (by decide) (by decide) (by simp) T.hp₁.salt_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, VG.Proof.Argon2.X86.Derive.bytesAt_length]; omega) h)
    (fun s h => absorb_ok T.hp₂ (ptr := 3) (len := 4) (by decide) (by decide) (by simp) T.hp₂.salt_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, VG.Proof.Argon2.X86.Derive.bytesAt_length]
          have := (VG.X86.arg s₀₂ 2).isLt; omega) h) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 9) (len := 10) (by decide) (by decide) (by simp) (by simp)
      T.hp₁.sec_fits T.hp₂.sec_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, VG.Proof.Argon2.X86.Derive.bytesAt_length]; omega)
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, VG.Proof.Argon2.X86.Derive.bytesAt_length, a2, a4])
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => absorb_ok T.hp₁ (ptr := 9) (len := 10) (by decide) (by decide) (by simp) T.hp₁.sec_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, VG.Proof.Argon2.X86.Derive.bytesAt_length]; omega) h)
    (fun s h => absorb_ok T.hp₂ (ptr := 9) (len := 10) (by decide) (by decide) (by simp) T.hp₂.sec_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, VG.Proof.Argon2.X86.Derive.bytesAt_length]
          have := (VG.X86.arg s₀₂ 2).isLt; have := (VG.X86.arg s₀₂ 4).isLt; omega) h) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 11) (len := 12) (by decide) (by decide) (by simp) (by simp)
      T.hp₁.ad_fits T.hp₂.ad_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, VG.Proof.Argon2.X86.Derive.bytesAt_length]; omega)
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, VG.Proof.Argon2.X86.Derive.bytesAt_length, a2, a4,
        a10])
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => absorb_ok T.hp₁ (ptr := 11) (len := 12) (by decide) (by decide) (by simp) T.hp₁.ad_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, VG.Proof.Argon2.X86.Derive.bytesAt_length]; omega) h)
    (fun s h => absorb_ok T.hp₂ (ptr := 11) (len := 12) (by decide) (by decide) (by simp) T.hp₂.ad_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, VG.Proof.Argon2.X86.Derive.bytesAt_length]
          have := (VG.X86.arg s₀₂ 2).isLt; have := (VG.X86.arg s₀₂ 4).isLt; have := (VG.X86.arg s₀₂ 10).isLt; omega) h) ?_
  exact T.finish_rel (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length,
    VG.Proof.Argon2.X86.Derive.bytesAt_length, a2, a4, a10, a12])

end Two

end VG.Proof.Argon2.X86.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.Derive.ReduceCT`. -/
section

/-!
# Argon2 on x86 (32-bit): the final block and the tag, in two runs

`reduce_rel`: XORing every lane's last block into the first leaks the same
trace in two runs (the lane's last block's address, which the taint analysis
forgets, is related by correctness); `finalOutput_rel`: so does the call of
H′ that writes the tag.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd wp_mov wp_movi wp_addi wp_subi)
open VG.Spec.Argon2 (Block zeroBlock)
open VG.Impl.Argon2.X86.Derive (argOff laneOff laneLenOff)

theorem RI.of_keep {s₀ s t : State} {M : Array Block} {l : Nat} (h : VG.Proof.Argon2.X86.Derive.RI s₀ M l s) (k : Divide.Keep s t) :
    VG.Proof.Argon2.X86.Derive.RI s₀ M l t :=
  ⟨h.inv.keep k, h.pr.of_mem k.mem, by rw [lw_mem k.mem]; exact h.lane, by rw [k.mem]; exact h.first,
    fun j hj j0 => by rw [k.mem]; exact h.rest j hj j0⟩

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The first part of a lane's reduction: `eax :=` the address of its last block. -/
theorem redPart1_ok {s : State} {M : Array Block} {l : Nat} (h : VG.Proof.Argon2.X86.Derive.RI s₀ M l s) (hl : l < lanesN s₀) :
    WP isa (.block (([.mov .eax (Impl.Argon2.X86.Derive.fr laneOff),
      .mov .ecx (Impl.Argon2.X86.Derive.fr laneLenOff), .alu .sub .ecx (.imm 1)] : List Instr) ++
      Impl.Argon2.X86.Derive.blockAddr)) s fun t => VG.Proof.Argon2.X86.Derive.RI s₀ M l t ∧
      t.gpr .eax = memP s₀ + BitVec.ofNat 32 ((l * (prm s₀).laneLen + ((prm s₀).laneLen - 1)) * 1024) := by
  have L8 := VG.Proof.Argon2.X86.Derive.laneLen_ge hp
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc hp h.inv (d := laneOff) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.inv.upd u₁ (by decide) (by decide)
  refine wp_ldloc hp i₁ (d := laneLenOff) (by decide) fun s₂ u₂ => wp_subi fun s₃ u₃ _ _ => ?_
  have i₃ := (i₁.upd u₂ (by decide) (by decide)).upd u₃ (by decide) (by decide)
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  rw [← List.append_nil Impl.Argon2.X86.Derive.blockAddr]
  refine VG.Proof.Argon2.X86.Derive.blockAddr_ok hp i₃ (h.pr.of_mem m₃) hl (col := (prm s₀).laneLen - 1) (by omega)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.lane])
    (by rw [u₃.gpr, u₂.gpr, lw_mem u₁.mem, h.pr.laneLen, Wp.ofNat_pred (by omega)]) fun s₄ a₄ _ k₄ =>
      WP.block_nil ⟨h.of_keep (((Divide.Keep.of_upd u₁ (by simp)).trans ((Divide.Keep.of_upd u₂ (by simp)).trans
        (Divide.Keep.of_upd u₃ (by simp)))).trans k₄), a₄⟩

/-- The instructions before `finalOutput`'s call of H′. -/
theorem foBlk_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) :
    WP isa (.block [.mov .esi (Impl.Argon2.X86.Derive.fr (argOff 13)), .mov .eax (.imm 1024),
      .mov .edi (Impl.Argon2.X86.Derive.fr (argOff 16)), .mov .ecx (Impl.Argon2.X86.Derive.fr (argOff 17)),
      .mov .edx (Impl.Argon2.X86.Derive.fr (argOff 15))]) s fun t => VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ t.gpr .edx = scrP s₀ ∧
      t.gpr .esi = memP s₀ ∧ t.gpr .eax = 1024 ∧ t.gpr .edi = outP s₀ ∧ t.gpr .ecx = VG.X86.arg s₀ 17 := by
  refine wp_ldarg hp h (i := 13) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁ (by decide) (by decide)
  refine wp_movi fun s₂ u₂ => ?_
  have i₂ := i₁.upd u₂ (by decide) (by decide)
  refine wp_ldarg hp i₂ (i := 16) (by decide) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃ (by decide) (by decide)
  refine wp_ldarg hp i₃ (i := 17) (by decide) fun s₄ u₄ => ?_
  have i₄ := i₃.upd u₄ (by decide) (by decide)
  refine wp_ldarg hp i₄ (i := 15) (by decide) fun s₅ u₅ => WP.block_nil ⟨i₄.upd u₅ (by decide) (by decide),
    u₅.gpr, ?_, ?_, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  · rw [u₅.other _ (by decide), u₄.gpr]

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : VG.Proof.Argon2.X86.Derive.Two s₀₁ s₀₂)
include T

/-- `reduce` leaks the same trace in two runs. -/
theorem reduce_rel {M₁ M₂ : Array Block} :
    RelCT isa (fun s₁ s₂ => (VG.Proof.Argon2.X86.Derive.Inv s₀₁ s₁ ∧ Prm s₀₁ s₁ ∧ Represents s₁.mem (memB s₀₁) (prm s₀₁).blocks M₁) ∧
      (VG.Proof.Argon2.X86.Derive.Inv s₀₂ s₂ ∧ Prm s₀₂ s₂ ∧ Represents s₂.mem (memB s₀₂) (prm s₀₂).blocks M₂))
      Impl.Argon2.X86.Derive.reduce fun _ _ => True := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  have hl1 := T.hp₁.lanes_pos
  unfold Impl.Argon2.X86.Derive.reduce
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.X86.Derive.reduceStart_ok T.hp₁ h.1 h.2.1 h.2.2) (fun s h => VG.Proof.Argon2.X86.Derive.reduceStart_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  generalize hN : lanesN s₀₁ = N at hl1
  have hN₂ : lanesN s₀₂ = N := by rw [← le, hN]
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ l, n = N - l ∧ l < N ∧
      VG.Proof.Argon2.X86.Derive.RI s₀₁ M₁ l s₁ ∧ VG.Proof.Argon2.X86.Derive.RI s₀₂ M₂ l s₂) ?step N).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, by omega, hl1, h.1, h.2⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨l, hn, hl, g₁, g₂⟩ e₁ e₂
  have body : RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.Derive.RI s₀₁ M₁ l s₁ ∧ VG.Proof.Argon2.X86.Derive.RI s₀₂ M₂ l s₂)
      (.block (Impl.Argon2.X86.Derive.reduceLane ++ Impl.Argon2.X86.Derive.advance laneOff
        (Impl.Argon2.X86.Derive.fr (argOff Impl.Argon2.X86.Derive.lanesArg)))) fun _ _ => True := by
    rw [show Impl.Argon2.X86.Derive.reduceLane ++ Impl.Argon2.X86.Derive.advance laneOff
        (Impl.Argon2.X86.Derive.fr (argOff Impl.Argon2.X86.Derive.lanesArg)) =
      ([.mov .eax (Impl.Argon2.X86.Derive.fr laneOff), .mov .ecx (Impl.Argon2.X86.Derive.fr laneLenOff),
        .alu .sub .ecx (.imm 1)] ++ Impl.Argon2.X86.Derive.blockAddr) ++
      ([.mov .esi (.reg .eax), .mov .edi (Impl.Argon2.X86.Derive.fr (argOff Impl.Argon2.X86.Derive.memoryArg))] ++
        Impl.Argon2.X86.Derive.writeBlock true ++ Impl.Argon2.X86.Derive.advance laneOff
          (Impl.Argon2.X86.Derive.fr (argOff Impl.Argon2.X86.Derive.lanesArg))) by
      simp only [Impl.Argon2.X86.Derive.reduceLane, List.append_assoc]]
    refine RelCT.block_split (RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩)
        ⟨_, by taint_decide⟩)
      (fun s h => VG.Proof.Argon2.X86.Derive.redPart1_ok T.hp₁ h (by rw [hN]; exact hl))
      (fun s h => VG.Proof.Argon2.X86.Derive.redPart1_ok T.hp₂ h (by rw [hN₂]; exact hl)) ?_)
    exact T.leafI [.eax] (fun s₁ s₂ h => ⟨h.1.1.inv, h.2.1.inv, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.2, h.2.2, pe, T.pb.memP_eq]⟩) ⟨_, by taint_decide⟩
  obtain ⟨ht, ⟨k₁, c₁⟩, ⟨k₂, c₂⟩⟩ := HPrime.rel_wp body
    (fun s h => VG.Proof.Argon2.X86.Derive.reduceLane_ok T.hp₁ h (by rw [hN]; exact hl))
    (fun s h => VG.Proof.Argon2.X86.Derive.reduceLane_ok T.hp₂ h (by rw [hN₂]; exact hl)) s₁ s₂ t₁ t₂ s₁' s₂' ⟨g₁, g₂⟩ e₁ e₂
  rw [hN] at c₁
  rw [hN₂] at c₂
  refine ⟨ht, by show s₁'.cf = s₂'.cf; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  have e : l + 1 < N := by
    rw [show isa.eval .b s₁' = s₁'.cf from rfl, c₁] at hc
    simpa using hc
  exact ⟨N - (l + 1), by omega, l + 1, rfl, e, k₁, k₂⟩

/-- `finalOutput` leaks the same trace in two runs. -/
theorem finalOutput_rel :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.Derive.Inv s₀₁ s₁ ∧ VG.Proof.Argon2.X86.Derive.Inv s₀₂ s₂) Impl.Argon2.X86.Derive.finalOutput fun _ _ => True := by
  have pre : ∀ {s₀ : State}, DPre s₀ → ∀ {t : State}, VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ t.gpr .edx = scrP s₀ ∧
      t.gpr .esi = memP s₀ ∧ t.gpr .eax = 1024 ∧ t.gpr .edi = outP s₀ ∧ t.gpr .ecx = VG.X86.arg s₀ 17 →
      VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ t.gpr .edx = scrP s₀ ∧
        (∃ R ∈ [memR s₀, locR s₀], ∃ off, (t.gpr .esi).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
          off + (t.gpr .eax).toNat ≤ R.len) ∧ (t.gpr .esi).toNat + (t.gpr .eax).toNat ≤ 2 ^ 32 ∧
        (∃ R ∈ [memR s₀, VG.Proof.Argon2.X86.Derive.outR s₀], ∃ off, (t.gpr .edi).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
          off + (t.gpr .ecx).toNat ≤ R.len) ∧ (t.gpr .edi).toNat + (t.gpr .ecx).toNat ≤ 2 ^ 32 ∧
        1 ≤ (t.gpr .ecx).toNat := fun {s₀} hp {t} ⟨i, d, si, ax, di, cx⟩ => by
    have b1 := blocks_pos hp
    have hm := hp.mem_fits
    have ho := hp.out_fits
    have tg := hp.tag_ge
    refine ⟨i, d, ⟨memR s₀, by simp, 0, by rw [si]; simp, by rw [ax]; show 0 + 1024 ≤ blocksN s₀ * 1024; omega⟩,
      by rw [si, ax]; show _ + 1024 ≤ 2 ^ 32; omega,
      ⟨VG.Proof.Argon2.X86.Derive.outR s₀, by simp, 0, by rw [di]; simp, by rw [cx]; show 0 + outL s₀ ≤ outL s₀; omega⟩,
      by rw [di, cx]; exact ho, by rw [cx]; show 1 ≤ outL s₀; omega⟩
  unfold Impl.Argon2.X86.Derive.finalOutput
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1, h.2, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.X86.Derive.foBlk_ok T.hp₁ h) (fun s h => VG.Proof.Argon2.X86.Derive.foBlk_ok T.hp₂ h) ?_
  refine T.hcall_rel (r := .esi) (by decide) fun s₁ s₂ k₁ k₂ =>
    ⟨pre T.hp₁ k₁, pre T.hp₂ k₂, ?_, ?_, ?_, ?_⟩
  · rw [k₁.2.2.1, k₂.2.2.1, T.pb.memP_eq]
  · rw [k₁.2.2.2.1, k₂.2.2.2.1]
  · rw [k₁.2.2.2.2.1, k₂.2.2.2.2.1, T.pb.outP_eq]
  · rw [k₁.2.2.2.2.2, k₂.2.2.2.2.2, T.pb.arg_eq (by decide)]

end Two

end VG.Proof.Argon2.X86.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.Derive.Verified`. -/
section

section

section

/-!
# Argon2 on x86 (32-bit): memory initialization, in two runs

`memoryInit_rel`: clearing the matrix and the calls of H′ for the first two
blocks of every lane leak the same trace in two runs with the same public
data: the calls' arguments are H₀'s place in the locals and the blocks'
addresses, which only the lane fixes.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd wp_mov wp_movi wp_addi)
open VG.Spec.Blake2 (bytesAt)
open VG.Impl.Sha512.X86 (at_)
open VG.Impl.Argon2.X86.Derive (argOff columnOff laneWordOff)

/-- The state before block `c` of lane `l`. -/
def IB (s₀ : State) (h0 : List Byte) (l c : Nat) (s : State) : Prop :=
  VG.Proof.Argon2.X86.Derive.Inv s₀ s ∧ Prm s₀ s ∧ bytesAt s.mem ((VG.Proof.Argon2.X86.Derive.E s₀).setWidth 64) 64 = h0 ∧ s.gpr .esi = BitVec.ofNat 32 l ∧
    s.gpr .edi = memP s₀ + BitVec.ofNat 32 ((l * (prm s₀).laneLen + c) * 1024)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem initBlock_w {h0 : List Byte} {l c : Nat} (hl : l < lanesN s₀) (hc : c < 2) {s : State}
    (h : VG.Proof.Argon2.X86.Derive.IB s₀ h0 l c s) : WP isa (Impl.Argon2.X86.Derive.initBlock c) s (VG.Proof.Argon2.X86.Derive.IB s₀ h0 l c) :=
  (initBlock_ok hp h.1 h.2.1 h.2.2.1 hl hc h.2.2.2.1 h.2.2.2.2).mono fun _ ⟨i, p, b, e, d, _, _⟩ =>
    ⟨i, p, b, e.trans h.2.2.2.1, d.trans h.2.2.2.2⟩

omit hp in
theorem nextBlock_w {h0 : List Byte} {l : Nat} {s : State} (h : VG.Proof.Argon2.X86.Derive.IB s₀ h0 l 0 s) :
    WP isa (.block [.alu .add .edi (.imm 1024)]) s (VG.Proof.Argon2.X86.Derive.IB s₀ h0 l 1) :=
  wp_addi fun t u => WP.block_nil ⟨h.1.upd u (by decide) (by decide), h.2.1.of_mem u.mem,
    by rw [u.mem]; exact h.2.2.1, by rw [u.other _ (by decide)]; exact h.2.2.2.1, by
      rw [u.gpr, h.2.2.2.2, show (1024 : BitVec 32) = BitVec.ofNat 32 1024 from rfl, BitVec.add_assoc,
        BitVec.ofNat_add_ofNat, show (l * (prm s₀).laneLen + 0) * 1024 + 1024 = (l * (prm s₀).laneLen + 1) * 1024 by
          rw [Nat.add_mul, Nat.add_mul]]⟩

/-- The instructions before `initBlock`'s call of H′. -/
theorem ibBlk_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) (c : Nat) :
    WP isa (.block [.mov .eax (.imm (BitVec.ofNat 32 c)), .store (at_ .ebp columnOff) .eax,
      .store (at_ .ebp laneWordOff) .esi, .mov .eax (.imm 72), .mov .ecx (.imm 1024),
      .mov .edx (Impl.Argon2.X86.Derive.fr (argOff 15))]) s fun t => VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ t.gpr .edx = scrP s₀ ∧
      t.gpr .eax = 72 ∧ t.gpr .ecx = 1024 ∧ t.gpr .edi = s.gpr .edi := by
  refine wp_movi fun s₁ u₁ => ?_
  have i₁ := h.upd u₁ (by decide) (by decide)
  refine wp_stloc hp i₁ (d := 64) (by decide) fun s₂ i₂ _ _ g₂ _ => ?_
  refine wp_stloc hp i₂ (d := 68) (by decide) fun s₃ i₃ _ _ g₃ _ => ?_
  refine wp_movi fun s₄ u₄ => wp_movi fun s₅ u₅ => wp_ldarg hp ((i₃.upd u₄ (by decide) (by decide)).upd u₅
    (by decide) (by decide)) (i := 15) (by decide) fun s₆ u₆ => WP.block_nil
    ⟨((i₃.upd u₄ (by decide) (by decide)).upd u₅ (by decide) (by decide)).upd u₆ (by decide) (by decide),
      u₆.gpr, by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr],
      by rw [u₆.other _ (by decide), u₅.gpr],
      by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), g₃, g₂,
        u₁.other _ (by decide)]⟩

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : VG.Proof.Argon2.X86.Derive.Two s₀₁ s₀₂)
include T

/-- `initBlock c` leaks the same trace in two runs at the same lane. -/
theorem initBlock_rel {h₁ h₂ : List Byte} {l c : Nat} (hl : l < lanesN s₀₁) (hc : c < 2)
    (hchk : ∃ hc, (VG.Taint.check taint (VG.Proof.Argon2.X86.Derive.τB [] []) (.block [.mov .eax (.imm (BitVec.ofNat 32 c)),
      .store (at_ .ebp columnOff) .eax, .store (at_ .ebp laneWordOff) .esi, .mov .eax (.imm 72),
      .mov .ecx (.imm 1024), .mov .edx (Impl.Argon2.X86.Derive.fr (argOff 15))]) hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.Derive.IB s₀₁ h₁ l c s₁ ∧ VG.Proof.Argon2.X86.Derive.IB s₀₂ h₂ l c s₂) (Impl.Argon2.X86.Derive.initBlock c)
      fun _ _ => True := by
  have pe := T.pb.prm_eq
  have cellF : ∀ {s₀ : State}, DPre s₀ → l < lanesN s₀ →
      (l * (prm s₀).laneLen + c) * 1024 + 1024 ≤ blocksN s₀ * 1024 ∧ l * (prm s₀).laneLen + c < blocksN s₀ :=
    fun {s₀} hp hl => by
      have L2 : 2 ≤ (prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega
      have : l * (prm s₀).laneLen + c < blocksN s₀ := by
        rw [hp.blocks_eq]
        have := Nat.mul_le_mul_right (prm s₀).laneLen (show l + 1 ≤ lanesN s₀ by omega)
        rw [Nat.succ_mul] at this
        omega
      exact ⟨by omega, this⟩
  have pre : ∀ {s₀ : State}, DPre s₀ → l < lanesN s₀ → ∀ {s t : State}, VG.Proof.Argon2.X86.Derive.IB s₀ h₁ l c s ∨ VG.Proof.Argon2.X86.Derive.IB s₀ h₂ l c s →
      VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ t.gpr .edx = scrP s₀ ∧ t.gpr .eax = 72 ∧ t.gpr .ecx = 1024 ∧ t.gpr .edi = s.gpr .edi →
      VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ t.gpr .edx = scrP s₀ ∧
        (∃ R ∈ [memR s₀, locR s₀], ∃ off, (t.gpr .ebp).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
          off + (t.gpr .eax).toNat ≤ R.len) ∧ (t.gpr .ebp).toNat + (t.gpr .eax).toNat ≤ 2 ^ 32 ∧
        (∃ R ∈ [memR s₀, VG.Proof.Argon2.X86.Derive.outR s₀], ∃ off, (t.gpr .edi).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
          off + (t.gpr .ecx).toNat ≤ R.len) ∧ (t.gpr .edi).toNat + (t.gpr .ecx).toNat ≤ 2 ^ 32 ∧
        1 ≤ (t.gpr .ecx).toNat := fun {s₀} hp hl {s t} hs ⟨i, d, a, c', e⟩ => by
    have hE := E_hi hp
    have hm := hp.mem_fits
    obtain ⟨hc', hk⟩ := cellF hp hl
    have ed : t.gpr .edi = memP s₀ + BitVec.ofNat 32 ((l * (prm s₀).laneLen + c) * 1024) := by
      rw [e]; rcases hs with hs | hs <;> exact hs.2.2.2.2
    have an : (memP s₀ + BitVec.ofNat 32 ((l * (prm s₀).laneLen + c) * 1024)).toNat =
        (memP s₀).toNat + (l * (prm s₀).laneLen + c) * 1024 := add_nat (by omega)
    refine ⟨i, d, ⟨locR s₀, by simp, 0, by rw [i.ebp]; simp, by rw [a]; show 0 + 72 ≤ 144; decide⟩,
      by rw [i.ebp, a]; show (VG.Proof.Argon2.X86.Derive.E s₀).toNat + 72 ≤ 2 ^ 32; omega,
      ⟨memR s₀, by simp, (l * (prm s₀).laneLen + c) * 1024, by rw [ed, cell_addr hp hk]; rfl,
        by rw [c']; exact hc'⟩, by rw [ed, c', an]; show _ + 1024 ≤ 2 ^ 32; omega,
      by rw [c']; decide⟩
  unfold Impl.Argon2.X86.Derive.initBlock Impl.Argon2.X86.Derive.hPrimeCall
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) hchk)
    (G₁ := fun t => ∃ s, VG.Proof.Argon2.X86.Derive.IB s₀₁ h₁ l c s ∧ VG.Proof.Argon2.X86.Derive.Inv s₀₁ t ∧ t.gpr .edx = scrP s₀₁ ∧ t.gpr .eax = 72 ∧
      t.gpr .ecx = 1024 ∧ t.gpr .edi = s.gpr .edi)
    (G₂ := fun t => ∃ s, VG.Proof.Argon2.X86.Derive.IB s₀₂ h₂ l c s ∧ VG.Proof.Argon2.X86.Derive.Inv s₀₂ t ∧ t.gpr .edx = scrP s₀₂ ∧ t.gpr .eax = 72 ∧
      t.gpr .ecx = 1024 ∧ t.gpr .edi = s.gpr .edi)
    (fun s h => (VG.Proof.Argon2.X86.Derive.ibBlk_ok T.hp₁ h.1 c).mono fun t ht => ⟨s, h, ht⟩)
    (fun s h => (VG.Proof.Argon2.X86.Derive.ibBlk_ok T.hp₂ h.1 c).mono fun t ht => ⟨s, h, ht⟩) ?_
  refine T.hcall_rel (r := .ebp) (by decide) fun s₁ s₂ ⟨a₁, g₁, k₁⟩ ⟨a₂, g₂, k₂⟩ =>
    ⟨pre T.hp₁ hl (.inl g₁) k₁, pre T.hp₂ (T.pb.lanesN_eq ▸ hl) (.inr g₂) k₂, ?_, ?_, ?_, ?_⟩
  · rw [k₁.1.ebp, k₂.1.ebp, T.pb.E]
  · rw [k₁.2.2.1, k₂.2.2.1]
  · rw [k₁.2.2.2.2, k₂.2.2.2.2, g₁.2.2.2.2, g₂.2.2.2.2, pe, T.pb.memP_eq]
  · rw [k₁.2.2.2.1, k₂.2.2.2.1]

/-- `initLane` leaks the same trace in two runs at the same lane. -/
theorem initLane_rel {h₁ h₂ : List Byte} {l : Nat} (hl : l < lanesN s₀₁) :
    RelCT isa (fun s₁ s₂ => LI s₀₁ h₁ l s₁ ∧ LI s₀₂ h₂ l s₂) Impl.Argon2.X86.Derive.initLane fun _ _ => True := by
  have hl₂ : l < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  have ib : ∀ {s₀ s : State} {h0 : List Byte}, LI s₀ h0 l s → VG.Proof.Argon2.X86.Derive.IB s₀ h0 l 0 s := fun h =>
    ⟨h.inv, h.pr, h.b0, h.esi, by rw [Nat.add_zero]; exact h.edi⟩
  unfold Impl.Argon2.X86.Derive.initLane
  refine (RelCT.seqW (T.initBlock_rel hl (by decide) ⟨_, by taint_decide⟩) (fun s h => VG.Proof.Argon2.X86.Derive.initBlock_w T.hp₁ hl (by decide) h)
    (fun s h => VG.Proof.Argon2.X86.Derive.initBlock_w T.hp₂ hl₂ (by decide) h) ?_).mono (fun _ _ h => ⟨ib h.1, ib h.2⟩) fun _ _ h => h
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.X86.Derive.nextBlock_w h) (fun s h => VG.Proof.Argon2.X86.Derive.nextBlock_w h) ?_
  refine RelCT.seqW (T.initBlock_rel hl (by decide) ⟨_, by taint_decide⟩) (fun s h => VG.Proof.Argon2.X86.Derive.initBlock_w T.hp₁ hl (by decide) h)
    (fun s h => VG.Proof.Argon2.X86.Derive.initBlock_w T.hp₂ hl₂ (by decide) h) ?_
  exact T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩

/-- `memoryInit` leaks the same trace in two runs. -/
theorem memoryInit_rel {h₁ h₂ : List Byte} :
    RelCT isa (fun s₁ s₂ => (VG.Proof.Argon2.X86.Derive.Inv s₀₁ s₁ ∧ Prm s₀₁ s₁ ∧ bytesAt s₁.mem ((VG.Proof.Argon2.X86.Derive.E s₀₁).setWidth 64) 64 = h₁) ∧
      (VG.Proof.Argon2.X86.Derive.Inv s₀₂ s₂ ∧ Prm s₀₂ s₂ ∧ bytesAt s₂.mem ((VG.Proof.Argon2.X86.Derive.E s₀₂).setWidth 64) 64 = h₂))
      Impl.Argon2.X86.Derive.memoryInit fun _ _ => True := by
  have le := T.pb.lanesN_eq
  have hl1 := T.hp₁.lanes_pos
  unfold Impl.Argon2.X86.Derive.memoryInit
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => clearW_ok T.hp₁ h.1 h.2.1 h.2.2) (fun s h => clearW_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => laneStart_ok T.hp₁ h) (fun s h => laneStart_ok T.hp₂ h) ?_
  generalize hN : lanesN s₀₁ = N at hl1
  have hN₂ : lanesN s₀₂ = N := by rw [← le, hN]
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ l, n = N - l ∧ l < N ∧
      LI s₀₁ h₁ l s₁ ∧ LI s₀₂ h₂ l s₂) ?step N).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, by omega, hl1, h.1, h.2⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨l, hn, hl, g₁, g₂⟩ e₁ e₂
  obtain ⟨ht, ⟨k₁, c₁⟩, ⟨k₂, c₂⟩⟩ := HPrime.rel_wp (T.initLane_rel (by rw [hN]; exact hl))
    (fun s h => lane_ok T.hp₁ (by rw [hN]; exact hl) h) (fun s h => lane_ok T.hp₂ (by rw [hN₂]; exact hl) h)
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨g₁, g₂⟩ e₁ e₂
  rw [hN] at c₁
  rw [hN₂] at c₂
  refine ⟨ht, by show s₁'.cf = s₂'.cf; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  have e : l + 1 < N := by
    rw [show isa.eval .b s₁' = s₁'.cf from rfl, c₁] at hc
    simpa using hc
  exact ⟨N - (l + 1), by omega, l + 1, rfl, e, k₁, k₂⟩

end Two

end VG.Proof.Argon2.X86.Derive

end

/-!
# Argon2 on x86 (32-bit): the derivation is constant time

`body_rel`: the body leaks the same trace in two runs with the same public
data and the same data-dependent references (`deriveX86.pub`), piece by
piece; `derive_ct`: so does the whole function, in its frames.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.Spec.Blake2 (bytesAt)

namespace Two
variable {s₀₁ s₀₂ : State} (T : VG.Proof.Argon2.X86.Derive.Two s₀₁ s₀₂)
include T

/-- The parameters' block leaks the same trace in two runs. -/
theorem parameters_rel :
    RelCT isa (fun s₁ s₂ => s₁ = entry s₀₁ ∧ s₂ = entry s₀₂)
      (.block (.mov .ebp (.reg .esp) :: Impl.Argon2.X86.Derive.parameters)) fun _ _ => True := by
  rw [← List.singleton_append]
  refine RelCT.block_split (RelCT.seqW (F₁ := fun s => s = entry s₀₁) (F₂ := fun s => s = entry s₀₂)
    (RelCT.taint (A := taint) (τr [.esp]) (fun s₁ s₂ h => agree_regs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1, h.2, entry_esp, entry_esp, T.pb.E]) (by taint_decide))
    (fun s h => by subst h; exact inv_start fun t i _ _ => WP.block_nil i)
    (fun s h => by subst h; exact inv_start fun t i _ _ => WP.block_nil i) ?_)
  exact T.leafI [] (fun s₁ s₂ h => ⟨h.1, h.2, by simp⟩) ⟨_, by taint_decide⟩

/-- The body leaks the same trace in two runs with the same data-dependent
references. -/
theorem body_rel
    (href : Spec.Argon2.references (prm s₀₁) (pwB s₀₁) (saltB s₀₁) (secB s₀₁) (adB s₀₁) =
      Spec.Argon2.references (prm s₀₂) (pwB s₀₂) (saltB s₀₂) (secB s₀₂) (adB s₀₂)) :
    RelCT isa (fun s₁ s₂ => s₁ = entry s₀₁ ∧ s₂ = entry s₀₂) Impl.Argon2.X86.Derive.body fun _ _ => True := by
  have pe := T.pb.prm_eq
  have L8 := VG.Proof.Argon2.X86.Derive.laneLen_ge T.hp₁
  have hind := Proof.Argon2.references_injective (prm s₀₁) (by omega) (pwB s₀₁) (saltB s₀₁) (secB s₀₁) (adB s₀₁)
    (pwB s₀₂) (saltB s₀₂) (secB s₀₂) (adB s₀₂) (by rw [href, pe])
  rw [← Proof.Argon2.iterations_fill, ← Proof.Argon2.iterations_fill] at hind
  unfold Impl.Argon2.X86.Derive.body
  refine RelCT.seqW T.parameters_rel (G₁ := fun t => VG.Proof.Argon2.X86.Derive.Inv s₀₁ t ∧ Prm s₀₁ t)
    (G₂ := fun t => VG.Proof.Argon2.X86.Derive.Inv s₀₂ t ∧ Prm s₀₂ t)
    (fun s h => by
      subst h
      rw [← List.append_nil (Instr.mov .ebp (.reg .esp) :: Impl.Argon2.X86.Derive.parameters)]
      exact parameters_ok T.hp₁ fun t i p => WP.block_nil ⟨i, p⟩)
    (fun s h => by
      subst h
      rw [← List.append_nil (Instr.mov .ebp (.reg .esp) :: Impl.Argon2.X86.Derive.parameters)]
      exact parameters_ok T.hp₂ fun t i p => WP.block_nil ⟨i, p⟩) ?_
  refine RelCT.seqW T.code_rel (fun s h => code_ok T.hp₁ h.1 h.2) (fun s h => code_ok T.hp₂ h.1 h.2) ?_
  refine RelCT.seqW T.memoryInit_rel (fun s h => memoryInit_ok T.hp₁ h.1 h.2.1 h.2.2)
    (fun s h => memoryInit_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  refine RelCT.seqW ((T.passes_rel (W₁ := Spec.Argon2.initMemory (prm s₀₁)
      (Spec.Argon2.initialHash (prm s₀₁) (pwB s₀₁) (saltB s₀₁) (secB s₀₁) (adB s₀₁)))
      (W₂ := Spec.Argon2.initMemory (prm s₀₂)
      (Spec.Argon2.initialHash (prm s₀₂) (pwB s₀₂) (saltB s₀₂) (secB s₀₂) (adB s₀₂)))
      (by rw [← pe]; exact hind)).mono (fun _ _ h => ⟨⟨h.1.1, h.1.2.1, h.1.2.2⟩, ⟨h.2.1, h.2.2.1, h.2.2.2⟩⟩)
      fun _ _ h => h)
    (fun s h => VG.Proof.Argon2.X86.Derive.passes_ok T.hp₁ ⟨h.1, h.2.1, h.2.2⟩) (fun s h => VG.Proof.Argon2.X86.Derive.passes_ok T.hp₂ ⟨h.1, h.2.1, h.2.2⟩) ?_
  refine RelCT.seqW (T.reduce_rel.mono (fun _ _ h => ⟨⟨h.1.inv, h.1.pr, h.1.mem⟩, ⟨h.2.inv, h.2.pr, h.2.mem⟩⟩)
      fun _ _ h => h)
    (fun s h => VG.Proof.Argon2.X86.Derive.reduce_ok T.hp₁ h.inv h.pr h.mem) (fun s h => VG.Proof.Argon2.X86.Derive.reduce_ok T.hp₂ h.inv h.pr h.mem) ?_
  exact T.finalOutput_rel.mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h

end Two

/-- A frame around code related from the pushed states. -/
theorem frame_chain {P : State → State → Prop} {f : State → State} {rs : List Reg} {r : Reg} {k : Nat}
    {body : Prog isa} {Q : State → State → Prop}
    (hsp : ∀ s₁ s₂, P s₁ s₂ → (f s₁).gpr .esp = (f s₂).gpr .esp)
    (h : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = pushed rs (f s₁) ∧ b = pushed rs (f s₂)) body Q) :
    RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = f s₁ ∧ b = f s₂) (.frame (.push rs) body (.pop r k))
      fun _ _ => True :=
  RelCT.frame (fun a b ⟨s₁, s₂, hp, ha, hb⟩ => by subst ha hb; exact hsp s₁ s₂ hp)
    (h.mono (fun a b ⟨x, y, ⟨s₁, s₂, hp, hx, hy⟩, ha, hb⟩ => ⟨s₁, s₂, hp, by rw [ha, hx], by rw [hb, hy]⟩)
      fun _ _ h => h)

/-- The derivation leaks the same trace in two runs with the same public data. -/
theorem derive_rel :
    RelCT isa (fun s₁ s₂ => deriveX86.pre s₁ ∧ deriveX86.pre s₂ ∧ deriveX86.pub s₁ s₂)
      Impl.Argon2.X86.Derive.derive fun _ _ => True := by
  have esp : ∀ s₁ s₂ : State, s₁.gpr .esp = s₂.gpr .esp → ∀ rs : List Reg,
      (pushed rs s₁).gpr .esp = (pushed rs s₂).gpr .esp := fun s₁ s₂ h rs => by
    rw [pushed_esp, pushed_esp, h]
  refine (VG.Proof.Argon2.X86.Derive.frame_chain (f := id) (fun s₁ s₂ h => h.2.2.1.1) (VG.Proof.Argon2.X86.Derive.frame_chain (f := fun s => pushed [.ebp] s)
    (fun s₁ s₂ h => esp _ _ h.2.2.1.1 _) (VG.Proof.Argon2.X86.Derive.frame_chain (f := fun s => pushed [.edi] (pushed [.ebp] s))
    (fun s₁ s₂ h => esp _ _ (esp _ _ h.2.2.1.1 _) _)
    (VG.Proof.Argon2.X86.Derive.frame_chain (f := fun s => pushed [.esi] (pushed [.edi] (pushed [.ebp] s)))
    (fun s₁ s₂ h => esp _ _ (esp _ _ (esp _ _ h.2.2.1.1 _) _) _)
    (VG.Proof.Argon2.X86.Derive.frame_chain (Q := fun _ _ => True) (f := fun s => pushed [.ebx] (pushed [.esi] (pushed [.edi] (pushed [.ebp] s))))
    (fun s₁ s₂ h => esp _ _ (esp _ _ (esp _ _ (esp _ _ h.2.2.1.1 _) _) _) _) ?_))))).mono
    (fun s₁ s₂ h => ⟨s₁, s₂, h, rfl, rfl⟩) fun _ _ h => h
  intro a b t₁ t₂ a' b' ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, ha, hb⟩ e₁ e₂
  exact Two.body_rel ⟨h₁, h₂, hpub.1⟩ hpub.2 a b t₁ t₂ a' b' ⟨ha, hb⟩ e₁ e₂

theorem derive_ct : ConstantTime isa deriveX86.pre deriveX86.pub Impl.Argon2.X86.Derive.derive :=
  derive_rel.constantTime

end VG.Proof.Argon2.X86.Derive

end

/-!
# Argon2 on x86 (32-bit): the derivation is verified

`derive_verified`: the derivation against `deriveX86` (correct, constant
time, and satisfiable: `satState`). `deriveShared_verified`: against the
shared contract `Spec.Argon2.deriveContract`, which also lets the code write
its arguments, by narrowing (`deriveWide`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86

/-! ## A state satisfying the precondition -/

/-- The arguments: Argon2d, empty inputs, one pass over 8 KiB in one lane, a
4-byte tag. -/
def satArgs : List Nat := [0, 0, 0, 0, 0, 1, 8, 1, 1, 0, 0, 0, 0, 0x10000, 8, 0x20000, 0x30000, 4]

/-- Memory holding `satArgs` at `0x40004`. -/
def satMem (a : Addr) : Byte :=
  if 0x40004 ≤ a.toNat ∧ a.toNat < 0x4004C then
    ((BitVec.ofNat 32 (VG.Proof.Argon2.X86.Derive.satArgs[(a.toNat - 0x40004) / 4]?.getD 0)) >>> (8 * ((a.toNat - 0x40004) % 4))).setWidth 8
  else 0

def satState : State where
  gpr r := match r with
    | .esp => 0x40000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Argon2.X86.Derive.satMem
  rd := [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x40004, 72⟩]
  wr := [⟨0x10000, 8192⟩, ⟨0x20000, 16384⟩, ⟨0x30000, 4⟩]

theorem sat_args : ∀ i < 18, VG.X86.arg VG.Proof.Argon2.X86.Derive.satState i = BitVec.ofNat 32 (VG.Proof.Argon2.X86.Derive.satArgs[i]?.getD 0) := by decide

theorem sat_pre : DPre VG.Proof.Argon2.X86.Derive.satState := by
  have a : ∀ i < 18, VG.X86.arg VG.Proof.Argon2.X86.Derive.satState i = BitVec.ofNat 32 (VG.Proof.Argon2.X86.Derive.satArgs[i]?.getD 0) := VG.Proof.Argon2.X86.Derive.sat_args
  have e : argAddr VG.Proof.Argon2.X86.Derive.satState 0 = 0x40004 := by decide
  have esp : satState.gpr .esp = 0x40000 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [pwR, saltR, secR, adR, memR, VG.Proof.Argon2.X86.Derive.scrR, VG.Proof.Argon2.X86.Derive.outR, VG.Proof.Argon2.X86.Derive.argR, VG.Proof.Argon2.X86.Derive.retR, VG.Proof.Argon2.X86.Derive.stkR, pwP, pwL, saltP, saltL, secP,
    secL, adP, adL, memP, blocksN, scrP, outP, outL, E0, kindV, itersN, mcostN, lanesN, threadsN, prm,
    a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide), a 4 (by decide), a 5 (by decide),
    a 6 (by decide), a 7 (by decide), a 8 (by decide), a 9 (by decide), a 10 (by decide), a 11 (by decide),
    a 12 (by decide), a 13 (by decide), a 14 (by decide), a 15 (by decide), a 16 (by decide), a 17 (by decide),
    e, esp]
  all_goals first
    | rfl
    | decide
    | (intro r hr w hw
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hw
       rcases hr with rfl | rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
         exact Region.disjoint_of_sep (by decide))
    | (intro w hw
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
       rcases hw with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))
    | (intro r hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))
    | exact Region.disjoint_of_sep (by decide)

theorem derive_verified : Verified X86.target Impl.Argon2.X86.Derive.derive deriveX86 :=
  ⟨fun _ hs => VG.Proof.Argon2.X86.Derive.correct hs, VG.Proof.Argon2.X86.Derive.derive_ct, ⟨VG.Proof.Argon2.X86.Derive.satState, VG.Proof.Argon2.X86.Derive.sat_pre⟩⟩

/-! ## Writable arguments, and the shared contract -/

/-- `deriveX86`, with the arguments writable, as `Sig.contract` lays the
regions out. -/
def deriveWide : Contract X86.isa :=
  { deriveX86 with
    pre := fun s =>
      let pw : Region := ⟨(VG.X86.arg s 1).setWidth 64, (VG.X86.arg s 2).toNat⟩
      let salt : Region := ⟨(VG.X86.arg s 3).setWidth 64, (VG.X86.arg s 4).toNat⟩
      let sec : Region := ⟨(VG.X86.arg s 9).setWidth 64, (VG.X86.arg s 10).toNat⟩
      let ad : Region := ⟨(VG.X86.arg s 11).setWidth 64, (VG.X86.arg s 12).toNat⟩
      let mem : Region := ⟨(VG.X86.arg s 13).setWidth 64, (VG.X86.arg s 14).toNat * 1024⟩
      let scr : Region := ⟨(VG.X86.arg s 15).setWidth 64, 16384⟩
      let out : Region := ⟨(VG.X86.arg s 16).setWidth 64, (VG.X86.arg s 17).toNat⟩
      let args : Region := ⟨argAddr s 0, 72⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 244, 244⟩
      s.rd = [pw, salt, sec, ad] ∧ s.wr = [mem, scr, out, args] ∧
      pw.Disjoint mem ∧ pw.Disjoint scr ∧ pw.Disjoint out ∧ salt.Disjoint mem ∧ salt.Disjoint scr ∧
      salt.Disjoint out ∧ sec.Disjoint mem ∧ sec.Disjoint scr ∧ sec.Disjoint out ∧ ad.Disjoint mem ∧
      ad.Disjoint scr ∧ ad.Disjoint out ∧ args.Disjoint mem ∧ args.Disjoint scr ∧ args.Disjoint out ∧
      mem.Disjoint scr ∧ mem.Disjoint out ∧ scr.Disjoint out ∧
      ret.Disjoint mem ∧ ret.Disjoint scr ∧ ret.Disjoint out ∧
      stack.Disjoint pw ∧ stack.Disjoint salt ∧ stack.Disjoint sec ∧ stack.Disjoint ad ∧ stack.Disjoint mem ∧
      stack.Disjoint scr ∧ stack.Disjoint out ∧
      (VG.X86.arg s 1).toNat + (VG.X86.arg s 2).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 3).toNat + (VG.X86.arg s 4).toNat ≤ 2 ^ 32 ∧
      (VG.X86.arg s 9).toNat + (VG.X86.arg s 10).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 11).toNat + (VG.X86.arg s 12).toNat ≤ 2 ^ 32 ∧
      (VG.X86.arg s 13).toNat + (VG.X86.arg s 14).toNat * 1024 ≤ 2 ^ 32 ∧ (VG.X86.arg s 15).toNat + 16384 ≤ 2 ^ 32 ∧
      (VG.X86.arg s 16).toNat + (VG.X86.arg s 17).toNat ≤ 2 ^ 32 ∧ 244 ≤ (s.gpr .esp).toNat ∧
      (s.gpr .esp).toNat + 4 + 72 ≤ 2 ^ 32 ∧ (VG.X86.arg s 0).toNat ≤ 2 ∧
      Spec.Argon2.valid (Spec.Argon2.params (VG.X86.arg s 0).toNat (VG.X86.arg s 5).toNat (VG.X86.arg s 6).toNat (VG.X86.arg s 7).toNat
        (VG.X86.arg s 17).toNat) (VG.X86.arg s 2).toNat (VG.X86.arg s 4).toNat (VG.X86.arg s 10).toNat (VG.X86.arg s 12).toNat ∧
      1 ≤ (VG.X86.arg s 8).toNat ∧ (VG.X86.arg s 8).toNat < 2 ^ 24 ∧
      (VG.X86.arg s 14).toNat = (Spec.Argon2.params (VG.X86.arg s 0).toNat (VG.X86.arg s 5).toNat (VG.X86.arg s 6).toNat (VG.X86.arg s 7).toNat
        (VG.X86.arg s 17).toNat).blocks }

/-- A state satisfying `deriveWide.pre`. -/
def satWide : State where
  gpr := satState.gpr
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Argon2.X86.Derive.satMem
  rd := [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  wr := [⟨0x10000, 8192⟩, ⟨0x20000, 16384⟩, ⟨0x30000, 4⟩, ⟨0x40004, 72⟩]

macro "dnarrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [deriveX86, deriveWide, VG.X86.arg_withRegions, VG.X86.argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_mem, State.withRegions_rd, State.withRegions_wr] $(loc)?)

theorem deriveWide_pre {s : State} (h : deriveWide.pre s) :
    DPre (s.withRegions [⟨(VG.X86.arg s 1).setWidth 64, (VG.X86.arg s 2).toNat⟩, ⟨(VG.X86.arg s 3).setWidth 64, (VG.X86.arg s 4).toNat⟩,
      ⟨(VG.X86.arg s 9).setWidth 64, (VG.X86.arg s 10).toNat⟩, ⟨(VG.X86.arg s 11).setWidth 64, (VG.X86.arg s 12).toNat⟩, ⟨argAddr s 0, 72⟩]
      [⟨(VG.X86.arg s 13).setWidth 64, (VG.X86.arg s 14).toNat * 1024⟩, ⟨(VG.X86.arg s 15).setWidth 64, 16384⟩,
        ⟨(VG.X86.arg s 16).setWidth 64, (VG.X86.arg s 17).toNat⟩]) := by
  obtain ⟨_, _, d₁, d₂, d₃, d₄, d₅, d₆, d₇, d₈, d₉, d₁₀, d₁₁, d₁₂, d₁₃, d₁₄, d₁₅, m₁, m₂, m₃, r₁, r₂, r₃,
    k₁, k₂, k₃, k₄, k₅, k₆, k₇, f₁, f₂, f₃, f₄, f₅, f₆, f₇, lo, hi, kd, vd, t₁, t₂, bl⟩ := h
  have e : (⟨((s.gpr .esp) - BitVec.ofNat 32 244).setWidth 64, 244⟩ : Region) =
      ⟨(s.gpr .esp).setWidth 64 - 244, 244⟩ := by rw [Taint.sub_setWidth lo]; rfl
  refine
    { rd := rfl
      wr := rfl
      ro_w := ?_
      mem_scr := m₁
      mem_out := m₂
      scr_out := m₃
      ret_w := ?_
      stk_all := ?_
      pw_fits := f₁
      salt_fits := f₂
      sec_fits := f₃
      ad_fits := f₄
      mem_fits := f₅
      scr_fits := f₆
      out_fits := f₇
      esp_lo := lo
      esp_hi := (by show (s.gpr .esp).toNat + 76 ≤ 2 ^ 32; omega)
      kind_le := kd
      valid := vd
      threads := ⟨t₁, t₂⟩
      blocks := bl }
  · show ∀ r ∈ [(⟨(VG.X86.arg s 1).setWidth 64, (VG.X86.arg s 2).toNat⟩ : Region), ⟨(VG.X86.arg s 3).setWidth 64, (VG.X86.arg s 4).toNat⟩,
        ⟨(VG.X86.arg s 9).setWidth 64, (VG.X86.arg s 10).toNat⟩, ⟨(VG.X86.arg s 11).setWidth 64, (VG.X86.arg s 12).toNat⟩, ⟨argAddr s 0, 72⟩],
      ∀ w ∈ [(⟨(VG.X86.arg s 13).setWidth 64, (VG.X86.arg s 14).toNat * 1024⟩ : Region), ⟨(VG.X86.arg s 15).setWidth 64, 16384⟩,
        ⟨(VG.X86.arg s 16).setWidth 64, (VG.X86.arg s 17).toNat⟩], r.Disjoint w
    intro r hr w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hw
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> with_reducible assumption
  · show ∀ w ∈ [(⟨(VG.X86.arg s 13).setWidth 64, (VG.X86.arg s 14).toNat * 1024⟩ : Region), ⟨(VG.X86.arg s 15).setWidth 64, 16384⟩,
        ⟨(VG.X86.arg s 16).setWidth 64, (VG.X86.arg s 17).toNat⟩], (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint w
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> with_reducible assumption
  · show ∀ r ∈ [(⟨(VG.X86.arg s 1).setWidth 64, (VG.X86.arg s 2).toNat⟩ : Region), ⟨(VG.X86.arg s 3).setWidth 64, (VG.X86.arg s 4).toNat⟩,
        ⟨(VG.X86.arg s 9).setWidth 64, (VG.X86.arg s 10).toNat⟩, ⟨(VG.X86.arg s 11).setWidth 64, (VG.X86.arg s 12).toNat⟩,
        ⟨(VG.X86.arg s 13).setWidth 64, (VG.X86.arg s 14).toNat * 1024⟩, ⟨(VG.X86.arg s 15).setWidth 64, 16384⟩,
        ⟨(VG.X86.arg s 16).setWidth 64, (VG.X86.arg s 17).toNat⟩], (below (s.gpr .esp) 244).Disjoint r
    rw [show below (s.gpr .esp) 244 = ⟨(s.gpr .esp).setWidth 64 - 244, 244⟩ from e]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem deriveWide_verified : Verified X86.target Impl.Argon2.X86.Derive.derive VG.Proof.Argon2.X86.Derive.deriveWide :=
  Verified.narrowTo VG.Proof.Argon2.X86.Derive.derive_verified
    (fun s => [⟨(VG.X86.arg s 1).setWidth 64, (VG.X86.arg s 2).toNat⟩, ⟨(VG.X86.arg s 3).setWidth 64, (VG.X86.arg s 4).toNat⟩,
      ⟨(VG.X86.arg s 9).setWidth 64, (VG.X86.arg s 10).toNat⟩, ⟨(VG.X86.arg s 11).setWidth 64, (VG.X86.arg s 12).toNat⟩, ⟨argAddr s 0, 72⟩])
    (fun s => [⟨(VG.X86.arg s 13).setWidth 64, (VG.X86.arg s 14).toNat * 1024⟩, ⟨(VG.X86.arg s 15).setWidth 64, 16384⟩,
      ⟨(VG.X86.arg s 16).setWidth 64, (VG.X86.arg s 17).toNat⟩])
    (fun _ h => VG.Proof.Argon2.X86.Derive.deriveWide_pre h)
    (fun _ h => by
      obtain ⟨h₁, h₂, _⟩ := h
      rw [h₁, h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), 0,
          by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self))), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), 0,
          by simp, by simp⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩)
    (fun _ _ _ h => by dnarrow at h ⊢; exact h)
    (fun _ _ _ _ h => by dnarrow; exact h)
    ⟨VG.Proof.Argon2.X86.Derive.satWide, by
      have a : ∀ i < 18, VG.X86.arg VG.Proof.Argon2.X86.Derive.satWide i = BitVec.ofNat 32 (VG.Proof.Argon2.X86.Derive.satArgs[i]?.getD 0) := VG.Proof.Argon2.X86.Derive.sat_args
      have e : argAddr VG.Proof.Argon2.X86.Derive.satWide 0 = 0x40004 := by decide
      simp only [VG.Proof.Argon2.X86.Derive.deriveWide, a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide), a 4 (by decide),
        a 5 (by decide), a 6 (by decide), a 7 (by decide), a 8 (by decide), a 9 (by decide), a 10 (by decide),
        a 11 (by decide), a 12 (by decide), a 13 (by decide), a 14 (by decide), a 15 (by decide),
        a 16 (by decide), a 17 (by decide), e]
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩ <;>
      exact Region.disjoint_of_sep (by decide)⟩

theorem derive_implies : deriveWide.Implies (Spec.Argon2.deriveContract X86.abi 244) := by
  sig_implies [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, VG.Proof.Argon2.X86.Derive.deriveWide, deriveX86,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [satWide, satState, satMem, satArgs, X86.arg, X86.argAddr, Mem.readW, Mem.read, Spec.Argon2.params,
      Spec.Argon2.valid, Spec.Argon2.Params.blocks, Spec.Argon2.Params.segmentLen] using VG.Proof.Argon2.X86.Derive.satWide

/-- The emitted function, against the shared contract. -/
theorem deriveShared_verified :
    Verified X86.target Impl.Argon2.X86.Derive.derive (Spec.Argon2.deriveContract X86.abi 244) :=
  deriveWide_verified.of_implies VG.Proof.Argon2.X86.Derive.derive_implies

end VG.Proof.Argon2.X86.Derive

end
