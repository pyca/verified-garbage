import VerifiedGarbage.Proof.Argon2.FillStep
import VerifiedGarbage.Proof.Argon2.FillPositions
import VerifiedGarbage.Proof.Argon2.X86.Derive.MemoryInit

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
    refine wp_add fun s₁ u₁ _ => dblA_ok (s := s₁) n ?_ fun t ht kt ot => k t ?_
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
theorem blockAddr_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {lane col : Nat} (hl : lane < lanesN s₀)
    (hc : col < (prm s₀).laneLen) (ha : s.gpr .eax = BitVec.ofNat 32 lane) (hcx : s.gpr .ecx = BitVec.ofNat 32 col)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .eax = memP s₀ + BitVec.ofNat 32 ((lane * (prm s₀).laneLen + col) * 1024) →
      t.gpr .ecx = s.gpr .ecx → Divide.Keep s t → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.X86.Derive.blockAddr ++ is)) s Q := by
  obtain ⟨cl, cf⟩ := cell_fits hp hl hc
  have hb := hp.blocks_lt
  have lt := hp.lanes_lt
  have hL : (prm s₀).laneLen < 2 ^ 32 := by
    have := Nat.le_mul_of_pos_left (prm s₀).laneLen (show 0 < lanesN s₀ from hp.lanes_pos)
    have e := hp.blocks_eq
    omega
  have lL : lane * (prm s₀).laneLen < 2 ^ 32 := by omega
  unfold Impl.Argon2.X86.Derive.blockAddr
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_ldloc hp h (d := laneLenOff) (by decide) fun s₁ u₁ => wp_mul fun s₂ a₂ d₂ k₂ o₂ =>
    wp_add fun s₃ u₃ _ => ?_
  have i₃ := ((h.upd u₁ (by decide) (by decide)).keep k₂).upd u₃ (by decide) (by decide)
  have e₃ : (s₃.gpr .eax).toNat = lane * (prm s₀).laneLen + col := by
    rw [u₃.gpr, o₂ .ecx (by decide) (by decide), u₁.other .ecx (by decide), hcx, a₂, u₁.other .eax (by decide), ha,
      u₁.gpr, pr.laneLen, BitVec.toNat_add, Wp.toNat_ofNat_lt (k := lane) (by omega), Wp.toNat_ofNat_lt hL,
      Wp.toNat_ofNat_lt lL, Wp.toNat_ofNat_lt (k := col) (by omega), Nat.mod_eq_of_lt (by omega)]
  refine dblA_ok 10 (by rw [e₃]; omega) fun s₄ e₄ k₄ o₄ => ?_
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

theorem Pos.of_mem {s₀ s t : State} {pass slice lane index : Nat} (h : Pos s₀ s pass slice lane index)
    (hm : t.mem = s.mem) : Pos s₀ t pass slice lane index :=
  ⟨by rw [lw_mem hm]; exact h.pass, by rw [lw_mem hm]; exact h.slice, by rw [lw_mem hm]; exact h.lane,
    by rw [lw_mem hm]; exact h.index⟩

theorem Pos.of_lw {s₀ s t : State} {pass slice lane index : Nat} (h : Pos s₀ s pass slice lane index)
    (hl : ∀ d ∈ [Impl.Argon2.X86.Derive.passOff, sliceOff, laneOff, indexOff], lw s₀ t d = lw s₀ s d) :
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

/-- `column`: `eax` and `ecx :=` the current column, `slice · segLen + index`. -/
theorem column_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {pass slice lane index : Nat}
    (ps : Pos s₀ s pass slice lane index) (hs : slice < 4) (hi : index < (prm s₀).segmentLen)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .eax = BitVec.ofNat 32 (slice * (prm s₀).segmentLen + index) →
      t.gpr .ecx = BitVec.ofNat 32 (slice * (prm s₀).segmentLen + index) → Divide.Keep s t →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.X86.Derive.column ++ is)) s Q := by
  have sl := segLen_lt hp
  have hc := Proof.Argon2.column_lt (prm s₀) hp.lanes_pos hs hi
  have := laneLen_ge hp
  have ll := hp.laneLen_eq
  unfold Impl.Argon2.X86.Derive.column
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc hp h (d := sliceOff) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁ (by decide) (by decide)
  refine wp_ldloc hp i₁ (d := segLenOff) (by decide) fun s₂ u₂ => wp_mul fun s₃ a₃ _ k₃ _ => ?_
  have i₃ := (i₁.upd u₂ (by decide) (by decide)).keep k₃
  have m₃ : s₃.mem = s.mem := by rw [k₃.mem, u₂.mem, u₁.mem]
  refine wp_addm i₃.ebp (loc_in' hp i₃ (d := indexOff) (by decide)) fun s₄ u₄ => wp_mov fun t u => k t ?_ ?_ ?_
  · have e : s₄.gpr .eax = BitVec.ofNat 32 (slice * (prm s₀).segmentLen + index) := by
      rw [u₄.gpr, a₃, u₂.other _ (by decide), u₁.gpr, u₂.gpr, lw_mem u₁.mem, ps.slice, pr.segLen,
        show s₃.mem.readW (addr (E s₀) indexOff) 32 = lw s₀ s₃ indexOff from rfl, lw_mem m₃, ps.index,
        Wp.toNat_ofNat_lt (by omega), Wp.toNat_ofNat_lt (by omega), BitVec.ofNat_add_ofNat]
    rw [u.other _ (by decide), e]
  · rw [u.gpr, u₄.gpr, a₃, u₂.other _ (by decide), u₁.gpr, u₂.gpr, lw_mem u₁.mem, ps.slice, pr.segLen,
      show s₃.mem.readW (addr (E s₀) indexOff) 32 = lw s₀ s₃ indexOff from rfl, lw_mem m₃, ps.index,
      Wp.toNat_ofNat_lt (by omega), Wp.toNat_ofNat_lt (by omega), BitVec.ofNat_add_ofNat]
  · exact (((Divide.Keep.of_upd u₁ (by simp)).trans (Divide.Keep.of_upd u₂ (by simp))).trans
      (k₃.trans (Divide.Keep.of_upd u₄ (by simp)))).trans (Divide.Keep.of_upd u (by simp))

/-- `prevColumn`: `ecx :=` the column before `ecx`, cyclically. -/
theorem prevColumn_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {col : Nat} (hc : col < (prm s₀).laneLen)
    (hx : s.gpr .ecx = BitVec.ofNat 32 col) :
    WP isa Impl.Argon2.X86.Derive.prevColumn s fun t =>
      t.gpr .ecx = BitVec.ofNat 32 ((col + (prm s₀).laneLen - 1) % (prm s₀).laneLen) ∧ Divide.Keep s t := by
  have sl := segLen_lt hp
  have := laneLen_ge hp
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
theorem prevPointer_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {pass slice lane index : Nat}
    (ps : Pos s₀ s pass slice lane index) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) :
    WP isa Impl.Argon2.X86.Derive.prevPointer s fun t =>
      t.gpr .eax = memP s₀ + BitVec.ofNat 32 ((lane * (prm s₀).laneLen +
        (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) % (prm s₀).laneLen) * 1024) ∧
      Divide.Keep s t := by
  have hc := Proof.Argon2.column_lt (prm s₀) hp.lanes_pos hs hi
  have := laneLen_ge hp
  unfold Impl.Argon2.X86.Derive.prevPointer
  refine WP.seq ?_
  rw [← List.append_nil Impl.Argon2.X86.Derive.column]
  refine column_ok hp h pr ps hs hi fun s₁ _ c₁ k₁ => WP.block_nil ?_
  refine WP.seq ((prevColumn_ok hp (h.keep k₁) (pr.of_mem k₁.mem) hc c₁).mono fun s₂ ⟨c₂, k₂⟩ => ?_)
  have i₂ := (h.keep k₁).keep k₂
  have m₂ : s₂.mem = s.mem := by rw [k₂.mem, k₁.mem]
  refine wp_ldloc hp i₂ (d := laneOff) (by decide) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃ (by decide) (by decide)
  rw [← List.append_nil Impl.Argon2.X86.Derive.blockAddr]
  refine blockAddr_ok hp i₃ (pr.of_mem (by rw [u₃.mem, m₂])) hl (Nat.mod_lt _ (by omega))
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
    (ctr = 0 ∨ 1 ≤ ctr ∧ blk s.mem (scrP s₀) 6144 = addressBlock (prm s₀) pass lane slice ctr)

/-- The counter after a block: the index's group, for data-independent addressing. -/
def ctrNext (p : Spec.Argon2.Params) (pass slice index ctr : Nat) : Nat :=
  if independent p pass slice then index / 128 + 1 else ctr

/-- The filling loops' state at a position, the memory matrix holding `st`'s. -/
structure FS (s₀ : State) (pass slice lane index ctr : Nat) (st : FillState) (s : State) : Prop where
  inv : Inv s₀ s
  pr : Prm s₀ s
  pos : Pos s₀ s pass slice lane index
  cache : CacheOk s₀ pass lane slice ctr s
  mem : Represents s.mem (memB s₀) (prm s₀).blocks st.memory

theorem Divide.Keep.of_fupd {s t : State} (f : Fupd s t) : Divide.Keep s t :=
  ⟨fun _ _ _ _ => by rw [f.gpr], f.mem, f.rd, f.wr⟩

theorem Represents.keep {m m' : Mem} {base : Addr} {n : Nat} {b : Array Block}
    (h : Represents m base n b) (hk : ∀ k < n, blockAt m' (matrixCell base k) = blockAt m (matrixCell base k)) :
    Represents m' base n b :=
  ⟨h.size, fun k hk' => (hk k hk').trans (h.block k hk')⟩

/-- The block at `B + o`, from `B + o` as its base. -/
theorem blk_shift (m : Mem) (B : BitVec 32) (o : Nat) : blk m (B + BitVec.ofNat 32 o) 0 = blk m B o := by
  apply Vector.ext
  intro j hj
  simp only [blk, Vector.getElem_ofFn, rd64, addr, Nat.zero_add, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
    Nat.add_assoc]

/-- The cells of the matrix, as `blk`. -/
theorem cell_blk {s₀ : State} (hp : DPre s₀) (m : Mem) {k : Nat} (hk : k < blocksN s₀) :
    blockAt m (matrixCell (memB s₀) k) = blk m (memP s₀) (k * 1024) := by
  have := hp.mem_fits
  have : k * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega
  rw [← cell_addr hp hk, Proof.Argon2.X86.blockAt_eq (by rw [add_nat (by omega)]; omega), blk_shift]

/-- The first word of a block. -/
theorem blk_zero (m : Mem) (B : BitVec 32) (o : Nat) :
    (blk m B o)[0] = m.readW (addr B (o + 4)) 32 ++ m.readW (addr B o) 32 := by
  simp only [blk, Vector.getElem_ofFn, rd64, Nat.mul_zero, Nat.add_zero]

/-- Word `j` of a block. -/
theorem blk_get (m : Mem) (B : BitVec 32) (o j : Nat) (hj : j < 128) :
    (blk m B o)[j] = m.readW (addr B (o + 8 * j + 4)) 32 ++ m.readW (addr B (o + 8 * j)) 32 := by
  simp only [blk, Vector.getElem_ofFn, rd64]

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
theorem addressMode_ok {s : State} (h : Inv s₀ s) {pass slice lane index : Nat}
    (ps : Pos s₀ s pass slice lane index) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa (.block Impl.Argon2.X86.Derive.addressMode) s fun t =>
      t.zf = some (!independent (prm s₀) pass slice) ∧ Divide.Keep s t := by
  have hk := hp.kind_le
  unfold Impl.Argon2.X86.Derive.addressMode
  refine wp_ldarg hp h (i := 0) (by decide) fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_xori fun s₃ u₃ =>
    wp_cmpi fun s₄ f₄ c₄ _ => wp_sbb_self c₄ fun s₅ u₅ => wp_mov fun s₆ u₆ => wp_xori fun s₇ u₇ =>
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
    rw [z, u₁₉.gpr, e₁₈, e₁₇, e₁₃, e₉, e₅, independent_eq hk]
    have k3 : decide ((kindV s₀ ^^^ 1).toNat < 1) = decide ((kindV s₀).toNat = 1) ∧
        decide ((kindV s₀ ^^^ 2).toNat < 1) = decide ((kindV s₀).toNat = 2) := by
      rcases (by omega : (kindV s₀).toNat = 0 ∨ (kindV s₀).toNat = 1 ∨ (kindV s₀).toNat = 2) with e | e | e <;>
        · rw [show kindV s₀ = BitVec.ofNat 32 (kindV s₀).toNat by simp, e]; decide
    rw [k3.1, k3.2, show decide (pass < 1) = decide (pass = 0) by simp only [Nat.lt_one_iff],
      mode_bits]
  · exact (((((((K₁₃.trans (Divide.Keep.of_upd u₁₄ (by simp))).trans (Divide.Keep.of_fupd f₁₅)).trans
      (Divide.Keep.of_upd u₁₆ (by simp))).trans (Divide.Keep.of_upd u₁₇ (by simp))).trans
      (Divide.Keep.of_upd u₁₈ (by simp))).trans (Divide.Keep.of_upd u₁₉ (by simp))).trans (Divide.Keep.of_fupd f))

end

end VG.Proof.Argon2.X86.Derive
