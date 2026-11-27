module

public import VerifiedGarbage.Proof.Argon2.FillStep
import VerifiedGarbage.Proof.Argon2.FillPositions
public import VerifiedGarbage.Proof.Argon2.Arm.Derive.FillCall
import VerifiedGarbage.Proof.Argon2.Arm.Derive.Initial
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.Matrix
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Sha512.Arm.Rounds
import VerifiedGarbage.Proof.Argon2.Arm.CompressLit
import VerifiedGarbage.Proof.Blake2.Arm.CompressB
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Argon2.Arm.CompressVerified
import VerifiedGarbage.Proof.Blake2.Arm.Stream.Update
import VerifiedGarbage.Proof.Argon2.Reference
import VerifiedGarbage.Proof.Argon2.Dimensions
public import VerifiedGarbage.Proof.Argon2.AddressInput

/-! ### `Argon2.Arm.Derive.FillCache`, which this module and modules that import it used -/

section

/-! ### `Argon2.Arm.Derive.FillInput`, which this module and modules that import it used -/

section

/-! ### `Argon2.Arm.Derive.FillDep`, which the modules that import this one used -/

section

/-!
# Argon2 on ARMv7: what keeps the filling state, and data-dependent addressing

`FS.keep`: the filling state is kept by steps that keep the parameters, the
position and counter in the locals, the cached address block and the
matrix. `dependentWord_ok`: J₁ and J₂ are the first word of the previous
block.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_ldr)
open VG.Spec.Argon2 (Block zeroBlock FillState)
open VG.Proof.Argon2.Arm (blk)
open VG.Proof.Sha512.Arm (Only A)
open VG.Impl.Argon2.Arm.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  divisorOff strideOff j1Off j2Off)

/-- The offsets of the locals the filling state is about. -/
abbrev fsOffs : List Nat :=
  [divisorOff, segLenOff, laneLenOff, strideOff, passOff, sliceOff, laneOff, indexOff, counterOff]

theorem FS.keep {s₀ s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (it : Inv s₀ t) (hl : ∀ d ∈ fsOffs, lw s₀ t d = lw s₀ s d)
    (hc : blk t.mem (scrP s₀) 6144 = blk s.mem (scrP s₀) 6144)
    (hm : ∀ k < (prm s₀).blocks, blockAt t.mem (matrixCell (memB s₀) k) = blockAt s.mem (matrixCell (memB s₀) k)) :
    FS s₀ pass slice lane index ctr st t := by
  refine ⟨it, Prm.of_lw h.pr fun d hd => hl d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
    h.pos.of_lw fun d hd => hl d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
    ?_, Represents.keep h.mem hm⟩
  obtain ⟨c0, c1, c2 | ⟨c3, c4⟩⟩ := h.cache
  · exact ⟨c0, by rw [hl _ (by simp)]; exact c1, .inl c2⟩
  · exact ⟨c0, by rw [hl _ (by simp)]; exact c1, .inr ⟨c3, by rw [hc]; exact c4⟩⟩

/-- A step that writes only registers but `r11` keeps the filling state. -/
theorem FS.of_only {s₀ s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) {ds : List Reg} (o : Only ds s t) (h11 : Reg.r11 ∉ ds) :
    FS s₀ pass slice lane index ctr st t :=
  h.keep (h.inv.only o h11) (fun d _ => lw_mem o.mem d) (by rw [o.mem]) fun _ _ => by rw [o.mem]

/-- `[B + o + d]` -/
theorem A_shift (B : BitVec 32) (o d : Nat) : A (B + BitVec.ofNat 32 o) d = A B (o + d) := by
  simp only [A, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- A block of `scratch`. -/
theorem scr_blk (m : Mem) {o : Nat} (ho : o + 1024 ≤ 16384) :
    blk m (scrP s₀) o = blockAt m (scrB s₀ + BitVec.ofNat 64 o) := by
  have := hp.scr_fits
  have f : (scrP s₀ + BitVec.ofNat 32 o).toNat + 1024 ≤ 2 ^ 32 := by rw [add_nat (by omega_arith)]; omega_arith
  rw [← scr_addr hp (by omega_arith), Proof.Argon2.Arm.blockAt_eq f, blk_shift]

/-- A word of the matrix is kept by a store to the locals. -/
theorem mem_loc_store {m : Mem} {d : Nat} (hd : d + 4 ≤ 144) (v : BitVec 32) {a : Addr}
    (ha : (memR s₀).Contains a 4) :
    (m.writeW (State.addr (E s₀ + BitVec.ofNat 32 d)) v).readW a 32 = m.readW a 32 :=
  ((Frame.refl [⟨State.addr (E s₀ + BitVec.ofNat 32 d), 4⟩] m).writeW (List.mem_singleton_self _) v
    (Region.contains_self _ _)).readW (r := memR s₀) ha (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (loc_disj hp hd (memR s₀) (by simp)).symm) (by decide)

/-- A store to the locals keeps what the filling state is about, but at the word `d`. -/
theorem FS.store {s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (it : Inv s₀ t) {d : Nat} (hd : d + 4 ≤ 144)
    (hd' : d ∉ fsOffs) (hd'' : d % 4 = 0) {v : BitVec 32}
    (hm : t.mem = s.mem.writeW (State.addr (E s₀ + BitVec.ofNat 32 d)) v) :
    FS s₀ pass slice lane index ctr st t := by
  have f : Frame [⟨State.addr (E s₀ + BitVec.ofNat 32 d), 4⟩] s.mem t.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) v (Region.contains_self _ _)
  refine h.keep it (fun e he => ?_) ?_ fun k hk => ?_
  · show t.mem.readW _ 32 = s.mem.readW _ 32
    rw [hm]
    simp only [fsOffs, List.mem_cons, List.not_mem_nil, or_false] at he hd'
    have : (e + 4 ≤ d ∨ d + 4 ≤ e) ∧ e + 4 ≤ 144 := by
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [divisorOff, segLenOff, laneLenOff, strideOff, passOff, sliceOff, laneOff, indexOff,
        counterOff] at hd' ⊢ <;> omega_arith
    exact lw_store hp (by omega_arith) (by omega_arith) this.1.symm v
  · rw [scr_blk hp t.mem (by decide), scr_blk hp s.mem (by decide)]
    refine blockAt_keep f fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact (loc_disj hp hd (scrR s₀) (by simp)).symm.sub_left (Offset.sub_base _ (by omega_arith))
  · refine blockAt_keep f fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have hk' : k < blocksN s₀ := by rw [hp.blocks]; exact hk
    exact (loc_disj hp hd (memR s₀) (by simp)).symm.sub_left (cell_in_mem hk')

/-- `dependentWord`: J₁ and J₂ are the halves of the previous block's first word. -/
theorem dependentWord_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) :
    WP isa Impl.Argon2.Arm.Derive.dependentWord s fun t => FS s₀ pass slice lane index ctr st t ∧
      lw s₀ t j2Off ++ lw s₀ t j1Off = (blockAt s.mem (matrixCell (memB s₀) (lane * (prm s₀).laneLen +
        (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) % (prm s₀).laneLen)))[0] := by
  have hm := hp.mem_fits
  have L8 := laneLen_ge hp
  obtain ⟨cl, cf⟩ := cell_fits hp hl (col := (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) %
    (prm s₀).laneLen) (Nat.mod_lt _ (by omega_arith))
  unfold Impl.Argon2.Arm.Derive.dependentWord
  refine WP.seq ((prevPointer_ok hp h.inv h.pr h.pos hl hs hi).mono fun s₁ ⟨a₁, k₁⟩ => ?_)
  generalize (lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) %
    (prm s₀).laneLen) = c at cl cf a₁ ⊢
  have h₁ := h.of_only k₁ (by decide)
  have inP : ∀ o, o + 4 ≤ 1024 → (memR s₀).Contains (A (memP s₀ + BitVec.ofNat 32 (c * 1024)) o) 4 :=
    fun o ho => by
      rw [A_shift, VG.Proof.Sha512.Arm.A_eq (by omega_arith)]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  have mW : ∀ t, Inv s₀ t → memR s₀ ∈ t.wr := fun t it => by rw [it.wr]; exact mem_mem hp
  refine wp_ldr (by decide) (by rw [a₁]) ⟨_, List.mem_append_right _ (mW _ h₁.inv), inP 0 (by decide)⟩
    fun s₂ u₂ => ?_
  have h₂ := h₁.of_only (Only.of_upd u₂) (by decide)
  refine wp_stloc hp h₂.inv (d := j1Off) (by decide) fun s₃ i₃ v₃ o₃ g₃ m₃ => ?_
  have h₃ := h₂.store hp i₃ (d := j1Off) (by decide) (by decide) (by decide) m₃
  refine wp_ldr (by decide) (by rw [g₃, u₂.other _ (by decide), a₁])
    ⟨_, List.mem_append_right _ (mW _ h₃.inv), inP 4 (by decide)⟩ fun s₄ u₄ => ?_
  have h₄ := h₃.of_only (Only.of_upd u₄) (by decide)
  refine wp_stloc hp h₄.inv (d := j2Off) (by decide) fun t it vt ot gt mt => WP.block_nil ⟨?_, ?_⟩
  · exact h₄.store hp it (d := j2Off) (by decide) (by decide) (by decide) mt
  · rw [vt, ot j1Off (by decide) (by decide), lw_mem u₄.mem, v₃, u₄.gpr, m₃,
      mem_loc_store hp (by decide) _ (inP 4 (by decide)), u₂.mem, u₂.gpr, k₁.mem, cell_blk hp _ cl, blk_zero,
      A_shift, A_shift, Nat.add_zero (c * 1024)]

end

/-- Regions a step of the filling loops may write without changing the filling state. -/
def Outside (s₀ : State) (r : Region) : Prop :=
  r.Disjoint (locR s₀) ∧ r.Disjoint ⟨scrB s₀ + BitVec.ofNat 64 6144, 1024⟩ ∧ r.Disjoint (memR s₀)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem loc_word_sub {d : Nat} (hd : d + 4 ≤ 144) :
    Region.Sub ⟨State.addr (E s₀ + BitVec.ofNat 32 d), 4⟩ (locR s₀) := by
  have := E_hi hp
  exact sub32 (by rw [loc_nat hp (by omega_arith)]; omega_arith) (by rw [loc_nat hp (by omega_arith)]; omega_arith)

theorem FS.frame {s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (it : Inv s₀ t) {rs : List Region} (f : Frame rs s.mem t.mem)
    (ho : ∀ r ∈ rs, Outside s₀ r) : FS s₀ pass slice lane index ctr st t := by
  refine h.keep it (fun d hd => ?_) ?_ fun k hk => ?_
  · have hd' : d + 4 ≤ 144 := by
      simp only [fsOffs, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact f.readW (r := ⟨State.addr (E s₀ + BitVec.ofNat 32 d), 4⟩) (Region.contains_self _ _)
      (fun r hr => (ho r hr).1.symm.sub_left (loc_word_sub hp hd')) (by decide)
  · rw [scr_blk hp t.mem (by decide), scr_blk hp s.mem (by decide)]
    exact blockAt_keep f fun r hr => (ho r hr).2.1.symm
  · have hk' : k < blocksN s₀ := by rw [hp.blocks]; exact hk
    exact blockAt_keep f fun r hr => (ho r hr).2.2.symm.sub_left (cell_in_mem hk')

theorem outside_scr {o n : Nat} (h : o + n ≤ 6144 ∨ (7168 ≤ o ∧ o + n ≤ 16384)) :
    Outside s₀ ⟨scrB s₀ + BitVec.ofNat 64 o, n⟩ := by
  have sub : Region.Sub ⟨scrB s₀ + BitVec.ofNat 64 o, n⟩ (scrR s₀) := Offset.sub_base _ (by omega_arith)
  refine ⟨(loc_disj' hp (R := scrR s₀) (by simp)).symm.sub_left sub, Offset.disjoint _ (by omega_arith) (by omega_arith)
    (by omega_arith), hp.mem_scr.symm.sub_left sub⟩

end

end VG.Proof.Argon2.Arm.Derive

end

end

/-!
# Argon2 on ARMv7: the input of the address block

`clearAt_ok`: `clearAt d` zeroes `scratch[d, d + 1024)`. `aheader_ok`: the
seven words of the address-generation input block (§3.4.1.2), at
`scratch + 5120`. `input_ok`: after both, the block there is
`addressInput`, and the one at `scratch + 7168` is zero.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_str op2_imm)
open VG.Spec.Argon2 (Block zeroBlock FillState)
open VG.Proof.Argon2.Arm (blk ofWords blk_of_words)
open VG.Proof.Sha512.Arm (A)
open VG.Impl.Argon2.Arm.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff)

/-- Words of `scratch`. -/
abbrev sw (s₀ : State) (m : Mem) (o : Nat) : BitVec 32 := m.readW (A (scrP s₀) o) 32

theorem toNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- A word of `scratch` after a store to another, or the same. -/
theorem sw_store (m : Mem) {a b : Nat} (ha : a + 4 ≤ 16384) (hb : b + 4 ≤ 16384)
    (h : a = b ∨ a + 4 ≤ b ∨ b + 4 ≤ a) (v : BitVec 32) :
    sw s₀ (m.writeW (A (scrP s₀) a) v) b = if a = b then v else sw s₀ m b := by
  by_cases e : a = b
  · subst e; rw [ite_eq_left rfl]; exact Mem.readW_writeW_self32 _ _ _
  · rw [ite_eq_right e, sw, sw, A, A, scr_addr hp (by omega_arith), scr_addr hp (by omega_arith)]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)

/-- `n` stores of `r0 = 0` to `[r2, #4k]`, with `r2 = scratch + d`. -/
theorem zeros_ok {s : State} (h : Inv s₀ s) {d : Nat} (hd : d + 1024 ≤ 16384)
    (hx : s.gpr .r2 = scrP s₀ + BitVec.ofNat 32 d) (ha : s.gpr .r0 = 0) :
    ∀ n ≤ 256, WP isa (.block ((List.range n).map fun k => Instr.str .r0 .r2 (4 * k))) s fun t =>
      Inv s₀ t ∧ t.gpr = s.gpr ∧ Frame [⟨scrB s₀ + BitVec.ofNat 64 d, 1024⟩] s.mem t.mem ∧
      ∀ i < n, sw s₀ t.mem (d + 4 * i) = 0
  | 0, _ => WP.block_nil ⟨h, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    have hs := hp.scr_fits
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append ((zeros_ok h hd hx ha n (by omega_arith)).mono fun t ⟨it, gt, ft, wt⟩ => ?_)
    have ea : State.addr (t.gpr .r2 + BitVec.ofNat 32 (4 * n)) = scrB s₀ + BitVec.ofNat 64 (d + 4 * n) := by
      rw [gt, hx, BitVec.add_assoc, BitVec.ofNat_add_ofNat, scr_addr hp (by omega_arith)]
    have hc : (scrR s₀).Contains (scrB s₀ + BitVec.ofNat 64 (d + 4 * n)) 4 :=
      Offset.contains_base _ (by omega_arith) (by omega_arith)
    have hc' : (⟨scrB s₀ + BitVec.ofNat 64 d, 1024⟩ : Region).Contains (scrB s₀ + BitVec.ofNat 64 (d + 4 * n)) 4 :=
      Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)
    refine wp_str (by omega_arith) ea ⟨_, by rw [it.wr]; exact scr_mem hp, hc⟩ fun t₁ u₁ => WP.block_nil
      ⟨it.store (R := scrR s₀) (by simp) hc u₁, by rw [u₁.gpr, gt], ?_, fun i hi => ?_⟩
    · rw [u₁.mem]
      exact ft.writeW (List.mem_singleton_self _) _ hc'
    · have e : scrB s₀ + BitVec.ofNat 64 (d + 4 * n) = A (scrP s₀) (d + 4 * n) := (scr_addr hp (by omega_arith)).symm
      rw [u₁.mem, e, gt, ha, sw_store hp _ (by omega_arith) (by omega_arith) (by omega_arith)]
      by_cases e : d + 4 * n = d + 4 * i
      · rw [ite_eq_left e]
      · rw [ite_eq_right e]; exact wt i (by omega_arith)

/-- `clearAt d`: zero `scratch[d, d + 1024)`. -/
theorem clearAt_ok {s : State} (h : Inv s₀ s) {d : Nat} (hd : d + 1024 ≤ 16384)
    (he : encodable (BitVec.ofNat 32 d) = true) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → (∀ r, r ≠ .r0 → r ≠ .r2 → t.gpr r = s.gpr r) →
      Frame [⟨scrB s₀ + BitVec.ofNat 64 d, 1024⟩] s.mem t.mem → (∀ i < 256, sw s₀ t.mem (d + 4 * i) = 0) →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.Arm.Derive.clearAt d ++ is)) s Q := by
  unfold Impl.Argon2.Arm.Derive.clearAt Impl.Argon2.Arm.Derive.scratchAt
  simp only [List.cons_append, List.nil_append]
  refine wp_ldarg hp h (i := 15) (by decide) fun s₁ u₁ => wp_add (op2_imm he) fun s₂ u₂ =>
    wp_mov (op2_imm (by decide)) fun s₃ u₃ => ?_
  have i₃ := ((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)
  refine WP.block_append ((zeros_ok hp i₃ hd (by rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr]) u₃.gpr 256
    (Nat.le_refl _)).mono fun t ⟨it, gt, ft, wt⟩ => k t it (fun r a b => ?_) ?_ wt)
  · rw [gt, u₃.other _ a, u₂.other _ b, u₁.other _ b]
  · rw [show s.mem = s₃.mem by rw [u₃.mem, u₂.mem, u₁.mem]]; exact ft

end

/-- The seven words of the address-generation input block. -/
def hdr (s₀ : State) (pass lane slice c : Nat) : Nat → BitVec 32
  | 0 => BitVec.ofNat 32 pass
  | 1 => BitVec.ofNat 32 lane
  | 2 => BitVec.ofNat 32 slice
  | 3 => arg s₀ 14
  | 4 => arg s₀ 5
  | 5 => arg s₀ 0
  | _ => BitVec.ofNat 32 c

/-- The words of the input block after its first `n` words are written over `m`'s. -/
def HW (s₀ : State) (m : Mem) (pass lane slice c n : Nat) (m' : Mem) : Prop :=
  ∀ i < 256, sw s₀ m' (5120 + 4 * i) =
    if i % 2 = 0 ∧ i < 2 * n then hdr s₀ pass lane slice c (i / 2) else sw s₀ m (5120 + 4 * i)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- One word of the header. -/
theorem hdr_step {m : Mem} {pass lane slice c n : Nat} (hn : n < 7) {u : State} (h : Inv s₀ u)
    (hx : u.gpr .r2 = scrP s₀ + BitVec.ofNat 32 5120) (ha : u.gpr .r0 = hdr s₀ pass lane slice c n)
    (hw : HW s₀ m pass lane slice c n u.mem) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → t.gpr = u.gpr → Frame [⟨scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] u.mem t.mem →
      HW s₀ m pass lane slice c (n + 1) t.mem → WP isa (.block is) t Q) :
    WP isa (.block (.str .r0 .r2 (8 * n) :: is)) u Q := by
  have hs := hp.scr_fits
  have ea : State.addr (u.gpr .r2 + BitVec.ofNat 32 (8 * n)) = A (scrP s₀) (5120 + 8 * n) := by
    rw [hx, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have eb : A (scrP s₀) (5120 + 8 * n) = scrB s₀ + BitVec.ofNat 64 (5120 + 8 * n) := scr_addr hp (by omega_arith)
  have hc : (scrR s₀).Contains (A (scrP s₀) (5120 + 8 * n)) 4 := by
    rw [eb]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  have hc' : (⟨scrB s₀ + BitVec.ofNat 64 5120, 1024⟩ : Region).Contains (A (scrP s₀) (5120 + 8 * n)) 4 := by
    rw [eb]; exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)
  refine wp_str (by omega_arith) ea ⟨_, by rw [h.wr]; exact scr_mem hp, hc⟩ fun t u₁ =>
    k t (h.store (R := scrR s₀) (by simp) hc u₁) u₁.gpr ?_ fun i hi => ?_
  · rw [u₁.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc'
  · rw [u₁.mem, sw_store hp _ (by omega_arith) (by omega_arith) (by omega_arith), ha, hw i hi]
    by_cases e : 5120 + 8 * n = 5120 + 4 * i
    · rw [ite_eq_left e, ite_eq_left (by omega_arith), show i / 2 = n by omega_arith]
    · rw [ite_eq_right e]
      by_cases c₁ : i % 2 = 0 ∧ i < 2 * n
      · rw [ite_eq_left c₁, ite_eq_left (by omega_arith)]
      · rw [ite_eq_right c₁, ite_eq_right (by omega_arith)]

theorem aheader_ok {s : State} (h : Inv s₀ s) {pass slice lane index c : Nat}
    (ps : Pos s₀ s pass slice lane index) (hc : lw s₀ s counterOff = BitVec.ofNat 32 c) :
    WP isa (.block Impl.Argon2.Arm.Derive.addressHeader) s fun t => Inv s₀ t ∧
      (∀ r, r ≠ .r0 → r ≠ .r2 → t.gpr r = s.gpr r) ∧
      Frame [⟨scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] s.mem t.mem ∧ HW s₀ s.mem pass lane slice c 7 t.mem := by
  have fsub : ∀ r ∈ [(⟨scrB s₀ + BitVec.ofNat 64 5120, 1024⟩ : Region)],
      ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
  unfold Impl.Argon2.Arm.Derive.addressHeader Impl.Argon2.Arm.Derive.scratchAt
  simp only [List.cons_append, List.nil_append]
  refine wp_ldarg hp h (i := 15) (by decide) fun s₀' u₀ => wp_add (op2_imm (by decide)) fun s₁ u₁ => ?_
  have i₁ := (h.upd u₀ (by decide)).upd u₁ (by decide)
  have x₁ : s₁.gpr .r2 = scrP s₀ + BitVec.ofNat 32 5120 := by rw [u₁.gpr, u₀.gpr]
  have m₁ : s₁.mem = s.mem := by rw [u₁.mem, u₀.mem]
  have w₀ : HW s₀ s.mem pass lane slice c 0 s₁.mem := fun i _ => by
    rw [ite_eq_right (by omega_arith), m₁]
  -- Word 0: the pass.
  refine wp_ldloc hp i₁ (d := passOff) (by decide) fun s₂ u₂ => ?_
  refine hdr_step hp (n := 0) (by decide) (i₁.upd u₂ (by decide)) (by rw [u₂.other _ (by decide), x₁])
    (by rw [u₂.gpr, lw_mem m₁, ps.pass]; rfl) (by rw [u₂.mem]; exact w₀) fun t₂ it₂ g₂ f₂ w₂ => ?_
  -- Word 1: the lane.
  refine wp_ldloc hp it₂ (d := laneOff) (by decide) fun s₃ u₃ => ?_
  refine hdr_step hp (n := 1) (by decide) (it₂.upd u₃ (by decide))
    (by rw [u₃.other _ (by decide), g₂, u₂.other _ (by decide), x₁])
    (by rw [u₃.gpr, lw_keep hp f₂ fsub (by decide), lw_mem u₂.mem, lw_mem m₁, ps.lane]; rfl)
    (by rw [u₃.mem]; exact w₂) fun t₃ it₃ g₃ f₃ w₃ => ?_
  have F₃ : Frame [⟨scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] s.mem t₃.mem := by
    rw [← m₁, ← u₂.mem]; exact f₂.trans (by rw [← u₃.mem]; exact f₃)
  -- Word 2: the slice.
  refine wp_ldloc hp it₃ (d := sliceOff) (by decide) fun s₄ u₄ => ?_
  refine hdr_step hp (n := 2) (by decide) (it₃.upd u₄ (by decide))
    (by rw [u₄.other _ (by decide), g₃, u₃.other _ (by decide), g₂, u₂.other _ (by decide), x₁])
    (by rw [u₄.gpr, lw_keep hp F₃ fsub (by decide), ps.slice]; rfl)
    (by rw [u₄.mem]; exact w₃) fun t₄ it₄ g₄ f₄ w₄ => ?_
  have F₄ : Frame [⟨scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] s.mem t₄.mem :=
    F₃.trans (by rw [← u₄.mem]; exact f₄)
  -- Words 3 to 5: the arguments.
  refine wp_ldarg hp it₄ (i := 14) (by decide) fun s₅ u₅ => ?_
  refine hdr_step hp (n := 3) (by decide) (it₄.upd u₅ (by decide))
    (by rw [u₅.other _ (by decide), g₄, u₄.other _ (by decide), g₃, u₃.other _ (by decide), g₂,
      u₂.other _ (by decide), x₁])
    (by rw [u₅.gpr]; rfl) (by rw [u₅.mem]; exact w₄) fun t₅ it₅ g₅ f₅ w₅ => ?_
  have F₅ : Frame [⟨scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] s.mem t₅.mem :=
    F₄.trans (by rw [← u₅.mem]; exact f₅)
  refine wp_ldarg hp it₅ (i := 5) (by decide) fun s₆ u₆ => ?_
  refine hdr_step hp (n := 4) (by decide) (it₅.upd u₆ (by decide))
    (by rw [u₆.other _ (by decide), g₅, u₅.other _ (by decide), g₄, u₄.other _ (by decide), g₃,
      u₃.other _ (by decide), g₂, u₂.other _ (by decide), x₁])
    (by rw [u₆.gpr]; rfl) (by rw [u₆.mem]; exact w₅) fun t₆ it₆ g₆ f₆ w₆ => ?_
  have F₆ : Frame [⟨scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] s.mem t₆.mem :=
    F₅.trans (by rw [← u₆.mem]; exact f₆)
  refine wp_ldarg hp it₆ (i := 0) (by decide) fun s₇ u₇ => ?_
  refine hdr_step hp (n := 5) (by decide) (it₆.upd u₇ (by decide))
    (by rw [u₇.other _ (by decide), g₆, u₆.other _ (by decide), g₅, u₅.other _ (by decide), g₄,
      u₄.other _ (by decide), g₃, u₃.other _ (by decide), g₂, u₂.other _ (by decide), x₁])
    (by rw [u₇.gpr]; rfl) (by rw [u₇.mem]; exact w₆) fun t₇ it₇ g₇ f₇ w₇ => ?_
  have F₇ : Frame [⟨scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] s.mem t₇.mem :=
    F₆.trans (by rw [← u₇.mem]; exact f₇)
  -- Word 6: the counter.
  refine wp_ldloc hp it₇ (d := counterOff) (by decide) fun s₈ u₈ => ?_
  refine hdr_step hp (n := 6) (by decide) (it₇.upd u₈ (by decide))
    (by rw [u₈.other _ (by decide), g₇, u₇.other _ (by decide), g₆, u₆.other _ (by decide), g₅,
      u₅.other _ (by decide), g₄, u₄.other _ (by decide), g₃, u₃.other _ (by decide), g₂,
      u₂.other _ (by decide), x₁])
    (by rw [u₈.gpr, lw_keep hp F₇ fsub (by decide), hc]; rfl)
    (by rw [u₈.mem]; exact w₇) fun t it g f w => WP.block_nil ⟨it, fun r a b => ?_,
      F₇.trans (by rw [← u₈.mem]; exact f), w⟩
  rw [g, u₈.other _ a, g₇, u₇.other _ a, g₆, u₆.other _ a, g₅, u₅.other _ a, g₄, u₄.other _ a, g₃,
    u₃.other _ a, g₂, u₂.other _ a, u₁.other _ b, u₀.other _ b]

end

theorem zero_append32 (x : BitVec 32) : 0#32 ++ x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_ofNat]
  simp
  have := x.isLt
  omega_arith

/-- The input block's words. -/
def inWord (s₀ : State) (pass lane slice c : Nat) (i : Nat) : BitVec 32 :=
  if i % 2 = 0 ∧ i < 14 then hdr s₀ pass lane slice c (i / 2) else 0

theorem input_words {s₀ : State} (hp : DPre s₀) {pass lane slice c : Nat} (h₁ : pass < 2 ^ 32)
    (h₂ : lane < 2 ^ 32) (h₃ : slice < 2 ^ 32) (h₄ : c < 2 ^ 32) :
    ofWords (inWord s₀ pass lane slice c) = Proof.Argon2.addressInput (prm s₀) pass lane slice c := by
  have eb : (arg s₀ 14).toNat = (prm s₀).blocks := hp.blocks
  have ep : (arg s₀ 5).toNat = (prm s₀).passes := rfl
  have ek : (arg s₀ 0).toNat = (prm s₀).variant.code := (variant_code hp.kind_le).symm
  apply Vector.ext
  intro j hj
  simp only [ofWords, Vector.getElem_ofFn, Proof.Argon2.addressInput, Vector.getElem_set, zeroBlock,
    Vector.getElem_replicate, inWord]
  rw [ite_eq_right (by omega_arith)]
  rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ 7 ≤ j) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | hj7
  · simp [hdr]; rw [zero_append32, toNat32 h₁]
  · simp [hdr]; rw [zero_append32, toNat32 h₂]
  · simp [hdr]; rw [zero_append32, toNat32 h₃]
  · simp [hdr]; rw [zero_append32, eb]
  · simp [hdr]; rw [zero_append32, ep]
  · simp [hdr]; rw [zero_append32, ek]
  · simp [hdr]; rw [zero_append32, toNat32 h₄]
  · rw [ite_eq_right (by omega_arith)]
    simp (disch := omega_arith) only [ite_eq_right]
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
theorem sw_frame {m m' : Mem} {a n : Nat} (f : Frame [⟨scrB s₀ + BitVec.ofNat 64 a, n⟩] m m') {o : Nat}
    (h : o + 4 ≤ a ∨ a + n ≤ o) (ho : o + 4 ≤ 16384) (hn : a + n ≤ 16384) : sw s₀ m' o = sw s₀ m o := by
  rw [sw, sw, A, scr_addr hp (by omega_arith)]
  refine f.readW (r := ⟨scrB s₀ + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint _ h (by omega_arith) (by omega_arith)

/-- The address-generation input block at `scratch + 5120`, and a zero block at `scratch + 7168`. -/
theorem input_ok {s : State} (h : Inv s₀ s) {pass slice lane index c : Nat}
    (ps : Pos s₀ s pass slice lane index) (hc : lw s₀ s counterOff = BitVec.ofNat 32 c)
    (h₁ : pass < 2 ^ 32) (h₂ : lane < 2 ^ 32) (h₃ : slice < 2 ^ 32) (h₄ : c < 2 ^ 32) :
    WP isa (.block (Impl.Argon2.Arm.Derive.clearAt 5120 ++ Impl.Argon2.Arm.Derive.clearAt 7168 ++
      Impl.Argon2.Arm.Derive.addressHeader)) s fun t => Inv s₀ t ∧
      (∀ r, r ≠ .r0 → r ≠ .r2 → t.gpr r = s.gpr r) ∧
      Frame [⟨scrB s₀ + BitVec.ofNat 64 5120, 1024⟩, ⟨scrB s₀ + BitVec.ofNat 64 7168, 1024⟩] s.mem t.mem ∧
      blk t.mem (scrP s₀) 5120 = Proof.Argon2.addressInput (prm s₀) pass lane slice c ∧
      blk t.mem (scrP s₀) 7168 = zeroBlock := by
  have fsub : ∀ d, d + 1024 ≤ 16384 → ∀ r ∈ [(⟨scrB s₀ + BitVec.ofNat 64 d, 1024⟩ : Region)],
      ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' := fun d hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, by simp, Offset.sub_base _ hd⟩
  rw [List.append_assoc]
  refine clearAt_ok hp h (d := 5120) (by decide) (by decide) fun t₁ i₁ g₁ f₁ z₁ => ?_
  refine clearAt_ok hp i₁ (d := 7168) (by decide) (by decide) fun t₂ i₂ g₂ f₂ z₂ => ?_
  have L : ∀ d, d + 4 ≤ 144 → lw s₀ t₂ d = lw s₀ s d := fun d hd => by
    rw [lw_keep hp f₂ (fsub _ (by decide)) hd, lw_keep hp f₁ (fsub _ (by decide)) hd]
  refine (aheader_ok hp i₂ (pass := pass) (slice := slice) (lane := lane) (index := index) (c := c)
    (ps.of_lw fun d hd => L d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide))
    (by rw [L _ (by decide)]; exact hc)).mono
    fun t ⟨it, gt, ft, wt⟩ => ⟨it, fun r a b => by rw [gt r a b, g₂ r a b, g₁ r a b], ?_, ?_, ?_⟩
  · refine (Frame.trans (f₁.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩)
      (f₂.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩)).trans
      (ft.sub fun r hr => ⟨⟨scrB s₀ + BitVec.ofNat 64 5120, 1024⟩, by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩)
  · rw [blk_of_words (f := inWord s₀ pass lane slice c) fun i hi => ?_, input_words hp h₁ h₂ h₃ h₄]
    have w := wt i hi
    simp only [sw] at w
    rw [w, inWord]
    by_cases e : i % 2 = 0 ∧ i < 2 * 7
    · rw [ite_eq_left e, ite_eq_left (by omega_arith)]
    · rw [ite_eq_right e, ite_eq_right (by omega_arith), ← sw, sw_frame hp f₂ (by omega_arith) (by omega_arith) (by decide)]
      exact z₁ i hi
  · rw [blk_of_words (f := fun _ => 0) fun i hi => ?_, ofWords_zero]
    rw [← sw, sw_frame hp ft (by omega_arith) (by omega_arith) (by decide)]
    exact z₂ i hi

end

end VG.Proof.Argon2.Arm.Derive

end

end

/-!
# Argon2 on ARMv7: the address block and the random word

`stage_ok`: G of two blocks of `scratch` to a third. `addressCalls_ok`: the
address block for the counter, G(0, G(0, input)), at `scratch + 6144`.
`addressCache_ok`: J₁, J₂ from the cached address block, regenerated when
the index enters a new group of 128. `randomSource_ok`: J₁, J₂ are the
random word of `FillStep.random`.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_and wp_cmp wp_ldr op2_imm op2_reg op2_lsr op2_lsl)
open VG.Spec.Argon2 (Block zeroBlock FillState compress addressBlock)
open VG.Proof.Argon2.Arm (blk)
open VG.Proof.Sha512.Arm (Only A)
open VG.Impl.Argon2.Arm.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem scr_blockAt (m : Mem) {o : Nat} (ho : o + 1024 ≤ 16384) :
    blockAt m (State.addr (scrP s₀ + BitVec.ofNat 32 o)) = blk m (scrP s₀) o := by
  have := hp.scr_fits
  rw [Proof.Argon2.Arm.blockAt_eq (by rw [add_nat (by omega_arith)]; omega_arith), blk_shift]

/-- `stage x y out`: G of the blocks at `scratch + x` and `scratch + y` to `scratch + out`. -/
theorem stage_ok {s : State} (h : Inv s₀ s) {x y o : Nat} (ho : 4096 ≤ o) (ho' : o + 1024 ≤ 16384)
    (hx : 4096 ≤ x) (hx' : x + 1024 ≤ 16384) (hxo : x + 1024 ≤ o ∨ o + 1024 ≤ x)
    (hy : 4096 ≤ y) (hy' : y + 1024 ≤ 16384) (hyo : y + 1024 ≤ o ∨ o + 1024 ≤ y)
    (ex : encodable (BitVec.ofNat 32 x) = true) (ey : encodable (BitVec.ofNat 32 y) = true)
    (eo : encodable (BitVec.ofNat 32 o) = true) :
    WP isa (Impl.Argon2.Arm.Derive.stage x y o) s fun t => Inv s₀ t ∧
      (∀ q ∈ preserved, q ≠ .lr → t.gpr q = s.gpr q) ∧
      Frame [⟨scrB s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨scrB s₀, 4096⟩] s.mem t.mem ∧
      blk t.mem (scrP s₀) o = compress (blk s.mem (scrP s₀) x) (blk s.mem (scrP s₀) y) := by
  unfold Impl.Argon2.Arm.Derive.stage
  refine WP.seq (wp_ldarg hp h (i := 15) (by decide) fun s₁ u₁ => wp_add (op2_imm ex) fun s₂ u₂ =>
    wp_add (op2_imm ey) fun s₃ u₃ => wp_add (op2_imm eo) fun s₄ u₄ => WP.block_nil ?_)
  have o₄ := (((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans (Only.of_upd u₄)
  have i₄ := h.only o₄ (by decide)
  have dx : s₄.gpr .r3 = scrP s₀ := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  have ax : s₄.gpr .r0 = scrP s₀ + BitVec.ofNat 32 x := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr]
  have sx : s₄.gpr .r1 = scrP s₀ + BitVec.ofNat 32 y := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.gpr]
  have cx : s₄.gpr .r2 = scrP s₀ + BitVec.ofNat 32 o := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  refine ccall_ok hp i₄ dx ho ho' cx (by rw [ax]; exact .inr ⟨x, hx, hx', hxo, rfl⟩)
    (by rw [sx]; exact .inr ⟨y, hy, hy', hyo, rfl⟩) fun t it cs f post =>
      ⟨it, fun q hq hl => ?_, by rw [← o₄.mem]; exact f,
        by rw [post, ax, sx, scr_blockAt hp _ hx', scr_blockAt hp _ hy', o₄.mem]⟩
  rw [cs q hq hl]
  refine o₄.gpr q ?_
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- A block of `scratch` at `d`, outside the regions G's call at `o` writes. -/
theorem stage_keep {m m' : Mem} {o : Nat} (ho : 4096 ≤ o) (ho' : o + 1024 ≤ 16384)
    (f : Frame [⟨scrB s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨scrB s₀, 4096⟩] m m') {d : Nat} (hd : 4096 ≤ d)
    (hd' : d + 1024 ≤ 16384) (hdo : d + 1024 ≤ o ∨ o + 1024 ≤ d) :
    blk m' (scrP s₀) d = blk m (scrP s₀) d := by
  rw [scr_blk hp m' hd', scr_blk hp m hd']
  refine blockAt_keep f fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ hdo (by omega_arith) (by omega_arith)
  · exact Offset.disjoint_base _ hd (by omega_arith)

omit hp in
theorem stage_frame {m m' : Mem} {o : Nat} (ho' : o + 1024 ≤ 16384)
    (f : Frame [⟨scrB s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨scrB s₀, 4096⟩] m m') :
    Frame [scrR s₀] m m' :=
  f.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, Offset.sub_base _ ho'⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩

/-- `addressCalls`: the address block for the counter `c` at `scratch + 6144`. -/
theorem addressCalls_ok {s : State} (h : Inv s₀ s) {pass slice lane index c : Nat}
    (ps : Pos s₀ s pass slice lane index) (hc : lw s₀ s counterOff = BitVec.ofNat 32 c)
    (h₁ : pass < 2 ^ 32) (h₂ : lane < 2 ^ 32) (h₃ : slice < 2 ^ 32) (h₄ : c < 2 ^ 32) :
    WP isa Impl.Argon2.Arm.Derive.addressCalls s fun t => Inv s₀ t ∧
      (∀ q ∈ preserved, q ≠ .lr → t.gpr q = s.gpr q) ∧ Frame [scrR s₀] s.mem t.mem ∧
      blk t.mem (scrP s₀) 6144 = addressBlock (prm s₀) pass lane slice c := by
  unfold Impl.Argon2.Arm.Derive.addressCalls
  refine WP.seq ((input_ok hp h ps hc h₁ h₂ h₃ h₄).mono fun t₁ ⟨i₁, g₁, f₁, b₁, z₁⟩ => ?_)
  refine WP.seq ((stage_ok hp i₁ (x := 7168) (y := 5120) (o := 4096) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono
    fun t₂ ⟨i₂, g₂, f₂, b₂⟩ => ?_)
  refine (stage_ok hp i₂ (x := 7168) (y := 4096) (o := 6144) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono
    fun t ⟨it, gt, ft, bt⟩ => ⟨it, fun q hq hl => ?_, ?_, ?_⟩
  · rw [gt q hq hl, g₂ q hq hl]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact g₁ _ (by decide) (by decide) | exact absurd rfl hl
  · refine Frame.trans (f₁.sub fun r hr => ?_) ((stage_frame (by decide) f₂).trans (stage_frame (by decide) ft))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
  · rw [bt, stage_keep hp (by decide) (by decide) f₂ (d := 7168) (by decide) (by decide) (by decide), b₂, z₁, b₁]
    rfl

end

theorem and127 {n : Nat} (h : n < 2 ^ 32) : BitVec.ofNat 32 n &&& 127 = BitVec.ofNat 32 (n % 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat32 h, toNat32 (by omega_arith),
    show (127 : BitVec 32).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem shr7 {n : Nat} (h : n < 2 ^ 32) : BitVec.ofNat 32 n >>> 7 = BitVec.ofNat 32 (n / 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat32 h, toNat32 (by omega_arith), Nat.shiftRight_eq_div_pow]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `cacheWord`: J₁ and J₂ are word `index mod 128` of the cached address block. -/
theorem cacheWord_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hi : index < 2 ^ 30) :
    WP isa (.block Impl.Argon2.Arm.Derive.cacheWord) s fun t => FS s₀ pass slice lane index ctr st t ∧
      lw s₀ t j2Off ++ lw s₀ t j1Off = (blk s.mem (scrP s₀) 6144)[index % 128]'(Nat.mod_lt _ (by decide)) := by
  have hs := hp.scr_fits
  have e8 : 8 * (index % 128) < 1024 := by omega_arith
  unfold Impl.Argon2.Arm.Derive.cacheWord
  refine wp_ldloc hp h.inv (d := indexOff) (by decide) fun s₁ u₁ => wp_and (op2_imm (by decide)) fun s₂ u₂ => ?_
  have o₂ := (Only.of_upd u₁).trans (Only.of_upd u₂)
  have h₂ := h.of_only o₂ (by decide)
  refine wp_ldarg hp h₂.inv (i := 15) (by decide) fun s₃ u₃ => wp_add (op2_lsl (by decide)) fun s₄ u₄ =>
    wp_add (op2_imm (by decide)) fun s₅ u₅ => ?_
  have h₅ := h₂.of_only (((Only.of_upd u₃).trans (Only.of_upd u₄)).trans (Only.of_upd u₅)) (by decide)
  have a₅ : s₅.gpr .r0 = scrP s₀ + BitVec.ofNat 32 (6144 + 8 * (index % 128)) := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₁.gpr, h.pos.index,
      and127 (by omega_arith), ofNat_shl (by omega_arith), show (6144 : BitVec 32) = BitVec.ofNat 32 6144 from rfl,
      BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    congr 2; omega_arith
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, o₂.mem]
  have inS : ∀ t : State, Inv s₀ t → ∀ o, o + 4 ≤ 1024 →
      InRegions (t.rd ++ t.wr) (State.addr (scrP s₀ + BitVec.ofNat 32 (6144 + 8 * (index % 128) + o))) 4 :=
    fun t it o ho => by
      rw [scr_addr hp (by omega_arith), it.wr]
      exact ⟨scrR s₀, List.mem_append_right _ (scr_mem hp), Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have ad : ∀ o, State.addr (s₅.gpr .r0 + BitVec.ofNat 32 o) =
      State.addr (scrP s₀ + BitVec.ofNat 32 (6144 + 8 * (index % 128) + o)) :=
    fun o => by rw [a₅, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  refine wp_ldr (by decide) (ad 0) (inS _ h₅.inv 0 (by decide)) fun s₆ u₆ => ?_
  have h₆ := h₅.of_only (Only.of_upd u₆) (by decide)
  refine wp_stloc hp h₆.inv (d := j1Off) (by decide) fun s₇ i₇ v₇ o₇ g₇ m₇ => ?_
  have h₇ := h₆.store hp i₇ (d := j1Off) (by decide) (by decide) (by decide) m₇
  refine wp_ldr (by decide) (by rw [g₇, u₆.other _ (by decide)]; exact ad 4) (inS _ h₇.inv 4 (by decide))
    fun s₈ u₈ => ?_
  have h₈ := h₇.of_only (Only.of_upd u₈) (by decide)
  refine wp_stloc hp h₈.inv (d := j2Off) (by decide) fun t it vt ot gt mt => WP.block_nil ⟨?_, ?_⟩
  · exact h₈.store hp it (d := j2Off) (by decide) (by decide) (by decide) mt
  · rw [vt, ot j1Off (by decide) (by decide), lw_mem u₈.mem, v₇, u₈.gpr, m₇,
      scr_addr hp (o := 6144 + 8 * (index % 128) + 4) (by omega_arith), scr_loc hp (by decide) (by omega_arith),
      ← scr_addr hp (by omega_arith), u₆.gpr, u₆.mem, m₅, blk_get _ _ _ _ (Nat.mod_lt _ (by decide)),
      Nat.add_zero (6144 + 8 * (index % 128))]

omit hp in
/-- The cached address block is that of `c`. -/
theorem cached {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) {c : Nat} (hc : 1 ≤ c) (hc' : c < 2 ^ 32)
    (he : lw s₀ s counterOff = BitVec.ofNat 32 c) :
    blk s.mem (scrP s₀) 6144 = addressBlock (prm s₀) pass lane slice c := by
  obtain ⟨c0, c1, c2 | ⟨_, c4⟩⟩ := h.cache
  · rw [he, c2] at c1
    have := congrArg BitVec.toNat c1
    rw [toNat32 hc'] at this
    exact absurd this (by simp; omega_arith)
  · rw [c4]
    rw [he] at c1
    have := congrArg BitVec.toNat c1
    rw [toNat32 hc', toNat32 c0] at this
    rw [this]

/-- `cacheCheck`: `r0 :=` the counter of the index's group; Z if it is cached. -/
theorem cacheCheck_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hi : index < (prm s₀).segmentLen) :
    WP isa (.block Impl.Argon2.Arm.Derive.cacheCheck) s fun t => FS s₀ pass slice lane index ctr st t ∧
      t.gpr .r0 = BitVec.ofNat 32 (index / 128 + 1) ∧
      VG.Arm.eval .eq t = some (BitVec.ofNat 32 (index / 128 + 1) - lw s₀ t counterOff == 0) := by
  have sl := segLen_lt hp
  unfold Impl.Argon2.Arm.Derive.cacheCheck
  refine wp_ldloc hp h.inv (d := indexOff) (by decide) fun s₁ u₁ => wp_mov (op2_lsr (by decide)) fun s₂ u₂ =>
    wp_add (op2_imm (by decide)) fun s₃ u₃ => ?_
  have o₃ := ((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)
  have h₃ := h.of_only o₃ (by decide)
  have a₃ : s₃.gpr .r0 = BitVec.ofNat 32 (index / 128 + 1) := by
    rw [u₃.gpr, u₂.gpr, u₁.gpr, h.pos.index, shr7 (by omega_arith), show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_add_ofNat]
  refine wp_ldloc hp h₃.inv (d := counterOff) (by decide) fun s₄ u₄ =>
    wp_cmp (op2_reg _ _) fun t f z => WP.block_nil ?_
  have o₄ := (Only.of_upd u₄).trans (Only.of_fupd f)
  refine ⟨h₃.of_only o₄ (by decide), by rw [o₄.gpr _ (by decide), a₃], ?_⟩
  rw [MdStream.Arm.eval_eq, z, u₄.other _ (by decide), a₃, u₄.gpr, lw_mem f.mem, lw_mem u₄.mem]

/-- The address block of the index's group, regenerated unless it is cached. -/
theorem cacheFill_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h₄ : FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) (a₃ : s.gpr .r0 = BitVec.ofNat 32 (index / 128 + 1))
    (z₄ : VG.Arm.eval .eq s = some (BitVec.ofNat 32 (index / 128 + 1) - lw s₀ s counterOff == 0)) :
    WP isa (.ite .eq (.block []) (.seq (.block [Impl.Argon2.Arm.Derive.st counterOff .r0])
      Impl.Argon2.Arm.Derive.addressCalls)) s fun t => FS s₀ pass slice lane index (index / 128 + 1) st t ∧
      blk t.mem (scrP s₀) 6144 = addressBlock (prm s₀) pass lane slice (index / 128 + 1) := by
  have sl := segLen_lt hp
  have hlt := hp.lanes_lt
  refine WP.ite (BitVec.ofNat 32 (index / 128 + 1) - lw s₀ s counterOff == 0) z₄
    (fun hb => ?_) fun hb => ?_
  · have ce : lw s₀ s counterOff = BitVec.ofNat 32 (index / 128 + 1) := by
      have e := beq_iff_eq.mp hb
      exact ((BitVec.sub_eq_iff_eq_add.mp e).trans (by simp)).symm
    have cb := cached h₄ (c := index / 128 + 1) (by omega_arith) (by omega_arith) ce
    exact WP.block_nil ⟨⟨h₄.inv, h₄.pr, h₄.pos, ⟨by omega_arith, ce, .inr ⟨by omega_arith, cb⟩⟩, h₄.mem⟩, cb⟩
  · refine WP.seq (wp_stloc hp h₄.inv (d := counterOff) (by decide) fun s₅ i₅ v₅ o₅ g₅ m₅ => WP.block_nil ?_)
    have L₅ : ∀ d ∈ fsOffs, d ≠ counterOff → lw s₀ s₅ d = lw s₀ s d := fun d hd hd' => by
      simp only [fsOffs, List.mem_cons, List.not_mem_nil, or_false] at hd
      refine o₅ d ?_ ?_ <;>
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | decide | exact absurd rfl hd'
    refine (addressCalls_ok hp i₅ (index := index) (c := index / 128 + 1)
      (h₄.pos.of_lw fun d hd => L₅ d (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl <;> decide) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl <;> decide))
      (by rw [v₅, a₃]) hpass (by omega_arith) (by omega_arith) (by omega_arith)).mono
      fun t ⟨it, _, ft, bt⟩ => ⟨?_, bt⟩
    have fsub : ∀ r ∈ [scrR s₀], ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' :=
      fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩
    have Lt : ∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ s₅ d := fun d hd => lw_keep hp ft fsub hd
    refine ⟨it, Prm.of_lw h₄.pr fun d hd => ?_, h₄.pos.of_lw fun d hd => ?_, ⟨by omega_arith,
      by rw [Lt _ (by decide), v₅, a₃], .inr ⟨by omega_arith, bt⟩⟩, Represents.keep h₄.mem fun k hk => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rw [Lt d (by rcases hd with rfl | rfl | rfl | rfl <;> decide)]
      exact L₅ d (by simp only [fsOffs]; rcases hd with rfl | rfl | rfl | rfl <;> simp)
        (by rcases hd with rfl | rfl | rfl | rfl <;> decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rw [Lt d (by rcases hd with rfl | rfl | rfl | rfl <;> decide)]
      exact L₅ d (by simp only [fsOffs]; rcases hd with rfl | rfl | rfl | rfl <;> simp)
        (by rcases hd with rfl | rfl | rfl | rfl <;> decide)
    · have hk' : k < blocksN s₀ := by rw [hp.blocks]; exact hk
      rw [blockAt_keep ft fun r hr => ?_, m₅, blockAt_keep (rs := [⟨State.addr (E s₀ + BitVec.ofNat 32 counterOff), 4⟩])
        ((Frame.refl _ _).writeW (w := 32) (List.mem_singleton_self _) _ (Region.contains_self _ _)) fun r hr => ?_]
      · simp only [List.mem_singleton] at hr; subst hr
        exact (loc_disj hp (d := counterOff) (by decide) (memR s₀) (by simp)).symm.sub_left (cell_in_mem hk')
      · simp only [List.mem_singleton] at hr; subst hr
        exact hp.mem_scr.sub_left (cell_in_mem hk')

/-- `addressCache`: J₁ and J₂ from the address block of the index's group of 128. -/
theorem addressCache_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) :
    WP isa Impl.Argon2.Arm.Derive.addressCache s fun t => FS s₀ pass slice lane index (index / 128 + 1) st t ∧
      lw s₀ t j2Off ++ lw s₀ t j1Off =
        (addressBlock (prm s₀) pass lane slice (index / 128 + 1))[index % 128]'(Nat.mod_lt _ (by decide)) := by
  have sl := segLen_lt hp
  unfold Impl.Argon2.Arm.Derive.addressCache
  refine WP.seq ((cacheCheck_ok hp h hi).mono fun s₄ ⟨h₄, a₄, z₄⟩ => ?_)
  have M := cacheFill_ok hp h₄ hpass hl hs hi a₄ z₄
  refine WP.seq (M.mono fun t ⟨ht, bt⟩ => (cacheWord_ok hp ht (by omega_arith)).mono fun u ⟨hu, wu⟩ => ⟨hu, ?_⟩)
  rw [wu, bt]

/-- `randomSource`: J₁ and J₂ are the step's random word. -/
theorem randomSource_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) :
    WP isa Impl.Argon2.Arm.Derive.randomSource s fun t =>
      FS s₀ pass slice lane index (ctrNext (prm s₀) pass slice index ctr) st t ∧
      lw s₀ t j2Off ++ lw s₀ t j1Off = Proof.Argon2.FillStep.random (prm s₀) pass lane slice index st.memory := by
  unfold Impl.Argon2.Arm.Derive.randomSource
  refine WP.seq ((addressMode_ok hp h.inv h.pos hpass hs).mono fun s₁ ⟨z₁, k₁⟩ => ?_)
  have h₁ := h.of_only k₁ (by decide)
  refine WP.ite (!Spec.Argon2.independent (prm s₀) pass slice) z₁ (fun hb => ?_) fun hb => ?_
  · have hind : Spec.Argon2.independent (prm s₀) pass slice = false := by simpa using hb
    refine (dependentWord_ok hp h₁ hl hs hi).mono fun t ⟨ht, wt⟩ => ⟨by rw [ctrNext, hind]; exact ht, ?_⟩
    have cl := Proof.Argon2.previous_cell_lt (prm s₀) hp.lanes_pos hp.memory_ge
      (column := slice * (prm s₀).segmentLen + index) hl
    rw [wt, k₁.mem, h.mem.block _ cl, Proof.Argon2.FillStep.random, hind]
    simp only [Bool.false_eq_true, ite_false]
  · have hind : Spec.Argon2.independent (prm s₀) pass slice = true := by simpa using hb
    refine (addressCache_ok hp h₁ hpass hl hs hi).mono fun t ⟨ht, wt⟩ => ⟨by rw [ctrNext, hind]; exact ht, ?_⟩
    rw [wt, Proof.Argon2.FillStep.random, hind]
    simp only [ite_true]

end

end VG.Proof.Argon2.Arm.Derive

end

end

/-! ### `Argon2.Arm.Derive.FillPtr`, which this module and modules that import it used -/

section

/-! ### `Argon2.Arm.Derive.FillCount`, which this module and modules that import it used -/

section

/-! ### `Argon2.Arm.Derive.FillRef`, which this module and modules that import it used -/

section

/-!
# Argon2 on ARMv7: the reference block's lane, start and base

`RS`: the filling state with J₁ and J₂ in the locals. `refLane_ok`: the
reference lane (RFC 9106 §3.4.2); `refStart_ok`: where the window of
eligible blocks starts; `countBase_ok`: the blocks before the current
segment that a reference may use.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_sub wp_orr wp_cmp op2_imm op2_reg)
open VG.Spec.Argon2 (Block zeroBlock FillState)
open VG.Proof.Sha512.Arm (Only)
open VG.Impl.Argon2.Arm.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off refLaneOff startOff countOff tmpOff curOff)

/-- The filling state, with J₁ and J₂ in the locals. -/
structure RS (s₀ : State) (pass slice lane index ctr : Nat) (st : FillState) (J1 J2 : BitVec 32) (s : State) :
    Prop where
  fs : FS s₀ pass slice lane index ctr st s
  j1 : lw s₀ s j1Off = J1
  j2 : lw s₀ s j2Off = J2

theorem RS.of_only {s₀ s t : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) {ds : List Reg} (o : Only ds s t) (h11 : Reg.r11 ∉ ds) :
    RS s₀ pass slice lane index ctr st J1 J2 t :=
  ⟨h.fs.of_only o h11, by rw [lw_mem o.mem]; exact h.j1, by rw [lw_mem o.mem]; exact h.j2⟩

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
    rw [BitVec.toNat_or, toNat32 ha, toNat32 hb] at this
    simpa using this
  · rintro ⟨rfl, rfl⟩; rfl

theorem sub_zero32 (y : BitVec 32) : y - 0 = y := by simp

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem RS.store {s t : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) (it : Inv s₀ t) {d : Nat} (hd : d + 4 ≤ 144) (ha : d % 4 = 0)
    (hd' : d ∉ fsOffs) (h1 : d ≠ j1Off) (h2 : d ≠ j2Off) {v : BitVec 32}
    (hm : t.mem = s.mem.writeW (State.addr (E s₀ + BitVec.ofNat 32 d)) v) :
    RS s₀ pass slice lane index ctr st J1 J2 t := by
  refine ⟨h.fs.store hp it hd hd' ha hm, ?_, ?_⟩
  · show t.mem.readW _ 32 = _
    rw [hm, lw_store hp (by omega_using [hd]) (by decide) (by simp [j1Off] at h1 ⊢; omega_using [ha, h1])]; exact h.j1
  · show t.mem.readW _ 32 = _
    rw [hm, lw_store hp (by omega_using [hd]) (by decide) (by simp [j2Off] at h2 ⊢; omega_using [ha, h2])]; exact h.j2

/-- The block of `refLane`: J₂ mod lanes, to the locals, and Z in the first
slice of the first pass. -/
theorem refLaneBlk_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa (.block ([Impl.Argon2.Arm.Derive.ld .r1 j2Off, Impl.Argon2.Arm.Derive.ld .r2 (argOff 7)] ++
      Impl.Argon2.Arm.Divide.code ++
      [Impl.Argon2.Arm.Derive.st refLaneOff .r0, Impl.Argon2.Arm.Derive.ld .r0 passOff,
        Impl.Argon2.Arm.Derive.ld .r1 sliceOff, .dp .orr .r0 .r0 (.reg .r1), .cmp .r0 (.imm 0)])) s fun t =>
      RS s₀ pass slice lane index ctr st J1 J2 t ∧ VG.Arm.eval .eq t = some (decide (pass = 0 ∧ slice = 0)) ∧
      lw s₀ t refLaneOff = BitVec.ofNat 32 (J2.toNat % lanesN s₀) := by
  have hlt := hp.lanes_lt
  have hl1 := hp.lanes_pos
  have e7 : lanesN s₀ = (arg s₀ 7).toNat := rfl
  rw [List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc hp h.fs.inv (d := j2Off) (by decide) fun s₁ u₁ =>
    wp_ldarg hp (h.fs.inv.upd u₁ (by decide)) (i := 7) (by decide) fun s₂ u₂ => ?_
  have h₂ := h.of_only ((Only.of_upd u₁).trans (Only.of_upd u₂)) (by decide)
  refine Divide.code_ok (D := arg s₀ 7) (by omega) (by omega) u₂.gpr fun s₃ _ r₃ k₃ => ?_
  have h₃ := h₂.of_only (Divide.Keep.only k₃) (by decide)
  refine wp_stloc hp h₃.fs.inv (d := refLaneOff) (by decide) fun s₄ i₄ v₄ _ g₄ m₄ => ?_
  have h₄ := h₃.store hp i₄ (d := refLaneOff) (by decide) (by decide) (by decide) (by decide) (by decide) m₄
  refine wp_ldloc hp h₄.fs.inv (d := passOff) (by decide) fun s₅ u₅ => ?_
  have h₅ := h₄.of_only (Only.of_upd u₅) (by decide)
  refine wp_ldloc hp h₅.fs.inv (d := sliceOff) (by decide) fun s₆ u₆ => wp_orr (op2_reg _ _) fun s₇ u₇ =>
    wp_cmp (op2_imm (by decide)) fun t f z => WP.block_nil ?_
  have h₇ := h₅.of_only (((Only.of_upd u₆).trans (Only.of_upd u₇)).trans (Only.of_fupd f)) (by decide)
  have r : s₃.gpr .r0 = BitVec.ofNat 32 (J2.toNat % lanesN s₀) := BitVec.eq_of_toNat_eq (by
    rw [r₃, u₂.other _ (by decide), u₁.gpr, h.j2, toNat32 (by have := J2.isLt; have := Nat.mod_le J2.toNat (lanesN s₀); omega_using [this])])
  refine ⟨h₇, ?_, by rw [lw_mem f.mem, lw_mem u₇.mem, lw_mem u₆.mem, lw_mem u₅.mem, v₄, r]⟩
  rw [MdStream.Arm.eval_eq, z, u₇.gpr, u₆.other _ (by decide), u₅.gpr, u₆.gpr, lw_mem u₅.mem, h₄.fs.pos.slice,
    h₄.fs.pos.pass, sub_zero32, or_zero hpass (by omega_using [hs])]

/-- `refLane`: the reference lane, to the locals. -/
theorem refLane_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa Impl.Argon2.Arm.Derive.refLane s fun t => RS s₀ pass slice lane index ctr st J1 J2 t ∧
      lw s₀ t refLaneOff = BitVec.ofNat 32 (refLaneV (lanesN s₀) pass slice lane J2.toNat) := by
  unfold Impl.Argon2.Arm.Derive.refLane
  refine WP.seq ((refLaneBlk_ok hp h hpass hs).mono fun s₅ ⟨h₅, z₅, e₃⟩ => ?_)
  refine WP.ite (decide (pass = 0 ∧ slice = 0)) z₅ (fun hb => ?_) fun hb => ?_
  · have hb' : pass = 0 ∧ slice = 0 := of_decide_eq_true hb
    refine wp_ldloc hp h₅.fs.inv (d := laneOff) (by decide) fun s₆ u₆ => ?_
    have h₆ := h₅.of_only (Only.of_upd u₆) (by decide)
    refine wp_stloc hp h₆.fs.inv (d := refLaneOff) (by decide) fun t it vt _ _ mt => WP.block_nil ⟨?_, ?_⟩
    · exact h₆.store hp it (d := refLaneOff) (by decide) (by decide) (by decide) (by decide) (by decide) mt
    · rw [vt, u₆.gpr, h₅.fs.pos.lane, refLaneV, ite_eq_left hb']
  · have hb' : ¬(pass = 0 ∧ slice = 0) := of_decide_eq_false hb
    refine WP.block_nil ⟨h₅, ?_⟩
    rw [e₃, refLaneV, ite_eq_right hb']

/-- `refStart`: where the window starts, to the locals. -/
theorem refStart_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa Impl.Argon2.Arm.Derive.refStart s fun t => RS s₀ pass slice lane index ctr st J1 J2 t ∧
      lw s₀ t refLaneOff = lw s₀ s refLaneOff ∧
      lw s₀ t startOff = BitVec.ofNat 32 (startV (prm s₀).segmentLen (prm s₀).laneLen pass slice) := by
  have sl := segLen_lt hp
  have ll := hp.laneLen_eq
  have s2 := hp.segLen_two
  unfold Impl.Argon2.Arm.Derive.refStart
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_)
  have h₁ := h.of_only (Only.of_upd u₁) (by decide)
  refine wp_stloc hp h₁.fs.inv (d := startOff) (by decide) fun s₂ i₂ v₂ o₂ _ m₂ => ?_
  have h₂ := h₁.store hp i₂ (d := startOff) (by decide) (by decide) (by decide) (by decide) (by decide) m₂
  refine wp_ldloc hp h₂.fs.inv (d := passOff) (by decide) fun s₃ u₃ =>
    wp_cmp (op2_imm (by decide)) fun s₄ f₄ z₄ => WP.block_nil ?_
  have h₄ := h₂.of_only ((Only.of_upd u₃).trans (Only.of_fupd f₄)) (by decide)
  have m₄ : s₄.mem = s₂.mem := by rw [f₄.mem, u₃.mem]
  have r₂ : lw s₀ s₂ refLaneOff = lw s₀ s refLaneOff := by
    rw [o₂ _ (by decide) (by decide), lw_mem u₁.mem]
  refine WP.ite (decide (pass = 0)) (by
    show VG.Arm.eval .eq _ = _
    rw [MdStream.Arm.eval_eq, z₄, u₃.gpr, h₂.fs.pos.pass, sub_zero32, MdStream.Arm.ofNat_beq_zero hpass])
    (fun hb => ?_) fun hb => ?_
  · refine WP.block_nil ⟨h₄, by rw [lw_mem m₄, r₂], ?_⟩
    rw [lw_mem m₄, v₂, u₁.gpr, startV, ite_eq_left (of_decide_eq_true hb)]; rfl
  · have hp0 : pass ≠ 0 := of_decide_eq_false hb
    refine WP.seq (wp_ldloc hp h₄.fs.inv (d := sliceOff) (by decide) fun s₅ u₅ =>
      wp_cmp (op2_imm (by decide)) fun s₆ f₆ z₆ => WP.block_nil ?_)
    have h₆ := h₄.of_only ((Only.of_upd u₅).trans (Only.of_fupd f₆)) (by decide)
    have m₆ : s₆.mem = s₂.mem := by rw [f₆.mem, u₅.mem, m₄]
    refine WP.ite (decide (slice = 3)) (by
      show VG.Arm.eval .eq _ = _
      rw [MdStream.Arm.eval_eq, z₆, u₅.gpr, h₄.fs.pos.slice, show (3 : BitVec 32) = BitVec.ofNat 32 3 from rfl,
        MdStream.Arm.sub_beq (by omega_using [hs]) (by decide)]) (fun hb' => ?_) fun hb' => ?_
    · refine WP.block_nil ⟨h₆, by rw [lw_mem m₆, r₂], ?_⟩
      rw [lw_mem m₆, v₂, u₁.gpr, startV, ite_eq_right hp0, of_decide_eq_true hb', ll, Nat.mod_self]; rfl
    · have hs3 : slice ≠ 3 := of_decide_eq_false hb'
      refine wp_ldloc hp h₆.fs.inv (d := sliceOff) (by decide) fun s₇ u₇ => wp_add (op2_imm (by decide))
        fun s₈ u₈ => ?_
      have h₈ := h₆.of_only ((Only.of_upd u₇).trans (Only.of_upd u₈)) (by decide)
      refine wp_ldloc hp h₈.fs.inv (d := segLenOff) (by decide) fun s₉ u₉ => wp_mul fun s₁₀ u₁₀ => ?_
      have h₁₀ := h₈.of_only ((Only.of_upd u₉).trans (Only.of_upd u₁₀)) (by decide)
      have m₁₀ : s₁₀.mem = s₂.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, m₆]
      refine wp_stloc hp h₁₀.fs.inv (d := startOff) (by decide) fun t it vt ot _ mt => WP.block_nil ⟨?_, ?_, ?_⟩
      · exact h₁₀.store hp it (d := startOff) (by decide) (by decide) (by decide) (by decide) (by decide) mt
      · rw [ot _ (by decide) (by decide), lw_mem m₁₀, r₂]
      · have : (slice + 1) * (prm s₀).segmentLen < (prm s₀).laneLen := by
          rw [ll]; exact Nat.mul_lt_mul_of_pos_right (by omega_using [hs, hs3]) (by omega_using [s2])
        rw [vt, u₁₀.gpr, u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₉.gpr, lw_mem u₈.mem, lw_mem u₇.mem,
          h₆.fs.pr.segLen, lw_mem (show s₆.mem = s₂.mem from m₆), h₂.fs.pos.slice,
          show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat, ofNat_mul_ofNat,
          startV, ite_eq_right hp0, Nat.mod_eq_of_lt this]

/-- `countBase`: `r0 :=` the blocks before the current segment that a reference may use. -/
theorem countBase_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) (hpass : pass < 2 ^ 32) :
    WP isa Impl.Argon2.Arm.Derive.countBase s fun t => Only [.r0, .r1, .r2] s t ∧
      t.gpr .r0 = BitVec.ofNat 32 (baseV (prm s₀).segmentLen (prm s₀).laneLen pass slice) := by
  have sl := segLen_lt hp
  have ll := hp.laneLen_eq
  unfold Impl.Argon2.Arm.Derive.countBase
  refine WP.seq (wp_ldloc hp h.fs.inv (d := passOff) (by decide) fun s₁ u₁ =>
    wp_cmp (op2_imm (by decide)) fun s₂ f₂ z₂ => WP.block_nil ?_)
  have k₂ := (Only.of_upd u₁).trans (Only.of_fupd f₂)
  have h₂ := h.of_only k₂ (by decide)
  refine WP.ite (decide (pass = 0)) (by
    show VG.Arm.eval .eq _ = _
    rw [MdStream.Arm.eval_eq, z₂, u₁.gpr, h.fs.pos.pass, sub_zero32, MdStream.Arm.ofNat_beq_zero hpass])
    (fun hb => ?_) fun hb => ?_
  · refine wp_ldloc hp h₂.fs.inv (d := sliceOff) (by decide) fun s₃ u₃ =>
      wp_ldloc hp (h₂.of_only (Only.of_upd u₃) (by decide)).fs.inv (d := segLenOff) (by decide) fun s₄ u₄ =>
      wp_mul fun t u => WP.block_nil ⟨(((k₂.trans (Only.of_upd u₃)).trans (Only.of_upd u₄)).trans
        (Only.of_upd u)).mono (by simp), ?_⟩
    rw [u.gpr, u₄.other _ (by decide), u₃.gpr, u₄.gpr, lw_mem u₃.mem, h₂.fs.pos.slice, h₂.fs.pr.segLen,
      ofNat_mul_ofNat, baseV, ite_eq_left (of_decide_eq_true hb)]
  · refine wp_ldloc hp h₂.fs.inv (d := laneLenOff) (by decide) fun s₃ u₃ =>
      wp_ldloc hp (h₂.of_only (Only.of_upd u₃) (by decide)).fs.inv (d := segLenOff) (by decide) fun s₄ u₄ =>
      wp_sub (op2_reg _ _) fun t u => WP.block_nil ⟨(((k₂.trans (Only.of_upd u₃)).trans (Only.of_upd u₄)).trans
        (Only.of_upd u)).mono (by simp), ?_⟩
    rw [u.gpr, u₄.other _ (by decide), u₃.gpr, u₄.gpr, lw_mem u₃.mem, h₂.fs.pr.laneLen, h₂.fs.pr.segLen,
      MdStream.Arm.sub_ofNat (by omega_using [ll]), baseV, ite_eq_right (of_decide_eq_false hb)]

end

end VG.Proof.Argon2.Arm.Derive

end

end

/-!
# Argon2 on ARMv7: the reference window's size

`countSelect_ok`: the number of eligible reference blocks, chosen between
the current lane's and another lane's by a mask (`sel`), to the locals.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_sub wp_orr wp_and op2_imm op2_reg op2_lsr)
open VG.Proof.Blake2.Arm.Stream (wp_eor)
open VG.Spec.Argon2 (Block zeroBlock FillState)
open VG.Proof.Sha512.Arm (Only)
open VG.Impl.Argon2.Arm.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off refLaneOff startOff countOff tmpOff curOff)

/-- A register after an update, as an `if` on the register. -/
theorem upd_get {s t : State} {d : Reg} {v : BitVec 32} (u : Upd s t d v) (r : Reg) :
    t.gpr r = if r = d then v else s.gpr r := by
  by_cases h : r = d
  · subst h; rw [ite_eq_left rfl, u.gpr]
  · rw [ite_eq_right h, u.other r h]

theorem sel (a c : BitVec 32) (p : Prop) [Decidable p] :
    a ^^^ ((c ^^^ a) &&& (if p then BitVec.allOnes 32 else 0)) = if p then c else a := by
  by_cases hp : p
  · simp only [hp, ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm c a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · simp [hp]

theorem mask_sub (p : Prop) [Decidable p] {x : BitVec 32} (hx : x = 1) :
    (if p then (0 : BitVec 32) else 1) - x = if p then BitVec.allOnes 32 else 0 := by
  subst hx
  by_cases hp : p <;> simp only [hp, ite_true, ite_false] <;> decide

theorem add_allOnes {x : Nat} (h : 1 ≤ x) (h' : x < 2 ^ 32) :
    BitVec.ofNat 32 x + BitVec.allOnes 32 = BitVec.ofNat 32 (x - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, toNat32 h', toNat32 (by omega_using [h']), BitVec.toNat_allOnes]
  omega_using [h, h']

theorem ofNat_eq_zero {n : Nat} (h : n < 2 ^ 32) : BitVec.ofNat 32 n = 0 ↔ n = 0 := by
  constructor
  · intro e; have := congrArg BitVec.toNat e; rwa [toNat32 h] at this
  · rintro rfl; rfl

theorem xor_eq_zero {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b = 0 ↔ a = b := by
  constructor
  · intro e
    have := congrArg BitVec.toNat (BitVec.xor_eq_zero_iff.mp e)
    rwa [toNat32 ha, toNat32 hb] at this
  · rintro rfl; simp

theorem ofNat_pred {n : Nat} (h : 1 ≤ n) {x : BitVec 32} (hx : x = 1) :
    BitVec.ofNat 32 n - x = BitVec.ofNat 32 (n - 1) := by
  rw [hx, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, MdStream.Arm.sub_ofNat h]

/-- The window's size. -/
def countV (base index : Nat) (same : Bool) : Nat :=
  if same then base + index - 1 else base - (if index = 0 then 1 else 0)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `countSelect`: the window's size, to the locals and `r0`. -/
theorem countSelect_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) {base rl : Nat} (hb : base < 2 ^ 31)
    (hi : index < (prm s₀).segmentLen) (hl : lane < lanesN s₀) (hrl : rl < lanesN s₀)
    (ha : s.gpr .r0 = BitVec.ofNat 32 base) (hr : lw s₀ s refLaneOff = BitVec.ofNat 32 rl)
    (hsame : rl = lane → 1 ≤ base + index) (hother : rl ≠ lane → index = 0 → 1 ≤ base)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, RS s₀ pass slice lane index ctr st J1 J2 t →
      t.gpr .r0 = BitVec.ofNat 32 (countV base index (rl == lane)) →
      lw s₀ t countOff = BitVec.ofNat 32 (countV base index (rl == lane)) →
      (∀ e, e + 4 ≤ 256 → (countOff + 4 ≤ e ∨ e + 4 ≤ countOff) → lw s₀ t e = lw s₀ s e) →
      (∀ r ∉ [Reg.r0, .r1, .r2, .r3], t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.Arm.Derive.countSelect ++ is)) s Q := by
  have sl := segLen_lt hp
  have lt := hp.lanes_lt
  unfold Impl.Argon2.Arm.Derive.countSelect
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc hp h.fs.inv (d := indexOff) (by decide) fun s₁ u₁ => wp_add (op2_reg _ _) fun s₂ u₂ =>
    wp_sub (op2_imm (by decide)) fun s₃ u₃ => wp_mov (op2_imm (by decide)) fun s₄ u₄ =>
    wp_sub (op2_reg _ _) fun s₅ u₅ => wp_orr (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_lsr (by decide)) fun s₇ u₇ =>
    wp_sub (op2_imm (by decide)) fun s₈ u₈ => wp_add (op2_reg _ _) fun s₉ u₉ => ?_
  have o₉ := ((((((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans (Only.of_upd u₄)).trans
    (Only.of_upd u₅)).trans (Only.of_upd u₆)).trans (Only.of_upd u₇)).trans (Only.of_upd u₈)).trans (Only.of_upd u₉)
  have h₉ := h.of_only o₉ (by decide)
  refine wp_ldloc hp h₉.fs.inv (d := refLaneOff) (by decide) fun s₁₀ u₁₀ =>
    wp_ldloc hp (h₉.fs.inv.upd u₁₀ (by decide)) (d := laneOff) (by decide) fun s₁₁ u₁₁ =>
    wp_eor (op2_reg _ _) fun s₁₂ u₁₂ => wp_mov (op2_imm (by decide)) fun s₁₃ u₁₃ =>
    wp_sub (op2_reg _ _) fun s₁₄ u₁₄ => wp_orr (op2_reg _ _) fun s₁₅ u₁₅ => wp_mov (op2_lsr (by decide)) fun s₁₆ u₁₆ =>
    wp_sub (op2_imm (by decide)) fun s₁₇ u₁₇ => wp_eor (op2_reg _ _) fun s₁₈ u₁₈ =>
    wp_and (op2_reg _ _) fun s₁₉ u₁₉ => wp_eor (op2_reg _ _) fun s₂₀ u₂₀ => ?_
  have o₂₀ := o₉.trans (((((((((((Only.of_upd u₁₀).trans (Only.of_upd u₁₁)).trans (Only.of_upd u₁₂)).trans
    (Only.of_upd u₁₃)).trans (Only.of_upd u₁₄)).trans (Only.of_upd u₁₅)).trans (Only.of_upd u₁₆)).trans
    (Only.of_upd u₁₇)).trans (Only.of_upd u₁₈)).trans (Only.of_upd u₁₉)).trans (Only.of_upd u₂₀))
  have h₂₀ := h.of_only o₂₀ (by decide)
  -- The value.
  have m : ∀ {t : State} {ds : List Reg}, Only ds s t → ∀ d, lw s₀ t d = lw s₀ s d := fun k d => lw_mem k.mem d
  have mi : lw s₀ s₉ refLaneOff = BitVec.ofNat 32 rl := by rw [m o₉, hr]
  have ml : lw s₀ s₁₀ laneOff = BitVec.ofNat 32 lane := by
    rw [lw_mem u₁₀.mem, m o₉, h.fs.pos.lane]
  have v : s₂₀.gpr .r0 = (s.gpr .r0 + (((((0 : BitVec 32) - lw s₀ s indexOff) ||| lw s₀ s indexOff) >>> 31) - (1 : BitVec 32))) ^^^
      (((s.gpr .r0 + lw s₀ s indexOff - (1 : BitVec 32)) ^^^ (s.gpr .r0 + (((((0 : BitVec 32) - lw s₀ s indexOff) ||| lw s₀ s indexOff) >>> 31) - (1 : BitVec 32)))) &&&
        (((((0 : BitVec 32) - (lw s₀ s₉ refLaneOff ^^^ lw s₀ s₁₀ laneOff)) ||| (lw s₀ s₉ refLaneOff ^^^ lw s₀ s₁₀ laneOff)) >>> 31) - (1 : BitVec 32))) := by
    simp only [upd_get u₂₀, upd_get u₁₉, upd_get u₁₈, upd_get u₁₇, upd_get u₁₆, upd_get u₁₅, upd_get u₁₄, upd_get u₁₃, upd_get u₁₂, upd_get u₁₁, upd_get u₁₀,
      upd_get u₉, upd_get u₈, upd_get u₇, upd_get u₆, upd_get u₅, upd_get u₄, upd_get u₃, upd_get u₂, upd_get u₁, ↓reduceIte, reduceCtorEq]
  have val : s₂₀.gpr .r0 = BitVec.ofNat 32 (countV base index (rl == lane)) := by
    rw [v, mi, ml, h.fs.pos.index, ha, nz, nz, mask_sub _ rfl, mask_sub _ rfl, sel, countV]
    simp only [ofNat_eq_zero (show index < 2 ^ 32 by omega_using [hi, sl]), xor_eq_zero (show rl < 2 ^ 32 by omega_using [hrl, lt])
      (show lane < 2 ^ 32 by omega_using [hl, lt])]
    by_cases hs : rl = lane
    · simp only [hs, ite_true, show (lane == lane) = true from beq_self_eq_true lane]
      rw [BitVec.ofNat_add_ofNat, ofNat_pred (hsame hs) rfl]
    · simp only [hs, ite_false, show (rl == lane) = false from beq_eq_false_iff_ne.mpr hs, Bool.false_eq_true]
      by_cases hi0 : index = 0
      · rw [ite_eq_left hi0, ite_eq_left hi0, add_allOnes (hother hs hi0) (by omega_using [hb])]
      · rw [ite_eq_right hi0, ite_eq_right hi0, Nat.sub_zero]
        exact BitVec.add_zero _
  refine wp_stloc hp h₂₀.fs.inv (d := countOff) (by decide) fun t it vt ot gt mt => k t ?_ (by rw [gt, val])
    (by rw [vt, val]) (fun e he hd => by rw [ot e he hd, m o₂₀]) (fun r hr => by rw [gt, (o₂₀.mono (es := [.r0, .r1, .r2, .r3]) (by simp)).gpr r hr])
  exact h₂₀.store hp it (d := countOff) (by decide) (by decide) (by decide) (by decide) (by decide) mt

end

end VG.Proof.Argon2.Arm.Derive

end

end

/-!
# Argon2 on ARMv7: the reference block's column and the block pointers

`relative_ok`: the position in the window that J₁ selects (RFC 9106
§3.4.2), with the high halves of the products from `mulHi`; `wrap_ok`: its
column, from the window's start, modulo the lane length; `refPointer_ok` and
`curPointer_ok`: the reference and current blocks' addresses, to the locals.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_sub wp_and op2_imm op2_reg)
open VG.Proof.Blake2.Arm.Stream (wp_adc)
open VG.Spec.Argon2 (Block zeroBlock FillState)
open VG.Proof.Sha512.Arm (Only)
open VG.Proof.Argon2.Arm (mulHi_ok mulHiV_eq)
open VG.Impl.Argon2.Arm.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off refLaneOff startOff countOff tmpOff curOff)

/-- The position in the window that `j1` selects. -/
def relV (cnt j1 : Nat) : Nat := cnt - 1 - cnt * (j1 * j1 / 2 ^ 32) / 2 ^ 32

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `relative`: `r0 :=` the position in the window. -/
theorem relative_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) {cnt : Nat} (hc : 1 ≤ cnt) (hc' : cnt < 2 ^ 32)
    (hcnt : lw s₀ s countOff = BitVec.ofNat 32 cnt) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .r0 = BitVec.ofNat 32 (relV cnt J1.toNat) →
      Only [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r12] s t → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.Arm.Derive.relative ++ is)) s Q := by
  have jb := J1.isLt
  have x32 := Proof.Argon2.reference_scaled_bound J1.toNat jb
  have lt := Proof.Argon2.reference_scale_lt_count cnt J1.toNat (by omega_arith) jb
  unfold Impl.Argon2.Arm.Derive.relative
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_ldloc hp h.fs.inv (d := j1Off) (by decide) fun s₁ u₁ =>
    mulHi_ok (by decide) (by decide) (by decide) fun s₂ o₂ p₂ => ?_
  have O₂ := (Only.of_upd u₁).trans o₂
  have h₂ := h.of_only O₂ (by decide)
  refine wp_ldloc hp h₂.fs.inv (d := countOff) (by decide) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ =>
    mulHi_ok (by decide) (by decide) (by decide) fun s₅ o₅ p₅ => wp_sub (op2_imm (by decide)) fun s₆ u₆ =>
    wp_sub (op2_reg _ _) fun t u => k t ?_ ?_
  · have x₄ : s₄.gpr .r6 = BitVec.ofNat 32 (J1.toNat * J1.toNat / 2 ^ 32) := by
      rw [u₄.gpr, u₃.other _ (by decide), p₂, u₁.gpr, h.j1, mulHiV_eq]
    have c₄ : s₄.gpr .r5 = BitVec.ofNat 32 cnt := by
      rw [u₄.other _ (by decide), u₃.gpr, lw_mem O₂.mem, hcnt]
    rw [u.gpr, u₆.gpr, u₆.other .r2 (by decide), o₅.gpr .r5 (by decide), p₅, x₄, c₄, mulHiV_eq,
      toNat32 hc', toNat32 x32, ofNat_pred hc rfl, MdStream.Arm.sub_ofNat (by omega_arith), relV]
  · exact ((((O₂.trans (Only.of_upd u₃)).trans (Only.of_upd u₄)).trans o₅).trans
      ((Only.of_upd u₆).trans (Only.of_upd u))).mono (by simp)

/-- `wrap`: `r0 := (start + r0) mod laneLen`. -/
theorem wrap_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) {rel stt : Nat} (hr : rel < (prm s₀).laneLen)
    (hs : stt < (prm s₀).laneLen) (ha : s.gpr .r0 = BitVec.ofNat 32 rel)
    (hst : lw s₀ s startOff = BitVec.ofNat 32 stt) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .r0 = BitVec.ofNat 32 ((stt + rel) % (prm s₀).laneLen) → Only [.r0, .r2, .r3] s t →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.Arm.Derive.wrap ++ is)) s Q := by
  have L22 : (prm s₀).laneLen < 2 ^ 22 := by
    have := Nat.le_mul_of_pos_left (prm s₀).laneLen (show 0 < lanesN s₀ from hp.lanes_pos)
    have e := hp.blocks_eq
    have := hp.blocks_lt
    omega_arith
  unfold Impl.Argon2.Arm.Derive.wrap
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc hp h.fs.inv (d := startOff) (by decide) fun s₁ u₁ => wp_add (op2_reg _ _) fun s₂ u₂ => ?_
  have O₂ := (Only.of_upd u₁).trans (Only.of_upd u₂)
  refine wp_ldloc hp (h.of_only O₂ (by decide)).fs.inv (d := laneLenOff) (by decide) fun s₃ u₃ =>
    wp_mov (op2_imm (by decide)) fun s₄ u₄ => Divide.wp_subsC (op2_reg _ _) fun s₅ u₅ c₅ =>
    wp_adc (op2_imm (by decide)) fun s₆ u₆ _ => wp_sub (op2_imm (by decide)) fun s₇ u₇ =>
    wp_and (op2_reg _ _) fun s₈ u₈ => wp_add (op2_reg _ _) fun t u => k t ?_ ?_
  · have L₂ : lw s₀ s₂ laneLenOff = BitVec.ofNat 32 (prm s₀).laneLen := by
      rw [lw_mem O₂.mem]; exact h.fs.pr.laneLen
    have x₄ : s₄.gpr .r0 = BitVec.ofNat 32 (stt + rel) := by
      rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), ha, hst,
        BitVec.ofNat_add_ofNat, Nat.add_comm]
    have l₄ : s₄.gpr .r2 = BitVec.ofNat 32 (prm s₀).laneLen := by
      rw [u₄.other _ (by decide), u₃.gpr, L₂]
    rw [x₄, l₄, toNat32 (by omega_arith), toNat32 (by omega_arith)] at c₅
    simp only [upd_get u, upd_get u₈, upd_get u₇, upd_get u₆, upd_get u₅, ↓reduceIte, reduceCtorEq, c₅, x₄, l₄,
      u₄.gpr]
    rw [Proof.Argon2.reference_wrap (stt + rel) (prm s₀).laneLen (by omega_arith)]
    by_cases c : stt + rel < (prm s₀).laneLen
    · have c' : ¬(prm s₀).laneLen ≤ stt + rel := by omega_arith
      simp only [c, c', decide_false, ite_true, Bool.false_eq_true, ite_false]
      rw [show (0 : BitVec 32) + 0 + 0 - 1 = BitVec.allOnes 32 by decide, BitVec.allOnes_and,
        BitVec.sub_add_cancel]
    · have c' : (prm s₀).laneLen ≤ stt + rel := by omega_arith
      simp only [c, c', decide_true, ite_true, ite_false]
      rw [show (0 : BitVec 32) + 0 + 1 - 1 = 0 by decide,
        show (0 : BitVec 32) &&& BitVec.ofNat 32 (prm s₀).laneLen = 0 from BitVec.zero_and]
      exact (BitVec.add_zero _).trans (MdStream.Arm.sub_ofNat c')
  · exact ((O₂.trans ((((((Only.of_upd u₃).trans (Only.of_upd u₄)).trans (Only.of_upd u₅)).trans
      (Only.of_upd u₆)).trans (Only.of_upd u₇)).trans (Only.of_upd u₈))).trans (Only.of_upd u)).mono (by simp)

/-- `refPointer`: the address of block `r0` of the reference lane, to the locals. -/
theorem refPointer_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) {col rl : Nat} (hc : col < (prm s₀).laneLen)
    (hrl : rl < lanesN s₀) (ha : s.gpr .r0 = BitVec.ofNat 32 col)
    (hr : lw s₀ s refLaneOff = BitVec.ofNat 32 rl) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, RS s₀ pass slice lane index ctr st J1 J2 t →
      lw s₀ t tmpOff = memP s₀ + BitVec.ofNat 32 ((rl * (prm s₀).laneLen + col) * 1024) →
      (∀ e, e + 4 ≤ 256 → (tmpOff + 4 ≤ e ∨ e + 4 ≤ tmpOff) → lw s₀ t e = lw s₀ s e) →
      (∀ r ∉ [Reg.r0, .r1, .r2], t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.Arm.Derive.refPointer ++ is)) s Q := by
  unfold Impl.Argon2.Arm.Derive.refPointer
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
  refine wp_ldloc hp (h.of_only (Only.of_upd u₁) (by decide)).fs.inv (d := refLaneOff) (by decide)
    fun s₂ u₂ => ?_
  have K₂ := (Only.of_upd u₁).trans (Only.of_upd u₂)
  refine blockAddr_ok hp (h.of_only K₂ (by decide)).fs.inv (h.of_only K₂ (by decide)).fs.pr hrl hc
    (by rw [u₂.gpr, lw_mem u₁.mem, hr]) (by rw [u₂.other _ (by decide), u₁.gpr, ha]) fun s₃ a₃ k₃ => ?_
  have K₃ := K₂.trans k₃
  refine wp_stloc hp (h.of_only K₃ (by decide)).fs.inv (d := tmpOff) (by decide) fun t it vt ot gt mt =>
    k t ?_ (by rw [vt, a₃]) (fun e he hd => by rw [ot e he hd, lw_mem K₃.mem]) (fun r hr => by
      rw [gt, (K₃.mono (es := [.r0, .r1, .r2]) (by simp)).gpr r hr])
  exact (h.of_only K₃ (by decide)).store hp it (d := tmpOff) (by decide) (by decide) (by decide) (by decide)
    (by decide) mt

/-- `curPointer`: the address of the current block, to the locals. -/
theorem curPointer_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, RS s₀ pass slice lane index ctr st J1 J2 t →
      lw s₀ t curOff = memP s₀ + BitVec.ofNat 32
        ((lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index)) * 1024) →
      (∀ e, e + 4 ≤ 256 → (curOff + 4 ≤ e ∨ e + 4 ≤ curOff) → lw s₀ t e = lw s₀ s e) →
      (∀ r ∉ [Reg.r0, .r1, .r2], t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.Arm.Derive.curPointer ++ is)) s Q := by
  have hc := Proof.Argon2.column_lt (prm s₀) hp.lanes_pos hs hi
  unfold Impl.Argon2.Arm.Derive.curPointer
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine column_ok hp h.fs.inv h.fs.pr h.fs.pos hs hi fun s₁ c₁ k₁ => ?_
  refine wp_ldloc hp (h.of_only k₁ (by decide)).fs.inv (d := laneOff) (by decide) fun s₂ u₂ => ?_
  have K₂ := k₁.trans (Only.of_upd u₂)
  refine blockAddr_ok hp (h.of_only K₂ (by decide)).fs.inv (h.of_only K₂ (by decide)).fs.pr hl hc
    (by rw [u₂.gpr, lw_mem k₁.mem]; exact h.fs.pos.lane) (by rw [u₂.other _ (by decide), c₁])
    fun s₃ a₃ k₃ => ?_
  have K₃ := K₂.trans k₃
  refine wp_stloc hp (h.of_only K₃ (by decide)).fs.inv (d := curOff) (by decide) fun t it vt ot gt mt =>
    k t ?_ (by rw [vt, a₃]) (fun e he hd => by rw [ot e he hd, lw_mem K₃.mem]) (fun r hr => by
      rw [gt, (K₃.mono (es := [.r0, .r1, .r2]) (by simp)).gpr r hr])
  exact (h.of_only K₃ (by decide)).store hp it (d := curOff) (by decide) (by decide) (by decide) (by decide)
    (by decide) mt

end

theorem j2_eq (J1 J2 : BitVec 32) : ((J2 ++ J1 : BitVec 64) >>> 32).toNat = J2.toNat := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ← Proof.Sha512.Word64.hi_toNat,
    Proof.Sha512.Word64.hi_append]

theorem j1_eq (J1 J2 : BitVec 32) : ((J2 ++ J1 : BitVec 64) &&& 0xffffffff).toNat = J1.toNat := by
  rw [BitVec.toNat_and, show (0xffffffff : BitVec 64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    ← Proof.Sha512.Word64.lo_toNat, Proof.Sha512.Word64.lo_append]

theorem count_eq (p : Spec.Argon2.Params) (pass slice index : Nat) (same : Bool) :
    Spec.Argon2.referenceCount p pass slice index same =
      countV (baseV p.segmentLen p.laneLen pass slice) index same := by
  unfold Spec.Argon2.referenceCount countV baseV
  by_cases h : pass = 0
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]

theorem ref_eq (p : Spec.Argon2.Params) (pass lane slice index : Nat) (J1 J2 : BitVec 32) :
    Spec.Argon2.reference p pass lane slice index (J2 ++ J1) =
      (refLaneV p.lanes pass slice lane J2.toNat,
        (startV p.segmentLen p.laneLen pass slice +
          relV (countV (baseV p.segmentLen p.laneLen pass slice) index
            (refLaneV p.lanes pass slice lane J2.toNat == lane)) J1.toNat) % p.laneLen) := by
  unfold Spec.Argon2.reference
  simp only [j1_eq, j2_eq, count_eq]
  rfl

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `reference`: the reference and current blocks' addresses, to the locals. -/
theorem reference_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index) :
    WP isa Impl.Argon2.Arm.Derive.reference s fun t => RS s₀ pass slice lane index ctr st J1 J2 t ∧
      lw s₀ t tmpOff = memP s₀ + BitVec.ofNat 32
        (((Spec.Argon2.reference (prm s₀) pass lane slice index (J2 ++ J1)).1 * (prm s₀).laneLen +
          (Spec.Argon2.reference (prm s₀) pass lane slice index (J2 ++ J1)).2) * 1024) ∧
      lw s₀ t curOff = memP s₀ + BitVec.ofNat 32
        ((lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index)) * 1024) := by
  have L22 : (prm s₀).laneLen < 2 ^ 22 := by
    have := Nat.le_mul_of_pos_left (prm s₀).laneLen (show 0 < lanesN s₀ from hp.lanes_pos)
    have e := hp.blocks_eq
    have := hp.blocks_lt
    omega_arith
  have ll := hp.laneLen_eq
  have s2 := hp.segLen_two
  have hl1 := hp.lanes_pos
  rw [ref_eq]
  generalize hRL : refLaneV (prm s₀).lanes pass slice lane J2.toNat = RL
  have hRL' : refLaneV (lanesN s₀) pass slice lane J2.toNat = RL := hRL
  have rl_lt : RL < lanesN s₀ := by
    rw [← hRL', refLaneV]; split
    · exact hl
    · exact Nat.mod_lt _ (by omega_arith)
  have first : pass = 0 → slice = 0 → RL = lane := fun a b => by rw [← hRL', refLaneV, ite_eq_left ⟨a, b⟩]
  generalize hB : baseV (prm s₀).segmentLen (prm s₀).laneLen pass slice = B
  have b_le : B ≤ (prm s₀).laneLen := by
    rw [← hB, baseV]; split
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (show slice ≤ 3 by omega_arith)) (by omega_arith))
    · omega_arith
  generalize hST : startV (prm s₀).segmentLen (prm s₀).laneLen pass slice = ST
  have st_lt : ST < (prm s₀).laneLen := by
    rw [← hST, startV]; split
    · omega_arith
    · exact Nat.mod_lt _ (by omega_arith)
  have cpos := Proof.Argon2.reference_count_positive (prm s₀) hp.lanes_pos hp.memory_ge pass slice index
    (RL == lane) active fun a b => by simp [first a b]
  have clt := Proof.Argon2.reference_count_lt_lane (prm s₀) hp.lanes_pos hp.memory_ge pass slice index
    (RL == lane) hs hi
  rw [count_eq, hB] at cpos clt
  unfold Impl.Argon2.Arm.Derive.reference
  refine WP.seq ((refLane_ok hp h hpass hs).mono fun t₁ ⟨h₁, r₁⟩ => ?_)
  rw [hRL'] at r₁
  refine WP.seq ((refStart_ok hp h₁ hpass hs).mono fun t₂ ⟨h₂, r₂, st₂⟩ => ?_)
  rw [hST] at st₂
  refine WP.seq ((countBase_ok hp h₂ hpass).mono fun t₃ ⟨k₃, a₃⟩ => ?_)
  rw [hB] at a₃
  have h₃ := h₂.of_only k₃ (by decide)
  simp only [List.append_assoc]
  rw [← List.append_nil Impl.Argon2.Arm.Derive.curPointer]
  refine countSelect_ok hp h₃ (base := B) (rl := RL) (by omega_arith) hi hl rl_lt a₃
    (by rw [lw_mem k₃.mem, r₂, r₁]) (fun e => ?_) (fun e e0 => ?_) fun t₄ h₄ a₄ c₄ o₄ g₄ => ?_
  · rw [← hB, baseV]; split
    · rename_i hp0
      by_cases hs0 : slice = 0
      · omega_arith
      · have := Nat.mul_le_mul_right (prm s₀).segmentLen (show 1 ≤ slice by omega_arith); omega_arith
    · omega_arith
  · have : ¬(pass = 0 ∧ slice = 0) := fun ⟨a, b⟩ => e (first a b)
    rw [← hB, baseV]; split
    · rename_i hp0
      have := Nat.mul_le_mul_right (prm s₀).segmentLen (show 1 ≤ slice by omega_arith); omega_arith
    · omega_arith
  refine relative_ok hp h₄ (cnt := countV B index (RL == lane)) cpos (by omega_arith) c₄ fun t₅ a₅ k₅ => ?_
  have h₅ := h₄.of_only k₅ (by decide)
  have rel_lt : relV (countV B index (RL == lane)) J1.toNat < (prm s₀).laneLen := by
    unfold relV; omega_arith
  refine wrap_ok hp h₅ rel_lt st_lt a₅ (by
      rw [lw_mem k₅.mem, o₄ _ (by decide) (by decide), lw_mem k₃.mem, st₂]) fun t₆ a₆ k₆ => ?_
  have h₆ := h₅.of_only k₆ (by decide)
  refine refPointer_ok hp h₆ (Nat.mod_lt _ (by omega_arith)) rl_lt a₆ (by
      rw [lw_mem k₆.mem, lw_mem k₅.mem, o₄ _ (by decide) (by decide), lw_mem k₃.mem, r₂, r₁])
    fun t₇ h₇ p₇ o₇ _ => ?_
  refine curPointer_ok hp h₇ hl hs hi fun t h' c' o' _ => WP.block_nil ⟨h', ?_, c'⟩
  rw [o' _ (by decide) (by decide), p₇]

end

end VG.Proof.Argon2.Arm.Derive

end

end

/-! ### `Argon2.Arm.Derive.FillWrite`, which this module and modules that import it used -/

section

/-!
# Argon2 on ARMv7: writing the new block

`writeWords_ok`: the words of G's output (at `r1`) to the current block (at
`r3`), XORed into the old ones after the first pass.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_ldr wp_str op2_reg)
open VG.Proof.Blake2.Arm.Stream (wp_eor)
open VG.Spec.Argon2 (Block zeroBlock FillState compress xorBlock)
open VG.Proof.Argon2.Arm (blk ofWords blk_of_words)
open VG.Proof.Sha512.Arm (A)
open VG.Impl.Argon2.Arm.Derive (writeWord)

/-- Words of the memory matrix. -/
abbrev mw (s₀ : State) (m : Mem) (o : Nat) : BitVec 32 := m.readW (A (memP s₀) o) 32

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem blocks22 : blocksN s₀ < 2 ^ 22 := by
  have hb := hp.blocks_lt
  omega_using [hb]

theorem mem_addr' {o : Nat} (ho : o < blocksN s₀ * 1024) : A (memP s₀) o = memB s₀ + BitVec.ofNat 64 o :=
  addr_add (by have := hp.mem_fits; omega_using [ho, this])

/-- A word of the matrix after a store to another, or the same. -/
theorem mw_store (m : Mem) {a b : Nat} (ha : a + 4 ≤ blocksN s₀ * 1024) (hb : b + 4 ≤ blocksN s₀ * 1024)
    (h : a = b ∨ a + 4 ≤ b ∨ b + 4 ≤ a) (v : BitVec 32) :
    mw s₀ (m.writeW (A (memP s₀) a) v) b = if a = b then v else mw s₀ m b := by
  have := blocks22 hp
  by_cases e : a = b
  · subst e; rw [ite_eq_left rfl]; exact Mem.readW_writeW_self32 _ _ _
  · rw [ite_eq_right e, mw, mw, mem_addr' hp (by omega_using [ha]), mem_addr' hp (by omega_using [hb])]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega_using [h, e]) (by omega_using [hb, this]) (by omega_using [ha, this])) (by decide)

/-- The words of the current block, `n` of them written. -/
theorem writeWords_ok {s : State} (h : Inv s₀ s) {cur : Nat} (hc : cur < blocksN s₀) (xo : Bool)
    {P : BitVec 32} (hsi : s.gpr .r1 = P) (hPfit : P.toNat + 1024 ≤ 2 ^ 32)
    (hPw : ∃ R ∈ [scrR s₀, memR s₀], ∃ off, State.addr P = R.base + BitVec.ofNat 64 off ∧ off + 1024 ≤ R.len)
    (hPC : Region.Disjoint ⟨State.addr P, 1024⟩ ⟨matrixCell (memB s₀) cur, 1024⟩)
    (hdi : s.gpr .r3 = memP s₀ + BitVec.ofNat 32 (cur * 1024)) :
    ∀ n ≤ 256, WP isa (.block ((List.range n).flatMap (writeWord xo))) s fun t =>
      Inv s₀ t ∧ (∀ r, r ≠ .r0 → r ≠ .r2 → t.gpr r = s.gpr r) ∧
      Frame [⟨matrixCell (memB s₀) cur, 1024⟩] s.mem t.mem ∧
      ∀ i < 256, mw s₀ t.mem (cur * 1024 + 4 * i) = if i < n then
        (if xo then s.mem.readW (A P (4 * i)) 32 ^^^ mw s₀ s.mem (cur * 1024 + 4 * i) else s.mem.readW (A P (4 * i)) 32)
        else mw s₀ s.mem (cur * 1024 + 4 * i)
  | 0, _ => WP.block_nil ⟨h, fun _ _ _ => rfl, Frame.refl _ _, fun i _ => by rw [ite_eq_right (by omega_using [])]⟩
  | n + 1, hn => by
    have hs := hp.scr_fits
    have hm := hp.mem_fits
    have hb := blocks22 hp
    have hc' : cur * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega_using [hc]
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append ((writeWords_ok h hc xo hsi hPfit hPw hPC hdi n (by omega_using [hn])).mono
      fun t ⟨it, gt, ft, wt⟩ => ?_)
    have cell : matrixCell (memB s₀) cur = memB s₀ + BitVec.ofNat 64 (cur * 1024) := rfl
    -- The source word is kept: only the current block has been written.
    have eP : A P (4 * n) = State.addr P + BitVec.ofNat 64 (4 * n) := addr_add (by omega_using [hPfit, hn])
    have sw_t : t.mem.readW (A P (4 * n)) 32 = s.mem.readW (A P (4 * n)) 32 := by
      rw [eP]
      refine ft.readW (r := ⟨State.addr P + BitVec.ofNat 64 (4 * n), 4⟩) (Region.contains_self _ _)
        (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact hPC.sub_left (Offset.sub_base _ (by omega_using [hn]))
    have ea : State.addr (t.gpr .r1 + BitVec.ofNat 32 (4 * n)) = A P (4 * n) := by
      rw [gt _ (by decide) (by decide), hsi]
    have eb : State.addr (t.gpr .r3 + BitVec.ofNat 32 (4 * n)) = A (memP s₀) (cur * 1024 + 4 * n) := by
      rw [gt _ (by decide) (by decide), hdi, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    have b1 : cur * 1024 + 4 * n + 4 ≤ blocksN s₀ * 1024 := by omega_using [hc', hn]
    have b2 : cur * 1024 + 1024 < 2 ^ 64 := by omega_using [hc', hb]
    have inS : InRegions (t.rd ++ t.wr) (A P (4 * n)) 4 := by
      obtain ⟨R, hR, off, bR, lR⟩ := hPw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      have RW : R ∈ t.wr ∧ R.len ≤ 2 ^ 32 := by
        rw [it.wr]
        rcases hR with rfl | rfl
        · exact ⟨scr_mem hp, by show 16384 ≤ 2 ^ 32; decide⟩
        · exact ⟨mem_mem hp, by show blocksN s₀ * 1024 ≤ 2 ^ 32; omega_using [hm]⟩
      rw [eP, bR, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact ⟨R, List.mem_append_right _ RW.1, Offset.contains_base _ (by omega_using [lR, hn])
        (by have := RW.2; omega_using [lR, hn, this])⟩
    have inMc : (memR s₀).Contains (A (memP s₀) (cur * 1024 + 4 * n)) 4 := by
      rw [mem_addr' hp (by omega_using [b1])]
      exact Offset.contains_base _ b1 (by omega_using [b1, hb])
    have inC : (⟨matrixCell (memB s₀) cur, 1024⟩ : Region).Contains (A (memP s₀) (cur * 1024 + 4 * n)) 4 := by
      rw [mem_addr' hp (by omega_using [b1]), cell]
      exact Offset.contains _ (by omega_using []) (by omega_using [hn]) b2
    have inM : ∀ u : State, Inv s₀ u → InRegions u.wr (A (memP s₀) (cur * 1024 + 4 * n)) 4 :=
      fun u iu => ⟨memR s₀, by rw [iu.wr]; exact mem_mem hp, inMc⟩
    -- The word.
    have fin : ∀ (v : BitVec 32) (u : State), u.mem = t.mem.writeW (A (memP s₀) (cur * 1024 + 4 * n)) v →
        u.rd = t.rd → u.wr = t.wr → u.sp = t.sp → (∀ r, r ≠ .r0 → r ≠ .r2 → u.gpr r = s.gpr r) →
        v = (if xo then s.mem.readW (A P (4 * n)) 32 ^^^ mw s₀ s.mem (cur * 1024 + 4 * n)
          else s.mem.readW (A P (4 * n)) 32) →
        Inv s₀ u ∧ (∀ r, r ≠ .r0 → r ≠ .r2 → u.gpr r = s.gpr r) ∧
        Frame [⟨matrixCell (memB s₀) cur, 1024⟩] s.mem u.mem ∧
        ∀ i < 256, mw s₀ u.mem (cur * 1024 + 4 * i) = if i < n + 1 then
          (if xo then s.mem.readW (A P (4 * i)) 32 ^^^ mw s₀ s.mem (cur * 1024 + 4 * i)
            else s.mem.readW (A P (4 * i)) 32)
          else mw s₀ s.mem (cur * 1024 + 4 * i) := fun v u hm hrd hwr hsp gu ev => by
      have fu : Frame [⟨matrixCell (memB s₀) cur, 1024⟩] s.mem u.mem := by
        rw [hm]; exact ft.writeW (List.mem_singleton_self _) v inC
      have iu : Inv s₀ u := it.step hsp (by rw [gu _ (by decide) (by decide), gt _ (by decide) (by decide)])
        hrd hwr (by rw [hm]; exact (Frame.refl _ _).writeW (r := memR s₀) (by simp) v inMc)
      refine ⟨iu, gu, fu, fun i hi => ?_⟩
      rw [hm, mw_store hp _ b1 (by omega_using [hi, hc', hb]) (by omega_using []), wt i hi]
      by_cases e : i = n
      · subst e
        rw [ite_eq_left rfl, ite_eq_left (show i < i + 1 by omega_using []), ev]
      · rw [ite_eq_right (show ¬cur * 1024 + 4 * n = cur * 1024 + 4 * i by omega_using [e])]
        by_cases c : i < n
        · rw [ite_eq_left c, ite_eq_left (show i < n + 1 by omega_using [c])]
        · rw [ite_eq_right c, ite_eq_right (show ¬i < n + 1 by omega_using [c, e])]
    have o4 : 4 * n < 4096 := by omega_using [hn]
    cases xo
    · simp only [writeWord, Bool.false_eq_true, ite_false, List.nil_append]
      refine wp_ldr o4 ea inS fun u₁ v₁ => ?_
      refine wp_str (a := A (memP s₀) (cur * 1024 + 4 * n)) o4 (by rw [v₁.other .r3 (by decide)]; exact eb) (by rw [v₁.wr]; exact inM _ it)
        fun u mu => WP.block_nil ?_
      refine fin _ u (by rw [mu.mem, v₁.mem, v₁.gpr]) (by rw [mu.rd, v₁.rd]) (by rw [mu.wr, v₁.wr])
        (by rw [mu.sp, v₁.sp]) (fun r a b => by rw [mu.gpr, v₁.other r a, gt r a b]) ?_
      simp only [Bool.false_eq_true, ite_false]
      rw [sw_t]
    · simp only [writeWord, ite_true, List.cons_append, List.nil_append]
      refine wp_ldr o4 ea inS fun u₁ v₁ => ?_
      refine wp_ldr (a := A (memP s₀) (cur * 1024 + 4 * n)) o4 (by rw [v₁.other .r3 (by decide)]; exact eb)
        (by rw [v₁.rd, v₁.wr]; exact ⟨memR s₀, List.mem_append_right _ (by rw [it.wr]; exact mem_mem hp), inMc⟩)
        fun u₂ v₂ => wp_eor (op2_reg _ _) fun u₃ v₃ => ?_
      refine wp_str (a := A (memP s₀) (cur * 1024 + 4 * n)) o4 (by rw [v₃.other .r3 (by decide), v₂.other .r3 (by decide), v₁.other .r3 (by decide)]; exact eb)
        (by rw [v₃.wr, v₂.wr, v₁.wr]; exact inM _ it) fun u mu => WP.block_nil ?_
      refine fin _ u (by rw [mu.mem, v₃.mem, v₂.mem, v₁.mem, v₃.gpr]) (by rw [mu.rd, v₃.rd, v₂.rd, v₁.rd])
        (by rw [mu.wr, v₃.wr, v₂.wr, v₁.wr]) (by rw [mu.sp, v₃.sp, v₂.sp, v₁.sp])
        (fun r a b => by rw [mu.gpr, v₃.other r a, v₂.other r b, v₁.other r a, gt r a b]) ?_
      simp only [ite_true]
      rw [v₂.other .r0 (by decide), v₁.gpr, v₂.gpr, v₁.mem, sw_t, ← mw, wt n (by omega_using [hn]),
        ite_eq_right (show ¬n < n by omega_using [])]

end

end VG.Proof.Argon2.Arm.Derive

end

end

/-!
# Argon2 on ARMv7: one block of the filling loops

`fillCompress_ok`: G of the previous and reference blocks to
`scratch + 4096`; `fillWrite_ok`: the current block, copied or XORed;
`fillBlock_ok`: the filling state after one block (`Spec.Argon2.fillBlock`).
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_cmp op2_imm op2_reg)
open VG.Spec.Argon2 (Block zeroBlock FillState compress xorBlock)
open VG.Proof.Argon2.Arm (blk ofWords blk_of_words xor_words)
open VG.Proof.Sha512.Arm (Only A)
open VG.Impl.Argon2.Arm.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off refLaneOff startOff countOff tmpOff curOff writeBlock)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem outside_work : Outside s₀ ⟨scrB s₀, 4096⟩ := by
  have := outside_scr hp (o := 0) (n := 4096) (.inl (by decide))
  simpa using this

/-- The locals are kept by writes outside them. -/
theorem lw_outside {s t : State} {rs : List Region} (f : Frame rs s.mem t.mem) (ho : ∀ r ∈ rs, Outside s₀ r)
    {d : Nat} (hd : d + 4 ≤ 144) : lw s₀ t d = lw s₀ s d :=
  f.readW (r := ⟨State.addr (E s₀ + BitVec.ofNat 32 d), 4⟩) (Region.contains_self _ _)
    (fun r hr => (ho r hr).1.symm.sub_left (loc_word_sub hp hd)) (by decide)

/-- `fillCompress`: G of the previous and reference blocks, to `scratch + 4096`. -/
theorem fillCompress_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) {R : Nat} (hR : R < blocksN s₀)
    (htmp : lw s₀ s tmpOff = memP s₀ + BitVec.ofNat 32 (R * 1024)) :
    WP isa Impl.Argon2.Arm.Derive.fillCompress s fun t => FS s₀ pass slice lane index ctr st t ∧
      (∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ s d) ∧
      blk t.mem (scrP s₀) 4096 = compress (blockAt s.mem (matrixCell (memB s₀) (lane * (prm s₀).laneLen +
        (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) % (prm s₀).laneLen)))
        (blockAt s.mem (matrixCell (memB s₀) R)) := by
  have L8 := laneLen_ge hp
  obtain ⟨cl, _⟩ := cell_fits hp hl (col := (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) %
    (prm s₀).laneLen) (Nat.mod_lt _ (by omega_using [L8]))
  unfold Impl.Argon2.Arm.Derive.fillCompress
  refine WP.seq ((prevPointer_ok hp h.inv h.pr h.pos hl hs hi).mono fun s₁ ⟨a₁, k₁⟩ => ?_)
  generalize (lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) %
    (prm s₀).laneLen) = P at cl a₁ ⊢
  have h₁ := h.of_only k₁ (by decide)
  refine WP.seq (wp_ldloc hp h₁.inv (d := tmpOff) (by decide) fun s₂ u₂ => ?_)
  have h₂ := h₁.of_only (Only.of_upd u₂) (by decide)
  refine wp_ldarg hp h₂.inv (i := 15) (by decide) fun s₃ u₃ => ?_
  have h₃ := h₂.of_only (Only.of_upd u₃) (by decide)
  refine wp_add (op2_imm (by decide)) fun s₄ u₄ => WP.block_nil ?_
  have h₄ := h₃.of_only (Only.of_upd u₄) (by decide)
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, k₁.mem]
  have ax : s₄.gpr .r0 = memP s₀ + BitVec.ofNat 32 (P * 1024) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), a₁]
  have sx : s₄.gpr .r1 = memP s₀ + BitVec.ofNat 32 (R * 1024) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, lw_mem k₁.mem, htmp]
  have dx : s₄.gpr .r3 = scrP s₀ := by
    rw [u₄.other _ (by decide), u₃.gpr]
  have cx : s₄.gpr .r2 = scrP s₀ + BitVec.ofNat 32 4096 := by
    rw [u₄.gpr, u₃.gpr]; rfl
  refine ccall_ok hp h₄.inv dx (o := 4096) (by decide) (by decide) cx (by rw [ax]; exact .inl ⟨P, cl, rfl⟩)
    (by rw [sx]; exact .inl ⟨R, hR, rfl⟩) fun t it _ f post => ?_
  have ho : ∀ r ∈ [⟨scrB s₀ + BitVec.ofNat 64 4096, 1024⟩, ⟨scrB s₀, 4096⟩], Outside s₀ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact outside_scr hp (.inl (by decide))
    · exact outside_work hp
  refine ⟨h₄.frame hp it f ho, fun d hd => by rw [lw_outside hp f ho hd, lw_mem m₄], ?_⟩
  rw [post, ax, sx, cell_addr hp cl, cell_addr hp hR, m₄]

/-- `fillWrite`: G's output to the current block, XORed into it after the first pass. -/
theorem fillWrite_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) {C : Nat} (hC : C < blocksN s₀)
    (hcur : lw s₀ s curOff = memP s₀ + BitVec.ofNat 32 (C * 1024)) :
    WP isa Impl.Argon2.Arm.Derive.fillWrite s fun t => Inv s₀ t ∧
      Frame [⟨matrixCell (memB s₀) C, 1024⟩] s.mem t.mem ∧
      blockAt t.mem (matrixCell (memB s₀) C) = if pass = 0 then blk s.mem (scrP s₀) 4096 else
        xorBlock (blk s.mem (scrP s₀) 4096) (blockAt s.mem (matrixCell (memB s₀) C)) := by
  unfold Impl.Argon2.Arm.Derive.fillWrite
  refine WP.seq (wp_ldarg hp h.inv (i := 15) (by decide) fun s₁ u₁ => wp_add (op2_imm (by decide)) fun s₂ u₂ => ?_)
  have h₂ := h.of_only ((Only.of_upd u₁).trans (Only.of_upd u₂)) (by decide)
  refine wp_ldloc hp h₂.inv (d := curOff) (by decide) fun s₃ u₃ => ?_
  have h₃ := h₂.of_only (Only.of_upd u₃) (by decide)
  refine wp_ldloc hp h₃.inv (d := passOff) (by decide) fun s₄ u₄ =>
    wp_cmp (op2_imm (by decide)) fun s₅ f₅ z₅ => WP.block_nil ?_
  have h₅ := h₃.of_only ((Only.of_upd u₄).trans (Only.of_fupd f₅)) (by decide)
  have m₅ : s₅.mem = s.mem := by rw [f₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have si : s₅.gpr .r1 = scrP s₀ + BitVec.ofNat 32 4096 := by
    rw [f₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr]; rfl
  have di : s₅.gpr .r3 = memP s₀ + BitVec.ofNat 32 (C * 1024) := by
    rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, lw_mem u₂.mem, lw_mem u₁.mem, hcur]
  have hsf := hp.scr_fits
  have eP : State.addr (scrP s₀ + BitVec.ofNat 32 4096) = scrB s₀ + BitVec.ofNat 64 4096 := scr_addr hp (by decide)
  have Pfit : (scrP s₀ + BitVec.ofNat 32 4096).toNat + 1024 ≤ 2 ^ 32 := by rw [add_nat (by omega_using [hsf])]; omega_using [hsf]
  have Pw : ∃ R ∈ [scrR s₀, memR s₀], ∃ off, State.addr (scrP s₀ + BitVec.ofNat 32 4096) =
      R.base + BitVec.ofNat 64 off ∧ off + 1024 ≤ R.len :=
    ⟨scrR s₀, by simp, 4096, eP, by show 4096 + 1024 ≤ 16384; decide⟩
  have PC : Region.Disjoint ⟨State.addr (scrP s₀ + BitVec.ofNat 32 4096), 1024⟩ ⟨matrixCell (memB s₀) C, 1024⟩ := by
    rw [eP]
    exact (hp.mem_scr.symm.sub_left (Offset.sub_base _ (by decide))).sub_right (cell_in_mem hC)
  have nxt : blk s.mem (scrP s₀) 4096 = ofWords fun i => sw s₀ s.mem (4096 + 4 * i) :=
    blk_of_words fun _ _ => rfl
  have old : blockAt s.mem (matrixCell (memB s₀) C) = ofWords fun i => mw s₀ s.mem (C * 1024 + 4 * i) := by
    rw [cell_blk hp _ hC]; exact blk_of_words fun _ _ => rfl
  have done : ∀ (xo : Bool) (t : State), (∀ i < 256, mw s₀ t.mem (C * 1024 + 4 * i) = if i < 256 then
        (if xo then s₅.mem.readW (A (scrP s₀ + BitVec.ofNat 32 4096) (4 * i)) 32 ^^^ mw s₀ s₅.mem (C * 1024 + 4 * i)
          else s₅.mem.readW (A (scrP s₀ + BitVec.ofNat 32 4096) (4 * i)) 32)
        else mw s₀ s₅.mem (C * 1024 + 4 * i)) →
      blockAt t.mem (matrixCell (memB s₀) C) = if xo then
        xorBlock (blk s.mem (scrP s₀) 4096) (blockAt s.mem (matrixCell (memB s₀) C)) else blk s.mem (scrP s₀) 4096 :=
    fun xo t wt => by
      have e : blockAt t.mem (matrixCell (memB s₀) C) = ofWords fun i => if xo then
          sw s₀ s.mem (4096 + 4 * i) ^^^ mw s₀ s.mem (C * 1024 + 4 * i) else sw s₀ s.mem (4096 + 4 * i) := by
        rw [cell_blk hp _ hC]
        exact blk_of_words fun i hi => by rw [← mw, wt i hi, ite_eq_left hi, m₅, A_shift]
      rw [e, nxt, old]
      cases xo
      · rfl
      · simp only [ite_true]; rw [xor_words]
  refine WP.ite (decide (pass = 0)) (by
    show VG.Arm.eval .eq _ = _
    rw [MdStream.Arm.eval_eq, z₅, u₄.gpr, lw_mem u₃.mem, lw_mem u₂.mem, lw_mem u₁.mem, h.pos.pass, sub_zero32,
      MdStream.Arm.ofNat_beq_zero hpass])
    (fun hb => ?_) fun hb => ?_
  · refine ((writeWords_ok hp h₅.inv hC false si Pfit Pw PC di 256 (Nat.le_refl _)).mono fun t ⟨it, _, ft, wt⟩ =>
      ⟨it, by rw [← m₅]; exact ft, ?_⟩)
    rw [done false t wt, ite_eq_left (of_decide_eq_true hb)]; rfl
  · refine ((writeWords_ok hp h₅.inv hC true si Pfit Pw PC di 256 (Nat.le_refl _)).mono fun t ⟨it, _, ft, wt⟩ =>
      ⟨it, by rw [← m₅]; exact ft, ?_⟩)
    rw [done true t wt, ite_eq_right (of_decide_eq_false hb)]; rfl

/-- `fillBlock`: one block of the filling loops. -/
theorem fillBlock_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index) :
    WP isa Impl.Argon2.Arm.Derive.fillBlock s fun t =>
      FS s₀ pass slice lane index (ctrNext (prm s₀) pass slice index ctr)
        (Spec.Argon2.fillBlock (prm s₀) pass slice lane index st) t := by
  have hb : blocksN s₀ = (prm s₀).blocks := hp.blocks
  unfold Impl.Argon2.Arm.Derive.fillBlock
  refine WP.seq ((randomSource_ok hp h hpass hl hs hi).mono fun t₁ ⟨h₁, w₁⟩ => ?_)
  refine WP.seq ((reference_ok hp ⟨h₁, rfl, rfl⟩ hpass hl hs hi active).mono fun t₂ ⟨h₂, tmp₂, cur₂⟩ => ?_)
  rw [w₁] at tmp₂
  have refLt := Proof.Argon2.reference_cell_lt (prm s₀) hp.lanes_pos hp.memory_ge pass lane slice index
    (Proof.Argon2.FillStep.random (prm s₀) pass lane slice index st.memory) hl
  have curLt := Proof.Argon2.current_cell_lt (prm s₀) hp.lanes_pos hl hs hi
  have prevLt := Proof.Argon2.previous_cell_lt (prm s₀) hp.lanes_pos hp.memory_ge
    (column := slice * (prm s₀).segmentLen + index) hl
  simp only at refLt
  refine WP.seq ((fillCompress_ok hp h₂.fs hl hs hi (by rw [hb]; exact refLt) tmp₂).mono
    fun t₃ ⟨h₃, l₃, c₃⟩ => ?_)
  refine (fillWrite_ok hp h₃ hpass (C := lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index))
    (by rw [hb]; exact curLt) (by rw [l₃ _ (by decide)]; exact cur₂)).mono
    fun t ⟨it, ft, bt⟩ => ?_
  have kept : ∀ j < (prm s₀).blocks, j ≠ lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index) →
      blockAt t.mem (matrixCell (memB s₀) j) = blockAt t₃.mem (matrixCell (memB s₀) j) := fun j hj ne =>
    blockAt_keep ft fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact cell_other hp (by rw [hb]; exact hj) (by rw [hb]; exact curLt) ne
  have lt : ∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ t₃ d := fun d hd =>
    ft.readW (r := ⟨State.addr (E s₀ + BitVec.ofNat 32 d), 4⟩) (Region.contains_self _ _) (fun r hr => by
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
      rw [scr_blk hp _ (by decide), blockAt_keep ft (fun r hr => ?_), ← scr_blk hp _ (by decide), c4]
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.mem_scr.symm.sub_left (Offset.sub_base _ (by decide))).sub_right
        (cell_in_mem (by rw [hb]; exact curLt))
  · rw [Proof.Argon2.FillStep.memory _ _ _ _ _ _ active]
    simp only [Proof.Argon2.FillStep.update]
    refine Represents.update h₃.mem _ curLt _ ?_ kept
    rw [bt, c₃, h₂.fs.mem.block _ prevLt, h₂.fs.mem.block _ refLt, h₃.mem.block _ curLt]

end

end VG.Proof.Argon2.Arm.Derive
