import VerifiedGarbage.Proof.Argon2.Arm.Derive.FillCount

/-!
# Argon2 on ARMv7: the reference block's column and the block pointers

`relative_ok`: the position in the window that J₁ selects (RFC 9106
§3.4.2), with the high halves of the products from `mulHi`; `wrap_ok`: its
column, from the window's start, modulo the lane length; `refPointer_ok` and
`curPointer_ok`: the reference and current blocks' addresses, to the locals.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_sub wp_and op2_imm op2_reg)
open VG.Proof.Blake2.Arm.Stream (wp_adc)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState)
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
  have lt := Proof.Argon2.reference_scale_lt_count cnt J1.toNat (by omega) jb
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
      toNat32 hc', toNat32 x32, ofNat_pred hc rfl, MdStream.Arm.sub_ofNat (by omega), relV]
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
    omega
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
    rw [x₄, l₄, toNat32 (by omega), toNat32 (by omega)] at c₅
    simp only [upd_get u, upd_get u₈, upd_get u₇, upd_get u₆, upd_get u₅, ↓reduceIte, reduceCtorEq, c₅, x₄, l₄,
      u₄.gpr]
    rw [Proof.Argon2.reference_wrap (stt + rel) (prm s₀).laneLen (by omega)]
    by_cases c : stt + rel < (prm s₀).laneLen
    · have c' : ¬(prm s₀).laneLen ≤ stt + rel := by omega
      simp only [c, c', decide_false, ite_true, Bool.false_eq_true, ite_false]
      rw [show (0 : BitVec 32) + 0 + 0 - 1 = BitVec.allOnes 32 by decide, BitVec.allOnes_and,
        BitVec.sub_add_cancel]
    · have c' : (prm s₀).laneLen ≤ stt + rel := by omega
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
    omega
  have ll := hp.laneLen_eq
  have s2 := hp.segLen_two
  have hl1 := hp.lanes_pos
  rw [ref_eq]
  generalize hRL : refLaneV (prm s₀).lanes pass slice lane J2.toNat = RL
  have hRL' : refLaneV (lanesN s₀) pass slice lane J2.toNat = RL := hRL
  have rl_lt : RL < lanesN s₀ := by
    rw [← hRL', refLaneV]; split
    · exact hl
    · exact Nat.mod_lt _ (by omega)
  have first : pass = 0 → slice = 0 → RL = lane := fun a b => by rw [← hRL', refLaneV, ite_eq_left ⟨a, b⟩]
  generalize hB : baseV (prm s₀).segmentLen (prm s₀).laneLen pass slice = B
  have b_le : B ≤ (prm s₀).laneLen := by
    rw [← hB, baseV]; split
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (show slice ≤ 3 by omega)) (by omega))
    · omega
  generalize hST : startV (prm s₀).segmentLen (prm s₀).laneLen pass slice = ST
  have st_lt : ST < (prm s₀).laneLen := by
    rw [← hST, startV]; split
    · omega
    · exact Nat.mod_lt _ (by omega)
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
  refine countSelect_ok hp h₃ (base := B) (rl := RL) (by omega) hi hl rl_lt a₃
    (by rw [lw_mem k₃.mem, r₂, r₁]) (fun e => ?_) (fun e e0 => ?_) fun t₄ h₄ a₄ c₄ o₄ g₄ => ?_
  · rw [← hB, baseV]; split
    · rename_i hp0
      by_cases hs0 : slice = 0
      · omega
      · have := Nat.mul_le_mul_right (prm s₀).segmentLen (show 1 ≤ slice by omega); omega
    · omega
  · have : ¬(pass = 0 ∧ slice = 0) := fun ⟨a, b⟩ => e (first a b)
    rw [← hB, baseV]; split
    · rename_i hp0
      have := Nat.mul_le_mul_right (prm s₀).segmentLen (show 1 ≤ slice by omega); omega
    · omega
  refine relative_ok hp h₄ (cnt := countV B index (RL == lane)) cpos (by omega) c₄ fun t₅ a₅ k₅ => ?_
  have h₅ := h₄.of_only k₅ (by decide)
  have rel_lt : relV (countV B index (RL == lane)) J1.toNat < (prm s₀).laneLen := by
    unfold relV; omega
  refine wrap_ok hp h₅ rel_lt st_lt a₅ (by
      rw [lw_mem k₅.mem, o₄ _ (by decide) (by decide), lw_mem k₃.mem, st₂]) fun t₆ a₆ k₆ => ?_
  have h₆ := h₅.of_only k₆ (by decide)
  refine refPointer_ok hp h₆ (Nat.mod_lt _ (by omega)) rl_lt a₆ (by
      rw [lw_mem k₆.mem, lw_mem k₅.mem, o₄ _ (by decide) (by decide), lw_mem k₃.mem, r₂, r₁])
    fun t₇ h₇ p₇ o₇ _ => ?_
  refine curPointer_ok hp h₇ hl hs hi fun t h' c' o' _ => WP.block_nil ⟨h', ?_, c'⟩
  rw [o' _ (by decide) (by decide), p₇]

end

end VG.Proof.Argon2.Arm.Derive
