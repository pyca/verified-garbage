import VerifiedGarbage.Proof.Argon2.Arm.Derive.FillCache
import VerifiedGarbage.Proof.Argon2.Reference

/-!
# Argon2 on ARMv7: the reference block's lane, start and base

`RS`: the filling state with J₁ and J₂ in the locals. `refLane_ok`: the
reference lane (RFC 9106 §3.4.2); `refStart_ok`: where the window of
eligible blocks starts; `countBase_ok`: the blocks before the current
segment that a reference may use.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_sub wp_orr wp_cmp op2_imm op2_reg)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState)
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
    rw [hm, lw_store hp (by omega) (by decide) (by simp [j1Off] at h1 ⊢; omega)]; exact h.j1
  · show t.mem.readW _ 32 = _
    rw [hm, lw_store hp (by omega) (by decide) (by simp [j2Off] at h2 ⊢; omega)]; exact h.j2

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
    rw [r₃, u₂.other _ (by decide), u₁.gpr, h.j2, toNat32 (by have := J2.isLt; have := Nat.mod_le J2.toNat (lanesN s₀); omega)])
  refine ⟨h₇, ?_, by rw [lw_mem f.mem, lw_mem u₇.mem, lw_mem u₆.mem, lw_mem u₅.mem, v₄, r]⟩
  rw [MdStream.Arm.eval_eq, z, u₇.gpr, u₆.other _ (by decide), u₅.gpr, u₆.gpr, lw_mem u₅.mem, h₄.fs.pos.slice,
    h₄.fs.pos.pass, sub_zero32, or_zero hpass (by omega)]

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
        MdStream.Arm.sub_beq (by omega) (by decide)]) (fun hb' => ?_) fun hb' => ?_
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
          rw [ll]; exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
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
      MdStream.Arm.sub_ofNat (by omega), baseV, ite_eq_right (of_decide_eq_false hb)]

end

end VG.Proof.Argon2.Arm.Derive
