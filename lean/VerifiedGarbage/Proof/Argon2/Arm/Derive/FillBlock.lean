module

public import VerifiedGarbage.Proof.Argon2.Arm.Derive.FillInput
public import VerifiedGarbage.Proof.Argon2.FillStep
import VerifiedGarbage.Proof.Argon2.FillPositions
import VerifiedGarbage.Proof.Argon2.Arm.Derive.FillCache
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
import VerifiedGarbage.Proof.Argon2.Arm.Words
import VerifiedGarbage.Proof.Argon2.Arm.Mix
import VerifiedGarbage.Proof.Blake2.Arm.Stream.Common
import VerifiedGarbage.Proof.Argon2.Reference
import VerifiedGarbage.Proof.Argon2.Dimensions

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
