module
public import VerifiedGarbage.Proof.Framework.AArch64.Tbl
public import VerifiedGarbage.Impl.Blowfish.AArch64
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Blowfish.AArch64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint

/-! ### `Blowfish.AArch64.Lookup`, which only this module used -/

section

/-!
# S-box lookups

`quarter_run`: four loads of quarter `q` of byte plane `b` of S-box `j`
into `v28`–`v31`, then a `tbl` (for `q = 0`) or `tbx` of them, leave in
each byte lane of the destination the plane's byte at the lane's index,
if it is in the quarter (below 64), and otherwise 0 (`tbl`) or the
destination's byte (`tbx`). `lookupPlane_run`: the four quarters, on the
index XORed with 0, 64, 128 and 192, leave the plane's byte at the index.
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64
open VG.AArch64.Tbl (VOnly)

/-- The schedule's planes are readable from `sch`, 16 bytes at a time. -/
def Readable (s : State) (sch : Reg) : Prop :=
  ∀ off, off < 4096 → InRegions (s.rd ++ s.wr) (s.gpr sch + BitVec.ofNat 64 off) 16

theorem repeat_succ_v28 : ∀ k < 4, Nat.repeat VReg.succ k (tReg 0) = tReg k := by decide

theorem loadQuarter_eq (sch : Reg) (j b q : Nat) :
    loadQuarter sch j b q =
      [.ldrq .v28 sch (planeOff j b + 64 * q + 16 * 0), .ldrq .v29 sch (planeOff j b + 64 * q + 16 * 1),
       .ldrq .v30 sch (planeOff j b + 64 * q + 16 * 2), .ldrq .v31 sch (planeOff j b + 64 * q + 16 * 3)] :=
  rfl

theorem quarter_run {s : State} {sch : Reg} (hR : Readable s sch) {j b q : Nat} (hj : j < 4)
    (hb : b < 4) (hq : q < 4) {d m : VReg} (hd : ∀ r < 4, d ≠ tReg r) (hm : ∀ r < 4, m ≠ tReg r) :
    ∃ s', runBlock isa (loadQuarter sch j b q ++ ([.vop (.tblN (q != 0) 4 d (tReg 0) m)] : List Instr)) s = some s' ∧
      (∀ e < 16, vbyte (s'.v d) e =
        if (vbyte (s.v m) e).toNat < 64 then
          s.mem (s.gpr sch + BitVec.ofNat 64 (planeOff j b + 64 * q + (vbyte (s.v m) e).toNat))
        else if q != 0 then vbyte (s.v d) e else 0) ∧
      VOnly [.v28, .v29, .v30, .v31, d] s s' := by
  let base := planeOff j b + 64 * q
  have hbase : base + 64 ≤ 4096 := by simp only [base, planeOff]; omega_arith
  let ld (r : Nat) := s.mem.read (s.gpr sch + BitVec.ofNat 64 (base + 16 * r)) 16
  let s₁ := s.setV .v28 (ld 0)
  let s₂ := s₁.setV .v29 (ld 1)
  let s₃ := s₂.setV .v30 (ld 2)
  let s₄ := s₃.setV .v31 (ld 3)
  have hv : ∀ r < 4, s₄.v (tReg r) = ld r := by
    intro r hr
    rcases (by omega_arith : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;> rfl
  have hv' : ∀ x, (∀ r < 4, x ≠ tReg r) → s₄.v x = s.v x := by
    intro x hx
    have h0 : x ≠ .v28 := hx 0 (by decide)
    have h1 : x ≠ .v29 := hx 1 (by decide)
    have h2 : x ≠ .v30 := hx 2 (by decide)
    have h3 : x ≠ .v31 := hx 3 (by decide)
    simp only [s₄, s₃, s₂, s₁, v_setV_of_ne _ _ h0, v_setV_of_ne _ _ h1, v_setV_of_ne _ _ h2,
      v_setV_of_ne _ _ h3]
  let s₅ := s₄.setV d (ofVBytes fun i =>
      if (vbyte (s₄.v m) i).toNat < 16 * 4 then tableByte s₄.v (tReg 0) (vbyte (s₄.v m) i).toNat
      else if (q != 0) then vbyte (s₄.v d) i else 0)
  have rd : ∀ r < 4, InRegions (s.rd ++ s.wr) (s.gpr sch + BitVec.ofNat 64 (base + 16 * r)) 16 :=
    fun r hr => hR _ (by omega_arith)
  have ho : ∀ r < 4, (base + 16 * r) % 16 = 0 ∧ base + 16 * r < 65536 := fun r hr => by
    simp only [base, planeOff]; omega_arith
  refine ⟨s₅, ?_, ?_, ?_⟩
  · have e₁ : exec (.ldrq .v28 sch (planeOff j b + 64 * q + 16 * 0)) s = some s₁ :=
      exec_ldrq (ho 0 (by decide)) (rd 0 (by decide))
    have e₂ : exec (.ldrq .v29 sch (planeOff j b + 64 * q + 16 * 1)) s₁ = some s₂ :=
      exec_ldrq (ho 1 (by decide)) (rd 1 (by decide))
    have e₃ : exec (.ldrq .v30 sch (planeOff j b + 64 * q + 16 * 2)) s₂ = some s₃ :=
      exec_ldrq (ho 2 (by decide)) (rd 2 (by decide))
    have e₄ : exec (.ldrq .v31 sch (planeOff j b + 64 * q + 16 * 3)) s₃ = some s₄ :=
      exec_ldrq (ho 3 (by decide)) (rd 3 (by decide))
    have e₅ : exec (.vop (.tblN (q != 0) 4 d (tReg 0) m)) s₄ = some s₅ := exec_tbl4 _ _ _ _ _
    rw [loadQuarter_eq]
    simp only [List.cons_append, List.nil_append]
    rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_cons, e₄, runStep_some, runBlock_cons, e₅, runStep_some, runBlock_nil]
  · intro e he
    simp only [s₅, v_setV_self]
    rw [vbyte_ofVBytes _ he, hv' m hm, hv' d hd]
    split
    · rename_i h
      rw [tableByte, repeat_succ_v28 _ (by omega_arith), hv _ (by omega_arith), vbyte_read16 _ _ (by omega_arith),
        Offset.add_add]
      exact congrArg _ (congrArg _ (congrArg _ (by omega_arith)))
    · rfl
  · refine ((((VOnly.setV s (by simp) _).trans (VOnly.setV _ (by simp) _)).trans
      (VOnly.setV _ (by simp) _)).trans (VOnly.setV _ (by simp) _)).trans (VOnly.setV _ (by simp) _)

/-- `tbl` of the first quarter at the index, then `tbx` of each other at the
index XORed with the quarter's base: the table's byte at the index. -/
theorem tbx_chain (T : Nat → BitVec 8) (X : Nat) (hX : X < 256) :
    (if X ^^^ 64 * 3 < 64 then T (64 * 3 + (X ^^^ 64 * 3)) else
      if X ^^^ 64 * 2 < 64 then T (64 * 2 + (X ^^^ 64 * 2)) else
      if X ^^^ 64 < 64 then T (64 + (X ^^^ 64)) else
      if X < 64 then T (64 * 0 + X) else 0) = T X := by
  have q := VG.AArch64.Tbl.xor_quarter X hX
  obtain ⟨h1, e1⟩ := q 1 (by decide)
  obtain ⟨h2, e2⟩ := q 2 (by decide)
  obtain ⟨h3, e3⟩ := q 3 (by decide)
  simp only [Nat.mul_one] at h1 e1
  rcases (by omega_arith : X / 64 = 0 ∨ X / 64 = 1 ∨ X / 64 = 2 ∨ X / 64 = 3) with h | h | h | h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h' => by have := h3.mp h'; omega_arith)), ite_eq_right_of_eq_false _ _ (eq_false (fun h' => by have := h2.mp h'; omega_arith)),
      ite_eq_right_of_eq_false _ _ (eq_false (fun h' => by have := h1.mp h'; omega_arith)), ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith))]
    exact congrArg T (by omega_arith)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h' => by have := h3.mp h'; omega_arith)), ite_eq_right_of_eq_false _ _ (eq_false (fun h' => by have := h2.mp h'; omega_arith)),
      ite_eq_left_of_eq_true _ _ (eq_true (h1.mpr h)), e1 h]
    exact congrArg T (by omega_arith)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h' => by have := h3.mp h'; omega_arith)), ite_eq_left_of_eq_true _ _ (eq_true (h2.mpr h)), e2 h]
    exact congrArg T (by omega_arith)
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (h3.mpr h)), e3 h]
    exact congrArg T (by omega_arith)

theorem out_ne_t : ∀ b < 4, ∀ r < 4, outReg b ≠ tReg r := by decide
theorem idx_ne_t : ∀ j < 4, ∀ r < 4, idxReg j ≠ tReg r := by decide
theorem q_ne_t : ∀ q < 4, ∀ r < 4, qReg q ≠ tReg r := by decide
theorem idx_ne_out : ∀ j < 4, ∀ b < 4, idxReg j ≠ outReg b := by decide
theorem q_ne_out : ∀ q < 4, ∀ b < 4, qReg q ≠ outReg b := by decide
theorem idx_ne_q : ∀ j < 4, ∀ q < 4, idxReg j ≠ qReg q := by decide

theorem regs_ne (j : Nat) (hj : j < 4) (b : Nat) (hb : b < 4) (q : Nat) (hq : q < 4) (r : Nat)
    (hr : r < 4) : outReg b ≠ tReg r ∧ idxReg j ≠ tReg r ∧ qReg q ≠ tReg r ∧ idxReg j ≠ outReg b ∧
      qReg q ≠ outReg b ∧ idxReg j ≠ qReg q :=
  ⟨out_ne_t b hb r hr, idx_ne_t j hj r hr, q_ne_t q hq r hr, idx_ne_out j hj b hb, q_ne_out q hq b hb,
    idx_ne_q j hj q hq⟩

theorem lookupPlane_eq (sch : Reg) (j b : Nat) :
    lookupPlane sch j b =
      (loadQuarter sch j b 0 ++ ([.vop (.tblN (0 != 0) 4 (outReg b) (tReg 0) (idxReg j))] : List Instr)) ++
      ((loadQuarter sch j b 1 ++ ([.vop (.tblN (1 != 0) 4 (outReg b) (tReg 0) (qReg 1))] : List Instr)) ++
      ((loadQuarter sch j b 2 ++ ([.vop (.tblN (2 != 0) 4 (outReg b) (tReg 0) (qReg 2))] : List Instr)) ++
      ((loadQuarter sch j b 3 ++ ([.vop (.tblN (3 != 0) 4 (outReg b) (tReg 0) (qReg 3))] : List Instr)) ++ []))) :=
  rfl

/-- Byte plane `b` of S-box `j`, at the indices in `idxReg j` (and them
XORed with 64, 128 and 192 in `qReg`). -/
theorem lookupPlane_run {s : State} {sch : Reg} (hR : Readable s sch) {j b : Nat} (hj : j < 4)
    (hb : b < 4) (hq : ∀ q < 4, 0 < q → ∀ e < 16,
      vbyte (s.v (qReg q)) e = vbyte (s.v (idxReg j)) e ^^^ BitVec.ofNat 8 (64 * q)) :
    ∃ s', runBlock isa (lookupPlane sch j b) s = some s' ∧
      (∀ e < 16, vbyte (s'.v (outReg b)) e =
        s.mem (s.gpr sch + BitVec.ofNat 64 (planeOff j b + (vbyte (s.v (idxReg j)) e).toNat))) ∧
      VOnly [.v28, .v29, .v30, .v31, outReg b] s s' := by
  have ne := regs_ne j hj b hb
  have hd : ∀ r < 4, outReg b ≠ tReg r := fun r hr => (ne 0 (by decide) r hr).1
  have hR' : ∀ {t : State}, VOnly [.v28, .v29, .v30, .v31, outReg b] s t → Readable t sch := by
    intro t ht off hoff
    rw [ht.rd, ht.wr, ht.gpr]; exact hR off hoff
  obtain ⟨s₁, r₁, v₁, o₁⟩ := quarter_run hR hj hb (by decide : 0 < 4) hd (fun r hr => (ne 0 (by decide) r hr).2.1)
  obtain ⟨s₂, r₂, v₂, o₂⟩ := quarter_run (hR' o₁) hj hb (by decide : 1 < 4) hd
    (fun r hr => (ne 1 (by decide) r hr).2.2.1)
  have o₁₂ := o₁.trans o₂
  obtain ⟨s₃, r₃, v₃, o₃⟩ := quarter_run (hR' o₁₂) hj hb (by decide : 2 < 4) hd
    (fun r hr => (ne 2 (by decide) r hr).2.2.1)
  have o₁₃ := o₁₂.trans o₃
  obtain ⟨s₄, r₄, v₄, o₄⟩ := quarter_run (hR' o₁₃) hj hb (by decide : 3 < 4) hd
    (fun r hr => (ne 3 (by decide) r hr).2.2.1)
  have o₁₄ := o₁₃.trans o₄
  refine ⟨s₄, ?_, ?_, o₁₄⟩
  · rw [lookupPlane_eq]
    exact VG.AArch64.Tbl.runBlock_cat_some r₁ (VG.AArch64.Tbl.runBlock_cat_some r₂
      (VG.AArch64.Tbl.runBlock_cat_some r₃ (VG.AArch64.Tbl.runBlock_cat_some r₄ runBlock_nil)))
  · intro e he
    -- the registers read are unchanged
    have kept : ∀ {t : State} (x : VReg), VOnly [.v28, .v29, .v30, .v31, outReg b] s t →
        (∀ r < 4, x ≠ tReg r) → x ≠ outReg b → t.v x = s.v x := by
      intro t x ht hx hxo
      refine ht.2 x ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      have := hx 0 (by decide); have := hx 1 (by decide); have := hx 2 (by decide)
      have := hx 3 (by decide)
      rintro (h | h | h | h | h) <;> contradiction
    have m₁ : s₁.mem = s.mem := o₁.mem
    have m₂ : s₂.mem = s.mem := o₁₂.mem
    have m₃ : s₃.mem = s.mem := o₁₃.mem
    have g₁ : s₁.gpr = s.gpr := o₁.gpr
    have g₂ : s₂.gpr = s.gpr := o₁₂.gpr
    have g₃ : s₃.gpr = s.gpr := o₁₃.gpr
    have q₁ : s₁.v (qReg 1) = s.v (qReg 1) := kept _ o₁ (fun r hr => (ne 1 (by decide) r hr).2.2.1)
      (ne 1 (by decide) 0 (by decide)).2.2.2.2.1
    have q₂ : s₂.v (qReg 2) = s.v (qReg 2) := kept _ o₁₂ (fun r hr => (ne 2 (by decide) r hr).2.2.1)
      (ne 2 (by decide) 0 (by decide)).2.2.2.2.1
    have q₃ : s₃.v (qReg 3) = s.v (qReg 3) := kept _ o₁₃ (fun r hr => (ne 3 (by decide) r hr).2.2.1)
      (ne 3 (by decide) 0 (by decide)).2.2.2.2.1
    let X := vbyte (s.v (idxReg j)) e
    have hX : X.toNat < 256 := X.isLt
    have hxq : ∀ q < 4, 0 < q → (vbyte (s.v (qReg q)) e).toNat = X.toNat ^^^ 64 * q := by
      intro q hq0 hq1
      rw [hq q hq0 hq1 e he, VG.AArch64.Tbl.toNat_xor_lit _ _ (by omega_arith)]
    rw [v₄ e he, q₃, hxq 3 (by decide) (by decide), v₃ e he, q₂, hxq 2 (by decide) (by decide),
      v₂ e he, q₁, hxq 1 (by decide) (by decide), v₁ e he, m₃, m₂, m₁, g₃, g₂, g₁]
    simp only [show (3 != 0) = true from rfl, show (2 != 0) = true from rfl,
      show (1 != 0) = true from rfl, show (0 != 0) = false from rfl, ite_true, Bool.false_eq_true,
      ite_false]
    have := tbx_chain (fun i => s.mem (s.gpr sch + BitVec.ofNat 64 (planeOff j b + i))) X.toNat hX
    simp only [Nat.add_assoc]
    exact this

end VG.Proof.Blowfish.AArch64

end

end


/-!
# One S-box

`lookup_run`: `lookup j` leaves in `outReg b` byte plane `b` of S-box `j` at
the indices in `idxReg j`. `combine_run`: `combine j` accumulates the words
into `fReg`.
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64
open VG.AArch64.Tbl (VOnly)

/-- 64 and 128 in every byte of `c64` and `c128`. -/
def Consts (s : State) : Prop :=
  (∀ e < 16, vbyte (s.v c64) e = 64) ∧ ∀ e < 16, vbyte (s.v c128) e = 128

/-- The registers `lookup` writes. -/
def lookupRegs : List VReg :=
  [.v24, .v25, .v26, .v28, .v29, .v30, .v31, .v20, .v21, .v22, .v23]

theorem VOnly.mono {ds ds' : List VReg} {a b : State} (h : VOnly ds a b) (hs : ∀ r ∈ ds, r ∈ ds') :
    VOnly ds' a b := ⟨h.1, fun r hr => h.2 r fun h' => hr (hs r h')⟩

theorem q_notin : ∀ q < 4, 0 < q → ∀ b < 4, qReg q ∉ [VReg.v28, .v29, .v30, .v31, outReg b] := by
  decide
theorem idx_notin : ∀ j < 4, ∀ b < 4, idxReg j ∉ [VReg.v28, .v29, .v30, .v31, outReg b] := by decide
theorem out_notin : ∀ b < 4, ∀ b' < 4, b ≠ b' → outReg b ∉ [VReg.v28, .v29, .v30, .v31, outReg b'] := by
  decide
theorem idx_ne_q123 : ∀ j < 4, idxReg j ≠ .v24 ∧ idxReg j ≠ .v25 ∧ idxReg j ≠ .v26 := by decide
theorem plane_sub : ∀ b < 4, ∀ r ∈ [VReg.v28, .v29, .v30, .v31, outReg b], r ∈ lookupRegs := by decide

theorem lookup_run {s : State} {sch : Reg} (hR : Readable s sch) (hc : Consts s) {j : Nat}
    (hj : j < 4) :
    ∃ s', runBlock isa (lookup sch j) s = some s' ∧
      (∀ b < 4, ∀ e < 16, vbyte (s'.v (outReg b)) e =
        s.mem (s.gpr sch + BitVec.ofNat 64 (planeOff j b + (vbyte (s.v (idxReg j)) e).toNat))) ∧
      VOnly lookupRegs s s' := by
  have hidx := idx_ne_q123 j hj
  let s₁ := s.setV (qReg 1) (s.v (idxReg j) ^^^ s.v c64)
  let s₂ := s₁.setV (qReg 2) (s₁.v (idxReg j) ^^^ s₁.v c128)
  let s₃ := s₂.setV (qReg 3) (s₂.v (qReg 1) ^^^ s₂.v c128)
  have X : s₃.v (idxReg j) = s.v (idxReg j) := by
    simp only [s₃, s₂, s₁, qReg, List.getD_cons_zero, List.getD_cons_succ, v_setV_of_ne _ _ hidx.1,
      v_setV_of_ne _ _ hidx.2.1, v_setV_of_ne _ _ hidx.2.2]
  have q1 : s₃.v (qReg 1) = s.v (idxReg j) ^^^ s.v c64 := by
    simp only [s₃, s₂, s₁, qReg, List.getD_cons_zero, List.getD_cons_succ, v_setV, reduceCtorEq,
      ite_true, ite_false]
  have q2 : s₃.v (qReg 2) = s.v (idxReg j) ^^^ s.v c128 := by
    simp only [s₃, s₂, s₁, qReg, List.getD_cons_zero, List.getD_cons_succ, v_setV, reduceCtorEq,
      ite_true, ite_false, c128, c64, hidx.1]
  have q3 : s₃.v (qReg 3) = s.v (idxReg j) ^^^ s.v c64 ^^^ s.v c128 := by
    simp only [s₃, s₂, s₁, qReg, List.getD_cons_zero, List.getD_cons_succ, v_setV, reduceCtorEq,
      ite_true, ite_false, c128, c64, hidx.1]
  have hq : ∀ q < 4, 0 < q → ∀ e < 16,
      vbyte (s₃.v (qReg q)) e = vbyte (s₃.v (idxReg j)) e ^^^ BitVec.ofNat 8 (64 * q) := by
    intro q hq0 hq1 e he
    rw [X]
    rcases (by omega_using [hq0, hq1] : q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl
    · rw [q1, vbyte_xor, hc.1 e he]; rfl
    · rw [q2, vbyte_xor, hc.2 e he]; rfl
    · rw [q3, vbyte_xor, vbyte_xor, hc.1 e he, hc.2 e he, BitVec.xor_assoc]; rfl
  have o₃ : VOnly lookupRegs s s₃ :=
    (((VOnly.setV s (by simp [lookupRegs, qReg]) _).trans (VOnly.setV _ (by simp [lookupRegs, qReg]) _)).trans
      (VOnly.setV _ (by simp [lookupRegs, qReg]) _))
  have hR₃ : ∀ {t : State}, VOnly lookupRegs s t → Readable t sch := by
    intro t ht off hoff
    rw [ht.rd, ht.wr, ht.gpr]; exact hR off hoff
  -- each plane keeps what the others read and wrote
  have step : ∀ {t : State} (b : Nat), b < 4 → VOnly lookupRegs s t →
      (∀ q < 4, 0 < q → ∀ e < 16,
        vbyte (t.v (qReg q)) e = vbyte (t.v (idxReg j)) e ^^^ BitVec.ofNat 8 (64 * q)) →
      ∃ t', runBlock isa (lookupPlane sch j b) t = some t' ∧
        (∀ e < 16, vbyte (t'.v (outReg b)) e =
          s.mem (s.gpr sch + BitVec.ofNat 64 (planeOff j b + (vbyte (t.v (idxReg j)) e).toNat))) ∧
        VOnly [.v28, .v29, .v30, .v31, outReg b] t t' := by
    intro t b hb ht hqt
    obtain ⟨t', r, v, o⟩ := lookupPlane_run (hR₃ ht) hj hb hqt
    refine ⟨t', r, fun e he => ?_, o⟩
    rw [v e he, ht.mem, ht.gpr]
  have ob := plane_sub
  have hqk : ∀ {t t' : State} (b : Nat), b < 4 → VOnly [.v28, .v29, .v30, .v31, outReg b] t t' →
      (∀ q < 4, 0 < q → ∀ e < 16,
        vbyte (t.v (qReg q)) e = vbyte (t.v (idxReg j)) e ^^^ BitVec.ofNat 8 (64 * q)) →
      (∀ q < 4, 0 < q → ∀ e < 16,
        vbyte (t'.v (qReg q)) e = vbyte (t'.v (idxReg j)) e ^^^ BitVec.ofNat 8 (64 * q)) := by
    intro t t' b hb o h q hq0 hq1 e he
    rw [o.2 _ (q_notin q hq0 hq1 b hb), o.2 _ (idx_notin j hj b hb)]; exact h q hq0 hq1 e he
  have ni := idx_notin j hj
  obtain ⟨t₀, r₀, v₀, o₀⟩ := step 0 (by decide) o₃ hq
  have p₀ := o₃.trans (VOnly.mono o₀ (ob 0 (by decide)))
  obtain ⟨t₁, r₁, v₁, o₁⟩ := step 1 (by decide) p₀ (hqk 0 (by decide) o₀ hq)
  have p₁ := p₀.trans (VOnly.mono o₁ (ob 1 (by decide)))
  obtain ⟨t₂, r₂, v₂, o₂⟩ := step 2 (by decide) p₁ (hqk 1 (by decide) o₁ (hqk 0 (by decide) o₀ hq))
  have p₂ := p₁.trans (VOnly.mono o₂ (ob 2 (by decide)))
  obtain ⟨t₃, r₃, v₃, o₃'⟩ := step 3 (by decide) p₂
    (hqk 2 (by decide) o₂ (hqk 1 (by decide) o₁ (hqk 0 (by decide) o₀ hq)))
  have p₃ := p₂.trans (VOnly.mono o₃' (ob 3 (by decide)))
  refine ⟨t₃, ?_, ?_, p₃⟩
  · have e₁ : exec (veor (qReg 1) (idxReg j) c64) s = some s₁ := rfl
    have e₂ : exec (veor (qReg 2) (idxReg j) c128) s₁ = some s₂ := rfl
    have e₃ : exec (veor (qReg 3) (qReg 1) c128) s₂ = some s₃ := rfl
    have l : lookup sch j = [veor (qReg 1) (idxReg j) c64, veor (qReg 2) (idxReg j) c128,
        veor (qReg 3) (qReg 1) c128] ++ (lookupPlane sch j 0 ++ (lookupPlane sch j 1 ++
        (lookupPlane sch j 2 ++ (lookupPlane sch j 3 ++ [])))) := rfl
    rw [l, List.cons_append, List.cons_append, List.cons_append, List.nil_append, runBlock_cons, e₁,
      runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃, runStep_some]
    exact VG.AArch64.Tbl.runBlock_cat_some r₀ (VG.AArch64.Tbl.runBlock_cat_some r₁
      (VG.AArch64.Tbl.runBlock_cat_some r₂ (VG.AArch64.Tbl.runBlock_cat_some r₃ runBlock_nil)))
  · -- the index register is never written
    have i₀ : t₀.v (idxReg j) = s.v (idxReg j) := (o₀.2 _ (ni 0 (by decide))).trans X
    have i₁ : t₁.v (idxReg j) = s.v (idxReg j) := (o₁.2 _ (ni 1 (by decide))).trans i₀
    have i₂ : t₂.v (idxReg j) = s.v (idxReg j) := (o₂.2 _ (ni 2 (by decide))).trans i₁
    intro b hb e he
    have nob := out_notin
    rcases (by omega_using [hb] : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl
    · rw [o₃'.2 _ (nob 0 (by decide) 3 (by decide) (by decide)), o₂.2 _ (nob 0 (by decide) 2 (by decide) (by decide)),
        o₁.2 _ (nob 0 (by decide) 1 (by decide) (by decide)), v₀ e he, X]
    · rw [o₃'.2 _ (nob 1 (by decide) 3 (by decide) (by decide)), o₂.2 _ (nob 1 (by decide) 2 (by decide) (by decide)),
        v₁ e he, i₀]
    · rw [o₃'.2 _ (nob 2 (by decide) 3 (by decide) (by decide)), v₂ e he, i₁]
    · rw [v₃ e he, i₂]

end VG.Proof.Blowfish.AArch64
