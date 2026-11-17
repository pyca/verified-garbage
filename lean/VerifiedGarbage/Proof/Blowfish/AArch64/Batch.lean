module

public import VerifiedGarbage.Proof.Blowfish.Feistel
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Blowfish.AArch64.Exec
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Blowfish.Blocks
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Blowfish.F
public import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Impl.Blowfish.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.Lit

/-! ### `Blowfish.AArch64.Round`, which this module and modules that import it used -/

section

/-! ### `Blowfish.AArch64.Sbox`, which this module and modules that import it used -/

section

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
  obtain hbase : base + 64 ≤ 4096 := by simp only [base, planeOff]; omega_arith
  let ld (r : Nat) := s.mem.read (s.gpr sch + BitVec.ofNat 64 (base + 16 * r)) 16
  let s₁ := s.setV .v28 (ld 0)
  let s₂ := s₁.setV .v29 (ld 1)
  let s₃ := s₂.setV .v30 (ld 2)
  let s₄ := s₃.setV .v31 (ld 3)
  obtain hv : ∀ r < 4, s₄.v (tReg r) = ld r := by
    intro r hr
    rcases (by omega_arith : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;> rfl
  obtain hv' : ∀ x, (∀ r < 4, x ≠ tReg r) → s₄.v x = s.v x := by
    intro x hx
    obtain h0 : x ≠ .v28 := hx 0 (by decide)
    obtain h1 : x ≠ .v29 := hx 1 (by decide)
    obtain h2 : x ≠ .v30 := hx 2 (by decide)
    obtain h3 : x ≠ .v31 := hx 3 (by decide)
    simp only [s₄, s₃, s₂, s₁, v_setV_of_ne _ _ h0, v_setV_of_ne _ _ h1, v_setV_of_ne _ _ h2,
      v_setV_of_ne _ _ h3]
  let s₅ := s₄.setV d (ofVBytes fun i =>
      if (vbyte (s₄.v m) i).toNat < 16 * 4 then tableByte s₄.v (tReg 0) (vbyte (s₄.v m) i).toNat
      else if (q != 0) then vbyte (s₄.v d) i else 0)
  obtain rd : ∀ r < 4, InRegions (s.rd ++ s.wr) (s.gpr sch + BitVec.ofNat 64 (base + 16 * r)) 16 :=
    fun r hr => hR _ (by omega_arith)
  obtain ho : ∀ r < 4, (base + 16 * r) % 16 = 0 ∧ base + 16 * r < 65536 := fun r hr => by
    simp only [base, planeOff]; omega_arith
  refine ⟨s₅, ?_, ?_, ?_⟩
  · have e₁ : exec (.ldrq .v28 sch (planeOff j b + 64 * q + 16 * 0)) s = some s₁ :=
      exec_ldrq (ho 0 (by decide)) (rd 0 (by decide))
    obtain e₂ : exec (.ldrq .v29 sch (planeOff j b + 64 * q + 16 * 1)) s₁ = some s₂ :=
      exec_ldrq (ho 1 (by decide)) (rd 1 (by decide))
    obtain e₃ : exec (.ldrq .v30 sch (planeOff j b + 64 * q + 16 * 2)) s₂ = some s₃ :=
      exec_ldrq (ho 2 (by decide)) (rd 2 (by decide))
    obtain e₄ : exec (.ldrq .v31 sch (planeOff j b + 64 * q + 16 * 3)) s₃ = some s₄ :=
      exec_ldrq (ho 3 (by decide)) (rd 3 (by decide))
    obtain e₅ : exec (.vop (.tblN (q != 0) 4 d (tReg 0) m)) s₄ = some s₅ := exec_tbl4 _ _ _ _ _
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
  obtain q := VG.AArch64.Tbl.xor_quarter X hX
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
  obtain ne := regs_ne j hj b hb
  obtain hd : ∀ r < 4, outReg b ≠ tReg r := fun r hr => (ne 0 (by decide) r hr).1
  obtain hR' : ∀ {t : State}, VOnly [.v28, .v29, .v30, .v31, outReg b] s t → Readable t sch := by
    intro t ht off hoff
    rw [ht.rd, ht.wr, ht.gpr]; exact hR off hoff
  obtain ⟨s₁, r₁, v₁, o₁⟩ := quarter_run hR hj hb (by decide : 0 < 4) hd (fun r hr => (ne 0 (by decide) r hr).2.1)
  obtain ⟨s₂, r₂, v₂, o₂⟩ := quarter_run (hR' o₁) hj hb (by decide : 1 < 4) hd
    (fun r hr => (ne 1 (by decide) r hr).2.2.1)
  obtain o₁₂ := o₁.trans o₂
  obtain ⟨s₃, r₃, v₃, o₃⟩ := quarter_run (hR' o₁₂) hj hb (by decide : 2 < 4) hd
    (fun r hr => (ne 2 (by decide) r hr).2.2.1)
  obtain o₁₃ := o₁₂.trans o₃
  obtain ⟨s₄, r₄, v₄, o₄⟩ := quarter_run (hR' o₁₃) hj hb (by decide : 3 < 4) hd
    (fun r hr => (ne 3 (by decide) r hr).2.2.1)
  obtain o₁₄ := o₁₃.trans o₄
  refine ⟨s₄, ?_, ?_, o₁₄⟩
  · rw [lookupPlane_eq]
    exact VG.AArch64.Tbl.runBlock_cat_some r₁ (VG.AArch64.Tbl.runBlock_cat_some r₂
      (VG.AArch64.Tbl.runBlock_cat_some r₃ (VG.AArch64.Tbl.runBlock_cat_some r₄ runBlock_nil)))
  · intro e he
    -- the registers read are unchanged
    obtain kept : ∀ {t : State} (x : VReg), VOnly [.v28, .v29, .v30, .v31, outReg b] s t →
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
    obtain q₁ : s₁.v (qReg 1) = s.v (qReg 1) := kept _ o₁ (fun r hr => (ne 1 (by decide) r hr).2.2.1)
      (ne 1 (by decide) 0 (by decide)).2.2.2.2.1
    obtain q₂ : s₂.v (qReg 2) = s.v (qReg 2) := kept _ o₁₂ (fun r hr => (ne 2 (by decide) r hr).2.2.1)
      (ne 2 (by decide) 0 (by decide)).2.2.2.2.1
    obtain q₃ : s₃.v (qReg 3) = s.v (qReg 3) := kept _ o₁₃ (fun r hr => (ne 3 (by decide) r hr).2.2.1)
      (ne 3 (by decide) 0 (by decide)).2.2.2.2.1
    let X := vbyte (s.v (idxReg j)) e
    have hX : X.toNat < 256 := X.isLt
    obtain hxq : ∀ q < 4, 0 < q → (vbyte (s.v (qReg q)) e).toNat = X.toNat ^^^ 64 * q := by
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
  obtain hidx := idx_ne_q123 j hj
  let s₁ := s.setV (qReg 1) (s.v (idxReg j) ^^^ s.v c64)
  let s₂ := s₁.setV (qReg 2) (s₁.v (idxReg j) ^^^ s₁.v c128)
  let s₃ := s₂.setV (qReg 3) (s₂.v (qReg 1) ^^^ s₂.v c128)
  obtain X : s₃.v (idxReg j) = s.v (idxReg j) := by
    simp only [s₃, s₂, s₁, qReg, List.getD_cons_zero, List.getD_cons_succ, v_setV_of_ne _ _ hidx.1,
      v_setV_of_ne _ _ hidx.2.1, v_setV_of_ne _ _ hidx.2.2]
  obtain q1 : s₃.v (qReg 1) = s.v (idxReg j) ^^^ s.v c64 := by
    simp only [s₃, s₂, s₁, qReg, List.getD_cons_zero, List.getD_cons_succ, v_setV, reduceCtorEq,
      ite_true, ite_false]
  obtain q2 : s₃.v (qReg 2) = s.v (idxReg j) ^^^ s.v c128 := by
    simp only [s₃, s₂, s₁, qReg, List.getD_cons_zero, List.getD_cons_succ, v_setV, reduceCtorEq,
      ite_true, ite_false, c128, c64, hidx.1]
  obtain q3 : s₃.v (qReg 3) = s.v (idxReg j) ^^^ s.v c64 ^^^ s.v c128 := by
    simp only [s₃, s₂, s₁, qReg, List.getD_cons_zero, List.getD_cons_succ, v_setV, reduceCtorEq,
      ite_true, ite_false, c128, c64, hidx.1]
  obtain hq : ∀ q < 4, 0 < q → ∀ e < 16,
      vbyte (s₃.v (qReg q)) e = vbyte (s₃.v (idxReg j)) e ^^^ BitVec.ofNat 8 (64 * q) := by
    intro q hq0 hq1 e he
    rw [X]
    rcases (by omega_using [hq0, hq1] : q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl
    · rw [q1, vbyte_xor, hc.1 e he]; rfl
    · rw [q2, vbyte_xor, hc.2 e he]; rfl
    · rw [q3, vbyte_xor, vbyte_xor, hc.1 e he, hc.2 e he, BitVec.xor_assoc]; rfl
  obtain o₃ : VOnly lookupRegs s s₃ :=
    (((VOnly.setV s (by simp [lookupRegs, qReg]) _).trans (VOnly.setV _ (by simp [lookupRegs, qReg]) _)).trans
      (VOnly.setV _ (by simp [lookupRegs, qReg]) _))
  obtain hR₃ : ∀ {t : State}, VOnly lookupRegs s t → Readable t sch := by
    intro t ht off hoff
    rw [ht.rd, ht.wr, ht.gpr]; exact hR off hoff
  -- each plane keeps what the others read and wrote
  obtain step : ∀ {t : State} (b : Nat), b < 4 → VOnly lookupRegs s t →
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
  obtain hqk : ∀ {t t' : State} (b : Nat), b < 4 → VOnly [.v28, .v29, .v30, .v31, outReg b] t t' →
      (∀ q < 4, 0 < q → ∀ e < 16,
        vbyte (t.v (qReg q)) e = vbyte (t.v (idxReg j)) e ^^^ BitVec.ofNat 8 (64 * q)) →
      (∀ q < 4, 0 < q → ∀ e < 16,
        vbyte (t'.v (qReg q)) e = vbyte (t'.v (idxReg j)) e ^^^ BitVec.ofNat 8 (64 * q)) := by
    intro t t' b hb o h q hq0 hq1 e he
    rw [o.2 _ (q_notin q hq0 hq1 b hb), o.2 _ (idx_notin j hj b hb)]; exact h q hq0 hq1 e he
  obtain ni := idx_notin j hj
  obtain ⟨t₀, r₀, v₀, o₀⟩ := step 0 (by decide) o₃ hq
  obtain p₀ := o₃.trans (VOnly.mono o₀ (ob 0 (by decide)))
  obtain ⟨t₁, r₁, v₁, o₁⟩ := step 1 (by decide) p₀ (hqk 0 (by decide) o₀ hq)
  obtain p₁ := p₀.trans (VOnly.mono o₁ (ob 1 (by decide)))
  obtain ⟨t₂, r₂, v₂, o₂⟩ := step 2 (by decide) p₁ (hqk 1 (by decide) o₁ (hqk 0 (by decide) o₀ hq))
  obtain p₂ := p₁.trans (VOnly.mono o₂ (ob 2 (by decide)))
  obtain ⟨t₃, r₃, v₃, o₃'⟩ := step 3 (by decide) p₂
    (hqk 2 (by decide) o₂ (hqk 1 (by decide) o₁ (hqk 0 (by decide) o₀ hq)))
  obtain p₃ := p₂.trans (VOnly.mono o₃' (ob 3 (by decide)))
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
    obtain i₀ : t₀.v (idxReg j) = s.v (idxReg j) := (o₀.2 _ (ni 0 (by decide))).trans X
    obtain i₁ : t₁.v (idxReg j) = s.v (idxReg j) := (o₁.2 _ (ni 1 (by decide))).trans i₀
    obtain i₂ : t₂.v (idxReg j) = s.v (idxReg j) := (o₂.2 _ (ni 2 (by decide))).trans i₁
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

end

end

/-! ### `Blowfish.AArch64.F`, which only this module used -/

section

/-! ### `Blowfish.AArch64.Planes`, which only this module used -/

section

/-! ### `Blowfish.AArch64.Transpose`, which only this module used -/

section

/-!
# Words to byte planes and back

`uzp_uzp`: two levels of `uzp1`/`uzp2` (as in `planes`) leave in byte `n`
of the result byte `o₁ + 2 o₂` of word `n` of four vectors (`o₁`, `o₂` 0 for
`uzp1` and 1 for `uzp2`). `zip_zip`: two levels of `zip1`/`zip2` (as in
`words`) turn four byte planes back into sixteen words.
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64

/-- `uzp1` (`o = 0`) or `uzp2` (`o = 1`). -/
def uzp (o : Nat) : VPermOp := if o = 0 then .uzp1 else .uzp2

theorem vbyte_uzp (o : Nat) (ho : o < 2) (x y : BitVec 128) {e : Nat} (he : e < 16) :
    vbyte (VPermOp.eval (uzp o) .b16 x y) e =
      if e < 8 then vbyte x (2 * e + o) else vbyte y (2 * e + o - 16) := by
  rcases (by omega_using [ho] : o = 0 ∨ o = 1) with rfl | rfl
  · exact vbyte_uzp1 x y he
  · exact vbyte_uzp2 x y he

/-- Word `k` of four vectors. -/
def four (W0 W1 W2 W3 : BitVec 128) (k : Nat) : BitVec 128 := [W0, W1, W2, W3].getD k 0

theorem uzp_uzp (W0 W1 W2 W3 : BitVec 128) {o₁ o₂ : Nat} (h₁ : o₁ < 2) (h₂ : o₂ < 2) {n : Nat}
    (hn : n < 16) :
    vbyte (VPermOp.eval (uzp o₂) .b16 (VPermOp.eval (uzp o₁) .b16 W0 W1)
        (VPermOp.eval (uzp o₁) .b16 W2 W3)) n =
      vbyte (four W0 W1 W2 W3 (n / 4)) (4 * (n % 4) + (o₁ + 2 * o₂)) := by
  rw [vbyte_uzp _ h₂ _ _ hn]
  split
  · rw [vbyte_uzp _ h₁ _ _ (by omega_arith)]
    split
    · rw [show n / 4 = 0 by omega_arith]; exact congrArg _ (by omega_arith)
    · rw [show n / 4 = 1 by omega_arith]; exact congrArg _ (by omega_arith)
  · rw [vbyte_uzp _ h₁ _ _ (by omega_using [h₂, hn])]
    split
    · rw [show n / 4 = 2 by omega_arith]; exact congrArg _ (by omega_arith)
    · rw [show n / 4 = 3 by omega_arith]; exact congrArg _ (by omega_arith)

/-- `zip1` (`o = 0`) or `zip2` (`o = 1`). -/
def zip (o : Nat) : VPermOp := if o = 0 then .zip1 else .zip2

theorem vbyte_zip (o : Nat) (ho : o < 2) (x y : BitVec 128) {e : Nat} (he : e < 16) :
    vbyte (VPermOp.eval (zip o) .b16 x y) e =
      if e % 2 = 0 then vbyte x (8 * o + e / 2) else vbyte y (8 * o + e / 2) := by
  rcases (by omega_using [ho] : o = 0 ∨ o = 1) with rfl | rfl
  · rw [show zip 0 = .zip1 from rfl, vbyte_zip1 x y he]; simp
  · exact vbyte_zip2 x y he

/-- Byte `b` of word `l` of `zip o₂ (zip o₁ P0 P2) (zip o₁ P1 P3)` is byte
`4 (2 o₁ + o₂) + l` of plane `b`: word `4 k + l` with `k = 2 o₁ + o₂`. -/
theorem zip_zip (P0 P1 P2 P3 : BitVec 128) {o₁ o₂ : Nat} (h₁ : o₁ < 2) (h₂ : o₂ < 2) {l b : Nat}
    (hl : l < 4) (hb : b < 4) :
    vbyte (VPermOp.eval (zip o₂) .b16 (VPermOp.eval (zip o₁) .b16 P0 P2)
        (VPermOp.eval (zip o₁) .b16 P1 P3)) (4 * l + b) =
      vbyte (four P0 P1 P2 P3 b) (4 * (2 * o₁ + o₂) + l) := by
  rw [vbyte_zip _ h₂ _ _ (by omega_using [hl, hb])]
  split
  · rw [vbyte_zip _ h₁ _ _ (by omega_using [h₂, hl, hb])]
    split
    · rw [show b = 0 by omega_arith]; exact congrArg _ (by omega_using [])
    · rw [show b = 2 by omega_arith]; exact congrArg _ (by omega_using [])
  · rw [vbyte_zip _ h₁ _ _ (by omega_using [h₂, hl, hb])]
    split
    · rw [show b = 1 by omega_arith]; exact congrArg _ (by omega_using [])
    · rw [show b = 3 by omega_arith]; exact congrArg _ (by omega_using [])

end VG.Proof.Blowfish.AArch64

end

end


/-!
# Byte planes in and out, and the accumulation of F

`planes_run`: `planes L` leaves in `idxReg j` byte `3 - j` of each word of
`L`. `words_run`: `words` turns the byte planes in `outReg` into words.
`combine_run`: `combine j` accumulates them into `fReg`.
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64
open VG.AArch64.Tbl (VOnly)

/-- The registers `planes` writes. -/
def planesRegs : List VReg := [.v0, .v1, .v20, .v21, .v16, .v17, .v18, .v19]

theorem four_regs (v : VReg → BitVec 128) (L : Nat → VReg) {k : Nat} (hk : k < 4) :
    four (v (L 0)) (v (L 1)) (v (L 2)) (v (L 3)) k = v (L k) := by
  rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem planes_run (s : State) (L : Nat → VReg) (hL : ∀ k < 4, L k ∉ planesRegs) :
    ∃ s', runBlock isa (planes L) s = some s' ∧
      (∀ j < 4, ∀ n < 16, vbyte (s'.v (idxReg j)) n = vbyte (s.v (L (n / 4))) (4 * (n % 4) + (3 - j))) ∧
      VOnly planesRegs s s' := by
  obtain h0 := hL 0 (by decide); have h1 := hL 1 (by decide)
  obtain h2 := hL 2 (by decide); have h3 := hL 3 (by decide)
  simp only [planesRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at h0 h1 h2 h3
  let p (o : Nat) (t : State) (d n m : VReg) := t.setV d (VPermOp.eval (uzp o) .b16 (t.v n) (t.v m))
  let s₁ := p 0 s .v0 (L 0) (L 1)
  let s₂ := p 1 s₁ .v1 (L 0) (L 1)
  let s₃ := p 0 s₂ .v20 (L 2) (L 3)
  let s₄ := p 1 s₃ .v21 (L 2) (L 3)
  let s₅ := p 0 s₄ .v19 .v0 .v20
  let s₆ := p 1 s₅ .v17 .v0 .v20
  let s₇ := p 0 s₆ .v18 .v1 .v21
  let s₈ := p 1 s₇ .v16 .v1 .v21
  refine ⟨s₈, ?_, ?_, ?_⟩
  · have e₁ : exec (vperm .uzp1 .b16 .v0 (L 0) (L 1)) s = some s₁ := rfl
    have e₂ : exec (vperm .uzp2 .b16 .v1 (L 0) (L 1)) s₁ = some s₂ := rfl
    have e₃ : exec (vperm .uzp1 .b16 (outReg 0) (L 2) (L 3)) s₂ = some s₃ := rfl
    have e₄ : exec (vperm .uzp2 .b16 (outReg 1) (L 2) (L 3)) s₃ = some s₄ := rfl
    have e₅ : exec (vperm .uzp1 .b16 (idxReg 3) .v0 (outReg 0)) s₄ = some s₅ := rfl
    have e₆ : exec (vperm .uzp2 .b16 (idxReg 1) .v0 (outReg 0)) s₅ = some s₆ := rfl
    have e₇ : exec (vperm .uzp1 .b16 (idxReg 2) .v1 (outReg 1)) s₆ = some s₇ := rfl
    have e₈ : exec (vperm .uzp2 .b16 (idxReg 0) .v1 (outReg 1)) s₇ = some s₈ := rfl
    rw [planes, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_cons, e₄, runStep_some, runBlock_cons, e₅, runStep_some, runBlock_cons,
      e₆, runStep_some, runBlock_cons, e₇, runStep_some, runBlock_cons, e₈, runStep_some, runBlock_nil]
  · have hne : ∀ k < 4, L k ≠ .v0 ∧ L k ≠ .v1 ∧ L k ≠ .v20 ∧ L k ≠ .v21 := fun k hk => by
      have := hL k hk
      simp only [planesRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at this
      exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩
    obtain r1 : s₄.v .v0 = VPermOp.eval (uzp 0) .b16 (s.v (L 0)) (s.v (L 1)) ∧
        s₄.v .v1 = VPermOp.eval (uzp 1) .b16 (s.v (L 0)) (s.v (L 1)) ∧
        s₄.v .v20 = VPermOp.eval (uzp 0) .b16 (s.v (L 2)) (s.v (L 3)) ∧
        s₄.v .v21 = VPermOp.eval (uzp 1) .b16 (s.v (L 2)) (s.v (L 3)) := by
      simp only [s₄, s₃, s₂, s₁, p, v_setV, reduceCtorEq, ite_true, ite_false, h0, h1, h2, h3,
        and_self]
    obtain i0 : s₈.v .v16 = VPermOp.eval (uzp 1) .b16 (s₄.v .v1) (s₄.v .v21) := by
      simp only [s₈, s₇, s₆, s₅, p, v_setV, reduceCtorEq, ite_true, ite_false]
    obtain i1 : s₈.v .v17 = VPermOp.eval (uzp 1) .b16 (s₄.v .v0) (s₄.v .v20) := by
      simp only [s₈, s₇, s₆, s₅, p, v_setV, reduceCtorEq, ite_true, ite_false]
    obtain i2 : s₈.v .v18 = VPermOp.eval (uzp 0) .b16 (s₄.v .v1) (s₄.v .v21) := by
      simp only [s₈, s₇, s₆, s₅, p, v_setV, reduceCtorEq, ite_true, ite_false]
    obtain i3 : s₈.v .v19 = VPermOp.eval (uzp 0) .b16 (s₄.v .v0) (s₄.v .v20) := by
      simp only [s₈, s₇, s₆, s₅, p, v_setV, reduceCtorEq, ite_true, ite_false]
    simp only [r1.1, r1.2.1, r1.2.2.1, r1.2.2.2] at i0 i1 i2 i3
    intro j hj n hn
    obtain key : ∀ (o₁ : Nat), o₁ < 2 → ∀ (o₂ : Nat), o₂ < 2 → ∀ x : BitVec 128, x = VPermOp.eval (uzp o₂) .b16
        (VPermOp.eval (uzp o₁) .b16 (s.v (L 0)) (s.v (L 1)))
        (VPermOp.eval (uzp o₁) .b16 (s.v (L 2)) (s.v (L 3))) →
        vbyte x n = vbyte (s.v (L (n / 4))) (4 * (n % 4) + (o₁ + 2 * o₂)) := by
      intro o₁ h₁ o₂ h₂ x e
      rw [e, uzp_uzp _ _ _ _ h₁ h₂ hn, four_regs _ _ (by omega_using [hn])]
    rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · exact key 1 (by decide) 1 (by decide) _ i0
    · exact key 0 (by decide) 1 (by decide) _ i1
    · exact key 1 (by decide) 0 (by decide) _ i2
    · exact key 0 (by decide) 0 (by decide) _ i3
  · exact (((((((VOnly.setV s (by simp [planesRegs]) _).trans (VOnly.setV _ (by simp [planesRegs]) _)).trans
      (VOnly.setV _ (by simp [planesRegs]) _)).trans (VOnly.setV _ (by simp [planesRegs]) _)).trans
      (VOnly.setV _ (by simp [planesRegs]) _)).trans (VOnly.setV _ (by simp [planesRegs]) _)).trans
      (VOnly.setV _ (by simp [planesRegs]) _)).trans (VOnly.setV _ (by simp [planesRegs]) _)

/-! ## Back to words -/

/-- The registers `words` writes. -/
def wordsRegs : List VReg := [.v0, .v1, .v20, .v21, .v22, .v23]

theorem words_run (s : State) :
    ∃ s', runBlock isa words s = some s' ∧
      (∀ k < 4, ∀ l < 4, ∀ b < 4, vbyte (s'.v (wordReg k)) (4 * l + b) = vbyte (s.v (outReg b)) (4 * k + l)) ∧
      VOnly wordsRegs s s' := by
  let p (o : Nat) (t : State) (d n m : VReg) := t.setV d (VPermOp.eval (zip o) .b16 (t.v n) (t.v m))
  let s₁ := p 0 s .v0 .v20 .v22
  let s₂ := p 1 s₁ .v1 .v20 .v22
  let s₃ := p 0 s₂ .v20 .v21 .v23
  let s₄ := p 1 s₃ .v22 .v21 .v23
  let s₅ := p 0 s₄ .v21 .v0 .v20
  let s₆ := p 1 s₅ .v23 .v0 .v20
  let s₇ := p 0 s₆ .v0 .v1 .v22
  let s₈ := p 1 s₇ .v1 .v1 .v22
  refine ⟨s₈, ?_, ?_, ?_⟩
  · have e₁ : exec (vperm .zip1 .b16 .v0 (outReg 0) (outReg 2)) s = some s₁ := rfl
    have e₂ : exec (vperm .zip2 .b16 .v1 (outReg 0) (outReg 2)) s₁ = some s₂ := rfl
    have e₃ : exec (vperm .zip1 .b16 (outReg 0) (outReg 1) (outReg 3)) s₂ = some s₃ := rfl
    have e₄ : exec (vperm .zip2 .b16 (outReg 2) (outReg 1) (outReg 3)) s₃ = some s₄ := rfl
    have e₅ : exec (vperm .zip1 .b16 (outReg 1) .v0 (outReg 0)) s₄ = some s₅ := rfl
    have e₆ : exec (vperm .zip2 .b16 (outReg 3) .v0 (outReg 0)) s₅ = some s₆ := rfl
    have e₇ : exec (vperm .zip1 .b16 .v0 .v1 (outReg 2)) s₆ = some s₇ := rfl
    have e₈ : exec (vperm .zip2 .b16 .v1 .v1 (outReg 2)) s₇ = some s₈ := rfl
    rw [words, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_cons, e₄, runStep_some, runBlock_cons, e₅, runStep_some, runBlock_cons,
      e₆, runStep_some, runBlock_cons, e₇, runStep_some, runBlock_cons, e₈, runStep_some, runBlock_nil]
  · let P := fun b => s.v (outReg b)
    obtain r : s₄.v .v0 = VPermOp.eval (zip 0) .b16 (P 0) (P 2) ∧
        s₄.v .v1 = VPermOp.eval (zip 1) .b16 (P 0) (P 2) ∧
        s₄.v .v20 = VPermOp.eval (zip 0) .b16 (P 1) (P 3) ∧
        s₄.v .v22 = VPermOp.eval (zip 1) .b16 (P 1) (P 3) := by
      simp only [s₄, s₃, s₂, s₁, p, P, v_setV, reduceCtorEq, ite_true, ite_false, outReg,
        List.getD_cons_zero, List.getD_cons_succ, and_self]
    obtain w0 : s₈.v (wordReg 0) = VPermOp.eval (zip 0) .b16 (s₄.v .v0) (s₄.v .v20) := by
      simp only [s₈, s₇, s₆, s₅, p, wordReg, outReg, List.getD_cons_zero, List.getD_cons_succ, v_setV,
        reduceCtorEq, ite_true, ite_false]
    obtain w1 : s₈.v (wordReg 1) = VPermOp.eval (zip 1) .b16 (s₄.v .v0) (s₄.v .v20) := by
      simp only [s₈, s₇, s₆, s₅, p, wordReg, outReg, List.getD_cons_zero, List.getD_cons_succ, v_setV,
        reduceCtorEq, ite_true, ite_false]
    obtain w2 : s₈.v (wordReg 2) = VPermOp.eval (zip 0) .b16 (s₄.v .v1) (s₄.v .v22) := by
      simp only [s₈, s₇, s₆, s₅, p, wordReg, outReg, List.getD_cons_zero, List.getD_cons_succ, v_setV,
        reduceCtorEq, ite_true, ite_false]
    obtain w3 : s₈.v (wordReg 3) = VPermOp.eval (zip 1) .b16 (s₄.v .v1) (s₄.v .v22) := by
      simp only [s₈, s₇, s₆, s₅, p, wordReg, outReg, List.getD_cons_zero, List.getD_cons_succ, v_setV,
        reduceCtorEq, ite_true, ite_false]
    simp only [r.1, r.2.1, r.2.2.1, r.2.2.2] at w0 w1 w2 w3
    obtain fourP : ∀ b < 4, four (P 0) (P 1) (P 2) (P 3) b = s.v (outReg b) := fun b hb =>
      four_regs s.v outReg hb
    intro k hk l hl b hb
    rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · rw [w0, zip_zip _ _ _ _ (by decide) (by decide) hl hb, fourP b hb]
    · rw [w1, zip_zip _ _ _ _ (by decide) (by decide) hl hb, fourP b hb]
    · rw [w2, zip_zip _ _ _ _ (by decide) (by decide) hl hb, fourP b hb]
    · rw [w3, zip_zip _ _ _ _ (by decide) (by decide) hl hb, fourP b hb]
  · exact (((((((VOnly.setV s (by simp [wordsRegs]) _).trans (VOnly.setV _ (by simp [wordsRegs]) _)).trans
      (VOnly.setV _ (by simp [wordsRegs]) _)).trans (VOnly.setV _ (by simp [wordsRegs]) _)).trans
      (VOnly.setV _ (by simp [wordsRegs]) _)).trans (VOnly.setV _ (by simp [wordsRegs]) _)).trans
      (VOnly.setV _ (by simp [wordsRegs]) _)).trans (VOnly.setV _ (by simp [wordsRegs]) _)

end VG.Proof.Blowfish.AArch64

end

end


/-!
# F on sixteen words

`f_run`: from the byte planes of sixteen words `x n` in `idxReg` (`planes`),
`f sch` leaves `F(x n)` in word `n % 4` of `fReg (n / 4)`, under the
schedule at `sch`.
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.AArch64.Tbl (VOnly)

/-- What `combine j` does to a register of F and a register of words. -/
def cop (j : Nat) (x y : BitVec 128) : BitVec 128 :=
  if j = 0 then y else if j = 2 then x ^^^ y else VArr.s4.map2 (fun _ a b => a + b) x y

theorem vword_cop (j : Nat) (x y : BitVec 128) {l : Nat} (hl : l < 4) :
    vword (cop j x y) l =
      if j = 0 then vword y l else if j = 2 then vword x l ^^^ vword y l else vword x l + vword y l := by
  simp only [cop]
  split
  · rfl
  · split
    · exact vword_xor x y l
    · exact vword_map2 _ x y hl

theorem exec_combine (s : State) (j : Nat) {k : Nat} (hk : k < 4) :
    exec ((combine j).getD k (.vop (.movi0 .v0))) s =
      some (s.setV (fReg k) (cop j (s.v (fReg k)) (s.v (wordReg k)))) := by
  simp only [combine, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
    Option.map_some, Option.getD_some, cop]
  split
  · rfl
  · split <;> rfl

def fRegs : List VReg := [.v12, .v13, .v14, .v15]

theorem wordReg_ne_fReg : ∀ k < 4, ∀ k' < 4, wordReg k ≠ fReg k' := by decide
theorem fReg_ne : ∀ k < 4, ∀ k' < 4, k ≠ k' → fReg k ≠ fReg k' := by decide

theorem combine_run (s : State) (j : Nat) :
    ∃ s', runBlock isa (combine j) s = some s' ∧
      (∀ k < 4, s'.v (fReg k) = cop j (s.v (fReg k)) (s.v (wordReg k))) ∧ VOnly fRegs s s' := by
  let t (k : Nat) (u : State) := u.setV (fReg k) (cop j (u.v (fReg k)) (u.v (wordReg k)))
  let s₁ := t 0 s
  let s₂ := t 1 s₁
  let s₃ := t 2 s₂
  let s₄ := t 3 s₃
  obtain e : ∀ (k : Nat) (u : State), k < 4 →
      exec ((combine j).getD k (.vop (.movi0 .v0))) u = some (t k u) := fun k u hk => by
    rw [exec_combine _ _ hk]
  obtain hl : combine j = [(combine j).getD 0 (.vop (.movi0 .v0)), (combine j).getD 1 (.vop (.movi0 .v0)),
      (combine j).getD 2 (.vop (.movi0 .v0)), (combine j).getD 3 (.vop (.movi0 .v0))] := by
    simp only [combine, List.getD_eq_getElem?_getD]; rfl
  refine ⟨s₄, ?_, ?_, ?_⟩
  · rw [hl, runBlock_cons, e 0 s (by decide), runStep_some, runBlock_cons, e 1 s₁ (by decide),
      runStep_some, runBlock_cons, e 2 s₂ (by decide), runStep_some, runBlock_cons,
      e 3 s₃ (by decide), runStep_some, runBlock_nil]
  · have wk : ∀ k < 4, ∀ (u : State) (k' : Nat), k' < 4 → (t k' u).v (wordReg k) = u.v (wordReg k) :=
      fun k hk u k' hk' => v_setV_of_ne _ _ (wordReg_ne_fReg k hk k' hk')
    obtain fk : ∀ k < 4, ∀ (u : State) (k' : Nat), k' < 4 → k ≠ k' → (t k' u).v (fReg k) = u.v (fReg k) :=
      fun k hk u k' hk' hne => v_setV_of_ne _ _ (fReg_ne k hk k' hk' hne)
    intro k hk
    rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · rw [fk 0 (by decide) _ 3 (by decide) (by decide), fk 0 (by decide) _ 2 (by decide) (by decide),
        fk 0 (by decide) _ 1 (by decide) (by decide)]
      exact v_setV_self _ _ _
    · rw [fk 1 (by decide) _ 3 (by decide) (by decide), fk 1 (by decide) _ 2 (by decide) (by decide)]
      show (s₁.setV _ _).v _ = _
      rw [v_setV_self, fk 1 (by decide) _ 0 (by decide) (by decide), wk 1 (by decide) _ 0 (by decide)]
    · rw [fk 2 (by decide) _ 3 (by decide) (by decide)]
      show (s₂.setV _ _).v _ = _
      rw [v_setV_self, fk 2 (by decide) _ 1 (by decide) (by decide), fk 2 (by decide) _ 0 (by decide) (by decide),
        wk 2 (by decide) _ 1 (by decide), wk 2 (by decide) _ 0 (by decide)]
    · show (s₃.setV _ _).v _ = _
      rw [v_setV_self, fk 3 (by decide) _ 2 (by decide) (by decide), fk 3 (by decide) _ 1 (by decide) (by decide),
        fk 3 (by decide) _ 0 (by decide) (by decide), wk 3 (by decide) _ 2 (by decide),
        wk 3 (by decide) _ 1 (by decide), wk 3 (by decide) _ 0 (by decide)]
  · exact (((VOnly.setV s (by simp [fRegs, fReg]) _).trans (VOnly.setV _ (by simp [fRegs, fReg]) _)).trans
      (VOnly.setV _ (by simp [fRegs, fReg]) _)).trans (VOnly.setV _ (by simp [fRegs, fReg]) _)

/-! ## One S-box of F -/

/-- Word `n` of sixteen in the registers `R`. -/
def lane (v : VReg → BitVec 128) (R : Nat → VReg) (n : Nat) : Word := vword (v (R (n / 4))) (n % 4)

def stepRegs : List VReg := lookupRegs ++ wordsRegs ++ fRegs

theorem fReg_notin : ∀ k < 4, fReg k ∉ lookupRegs ∧ fReg k ∉ wordsRegs := by decide

theorem sbox_run {s : State} {sch : Reg} (hR : Readable s sch) (hc : Consts s) {j : Nat} (hj : j < 4)
    (x : Nat → Word) (hx : ∀ n < 16, vbyte (s.v (idxReg j)) n = quarter (x n) j)
    (hprev : 0 < j → ∀ n < 16, lane s.v fReg n = fAcc (scheduleAt s.mem (s.gpr sch)) (x n) (j - 1)) :
    ∃ s', runBlock isa (lookup sch j ++ words ++ combine j) s = some s' ∧
      (∀ n < 16, lane s'.v fReg n = fAcc (scheduleAt s.mem (s.gpr sch)) (x n) j) ∧
      VOnly stepRegs s s' := by
  let K := scheduleAt s.mem (s.gpr sch)
  obtain ⟨s₁, r₁, v₁, o₁⟩ := lookup_run hR hc hj
  obtain ⟨s₂, r₂, v₂, o₂⟩ := words_run s₁
  obtain ⟨s₃, r₃, v₃, o₃⟩ := combine_run s₂ j
  refine ⟨s₃, VG.AArch64.Tbl.runBlock_cat_some (VG.AArch64.Tbl.runBlock_cat_some r₁ r₂) r₃, ?_, ?_⟩
  · intro n hn
    obtain hk : n / 4 < 4 := by omega_using [hn]
    obtain hl : n % 4 < 4 := by omega_using []
    -- the words of S-box `j`
    obtain w : vword (s₂.v (wordReg (n / 4))) (n % 4) = sq K (x n) j := by
      refine word_ext fun b hb => ?_
      rw [← vbyte_word _ hb, v₂ _ hk _ hl _ hb, show 4 * (n / 4) + n % 4 = n by omega_using [], v₁ _ hb _ hn, hx n hn,
        sq, sEntry_byte _ _ hj hb]
      rfl
    obtain f₂ : s₂.v (fReg (n / 4)) = s.v (fReg (n / 4)) := by
      rw [o₂.2 _ (fReg_notin _ hk).2, o₁.2 _ (fReg_notin _ hk).1]
    simp only [lane]
    rw [v₃ _ hk, vword_cop _ _ _ hl, w, f₂]
    exact fAcc_step K (x n) hj _ fun h => hprev h n hn
  · exact ((VOnly.mono o₁ (by decide)).trans (VOnly.mono o₂ (by decide))).trans (VOnly.mono o₃ (by decide))

theorem idx_notin_step : ∀ j < 4, idxReg j ∉ stepRegs := by decide
theorem const_notin_step : c64 ∉ stepRegs ∧ c128 ∉ stepRegs := by decide

theorem f_eq (sch : Reg) :
    f sch = (lookup sch 0 ++ words ++ combine 0) ++ ((lookup sch 1 ++ words ++ combine 1) ++
      ((lookup sch 2 ++ words ++ combine 2) ++ ((lookup sch 3 ++ words ++ combine 3) ++ []))) := rfl

/-- F of sixteen words whose byte planes are in `idxReg`. -/
theorem f_run {s : State} {sch : Reg} (hR : Readable s sch) (hc : Consts s) (x : Nat → Word)
    (hx : ∀ j < 4, ∀ n < 16, vbyte (s.v (idxReg j)) n = quarter (x n) j) :
    ∃ s', runBlock isa (f sch) s = some s' ∧
      (∀ n < 16, lane s'.v fReg n = Spec.Blowfish.f (scheduleAt s.mem (s.gpr sch)) (x n)) ∧
      VOnly stepRegs s s' := by
  obtain keep : ∀ {t : State}, VOnly stepRegs s t →
      Readable t sch ∧ Consts t ∧ (∀ j < 4, ∀ n < 16, vbyte (t.v (idxReg j)) n = quarter (x n) j) ∧
        t.mem = s.mem ∧ t.gpr = s.gpr := by
    intro t ht
    refine ⟨fun off hoff => ?_, ⟨fun e he => ?_, fun e he => ?_⟩, fun j hj n hn => ?_, ht.mem, ht.gpr⟩
    · rw [ht.rd, ht.wr, ht.gpr]; exact hR off hoff
    · rw [ht.2 _ const_notin_step.1]; exact hc.1 e he
    · rw [ht.2 _ const_notin_step.2]; exact hc.2 e he
    · rw [ht.2 _ (idx_notin_step j hj)]; exact hx j hj n hn
  obtain ⟨s₀, r₀, v₀, o₀⟩ := sbox_run hR hc (by decide : 0 < 4) x (hx 0 (by decide)) (by intro h; omega)
  obtain k₀ := keep o₀
  obtain ⟨s₁, r₁, v₁, o₁⟩ := sbox_run k₀.1 k₀.2.1 (by decide : 1 < 4) x (k₀.2.2.1 1 (by decide))
    (fun _ n hn => by rw [v₀ n hn, k₀.2.2.2.1, k₀.2.2.2.2])
  obtain p₁ := o₀.trans o₁
  obtain k₁ := keep p₁
  obtain ⟨s₂, r₂, v₂, o₂⟩ := sbox_run k₁.1 k₁.2.1 (by decide : 2 < 4) x (k₁.2.2.1 2 (by decide))
    (fun _ n hn => by rw [v₁ n hn, k₀.2.2.2.1, k₀.2.2.2.2, k₁.2.2.2.1, k₁.2.2.2.2])
  obtain p₂ := p₁.trans o₂
  obtain k₂ := keep p₂
  obtain ⟨s₃, r₃, v₃, o₃⟩ := sbox_run k₂.1 k₂.2.1 (by decide : 3 < 4) x (k₂.2.2.1 3 (by decide))
    (fun _ n hn => by rw [v₂ n hn, k₁.2.2.2.1, k₁.2.2.2.2, k₂.2.2.2.1, k₂.2.2.2.2])
  obtain p₃ := p₂.trans o₃
  refine ⟨s₃, ?_, fun n hn => ?_, p₃⟩
  · rw [f_eq]
    exact VG.AArch64.Tbl.runBlock_cat_some r₀ (VG.AArch64.Tbl.runBlock_cat_some r₁
      (VG.AArch64.Tbl.runBlock_cat_some r₂ (VG.AArch64.Tbl.runBlock_cat_some r₃ runBlock_nil)))
  · rw [v₃ n hn, k₂.2.2.2.1, k₂.2.2.2.2, fAcc_three]

end VG.Proof.Blowfish.AArch64

end

end


/-!
# One round on sixteen blocks

`round_run`: `round sch up L R`, with `x5` at Pᵢ₊₁ in the schedule at `sch`,
leaves `L ^ Pᵢ₊₁` in `L` and `R ^ F(L ^ Pᵢ₊₁)` in `R`, word by word, and
moves `x5` to the next entry (`up`) or the previous one.
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.AArch64.Tbl (VOnly)

/-- Only the general-purpose registers `gs` and the vector registers `vs` change. -/
structure Only (gs : List Reg) (vs : List VReg) (s s' : State) : Prop where
  eq : s' = { s with gpr := s'.gpr, v := s'.v }
  g : ∀ r, r ∉ gs → s'.gpr r = s.gpr r
  v : ∀ r, r ∉ vs → s'.v r = s.v r

theorem Only.trans {gs : List Reg} {vs : List VReg} {a b c : State} (h₁ : Only gs vs a b) (h₂ : Only gs vs b c) :
    Only gs vs a c := by
  refine ⟨?_, fun r hr => (h₂.g r hr).trans (h₁.g r hr), fun r hr => (h₂.v r hr).trans (h₁.v r hr)⟩
  rw [h₂.eq, h₁.eq]

theorem Only.mono {gs gs' : List Reg} {vs vs' : List VReg} {a b : State} (h : Only gs vs a b)
    (hg : ∀ r ∈ gs, r ∈ gs') (hv : ∀ r ∈ vs, r ∈ vs') : Only gs' vs' a b :=
  ⟨h.eq, fun r hr => h.g r fun h' => hr (hg r h'), fun r hr => h.v r fun h' => hr (hv r h')⟩

theorem Only.ofV {vs : List VReg} {a b : State} (h : VOnly vs a b) : Only [] vs a b := by
  refine ⟨?_, fun r _ => ?_, h.2⟩
  · rw [h.1]
  · rw [h.1]

theorem Only.mem {gs : List Reg} {vs : List VReg} {a b : State} (h : Only gs vs a b) : b.mem = a.mem := by
  rw [h.eq]
theorem Only.rd {gs : List Reg} {vs : List VReg} {a b : State} (h : Only gs vs a b) : b.rd = a.rd := by
  rw [h.eq]
theorem Only.wr {gs : List Reg} {vs : List VReg} {a b : State} (h : Only gs vs a b) : b.wr = a.wr := by
  rw [h.eq]
theorem Only.sp {gs : List Reg} {vs : List VReg} {a b : State} (h : Only gs vs a b) : b.sp = a.sp := by
  rw [h.eq]

/-- The schedule at `sch` is readable. -/
def SchedIn (s : State) (sch : Reg) : Prop :=
  ∀ off n, off + n ≤ 4168 → InRegions (s.rd ++ s.wr) (s.gpr sch + BitVec.ofNat 64 off) n

theorem SchedIn.readable {s : State} {sch : Reg} (h : SchedIn s sch) : Readable s sch :=
  fun off hoff => h off 16 (by omega_using [hoff])

/-- The registers of the halves. -/
def halfRegs : List VReg := [.v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11]

/-- What a round writes: `v0` and the registers of `planes` and `f`, and the halves. -/
def roundRegs : List VReg := .v0 :: planesRegs ++ stepRegs ++ halfRegs

/-- Halves `L` and `R`: `A` and `B` (`v4`–`v11`), in either role. -/
structure Halves (L R : Nat → VReg) : Prop where
  inL : ∀ k < 4, L k ∈ halfRegs
  inR : ∀ k < 4, R k ∈ halfRegs
  injL : ∀ k < 4, ∀ k' < 4, k ≠ k' → L k ≠ L k'
  injR : ∀ k < 4, ∀ k' < 4, k ≠ k' → R k ≠ R k'
  ne : ∀ k < 4, ∀ k' < 4, L k ≠ R k'

theorem halves_ab : Halves aReg bReg := ⟨by decide, by decide, by decide, by decide, by decide⟩
theorem halves_ba : Halves bReg aReg := ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem half_notin : ∀ r ∈ halfRegs, r ∉ planesRegs ∧ r ∉ stepRegs ∧ r ≠ .v0 := by decide

/-- XOR of a register with `v0`, for each of the four registers of a half `H`. -/
def xorHalf (H : Nat → VReg) (S : Nat → VReg) : List Instr :=
  (List.range 4).map fun k => veor (H k) (H k) (S k)

theorem xorHalf_run (s : State) {H S : Nat → VReg} (hinj : ∀ k < 4, ∀ k' < 4, k ≠ k' → H k ≠ H k')
    (hS : ∀ k < 4, ∀ k' < 4, S k ≠ H k') :
    ∃ s', runBlock isa (xorHalf H S) s = some s' ∧
      (∀ k < 4, s'.v (H k) = s.v (H k) ^^^ s.v (S k)) ∧ Only [] [H 0, H 1, H 2, H 3] s s' := by
  let t (k : Nat) (u : State) := u.setV (H k) (u.v (H k) ^^^ u.v (S k))
  let s₁ := t 0 s
  let s₂ := t 1 s₁
  let s₃ := t 2 s₂
  let s₄ := t 3 s₃
  refine ⟨s₄, ?_, ?_, ?_⟩
  · have e : ∀ k (u : State), exec (veor (H k) (H k) (S k)) u = some (t k u) := fun _ _ => rfl
    show runBlock isa [veor (H 0) (H 0) (S 0), veor (H 1) (H 1) (S 1), veor (H 2) (H 2) (S 2),
      veor (H 3) (H 3) (S 3)] s = _
    rw [runBlock_cons, e, runStep_some, runBlock_cons, e, runStep_some, runBlock_cons, e, runStep_some,
      runBlock_cons, e, runStep_some, runBlock_nil]
  · have hh : ∀ k < 4, ∀ k' < 4, k ≠ k' → ∀ u : State, (t k' u).v (H k) = u.v (H k) :=
      fun k hk k' hk' hne u => v_setV_of_ne _ _ (hinj k hk k' hk' hne)
    obtain hs : ∀ k < 4, ∀ k' < 4, ∀ u : State, (t k' u).v (S k) = u.v (S k) :=
      fun k hk k' hk' u => v_setV_of_ne _ _ (hS k hk k' hk')
    intro k hk
    rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · rw [hh 0 (by decide) 3 (by decide) (by decide), hh 0 (by decide) 2 (by decide) (by decide),
        hh 0 (by decide) 1 (by decide) (by decide)]
      exact v_setV_self _ _ _
    · rw [hh 1 (by decide) 3 (by decide) (by decide), hh 1 (by decide) 2 (by decide) (by decide)]
      show (s₁.setV _ _).v _ = _
      rw [v_setV_self, hh 1 (by decide) 0 (by decide) (by decide), hs 1 (by decide) 0 (by decide)]
    · rw [hh 2 (by decide) 3 (by decide) (by decide)]
      show (s₂.setV _ _).v _ = _
      rw [v_setV_self, hh 2 (by decide) 1 (by decide) (by decide), hh 2 (by decide) 0 (by decide) (by decide),
        hs 2 (by decide) 1 (by decide), hs 2 (by decide) 0 (by decide)]
    · show (s₃.setV _ _).v _ = _
      rw [v_setV_self, hh 3 (by decide) 2 (by decide) (by decide), hh 3 (by decide) 1 (by decide) (by decide),
        hh 3 (by decide) 0 (by decide) (by decide), hs 3 (by decide) 2 (by decide),
        hs 3 (by decide) 1 (by decide), hs 3 (by decide) 0 (by decide)]
  · exact Only.ofV ((((VOnly.setV s (by simp) _).trans (VOnly.setV _ (by simp) _)).trans
      (VOnly.setV _ (by simp) _)).trans (VOnly.setV _ (by simp) _))

theorem round_eq (sch : Reg) (up : Bool) (L R : Nat → VReg) :
    round sch up L R = loadP ++ xorHalf L (fun _ => .v0) ++ planes L ++ f sch ++ xorHalf R fReg ++
      [if up then .addImm .x .x5 .x5 4 else .subImm .x .x5 .x5 4] := rfl

theorem quarter_lane (x : BitVec 128) {n j : Nat} (hj : j < 4) :
    vbyte x (4 * (n % 4) + (3 - j)) = quarter (vword x (n % 4)) j := by
  rw [vbyte_word _ (by omega)]; rfl

theorem fReg_ne_half : ∀ k < 4, ∀ r ∈ halfRegs, fReg k ≠ r := by decide

theorem round_run {s : State} {sch : Reg} (hS : SchedIn s sch) (hc : Consts s) (up : Bool)
    {L R : Nat → VReg} (H : Halves L R) {i : Nat} (hi : i < 18)
    (hx5 : s.gpr .x5 = s.gpr sch + BitVec.ofNat 64 (4 * i)) (hsch : sch ≠ .x5 ∧ sch ≠ .x6) :
    ∃ s', runBlock isa (round sch up L R) s = some s' ∧
      (∀ n < 16, lane s'.v L n = lane s.v L n ^^^ pEntry (scheduleAt s.mem (s.gpr sch)) i) ∧
      (∀ n < 16, lane s'.v R n = lane s.v R n ^^^
        Spec.Blowfish.f (scheduleAt s.mem (s.gpr sch)) (lane s.v L n ^^^ pEntry (scheduleAt s.mem (s.gpr sch)) i)) ∧
      s'.gpr .x5 = (if up then s.gpr .x5 + 4 else s.gpr .x5 - 4) ∧
      Only [.x5, .x6] roundRegs s s' := by
  let K := scheduleAt s.mem (s.gpr sch)
  let p := pEntry K i
  -- the P-array entry
  obtain hp : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 pOff) 4 := by
    rw [hx5, Offset.add_add]; exact hS _ _ (by simp only [pOff]; omega_using [hi])
  obtain hread : s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 pOff) 32 = p := by
    rw [hx5, Offset.add_add, show 4 * i + pOff = 4096 + 4 * i by simp only [pOff]; omega_using []]
    exact (pEntry_read _ _ hi).symm
  let s₁ := s.write .w .x6 (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 pOff) 32)
  let s₂ := s₁.setV .v0 (let w := (s₁.gpr .x6).setWidth 32; ofVWords w w w w)
  obtain r₂ : runBlock isa loadP s = some s₂ := by
    rw [loadP, runBlock_cons, exec_ldr_w (by simp only [pOff]; decide) hp, runStep_some, runBlock_cons,
      exec_dup4, runStep_some, runBlock_nil]
  obtain v0₂ : ∀ l < 4, vword (s₂.v .v0) l = p := by
    intro l hl
    simp only [s₂, v_setV_self]
    rw [vword_ofVWords _ _ _ _ hl]
    have : (s₁.gpr .x6).setWidth 32 = p := by
      simp only [s₁, gpr_write_self, ← hread]; exact BitVec.setWidth_setWidth_of_le _ (by omega_using []) |>.trans (by simp)
    rcases (by omega_using [hl] : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> exact this
  obtain o₂ : Only [.x6] [.v0] s s₂ := by
    refine ⟨rfl, fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_singleton] at hr
      simp only [s₂, s₁, gpr_setV, gpr_write_of_ne _ _ _ hr]
    · simp only [List.mem_singleton] at hr
      exact v_setV_of_ne _ _ hr
  obtain hL := fun k hk => half_notin _ (H.inL k hk)
  obtain hR := fun k hk => half_notin _ (H.inR k hk)
  -- L ^= P
  obtain ⟨s₃, r₃, v₃, o₃⟩ := xorHalf_run s₂ H.injL (S := fun _ => .v0) fun k _ k' hk' => (hL k' hk').2.2.symm
  obtain L₃ : ∀ n < 16, lane s₃.v L n = lane s.v L n ^^^ p := by
    intro n hn
    simp only [lane]
    rw [v₃ _ (by omega_using [hn]), vword_xor, v0₂ _ (by omega_using []), o₂.v _ (by simp; exact (hL _ (by omega_using [hn])).2.2)]
  -- the planes
  obtain ⟨s₄, r₄, v₄, o₄⟩ := planes_run s₃ L fun k hk => (hL k hk).1
  -- F
  obtain o₂₄ : Only [.x6] roundRegs s s₄ := (o₂.mono (by simp) (by simp [roundRegs])).trans
    ((o₃.mono (by simp) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with h | h | h | h <;> subst h <;>
          exact List.mem_append_right _ (H.inL _ (by decide))).trans
      ((Only.ofV o₄).mono (by simp) (fun r hr => by simp [roundRegs, hr])))
  obtain hS₄ : Readable s₄ sch := fun off hoff => by
    rw [o₂₄.rd, o₂₄.wr, o₂₄.g _ (by simp; exact hsch.2)]; exact hS.readable off hoff
  obtain hc₄ : Consts s₄ := by
    obtain n64 : c64 ∉ roundRegs := by decide
    obtain n128 : c128 ∉ roundRegs := by decide
    exact ⟨fun e he => by rw [o₂₄.v _ n64]; exact hc.1 e he, fun e he => by rw [o₂₄.v _ n128]; exact hc.2 e he⟩
  obtain ⟨s₅, r₅, v₅, o₅⟩ := f_run hS₄ hc₄ (lane s₃.v L) fun j hj n hn => by
    rw [v₄ j hj n hn, quarter_lane _ hj]; rfl
  obtain K₅ : scheduleAt s₄.mem (s₄.gpr sch) = K := by
    rw [o₂₄.mem, o₂₄.g _ (by simp; exact hsch.2)]
  -- R ^= F
  obtain ⟨s₆, r₆, v₆, o₆⟩ := xorHalf_run s₅ H.injR (S := fReg) fun k hk k' hk' =>
    fReg_ne_half k hk _ (H.inR k' hk')
  let s₇ := s₆.write .x .x5 (if up then s₆.read .x .x5 + BitVec.ofNat _ 4 else s₆.read .x .x5 - BitVec.ofNat _ 4)
  obtain r₇ : runBlock isa [if up then .addImm .x .x5 .x5 4 else .subImm .x .x5 .x5 4] s₆ = some s₇ := by
    cases up
    · rw [runBlock_cons]; simp only [Bool.false_eq_true, ite_false]
      rw [exec_subImm_x (by decide), runStep_some, runBlock_nil]; rfl
    · rw [runBlock_cons]; simp only [ite_true]
      rw [exec_addImm_x (by decide), runStep_some, runBlock_nil]; rfl
  obtain o₂₆ : Only [.x6] roundRegs s s₆ := o₂₄.trans (((Only.ofV o₅).mono (by simp) (fun r hr => by simp [roundRegs, hr])).trans
    (o₆.mono (by simp) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with h | h | h | h <;> subst h <;>
          exact List.mem_append_right _ (H.inR _ (by decide))))
  obtain o₇ : Only [.x5, .x6] roundRegs s s₇ := by
    refine (o₂₆.mono (by simp) (fun _ h => h)).trans ⟨rfl, fun r hr => ?_, fun _ _ => rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [s₇, gpr_write_of_ne _ _ _ hr.1]
  refine ⟨s₇, ?_, ?_, ?_, ?_, o₇⟩
  · rw [round_eq]
    exact VG.AArch64.Tbl.runBlock_cat_some (VG.AArch64.Tbl.runBlock_cat_some
      (VG.AArch64.Tbl.runBlock_cat_some (VG.AArch64.Tbl.runBlock_cat_some
        (VG.AArch64.Tbl.runBlock_cat_some r₂ r₃) r₄) r₅) r₆) r₇
  · intro n hn
    obtain hk : n / 4 < 4 := by omega_using [hn]
    obtain nr : ∀ k < 4, L k ∉ [R 0, R 1, R 2, R 3] := fun k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨H.ne k hk 0 (by decide), H.ne k hk 1 (by decide), H.ne k hk 2 (by decide), H.ne k hk 3 (by decide)⟩
    simp only [lane] at L₃ ⊢
    rw [show s₇.v = s₆.v from rfl, o₆.v _ (nr _ hk), o₅.2 _ (hL _ hk).2.1, o₄.2 _ (hL _ hk).1, L₃ n hn]
  · intro n hn
    obtain hk : n / 4 < 4 := by omega_using [hn]
    obtain nl : R (n / 4) ∉ [L 0, L 1, L 2, L 3] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(H.ne 0 (by decide) _ hk).symm, (H.ne 1 (by decide) _ hk).symm,
        (H.ne 2 (by decide) _ hk).symm, (H.ne 3 (by decide) _ hk).symm⟩
    obtain hRv : s₅.v (R (n / 4)) = s.v (R (n / 4)) := by
      rw [o₅.2 _ (hR _ hk).2.1, o₄.2 _ (hR _ hk).1, o₃.v _ nl,
        o₂.v _ (by simp; exact (hR _ hk).2.2)]
    obtain L₃n := L₃ n hn
    simp only [lane] at v₅ L₃n ⊢
    rw [show s₇.v = s₆.v from rfl, v₆ _ hk, vword_xor, v₅ n hn, K₅, L₃n, hRv]
  · simp only [s₇, gpr_write_self, State.read, BitVec.setWidth_eq]
    rw [o₂₆.g _ (by simp)]
    cases up <;> rfl

end VG.Proof.Blowfish.AArch64

end

end

/-! ### `Blowfish.AArch64.Cipher`, which only this module used -/

section

/-!
# The sixteen rounds on sixteen blocks

`cipher_run`: `cipher sch up`, with xL of sixteen blocks in `A` and xR in
`B`, leaves `feistel` of each (encryption if `up`, decryption otherwise):
its xL in `B` and its xR in `A`.
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.AArch64.Tbl (VOnly)

/-- The P-array entry of round `m`. -/
def order (up : Bool) (m : Nat) : Nat := if up then m else 17 - m

theorem order_true : order true = id := rfl
theorem eval_nonzero (s : State) (r : Reg) {m : Nat} (h : s.gpr r = BitVec.ofNat 64 m)
    (hm : m < 2 ^ 64) : isa.eval (.nonzero .x r) s = some (m != 0) := by
  show some (s.read .x r != 0) = _
  simp only [State.read, BitVec.setWidth_eq, h]
  congr 1
  by_cases h0 : m = 0
  · subst h0; rfl
  · have : BitVec.ofNat 64 m ≠ 0 := by
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm] at this
      simp at this; omega_using [h0, this]
    simp only [bne, beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h0]

/-- The P pointer after round `m`. -/
theorem x5_next (p : Addr) (up : Bool) {m : Nat} (hm : m < 17) :
    (if up then p + BitVec.ofNat 64 (4 * order up m) + 4 else p + BitVec.ofNat 64 (4 * order up m) - 4) =
      p + BitVec.ofNat 64 (4 * order up (m + 1)) := by
  cases up
  · simp only [order, Bool.false_eq_true, ite_false]
    rw [show 4 * (17 - m) = 4 * (17 - (m + 1)) + 4 by omega_using [hm], ← Offset.add_add]
    exact BitVec.add_sub_cancel _ _
  · simp only [order, ite_true]
    rw [show 4 * (m + 1) = 4 * m + 4 by omega_using [], ← Offset.add_add]; rfl

theorem order_lt (up : Bool) {m : Nat} (hm : m < 18) : order up m < 18 := by
  cases up <;> simp only [order, Bool.false_eq_true, ite_false, ite_true] <;> omega_arith

structure CipherInv (s₀ : State) (sch : Reg) (up : Bool) (t : Nat) (u : State) : Prop where
  le : t ≤ 8
  a : ∀ n < 16, lane u.v aReg n =
    (iter (scheduleAt s₀.mem (s₀.gpr sch)) (order up) (2 * t) (lane s₀.v aReg n, lane s₀.v bReg n)).1
  b : ∀ n < 16, lane u.v bReg n =
    (iter (scheduleAt s₀.mem (s₀.gpr sch)) (order up) (2 * t) (lane s₀.v aReg n, lane s₀.v bReg n)).2
  x5 : u.gpr .x5 = s₀.gpr sch + BitVec.ofNat 64 (4 * order up (2 * t))
  x7 : u.gpr .x7 = BitVec.ofNat 64 (8 - t)
  only : Only [.x5, .x6, .x7] roundRegs s₀ u

theorem c_notin : c64 ∉ roundRegs ∧ c128 ∉ roundRegs := by decide

theorem pair_run {s₀ : State} {sch : Reg} (hS : SchedIn s₀ sch) (hc : Consts s₀)
    (hsch : sch ≠ .x5 ∧ sch ≠ .x6 ∧ sch ≠ .x7) (up : Bool) {t : Nat} (ht : t < 8) {u : State}
    (I : CipherInv s₀ sch up t u) :
    ∃ u', runBlock isa (roundPair sch up) u = some u' ∧ CipherInv s₀ sch up (t + 1) u' := by
  let K := scheduleAt s₀.mem (s₀.gpr sch)
  obtain hsc : u.gpr sch = s₀.gpr sch := I.only.g _ (by simp; exact ⟨hsch.1, hsch.2.1, hsch.2.2⟩)
  obtain hSu : ∀ {v : State}, Only [.x5, .x6, .x7] roundRegs s₀ v → SchedIn v sch ∧ Consts v ∧
      scheduleAt v.mem (v.gpr sch) = K := by
    intro v hv
    obtain hg : v.gpr sch = s₀.gpr sch := hv.g _ (by simp; exact ⟨hsch.1, hsch.2.1, hsch.2.2⟩)
    refine ⟨fun off n h => ?_, ⟨fun e he => ?_, fun e he => ?_⟩, by rw [hv.mem, hg]⟩
    · rw [hv.rd, hv.wr, hg]; exact hS off n h
    · rw [hv.v _ c_notin.1]; exact hc.1 e he
    · rw [hv.v _ c_notin.2]; exact hc.2 e he
  obtain ⟨hSu₀, hcu₀, Ku₀⟩ := hSu I.only
  obtain ⟨u₁, r₁, a₁, b₁, x5₁, o₁⟩ := round_run hSu₀ hcu₀ up halves_ab (order_lt up (by omega_using [ht] : 2 * t < 18))
    (by rw [I.x5, hsc]) ⟨hsch.1, hsch.2.1⟩
  obtain p₁ : Only [.x5, .x6, .x7] roundRegs s₀ u₁ := I.only.trans (o₁.mono (by simp) (fun _ h => h))
  obtain ⟨hSu₁, hcu₁, Ku₁⟩ := hSu p₁
  obtain x5₁' : u₁.gpr .x5 = u₁.gpr sch + BitVec.ofNat 64 (4 * order up (2 * t + 1)) := by
    rw [x5₁, I.x5, x5_next _ _ (by omega_using [ht]), p₁.g _ (by simp; exact ⟨hsch.1, hsch.2.1, hsch.2.2⟩)]
  obtain ⟨u₂, r₂, a₂, b₂, x5₂, o₂⟩ := round_run hSu₁ hcu₁ up halves_ba (order_lt up (by omega_using [ht] : 2 * t + 1 < 18))
    x5₁' ⟨hsch.1, hsch.2.1⟩
  obtain p₂ : Only [.x5, .x6, .x7] roundRegs s₀ u₂ := p₁.trans (o₂.mono (by simp) (fun _ h => h))
  let u₃ := u₂.write .x .x7 (u₂.read .x .x7 - BitVec.ofNat _ 1)
  obtain r₃ : runBlock isa [.subImm .x .x7 .x7 1] u₂ = some u₃ := by
    rw [runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil]
  obtain hx7₂ : u₂.gpr .x7 = u.gpr .x7 := by
    rw [o₂.g _ (by simp), o₁.g _ (by simp)]
  refine ⟨u₃, VG.AArch64.Tbl.runBlock_cat_some (VG.AArch64.Tbl.runBlock_cat_some r₁ r₂) r₃, ?_⟩
  obtain st : ∀ n < 16, iter K (order up) (2 * (t + 1)) (lane s₀.v aReg n, lane s₀.v bReg n) =
      (lane u₂.v aReg n, lane u₂.v bReg n) := by
    intro n hn
    rw [show 2 * (t + 1) = (2 * t + 1) + 1 by omega_using [], iter_succ, iter_succ]
    simp only [roundStep]
    rw [← I.a n hn, ← I.b n hn]
    refine Prod.ext ?_ ?_
    · show _ = lane u₂.v aReg n
      rw [b₂ n hn, a₁ n hn, b₁ n hn, Ku₁, Ku₀]
      dsimp only
      rw [BitVec.xor_comm (Spec.Blowfish.f K _) (lane u.v bReg n)]
      exact BitVec.xor_comm _ _
    · show _ = lane u₂.v bReg n
      rw [a₂ n hn, b₁ n hn, Ku₁, Ku₀]
      dsimp only
      rw [BitVec.xor_comm (Spec.Blowfish.f K _) (lane u.v bReg n)]
  refine ⟨by omega_using [ht], fun n hn => by rw [st n hn]; rfl, fun n hn => by rw [st n hn]; rfl, ?_, ?_, ?_⟩
  · simp only [u₃, gpr_write_of_ne _ _ _ (by decide : Reg.x5 ≠ .x7)]
    rw [x5₂, x5₁, I.x5, x5_next _ _ (by omega_using [ht]), x5_next _ _ (by omega_using [ht]),
      show 2 * t + 1 + 1 = 2 * (t + 1) by omega_using []]
  · simp only [u₃, gpr_write_self, State.read, BitVec.setWidth_eq]
    rw [hx7₂, I.x7, show 8 - t = (8 - (t + 1)) + 1 by omega_using [ht], ← BitVec.ofNat_add_ofNat]
    exact BitVec.add_sub_cancel _ _
  · exact p₂.trans ⟨rfl, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [u₃, gpr_write_of_ne _ _ _ hr.2.2], fun _ _ => rfl⟩

/-- `x6 := Pᵢ₊₁` and `v0 := Pᵢ₊₁` in every word, then `H ^= v0`. -/
theorem xorP_run {s : State} {sch : Reg} (hS : SchedIn s sch) {i : Nat} (hi : i < 18) {H : Nat → VReg}
    (hinj : ∀ k < 4, ∀ k' < 4, k ≠ k' → H k ≠ H k') (hH : ∀ k < 4, H k ≠ .v0) :
    ∃ s', runBlock isa (([.ldr .w .x6 sch (pOff + 4 * i), .vop (.dup .s4 .v0 .x6)] : List Instr) ++ xorHalf H (fun _ => .v0)) s =
        some s' ∧
      (∀ n < 16, lane s'.v H n = lane s.v H n ^^^ pEntry (scheduleAt s.mem (s.gpr sch)) i) ∧
      Only [.x6] [.v0, H 0, H 1, H 2, H 3] s s' := by
  let p := pEntry (scheduleAt s.mem (s.gpr sch)) i
  obtain hp : InRegions (s.rd ++ s.wr) (s.gpr sch + BitVec.ofNat 64 (pOff + 4 * i)) 4 :=
    hS _ _ (by simp only [pOff]; omega_using [hi])
  obtain hread : s.mem.readW (s.gpr sch + BitVec.ofNat 64 (pOff + 4 * i)) 32 = p :=
    (pEntry_read _ _ hi).symm
  let s₁ := s.write .w .x6 (s.mem.readW (s.gpr sch + BitVec.ofNat 64 (pOff + 4 * i)) 32)
  let s₂ := s₁.setV .v0 (let w := (s₁.gpr .x6).setWidth 32; ofVWords w w w w)
  obtain r₂ : runBlock isa [.ldr .w .x6 sch (pOff + 4 * i), .vop (.dup .s4 .v0 .x6)] s = some s₂ := by
    rw [runBlock_cons, exec_ldr_w (by simp only [pOff]; omega_using [hi]) hp, runStep_some, runBlock_cons,
      exec_dup4, runStep_some, runBlock_nil]
  obtain v0₂ : ∀ l < 4, vword (s₂.v .v0) l = p := by
    intro l hl
    simp only [s₂, v_setV_self]
    rw [vword_ofVWords _ _ _ _ hl]
    have : (s₁.gpr .x6).setWidth 32 = p := by
      simp only [s₁, gpr_write_self, ← hread]; exact BitVec.setWidth_setWidth_of_le _ (by omega_using []) |>.trans (by simp)
    rcases (by omega_using [hl] : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> exact this
  obtain ⟨s₃, r₃, v₃, o₃⟩ := xorHalf_run s₂ hinj (S := fun _ => .v0) fun k _ k' hk' => (hH k' hk').symm
  refine ⟨s₃, VG.AArch64.Tbl.runBlock_cat_some r₂ r₃, fun n hn => ?_, ?_⟩
  · simp only [lane]
    rw [v₃ _ (by omega_using [hn]), vword_xor, v0₂ _ (by omega_using [])]
    exact congrArg (· ^^^ p) (congrArg (vword · _) (v_setV_of_ne _ _ (hH _ (by omega_using [hn]))))
  · refine (⟨rfl, fun r hr => ?_, fun r hr => ?_⟩ : Only [.x6] [.v0, H 0, H 1, H 2, H 3] s s₂).trans
      (o₃.mono (by simp) (fun r hr => List.mem_cons_of_mem _ hr))
    · simp only [List.mem_singleton] at hr
      simp only [s₂, s₁, gpr_setV, gpr_write_of_ne _ _ _ hr]
    · simp only [List.mem_cons, not_or] at hr
      exact v_setV_of_ne _ _ hr.1

theorem finish_eq (sch : Reg) (up : Bool) :
    finish sch up = (([.ldr .w .x6 sch (pOff + 4 * order up 16), .vop (.dup .s4 .v0 .x6)] : List Instr) ++
      xorHalf aReg (fun _ => .v0)) ++
      (([.ldr .w .x6 sch (pOff + 4 * order up 17), .vop (.dup .s4 .v0 .x6)] : List Instr) ++ xorHalf bReg (fun _ => .v0)) := by
  cases up <;> rfl

theorem cipher_run {s : State} {sch : Reg} (hS : SchedIn s sch) (hc : Consts s)
    (hsch : sch ≠ .x5 ∧ sch ≠ .x6 ∧ sch ≠ .x7) (up : Bool) :
    WP isa (cipher sch up) s fun s' =>
      (∀ n < 16, lane s'.v bReg n =
          (feistel (scheduleAt s.mem (s.gpr sch)) (order up) (lane s.v aReg n) (lane s.v bReg n)).1 ∧
        lane s'.v aReg n =
          (feistel (scheduleAt s.mem (s.gpr sch)) (order up) (lane s.v aReg n) (lane s.v bReg n)).2) ∧
      Only [.x5, .x6, .x7] roundRegs s s' := by
  let K := scheduleAt s.mem (s.gpr sch)
  obtain hsch' : ∀ r ∈ [Reg.x5, .x6, .x7], sch ≠ r := by simp; exact hsch
  -- the setup
  let s₁ := s.write .x .x5 (s.read .x sch + BitVec.ofNat _ (if up then 0 else 68))
  let s₂ := s₁.write .x .x7 ((8 : BitVec 16).setWidth 64 <<< (16 * 0))
  obtain r₂ : runBlock isa [.addImm .x .x5 sch (if up then 0 else 68), .movz .x .x7 8 0] s = some s₂ := by
    rw [runBlock_cons, exec_addImm_x (by cases up <;> decide), runStep_some, runBlock_cons]
    rfl
  obtain I₀ : CipherInv s sch up 0 s₂ := by
    refine ⟨by omega_using [], fun n _ => rfl, fun n _ => rfl, ?_, rfl, ⟨rfl, fun r hr => ?_, fun _ _ => rfl⟩⟩
    · simp only [s₂, s₁, gpr_write_of_ne _ _ _ (by decide : Reg.x5 ≠ .x7), gpr_write_self, State.read,
        BitVec.setWidth_eq]
      cases up <;> rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [s₂, s₁, gpr_write_of_ne _ _ _ hr.2.2, gpr_write_of_ne _ _ _ hr.1]
  apply WP.seq
  refine WP.of_runBlock ⟨s₂, r₂, ?_⟩
  apply WP.seq
  -- the loop
  let Inv (m : Nat) (u : State) : Prop := ∃ t, t < 8 ∧ m = 8 - t ∧ CipherInv s sch up t u
  refine WP.mono (WP.loop (M := isa) (Q := CipherInv s sch up 8) Inv ?_ 8 s₂ (show Inv 8 s₂ from ⟨0, by omega_using [], rfl, I₀⟩)) ?_
  · intro m u ⟨t, ht, hm, I⟩
    obtain ⟨u', r, I'⟩ := pair_run hS hc hsch up ht I
    refine WP.of_runBlock ⟨u', r, ?_⟩
    obtain flag := eval_nonzero u' .x7 I'.x7 (by omega_using [])
    by_cases h : t + 1 = 8
    · left
      refine ⟨by rw [flag]; simp; omega_using [h], ?_⟩
      rw [← h]; exact I'
    · right
      refine ⟨by rw [flag]; simp; omega_using [ht, h], 8 - (t + 1), by omega_using [ht, hm], t + 1, by omega_using [ht, h], rfl, I'⟩
  · intro u I
    obtain hg : u.gpr sch = s.gpr sch := I.only.g _ (by simp; exact hsch)
    obtain hSu : SchedIn u sch := fun off n h => by rw [I.only.rd, I.only.wr, hg]; exact hS off n h
    obtain ⟨u₁, r₁, a₁, o₁⟩ := xorP_run hSu (order_lt up (by decide : 16 < 18)) (H := aReg)
      (by decide) (by decide)
    obtain hSu₁ : SchedIn u₁ sch := fun off n h => by
      rw [o₁.rd, o₁.wr, o₁.g _ (by simp; exact hsch.2.1)]; exact hSu off n h
    obtain ⟨u₂, r₂', b₂, o₂⟩ := xorP_run hSu₁ (order_lt up (by decide : 17 < 18)) (H := bReg)
      (by decide) (by decide)
    refine WP.of_runBlock ⟨u₂, by rw [finish_eq]; exact VG.AArch64.Tbl.runBlock_cat_some r₁ r₂', ?_⟩
    obtain K₁ : scheduleAt u₁.mem (u₁.gpr sch) = K := by
      rw [o₁.mem, o₁.g _ (by simp; exact hsch.2.1), I.only.mem, hg]
    obtain K₀ : scheduleAt u.mem (u.gpr sch) = K := by rw [I.only.mem, hg]
    refine ⟨fun n hn => ⟨?_, ?_⟩, ?_⟩
    · have nb : ∀ k < 4, bReg k ∉ [VReg.v0, aReg 0, aReg 1, aReg 2, aReg 3] := by decide
      obtain hb₁ : lane u₁.v bReg n = lane u.v bReg n := by
        simp only [lane]; rw [o₁.v _ (nb _ (by omega_using [hn]))]
      rw [b₂ n hn, K₁, feistel_eq, hb₁, I.b n hn]
    · have na : ∀ k < 4, aReg k ∉ [VReg.v0, bReg 0, bReg 1, bReg 2, bReg 3] := by decide
      simp only [lane] at a₁ ⊢
      rw [o₂.v _ (na _ (by omega_using [hn])), a₁ n hn, K₀, feistel_eq]
      have := I.a n hn
      simp only [lane] at this
      rw [this]
    · exact I.only.trans ((o₁.mono (by simp) (by decide)).trans (o₂.mono (by simp) (by decide)))

end VG.Proof.Blowfish.AArch64

end

end


/-!
# A batch of sixteen blocks

`loadBatch_run`: the sixteen blocks at `x4` into `A` (xL) and `B` (xR), as
big-endian words. `storeBatch_run`: xL from `B` and xR from `A` back, as
blocks.
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.AArch64.Tbl (VOnly)

/-- Word `w` of a reversed 16-byte load: the big-endian word at `4 w`, which
is half `w % 2` of block `w / 2`. -/
theorem vword_rev_read (m : Mem) (a : Addr) {w : Nat} (hw : w < 4) :
    vword (VRevOp.eval .rev32b (m.read a 16)) w =
      decodeWord (blockAt m (a + BitVec.ofNat 64 (8 * (w / 2)))) (4 * (w % 2)) := by
  refine word_ext fun b hb => ?_
  rw [← vbyte_word _ hb, vbyte_rev32b _ (by omega_arith), vbyte_read16 _ _ (by omega_arith), decodeWord_byte _ _ hb,
    blockAt_getD _ _ (by omega_arith), Offset.add_add,
    show 4 * ((4 * w + b) / 4) + (3 - (4 * w + b) % 4) = 8 * (w / 2) + (4 * (w % 2) + (3 - b)) by omega_arith]

theorem ldrq_run {t : State} (d : VReg) (n : Reg) {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions (t.rd ++ t.wr) (t.gpr n + BitVec.ofNat 64 off) 16) :
    ∃ t', runBlock isa [.ldrq d n off] t = some t' ∧
      t'.v d = t.mem.read (t.gpr n + BitVec.ofNat 64 off) 16 ∧ VOnly [d] t t' :=
  ⟨_, by rw [runBlock_cons, exec_ldrq ho h, runStep_some, runBlock_nil], v_setV_self _ _ _,
    VOnly.setV _ (by simp) _⟩

theorem vop_run {t : State} (op : VOp) (d : VReg) (x : BitVec 128) (h : exec (.vop op) t = some (t.setV d x)) :
    ∃ t', runBlock isa [.vop op] t = some t' ∧ t'.v d = x ∧ VOnly [d] t t' :=
  ⟨_, by rw [runBlock_cons, h, runStep_some, runBlock_nil], v_setV_self _ _ _, VOnly.setV _ (by simp) _⟩

/-- Chaining two steps that each change one register. -/
theorem cat_run {a b : List Instr} {s s₁ s₂ : State} (h₁ : runBlock isa a s = some s₁)
    (h₂ : runBlock isa b s₁ = some s₂) : runBlock isa (a ++ b) s = some s₂ :=
  VG.AArch64.Tbl.runBlock_cat_some h₁ h₂

theorem ab_ne : ∀ k < 4, aReg k ≠ .v20 ∧ aReg k ≠ .v21 ∧ bReg k ≠ .v20 ∧ bReg k ≠ .v21 ∧ aReg k ≠ bReg k := by
  decide

/-- Blocks `4 k`…`4 k + 3` into word `k` of `A` and `B`. -/
theorem loadPair_run {s : State} {k : Nat} (hk : k < 4)
    (hR : ∀ j < 2, InRegions (s.rd ++ s.wr) (s.gpr .x4 + BitVec.ofNat 64 (32 * k + 16 * j)) 16) :
    ∃ s', runBlock isa (loadPair .x4 k) s = some s' ∧
      (∀ l < 4, vword (s'.v (aReg k)) l =
        decodeWord (blockAt s.mem (s.gpr .x4 + BitVec.ofNat 64 (8 * (4 * k + l)))) 0) ∧
      (∀ l < 4, vword (s'.v (bReg k)) l =
        decodeWord (blockAt s.mem (s.gpr .x4 + BitVec.ofNat 64 (8 * (4 * k + l)))) 4) ∧
      VOnly [.v20, .v21, aReg k, bReg k] s s' := by
  obtain ne := ab_ne k hk
  obtain ⟨s₁, r₁, v₁, o₁⟩ := ldrq_run (t := s) .v20 .x4 (off := 32 * k) (by omega_arith)
    (by have := hR 0 (by decide); simpa using this)
  obtain ⟨s₂, r₂, v₂, o₂⟩ := ldrq_run (t := s₁) .v21 .x4 (off := 32 * k + 16) (by omega_arith)
    (by rw [o₁.rd, o₁.wr, o₁.gpr]; exact hR 1 (by decide))
  obtain ⟨s₃, r₃, v₃, o₃⟩ := vop_run (t := s₂) (.rev .rev32b .v20 .v20) .v20 _ (exec_rev32b _ _ _)
  obtain ⟨s₄, r₄, v₄, o₄⟩ := vop_run (t := s₃) (.rev .rev32b .v21 .v21) .v21 _ (exec_rev32b _ _ _)
  obtain ⟨s₅, r₅, v₅, o₅⟩ := vop_run (t := s₄) (.perm .uzp1 .s4 (aReg k) .v20 .v21) (aReg k) _
    (exec_vperm _ _ _ _ _ _)
  obtain ⟨s₆, r₆, v₆, o₆⟩ := vop_run (t := s₅) (.perm .uzp2 .s4 (bReg k) .v20 .v21) (bReg k) _
    (exec_vperm _ _ _ _ _ _)
  -- the two reversed loads
  have m₁ : s₁.mem = s.mem := o₁.mem
  have g₁ : s₁.gpr = s.gpr := o₁.gpr
  obtain w20 : s₄.v .v20 = VRevOp.eval .rev32b (s.mem.read (s.gpr .x4 + BitVec.ofNat 64 (32 * k)) 16) := by
    rw [o₄.2 _ (by simp), v₃, o₂.2 _ (by simp), v₁]
  obtain w21 : s₄.v .v21 =
      VRevOp.eval .rev32b (s.mem.read (s.gpr .x4 + BitVec.ofNat 64 (32 * k + 16)) 16) := by
    rw [v₄, o₃.2 _ (by simp), v₂, m₁, g₁]
  obtain w20' : s₅.v .v20 = s₄.v .v20 := o₅.2 _ (by simp; exact ne.1.symm)
  obtain w21' : s₅.v .v21 = s₄.v .v21 := o₅.2 _ (by simp; exact ne.2.1.symm)
  refine ⟨s₆, cat_run r₁ (cat_run r₂ (cat_run r₃ (cat_run r₄ (cat_run r₅ r₆)))), ?_, ?_, ?_⟩
  · intro l hl
    rw [o₆.2 _ (by simp; exact ne.2.2.2.2), v₅, vword_uzp1 _ _ hl, w20, w21]
    split
    · rw [vword_rev_read _ _ (by omega_arith), Offset.add_add, show 32 * k + 8 * (2 * l / 2) = 8 * (4 * k + l) by omega_arith,
        show 4 * (2 * l % 2) = 0 by omega_arith]
    · rw [vword_rev_read _ _ (by omega_arith), Offset.add_add,
        show 32 * k + 16 + 8 * ((2 * l - 4) / 2) = 8 * (4 * k + l) by omega_arith,
        show 4 * ((2 * l - 4) % 2) = 0 by omega_arith]
  · intro l hl
    rw [v₆, w20', w21', vword_uzp2 _ _ hl, w20, w21]
    split
    · rw [vword_rev_read _ _ (by omega_arith), Offset.add_add,
        show 32 * k + 8 * ((2 * l + 1) / 2) = 8 * (4 * k + l) by omega_arith,
        show 4 * ((2 * l + 1) % 2) = 4 by omega_arith]
    · rw [vword_rev_read _ _ (by omega_arith), Offset.add_add,
        show 32 * k + 16 + 8 * ((2 * l + 1 - 4) / 2) = 8 * (4 * k + l) by omega_arith,
        show 4 * ((2 * l + 1 - 4) % 2) = 4 by omega_arith]
  · exact (((((VOnly.mono o₁ (by simp)).trans (VOnly.mono o₂ (by simp))).trans (VOnly.mono o₃ (by simp))).trans
      (VOnly.mono o₄ (by simp))).trans (VOnly.mono o₅ (by simp))).trans (VOnly.mono o₆ (by simp))

theorem loadPair_eq : (List.range 4).flatMap (loadPair .x4) =
    loadPair .x4 0 ++ (loadPair .x4 1 ++ (loadPair .x4 2 ++ (loadPair .x4 3 ++ []))) := rfl

/-- The sixteen blocks at `x4` into `A` (xL) and `B` (xR). -/
theorem loadBatch_run {s : State}
    (hR : ∀ k < 8, InRegions (s.rd ++ s.wr) (s.gpr .x4 + BitVec.ofNat 64 (16 * k)) 16) :
    ∃ s', runBlock isa (loadBatch .x4) s = some s' ∧
      (∀ n < 16, lane s'.v aReg n = decodeWord (blockAt s.mem (s.gpr .x4 + BitVec.ofNat 64 (8 * n))) 0) ∧
      (∀ n < 16, lane s'.v bReg n = decodeWord (blockAt s.mem (s.gpr .x4 + BitVec.ofNat 64 (8 * n))) 4) ∧
      VOnly (.v20 :: .v21 :: halfRegs) s s' := by
  obtain hR' : ∀ {t : State}, VOnly (.v20 :: .v21 :: halfRegs) s t → ∀ k < 4, ∀ j < 2,
      InRegions (t.rd ++ t.wr) (t.gpr .x4 + BitVec.ofNat 64 (32 * k + 16 * j)) 16 := by
    intro t ht k hk j hj
    rw [ht.rd, ht.wr, ht.gpr, show 32 * k + 16 * j = 16 * (2 * k + j) by omega_arith]
    exact hR _ (by omega_arith)
  obtain sub : ∀ k < 4, ∀ r ∈ [VReg.v20, .v21, aReg k, bReg k], r ∈ VReg.v20 :: .v21 :: halfRegs := by decide
  obtain ⟨s₀, r₀, a₀, b₀, o₀⟩ := loadPair_run (s := s) (by decide : 0 < 4) (hR' (VOnly.refl _ _) 0 (by decide))
  obtain p₀ := VOnly.mono o₀ (sub 0 (by decide))
  obtain ⟨s₁, r₁, a₁, b₁, o₁⟩ := loadPair_run (s := s₀) (by decide : 1 < 4) (hR' p₀ 1 (by decide))
  obtain p₁ := p₀.trans (VOnly.mono o₁ (sub 1 (by decide)))
  obtain ⟨s₂, r₂, a₂, b₂, o₂⟩ := loadPair_run (s := s₁) (by decide : 2 < 4) (hR' p₁ 2 (by decide))
  obtain p₂ := p₁.trans (VOnly.mono o₂ (sub 2 (by decide)))
  obtain ⟨s₃, r₃, a₃, b₃, o₃⟩ := loadPair_run (s := s₂) (by decide : 3 < 4) (hR' p₂ 3 (by decide))
  obtain p₃ := p₂.trans (VOnly.mono o₃ (sub 3 (by decide)))
  refine ⟨s₃, by rw [loadBatch, loadPair_eq]; exact cat_run r₀ (cat_run r₁ (cat_run r₂ (cat_run r₃ runBlock_nil))),
    ?_, ?_, p₃⟩
  all_goals
    intro n hn
    obtain m₀ := o₀.mem; have m₁ := o₁.mem; have m₂ := o₂.mem
    obtain g₀ := o₀.gpr; have g₁ := o₁.gpr; have g₂ := o₂.gpr
    obtain pres : ∀ k < 4, ∀ k' < 4, k ≠ k' → aReg k ∉ [VReg.v20, .v21, aReg k', bReg k'] ∧
        bReg k ∉ [VReg.v20, .v21, aReg k', bReg k'] := by decide
    simp only [lane]
    rcases (by omega_arith : n / 4 = 0 ∨ n / 4 = 1 ∨ n / 4 = 2 ∨ n / 4 = 3) with h | h | h | h <;> rw [h]
  · rw [o₃.2 _ (pres 0 (by decide) 3 (by decide) (by decide)).1, o₂.2 _ (pres 0 (by decide) 2 (by decide) (by decide)).1, o₁.2 _ (pres 0 (by decide) 1 (by decide) (by decide)).1, a₀ _ (by omega_arith)]
    exact congrArg (decodeWord · 0) (congrArg _ (congrArg _ (congrArg _ (by omega_arith))))
  · rw [o₃.2 _ (pres 1 (by decide) 3 (by decide) (by decide)).1, o₂.2 _ (pres 1 (by decide) 2 (by decide) (by decide)).1, a₁ _ (by omega_arith), m₀, g₀]
    exact congrArg (decodeWord · 0) (congrArg _ (congrArg _ (congrArg _ (by omega_arith))))
  · rw [o₃.2 _ (pres 2 (by decide) 3 (by decide) (by decide)).1, a₂ _ (by omega_arith), m₁, g₁, m₀, g₀]
    exact congrArg (decodeWord · 0) (congrArg _ (congrArg _ (congrArg _ (by omega_arith))))
  · rw [a₃ _ (by omega_arith), m₂, g₂, m₁, g₁, m₀, g₀]
    exact congrArg (decodeWord · 0) (congrArg _ (congrArg _ (congrArg _ (by omega_arith))))
  · rw [o₃.2 _ (pres 0 (by decide) 3 (by decide) (by decide)).2, o₂.2 _ (pres 0 (by decide) 2 (by decide) (by decide)).2, o₁.2 _ (pres 0 (by decide) 1 (by decide) (by decide)).2, b₀ _ (by omega_arith)]
    exact congrArg (decodeWord · 4) (congrArg _ (congrArg _ (congrArg _ (by omega_arith))))
  · rw [o₃.2 _ (pres 1 (by decide) 3 (by decide) (by decide)).2, o₂.2 _ (pres 1 (by decide) 2 (by decide) (by decide)).2, b₁ _ (by omega_arith), m₀, g₀]
    exact congrArg (decodeWord · 4) (congrArg _ (congrArg _ (congrArg _ (by omega_arith))))
  · rw [o₃.2 _ (pres 2 (by decide) 3 (by decide) (by decide)).2, b₂ _ (by omega_arith), m₁, g₁, m₀, g₀]
    exact congrArg (decodeWord · 4) (congrArg _ (congrArg _ (congrArg _ (by omega_arith))))
  · rw [b₃ _ (by omega_arith), m₂, g₂, m₁, g₁, m₀, g₀]
    exact congrArg (decodeWord · 4) (congrArg _ (congrArg _ (congrArg _ (by omega_arith))))

/-! ## Storing -/

/-- Byte `j` (< 128) of the sixteen blocks whose halves are the words of `A`
and `B` (xL in `B`, xR in `A`). -/
def outByte (v : VReg → BitVec 128) (j : Nat) : Byte :=
  (encodeBlock (lane v bReg (j / 8)) (lane v aReg (j / 8))).getD (j % 8) 0

theorem write16_byte (m : Mem) (p : Addr) (x : BitVec 128) {o j : Nat} (ho : o + 16 ≤ 128) (hj : j < 128) :
    m.write (p + BitVec.ofNat 64 o) 16 x (p + BitVec.ofNat 64 j) =
      if o ≤ j ∧ j < o + 16 then vbyte x (j - o) else m (p + BitVec.ofNat 64 j) := by
  simp only [Mem.write, Offset.sub_toNat' p (show o < 2 ^ 64 by omega_arith) (show j < 2 ^ 64 by omega_arith)]
  by_cases h : o ≤ j
  · simp only [h, ite_true, true_and]
    by_cases h' : j < o + 16
    · simp only [show j - o < 16 by omega_arith, h', ite_true]; rfl
    · simp only [show ¬ j - o < 16 by omega_arith, h', ite_false]
  · simp only [h, ite_false, false_and]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]

/-- What `rev32 (zip1/zip2 .4s B A)` holds: byte `e` of it is byte `e % 8` of
block `2 o + e / 8` of the four in words `k` of `A` and `B`. -/
theorem stored_byte (Bk Ak : BitVec 128) {o e : Nat} (ho : o < 2) (he : e < 16) :
    vbyte (VRevOp.eval .rev32b (VPermOp.eval (if o = 0 then .zip1 else .zip2) .s4 Bk Ak)) e =
      (encodeBlock (vword Bk (2 * o + e / 8)) (vword Ak (2 * o + e / 8))).getD (e % 8) 0 := by
  rw [vbyte_rev32b _ he, vbyte_word _ (by omega_arith), encodeBlock_getD _ _ (by omega_arith)]
  obtain hw : (e / 4) / 2 = e / 8 := by omega_arith
  rcases (by omega_arith : o = 0 ∨ o = 1) with rfl | rfl
  · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), vword_zip1 _ _ (by omega_arith), hw]
    by_cases h : e % 8 < 4
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith)), ite_eq_left_of_eq_true _ _ (eq_true h),
        show 3 - e % 4 = 3 - e % 8 by omega_arith, show 2 * 0 + e / 8 = e / 8 by omega_arith]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)), ite_eq_right_of_eq_false _ _ (eq_false h),
        show 3 - e % 4 = 7 - e % 8 by omega_arith, show 2 * 0 + e / 8 = e / 8 by omega_arith]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide)), vword_zip2 _ _ (by omega_arith), hw]
    by_cases h : e % 8 < 4
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith)), ite_eq_left_of_eq_true _ _ (eq_true h),
        show 3 - e % 4 = 3 - e % 8 by omega_arith, show 2 * 1 + e / 8 = 2 + e / 8 by omega_arith]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)), ite_eq_right_of_eq_false _ _ (eq_false h),
        show 3 - e % 4 = 7 - e % 8 by omega_arith, show 2 * 1 + e / 8 = 2 + e / 8 by omega_arith]

/-- Only the memory and the vector registers `vs` change. -/
structure MOnly (vs : List VReg) (s s' : State) : Prop where
  eq : s' = { s with v := s'.v, mem := s'.mem }
  v : ∀ r, r ∉ vs → s'.v r = s.v r

theorem MOnly.trans {vs : List VReg} {a b c : State} (h₁ : MOnly vs a b) (h₂ : MOnly vs b c) : MOnly vs a c := by
  refine ⟨?_, fun r hr => (h₂.v r hr).trans (h₁.v r hr)⟩
  rw [h₂.eq, h₁.eq]

theorem MOnly.ofV {vs : List VReg} {a b : State} (h : VOnly vs a b) : MOnly vs a b :=
  ⟨by rw [h.1], h.2⟩

theorem MOnly.gpr {vs : List VReg} {a b : State} (h : MOnly vs a b) : b.gpr = a.gpr := by rw [h.eq]
theorem MOnly.rd {vs : List VReg} {a b : State} (h : MOnly vs a b) : b.rd = a.rd := by rw [h.eq]
theorem MOnly.wr {vs : List VReg} {a b : State} (h : MOnly vs a b) : b.wr = a.wr := by rw [h.eq]
theorem MOnly.sp {vs : List VReg} {a b : State} (h : MOnly vs a b) : b.sp = a.sp := by rw [h.eq]

theorem strq_run {t : State} (d : VReg) (n : Reg) {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions t.wr (t.gpr n + BitVec.ofNat 64 off) 16) :
    ∃ t', runBlock isa [.strq d n off] t = some t' ∧
      t'.mem = t.mem.write (t.gpr n + BitVec.ofNat 64 off) 16 (t.v d) ∧ MOnly [] t t' :=
  ⟨{ t with mem := t.mem.write (t.gpr n + BitVec.ofNat 64 off) 16 (t.v d) },
    by rw [runBlock_cons, exec_strq ho h, runStep_some, runBlock_nil], rfl, ⟨rfl, fun _ _ => rfl⟩⟩

theorem storePair_run {s : State} {k : Nat} (hk : k < 4)
    (hW : ∀ j < 2, InRegions s.wr (s.gpr .x4 + BitVec.ofNat 64 (32 * k + 16 * j)) 16) :
    ∃ s', runBlock isa (storePair .x4 k) s = some s' ∧
      (∀ j < 128, s'.mem (s.gpr .x4 + BitVec.ofNat 64 j) =
        if 32 * k ≤ j ∧ j < 32 * k + 32 then outByte s.v j else s.mem (s.gpr .x4 + BitVec.ofNat 64 j)) ∧
      Frame [⟨s.gpr .x4, 128⟩] s.mem s'.mem ∧ MOnly [.v20, .v21] s s' := by
  obtain ne := ab_ne k hk
  obtain ⟨s₁, r₁, v₁, o₁⟩ := vop_run (t := s) (.perm .zip1 .s4 .v20 (bReg k) (aReg k)) .v20 _
    (exec_vperm _ _ _ _ _ _)
  obtain ⟨s₂, r₂, v₂, o₂⟩ := vop_run (t := s₁) (.perm .zip2 .s4 .v21 (bReg k) (aReg k)) .v21 _
    (exec_vperm _ _ _ _ _ _)
  obtain ⟨s₃, r₃, v₃, o₃⟩ := vop_run (t := s₂) (.rev .rev32b .v20 .v20) .v20 _ (exec_rev32b _ _ _)
  obtain ⟨s₄, r₄, v₄, o₄⟩ := vop_run (t := s₃) (.rev .rev32b .v21 .v21) .v21 _ (exec_rev32b _ _ _)
  obtain o₁₄ : VOnly [.v20, .v21] s s₄ := (((VOnly.mono o₁ (by simp)).trans (VOnly.mono o₂ (by simp))).trans
    (VOnly.mono o₃ (by simp))).trans (VOnly.mono o₄ (by simp))
  obtain ⟨s₅, r₅, m₅, o₅⟩ := strq_run (t := s₄) .v20 .x4 (off := 32 * k) (by omega_arith)
    (by rw [o₁₄.wr, o₁₄.gpr]; simpa using hW 0 (by decide))
  obtain ⟨s₆, r₆, m₆, o₆⟩ := strq_run (t := s₅) .v21 .x4 (off := 32 * k + 16) (by omega_arith)
    (by rw [o₅.wr, o₅.gpr, o₁₄.wr, o₁₄.gpr]; exact hW 1 (by decide))
  -- the values stored
  obtain x20 : s₄.v .v20 = VRevOp.eval .rev32b (VPermOp.eval .zip1 .s4 (s.v (bReg k)) (s.v (aReg k))) := by
    rw [o₄.2 _ (by simp), v₃, o₂.2 _ (by simp), v₁]
  obtain x21 : s₅.v .v21 = VRevOp.eval .rev32b (VPermOp.eval .zip2 .s4 (s.v (bReg k)) (s.v (aReg k))) := by
    rw [o₅.v _ (by simp), v₄, o₃.2 _ (by simp), v₂, o₁.2 _ (by simp; exact ne.2.2.1),
      o₁.2 _ (by simp; exact ne.1)]
  have g₄' : s₄.gpr = s.gpr := o₁₄.gpr
  obtain g₅' : s₅.gpr = s.gpr := by rw [o₅.gpr, g₄']
  obtain fr : Frame [⟨s.gpr .x4, 128⟩] s.mem s₆.mem := by
    rw [m₆, m₅, g₅', g₄', o₁₄.mem]
    exact ((Frame.refl _ _).write (List.mem_singleton.mpr rfl) _
      (Offset.contains_base _ (by omega_arith) (by omega_arith))).write (List.mem_singleton.mpr rfl) _
      (Offset.contains_base _ (by omega_arith) (by omega_arith))
  refine ⟨s₆, cat_run r₁ (cat_run r₂ (cat_run r₃ (cat_run r₄ (cat_run r₅ r₆)))), fun j hj => ?_, fr,
    (MOnly.ofV o₁₄).trans (o₅.trans o₆ |>.trans ⟨rfl, fun _ _ => rfl⟩ |> fun h => ⟨h.eq, fun r _ => h.v r (by simp)⟩)⟩
  have g₄ : s₄.gpr = s.gpr := o₁₄.gpr
  obtain g₅ : s₅.gpr = s.gpr := by rw [o₅.gpr, g₄]
  rw [m₆, g₅, show s.gpr .x4 + BitVec.ofNat 64 (32 * k + 16) = s.gpr .x4 + BitVec.ofNat 64 (32 * k + 16) from rfl,
    write16_byte _ _ _ (by omega_arith) hj, m₅, g₄, write16_byte _ _ _ (by omega_arith) hj, o₁₄.mem, x21, x20]
  obtain lane_k : ∀ (R : Nat → VReg) (e : Nat), e < 16 → ∀ o < 2,
      vword (s.v (R k)) (2 * o + e / 8) = lane s.v R (4 * k + (2 * o + e / 8)) := by
    intro R e he o ho
    simp only [lane]
    rw [show (4 * k + (2 * o + e / 8)) / 4 = k by omega_arith, show (4 * k + (2 * o + e / 8)) % 4 = 2 * o + e / 8 by omega_arith]
  by_cases h₂ : 32 * k + 16 ≤ j ∧ j < 32 * k + 16 + 16
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h₂), ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith)),
      show VPermOp.zip2 = (if 1 = 0 then .zip1 else .zip2) from rfl, stored_byte _ _ (by decide) (by omega_arith),
      lane_k bReg _ (by omega_arith) 1 (by decide), lane_k aReg _ (by omega_arith) 1 (by decide), outByte,
      show 4 * k + (2 * 1 + (j - (32 * k + 16)) / 8) = j / 8 by omega_arith,
      show (j - (32 * k + 16)) % 8 = j % 8 by omega_arith]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h₂)]
    by_cases h₁ : 32 * k ≤ j ∧ j < 32 * k + 16
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h₁), ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith)),
        show VPermOp.zip1 = (if 0 = 0 then .zip1 else .zip2) from rfl, stored_byte _ _ (by decide) (by omega_arith),
        lane_k bReg _ (by omega_arith) 0 (by decide), lane_k aReg _ (by omega_arith) 0 (by decide), outByte,
        show 4 * k + (2 * 0 + (j - 32 * k) / 8) = j / 8 by omega_arith,
        show (j - 32 * k) % 8 = j % 8 by omega_arith]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h₁), ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]

theorem storePair_eq : (List.range 4).flatMap (storePair .x4) =
    storePair .x4 0 ++ (storePair .x4 1 ++ (storePair .x4 2 ++ (storePair .x4 3 ++ []))) := rfl

theorem outByte_congr {v v' : VReg → BitVec 128} (h : ∀ r ∈ halfRegs, v' r = v r) (j : Nat) :
    outByte v' j = outByte v j := by
  obtain ha : ∀ n, lane v' aReg n = lane v aReg n := fun n => by
    simp only [lane]; rw [h _ (by
      rcases (by omega_arith : n / 4 = 0 ∨ n / 4 = 1 ∨ n / 4 = 2 ∨ n / 4 = 3 ∨ 4 ≤ n / 4) with e | e | e | e | e <;>
        simp [e, aReg, halfRegs])]
  obtain hb : ∀ n, lane v' bReg n = lane v bReg n := fun n => by
    simp only [lane]; rw [h _ (by
      rcases (by omega_arith : n / 4 = 0 ∨ n / 4 = 1 ∨ n / 4 = 2 ∨ n / 4 = 3 ∨ 4 ≤ n / 4) with e | e | e | e | e <;>
        simp [e, bReg, halfRegs])]
  simp only [outByte, ha, hb]

/-- The halves of the sixteen blocks back to the 128 bytes at `x4`. -/
theorem storeBatch_run {s : State}
    (hW : ∀ k < 8, InRegions s.wr (s.gpr .x4 + BitVec.ofNat 64 (16 * k)) 16) :
    ∃ s', runBlock isa (storeBatch .x4) s = some s' ∧
      (∀ j < 128, s'.mem (s.gpr .x4 + BitVec.ofNat 64 j) = outByte s.v j) ∧
      Frame [⟨s.gpr .x4, 128⟩] s.mem s'.mem ∧ MOnly [.v20, .v21] s s' := by
  obtain hW' : ∀ {t : State}, MOnly [.v20, .v21] s t → ∀ k < 4, ∀ j < 2,
      InRegions t.wr (t.gpr .x4 + BitVec.ofNat 64 (32 * k + 16 * j)) 16 := by
    intro t ht k hk j hj
    rw [ht.wr, ht.gpr, show 32 * k + 16 * j = 16 * (2 * k + j) by omega_arith]
    exact hW _ (by omega_arith)
  obtain hh : ∀ {t : State}, MOnly [.v20, .v21] s t → ∀ r ∈ halfRegs, t.v r = s.v r := fun ht r hr =>
    ht.v r (by revert r; decide)
  obtain ⟨s₀, r₀, m₀, f₀, o₀⟩ := storePair_run (s := s) (by decide : 0 < 4) (hW' ⟨rfl, fun _ _ => rfl⟩ 0 (by decide))
  obtain ⟨s₁, r₁, m₁, f₁, o₁⟩ := storePair_run (s := s₀) (by decide : 1 < 4) (hW' o₀ 1 (by decide))
  obtain p₁ := o₀.trans o₁
  obtain ⟨s₂, r₂, m₂, f₂, o₂⟩ := storePair_run (s := s₁) (by decide : 2 < 4) (hW' p₁ 2 (by decide))
  obtain p₂ := p₁.trans o₂
  obtain ⟨s₃, r₃, m₃, f₃, o₃⟩ := storePair_run (s := s₂) (by decide : 3 < 4) (hW' p₂ 3 (by decide))
  obtain p₃ := p₂.trans o₃
  obtain g₀ := o₀.gpr; have g₁ := p₁.gpr; have g₂ := p₂.gpr
  obtain b₀ := outByte_congr (hh o₀); have b₁ := outByte_congr (hh p₁); have b₂ := outByte_congr (hh p₂)
  obtain mem : ∀ j < 128, s₃.mem (s.gpr .x4 + BitVec.ofNat 64 j) = outByte s.v j := by
    intro j hj
    obtain e₃ := m₃ j hj; have e₂ := m₂ j hj; have e₁ := m₁ j hj; have e₀ := m₀ j hj
    rw [g₂] at e₃; rw [g₁] at e₂; rw [g₀] at e₁
    rw [e₃, b₂]
    split
    · rfl
    · rw [e₂, b₁]; split
      · rfl
      · rw [e₁, b₀]; split
        · rfl
        · rw [e₀]; split
          · rfl
          · omega_arith
  refine ⟨s₃, by rw [storeBatch, storePair_eq]; exact cat_run r₀ (cat_run r₁ (cat_run r₂ (cat_run r₃ runBlock_nil))),
    mem, ?_, p₃⟩
  rw [g₂] at f₃; rw [g₁] at f₂; rw [g₀] at f₁
  exact f₀.trans (f₁.trans (f₂.trans f₃))

/-! ## The batch -/

/-- A block's encryption (`up`) or decryption. -/
def blockOut (K : Schedule) (up : Bool) (b : Block) : Block :=
  if up then encryptBlock K b else decryptBlock K b

theorem blockOut_eq (K : Schedule) (up : Bool) (b : Block) :
    blockOut K up b = encodeBlock (feistel K (order up) (decodeWord b 0) (decodeWord b 4)).1
      (feistel K (order up) (decodeWord b 0) (decodeWord b 4)).2 := by
  cases up <;> rfl

structure BatchPost (up : Bool) (s s' : State) : Prop where
  out : ∀ n < 16, blockAt s'.mem (s.gpr .x4 + BitVec.ofNat 64 (8 * n)) =
    blockOut (scheduleAt s.mem (s.gpr .x0)) up (blockAt s.mem (s.gpr .x4 + BitVec.ofNat 64 (8 * n)))
  gpr : ∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [⟨s.gpr .x4, 128⟩] s.mem s'.mem
  v : ∀ r, r ∉ roundRegs → s'.v r = s.v r

theorem io_sub : ∀ r ∈ (VReg.v20 :: .v21 :: halfRegs), r ∈ roundRegs := by decide

theorem batch_ok (up : Bool) {s : State} (hS : SchedIn s .x0) (hc : Consts s)
    (hW : ∀ k < 8, InRegions s.wr (s.gpr .x4 + BitVec.ofNat 64 (16 * k)) 16) :
    WP isa (batch up) s (BatchPost up s) := by
  let K := scheduleAt s.mem (s.gpr .x0)
  obtain ⟨s₁, r₁, a₁, b₁, o₁⟩ := loadBatch_run (s := s) fun k hk => by
    obtain ⟨r, hr, hc'⟩ := hW k hk; exact ⟨r, List.mem_append_right _ hr, hc'⟩
  rw [batch]
  apply WP.seq
  refine WP.of_runBlock ⟨s₁, r₁, ?_⟩
  obtain hS₁ : SchedIn s₁ .x0 := fun off n h => by rw [o₁.rd, o₁.wr, o₁.gpr]; exact hS off n h
  obtain hc₁ : Consts s₁ :=
    ⟨fun e he => by rw [o₁.2 _ (by decide)]; exact hc.1 e he, fun e he => by rw [o₁.2 _ (by decide)]; exact hc.2 e he⟩
  apply WP.seq
  refine WP.mono (cipher_run hS₁ hc₁ (by decide) up) ?_
  intro s₂ ⟨hl, o₂⟩
  obtain hW₂ : ∀ k < 8, InRegions s₂.wr (s₂.gpr .x4 + BitVec.ofNat 64 (16 * k)) 16 := fun k hk => by
    rw [o₂.wr, o₂.g _ (by simp), o₁.wr, o₁.gpr]; exact hW k hk
  obtain ⟨s₃, r₃, m₃, f₃, o₃⟩ := storeBatch_run hW₂
  refine WP.of_runBlock ⟨s₃, r₃, ?_⟩
  obtain g₂ : s₂.gpr .x4 = s.gpr .x4 := by rw [o₂.g _ (by simp), o₁.gpr]
  obtain K₁ : scheduleAt s₁.mem (s₁.gpr .x0) = K := by rw [o₁.mem, o₁.gpr]
  refine ⟨fun n hn => ?_, fun r h5 h6 h7 => ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · refine blockAt_eq _ _ _ fun i hi => ?_
    rw [← g₂, Offset.add_add, m₃ _ (by omega_arith), outByte, show (8 * n + i) / 8 = n by omega_arith,
      show (8 * n + i) % 8 = i by omega_arith, (hl n hn).1, (hl n hn).2, K₁, a₁ n hn, b₁ n hn, ← blockOut_eq, g₂]
  · rw [o₃.gpr, o₂.g _ (by simp; exact ⟨h5, h6, h7⟩), o₁.gpr]
  · rw [o₃.rd, o₂.rd, o₁.rd]
  · rw [o₃.wr, o₂.wr, o₁.wr]
  · rw [o₃.sp, o₂.sp, o₁.1]
  · rw [g₂] at f₃; rw [← o₁.mem, ← o₂.mem]; exact f₃
  · have n20 : r ∉ [VReg.v20, .v21] := fun h => hr (io_sub _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with h | h <;> simp [h]))
    rw [o₃.v _ n20, o₂.v _ hr, o₁.2 _ (fun h => hr (io_sub _ h))]

end VG.Proof.Blowfish.AArch64
