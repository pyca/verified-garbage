module

public import VerifiedGarbage.Impl.Cast5.AArch64.Tbl
public import VerifiedGarbage.Proof.Blowfish.AArch64.Sbox
public import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
import VerifiedGarbage.Proof.Blowfish.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint

/-!
# CAST5 on AArch64: S-box lookups by `tbl`

As Blowfish's (`Proof/Blowfish/AArch64/Sbox.lean`), with the planes in the
table of constants the loads carry (`ldrqTbl`) rather than in memory.

`quarter_run`: four loads of quarter `q` of byte plane `b` of S-box `j` into
`v28`–`v31`, then a `tbl` (for `q = 0`) or `tbx` of them, leave in each byte
lane of the destination the plane's byte at the lane's index, if it is in
the quarter (below 64), and otherwise 0 (`tbl`) or the destination's byte
(`tbx`). `lookupPlane_run`: the four quarters, on the index XORed with 0, 64,
128 and 192, leave the plane's byte at the index. `lookup_run`: `lookup j`
leaves in `outReg b` byte `b` of S-box `j` at the indices in `idxReg j`.
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64.Tbl

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Cast5.AArch64.Tbl
open VG.Impl.Blowfish.AArch64 (aReg bReg fReg idxReg outReg qReg tReg c64 c128 veor vperm planeOff)
open VG.AArch64.Tbl (VOnly)
open VG.Proof.Blowfish.AArch64 (vbyte_xor tbx_chain regs_ne repeat_succ_v28 exec_tbl4 Consts lookupRegs
  VOnly.mono q_notin idx_notin out_notin idx_ne_q123 plane_sub)

/-! ## The table -/

theorem planeWords_length : planeWords.length = 512 := by
  simp only [planeWords, List.length_map, List.length_range]

theorem planeWords_getD (i : Nat) (hi : i < 512) :
    planeWords.getD i 0 = (planeVec (i / 2)).extractLsb' (64 * (i % 2)) 64 := by
  simp only [planeWords, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]

/-- A load of the table's sixteen bytes at `off`. -/
theorem exec_pld (s : State) (t : VReg) {off : Nat} (ho : off % 16 = 0 ∧ off + 16 ≤ 4096)
    (h9 : s.gpr .x9 = s.syms planesSym) :
    exec (.ldrqTbl t .x9 off planesSym planeWords) s = some (s.setV t (planeVec (off / 16))) := by
  have hc : s.gpr .x9 = s.syms planesSym ∧ off % 16 = 0 ∧ off < 65536 ∧ off / 8 + 2 ≤ planeWords.length := by
    rw [planeWords_length]; exact ⟨h9, ho.1, by omega_using [ho], by omega_using [ho]⟩
  have hv : planeWords.getD (off / 8 + 1) 0 ++ planeWords.getD (off / 8) 0 = planeVec (off / 16) := by
    rw [planeWords_getD _ (by omega_using [ho]), planeWords_getD _ (by omega_using [ho]),
      show (off / 8 + 1) / 2 = off / 16 by omega_using [ho], show (off / 8 + 1) % 2 = 1 by omega_using [ho],
      show off / 8 / 2 = off / 16 by omega_using [], show off / 8 % 2 = 0 by omega_using [ho]]
    exact VG.AArch64.Tbl.ofVDwords_halves (planeVec (off / 16))
  change (if _ then _ else _) = _
  rw [ite_eq_left hc, hv]

theorem vbyte_planeVec (r : Nat) {e : Nat} (he : e < 16) : vbyte (planeVec r) e = planeByte (16 * r + e) := by
  rw [planeVec, vbyte_ofVBytes _ he]

/-- Byte `b` of S-box `j` at `x`. -/
theorem planeByte_eq {j b : Nat} (hj : j < 4) (hb : b < 4) (x : Byte) :
    planeByte (planeOff j b + x.toNat) = (sbox j x).extractLsb' (8 * b) 8 := by
  have hx := x.isLt
  have e1 : (planeOff j b + x.toNat) / 1024 = j := by simp only [planeOff]; omega_arith
  have e2 : (planeOff j b + x.toNat) / 256 % 4 = b := by simp only [planeOff]; omega_arith
  have e3 : BitVec.ofNat 8 (planeOff j b + x.toNat) = x := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]; simp only [planeOff]; omega_arith
  rw [planeByte, e1, e2, e3]

/-! ## A quarter -/

theorem loadQuarter_eq (j b q : Nat) :
    loadQuarter j b q =
      [.ldrqTbl .v28 .x9 (planeOff j b + 64 * q + 16 * 0) planesSym planeWords,
       .ldrqTbl .v29 .x9 (planeOff j b + 64 * q + 16 * 1) planesSym planeWords,
       .ldrqTbl .v30 .x9 (planeOff j b + 64 * q + 16 * 2) planesSym planeWords,
       .ldrqTbl .v31 .x9 (planeOff j b + 64 * q + 16 * 3) planesSym planeWords] :=
  rfl

theorem quarter_run {s : State} (h9 : s.gpr .x9 = s.syms planesSym) {j b q : Nat} (hj : j < 4)
    (hb : b < 4) (hq : q < 4) {d m : VReg} (hd : ∀ r < 4, d ≠ tReg r) (hm : ∀ r < 4, m ≠ tReg r) :
    ∃ s', runBlock isa (loadQuarter j b q ++ ([.vop (.tblN (q != 0) 4 d (tReg 0) m)] : List Instr)) s = some s' ∧
      (∀ e < 16, vbyte (s'.v d) e =
        if (vbyte (s.v m) e).toNat < 64 then
          planeByte (planeOff j b + 64 * q + (vbyte (s.v m) e).toNat)
        else if q != 0 then vbyte (s.v d) e else 0) ∧
      VOnly [.v28, .v29, .v30, .v31, d] s s' := by
  let base := planeOff j b + 64 * q
  have hbase : base % 16 = 0 ∧ base + 64 ≤ 4096 := by simp only [base, planeOff]; omega_arith
  let ld (r : Nat) := planeVec ((base + 16 * r) / 16)
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
  have ho : ∀ r < 4, (base + 16 * r) % 16 = 0 ∧ base + 16 * r + 16 ≤ 4096 := fun r hr => by
    omega_using [hbase, hr]
  refine ⟨s₅, ?_, ?_, ?_⟩
  · have e₁ : exec (.ldrqTbl .v28 .x9 (planeOff j b + 64 * q + 16 * 0) planesSym planeWords) s = some s₁ :=
      exec_pld s _ (ho 0 (by decide)) h9
    have e₂ : exec (.ldrqTbl .v29 .x9 (planeOff j b + 64 * q + 16 * 1) planesSym planeWords) s₁ = some s₂ :=
      exec_pld s₁ _ (ho 1 (by decide)) h9
    have e₃ : exec (.ldrqTbl .v30 .x9 (planeOff j b + 64 * q + 16 * 2) planesSym planeWords) s₂ = some s₃ :=
      exec_pld s₂ _ (ho 2 (by decide)) h9
    have e₄ : exec (.ldrqTbl .v31 .x9 (planeOff j b + 64 * q + 16 * 3) planesSym planeWords) s₃ = some s₄ :=
      exec_pld s₃ _ (ho 3 (by decide)) h9
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
      rw [tableByte, repeat_succ_v28 _ (by omega_arith), hv _ (by omega_arith), vbyte_planeVec _ (by omega_arith)]
      exact congrArg planeByte (by omega_using [hbase, h])
    · rfl
  · refine ((((VOnly.setV s (by simp) _).trans (VOnly.setV _ (by simp) _)).trans
      (VOnly.setV _ (by simp) _)).trans (VOnly.setV _ (by simp) _)).trans (VOnly.setV _ (by simp) _)

/-! ## A byte plane -/

theorem lookupPlane_eq (j b : Nat) :
    lookupPlane j b =
      (loadQuarter j b 0 ++ ([.vop (.tblN (0 != 0) 4 (outReg b) (tReg 0) (idxReg j))] : List Instr)) ++
      ((loadQuarter j b 1 ++ ([.vop (.tblN (1 != 0) 4 (outReg b) (tReg 0) (qReg 1))] : List Instr)) ++
      ((loadQuarter j b 2 ++ ([.vop (.tblN (2 != 0) 4 (outReg b) (tReg 0) (qReg 2))] : List Instr)) ++
      ((loadQuarter j b 3 ++ ([.vop (.tblN (3 != 0) 4 (outReg b) (tReg 0) (qReg 3))] : List Instr)) ++ []))) :=
  rfl

/-- Byte plane `b` of S-box `j`, at the indices in `idxReg j` (and them
XORed with 64, 128 and 192 in `qReg`). -/
theorem lookupPlane_run {s : State} (h9 : s.gpr .x9 = s.syms planesSym) {j b : Nat} (hj : j < 4)
    (hb : b < 4) (hq : ∀ q < 4, 0 < q → ∀ e < 16,
      vbyte (s.v (qReg q)) e = vbyte (s.v (idxReg j)) e ^^^ BitVec.ofNat 8 (64 * q)) :
    ∃ s', runBlock isa (lookupPlane j b) s = some s' ∧
      (∀ e < 16, vbyte (s'.v (outReg b)) e = planeByte (planeOff j b + (vbyte (s.v (idxReg j)) e).toNat)) ∧
      VOnly [.v28, .v29, .v30, .v31, outReg b] s s' := by
  have ne := regs_ne j hj b hb
  have hd : ∀ r < 4, outReg b ≠ tReg r := fun r hr => (ne 0 (by decide) r hr).1
  have h9' : ∀ {t : State}, VOnly [.v28, .v29, .v30, .v31, outReg b] s t → t.gpr .x9 = t.syms planesSym := by
    intro t ht
    rw [ht.gpr, ht.1]; exact h9
  obtain ⟨s₁, r₁, v₁, o₁⟩ := quarter_run h9 hj hb (by decide : 0 < 4) hd (fun r hr => (ne 0 (by decide) r hr).2.1)
  obtain ⟨s₂, r₂, v₂, o₂⟩ := quarter_run (h9' o₁) hj hb (by decide : 1 < 4) hd
    (fun r hr => (ne 1 (by decide) r hr).2.2.1)
  have o₁₂ := o₁.trans o₂
  obtain ⟨s₃, r₃, v₃, o₃⟩ := quarter_run (h9' o₁₂) hj hb (by decide : 2 < 4) hd
    (fun r hr => (ne 2 (by decide) r hr).2.2.1)
  have o₁₃ := o₁₂.trans o₃
  obtain ⟨s₄, r₄, v₄, o₄⟩ := quarter_run (h9' o₁₃) hj hb (by decide : 3 < 4) hd
    (fun r hr => (ne 3 (by decide) r hr).2.2.1)
  have o₁₄ := o₁₃.trans o₄
  refine ⟨s₄, ?_, ?_, o₁₄⟩
  · rw [lookupPlane_eq]
    exact VG.AArch64.Tbl.runBlock_cat_some r₁ (VG.AArch64.Tbl.runBlock_cat_some r₂
      (VG.AArch64.Tbl.runBlock_cat_some r₃ (VG.AArch64.Tbl.runBlock_cat_some r₄ runBlock_nil)))
  · intro e he
    have kept : ∀ {t : State} (x : VReg), VOnly [.v28, .v29, .v30, .v31, outReg b] s t →
        (∀ r < 4, x ≠ tReg r) → x ≠ outReg b → t.v x = s.v x := by
      intro t x ht hx hxo
      refine ht.2 x ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      have := hx 0 (by decide); have := hx 1 (by decide); have := hx 2 (by decide)
      have := hx 3 (by decide)
      rintro (h | h | h | h | h) <;> contradiction
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
      v₂ e he, q₁, hxq 1 (by decide) (by decide), v₁ e he]
    simp only [show (3 != 0) = true from rfl, show (2 != 0) = true from rfl,
      show (1 != 0) = true from rfl, show (0 != 0) = false from rfl, ite_true, Bool.false_eq_true,
      ite_false]
    have := tbx_chain (fun i => planeByte (planeOff j b + i)) X.toNat hX
    simp only [Nat.add_assoc]
    exact this

/-! ## An S-box -/

theorem lookup_run {s : State} (h9 : s.gpr .x9 = s.syms planesSym) (hc : Consts s) {j : Nat} (hj : j < 4) :
    ∃ s', runBlock isa (lookup j) s = some s' ∧
      (∀ b < 4, ∀ e < 16, vbyte (s'.v (outReg b)) e =
        (sbox j (vbyte (s.v (idxReg j)) e)).extractLsb' (8 * b) 8) ∧
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
  have h9₃ : ∀ {t : State}, VOnly lookupRegs s t → t.gpr .x9 = t.syms planesSym := by
    intro t ht
    rw [ht.gpr, ht.1]; exact h9
  have step : ∀ {t : State} (b : Nat), b < 4 → VOnly lookupRegs s t →
      (∀ q < 4, 0 < q → ∀ e < 16,
        vbyte (t.v (qReg q)) e = vbyte (t.v (idxReg j)) e ^^^ BitVec.ofNat 8 (64 * q)) →
      ∃ t', runBlock isa (lookupPlane j b) t = some t' ∧
        (∀ e < 16, vbyte (t'.v (outReg b)) e = planeByte (planeOff j b + (vbyte (t.v (idxReg j)) e).toNat)) ∧
        VOnly [.v28, .v29, .v30, .v31, outReg b] t t' := by
    intro t b hb ht hqt
    exact lookupPlane_run (h9₃ ht) hj hb hqt
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
    have l : lookup j = [veor (qReg 1) (idxReg j) c64, veor (qReg 2) (idxReg j) c128,
        veor (qReg 3) (qReg 1) c128] ++ (lookupPlane j 0 ++ (lookupPlane j 1 ++
        (lookupPlane j 2 ++ (lookupPlane j 3 ++ [])))) := rfl
    rw [l, List.cons_append, List.cons_append, List.cons_append, List.nil_append, runBlock_cons, e₁,
      runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃, runStep_some]
    exact VG.AArch64.Tbl.runBlock_cat_some r₀ (VG.AArch64.Tbl.runBlock_cat_some r₁
      (VG.AArch64.Tbl.runBlock_cat_some r₂ (VG.AArch64.Tbl.runBlock_cat_some r₃ runBlock_nil)))
  · have i₀ : t₀.v (idxReg j) = s.v (idxReg j) := (o₀.2 _ (ni 0 (by decide))).trans X
    have i₁ : t₁.v (idxReg j) = s.v (idxReg j) := (o₁.2 _ (ni 1 (by decide))).trans i₀
    have i₂ : t₂.v (idxReg j) = s.v (idxReg j) := (o₂.2 _ (ni 2 (by decide))).trans i₁
    intro b hb e he
    have nob := out_notin
    rw [← planeByte_eq hj hb]
    rcases (by omega_using [hb] : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl
    · rw [o₃'.2 _ (nob 0 (by decide) 3 (by decide) (by decide)), o₂.2 _ (nob 0 (by decide) 2 (by decide) (by decide)),
        o₁.2 _ (nob 0 (by decide) 1 (by decide) (by decide)), v₀ e he, X]
    · rw [o₃'.2 _ (nob 1 (by decide) 3 (by decide) (by decide)), o₂.2 _ (nob 1 (by decide) 2 (by decide) (by decide)),
        v₁ e he, i₀]
    · rw [o₃'.2 _ (nob 2 (by decide) 3 (by decide) (by decide)), v₂ e he, i₁]
    · rw [v₃ e he, i₂]

end VG.Proof.Cast5.AArch64.Tbl
