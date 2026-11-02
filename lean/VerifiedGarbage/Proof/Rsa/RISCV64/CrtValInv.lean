module

public import VerifiedGarbage.Proof.Rsa.RISCV64.CrtValSetup
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyInv
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_crt_values` on RISC-V: the inverse, in the working space of the primes' words
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.CrtValues

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs mov)
open VG.Impl.Rsa.RISCV64.Keys (zeroArrays load orOne copy setOne sub3 aM aNM aZero)
open VG.Impl.Rsa.RISCV64.CrtValues (narrow widen invSetup nInv aOne)

/-- The primes' words. -/
abbrev wP (s0 : State) : Nat := (max (pL s0) (qL s0) + 7) / 8

/-- The branch-free maximum of `narrow`. -/
theorem max_sel (a b : BitVec 64) :
    (a - (a - b &&& 0 - if a < b then 1 else 0)) = BitVec.ofNat 64 (max a.toNat b.toNat) := by
  have ha := a.isLt
  have hb := b.isLt
  by_cases hab : a < b
  · have e : (0 : BitVec 64) - 1 = BitVec.allOnes 64 := by decide
    simp only [hab, ↓reduceIte, e, BitVec.and_allOnes]
    rw [BitVec.lt_def] at hab
    rw [Nat.max_eq_right (Nat.le_of_lt hab)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_arith
  · simp only [hab, ↓reduceIte, BitVec.sub_self, BitVec.and_zero, BitVec.sub_zero]
    rw [BitVec.lt_def] at hab
    rw [Nat.max_eq_left (Nat.le_of_not_lt hab), BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem shl2_add (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 64 a + BitVec.ofNat 64 b) <<< 2 = BitVec.ofNat 64 (4 * (a + b)) := by
  have := ha; have := hb
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq]
  omega_arith

theorem narrow_ok {s0 s : State} (h : PreC s0) (c : CB s0 s0.mem s) (h9 : s.gpr .s9 = BitVec.ofNat 64 (wOf s0)) :
    WP isa (.block narrow) s fun t =>
      (t.gpr .s0 = BitVec.ofNat 64 (wOf s0) ∧ t.gpr .s9 = BitVec.ofNat 64 (wP s0) ∧
        t.gpr .s10 = BitVec.ofNat 64 (S (wP s0)) ∧ t.gpr .s7 = BitVec.ofNat 64 (4 * (pL s0 + qL s0)) ∧
        t.mem = s.mem) ∧ Keep [.s0, .t6, .t5, .s9, .s10, .s7] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  have ⟨lp, lq⟩ := lt32 h
  have e4 : stackArg s0 1 = BitVec.ofNat 64 (pL s0) := toNat_ofNat_eq _
  have e6 : stackArg s0 3 = BitVec.ofNat 64 (qL s0) := toNat_ofNat_eq _
  have hm : max (pL s0) (qL s0) < 2 ^ 32 := by simp only [pL, qL]; omega_arith
  brun [narrow, mov, h9, c.s4, c.s6, fin64_exec_li_zero]
  refine ⟨BitVec.add_zero _, ?_, ?_, ?_⟩
  · rw [max_sel, add7_shr3 _ hm]
  · rw [max_sel, add7_shr3 _ hm, add2_shl3]
  · rw [e4, e6, shl2_add _ _ lp lq]

theorem widen_ok {s : State} {w : Nat} (h0 : s.gpr .s0 = BitVec.ofNat 64 w) :
    WP isa (.block widen) s fun t =>
      (t.gpr .s9 = BitVec.ofNat 64 w ∧ t.gpr .s10 = BitVec.ofNat 64 (S w) ∧ t.mem = s.mem) ∧
        Keep [.s9, .s10] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [widen, mov, h0, add2_shl3]
  exact BitVec.add_zero _

/-! ## The inverse's start -/

/-- `m = p | 1`. -/
abbrev Mv (s0 : State) : Nat := Pv s0 / 2 * 2 + 1

theorem PreC.wP_bounds {s0 : State} (h : PreC s0) :
    1 ≤ wP s0 ∧ wP s0 ≤ wOf s0 ∧ pL s0 ≤ 8 * wP s0 ∧ qL s0 ≤ 8 * wP s0 := by
  have := h.p1; have := h.p2; have := h.q1; have := h.q2
  simp only [wP, wOf, kOf, pL, qL]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega_arith

/-- The inverse's arrays after its start. -/
structure IS (s0 : State) (t : State) : Prop where
  n0 : num t.mem (bOf s0) (wP s0) 0 = Qv s0
  n1 : num t.mem (bOf s0) (wP s0) 1 = Mv s0
  n2 : num t.mem (bOf s0) (wP s0) 2 = 1
  n3 : num t.mem (bOf s0) (wP s0) 3 = 0
  nM : num t.mem (bOf s0) (wP s0) aM = Mv s0
  nNM : num t.mem (bOf s0) (wP s0) aNM + Mv s0 = 2 ^ (64 * wP s0)
  nZ : num t.mem (bOf s0) (wP s0) aZero = 0
  nOne : num t.mem (bOf s0) (wP s0) aOne = 1

theorem invSetup_ok {s0 s : State} (h : PreC s0) (c : CB s0 s0.mem s)
    (ws : Ws s (bOf s0) (zOf s0) (wP s0) nInv) :
    WP isa (seqs invSetup) s fun t => CB s0 s0.mem t ∧ Ws t (bOf s0) (zOf s0) (wP s0) nInv ∧
      Keys.Frame (bOf s0) (wP s0) (List.range nInv) [] s.mem t.mem ∧ IS s0 t ∧ Keep opRegs s t := by
  have ⟨b1, b2, b3, b4⟩ := h.wP_bounds
  have hz := h.zk
  have fitZ : ∀ j < nInv, arr (wP s0) j + S (wP s0) ≤ zOf s0 := fun j hj =>
    Nat.le_trans (arr_end hj) ws.fits
  have fit : ∀ j < nInv, arr (wP s0) j + S (wP s0) ≤ 2 ^ 64 := fun j hj => ws.fit64 hj
  have step : ∀ {u v : State} {js ds : List Nat}, CB s0 s0.mem u →
      Keys.Frame (bOf s0) (wP s0) js ds u.mem v.mem → (∀ j ∈ js, j < nInv) → (∀ d ∈ ds, 96 ≤ d ∧ d + 8 ≤ Keys.hdr) →
      ∀ {rs : List Reg}, Keep rs u v → (∀ r ∈ cbRegs, r ∉ rs) → CB s0 s0.mem v :=
    fun cu f hjs hds _ k hr => cu.of_frame f (fun j hj => fitZ j (hjs j hj)) hds
      (by simp only [hdr_eq, zOf] at hz ⊢; omega_arith) k hr
  have ⟨lp, lq⟩ := lt32 h
  unfold invSetup
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (zeroArrays_ok ws (by decide) (by decide) (by decide)) fun t1 ⟨w1, f1, z1, k1⟩ => ?_
  have c1 := step c f1 (fun j hj => List.mem_range.mp hj) (by simp) k1 (by decide)
  have z1' : ∀ j < nInv, num t1.mem (bOf s0) (wP s0) j = 0 := fun j hj =>
    wordsVal_zero_part (a := 0) (z1 j hj) (by omega_arith)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (load_ok w1 (j := 0) (by decide) (by decide) (by decide) c1.s5
    (by rw [c1.s6]; exact toNat_ofNat_eq _) h.q1 b4
    (fun i hi => by rw [c1.rd]; exact inRegions_left (bytes_in h.qR_rd (by have := h.wq; omega_arith) i hi))
    (bytes_sep h.qs (by have := h.wq; omega_arith)) (z1' 0 (by decide)))
    fun t2 ⟨w2, f2, v2, k2, _⟩ => ?_
  have c2 := step c1 f2 (by decide) (by simp) k2 (by decide)
  rw [c1.bytes h.qs (by have := h.wq; omega_arith)] at v2
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (load_ok w2 (j := aM) (by decide) (by decide) (by decide) c2.s3
    (by rw [c2.s4]; exact toNat_ofNat_eq _) h.p1 b3
    (fun i hi => by rw [c2.rd]; exact inRegions_left (bytes_in h.pR_rd (by have := h.wp; omega_arith) i hi))
    (bytes_sep h.ps (by have := h.wp; omega_arith))
    (by rw [f2.num (j := aM) (by decide) (by simp) (fit _ (by decide))]; exact z1' aM (by decide)))
    fun t3 ⟨w3, f3, v3, k3, _⟩ => ?_
  have c3 := step c2 f3 (by decide) (by simp) k3 (by decide)
  rw [c2.bytes h.ps (by have := h.wp; omega_arith)] at v3
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (orOne_ok w3 (j := aM) (by decide) (by decide)) fun t4 ⟨w4, f4, v4, k4⟩ => ?_
  have c4 := step c3 f4 (by decide) (by simp) k4 (by decide)
  rw [v3] at v4
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok w4 (o := 1) (a := aM) (by decide) (by decide) (by decide) (by decide))
    fun t5 ⟨w5, f5, v5, k5, _⟩ => ?_
  have c5 := step c4 f5 (by decide) (by simp) k5 (by decide)
  rw [v4] at v5
  rw [wp_seqs_cons (List.cons_ne_nil _ _), WP.block_append_iff]
  refine WP.mono (setOne_ok w5 (j := 2) (by decide) (by decide)) fun t6 ⟨w6, f6, v6, k6⟩ => ?_
  have c6 := step c5 f6 (by decide) (by simp) k6 (by decide)
  refine WP.mono (setOne_ok w6 (j := aOne) (by decide) (by decide)) fun t7 ⟨w7, f7, v7, k7⟩ => ?_
  have c7 := step c6 f7 (by decide) (by simp) k7 (by decide)
  refine WP.mono (sub3_ok w7 (o := aNM) (a := aZero) (b := aM) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun t ⟨w8, f8, v8, b8, k8⟩ => ?_
  have c8 := step c7 f8 (by decide) (by simp) k8 (by decide)
  -- The values, through the frames.
  have z5 : ∀ j < nInv, j ≠ 0 → j ≠ aM → j ≠ 1 → num t5.mem (bOf s0) (wP s0) j = 0 := fun j hj a0 aM' a1 => by
    rw [f5.num (fun _ hk => by rw [List.mem_singleton.mp hk]; exact Ne.symm a1) (by simp) (fit _ hj),
      f4.num (fun _ hk => by rw [List.mem_singleton.mp hk]; exact Ne.symm aM') (by simp) (fit _ hj),
      f3.num (fun _ hk => by rw [List.mem_singleton.mp hk]; exact Ne.symm aM') (by simp) (fit _ hj),
      f2.num (fun _ hk => by rw [List.mem_singleton.mp hk]; exact Ne.symm a0) (by simp) (fit _ hj), z1' j hj]
  have M5 : num t5.mem (bOf s0) (wP s0) aM = Mv s0 := by
    rw [f5.num (j := aM) (by decide) (by simp) (fit _ (by decide)), v4]
  have M7 : num t7.mem (bOf s0) (wP s0) aM = Mv s0 := by
    rw [f7.num (j := aM) (by decide) (by simp) (fit _ (by decide)),
      f6.num (j := aM) (by decide) (by simp) (fit _ (by decide)), M5]
  have Z7 : num t7.mem (bOf s0) (wP s0) aZero = 0 := by
    rw [f7.num (j := aZero) (by decide) (by simp) (fit _ (by decide)),
      f6.num (j := aZero) (by decide) (by simp) (fit _ (by decide))]
    exact z5 aZero (by decide) (by decide) (by decide) (by decide)
  rw [M7, Z7, Nat.zero_add] at v8
  have hM : 0 < Mv s0 := Nat.succ_pos _
  have hb8 : (t.gpr .t4).toNat = 1 := by
    have := wordsVal_lt t.mem (bOf s0) (arr (wP s0) aNM) (wP s0)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b8 with e | e
    · rw [e] at v8; simp only [Nat.mul_zero] at v8; omega_arith
    · exact e
  rw [hb8, Nat.mul_one] at v8
  have R : ∀ {m m' : Mem} {js : List Nat}, Keys.Frame (bOf s0) (wP s0) js [] m m' → (∀ j ∈ js, j < nInv) →
      Keys.Frame (bOf s0) (wP s0) (List.range nInv) [] m m' :=
    fun f hj => f.mono (fun j h => List.mem_range.mpr (hj j h)) (by simp)
  refine ⟨c8, w8, f1.trans ((R f2 (by decide)).trans ((R f3 (by decide)).trans ((R f4 (by decide)).trans
    ((R f5 (by decide)).trans ((R f6 (by decide)).trans ((R f7 (by decide)).trans (R f8 (by decide)))))))), ⟨?_, ?_, ?_, ?_, ?_, v8, ?_, ?_⟩,
    Keep.trans' k1 (Keep.trans' (Keep.mono k2 (by decide)) (Keep.trans' (Keep.mono k3 (by decide))
      (Keep.trans' k4 (Keep.trans' k5 (Keep.trans' k6 (Keep.trans' k7 k8))))))⟩
  · rw [f8.num (j := 0) (by decide) (by simp) (fit _ (by decide)), f7.num (j := 0) (by decide) (by simp) (fit _ (by decide)),
      f6.num (j := 0) (by decide) (by simp) (fit _ (by decide)), f5.num (j := 0) (by decide) (by simp) (fit _ (by decide)),
      f4.num (j := 0) (by decide) (by simp) (fit _ (by decide)), f3.num (j := 0) (by decide) (by simp) (fit _ (by decide)), v2]
  · rw [f8.num (j := 1) (by decide) (by simp) (fit _ (by decide)), f7.num (j := 1) (by decide) (by simp) (fit _ (by decide)),
      f6.num (j := 1) (by decide) (by simp) (fit _ (by decide)), v5]
  · rw [f8.num (j := 2) (by decide) (by simp) (fit _ (by decide)), f7.num (j := 2) (by decide) (by simp) (fit _ (by decide)),
      v6, z5 2 (by decide) (by decide) (by decide) (by decide)]
  · rw [f8.num (j := 3) (by decide) (by simp) (fit _ (by decide)), f7.num (j := 3) (by decide) (by simp) (fit _ (by decide)),
      f6.num (j := 3) (by decide) (by simp) (fit _ (by decide)), z5 3 (by decide) (by decide) (by decide) (by decide)]
  · rw [f8.num (j := aM) (by decide) (by simp) (fit _ (by decide)), M7]
  · rw [f8.num (j := aZero) (by decide) (by simp) (fit _ (by decide)), Z7]
  · rw [f8.num (j := aOne) (by decide) (by simp) (fit _ (by decide)), v7,
      f6.num (j := aOne) (by decide) (by simp) (fit _ (by decide)),
      z5 aOne (by decide) (by decide) (by decide) (by decide)]

end VG.Proof.Rsa.RISCV64.CrtValues
