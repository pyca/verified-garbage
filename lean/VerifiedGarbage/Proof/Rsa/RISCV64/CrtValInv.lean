module

public import VerifiedGarbage.Proof.Rsa.RISCV64.CrtValSetup
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyInv
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_crt_values` on RISC-V: the inverse, in the working space of the primes' words
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.CrtValues

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs mov)
open VG.Impl.Rsa.RISCV64.Keys (zeroArrays load orOne copy setOne sub3 aM aNM aZero inverse eqS sOdd sB sC)
open VG.Impl.Rsa.RISCV64.Keys (andS)
open VG.Impl.Rsa.RISCV64.CrtValues (narrow widen invSetup nInv aOne sE3 sPodd sE1 sE2 sMask mask)

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

/-! ## The inverse and the gcd's check -/

theorem Mv_lt (s0 : State) : Mv s0 < 2 ^ (8 * pL s0) ∨ pL s0 = 0 := by
  rcases Nat.eq_zero_or_pos (pL s0) with e | e
  · exact .inr e
  · left
    have hp := os2ip_bytes_lt s0.mem (stackArg s0 0) (pL s0)
    have e2 : 2 ^ (8 * pL s0) = 2 * 2 ^ (8 * pL s0 - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega_arith
    rw [e2] at hp ⊢
    simp only [Mv, Pv, pB]
    omega_arith

theorem QM_lt {s0 : State} (h : PreC s0) : Qv s0 * Mv s0 < 2 ^ (2 * (4 * (pL s0 + qL s0))) := by
  have hq := os2ip_bytes_lt s0.mem (stackArg s0 2) (qL s0)
  have hm := (Mv_lt s0).resolve_right (by have := h.p1; simp only [pL]; omega_arith)
  have e : 2 ^ (2 * (4 * (pL s0 + qL s0))) = 2 ^ (8 * qL s0) * 2 ^ (8 * pL s0) := by
    rw [← Nat.pow_add]; congr 1; omega_arith
  rw [e]
  exact Nat.mul_lt_mul'' hq hm

/-- After the inverse: `V` the gcd and `X` the inverse it found. -/
structure IC (s0 : State) (V X : Nat) : Prop where
  vx : 1 < Mv s0 → V = Nat.gcd (Qv s0) (Mv s0) ∧ (Mv s0 : Int) ∣ (X : Int) * Qv s0 - V ∧ X < Mv s0

/-- The arrays and slots the inverse's phase writes. -/
abbrev invDs : List Nat := [sOdd, sB, sC, sE3]

theorem invCore_ok {s0 s : State} (h : PreC s0) (c : CB s0 s0.mem s)
    (ws : Ws s (bOf s0) (zOf s0) (wP s0) nInv) (is : IS s0 s)
    (h7 : s.gpr .s7 = BitVec.ofNat 64 (4 * (pL s0 + qL s0))) :
    WP isa (.seq inverse (eqS sE3 1 aOne)) s fun t => CB s0 s0.mem t ∧ Ws t (bOf s0) (zOf s0) (wP s0) nInv ∧
      Keys.Frame (bOf s0) (wP s0) (List.range nInv) invDs s.mem t.mem ∧
      IC s0 (num t.mem (bOf s0) (wP s0) 1) (num t.mem (bOf s0) (wP s0) 3) ∧
      slot t.mem (bOf s0) sE3 = (if num t.mem (bOf s0) (wP s0) 1 = 1 then 1 else 0) ∧
      Keep (.s7 :: opRegs) s t := by
  have hz := h.zk
  have hp1 := h.p1
  have hq1 := h.q1
  have ⟨lp, lq⟩ := lt32 h
  have fitZ : ∀ j < nInv, arr (wP s0) j + S (wP s0) ≤ zOf s0 := fun j hj =>
    Nat.le_trans (arr_end hj) ws.fits
  have fit : ∀ j < nInv, arr (wP s0) j + S (wP s0) ≤ 2 ^ 64 := fun j hj => ws.fit64 hj
  rw [WP.seq_iff]
  refine WP.mono (inverse_ok ws (by decide) (by decide) h7 (by simp only [pL]; omega_arith)
    (by simp only [pL, qL]; omega_arith)) fun t1 ⟨w1, f1, k1, v1⟩ => ?_
  have c1 := c.of_frame f1 (fun j hj => fitZ j (by revert j hj; decide)) (by decide)
    (by simp only [hdr_eq, zOf] at hz ⊢; omega_arith) k1 (by decide)
  have hodd : Mv s0 % 2 = 1 := by simp only [Mv]; omega_arith
  have D := fun h1M => inverse_done (t := t1.mem) (K := 4 * (pL s0 + qL s0))
    (by rw [is.nM]; exact hodd) (by rw [is.nM]; exact h1M) (by rw [is.n0, is.nM]; exact QM_lt h)
    (by simp only [bank, is.n0, is.n1, is.n2, is.n3, is.nM]) (v1 (by rw [is.nM]; exact is.nNM)
      is.nZ (by rw [is.nM]; exact hodd) (by rw [is.nM]; exact h1M)
      (by simp only [bank, is.n0, is.n1, is.n2, is.n3, is.nM]))
  rw [is.n0, is.nM] at D
  refine WP.mono (eqS_ok w1 (d := sE3) (a := 1) (b := aOne) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun t ⟨w2, f2, v2, k2⟩ => ?_
  have c2 := c1.of_frame f2 (by simp) (by decide) (by simp only [hdr_eq, zOf] at hz ⊢; omega_arith) k2 (by decide)
  have o1 : num t1.mem (bOf s0) (wP s0) aOne = 1 := by
    rw [f1.num (j := aOne) (by decide) (by decide) (fit _ (by decide)), is.nOne]
  have n1 : num t.mem (bOf s0) (wP s0) 1 = num t1.mem (bOf s0) (wP s0) 1 :=
    f2.num (j := 1) (by simp) (by decide) (fit _ (by decide))
  have n3 : num t.mem (bOf s0) (wP s0) 3 = num t1.mem (bOf s0) (wP s0) 3 :=
    f2.num (j := 3) (by simp) (by decide) (fit _ (by decide))
  refine ⟨c2, w2, (f1.mono (fun j hj => List.mem_range.mpr (by revert j hj; decide)) (by decide)).trans
      (f2.mono (by simp) (by decide)), ⟨fun h1M => by rw [n1, n3]; exact D h1M⟩, by rw [v2, o1, n1],
    Keep.trans' k1 (Keep.mono k2 (by decide))⟩

/-! ## Back to the working space of `w` words -/

/-- An array from 16 on of the working space of `w` words, past the narrowed one's 16 arrays. -/
theorem wide_words {B : Addr} {w w' : Nat} {ds : List Nat} {m m' : Mem}
    (f : Keys.Frame B w' (List.range nInv) ds m m') (hw : w' ≤ w) (hds : ∀ d ∈ ds, d + 8 ≤ Keys.hdr)
    {j k : Nat} (hj : nInv ≤ j) (hk : k ≤ w + 2) (fit : arr w j + S w ≤ 2 ^ 64) :
    wordsVal m' B (arr w j) k = wordsVal m B (arr w j) k := by
  refine f.words (fun j' hj' => .inr ?_) (fun d hd => .inr ?_) (by simp only [S] at fit; omega_arith)
  · have := List.mem_range.mp hj'
    have e1 := arr_end (w := w') this
    have e2 : arr w' nInv ≤ arr w nInv := by simp only [arr, S]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega_arith)) _
    have e3 := arr_mono (w := w) hj
    omega_arith
  · have := hds d hd; have := hdr_le_arr w j; omega_arith

/-- A slot, past a frame of arrays. -/
theorem slot_of_arrs {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (f : Keys.Frame B w js [] m m') {e : Nat}
    (he : e + 8 ≤ Keys.hdr) : slot m' B e = slot m B e := f.slot he (by simp)

/-- Words of the working space, past a write apart from it. -/
theorem wordsVal_of_out {O B : Addr} {L Z : Nat} {m m' : Mem} (hd : (⟨O, L⟩ : Region).Disjoint ⟨B, Z⟩)
    (ho : Outside O 0 L m m') {d k : Nat} (hdk : d + 8 * k ≤ Z) (hZ : Z < 2 ^ 64) :
    wordsVal m' B d k = wordsVal m B d k := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
    simp only [wordsVal]
    have hw : word m' B d = word m B d := Mem.readW_congr fun i hi => by
      refine out_of_scr hd ho ?_
      rw [off_add]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)
    rw [hw, ih (by omega_arith)]

/-! ## The mask -/

theorem mask_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) (bit : slot s.mem B sMask ≤ 1) :
    WP isa (.block mask) s fun t =>
      (t.gpr .t4 = (if decide (slot s.mem B sMask ≠ 0) then BitVec.allOnes 64 else 0) ∧ t.mem = s.mem) ∧
        Keep [.t4, .t5] s t := by
  have hz := h.hdr_le
  have nw := h.nowrap
  refine WP.keep _ ?_ (by rfl) (by rfl)
  have hz' : sMask + 8 ≤ Z := by simp only [hdr_eq, sMask] at hz ⊢; omega_arith
  brun [mask, h.s11, fin64_exec_li_zero, add_ofNat_zero', h.scr.al8 (d := sMask) (by omega_arith) (by decide),
    h.scr.ld (d := sMask) (n := 8) hz', show sMask < 2048 by decide]
  exact mask_of_slot _ bit

theorem mul_le_one' {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 :=
  Nat.le_trans (Nat.mul_le_mul ha hb) (by decide)

theorem bit_ite {c : Prop} [Decidable c] : (if c then 1 else 0 : Nat) ≤ 1 := by split <;> decide

/-- The checks and'ed into `sMask`, and its mask in `t4`. -/
theorem maskBlk_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N)
    (b1 : slot s.mem B sPodd ≤ 1) (b2 : slot s.mem B sE1 ≤ 1) (b3 : slot s.mem B sE2 ≤ 1)
    (b4 : slot s.mem B sE3 ≤ 1) :
    WP isa (.block (andS sMask sPodd sE1 ++ andS sMask sMask sE2 ++ andS sMask sMask sE3 ++ mask)) s fun t =>
      Ws t B Z w N ∧ Keys.Frame B w [] [sMask] s.mem t.mem ∧
      slot t.mem B sMask = slot s.mem B sPodd * slot s.mem B sE1 * slot s.mem B sE2 * slot s.mem B sE3 ∧
      t.gpr .t4 = (if decide (slot t.mem B sMask ≠ 0) then BitVec.allOnes 64 else 0) ∧ Keep opRegs s t := by
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (andS_ok h (d := sMask) (a := sPodd) (b := sE1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) b1 b2) fun t1 ⟨w1, f1, v1, k1⟩ => ?_
  rw [WP.block_append_iff]
  have e2 : slot t1.mem B sE2 = slot s.mem B sE2 := f1.slot (by decide) (by decide)
  have e3 : slot t1.mem B sE3 = slot s.mem B sE3 := f1.slot (by decide) (by decide)
  refine WP.mono (andS_ok w1 (d := sMask) (a := sMask) (b := sE2) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [v1]; exact mul_le_one' b1 b2) (by rw [e2]; exact b3))
    fun t2 ⟨w2, f2, v2, k2⟩ => ?_
  rw [WP.block_append_iff]
  have e3' : slot t2.mem B sE3 = slot s.mem B sE3 := by rw [f2.slot (by decide) (by decide), e3]
  refine WP.mono (andS_ok w2 (d := sMask) (a := sMask) (b := sE3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [v2, v1, e2]; exact mul_le_one' (mul_le_one' b1 b2) b3)
    (by rw [e3']; exact b4)) fun t3 ⟨w3, f3, v3, k3⟩ => ?_
  have V : slot t3.mem B sMask = slot s.mem B sPodd * slot s.mem B sE1 * slot s.mem B sE2 * slot s.mem B sE3 := by
    rw [v3, v2, v1, e2, e3']
  refine WP.mono (mask_ok w3 (by rw [V]; exact mul_le_one' (mul_le_one' (mul_le_one' b1 b2) b3) b4))
    fun t ⟨⟨u4, um⟩, k4⟩ => ?_
  rw [← um] at V u4
  exact ⟨w3.of_keep k4, by rw [um]; exact (f1.trans f2).trans f3, V, u4,
    Keep.trans' k1 (Keep.trans' k2 (Keep.trans' k3 (Keep.mono k4 (by decide))))⟩

end VG.Proof.Rsa.RISCV64.CrtValues
