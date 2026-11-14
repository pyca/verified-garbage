module

public import VerifiedGarbage.Proof.Rsa.RISCV64.CrtValSetup
public import VerifiedGarbage.Proof.Rsa.RISCV64.InvLaw
public import VerifiedGarbage.Proof.Rsa.RISCV64.CrtValTail
public import VerifiedGarbage.Proof.Rsa.CrtValuesMask
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_crt_values` on RISC-V: the inverse

`nCalc_ok`: the primes' digits `nP = ⌈max(p_len, q_len) / 4⌉` into `s8`;
`invSetup_ok`: the inverse's start (`IS`); `invCore_ok`: the batched inverse
(`Proof/Rsa/RISCV64/IbInverse.lean`) and the gcd's check (`IC`);
`maskBlk_ok`: the checks' mask. `invPart_ok`: from the checks of `p q = n`
(`Ck`), the whole phase: the mask of every check in `sMask` and `qInv`
written under it, the arrays from 16 on as they were (`Iv`).
-/

-- separate module: its proofs (the inverse and `invPart_ok`) are not re-checked with every change to the
-- divisions', the stores' or the constant-time proofs

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.CrtValues

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs mov)
open VG.Impl.Rsa.RISCV64.Keys (orOne copy setOne eqS sOdd sB sC)
open VG.Impl.Rsa.RISCV64.Keys (andS)
open VG.Impl.Rsa.RISCV64.CrtValues (nCalc invSetup invG nArr aOne aP aQ aDQ aDR sE3 sPodd sE1 sE2 sMask mask
  restoreK)

/-- The primes' digits. -/
abbrev nP (s0 : State) : Nat := (max (pL s0) (qL s0) + 3) / 4

/-- The branch-free maximum of `nCalc`. -/
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

theorem add3_shr2 (k : Nat) (hk : k < 2 ^ 32) :
    (BitVec.ofNat 64 k + BitVec.ofNat 64 3) >>> 2 = BitVec.ofNat 64 ((k + 3) / 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (a := k) (by omega_arith), Nat.mod_eq_of_lt (a := 3) (by decide),
    Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

theorem nCalc_ok {s0 s : State} (h : PreC s0) (c : CB s0 s0.mem s) :
    WP isa (.block nCalc) s fun t => (t.gpr .s8 = BitVec.ofNat 64 (nP s0) ∧ t.mem = s.mem) ∧
      Keep [.t6, .t5, .s8] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  have ⟨lp, lq⟩ := lt32 h
  have e4 : stackArg s0 1 = BitVec.ofNat 64 (pL s0) := toNat_ofNat_eq _
  have e6 : stackArg s0 3 = BitVec.ofNat 64 (qL s0) := toNat_ofNat_eq _
  have hm : max (pL s0) (qL s0) < 2 ^ 32 := by simp only [pL, qL]; omega_arith
  brun [nCalc, c.s4, c.s6, fin64_exec_li_zero]
  rw [max_sel, add3_shr2 _ hm]

/-! ## The inverse's start -/

/-- `m = p | 1`. -/
abbrev Mv (s0 : State) : Nat := Pv s0 / 2 * 2 + 1

theorem PreC.nP_bounds {s0 : State} (h : PreC s0) :
    1 ≤ nP s0 ∧ nP s0 ≤ 2 * wOf s0 ∧ pL s0 ≤ 4 * nP s0 ∧ qL s0 ≤ 4 * nP s0 := by
  have := h.p1; have := h.p2; have := h.q1; have := h.q2
  simp only [nP, wOf, kOf, pL, qL]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega_arith

/-- The inverse's arrays after its start. -/
structure IS (s0 : State) (t : State) : Prop where
  nx : num t.mem (bOf s0) (wOf s0) Impl.Rsa.RISCV64.InvBatch.aX = Qv s0
  nm : num t.mem (bOf s0) (wOf s0) Impl.Rsa.RISCV64.InvBatch.aMin = Mv s0
  nOne : num t.mem (bOf s0) (wOf s0) aOne = 1
  s8 : t.gpr .s8 = BitVec.ofNat 64 (nP s0)

/-- The arrays `invSetup` writes. -/
abbrev setupArrs : List Nat := [Impl.Rsa.RISCV64.InvBatch.aX, Impl.Rsa.RISCV64.InvBatch.aMin, aOne]

theorem invSetup_ok {s0 s : State} {X₁ X₂ : Nat} (h : PreC s0) (ck : Ck s0 X₁ X₂ s) :
    WP isa (seqs invSetup) s fun t => CB s0 s0.mem t ∧ Ws t (bOf s0) (zOf s0) (wOf s0) nArr ∧
      Keys.Frame (bOf s0) (wOf s0) setupArrs [] s.mem t.mem ∧ IS s0 t ∧ Keep (.s8 :: InvBatch.kRegs) s t := by
  have ⟨b1, b2, b3, b4⟩ := h.nP_bounds
  have ⟨w1, w2⟩ := h.w_bounds
  have hz := h.zk
  have c := ck.cb
  have ws := ck.ws
  have fitZ : ∀ j < nArr, arr (wOf s0) j + S (wOf s0) ≤ zOf s0 := fun j hj =>
    Nat.le_trans (arr_end hj) ws.fits
  have fit : ∀ j < nArr, arr (wOf s0) j + S (wOf s0) ≤ 2 ^ 64 := fun j hj => ws.fit64 hj
  have step : ∀ {u v : State} {js ds : List Nat}, CB s0 s0.mem u →
      Keys.Frame (bOf s0) (wOf s0) js ds u.mem v.mem → (∀ j ∈ js, j < nArr) → (∀ d ∈ ds, 96 ≤ d ∧ d + 8 ≤ Keys.hdr) →
      ∀ {rs : List Reg}, Keep rs u v → (∀ r ∈ cbRegs, r ∉ rs) → CB s0 s0.mem v :=
    fun cu f hjs hds _ k hr => cu.of_frame f (fun j hj => fitZ j (hjs j hj)) hds
      (by simp only [hdr_eq, zOf] at hz ⊢; omega_arith) k hr
  unfold invSetup
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok ws (o := Impl.Rsa.RISCV64.InvBatch.aX) (a := aQ) (by decide) (by decide) (by decide) (by decide))
    fun t1 ⟨w1', f1, v1, k1, _⟩ => ?_
  have c1 := step c f1 (by decide) (by simp) k1 (by decide)
  rw [ck.q] at v1
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok w1' (o := Impl.Rsa.RISCV64.InvBatch.aMin) (a := aP) (by decide) (by decide) (by decide) (by decide))
    fun t2 ⟨w2', f2, v2, k2, _⟩ => ?_
  have c2 := step c1 f2 (by decide) (by simp) k2 (by decide)
  rw [f1.num (j := aP) (by decide) (by simp) (fit _ (by decide)), ck.p] at v2
  rw [wp_seqs_cons (List.cons_ne_nil _ _), WP.block_append_iff]
  refine WP.mono (orOne_ok w2' (j := Impl.Rsa.RISCV64.InvBatch.aMin) (by decide) (by decide)) fun t3 ⟨w3, f3, v3, k3⟩ => ?_
  have c3 := step c2 f3 (by decide) (by simp) k3 (by decide)
  rw [v2] at v3
  refine WP.mono (nCalc_ok h c3) fun t4 ⟨⟨u8, um⟩, k4⟩ => ?_
  have c4 := c3.of_keep k4 um
  have w4 := w3.of_keep k4
  have ctx : InvBatch.Ctx t4 (bOf s0) (zOf s0) (wOf s0) nArr (nP s0) := ⟨w4, u8, b1, b2, by decide, by omega_arith⟩
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (InvBatch.zeroW_ok ctx (j := aOne) (by decide) (by decide)) fun t5 ⟨h5, f5, _, z5, k5⟩ => ?_
  have c5 := step c4 f5 (by decide) (by simp) (k5.mono (rs' := InvBatch.kRegs) (by decide)) (by decide)
  have n5 : num t5.mem (bOf s0) (wOf s0) aOne = 0 := by
    have z := z5
    rw [VG.Proof.Mont.wordsVal_succ_top] at z
    show VG.Proof.Mont.wordsVal _ _ _ (wOf s0) = 0
    omega_using [z]
  refine WP.mono (setOne_ok h5.ws (j := aOne) (by decide) (by decide)) fun t ⟨w6, f6, v6, k6⟩ => ?_
  have c6 := step c5 f6 (by decide) (by simp) k6 (by decide)
  rw [n5] at v6
  have K : Keys.Frame (bOf s0) (wOf s0) setupArrs [] s.mem t.mem :=
    (f1.mono (by simp) (by simp)).trans ((f2.mono (by simp) (by simp)).trans ((f3.mono (by simp) (by simp)).trans
      ((show Keys.Frame (bOf s0) (wOf s0) setupArrs [] t3.mem t4.mem by rw [um]; exact Keys.Frame.refl _ _ _ _ _).trans
        ((f5.mono (by simp) (by simp)).trans (f6.mono (by simp) (by simp))))))
  refine ⟨c6, w6, K, ⟨?_, ?_, by rw [v6], ?_⟩,
    Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans' (k1.mono (by decide)) (k2.mono (by decide)))
      (k3.mono (by decide))) (k4.mono (by decide))) (k5.mono (by decide))) (k6.mono (by decide))⟩
  · rw [f6.num (j := Impl.Rsa.RISCV64.InvBatch.aX) (by decide) (by simp) (fit _ (by decide)),
      f5.num (j := Impl.Rsa.RISCV64.InvBatch.aX) (by decide) (by simp) (fit _ (by decide)),
      show num t4.mem (bOf s0) (wOf s0) Impl.Rsa.RISCV64.InvBatch.aX = num t3.mem (bOf s0) (wOf s0) Impl.Rsa.RISCV64.InvBatch.aX by rw [um],
      f3.num (j := Impl.Rsa.RISCV64.InvBatch.aX) (by decide) (by simp) (fit _ (by decide)),
      f2.num (j := Impl.Rsa.RISCV64.InvBatch.aX) (by decide) (by simp) (fit _ (by decide)), v1]
  · rw [f6.num (j := Impl.Rsa.RISCV64.InvBatch.aMin) (by decide) (by simp) (fit _ (by decide)),
      f5.num (j := Impl.Rsa.RISCV64.InvBatch.aMin) (by decide) (by simp) (fit _ (by decide)),
      show num t4.mem (bOf s0) (wOf s0) Impl.Rsa.RISCV64.InvBatch.aMin = num t3.mem (bOf s0) (wOf s0) Impl.Rsa.RISCV64.InvBatch.aMin by rw [um], v3]
  · rw [k6.gpr (by decide), k5.gpr (by decide)]; exact u8

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

/-- A balanced key, from the lengths. -/
abbrev Bal (s0 : State) : Prop := pL s0 % 8 = 0 ∧ 4 * wOf s0 = pL s0 ∧ pL s0 = qL s0 ∧ 32 ≤ pL s0

/-- After the inverse: `V` the gcd, and `X` an inverse, unless the key is
balanced and `p | 1` is not a number of exactly `w / 2` words (which `p q = n`
excludes), where the tail's division by words is not exact. -/
structure IC (s0 : State) (V X : Nat) : Prop where
  vx : 1 < Mv s0 → V = Nat.gcd (Qv s0) (Mv s0) ∧ ∃ X' : Nat, (Mv s0 : Int) ∣ (X' : Int) * Qv s0 - V ∧
    X' < Mv s0 ∧ ((Bal s0 → InW (wOf s0) (Mv s0)) → X = X')

/-- The inverse: for a balanced key without its doublings, then the tail. -/
theorem invG_ok [InvLaw] {s0 s : State} (h : PreC s0) (c : CB s0 s0.mem s)
    (ws : Ws s (bOf s0) (zOf s0) (wOf s0) nArr) (is : IS s0 s) :
    WP isa invG s fun t => CB s0 s0.mem t ∧ Ws t (bOf s0) (zOf s0) (wOf s0) nArr ∧
      Keys.Frame (bOf s0) (wOf s0) (aDQ :: aDR :: InvBatch.invArrs) [] s.mem t.mem ∧
      Keep (.s0 :: InvBatch.invRegs) s t ∧
      (1 < Mv s0 → num t.mem (bOf s0) (wOf s0) 1 = Nat.gcd (Qv s0) (Mv s0) ∧
        ∃ X' : Nat, (Mv s0 : Int) ∣ (X' : Int) * Qv s0 - num t.mem (bOf s0) (wOf s0) 1 ∧ X' < Mv s0 ∧
          ((Bal s0 → InW (wOf s0) (Mv s0)) → num t.mem (bOf s0) (wOf s0) 3 = X')) := by
  have ⟨b1, b2, b3, b4⟩ := h.nP_bounds
  have ⟨w1, w2⟩ := h.w_bounds
  have hz := h.zk
  have hp1 := h.p1
  have ⟨lp, lq⟩ := lt32 h
  have fitZ : ∀ j < nArr, arr (wOf s0) j + S (wOf s0) ≤ zOf s0 := fun j hj =>
    Nat.le_trans (arr_end hj) ws.fits
  have fit : ∀ j < nArr, arr (wOf s0) j + S (wOf s0) ≤ 2 ^ 64 := fun j hj => ws.fit64 hj
  have ctx : InvBatch.Ctx s (bOf s0) (zOf s0) (wOf s0) nArr (nP s0) := ⟨ws, is.s8, b1, b2, by decide, by omega_arith⟩
  have hq : Qv s0 < 2 ^ (32 * nP s0) := by
    have := os2ip_bytes_lt s0.mem (stackArg s0 2) (qL s0)
    have : 2 ^ (8 * qL s0) ≤ 2 ^ (32 * nP s0) := Nat.pow_le_pow_right (by decide) (by omega_arith)
    simp only [Qv, qB] at *; omega_arith
  have hmp := (Mv_lt s0).resolve_right (by simp only [pL]; omega_arith)
  have hm : Mv s0 < 2 ^ (32 * nP s0) := by
    have : 2 ^ (8 * pL s0) ≤ 2 ^ (32 * nP s0) := Nat.pow_le_pow_right (by decide) (by omega_arith)
    omega_arith
  have hodd : Mv s0 % 2 = 1 := by simp only [Mv]; omega_arith
  unfold invG
  rw [WP.seq_iff]
  refine WP.mono (shape_ok (pl := pL s0) (ql := qL s0) (w := wOf s0) (c.s4.trans (toNat_ofNat_eq _))
    (c.s6.trans (toNat_ofNat_eq _)) ws.s9 lp lq ws.wle) fun t ⟨⟨hiff, tm⟩, kt⟩ => ?_
  have ct := c.of_keep kt tm
  have wt := ws.of_keep kt
  have ctxt : InvBatch.Ctx t (bOf s0) (zOf s0) (wOf s0) nArr (nP s0) :=
    ⟨wt, (kt.gpr (by decide)).trans is.s8, b1, b2, by decide, by omega_arith⟩
  have nxt : num t.mem (bOf s0) (wOf s0) Impl.Rsa.RISCV64.InvBatch.aX = Qv s0 := by rw [tm]; exact is.nx
  have nmt : num t.mem (bOf s0) (wOf s0) Impl.Rsa.RISCV64.InvBatch.aMin = Mv s0 := by rw [tm]; exact is.nm
  refine WP.ite _ (Steps.eval_zero t .t0) (fun hz0 => ?_) (fun _ => ?_)
  · -- A balanced key: the inverse without its doublings, then the tail.
    have hb : Bal s0 := hiff.mp (by simpa using hz0)
    obtain ⟨hb8, hb4, hbq, hb32⟩ := hb
    have hw8 : 8 ≤ wOf s0 := by omega_using [w1]
    have hw2 : wOf s0 % 2 = 0 := by omega_using [hb8, hb4]
    have hnw : nP s0 = wOf s0 := by simp only [nP]; omega_using [hb4, hbq]
    rw [wp_seqs_cons (List.cons_ne_nil _ _)]
    refine WP.mono (InvLaw.inverseS_ok ctxt (by decide) nxt hq nmt hm hodd) fun t1 ⟨w1', f1, k1, v1⟩ => ?_
    rw [wp_seqs_cons (List.cons_ne_nil _ _)]
    refine WP.mono (saveK_ok w1' (by decide) (by omega_using [w1])) fun t2 ⟨w2', f2, k2, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ => ?_
    rw [wp_seqs_cons (List.cons_ne_nil _ _), show seqs [.block restoreK] = .block restoreK from rfl]
    refine WP.mono (tail_ok w2' hw8 w2 hw2) fun t3 ⟨w3', f3, k3, v3⟩ => ?_
    have kq : ∀ i < wOf s0 + 2, word t3.mem (bOf s0) (arr (wOf s0) aDQ + 8 * i) =
        word t2.mem (bOf s0) (arr (wOf s0) aDQ + 8 * i) := fun i hi =>
      f3.word hi (by decide) (by simp) (fit _ (by decide))
    have q : ∀ {d : Nat}, d % 8 = 0 → d < 72 → word t3.mem (bOf s0) (arr (wOf s0) aDQ + d) =
        word t2.mem (bOf s0) (arr (wOf s0) aDQ + d) := fun {d} h8 h72 => by
      have := kq (d / 8) (by omega_using [w1, h72])
      rwa [show 8 * (d / 8) = d by omega_using [h8]] at this
    have q0 := kq 0 (by omega_using [])
    rw [Nat.mul_zero, Nat.add_zero] at q0
    refine WP.mono (restoreK_ok w3' (by decide) (by omega_using [w1]) (q0.trans e1) ((q (by decide) (by decide)).trans e2)
      ((q (by decide) (by decide)).trans e3) ((q (by decide) (by decide)).trans e4) ((q (by decide) (by decide)).trans e5)
      ((q (by decide) (by decide)).trans e6) ((q (by decide) (by decide)).trans e7) ((q (by decide) (by decide)).trans e8)
      ((q (by decide) (by decide)).trans e9)) fun u ⟨⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, um⟩, k4⟩ => ?_
    -- The registers: those of `kept` restored, the rest kept or written.
    have K : Keep (.s0 :: InvBatch.invRegs) s u := by
      have K1 : Keep (.s0 :: InvBatch.invRegs) t u := by
        refine ⟨fun r hr => ?_, k4.2.1.trans (k3.2.1.trans (k2.2.1.trans k1.2.1)),
          k4.2.2.trans (k3.2.2.trans (k2.2.2.trans k1.2.2))⟩
        by_cases hk : r ∈ VG.Impl.Rsa.RISCV64.CrtValues.kept
        · have kk : ∀ r ∈ VG.Impl.Rsa.RISCV64.CrtValues.kept, t1.gpr r = t.gpr r := fun r hr =>
            k1.gpr (by revert r; decide)
          simp only [VG.Impl.Rsa.RISCV64.CrtValues.kept, List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · rw [r1, ← kk _ (by decide)]
          · rw [r2, ← kk _ (by decide)]
          · rw [r3, ← kk _ (by decide)]
          · rw [r4, ← kk _ (by decide)]
          · rw [r5, ← kk _ (by decide)]
          · rw [r6, ← kk _ (by decide)]
          · rw [r7, ← kk _ (by decide)]
          · rw [r8, ← kk _ (by decide)]
          · rw [r9, ← kk _ (by decide)]
        · have sub : ∀ x ∈ (((InvBatch.invRegs ++ [.t0]) ++ dwRegs) ++ [.t0, .s1, .s2, .s3, .s4, .a0, .a1, .a2, .a3, .a6]),
              x ∈ (.s0 :: InvBatch.invRegs) ∨ x ∈ VG.Impl.Rsa.RISCV64.CrtValues.kept := by decide
          exact (((k1.trans k2).trans k3).trans k4).gpr fun hm => (sub r hm).elim hr hk
      exact (kt.trans K1).mono (by decide)
    have F : Keys.Frame (bOf s0) (wOf s0) (aDQ :: aDR :: InvBatch.invArrs) [] s.mem u.mem := by
      rw [um, ← tm]
      exact (f1.mono (by simp) (by simp)).trans ((f2.mono (by simp) (by simp)).trans (f3.mono (by decide) (by simp)))
    refine ⟨c.of_frame F (fun j hj => fitZ j (by revert j hj; decide)) (by simp)
      (by simp only [hdr_eq, zOf] at hz ⊢; omega_arith) K (by decide), w3'.of_keep k4, F, K, fun h1M => ?_⟩
    obtain ⟨g, d, l⟩ := v1 h1M
    have g3 : num u.mem (bOf s0) (wOf s0) 1 = num t1.mem (bOf s0) (wOf s0) 1 := by
      rw [um, f3.num (by decide) (by simp) (fit _ (by decide)), f2.num (by decide) (by simp) (fit _ (by decide))]
    have y2 : num t2.mem (bOf s0) (wOf s0) 3 = num t1.mem (bOf s0) (wOf s0) 3 :=
      f2.num (by decide) (by simp) (fit _ (by decide))
    have m2 : num t2.mem (bOf s0) (wOf s0) 8 = num t1.mem (bOf s0) (wOf s0) 8 :=
      f2.num (by decide) (by simp) (fit _ (by decide))
    have m1 : num t1.mem (bOf s0) (wOf s0) 8 = Mv s0 := by
      rw [f1.num (by decide) (by simp) (fit _ (by decide))]; exact nmt
    rw [g3, hnw] at *
    refine ⟨by rw [g, Nat.gcd_comm], _, d, Nat.mod_lt _ (by omega_using [hodd]), fun hin => ?_⟩
    have yv : num t1.mem (bOf s0) (wOf s0) 3 < 2 ^ (64 * (wOf s0 / 2)) := by
      have : 2 ^ (8 * pL s0) = 2 ^ (64 * (wOf s0 / 2)) := by congr 1; omega_using [hb8, hb4]
      omega_using [hmp, v1, h1M, this]
    rw [um, v3 (by rw [y2]; exact yv) (by rw [m2, m1]; exact hin ⟨hb8, hb4, hbq, hb32⟩), y2, m2, m1,
      show InvBatch.nu (wOf s0) = wOf s0 / 2 by unfold InvBatch.nu; omega_using [hw2]]
  · -- Else as it is.
    refine WP.mono (InvLaw.inverse_ok ctxt (by decide) nxt hq nmt hm hodd) fun u ⟨w1', f1, k1, v1⟩ => ?_
    have F : Keys.Frame (bOf s0) (wOf s0) (aDQ :: aDR :: InvBatch.invArrs) [] s.mem u.mem := by
      rw [← tm]; exact f1.mono (by simp) (by simp)
    have K : Keep (.s0 :: InvBatch.invRegs) s u := (kt.trans k1).mono (by decide)
    refine ⟨c.of_frame F (fun j hj => fitZ j (by revert j hj; decide)) (by simp)
      (by simp only [hdr_eq, zOf] at hz ⊢; omega_arith) K (by decide), w1', F, K, fun h1M => ?_⟩
    obtain ⟨g, d, l⟩ := v1 h1M
    exact ⟨by rw [g, Nat.gcd_comm], _, d, l, fun _ => rfl⟩

theorem invCore_ok [InvLaw] {s0 s : State} (h : PreC s0) (c : CB s0 s0.mem s)
    (ws : Ws s (bOf s0) (zOf s0) (wOf s0) nArr) (is : IS s0 s) :
    WP isa (.seq invG (eqS sE3 1 aOne)) s fun t => CB s0 s0.mem t ∧
      Ws t (bOf s0) (zOf s0) (wOf s0) nArr ∧
      Keys.Frame (bOf s0) (wOf s0) (aDQ :: aDR :: InvBatch.invArrs) [sE3] s.mem t.mem ∧
      IC s0 (num t.mem (bOf s0) (wOf s0) 1) (num t.mem (bOf s0) (wOf s0) 3) ∧
      slot t.mem (bOf s0) sE3 = (if num t.mem (bOf s0) (wOf s0) 1 = 1 then 1 else 0) ∧
      Keep (.s0 :: InvBatch.invRegs) s t := by
  have hz := h.zk
  have fit : ∀ j < nArr, arr (wOf s0) j + S (wOf s0) ≤ 2 ^ 64 := fun j hj => ws.fit64 hj
  rw [WP.seq_iff]
  refine WP.mono (invG_ok h c ws is) fun t1 ⟨c1, w1', f1, k1, v1⟩ => ?_
  refine WP.mono (eqS_ok w1' (d := sE3) (a := 1) (b := aOne) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun t ⟨w2', f2, v2, k2⟩ => ?_
  have c2 := c1.of_frame f2 (by simp) (by decide) (by simp only [hdr_eq, zOf] at hz ⊢; omega_arith) k2 (by decide)
  have o1 : num t1.mem (bOf s0) (wOf s0) aOne = 1 := by
    rw [f1.num (j := aOne) (by decide) (by simp) (fit _ (by decide)), is.nOne]
  have n1 : num t.mem (bOf s0) (wOf s0) 1 = num t1.mem (bOf s0) (wOf s0) 1 :=
    f2.num (j := 1) (by simp) (by decide) (fit _ (by decide))
  have n3 : num t.mem (bOf s0) (wOf s0) 3 = num t1.mem (bOf s0) (wOf s0) 3 :=
    f2.num (j := 3) (by simp) (by decide) (fit _ (by decide))
  refine ⟨c2, w2', (f1.mono (by simp) (by simp)).trans (f2.mono (by simp) (by simp)),
    ⟨fun h1M => by rw [n1, n3]; exact v1 h1M⟩, by rw [v2, o1, n1],
    Keep.trans' k1 (k2.mono (by decide))⟩

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


namespace VG.Proof.Rsa.RISCV64.CrtValues

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs eqS storeBytes andS sOdd sB sC)
open VG.Impl.Rsa.RISCV64.CrtValues (invSetup invPart storeQ nArr aOne aP aQ aD aDD sE3 sPodd sE1
  sE2 sMask mask)
open VG.Proof.Rsa.CrtValues (maskOf)

/-- After the inverse's phase. -/
structure Iv (s0 : State) (X₁ X₂ V X : Nat) (t : State) : Prop where
  cb : CB s0 t.mem t
  ws : Ws t (bOf s0) (zOf s0) (wOf s0) nArr
  p : num t.mem (bOf s0) (wOf s0) aP = Pv s0
  q : num t.mem (bOf s0) (wOf s0) aQ = Qv s0
  d : num t.mem (bOf s0) (wOf s0) aD = Dv s0
  ddz : word t.mem (bOf s0) (arr (wOf s0) aDD + 8 * wOf s0) = 0
  x : 0 < Pv s0 → X₁ = Nv s0 / Pv s0 ∧ X₂ = Nv s0 % Pv s0
  ic : IC s0 V X
  mask : slot t.mem (bOf s0) sMask = if maskOf (Pv s0) (Qv s0) X₁ X₂ V then 1 else 0
  qi : Spec.Rsa.bytesAt t.mem (s0.gpr .a4) (pL s0) = if maskOf (Pv s0) (Qv s0) X₁ X₂ V then
    Spec.Rsa.i2osp (X % 256 ^ pL s0) (pL s0) else List.replicate (pL s0) 0

/-- Before `qInv` is written: the mask in `t4`, and `X` in array 3. -/
structure IvA (s0 : State) (X₁ X₂ V X : Nat) (t : State) : Prop where
  cb : CB s0 s0.mem t
  ws : Ws t (bOf s0) (zOf s0) (wOf s0) nArr
  p : num t.mem (bOf s0) (wOf s0) aP = Pv s0
  q : num t.mem (bOf s0) (wOf s0) aQ = Qv s0
  d : num t.mem (bOf s0) (wOf s0) aD = Dv s0
  ddz : word t.mem (bOf s0) (arr (wOf s0) aDD + 8 * wOf s0) = 0
  x : 0 < Pv s0 → X₁ = Nv s0 / Pv s0 ∧ X₂ = Nv s0 % Pv s0
  ic : IC s0 V X
  mask : slot t.mem (bOf s0) sMask = if maskOf (Pv s0) (Qv s0) X₁ X₂ V then 1 else 0
  m4 : t.gpr .t4 = (if decide (slot t.mem (bOf s0) sMask ≠ 0) then BitVec.allOnes 64 else 0)
  y : num t.mem (bOf s0) (wOf s0) 3 = X

theorem mask_prod (P Q X₁ X₂ V : Nat) :
    P % 2 * (if X₁ = Q then 1 else 0) * (if X₂ = 0 then 1 else 0) * (if V = 1 then 1 else 0) =
      if maskOf P Q X₁ X₂ V then 1 else 0 := by
  rcases Nat.mod_two_eq_zero_or_one P with e | e <;>
    by_cases a : X₁ = Q <;> by_cases b : X₂ = 0 <;> by_cases c : V = 1 <;> simp [maskOf, e, a, b, c]

/-- Words of the working space, past a write apart from it. -/
theorem wordsVal_of_out {O B : Addr} {L Z : Nat} {m m' : Mem} (hd : (⟨O, L⟩ : Region).Disjoint ⟨B, Z⟩)
    (ho : Outside O 0 L m m') {d k : Nat} (hdk : d + 8 * k ≤ Z) (hZ : Z ≤ 2 ^ 64) :
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

/-- The arrays and slots that the inverse's phase writes. -/
abbrev phaseArrs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 15, 18, 19]

theorem invPart_ok [InvLaw] {s0 s : State} (h : PreC s0) {X₁ X₂ : Nat} (ck : Ck s0 X₁ X₂ s) :
    WP isa invPart s fun t => ∃ V X, IvA s0 X₁ X₂ V X t := by
  have ⟨b1, b2, b3, b4⟩ := h.nP_bounds
  have ⟨w1, w2⟩ := h.w_bounds
  have hz := h.zk
  have fitW : ∀ j < nArr, arr (wOf s0) j + S (wOf s0) ≤ 2 ^ 64 := fun j hj => ck.ws.fit64 hj
  have lt16 : ∀ k ∈ phaseArrs, k < 20 := by decide
  unfold invPart
  rw [wp_seqs_append (by unfold invSetup; simp) (by simp)]
  refine WP.mono (invSetup_ok h ck) fun t2 ⟨c2, ws2, f2, is2, k2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (WP.seq_iff.mp (invCore_ok h c2 ws2 is2)) fun t3 h3 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono h3 fun t4 ⟨c4, ws4, f4, ic4, e4, k4⟩ => ?_
  -- The checks' slots, kept.
  have sl : ∀ e ∈ [sPodd, sE1, sE2], slot t4.mem (bOf s0) e = slot s.mem (bOf s0) e := by
    intro e he
    have h8 : e + 8 ≤ Keys.hdr := by revert e; decide
    rw [f4.slot h8 (by revert e; decide), f2.slot h8 (by simp)]
  have sp4 := sl sPodd (by simp)
  have se1 := sl sE1 (by simp)
  have se2 := sl sE2 (by simp)
  rw [ck.podd] at sp4
  rw [show seqs [Code.block (andS sMask sPodd sE1 ++ andS sMask sMask sE2 ++ andS sMask sMask sE3 ++ mask)] =
    Code.block (andS sMask sPodd sE1 ++ andS sMask sMask sE2 ++ andS sMask sMask sE3 ++ mask) from rfl]
  refine WP.mono (maskBlk_ok ws4 (by rw [sp4]; omega_arith) (by rw [se1]; exact ck.b1)
    (by rw [se2]; exact ck.b2) (by rw [e4]; exact bit_ite)) fun t5 ⟨ws5, f5, v5, m5, k5⟩ => ?_
  rw [sp4, se1, se2, ck.e12, e4, mask_prod] at v5
  have c5 := c4.of_frame f5 (by simp) (by decide) (by simp only [hdr_eq, zOf] at hz ⊢; omega_arith) k5
  -- Memory past the inverse's arrays, and the slot `sMask`.
  have Fw : Keys.Frame (bOf s0) (wOf s0) phaseArrs [sE3, sMask] s.mem t5.mem :=
    (f2.mono (by decide) (by simp)).trans ((f4.mono (by decide) (by simp)).trans (f5.mono (by simp) (by simp)))
  have nW : ∀ j, 20 ≤ j → j < nArr → num t5.mem (bOf s0) (wOf s0) j = num s.mem (bOf s0) (wOf s0) j :=
    fun j hj hj' => Fw.num (fun k hk => by have := lt16 k hk; omega_using [hj, this]) (by decide) (fitW _ hj')
  have nW' : ∀ j, j = aP ∨ j = aQ → num t5.mem (bOf s0) (wOf s0) j = num s.mem (bOf s0) (wOf s0) j :=
    fun j hj => Fw.num (fun k hk => by
      rcases hj with rfl | rfl <;> revert k <;> decide) (by decide) (fitW _ (by rcases hj with rfl | rfl <;> decide))
  refine ⟨num t4.mem (bOf s0) (wOf s0) 1, num t4.mem (bOf s0) (wOf s0) 3, c5, ws5,
    by rw [nW' aP (.inl rfl), ck.p], by rw [nW' aQ (.inr rfl), ck.q],
    by rw [nW aD (by decide) (by decide), ck.d], ?_, ck.x, ic4, v5, m5, ?_⟩
  · rw [Fw.word (j := aDD) (i := wOf s0) (by omega_arith)
      (fun k hk => by have := lt16 k hk; unfold aDD; omega_using [this]) (by decide) (fitW _ (by decide))]
    exact ck.ddz
  · exact f5.num (j := 3) (by simp) (by decide) (ws4.fit64 (by decide))

/-- `storeQ`: `qInv` written under the mask. -/
theorem storeQ_ok {s0 s : State} (h : PreC s0) {X₁ X₂ V X : Nat} (ia : IvA s0 X₁ X₂ V X s) :
    WP isa storeQ s (Iv s0 X₁ X₂ V X) := by
  have hz := h.zk
  have hp1 := h.p1
  have hpw : pL s0 ≤ 8 * wOf s0 := by have := h.p2; simp only [pL, wOf, kOf]; omega_arith
  have fitW : ∀ j < nArr, arr (wOf s0) j + S (wOf s0) ≤ 2 ^ 64 := fun j hj => ia.ws.fit64 hj
  have c5 := ia.cb
  have wqi : (s0.gpr .a4).toNat + pL s0 ≤ 2 ^ 64 := by have := h.wqi; rw [h.h5] at this; exact this
  have qiw : (⟨s0.gpr .a4, pL s0⟩ : Region) ∈ s0.wr := by rw [← h.qiR_eq, h.hwr]; simp
  have qis : (⟨s0.gpr .a4, pL s0⟩ : Region).Disjoint (sR s0) := by rw [← h.qiR_eq]; exact h.qis
  refine WP.mono (storeBytes_ok ia.ws (j := 3) (by decide) (by decide) c5.a6
    (by rw [c5.s4]; exact toNat_ofNat_eq _) (by decide) (by decide) (by decide) ia.m4 hp1 hpw
    (fun i hi => by rw [c5.wr]; exact bytes_in qiw (by omega_arith) i hi) (bytes_sep qis (by omega_arith)) wqi)
    fun t ⟨ws6, by6, o6, k6⟩ => ?_
  have c6 := c5.of_out k6 o6 qis (by omega_arith)
  have Z64 : zOf s0 ≤ 2 ^ 64 := by have := h.ws; simp only [zOf]; omega_arith
  have nW : ∀ j < nArr, num t.mem (bOf s0) (wOf s0) j = num s.mem (bOf s0) (wOf s0) j :=
    fun j hj' => wordsVal_of_out qis o6 (Nat.le_trans (Nat.add_le_add_left
      (show 8 * wOf s0 ≤ S (wOf s0) by simp only [S]; omega_using []) _) (Nat.le_trans (arr_end hj') h.fits)) Z64
  have W1 : ∀ {m : Mem} {d : Nat}, wordsVal m (bOf s0) d 1 = (word m (bOf s0) d).toNat := by
    intro m d; simp [wordsVal]
  refine ⟨c6, ws6, by rw [nW aP (by decide), ia.p], by rw [nW aQ (by decide), ia.q],
    by rw [nW aD (by decide), ia.d], ?_, ia.x, ia.ic, ?_, ?_⟩
  · have hDD : arr (wOf s0) aDD + 8 * wOf s0 + 8 * 1 ≤ zOf s0 := by
      have := Nat.le_trans (arr_end (show aDD < nArr by decide)) h.fits
      simp only [S] at this; omega_arith
    have e : wordsVal t.mem (bOf s0) (arr (wOf s0) aDD + 8 * wOf s0) 1 =
        wordsVal s.mem (bOf s0) (arr (wOf s0) aDD + 8 * wOf s0) 1 := wordsVal_of_out qis o6 hDD Z64
    rw [W1, W1] at e
    rw [BitVec.eq_of_toNat_eq e]
    exact ia.ddz
  · have e : wordsVal t.mem (bOf s0) sMask 1 = wordsVal s.mem (bOf s0) sMask 1 := by
      rw [wordsVal_of_out qis o6 (by simp only [zOf, sMask] at hz ⊢; omega_arith) Z64]
    rw [W1, W1] at e
    change (word t.mem (bOf s0) sMask).toNat = _
    rw [e]; exact ia.mask
  · have v5 := ia.mask
    by_cases hm : maskOf (Pv s0) (Qv s0) X₁ X₂ V = true
    · simp only [hm, ↓reduceIte] at v5 ⊢
      rw [bytes_of_store hpw (fun c hc => by rw [by6 c hc, v5]; rfl), ia.y]
    · simp only [hm, ↓reduceIte, Bool.false_eq_true] at v5 ⊢
      exact bytesAt_zero fun c hc => by rw [by6 c hc, v5]; rfl

end VG.Proof.Rsa.RISCV64.CrtValues
