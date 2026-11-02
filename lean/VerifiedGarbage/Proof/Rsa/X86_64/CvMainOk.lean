module

public import VerifiedGarbage.Proof.Rsa.X86_64.InvLaw

-- separate module: `cvMain_ok` uses the inverse, whose proofs import algebra, and `CvMain` is imported by many modules
public import VerifiedGarbage.Proof.Rsa.X86_64.CvMain
import VerifiedGarbage.Proof.Rsa.X86_64.CvInv
import VerifiedGarbage.Proof.Rsa.KeyMath
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# `vg_rsa_crt_values` on x86-64: `main`'s correctness (`cvMain_ok`)
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)

/-- `main`, from a valid modulus. -/
theorem cvMain_ok [InvLaw] {I : CvIn} {s : State} (h : CvPre I s) (hv : Spec.Rsa.modulusValid I.N I.k = true) :
    WP isa main s fun t => ∃ X : Nat, (I.ok = true → Spec.Rsa.inverse I.Q I.P = some X) ∧
      (List.range I.pl).map (fun i => t.mem (I.pQi + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if I.ok then X else 0) I.pl ∧
      (List.range I.pl).map (fun i => t.mem (I.pDp + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if I.ok then I.D % (I.P - 1) else 0) I.pl ∧
      (List.range I.ql).map (fun i => t.mem (I.pDq + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if I.ok then I.D % (I.Q - 1) else 0) I.ql ∧
      t.gpr .rax = BitVec.ofNat 64 I.ok.toNat ∧ (∀ i < 6, t.gpr (saved.getD i .rax) = I.sv i) ∧
      (∀ x, I.Z ≤ ofs I.B x → (∀ i < I.pl, x ≠ I.pQi + BitVec.ofNat 64 i) →
        (∀ i < I.pl, x ≠ I.pDp + BitVec.ofNat 64 i) → (∀ i < I.ql, x ≠ I.pDq + BitVec.ofNat 64 i) →
        t.mem x = s.mem x) ∧
      t.gpr .rsp = s.gpr .rsp := by
  have L := h.L
  have k1 := L.k1
  have k2 := L.k2
  have hn := h.scr.nowrap
  have hZ := L.z
  obtain ⟨hNo, hlo⟩ := valid_lo hv
  have hPl : I.P < 256 ^ I.pl := by have := os2ip_lt I.pb; rw [L.pbl] at this; exact this
  have hQl : I.Q < 256 ^ I.ql := by have := os2ip_lt I.qb; rw [L.qbl] at this; exact this
  have hPw := pow256_le_w (k := I.k) L.pl2
  have hQw := pow256_le_w (k := I.k) L.ql2
  have eM : Impl.Bignum.X86_64.Public.sMask = 22 := rfl
  rw [main_eq]
  -- The head.
  refine wp_seqs_append (by simp) (by simp [loadA]) (WP.mono (cvHeadS_ok h) fun s₁ ⟨h₁, hm₁⟩ => ?_)
  -- The loads.
  refine wp_seqs_append (by simp [loadA]) (by simp [pqCheck]) (WP.mono (cvLoads_ok h₁ L)
    fun s₂ ⟨h₂, m₂, vN, vP, vQ, vD⟩ => ?_)
  -- `p q = n`.
  refine wp_seqs_append (by simp [pqCheck]) (by simp [invPart]) (WP.mono (cvCheck_ok h₂ L (c := true)
    (by rw [m₂]; exact hm₁) (by rw [vN]; exact hNo)) fun s₃ ⟨h₃, m₃, p₃⟩ => ?_)
  rw [vP, vQ, vN, Bool.true_and] at m₃
  have vP₃ : wv s₃.mem I.B (slot (wk I.k) aP) (wk I.k) = I.P := by rw [p₃ aP (.inl rfl), vP]
  have vQ₃ : wv s₃.mem I.B (slot (wk I.k) aQ) (wk I.k) = I.Q := by rw [p₃ aQ (.inr (.inl rfl)), vQ]
  have vD₃ : wv s₃.mem I.B (slot (wk I.k) aD) (wk I.k) = I.D := by rw [p₃ aD (.inr (.inr rfl)), vD]
  have hf : I.P * I.Q = I.N → I.P % 2 = 1 ∧ 1 < I.P ∧ I.Q % 2 = 1 ∧ 1 < I.Q :=
    factors_of hNo hlo hPl hQl L.pl2 L.ql2
  -- `qInv` and `gcd(q, p) = 1`.
  refine wp_seqs_append (by simp [invPart]) (by simp [divisor]) (WP.mono (cvInv_ok h₃ L m₃ (fun hc => by
    rw [vP₃]; have := hf (of_decide_eq_true hc); exact ⟨this.1, this.2.1⟩)) fun s₄ ⟨h₄, m₄, i₄, p₄⟩ => ?_)
  rw [vP₃, vQ₃] at m₄ i₄
  have vP₄ : wv s₄.mem I.B (slot (wk I.k) aP) (wk I.k) = I.P := by rw [p₄ aP (.inl rfl), vP₃]
  have vQ₄ : wv s₄.mem I.B (slot (wk I.k) aQ) (wk I.k) = I.Q := by rw [p₄ aQ (.inr (.inl rfl)), vQ₃]
  have vD₄ : wv s₄.mem I.B (slot (wk I.k) aD) (wk I.k) = I.D := by rw [p₄ aD (.inr (.inr rfl)), vD₃]
  have hok : (decide (I.P * I.Q = I.N) && decide (Nat.gcd I.Q I.P = 1)) = I.ok := by
    simp only [CvIn.ok, Bool.decide_and]
  rw [hok] at m₄
  have hokP : I.ok = true → I.P * I.Q = I.N ∧ Nat.gcd I.Q I.P = 1 := fun hc => of_decide_eq_true hc
  -- `dP` into `aV`.
  refine wp_seqs_append (by simp [divisor]) (by simp) (WP.mono (cvDivPart_ok h₄ L (j := aP) (.inl rfl))
    fun s₅ ⟨h₅, m₅, d₅, p₅⟩ => ?_)
  rw [vP₄, vD₄] at d₅
  -- `dP` into `aX₁`.
  have hZ' := h₅.ws.hZ
  have hn' := h₅.ws.scr.nowrap
  refine wp_seqs_append (by simp) (by simp [divisor]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_ok h₅.ws (j := aX₁) (by decide)) fun s₆ ⟨_, o₆, k₆⟩ => ?_)
  have h₆ := h₅.arr (by decide) (Nat.le_refl _) o₆ k₆ (by decide)
  refine WP.mono (copyA_ok h₆.ws (o := aX₁) (a := aV) (by decide) (by decide) (by decide)) fun s₇ ⟨c₇, o₇, k₇⟩ => ?_
  have h₇ := h₆.arr (by decide) (by omega_arith) o₇ k₇ (by decide)
  have ot : ∀ {m m' : Mem} {j i Ln : Nat}, Outside I.B (slot (wk I.k) j) Ln m m' → Ln ≤ 8 * (wk I.k + 2) → i ≠ j →
      i < 16 → wv m' I.B (slot (wk I.k) i) (wk I.k) = wv m I.B (slot (wk I.k) i) (wk I.k) :=
    fun o hL hij hi => outside_arr o hL hij (by omega_arith) hi hZ' hn'
  have hmw : ∀ {m m' : Mem} {i L' : Nat}, Outside I.B (slot (wk I.k) i) L' m m' → L' ≤ 8 * (wk I.k + 2) →
      mword m' I.B = mword m I.B := fun {_ _ i _} o _ =>
    o.word (Or.inl (by have := hdr_lt_slot (wk I.k) i (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith))
      (by omega_arith)
  have m₇ : mword s₇.mem I.B = mask I.ok := by rw [hmw o₇ (by omega_arith), hmw o₆ (Nat.le_refl _), m₅, m₄]
  have pr₇ : ∀ i, i = aP ∨ i = aQ ∨ i = aD ∨ i = aX₂ →
      wv s₇.mem I.B (slot (wk I.k) i) (wk I.k) = wv s₄.mem I.B (slot (wk I.k) i) (wk I.k) := fun i hi => by
    have h1 : i ≠ aX₁ := by rcases hi with rfl | rfl | rfl | rfl <;> decide
    have h2 : i < 16 := by rcases hi with rfl | rfl | rfl | rfl <;> decide
    rw [ot o₇ (by omega_arith) h1 h2, ot o₆ (Nat.le_refl _) h1 h2,
      p₅ i (by rcases hi with rfl | rfl | rfl | rfl <;> simp)]
  have dP₇ : I.ok = true → wv s₇.mem I.B (slot (wk I.k) aX₁) (wk I.k) = I.D % (I.P - 1) := fun hc => by
    obtain ⟨hpq, -⟩ := hokP hc
    have hfp := hf hpq
    have e := d₅ hfp.1 hfp.2.1
    rw [c₇, ot o₆ (Nat.le_refl _) (by decide) (by decide)]
    rw [← e]
    refine wv_low_of_lt (by omega_arith) ?_
    rw [e]
    have : I.D % (I.P - 1) < I.P - 1 := Nat.mod_lt _ (by omega_arith)
    omega_arith
  -- `dQ` into `aV`.
  have vQ₇ : wv s₇.mem I.B (slot (wk I.k) aQ) (wk I.k) = I.Q := by rw [pr₇ aQ (by simp), vQ₄]
  have vD₇ : wv s₇.mem I.B (slot (wk I.k) aD) (wk I.k) = I.D := by rw [pr₇ aD (by simp), vD₄]
  refine wp_seqs_append (by simp [divisor]) (by simp [storeA]) (WP.mono (cvDivPart_ok h₇ L (j := aQ) (.inr rfl))
    fun s₈ ⟨h₈, m₈, d₈, p₈⟩ => ?_)
  rw [vQ₇, vD₇] at d₈
  rw [m₇] at m₈
  -- The stores.
  have hw := h₈.ws.w1
  have := L.pl2
  have := L.ql2
  refine WP.mono (cvStores_ok h₈.ws h₈.args m₈ L.pl1 (by unfold wk; omega_arith) L.ql1 (by unfold wk; omega_arith)
    ⟨fun i hi => by rw [h₈.wr, ← h.wr]; exact h.oQi.wr i hi, h.oQi.sep⟩
    ⟨fun i hi => by rw [h₈.wr, ← h.wr]; exact h.oDp.wr i hi, h.oDp.sep⟩
    ⟨fun i hi => by rw [h₈.wr, ← h.wr]; exact h.oDq.wr i hi, h.oDq.sep⟩ h.a1 h.a2 h.a3)
    fun t ⟨bQi, bDp, bDq, hax, hsv, hfr, kt⟩ => ?_
  have vX₈ : wv s₈.mem I.B (slot (wk I.k) aX₂) (wk I.k) = wv s₄.mem I.B (slot (wk I.k) aX₂) (wk I.k) := by
    rw [p₈ aX₂ (by simp), pr₇ aX₂ (by simp)]
  have vX₁₈ : wv s₈.mem I.B (slot (wk I.k) aX₁) (wk I.k) = wv s₇.mem I.B (slot (wk I.k) aX₁) (wk I.k) :=
    p₈ aX₁ (by simp)
  refine ⟨wv s₄.mem I.B (slot (wk I.k) aX₂) (wk I.k), fun hc => ?_, ?_, ?_, ?_, hax, hsv,
    fun x hx n1 n2 n3 => by rw [hfr x n1 n2 n3, h₈.inScr x hx],
    (kt.gpr (by decide)).trans (h₈.rsp.trans h.rsp.symm)⟩
  · obtain ⟨hpq, hg⟩ := hokP hc
    obtain ⟨hdvd, hlt⟩ := i₄ (decide_eq_true hpq)
    rw [hg] at hdvd
    exact VG.Proof.Rsa.inverse_eq (hf hpq).2.1 hlt (by exact_mod_cast hdvd)
  · rw [bQi]
    cases hc : I.ok
    · rfl
    · obtain ⟨hpq, -⟩ := hokP hc
      obtain ⟨-, hlt⟩ := i₄ (decide_eq_true hpq)
      have := pow256_le_wk I.pl
      simp only [ite_true]
      rw [← vX₈]
      exact congrArg (Spec.Rsa.i2osp · I.pl) (wv_low_of_lt (by unfold wk; omega_arith) (by omega_arith))
  · rw [bDp]
    cases hc : I.ok
    · rfl
    · obtain ⟨hpq, -⟩ := hokP hc
      have hfp := hf hpq
      have e := dP₇ hc
      have := pow256_le_wk I.pl
      have : I.D % (I.P - 1) < I.P - 1 := Nat.mod_lt _ (by omega_arith)
      simp only [ite_true]
      rw [← e, ← vX₁₈]
      exact congrArg (Spec.Rsa.i2osp · I.pl) (wv_low_of_lt (by unfold wk; omega_arith) (by rw [vX₁₈, e]; omega_arith))
  · rw [bDq]
    cases hc : I.ok
    · rfl
    · obtain ⟨hpq, -⟩ := hokP hc
      have hfp := hf hpq
      have e := d₈ hfp.2.2.1 hfp.2.2.2
      have := pow256_le_wk I.ql
      have : I.D % (I.Q - 1) < I.Q - 1 := Nat.mod_lt _ (by omega_arith)
      simp only [ite_true]
      rw [← e]
      exact congrArg (Spec.Rsa.i2osp · I.ql) (wv_low_of_lt (by unfold wk; omega_arith) (by rw [e]; omega_arith))

end VG.Proof.Rsa.X86_64
