import VerifiedGarbage.Proof.Rsa.AArch64.CvCheck
import VerifiedGarbage.Proof.Rsa.AArch64.CvStore
import VerifiedGarbage.Proof.Rsa.KeyMath

/-!
# `vg_rsa_crt_values` on AArch64: `main`

From a valid modulus, `main` writes `dP`, `dQ` and `qInv` if `p q = n`
and `gcd(q, p) = 1`, and zeros otherwise (`cvMain_ok`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.Keys.CrtValues
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN)

/-- The inputs as numbers. -/
abbrev CvIn.N (I : CvIn) : Nat := Spec.Rsa.os2ip I.nb
abbrev CvIn.P (I : CvIn) : Nat := Spec.Rsa.os2ip I.pb
abbrev CvIn.Q (I : CvIn) : Nat := Spec.Rsa.os2ip I.qb
abbrev CvIn.D (I : CvIn) : Nat := Spec.Rsa.os2ip I.db

/-- Whether `main` writes the values: `p q = n` and `gcd(q, p) = 1`. -/
abbrev CvIn.ok (I : CvIn) : Bool := decide (I.P * I.Q = I.N ∧ Nat.gcd I.Q I.P = 1)

/-- What `main` needs on entry. -/
structure CvPre (I : CvIn) (s : State) : Prop where
  scr : Scr s I.B I.Z
  x0 : s.gpr .x0 = I.B
  args : CvArgs s.mem I.B I.k I.pl I.ql I.dl I.pDp I.pDq I.pQi I.pN I.pP I.pQ I.pD
  n : Src s I.B I.Z I.pN I.nb
  p : Src s I.B I.Z I.pP I.pb
  q : Src s I.B I.Z I.pQ I.qb
  d : Src s I.B I.Z I.pD I.db
  L : CvLens I
  oQi : OutOk s I.B I.Z I.pQi I.pl
  oDp : OutOk s I.B I.Z I.pDp I.pl
  oDq : OutOk s I.B I.Z I.pDq I.ql
  a1 : Apart I.pQi I.pl I.pDp I.pl
  a2 : Apart I.pQi I.pl I.pDq I.ql
  a3 : Apart I.pDp I.pl I.pDq I.ql
  wr : s.wr = I.W

theorem main_eq : main = seqs (([.block head] : List (Prog isa)) ++
    ((loadA aN Public.sN Public.sK ++
      (loadA aP sP sPl ++ (loadA aQ sQ sQl ++ loadA aD sD sDl))) ++
    (pqCheck ++ (invPart ++ ((divisor aP ++ ([divmod aU aV aC aT] : List (Prog isa))) ++
    (([zeroA aX₁, copyA aX₁ aV] : List (Prog isa)) ++
    ((divisor aQ ++ ([divmod aU aV aC aT] : List (Prog isa))) ++
    (storeA aX₂ sQi sPl Public.sMask ++
      (storeA aX₁ sDp sPl Public.sMask ++
        (storeA aV sDq sQl Public.sMask ++ ([.block retMask] : List (Prog isa)))))))))))) := by
  simp only [main, List.append_assoc, List.cons_append, List.nil_append]

/-- A valid modulus is odd and at least `256^(k - 1)`. -/
theorem valid_lo {N k : Nat} (hv : Spec.Rsa.modulusValid N k = true) : N % 2 = 1 ∧ 256 ^ (k - 1) ≤ N := by
  rw [Spec.Rsa.modulusValid, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hv
  obtain ⟨⟨⟨h1, -⟩, -⟩, h4⟩ := hv
  exact ⟨by simpa using h1, of_decide_eq_true h4⟩

/-- Factors of a valid modulus, each shorter than it: odd and above 1. -/
theorem factors_of {N P Q k pl ql : Nat} (hN : N % 2 = 1) (hlo : 256 ^ (k - 1) ≤ N) (hP : P < 256 ^ pl)
    (hQ : Q < 256 ^ ql) (hpl : pl < k) (hql : ql < k) (h : P * Q = N) :
    P % 2 = 1 ∧ 1 < P ∧ Q % 2 = 1 ∧ 1 < Q := by
  have hp1 : 256 ^ pl ≤ 256 ^ (k - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hq1 : 256 ^ ql ≤ 256 ^ (k - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hpo := (pq_iff hN).mpr h
  have hqo := (pq_iff (P := Q) (Q := P) hN).mpr (by rw [Nat.mul_comm]; exact h)
  refine ⟨hpo.1, ?_, hqo.1, ?_⟩
  · rcases Nat.lt_or_ge 1 P with h1 | h1
    · exact h1
    · exfalso
      have : P * Q ≤ 1 * Q := Nat.mul_le_mul_right _ h1
      omega
  · rcases Nat.lt_or_ge 1 Q with h1 | h1
    · exact h1
    · exfalso
      have : P * Q ≤ P * 1 := Nat.mul_le_mul_left _ h1
      omega

theorem pow256_le_wk (len : Nat) : 256 ^ len ≤ 2 ^ (64 * ((len + 7) / 8)) := by
  rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by omega)

theorem pow256_le_w {len k : Nat} (h : len < k) : 256 ^ len ≤ 2 ^ (64 * wk k) := by
  rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by unfold wk; omega)

/-- `head`: the working space, the mask all ones, and `CvS` from the
memory on entry to `main`. -/
theorem cvHeadS_ok {I : CvIn} {s : State} (h : CvPre I s) :
    WP isa (.block head) s fun t => CvS I s.mem t ∧ mword t.mem I.B = mask true := by
  have L := h.L
  have hZ := L.z
  refine WP.mono (cvHead_ok h.scr h.x0 L.k1 L.k2 hZ h.args.k) fun s₁ ⟨hw₁, hm₁, f₁, k₁⟩ => ⟨?_, hm₁⟩
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eS : sStride = 28 := rfl
  have eM : Public.sMask = 22 := rfl
  have k1 := L.k1
  have hi₁ : InScr I.B I.Z s.mem s₁.mem := InScr.of_frm f₁ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega)
  exact ⟨hw₁, h.args.congr fun i hi => f₁.word_eq (fun r hr => by
      unfold argSlot at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega) (by unfold argSlot at hi; omega),
    h.n.congrK hi₁ k₁, h.p.congrK hi₁ k₁, h.q.congrK hi₁ k₁, h.d.congrK hi₁ k₁, hi₁, k₁.wr.trans h.wr⟩

/-- `main`, from a valid modulus. -/
theorem cvMain_ok {I : CvIn} {s : State} (h : CvPre I s) (hv : Spec.Rsa.modulusValid I.N I.k = true) :
    WP isa main s fun t => ∃ X : Nat, (I.ok = true → Spec.Rsa.inverse I.Q I.P = some X) ∧
      (List.range I.pl).map (fun i => t.mem (I.pQi + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if I.ok then X else 0) I.pl ∧
      (List.range I.pl).map (fun i => t.mem (I.pDp + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if I.ok then I.D % (I.P - 1) else 0) I.pl ∧
      (List.range I.ql).map (fun i => t.mem (I.pDq + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if I.ok then I.D % (I.Q - 1) else 0) I.ql ∧
      t.gpr .x0 = BitVec.ofNat 64 I.ok.toNat ∧
      (∀ x, I.Z ≤ ofs I.B x → (∀ i < I.pl, x ≠ I.pQi + BitVec.ofNat 64 i) →
        (∀ i < I.pl, x ≠ I.pDp + BitVec.ofNat 64 i) → (∀ i < I.ql, x ≠ I.pDq + BitVec.ofNat 64 i) →
        t.mem x = s.mem x) := by
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
  have eM : Public.sMask = 22 := rfl
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
  refine WP.seq (WP.mono (zeroA_ok h₅.ws (j := aX₁) (by decide)) fun s₆ ⟨_, o₆, _, _, _, k₆⟩ => ?_)
  have h₆ := h₅.arr (by decide) (Nat.le_refl _) o₆ k₆ (by decide)
  refine WP.mono (copyA_ok h₆.ws (o := aX₁) (a := aV) (by decide) (by decide) (by decide)) fun s₇ ⟨c₇, o₇, _, _, k₇⟩ => ?_
  have h₇ := h₆.arr (by decide) (by omega) o₇ k₇ (by decide)
  have ot : ∀ {m m' : Mem} {j i Ln : Nat}, Outside I.B (slot (wk I.k) j) Ln m m' → Ln ≤ 8 * (wk I.k + 2) → i ≠ j →
      i < 16 → wv m' I.B (slot (wk I.k) i) (wk I.k) = wv m I.B (slot (wk I.k) i) (wk I.k) :=
    fun o hL hij hi => outside_arr o hL hij (by omega) hi hZ' hn'
  have hmw : ∀ {m m' : Mem} {i L' : Nat}, Outside I.B (slot (wk I.k) i) L' m m' → L' ≤ 8 * (wk I.k + 2) →
      mword m' I.B = mword m I.B := fun {_ _ i _} o _ =>
    o.word (Or.inl (by have := hdr_lt_slot (wk I.k) i (show Public.sMask < 32 by decide); omega))
      (by omega)
  have m₇ : mword s₇.mem I.B = mask I.ok := by rw [hmw o₇ (by omega), hmw o₆ (Nat.le_refl _), m₅, m₄]
  have pr₇ : ∀ i, i = aP ∨ i = aQ ∨ i = aD ∨ i = aX₂ →
      wv s₇.mem I.B (slot (wk I.k) i) (wk I.k) = wv s₄.mem I.B (slot (wk I.k) i) (wk I.k) := fun i hi => by
    have h1 : i ≠ aX₁ := by rcases hi with rfl | rfl | rfl | rfl <;> decide
    have h2 : i < 16 := by rcases hi with rfl | rfl | rfl | rfl <;> decide
    rw [ot o₇ (by omega) h1 h2, ot o₆ (Nat.le_refl _) h1 h2,
      p₅ i (by rcases hi with rfl | rfl | rfl | rfl <;> simp)]
  have dP₇ : I.ok = true → wv s₇.mem I.B (slot (wk I.k) aX₁) (wk I.k) = I.D % (I.P - 1) := fun hc => by
    obtain ⟨hpq, -⟩ := hokP hc
    have hfp := hf hpq
    have e := d₅ hfp.1 hfp.2.1
    rw [c₇, ot o₆ (Nat.le_refl _) (by decide) (by decide)]
    rw [← e]
    refine wv_low_of_lt (by omega) ?_
    rw [e]
    have : I.D % (I.P - 1) < I.P - 1 := Nat.mod_lt _ (by omega)
    omega
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
  refine WP.mono (cvStores_ok h₈.ws h₈.args m₈ L.pl1 (by unfold wk; omega) L.ql1 (by unfold wk; omega)
    ⟨fun i hi => by rw [h₈.wr, ← h.wr]; exact h.oQi.wr i hi, h.oQi.sep⟩
    ⟨fun i hi => by rw [h₈.wr, ← h.wr]; exact h.oDp.wr i hi, h.oDp.sep⟩
    ⟨fun i hi => by rw [h₈.wr, ← h.wr]; exact h.oDq.wr i hi, h.oDq.sep⟩ h.a1 h.a2 h.a3)
    fun t ⟨bQi, bDp, bDq, hax, hfr, kt⟩ => ?_
  have vX₈ : wv s₈.mem I.B (slot (wk I.k) aX₂) (wk I.k) = wv s₄.mem I.B (slot (wk I.k) aX₂) (wk I.k) := by
    rw [p₈ aX₂ (by simp), pr₇ aX₂ (by simp)]
  have vX₁₈ : wv s₈.mem I.B (slot (wk I.k) aX₁) (wk I.k) = wv s₇.mem I.B (slot (wk I.k) aX₁) (wk I.k) :=
    p₈ aX₁ (by simp)
  refine ⟨wv s₄.mem I.B (slot (wk I.k) aX₂) (wk I.k), fun hc => ?_, ?_, ?_, ?_, hax,
    fun x hx n1 n2 n3 => by rw [hfr x n1 n2 n3, h₈.inScr x hx]⟩
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
      exact congrArg (Spec.Rsa.i2osp · I.pl) (wv_low_of_lt (by unfold wk; omega) (by omega))
  · rw [bDp]
    cases hc : I.ok
    · rfl
    · obtain ⟨hpq, -⟩ := hokP hc
      have hfp := hf hpq
      have e := dP₇ hc
      have := pow256_le_wk I.pl
      have : I.D % (I.P - 1) < I.P - 1 := Nat.mod_lt _ (by omega)
      simp only [ite_true]
      rw [← e, ← vX₁₈]
      exact congrArg (Spec.Rsa.i2osp · I.pl) (wv_low_of_lt (by unfold wk; omega) (by rw [vX₁₈, e]; omega))
  · rw [bDq]
    cases hc : I.ok
    · rfl
    · obtain ⟨hpq, -⟩ := hokP hc
      have hfp := hf hpq
      have e := d₈ hfp.2.2.1 hfp.2.2.2
      have := pow256_le_wk I.ql
      have : I.D % (I.Q - 1) < I.Q - 1 := Nat.mod_lt _ (by omega)
      simp only [ite_true]
      rw [← e]
      exact congrArg (Spec.Rsa.i2osp · I.ql) (wv_low_of_lt (by unfold wk; omega) (by rw [e]; omega))

end VG.Proof.Rsa.AArch64
