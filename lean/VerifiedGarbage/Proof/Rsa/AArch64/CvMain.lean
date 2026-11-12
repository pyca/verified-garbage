module

public import VerifiedGarbage.Proof.Rsa.AArch64.InvLaw
public import VerifiedGarbage.Proof.Rsa.AArch64.CvCheck
public import VerifiedGarbage.Proof.Rsa.AArch64.CvStore
import VerifiedGarbage.Proof.Rsa.KeyMath
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Rsa.AArch64.WDiv
import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# `vg_rsa_crt_values` on AArch64: `main`

From a valid modulus, `main` writes `dP`, `dQ` and `qInv` if `p q = n`
and `gcd(q, p) = 1`, and zeros otherwise (`cvMain_ok`).
-/

@[expose] public section

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
    (pqCheck ++ (invPart ++ (([wordChoice aP] : List (Prog isa)) ++
    (([zeroA aX₁, copyA aX₁ aV] : List (Prog isa)) ++
    (([wordChoice aQ] : List (Prog isa)) ++
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
  have hp1 : 256 ^ pl ≤ 256 ^ (k - 1) := Nat.pow_le_pow_right (by decide) (by omega_arith)
  have hq1 : 256 ^ ql ≤ 256 ^ (k - 1) := Nat.pow_le_pow_right (by decide) (by omega_arith)
  have hpo := (pq_iff hN).mpr h
  have hqo := (pq_iff (P := Q) (Q := P) hN).mpr (by rw [Nat.mul_comm]; exact h)
  refine ⟨hpo.1, ?_, hqo.1, ?_⟩
  · rcases Nat.lt_or_ge 1 P with h1 | h1
    · exact h1
    · exfalso
      have : P * Q ≤ 1 * Q := Nat.mul_le_mul_right _ h1
      omega_arith
  · rcases Nat.lt_or_ge 1 Q with h1 | h1
    · exact h1
    · exfalso
      have : P * Q ≤ P * 1 := Nat.mul_le_mul_left _ h1
      omega_arith

theorem pow256_le_wk (len : Nat) : 256 ^ len ≤ 2 ^ (64 * ((len + 7) / 8)) := by
  rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by omega_arith)

theorem pow256_le_w {len k : Nat} (h : len < k) : 256 ^ len ≤ 2 ^ (64 * wk k) := by
  rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by unfold wk; omega_arith)

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
    rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith)
  exact ⟨hw₁, h.args.congr fun i hi => f₁.word_eq (fun r hr => by
      unfold argSlot at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith) (by unfold argSlot at hi; omega_arith),
    h.n.congrK hi₁ k₁, h.p.congrK hi₁ k₁, h.q.congrK hi₁ k₁, h.d.congrK hi₁ k₁, hi₁, k₁.wr.trans h.wr⟩

/-- `wordChoice j`: `[aV] := d mod ([j] - 1)` when `p q = n`, by `wdiv` if the
guard passes, by `divmod` otherwise. -/
theorem cvWordChoice_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) {j : Nat}
    (hj : j = aP ∨ j = aQ) (hP : wv s.mem I.B (slot (wk I.k) aP) (wk I.k) = I.P)
    (hQ : wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) = I.Q)
    (hf : I.P * I.Q = I.N → I.P % 2 = 1 ∧ 1 < I.P ∧ I.Q % 2 = 1 ∧ 1 < I.Q) :
    WP isa (wordChoice j) s fun t =>
      CvS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      (I.P * I.Q = I.N → wv t.mem I.B (slot (wk I.k) aV) (wk I.k + 1) =
          wv s.mem I.B (slot (wk I.k) aD) (wk I.k) % (wv s.mem I.B (slot (wk I.k) j) (wk I.k) - 1)) ∧
      ∀ i, i = aP ∨ i = aQ ∨ i = aD ∨ i = aX₁ ∨ i = aX₂ →
        wv t.mem I.B (slot (wk I.k) i) (wk I.k) = wv s.mem I.B (slot (wk I.k) i) (wk I.k) := by
  have hk1 := L.k1
  have hk2 := L.k2
  have hpl := L.pl2
  have hql := L.ql2
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have h256 := h.ws.h256
  have hn0 : 0 < I.nb.length := by rw [L.nl]; omega_arith
  have hX : wv s.mem I.B (slot (wk I.k) j) (wk I.k) = I.P ∨ wv s.mem I.B (slot (wk I.k) j) (wk I.k) = I.Q := by
    rcases hj with rfl | rfl
    exacts [.inl hP, .inr hQ]
  have hXo : I.P * I.Q = I.N → wv s.mem I.B (slot (wk I.k) j) (wk I.k) % 2 = 1 ∧
      1 < wv s.mem I.B (slot (wk I.k) j) (wk I.k) := fun he => by
    have := hf he
    rcases hX with e | e <;> rw [e] <;> omega_arith
  unfold wordChoice
  refine WP.seq (WP.mono (wordGuard_ok (b := s.mem.read I.pN 1) h.ws.scr h.ws.x0 h256 (by decide) (by decide)
    h.args.k h.args.pl h.args.ql h.args.n rfl (by simpa using h.n.rd 0 hn0)) fun s₁ ⟨⟨h9, m₁⟩, k₁⟩ => ?_)
  have h₁ := h.step (rs := []) (by rw [m₁]; exact Frm.refl _ _ _) (by simp) (by simp) k₁ (by decide)
  have e₁ : ∀ i, wv s₁.mem I.B (slot (wk I.k) i) (wk I.k) = wv s.mem I.B (slot (wk I.k) i) (wk I.k) := fun i => by
    rw [m₁]
  refine WP.ite (s₁.gpr .x9 == 0) (VG.Proof.MlKem.AArch64.eval_zero _ _) (fun hb => ?_) (fun _ => ?_)
  · -- The guard passes: `wdiv`.
    have hg : guardVal I.k I.pl I.ql (s.mem.read I.pN 1) = 0 := by
      rw [← h9]; simpa using hb
    obtain ⟨g16, g2, gpq, gb⟩ := guard_zero (by omega_arith) (by omega_arith) (by omega_arith) hg
    have hb0 : 128 ≤ (I.nb[0]'hn0).toNat := by
      rw [read_one, show I.pN = I.pN + BitVec.ofNat 64 0 by simp, h.n.val 0 hn0] at gb; exact gb
    have hw8 : 8 ≤ wk I.k := by unfold wk; omega_arith
    have hwk : wk I.k = I.k / 8 := by unfold wk; omega_arith
    refine wp_seqs_append (by simp [divisor]) (by simp) (WP.mono (cvDivisor_ok h₁ L hj) fun s₂ ⟨h₂, m₂, c₂, _, f₂⟩ => ?_)
    simp only [seqs]
    have hwm := cvWm_ok (wk I.k) (by unfold wk; omega_arith)
    have hL := cvLen_ok (wk I.k)
    have hxb := cvXb_ok I.B (wk I.k) (by unfold wk; omega_arith) (by unfold wk; omega_arith)
    refine WP.mono (wdiv_ok h₂.ws (iX := aD) (iM := aC) (iR := aV) (iT := aT) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hwm hL hxb (by omega_arith)
      (by omega_arith) (by omega_arith) (by omega_arith)) fun t ⟨_, ft, kt, hval⟩ => ?_
    have ht := h₂.step ft (fun r hr => by
      simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Mut.ofSlot _ _ _) (fun r hr => by
      simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> exact h.ws.sl (by decide)) kt (by decide)
    have fA : ∀ i, i < 16 → i ≠ aC → i ≠ aV → i ≠ aT → i ≠ aU →
        wv t.mem I.B (slot (wk I.k) i) (wk I.k) = wv s.mem I.B (slot (wk I.k) i) (wk I.k) := fun i hi h1 h2 h3 h4 => by
      rw [ft.wv_eq (fun r hr => by
        simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> dsimp only
        · have := slot_sep (w := wk I.k) h2; omega_arith
        · have := slot_sep (w := wk I.k) h3; omega_arith) (by have := h.ws.sl hi; omega_arith),
        f₂.wv_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> dsimp only
        · have := slot_sep (w := wk I.k) h1; omega_arith
        · have := slot_sep (w := wk I.k) h4; omega_arith) (by have := h.ws.sl hi; omega_arith), e₁]
    refine ⟨ht, ?_, fun he => ?_, fun i hi => ?_⟩
    · show word t.mem I.B (8 * Public.sMask) = word s.mem I.B (8 * Public.sMask)
      rw [ft.word_eq (fun r hr => by
        simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> dsimp only <;>
          exact .inl (hdr_lt_slot _ _ (show Public.sMask < 32 by decide))) (by unfold Public.sMask sFn; omega_arith),
        ← m₁]
      exact m₂
    · -- `[aC] = X - 1` with its top bit set.
      obtain ⟨fp, fq⟩ := guard_factors L.nl (by omega_arith) L.pbl L.qbl g16 g2 gpq hb0 he
      have hXf : 2 ^ (64 * (wk I.k / 2) - 1) ≤ wv s.mem I.B (slot (wk I.k) j) (wk I.k) - 1 ∧
          wv s.mem I.B (slot (wk I.k) j) (wk I.k) < 2 ^ (64 * (wk I.k / 2)) := by
        rcases hX with e | e <;> rw [e]
        exacts [fp, fq]
      have hC₂ := c₂ (by rw [e₁]; exact (hXo he).1)
      rw [e₁] at hC₂
      have hC₂m : wv s₂.mem I.B (slot (wk I.k) aC) (wk I.k / 2) = wv s.mem I.B (slot (wk I.k) j) (wk I.k) - 1 := by
        have hb : wv s₂.mem I.B (slot (wk I.k) aC) (wk I.k) < 2 ^ (64 * (wk I.k / 2)) := by
          rw [hC₂]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) hXf.2
        rw [wv_low_of_lt (by omega_arith) hb, hC₂]
      have htop : 2 ^ 63 ≤ (word s₂.mem I.B (slot (wk I.k) aC + 8 * (wk I.k / 2 - 1))).toNat := by
        rw [word_of_wv _ _ _ (wk I.k / 2) (by omega_arith), hC₂m]
        exact top_word_of (by omega_arith) hXf.1 (by omega_arith)
      have hval := hval htop
      rw [hC₂m] at hval
      have pDC := slot_sep (w := wk I.k) (show aD ≠ aC by decide)
      have pDU := slot_sep (w := wk I.k) (show aD ≠ aU by decide)
      have sD := h.ws.sl (j := aD) (by decide)
      have hD₂ : wv s₂.mem I.B (slot (wk I.k) aD) (wk I.k) = wv s.mem I.B (slot (wk I.k) aD) (wk I.k) := by
        rw [f₂.wv_eq (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith), e₁]
      rw [hD₂] at hval
      have hX0 : 0 < wv s.mem I.B (slot (wk I.k) j) (wk I.k) - 1 := by
        have := Nat.two_pow_pos (64 * (wk I.k / 2) - 1); omega_arith
      have hle : 2 ^ (64 * (wk I.k / 2)) ≤ 2 ^ (64 * (wk I.k + 1)) := Nat.pow_le_pow_right (by decide) (by omega_arith)
      have hlt : wv t.mem I.B (slot (wk I.k) aV) (wk I.k + 2) < 2 ^ (64 * (wk I.k + 1)) := by
        rw [hval]
        exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hX0) (Nat.le_trans (Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hXf.2)) hle)
      rw [wv_low_of_lt (by omega_arith) hlt, hval]
    · have hi16 : i < 16 := by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
      exact fA i hi16 (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide) (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)
  · -- `divmod`.
    refine WP.mono (cvDivPart_ok h₁ L hj) fun t ⟨ht, mt, vt, pt⟩ => ⟨ht, by rw [mt, m₁], fun he => ?_, fun i hi => by
      rw [pt i hi, e₁]⟩
    obtain ⟨o, g⟩ := hXo he
    rw [vt (by rw [e₁]; exact o) (by rw [e₁]; exact g), e₁, e₁]

/-- `main`, from a valid modulus. -/
theorem cvMain_ok [InvLaw] {I : CvIn} {s : State} (h : CvPre I s) (hv : Spec.Rsa.modulusValid I.N I.k = true) :
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
    (by rw [m₂]; exact hm₁) (by rw [vP]; exact hPl) (by rw [vQ]; exact hQl)) fun s₃ ⟨h₃, ⟨c₃, m₃, e₃⟩, p₃⟩ => ?_)
  rw [e₃] at m₃
  rw [vP, vQ, vN, Bool.true_and] at m₃
  have vP₃ : wv s₃.mem I.B (slot (wk I.k) aP) (wk I.k) = I.P := by rw [p₃ aP (.inl rfl), vP]
  have vQ₃ : wv s₃.mem I.B (slot (wk I.k) aQ) (wk I.k) = I.Q := by rw [p₃ aQ (.inr (.inl rfl)), vQ]
  have vD₃ : wv s₃.mem I.B (slot (wk I.k) aD) (wk I.k) = I.D := by rw [p₃ aD (.inr (.inr rfl)), vD]
  have hf : I.P * I.Q = I.N → I.P % 2 = 1 ∧ 1 < I.P ∧ I.Q % 2 = 1 ∧ 1 < I.Q :=
    factors_of hNo hlo hPl hQl L.pl2 L.ql2
  -- `qInv` and `gcd(q, p) = 1`.
  refine wp_seqs_append (by simp [invPart]) (by simp) (WP.mono (cvInv_ok h₃ L m₃ (fun hc => by
    rw [vP₃]; have := hf (of_decide_eq_true hc); exact ⟨this.1, this.2.1⟩) (by rw [vP₃]; exact hPl)
    (by rw [vQ₃]; exact hQl)) fun s₄ ⟨h₄, m₄, i₄, p₄⟩ => ?_)
  rw [vP₃, vQ₃] at m₄ i₄
  have vP₄ : wv s₄.mem I.B (slot (wk I.k) aP) (wk I.k) = I.P := by rw [p₄ aP (.inl rfl), vP₃]
  have vQ₄ : wv s₄.mem I.B (slot (wk I.k) aQ) (wk I.k) = I.Q := by rw [p₄ aQ (.inr (.inl rfl)), vQ₃]
  have vD₄ : wv s₄.mem I.B (slot (wk I.k) aD) (wk I.k) = I.D := by rw [p₄ aD (.inr (.inr rfl)), vD₃]
  have hok : (decide (I.P * I.Q = I.N) && decide (Nat.gcd I.Q I.P = 1)) = I.ok := by
    simp only [CvIn.ok, Bool.decide_and]
  rw [hok] at m₄
  have hokP : I.ok = true → I.P * I.Q = I.N ∧ Nat.gcd I.Q I.P = 1 := fun hc => of_decide_eq_true hc
  -- `dP` into `aV`.
  refine wp_seqs_append (by simp) (by simp) (WP.mono (cvWordChoice_ok h₄ L (j := aP) (.inl rfl) vP₄ vQ₄ hf)
    fun s₅ ⟨h₅, m₅, d₅, p₅⟩ => ?_)
  rw [vP₄, vD₄] at d₅
  -- `dP` into `aX₁`.
  have hZ' := h₅.ws.hZ
  have hn' := h₅.ws.scr.nowrap
  refine wp_seqs_append (by simp) (by simp) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_ok h₅.ws (j := aX₁) (by decide)) fun s₆ ⟨_, o₆, _, _, _, k₆⟩ => ?_)
  have h₆ := h₅.arr (by decide) (Nat.le_refl _) o₆ k₆ (by decide)
  refine WP.mono (copyA_ok h₆.ws (o := aX₁) (a := aV) (by decide) (by decide) (by decide)) fun s₇ ⟨c₇, o₇, _, _, k₇⟩ => ?_
  have h₇ := h₆.arr (by decide) (by omega_arith) o₇ k₇ (by decide)
  have ot : ∀ {m m' : Mem} {j i Ln : Nat}, Outside I.B (slot (wk I.k) j) Ln m m' → Ln ≤ 8 * (wk I.k + 2) → i ≠ j →
      i < 16 → wv m' I.B (slot (wk I.k) i) (wk I.k) = wv m I.B (slot (wk I.k) i) (wk I.k) :=
    fun o hL hij hi => outside_arr o hL hij (by omega_arith) hi hZ' hn'
  have hmw : ∀ {m m' : Mem} {i L' : Nat}, Outside I.B (slot (wk I.k) i) L' m m' → L' ≤ 8 * (wk I.k + 2) →
      mword m' I.B = mword m I.B := fun {_ _ i _} o _ =>
    o.word (Or.inl (by have := hdr_lt_slot (wk I.k) i (show Public.sMask < 32 by decide); omega_arith))
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
    have e := d₅ hpq
    rw [c₇, ot o₆ (Nat.le_refl _) (by decide) (by decide)]
    rw [← e]
    refine wv_low_of_lt (by omega_arith) ?_
    rw [e]
    have : I.D % (I.P - 1) < I.P - 1 := Nat.mod_lt _ (by omega_arith)
    omega_arith
  -- `dQ` into `aV`.
  have vQ₇ : wv s₇.mem I.B (slot (wk I.k) aQ) (wk I.k) = I.Q := by rw [pr₇ aQ (by simp), vQ₄]
  have vD₇ : wv s₇.mem I.B (slot (wk I.k) aD) (wk I.k) = I.D := by rw [pr₇ aD (by simp), vD₄]
  have vP₇ : wv s₇.mem I.B (slot (wk I.k) aP) (wk I.k) = I.P := by rw [pr₇ aP (by simp), vP₄]
  refine wp_seqs_append (by simp) (by simp [storeA]) (WP.mono (cvWordChoice_ok h₇ L (j := aQ) (.inr rfl) vP₇ vQ₇ hf)
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
      have e := d₈ hpq
      have := pow256_le_wk I.ql
      have : I.D % (I.Q - 1) < I.Q - 1 := Nat.mod_lt _ (by omega_arith)
      simp only [ite_true]
      rw [← e]
      exact congrArg (Spec.Rsa.i2osp · I.ql) (wv_low_of_lt (by unfold wk; omega_arith) (by rw [e]; omega_arith))

end VG.Proof.Rsa.AArch64
