import VerifiedGarbage.Proof.Rsa.AArch64.CkMain
import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyPhase

/-!
# `vg_rsa_check_crt_key` on AArch64: `main`

`vg_rsa_check_key`'s phases without `d < n` and the checks of `d`, with the
shortened remainders (`phModC_ok`, `phQIC_ok`): the mask they leave is
`crtKeyValid` of the key (`ckc_final`), for a valid modulus and exponent.
The inputs are `CkIn`'s, with `p` as `d` (the entry stores `p` in `d`'s
slots, which nothing reads).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.CheckKey (sE sElen sP sPlen sQ sQlen sDP sDQ sQI aX aR aM aA aE aOne ltA mulXR)
open VG.Impl.Rsa.AArch64.CheckCrtKey (modChecks modOne topQ)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

/-- The masks of the phases and'ed are `crtKeyValid`. -/
theorem ckc_final {k N E P Q DP DQ QI : Nat} {pq gP gQ gQI : Bool} (hv : Spec.Rsa.modulusValid N k = true)
    (he : Spec.Rsa.exponentValid E = true) (hpq : pq = decide (P * Q = N))
    (hf : P * Q = N → P % 2 = 1 ∧ 1 < P ∧ Q % 2 = 1 ∧ 1 < Q)
    (hgP : P % 2 = 1 → 1 < P → gP = (decide (DP < P - 1) && decide (E * DP % (P - 1) = 1)))
    (hgQ : Q % 2 = 1 → 1 < Q → gQ = (decide (DQ < Q - 1) && decide (E * DQ % (Q - 1) = 1)))
    (hgQI : 0 < P → gQI = (decide (QI < P) && decide (Q * QI % P = 1))) :
    (gQI && (gQ && (gP && (pq && true)))) = Spec.Rsa.crtKeyValid k N E P Q DP DQ QI := by
  unfold Spec.Rsa.crtKeyValid
  rw [hv, he, hpq]
  by_cases h : P * Q = N
  · obtain ⟨p1, p2, q1, q2⟩ := hf h
    rw [hgP p1 p2, hgQ q1 q2, hgQI (by omega)]
    have hb : ∀ a b : Nat, (a == b) = decide (a = b) := fun a b => by
      cases h' : decide (a = b) <;> simp_all
    simp only [hb, h, decide_true, Bool.true_and, Bool.and_true, Bool.and_assoc]
    cases decide (DP < P - 1) <;> cases decide (E * DP % (P - 1) = 1) <;> cases decide (DQ < Q - 1) <;>
      cases decide (E * DQ % (Q - 1) = 1) <;> cases decide (QI < P) <;> cases decide (Q * QI % P = 1) <;> rfl
  · have : (P * Q == N) = false := by simpa using h
    simp [h, this]

theorem ckcMain_eq : VG.Impl.Rsa.AArch64.CheckCrtKey.main = seqs (([.block VG.Impl.Rsa.AArch64.CheckKey.head] : List (Prog isa)) ++
    (loadA 0 Public.sN Public.sK ++
    (loadA aE sE sElen ++ (([zeroA aOne, .block (setOneA aOne)] : List (Prog isa)) ++
    ((loadA aX sP sPlen ++ (loadA aR sQ sQlen ++ (mulXR ++ (eqA aA 0 ++ ([.block andZero] : List (Prog isa)))))) ++
    (modChecks sP sPlen sDP ++ (modChecks sQ sQlen sDQ ++
    ((loadA aM sP sPlen ++ (loadA aX sQI sPlen ++ (ltA aX aM ++ (loadA aR sQ sQlen ++ (mulXR ++ modOne topQ))))) ++
    ([.block retMask] : List (Prog isa)))))))))) := by
  simp only [VG.Impl.Rsa.AArch64.CheckCrtKey.main, List.append_assoc]

/-- `main`, from a valid modulus and exponent: the mask of `crtKeyValid`
returned. -/
theorem ckcMain_ok {I : CkIn} {s : State} (h : CkPre I s) (hv : Spec.Rsa.modulusValid I.N I.k = true)
    (he : Spec.Rsa.exponentValid I.E = true) :
    WP isa VG.Impl.Rsa.AArch64.CheckCrtKey.main s fun t =>
      t.gpr .x0 = BitVec.ofNat 64 (Spec.Rsa.crtKeyValid I.k I.N I.E I.P I.Q I.DP I.DQ I.QI).toNat := by
  have L := h.L
  have k1 := L.k1
  obtain ⟨hNo, hlo⟩ := valid_lo hv
  have hE64 : I.E < 2 ^ 64 := by
    simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, decide_eq_true_eq] at he
    omega
  have hPl : I.P < 256 ^ I.pl := by have := os2ip_lt I.pb; rw [L.pbl] at this; exact this
  have hQl : I.Q < 256 ^ I.ql := by have := os2ip_lt I.qb; rw [L.qbl] at this; exact this
  have hPn : I.P < I.N := Nat.lt_of_lt_of_le hPl ((Nat.pow_le_pow_right (by decide) (by have := L.pl2; omega)).trans hlo)
  have hQn : I.Q < I.N := Nat.lt_of_lt_of_le hQl ((Nat.pow_le_pow_right (by decide) (by have := L.ql2; omega)).trans hlo)
  rw [ckcMain_eq]
  refine wp_seqs_append (by simp) (by simp [loadA]) (WP.mono (ckHeadS_ok h) fun s₁ ⟨h₁, m₁⟩ => ?_)
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (ckLoad_ok h₁ (j := 0) (by decide) (by decide)
    (by decide) h₁.args.n h₁.args.k h₁.n L.nl (by omega) (Nat.le_refl _)) fun s₂ ⟨h₂, m₂, v₂, o₂⟩ => ?_)
  refine wp_seqs_append (by simp [loadA]) (by simp) (WP.mono (ckLoad_ok h₂ (j := aE) (by decide) (by decide)
    (by decide) h₂.args.e h₂.args.el h₂.e L.ebl L.el1 L.el2) fun s₃ ⟨h₃, m₃, v₃, o₃⟩ => ?_)
  refine wp_seqs_append (by simp) (by simp [loadA]) (WP.mono (ckOne_ok h₃) fun s₄ ⟨h₄, m₄, v₄, o₄⟩ => ?_)
  have k₄ : KS I s.mem true s₄ := ⟨h₄, by rw [m₄, m₃, m₂, m₁],
    by rw [o₄ 0 (by decide) (by decide), o₃ 0 (by decide) (by decide), v₂],
    by rw [o₄ aE (by decide) (by decide), v₃], v₄⟩
  refine wp_seqs_append (by simp [loadA]) (by simp [modChecks]) (WP.mono (phPQ_ok k₄ L) fun s₆ k₆ => ?_)
  refine wp_seqs_append (by simp [modChecks]) (by simp [modChecks]) (WP.mono (phModC_ok k₆ L hE64
    (by decide) (by decide) (by decide) L.pl1 L.pl2 L.pbl L.dpbl
    (fun t ht => ⟨ht.args.p, ht.args.pl, ht.p, ht.args.dp, ht.dp⟩)) fun s₇ ⟨gP, k₇, hgP⟩ => ?_)
  refine wp_seqs_append (by simp [modChecks]) (by simp [loadA]) (WP.mono (phModC_ok k₇ L hE64
    (by decide) (by decide) (by decide) L.ql1 L.ql2 L.qbl L.dqbl
    (fun t ht => ⟨ht.args.q, ht.args.ql, ht.q, ht.args.dq, ht.dq⟩)) fun s₈ ⟨gQ, k₈, hgQ⟩ => ?_)
  refine wp_seqs_append (by simp [loadA]) (by simp) (WP.mono (phQIC_ok k₈ L) fun s₉ ⟨gQI, k₉, hgQI⟩ => ?_)
  obtain ⟨h₉, m₉, -⟩ := k₉
  refine WP.mono (cvExit_ok h₉.ws m₉) fun t ⟨⟨hx, _⟩, _⟩ => ?_
  rw [hx, ckc_final hv he rfl (factors_of hNo hlo hPl hQl L.pl2 L.ql2) hgP hgQ hgQI]

end VG.Proof.Rsa.AArch64
