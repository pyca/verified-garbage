module
public import VerifiedGarbage.Impl.Rsa.AArch64.CheckKey
public import VerifiedGarbage.Proof.Rsa.AArch64.CkPhaseCore

import VerifiedGarbage.Proof.Rsa.AArch64.CkPhase
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.AArch64.CvMain
import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyPhase
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# `vg_rsa_check_key` on AArch64: `main`

The phases in sequence (`ckMain_ok`): the mask they leave is `keyValid`
of the key (`ck_final`), for a valid modulus and exponent.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG.Impl.Rsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.CheckKey
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The masks of the phases and'ed are `keyValid`. -/
theorem ck_final {k N E D P Q DP DQ QI : Nat} {dn pq gP gQ gQI : Bool} (hv : Spec.Rsa.modulusValid N k = true)
    (he : Spec.Rsa.exponentValid E = true) (hdn : dn = decide (D < N)) (hpq : pq = decide (P * Q = N))
    (hPn : P < N) (hQn : Q < N) (hf : P * Q = N → P % 2 = 1 ∧ 1 < P ∧ Q % 2 = 1 ∧ 1 < Q)
    (hgP : P % 2 = 1 → 1 < P → D < N → P * Q = N →
      gP = (decide (DP < P - 1) && decide (D * E % (P - 1) = 1) && decide (E * DP % (P - 1) = 1)))
    (hgQ : Q % 2 = 1 → 1 < Q → D < N → Q * P = N →
      gQ = (decide (DQ < Q - 1) && decide (D * E % (Q - 1) = 1) && decide (E * DQ % (Q - 1) = 1)))
    (hgQI : 0 < P → gQI = (decide (QI < P) && decide (Q * QI % P = 1))) :
    (gQI && (gQ && (gP && (pq && (dn && true))))) = Spec.Rsa.keyValid k N E D P Q DP DQ QI := by
  unfold Spec.Rsa.keyValid
  rw [hv, he, hdn, hpq]
  by_cases hd : D < N
  · by_cases h : P * Q = N
    · obtain ⟨p1, p2, q1, q2⟩ := hf h
      rw [hgP p1 p2 hd h, hgQ q1 q2 hd (by rw [Nat.mul_comm]; exact h), hgQI (by omega_arith)]
      have hb : ∀ a b : Nat, (a == b) = decide (a = b) := fun a b => by
        cases h' : decide (a = b) <;> simp_all
      simp only [hb, h, hPn, hQn, decide_true, Bool.true_and, Bool.and_true, Bool.and_assoc]
      generalize decide (D < N) = b0
      generalize decide (DP < P - 1) = b1
      generalize decide (D * E % (P - 1) = 1) = b2
      generalize decide (E * DP % (P - 1) = 1) = b3
      generalize decide (DQ < Q - 1) = b4
      generalize decide (D * E % (Q - 1) = 1) = b5
      generalize decide (E * DQ % (Q - 1) = 1) = b6
      generalize decide (QI < P) = b7
      generalize decide (Q * QI % P = 1) = b8
      revert b0 b1 b2 b3 b4 b5 b6 b7 b8
      decide
    · have : (P * Q == N) = false := by simpa using h
      simp [h, this]
  · simp only [hd, decide_false, Bool.false_and, Bool.and_false]

/-- What `main` needs on entry. -/
structure CkPre (I : CkIn) (s : State) : Prop where
  scr : Scr s I.B I.Z
  x0 : s.gpr .x0 = I.B
  args : CkArgs s.mem I.B I.k I.el I.dl I.pl I.ql I.pN I.pE I.pD I.pP I.pQ I.pDp I.pDq I.pQi
  n : Src s I.B I.Z I.pN I.nb
  e : Src s I.B I.Z I.pE I.eb
  d : Src s I.B I.Z I.pD I.db
  p : Src s I.B I.Z I.pP I.pb
  q : Src s I.B I.Z I.pQ I.qb
  dp : Src s I.B I.Z I.pDp I.dpb
  dq : Src s I.B I.Z I.pDq I.dqb
  qi : Src s I.B I.Z I.pQi I.qib
  L : CkLens I
  wr : s.wr = I.W

/-- `head`: the layout, the mask all ones, and `CkS` from the memory on
entry to `main`. -/
theorem ckHeadS_ok {I : CkIn} {s : State} (h : CkPre I s) (hc : I.cap = I.k) :
    WP isa (.block VG.Impl.Rsa.AArch64.CheckKey.head) s fun t => CkS I s.mem t ∧ mword t.mem I.B = mask true := by
  have L := h.L
  have hZ := L.z
  refine WP.mono (ckHead_ok h.scr h.x0 L.k1 L.k2 hZ h.args.k) fun s₁ ⟨hw₁, hm₁, f₁, k₁⟩ => ⟨?_, hm₁⟩
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eS : sStride = 28 := rfl
  have eM : Public.sMask = 22 := rfl
  have k1 := L.k1
  have hi₁ : InScr I.B I.Z s.mem s₁.mem := InScr.of_frm f₁ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith)
  exact ⟨L.fit, hc ▸ hw₁, h.args.congr fun i hi => f₁.word_eq (fun r hr => by
      unfold ckSlot at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith) (by unfold ckSlot at hi; omega_arith),
    h.n.congrK hi₁ k₁, h.e.congrK hi₁ k₁, h.d.congrK hi₁ k₁, h.p.congrK hi₁ k₁, h.q.congrK hi₁ k₁,
    h.dp.congrK hi₁ k₁, h.dq.congrK hi₁ k₁, h.qi.congrK hi₁ k₁, hi₁, k₁.wr.trans h.wr⟩

theorem ckMain_eq : VG.Impl.Rsa.AArch64.CheckKey.main = seqs (([.block VG.Impl.Rsa.AArch64.CheckKey.head] : List (Prog isa)) ++ (loadA 0 Public.sN Public.sK ++
    (loadA aE sE sElen ++ (([zeroA aOne, .block (setOneA aOne)] : List (Prog isa)) ++
    ((loadA aX sD sDlen ++ ltA aX 0) ++
    ((loadA aX sP sPlen ++ (loadA aR sQ sQlen ++ (mulXR ++ (eqA aA 0 ++ ([.block andZero] : List (Prog isa)))))) ++
    (modChecks sP sPlen sDP sQlen ++ (modChecks sQ sQlen sDQ sPlen ++
    ((loadA aM sP sPlen ++ (loadA aX sQI sPlen ++ (ltA aX aM ++ (loadA aR sQ sQlen ++ (mulXR ++ CheckCrtKey.modOne CheckCrtKey.topQ))))) ++
    ([.block retMask] : List (Prog isa))))))))))) := by
  simp only [VG.Impl.Rsa.AArch64.CheckKey.main, List.append_assoc]

/-- `main`, from a valid modulus and exponent: the mask of `keyValid`
returned. -/
theorem ckMain_ok {I : CkIn} {s : State} (h : CkPre I s) (hv : Spec.Rsa.modulusValid I.N I.k = true)
    (he : Spec.Rsa.exponentValid I.E = true) (hc : I.cap = I.k) :
    WP isa VG.Impl.Rsa.AArch64.CheckKey.main s fun t =>
      t.gpr .x0 = BitVec.ofNat 64 (Spec.Rsa.keyValid I.k I.N I.E I.D I.P I.Q I.DP I.DQ I.QI).toNat := by
  have L := h.L
  have k1 := L.k1
  obtain ⟨hNo, hlo⟩ := valid_lo hv
  have hE64 : I.E < 2 ^ 64 := by
    simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, decide_eq_true_eq] at he
    omega
  have hPl : I.P < 256 ^ I.pl := by have := os2ip_lt I.pb; rw [L.pbl] at this; exact this
  have hQl : I.Q < 256 ^ I.ql := by have := os2ip_lt I.qb; rw [L.qbl] at this; exact this
  have hPn : I.P < I.N := Nat.lt_of_lt_of_le hPl ((Nat.pow_le_pow_right (by decide) (by have := L.pl2; omega_arith)).trans hlo)
  have hQn : I.Q < I.N := Nat.lt_of_lt_of_le hQl ((Nat.pow_le_pow_right (by decide) (by have := L.ql2; omega_arith)).trans hlo)
  rw [ckMain_eq]
  refine wp_seqs_append (by simp) (by simp [loadA]) (WP.mono (ckHeadS_ok h hc) fun s₁ ⟨h₁, m₁⟩ => ?_)
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (ckLoad_ok h₁ (j := 0) (by decide) (by decide)
    (by decide) h₁.args.n h₁.args.k h₁.n L.nl (by omega_arith) (Nat.le_refl _)) fun s₂ ⟨h₂, m₂, v₂, o₂⟩ => ?_)
  refine wp_seqs_append (by simp [loadA]) (by simp) (WP.mono (ckLoad_ok h₂ (j := aE) (by decide) (by decide)
    (by decide) h₂.args.e h₂.args.el h₂.e L.ebl L.el1 L.el2) fun s₃ ⟨h₃, m₃, v₃, o₃⟩ => ?_)
  refine wp_seqs_append (by simp) (by simp [loadA]) (WP.mono (ckOne_ok h₃) fun s₄ ⟨h₄, m₄, v₄, o₄⟩ => ?_)
  have k₄ : KS I s.mem true s₄ := ⟨h₄, by rw [m₄, m₃, m₂, m₁],
    by rw [o₄ 0 (by decide) (by decide), o₃ 0 (by decide) (by decide), v₂],
    by rw [o₄ aE (by decide) (by decide), v₃], v₄⟩
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (phDN_ok k₄ L) fun s₅ k₅ => ?_)
  refine wp_seqs_append (by simp [loadA]) (by simp [modChecks]) (WP.mono (phPQ_ok k₅ L) fun s₆ k₆ => ?_)
  refine wp_seqs_append (by simp [modChecks]) (by simp [modChecks]) (WP.mono (phMod_ok k₆ L hE64
    (by decide) (by decide) (by decide) L.pl1 L.pl2 L.pcap L.pbl L.dpbl
    (fun t ht => ⟨ht.args.p, ht.args.pl, ht.p, ht.args.dp, ht.dp⟩)
    (Y := I.Q) (by decide) L.qcap (fun _ h => h.args.ql)
    (lt_w (by rw [L.qbl]))
    (by simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he; exact he.2)) fun s₇ ⟨gP, k₇, hgP⟩ => ?_)
  refine wp_seqs_append (by simp [modChecks]) (by simp [loadA]) (WP.mono (phMod_ok k₇ L hE64
    (by decide) (by decide) (by decide) L.ql1 L.ql2 L.qcap L.qbl L.dqbl
    (fun t ht => ⟨ht.args.q, ht.args.ql, ht.q, ht.args.dq, ht.dq⟩)
    (Y := I.P) (by decide) L.pcap (fun _ h => h.args.pl)
    (lt_w (by rw [L.pbl]))
    (by simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he; exact he.2)) fun s₈ ⟨gQ, k₈, hgQ⟩ => ?_)
  refine wp_seqs_append (by simp [loadA]) (by simp) (WP.mono (phQIC_ok k₈ L) fun s₉ ⟨gQI, k₉, hgQI⟩ => ?_)
  obtain ⟨h₉, m₉, -⟩ := k₉
  refine WP.mono (cvExit_ok h₉.ws m₉) fun t ⟨⟨hx, _⟩, _⟩ => ?_
  rw [hx, ck_final hv he rfl rfl hPn hQn (factors_of hNo hlo hPl hQl L.pl2 L.ql2) hgP hgQ hgQI]

end VG.Proof.Rsa.AArch64
