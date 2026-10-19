module

public import VerifiedGarbage.Proof.Rsa.CrtValuesMask
public import VerifiedGarbage.Proof.Rsa.Arm.CvChecksA

/-! # `vg_rsa_crt_values` on ARMv7: the inverse, the mask, and the division of `d` set up -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

/-- The mask of the checks, from the quotient `X₁` and remainder `X₂` of `n / p` and the gcd `V`. -/
abbrev maskOf := VG.Proof.Rsa.CrtValues.maskOf

/-- Before the division of `d` by `p - 1`. -/
structure StD (s0 : State) (X₁ X₂ : Nat) (s : State) : Prop where
  base : Base s0 s
  ws : Ws s (cvB s0) (cvZ s0) (cvW s0) nArr
  count : s.mem.readW (off (State.addr (cvB s0)) 16) 32 = BitVec.ofNat 32 (cvW s0)
  q : num s.mem (cvB s0) (cvW s0) aQ = cvQ s0
  d : num s.mem (cvB s0) (cvW s0) aD = cvD s0
  ddTop : w32 s.mem (State.addr (cvB s0)) (arr (cvW s0) aDD + 4 * cvW s0) = 0
  dq : num s.mem (cvB s0) (cvW s0) aDQ = cvD s0
  dd : num s.mem (cvB s0) (cvW s0) aDD = 2 * (cvP s0 / 2)
  hdr : DivHdr s.mem (cvB s0) (cvW s0) aDQ aDR2 aDD aDT
  mask : ∃ V, slot s.mem (cvB s0) sMask = (if maskOf (cvP s0) (cvQ s0) X₁ X₂ V then 1 else 0) ∧
    (1 < cvM s0 → V = Nat.gcd (cvQ s0) (cvM s0) ∧
      (cvM s0 : Int) ∣ (num s.mem (cvB s0) (cvW s0) 3 : Int) * cvQ s0 - V ∧
      num s.mem (cvB s0) (cvW s0) 3 < cvM s0)

theorem checksB_ok {s0 s : State} {X₁ X₂ : Nat} (h : StI s0 X₁ X₂ s) :
    WP isa (seqs checksB) s (StD s0 X₁ X₂) := by
  have pre := h.base.pre
  have hw := h.ws
  have fit := fun j (hj : j < nArr) => hw.fit64 (j := j) hj
  unfold checksB
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (inverse_ok hw (by decide) (by decide)) fun t1 ⟨h1, k1, r1, inv⟩ => ?_
  have I := fun (hM : 1 < cvM s0) => inv (by rw [h.m, h.nm]) h.zero (by rw [h.m]; simp only [cvM]; omega)
    (by rw [h.m]; exact hM) (by simp only [bank]; rw [h.u, h.v, h.x₁, h.x₂, h.m])
  rw [h.m, h.u] at I
  have b1 := h.base.keep k1 (by decide) (by decide) (by decide) r1.sp r1.rd r1.wr
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h1 (d := sE3) (a := 1) (b := aOne) (t := aT1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  have one1 : num t1.mem (cvB s0) (cvW s0) aOne = 1 := by
    rw [k1.num (by decide) (by decide) (fit _ (by decide)), h.one]
  rw [one1] at e2
  have sl : ∀ d, d + 4 ≤ hdr → d % 4 = 0 → d ∉ [sT, sE3, sOdd, sB, sC] →
      slot t2.mem (cvB s0) d = slot s.mem (cvB s0) d := fun d hd h4 hn => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    simp only [sT, sE3, sOdd, sB, sC, hdr] at hn hd
    rw [k2.slot (by simp only [hdr]; omega) (by simp only [sT, sE3]; simp; omega),
      k1.slot (by simp only [hdr]; omega) (by simp only [invSlots, sOdd, sB, sC]; simp; omega)]
  rw [wp_seqs_cons (List.cons_ne_nil _ _), List.append_assoc, ← List.append_nil (andS sMask sMask sE3)]
  refine andS_ok h2 (d := sMask) (a := sPodd) (b := sE1) (by decide) (by decide) (by decide)
    (by rw [sl _ (by decide) (by decide) (by decide), h.podd]; omega) (by rw [sl _ (by decide) (by decide) (by decide), h.e1]; split <;> omega)
    fun t3a h3a k3a m3a r3a => ?_
  refine andS_ok h3a (d := sMask) (a := sMask) (b := sE2) (by decide) (by decide) (by decide)
    (by rw [m3a]; split <;> omega) (by rw [k3a.slot (by decide) (by decide), sl _ (by decide) (by decide) (by decide), h.e2]; split <;> omega)
    fun t3b h3b k3b m3b r3b => ?_
  refine andS_ok h3b (d := sMask) (a := sMask) (b := sE3) (by decide) (by decide) (by decide)
    (by rw [m3b]; split <;> omega)
    (by rw [k3b.slot (by decide) (by decide), k3a.slot (by decide) (by decide), e2]; split <;> omega)
    fun t3 h3 k3 m3 r3 => WP.block_nil ?_
  have K3 : Keep (cvB s0) (cvW s0) [] [sMask] t2.mem t3.mem := k3a.trans (k3b.trans k3)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h3 (o := aDQ) (a := aD) (by decide) (by decide) (by decide) (by decide))
    fun t4 ⟨h4, k4, e4, r4, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h4 (o := aDD) (a := aP) (by decide) (by decide) (by decide) (by decide))
    fun t5 ⟨h5, k5, e5, r5, top5⟩ => ?_
  refine clrLow_ok h5 (by decide) (by decide) fun t6 h6 k6 e6 r6 top6 => ?_
  rw [← List.append_nil (divHdr _ _ _ _)]
  -- The count, through every step.
  have K : Keep (cvB s0) (cvW s0) (invArrs ++ [aDQ, aDD]) (invSlots ++ [sT, sE3, sMask]) s.mem t6.mem :=
    k1.mono.trans (k2.mono.trans (K3.mono.trans (k4.mono.trans (k5.mono.trans k6.mono))))
  have c6 : t6.mem.readW (off (State.addr (cvB s0)) 16) 32 = BitVec.ofNat 32 (cvW s0) := by
    rw [← h.count]; refine BitVec.eq_of_toNat_eq ?_
    exact K.slot (e := 16) (by decide) (by decide)
  refine divHdr_ok h6 (by decide) (by decide) (by decide) (by decide) c6 fun t h7 k7 d7 r7 => WP.block_nil ?_
  have KK : Keep (cvB s0) (cvW s0) (invArrs ++ [aDQ, aDD]) (invSlots ++ [sT, sE3, sMask, 0, 4, 8, 12])
      s.mem t.mem := K.mono.trans k7.mono
  have R : Rest (.r6 :: opRegs) s t := r1.trans ((r2.mono (by simp)).trans ((r3a.mono (by simp)).trans
    ((r3b.mono (by simp)).trans ((r3.mono (by simp)).trans ((r4.mono (by simp)).trans ((r5.mono (by simp)).trans
      ((r6.mono (by simp)).trans (r7.mono (by simp)))))))))
  have bt := h.base.keep KK (by decide) (by decide) (by decide) R.sp R.rd R.wr
  have tr : ∀ j, j < nArr → j ∉ invArrs ++ [aDQ, aDD] →
      num t.mem (cvB s0) (cvW s0) j = num s.mem (cvB s0) (cvW s0) j := fun j hj hn =>
    KK.num (fun k hk e => hn (by subst e; exact hk)) (by decide) (fit j hj)
  have fDD := fit aDD (by decide)
  have hS : S (cvW s0) = 4 * (cvW s0 + 2) := rfl
  refine ⟨bt, h7, ?_, ?_, ?_, ?_, ?_, ?_, d7, ?_⟩
  · rw [← h.count]; refine BitVec.eq_of_toNat_eq ?_
    exact KK.slot (e := 16) (by decide) (by decide)
  · rw [tr _ (by decide) (by decide), h.q]
  · rw [tr _ (by decide) (by decide), h.d]
  · rw [k7.word (by omega) (by simp) (by decide) fDD, top6, top5,
      k4.word (by omega) (by decide) (by simp) fDD, K3.word (by omega) (by simp) (by decide) fDD,
      k2.word (by omega) (by decide) (by decide) fDD, k1.word (by omega) (by decide) (by decide) fDD, h.ddTop]
  · rw [k7.num (by simp) (by decide) (fit _ (by decide)), k6.num (by decide) (by simp) (fit _ (by decide)),
      k5.num (by decide) (by simp) (fit _ (by decide)), e4, K3.num (by simp) (by decide) (fit _ (by decide)),
      k2.num (by decide) (by decide) (fit _ (by decide)), k1.num (by decide) (by decide) (fit _ (by decide)), h.d]
  · rw [k7.num (by simp) (by decide) (fit _ (by decide)), e6, e5, k4.num (by decide) (by simp) (fit _ (by decide)),
      K3.num (by simp) (by decide) (fit _ (by decide)), k2.num (by decide) (by decide) (fit _ (by decide)),
      k1.num (by decide) (by decide) (fit _ (by decide)), h.p]
  · have x3 : num t.mem (cvB s0) (cvW s0) 3 = num t1.mem (cvB s0) (cvW s0) 3 := by
      rw [k7.num (by simp) (by decide) (fit _ (by decide)), k6.num (by decide) (by simp) (fit _ (by decide)),
        k5.num (by decide) (by simp) (fit _ (by decide)), k4.num (by decide) (by simp) (fit _ (by decide)),
        K3.num (by simp) (by decide) (fit _ (by decide)), k2.num (by decide) (by decide) (fit _ (by decide))]
    refine ⟨num t1.mem (cvB s0) (cvW s0) 1, ?_, fun hM => by rw [x3]; exact I hM⟩
    rw [k7.slot (by decide) (by decide), k6.slot (by decide) (by simp), k5.slot (by decide) (by simp),
      k4.slot (by decide) (by simp), m3, m3b, k3b.slot (e := sE3) (by decide) (by decide), m3a,
      k3a.slot (e := sE2) (by decide) (by decide), k3a.slot (e := sE3) (by decide) (by decide), e2,
      sl sPodd (by decide) (by decide) (by decide), sl sE1 (by decide) (by decide) (by decide),
      sl sE2 (by decide) (by decide) (by decide), h.podd, h.e1, h.e2]
    simp only [maskOf, VG.Proof.Rsa.CrtValues.maskOf]
    by_cases a : cvP s0 % 2 = 1 <;> by_cases b : X₁ = cvQ s0 <;> by_cases c : X₂ = 0 <;>
      by_cases d : num t1.mem (cvB s0) (cvW s0) 1 = 1 <;> simp [a, b, c, d]

end VG.Proof.Rsa.Arm.CrtValues
