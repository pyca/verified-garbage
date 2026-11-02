module

public import VerifiedGarbage.Proof.Rsa.Arm.CvDivN
import VerifiedGarbage.Proof.Rsa.Arm.InvParts
import VerifiedGarbage.Proof.Rsa.Arm.KeyWord
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Tactic.Push
import Mathlib.Algebra.NeZero
import Mathlib.Basic.IsEmpty.Defs
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # `vg_rsa_crt_values` on ARMv7: the checks of `p q = n`, and `inverse`'s start -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

abbrev cvP (s0 : State) : Nat := Spec.Rsa.os2ip (pBytes s0)
abbrev cvQ (s0 : State) : Nat := Spec.Rsa.os2ip (qBytes s0)
abbrev cvD (s0 : State) : Nat := Spec.Rsa.os2ip (dBytes s0)
abbrev cvN (s0 : State) : Nat := Spec.Rsa.os2ip (nBytes s0)
/-- `inverse`'s modulus `p | 1`. -/
abbrev cvM (s0 : State) : Nat := 2 * (cvP s0 / 2) + 1

def checksA : List (Prog isa) := [.block ctx, eqS sE1 aDQ aQ aT1, eqS sE2 aDR aZero aT1] ++ invSetup
def checksB : List (Prog isa) := [.block primeWidth, inverse, .block ctx, eqS sE3 1 aOne aT1,
  .block (andS sMask sPodd sE1 ++ andS sMask sMask sE2 ++ andS sMask sMask sE3),
  copy aDQ aD, copy aDD aP, .block (clrLow aDD ++ divHdr aDQ aDR2 aDD aDT)]

theorem checks_eq : checks = seqs (checksA ++ checksB) := rfl

/-- Before `inverse`, with the quotient `X₁` and the remainder `X₂` of the first division. -/
structure StI (s0 : State) (X₁ X₂ : Nat) (s : State) : Prop where
  base : Base s0 s
  ws : Ws s (cvB s0) (cvZ s0) (cvW s0) nArr
  count : s.mem.readW (off (State.addr (cvB s0)) 16) 32 = BitVec.ofNat 32 (cvW s0)
  podd : slot s.mem (cvB s0) sPodd = cvP s0 % 2
  e1 : slot s.mem (cvB s0) sE1 = if X₁ = cvQ s0 then 1 else 0
  e2 : slot s.mem (cvB s0) sE2 = if X₂ = 0 then 1 else 0
  p : num s.mem (cvB s0) (cvW s0) aP = cvP s0
  q : num s.mem (cvB s0) (cvW s0) aQ = cvQ s0
  d : num s.mem (cvB s0) (cvW s0) aD = cvD s0
  ddTop : w32 s.mem (State.addr (cvB s0)) (arr (cvW s0) aDD + 4 * cvW s0) = 0
  u : num s.mem (cvB s0) (cvW s0) 0 = cvQ s0
  v : num s.mem (cvB s0) (cvW s0) 1 = cvM s0
  x₁ : num s.mem (cvB s0) (cvW s0) 2 = 1
  x₂ : num s.mem (cvB s0) (cvW s0) 3 = 0
  m : num s.mem (cvB s0) (cvW s0) aM = cvM s0
  nm : num s.mem (cvB s0) (cvW s0) aNM + cvM s0 = 2 ^ (32 * cvW s0)
  zero : num s.mem (cvB s0) (cvW s0) aZero = 0
  one : num s.mem (cvB s0) (cvW s0) aOne = 1

theorem cvM_pos (s0 : State) : 0 < cvM s0 := by simp only [cvM]; omega_arith

theorem checksA_ok {s0 s : State} (h : StC s0 s) :
    WP isa (seqs checksA) s (StI s0 (num s.mem (cvB s0) (cvW s0) aDQ) (num s.mem (cvB s0) (cvW s0) aDR)) := by
  have pre := h.base.pre
  unfold checksA invSetup
  simp only [List.cons_append, List.nil_append]
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil ctx]
  refine ctx_ok h.base fun t1 b1 h1 r1 m1 => WP.block_nil ?_
  have fit := fun j (hj : j < nArr) => h1.fit64 (j := j) hj
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h1 (d := sE1) (a := aDQ) (b := aQ) (t := aT1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h2 (d := sE2) (a := aDR) (b := aZero) (t := aT1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun t3 ⟨h3, k3, e3, r3⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h3 (o := 0) (a := aQ) (by decide) (by decide) (by decide) (by decide))
    fun t4 ⟨h4, k4, e4, r4, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h4 (o := aM) (a := aP) (by decide) (by decide) (by decide) (by decide))
    fun t5 ⟨h5, k5, e5, r5, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil (orOne aM)]
  refine orOne_ok h5 (by decide) (by decide) fun t6 h6 k6 e6 r6 => WP.block_nil ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h6 (o := 1) (a := aM) (by decide) (by decide) (by decide) (by decide))
    fun t7 ⟨h7, k7, e7, r7, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil (setOne aOne), ← List.append_assoc]
  refine setOne_ok h7 (j := 2) (by decide) (by decide) fun t8' h8' k8' e8' r8' => ?_
  refine setOne_ok h8' (j := aOne) (by decide) (by decide) fun t8 h8 k8 e8 r8 => WP.block_nil ?_
  refine WP.mono (sub3_ok h8 (o := aNM) (a := aZero) (b := aM) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun t ⟨ht, k9, e9, b9, r9⟩ => ?_
  have K : Keep (cvB s0) (cvW s0) [aT1, 0, aM, 1, 2, aOne, aNM] [sT, sE1, sE2] t1.mem t.mem :=
    k2.mono.trans (k3.mono.trans (k4.mono.trans (k5.mono.trans (k6.mono.trans (k7.mono.trans
      (k8'.mono.trans (k8.mono.trans k9.mono)))))))
  have R : Rest opRegs t1 t := r2.trans (r3.trans (r4.trans (r5.trans (r6.trans (r7.trans (r8'.trans
    (r8.trans r9)))))))
  have z0 : ∀ j ∈ zeroC, num t1.mem (cvB s0) (cvW s0) j = 0 := fun j hj => by rw [m1]; exact num_of_zero (h.zeros j hj)
  have K1 : ∀ j, j < nArr → j ∉ [aT1, 0, aM, 1, 2, aOne, aNM] →
      num t.mem (cvB s0) (cvW s0) j = num s.mem (cvB s0) (cvW s0) j := fun j hj hn => by
    rw [K.num (fun k hk e => hn (by subst e; exact hk)) (by decide) (fit j hj), m1]
  -- `M`.
  have M5 : num t5.mem (cvB s0) (cvW s0) aM = cvP s0 := by
    rw [e5, k4.num (by decide) (by simp) (fit _ (by decide)), k3.num (by decide) (by decide) (fit _ (by decide)),
      k2.num (by decide) (by decide) (fit _ (by decide)), m1, h.p]
  have M6 : num t6.mem (cvB s0) (cvW s0) aM = cvM s0 := by rw [e6, M5]
  have M8 : num t8.mem (cvB s0) (cvW s0) aM = cvM s0 := by
    rw [k8.num (by decide) (by simp) (fit _ (by decide)), k8'.num (by decide) (by simp) (fit _ (by decide)),
      k7.num (by decide) (by simp) (fit _ (by decide)), M6]
  have Z8 : num t8.mem (cvB s0) (cvW s0) aZero = 0 := by
    rw [k8.num (by decide) (by simp) (fit _ (by decide)), k8'.num (by decide) (by simp) (fit _ (by decide)),
      k7.num (by decide) (by simp) (fit _ (by decide)), k6.num (by decide) (by simp) (fit _ (by decide)),
      k5.num (by decide) (by simp) (fit _ (by decide)), k4.num (by decide) (by simp) (fit _ (by decide)),
      k3.num (by decide) (by decide) (fit _ (by decide)), k2.num (by decide) (by decide) (fit _ (by decide)),
      z0 _ (by decide)]
  have bt : Base s0 t := b1.keep K (by decide) (by decide) (by decide) R.sp R.rd R.wr
  refine ⟨bt, ht, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h.count, ← m1]
    refine BitVec.eq_of_toNat_eq ?_
    exact K.slot (e := 16) (by decide) (by decide)
  · rw [K.slot (by decide) (by decide), m1, h.podd]
  · rw [k9.slot (by decide) (by simp), k8.slot (by decide) (by simp), k8'.slot (by decide) (by simp),
      k7.slot (by decide) (by simp), k6.slot (by decide) (by simp), k5.slot (by decide) (by simp),
      k4.slot (by decide) (by simp), k3.slot (by decide) (by decide), e2, m1, h.q]
  · rw [k9.slot (by decide) (by simp), k8.slot (by decide) (by simp), k8'.slot (by decide) (by simp),
      k7.slot (by decide) (by simp), k6.slot (by decide) (by simp), k5.slot (by decide) (by simp),
      k4.slot (by decide) (by simp), e3, k2.num (j := aDR) (by decide) (by decide) (fit _ (by decide)),
      k2.num (j := aZero) (by decide) (by decide) (fit _ (by decide)), z0 aZero (by decide), m1]
  · rw [K1 _ (by decide) (by decide), h.p]
  · rw [K1 _ (by decide) (by decide), h.q]
  · rw [K1 _ (by decide) (by decide), h.d]
  · rw [K.word (by simp only [S]; omega_arith) (by decide) (by decide) (fit _ (by decide)), m1, h.ddTop]
  · rw [k9.num (by decide) (by simp) (fit _ (by decide)), k8.num (by decide) (by simp) (fit _ (by decide)),
      k8'.num (by decide) (by simp) (fit _ (by decide)), k7.num (by decide) (by simp) (fit _ (by decide)),
      k6.num (by decide) (by simp) (fit _ (by decide)), k5.num (by decide) (by simp) (fit _ (by decide)), e4,
      k3.num (by decide) (by decide) (fit _ (by decide)), k2.num (by decide) (by decide) (fit _ (by decide)),
      m1, h.q]
  · rw [k9.num (by decide) (by simp) (fit _ (by decide)), k8.num (by decide) (by simp) (fit _ (by decide)),
      k8'.num (by decide) (by simp) (fit _ (by decide)), e7, M6]
  · rw [k9.num (by decide) (by simp) (fit _ (by decide)), k8.num (by decide) (by simp) (fit _ (by decide)), e8',
      k7.num (by decide) (by simp) (fit _ (by decide)), k6.num (by decide) (by simp) (fit _ (by decide)),
      k5.num (by decide) (by simp) (fit _ (by decide)), k4.num (by decide) (by simp) (fit _ (by decide)),
      k3.num (by decide) (by decide) (fit _ (by decide)), k2.num (by decide) (by decide) (fit _ (by decide)),
      z0 _ (by decide)]
  · rw [K1 _ (by decide) (by decide)]; rw [← m1]; exact z0 _ (by decide)
  · rw [k9.num (by decide) (by simp) (fit _ (by decide)), M8]
  · rw [Z8, M8] at e9
    have := cvM_pos s0
    have l := val32_lt t.mem (State.addr (cvB s0)) (arr (cvW s0) aNM) (cvW s0)
    rcases (by omega_arith : (t.gpr .r11).toNat = 0 ∨ (t.gpr .r11).toNat = 1) with e | e <;> rw [e] at e9 <;> omega_arith
  · rw [K1 _ (by decide) (by decide)]; rw [← m1]; exact z0 _ (by decide)
  · rw [k9.num (by decide) (by simp) (fit _ (by decide)), e8, k8'.num (by decide) (by simp) (fit _ (by decide)),
      k7.num (by decide) (by simp) (fit _ (by decide)), k6.num (by decide) (by simp) (fit _ (by decide)),
      k5.num (by decide) (by simp) (fit _ (by decide)), k4.num (by decide) (by simp) (fit _ (by decide)),
      k3.num (by decide) (by decide) (fit _ (by decide)), k2.num (by decide) (by decide) (fit _ (by decide)),
      z0 _ (by decide)]

end VG.Proof.Rsa.Arm.CrtValues
