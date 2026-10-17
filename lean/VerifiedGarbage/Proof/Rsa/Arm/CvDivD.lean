module

public import VerifiedGarbage.Proof.Rsa.Arm.CvStore
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `vg_rsa_crt_values` on ARMv7: the divisions of `d` -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

theorem divR_ok {s0 s : State} (b : Base s0 s) (hw : Ws s (cvB s0) (cvZ s0) (cvW s0) nArr) {r : Nat}
    (hr : r = aDR2 ∨ r = aDR3) (hd : DivHdr s.mem (cvB s0) (cvW s0) aDQ r aDD aDT)
    (top : w32 s.mem (State.addr (cvB s0)) (arr (cvW s0) aDD + 4 * cvW s0) = 0) :
    WP isa VG.Impl.Rsa.Arm.Div.code s fun t => Base s0 t ∧ Keep (cvB s0) (cvW s0) [aDQ, r, aDT] [] s.mem t.mem ∧
      (0 < num s.mem (cvB s0) (cvW s0) aDD → num t.mem (cvB s0) (cvW s0) r =
        num s.mem (cvB s0) (cvW s0) aDQ % num s.mem (cvB s0) (cvW s0) aDD) := by
  have hr' : r < nArr ∧ r ≠ aDQ ∧ r ≠ aDD ∧ r ≠ aDT := by rcases hr with rfl | rfl <;> decide
  refine WP.mono (div_ok hw (q := aDQ) (r := r) (d := aDD) (t := aDT) (by decide) hr'.1 (by decide) (by decide)
    (Ne.symm hr'.2.1) (by decide) (by decide) hr'.2.2.1 hr'.2.2.2 (by decide) hd top) fun t ⟨k, rt, v⟩ =>
    ⟨b.keep k (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro j (rfl | rfl | rfl) <;>
      first | decide | exact hr'.1) (by simp) (by simp) rt.sp rt.rd rt.wr, k, fun pos => (v pos).1⟩

/-- After the division of `d` by `p - 1`. -/
structure StE (s0 : State) (X₁ X₂ : Nat) (s : State) : Prop where
  base : Base s0 s
  count : s.mem.readW (off (State.addr (cvB s0)) 16) 32 = BitVec.ofNat 32 (cvW s0)
  q : num s.mem (cvB s0) (cvW s0) aQ = cvQ s0
  d : num s.mem (cvB s0) (cvW s0) aD = cvD s0
  ddTop : w32 s.mem (State.addr (cvB s0)) (arr (cvW s0) aDD + 4 * cvW s0) = 0
  dp : 0 < 2 * (cvP s0 / 2) → num s.mem (cvB s0) (cvW s0) aDR2 = cvD s0 % (2 * (cvP s0 / 2))
  mask : ∃ V, slot s.mem (cvB s0) sMask = (if maskOf (cvP s0) (cvQ s0) X₁ X₂ V then 1 else 0) ∧
    (1 < cvM s0 → V = Nat.gcd (cvQ s0) (cvM s0) ∧
      (cvM s0 : Int) ∣ (num s.mem (cvB s0) (cvW s0) 3 : Int) * cvQ s0 - V ∧
      num s.mem (cvB s0) (cvW s0) 3 < cvM s0)

theorem divP_ok {s0 s : State} {X₁ X₂ : Nat} (h : StD s0 X₁ X₂ s) :
    WP isa VG.Impl.Rsa.Arm.Div.code s (StE s0 X₁ X₂) := by
  have hw := h.ws
  have fit := fun j (hj : j < nArr) => hw.fit64 (j := j) hj
  have hS : S (cvW s0) = 4 * (cvW s0 + 2) := rfl
  refine WP.mono (divR_ok h.base hw (.inl rfl) h.hdr h.ddTop) fun t ⟨bt, k, v⟩ => ?_
  obtain ⟨V, mV, iV⟩ := h.mask
  refine ⟨bt, ?_, ?_, ?_, ?_, fun pos => ?_, ⟨V, ?_, ?_⟩⟩
  · rw [← h.count]; exact BitVec.eq_of_toNat_eq (k.slot (e := 16) (by decide) (by simp))
  · rw [k.num (by decide) (by simp) (fit _ (by decide)), h.q]
  · rw [k.num (by decide) (by simp) (fit _ (by decide)), h.d]
  · rw [k.word (by omega) (by decide) (by simp) (fit _ (by decide)), h.ddTop]
  · rw [v (by rw [h.dd]; exact pos), h.dq, h.dd]
  · rw [k.slot (by decide) (by simp), mV]
  · rw [k.num (by decide) (by simp) (fit _ (by decide))]; exact iV

/-- After the division of `d` by `q - 1`. -/
structure StG (s0 : State) (X₁ X₂ : Nat) (s : State) : Prop where
  base : Base s0 s
  dp : 0 < 2 * (cvP s0 / 2) → num s.mem (cvB s0) (cvW s0) aDR2 = cvD s0 % (2 * (cvP s0 / 2))
  dq : 0 < 2 * (cvQ s0 / 2) → num s.mem (cvB s0) (cvW s0) aDR3 = cvD s0 % (2 * (cvQ s0 / 2))
  mask : ∃ V, slot s.mem (cvB s0) sMask = (if maskOf (cvP s0) (cvQ s0) X₁ X₂ V then 1 else 0) ∧
    (1 < cvM s0 → V = Nat.gcd (cvQ s0) (cvM s0) ∧
      (cvM s0 : Int) ∣ (num s.mem (cvB s0) (cvW s0) 3 : Int) * cvQ s0 - V ∧
      num s.mem (cvB s0) (cvW s0) 3 < cvM s0)

theorem divQ_ok {s0 s : State} {X₁ X₂ : Nat} (h : StE s0 X₁ X₂ s) :
    WP isa (.seq divQ VG.Impl.Rsa.Arm.Div.code) s (StG s0 X₁ X₂) := by
  have hS : S (cvW s0) = 4 * (cvW s0 + 2) := rfl
  rw [WP.seq_iff]
  unfold divQ
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil ctx]
  refine ctx_ok h.base fun t1 b1 h1 r1 m1 => WP.block_nil ?_
  have fit := fun j (hj : j < nArr) => h1.fit64 (j := j) hj
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h1 (o := aDQ) (a := aD) (by decide) (by decide) (by decide) (by decide))
    fun t2 ⟨h2, k2, e2, r2, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h2 (o := aDD) (a := aQ) (by decide) (by decide) (by decide) (by decide))
    fun t3 ⟨h3, k3, e3, r3, top3⟩ => ?_
  show WP isa (.block (clrLow aDD ++ divHdr aDQ aDR3 aDD aDT)) t3 _
  refine clrLow_ok h3 (by decide) (by decide) fun t4 h4 k4 e4 r4 top4 => ?_
  rw [← List.append_nil (divHdr _ _ _ _)]
  have K : Keep (cvB s0) (cvW s0) [aDQ, aDD] [] t1.mem t4.mem := k2.mono.trans (k3.mono.trans k4.mono)
  have c4 : t4.mem.readW (off (State.addr (cvB s0)) 16) 32 = BitVec.ofNat 32 (cvW s0) := by
    rw [← h.count, ← m1]; exact BitVec.eq_of_toNat_eq (K.slot (e := 16) (by decide) (by simp))
  refine divHdr_ok h4 (by decide) (by decide) (by decide) (by decide) c4 fun t5 h5 k5 d5 r5 => WP.block_nil ?_
  have K5 : Keep (cvB s0) (cvW s0) [aDQ, aDD] [0, 4, 8, 12] t1.mem t5.mem := K.mono.trans k5.mono
  have R5 : Rest opRegs t1 t5 := r2.trans (r3.trans (r4.trans r5))
  have b5 := b1.keep K5 (by decide) (by decide) (by decide) R5.sp R5.rd R5.wr
  have fDD := fit aDD (by decide)
  have top5 : w32 t5.mem (State.addr (cvB s0)) (arr (cvW s0) aDD + 4 * cvW s0) = 0 := by
    rw [k5.word (by omega) (by simp) (by decide) fDD, top4, top3, k2.word (by omega) (by decide) (by simp) fDD, m1,
      h.ddTop]
  refine WP.mono (divR_ok b5 h5 (.inr rfl) d5 top5) fun t ⟨bt, k, v⟩ => ?_
  obtain ⟨V, mV, iV⟩ := h.mask
  have tr : ∀ j, j < nArr → j ∉ [aDQ, aDD, aDR3, aDT] →
      num t.mem (cvB s0) (cvW s0) j = num s.mem (cvB s0) (cvW s0) j := fun j hj hn => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    rw [k.num (by simp; omega) (by simp) (fit j hj), K5.num (by simp; omega) (by decide) (fit j hj), m1]
  refine ⟨bt, fun pos => ?_, fun pos => ?_, ⟨V, ?_, ?_⟩⟩
  · rw [tr _ (by decide) (by decide)]; exact h.dp pos
  · have dd5 : num t5.mem (cvB s0) (cvW s0) aDD = 2 * (cvQ s0 / 2) := by
      rw [k5.num (by simp) (by decide) fDD, e4, e3, k2.num (by decide) (by simp) (fit _ (by decide)), m1, h.q]
    have dq5 : num t5.mem (cvB s0) (cvW s0) aDQ = cvD s0 := by
      rw [k5.num (by simp) (by decide) (fit _ (by decide)), k4.num (by decide) (by simp) (fit _ (by decide)),
        k3.num (by decide) (by simp) (fit _ (by decide)), e2, m1, h.d]
    rw [v (by rw [dd5]; exact pos), dq5, dd5]
  · rw [k.slot (by decide) (by simp), K5.slot (by decide) (by decide), m1, mV]
  · rw [tr _ (by decide) (by decide)]; exact iV

end VG.Proof.Rsa.Arm.CrtValues
