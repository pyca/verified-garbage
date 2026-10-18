module

public import VerifiedGarbage.Proof.Dsa.Arm.Session
public import VerifiedGarbage.Proof.Dsa.Accepted
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA on 32-bit ARM: the checks of the domain and the keys

`domain_ok`: the flag `&=` the ranges of g and y and `q ∣ p - 1`, and
`q - 2` is stored for the inverses; `subgroup_ok`: `g^q = y^q = 1 mod p`;
`privateKey_ok`: the ranges of x and the nonce, and `g^x = y mod p`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.Ecdsa.Arm (mask32 mask32_and)

/-- Validation leaves the shared helper's register-save words untouched. -/
structure ValidationRun (base : Addr) (s t : State) : Prop extends Run base s t where
  saved : ∀ d, 168 ≤ d → d + 4 ≤ 204 →
    t.mem.readW (off base d) 32 = s.mem.readW (off base d) 32

instance {base s t} : Coe (ValidationRun base s t) (Run base s t) := ⟨ValidationRun.toRun⟩

theorem ValidationRun.trans {base : Addr} {s t u : State}
    (A : ValidationRun base s t) (B : ValidationRun base t u) : ValidationRun base s u :=
  ⟨A.toRun.trans B.toRun, fun d lo hi => (B.saved d lo hi).trans (A.saved d lo hi)⟩

theorem Stage.validationRun {base : Addr} {s t : State} {o l : Nat}
    (St : Stage base s t o l) (H : o = 116 ∧ l = 4 ∨ 4960 ≤ o ∧ o + l ≤ 15712) :
    ValidationRun base s t := by
  refine ⟨St.run H, fun d lo hi => Mem.readW_congr fun i hᵢ => ?_⟩
  apply St.mem
  intro r hr
  simp only [arithRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [ofs_off base (by omega)]
  rcases hr with rfl | rfl | rfl <;> simp only <;> omega

/-- The working space and the widths of a call. -/
structure Sched (s : State) (base : Addr) (size pLen qLen nP nQ : Nat) : Prop where
  ws : Ws s base size
  big : 15712 < size
  wp : Width pLen nP
  wq : Width qLen nQ
  qp : qLen ≤ pLen
  q32 : qLen ≤ 32

theorem Sched.run {s t : State} {base : Addr} {size pLen qLen nP nQ : Nat} (S : Sched s base size pLen qLen nP nQ)
    (Rn : Run base s t) : Sched t base size pLen qLen nP nQ :=
  ⟨Rn.ws S.ws, S.big, S.wp, S.wq, S.qp, S.q32⟩

theorem Sched.stage {s t : State} {base : Addr} {size pLen qLen nP nQ o l : Nat}
    (S : Sched s base size pLen qLen nP nQ) (St : Stage base s t o l) : Sched t base size pLen qLen nP nQ :=
  ⟨St.ws S.ws, S.big, S.wp, S.wq, S.qp, S.q32⟩

theorem Sched.fits {s : State} {base : Addr} {size pLen qLen nP nQ : Nat} (S : Sched s base size pLen qLen nP nQ) :
    size ≤ 2 ^ 32 := by
  have := S.ws.nowrap; omega

theorem Sched.lens {s : State} {base : Addr} {size pLen qLen nP nQ : Nat} (S : Sched s base size pLen qLen nP nQ) :
    4 ≤ qLen ∧ qLen ≤ pLen ∧ pLen ≤ 384 ∧ qLen ≤ 32 ∧ pLen % 4 = 0 ∧ qLen % 4 = 0 :=
  ⟨S.wq.four, S.qp, S.wp.max, S.q32, S.wp.word, S.wq.word⟩

/-- An input after an operation that writes the flag or a computed value. -/
theorem Input.next {s t : State} {base : Addr} {size pLen qLen nP nQ o l : Nat} {p : Impl.Dsa.Layout.Pointer}
    {len v : Nat} (I : Input s base size p len v) (S : Sched s base size pLen qLen nP nQ) (St : Stage base s t o l)
    (ho : o = 116 ∧ l = 4 ∨ 4960 ≤ o ∧ o + l ≤ 15712) : Input t base size p len v :=
  I.stage St (by omega) (by have := S.big; omega) S.fits (by have := S.big; omega)

theorem operand_lt_of {base : Addr} {s : State} {size : Nat} {p : Impl.Dsa.Layout.Pointer} {len v : Nat}
    (I : Input s base size p len v) : v < 256 ^ len :=
  I.value ▸ operand_lt base s p len

theorem domain_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G Y : Nat}
    (S : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Iy : Input s base size (.input .y) pLen Y)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1) :
    WP isa (Validate.domain pLen qLen) s fun t =>
      maskW base t = maskW base s &&& mask32 (((1 < G ∧ G < P) ∧ (1 < Y ∧ Y < P)) ∧ (P - 1) % Q = 0) ∧
      localVal base t Impl.Dsa.Layout.qMinusTwo qLen = Q - 2 ∧ ValidationRun base s t := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := S.lens
  have big := S.big
  have fits := S.fits
  have Plt := operand_lt_of Ip
  have Qlt := operand_lt_of Iq
  simp only [Validate.domain, Core.sequence, List.foldr]
  refine WP.seq (WP.seq (WP.mono (range_ok S.ws (by omega) S.wp Ip.toReady Ig.toReady true) fun v₁ ⟨F₁, St₁⟩ =>
    WP.mono (range_ok (St₁.ws S.ws) (by omega) S.wp (Ip.next S St₁ (.inl ⟨rfl, rfl⟩)).toReady
      (Iy.next S St₁ (.inl ⟨rfl, rfl⟩)).toReady true) fun v₂ ⟨F₂, St₂⟩ => ?_))
  have S₂ := (S.stage St₁).stage St₂
  have Ip₂ := (Ip.next S St₁ (.inl ⟨rfl, rfl⟩)).next (S.stage St₁) St₂ (.inl ⟨rfl, rfl⟩)
  have Iq₂ := (Iq.next S St₁ (.inl ⟨rfl, rfl⟩)).next (S.stage St₁) St₂ (.inl ⟨rfl, rfl⟩)
  rw [(Ip.next S St₁ (.inl ⟨rfl, rfl⟩)).value, (Iy.next S St₁ (.inl ⟨rfl, rfl⟩)).value] at F₂
  rw [Ip.value, Ig.value] at F₁
  -- `p - 1`
  refine WP.seq (WP.mono (minus_ok (output := Impl.Dsa.Layout.t) S₂.ws (by omega) S.wp Ip₂.toReady Ip₂.value hP hPo
    (by omega) (by decide) (by decide) (by simp only [Impl.Dsa.Layout.t]; omega) (by decide))
    fun v₃ ⟨B₃, St₃⟩ => ?_)
  have S₃ := S₂.stage St₃
  have ho₃ : 4960 ≤ Impl.Dsa.Layout.t ∧ Impl.Dsa.Layout.t + pLen ≤ 15712 := by
    simp only [Impl.Dsa.Layout.t]; omega
  have Iq₃ := Iq₂.next S₂ St₃ (.inr ho₃)
  have L₃ : localVal base v₃ Impl.Dsa.Layout.t pLen = P - 1 := localVal_of_bytes B₃ (by omega)
  -- `(p - 1) mod q`
  refine WP.seq (WP.mono (reduce_ok (output := Impl.Dsa.Layout.u) S₃.ws (by omega) S.wq Iq₃.toReady
    (count := .imm pLen) (input := .local Impl.Dsa.Layout.t) (show pLen < 2 ^ 16 by omega)
    (localReady S₃.ws (by decide) (by simp only [countValue, Impl.Dsa.Layout.t]; omega) (by decide))
    Iq₃.value hQ hQo (by decide) (by simp only [Impl.Dsa.Layout.u]; omega) (by decide)) fun v₄ ⟨B₄, St₄⟩ => ?_)
  rw [countValue, local_operand S₃.ws (by simp only [Impl.Dsa.Layout.t]; omega), L₃] at B₄
  have S₄ := S₃.stage St₄
  have ho₄ : 4960 ≤ Impl.Dsa.Layout.u ∧ Impl.Dsa.Layout.u + qLen ≤ 15712 := by
    simp only [Impl.Dsa.Layout.u]; omega
  have Iq₄ := Iq₃.next S₃ St₄ (.inr ho₄)
  have L₄ : localVal base v₄ Impl.Dsa.Layout.u qLen = (P - 1) % Q :=
    localVal_of_bytes B₄ (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (Nat.le_of_lt Qlt))
  -- `q ∣ p - 1`
  refine WP.seq (WP.mono (zero_ok S₄.ws (by omega) S.wq
    (localReady (len := qLen) S₄.ws (by decide) (by simp only [Impl.Dsa.Layout.u]; omega) (by decide)) false)
    fun v₅ ⟨F₅, St₅⟩ => ?_)
  rw [local_operand S₄.ws (by simp only [Impl.Dsa.Layout.u]; omega), L₄] at F₅
  have S₅ := S₄.stage St₅
  have Iq₅ := Iq₄.next S₄ St₅ (.inl ⟨rfl, rfl⟩)
  -- `q - 2`
  refine WP.seq (WP.mono (minus_ok (output := Impl.Dsa.Layout.qMinusTwo) S₅.ws (by omega) S.wq Iq₅.toReady
    Iq₅.value (by omega) hQo (by omega) (by decide) (by decide) (by simp only [Impl.Dsa.Layout.qMinusTwo]; omega)
    (by decide)) fun v₆ ⟨B₆, St₆⟩ => WP.block_nil ⟨?_, localVal_of_bytes B₆ (by omega), ?_⟩)
  · rw [St₆.maskW (by decide), F₅, St₄.maskW (by decide), St₃.maskW (by decide), F₂, F₁,
      BitVec.and_assoc, BitVec.and_assoc, mask32_and, mask32_and]
    exact congrArg _ (mask32_iff (by simp only [↓reduceIte, Bool.false_eq_true]; omega))
  · exact ((((St₁.validationRun (.inl ⟨rfl, rfl⟩)).trans (St₂.validationRun (.inl ⟨rfl, rfl⟩))).trans (St₃.validationRun (.inr ho₃))).trans
      ((St₄.validationRun (.inr ho₄)).trans (St₅.validationRun (.inl ⟨rfl, rfl⟩)))).trans
      (St₆.validationRun (.inr (by simp only [Impl.Dsa.Layout.qMinusTwo]; omega)))

/-- The window of the scalars below `t`. -/
abbrev scalars : Nat × Nat := (4960, Impl.Dsa.Layout.t)

theorem subgroup_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G Y : Nat}
    (S : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Iy : Input s base size (.input .y) pLen Y)
    (hP : 1 < P) (hPo : P % 2 = 1) :
    WP isa (Validate.subgroup pLen qLen) s fun t =>
      maskW base t = maskW base s &&& mask32 (G ^ Q % P = 1 ∧ Y ^ Q % P = 1) ∧
      KeepsLocals base s t scalars.1 scalars.2 ∧ ValidationRun base s t := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := S.lens
  have big := S.big
  have fits := S.fits
  have Plt := operand_lt_of Ip
  have ho : 4960 ≤ Impl.Dsa.Layout.t ∧ Impl.Dsa.Layout.t + pLen ≤ 15712 := by
    simp only [Impl.Dsa.Layout.t]; omega
  have ht : Impl.Dsa.Layout.t + pLen < size := by omega
  simp only [Validate.subgroup, Core.sequence, List.foldr]
  refine WP.seq (WP.mono (power_ok (output := Impl.Dsa.Layout.t) S.ws (by omega) S.wp q4 qp qw Ip.toReady
    Ig.toReady Iq.toReady Ip.value hP hPo ho.1 (by omega) (by decide)) fun v₁ ⟨B₁, St₁⟩ => ?_)
  rw [Ig.value, Iq.value] at B₁
  have S₁ := S.stage St₁
  refine WP.seq (WP.mono (isOne_ok S₁.ws (by omega) S.wp (localReady S₁.ws ho.1 ht (by decide)))
    fun v₂ ⟨F₂, St₂⟩ => ?_)
  rw [local_operand S₁.ws (by omega), localVal_of_bytes B₁ (Nat.lt_trans (Nat.mod_lt _ (by omega)) Plt)] at F₂
  have S₂ := S₁.stage St₂
  have Ip₂ := (Ip.next S St₁ (.inr ho)).next S₁ St₂ (.inl ⟨rfl, rfl⟩)
  have Iq₂ := (Iq.next S St₁ (.inr ho)).next S₁ St₂ (.inl ⟨rfl, rfl⟩)
  have Iy₂ := (Iy.next S St₁ (.inr ho)).next S₁ St₂ (.inl ⟨rfl, rfl⟩)
  refine WP.seq (WP.mono (power_ok (output := Impl.Dsa.Layout.t) S₂.ws (by omega) S.wp q4 qp qw Ip₂.toReady
    Iy₂.toReady Iq₂.toReady Ip₂.value hP hPo ho.1 (by omega) (by decide)) fun v₃ ⟨B₃, St₃⟩ => ?_)
  rw [Iy₂.value, Iq₂.value] at B₃
  have S₃ := S₂.stage St₃
  refine WP.seq (WP.mono (isOne_ok S₃.ws (by omega) S.wp (localReady S₃.ws ho.1 ht (by decide)))
    fun v₄ ⟨F₄, St₄⟩ => WP.block_nil ⟨?_, ?_, ?_⟩)
  · rw [local_operand S₃.ws (by omega), localVal_of_bytes B₃ (Nat.lt_trans (Nat.mod_lt _ (by omega)) Plt)] at F₄
    rw [F₄, St₃.maskW (by decide), F₂, St₁.maskW (by decide), BitVec.and_assoc, mask32_and]
  · have k : ∀ {a b : State} {o l : Nat}, Stage base a b o l → o + l ≤ 15712 →
        (14944 ≤ o ∨ o + l ≤ 4960) → KeepsLocals base a b scalars.1 scalars.2 := fun St h₁ h₂ =>
      St.keeps (by decide) (by decide) (by omega) (by simp only [Impl.Dsa.Layout.t]; omega)
    have ht' : Impl.Dsa.Layout.t = 14944 := rfl
    exact (((k St₁ (by omega) (by omega)).trans (k St₂ (by decide) (by decide))).trans
      (k St₃ (by omega) (by omega))).trans (k St₄ (by decide) (by decide))
  · exact (((St₁.validationRun (.inr ho)).trans (St₂.validationRun (.inl ⟨rfl, rfl⟩))).trans (St₃.validationRun (.inr ho))).trans
      (St₄.validationRun (.inl ⟨rfl, rfl⟩))

theorem Stage.keepsScalars {base : Addr} {a b : State} {o l : Nat} (St : Stage base a b o l) (h₁ : o + l ≤ 15712)
    (h₂ : 14944 ≤ o ∨ o + l ≤ 4960) : KeepsLocals base a b scalars.1 scalars.2 :=
  St.keeps (by decide) (by decide) (by omega) (by simp only [Impl.Dsa.Layout.t]; omega)

theorem publicKey_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G Y : Nat}
    (S : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Iy : Input s base size (.input .y) pLen Y)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1) :
    WP isa (Validate.publicKey pLen qLen) s fun t =>
      maskW base t = maskW base s &&& mask32 (publicChecks P Q G Y) ∧
      localVal base t Impl.Dsa.Layout.qMinusTwo qLen = Q - 2 ∧ ValidationRun base s t := by
  have big := S.big
  have fits := S.fits
  unfold Validate.publicKey
  refine WP.seq (WP.mono (domain_ok S Ip Iq Ig Iy hP hPo hQ hQo) fun u ⟨Fu, Lu, Ru⟩ =>
    WP.mono (subgroup_ok (S.run Ru) (Ip.run Ru (by omega) fits) (Iq.run Ru (by omega) fits)
      (Ig.run Ru (by omega) fits) (Iy.run Ru (by omega) fits) hP hPo) fun t ⟨Ft, Kt, Rt⟩ => ?_)
  have L : localVal base t Impl.Dsa.Layout.qMinusTwo qLen = Q - 2 := by
    rw [Kt _ _ (by decide) (by simp only [Impl.Dsa.Layout.qMinusTwo, Impl.Dsa.Layout.t]; have := S.q32; omega)]
    exact Lu
  refine ⟨?_, L, Ru.trans Rt⟩
  rw [Ft, Fu, BitVec.and_assoc, mask32_and]
  exact congrArg _ (mask32_iff (by simp only [publicChecks, and_assoc]))

theorem privateKey_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G Y X K : Nat}
    (S : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Iy : Input s base size (.input .y) pLen Y)
    (Ix : Input s base size (.input .x) qLen X) (Ik : Input s base size (.input .nonce) qLen K)
    (hP : 1 < P) (hPo : P % 2 = 1) :
    WP isa (Validate.privateKey pLen qLen) s fun t =>
      maskW base t = maskW base s &&& mask32 (((0 < X ∧ X < Q) ∧ (0 < K ∧ K < Q)) ∧ G ^ X % P = Y) ∧
      KeepsLocals base s t scalars.1 scalars.2 ∧ Run base s t := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := S.lens
  have big := S.big
  have fits := S.fits
  have Plt := operand_lt_of Ip
  have ho : 4960 ≤ Impl.Dsa.Layout.t ∧ Impl.Dsa.Layout.t + pLen ≤ 15712 := by
    simp only [Impl.Dsa.Layout.t]; omega
  have ht : Impl.Dsa.Layout.t + pLen < size := by omega
  have ht' : Impl.Dsa.Layout.t = 14944 := rfl
  simp only [Validate.privateKey, Core.sequence, List.foldr]
  refine WP.seq (WP.seq (WP.mono (range_ok S.ws (by omega) S.wq Iq.toReady Ix.toReady false) fun v₁ ⟨F₁, St₁⟩ =>
    WP.mono (range_ok (St₁.ws S.ws) (by omega) S.wq (Iq.next S St₁ (.inl ⟨rfl, rfl⟩)).toReady
      (Ik.next S St₁ (.inl ⟨rfl, rfl⟩)).toReady false) fun v₂ ⟨F₂, St₂⟩ => ?_))
  rw [Iq.value, Ix.value] at F₁
  rw [(Iq.next S St₁ (.inl ⟨rfl, rfl⟩)).value, (Ik.next S St₁ (.inl ⟨rfl, rfl⟩)).value] at F₂
  have S₂ := (S.stage St₁).stage St₂
  have nx : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₂ base size p len v :=
    fun I => (I.next S St₁ (.inl ⟨rfl, rfl⟩)).next (S.stage St₁) St₂ (.inl ⟨rfl, rfl⟩)
  refine WP.seq (WP.mono (power_ok (output := Impl.Dsa.Layout.t) S₂.ws (by omega) S.wp q4 qp qw (nx Ip).toReady
    (nx Ig).toReady (nx Ix).toReady (nx Ip).value hP hPo ho.1 (by omega) (by decide)) fun v₃ ⟨B₃, St₃⟩ => ?_)
  rw [(nx Ig).value, (nx Ix).value] at B₃
  have S₃ := S₂.stage St₃
  have Iy₃ := (nx Iy).next S₂ St₃ (.inr ho)
  refine WP.seq (WP.mono (equalValues_ok S₃.ws (by omega) S.wp (localReady S₃.ws ho.1 ht (by decide)) Iy₃.toReady)
    fun v₄ ⟨F₄, St₄⟩ => WP.block_nil ⟨?_, ?_, ?_⟩)
  · rw [local_operand S₃.ws (by omega), localVal_of_bytes B₃ (Nat.lt_trans (Nat.mod_lt _ (by omega)) Plt),
      Iy₃.value] at F₄
    rw [F₄, St₃.maskW (by decide), F₂, F₁, BitVec.and_assoc, BitVec.and_assoc, mask32_and, mask32_and]
    exact congrArg _ (mask32_iff (by simp only [Bool.false_eq_true, ↓reduceIte]; omega))
  · exact (((St₁.keepsScalars (by decide) (by decide)).trans (St₂.keepsScalars (by decide) (by decide))).trans
      (St₃.keepsScalars (by omega) (by omega))).trans (St₄.keepsScalars (by decide) (by decide))
  · exact (((St₁.run (.inl ⟨rfl, rfl⟩)).trans (St₂.run (.inl ⟨rfl, rfl⟩))).trans (St₃.run (.inr ho))).trans
      (St₄.run (.inl ⟨rfl, rfl⟩))

end VG.Proof.Dsa.Arm
