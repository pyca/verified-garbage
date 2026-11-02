module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.St
public import VerifiedGarbage.Proof.Rsa.Arm.InvLaw
import VerifiedGarbage.Proof.Rsa.Arm.InverseCT
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rsa.Arm.RvLoads
import VerifiedGarbage.Proof.Rsa.RecoverSubtract

/-! # An RSA key on ARMv7: inverses

`invOf a m`: from `(a, m, 1, 0)`, `inverse` modulo the odd `m > 1` leaves
`ivr W a m` in arrays 0–3 (`inverse_ok'`): `gcd(a, m)` in array 1 and
`x < m` with `x a ≡ gcd(a, m) (mod m)` in array 3 (`ivr_spec`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP sub32 sub32_of)

/-- What `inverse` leaves in arrays 1 and 3 for `a` modulo `m`, with `W` words. -/
def ivr (W a m : Nat) : Nat × Nat × Nat × Nat := (0, Nat.gcd a m, 0, VG.Proof.Rsa.Divstep.inv30 W a m)

theorem ivr_spec [VG.Proof.Rsa.Arm.Keys.InvLaw] {W a m : Nat} (hm : m % 2 = 1) (h1 : 1 < m) (ha : a < 2 ^ (32 * W)) (hmW : m < 2 ^ (32 * W)) :
    (ivr W a m).2.1 = Nat.gcd a m ∧ (m : Int) ∣ ((ivr W a m).2.2.2 : Int) * a - (ivr W a m).2.1 ∧
      (ivr W a m).2.2.2 < m := by
  have d := VG.Proof.Rsa.Arm.Keys.InvLaw.inv30_spec hm h1 ha hmW
  simp only [ivr]
  exact ⟨trivial, d.1, d.2⟩

end VG.Proof.RsaKeyGen.Arm.Key

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm

/-- `inverse_ok`, with the values it leaves. -/
theorem inverse_ok' [InvLaw] {s : State} {B : BitVec 32} {Z w N : Nat} (h : Ws s B Z w N) (hN15 : 15 ≤ N) (hN : N ≤ 256) :
    WP isa VG.Impl.Rsa.Arm.Keys.inverse s fun t => Ws t B Z w N ∧ Keep B w invArrs invSlots s.mem t.mem ∧
      Rest (.r6 :: opRegs) s t ∧
      (num s.mem B w aNM + num s.mem B w aM = 2 ^ (32 * w) → num s.mem B w aZero = 0 →
        num s.mem B w aM % 2 = 1 → 1 < num s.mem B w aM →
        bank s.mem B w 0 = (num s.mem B w 0, num s.mem B w aM, 1, 0) →
        num t.mem B w 1 = (VG.Proof.RsaKeyGen.Arm.Key.ivr w (num s.mem B w 0) (num s.mem B w aM)).2.1 ∧
        num t.mem B w 3 = (VG.Proof.RsaKeyGen.Arm.Key.ivr w (num s.mem B w 0) (num s.mem B w aM)).2.2.2) := by
  have g : VG.Proof.Rsa.Arm.Inv.Gk s B Z w w N :=
    ⟨h.nowrap, h.writable, h.fits, h.wpos, le_refl _, h.wle, h.r7, h.r8, h.r9⟩
  exact WP.mono (InvLaw.inverseK_ok g hN15 hN) fun t ⟨gt, kt, rt, v⟩ =>
    ⟨⟨gt.nowrap, gt.writable, gt.fits, gt.kpos, gt.wle, gt.r7, gt.r8, gt.r9⟩, kt, rt,
      fun _ _ hmo hm1 _ => by simp only [VG.Proof.RsaKeyGen.Arm.Key.ivr]; exact v hmo hm1⟩

end VG.Proof.Rsa.Arm.Keys

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP sub32 sub32_of)

section
variable {P : KP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

/-- `sub3 o a b`: `[o] := [a] − [b]` modulo `2^(32 W)`. -/
theorem St.psub3 {o a b : Nat} (cert : Cert (sub3 o a b)) (ho : o < nArr) (ha : a ∈ L) (hb : b ∈ L) (hoa : o ≠ a)
    (hob : o ≠ b) :
    VP (St P E A L V LS) (sub3 o a b) (St P E (fun σ => upd (A σ) o (sub32 P.W (A σ a) (A σ b))) (o :: L) V LS) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ =>
    WP.mono (sub3_ok hw ho (h.live_lt a ha) (h.live_lt b hb) (by decide) hoa hob) fun t ⟨ht, k, v, bo, r⟩ => by
      obtain ⟨e1, -⟩ := sub32_of (val32_lt _ _ _ _) (val32_lt _ _ _ _) v bo
      have ea : val32 s.mem (State.addr P.B) (arr P.W a) P.W = A σ a := h.arrs a ha
      have eb : val32 s.mem (State.addr P.B) (arr P.W b) P.W = A σ b := h.arrs b hb
      simp only [num, ea, eb] at e1
      exact ⟨e, h.write1 k ho (by simp) r.sp r.rd r.wr e1 (by simp), ht⟩

theorem inverse_cert : ∀ σ₁ σ₂ : State, RelCT isa
    (fun s₁ s₂ => St P E A L V LS σ₁ s₁ ∧ St P E A L V LS σ₂ s₂) VG.Impl.Rsa.Arm.Keys.inverse (fun _ _ => True) :=
  fun _ _ s t tr1 tr2 u v h e1 e2 =>
    ⟨inverse_ct s t tr1 tr2 u v trivial trivial
      ⟨by rw [h.1.2.2.r7, h.2.2.2.r7], by rw [h.1.2.2.r8, h.2.2.2.r8], by rw [h.1.2.2.r9, h.2.2.2.r9]⟩ e1 e2,
      trivial⟩

/-- `inverse` from `(a, m, 1, 0)` in arrays 0–3. -/
theorem St.pinverse [VG.Proof.Rsa.Arm.Keys.InvLaw] {L0 : List Nat} (hZ : aZero ∈ L0) (hL0 : ∀ j ∈ L0, j ∉ invArrs) (hLS : ∀ d ∈ LS, d ∉ invSlots)
    (hv : ∀ σ s, St P E A (aNM :: 3 :: 2 :: 1 :: 0 :: aM :: L0) V LS σ s → A σ aZero = 0 ∧
      A σ aNM + A σ aM = 2 ^ (32 * P.W) ∧ A σ aM % 2 = 1 ∧ 1 < A σ aM ∧ A σ 1 = A σ aM ∧ A σ 2 = 1 ∧ A σ 3 = 0) :
    VP (St P E A (aNM :: 3 :: 2 :: 1 :: 0 :: aM :: L0) V LS) VG.Impl.Rsa.Arm.Keys.inverse
      (St P E (fun σ => upd (upd (A σ) 1 (ivr P.W (A σ 0) (A σ aM)).2.1) 3 (ivr P.W (A σ 0) (A σ aM)).2.2.2)
        (1 :: 3 :: aNM :: aM :: L0) V LS) := by
  refine VP.of_ct (fun σ₁ σ₂ => inverse_cert σ₁ σ₂) fun σ s ⟨e, h, hw⟩ => ?_
  obtain ⟨vZ, vNM, vodd, v1, e1, e2, e3⟩ := hv σ s ⟨e, h, hw⟩
  refine WP.mono (inverse_ok' hw (by decide) (by decide)) fun t ⟨ht, k, r, v⟩ => ⟨e, ?_, ht⟩
  have g : ∀ j ∈ aNM :: 3 :: 2 :: 1 :: 0 :: aM :: L0, num s.mem P.B P.W j = A σ j := fun j hj => h.arrs j hj
  have bk := v (by rw [g aNM (by simp), g aM (by simp)]; exact vNM) (by rw [g aZero (by simp [hZ])]; exact vZ)
    (by rw [g aM (by simp)]; exact vodd) (by rw [g aM (by simp)]; exact v1)
    (by simp only [bank]; rw [g 0 (by simp), g 1 (by simp), g 2 (by simp), g 3 (by simp), g aM (by simp), e1, e2, e3])
  rw [g 0 (by simp), g aM (by simp)] at bk
  have hds : ∀ d ∈ invSlots, SlotOk d := by decide
  refine h.core k (by decide) hds r.sp r.rd r.wr (fun j hj => ?_) (h.sl_keep k hds hLS) (fun j hj => ?_) h.ls_ok
  · dsimp only
    simp only [List.mem_cons] at hj
    rcases hj with rfl | rfl | rfl | rfl | hj
    · rw [upd_ne _ _ (by decide), upd_self]; exact bk.1
    · rw [upd_self]; exact bk.2
    · rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), k.num (by decide) (fun d hd => (hds d hd).1)
        (h.pre.fit (by decide))]
      exact g aNM (by simp)
    · rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), k.num (by decide) (fun d hd => (hds d hd).1)
        (h.pre.fit (by decide))]
      exact g aM (by simp)
    · have n1 : j ≠ 1 := fun x => hL0 j hj (by rw [x]; decide)
      have n3 : j ≠ 3 := fun x => hL0 j hj (by rw [x]; decide)
      rw [upd_ne _ _ n3, upd_ne _ _ n1, k.num (fun i hi ei => by subst ei; exact hL0 _ hj hi)
        (fun d hd => (hds d hd).1) (h.pre.fit (h.live_lt j (by simp [hj])))]
      exact g j (by simp [hj])
  · simp only [List.mem_cons] at hj
    rcases hj with rfl | rfl | rfl | rfl | hj
    · decide
    · decide
    · decide
    · decide
    · exact h.live_lt j (by simp [hj])

/-- `invOf a m`: `inverse` of `[a]` modulo `[m]`, which is odd and above 1. -/
theorem St.pinv [VG.Proof.Rsa.Arm.Keys.InvLaw] {a m : Nat} (cm : Cert (copy aM m)) (ca : Cert (copy 0 a)) (ha : a ∈ L) (hm : m ∈ L)
    (hZ : aZero ∈ L) (hO : aOne ∈ L) (hL : ∀ j ∈ L, j = aZero ∨ 15 ≤ j) (hLS : ∀ d ∈ LS, d ∉ invSlots)
    (hv : ∀ σ, E σ → A σ aZero = 0 ∧ A σ aOne = 1 ∧ A σ m % 2 = 1 ∧ 1 < A σ m) :
    VP (St P E A L V LS) (invOf a m)
      (St P E (fun σ => upd (upd (A σ) 1 (ivr P.W (A σ a) (A σ m)).2.1) 3 (ivr P.W (A σ a) (A σ m)).2.2.2)
        (1 :: 3 :: L) V LS) := by
  have low : ∀ j, (j = aZero ∨ 15 ≤ j) → j ∉ invArrs ∧ j ≠ aM ∧ j ≠ aNM ∧ j ≠ 0 := fun j h => by
    rcases h with rfl | h
    · decide
    · simp only [invArrs, aM, aNM, aT1, aT2, aT3, aT4, List.mem_cons, List.not_mem_nil, or_false]; omega_arith
  have nmM : aM ≠ m := fun x => (low m (hL m hm)).2.1 x.symm
  have na0 : (0 : Nat) ≠ a := fun x => (low a (hL a ha)).2.2.2 x.symm
  have hL0 : ∀ j ∈ L, j ∉ invArrs := fun j hj => (low j (hL j hj)).1
  simp only [invOf, seqs]
  refine VP.seq (St.pcopy cm (by decide) hm nmM) ?_
  refine VP.seq (St.pcopy ca (by decide) (List.mem_cons_of_mem _ ha) na0) ?_
  refine VP.seq (St.pcopy copy1M_taint (by decide) (by simp) (by decide)) ?_
  refine VP.seq (St.pcopy copy2One_taint (by decide) (by simp [hO]) (by decide)) ?_
  refine VP.seq (St.pcopy copy3Zero_taint (by decide) (by simp [hZ]) (by decide)) ?_
  refine VP.seq (St.psub3 subNM_taint (by decide) (by simp [hZ]) (by simp) (by decide) (by decide)) ?_
  refine (St.pinverse (L0 := L) hZ hL0 hLS fun σ s hs => ?_).mono (fun _ _ h => h) fun σ s h => h.mono
    (fun j hj => ⟨?_, ?_⟩) (fun d hd => ⟨hd, rfl⟩)
  · obtain ⟨vZ, vO, vodd, v1⟩ := hv σ hs.1
    have ma : (a = aM) = False := eq_false fun x => (low a (hL a ha)).2.1 x
    have mlt : A σ m < 2 ^ (32 * P.W) := by
      have := hs.2.1.lt (j := aM) (by simp)
      simp (config := {decide := true}) only [upd, ↓reduceIte] at this
      exact this
    simp (config := {decide := true}) only [upd, sub32, ↓reduceIte]
    refine ⟨vZ, ?_, vodd, v1, trivial, vO, vZ⟩
    rw [vZ, Nat.zero_add, Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  · simp only [List.mem_cons] at hj ⊢
    rcases hj with rfl | rfl | hj
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact Or.inr (Or.inr (Or.inr (Or.inr hj)))
  · have ma : (a = aM) = False := eq_false fun x => (low a (hL a ha)).2.1 x
    have m0 : (a = 0) = False := eq_false fun x => (low a (hL a ha)).2.2.2 x
    simp only [List.mem_cons] at hj
    rcases hj with rfl | rfl | hj
    · simp (config := {decide := true}) only [upd, ↓reduceIte, ma]
    · simp (config := {decide := true}) only [upd, ↓reduceIte, ma]
    · obtain ⟨_, l1, l2, l3⟩ := low j (hL j hj)
      have l4 : j ≠ 1 := fun x => hL0 j hj (by rw [x]; decide)
      have l5 : j ≠ 2 := fun x => hL0 j hj (by rw [x]; decide)
      have l6 : j ≠ 3 := fun x => hL0 j hj (by rw [x]; decide)
      simp (config := {decide := true}) only [upd, ↓reduceIte, l1, l2, l3, l4, l5, l6]

end

end VG.Proof.RsaKeyGen.Arm.Key
