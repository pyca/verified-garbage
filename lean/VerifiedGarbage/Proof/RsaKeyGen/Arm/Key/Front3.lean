module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Front2
public import VerifiedGarbage.Proof.Rsa.Arm.RvRest
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # An RSA key on ARMv7: `φ` and its halving (`halving_vp`)

`φ = pm qm`, then `8 p_len` steps of the halving of `(u, v, φ)` from
`(pm, qm, φ)` while `u` and `v` are both even: the stage `S2`, with the
halving's result `hv` (`Proof/RsaKeyGen/KeyMath.lean`'s `halveIter`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP sub32 VP.of_imp)
open VG.Proof.Rsa (b2n)
open VG.Proof.RsaKeyGen (halveIter halveStep)

section
variable {P : KP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

/-- `norTail`: `sH := ¬(sBu ∨ sBv)`. -/
theorem St.pnor {X Y : State → Bool} (ha : sBu ∈ LS) (hb : sBv ∈ LS) (hX : ∀ σ, E σ → V σ sBu = b2n (X σ))
    (hY : ∀ σ, E σ → V σ sBv = b2n (Y σ)) :
    VP (St P E A L V LS) (.block norTail) (St P E A L (fun σ => upd (V σ) sH (b2n (!(X σ || Y σ)))) (sH :: LS)) :=
  VP.kv nor_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    unfold norTail
    refine h.ldr hw ha (r := .r1) (by decide) fun s1 h1 hw1 u1 => ?_
    refine h1.ldr hw1 hb (r := .r2) (by decide) fun s2 h2 hw2 u2 => ?_
    refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
    have h3 := h2.of_rest (u3.rest (ws := [.r1]) (by simp)) u3.mem
    have hw3 := hw2.of_upd u3 (by decide) (by decide) (by decide)
    refine wp_dp (op2_imm (by decide)) fun s4 u4 => ?_
    have h4 := h3.of_rest (u4.rest (ws := [.r1]) (by simp)) u4.mem
    have hw4 := hw3.of_upd u4 (by decide) (by decide) (by decide)
    refine h4.str hw4 (by decide) fun t ht hwt _ => WP.block_nil ⟨e, ?_, hwt⟩
    have x3 : s3.gpr .r1 = BitVec.ofNat 32 (b2n (X σ || Y σ)) := by
      rw [u3.gpr, dpVal, u2.gpr, u2.other _ (by decide), u1.gpr, hX σ e, hY σ e]
      apply BitVec.eq_of_toNat_eq; rw [b2n_or, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (b2n_lt _)]
    rwa [u4.gpr, dpVal, x3, b2n_xor] at ht

/-- `str r6, [r8, #sHc]`. -/
theorem St.pstrHc {n : Nat} :
    VP (fun σ s => St P E A L V LS σ s ∧ s.gpr .r6 = BitVec.ofNat 32 n) (.block [.str .r6 .r8 sHc])
      (St P E A L (fun σ => upd (V σ) sHc (n % 2 ^ 32)) (sHc :: LS)) :=
  VP.kv strHc_taint (fun _ _ h => h.1.2.2) fun σ s ⟨⟨e, h, hw⟩, r6⟩ =>
    h.str hw (by decide) fun t ht hwt _ => WP.block_nil ⟨e, by rwa [r6, BitVec.toNat_ofNat] at ht, hwt⟩

/-- `cntDown`: the count decremented, Z when it reaches 0. -/
theorem St.pcntDown {n : Nat} (hc : sHc ∈ LS) (hn : n + 1 < 2 ^ 32) (hv : ∀ σ, E σ → V σ sHc = n + 1) :
    VP (St P E A L V LS) (.block cntDown)
      (fun σ s => St P E A L (fun σ => upd (V σ) sHc n) (sHc :: LS) σ s ∧ s.z = decide (n = 0)) :=
  VP.kv cntDown_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    unfold cntDown
    refine h.ldr hw hc (r := .r1) (by decide) fun s1 h1 hw1 u1 => ?_
    refine wp_subs (op2_imm (by decide)) fun s2 u2 z2 => ?_
    have h2 := h1.of_rest (u2.rest (ws := [.r1]) (by simp)) u2.mem
    have hw2 := hw1.of_upd u2 (by decide) (by decide) (by decide)
    have e2 : s2.gpr .r1 = BitVec.ofNat 32 n := by
      rw [u2.gpr, u1.gpr, hv σ e]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
      omega
    refine h2.strz hw2 (by decide) fun t ht hwt zt => WP.block_nil ⟨⟨e, ?_, hwt⟩, ?_⟩
    · rwa [e2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
    · rw [zt, z2, u1.gpr, hv σ e, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
      simp

end

/-- `k` steps of the halving. -/
def hk (P : KP) (σ : State) (k : Nat) : Nat × Nat × Nat := halveIter k (pm P σ, qm P σ, pm P σ * qm P σ)

/-- The arrays after `k` steps of the halving. -/
def AH (P : KP) (σ : State) (k : Nat) : Nat → Nat :=
  upd (upd (upd (A1 P σ) aU (hk P σ k).1) aV (hk P σ k).2.1) aF (hk P σ k).2.2

abbrev LH : List Nat := aF :: aV :: aU :: L1

/-- The halving with `c` steps left. -/
def IH (P : KP) (E : State → Prop) (c : Nat) (σ s : State) : Prop :=
  St P E (fun σ => AH P σ (8 * P.K - c)) LH (fun _ => upd (fun _ => 0) sHc c) [sHc] σ s ∧ c ≤ 8 * P.K

/-- After the halving. -/
abbrev S2 (P : KP) (E : State → Prop) : State → State → Prop :=
  St P E (fun σ => AH P σ (8 * P.K)) LH (fun _ _ => 0) []

section
variable {P : KP}

theorem hk_succ (P : KP) (σ : State) (k : Nat) : hk P σ (k + 1) = halveStep (hk P σ k) :=
  VG.Proof.RsaKeyGen.halveIter_succ' k _

theorem hk_le (P : KP) (σ : State) (k : Nat) :
    (hk P σ k).1 ≤ pm P σ ∧ (hk P σ k).2.1 ≤ qm P σ ∧ (hk P σ k).2.2 ≤ pm P σ * qm P σ := by
  obtain ⟨j, ha, hb, hf⟩ := VG.Proof.RsaKeyGen.halveIter_inv k (a := pm P σ) (b := qm P σ)
    (st := (pm P σ, qm P σ, pm P σ * qm P σ)) ⟨0, by simp, by simp, by simp⟩
  unfold hk
  generalize halveIter k (pm P σ, qm P σ, pm P σ * qm P σ) = st at ha hb hf
  obtain ⟨u, v, f⟩ := st
  dsimp only at ha hb hf ⊢
  have p : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  refine ⟨?_, ?_, ?_⟩
  · rw [ha]; exact Nat.le_mul_of_pos_left _ p
  · rw [hb]; exact Nat.le_mul_of_pos_left _ p
  · rw [ha, hb, hf]
    exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ p)

/-- `φ` and the halving's start. -/
theorem halvingStart_vp {E : State → Prop} {c : Prog isa} {G : State → State → Prop}
    (hc : VP (IH P E (8 * P.K)) c G) :
    VP (S1 P E) (seqs [mulFrom aF aPm aQm aZero cnt8, copy aU aPm, copy aV aQm,
      .seq (.block (cnt8 ++ ([.str .r6 .r8 sHc] : List Instr))) c]) G := by
  simp only [seqs]
  have m1 : ∀ σ : State, A1 P σ aMod = 2 ^ (32 * P.W - 1) := fun σ => by
    simp (config := {decide := true}) only [A1, A0, upd, ↓reduceIte]
  have z1 : ∀ σ : State, A1 P σ aZero = 0 := fun σ => by
    simp (config := {decide := true}) only [A1, A0, Aload, upd, ↓reduceIte]
  have pm1 : ∀ σ : State, A1 P σ aPm = pm P σ := fun σ => by
    simp (config := {decide := true}) only [A1, upd, ↓reduceIte]
  have qm1 : ∀ σ : State, A1 P σ aQm = qm P σ := fun σ => by
    simp (config := {decide := true}) only [A1, upd, ↓reduceIte]
  have b8 : ∀ σ : State, pm P σ < 2 ^ (32 * P.W - 1) := fun σ =>
    Nat.lt_of_lt_of_le (pm_lt P σ) (Nat.pow_le_pow_right (by decide) (by simp only [KP.W]; omega))
  refine VP.seq (St.pmulFrom myQm_taint mxPm_taint maZero_taint fMa_taint St.pcnt8 (n := 8 * P.K)
    (fun σ pre => by have := pre.k1; have := pre.k2; omega)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by decide) (by decide) (by decide) (by simp)
    fun σ _ => ⟨z1 σ, by rw [z1, m1]; exact Nat.two_pow_pos _, by rw [pm1, m1]; exact b8 σ, by
      rw [m1, Nat.mul_comm, ← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) (by simp only [KP.W]; omega)⟩) ?_
  refine VP.seq (St.pcopy uPm_taint (by decide) (by simp) (by decide)) ?_
  refine VP.seq (St.pcopy vQm_taint (by decide) (by simp) (by decide)) ?_
  refine VP.seq ?_ hc
  refine (VP.block_append (l₁ := cnt8) St.pcnt8 St.pstrHc).mono (fun _ _ h => h) fun σ s h =>
    ⟨h.mono (fun j hj => ⟨by mem_sub, ?_⟩) (fun d hd => ⟨hd, ?_⟩), Nat.le_refl _⟩
  · have phi : (0 + qm P σ % 2 ^ (8 * P.K) * pm P σ) % 2 ^ (32 * P.W - 1) = pm P σ * qm P σ := by
      rw [Nat.zero_add, Nat.mod_eq_of_lt (qm_lt P σ), Nat.mul_comm]
      refine Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (phi_lt P σ) (Nat.pow_le_pow_right (by decide) ?_))
      simp only [KP.W]; omega
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [AH, hk, upd, ↓reduceIte, Nat.sub_self, halveIter, pm1, qm1, z1, m1, phi]
  · simp only [List.mem_singleton] at hd; subst hd
    rw [upd_self, upd_self, Nat.mod_eq_of_lt (by have := h.2.1.pre.k2; omega)]

/-- One step of the halving, with `n + 1` left. -/
theorem halfStep_vp {E : State → Prop} (n : Nat) :
    VP (IH P E (n + 1)) halfStep (fun σ s => isa.eval .ne s = some (decide (0 < n)) ∧
      (n = 0 → IH P E 0 σ s) ∧ (0 < n → IH P E n σ s)) := by
  refine VP.of_imp (p := n + 1 ≤ 8 * P.K ∧ P.K ≤ 512) (fun _ _ h => ⟨h.2, h.1.2.1.pre.k2⟩) fun ⟨hb, k2⟩ => ?_
  refine VP.mono (F := St P E (fun σ => AH P σ (8 * P.K - (n + 1))) LH (fun _ => upd (fun _ => 0) sHc (n + 1)) [sHc])
    ?_ (fun _ _ h => h.1) fun _ _ h => h
  simp only [halfStep, seqs]
  rw [bothEven_eq]
  refine VP.seq (VP.block_append (St.pbitOf bitU_taint (by simp) (by decide))
    (VP.block_append (St.pbitOf bitV_taint (by simp) (by decide))
      (St.pnor (X := fun σ => decide (AH P σ (8 * P.K - (n + 1)) aU % 2 = 1))
        (Y := fun σ => decide (AH P σ (8 * P.K - (n + 1)) aV % 2 = 1)) (by simp) (by simp)
        (fun _ _ => by rw [upd_ne _ _ (by decide), upd_self]) (fun _ _ => by rw [upd_self])))) ?_
  refine VP.seq (St.phalfSel tU_taint t2U_taint sU_taint (by simp) (by decide) (by decide) (by decide) (by simp)
    fun _ _ => by rw [upd_self]; exact b2n_le' _) ?_
  refine VP.seq (St.phalfSel tV_taint t2V_taint sV_taint (by simp) (by decide) (by decide) (by decide) (by simp)
    fun _ _ => by rw [upd_self]; exact b2n_le' _) ?_
  refine VP.seq (St.phalfSel tF_taint t2F_taint sF_taint (by simp) (by decide) (by decide) (by decide) (by simp)
    fun _ _ => by rw [upd_self]; exact b2n_le' _) ?_
  refine (St.pcntDown (n := n) (by simp) (by omega) fun _ _ => by
    simp (config := {decide := true}) only [upd, ↓reduceIte]).mono (fun _ _ h => h) fun σ s ⟨h, z⟩ => ?_
  have st : St P E (fun σ => AH P σ (8 * P.K - n)) LH (fun _ => upd (fun _ => 0) sHc n) [sHc] σ s := by
    refine h.mono (fun j hj => ⟨by mem_sub, ?_⟩) (fun d hd => ⟨by simp only [List.mem_singleton] at hd; simp [hd], ?_⟩)
    · have e : 8 * P.K - n = (8 * P.K - (n + 1)) + 1 := by omega
      rw [e]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> simp (config := {decide := true}) only [AH, upd, ↓reduceIte]
      all_goals
        rw [hk_succ]
        generalize hk P σ (8 * P.K - (n + 1)) = st
        obtain ⟨u, v, f⟩ := st
        unfold halveStep
        by_cases hu : u % 2 = 0 <;> by_cases hv : v % 2 = 0 <;> simp [hu, hv, b2n]
    · simp only [List.mem_singleton] at hd; subst hd; simp only [upd_self]
  refine ⟨?_, fun h0 => ⟨?_, by omega⟩, fun hp => ⟨st, by omega⟩⟩
  · show some (!s.z) = _; rw [z]; simp only [Option.some.injEq]; by_cases h0 : n = 0 <;> simp [h0] <;> omega
  · subst h0; exact st

/-- `φ` and its halving. -/
theorem halving_vp {E : State → Prop} : VP (S1 P E) halving (S2 P E) := by
  refine VP.of_imp (p := 1 ≤ 8 * P.K) (fun _ _ h => by have := h.2.1.pre.k1; omega) fun hk => ?_
  have e : halving = seqs [mulFrom aF aPm aQm aZero cnt8, copy aU aPm, copy aV aQm,
      .seq (.block (cnt8 ++ [.str .r6 .r8 sHc])) (.loop halfStep .ne)] := rfl
  rw [e]
  refine halvingStart_vp ?_
  have l := VP.loop (I := fun c => IH P E c) (fun n => halfStep_vp n) (8 * P.K - 1)
  rw [show 8 * P.K - 1 + 1 = 8 * P.K by omega] at l
  refine l.mono (fun _ _ h => h) fun σ s h => ?_
  exact h.1.mono (fun j hj => ⟨hj, by rw [Nat.sub_zero]⟩) (fun d hd => absurd hd (by simp))

end

end VG.Proof.RsaKeyGen.Arm.Key
