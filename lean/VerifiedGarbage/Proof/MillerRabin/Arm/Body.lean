module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Win
import VerifiedGarbage.Proof.MillerRabin.Arm.Mont
import VerifiedGarbage.Proof.MillerRabin.Arm.Ops
import VerifiedGarbage.Proof.Rsa.Arm.KeyDiv
import VerifiedGarbage.Proof.Rsa.Arm.RvKS

/-! # The Miller–Rabin round on ARMv7: the body

From the state `σ` after the push (`In P σ`, `ws` in `r0`): the table's
first entries (`tabInit_vp`), its loop, the windows' start (`winInit_vp`),
the words, the last three squarings with the threshold `4 − σ`, and the
flag into `r0` (`body_vp`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)
open VG.Proof.RsaKeyGen (sigOf sigOf_pos)

/-- The body's start. -/
def Start (P : MP) (σ s : State) : Prop := s = σ ∧ In P σ ∧ σ.gpr .r0 = P.ws

/-- The threshold of the last squarings: `4 − σ`. -/
abbrev rEnd (P : MP) (σ : State) : Nat := 4 - sigOf (tOf P σ % 64)

/-- The flag after the last squarings. -/
abbrev fl (P : MP) (σ : State) : Bool := (sqst P 3 (rEnd P) (fun σ => wst P σ (16 * P.w)) σ 3).2

/-- The body's end: the flag in `r0`. -/
def Done (P : MP) (σ s : State) : Prop :=
  (∃ A L V LS, KS P σ A L V LS s) ∧ s.gpr .r0 = BitVec.ofNat 32 (fl P σ).toNat

/-- The arrays the table's loop starts from: `x` and the original arrays it shifts. -/
abbrev L0 : List Nat := [aX, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]

section
variable {P : MP}

/-- `x`'s top words cleared. -/
theorem St.pclrX {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
    {LS : List Nat} (hx : aX ∈ L) (hv : ∀ σ, E σ → A σ aX = num σ.mem P.B P.W aX) :
    VP (St P E A L V LS) (.block (Impl.Rsa.Arm.Recover.clrTop aX))
      (St P E (fun σ => upd (A σ) aX (xOf P σ)) (aX :: L) V LS) := by
  refine VP.kv clrX_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
  rw [← List.append_nil (Impl.Rsa.Arm.Recover.clrTop aX)]
  refine h.clrTop_ok hw (by decide) fun t ht hwt _ => WP.block_nil ⟨e, ?_, hwt⟩
  have pre := h.pre
  have a1 := (h.arrs aX hx).trans (hv σ e)
  have e1 : val32 s.mem (State.addr P.B) (arr P.W aX) (2 * P.w) = xOf P σ :=
    calc val32 s.mem (State.addr P.B) (arr P.W aX) (2 * P.w)
        = num s.mem P.B P.W aX % 2 ^ (32 * (2 * P.w)) := val32_low _ _ _ _ 2
      _ = num σ.mem P.B P.W aX % 2 ^ (32 * (2 * P.w)) := by rw [a1]
      _ = val32 σ.mem (State.addr P.B) (arr P.W aX) (2 * P.w) := (val32_low _ _ _ _ 2).symm
      _ = xOf P σ := (pre.numAt_val32 σ.mem aX).symm
  rwa [e1] at ht

theorem tabInit_vp : VP (Start P) (seqs tabInit) (TS P 14) := by
  simp only [tabInit, seqs]
  let A0 := fun σ : State => fun j => num σ.mem P.B P.W j
  refine VP.seq (G := St P (In P) A0 L0 (fun _ _ => 0) []) ?_ ?_
  · refine VP.taint [.r0] ctx_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s ⟨hs, pre, r0⟩ => ?_
    · simp only [List.mem_singleton] at hr; subst hr
      rw [h₁.1, h₂.1, h₁.2.2, h₂.2.2]
    · rw [hs, ← List.append_nil ctx]
      have k0 : KS P σ (A0 σ) L0 (fun _ => 0) [] σ :=
        ⟨pre, rfl, rfl, rfl, Keep.refl _ _ _ _ _, fun j _ => rfl, fun _ h => absurd h List.not_mem_nil,
          by decide, fun _ h => absurd h List.not_mem_nil⟩
      exact k0.ctx_ok r0 fun t ht hwt _ _ => WP.block_nil ⟨pre, ht, hwt⟩
  refine VP.seq (St.pcopyClr cT0_taint (by decide) (by decide) (by decide) (by decide)) ?_
  refine VP.seq (St.pclrX (by decide) fun σ _ => rfl) ?_
  refine VP.seq (St.pcopy cT1_taint (by decide) (by decide) (by decide)) ?_
  refine VP.seq (St.pcopy cYX_taint (by decide) (by decide) (by decide)) ?_
  refine St.ptabCnt.mono (fun _ _ h => h) fun σ s h => ⟨by decide, h.mono (fun i hi => ⟨?_, ?_⟩)
    (fun d hd => ⟨by simp only [List.mem_singleton] at hd; simp [hd], by
      simp only [List.mem_singleton] at hd; subst hd; rfl⟩)⟩
  · exact (by decide : ∀ i ∈ LT, i ∈ aY :: (aT0 + 1) :: aX :: aT0 :: L0) i hi
  · simp only [LT, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> rfl

theorem tab_final {σ : State} : ∀ i ∈ LT, i ≠ aY → i ≠ aX → AT P 14 σ i = tv P σ (i - aT0) := by
  intro i hi h1 h2
  simp only [LT, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact absurd rfl h1
  · exact absurd rfl h2
  all_goals rfl

theorem winInit_vp : VP (TS P 0) (seqs winInit) (WO P (2 * P.w)) := by
  simp only [winInit, seqs]
  refine VP.mono (F := St P (In P) (AT P 14) LT (fun _ => upd (fun _ => 0) sK 0) [sK]) ?_ (fun σ s h => h.2)
    (fun _ _ h => h)
  refine VP.seq (St.pcopyClr cM1_taint (by decide) (by decide) (by decide) (by decide)) ?_
  refine VP.seq (St.pcopy cY0_taint (by decide) (by decide) (by decide)) ?_
  refine St.pwinCnt.mono (fun _ _ h => h) fun σ s h => ⟨Nat.le_refl _, h.mono (fun i hi => ⟨?_, ?_⟩)
    (fun d hd => ⟨?_, ?_⟩)⟩
  · exact (by decide : ∀ i ∈ LW, i ∈ aY :: aM1 :: LT) i hi
  · rw [show 16 * P.w - 8 * (2 * P.w) = 0 by omega]
    rcases List.mem_cons.mp hi with rfl | hi
    · rfl
    rcases List.mem_cons.mp hi with rfl | hi
    · rfl
    · obtain ⟨h1, h2, h3⟩ := Lt_ne i hi
      rw [upd_ne _ _ h1, upd_ne _ _ h3, tab_final i ((by decide : ∀ i ∈ Lt, i ∈ LT) i hi) h1 h2, AW_tab hi]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢; rcases hd with rfl | rfl <;> simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · rw [upd_self, upd_self]; omega
    · rw [upd_ne _ _ (by decide), upd_self, upd_ne _ _ (by decide), upd_self,
        show 16 * P.w - 8 * (2 * P.w) = 0 by omega]
      rfl

/-- The threshold from the word `2^(t mod 64)`. -/
theorem rEnd_eq {σ : State} (pre : In P σ) :
    (foldR (BitVec.ofNat 32 (ew P σ (2 * P.w))) (BitVec.ofNat 32 (ew P σ (2 * P.w + 1)))).toNat = rEnd P σ := by
  obtain ⟨e1, e2⟩ := pre.ew_low
  rw [e1, e2, foldR_eq _ (Nat.mod_lt _ (by decide)), ofNat_toNat32 (by omega)]

theorem body_vp (fios : Bool := false) : VP (Start P) (body (fios := fios)) (Done P) := by
  simp only [body, seqs]
  refine VP.seq tabInit_vp (VP.seq (tab_loop (fios := fios)) (VP.seq winInit_vp (VP.seq (words_loop (fios := fios)) ?_)))
  refine VP.mono (F := St P (In P) (AW P (16 * P.w)) LW
    (fun σ => upd (upd (fun _ => 0) sF (wst P σ (16 * P.w)).2.toNat) sK 0) [sK, sF]) ?_ (fun σ s h => h.2)
    (fun _ _ h => h)
  let V' := fun σ => upd (upd (upd (fun _ => 0) sF (wst P σ (16 * P.w)).2.toNat) sK 0) sR (rEnd P σ)
  refine VP.seq (G := SqS P (In P) (AW P (16 * P.w)) LW.tail V' [sQ, sR, sK, sF] 3 (rEnd P)
    (fun σ => wst P σ (16 * P.w)) 3) ?_ ?_
  · refine (St.plowBits (fun σ e => e)).mono (fun _ _ h => h) fun σ s h => ⟨by decide,
      h.mono (fun i hi => ⟨hi, ?_⟩) (fun d hd => ⟨hd, ?_⟩)⟩
    · rcases List.mem_cons.mp hi with rfl | hi
      · rw [upd_self]; unfold AW; rw [ite_eq_left rfl]; rfl
      · exact (upd_ne _ _ ((by decide : ∀ i ∈ LW.tail, i ≠ aY) i hi)).symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl
      · simp only [upd_self]
      · simp only [V', upd, show sR ≠ sQ by decide, show sR ≠ sF by decide, ↓reduceIte]
        exact rEnd_eq h.1
      · simp only [V', upd, show sK ≠ sQ by decide, show sK ≠ sF by decide, show sK ≠ sR by decide, ↓reduceIte]
      · simp only [V', upd, show sF ≠ sQ by decide, show sF ≠ sR by decide, ↓reduceIte]; rfl
  refine VP.seq (sq_loop (fios := fios) (fun σ e => e) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (fun σ _ => rfl) (fun σ _ => upd_self _ _ _)
    (fun σ _ => by show 4 - sigOf (tOf P σ % 64) < 2 ^ 31; omega) (by decide) (fun σ e => wst_lt e _) 2) ?_
  refine VP.kv ret_taint (fun _ _ h => h.2.2.2) fun σ s ⟨_, e, h, hw⟩ => ?_
  refine h.ldr hw (d := sF) (by decide) (r := .r0) (by decide) fun t ht _ u => WP.block_nil ⟨⟨_, _, _, _, ht⟩, ?_⟩
  rw [u.gpr]
  simp only [upd, show sF ≠ sQ by decide, ↓reduceIte]

end

end VG.Proof.MillerRabin.Arm
