module

public import VerifiedGarbage.Proof.Rsa.Arm.RvSk
public import VerifiedGarbage.Proof.Rsa.Arm.RvCand4
public import VerifiedGarbage.Proof.Rsa.Arm.RvTaint3
import VerifiedGarbage.Proof.Rsa.Arm.RvKM
import VerifiedGarbage.Proof.Rsa.Arm.RvSlots
import VerifiedGarbage.Proof.Rsa.Arm.RvMmul2
import VerifiedGarbage.Proof.Bignum.Arm.WideMul

/-! # `vg_rsa_recover_primes` on ARMv7: `y` out of Montgomery form, and `p = gcd(y - 1, n)`

After the candidates (`J = nt - 1` the last): `ok` into the mask, `y` out
of Montgomery form (`finY_vp`), and `inverse`'s start and run
(`gcd_vp`): `[1] = gcd(y - 1, n)` (`y - 1` modulo `2^(32 w)`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa (b2n)

/-- A bounded result supplied by either recovery algorithm. The success
flag determines whether factor extraction's output is used. -/
structure FinishInputs (P : RP) where
  value : State → Nat
  ok : State → Bool
  bounded : ∀ σ, 0 < P.n → value σ < P.n

abbrev Jl (P : RP) : Nat := P.nt - 1

def legacyFinish (P : RP) : FinishInputs P :=
  ⟨fun σ => (sqst P σ (Jl P) P.c).1,
    fun σ => (sqst P σ (Jl P) P.c).2.2,
    fun σ hn => sqst_lt hn σ (Jl P) P.c⟩

abbrev yF (P : RP) (σ : State) (F : FinishInputs P := legacyFinish P) : Nat := F.value σ
abbrev okF (P : RP) (σ : State) (F : FinishInputs P := legacyFinish P) : Bool := F.ok σ

/-- The arrays once `y` is out of Montgomery form. -/
def AY (P : RP) (σ : State) (F : FinishInputs P := legacyFinish P) : Nat → Nat := upd (upd (fun _ => 0) aN P.n) mY (yF (F := F) P σ)

/-- After `y` out of Montgomery form: `y`, `n`, 0, 1 and the mask. -/
abbrev Fy (P : RP) (E : State → Prop) (F : FinishInputs P := legacyFinish P) : State → State → Prop :=
  Sk P E (fun σ => upd (upd (AY (F := F) P σ) aZ 0) aOne 1) [mY, aN, aZ, aOne] (fun _ _ => 0) []
    (fun σ => upd (fun _ => 0) sMask (b2n (okF (F := F) P σ))) [sMask] P.w nArr

section
variable {P : RP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {AW : State → Nat → Nat}
  {LW : List Nat} {V : State → Nat → Nat} {LS : List Nat}

/-- `ok` into the mask. -/
theorem St.pokMask (ho : sOk ∈ LS) :
    VP (St P E A L AW LW V LS P.w nArr) (.block okMask)
      (St P E A L AW LW (fun σ => upd (V σ) sMask (V σ sOk)) (sMask :: LS) P.w nArr) := by
  refine VP.ctx okMask_taint (fun _ _ h => h.2.2.2) fun σ s ⟨e, h, hm, hw⟩ => ?_
  refine h.ldrSlot hw ho (r := .r1) (by decide) fun s1 g1 hw1 u1 => ?_
  refine g1.strSlot_m (hm.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem) hw1 (d := sMask) (r := .r1)
    (by decide) fun t ht mt hwt _ _ => WP.block_nil ⟨e, ?_, mt, hwt⟩
  rw [u1.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [← h.sl sOk ho]; exact BitVec.isLt _)] at ht
  exact ht

end

section
variable {P : RP}

/-- The common interface between either search and factor extraction. -/
def finishA (P : RP) (F : FinishInputs P) (σ : State) : Nat → Nat :=
  upd (AM P) mY (F.value σ * Rm P % P.n)

abbrev FinishStart (P : RP) (E : State → Prop) (F : FinishInputs P) : State → State → Prop :=
  St P E (finishA P F) Lq (fun _ _ => 0) []
    (fun σ => upd (fun _ => 0) sOk (b2n (F.ok σ))) [sOk] P.w nArr

/-- Decode any bounded saved root and preserve its success mask. -/
theorem finYWith_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) {E : State → Prop} (F : FinishInputs P) :
    VP (FinishStart P E F) finY (Fy (F := F) P E) := by
  have hn0 : 0 < P.n := by omega
  simp only [finY, seqs]
  refine VP.seq (St.pokMask (by decide)) ?_
  refine VP.seq (St.pcopy xmOne_taint (o := mXm) (a := aOne) (by decide) (by decide) (by decide) (by decide)
    (by simp)) ?_
  refine (St.pmmul (o := iY) (a := iY) (b := iXm) (by decide) hn.1
    (T := F.value) (by decide) (by decide) (by decide) (by decide) (by simp) fun σ _ => ?_).mono
    (fun _ _ h => h) fun σ s h => ⟨h.1, h.2.1.mono ?_ ?_ ?_, h.2.2.2⟩
  · have e1 : upd (finishA P F σ) mXm (finishA P F σ aOne) (mBase + iY) =
        F.value σ * Rm P % P.n := by simp [finishA, upd, mXm, mY, mBase, iY]
    have e2 : upd (finishA P F σ) mXm (finishA P F σ aOne) (mBase + iXm) = 1 := by
      simp [finishA, AM, upd, mXm, mY, mBase, iXm, aOne, aNg, aO, mR2]
    rw [e1, e2]
    exact ⟨Nat.mod_lt _ hn0, by omega, F.bounded σ hn0,
      by rw [Nat.mul_one, Nat.mod_mod]⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    refine ⟨by simp only [Lq, liveM, List.mem_cons, List.not_mem_nil, or_false]; omega, ?_⟩
    rcases hx with rfl | rfl | rfl | rfl <;>
      simp [AY, finishA, AM, upd, mXm, mY, mBase, iY, aOne, aNg, aO, mR2, aZ, aN, yF]
  · intro x hx; simp at hx
  · intro d hd
    simp only [List.mem_singleton] at hd; subst hd
    exact ⟨by simp, by simp [upd, sMask, sOk, okF]⟩

/-- The original search supplies the same common factor-extraction input. -/
theorem finY_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) {E : State → Prop} :
    VP (Cf P E (Jl P)) finY (Fy P E) := by
  refine (finYWith_vp hn (legacyFinish P)).mono (fun σ s h => h.mono ?_ ?_ ?_) (fun _ _ h => h)
  · intro j hj
    exact ⟨hj, by simp only [finishA, legacyFinish, Aq]⟩
  · intro j hj; simp at hj
  · intro d hd
    simp only [List.mem_singleton] at hd; subst hd
    exact ⟨by decide, by simp [upd, Vq, sOk, sCand, legacyFinish]⟩

end

end VG.Proof.Rsa.Arm.Recover
