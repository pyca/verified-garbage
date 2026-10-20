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

/-- The last candidate, its `y` and whether it gave the factors. -/
abbrev Jl (P : RP) : Nat := P.nt - 1
abbrev yF (P : RP) (σ : State) : Nat := (sqst P σ (Jl P) P.c).1
abbrev okF (P : RP) (σ : State) : Bool := (sqst P σ (Jl P) P.c).2.2

/-- The arrays once `y` is out of Montgomery form. -/
def AY (P : RP) (σ : State) : Nat → Nat := upd (upd (fun _ => 0) aN P.n) mY (yF P σ)

/-- After `y` out of Montgomery form: `y`, `n`, 0, 1 and the mask. -/
abbrev Fy (P : RP) (E : State → Prop) : State → State → Prop :=
  Sk P E (fun σ => upd (upd (AY P σ) aZ 0) aOne 1) [mY, aN, aZ, aOne] (fun _ _ => 0) []
    (fun σ => upd (fun _ => 0) sMask (b2n (okF P σ))) [sMask] P.w nArr

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

/-- `ok` into the mask and `y` out of Montgomery form. -/
theorem finY_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) {E : State → Prop} :
    VP (Cf P E (Jl P)) finY (Fy P E) := by
  have hn0 : 0 < P.n := by omega
  simp only [finY, seqs]
  refine VP.seq (St.pokMask (by decide)) ?_
  refine VP.seq (St.pcopy xmOne_taint (o := mXm) (a := aOne) (by decide) (by decide) (by decide) (by decide)
    (by decide)) ?_
  refine (St.pmmul (o := iY) (a := iY) (b := iXm) (by decide) hn.1 (T := fun σ => yF P σ) (by decide) (by decide)
    (by decide) (by decide) (by decide) fun σ _ => ?_).mono (fun _ _ h => h)
    fun σ s h => ⟨h.1, h.2.1.mono ?_ ?_ ?_, h.2.2.2⟩
  · have e1 : upd (Aq P σ (Jl P) P.c) mXm (Aq P σ (Jl P) P.c aOne) (mBase + iY) = yF P σ * Rm P % P.n := by
      simp [Aq, upd, mXm, mY, mBase, iY]
    have e2 : upd (Aq P σ (Jl P) P.c) mXm (Aq P σ (Jl P) P.c aOne) (mBase + iXm) = 1 := by
      simp [Aq, AM, upd, mXm, mY, mBase, iXm, aOne, aNg, aO, mR2]
    rw [e1, e2]
    have hy := sqst_lt hn0 σ (Jl P) P.c
    exact ⟨Nat.mod_lt _ hn0, by omega, hy, by rw [Nat.mul_one, Nat.mod_mod]⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    refine ⟨by simp only [Lq, liveM, List.mem_cons, List.not_mem_nil, or_false]; omega, ?_⟩
    rcases hx with rfl | rfl | rfl | rfl <;> simp [AY, Aq, AM, upd, mXm, mY, mBase, iY, aOne, aNg, aO, mR2, aZ, aN]
  · intro x hx; simp at hx
  · intro d hd
    simp only [List.mem_singleton] at hd; subst hd
    exact ⟨by simp, by simp [upd, Vq, sMask, sOk, sCand]⟩

end

end VG.Proof.Rsa.Arm.Recover
