module

public import VerifiedGarbage.Proof.Rsa.Arm.RvFusedState
public import VerifiedGarbage.Proof.Rsa.Arm.RvFusedMasks
import VerifiedGarbage.Proof.Rsa.Arm.RvFusedBitHead
import VerifiedGarbage.Proof.Rsa.Arm.RvFusedCompare
import VerifiedGarbage.Proof.Rsa.Arm.RvTaint3
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Rsa.Arm.RecoverFused
meta import VerifiedGarbage.Proof.Rsa.Arm.RvTaint2
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! The square and root-detection half of one fused exponent bit. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover
open VG.Proof.Rsa.Arm.Keys
open VG.Impl.Rsa.Arm.RecoverFused
open VG.Proof.Rsa (b2n)

def fusedBit (V : Nat → Nat) : Bool := decide (V sByte / 128 % 2 = 1)

theorem fusedBit_word (V : Nat → Nat) : V sByte / 128 % 2 = b2n (fusedBit V) := by
  have bound := Nat.mod_lt (V sByte / 128) (by decide : 0 < 2)
  dsimp only [fusedBit, b2n]
  split_ifs <;> simp_all

def fusedHeadV (V : Nat → Nat) (st : VG.Proof.Rsa.Fused.State) : Nat → Nat :=
  upd (upd (fusedV V st) sBit (b2n (fusedBit V))) sByte (2 * V sByte % 256)

def fusedSquareA (P : RP) (j : Nat) (st : VG.Proof.Rsa.Fused.State) : Nat → Nat :=
  upd (fusedA P j st) mX (st.value * st.value % P.n * Rm P % P.n)

def fusedSquareV (P : RP) (V : Nat → Nat) (st : VG.Proof.Rsa.Fused.State) : Nat → Nat :=
  fusedHitV (upd (upd (fusedHeadV V st) sE1 (b2n (decide (st.value * st.value % P.n = 1))))
    sE2 (b2n (decide (st.value * st.value % P.n = P.n - 1))))
    st.done st.root.isSome (fusedBit V) (decide (st.value * st.value % P.n = 1))
    (decide (st.value * st.value % P.n = P.n - 1))

abbrev fusedSquareSlots : List Nat :=
  [sDone, sOk, sLive, sTmp, sE2, sE1, sByte, sBit] ++ fusedSlots

section
variable {P : RP} {E : State → Prop} {j : Nat} {st : State → VG.Proof.Rsa.Fused.State}
  {V : State → Nat → Nat}

theorem fusedSquare_vp (hn : P.n % 2 = 1 ∧ 1 < P.n)
    (byte : ∀ σ, E σ → V σ sByte < 256) :
    VP (FI P E j st V)
      (seqs [.block bitHead, seqs (mmul iX iY iY), eqAt sE1 mX aO, eqAt sE2 mX aNg, hit])
      (St P E (fun σ => fusedSquareA P j (st σ)) (mX :: fusedKeep)
        (fun σ => fusedAW P σ) [wM] (fun σ => fusedSquareV P (V σ) (st σ))
        fusedSquareSlots P.w nArr) := by
  have pos : 0 < P.n := by omega
  simp only [seqs]
  refine VP.seq (St.pfusedBitHead (by decide) (fun σ e => by
    simpa only [fusedV, upd_ne _ _ (show sByte ≠ sOk by decide),
      upd_ne _ _ (show sByte ≠ sDone by decide)] using byte σ e)) ?_
  refine VP.seq (St.pmmul (o := iX) (a := iY) (b := iY) (by decide) hn.1
    (T := fun σ => (st σ).value * (st σ).value % P.n * Rm P % P.n)
    (by decide) (by decide) (by decide) (by decide) (by decide) (fun σ _ => ?_)) ?_
  · have val : fusedA P j (st σ) (mBase + iY) = (st σ).value * Rm P % P.n := by
      simp [fusedA, upd, mY, mBase, iY]
    rw [val]
    exact ⟨Nat.mod_lt _ pos, Nat.mod_lt _ pos, Nat.mod_lt _ pos, VG.Proof.Rsa.mont_sq_eq _ _ _ _⟩
  refine VP.seq (St.peqMont hn false (d := sE1) (a := mX)
    (y := fun σ => (st σ).value * (st σ).value % P.n) eqX1_taint
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun σ _ => ?_)) ?_
  · refine ⟨?_, ?_, Nat.mod_lt _ pos⟩ <;>
      simp [fusedA, AM, upd, mBase, iX, mX, mY, mG, aO, aRoot, aNg]
  refine VP.seq (St.peqMont hn true (d := sE2) (a := mX)
    (y := fun σ => (st σ).value * (st σ).value % P.n) eqX2_taint
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun σ _ => ?_)) ?_
  · refine ⟨?_, ?_, Nat.mod_lt _ pos⟩ <;>
      simp [fusedA, AM, upd, mBase, iX, mX, mY, mG, aRoot, aNg]
  refine (St.pfusedHit (dn := fun σ => (st σ).done) (ok := fun σ => (st σ).root.isSome)
    (bit := fun σ => fusedBit (V σ)) (e1 := fun σ => decide ((st σ).value * (st σ).value % P.n = 1))
    (e2 := fun σ => decide ((st σ).value * (st σ).value % P.n = P.n - 1))
    (by decide) (fun σ _ => ?_)).mono (fun _ _ h => h) fun σ s h => h.mono
      (fun k hk => ⟨hk, rfl⟩) (fun k hk => ⟨hk, rfl⟩) ?_
  · dsimp [upd, fusedV, sE1, sE2, sDone, sOk, sBit, sByte]
    exact ⟨fusedBit_word (V σ), rfl, rfl, rfl, rfl⟩
  · intro d hd
    refine ⟨hd, ?_⟩
    simp only [fusedSquareV, fusedHeadV]
    rw [← fusedBit_word]
    rfl

end
end VG.Proof.Rsa.Arm.Recover
