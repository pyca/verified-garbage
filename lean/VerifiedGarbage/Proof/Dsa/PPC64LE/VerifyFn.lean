module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyFront
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyBody
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.Accepted
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# DSA verification on PPC64LE: the function

`verify_correct`: `vg_dsa_verify` meets `vContract`. After `entry`
(`front_ok`), `checkKey` either runs `body` (`body_ok`) or leaves 0, and
`restore` gives back the nonvolatile registers (`finish_ok`); the result is
the specification's by `Proof/Dsa/Accepted.lean`'s `verifyBytes_compute`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE

/-- The bytes of a buffer apart from `scratch`, kept by a change in its first `n` bytes. -/
theorem Src.bytesOut {s : State} {L : Lay} {D : Addr} {k : Nat} (h : Src s L D k) {m m' : Mem} {n : Nat}
    (ho : Outside L.S 0 n m m') (hn : n ≤ L.Z) : Spec.Rsa.bytesAt m' D k = Spec.Rsa.bytesAt m D k := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ho _ (Or.inr ?_)
  have hi := List.mem_range.mp hi
  by_contra hc
  exact h.sep i hi (D + BitVec.ofNat 64 i) (by omega) rfl

theorem ret_ofNat (c : Prop) [Decidable c] :
    ((BitVec.ofNat 64 (if c then 1 else 0)).setWidth 32).toNat = if c then 1 else 0 := by
  split <;> rfl

theorem saved_only_r2 : ∀ r ∈ preserved, (∀ i < 18, r ≠ saved i) → r = .r2 := by decide

/-- `restore`, from a state with `S` in `r21`, `s`'s nonvolatile registers in
the saved words, and `r2` kept. -/
theorem finish_ok {s u : State} {S : Addr} {rs : List Reg} (h21 : u.gpr .r21 = S)
    (hwr : ∀ i < 18, InRegions u.wr (off (savW S) (8 * i)) 8)
    (hsav : ∀ i < 18, word u.mem S (saveOff i) = s.gpr (saved i)) (hk : Keep rs s u) (hr2 : Reg.r2 ∉ rs) :
    WP isa (.block restore) u fun w => abiPreserved s w ∧ w.gpr .r3 = u.gpr .r3 := by
  refine WP.mono (restore_ok u (v := fun i => s.gpr (saved i)) h21 hwr fun i hi => ?_)
    fun w ⟨wrs, wot, _, _, _, wsp, wlr⟩ => ⟨⟨fun r hr => ?_, by rw [wsp, hk.sp], by rw [wlr, hk.lr]⟩,
      wot .r3 (by decide)⟩
  · rw [← hsav i hi]
    show u.mem.readW (S + BitVec.ofNat 64 112 + BitVec.ofNat 64 (8 * i)) 64 = u.mem.readW (S + BitVec.ofNat 64 (112 + 8 * i)) 64
    rw [Offset.add_add]
  · by_cases hs' : ∃ i < 18, r = saved i
    · obtain ⟨i, hi, rfl⟩ := hs'
      exact wrs i hi
    · have hn : ∀ i < 18, r ≠ saved i := fun i hi e => hs' ⟨i, hi, e⟩
      have := saved_only_r2 r hr hn
      subst this
      rw [wot .r2 hn, hk.gpr .r2 hr2]

theorem verify_correct (s : State) (h : vContract.pre s) :
    ∃ tr t, Exec isa Verify.verify s tr t ∧ abiPreserved s t ∧ vContract.post s t := by
  sorry

end VG.Proof.Dsa.PPC64LE
