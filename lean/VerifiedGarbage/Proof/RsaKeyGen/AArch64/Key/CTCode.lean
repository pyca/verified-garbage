import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTSmall
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTTail
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTFront

/-!
# `vg_rsa_keygen_key` on AArch64: constant time

The pieces leak the same in runs with the same public data (`KP`): the
front, the lcm, `d` (whose branches depend on `e` alone), the mask of a
small `d`, and the branch on it (`branch_ct`: status 2, the leak's), to the
zeros or to the key and its outputs (`keyCode_ct`); hence the contract's
`ConstantTime` (`keyCode_constantTime`).
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

theorem code_ct_eq : code = seqs (([.block (entry ++ VG.Impl.Rsa.AArch64.Keys.head)] : List (Prog isa)) ++
    (frontL ++ (lcmPart ++ (([dPart] : List (Prog isa)) ++ (smallMask ++
      ([.ite (.nonzero .x .x15) (zeros 2) keyPart] : List (Prog isa))))))) := by
  simp only [code, frontL, List.append_assoc]

/-- The branch on a small `d`, status 2 (the leak's). -/
theorem branch_ct : RelCT isa (Two (KG FF)) (.ite (.nonzero .x .x15) (zeros 2) keyPart) fun _ _ => True :=
  kg_ite (kg_nonzero_eq (g := fun p => mask (decide (p.st = 2))) fun _ _ hf => hf.x15)
    (zeros2_ct.mono (fun _ _ ⟨p, h₁, h₂, hsp⟩ =>
      ⟨p, EG.of_kg (h₁.imp fun _ _ => trivial), EG.of_kg (h₂.imp fun _ _ => trivial), hsp⟩)
      fun _ _ h => h)
    (keyPart_ct.mono (fun _ _ h => two_kg (fun _ _ ⟨⟨hp, _, ok, hok, _⟩, _⟩ => ⟨hp, ok, hok⟩) h) fun _ _ h => h)

/-- `vg_rsa_keygen_key` leaks the same in runs with the same public data. -/
theorem keyCode_ct : RelCT isa (Two KRel) code fun _ _ => True := by
  rw [code_ct_eq]
  refine rs_app (by simp) (by simp [frontL, loadA]) Key.start_ct ?_
  refine rs_app (by simp [frontL, loadA]) (by simp [lcmPart, phi, mulTo]) front_ct ?_
  refine rs_app (by simp [lcmPart, phi, mulTo]) (by simp) lcmPart_ct ?_
  refine rs_app (by simp) (by simp [smallMask, constA]) dPart_ct ?_
  exact rs_app (by simp [smallMask, constA]) (by simp) smallMask_ct branch_ct

/-- `vg_rsa_keygen_key` is constant time but for the lengths, `e`, and
whether `d` is too small. -/
theorem keyCode_constantTime : ConstantTime isa keyA.pre keyA.pub code := keyCT_of keyCode_ct

end VG.Proof.RsaKeyGen.AArch64.Key
