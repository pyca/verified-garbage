module
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Arguments
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ProbablePrime
public import Mathlib.Data.Int.ModEq

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Workspace
import VerifiedGarbage.Proof.Framework.Omega

/-! # Frame words outside the arithmetic workspace keep their values -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.MillerRabin.X86_64 VG.Impl.Bignum.X86_64

/-- A frame word outside the arithmetic workspace survives bounded writes. -/
theorem frame_word_of_workspace {B F : Addr} {Z k : Nat} {rs : List (Nat × Nat)} {m m' : Mem}
    (hf : Frm B rs m m') (hr : ∀ r ∈ rs, r.1 + r.2 ≤ Z)
    (ho : ∀ i < 8, Z ≤ ofs B (off (off F (8 * k)) i)) :
    word m' F (8 * k) = word m F (8 * k) := by
  apply Mem.readW_congr
  intro i hi
  exact hf _ (fun r h => Or.inr (Nat.le_trans (hr r h) (ho i hi)))

end VG.Proof.Dsa.X86_64.Generation
