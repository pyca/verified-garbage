module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenPrefix
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TableApart
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Tables
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixTable
public import VerifiedGarbage.Proof.MlKem.AArch64.KgA
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenTiming
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.MlKem.AArch64.KeyGen
variable {P : KemLay}
theorem keyGen_using_prefix (hash : FixedHash.HashFn)
 (hG : FixedHash.HashCorrect hash .x28 KG.ST KG.WK 72 6
  [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩] [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩]) {s : State} (hp : KeyGen.Pre P s) (tables : Tables s)
    (depth : (FixedHashCallers.kgAUsing hash P).aarch64Depth≤1) :
    WP isa (FixedHashCallers.kgAUsing hash P) s (fun t=>AfterA P s t ∧ MatrixTable P s t) := by
  refine WP.mono (WP.tablesDepth (a_using_ok hash hG hp) tables depth) fun t ⟨ha,tb⟩=>?_
  have scratch : Covers [⟨kA s 3,P.scl⟩] t.wr := by
    simpa only [R,ptr_zero] using cov_w hp ha.kb (b:=3) (o:=0) (l:=P.scl) (by decide) (by kl)
  exact ⟨ha,tb.shuffle,tb.shuffleRead,apart_of_covers tb.shuffleApart scratch⟩
end VG.Proof.MlKem.AArch64.Optimized
