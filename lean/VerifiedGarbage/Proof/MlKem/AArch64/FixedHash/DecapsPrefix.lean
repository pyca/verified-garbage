module
public import VerifiedGarbage.Impl.MlKem.AArch64.FixedHashDecaps
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DecryptStart
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TableApart
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Tables
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixCall
public import VerifiedGarbage.Proof.MlKem.AArch64.DecapsA
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.EncapsTiming
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem
open VG.Proof.MlKem.AArch64.Kem
variable {P : KemLay}
theorem decaps_using_prefix (hash : FixedHash.HashFn)
 (hG : FixedHash.HashCorrect hash .x28 KEM.ST KEM.WK 72 6
 [⟨.x28,KEM.MB,32⟩,⟨.x25,768*P.k+32,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩]) {s : State} (hp : Pre P (Decaps.deL P) s) (calls : Calls P) (tables : Tables s)
    (depth : (Impl.MlKem.AArch64.FixedHashDecaps.deStartUsing hash P).aarch64Depth≤1) :
    WP isa (Impl.MlKem.AArch64.FixedHashDecaps.deStartUsing hash P) s
      (fun t=>BInv P (Decaps.deL P) s t.mem (Decaps.rhoD P s) 0 t ∧ MatrixTable P (Decaps.deL P) s t) := by
  have scratch : Covers [⟨kA s (Decaps.deL P).sc,P.scl⟩] s.wr := by
    have hh := cov_w₀ hp (b:=(Decaps.deL P).sc) (o:=0) (l:=P.scl) ⟨hp.scw,hp.scb⟩ (by rw [hp.scl]; omega)
    simpa only [R,ptr_zero] using hh
  refine WP.mono (WP.tablesDepth (Decaps.start_using_ok hash hG hp calls tables.transforms tables.gamma tables.gammaRead
    (apart_of_covers tables.gammaApart scratch)) tables depth) fun t ⟨ha,tb⟩=>?_
  exact ⟨BInv.zero ha.kb ha.x24 ha.rho,matrix_table_of_kb hp ha.kb tb⟩

end VG.Proof.MlKem.AArch64.Optimized
