module
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Result
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Words
import VerifiedGarbage.Proof.MlKem.AArch64.Barrett
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem
open VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.Ntt16.Readonly

/-- The emitted readonly gamma artifact, as its 64 doublewords. -/
def GammaArtifact (m : Mem) (p : Addr) : Prop :=
  ∀ i < 64, m.readW (p+BitVec.ofNat 64 (8*i)) 64 = (words 32 gammaTable).getD i 0

theorem GammaArtifact.word {m : Mem} {p : Addr} (h : GammaArtifact m p)
    {k : Nat} (hk : k < 128) :
    m.readW (p+BitVec.ofNat 64 (4*k)) 32 = BitVec.ofNat 32 (gammaValues k) := by
  have hi : k/2 < 64 := by omega
  have hv := h (k/2) hi
  have hr : k%2=0 ∨ k%2=1 := by omega
  have hg : gammaTable.getD k 0 = gammaValues k := by
    rw [gammaTable_eq,gammas_getD hk]; rfl
  rw [←hg]
  rcases hr with hr | hr
  · have he : k=2*(k/2) := by omega
    have hx := congrArg (fun v : BitVec 64 => v.extractLsb' 0 32) hv
    rw [readW64_lo,Ntt16.Readonly.gamma_low _ hi] at hx
    simpa only [show 8*(k/2)=4*k by omega,←he] using hx
  · have he : k=2*(k/2)+1 := by omega
    have hx := congrArg (fun v : BitVec 64 => v.extractLsb' 32 32) hv
    rw [readW64_hi,Ntt16.Readonly.gamma_high _ hi,BitVec.add_assoc,
      ←BitVec.ofNat_add (8*(k/2)) 4] at hx
    simpa only [show 8*(k/2)+4=4*k by omega,←he] using hx

theorem GammaArtifact.lanes {m : Mem} {p : Addr} (h : GammaArtifact m p)
    {c : Nat} (hc : c < 32) :
    Lanes (m.read (p+BitVec.ofNat 64 (16*c)) 16) (blockGamma gammaValues c) := by
  have hs : p+BitVec.ofNat 64 (16*c) = coeffAddr p (4*c) := by
    unfold coeffAddr; congr 2; omega
  rw [hs]
  apply lanes_coeffs (m:=m) (p:=p) (j:=4*c)
  intro e he
  change (m.readW (p+BitVec.ofNat 64 (4*(4*c+e))) 32).toNat = gammaValues (4*c+e)
  rw [h.word (by omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
  exact Nat.lt_trans (gamma (4*c+e)).isLt (by decide)

end VG.Proof.MlKem.AArch64.Dot
