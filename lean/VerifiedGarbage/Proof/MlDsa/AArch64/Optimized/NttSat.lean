import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableArtifact
import VerifiedGarbage.Proof.Framework.ConstMem

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def nttSat : State where
  gpr r := if r=.x0 then 4096 else 0
  sp := 131072
  syms _ := 65536
  mem := constMem 65536 staticNttWords
  rd := [⟨65536,3904⟩]
  wr := [⟨4096,1024⟩]

theorem nttSat_held : ∀ i<488,
    nttSat.mem.readW (65536+BitVec.ofNat 64 (8*i)) 64=staticNttWords.getD i 0 := by
  intro i hi
  dsimp only [nttSat]
  exact constMem_held 65536 staticNttWords (by rw [TableConstants.staticNttWords_length]; decide)
    i (by rw [TableConstants.staticNttWords_length]; exact hi)

theorem nttSat_reduced : Reduced nttSat.mem 4096 := by
  intro i hi
  simp only [nttSat,coeffAt,Mem.readW,BitVec.setWidth_eq]
  rw [Mem.read_eq_of_bytes (v := (0#32)) ?_]
  · decide
  · intro j hj
    have ha : ¬ ((4096+BitVec.ofNat 64 (4*i)+BitVec.ofNat 64 j)-65536).toNat<8*staticNttWords.length := by
      rw [TableConstants.staticNttWords_length]
      have hi' : i<256 := hi
      simp only [BitVec.toNat_sub,BitVec.toNat_add,BitVec.toNat_ofNat,show (4096:BitVec 64).toNat=4096 by decide,
        show (65536:BitVec 64).toNat=65536 by decide]
      omega
    simp only [constMem,ha,ite_false]
    simp

end VG.Proof.MlDsa.AArch64.Optimized
