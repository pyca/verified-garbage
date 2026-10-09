import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableMemory
import VerifiedGarbage.Proof.Framework.ConstMem

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

def inverseSat : State where
  gpr r := if r=.x0 then 4096 else if r=.x1 then 8192 else 0
  sp := 131072
  syms _ := 65536
  mem := constMem 65536 expandedWords
  rd := [⟨65536,3904⟩]
  wr := [⟨4096,1024⟩,⟨8192,1024⟩]

theorem inverseSat_held : ∀ i<488,
    inverseSat.mem.readW (65536+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0 := by
  intro i hi
  dsimp only [inverseSat]
  exact constMem_held 65536 expandedWords (by rw [InverseTable.expandedWords_length]; decide)
    i (by rw [InverseTable.expandedWords_length]; exact hi)

theorem inverseSat_reduced : Reduced inverseSat.mem 4096 := by
  intro i hi
  simp only [inverseSat,coeffAt,Mem.readW,BitVec.setWidth_eq]
  rw [Mem.read_eq_of_bytes (v := (0#32)) ?_]
  · decide
  · intro j hj
    have ha : ¬ ((4096+BitVec.ofNat 64 (4*i)+BitVec.ofNat 64 j)-65536).toNat<8*expandedWords.length := by
      rw [InverseTable.expandedWords_length]
      have hi' : i<256 := hi
      simp only [BitVec.toNat_sub,BitVec.toNat_add,BitVec.toNat_ofNat,show (4096:BitVec 64).toNat=4096 by decide,
        show (65536:BitVec 64).toNat=65536 by decide]
      omega
    simp only [constMem,ha,ite_false]
    simp

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
