import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourRead
import VerifiedGarbage.Proof.Framework.AArch64.Tbl

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour

def initLo (mask : Nat) : BitVec 64 := BitVec.ofNat 64 (bytesWord ((shuffleBytes mask).take 8))
def initHi (mask : Nat) : BitVec 64 := BitVec.ofNat 64 (bytesWord ((shuffleBytes mask).drop 8))

def initEntry (mask : Nat) : List Instr :=
 VG.Impl.Tbl.AArch64.const64 .x6 (initLo mask) ++
 ([.str .x .x6 .x19 (6000+64*mask)] : List Instr) ++
 VG.Impl.Tbl.AArch64.const64 .x6 (initHi mask) ++
 [.str .x .x6 .x19 (6000+64*mask+8),
  .movz .x .x6 (BitVec.ofNat 16 (acceptedIndices mask).length) 0,
  .str .x .x6 .x19 (6000+64*mask+32)]

theorem entryInit_eq {mask : Nat} (hm : mask<16) : entryInit true mask=initEntry mask := by
  have h : ∀m : Fin 16,entryInit true m.val=initEntry m.val := by decide
  exact h ⟨mask,hm⟩

theorem init_words {mask : Nat} (hm : mask<16) :
    ofVDwords (initLo mask) (initHi mask)=shuffleWord mask := by
  have h : ∀m : Fin 16,ofVDwords (initLo m.val) (initHi m.val)=shuffleWord m.val := by decide
  exact h ⟨mask,hm⟩

theorem init_count {mask : Nat} (hm : mask<16) :
    (BitVec.ofNat 16 (acceptedIndices mask).length).setWidth 64=
      BitVec.ofNat 64 (acceptedIndices mask).length := by
  have h : ∀m : Fin 16,(BitVec.ofNat 16 (acceptedIndices m.val).length).setWidth 64=
      BitVec.ofNat 64 (acceptedIndices m.val).length := by decide
  exact h ⟨mask,hm⟩
end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
