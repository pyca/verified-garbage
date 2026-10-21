module

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Pre
public import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
public import VerifiedGarbage.Proof.MlKem.Mem

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Ntt16.Readonly
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem.AArch64

/-- A readonly table's caller obligations, independent of polynomial values. -/
structure TableReady (s : State) (symbol : String) (H : List Nat) (f w : Addr) : Prop where
  table : ∀ i<64, s.mem.readW (s.syms symbol+BitVec.ofNat 64 (8*i)) 64=hw4 H i
  readable : Covers [⟨s.syms symbol,512⟩] (s.rd++s.wr)
  output : (polyRegion f).Disjoint ⟨s.syms symbol,512⟩
  scratch : (polyRegion w).Disjoint ⟨s.syms symbol,512⟩

end VG.Proof.MlKem.AArch64.Ntt16.Readonly
