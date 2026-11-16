module

public import VerifiedGarbage.Proof.Sha3.Spec
public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (wp_vop VChg)
open VG.Proof.Sha3 (C)

def Pairs (s : State) (A B : Spec.Sha3.State) : Prop :=
  ∀ i < 25, s.v (vreg i) = ofVDwords A[i]! B[i]!

theorem vreg_inj : ∀ i < 32, ∀ j < 32, vreg i = vreg j ↔ i = j := by decide

theorem pair_xor (a b c d : BitVec 64) :
    ofVDwords a b ^^^ ofVDwords c d = ofVDwords (a ^^^ c) (b ^^^ d) := by
  apply vec64_ext <;> simp only [vdword,BitVec.extractLsb'_xor]
  · change vdword (ofVDwords a b) 0 ^^^ vdword (ofVDwords c d) 0 = vdword (ofVDwords (a ^^^ c) (b ^^^ d)) 0
    rw [vdword_ofVDwords_0,vdword_ofVDwords_0,vdword_ofVDwords_0]
  · change vdword (ofVDwords a b) 1 ^^^ vdword (ofVDwords c d) 1 = vdword (ofVDwords (a ^^^ c) (b ^^^ d)) 1
    rw [vdword_ofVDwords_1,vdword_ofVDwords_1,vdword_ofVDwords_1]

/-- Internal kernels may use every vector register; their boundaries save the ABI-preserved lanes. -/
def allV : List VReg := (List.range 32).map vreg

theorem allV_mem : ∀ r : VReg, r ∈ allV := by intro r; cases r <;> decide

end VG.Proof.Sha3.AArch64.Neon
