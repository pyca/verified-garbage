import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackLoads
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFields
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack

def inputValue (signed : Bool) (b : Nat) (m : Mem) (p : Addr) (j : Nat) : BitVec 64 :=
  (if signed then encoded b (coeffAt m p j) else coeffAt m p j).setWidth 64

theorem inputWord (m : Mem) (p : Addr) (j : Nat) :
    vword (m.read (p+BitVec.ofNat 64 (16*(j/4))) 16) (j%4)=coeffAt m p j := by
  rw [VG.AArch64.vword_read16 _ _ (by omega),BitVec.add_assoc,←BitVec.ofNat_add,
    show 16*(j/4)+4*(j%4)=4*j by omega]
  rfl

theorem loadVec_ok (signed : Bool) (b c : Nat) (hc : c≤8) (hc4 : c%4=0) (s : State)
    (hconst : signed=true → Constants b s)
    (hin : ∀off,off+16≤4*c → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16) :
    WP isa (.block (loadVec signed c)) s fun t =>
      VChg [.v0,.v1,.v2,.v3,.v4] s t ∧ (signed=true → Constants b t) ∧
      ∀j<c,fieldValue t.v j=inputValue signed b s.mem (s.gpr .x0) j := by
  have hcode : loadVec signed c=(List.range (c/4)).flatMap (loadCode signed) := by
    unfold loadVec
    congr 1
  rw [hcode]
  refine WP.mono (loadCount_ok signed b (c/4) (by omega) s hconst ?_) fun t ⟨hk,hct,hv⟩ => ?_
  · intro j hj
    exact hin _ (by omega)
  · refine ⟨hk,hct,?_⟩
    intro j hj
    have hreg : regAt (j/4)=(if j<4 then VReg.v0 else .v1) := by
      unfold regAt
      split_ifs <;> first | rfl | omega
    have h := hv (j/4) (by omega) (j%4) (by omega)
    rw [hreg,inputWord] at h
    exact congrArg (BitVec.setWidth 64) h

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
