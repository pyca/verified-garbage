module
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp

import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.WordSemantic
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Word
public import VerifiedGarbage.Impl.MlKem.AArch64.Top
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Sums

/-! # Copy a bounded sequence of state words without touching the source -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem

def WordCopies (s : State) (src dst : Addr) (len n : Nat) (t : State) : Prop :=
 Keep [.x2,.x9] s t ∧ Frame [⟨dst,len⟩] s.mem t.mem ∧
 ∀j<8*n,t.mem (dst+BitVec.ofNat 64 j)=s.mem (src+BitVec.ofNat 64 j)

theorem squeezeWords_ok {s : State} {sc base : Reg} {srcOff dstOff N : Nat}
    (sc2 : sc≠.x2) (sc9 : sc≠.x9) (b2 : base≠.x2) (b9 : base≠.x9)
    (sa : srcOff%8=0) (sf : srcOff+8*N≤32768) (df : dstOff+8*N≤65536)
    (read : ∀i<N,InRegions (s.rd++s.wr) (s.gpr sc+BitVec.ofNat 64 (srcOff+8*i)) 8)
    (write : ∀i<N,InRegions s.wr (s.gpr base+BitVec.ofNat 64 (dstOff+8*i)) 8)
    (apart : (⟨s.gpr sc+BitVec.ofNat 64 srcOff,8*N⟩:Region).Disjoint
      ⟨s.gpr base+BitVec.ofNat 64 dstOff,8*N⟩) :
    WP isa (.block ((List.range N).flatMap fun i=>
      ([.ldr .x .x9 sc (srcOff+8*i)] : List Instr) ++ ptrTo .x2 base (dstOff+8*i) ++ ([.str .x .x9 .x2 0] : List Instr))) s
      (WordCopies s (s.gpr sc+BitVec.ofNat 64 srcOff) (s.gpr base+BitVec.ofNat 64 dstOff) (8*N) N) := by
  let src := s.gpr sc+BitVec.ofNat 64 srcOff
  let dst := s.gpr base+BitVec.ofNat 64 dstOff
  refine wp_range_flatMap (M:=isa) (N:=N) (WordCopies s src dst (8*N)) ?_ N (Nat.le_refl _) s
    ⟨Keep.refl _ _,Frame.refl _ _,by intro j hj; omega⟩
  intro i a hi ha
  have asrc := ha.1.get sc (by simp [sc2,sc9])
  have adst := ha.1.get base (by simp [b2,b9])
  refine WP.mono (squeezeWord_ok (src:=srcOff+8*i) (off:=dstOff+8*i) b2 b9 (by omega)
    ⟨by omega,by omega⟩
    (by rw [ha.1.rd,ha.1.wr,asrc]; exact read i hi)
    (by rw [ha.1.wr,adst]; exact write i hi)) fun t ht=>?_
  have mt : t.mem=a.mem.writeW (dst+BitVec.ofNat 64 (8*i)) (a.mem.readW (src+BitVec.ofNat 64 (8*i)) 64) := by
    have hh:=ht.2
    rw [adst,asrc,←ptr_add,←ptr_add] at hh
    exact hh
  have step : Frame [⟨dst+BitVec.ofNat 64 (8*i),8⟩] a.mem t.mem := by
    rw [mt]
    exact Frame.writeW (r:=⟨dst+BitVec.ofNat 64 (8*i),8⟩) (Frame.refl _ _) (by simp) _ (by simp [Region.Contains])
  refine ⟨(ha.1.trans ht.1).mono (by simp),?_,?_⟩
  · rw [mt]
    exact Frame.writeW (r:=⟨dst,8*N⟩) ha.2.1 (by simp) _ (Offset.contains_base dst (by omega) (by omega))
  · intro j hj
    by_cases old : j<8*i
    · rw [bytes_frame step (p:=dst) (len:=8*i) (fun r hr=>by
        rw [List.mem_singleton.mp hr]
        exact Offset.base_disjoint dst (by omega) (by omega)) (by omega) j old]
      exact ha.2.2 j old
    · have hk : j-8*i<8 := by omega
      have out := squeezeWord_bytes a.mem (src+BitVec.ofNat 64 (8*i)) (dst+BitVec.ofNat 64 (8*i))
      rw [←mt] at out
      have byte := congrArg (fun bs : List Byte=>bs[j-8*i]?.getD 0) out
      simp only [←List.getD_eq_getElem?_getD,bytesAt_getD _ _ hk,ptr_add] at byte
      have idx : 8*i+(j-8*i)=j := by omega
      rw [idx] at byte
      rw [byte]
      exact bytes_frame ha.2.1 (p:=src) (len:=8*N)
        (fun r hr=>by rw [List.mem_singleton.mp hr]; exact apart) (by omega) j (by omega)

end VG.Proof.MlKem.AArch64.FixedHash
