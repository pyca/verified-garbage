module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.SqueezeCode
public import VerifiedGarbage.Proof.MlKem.AArch64.HashProof

import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.SqueezeWords
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-! # One output piece is the consecutive bytes of the padded permutation -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem
open VG.Spec.Sha3 (bytesAt stateAt squeezeFrom)

theorem bytesAt_squeeze {m : Mem} {p : Addr} {rate pos len : Nat}
    (hr : 0<rate) (hr200 : rate≤200) (fit : pos+len≤rate) :
    bytesAt m (p+BitVec.ofNat 64 pos) len=squeezeFrom rate (stateAt m p) pos len := by
  apply List.ext_getElem
  · rw [bytesAt_length,Proof.Sha3.length_squeezeFrom hr hr200]
  · intro i hi hj
    have ilt : i<len := by simpa only [bytesAt_length] using hi
    rw [bytesAt_getElem,Proof.Sha3.squeezeFrom_getElem hr hr200 _ ilt,
      Nat.div_eq_of_lt (by omega : pos+i<rate),Nat.mod_eq_of_lt (by omega : pos+i<rate)]
    change m _=Proof.Sha3.byteOf (stateAt m p) (pos+i)
    rw [Proof.Sha3.byteOf_stateAt _ _ (by omega),ptr_add]

theorem squeezePiece_ok {s : State} {sc : Reg} {st wk rate pos : Nat} {p : Piece}
    (hs : HSetup sc st wk rate s) (ho : PieceOk sc st wk s true p)
    (sa : st%8=0) (pa : pos%8=0) (sf : st+rate≤32768)
    (df : p.off+p.len≤65536) (len : p.len%8=0) (fit : pos+p.len≤rate) :
    WP isa (.block (squeezePieceCode sc st pos p)) s fun t=>
      Keep [.x2,.x9] s t ∧ Frame [preg s p] s.mem t.mem ∧
      bytesAt t.mem (s.gpr p.base+BitVec.ofNat 64 p.off) p.len=
        squeezeFrom rate (stateAt s.mem (s.gpr sc+BitVec.ofNat 64 st)) pos p.len := by
  have hr := Proof.Sha3.rate_bounds hs.hrate
  have ne : ∀r∈preserved,r≠Reg.x2 ∧ r≠Reg.x9 := by decide
  have div : 8*(p.len/8)=p.len := by omega
  have sub : Region.Sub ⟨s.gpr sc+BitVec.ofNat 64 (st+pos),8*(p.len/8)⟩ (STr sc st s) := by
    rw [←ptr_add,div]
    exact Offset.sub_base _ (by omega)
  have rd : ∀i<p.len/8,InRegions (s.rd++s.wr) (s.gpr sc+BitVec.ofNat 64 (st+pos+8*i)) 8 := by
    intro i hi
    rw [Nat.add_assoc,←ptr_add]
    exact covers_rw' hs.cov _ _ ⟨STr sc st s,by simp [STr],Offset.contains_base _ (by omega) (by omega)⟩
  have wr : ∀i<p.len/8,InRegions s.wr (s.gpr p.base+BitVec.ofNat 64 (p.off+8*i)) 8 := by
    intro i hi
    rw [←ptr_add]
    exact ho.covW _ _ ⟨preg s p,by simp,Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (squeezeWords_ok (N:=p.len/8) (ne _ hs.hsc.1).1 (ne _ hs.hsc.1).2
    (ne _ ho.base.1).1 (ne _ ho.base.1).2 (by omega) (by omega) (by omega) rd wr
    (by rw [div]; exact ho.dst.symm.sub_left (by simpa only [div] using sub))) fun t ht=>?_
  refine ⟨ht.1,by simpa only [div] using ht.2.1,?_⟩
  rw [←bytesAt_squeeze (by omega : 0<rate) (by omega : rate≤200) fit]
  apply List.ext_getElem
  · simp only [bytesAt_length]
  · intro i hi hj
    have hh := ht.2.2 i (by simpa only [bytesAt_length,div] using hi)
    simpa only [bytesAt_getElem,ptr_add] using hh

end VG.Proof.MlKem.AArch64.FixedHash
