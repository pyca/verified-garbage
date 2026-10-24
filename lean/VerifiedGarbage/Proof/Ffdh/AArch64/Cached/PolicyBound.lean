module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicySource
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyScan
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyCount
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! The uncapped public scalar width is the significant bit length of the bound. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.RsaKeyGen (bitLength)

theorem policyBound_ok {s : State} {B dom : Addr} {Z k dl L : Nat} {bs : List Byte}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B)
 (positive : 0<k) (size : k<2^31) (shape : dl=2*k ∨ dl=3*k)
 (pointer : word s.mem B (8*sDom)=dom) (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k)
 (domainLength : word s.mem B (8*sDL)=BitVec.ofNat 64 dl)
 (source : Source (if dl=2*k then dom else off dom (2*k)) bs s) (bsLength : bs.length=k)
 (inside : L<bs.length) (zeros : ∀ i<L,bs.getD i 0=0#8) (nonzero : bs.getD L 0≠0#8) :
 WP isa Policy.boundBits s fun t =>
 t.mem=s.mem.writeW (off B (8*sBits))
  (BitVec.ofNat 64 (8*(bs.length-L-1)+bitLength (bs.getD L 0).toNat)) ∧
 Keep [.x1,.x2,.x3,.x4,.x10] s t := by
 have bytePositive : 0<(bs.getD L 0).toNat := by
  have : (bs.getD L 0).toNat≠0 := fun eq => nonzero (BitVec.eq_of_toNat_eq eq)
  omega
 have byteSize := (bs.getD L 0).isLt
 unfold Policy.boundBits
 rw [WP.seq_iff]
 refine WP.mono (policySource_ok scratch room base positive size shape pointer length domainLength) ?_
 rintro a ⟨⟨ptrA,lenA,zeroA,memA⟩,restA⟩
 rw [WP.seq_iff]
 refine WP.mono (policyScan_ok a (source.of_mem memA restA) (by omega) inside zeros nonzero ptrA (bsLength ▸ lenA)) ?_
 rintro b ⟨_,lenB,byteB,memB,restB⟩
 rw [WP.seq_iff]
 have shift : BitVec.ofNat 64 (bs.length-(L+1)) <<< 3=BitVec.ofNat 64 (8*(bs.length-L-1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq]
  omega
 refine WP.mono (WP.keep [.x2] (Q:=fun c =>
  c.gpr .x2=BitVec.ofNat 64 (8*(bs.length-L-1)) ∧ c.mem=b.mem) ?_ rfl rfl rfl) ?_
 · brun [lenB,shift]
 · rintro c ⟨⟨lenC,memC⟩,restC⟩
   rw [WP.seq_iff]
   have zeroC : c.gpr .x10=0#64 :=
    (restC.gpr .x10 (by decide)).trans ((restB.gpr .x10 (by decide)).trans zeroA)
   refine WP.mono (policyCount_ok c byteSize bytePositive
    ((restC.gpr .x3 (by decide)).trans byteB) zeroC) ?_
   rintro d ⟨_,countD,memD,restD⟩
   have rest := ((restA.trans restB).trans restC).trans restD
   have mem : d.mem=s.mem := ((memD.trans memC).trans memB).trans memA
   have value : d.gpr .x10+d.gpr .x2=
    BitVec.ofNat 64 (8*(bs.length-L-1)+bitLength (bs.getD L 0).toNat) := by
    rw [countD,restD.gpr .x2 (by decide),lenC,←BitVec.ofNat_add]
    congr 1
    omega
   refine WP.mono (WP.keep [.x10] (Q:=fun t =>
    t.mem=d.mem.writeW (off B (8*sBits)) (BitVec.ofNat 64 (8*(bs.length-L-1)+bitLength (bs.getD L 0).toNat)))
    ?_ rfl rfl rfl) ?_
   · brun [(rest.gpr .x0 (by decide)).trans base,hdr_enc (show sBits<32 by decide),value,
      (scratch.congr rest.wr).st (d:=8*sBits) (by unfold sBits;omega)]
   · rintro t ⟨memT,restT⟩
     exact ⟨by rw [memT,mem],(rest.trans restT).mono (by decide)⟩

end VG.Proof.Ffdh.AArch64.Cached
