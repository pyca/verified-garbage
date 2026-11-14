module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyScan
public import VerifiedGarbage.Proof.Ffdh.KeyScalar
import Mathlib.Tactic.SplitIfs

/-! ### `Ffdh.AArch64.Cached.PolicySource`, which only this module used -/

section

/-! Select q's public bytes when present, otherwise p's public bytes. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

private theorem exec_cselc_x (s : State) (d n m : Reg) (cond : CondCode) :
 exec (.cselc .x d n m cond) s=some (s.write .x d (if cond.holds s then s.gpr n else s.gpr m)) := rfl
private theorem zeroFlag (s : State) (d : Reg) (a b : BitVec 64) (c : Bool) :
 (s.addWithCarry .x d a b c).zf=decide (a+b+BitVec.ofNat 64 c.toNat=0#64) := rfl

private theorem publicSub (k dl : Nat) (size : k<2^31) (shape : dl=2*k ∨ dl=3*k) :
 BitVec.ofNat 64 dl+ ~~~BitVec.ofNat 64 (2*k)+1#64=BitVec.ofNat 64 (dl-2*k) := by
 rw [BitVec.add_assoc,←BitVec.neg_eq_not_add,←BitVec.sub_eq_add_neg]
 exact BitVec.ofNat_sub_ofNat_of_le dl (2*k) (by omega_using [size]) (by omega_using [shape])

theorem policySource_ok {s : State} {B dom : Addr} {Z k dl : Nat}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B)
 (positive : 0<k) (size : k<2^31) (shape : dl=2*k ∨ dl=3*k)
 (pointer : word s.mem B (8*sDom)=dom) (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k)
 (domainLength : word s.mem B (8*sDL)=BitVec.ofNat 64 dl) :
 WP isa (.block (Policy.boundSource++[movi .x10 0])) s fun t =>
 (t.gpr .x1=(if dl=2*k then dom else off dom (2*k)) ∧
 t.gpr .x2=BitVec.ofNat 64 k ∧ t.gpr .x10=0#64 ∧ t.mem=s.mem) ∧ Keep [.x1,.x2,.x3,.x4,.x10] s t := by
 have shift : BitVec.ofNat 64 k <<< 1=BitVec.ofNat 64 (2*k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq]
  omega_using []
 have choose : (if decide (BitVec.ofNat 64 (dl-2*k)=0#64) then dom else dom+BitVec.ofNat 64 (2*k))=
  (if dl=2*k then dom else off dom (2*k)) := by
  rcases shape with eq | eq
  · subst dl
    simp
  · subst dl
    have ne : BitVec.ofNat 64 (3*k-2*k)≠0#64 := by
     intro zero
     have := congrArg BitVec.toNat zero
     simp only [BitVec.toNat_ofNat] at this
     omega_using [positive, size, this]
    simp only [ne,decide_false,ite_false,show ¬3*k=2*k by omega_using [positive]]
    rfl
 refine WP.keep [.x1,.x2,.x3,.x4,.x10] ?_ rfl rfl rfl
 unfold Policy.boundSource
 brun [base,hdr_enc (show sDom<32 by decide),hdr_enc (show sLen<32 by decide),hdr_enc (show sDL<32 by decide),
  scratch.ld (d:=8*sDom) (by unfold sDom;omega_using [room]),scratch.ld (d:=8*sLen) (by unfold sLen;omega_using [room]),
  scratch.ld (d:=8*sDL) (by unfold sDL;omega_using [room]),pointer,length,domainLength,shift,
  exec_cselc_x,CondCode.holds,RegUpd.zf_write,zeroFlag,Bool.toNat_true,publicSub k dl size shape,choose]

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.PolicyCount`, which only this module used -/

section

/-! Count the significant bits of the public first nonzero bound byte. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero)
open VG.Spec.RsaKeyGen (bitLength)

private theorem byteLengths : ∀ n<256, 0<n →
 0<bitLength n ∧ bitLength n≤8 ∧ bitLength (n/2)+1=bitLength n := by decide +kernel

theorem policyCountStep (s : State) {n j : Nat} (size : n<256)
 (byte : s.gpr .x3=BitVec.ofNat 64 n) (count : s.gpr .x10=BitVec.ofNat 64 j) :
 WP isa (.block Policy.countStep) s fun t =>
 (t.gpr .x3=BitVec.ofNat 64 (n/2) ∧ t.gpr .x10=BitVec.ofNat 64 (j+1) ∧ t.mem=s.mem) ∧
 Keep [.x3,.x10] s t := by
 have shift : BitVec.ofNat 64 n >>> 1=BitVec.ofNat 64 (n/2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  omega_using [size]
 refine WP.keep [.x3,.x10] ?_ rfl rfl rfl
 unfold Policy.countStep
 brun [byte,count,shift]
 exact (BitVec.ofNat_add _ _).symm

theorem policyCount_ok (s : State) {b : Nat} (size : b<256) (positive : 0<b)
 (byte : s.gpr .x3=BitVec.ofNat 64 b) (count : s.gpr .x10=0#64) :
 WP isa (.loop (.block Policy.countStep) (.nonzero .x .x3)) s fun t =>
 t.gpr .x3=0#64 ∧ t.gpr .x10=BitVec.ofNat 64 (bitLength b) ∧ t.mem=s.mem ∧ Keep [.x3,.x10] s t := by
 let I := fun n t => 0<n ∧ n≤b ∧ t.gpr .x3=BitVec.ofNat 64 n ∧
  t.gpr .x10=BitVec.ofNat 64 (bitLength b-bitLength n) ∧ t.mem=s.mem ∧ Keep [.x3,.x10] s t
 have monotone (n : Nat) (hn : n≤b) : bitLength n≤bitLength b := by
  unfold bitLength
  split_ifs <;> try omega
  have lower := Nat.log2_self_le (show n≠0 by assumption)
  have order := (Nat.le_log2 (show b≠0 by omega_using [positive])).mpr (Nat.le_trans lower hn)
  omega_using [order]
 refine WP.loop (M:=isa) I ?_ b s ?_
 · intro n t h
   obtain ⟨posN,leN,byteT,countT,memT,restT⟩ := h
   have lengths := byteLengths n (by omega_using [size, leN]) posN
   have countNext : bitLength b-bitLength n+1=bitLength b-bitLength (n/2) := by
    have := monotone n leN
    omega_using [lengths, this]
   refine WP.mono (policyCountStep t (by omega_using [size, leN]) byteT countT) ?_
   rintro u ⟨⟨byteU,countU,memU⟩,restU⟩
   by_cases last : n=1
   · left
     refine ⟨?_,?_,?_,memU.trans memT,(restT.trans restU).mono (by decide)⟩
     · rw [eval_nonzero,byteU,last]
       decide
     · rw [byteU,last]
     · rw [countU,countNext,last]
       simp only [show 1/2=0 from rfl,bitLength,ite_true,Nat.sub_zero]
   · right
     refine ⟨?_,n/2,by omega_using [posN],by omega_using [posN, last],by omega_using [leN],byteU,?_,memU.trans memT,(restT.trans restU).mono (by decide)⟩
     · rw [eval_nonzero,byteU]
       change some (BitVec.ofNat 64 (n/2) != 0#64)=some true
       rw [ofNat_nonzero (by omega_using [size, leN]),decide_eq_true (by omega_using [posN, last] : 0<n/2)]
     · rw [countU,countNext]
 · refine ⟨positive,Nat.le_refl _,byte,?_,rfl,Keep.refl _ _⟩
   simpa only [Nat.sub_self] using count

end VG.Proof.Ffdh.AArch64.Cached

end

end


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
  omega_using [this]
 have byteSize := (bs.getD L 0).isLt
 unfold Policy.boundBits
 rw [WP.seq_iff]
 refine WP.mono (policySource_ok scratch room base positive size shape pointer length domainLength) ?_
 rintro a ⟨⟨ptrA,lenA,zeroA,memA⟩,restA⟩
 rw [WP.seq_iff]
 refine WP.mono (policyScan_ok a (source.of_mem memA restA) (by omega_using [size, bsLength]) inside zeros nonzero ptrA (bsLength ▸ lenA)) ?_
 rintro b ⟨_,lenB,byteB,memB,restB⟩
 rw [WP.seq_iff]
 have shift : BitVec.ofNat 64 (bs.length-(L+1)) <<< 3=BitVec.ofNat 64 (8*(bs.length-L-1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq]
  omega_using []
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
    omega_using []
   refine WP.mono (WP.keep [.x10] (Q:=fun t =>
    t.mem=d.mem.writeW (off B (8*sBits)) (BitVec.ofNat 64 (8*(bs.length-L-1)+bitLength (bs.getD L 0).toNat)))
    ?_ rfl rfl rfl) ?_
   · brun [(rest.gpr .x0 (by decide)).trans base,hdr_enc (show sBits<32 by decide),value,
      (scratch.congr rest.wr).st (d:=8*sBits) (by unfold sBits;omega_using [room])]
   · rintro t ⟨memT,restT⟩
     exact ⟨by rw [memT,mem],(rest.trans restT).mono (by decide)⟩

end VG.Proof.Ffdh.AArch64.Cached
