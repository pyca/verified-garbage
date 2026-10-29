module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.MaskShift
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Exact public top-byte mask, including widths divisible by eight. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

def sampleMask (N : Nat) : Addr := BitVec.ofNat 64 (2^((N-1)%8+1)-1)

private theorem byteMask : ∀ n<8,(255#64 >>> (7-n))=BitVec.ofNat 64 (2^(n+1)-1) := by decide +kernel

theorem sampleMaskHead_ok {s : State} {B : Addr} {Z N : Nat}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B)
 (positive : 0<N) (_bound : N≤8192) (bits : word s.mem B (8*sBits)=BitVec.ofNat 64 N) :
 WP isa (.block [ldh .x3 sBits,.subImm .x .x3 .x3 1,movi .x4 7,
 .logic .and .x .x3 .x3 .x4,.sub .x .x3 .x4 .x3,movi .x12 255]) s fun t =>
 (t.gpr .x3=BitVec.ofNat 64 (7-(N-1)%8) ∧ t.gpr .x12=255#64 ∧ t.mem=s.mem) ∧ Keep [.x3,.x4,.x12] s t := by
 have low : BitVec.ofNat 64 (N-1) &&& 7#64=BitVec.ofNat 64 ((N-1)%8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and,BitVec.toNat_ofNat]
  change ((N-1)%2^64) &&& (2^3-1)=_
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega
 have sub : (7#64 : Addr)-BitVec.ofNat 64 ((N-1)%8)=BitVec.ofNat 64 (7-(N-1)%8) :=
  BitVec.ofNat_sub_ofNat_of_le 7 ((N-1)%8) (by omega) (by omega)
 refine WP.keep [.x3,.x4,.x12] ?_ rfl rfl rfl
 brun [movi_nat (show 7<2^16 by decide),movi_nat (show 255<2^16 by decide),base,hdr_enc (show sBits<32 by decide),scratch.ld (d:=8*sBits) (by unfold sBits;omega),bits,
  BitVec.ofNat_sub_ofNat_of_le (w:=64) N 1 (by decide) positive,low,sub]

theorem sampleMask_ok {s : State} {B : Addr} {Z N : Nat}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B)
 (positive : 0<N) (bound : N≤8192) (bits : word s.mem B (8*sBits)=BitVec.ofNat 64 N) :
 WP isa Generate.mask s fun t =>
 t.gpr .x12=sampleMask N ∧ word t.mem B (8*sMask)=sampleMask N ∧ t.mem=s.mem.writeW (off B (8*sMask)) (sampleMask N) ∧ Outside B (8*sMask) 8 s.mem t.mem ∧ Keep [.x3,.x4,.x12] s t := by
 unfold Generate.mask
 rw [WP.seq_iff]
 refine WP.mono (sampleMaskHead_ok scratch room base positive bound bits) ?_
 rintro a ⟨⟨countA,valueA,memA⟩,restA⟩
 rw [WP.seq_iff]
 have shifts : WP isa (.ite (.zero .x .x3) (.block [])
  (.loop (.block [.lsr .x .x12 .x12 1,.subImm .x .x3 .x3 1]) (.nonzero .x .x3))) a fun b =>
  b.gpr .x12=sampleMask N ∧ b.mem=a.mem ∧ Keep [.x3,.x12] a b := by
  by_cases zero : 7-(N-1)%8=0
  · have value : a.gpr .x12=sampleMask N := by rw [valueA,sampleMask,←byteMask ((N-1)%8) (by omega),zero];rfl
    refine ⟨_,a,.iteT ?_ (.block rfl),value,rfl,Keep.refl _ _⟩
    rw [eval_zero,countA,zero];decide
  · obtain ⟨tr,b,run,word,_,mem,rest⟩ := maskShift_ok a (by omega : 0<7-(N-1)%8) (by omega) countA
    refine ⟨_,b,.iteF ?_ run,?_,mem,rest⟩
    · rw [eval_zero,countA]
      have nz : BitVec.ofNat 64 (7-(N-1)%8)≠0#64 := by
       intro eq;have := congrArg BitVec.toNat eq;change (7-(N-1)%8)%2^64=0 at this;omega
      simp [nz]
    · rw [word,valueA,byteMask ((N-1)%8) (by omega)];rfl
 refine WP.mono shifts ?_
 rintro b ⟨maskB,memB,restB⟩
 have rest := restA.trans restB
 refine WP.mono (WP.keep [] (Q:=fun t =>t.mem=b.mem.writeW (off B (8*sMask)) (sampleMask N)) ?_ rfl rfl rfl) ?_
 · brun [(rest.gpr .x0 (by decide)).trans base,hdr_enc (show sMask<32 by decide),maskB,
    (scratch.congr rest.wr).st (d:=8*sMask) (by unfold sMask;omega)]
 · rintro t ⟨mem,restT⟩
   refine ⟨(restT.gpr .x12 (by simp)).trans maskB,?_,?_,?_,(rest.trans restT).mono (by simp)⟩
   · rw [mem,word_writeW_self]
   · rw [mem,memB,memA]
   · rw [mem,memB,memA];exact writeW_outside _ _ _ (by decide)

end VG.Proof.Ffdh.AArch64.Cached
