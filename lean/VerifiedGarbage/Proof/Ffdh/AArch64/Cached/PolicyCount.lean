module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
public import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

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
  omega
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
  have order := (Nat.le_log2 (show b≠0 by omega)).mpr (Nat.le_trans lower hn)
  omega
 refine WP.loop (M:=isa) I ?_ b s ?_
 · intro n t h
   obtain ⟨posN,leN,byteT,countT,memT,restT⟩ := h
   have lengths := byteLengths n (by omega) posN
   have countNext : bitLength b-bitLength n+1=bitLength b-bitLength (n/2) := by
    have := monotone n leN
    omega
   refine WP.mono (policyCountStep t (by omega) byteT countT) ?_
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
     refine ⟨?_,n/2,by omega,by omega,by omega,byteU,?_,memU.trans memT,(restT.trans restU).mono (by decide)⟩
     · rw [eval_nonzero,byteU]
       change some (BitVec.ofNat 64 (n/2) != 0#64)=some true
       rw [ofNat_nonzero (by omega),decide_eq_true (by omega : 0<n/2)]
     · rw [countU,countNext]
 · refine ⟨positive,Nat.le_refl _,byte,?_,rfl,Keep.refl _ _⟩
   simpa only [Nat.sub_self] using count

end VG.Proof.Ffdh.AArch64.Cached
