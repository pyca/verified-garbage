module

public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming

public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
import VerifiedGarbage.Proof.Bignum.X86.PublicSetup
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Mont.X86.ExponentTiming
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
import VerifiedGarbage.Proof.Mont.X86.PublicPowerTiming
import VerifiedGarbage.Proof.Mont.X86.CombDigitMath
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
meta import VerifiedGarbage.Impl.Bignum.X86.PublicContext
meta import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
meta import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! Public RSA setup shares the modulus-dependent seed and fixed-count square timing proofs. -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Bignum.X86.PublicContext
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86

theorem start_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (start n)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  have check : VG.Taint.check taint (workspaceTaint false) (start n)
      (.seq (workspaceTaint false) (.block []) (oneHint false))=some (zerosTaint false) :=
    exponent_check_seq taint (setupInverse_taint false (slot n 0) inverseOffset) (by rfl)
      (one_check false n (slot n 4))
  exact checkedProgramChange check rfl

theorem setup_relCT (base : Addr) (bytes n m : Nat) (hn : 0<n)
    (size : size n≤bytes) (hm : 1<m) (odd : m%2=1) :
    RelCT isa (fun s t => Scr s base bytes ∧ Scr t base bytes ∧
      wordsVal s.mem base (slot n 0) n=m ∧ wordsVal t.mem base (slot n 0) n=m)
      (setup n) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold setup
  refine VG.RelCT.seq (R := fun s t => Context n m base bytes s ∧ Context n m base bytes t) ?_ ?_
  · intro s t tr ur sf tf ⟨S,T,Vs,Vt⟩ Es Et
    have DI : s.gpr .edi=t.gpr .edi := BitVec.eq_of_toNat_eq (S.edi_toNat.trans T.edi_toNat.symm)
    have A := agree_regs (rs := [.edi]) (fun r hr => by obtain rfl := List.mem_singleton.mp hr;exact DI)
    exact ⟨(start_relCT n _ _ _ _ _ _ A Es Et).1,
      (wp_result (start_ok S hn size Vs hm odd) Es).1,
      (wp_result (start_ok T hn size Vt hm odd) Et).1⟩
  refine VG.RelCT.seq ?_ (repeatSquaresAt_relCT _ _ _ _ _)
  apply (publicPower_relCT (modulus n) (slot n 2) (slot n 5) base bytes ?_).mono
  · intro s t ⟨S,T⟩
    refine ⟨S.scr,T.scr,?_⟩
    change w32 s.mem base (slot n 0+4*(2*n-1))=w32 t.mem base (slot n 0+4*(2*n-1))
    rw [←VG.Proof.Mont.X86.Comb.val32_word (by omega : 2*n-1<2*n),
      ←VG.Proof.Mont.X86.Comb.val32_word (by omega : 2*n-1<2*n),
      ←wordsVal_eq_val32,←wordsVal_eq_val32]
    rw [show wordsVal s.mem base (slot n 0) n=m from S.mod.val,
      show wordsVal t.mem base (slot n 0) n=m from T.mod.val]
  · exact fun _ _ h => h
  · have b0 := slot_bound (n := n) (i := 0) (by decide)
    change slot n 0+4*(2*n-1)+4≤bytes
    unfold stride at b0
    omega

end VG.Proof.Bignum.X86.PublicContext
