module

public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedFn
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Derive the packed-key width from the public output length -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem precomputedWidth_ok {s : State} {len : Nat} (bound : len ≤ 1024)
    (count : readSrc s (.mem (PublicFn.argument 1)) = some (BitVec.ofNat 32 len)) :
    WP isa (.block PrecomputedFn.widthArgs) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.modulusWords len) ∧
      t.mem = s.mem ∧ Keeps [.eax] s t := by
  unfold PrecomputedFn.widthArgs
  refine wp_movS count fun u A _ => ?_
  refine wp_addS rfl fun v B _ => ?_
  refine wp_shr (by decide) fun t C _ => WP.block_nil ?_
  refine ⟨?_, C.mem.trans (B.mem.trans A.mem), (A.keeps.trans B.keeps).trans C.keeps⟩
  rw [C.gpr, B.gpr, A.gpr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Spec.Rsa.modulusWords, show (7 : BitVec 32).toNat = 7 from rfl]
  omega

end VG.Proof.Bignum.X86
