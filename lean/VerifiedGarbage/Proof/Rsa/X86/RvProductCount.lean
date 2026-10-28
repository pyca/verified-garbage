module

public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Impl.Rsa.X86.Recover
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Rsa.X86.KeyWs

/-! # The public iteration count for the exponent product -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys VG.Proof.Bignum.X86

theorem prodCount_ok {s : State} {base : Addr} {size eLen : Nat}
    (h : CallArgument s base size 7 (BitVec.ofNat 32 eLen)) :
    WP isa (.block prodCount) s fun t => t.gpr .esi = BitVec.ofNat 32 (8 * eLen) ∧
      t.mem = s.mem ∧ Keeps [.esi] s t := by
  unfold prodCount
  refine wp_movS h.readSrc fun u U _ => ?_
  refine wp_addS rfl fun v V _ => ?_
  refine wp_addS rfl fun w W _ => ?_
  refine wp_addS rfl fun t T _ => WP.block_nil ?_
  refine ⟨?_, T.mem.trans (W.mem.trans (V.mem.trans U.mem)),
    U.keeps.trans (V.keeps.trans (W.keeps.trans T.keeps))⟩
  rw [T.gpr, W.gpr, V.gpr, U.gpr]
  simp only [← BitVec.ofNat_add]
  congr 1
  omega

end VG.Proof.Rsa.X86.Recover
