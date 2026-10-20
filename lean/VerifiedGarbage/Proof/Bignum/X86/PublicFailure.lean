module
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Impl.Bignum.X86.PublicFn
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Dsa.X86.FailureLoop
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Invalid public RSA keys return zero and clear the complete output -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem publicFailure_ok {s : State} {out : BitVec 32} {len : Nat}
    (hl : 0 < len) (h32 : len < 2 ^ 32) (fit : out.toNat + len ≤ 2 ^ 32)
    (P : readSrc s (.mem (PublicFn.argument 0)) = some out)
    (C : readSrc s (.mem (PublicFn.argument 1)) = some (BitVec.ofNat 32 len))
    (write : InRegions s.wr (out.setWidth 64) len) :
    WP isa PublicFn.failure s fun t =>
      Spec.Rsa.bytesAt t.mem (out.setWidth 64) len = List.replicate len 0 ∧
      t.gpr .eax = 0 ∧ Outside (out.setWidth 64) 0 len s.mem t.mem ∧
      Keeps [.esi, .ecx, .eax] s t := by
  unfold PublicFn.failure
  refine WP.seq (wp_movS P fun u a _ => ?_)
  refine wp_movS (by rw [argument_keep a.keeps (by decide) a.mem 1]; exact C) fun v b _ => ?_
  refine wp_movS rfl fun w c _ => WP.block_nil ?_
  have K : Keeps [.esi, .ecx, .eax] s w :=
    ((a.keeps.mono (by decide)).widen b.keeps).widen c.keeps
  have M : w.mem = s.mem := c.mem.trans (b.mem.trans a.mem)
  refine WP.mono (VG.Proof.Dsa.X86.failureLoop_ok hl h32 fit
    (by rw [c.other .esi (by decide), b.other .esi (by decide), a.gpr])
    (by rw [c.other .ecx (by decide), b.gpr]) c.gpr ?_) fun t ⟨V, Z, O, T⟩ => ?_
  · intro i hi
    rw [K.2.2]
    obtain ⟨r, hr, hc⟩ := write
    exact ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)⟩
  · exact ⟨V, Z, M ▸ O, K.trans (T.mono (by decide))⟩

end VG.Proof.Bignum.X86
