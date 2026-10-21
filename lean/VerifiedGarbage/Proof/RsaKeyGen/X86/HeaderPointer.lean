module

import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderStore
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Header
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Initialize one public prepared-array pointer -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Header
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.Header

theorem pointer_ok {s : State} {base : Addr} {size w i : Nat}
    (scratch : Scr s base size) (fit : 64 + 8 * i + 8 ≤ size) (zero : s.gpr .edx = 0#32) :
    WP isa (.block (pointer w i)) s fun t =>
      t.mem = s.mem.writeW (off base (64 + 8 * i))
        (0#32 ++ (s.gpr .edi + BitVec.ofNat 32 (slot w i))) ∧
      Outside base (64 + 8 * i) 8 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold pointer
  refine wp_movS rfl fun a A _ => wp_addS rfl fun b B _ => ?_
  have K : Keeps [.eax] s b := A.keeps.trans B.keeps
  have addr : 68 + 8 * i = 64 + 8 * i + 4 := by omega
  rw [addr]
  refine WP.mono (storePair_ok (scratch.of_keeps K (by decide)) fit) fun t ⟨M, O, Kt⟩ => ?_
  refine ⟨?_, ?_, K.widen Kt⟩
  · rw [M, B.mem, A.mem, K.1 .edx (by decide), zero, B.gpr, A.gpr]
  · rw [B.mem, A.mem] at O
    exact O

end VG.Proof.RsaKeyGen.X86.Header
