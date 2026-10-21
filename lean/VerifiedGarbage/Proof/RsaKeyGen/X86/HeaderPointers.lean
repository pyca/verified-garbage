module

import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderPointer
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Header
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Initialize all prepared pointers while retaining the public workspace base -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Header
open VG VG.X86 VG.Impl.Bignum.X86.PublicContext VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Header

def pointerMemory (base : Addr) (p : BitVec 32) (w : Nat) (m : Mem) (i : Nat) : Mem :=
  m.writeW (off base (64 + 8 * i)) (0#32 ++ (p + BitVec.ofNat 32 (slot w i)))

theorem pointers_ok (indices : List Nat) {s : State} {base : Addr} {size w : Nat}
    (scratch : Scr s base size) (fit : ∀ i ∈ indices, 64 + 8 * i + 8 ≤ size)
    (zero : s.gpr .edx = 0#32) :
    WP isa (.block (indices.flatMap (pointer w))) s fun t =>
      t.mem = indices.foldl (pointerMemory base (s.gpr .edi) w) s.mem ∧ Keeps [.eax] s t := by
  induction indices generalizing s with
  | nil => exact WP.block_nil ⟨rfl, Keeps.refl _ _⟩
  | cons i indices ih =>
    rw [List.flatMap_cons]
    refine WP.block_append (WP.mono (pointer_ok scratch (fit i (by simp)) zero) fun a ⟨M, _, K⟩ => ?_)
    refine WP.mono (ih (scratch.of_keeps K (by decide))
      (fun j mem => fit j (List.mem_cons_of_mem _ mem)) ((K.1 .edx (by decide)).trans zero))
      fun t ⟨Mt, Kt⟩ => ?_
    refine ⟨?_, K.trans Kt⟩
    rw [Mt, K.1 .edi (by decide), M]
    rfl

end VG.Proof.RsaKeyGen.X86.Header
