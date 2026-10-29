module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Header
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderStore
import VerifiedGarbage.Proof.Framework.Block
/-! # Complete initialization of the public prepared header -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/HeaderPointer.lean`, which only this module imported.
section

/-! # Initialize one public prepared-array pointer -/

section
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
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/HeaderPointers.lean`, which only this module imported.
section

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
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Header
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.Header

def headerMemory (base : Addr) (p : BitVec 32) (w : Nat) (m : Mem) : Mem :=
  (List.range 8).foldl (pointerMemory base p w)
    ((m.writeW (off base 48) (0#32 ++ BitVec.ofNat 32 w)).writeW
      (off base 224) (0#32 ++ BitVec.ofNat 32 (stride w)))

theorem code_ok {s : State} {base : Addr} {size w : Nat}
    (scratch : Scr s base size) (fit : 256 ≤ size) :
    WP isa (.block (code w)) s fun t =>
      t.mem = headerMemory base (s.gpr .edi) w s.mem ∧ Keeps [.eax, .edx] s t := by
  unfold code
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movS rfl fun a A _ => ?_
  refine WP.block_append (WP.mono (literal_ok (scratch.of_keeps A.keeps (by decide)) (by omega) A.gpr)
    fun b ⟨Mb, _, Kb⟩ => ?_)
  have K : Keeps [.eax, .edx] s b := (A.keeps.mono (by decide)).widen Kb
  have zeroB : b.gpr .edx = 0#32 := (Kb.1 .edx (by decide)).trans A.gpr
  refine WP.block_append (WP.mono (literal_ok (scratch.of_keeps K (by decide)) (by omega) zeroB)
    fun c ⟨Mc, _, Kc⟩ => ?_)
  have K' : Keeps [.eax, .edx] s c := K.widen Kc
  have zeroC : c.gpr .edx = 0#32 := (Kc.1 .edx (by decide)).trans zeroB
  refine WP.mono (pointers_ok (List.range 8) (scratch.of_keeps K' (by decide))
    (fun i mem => by have := List.mem_range.mp mem; omega) zeroC) fun t ⟨Mt, Kt⟩ => ?_
  refine ⟨?_, K'.widen Kt⟩
  rw [Mt, K'.1 .edi (by decide), Mc, Mb, A.mem]
  rfl

end VG.Proof.RsaKeyGen.X86.Header
