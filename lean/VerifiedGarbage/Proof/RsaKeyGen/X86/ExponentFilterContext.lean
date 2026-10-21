module

import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentFilter
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRanges
public import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.WorkspaceDisjoint
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.Framework.Offset

/-! # Public geometry and preserved candidate data across exponent classification -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentFilter
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Bignum.X86.PublicContext VG.Proof.MillerRabin.X86

structure Input (base : Addr) (size w candidate exponent : Nat) (s : State) : Prop where
  scratch : Scr s base size
  width : 4 ≤ w
  widthBound : w ≤ 64
  space : slot w 5 + 8 * w ≤ size
  original : val32 s.mem base (slot w 0) (2 * w) = candidate
  saved : val32 s.mem base (slot w 5) (2 * w) = candidate - 1
  large : 1 < candidate
  odd : candidate % 2 = 1
  exponentEq : Mod64.exponentValue s.mem base 128 = exponent
  fit : 40 ≤ (s.gpr .esp).toNat
  separate : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + size + 40 ≤ (s.gpr .esp).toNat

theorem Input.header {base : Addr} {size w candidate exponent : Nat} {s : State}
    (S : Input base size w candidate exponent s) : 136 ≤ size := by
  have := S.space
  simp only [slot, VG.Impl.Bignum.X86.PublicContext.stride, VG.Impl.Bignum.hdrBytes] at this
  omega

theorem Input.keepReadonly {base : Addr} {size w candidate exponent : Nat} {s t : State}
    (S : Input base size w candidate exponent s) (M : t.mem = s.mem) (K : Keeps [.eax] s t) :
    Input base size w candidate exponent t := by
  refine ⟨S.scratch.of_keeps K (by decide), S.width, S.widthBound, S.space, ?_, ?_, S.large, S.odd, ?_, ?_, ?_⟩
  · rw [M]; exact S.original
  · rw [M]; exact S.saved
  · rw [M]; exact S.exponentEq
  · rw [K.1 .esp (by decide)]; exact S.fit
  · rw [K.1 .esp (by decide)]; exact S.separate

structure Output (base : Addr) (size w candidate exponent : Nat) (s t : State) : Prop where
  result : t.gpr .eax = BitVec.ofNat 32 (decide (Nat.gcd (candidate - 1) exponent = 1)).toNat
  original : val32 t.mem base (slot w 0) (2 * w) = candidate
  frame : Frame [⟨base, size⟩, below (s.gpr .esp) 20] s.mem t.mem
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t
  workspace : WorkspaceFrame ⟨base, size, w⟩ (ranges w) s.mem t.mem

theorem Output.prepend {base : Addr} {size w candidate exponent : Nat} {s a t : State}
    (H : Output base size w candidate exponent a t) (M : a.mem = s.mem) (K : Keeps [.eax] s a) :
    Output base size w candidate exponent s t := by
  refine ⟨H.result, H.original, ?_, (K.mono (by decide)).trans H.keeps, ?_⟩
  · have F := H.frame
    rw [K.1 .esp (by decide), M] at F
    exact F
  · rw [← M]; exact H.workspace

theorem Input.readonlyOutput {base : Addr} {size w candidate exponent : Nat} {s t : State}
    (S : Input base size w candidate exponent s)
    (result : t.gpr .eax = BitVec.ofNat 32 (decide (Nat.gcd (candidate - 1) exponent = 1)).toNat)
    (M : t.mem = s.mem) (K : Keeps [.eax] s t) : Output base size w candidate exponent s t := by
  refine ⟨result, ?_, ?_, K.mono (by decide), ?_⟩
  · rw [M]; exact S.original
  · rw [M]; exact Frame.refl _ _
  · rw [M]; exact WorkspaceFrame.refl _ _ _

theorem Input.stackFrameValue {base : Addr} {size w candidate exponent : Nat} {s t : State}
    (S : Input base size w candidate exponent s) (F : Frame [below (s.gpr .esp) 20] s.mem t.mem) :
    val32 t.mem base (slot w 0) (2 * w) = candidate := by
  rw [← S.original]
  apply val32_congr
  intro i index
  have far : (⟨base, size⟩ : Region).Disjoint (below (s.gpr .esp) 20) :=
    FilterStack.allocated_apart (by have := S.fit; omega) S.scratch.nowrap
      (by have := S.separate; rcases this with h | h; exact Or.inl h; exact Or.inr (by omega))
  have sourceFit : slot w 0 + 8 * w ≤ size := by
    have := S.space
    simp only [slot, VG.Impl.Bignum.X86.PublicContext.stride, VG.Impl.Bignum.hdrBytes] at this ⊢
    omega
  exact congrArg BitVec.toNat (F.readW (r := ⟨base, size⟩)
    (Offset.contains_base _ (by omega) (by have := S.scratch.nowrap; omega))
    (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact far) (by decide))

theorem Input.stackWorkspaceFrame {base : Addr} {size w candidate exponent : Nat} {s t : State}
    (S : Input base size w candidate exponent s) (F : Frame [below (s.gpr .esp) 20] s.mem t.mem) :
    WorkspaceFrame ⟨base, size, w⟩ (ranges w) s.mem t.mem := by
  have far : (⟨base, size⟩ : Region).Disjoint (below (s.gpr .esp) 20) :=
    FilterStack.allocated_apart (by have := S.fit; omega) S.scratch.nowrap
      (by have := S.separate; rcases this with h | h; exact Or.inl h; exact Or.inr (by omega))
  have W : WorkspaceFrame ⟨base, size, w⟩ [] s.mem t.mem :=
    workspace_of_frame F S.scratch.nowrap (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact far)
  exact W.mono (by intro r mem; nomatch mem)

theorem Output.metadata32 {base : Addr} {size w candidate exponent : Nat} {s t : State}
    (O : Output base size w candidate exponent s t) {d : Nat} (fit : d + 4 ≤ size)
    (safe : protectedHeader d 4) : t.mem.readW (off base d) 32 = s.mem.readW (off base d) 32 :=
  O.workspace.read32 fit (fun _ mem => ranges_apart safe mem)

theorem Output.savedValue {base : Addr} {size w candidate exponent : Nat} {s t : State}
    (O : Output base size w candidate exponent s t) (width : 4 ≤ w) (space : slot w 5 + 8 * w ≤ size) :
    val32 t.mem base (slot w 5) (2 * w) = val32 s.mem base (slot w 5) (2 * w) :=
  O.workspace.val32 (by change slot w 5 + 4 * (2 * w) ≤ size; omega) (fun _ mem => Or.inr (saved_apart width mem))

end VG.Proof.RsaKeyGen.X86.ExponentFilter
