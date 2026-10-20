module
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchContext
import VerifiedGarbage.Proof.Dsa.X86.KeyCopy
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameMemory
public import Aesop.BuiltinRules
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Pack
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryBuffers
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate
import VerifiedGarbage.Proof.Dsa.X86.Generation.PackArguments
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchWrites

/-! # Copy one domain component into a disjoint persistent packing buffer -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Dsa.X86.Generation

theorem packPart_ok {P : SearchContextPlan} {W : Nat → BitVec 32} {s : State} {src dst len : Nat}
    (R : SearchContext P W s) (positive : 0 < len) (small : len < 2 ^ 32)
    (sourceRoom : src + len ≤ usedBytes P.geometry.pLen) (destRoom : dst + len ≤ usedBytes P.geometry.pLen)
    (mutable : VG.Impl.Dsa.Generation.Layout.hash ≤ dst)
    (apart : (P.geometry.part src len).Disjoint (P.geometry.part dst len)) :
    WP isa (packPart src dst len) s fun t => SearchContext P W t ∧
      Spec.Rsa.bytesAt t.mem (off P.geometry.base dst) len = Spec.Rsa.bytesAt s.mem (off P.geometry.base src) len ∧
      Frame [P.geometry.part dst len] s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := by
  have ss : src < usedBytes P.geometry.pLen := by omega
  have ds : dst < usedBytes P.geometry.pLen := by omega
  have parent : s.mem.readW (off P.geometry.frameBase 20) 32 = P.geometry.parent :=
    (R.representation 5 (by decide)).trans ((R.fixed 5 (by decide) (by decide)).trans P.parent)
  unfold packPart
  refine WP.seq (WP.mono (packArgs_ok R.arena.frame parent src dst len) fun a ⟨si, dx, cx, bx, mem, Ka⟩ => ?_)
  have Ra := R.congr mem Ka (by decide)
  refine WP.mono (keyCopy_ok positive small (P.geometry.pointer_fit ss sourceRoom) (P.geometry.pointer_fit ds destRoom)
    (by rw [P.geometry.pointer_addr ss, P.geometry.pointer_addr ds]; exact apart) si dx cx bx
    (by intro i hi; exact Ra.arena.readPointer ss sourceRoom i 1 (by omega))
    (by intro i hi; exact Ra.arena.writePointer ds destRoom i 1 (by omega))) fun t I => ?_
  have bytes := copied_unmasked I
  rw [P.geometry.pointer_addr ss, P.geometry.pointer_addr ds, mem] at bytes
  have O := copyOutside_frame I.mem
  rw [P.geometry.pointer_addr ds, mem] at O
  have Kt : Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := (Ka.mono (by decide)).trans (I.keeps.mono (by decide))
  have rep := R.representation.keep O (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact P.geometry.frame_part destRoom)
  exact ⟨R.frame rep (fun _ _ _ => rfl) (O.sub (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_cons_self, P.geometry.mutablePart mutable destRoom⟩)) Kt (by decide), bytes, O, Kt⟩
end VG.Proof.Dsa.X86.Generation
