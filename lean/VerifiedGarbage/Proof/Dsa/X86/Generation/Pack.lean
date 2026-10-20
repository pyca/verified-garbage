module
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
public import Aesop.BuiltinRules
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Pack
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchContext
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryBuffers
import VerifiedGarbage.Proof.Dsa.X86.Generation.PackPart

/-! # Pack the accepted domain as p, q, g without disturbing the persistent search frame -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Dsa.X86.Generation

theorem pack_ok {P : SearchContextPlan} {W : Nat → BitVec 32} {s : State} (R : SearchContext P W s) :
    WP isa (pack P.geometry.pLen P.geometry.qLen) s fun t => SearchContext P W t ∧
      Spec.Rsa.bytesAt t.mem (off P.geometry.base packed) (2 * P.geometry.pLen + P.geometry.qLen) =
        Spec.Rsa.bytesAt s.mem (off P.geometry.base p) P.geometry.pLen ++
        Spec.Rsa.bytesAt s.mem (off P.geometry.base q) P.geometry.qLen ++
        Spec.Rsa.bytesAt s.mem (off P.geometry.base g) P.geometry.pLen ∧
      Frame [P.geometry.part packed (2 * P.geometry.pLen + P.geometry.qLen)] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := by
  have pw := P.geometry.width
  have qw := P.geometry.qWidth
  have pr : p + P.geometry.pLen ≤ usedBytes P.geometry.pLen := by unfold p usedBytes domainCheck; omega
  have qr : q + P.geometry.qLen ≤ usedBytes P.geometry.pLen := by unfold q usedBytes domainCheck; omega
  have gr : g + P.geometry.pLen ≤ usedBytes P.geometry.pLen := by unfold g usedBytes domainCheck; omega
  have pkr : packed + (2 * P.geometry.pLen + P.geometry.qLen) ≤ usedBytes P.geometry.pLen := by unfold packed usedBytes domainCheck; omega
  have r1 : packed + P.geometry.pLen ≤ usedBytes P.geometry.pLen := by omega
  have r2 : packed + P.geometry.pLen + P.geometry.qLen ≤ usedBytes P.geometry.pLen := by omega
  have r3 : packed + P.geometry.pLen + P.geometry.qLen + P.geometry.pLen ≤ usedBytes P.geometry.pLen := by omega
  have widen1 {a b : Mem} (O : Frame [P.geometry.part packed P.geometry.pLen] a b) :
      Frame [P.geometry.part packed (2 * P.geometry.pLen + P.geometry.qLen)] a b := O.sub (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_singleton_self _, fun _ h => Nat.le_trans h (by change P.geometry.pLen ≤ 2 * P.geometry.pLen + P.geometry.qLen; omega)⟩)
  have widen2 {a b : Mem} (O : Frame [P.geometry.part (packed + P.geometry.pLen) P.geometry.qLen] a b) :
      Frame [P.geometry.part packed (2 * P.geometry.pLen + P.geometry.qLen)] a b := O.sub (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_singleton_self _, P.geometry.subarea (by omega)⟩)
  have widen3 {a b : Mem} (O : Frame [P.geometry.part (packed + P.geometry.pLen + P.geometry.qLen) P.geometry.pLen] a b) :
      Frame [P.geometry.part packed (2 * P.geometry.pLen + P.geometry.qLen)] a b := O.sub (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_singleton_self _, by
      rw [Nat.add_assoc packed]; exact P.geometry.subarea (by omega)⟩)
  have preserved {a b : Mem} (O : Frame [P.geometry.part packed (2 * P.geometry.pLen + P.geometry.qLen)] a b)
      {d n : Nat} (room : d + n ≤ usedBytes P.geometry.pLen) (before : d + n ≤ packed) :
      Spec.Rsa.bytesAt b (off P.geometry.base d) n = Spec.Rsa.bytesAt a (off P.geometry.base d) n :=
    drawFrame_bytes O (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact P.geometry.parts_disjoint room pkr (.inl before))
      (by unfold packed at before; omega)
  unfold pack
  refine WP.seq (WP.mono (packPart_ok R (by omega) (by omega) pr r1 (by decide)
    (P.geometry.parts_disjoint pr r1 (.inl (by unfold p packed; omega)))) fun a ⟨Ra, ba, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (packPart_ok Ra (by omega) (by omega) qr r2 (by unfold VG.Impl.Dsa.Generation.Layout.hash packed; omega)
    (P.geometry.parts_disjoint qr r2 (.inl (by unfold q packed; omega)))) fun b ⟨Rb, bb, Ob, Kb⟩ => ?_)
  rw [preserved (widen1 Oa) qr (by unfold q packed; omega)] at bb
  refine WP.mono (packPart_ok Rb (by omega) (by omega) gr r3 (by unfold VG.Impl.Dsa.Generation.Layout.hash packed; omega)
    (P.geometry.parts_disjoint gr r3 (.inl (by unfold g packed; omega)))) fun t ⟨Rt, bt, Ot, Kt⟩ => ?_
  rw [preserved ((widen1 Oa).trans (widen2 Ob)) gr (by unfold g packed; omega)] at bt
  have pfinal : Spec.Rsa.bytesAt t.mem (off P.geometry.base packed) P.geometry.pLen =
      Spec.Rsa.bytesAt s.mem (off P.geometry.base p) P.geometry.pLen := by
    rw [drawFrame_bytes Ot (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact P.geometry.parts_disjoint r1 r3 (.inl (by omega))) (by omega),
      drawFrame_bytes Ob (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact P.geometry.parts_disjoint r1 r2 (.inl (by omega))) (by omega), ba]
  have qfinal : Spec.Rsa.bytesAt t.mem (off P.geometry.base (packed + P.geometry.pLen)) P.geometry.qLen =
      Spec.Rsa.bytesAt s.mem (off P.geometry.base q) P.geometry.qLen := by
    rw [drawFrame_bytes Ot (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact P.geometry.parts_disjoint r2 r3 (.inl (Nat.le_refl _))) (by omega), bb]
  refine ⟨Rt, ?_, ((widen1 Oa).trans (widen2 Ob)).trans (widen3 Ot), Ka.trans (Kb.trans Kt)⟩
  rw [show 2 * P.geometry.pLen + P.geometry.qLen = (P.geometry.pLen + P.geometry.qLen) + P.geometry.pLen by omega,
    VG.Proof.Dsa.Generation.bytesAt_append, VG.Proof.Dsa.Generation.bytesAt_append]
  have add (d e : Nat) : VG.Proof.Bignum.off (off P.geometry.base d) e = off P.geometry.base (d + e) := by
    simp only [VG.Proof.Bignum.off, off, BitVec.ofNat_add, BitVec.add_assoc]
  rw [add, add, ← Nat.add_assoc packed, pfinal, qfinal, bt]
end VG.Proof.Dsa.X86.Generation
