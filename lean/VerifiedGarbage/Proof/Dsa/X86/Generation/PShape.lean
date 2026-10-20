module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PShape
import VerifiedGarbage.Proof.Mont.X86.Instr
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.Shape
import VerifiedGarbage.Proof.Dsa.X86.KeyCopy

/-! # The p-candidate byte shaper matches the shared full-width shaper -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem pShapeArgs_ok (len : Nat) {s : State} : WP isa (.block (pShapeArgs len)) s fun t =>
    t.gpr .edx = s.gpr .edi ∧ t.gpr .ecx = BitVec.ofNat 32 len ∧ t.gpr .ebx = BitVec.allOnes 32 ∧
    t.mem = s.mem ∧ Keeps [.ebx, .ecx, .edx] s t := by
  unfold pShapeArgs
  refine wp_movS rfl fun a sa _ => wp_movS rfl fun b ab _ => wp_movS rfl fun t bt _ => WP.block_nil ?_
  exact ⟨(bt.other _ (by decide)).trans ((ab.other _ (by decide)).trans sa.gpr),
    (bt.other _ (by decide)).trans ab.gpr, bt.gpr, bt.mem.trans (ab.mem.trans sa.mem),
    ((sa.keeps.mono (by decide)).trans (ab.keeps.mono (by decide))).trans (bt.keeps.mono (by decide))⟩

theorem pShape_ok {s : State} {src out : BitVec 32} {len : Nat}
    (lengthMin : 2 ≤ len) (lengthMax : len < 2 ^ 32)
    (sourceFit : src.toNat + len ≤ 2 ^ 32) (outputFit : out.toNat + len ≤ 2 ^ 32)
    (apart : Region.Disjoint ⟨src.setWidth 64, len⟩ ⟨out.setWidth 64, len⟩)
    (si : s.gpr .esi = src) (di : s.gpr .edi = out)
    (read : ∀ i < len, InRegions (s.rd ++ s.wr) (off (src.setWidth 64) i) 1)
    (write : ∀ i < len, InRegions s.wr (off (out.setWidth 64) i) 1) :
    WP isa (pShape len) s fun t =>
      Spec.Rsa.bytesAt t.mem (out.setWidth 64) len =
        VG.Proof.Ffdh.ParameterCandidate.shapedOctets (Spec.Rsa.bytesAt s.mem (src.setWidth 64) len) 7 ∧
      Frame [⟨out.setWidth 64, len⟩] s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := by
  unfold pShape
  refine WP.seq (WP.mono (pShapeArgs_ok len) fun a ⟨dx, cx, bx, mem, Ka⟩ => ?_)
  refine WP.seq (WP.mono (keyCopy_ok (by omega) lengthMax sourceFit outputFit apart
    ((Ka.1 _ (by decide)).trans si) (dx.trans di) cx bx
    (by intro i hi; rw [Ka.2.1, Ka.2.2]; exact read i hi)
    (by intro i hi; rw [Ka.2.2]; exact write i hi)) fun b I => ?_)
  have bytes := copied_unmasked I
  rw [mem] at bytes
  let bs := Spec.Rsa.bytesAt s.mem (src.setWidth 64) len
  have bl : bs.length = len := by simp [bs, Spec.Rsa.bytesAt]
  change Spec.Rsa.bytesAt b.mem (out.setWidth 64) len = bs at bytes
  have Kb : Keeps [.eax, .ebx, .ecx, .edx, .esi] s b := (Ka.mono (by decide)).trans (I.keeps.mono (by decide))
  have writable : ∀ i < bs.length, InRegions b.wr (off (out.setWidth 64) i) 1 := by
    intro i hi; rw [Kb.2.2]; exact write i (by omega)
  have data : ∀ i < bs.length, b.mem (off (out.setWidth 64) i) = bs.getD i 0 := by
    intro i hi
    have e := congrArg (fun xs : List Byte => xs[i]?) bytes
    simpa only [Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range (by omega : i < len),
      Option.map_some, List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD, Option.getD_some,
      Option.some.injEq] using e
  have step := shape_ok (by omega : 2 ≤ bs.length) ((Kb.1 _ (by decide)).trans di)
    (by rw [bl]; exact outputFit) (fun i hi => by
      obtain ⟨r, hr, hc⟩ := writable i hi
      exact ⟨r, List.mem_append_right _ hr, hc⟩) writable data
  rw [bl] at step
  refine WP.mono step fun t ⟨result, F, Kt⟩ => ?_
  refine ⟨result, ?_, Kb.trans (Kt.mono (by decide))⟩
  have Fc := copyOutside_frame I.mem
  rw [mem] at Fc
  exact Fc.trans F
end VG.Proof.Dsa.X86.Generation
