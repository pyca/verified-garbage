module
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Impl.Dsa.X86.Generation.DrawWitness
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawArguments
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
import VerifiedGarbage.Proof.Dsa.X86.KeyCopy

/-! # Witness drawing copies exactly the significant slice and records whole consumption -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86.Generation

theorem drawWitness_ok {s : State} {base : Addr} {size len draw used : Nat} {tape out src : BitVec 32}
    (S : Scr s base size) (room : primeWitness + 4 ≤ size)
    (source : s.mem.readW (off base primeTape) 32 = tape)
    (consumed : s.mem.readW (off base primeUsed) 32 = BitVec.ofNat 32 used)
    (output : s.mem.readW (off base primeWitness) 32 = out)
    (slice : src = tape + BitVec.ofNat 32 (used + (draw - len)))
    (positive : 0 < len) (len32 : len < 2 ^ 32) (sourceFit : src.toNat + len ≤ 2 ^ 32) (outputFit : out.toNat + len ≤ 2 ^ 32)
    (sourceOutput : Region.Disjoint ⟨src.setWidth 64, len⟩ ⟨out.setWidth 64, len⟩)
    (sourceUsed : Region.Disjoint ⟨src.setWidth 64, len⟩ ⟨off base primeUsed, 4⟩)
    (usedOutput : Region.Disjoint ⟨off base primeUsed, 4⟩ ⟨out.setWidth 64, len⟩)
    (pointerOutput : Region.Disjoint ⟨off base primeWitness, 4⟩ ⟨out.setWidth 64, len⟩)
    (read : ∀ i < len, InRegions (s.rd ++ s.wr) (off (src.setWidth 64) i) 1)
    (write : ∀ i < len, InRegions s.wr (off (out.setWidth 64) i) 1) :
    WP isa (drawWitness len draw) s fun t =>
      Spec.Rsa.bytesAt t.mem (out.setWidth 64) len = Spec.Rsa.bytesAt s.mem (src.setWidth 64) len ∧
      t.mem.readW (off base primeUsed) 32 = BitVec.ofNat 32 (used + draw) ∧ t.gpr .esi = out ∧
      Frame [⟨off base primeUsed, 4⟩, ⟨out.setWidth 64, len⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := by
  unfold drawWitness
  refine WP.seq (WP.mono (drawWitnessArgs_ok S room source consumed output) fun a ⟨si, dx, cx, bx, ma, Ka⟩ => ?_)
  have Oa : Frame [⟨off base primeUsed, 4⟩] s.mem a.mem := by rw [ma]; exact drawStore_frame _ _ _
  refine WP.seq (WP.mono (keyCopy_ok positive len32 sourceFit outputFit sourceOutput
    (si.trans slice.symm) dx cx bx
    (fun i hi => by rw [Ka.2.1, Ka.2.2]; exact read i hi)
    (fun i hi => by rw [Ka.2.2]; exact write i hi)) fun b I => ?_)
  have Ob := copyOutside_frame I.mem
  have Kb : Keeps [.eax, .ebx, .ecx, .edx, .esi] s b := Ka.trans (I.keeps.mono (by decide))
  have Sb := S.of_keeps Kb (by decide)
  have pointer : b.mem.readW (off base primeWitness) 32 = out := by
    rw [Ob.readW (Region.contains_self _ 4) (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact pointerOutput) (by decide),
      ma, Mem.readW_writeW_sep (Offset.sep base (by decide : primeWitness + 4 ≤ primeUsed ∨ primeUsed + 4 ≤ primeWitness)
        (by decide) (by decide)) (by decide), output]
  refine wp_movS (v := out) (by rw [readSrc_sc Sb room, pointer]) fun t bt _ => WP.block_nil ?_
  refine ⟨?_, ?_, bt.gpr, ?_, Kb.widen bt.keeps⟩
  · rw [bt.mem, copied_unmasked I, drawFrame_bytes Oa (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact sourceUsed) (by omega)]
  · rw [bt.mem, Ob.readW (Region.contains_self _ 4) (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact usedOutput) (by decide),
      ma, Mem.readW_writeW_self32]
  · rw [bt.mem]
    exact (Oa.mono (by intro r hr; simp_all)).trans (Ob.mono (by intro r hr; simp_all))
end VG.Proof.Dsa.X86.Generation
