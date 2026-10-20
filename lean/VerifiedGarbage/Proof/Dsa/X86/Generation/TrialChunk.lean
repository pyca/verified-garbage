module
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Sha256.X86.Stream.Common
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Trial
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialChunkValue
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialRemainder

/-! # One two-byte trial-division iteration -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem trialChunk_ok {s : State} {input : BitVec 32} {r p count : Nat}
    (hp : 1 < p) (pfit : p < 65536) (hr : r < p) (hc : 1 ≤ count) (hcfit : count < 2 ^ 32)
    (bp : s.gpr .ebp = input) (xb : s.gpr .ebx = BitVec.ofNat 32 r)
    (cx : s.gpr .ecx = BitVec.ofNat 32 count)
    (ps : s.gpr .esi = BitVec.ofNat 32 p) (vi : s.gpr .edi = BitVec.ofNat 32 (2 ^ 32 / p))
    (fit : input.toNat + 2 ≤ 2 ^ 32)
    (rd : ∀ i < 2, InRegions (s.rd ++ s.wr) (off (input.setWidth 64) i) 1) :
    WP isa (.block trialChunk) s fun t =>
      t.gpr .ebx = BitVec.ofNat 32 ((r * 65536 + (s.mem (input.setWidth 64)).toNat * 256 +
        (s.mem (off (input.setWidth 64) 1)).toNat) % p) ∧
      t.gpr .ebp = input + 2#32 ∧ t.gpr .ecx = BitVec.ofNat 32 (count - 1) ∧
      t.zf = some (decide (count = 1)) ∧ t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have b0 := (s.mem (input.setWidth 64)).isLt
  have b1 := (s.mem (off (input.setWidth 64) 1)).isLt
  unfold trialChunk
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (trialChunkValue_ok (by omega) bp xb fit rd) fun a ⟨ax, ma, ka⟩ => ?_)
  refine WP.block_append (WP.mono (smallRemainder_ok hp pfit (by omega) ax
    ((ka.1 _ (by decide)).trans ps) ((ka.1 _ (by decide)).trans vi)) fun b ⟨bx, mb, kb⟩ => ?_)
  refine wp_addi fun c bc => wp_subi fun t ct _ zt => WP.block_nil ?_
  have k : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := (((ka.mono (by decide)).trans
    (kb.mono (by decide))).trans (bc.keeps.mono (by decide))).trans (ct.keeps.mono (by decide))
  refine ⟨?_, ?_, ?_, ?_, by rw [ct.mem, bc.mem, mb, ma], k⟩
  · rw [ct.other _ (by decide), bc.other _ (by decide), bx]
  · rw [ct.other _ (by decide), bc.gpr, kb.1 _ (by decide), ka.1 _ (by decide), bp]; rfl
  · rw [ct.gpr, bc.other _ (by decide), kb.1 _ (by decide), ka.1 _ (by decide), cx]
    exact VG.Proof.Sha256.X86.Stream.sub_ofNat hc
  · rw [zt, bc.other _ (by decide), kb.1 _ (by decide), ka.1 _ (by decide), cx,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_beq hcfit (by decide)]
end VG.Proof.Dsa.X86.Generation
