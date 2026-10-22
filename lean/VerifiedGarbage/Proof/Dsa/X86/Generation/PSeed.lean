module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.PSeedArguments
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeBytes
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SeedAdd
import VerifiedGarbage.Proof.Dsa.X86.Generation.HashWorkspacePointers
import VerifiedGarbage.Proof.Framework.Offset

/-! Construct a wrapped seed contribution without disturbing the retained subgroup. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86

theorem p_seed {s : State} {base : Addr} {bytes offset j : Nat} {src : BitVec 32} {seed : List Byte}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes)
    (tape : WitnessTape base bytes (s.gpr .esp) src seed s) (length : seed.length ≤ 32)
    (pointer : s.mem.readW (off base seedPointer) 32 = src)
    (value : s.mem.readW (off base candidateOffset) 32 = BitVec.ofNat 32 offset)
    (small : offset + j < 2 ^ 31) :
    WP isa (pSeed seed.length j) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base Layout.wrappedSeed) seed.length =
        Spec.Dsa.encodeBE seed.length (Spec.Dsa.decodeBE seed + (offset + j)) ∧
      Frame [⟨off base Layout.wrappedSeed, seed.length⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := by
  let dst := s.gpr .edi + BitVec.ofNat 32 Layout.wrappedSeed
  have dstAddr : byteAddr dst = off base Layout.wrappedSeed := workspace_pointer_address scr (by unfold Layout.wrappedSeed; omega)
  have fit : Layout.wrappedSeed + seed.length ≤ bytes := by unfold Layout.wrappedSeed; omega
  unfold pSeed
  refine WP.seq (WP.mono (p_seed_arguments scr capacity pointer value) fun a ⟨source, dest, carry, memory, K⟩ => ?_)
  have Sa := scr.of_keeps K (by decide)
  have Ta := tape.of_keeps K.2.1 K.2.2 memory
  refine WP.mono (seed_add seed (by omega) small tape.fit
    (workspace_pointer_fit scr (by unfold Layout.wrappedSeed; omega)) source dest carry
    (fun i hi => Ta.byte_read hi)
    (by
      intro i hi
      rw [dstAddr]
      apply Covers.one (Sa.write fit)
      exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi => Ta.byte_value hi)
    (by
      intro i hi k hk
      rw [dstAddr]
      exact Ta.byte_apart hi hk fit (by have := scr.nowrap; omega)))
    fun t ⟨encoded, outside, KT⟩ => ?_
  rw [dstAddr] at encoded
  refine ⟨encoded, ?_, (K.mono (by decide)).trans (KT.mono (by decide))⟩
  intro address untouched
  rw [← memory]
  apply outside address
  intro i hi eq
  apply untouched ⟨off base Layout.wrappedSeed, seed.length⟩ (List.mem_singleton_self _)
  rw [eq, dstAddr]
  exact Offset.contains_base _ (by omega) (by omega)

end VG.Proof.Dsa.X86.Generation
