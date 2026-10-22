module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.PHash
public import VerifiedGarbage.Proof.Mont.X86.Instr

/-! Load the retained seed pointer and the current public modulus-search offset. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Proof.Mont VG.Proof.Mont.X86

theorem p_seed_arguments {s : State} {base : Addr} {bytes offset j : Nat} {src : BitVec 32}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes)
    (pointer : s.mem.readW (off base seedPointer) 32 = src)
    (value : s.mem.readW (off base candidateOffset) 32 = BitVec.ofNat 32 offset) :
    WP isa (.block (pSeedArguments j)) s fun t =>
      t.gpr .esi = src ∧
      t.gpr .ebx = s.gpr .edi + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.wrappedSeed ∧
      t.gpr .edx = BitVec.ofNat 32 (offset + j) ∧ t.mem = s.mem ∧ Keeps [.esi, .ebx, .edx] s t := by
  unfold pSeedArguments
  refine wp_movS (readSrc_sc scr (d := seedPointer) (by unfold seedPointer VG.Impl.Dsa.Generation.Layout.packed; omega))
    fun a A _ => wp_movS rfl fun b B _ => wp_addS rfl fun c C _ => ?_
  have SC := (scr.of_keeps A.keeps (by decide)).of_keeps B.keeps (by decide) |>.of_keeps C.keeps (by decide)
  refine wp_movS (readSrc_sc SC (d := candidateOffset)
    (by unfold candidateOffset VG.Impl.Dsa.Generation.Layout.packed; omega))
    fun d D _ => wp_addS rfl fun t T _ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [T.other .esi (by decide), D.other .esi (by decide), C.other .esi (by decide), B.other .esi (by decide), A.gpr, pointer]
  · rw [T.other .ebx (by decide), D.other .ebx (by decide), C.gpr, B.gpr, A.other .edi (by decide)]
  · rw [T.gpr, D.gpr, C.mem, B.mem, A.mem, value, BitVec.ofNat_add]
  · rw [T.mem, D.mem, C.mem, B.mem, A.mem]
  · exact (((A.keeps.mono (by decide)).trans (B.keeps.mono (by decide))).trans
      ((C.keeps.mono (by decide)).trans (D.keeps.mono (by decide)))).trans (T.keeps.mono (by decide))

end VG.Proof.Dsa.X86.Generation
