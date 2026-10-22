module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.PSearch
public import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-! Advance the public attempt counter and seed offset without touching randomness tapes. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Proof.Mont VG.Proof.Mont.X86

def pAdvanceMemory (m : Mem) (base : Addr) (i offset stride : Nat) : Mem :=
  (m.writeW (off base pIndex) (BitVec.ofNat 32 (i + 1))).writeW
    (off base candidateOffset) (BitVec.ofNat 32 (offset + stride))

theorem p_search_advance_head {s : State} {base : Addr} {bytes i offset limit stride : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes)
    (index : s.mem.readW (off base pIndex) 32 = BitVec.ofNat 32 i)
    (seedOffset : s.mem.readW (off base candidateOffset) 32 = BitVec.ofNat 32 offset)
    (indexBound : i + 1 < 2 ^ 32) (limitBound : limit < 2 ^ 32) :
    WP isa (.block (pSearchAdvanceHead limit stride)) s fun t =>
      t.cf = some (decide (i + 1 < limit)) ∧ t.mem = pAdvanceMemory s.mem base i offset stride ∧
      t.gpr .eax = BitVec.ofNat 32 (i + 1) ∧ Keeps [.eax, .ecx] s t := by
  have indexFit : pIndex + 4 ≤ bytes := Nat.le_trans (by decide : pIndex + 4 ≤ 40960) capacity
  have offsetFit : candidateOffset + 4 ≤ bytes := Nat.le_trans (by decide : candidateOffset + 4 ≤ 40960) capacity
  unfold pSearchAdvanceHead
  refine wp_movS (readSrc_sc scr (d := pIndex) indexFit) fun a A _ => wp_addS rfl fun b B _ => ?_
  have Sb := (scr.of_keeps A.keeps (by decide)).of_keeps B.keeps (by decide)
  refine wp_storeS (Sb.ea (by omega)) (Sb.write indexFit) fun c C => ?_
  have Sc := Sb.of_keeps (C.keeps []) (by decide)
  refine wp_movS (readSrc_sc Sc (d := candidateOffset) offsetFit) fun d D _ => wp_addS rfl fun e E _ => ?_
  have Se := (Sc.of_keeps D.keeps (by decide)).of_keeps E.keeps (by decide)
  refine wp_storeS (Se.ea (by omega)) (Se.write offsetFit) fun f F =>
    wp_cmpi fun t T carry _ => WP.block_nil ?_
  have valueB : b.gpr .eax = BitVec.ofNat 32 (i + 1) := by
    rw [B.gpr, A.gpr, index, BitVec.ofNat_add]
    rfl
  have memoryC : c.mem = s.mem.writeW (off base pIndex) (BitVec.ofNat 32 (i + 1)) := by
    rw [C.mem, B.mem, A.mem, valueB]
  have valueE : e.gpr .ecx = BitVec.ofNat 32 (offset + stride) := by
    rw [E.gpr, D.gpr, memoryC,
      Mem.readW_writeW_sep (Offset.sep base (.inl (by decide : candidateOffset + 4 ≤ pIndex)) (by decide) (by decide))
        (by decide), seedOffset, BitVec.ofNat_add]
  have eax : t.gpr .eax = BitVec.ofNat 32 (i + 1) := by
    rw [T.gpr, F.gpr, E.other .eax (by decide), D.other .eax (by decide), C.gpr, valueB]
  refine ⟨?_, ?_, eax, ?_⟩
  · rw [carry, F.gpr, E.other .eax (by decide), D.other .eax (by decide), C.gpr, valueB,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt indexBound, Nat.mod_eq_of_lt limitBound]
  · rw [T.mem, F.mem, E.mem, D.mem, memoryC, valueE]
    rfl
  · exact ((((((A.keeps.mono (by decide)).trans (B.keeps.mono (by decide))).trans (C.keeps _)).trans
      (D.keeps.mono (by decide))).trans (E.keeps.mono (by decide))).trans (F.keeps _)).trans (T.keeps _)

end VG.Proof.Dsa.X86.Generation
