module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.ForceWitness
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Dsa.Generation.WitnessBytes
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.Generation.WitnessMemory
import VerifiedGarbage.Proof.Dsa.X86.RandomScan

/-! # The endpoint writes implement the specification's forced witness -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86

theorem forceWitness_ok {s : State} {p : BitVec 32} {len : Nat}
    (hn : 2 ≤ len) (hp : s.gpr .esi = p) (hfit : p.toNat + len ≤ 2 ^ 32)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (off (p.setWidth 64) i) 1)
    (hwr : ∀ i < len, InRegions s.wr (off (p.setWidth 64) i) 1) :
    WP isa (.block (Impl.Dsa.X86.Generation.forceWitness len)) s fun t =>
      Spec.Rsa.bytesAt t.mem (p.setWidth 64) len =
        VG.Proof.Dsa.Generation.forcedWitnessBytes (Spec.Rsa.bytesAt s.mem (p.setWidth 64) len) ∧
      Frame [⟨p.setWidth 64, len⟩] s.mem t.mem ∧
      Keeps [.eax] s t := by
  have addr0 : s.ea (at_ .esi 0) = p.setWidth 64 := by
    change (s.gpr .esi + 0#32).setWidth 64 = _; rw [BitVec.add_zero, hp]
  have rd0 : InRegions (s.rd ++ s.wr) (p.setWidth 64) 1 := by simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hrd 0 (by omega)
  have wr0 : InRegions s.wr (p.setWidth 64) 1 := by simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hwr 0 (by omega)
  have neq : off (p.setWidth 64) (len - 1) ≠ p.setWidth 64 := by
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using Offset.add_ofNat_ne (p.setWidth 64)
      (by omega : len - 1 < 2 ^ 64) (by decide : 0 < 2 ^ 64) (by omega : len - 1 ≠ 0)
  unfold Impl.Dsa.X86.Generation.forceWitness
  refine wp_load8 addr0 rd0 fun a sa _ _ => wp_logicS (.inl rfl) rfl fun b ab => ?_
  have dst0 : b.ea (at_ .esi 0) = p.setWidth 64 := by
    change (b.gpr .esi + 0#32).setWidth 64 = _
    rw [BitVec.add_zero, ab.other _ (by decide), sa.other _ (by decide), hp]
  refine wp_store8 dst0 (by rw [ab.wr, sa.wr]; exact wr0) fun c bc => ?_
  have dstL : c.ea (at_ .esi (len - 1)) = off (p.setWidth 64) (len - 1) := by
    change (c.gpr .esi + BitVec.ofNat 32 (len - 1)).setWidth 64 = _
    rw [bc.gpr, ab.other _ (by decide), sa.other _ (by decide), hp]; exact addr_eq (by omega)
  refine wp_load8 dstL (by rw [bc.rd, bc.wr, ab.rd, ab.wr, sa.rd, sa.wr]; exact hrd _ (by omega)) fun d cd _ _ =>
    wp_orS rfl fun e de => ?_
  have dstL' : e.ea (at_ .esi (len - 1)) = off (p.setWidth 64) (len - 1) := by
    change (e.gpr .esi + BitVec.ofNat 32 (len - 1)).setWidth 64 = _
    rw [de.other _ (by decide), cd.other _ (by decide)]
    exact dstL
  refine wp_store8 dstL' (by rw [de.wr, cd.wr, bc.wr, ab.wr, sa.wr]; exact hwr _ (by omega)) fun t et => WP.block_nil ?_
  have b0 : (b.gpr .eax).setWidth 8 = s.mem (p.setWidth 64) &&& (127#8) := by
    rw [ab.gpr, sa.gpr, ite_eq_left rfl]; simp only [BitVec.setWidth_and, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide), BitVec.setWidth_eq]; rfl
  have bl : (e.gpr .eax).setWidth 8 = s.mem (off (p.setWidth 64) (len - 1)) ||| (2#8) := by
    rw [de.gpr, cd.gpr, bc.mem, ab.mem, sa.mem, WriteBytes.writeW8_apply, ite_eq_right neq]
    simp only [BitVec.setWidth_or, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide), BitVec.setWidth_eq]; rfl
  have mem : t.mem = (s.mem.writeW (p.setWidth 64) (s.mem (p.setWidth 64) &&& (127#8))).writeW
      (off (p.setWidth 64) (len - 1)) (s.mem (off (p.setWidth 64) (len - 1)) ||| (2#8)) := by
    rw [et.mem, show Reg8.al.reg = Reg.eax from rfl, bl, de.mem, cd.mem, bc.mem,
      show Reg8.al.reg = Reg.eax from rfl, b0, ab.mem, sa.mem]
  refine ⟨?_, ?_, (((((sa.keeps.trans ab.keeps).trans (bc.keeps _)).trans cd.keeps).trans de.keeps).trans (et.keeps _))⟩
  · rw [mem]; exact VG.Proof.Dsa.Generation.forcedWitness_memory _ _ hn (by omega)
  · intro a outside
    have ha : ∀ i < len, a ≠ off (p.setWidth 64) i := by
      intro i hi eq
      apply outside ⟨p.setWidth 64, len⟩ (by simp)
      rw [eq]
      exact Offset.contains_base _ hi (by omega)
    have h0 : a ≠ p.setWidth 64 := by simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ha 0 (by omega)
    rw [mem, WriteBytes.writeW8_apply, ite_eq_right (ha _ (by omega)), WriteBytes.writeW8_apply, ite_eq_right h0]
end VG.Proof.Dsa.X86.Generation
