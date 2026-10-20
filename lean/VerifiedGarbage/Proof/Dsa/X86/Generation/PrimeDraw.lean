module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReady
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Dsa.X86.Generation.DrawWitness
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawWitness
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeEffects

/-! # A full available draw preserves the prime-test invariant -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem primeDraw_ok {G : PrimeConfig} {s : State} {used : Nat} (R : PrimeReady G s)
    (full : used + G.draw ≤ G.tapeLen)
    (consumed : s.mem.readW (off G.base primeUsed) 32 = BitVec.ofNat 32 used) :
    WP isa (drawWitness G.len G.draw) s fun t => PrimeReady G t ∧
      Spec.Rsa.bytesAt t.mem (G.witness.setWidth 64) G.len =
        Spec.Rsa.bytesAt s.mem (off (G.tape.setWidth 64) (used + (G.draw - G.len))) G.len ∧
      t.mem.readW (off G.base primeUsed) 32 = BitVec.ofNat 32 (used + G.draw) ∧ t.gpr .esi = G.witness ∧
      t.mem.readW (off G.base primeUniform) 32 = s.mem.readW (off G.base primeUniform) 32 ∧
      PrimeFrame G.base G.n (G.witness.setWidth 64) G.len s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := by
  have lmin := G.lenMin
  have lmax := G.lenMax
  have tapeFit := G.tapeFit
  have tape32 := G.tapeLen32
  have drawEnough : G.len ≤ G.draw := by unfold PrimeConfig.draw PrimeConfig.n; omega
  let offset := used + (G.draw - G.len)
  let src := G.tape + BitVec.ofNat 32 offset
  have offsetBound : offset + G.len ≤ G.tapeLen := by dsimp only [offset]; omega
  have srcNat : src.toNat = G.tape.toNat + offset := by
    simp only [src, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : offset < 2 ^ 32), Nat.mod_eq_of_lt (by omega)]
  have srcAddr : src.setWidth 64 = off (G.tape.setWidth 64) offset := addr_eq (by omega)
  have sub : Region.Sub ⟨src.setWidth 64, G.len⟩ ⟨G.tape.setWidth 64, G.tapeLen⟩ := by
    rw [srcAddr]
    exact Offset.sub_base _ offsetBound
  have usedRoom : primeUsed + 4 ≤ G.size := by have := G.room; unfold primeUsed primeExponent at *; omega
  have pointerRoom : primeWitness + 4 ≤ G.size := by have := G.room; unfold primeWitness primeExponent at *; omega
  refine WP.mono (drawWitness_ok R.context.scr pointerRoom R.tape consumed R.witness
    (src := src) rfl (by omega) (by omega) (by rw [srcNat]; omega) G.witnessFit
    (G.tapeWitness.sub_left sub)
    ((G.tapeScratch.sub_left sub).sub_right (Offset.sub_base _ usedRoom))
    (G.witnessScratch.symm.sub_left (Offset.sub_base _ usedRoom))
    (G.witnessScratch.symm.sub_left (Offset.sub_base _ pointerRoom))
    (fun i hi => by
      rw [srcAddr, off, off, Offset.add_add]
      exact R.tapeRead _ (by omega)) R.witnessWrite) fun t ⟨bytes, count, pointer, O, K⟩ => ?_
  have F := primeFrame_draw (n := G.n) O
  refine ⟨R.keep F K (by decide) (by decide), by rw [bytes, srcAddr], count, pointer, ?_, F, K⟩
  apply O.readW (Region.contains_self _ 4) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint G.base (by decide) (by decide) (by decide)
  · exact G.witnessScratch.symm.sub_left (Offset.sub_base _ (by
      have := G.flagRoom; unfold primeUniform primeIsUniform at *; omega))
end VG.Proof.Dsa.X86.Generation
