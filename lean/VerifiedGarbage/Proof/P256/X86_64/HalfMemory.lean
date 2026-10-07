import VerifiedGarbage.Proof.P256.X86_64.Half
import VerifiedGarbage.Proof.Mont.X86_64.Chain

/-! Memory contract for P-256 modular halving, permitting in-place operation. -/
namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.P256.X86_64 VG.Impl.Mont.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.X25519.X86_64

private theorem regsVal_four (s : State) :
    regsVal s [.r8,.r9,.r10,.r11]=val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) := by
  simp only [regsVal,val4]
  omega

/-- A canonical input yields its canonical modular half, preserving all memory
outside the output. No separation between input and output is needed. -/
theorem half_ok {s : State} {base : Addr} {size a o : Nat}
    (hs : Scr s base size) (ha : a+32≤size) (ho : o+32≤size)
    (hx : wordsVal s.mem base a 4 < Spec.P256.p) :
    WP isa (.block (half o a)) s fun t =>
      wordsVal t.mem base o 4 = halfValue (wordsVal s.mem base a 4) ∧
      wordsVal t.mem base o 4 < Spec.P256.p ∧
      (2*wordsVal t.mem base o 4)%Spec.P256.p=wordsVal s.mem base a 4 ∧
      KeepRegs [.rax,.rcx,.rdx,.rbp,.r8,.r9,.r10,.r11,.r12] s t ∧
      Outside base o 32 s.mem t.mem := by
  rw [half,show (loads [.r8,.r9,.r10,.r11] a ++ Half.mask ++ Half.add ++ Half.shift ++
      stores [.r8,.r9,.r10,.r11] o) = loads [.r8,.r9,.r10,.r11] a ++
        ((Half.mask ++ Half.add ++ Half.shift) ++ stores [.r8,.r9,.r10,.r11] o) by
          simp only [List.append_assoc],WP.block_append_iff]
  refine WP.mono (loads_ok [.r8,.r9,.r10,.r11] hs ha (by constructor <;> decide)) fun u ⟨hu,ku⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (half_core_ok u) fun v ⟨hv,kv⟩ => ?_
  have hs₁ := hs.of_keeps ku (by decide)
  have hs₂ := hs₁.of_keeps kv (by decide)
  refine WP.mono (stores_ok [.r8,.r9,.r10,.r11] hs₂ ho (by decide)) fun t ⟨ht,kt,ot⟩ => ?_
  change regsVal u [.r8,.r9,.r10,.r11]=wordsVal s.mem base a 4 at hu
  change wordsVal t.mem base o 4=regsVal v [.r8,.r9,.r10,.r11] at ht
  have he : wordsVal t.mem base o 4=halfValue (wordsVal s.mem base a 4) := by
    rw [ht,regsVal_four,hv,←regsVal_four,hu]
  refine ⟨he,he ▸ halfValue_lt hx,?_,?_,?_⟩
  · rw [he]; exact halfValue_twice hx
  · exact ((VG.Proof.Mont.X86_64.Keeps.regs ku).mono (by simp)).trans
      ((VG.Proof.Mont.X86_64.Keeps.regs kv).trans (kt.mono (by simp)))
  · rw [←ku.2.1,←kv.2.1]
    exact ot

end VG.Proof.P256.X86_64
