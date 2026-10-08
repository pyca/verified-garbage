import VerifiedGarbage.Proof.Weierstrass.X86.NafSubWord

/-! Borrow propagation through the public scalar's scratch words. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Weierstrass.X86 VG.Proof.Mont.X86 VG.Proof.Mont

/-- Low word followed by k copies of a sign-extension word. -/
def nafDigitVal (d e : BitVec 32) : Nat → Nat
  | 0 => d.toNat
  | k+1 => nafDigitVal d e k + 2^(32*(k+1))*e.toNat

theorem nafSubChain_ok {s : State} {base : Addr} {size work : Nat}
    (hs : Scr s base size) : ∀ k, work+4*(k+1)≤size →
    WP isa (.block (Naf.subWord .sub work 0 .ecx ++
      (List.range k).flatMap fun i => Naf.subWord .sbb work (i+1) .edx)) s fun u =>
      Outside base work (4*(k+1)) s.mem u.mem ∧
      (∃ c, u.cf=some c ∧ val32 u.mem base work (k+1)+nafDigitVal (s.gpr .ecx) (s.gpr .edx) k =
        val32 s.mem base work (k+1)+2^(32*(k+1))*c.toNat) ∧ Keeps [.eax] s u
  | 0, ha => by
    simp only [List.range_zero,List.flatMap_nil,List.append_nil]
    refine WP.mono (nafSubWord_ok hs (by omega) (by decide) (.inl ⟨rfl,rfl⟩))
      fun u ⟨O,⟨c,hc,V⟩,K⟩ => ⟨by simpa using O,⟨c,hc,?_⟩,K⟩
    simpa only [val32,nafDigitVal,Nat.mul_zero,Nat.add_zero,Bool.toNat_false] using V
  | k+1, ha => by
    have hn := hs.nowrap
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton,←List.append_assoc,
      WP.block_append_iff]
    refine WP.mono (nafSubChain_ok hs k (by omega)) fun s₁ ⟨O₁,⟨c₁,hc₁,V₁⟩,K₁⟩ => ?_
    refine WP.mono (nafSubWord_ok (hs.of_keeps K₁ (by decide)) ha (by decide) (.inr ⟨rfl,hc₁⟩))
      fun u ⟨O,⟨c,hc,V⟩,K⟩ => ⟨?_,⟨c,hc,?_⟩,K₁.trans K⟩
    · exact (O₁.mono (Nat.le_refl _) (by omega)).trans (O.mono (by omega) (by omega))
    · rw [O₁.w32 (d := work+4*(k+1)) (by omega) (by omega),K₁.1 .edx (by decide)] at V
      rw [val32_succ u.mem base work (k+1),val32_succ s.mem base work (k+1),
        O.val32 (by omega) (by omega),nafDigitVal,pow32_succ (k+1)]
      generalize 2^(32*(k+1))=P at *
      grind

end VG.Proof.Weierstrass.X86
