module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchDone
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchMemory
import VerifiedGarbage.Proof.Framework.Offset

/-! # Returning a complete native search preserves its output and System V registers -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

def SearchReturned (p : SearchPublic) (result : Spec.Ffdh.ParameterSearchResult) (t : State) : Prop :=
  ((t.gpr .rax).setWidth 32).toNat = result.status ∧ SearchOutput p result t.mem ∧
    Spec.Rsa.wordsAt t.mem p.c.up 1 = [BitVec.ofNat 64 result.used] ∧
    Spec.Rsa.wordsAt t.mem p.control 4 =
      [BitVec.ofNat 64 result.remaining, BitVec.ofNat 64 p.c.k,
        BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits), BitVec.ofNat 64 result.requested]

theorem search_finish {p : SearchPublic} {original s : State} {result : Spec.Ffdh.ParameterSearchResult}
    (h : SearchDone p original result s) :
    WP isa (.block finish) s fun t => SearchReturned p result t ∧
      (∀ reg ∈ calleeSaved, t.gpr reg = original.gpr reg) ∧ t.rd = original.rd ∧ t.wr = original.wr := by
  refine WP.mono (search_finish_values h) fun t ⟨ha, hr12, hm, k⟩ => ?_
  have hf : Frame [⟨p.c.up, 8⟩] s.mem t.mem := by
    rw [hm]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have ho : Spec.Rsa.bytesAt t.mem p.c.op p.c.k = Spec.Rsa.bytesAt s.mem p.c.op p.c.k := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact hf.bytes (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact h.input.output_used_disjoint)
      (Nat.le_of_lt h.input.length_lt) (List.mem_range.mp hi)
  have hc (j : Nat) (hj : j < 4) : word t.mem p.control (8 * j) = word s.mem p.control (8 * j) :=
    hf.readW (r := ⟨p.control, 128⟩)
      (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact h.input.control_used_disjoint) (by decide)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, k.2.1.trans h.rd, k.2.2.trans h.wr⟩
  · rw [ha]
    cases result <;> rfl
  · change Spec.Rsa.bytesAt t.mem p.c.op p.c.k = _
    rw [ho]
    exact h.output
  · change [word t.mem p.c.up 0] = [_]
    rw [hm]
    congr 1
    simpa only [Bignum.word, off, BitVec.add_zero] using
      Mem.readW_writeW_self64 s.mem p.c.up (BitVec.ofNat 64 result.used)
  · have he : Spec.Rsa.wordsAt t.mem p.control 4 = Spec.Rsa.wordsAt s.mem p.control 4 := by
      change [word t.mem p.control 0, word t.mem p.control 8, word t.mem p.control 16, word t.mem p.control 24] = _
      rw [hc 0 (by decide), hc 1 (by decide), hc 2 (by decide), hc 3 (by decide)]
      rfl
    exact he.trans h.policy
  · intro reg hreg
    by_cases he : reg = .r12
    · subst he; exact hr12
    · exact (k.gpr (by cases reg <;> simp_all [calleeSaved])).trans (h.saved reg hreg he)

end VG.Proof.Ffdh.X86_64.Generation
