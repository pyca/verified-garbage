module
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchData

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState

/-! # Output permissions relative to the persistent generation controller -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem SearchInput.length_lt {p : SearchPublic} {original : State} (h : SearchInput p original) :
    p.c.k < 2 ^ 64 := by
  cases h.2
  exact (original.gpr .rsi).isLt

theorem SearchInput.tape_lt {p : SearchPublic} {original : State} (h : SearchInput p original) :
    p.c.rand.length < 2 ^ 64 := by
  cases h.2
  simpa only [searchOfState, SearchPublic.c, candidateOfState, pcRand, Spec.Rsa.bytesAt,
    List.length_map, List.length_range] using (stackArg original 0).isLt

theorem SearchInput.width_bounds {p : SearchPublic} {original : State} (h : SearchInput p original) :
    64 ≤ p.c.k ∧ p.c.k ≤ 1024 := by
  have hc := pcCtx_of h.1.1
  cases h.2
  change 64 ≤ (original.gpr .rsi).toNat ∧ (original.gpr .rsi).toNat ≤ 1024
  have hbits1 : 512 ≤ (original.gpr .rcx).toNat := hc.bits1
  have hbits2 : (original.gpr .rcx).toNat ≤ 8192 := hc.bits2
  have hlen : (original.gpr .rsi).toNat = ((original.gpr .rcx).toNat + 7) / 8 := hc.len
  omega_using [hbits1, hbits2, hlen]

theorem SearchInput.width_bits {p : SearchPublic} {original : State} (h : SearchInput p original) :
    p.c.k = (p.c.bits + 7) / 8 := by
  cases h.2
  exact (pcCtx_of h.1.1).len

theorem SearchInput.entropy_bound {p : SearchPublic} {original : State} (h : SearchInput p original) :
    Spec.Ffdh.parameterEntropy p.c.bits ≤ 33555456 := by
  have hk := h.width_bounds.2
  rw [Spec.Ffdh.parameterEntropy, ← h.width_bits]
  omega_using [hk]

theorem SearchInput.tape_bound {p : SearchPublic} {original : State} (h : SearchInput p original) :
    p.c.rand.length ≤ Spec.Ffdh.parameterEntropy p.c.bits := by
  cases h.2
  simpa only [searchOfState, SearchPublic.c, candidateOfState, pcRand, Spec.Rsa.bytesAt,
    List.length_map, List.length_range] using h.1.2.2.2.2.2.2.2.2.2.2.2.2

theorem SearchInput.output {p : SearchPublic} {original s : State} (h : SearchInput p original)
    (hw : s.wr = original.wr) : OutOk s p.control 128 p.c.op p.c.k := by
  have hk := h.length_lt
  cases h.2
  change OutOk s (stackArg original 3) 128 (original.gpr .rdi) (original.gpr .rsi).toNat
  have hd : (inputControl original).Disjoint ⟨original.gpr .rdi, (original.gpr .rsi).toNat⟩ :=
    h.1.2.2.2.2.2.1 _ (by simp [inputBuffers])
  refine ⟨?_, ?_⟩
  · intro i hi
    rw [hw, h.1.2.2.2.1]
    exact ⟨⟨original.gpr .rdi, (original.gpr .rsi).toNat⟩, by simp [inputBuffers],
      contains_byte _ (by omega_using [hi]) (by omega_using [hi, hk])⟩
  · intro i hi
    exact out_scr hd.symm (contains_byte _ (by omega_using [hi]) (by omega_using [hi, hk]))

theorem SearchInput.used_memory {p : SearchPublic} {original s : State} (h : SearchInput p original)
    (hw : s.wr = original.wr) : Scr s p.c.up 8 := by
  cases h.2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hu, _⟩ := h.1.1
  exact Scr.of_mem (by rw [hw, h.1.2.2.2.1]; simp [inputBuffers, searchOfState, SearchPublic.c, candidateOfState]) hu

theorem SearchInput.output_used_disjoint {p : SearchPublic} {original : State} (h : SearchInput p original) :
    (⟨p.c.op, p.c.k⟩ : Region).Disjoint ⟨p.c.up, 8⟩ := by
  cases h.2
  obtain ⟨_, _, _, _, hd, _⟩ := h.1.1
  exact hd

theorem SearchInput.control_used_disjoint {p : SearchPublic} {original : State} (h : SearchInput p original) :
    (⟨p.control, 128⟩ : Region).Disjoint ⟨p.c.up, 8⟩ := by
  cases h.2
  exact h.1.2.2.2.2.2.1 _ (List.mem_append_left _
    (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

end VG.Proof.Ffdh.X86_64.Generation
