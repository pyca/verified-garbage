module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCallPre
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Internal candidate permissions and the exact unconsumed entropy suffix -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem callWrites_eq {p : SearchPublic} {s : State} (h : SearchInput p s) :
    callWrites p = inputBuffers s := by
  cases h.2
  rfl

theorem search_call_writes {p : SearchPublic} {original s t : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s)
    (hw : t.wr = (allocated 32 s).wr) : Covers (callWrites p) t.wr := by
  apply Covers.of_mem
  intro r hr
  rw [hw]
  apply List.mem_cons_of_mem
  rw [h.wr, h.input.1.2.2.2.1, ← callWrites_eq h.input]
  exact List.mem_append_left _ hr

theorem search_call_reads {p : SearchPublic} {original s t : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s)
    (hrd : t.rd = (allocated 32 s).rd) (hwr : t.wr = (allocated 32 s).wr) :
    Covers (callReads p used) (t.rd ++ t.wr) := by
  apply Covers.of_sub
  intro r hr
  simp only [callReads, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨inputRand original, ?_, used, ?_, ?_⟩
    · rw [hrd]
      exact List.mem_append_left _ (by change inputRand original ∈ s.rd; rw [h.rd, h.input.1.2.2.1]; simp)
    · cases h.input.2
      rfl
    · cases h.input.2
      dsimp only [inputRand, searchOfState, SearchPublic.c, candidateOfState]
      have hl : (pcRand original).length = (stackArg original 0).toNat := by
        simp only [pcRand, Spec.Rsa.bytesAt, List.length_map, List.length_range]
      have hu : used ≤ (pcRand original).length := h.used_le
      rw [hl] at hu ⊢
      omega_using [hu]
  · refine ⟨⟨s.gpr .rsp - 32, 32⟩, ?_, 8, ?_, by dsimp only; decide⟩
    · rw [hwr]
      exact List.mem_append_right _ (List.mem_cons_self ..)
    · rw [h.rsp]
      rfl

theorem search_arguments_frame {p : SearchPublic} {s t : State} {used : Nat}
    (hm : t.mem = writeController s.mem (s.gpr .rsp - 32) (searchCallValues p used)) :
    Frame [below (s.gpr .rsp) 32] s.mem t.mem := by
  rw [hm]
  apply writeController_frame_size _ _ _ (by decide)
  simp only [searchCallValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide

theorem search_call_random {p : SearchPublic} {original s t : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (ha : SearchArgs p used t)
    (hm : t.mem = writeController s.mem (s.gpr .rsp - 32) (searchCallValues p used))
    (hsp : t.gpr .rsp = s.gpr .rsp - 32) :
    pcRand t = p.c.rand.drop used := by
  have hf : Frame (original.wr ++ [below (original.gpr .rsp) 160]) s.mem t.mem := by
    apply (search_arguments_frame hm).sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨below (original.gpr .rsp) 160, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
    have hs : s.gpr .rsp = original.gpr .rsp := by cases h.input.2; exact h.rsp
    rw [hs]
    exact Offset.below_mono _ (by decide) (by decide)
  have hrandom : Spec.Rsa.bytesAt t.mem p.c.rp p.c.rand.length = p.c.rand :=
    (h.input.random_frame hf).trans h.random
  have hlen : p.c.rand.length < 2 ^ 64 := by
    cases h.input.2
    simpa only [searchOfState, SearchPublic.c, candidateOfState, pcRand, Spec.Rsa.bytesAt,
      List.length_map, List.length_range] using (stackArg original 0).isLt
  have ha0 : stackArg t 0 = BitVec.ofNat 64 (p.c.rand.length - used) :=
    search_call_args hsp hm 0 (by decide)
  have hs := VG.Proof.Dsa.bytesAt_slice t.mem p.c.rp
    (total := p.c.rand.length) (offset := used) (len := p.c.rand.length - used) (by omega_using [h.used_le])
  rw [hrandom, ← show (p.c.rand.drop used).length = p.c.rand.length - used from List.length_drop,
    List.take_length] at hs
  simpa only [pcRand, ha.2.2.2.2.2, ha0, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega_using [hlen] : p.c.rand.length - used < 2 ^ 64), off, List.length_drop] using hs.symm

end VG.Proof.Ffdh.X86_64.Generation
