module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchData
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # The native controller, tape, and candidate workspace are disjoint -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate

namespace SearchInput

variable {p : SearchPublic} {original : State}

theorem control_scr (h : SearchInput p original) {s : State} (hw : s.wr = original.wr) :
    Scr s p.control 128 := by
  cases h.2
  obtain ⟨_, _, _, hwr, hroom, _⟩ := h.1
  exact Scr.of_mem (by rw [hw, hwr]; simp [searchOfState, inputControl]) hroom

theorem random_disjoint (h : SearchInput p original) :
    ∀ r ∈ original.wr ++ [below (original.gpr .rsp) 160], (inputRand original).Disjoint r := by
  obtain ⟨hc, _, _, hwr, _, hctrl, _, _, hstack, _⟩ := h.1
  obtain ⟨_, _, _, _, _, dor, _, _, dur, _, _, drs, _, _, _, _, _, _, _, _, _, _⟩ := hc
  intro r hr
  rw [hwr] at hr
  simp only [inputBuffers, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact dor.symm
  · exact dur.symm
  · exact drs
  · exact (hctrl (inputRand original) (by simp)).symm
  · exact (hstack (inputRand original) (by simp)).symm

theorem random_frame (h : SearchInput p original) {m m' : Mem}
    (hf : Frame (original.wr ++ [below (original.gpr .rsp) 160]) m m') :
    Spec.Rsa.bytesAt m' p.c.rp p.c.rand.length = Spec.Rsa.bytesAt m p.c.rp p.c.rand.length := by
  cases h.2
  change Spec.Rsa.bytesAt m' (original.gpr .r9) (pcRand original).length =
    Spec.Rsa.bytesAt m (original.gpr .r9) (pcRand original).length
  have hl : (pcRand original).length = (stackArg original 0).toNat := by
    simp only [pcRand, Spec.Rsa.bytesAt, List.length_map, List.length_range]
  rw [hl]
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  exact hf.bytes (h.random_disjoint) (Nat.le_of_lt (BitVec.isLt _)) (List.mem_range.mp hi)

theorem control_disjoint (h : SearchInput p original) :
    ∀ r ∈ inputBuffers original ++ [below (original.gpr .rsp) 160], (inputControl original).Disjoint r := by
  intro r hr
  obtain ⟨_, _, _, _, _, hd, _⟩ := h.1
  rcases List.mem_append.mp hr with hr | hr
  · exact hd _ (List.mem_append_left _ hr)
  · simp only [List.mem_singleton] at hr; subst r
    exact hd _ (by simp)

theorem control_frame (h : SearchInput p original) {m m' : Mem}
    (hf : Frame (inputBuffers original ++ [below (original.gpr .rsp) 160]) m m')
    (j : Nat) (hj : j < 16) : word m' p.control (8 * j) = word m p.control (8 * j) := by
  cases h.2
  exact hf.readW (r := inputControl original)
    (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
    h.control_disjoint (by decide)

end SearchInput

end VG.Proof.Ffdh.X86_64.Generation
