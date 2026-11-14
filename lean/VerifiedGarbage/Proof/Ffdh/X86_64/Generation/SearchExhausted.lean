module

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchTerminate
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchData
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRestore
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchMemory
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ZeroOut
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchDone

/-! ### `Ffdh.X86_64.Generation.SearchClear`, which only this module used -/

section

/-! # Clearing a failed search preserves the native controller -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem search_clear {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (hdi : s.gpr .rdi = p.control) :
    WP isa (VG.Impl.Rsa.X86_64.Keys.zeroOut 5 6) s fun t =>
      SearchLive p original used remaining t ∧
      Spec.Rsa.bytesAt t.mem p.c.op p.c.k = List.replicate p.c.k 0 ∧
      (∀ j < 16, word t.mem p.control (8 * j) = word s.mem p.control (8 * j)) ∧
      Keep [.rsi, .rcx, .rax] s t := by
  have hk := h.input.width_bounds
  have scr := h.input.control_scr h.wr
  refine WP.mono (controller_zero_out scr hdi (by decide) (by decide) (by decide)
    (h.headers (5, p.c.op) (by simp [SearchPublic.headers]))
    (h.headers (6, BitVec.ofNat 64 p.c.k) (by simp [SearchPublic.headers]))
    (by omega_using [hk.1]) (by omega_using [hk.2]) (h.input.output h.wr))
    fun t ⟨hv, hf, k⟩ => ?_
  have hframe : Frame (inputBuffers original ++ [below (original.gpr .rsp) 160]) s.mem t.mem := by
    intro a ha
    apply hf
    intro i hi he
    have hr : (⟨p.c.op, p.c.k⟩ : Region) ∈ inputBuffers original := by
      cases h.input.2
      exact List.mem_cons_self ..
    apply ha _ (List.mem_append_left _ hr)
    rw [he]
    exact contains_byte _ (by omega_using [hi]) (by omega_using [hi, h.input.length_lt])
  refine ⟨h.restore k.2.1 k.2.2 (fun r hr => k.gpr (by cases r <;> simp_all [calleeSaved])) hframe,
    ?_, h.input.control_frame hframe, k⟩
  refine List.eq_replicate_iff.mpr ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range], ?_⟩
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact hv i (List.mem_range.mp hi)

end VG.Proof.Ffdh.X86_64.Generation

end

end


/-! # Exhausted native searches return zero output and a terminal controller -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem search_exhausted {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    WP isa exhausted s (SearchDone p original (.exhausted used)) := by
  unfold exhausted
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (search_terminal h 3) fun u ⟨h0, hq, hs⟩ => ?_
  have hmov : WP isa (.block [.mov .rdi (.reg .r12)]) u fun v =>
      (v.gpr .rdi = p.control ∧ v.mem = u.mem) ∧ Keep [.rdi] u v := by
    refine WP.keep [.rdi] ?_ rfl
    xrun [h0.r12]
  refine WP.mono hmov fun v ⟨⟨hdv, hmv⟩, kv⟩ => ?_
  have hv := h0.keep kv hmv (by decide)
  refine WP.mono (search_clear hv hdv) fun t ⟨ht, hout, hw, _⟩ => ?_
  refine done_of_live ht rfl rfl ?_ ?_ hout
  · have hs' : word v.mem p.control 112 = BitVec.ofNat 64 3 := by rw [hmv]; exact hs
    exact (hw 14 (by decide)).trans hs'
  · have hq' : word v.mem p.control 24 = BitVec.ofNat 64 0 := by rw [hmv]; exact hq
    exact (hw 3 (by decide)).trans hq'

end VG.Proof.Ffdh.X86_64.Generation
