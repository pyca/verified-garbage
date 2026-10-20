module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchDone
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ControlMemory
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchMemory

/-! # Terminal controller writes preserve the accepted output and saved ABI -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem controller_output {p : SearchPublic} {original : State} (h : SearchInput p original)
    {m m' : Mem} (hf : Frame [⟨p.control, 128⟩] m m') :
    Spec.Rsa.bytesAt m' p.c.op p.c.k = Spec.Rsa.bytesAt m p.c.op p.c.k := by
  have hd : (⟨p.c.op, p.c.k⟩ : Region).Disjoint ⟨p.control, 128⟩ := by
    cases h.2
    exact (h.1.2.2.2.2.2.1 _ (List.mem_append_left _ (List.mem_cons_self ..))).symm
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  exact hf.bytes (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hd)
    (Nat.le_of_lt h.length_lt) (List.mem_range.mp hi)

theorem done_update {p : SearchPublic} {original s t : State} {used remaining : Nat}
    {result : Spec.Ffdh.ParameterSearchResult} (h : SearchLive p original used remaining s)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 16)
    (hkeep : ∀ j ∈ [4, 5, 7], ∀ e ∈ values, j ≠ e.1)
    (hm : t.mem = writeController s.mem p.control values)
    (hread : t.rd = s.rd) (hwrite : t.wr = s.wr)
    (hg : ∀ reg ∈ calleeSaved, t.gpr reg = s.gpr reg)
    (hused : word t.mem p.control 96 = BitVec.ofNat 64 result.used)
    (hstatus : word t.mem p.control 112 = BitVec.ofNat 64 result.status)
    (hpolicy : Spec.Rsa.wordsAt t.mem p.control 4 =
      [BitVec.ofNat 64 result.remaining, BitVec.ofNat 64 p.c.k,
        BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits), BitVec.ofNat 64 result.requested])
    (hout : SearchOutput p result s.mem) : SearchDone p original result t := by
  have hw (j : Nat) (hj : j ∈ [4, 5, 7]) :
      word t.mem p.control (8 * j) = word s.mem p.control (8 * j) := by
    have hbound : j < 16 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> decide
    rw [hm, writeController_word _ _ _ hb j hbound, controllerValue_unchanged _ _ _ (hkeep j hj)]
  refine ⟨h.input, hread.trans h.rd, hwrite.trans h.wr,
    (hg .rsp (by decide)).trans h.rsp, (hg .r12 (by decide)).trans h.r12,
    fun reg hr hn => (hg reg hr).trans (h.saved reg hr hn), ?_, ?_, ?_, hused, hstatus, hpolicy, ?_⟩
  · exact (hw 4 (by decide)).trans h.savedR12
  · exact (hw 5 (by decide)).trans (h.headers (5, p.c.op) (by simp [SearchPublic.headers]))
  · exact (hw 7 (by decide)).trans (h.headers (7, p.c.up) (by simp [SearchPublic.headers]))
  · change Spec.Rsa.bytesAt t.mem p.c.op p.c.k = _
    rw [hm, controller_output h.input (writeController_frame _ _ _ hb)]
    exact hout

end VG.Proof.Ffdh.X86_64.Generation
