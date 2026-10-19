module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.Outgoing
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Depth

/-! # Candidate preconditions in the controller's private stack frame -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem outgoing_pre {s : State} (h : searchPre s) : pcPre (candidateReference s) := by
  obtain ⟨hc, _, _, _, _, _, _, hsp, hspace, _⟩ := h
  obtain ⟨_, _, _, _, dou, dor, dos, _, dur, dus, _, drs, _, _, _, _, _, _, _, _, _, _, _,
    hwo, hwu, hwr, hws, hb1, hb2, hlen, hgen, hroom⟩ := hc
  have hn := outgoing_nat (by omega_using [hsp] : 32 ≤ (s.gpr .rsp).toNat)
  have hret : Region.Sub ⟨outgoingSP s, 8⟩ (below (s.gpr .rsp) 160) :=
    Offset.sub_below _ (by decide) (by decide)
  have harg : outgoingSP s + 8 = s.gpr .rsp - 24 := by
    exact (Offset.sub_ofNat_eq (s.gpr .rsp) (a := 24) (b := 32) (by decide)).symm
  have hargs : Region.Sub ⟨outgoingSP s + 8, 24⟩ (below (s.gpr .rsp) 160) := by
    rw [harg]
    exact Offset.sub_below _ (by decide) (by decide)
  have hbelow : Region.Sub (below (outgoingSP s) 128) (below (s.gpr .rsp) 160) :=
    below_below (s.gpr .rsp) 32 128
  have hbuf : ∀ r ∈ inputBuffers s, (below (s.gpr .rsp) 160).Disjoint r :=
    fun r hr => hspace r (List.mem_append_left _ hr)
  have ho := hbuf ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ (by simp [inputBuffers])
  have hu := hbuf ⟨s.gpr .rdx, 8⟩ (by simp [inputBuffers])
  have hs := hbuf ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩ (by simp [inputBuffers])
  have hr := hspace (inputRand s) (by simp)
  have hregs : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9],
      (candidateReference s).gpr r = s.gpr r := by
    intro r hmem
    apply reference_reg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have ha : stackArgAddr (candidateReference s) 0 = outgoingSP s + 8 := rfl
  have hrd : (candidateReference s).rd = [inputRand s, ⟨outgoingSP s + 8, 24⟩] := rfl
  have hwr' : (candidateReference s).wr = inputBuffers s := rfl
  unfold pcPre
  simp only [reference_rsp, hregs .rdi (by simp), hregs .rsi (by simp), hregs .rdx (by simp),
    hregs .rcx (by simp), hregs .r8 (by simp), hregs .r9 (by simp),
    reference_arg s 0 (by decide), reference_arg s 1 (by decide), reference_arg s 2 (by decide),
    ha, hrd, hwr', inputRand, inputBuffers]
  refine ⟨?_, ?_, True.intro, True.intro, dou, dor, dos, (ho.sub_left hargs).symm, dur, dus,
    (hu.sub_left hargs).symm, drs, (hs.sub_left hargs).symm,
    ho.sub_left hret, hu.sub_left hret, hr.sub_left hret, hs.sub_left hret,
    ?_, ho.sub_left hbelow, hu.sub_left hbelow, hr.sub_left hbelow, hs.sub_left hbelow,
    ?_, hwo, hwu, hwr, hws, hb1, hb2, hlen, hgen, hroom⟩
  · rw [hn]
    omega_using [(s.gpr .rsp).isLt, hsp]
  · rw [hn]
    omega_using [hsp]
  · exact Offset.base_disjoint (outgoingSP s) (e := 8) (n := 24) (k := 8) (by decide) (by decide)
  · exact (Offset.disjoint_below (outgoingSP s) (n := 128) (d := 8) (k := 24) (by decide)).symm

end VG.Proof.Ffdh.X86_64.Generation
