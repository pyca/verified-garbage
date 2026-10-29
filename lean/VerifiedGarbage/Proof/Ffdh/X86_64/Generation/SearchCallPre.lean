module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchArguments

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchContract
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ControlMemory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Contract
/-! # The verified candidate contract holds for every internal invocation -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/Generation/Outgoing.lean`, which only this module imported.
section

/-! # A private outgoing-argument frame for the native candidate operation -/

section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum

def outgoingSP (s : State) : Addr := s.gpr .rsp - 32

def referenceValues (s : State) : List (Nat × BitVec 64) :=
  [(1, stackArg s 0), (2, stackArg s 1), (3, stackArg s 2)]

def candidateReference (s : State) : State :=
  { s with
    gpr := fun r => if r = .rsp then outgoingSP s else s.gpr r
    mem := writeController s.mem (outgoingSP s) (referenceValues s)
    rd := [inputRand s, ⟨outgoingSP s + 8, 24⟩]
    wr := inputBuffers s }

theorem reference_rsp (s : State) : (candidateReference s).gpr .rsp = outgoingSP s := rfl

theorem reference_reg (s : State) (r : Reg) (h : r ≠ .rsp) :
    (candidateReference s).gpr r = s.gpr r := ite_eq_right h

theorem reference_arg (s : State) (j : Nat) (hj : j < 3) :
    stackArg (candidateReference s) j = stackArg s j := by
  change word (writeController s.mem (outgoingSP s) (referenceValues s)) (outgoingSP s) (8 * (j + 1)) = _
  have hv : ∀ e ∈ referenceValues s, e.1 < 16 := by
    simp only [referenceValues, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide
  rw [writeController_word _ _ _ hv _ (by omega_using [hj])]
  have he : j = 0 ∨ j = 1 ∨ j = 2 := by omega_using [hj]
  rcases he with rfl | rfl | rfl <;>
    simp only [controllerValue, referenceValues, List.foldl_cons, List.foldl_nil,
      Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false]

theorem outgoing_nat {s : State} (h : 32 ≤ (s.gpr .rsp).toNat) :
    (outgoingSP s).toNat = (s.gpr .rsp).toNat - 32 := by
  have he : (32 : BitVec 64) ≤ s.gpr .rsp := by
    change (32 : BitVec 64).toNat ≤ (s.gpr .rsp).toNat
    exact h
  rw [outgoingSP, BitVec.toNat_sub_of_le he]
  rfl

end VG.Proof.Ffdh.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/Generation/OutgoingPre.lean`, which only this module imported.
section

/-! # Candidate preconditions in the controller's private stack frame -/

section

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
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/Generation/CandidatePre.lean`, which only this module imported.
section

/-! # Reuse the candidate ABI on an unconsumed suffix of the random tape -/

section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

private theorem suffix_nowrap {p : Addr} {n used : Nat}
    (h : p.toNat + n ≤ 2 ^ 64) (hu : used ≤ n) :
    (p + BitVec.ofNat 64 used).toNat + (n - used) ≤ 2 ^ 64 := by
  have hn : n ≤ 2 ^ 64 := by omega_using [h]
  by_cases he : used = 2 ^ 64
  · have hp : p.toNat = 0 := by omega_using [h, hu, he]
    have hz : n - used = 0 := by omega_using [hn, hu, he]
    rw [hz, Nat.add_zero]
    exact Nat.le_of_lt (BitVec.isLt _)
  · have hul : used < 2 ^ 64 := by omega_using [hn, hu, he]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hul]
    by_cases hz : p.toNat + used < 2 ^ 64
    · rw [Nat.mod_eq_of_lt hz]
      omega_using [h, hu]
    · have eq : p.toNat + used = 2 ^ 64 := by omega_using [h, hu, hz]
      rw [eq, Nat.mod_self]
      omega_using [hn]

theorem candidate_pre_suffix {s t : State} (h : pcPre s) {used : Nat}
    (hu : used ≤ (stackArg s 0).toNat)
    (hsp : t.gpr .rsp = s.gpr .rsp)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rsi)
    (hdx : t.gpr .rdx = s.gpr .rdx) (hcx : t.gpr .rcx = s.gpr .rcx)
    (hgen : (t.gpr .r8).setWidth 32 = (s.gpr .r8).setWidth 32)
    (hrand : t.gpr .r9 = s.gpr .r9 + BitVec.ofNat 64 used)
    (ha0 : stackArg t 0 = BitVec.ofNat 64 ((stackArg s 0).toNat - used))
    (ha1 : stackArg t 1 = stackArg s 1) (ha2 : stackArg t 2 = stackArg s 2)
    (hrd : t.rd = [⟨t.gpr .r9, (stackArg t 0).toNat⟩, ⟨stackArgAddr t 0, 24⟩])
    (hwr : t.wr = [⟨t.gpr .rdi, (t.gpr .rsi).toNat⟩, ⟨t.gpr .rdx, 8⟩,
      ⟨stackArg t 1, (stackArg t 2).toNat * 8⟩]) : pcPre t := by
  obtain ⟨hspb, hspl, _, _, dou, dor, dos, doa, dur, dus, dua, drs, dsa,
    dro, dru, drr, drs', dra, dbo, dbu, dbr, dbs, dba,
    hwo, hwu, hwrand, hws, hb1, hb2, hlen, hg, hroom⟩ := h
  have hu64 : (stackArg s 0).toNat - used < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) (BitVec.isLt _)
  have hlen0 : (stackArg t 0).toNat = (stackArg s 0).toNat - used := by
    rw [ha0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu64]
  have hsub : Region.Sub
      ⟨s.gpr .r9 + BitVec.ofNat 64 used, (stackArg s 0).toNat - used⟩
      ⟨s.gpr .r9, (stackArg s 0).toNat⟩ :=
    Offset.sub_base _ (by omega_using [hu])
  have hargs : stackArgAddr t 0 = stackArgAddr s 0 := by
    simp only [stackArgAddr, hsp]
  unfold pcPre
  simp only [hsp, hdi, hsi, hdx, hcx, hgen, hrand, ha1, ha2, hlen0, hargs]
  refine ⟨hspb, hspl, ?_, ?_, dou, dor.sub_right hsub, dos, doa,
    dur.sub_right hsub, dus, dua, drs.sub_left hsub, dsa,
    dro, dru, drr.sub_right hsub, drs', dra, dbo, dbu, dbr.sub_right hsub, dbs, dba,
    hwo, hwu, suffix_nowrap hwrand hu, hws, hb1, hb2, hlen, hg, hroom⟩
  · simpa only [hrand, hlen0, hargs] using hrd
  · simpa only [hdi, hsi, hdx, ha1, ha2] using hwr

end VG.Proof.Ffdh.X86_64.Generation
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate

def callReads (p : SearchPublic) (used : Nat) : List Region :=
  [⟨off p.c.rp used, p.c.rand.length - used⟩, ⟨p.c.sp - 32 + 8, 24⟩]

def callWrites (p : SearchPublic) : List Region :=
  [⟨p.c.op, p.c.k⟩, ⟨p.c.up, 8⟩, ⟨p.c.B, p.c.Z⟩]

theorem searchCallValues_bound (p : SearchPublic) (used : Nat) :
    ∀ e ∈ searchCallValues p used, e.1 < 16 := by
  simp only [searchCallValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide

theorem search_call_args {p : SearchPublic} {s t : State} {used : Nat}
    (hsp : t.gpr .rsp = s.gpr .rsp - 32)
    (hm : t.mem = writeController s.mem (s.gpr .rsp - 32) (searchCallValues p used))
    (j : Nat) (hj : j < 3) :
    stackArg t j = match j with
      | 0 => BitVec.ofNat 64 (p.c.rand.length - used)
      | 1 => p.c.B
      | _ => BitVec.ofNat 64 (p.c.Z / 8) := by
  change word t.mem (t.gpr .rsp) (8 * (j + 1)) = _
  rw [hsp, hm, writeController_word _ _ _ (searchCallValues_bound p used) _ (by omega_using [hj])]
  have he : j = 0 ∨ j = 1 ∨ j = 2 := by omega_using [hj]
  rcases he with rfl | rfl | rfl <;>
    simp only [searchCallValues, controllerValue, List.foldl_cons, List.foldl_nil,
      Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false]

theorem search_call_pre {p : SearchPublic} {original s t : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (ha : SearchArgs p used t)
    (hm : t.mem = writeController s.mem (s.gpr .rsp - 32) (searchCallValues p used))
    (k : Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11] (allocated 32 s) t) :
    pcPre (t.withRegions (callReads p used) (callWrites p)) := by
  have hsp : t.gpr .rsp = s.gpr .rsp - 32 := k.gpr (by decide)
  have ha0 : stackArg t 0 = BitVec.ofNat 64 (p.c.rand.length - used) :=
    search_call_args hsp hm 0 (by decide)
  have ha1 : stackArg t 1 = p.c.B := search_call_args hsp hm 1 (by decide)
  have ha2 : stackArg t 2 = BitVec.ofNat 64 (p.c.Z / 8) := search_call_args hsp hm 2 (by decide)
  have hargs (j : Nat) : stackArg (t.withRegions (callReads p used) (callWrites p)) j = stackArg t j := rfl
  have hin := h.input
  cases hin.2
  have hu : used ≤ (stackArg original 0).toNat := by
    simpa only [searchOfState, SearchPublic.c, candidateOfState, pcRand,
      Spec.Rsa.bytesAt, List.length_map, List.length_range] using h.used_le
  have hsp' : s.gpr .rsp = original.gpr .rsp := h.rsp
  obtain ⟨hdi, hsi, hdx, hcx, hgen, hrand⟩ := ha
  refine candidate_pre_suffix (outgoing_pre hin.1) (used := used) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals try simp only [State.withRegions_gpr, hargs]
  · simpa only [reference_arg original 0 (by decide)] using hu
  · exact hsp.trans (congrArg (fun sp => sp - 32) hsp')
  · exact hdi
  · simpa only [searchOfState, SearchPublic.c, candidateOfState, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      reference_reg original .rsi (by decide)]
      using hsi
  · exact hdx
  · simpa only [searchOfState, SearchPublic.c, candidateOfState, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      reference_reg original .rcx (by decide)]
      using hcx
  · rw [hgen]
    simp only [searchOfState, SearchPublic.c, candidateOfState, reference_reg original .r8 (by decide),
      BitVec.ofNat_toNat]
    exact BitVec.setWidth_setWidth_of_le _ (by decide)
  · exact hrand
  · simpa only [searchOfState, SearchPublic.c, candidateOfState, pcRand, Spec.Rsa.bytesAt,
      List.length_map, List.length_range, reference_arg original 0 (by decide)] using ha0
  · simpa only [searchOfState, SearchPublic.c, candidateOfState, reference_arg original 1 (by decide)]
      using ha1
  · simpa only [searchOfState, SearchPublic.c, candidateOfState, Nat.mul_div_cancel _ (by decide : 0 < 8),
      BitVec.ofNat_toNat, BitVec.setWidth_eq, reference_arg original 2 (by decide)] using ha2
  · change callReads _ used = _
    simp only [callReads, hrand, ha0, stackArgAddr, State.withRegions_gpr, hsp, hsp',
      searchOfState, SearchPublic.c, candidateOfState, pcRand, Spec.Rsa.bytesAt,
      List.length_map, List.length_range, Nat.zero_add, Nat.mul_one, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_using [(stackArg original 0).isLt])]
    rfl
  · change callWrites _ = _
    simp only [callWrites, hdi, hsi, hdx, ha1, ha2,
      searchOfState, SearchPublic.c, candidateOfState, Nat.mul_div_cancel _ (by decide : 0 < 8),
      BitVec.ofNat_toNat, BitVec.setWidth_eq]

end VG.Proof.Ffdh.X86_64.Generation
