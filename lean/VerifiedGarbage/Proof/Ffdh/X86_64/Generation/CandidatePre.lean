module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # Reuse the candidate ABI on an unconsumed suffix of the random tape -/

@[expose] public section

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
