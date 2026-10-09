import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.MaskPairLoop

namespace VG.Proof.MlDsa.AArch64.Sign
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlDsa.Sign VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- What the commitment needs of the layout. -/
def cChk (p : Params) : Bool :=
  masksPairChk p && (List.range p.k).all (wChk p) && (List.range p.k).all (hChk p) &&
    hashChk (sgR p) (sgW p) [⟨.x26, 0, 64⟩, ⟨.x28, oW1, p.k * w1Len p⟩] ⟨.x28, oCT, cLen p⟩ &&
    icwChk p [(sc 0, 200), (sc 200, 640), (sc oCT, cLen p)] p.k

theorem cChk_ok {p : Params} (h : Ok3 p) : cChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

theorem commit_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : cChk p = true) {σ : State} {t : Nat}
    {s : State} (h : IL p D σ t s) : WP isa (commitWith keccak.callee P p) s (IC p D σ t) := by
  simp only [cChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨hm, hw⟩, hh⟩, hs⟩, hk⟩ := hc
  unfold commitWith
  refine WP.seq (WP.mono (masks_ok hP hm h) fun s1 hs1 => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun i => ICw p D σ t i) p.k 0
    (fun i _ hi s hs => rowW_ok hP (hw i (by omega)) (by omega) hs) s1
    ⟨hs1.l, hs1.y, hs1.yh, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s2 hs2 => ?_)
  rw [Nat.zero_add] at hs2
  refine WP.seq (WP.mono (seqR_ok (I := fun i => ICh p D σ t i) p.k 0
    (fun i _ hi s hs => w1R_ok hP (hh i (by omega)) (by omega) hs) s2
    ⟨hs2, by simp [w1Enc]; rfl⟩) fun s3 hs3 => ?_)
  rw [Nat.zero_add] at hs3
  refine WP.mono (shake_ok hP.s16 hP.s64 hs3.c.l.st.lay (by simp) hs) fun s4 ⟨hP4, _, hb⟩ =>
    ⟨hs3.c.step hP4 hk, ?_⟩
  rw [hP4.pa (by decide), hb]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
  show H (bytesAt s3.mem (pa s3 (.x26, 0)) 64 ++ bytesAt s3.mem (pa s3 (sc oW1)) (p.k * w1Len p)) (cLen p) = _
  rw [Nat.mul_comm p.k, hs3.w1, hs3.c.l.st.mu]
  simp only [CTv, ctF, w1Encode, List.flatMap_map]

end VG.Proof.MlDsa.AArch64.Sign
