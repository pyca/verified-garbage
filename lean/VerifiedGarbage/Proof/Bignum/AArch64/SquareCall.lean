module

public import VerifiedGarbage.Impl.Bignum.AArch64.SquareCall
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section

namespace VG.Proof.Bignum.AArch64.SquareCall
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.AArch64.SquareCall

theorem save_ok (s : State) : WP isa (.block save) s fun t =>
    t.mem = s.mem ∧ (t.v .v31).extractLsb' 0 64 = s.gpr .x30 ∧ Keep [] s t := by
  refine WP.mono (WP.keep [] (c := .block save)
    (Q := fun t => t.mem = s.mem ∧ (t.v .v31).extractLsb' 0 64 = s.gpr .x30) ?_ rfl rfl rfl)
    (fun _ ⟨⟨hm, hv⟩, hk⟩ => ⟨hm, hv, hk⟩)
  apply WP.of_runBlock
  simp only [save, runBlock_cons, exec_ins (show 0 < 2 by decide), runStep_some,
    runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_⟩
  simpa only [RegUpd.v_setV_self, Nat.mul_zero, ite_true] using
    (extract_setLane64 (s.v .v31) (s.gpr .x30) (i := 0) (j := 0) (by decide) (by decide))

theorem restore_ok (s : State) : WP isa (.block restore) s fun t =>
    t.mem = s.mem ∧ t.gpr .x30 = (s.v .v31).extractLsb' 0 64 ∧ Keep [.x30] s t := by
  refine WP.mono (WP.keep [.x30] (c := .block restore)
    (Q := fun t => t.mem = s.mem ∧ t.gpr .x30 = (s.v .v31).extractLsb' 0 64) ?_ rfl rfl rfl)
    (fun _ ⟨⟨hm, hv⟩, hk⟩ => ⟨hm, hv, hk⟩)
  apply WP.of_runBlock
  simp only [restore, runBlock_cons, exec_umov (show 0 < 2 by decide), runStep_some,
    runBlock_nil, Option.some.injEq, exists_eq_left', laneOf, Nat.mul_zero]
  exact ⟨rfl, by simp only [RegUpd.gpr_write, ite_true, BitVec.setWidth_eq]⟩

theorem good_callEntry {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) : Good s.callEntry B Z w minv :=
  ⟨hg.scr.congr rfl, (State.callEntry_gpr s (by decide)).trans hg.x0, hg.hdr⟩

/-- Outlining does not require any stronger arithmetic precondition. -/
theorem call_ok (M : Mont) {name : String} {s : State} {B : Addr} {Z w : Nat}
    {minv : BitVec 64} {o a b : Nat}
    (hv : ∀ i ∈ instrs (M.mm o a b), vdstOf i ≠ some .v31)
    (hg : Good s B Z w minv) (hz : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (d1 : o ≠ Public.aAcc) (d2 : o ≠ Public.aTmp)
    (d3 : a ≠ Public.aAcc) (d4 : a ≠ Public.aTmp)
    (d5 : b ≠ Public.aAcc) (d6 : b ≠ Public.aTmp)
    (hinv : ((word s.mem B (slot w Public.aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w Public.aN) w) :
    WP isa (VG.Impl.Bignum.AArch64.SquareCall.call name (M.mm o a b)) s fun t =>
      Good t B Z w minv ∧ wv t.mem B (slot w o) w < wv s.mem B (slot w Public.aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w Public.aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w Public.aN) w ∧
      Arrays B w [Public.aAcc, Public.aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold VG.Impl.Bignum.AArch64.SquareCall.call
  refine WP.seq (WP.mono (save_ok s) fun u ⟨hm, hl, ku⟩ => ?_)
  have hgu : Good u B Z w minv :=
    ⟨hg.scr.congr ku.wr, (ku.gpr .x0 (by simp)).trans hg.x0, hm ▸ hg.hdr⟩
  have hinvu : ((word u.callEntry.mem B (slot w Public.aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [State.callEntry_mem, hm]; exact hinv
  have hbu : wv u.callEntry.mem B (slot w b) w < wv u.callEntry.mem B (slot w Public.aN) w := by
    rw [State.callEntry_mem, hm]; exact hB
  obtain ⟨tr, v, he, hgv, hn, heq, hf, kv⟩ :=
    M.ok (good_callEntry hgu) hz hw hw' ho ha hb d1 d2 d3 d4 d5 d6 hinvu hbu
  have lr := kv.gpr .x30 (by decide)
  have hret : isa.ret u.callEntry v = some v := by
    simp only [isa, ret, lr, ite_true]
  have hc := Exec.call (name := name) (call_callEntry u) he hret
  refine WP.seq (show WP isa (.call name (M.mm o a b)) u _ from ⟨_, _, hc, ?_⟩)
  refine WP.mono (restore_ok v) fun t ⟨hm', hl', kt⟩ => ?_
  have v31 : v.v .v31 = u.v .v31 := (Exec.vec hv he).trans rfl
  have ht30 : t.gpr .x30 = s.gpr .x30 := by rw [hl', v31, hl]
  have kout : Keep mmRegs s t := by
    refine ⟨?_, kt.rd.trans (kv.rd.trans ku.rd), kt.wr.trans (kv.wr.trans ku.wr),
      kt.sp.trans (kv.sp.trans ku.sp), ?_⟩
    · intro r hr
      by_cases h30 : r = .x30
      · subst r; exact ht30
      have hnlink : r ∉ linkRegs := by
        intro h
        simp only [linkRegs, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl
        all_goals first | exact h30 rfl | exact hr (by decide)
      rw [kt.gpr r (by simpa using h30), kv.gpr r hr, State.callEntry_gpr u hnlink,
        ku.gpr r (by simp)]
    · intro r hr
      exact (kt.vcs r hr).trans ((kv.vcs r hr).trans (ku.vcs r hr))
  simp only [State.callEntry_mem, hm] at hn heq hf
  refine ⟨⟨hgv.scr.congr kt.wr, (kt.gpr .x0 (by decide)).trans hgv.x0, hm' ▸ hgv.hdr⟩,
    ?_, ?_, ?_, kout⟩
  · rw [hm']; exact hn
  · rw [hm']; exact heq
  · rw [hm']; exact hf

end VG.Proof.Bignum.AArch64.SquareCall
