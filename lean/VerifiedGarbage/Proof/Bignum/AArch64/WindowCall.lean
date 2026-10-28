module

public import VerifiedGarbage.Impl.Rsa.AArch64.WindowCall
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
public import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowCall
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowCall
open VG.Proof.Bignum.AArch64.WindowFive

theorem save_ok (s : State) : WP isa (.block save) s fun t =>
    t.mem = s.mem ∧ (t.v .v7).extractLsb' 0 64 = s.gpr .x30 ∧ Keep [] s t := by
  refine WP.mono (WP.keep [] (c := .block save)
    (Q := fun t => t.mem = s.mem ∧ (t.v .v7).extractLsb' 0 64 = s.gpr .x30) ?_ rfl rfl rfl)
    (fun _ ⟨⟨hm, hv⟩, hk⟩ => ⟨hm, hv, hk⟩)
  apply WP.of_runBlock
  simp only [save, runBlock_cons, exec_ins (show 0 < 2 by decide), runStep_some,
    runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_⟩
  simpa only [RegUpd.v_setV_self, Nat.mul_zero, ite_true] using
    (extract_setLane64 (s.v .v7) (s.gpr .x30) (i := 0) (j := 0) (by decide) (by decide))

theorem restore_ok (s : State) : WP isa (.block restore) s fun t =>
    t.mem = s.mem ∧ t.gpr .x30 = (s.v .v7).extractLsb' 0 64 ∧ Keep [.x30] s t := by
  refine WP.mono (WP.keep [.x30] (c := .block restore)
    (Q := fun t => t.mem = s.mem ∧ t.gpr .x30 = (s.v .v7).extractLsb' 0 64) ?_ rfl rfl rfl)
    (fun _ ⟨⟨hm, hv⟩, hk⟩ => ⟨hm, hv, hk⟩)
  apply WP.of_runBlock
  simp only [restore, runBlock_cons, exec_umov (show 0 < 2 by decide), runStep_some,
    runBlock_nil, Option.some.injEq, exists_eq_left', laneOf, Nat.mul_zero]
  exact ⟨rfl, by simp only [RegUpd.gpr_write, ite_true, BitVec.setWidth_eq]⟩

theorem context_callEntry {s : State} {P : Addr} {w : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) : TableCtx s.callEntry P w mi X Xc :=
  hc.of_win (Frm.refl _ _ _) rfl (State.callEntry_gpr s (by decide))

theorem call_ok (W : Window) {name : String} {s : State} {P : Addr} {w : Nat}
    {mi : BitVec 64} {X Xc x E v : Nat} {Q : Prop}
    (hv : ∀ i ∈ instrs W.code, vdstOf i ≠ some .v7)
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X Q x)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hy : wv s.mem P (slot w Public.aY) w < X)
    (hyv : Q → wv s.mem P (slot w Public.aY) w % X = x ^ E * 2 ^ (64 * w) % X)
    (hd : v < 32) (hn : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (VG.Impl.Rsa.AArch64.WindowCall.call name W.code) s
      (WindowPost s P w mi X Xc Q x E v) := by
  unfold VG.Impl.Rsa.AArch64.WindowCall.call
  refine WP.seq (WP.mono (save_ok s) fun u ⟨hm,hl,ku⟩ => ?_)
  have fu : Frm P (crtWinRanges w) s.mem u.mem := hm.symm ▸ Frm.refl _ _ _
  have cu := hc.of_win fu ku.wr (ku.gpr .x0 (by simp))
  obtain ⟨tr,a,he,ca,ta,ya,va,fa,ka,na,ba,ha⟩ := W.ok (context_callEntry cu)
    (by simpa only [State.callEntry_mem,hm] using ht) hw hw' hR
    (by simpa only [State.callEntry_mem,hm] using hy)
    (by simpa only [State.callEntry_mem,hm] using hyv) hd
    (by simpa only [State.callEntry_mem,hm] using hn)
  have lr := ka.gpr .x30 (by decide)
  have hret : isa.ret u.callEntry a = some a := by
    simp only [isa,ret,lr,ite_true]
  have ex := Exec.call (name := name) (call_callEntry u) he hret
  refine WP.seq (show WP isa (.call name W.code) u _ from ⟨_,_,ex,?_⟩)
  refine WP.mono (restore_ok a) fun t ⟨hm',hl',kt⟩ => ?_
  have v7 : a.v .v7 = u.v .v7 := (Exec.vec hv he).trans rfl
  have ht30 : t.gpr .x30 = s.gpr .x30 := by rw [hl',v7,hl]
  have kout : Keep mmRegs s t := by
    refine ⟨?_,kt.rd.trans (ka.rd.trans ku.rd),kt.wr.trans (ka.wr.trans ku.wr),
      kt.sp.trans (ka.sp.trans ku.sp),?_⟩
    · intro r hr
      by_cases h30 : r = .x30
      · subst r; exact ht30
      have hnlink : r ∉ linkRegs := by
        intro h
        simp only [linkRegs,List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with rfl | rfl | rfl
        all_goals first | exact h30 rfl | exact hr (by decide)
      rw [kt.gpr r (by simpa using h30),ka.gpr r hr,State.callEntry_gpr u hnlink,
        ku.gpr r (by simp)]
    · intro r hr
      exact (kt.vcs r hr).trans ((ka.vcs r hr).trans (ku.vcs r hr))
  have ft : Frm P (crtWinRanges w) a.mem t.mem := hm'.symm ▸ Frm.refl _ _ _
  refine ⟨ca.of_win ft kt.wr (kt.gpr .x0 (by decide)),hm'.symm ▸ ta,hm'.symm ▸ ya,
    ?_,?_,kout,hm'.symm ▸ na,hm'.symm ▸ ba,?_⟩
  · simpa only [hm'] using va
  · simpa only [State.callEntry_mem,hm,hm'] using fa
  · intro k hk h1 h2 h3 h4
    simpa only [State.callEntry_mem,hm,hm'] using ha k hk h1 h2 h3 h4

end VG.Proof.Bignum.AArch64.WindowCall
