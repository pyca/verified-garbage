module

public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.ForwardLoop
public import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Interleave

@[expose] public section
namespace VG.Proof.Gcm.AArch64.Stitch
open VG VG.AArch64 VG.Impl.Gcm.AArch64.Stitch

abbrev lanes : List (Reg × VReg × Nat) := vecSaves.map fun (v,r) => (r,v,0)
abbrev borrowed : List Reg := lanes.map Prod.fst

private theorem valid : ∀ k ∈ lanes, k.2.2 < 2 := by decide
private theorem coverage : ∀ v ∈ preservedV, ∃ r ∈ borrowed, (r,v,0) ∈ lanes := by decide

private theorem block_post {xs : List Instr} {s t : State} {tr : List Leak} {Q : State → Prop}
    (he : Exec isa (.block xs) s tr t) (h : WP isa (.block xs) s Q) : Q t := by
  obtain ⟨tr', t', e, hq⟩ := h
  cases he with | block a =>
    cases e with | block b =>
      rw [a] at b
      cases b
      exact hq

private theorem safe : ∀ q ∈ borrowed, forwardCore.allInstrs (fun i => !clobbers i q) = true := by decide +kernel

/-- Exact saves and restores; the AES and GHASH loop itself never uses these
volatile integer registers. This part holds for every successful execution. -/
theorem forwardSeal_preserves {s t : State} {tr : List Leak} (h : Exec isa forwardSeal s tr t) :
    ∀ v ∈ preservedV, (t.v v).extractLsb' 0 64 = (s.v v).extractLsb' 0 64 := by
  cases h with | seq se inner =>
    cases inner with | seq loop re =>
      obtain ⟨_, _, _, _, saved, _⟩ := block_post se (umovOf_ok lanes s valid (by decide))
      obtain ⟨_, _, _, _, _, restored, _⟩ := block_post re (insOf_ok lanes _ valid (by decide))
      intro v hv
      obtain ⟨r, hr, hk⟩ := coverage v hv
      have keep := Exec.gpr (r := r) (fun i hi => by
        have x := (List.all_eq_true.mp ((Code.allInstrs_eq _ _) ▸ safe r hr)) i hi
        simpa using x) loop (.inl (by decide +kernel))
      exact (restored _ hk).trans (keep.trans (saved _ hk))

private theorem save_pre {s a : State} (hp : SealToPre s) (hm : a.mem = s.mem)
    (hd : a.rd = s.rd) (hw : a.wr = s.wr) (hg : ∀ r, r ∉ borrowed → a.gpr r = s.gpr r) : SealToPre a := by
  have g15 := hg .x15 (by decide)
  have g19 := hg .x19 (by decide)
  have g20 := hg .x20 (by decide)
  have g21 := hg .x21 (by decide)
  have g22 := hg .x22 (by decide)
  have g23 := hg .x23 (by decide)
  have g26 := hg .x26 (by decide)
  exact {
    rounds := by simpa only [rounds, g22] using hp.rounds
    nb1 := by simpa only [nb, g26] using hp.nb1
    k_in := by simpa only [kc, hd, hw, g21] using hp.k_in
    y_in := by simpa only [stp, hw, g20] using hp.y_in
    c_in := by simpa only [stp, hw, g20] using hp.c_in
    d_in := by simpa only [dp, nb, hw, g23, g26] using hp.d_in
    t_in := by simpa only [wp, hd, hw, g19] using hp.t_in
    d_k := by simpa only [dR, kR, dp, nb, kc, g23, g26, g21] using hp.d_k
    d_y := by simpa only [dR, yR, dp, nb, stp, g23, g26, g20] using hp.d_y
    d_c := by simpa only [dR, cR, dp, nb, stp, g23, g26, g20] using hp.d_c
    d_t := by simpa only [dR, tR, dp, nb, wp, g23, g26, g19] using hp.d_t
    y_c := by simpa only [yR, cR, stp, g20] using hp.y_c
    wrap_d := by simpa only [dp, nb, g23, g26] using hp.wrap_d
    wrap_k := by simpa only [kc, g21] using hp.wrap_k
    wrap_t := by simpa only [wp, g19] using hp.wrap_t
    wrap_s := by simpa only [stp, g20] using hp.wrap_s
    tbl := by simpa only [wp, hk, kc, hm, g19, g21] using hp.tbl
    src_in := by simpa only [nb, hd, hw, g15, g26] using hp.src_in
    src_dst := by simpa only [dp, nb, dR, g15, g23, g26] using hp.src_dst
    wrap_src := by simpa only [nb, g15, g26] using hp.wrap_src
  }

theorem forwardSeal_ok {s : State} (hp : SealToPre s) (gh : Gh8Ok) :
    WP isa forwardSeal s (fun t => SealToPost s t (kRegsT true ++ borrowed)) := by
  refine WP.seq (WP.mono (umovOf_ok lanes s valid (by decide)) fun a ⟨hm,hd,hw,hs,_,hg⟩ => ?_)
  refine WP.seq (WP.mono (forwardCore_ok (save_pre hp hm hd hw hg) gh) fun b z => ?_)
  refine WP.mono (insOf_ok lanes b valid (by decide)) fun t ⟨tg,tm,td,tw,ts,_,_⟩ => ?_
  have g19 := hg .x19 (by decide)
  have g20 := hg .x20 (by decide)
  have g21 := hg .x21 (by decide)
  have g22 := hg .x22 (by decide)
  have g23 := hg .x23 (by decide)
  have g26 := hg .x26 (by decide)
  have g15 := hg .x15 (by decide)
  obtain ⟨data,ctr,hash,dst,src,frame,gr,sp,rd,wr⟩ := z
  refine ⟨?_,?_,?_,?_,?_,?_,fun r hr => ?_,ts.trans (sp.trans hs),td.trans (rd.trans hd),tw.trans (wr.trans hw)⟩
  · simpa only [tm, dp, nb, g23, g26, ciph, rounds, ksch, kc, g21, g22, hm, icb, stp, g20, g15] using data
  · simpa only [tm, stp, g20, nb, g26, icb, hm] using ctr
  · simpa only [tm, dp, g23, stp, g20, hk, kc, g21, hm, y₀, nb, g26] using hash
  · simpa only [tg, dp, nb, g23, g26] using dst
  · simpa only [tg, g15, nb, g26] using src
  · simpa only [tm, dR, yR, cR, stp, g20, dp, g23, nb, g26, hm] using frame
  · exact (congrFun tg r).trans ((gr r (fun h => hr (List.mem_append_left _ h))).trans
      (hg r (fun h => hr (List.mem_append_right _ h))))

theorem forwardCall_ok {s : State} (hp : SealToPre s) (gh : Gh8Ok) :
    WP isa forwardCall s (fun u => SealToPost s u ((kRegsT true ++ borrowed) ++ linkRegs)) := by
  have hp' : SealToPre s.callEntry := ⟨⟨hp.rounds, hp.nb1, hp.k_in, hp.y_in, hp.c_in, hp.d_in,
    hp.t_in, hp.d_k, hp.d_y, hp.d_c, hp.d_t, hp.y_c, hp.wrap_d, hp.wrap_k, hp.wrap_t, hp.wrap_s, hp.tbl⟩,
    hp.src_in, hp.src_dst, hp.wrap_src⟩
  obtain ⟨tr, u, run, h⟩ := forwardSeal_ok hp' gh
  refine ⟨_, _, Exec.call (call_callEntry s) run ?_, h.data, h.ctr, h.y, h.dst, h.src, h.frame, ?_, h.sp, h.rd, h.wr⟩
  · simp only [isa, ret, h.gpr .x30 (by decide), ite_true]
  · intro r hr
    exact (h.gpr r (fun h => hr (List.mem_append_left _ h))).trans
      (s.callEntry_gpr (fun h => hr (List.mem_append_right _ h)))

end VG.Proof.Gcm.AArch64.Stitch
