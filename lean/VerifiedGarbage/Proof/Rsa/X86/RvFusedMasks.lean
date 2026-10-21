module

public import VerifiedGarbage.Proof.Rsa.X86.RvFusedFlags
import Mathlib.Tactic.SplitIfs

/-! Root detection flags in the fused pass. -/
@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Impl.Rsa.X86.Recover VG.Proof.Mont.X86
open VG.Proof.Rsa (b2n)
open VG.Proof.Rsa.X86.Keys (upd)

def fusedVH (V : Nat → Nat) (dn ok bit e1 e2 : Bool) : Nat → Nat :=
  upd (upd (upd (upd V sMask (b2n (!bit)))
    sLive (b2n (!dn && e1 && !bit))) sOk (b2n ((ok || (!dn && e1 && !bit)) && !bit)))
    sDone (b2n ((dn || e1 || e2) && !bit))

theorem fusedHit_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {live liveW ls : List Nat}
    {dn ok bit e1 e2 : Bool}
    (h : KS g s0 A live AW liveW V ls s)
    (ld : sDone ∈ ls) (lo : sOk ∈ ls) (lb : sBit ∈ ls) (l1 : sE1 ∈ ls) (l2 : sE2 ∈ ls)
    (vd : V sDone = b2n dn) (vo : V sOk = b2n ok) (vb : V sBit = b2n bit)
    (v1 : V sE1 = b2n e1) (v2 : V sE2 = b2n e2) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.fusedHit s fun t =>
      KS g s0 A live AW liveW (fusedVH V dn ok bit e1 e2)
        ([sDone,sOk,sLive,sMask] ++ ls) t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.fusedHit
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine WP.seq (WP.mono (h.flagNot_ok (d := sLive) (a := sDone) (x := dn) (by decide) (by simp [ld]) vd) fun u1 h1 => ?_)
  refine WP.seq (WP.mono (h1.flagAnd_ok (d := sLive) (a := sLive) (b := sE1) (x := !dn) (y := e1) (by decide) (by simp) (by simp [l1]) rfl v1) fun u2 h2 => ?_)
  refine WP.seq (WP.mono (h2.flagNot_ok (d := sMask) (a := sBit) (x := bit) (by decide) (by simp [lb]) vb) fun u3 h3 => ?_)
  refine WP.seq (WP.mono (h3.flagAnd_ok (d := sLive) (a := sLive) (b := sMask) (x := !dn && e1) (y := !bit) (by decide) (by simp) (by simp) rfl rfl) fun u4 h4 => ?_)
  refine WP.seq (WP.mono (h4.flagOr_ok (d := sOk) (a := sOk) (b := sLive) (x := ok) (y := !dn && e1 && !bit) (by decide) (by simp [lo]) (by simp) vo rfl) fun u5 h5 => ?_)
  refine WP.seq (WP.mono (h5.flagAnd_ok (d := sOk) (a := sOk) (b := sMask) (x := ok || (!dn && e1 && !bit)) (y := !bit) (by decide) (by simp) (by simp) rfl rfl) fun u6 h6 => ?_)
  refine WP.seq (WP.mono (h6.flagOr_ok (d := sDone) (a := sDone) (b := sE1) (x := dn) (y := e1) (by decide) (by simp [ld]) (by simp [l1]) vd v1) fun u7 h7 => ?_)
  refine WP.seq (WP.mono (h7.flagOr_ok (d := sDone) (a := sDone) (b := sE2) (x := dn || e1) (y := e2) (by decide) (by simp) (by simp [l2]) rfl v2) fun u8 h8 => ?_)
  refine WP.mono (h8.flagAnd_ok (d := sDone) (a := sDone) (b := sMask) (x := dn || e1 || e2) (y := !bit) (by decide) (by simp) (by simp) rfl rfl) fun t ht => ?_
  refine ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩) fun d hd => ⟨?_, ?_⟩
  · rcases List.mem_append.mp hd with hd | hd
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> simp
    · simp [hd]
  ·
    dsimp only [fusedVH, upd, sLive, sMask, sOk, sDone]
    split_ifs <;> simp_all

end VG.Proof.Rsa.X86.Recover
