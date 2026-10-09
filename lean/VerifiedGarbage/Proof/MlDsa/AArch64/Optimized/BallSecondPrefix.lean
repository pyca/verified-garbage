import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallSecondCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallChunkTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.Sha3 (bytesAt stateAt)

def secondPrefix (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .seq (.block (([.str .x .x9 .x25 1800,.str .x .x10 .x25 1808,.str .x .x11 .x25 1816] : List VG.AArch64.Instr) ++ args))
    (.seq (.call ("vg_keccak_squeeze_scratch"++c.suffix) (Impl.Sha3.AArch64.Stream.squeezeWith c)) (.block restore))

structure PrefixPost (P : Sp) (σ : State) (c : Spec.MlDsa.IPoly) (i : Nat) (w : BitVec 64) (Y : List Byte) (s : State) : Prop where
  env : Env P σ s
  ready : ChunkReady P.a (P.at' 840) c i w Y s

theorem secondPrefix_ok (v : Proof.Sha3.AArch64.Permutation) {P : Sp} {σ s : State}
    {i : Nat} {c : Spec.MlDsa.IPoly} {w : BitVec 64} {Y : List Byte}
    (hp : SpOk P σ) (he : Env P σ s) (hparser : Parser P.a c i w s)
    (hY : Y.length=136) (hpos : (s.gpr .x0).toNat≤136)
    (hn : Spec.Sha3.squeezeFrom 136 (stateAt s.mem P.scr) (s.gpr .x0).toNat 136=Y)
    : WP isa (secondPrefix v.callee) s (PrefixPost P σ c i w Y) := by
  unfold secondPrefix
  refine WP.seq (WP.block_append (M := isa) (l₁ := ([.str .x .x9 .x25 1800,.str .x .x10 .x25 1808,.str .x .x11 .x25 1816] : List VG.AArch64.Instr))
    (l₂ := args) (WP.mono (save_ok (s := s) (p := P.scr) he.x25 (fun d hd => inScr hp he.wr (by
      rcases mem3 hd with rfl | rfl | rfl <;> omega))) fun t ⟨kt,ft,sv⟩ => ?_))
  have et := env_saved hp he kt ft
  have ct : VG.Proof.MlDsa.AArch64.Sample.Ball.CStored t.mem P.a c := stored_frame hparser.stored ft (by
    intro r hr; rcases mem3 hr with rfl|rfl|rfl <;> exact a_scr' hp (by decide))
  have st : stateAt t.mem P.scr=stateAt s.mem P.scr := state_frame ft (by
    intro r hr
    have sep (d : Nat) (hd : 200≤d) (hd2 : d+8≤2048) :
        Region.Disjoint ⟨P.scr,200⟩ ⟨P.at' d,8⟩ := by
      simpa only [at_zero] using (disj_scr (P := P) (a := 0) (n := 200) (b := d) (m := 8) (.inl hd) (by decide) hd2)
    rcases mem3 hr with rfl|rfl|rfl <;> exact sep _ (by decide) (by decide))
  refine WP.mono (args_ok et.x25) fun u ⟨ku,ua⟩ => ?_
  have eu := et.keep ku.keep ku.mem
  refine WP.seq (WP.mono (resume_call_ok v (c := c) (Y := Y) (w9 := s.gpr .x9) (w10 := s.gpr .x10) (w11 := s.gpr .x11) hp eu ua
    (by rw [kt.get .x0]; exact hpos)
    (by rw [ku.mem,st,kt.get .x0]; exact hn)
    (by exact ⟨by rw [ku.mem]; exact sv.r9,by rw [ku.mem]; exact sv.r10,by rw [ku.mem]; exact sv.r11⟩) (by simpa only [ku.mem] using ct)) fun t₂ ⟨et₂,sv₂,ct₂,ot₂⟩ => ?_)
  refine WP.mono (restore_ok et₂.x25 sv₂ (fun d hd => inScrRd hp et₂.rd et₂.wr (by
    rcases mem3 hd with rfl | rfl | rfl <;> omega))) fun t₃ ⟨kr,rr⟩ => ?_
  have er := et₂.keep kr.keep kr.mem
  have pr : Parser P.a c i w t₃ := ⟨er.x26,rr.x9.trans hparser.x9,
    by rw [rr.x10,hparser.x10],by rw [rr.x11,hparser.x11],rr.x12,rr.x15,by rw [kr.mem]; exact ct₂⟩
  refine ⟨er,pr,rr.x2,?_,?_,?_,?_⟩
  · rw [hY]; exact rr.x5
  · intro j hj
    rw [kr.mem,← ot₂,MlKem.bytesAt_getD _ _ (by rw [hY] at hj; exact hj)]
  · rw [regions hp er]
    refine Covers.of_sub fun r hr => ?_
    rcases mem2 hr with rfl|rfl
    · exact ⟨P.scrR,by simp,840,rfl,by change 840+Y.length≤2048; rw [hY]; decide⟩
    · exact ⟨polyR P.a,by simp,0,(ptr_zero _).symm,by simp⟩
  · rw [er.wr,hp.wr]
    exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨polyR P.a,by simp,0,(ptr_zero _).symm,by simp⟩
end VG.Proof.MlDsa.AArch64.Optimized.Ball
