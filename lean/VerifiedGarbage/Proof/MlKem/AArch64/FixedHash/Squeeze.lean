module
public import Mathlib.Tactic.Conv
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.SqueezeCode
public import VerifiedGarbage.Proof.MlKem.AArch64.HashProof

import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.SqueezeTransport
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.SqueezePiece
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Block

/-! # Complete fixed-length single-block squeezing into disjoint output pieces -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem
open VG.Spec.Sha3 (stateAt bytesAt)

theorem squeeze_ok {sc : Reg} {st wk rate : Nat} (ps : List Piece) :
    ∀{s : State} {pos : Nat}, HSetup sc st wk rate s→
    (∀p∈ps,PieceOk sc st wk s true p)→
    ps.Pairwise (fun p q=>(preg s p).Disjoint (preg s q))→
    st%8=0→pos%8=0→st+rate≤32768→
    (∀p∈ps,p.off+p.len≤65536 ∧ p.len%8=0)→
    pos+(ps.map Piece.len).sum≤rate→
    WP isa (.block (squeezeCode sc st pos ps)) s fun t=>
      Keep [.x2,.x9] s t ∧ Frame (ps.map (preg s)) s.mem t.mem ∧
      Outs s t.mem rate (stateAt s.mem (s.gpr sc+BitVec.ofNat 64 st)) pos ps := by
  induction ps with
  | nil=>
    intro s pos hs hp sep sa pa sf of fit
    exact WP.block_nil ⟨Keep.refl _ _,Frame.refl _ _,trivial⟩
  | cons p ps ih=>
    intro s pos hs hp sep sa pa sf of fit
    have pp := hp p (by simp)
    have num := of p (by simp)
    have fitp : pos+p.len≤rate := by simp only [List.map_cons,List.sum_cons] at fit; omega
    change WP isa (.block (squeezePieceCode sc st pos p ++ squeezeCode sc st (pos+p.len) ps)) s _
    rw [WP.block_append_iff]
    refine WP.mono (squeezePiece_ok hs pp sa pa sf num.1 num.2 fitp) fun a ha=>?_
    have hp' : ∀q∈ps,PieceOk sc st wk s true q := fun q hq=>hp q (by simp [hq])
    have pregEq : ∀q∈ps,preg a q=preg s q := fun q hq=>preg_copy (hp' q hq) ha.1
    have maps : ps.map (preg a)=ps.map (preg s) := List.map_congr_left pregEq
    have sepa : ps.Pairwise (fun p q=>(preg a p).Disjoint (preg a q)) := by
      apply sep.tail.imp_of_mem
      intro x y hx hy hxy
      simpa only [pregEq x hx,pregEq y hy] using hxy
    have state : stateAt a.mem (a.gpr sc+BitVec.ofNat 64 st)=stateAt s.mem (s.gpr sc+BitVec.ofNat 64 st) := by
      rw [ha.1.get sc (squeeze_ne _ hs.hsc.1)]
      apply Proof.Sha3.stateAt_congr
      exact bytes_frame ha.2.1 (fun r hr=>by rw [List.mem_singleton.mp hr]; exact pp.dst.symm) (by decide)
    refine WP.mono (ih (hsetup_copy hs ha.1) (fun q hq=>piece_copy hs (hp' q hq) ha.1) sepa
      sa (by omega) sf (fun q hq=>of q (by simp [hq]))
      (by simpa only [List.map_cons,List.sum_cons,Nat.add_assoc] using fit)) fun t ht=>?_
    have frame : Frame (ps.map (preg s)) a.mem t.mem := by simpa only [maps] using ht.2.1
    refine ⟨(ha.1.trans ht.1).mono (by simp),?_,?_,?_⟩
    · exact (ha.2.1.mono (by intro r hr; simp only [List.mem_singleton] at hr; rw [hr]; simp)).trans
        (frame.mono (by intro r hr; exact List.mem_cons_of_mem _ hr))
    · rw [bytesAt_frame frame (fun r hr=>by
          obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hr
          exact (List.pairwise_cons.mp sep).1 q hq ) (by have := pp.len; omega)]
      exact ha.2.2
    · have out := ht.2.2
      rw [state] at out
      exact (outs_copy hp' ha.1).mp out

theorem squeeze_kept {s : State} {sc : Reg} {st wk rate pos : Nat} {ps : List Piece}
    (hs : HSetup sc st wk rate s) (hp : ∀p∈ps,PieceOk sc st wk s true p)
    (sep : ps.Pairwise (fun p q=>(preg s p).Disjoint (preg s q)))
    (sa : st%8=0) (pa : pos%8=0) (sf : st+rate≤32768)
    (of : ∀p∈ps,p.off+p.len≤65536 ∧ p.len%8=0)
    (fit : pos+(ps.map Piece.len).sum≤rate) :
    WP isa (.block (squeezeCode sc st pos ps)) s fun t=>
      Kept (ps.map (preg s)) s t ∧ t.gpr .x30=s.gpr .x30 ∧
      Outs s t.mem rate (stateAt s.mem (s.gpr sc+BitVec.ofNat 64 st)) pos ps := by
  refine WP.mono (squeeze_ok ps hs hp sep sa pa sf of fit) fun t ⟨hk,hf,out⟩=>?_
  exact ⟨⟨fun r hr _=>hk.get r (squeeze_ne r hr),hk.sp,hk.rd,hk.wr,hf,hk.vcs⟩,
    hk.get .x30 (by decide),out⟩

end VG.Proof.MlKem.AArch64.FixedHash
