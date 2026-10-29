module

public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole

import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.CompiledShapes
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Schedules
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.AbsorbPlan
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Permute
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Finish
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Init
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Compiled
import VerifiedGarbage.Impl.MlKem.AArch64.FixedHash
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Fusion
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Transport

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/FixedHash/AbsorbLoop.lean`, which only this module imported.
section

section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Proof.Sha3 (Rep xorAt rep_append bytesAt_length)

theorem nextPos_mod {rate pos : Nat} {w : Bool} {msg : List Byte} {bs : List Byte}
 (hr : 0<rate) (hp : pos=msg.length%rate) (hb : bs.length=width w)
 (hf : pos+width w≤rate) : nextPos rate pos w=(msg++bs).length%rate := by
 rw [List.length_append,hb,Nat.add_mod,←hp]
 have hp' : pos<rate := by rw [hp]; exact Nat.mod_lt _ hr
 have eq : (pos+width w%rate)%rate=(pos+width w)%rate := by
   simpa only [Nat.mod_eq_of_lt hp'] using (Nat.add_mod pos (width w) rate).symm
 rw [eq]
 unfold nextPos
 split <;> rename_i h
 · rw [h,Nat.mod_self]
 · rw [Nat.mod_eq_of_lt (by omega)]

theorem compile_ok (v : Proof.Sha3.AArch64.Permutation)
 {s₀ : State} {sc : Reg} {st wk rate : Nat}
 (hS : HSetup sc st wk rate s₀) (ha : st%8=0) (hb : st+rate≤4096)
 {ps : List Piece} {i pos last : Nat} {acts : List Action}
 (valid : Valid rate ps i pos acts last) :
 ∀s msg, (∀p∈ps,PieceOk sc st wk s₀ false p) → (∀p∈ps,p.off+p.len≤65536) →
 Kept [STr sc st s₀,WKr sc wk s₀] s₀ s →
 stateAt s.mem (s₀.gpr sc+BitVec.ofNat 64 st)=Rep rate msg → pos=msg.length%rate →
 WP isa (compile v.callee sc st wk rate acts) s fun t=>
 Kept [STr sc st s₀,WKr sc wk s₀] s₀ t ∧
 stateAt t.mem (s₀.gpr sc+BitVec.ofNat 64 st)=Rep rate (msg++remainingBytes s₀ ps i) ∧
 last=(msg++remainingBytes s₀ ps i).length%rate ∧
 Frame [STr sc st s₀,⟨s₀.gpr sc+BitVec.ofNat 64 wk,512⟩] s.mem t.mem := by
 induction valid with
 | done pos =>
   intro s msg _ _ hk hm hp
   exact wp_nil ⟨hk,by simpa [remainingBytes] using hm,by simpa [remainingBytes] using hp,Frame.refl _ _⟩
 | @skip p ps pos acts last tail ih =>
   intro s msg hp ho hk hm hpos
   simpa only [remaining_skip] using ih s msg
     (fun q hq=>hp q (List.mem_cons_of_mem _ hq))
     (fun q hq=>ho q (List.mem_cons_of_mem _ hq)) hk hm hpos
 | @step p ps i pos w acts last hi hfit hw tail ih =>
   intro s msg hp ho hk hm hpos
   have pOk:=hp p (List.mem_cons_self ..)
   have pOff:=ho p (List.mem_cons_self ..)
   have hr:=(rate_bounds hS.hrate).1
   have hr':=(rate_bounds hS.hrate).2
   have bw : (chunkBytes s₀ p i (width w)).length=width w := bytesAt_length ..
   have rep := rep_append hr (by omega) msg (chunkBytes s₀ p i (width w))
     (by rw [bw]; cases w <;> decide) (by rw [bw,←hpos]; exact hfit)
   rw [bw,←hpos] at rep
   have nx := nextPos_mod hr hpos bw hfit
   dsimp only [compile,action]
   refine WP.seq (WP.mono (action_piece_ok hS pOk hk.rg hi pOff hfit hw ha hb) fun t ⟨kt,mt⟩=> ?_)
   have k':=hk.trans (kt.mono (by simp))
   rw [hm,chunkBytes_frame pOk hk hi] at mt
   have finish {u : State} (ku : Kept [STr sc st s₀,WKr sc wk s₀] s₀ u)
       (mu : stateAt u.mem (s₀.gpr sc+BitVec.ofNat 64 st)=
         Rep rate (msg++chunkBytes s₀ p i (width w))) :=
     ih u (msg++chunkBytes s₀ p i (width w)) hp ho ku mu nx
   by_cases he : pos+width w=rate
   · rw [ite_eq_left he]
     refine WP.seq (WP.mono (permute_ok v hS k'.rg) fun u ⟨ku,mu⟩=> ?_)
     have k'' := k'.trans (ku.sub (by
       intro r hh
       rcases mem2' hh with rfl|rfl
       · exact ⟨_,List.mem_cons_self ..,fun _ h=>h⟩
       · exact ⟨WKr sc wk s₀,by simp,fun _ h=>Nat.le_trans h (by decide : 512≤640)⟩))
     have out := finish k'' (by rw [mu,mt,rep,ite_eq_left he])
     refine WP.mono out fun fin ⟨kf,mf,pf,ff⟩=>⟨kf,?_,?_,?_⟩
     · simpa only [remaining_step s₀ p ps hi,List.append_assoc] using mf
     · simpa only [remaining_step s₀ p ps hi,List.append_assoc] using pf
     · exact (kt.frame.mono (by simp)).trans (ku.frame.trans ff)
   · rw [ite_eq_right he]
     have out := finish k' (by rw [mt,rep,ite_eq_right he])
     refine WP.mono out fun fin ⟨kf,mf,pf,ff⟩=>⟨kf,?_,?_,?_⟩
     · simpa only [remaining_step s₀ p ps hi,List.append_assoc] using mf
     · simpa only [remaining_step s₀ p ps hi,List.append_assoc] using pf
     · exact (kt.frame.mono (by simp)).trans ff
end VG.Proof.MlKem.AArch64.FixedHash
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/FixedHash/Correct.lean`, which only this module imported.
section

section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.Sha3 (stateAt absorb pad)

theorem compiled_ok (v : Proof.Sha3.AArch64.Permutation)
 {s₀ : State} {sc : Reg} {st wk rate sfx : Nat} {ins outs : List Piece}
 (hs : HSetup sc st wk rate s₀) (ha : st%8=0) (hb : st+rate≤4096)
 (hl : (wk+600)%8=0 ∧ wk+600<32768)
 (hi : ∀p∈ins,PieceOk sc st wk s₀ false p)
 (hio : ∀p∈ins,p.off+p.len≤65536)
 (valid : Valid rate ins 0 0 (schedule rate ins).1 (schedule rate ins).2)
 (ho : ∀p∈outs,PieceOk sc st wk s₀ true p)
 (hp : outs.Pairwise (fun p q=>(preg s₀ p).Disjoint (preg s₀ q)))
 (hn : ∀p∈outs,p.off+p.len≤65536 ∧ p.len%8=0)
 (ht : (outs.map Piece.len).sum≤rate) :
 WP isa (compiled v.callee sc st wk rate sfx ins outs) s₀ fun t=>
 Kept (STr sc st s₀::WKr sc wk s₀::outs.map (preg s₀)) s₀ t ∧
 t.gpr .x30=s₀.gpr .x30 ∧
 Outs s₀ t.mem rate (absorb rate (pad rate (BitVec.ofNat 8 sfx)
   (ins.map (pbytes s₀)).flatten)) 0 outs := by
 dsimp only [compiled]
 refine WP.seq (WP.mono (zeroSave_ok hs hl) fun a ⟨ka,za,la⟩=>?_)
 refine WP.seq (WP.mono (compile_ok v hs ha hb valid a [] hi hio ka
   (by rw [Proof.Sha3.rep_nil]; exact za) (by simp)) fun b ⟨kb,mb,pb,fb⟩=>?_)
 simp only [List.nil_append,remaining_zero] at mb pb
 exact finish_ok v hs ha hb hl ho hp hn ht kb mb pb (by rw [link_frame hs fb,la])

/-- Original hash interface, with only the specialization's encoding and schedule checks added. -/
theorem code_ok (v : Proof.Sha3.AArch64.Permutation)
 {s₀ : State} {sc : Reg} {st wk rate sfx : Nat} {ins outs : List Piece}
 (hs : HSetup sc st wk rate s₀) (ha : st%8=0) (hb : st+rate≤4096)
 (hl : (wk+600)%8=0 ∧ wk+600<32768)
 (hi : ∀p∈ins,PieceOk sc st wk s₀ false p)
 (hio : ∀p∈ins,p.off+p.len≤65536)
 (valid : Valid rate ins 0 0 (schedule rate ins).1 (schedule rate ins).2)
 (ho : ∀p∈outs,PieceOk sc st wk s₀ true p)
 (hp : outs.Pairwise (fun p q=>(preg s₀ p).Disjoint (preg s₀ q)))
 (hn : ∀p∈outs,p.off+p.len≤65536 ∧ p.len%8=0)
 (ht : (outs.map Piece.len).sum≤rate)
 (same : Fusion.Same (compiled v.callee sc st wk rate sfx ins outs)
   (Impl.MlKem.AArch64.FixedHash.code v.callee sc st wk rate sfx ins outs)) :
 WP isa (Impl.MlKem.AArch64.FixedHash.code v.callee sc st wk rate sfx ins outs) s₀ fun t=>
 Kept (STr sc st s₀::WKr sc wk s₀::below s₀.sp 16::outs.map (preg s₀)) s₀ t ∧
 Outs s₀ t.mem rate (absorb rate (pad rate (BitVec.ofNat 8 sfx)
   (ins.map (pbytes s₀)).flatten)) 0 outs := by
 apply same.wp.mp
 refine WP.mono (compiled_ok v hs ha hb hl hi hio valid ho hp hn ht) fun t ⟨hk,_,out⟩=>⟨hk.mono ?_,out⟩
 intro r hr
 simp only [List.mem_cons] at hr ⊢
 rcases hr with h|h|h
 · exact Or.inl h
 · exact Or.inr (Or.inl h)
 · exact Or.inr (Or.inr (Or.inr h))
end VG.Proof.MlKem.AArch64.FixedHash
end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64

/-! The fixed hash's shapes are correct for any permutation `v`. -/

theorem kgG768_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KG.ST KG.WK 72 6
        [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩] [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound kgG768_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (kgG768_compiled v.callee)

theorem kgH768_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KG.ST KG.WK 136 6
        [⟨.x26,0,lay768.ekLen⟩] [⟨.x27,2336,32⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound kgH768_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (kgH768_compiled v.callee)

theorem prf768_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KEM.ST KEM.WK 136 0x1f
        [⟨.x28,KEM.RB,33⟩] [⟨.x28,KEM.PB,128⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound prf768_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (prf768_compiled v.callee)

theorem enH768_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KEM.ST KEM.WK 136 6
        [⟨.x25,0,lay768.ekLen⟩] [⟨.x28,KEM.HB,32⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound enH768_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (enH768_compiled v.callee)

theorem enG768_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩] [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound enG768_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (enG768_compiled v.callee)

theorem deG768_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x25,2336,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound deG768_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (deG768_compiled v.callee)

theorem kgG1024_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KG.ST KG.WK 72 6
        [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩] [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound kgG1024_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (kgG1024_compiled v.callee)

theorem kgH1024_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KG.ST KG.WK 136 6
        [⟨.x26,0,Impl.MlKem1024.AArch64.lay1024.ekLen⟩] [⟨.x27,3104,32⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound kgH1024_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (kgH1024_compiled v.callee)

theorem prf1024_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KEM.ST KEM.WK 136 0x1f
        [⟨.x28,KEM.RB,33⟩] [⟨.x28,KEM.PB,128⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound prf1024_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (prf1024_compiled v.callee)

theorem enH1024_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KEM.ST KEM.WK 136 6
        [⟨.x25,0,Impl.MlKem1024.AArch64.lay1024.ekLen⟩] [⟨.x28,KEM.HB,32⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound enH1024_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (enH1024_compiled v.callee)

theorem enG1024_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩] [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound enG1024_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (enG1024_compiled v.callee)

theorem deG1024_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x25,3104,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound deG1024_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (deG1024_compiled v.callee)

end VG.Proof.MlKem.AArch64.FixedHash
