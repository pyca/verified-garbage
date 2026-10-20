module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.AbsorbPlan
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Permute
import VerifiedGarbage.Proof.Sha3.Arith
@[expose] public section
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
