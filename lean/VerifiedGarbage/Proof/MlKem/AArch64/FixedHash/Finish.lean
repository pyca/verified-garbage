module
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Transport
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.PadState
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Squeeze
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Schedule
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Link
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Pad
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.SqueezeCode
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Permute
import VerifiedGarbage.Proof.Framework.Offset
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.Sha3 (stateAt absorb pad)

theorem finish_ok (v : Proof.Sha3.AArch64.Permutation)
 {s₀ s : State} {sc : Reg} {st wk rate pos sfx : Nat} {msg : List Byte} {outs : List Piece}
 (hs : HSetup sc st wk rate s₀) (ha : st%8=0) (hb : st+rate≤4096)
 (hl : (wk+600)%8=0 ∧ wk+600<32768)
 (ho : ∀p∈outs,PieceOk sc st wk s₀ true p)
 (hp : outs.Pairwise (fun p q=>(preg s₀ p).Disjoint (preg s₀ q)))
 (hn : ∀p∈outs,p.off+p.len≤65536 ∧ p.len%8=0)
 (ht : (outs.map Piece.len).sum≤rate)
 (hk : Kept [STr sc st s₀,WKr sc wk s₀] s₀ s)
 (hm : stateAt s.mem (s₀.gpr sc+BitVec.ofNat 64 st)=Proof.Sha3.Rep rate msg)
 (hpos : pos=msg.length%rate)
 (hlink : s.mem.readW (linkSlot sc wk s₀) 64=s₀.gpr .x30) :
 WP isa (.seq (.block (padCode sc st rate pos sfx))
 (.seq (permute v.callee sc st wk)
 (.seq (.block (squeezeCode sc st 0 outs)) (.block [.ldr .x .x30 sc (wk+600)])))) s fun t=>
 Kept (STr sc st s₀::WKr sc wk s₀::outs.map (preg s₀)) s₀ t ∧
 t.gpr .x30=s₀.gpr .x30 ∧
 Outs s₀ t.mem rate (absorb rate (pad rate (BitVec.ofNat 8 sfx) msg)) 0 outs := by
 have gs:=hk.rg
 have es:=gs.cs sc hs.hsc.1 hs.hsc.2
 refine WP.seq (WP.mono (pad_repr (hsetup_rg hs gs) hb (by rw [Proof.Sha3.repr_iff]; simpa only [es] using hm) hpos) fun a ⟨ka,_,ma⟩=>?_)
 simp only [STr,es] at ka
 rw [es] at ma
 have kaa:=hk.trans (ka.mono (by simp))
 have la : a.mem.readW (linkSlot sc wk s₀) 64=s₀.gpr .x30 := by
   rw [link_frame hs (ka.frame.mono (by simp)),hlink]
 refine WP.seq (WP.mono (permute_ok v hs kaa.rg) fun b ⟨kb,mb⟩=>?_)
 have kb' : Kept [STr sc st s₀,WKr sc wk s₀] a b := kb.sub (by
   intro r hr; rcases mem2' hr with rfl|rfl
   · exact ⟨_,by simp,fun _ h=>h⟩
   · exact ⟨WKr sc wk s₀,by simp,fun _ h=>Nat.le_trans h (show 512≤640 by decide)⟩)
 have kbb:=kaa.trans kb'
 have lb : b.mem.readW (linkSlot sc wk s₀) 64=s₀.gpr .x30 := by rw [link_frame hs kb.frame,la]
 have gb:=kbb.rg
 have eb:=gb.cs sc hs.hsc.1 hs.hsc.2
 have pe : ∀p∈outs,preg b p=preg s₀ p := fun p h=>preg_rg (ho p h) gb
 have maps : outs.map (preg b)=outs.map (preg s₀) := List.map_congr_left pe
 have pb : outs.Pairwise (fun p q=>(preg b p).Disjoint (preg b q)) :=
   by
   apply hp.imp_of_mem
   intro p q h₁ h₂ hh
   simpa only [pe p h₁,pe q h₂] using hh
 refine WP.seq (WP.mono (squeeze_kept (hsetup_rg hs gb) (fun p h=>piece_rg hs (ho p h) gb)
   pb ha (by decide) (by omega) hn (by simpa using ht)) fun c ⟨kc,_,oc⟩=>?_)
 rw [maps] at kc
 have kcc : Kept (STr sc st s₀::WKr sc wk s₀::outs.map (preg s₀)) s₀ c := (kbb.mono (by simp)).trans (kc.mono (by intro r hr; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))
 have lc : c.mem.readW (linkSlot sc wk s₀) 64=s₀.gpr .x30 := by
   rw [kc.frame.readW (w:=64) (r:=⟨linkSlot sc wk s₀,8⟩) (Region.contains_self _ _) ?_ (by decide),lb]
   intro r hr
   obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hr
   exact (ho p hp).dwk.symm.sub_left (Offset.sub_base _ (d:=600) (by decide))
 rw [eb,mb,ma] at oc
 have oc':= (outs_rg ho gb).mp oc
 refine WP.mono (restoreLink_ok hs kcc.rg hl) fun t ⟨kt,mt,lt⟩=>?_
 exact ⟨kcc.trans (kt.mono (by simp)),lt.trans lc,by simpa only [mt] using oc'⟩
end VG.Proof.MlKem.AArch64.FixedHash
