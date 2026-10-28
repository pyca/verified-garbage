module
public import VerifiedGarbage.Impl.MlKem.AArch64.Paired
public import VerifiedGarbage.Proof.MlKem.AArch64.Lay
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Checkpoint
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Vector

import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Memory
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Keep
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Segment
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Extra
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.SplitIfs

/-! # Resume both public matrix streams and combine their success flags

`Paired.extraBoth` runs `extraReject` once per stream, as a loop counted by
`x23`: the first iteration resumes the stream whose buffer is at 400 and
cursor at 1680, the second the one at 904 and 1696. -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

def bothWrites (p a b : Addr) : List Region :=
  [polyRegion a,polyRegion b,⟨p+1680,16⟩,⟨p+1696,16⟩]
def bothRegs : List Reg :=
  [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x20,.x22,.x23]

/-- 1 when `L` is complete. -/
def fullFlag (L : List Zq) : BitVec 64 := if L.length=256 then 1 else 0

/-- A stream ready to resume: its next block at `buf`, its cursor at `cur`,
its coefficients at `aP`. -/
structure ReadyW (w16 : Bool) (L : List Zq) (B : Nat→Byte) (buf cur aP : Addr) (s : State) : Prop where
  env : Rej8.EnvW w16 56 B buf aP s
  len : L.length≤256
  coeffs : Rej8.Scalar.CoeffsW w16 s.mem aP L
  saved : checkpointW w16 cur aP L s.mem
  out0 : InRegions s.wr cur 8
  out1 : InRegions s.wr (cur+8) 8
  apart : (polyRegion aP).Disjoint ⟨cur,16⟩

/-- An iteration of `extraBoth`. -/
def bothBody (w16 : Bool := false) : Prog isa :=
  .seq (Impl.MlKem.AArch64.Paired.extraReject w16)
    (.block [.logic .and .x .x22 .x22 .x0,.addImm .x .x20 .x20 504,.addImm .x .x1 .x1 16,
      .subImm .x .x23 .x23 1])

structure BodyPostW (w16 : Bool) (L : List Zq) (B : Nat→Byte) (cur aP : Addr) (t u : State) : Prop where
  keep : Keep bothRegs t u
  frame : Frame [polyRegion aP,⟨cur,16⟩] t.mem u.mem
  coeffs : Rej8.Scalar.CoeffsW w16 u.mem aP (sampleAfter L B 56)
  checkpoint : checkpointW w16 cur aP (sampleAfter L B 56) u.mem
  flag : u.gpr .x22=t.gpr .x22 &&& fullFlag (sampleAfter L B 56)
  x20 : u.gpr .x20=t.gpr .x20+BitVec.ofNat 64 504
  x1 : u.gpr .x1=t.gpr .x1+BitVec.ofNat 64 16
  x23 : u.gpr .x23=t.gpr .x23-BitVec.ofNat 64 1
  constants : Rej8.Constants u

theorem bothBody_ok {w16 : Bool} {t : State} {L : List Zq} {B : Nat→Byte} {aP : Addr}
    (h : ReadyW w16 L B (t.gpr .x20) (t.gpr .x1) aP t) (hc : Rej8.Constants t) :
    WP isa (bothBody w16) t (BodyPostW w16 L B (t.gpr .x1) aP t) := by
  have run := Rej8.WP.constants (extra_ok t h.env hc h.len h.coeffs h.saved h.out0 h.out1 h.apart) hc
    (by cases w16 <;> rfl)
  refine WP.seq (WP.mono run fun m ⟨hm,_⟩ => ?_)
  have blk : WP isa (.block [.logic .and .x .x22 .x22 .x0,.addImm .x .x20 .x20 504,.addImm .x .x1 .x1 16,
      .subImm .x .x23 .x23 1]) m fun u => Only [.x22,.x20,.x1,.x23] m u ∧
        u.gpr .x22=m.gpr .x22 &&& m.gpr .x0 ∧ u.gpr .x20=m.gpr .x20+BitVec.ofNat 64 504 ∧
        u.gpr .x1=m.gpr .x1+BitVec.ofNat 64 16 ∧ u.gpr .x23=m.gpr .x23-BitVec.ofNat 64 1 :=
    wp_and fun a ka ea => wp_addImm (by decide) fun b kb eb => wp_addImm (by decide) fun c kc ec =>
      wp_subImm (by decide) fun u ku eu => wp_nil
        ⟨(((ka.trans kb).trans kc).trans ku).mono,
          by rw [ku.get .x22,kc.get .x22,kb.get .x22,ea],
          by rw [ku.get .x20,kc.get .x20,eb,ka.get .x20],
          by rw [ku.get .x1,ec,kb.get .x1,ka.get .x1],
          by rw [eu,kc.get .x23,kb.get .x23,ka.get .x23]⟩
  refine WP.mono (WP.keepV (by rfl) blk) fun u ⟨⟨ku,e22,e20,e1,e23⟩,vu⟩ => ?_
  have cm := ‹Rej8.Constants m›
  have m0 : m.gpr .x0=fullFlag (sampleAfter L B 56) := by
    apply BitVec.eq_of_toNat_eq
    rw [hm.flagValue,fullFlag]
    split <;> rfl
  refine ⟨(hm.keep.trans ku.keep).mono,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [ku.mem]; exact hm.frame
  · rw [ku.mem]; exact hm.coeffs
  · rw [ku.mem]; exact hm.checkpoint
  · rw [e22,m0,hm.keep.get .x22]
  · rw [e20,hm.keep.get .x20]
  · rw [e1,hm.keep.get .x1]
  · rw [e23,hm.keep.get .x23]
  · exact ⟨by rw [vu]; exact cm.index,by rw [vu]; exact cm.mask,
      by simpa only [vu] using cm.q,by simpa only [vu] using cm.weights,by simpa only [vu] using cm.zero⟩

structure BothPostW (w16 : Bool) (L M : List Zq) (p a b : Addr) (s u : State) : Prop where
  keep : Keep bothRegs s u
  frame : Frame (bothWrites p a b) s.mem u.mem
  left : Rej8.Scalar.CoeffsW w16 u.mem a L
  right : Rej8.Scalar.CoeffsW w16 u.mem b M
  saveLeft : checkpointW w16 (p+1680) a L u.mem
  saveRight : checkpointW w16 (p+1696) b M u.mem
  flagBoth : (u.gpr .x6).toNat=if L.length=256 ∧ M.length=256 then 1 else 0
  constants : Rej8.Constants u

/-- What `extraBoth` needs: both streams ready at their places. -/
structure BothReadyW (w16 : Bool) (L M : List Zq) (A B : Nat→Byte) (p a b : Addr) (s : State) : Prop where
  pointer : s.gpr .x19=p
  scratch : Covers [⟨p,2048⟩] s.wr
  farA : (Region.mk p 2048).Disjoint (polyRegion a)
  farB : (Region.mk p 2048).Disjoint (polyRegion b)
  apart : (polyRegion a).Disjoint (polyRegion b)
  left : ReadyW w16 L A (p+400) (p+1680) a s
  right : ReadyW w16 M B (p+904) (p+1696) b s
  table : ∀mask<256,(Region.mk (s.gpr .x16+BitVec.ofNat 64 (16*mask)) 16).Disjoint ⟨p,2048⟩
  constants : Rej8.Constants s

theorem ReadyW.only {w16 : Bool} {L : List Zq} {B : Nat→Byte} {buf cur aP : Addr} {s u : State}
    {rs : List Reg} (h : ReadyW w16 L B buf cur aP s) (k : Only rs s u) (h16 : .x16 ∉ rs := by decide) :
    ReadyW w16 L B buf cur aP u := by
  refine ⟨h.env.transfer k.mem k.rd k.wr (k.get .x16 h16),h.len,?_,?_,?_,?_,h.apart⟩
  · rw [k.mem]; exact h.coeffs
  · rw [k.mem]; exact h.saved
  · rw [k.wr]; exact h.out0
  · rw [k.wr]; exact h.out1

theorem ReadyW.frame {w16 : Bool} {L : List Zq} {B : Nat→Byte} {buf cur aP : Addr} {t u : State}
    {rs : List Reg} {ws : List Region} (h : ReadyW w16 L B buf cur aP t) (k : Keep rs t u)
    (hf : Frame ws t.mem u.mem) (h16 : .x16 ∉ rs := by decide)
    (db : ∀r∈ws,(Region.mk buf (3*56+4)).Disjoint r) (dp : ∀r∈ws,(polyRegion aP).Disjoint r)
    (dc : ∀r∈ws,(Region.mk cur 16).Disjoint r)
    (dt : ∀mask<256,∀r∈ws,(Region.mk (t.gpr .x16+BitVec.ofNat 64 (16*mask)) 16).Disjoint r) :
    ReadyW w16 L B buf cur aP u := by
  refine ⟨h.env.frame k.rd k.wr (k.get .x16 h16) hf db dt,h.len,coeffs_frame h.coeffs h.len hf dp,
    checkpoint_frame h.saved hf dc,?_,?_,h.apart⟩
  · rw [k.wr]; exact h.out0
  · rw [k.wr]; exact h.out1

theorem one_and_fullFlag (L : List Zq) : (1 : BitVec 64) &&& fullFlag L=fullFlag L := by
  unfold fullFlag; split <;> rfl

/-- The state before iteration `k` of `extraBoth`'s loop. -/
def BothInv (w16 : Bool) (L M : List Zq) (A B : Nat→Byte) (p a b : Addr) (s : State) : Nat → State → Prop
  | 0, t => Keep bothRegs s t ∧ Frame (bothWrites p a b) s.mem t.mem ∧ Rej8.Constants t ∧
      t.gpr .x20=p+400 ∧ t.gpr .x1=p+1680 ∧ t.gpr .x23=2 ∧ t.gpr .x22=1 ∧
      ReadyW w16 L A (p+400) (p+1680) a t ∧ ReadyW w16 M B (p+904) (p+1696) b t
  | 1, t => Keep bothRegs s t ∧ Frame (bothWrites p a b) s.mem t.mem ∧ Rej8.Constants t ∧
      t.gpr .x20=p+904 ∧ t.gpr .x1=p+1696 ∧ t.gpr .x23=1 ∧ t.gpr .x22=fullFlag (sampleAfter L A 56) ∧
      Rej8.Scalar.CoeffsW w16 t.mem a (sampleAfter L A 56) ∧
      checkpointW w16 (p+1680) a (sampleAfter L A 56) t.mem ∧ ReadyW w16 M B (p+904) (p+1696) b t
  | _, t => Keep bothRegs s t ∧ Frame (bothWrites p a b) s.mem t.mem ∧ Rej8.Constants t ∧
      t.gpr .x23=0 ∧ t.gpr .x22=fullFlag (sampleAfter L A 56) &&& fullFlag (sampleAfter M B 56) ∧
      Rej8.Scalar.CoeffsW w16 t.mem a (sampleAfter L A 56) ∧
      checkpointW w16 (p+1680) a (sampleAfter L A 56) t.mem ∧
      Rej8.Scalar.CoeffsW w16 t.mem b (sampleAfter M B 56) ∧
      checkpointW w16 (p+1696) b (sampleAfter M B 56) t.mem

theorem bothStep0_ok {w16 : Bool} {s t : State} {p a b : Addr} {L M : List Zq} {A B : Nat→Byte}
    (h : BothReadyW w16 L M A B p a b s) (ht : BothInv w16 L M A B p a b s 0 t) :
    WP isa (bothBody w16) t fun u => BothInv w16 L M A B p a b s 1 u ∧ ((u.gpr .x23).toNat≠0 ↔ 0+1≠2) := by
  obtain ⟨kt,ft,ct,t20,t1,t23,t22,ra,rb⟩ := ht
  have sA : Region.Sub ⟨p+1680,16⟩ ⟨p,2048⟩ := Offset.sub_base p (by decide)
  have sB : Region.Sub ⟨p+1696,16⟩ ⟨p,2048⟩ := Offset.sub_base p (by decide)
  have t16 : t.gpr .x16=s.gpr .x16 := kt.get .x16
  refine WP.mono (bothBody_ok (by rw [t20,t1]; exact ra) ct) fun u hu => ?_
  rw [t1] at hu
  have rb' : ReadyW w16 M B (p+904) (p+1696) b u := by
    refine rb.frame hu.keep hu.frame (by decide) ?_ ?_ ?_ ?_
    all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    · exact ⟨h.farA.sub_left (Offset.sub_base p (by decide)),Offset.disjoint p (by decide) (by decide) (by decide)⟩
    · exact ⟨h.apart.symm,h.farB.symm.sub_right sA⟩
    · exact ⟨h.farA.sub_left sB,(Offset.disjoint p (by decide) (by decide) (by decide))⟩
    · intro mask hm
      exact ⟨ra.env.tableDisj mask hm,by rw [t16]; exact (h.table mask hm).sub_right sA⟩
  have u23 : u.gpr .x23=1 := by rw [hu.x23,t23]; rfl
  refine ⟨⟨(kt.trans hu.keep).mono,ft.trans (hu.frame.mono (by simp [bothWrites])),hu.constants,
    by rw [hu.x20,t20,BitVec.add_assoc]; rfl,by rw [hu.x1,t1,BitVec.add_assoc]; rfl,u23,
    by rw [hu.flag,t22,one_and_fullFlag],hu.coeffs,hu.checkpoint,rb'⟩,?_⟩
  rw [u23]; decide

theorem bothStep1_ok {w16 : Bool} {s t : State} {p a b : Addr} {L M : List Zq} {A B : Nat→Byte}
    (h : BothReadyW w16 L M A B p a b s) (ht : BothInv w16 L M A B p a b s 1 t) :
    WP isa (bothBody w16) t fun u => BothInv w16 L M A B p a b s 2 u ∧ ((u.gpr .x23).toNat≠0 ↔ 1+1≠2) := by
  obtain ⟨kt,ft,ct,t20,t1,t23,t22,ca,sa,rb⟩ := ht
  have sA : Region.Sub ⟨p+1680,16⟩ ⟨p,2048⟩ := Offset.sub_base p (by decide)
  have sB : Region.Sub ⟨p+1696,16⟩ ⟨p,2048⟩ := Offset.sub_base p (by decide)
  refine WP.mono (bothBody_ok (by rw [t20,t1]; exact rb) ct) fun u hu => ?_
  rw [t1] at hu
  have u23 : u.gpr .x23=0 := by rw [hu.x23,t23]; rfl
  refine ⟨⟨(kt.trans hu.keep).mono,ft.trans (hu.frame.mono (by simp [bothWrites])),hu.constants,u23,
    by rw [hu.flag,t22],?_,?_,hu.coeffs,hu.checkpoint⟩,?_⟩
  · refine coeffs_frame ca (sampleAfter_length_le h.left.len A 56) hu.frame ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    exact ⟨h.apart,h.farA.symm.sub_right sB⟩
  · refine checkpoint_frame sa hu.frame ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    exact ⟨h.farB.sub_left sA,Offset.disjoint p (by decide) (by decide) (by decide)⟩
  · rw [u23]; decide

/-- `extraBoth`'s start: the first stream's pointers, the flag and the count. -/
theorem bothStart_ok {w16 : Bool} {s : State} {p a b : Addr} {L M : List Zq} {A B : Nat→Byte}
    (h : BothReadyW w16 L M A B p a b s) :
    WP isa (.block [.addImm .x .x20 .x19 400,.addImm .x .x1 .x19 1680,.movz .x .x22 1 0,
      .movz .x .x23 2 0]) s (BothInv w16 L M A B p a b s 0) := by
  have hp := h.pointer
  have blk : WP isa (.block [.addImm .x .x20 .x19 400,.addImm .x .x1 .x19 1680,.movz .x .x22 1 0,
      .movz .x .x23 2 0]) s fun t => Only ([.x20]++[.x1]++[.x22]++[.x23]) s t ∧ t.gpr .x20=p+400 ∧
        t.gpr .x1=p+1680 ∧ t.gpr .x23=2 ∧ t.gpr .x22=1 :=
    wp_addImm (by decide) fun t₁ k₁ e₁ => wp_addImm (by decide) fun t₂ k₂ e₂ =>
      wp_movz fun t₃ k₃ e₃ => wp_movz fun t k₄ e₄ => wp_nil
      ⟨((k₁.trans k₂).trans k₃).trans k₄,
        by rw [k₄.get .x20,k₃.get .x20,k₂.get .x20,e₁,hp]; rfl,
        by rw [k₄.get .x1,k₃.get .x1,e₂,k₁.get .x19,hp]; rfl,
        by rw [e₄]; rfl,
        by rw [k₄.get .x22,e₃]; rfl⟩
  refine WP.mono (Rej8.WP.constants blk h.constants (by rfl)) fun t ⟨⟨kt,t20,t1,t23,t22⟩,ct⟩ => ?_
  exact ⟨kt.keep.mono,by rw [kt.mem]; exact Frame.refl _ _,ct,t20,t1,t23,t22,h.left.only kt,h.right.only kt⟩

theorem extraBoth_ok {w16 : Bool} {s : State} {p a b : Addr} {L M : List Zq} {A B : Nat→Byte}
    (h : BothReadyW w16 L M A B p a b s) :
    WP isa (Impl.MlKem.AArch64.Paired.extraBoth w16) s
      (BothPostW w16 (sampleAfter L A 56) (sampleAfter M B 56) p a b s) := by
  refine WP.seq (WP.mono (bothStart_ok h) fun t i0 => ?_)
  refine WP.seq (WP.mono (count_loop (n:=2) (cr:=.x23) (body:=bothBody w16) (by decide)
    (BothInv w16 L M A B p a b s) (fun k hk v hv => ?_) i0) fun u hu => ?_)
  · rcases (show k=0 ∨ k=1 by omega) with rfl|rfl
    · exact bothStep0_ok h hv
    · exact bothStep1_ok h hv
  obtain ⟨ku,fu,cu,_,u22,ca,sa,cb,sb⟩ := hu
  have fin : WP isa (.block [Impl.MlKem.AArch64.mov .x6 .x22]) u fun v =>
      Only [.x6] u v ∧ v.gpr .x6=u.gpr .x22 := wp_mov fun v kv ev => wp_nil ⟨kv,ev⟩
  refine WP.mono (Rej8.WP.constants fin cu (by rfl)) fun v ⟨⟨kv,ev⟩,cv⟩ => ?_
  refine ⟨(ku.trans kv.keep).mono,by rw [kv.mem]; exact fu,by rw [kv.mem]; exact ca,
    by rw [kv.mem]; exact cb,by rw [kv.mem]; exact sa,by rw [kv.mem]; exact sb,?_,cv⟩
  rw [ev,u22]; unfold fullFlag; split_ifs <;> simp_all

end VG.Proof.MlKem.AArch64.Paired
