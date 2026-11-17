module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Resume
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Context
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.NextBlock
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Memory
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dd10Step
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdStore
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Blocks
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Pair
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.MlKem.AArch64.Paired
public import VerifiedGarbage.Proof.MlKem.AArch64.Lay
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Checkpoint
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Vector
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Keep
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Segment
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Store
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Continue
import VerifiedGarbage.Proof.MlKem.Arith

/-! ### `MlKem.AArch64.Paired.ExtraBoth`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Paired.Extra`, which this module and modules that import it used -/

section

/-! # One continued rejection stream and its checkpoint -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

structure ExtraPostW (w16 : Bool) (L : List Zq) (B : Nat → Byte) (aP p : Addr) (s u : State) : Prop where
  keep : Keep [.x0,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15] s u
  frame : Frame [polyRegion aP,⟨p,16⟩] s.mem u.mem
  coeffs : Rej8.Scalar.CoeffsW w16 u.mem aP (sampleAfter L B 56)
  checkpoint : checkpointW w16 p aP (sampleAfter L B 56) u.mem
  x3 : u.gpr .x3=cAddr w16 aP (sampleAfter L B 56).length
  x4 : (u.gpr .x4).toNat=256-(sampleAfter L B 56).length
  flagValue : (u.gpr .x0).toNat=if (sampleAfter L B 56).length=256 then 1 else 0

/-- `extraReject`: the stream's buffer at `x20`, its cursor at `x1`. -/
theorem extra_ok {w16 : Bool} (s : State)
    {B : Nat → Byte} {L : List Zq} {aP : Addr}
    (hp : Rej8.EnvW w16 56 B (s.gpr .x20) aP s) (hc : Rej8.Constants s)
    (hl : L.length≤256) (hcoeff : Rej8.Scalar.CoeffsW w16 s.mem aP L)
    (hcp : checkpointW w16 (s.gpr .x1) aP L s.mem)
    (h0 : InRegions s.wr (s.gpr .x1) 8)
    (h1 : InRegions s.wr (s.gpr .x1+8) 8)
    (hd : (polyRegion aP).Disjoint ⟨s.gpr .x1,16⟩) :
    WP isa (Impl.MlKem.AArch64.Paired.extraReject w16) s
      (ExtraPostW w16 L B aP (s.gpr .x1) s) := by
  have z0 : ∀ x : Addr, x+BitVec.ofNat 64 0=x := ptr_zero
  have h0' : InRegions s.wr (s.gpr .x1+BitVec.ofNat 64 0) 8 := by rw [z0]; exact h0
  have h1' : InRegions s.wr (s.gpr .x1+BitVec.ofNat 64 (0+8)) 8 := h1
  refine WP.seq (WP.mono (load_checkpoint s (r:=.x1) (slot:=0) (by decide) (by decide) (in_rd_wr h0')
    (in_rd_wr h1')) fun a ⟨ha,hv,h3,h4⟩ => ?_)
  have a3 : a.gpr .x3=cAddr w16 aP L.length := by rw [h3,z0]; exact hcp.1
  have a4 : (a.gpr .x4).toNat=256-L.length := by rw [h4]; exact hcp.2
  have ac : Rej8.Constants a := ⟨by rw [hv]; exact hc.index,by rw [hv]; exact hc.mask,
    by simpa only [hv] using hc.q,by simpa only [hv] using hc.weights,by simpa only [hv] using hc.zero⟩
  have ap : Rej8.EnvW w16 56 B (a.gpr .x20) aP a := by
    rw [ha.get .x20]
    exact hp.transfer ha.mem ha.rd ha.wr (ha.get .x16)
  refine WP.ite (a.gpr .x4 == 0) (eval_zero _ _) (fun hz => ?_) (fun _ => ?_)
  · rw [eq_zero_iff,decide_eq_true_eq,a4] at hz
    have full : L.length=256 := by omega_using [hl, hz]
    have eqL : sampleAfter L B 56=L := sampleAfter_full (t := 0) full 56 (by omega_using [])
    refine wp_movz fun u hu eu => wp_nil ?_
    refine ⟨(ha.keep.trans hu.keep).mono (by simp),?_,?_,?_,?_,?_,?_⟩
    · rw [hu.mem,ha.mem]; exact Frame.refl _ _
    · rw [eqL,hu.mem,ha.mem]; exact hcoeff
    · rw [eqL,hu.mem,ha.mem]; exact hcp
    · rw [eqL,hu.get .x3,a3]
    · rw [eqL,hu.get .x4,a4]
    · rw [eqL,eu,ite_eq_left full]; rfl
  · have hrun := continue_ok a ap ac hl (by rw [ha.mem]; exact hcoeff) a3 a4
    change WP isa (.seq (.block continueEntry)
      (.seq (Impl.MlKem.AArch64.Rej8.rejLoop w16) (.block _))) a _
    apply WP.assoc
    refine WP.seq (WP.mono hrun fun b ⟨kb,fb,cb,b3,b4,b0⟩ => ?_)
    have b1 : b.gpr .x1=s.gpr .x1 := (kb.get .x1).trans (ha.get .x1)
    refine WP.mono (store_ok b (r:=.x1) (slot:=0) (by decide) (by decide)
      (sampleAfter_length_le hl B 56) cb b3 b4
      (by rw [kb.wr,ha.wr,b1]; exact h0')
      (by rw [kb.wr,ha.wr,b1]; exact h1')
      (by rw [b1,z0]; exact hd)) fun u hu => ?_
    rw [b1,z0] at hu
    refine ⟨((ha.keep.trans kb).trans hu.keep).mono (by simp),?_,hu.coeffs,hu.checkpoint,hu.x3,hu.x4,?_⟩
    · have fb' : Frame [polyRegion aP,⟨s.gpr .x1,16⟩] s.mem b.mem := by
        rw [←ha.mem]
        exact fb.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)
      exact fb'.trans (hu.frame.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp))
    · rw [hu.keep.get .x0,b0]

end VG.Proof.MlKem.AArch64.Paired

end

end

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
  · rcases (show k=0 ∨ k=1 by omega_using [hk]) with rfl|rfl
    · exact bothStep0_ok h hv
    · exact bothStep1_ok h hv
  obtain ⟨ku,fu,cu,_,u22,ca,sa,cb,sb⟩ := hu
  have fin : WP isa (.block [Impl.MlKem.AArch64.mov .x6 .x22]) u fun v =>
      Only [.x6] u v ∧ v.gpr .x6=u.gpr .x22 := wp_mov fun v kv ev => wp_nil ⟨kv,ev⟩
  refine WP.mono (Rej8.WP.constants fin cu (by rfl)) fun v ⟨⟨kv,ev⟩,cv⟩ => ?_
  refine ⟨(ku.trans kv.keep).mono,by rw [kv.mem]; exact fu,by rw [kv.mem]; exact ca,
    by rw [kv.mem]; exact cb,by rw [kv.mem]; exact sa,by rw [kv.mem]; exact sb,?_,cv⟩
  rw [ev,u22]; unfold fullFlag; (repeat' split) <;> simp_all

end VG.Proof.MlKem.AArch64.Paired

end

end

/-! ### `MlKem.AArch64.Paired.ExtraStep`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
variable {sha3 : Bool}
open VG VG.AArch64 VG.Proof.MlKem VG.Spec.MlKem VG.Proof.Sha3.AArch64.Neon

def stepRegs : List Reg := nextRegs++bothRegs
structure StepPostW (w16 : Bool) (A B : Spec.Sha3.State) (L M : List Zq) (p a b c : Addr) (s t : State) : Prop where
 keep : Keep stepRegs s t
 frame : Frame (stepWrites p a b) s.mem t.mem
 frameFine : Frame [⟨p,1712⟩,polyRegion a,polyRegion b] s.mem t.mem
 context : Context p a b c t
 pointer : t.gpr .x19=p
 pair : PairAt t.mem p (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B)
 left : Rej8.Scalar.CoeffsW w16 t.mem a L
 right : Rej8.Scalar.CoeffsW w16 t.mem b M
 saveLeft : checkpointW w16 (p+1680) a L t.mem
 saveRight : checkpointW w16 (p+1696) b M t.mem
 flagBoth : (t.gpr .x6).toNat=if L.length=256 ∧ M.length=256 then 1 else 0
 constants : Rej8.Constants t

theorem extraStep_ok {w16 : Bool} {s : State} {p a b c : Addr} {A B : Spec.Sha3.State} {L M : List Zq}
 (ctx : Context p a b c s) (hp : s.gpr .x19=p) (sym : s.syms "VG_MLKEM_REJ_SHUFFLE"=c)
 (pair : PairAt s.mem p A B) (hl : L.length≤256) (hm : M.length≤256)
 (ca : Rej8.Scalar.CoeffsW w16 s.mem a L) (cb : Rej8.Scalar.CoeffsW w16 s.mem b M)
 (sa : checkpointW w16 (p+1680) a L s.mem) (sb : checkpointW w16 (p+1696) b M s.mem) :
 WP isa (Impl.MlKem.AArch64.Paired.extraStep sha3 w16) s
 (StepPostW w16 A B (sampleAfter L (Proof.Sha3.byteOf (Spec.Sha3.keccakF A)) 56)
 (sampleAfter M (Proof.Sha3.byteOf (Spec.Sha3.keccakF B)) 56) p a b c s) := by
 have grouped : WP isa (.seq (nextBlock sha3) (Impl.MlKem.AArch64.Paired.extraBoth w16)) s
     (StepPostW w16 A B (sampleAfter L (Proof.Sha3.byteOf (Spec.Sha3.keccakF A)) 56)
       (sampleAfter M (Proof.Sha3.byteOf (Spec.Sha3.keccakF B)) 56) p a b c s) := by
  refine WP.seq (WP.mono_syms (nextBlock_ok (sha3 := sha3) hp ctx.scratch pair) fun u h hsym => ?_)
  rcases h with ⟨ku,fu,precise,up,pu,ra,rb,cs,ut⟩
  have fu' : Frame (stepWrites p a b) s.mem u.mem := fu.mono (by simp [stepWrites])
  have cu := ctx.frame ku.rd ku.wr fu'
  have ux : u.gpr .x16=c := by rw [ut,hsym,sym]
  have ua := coeffs_frame ca hl fu (by intro r hr; rw [List.mem_singleton.mp hr]; exact ctx.farA.symm)
  have ub := coeffs_frame cb hm fu (by intro r hr; rw [List.mem_singleton.mp hr]; exact ctx.farB.symm)
  have checkpoints {off : Nat} (ho : off=1680 ∨ off=1696) :
      ∀r∈nextWrites p,(Region.mk (p+BitVec.ofNat 64 off) 16).Disjoint r := by
   have hlo : 1680≤off := by omega_using [ho]
   have hhi : off≤1696 := by omega_using [ho]
   intro r hr
   simp only [nextWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl|rfl|rfl|rfl
   · exact Offset.disjoint_base p (d:=off) (n:=16) (k:=400) (by omega_using [ho]) (by omega_using [ho])
   · exact Offset.disjoint p (d:=off) (n:=16) (e:=400) (k:=168) (by omega_using [ho]) (by omega_using [ho]) (by decide)
   · exact Offset.disjoint p (d:=off) (n:=16) (e:=904) (k:=168) (by omega_using [ho]) (by omega_using [ho]) (by decide)
   · exact Offset.disjoint p (d:=off) (n:=16) (e:=1536) (k:=136) (by omega_using [ho]) (by omega_using [ho]) (by decide)
   · exact Offset.disjoint p (d:=off) (n:=16) (e:=1408) (k:=8) (by omega_using [ho]) (by omega_using [ho]) (by decide)
  have usa := checkpoint_frame sa precise (checkpoints (Or.inl rfl))
  have usb := checkpoint_frame sb precise (checkpoints (Or.inr rfl))
  have ea := cu.envW (w16 := w16) ux (N:=56) (off:=400) (by decide) (by decide) (Or.inl rfl) (fun i hi=>ra.byte hi)
  have eb := cu.envW (w16 := w16) ux (N:=56) (off:=904) (by decide) (by decide) (Or.inr rfl) (fun i hi=>rb.byte hi)
  have iw {o l : Nat} (h : o+l≤2048) := Noise.inScratch cu.scratch h (by decide)
  have ready : BothReadyW w16 L M (Proof.Sha3.byteOf (Spec.Sha3.keccakF A))
      (Proof.Sha3.byteOf (Spec.Sha3.keccakF B)) p a b u :=
    ⟨up,cu.scratch,cu.farA,cu.farB,cu.apart,
      ⟨ea,hl,ua,usa,iw (o:=1680) (by decide),by rw [BitVec.add_assoc]; exact iw (o:=1688) (by decide),
        cu.farA.symm.sub_right (Offset.sub_base p (by decide))⟩,
      ⟨eb,hm,ub,usb,iw (o:=1696) (by decide),by rw [BitVec.add_assoc]; exact iw (o:=1704) (by decide),
        cu.farB.symm.sub_right (Offset.sub_base p (by decide))⟩,
      by intro mask hmask; rw [ux]; exact cu.tableScratch.sub_left (Rej8.table_sub c hmask),cs⟩
  refine WP.mono (extraBoth_ok ready) fun t ht => ?_
  have ft : Frame (stepWrites p a b) u.mem t.mem := ht.frame.sub (by
   intro r hr
   simp only [bothWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl|rfl|rfl
   · exact ⟨polyRegion a,by simp [stepWrites],fun _ h=>h⟩
   · exact ⟨polyRegion b,by simp [stepWrites],fun _ h=>h⟩
   · exact ⟨⟨p,2048⟩,by simp [stepWrites],Offset.sub_base p (by decide)⟩
   · exact ⟨⟨p,2048⟩,by simp [stepWrites],Offset.sub_base p (by decide)⟩)
  have fine : Frame [⟨p,1712⟩,polyRegion a,polyRegion b] s.mem t.mem := by
   apply (precise.sub ?_).trans (ht.frame.sub ?_)
   · intro r hr
     simp only [nextWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
     rcases hr with rfl|rfl|rfl|rfl|rfl
     · exact ⟨⟨p,1712⟩,by simp,Region.sub_prefix (by decide)⟩
     all_goals exact ⟨⟨p,1712⟩,by simp,Offset.sub_base p (by decide)⟩
   · intro r hr
     simp only [bothWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
     rcases hr with rfl|rfl|rfl|rfl
     · exact ⟨polyRegion a,by simp,fun _ h=>h⟩
     · exact ⟨polyRegion b,by simp,fun _ h=>h⟩
     all_goals exact ⟨⟨p,1712⟩,by simp,Offset.sub_base p (by decide)⟩
  refine ⟨(ku.trans ht.keep).mono (by decide),fu'.trans ft,fine,cu.frame ht.keep.rd ht.keep.wr ft,
    (ht.keep.get .x19).trans up,?_,ht.left,ht.right,ht.saveLeft,ht.saveRight,
    ht.flagBoth,ht.constants⟩
  exact pair_frame pu ht.frame (by
   intro r hr; simp only [bothWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl|rfl|rfl
   · exact cu.farA.sub_left (Region.sub_prefix (by decide))
   · exact cu.farB.sub_left (Region.sub_prefix (by decide))
   · exact Offset.base_disjoint p (by decide) (by decide)
   · exact Offset.base_disjoint p (by decide) (by decide))
 exact WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc grouped)) fun _ h => WP.assoc h)
end VG.Proof.MlKem.AArch64.Paired

end

end


/-! # Complete the paired matrix sampler within the shared five-block bound -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
variable {sha3 : Bool}
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem VG.Proof.Sha3

theorem advance_ok {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s : State} {n : Nat}
    (h : ProgressW w16 A B n p a b c s) (hs : s.syms "VG_MLKEM_REJ_SHUFFLE"=c) :
    WP isa (Impl.MlKem.AArch64.Paired.extraStep sha3 w16) s (AdvancedW w16 A B (n+1) p a b c s) := by
  have run := extraStep_ok (sha3 := sha3) h.context h.ptr hs h.pair (accepted_length A n) (accepted_length B n)
    h.left h.right h.saveLeft h.saveRight
  have ea : sampleAfter (accepted A n) (byteOf (Spec.Sha3.keccakF (iterF n A))) 56=accepted A (n+1) :=
    accepted_next A n
  have eb : sampleAfter (accepted B n) (byteOf (Spec.Sha3.keccakF (iterF n B))) 56=accepted B (n+1) :=
    accepted_next B n
  rw [ea,eb] at run
  refine WP.mono run fun t ht => ?_
  exact ⟨ht.keep.mono (by decide),ht.frameFine,
    ⟨ht.context,ht.pointer,ht.pair,ht.left,ht.right,ht.saveLeft,ht.saveRight⟩,ht.flagBoth⟩

theorem extraPair_ok {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s : State}
    (h : ProgressW w16 A B 3 p a b c s) (hs : s.syms "VG_MLKEM_REJ_SHUFFLE"=c) :
    WP isa (Impl.MlKem.AArch64.Paired.extraPair sha3 w16) s (ResumePostW w16 A B p a b s) :=
  resume_ok (sha3 := sha3) (fun _ ht hs=>advance_ok (sha3 := sha3) ht hs) h hs

end VG.Proof.MlKem.AArch64.Paired
