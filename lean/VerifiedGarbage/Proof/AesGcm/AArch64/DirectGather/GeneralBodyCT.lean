module

public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.DirectGeneral
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GeneralSetup
public import VerifiedGarbage.Proof.AesGcm.AArch64.SealCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GeneralSetup
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.DirectGeneral
import VerifiedGarbage.Proof.AesGcm.AArch64.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.AesGcm.AArch64.Tag
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.DirectBody
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GenericLoopCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.LoopCT
meta import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.DirectBody

/-! Public addresses and lengths determine the traces of scratch initialization,
nonce processing, and additional-data hashing. -/
@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (blockAt)

theorem generalSetup_rel {o p s t : State} {wn : Nat} (a : GeneralEntry o s wn) (b : GeneralEntry p t wn)
    (sp : o.sp = p.sp) :
    RelCT isa (Eq2 s t) (.block (oneEntry 24 ++ gatherSlots ++ stashArg 16)) TT := by
  have load {u x : State} (e : GeneralEntry u x wn) := ldr9_ok (k := 24) (by decide) e.work
    (show InRegions (x.rd++x.wr) (x.sp+24) 8 by
      rw [e.wr,e.sp]; exact ⟨_,List.mem_append_right _ (List.mem_cons_self ..),
        Offset.contains_base _ (by change 24+8≤wn+32; omega) (by decide)⟩)
  have eqSP : s.sp = t.sp := by rw [a.sp,b.sp,genBase,genBase,sp]
  change RelCT isa _ (.block ([.ldrSp .x9 24] ++ ((oneEntry 24).tail ++ gatherSlots ++ stashArg 16))) _
  apply RelCT.block_split
  refine rel_seq (rel_taint [] eqSP (by agree_tac []) ⟨_,by taint_decide⟩) (load a) (load b)
    fun _ _ ⟨sa,_,spa,_,_⟩ ⟨sb,_,spb,_,_⟩ => ?_
  have w : genWork o wn = genWork p wn := by simp only [genWork,genBase,sp]
  exact rel_taint [.x9] (by rw [spa,spb,eqSP]) (by agree_tac [sa,sb,w]) ⟨_,by taint_decide⟩

abbrev generalAadOff : List Instr := [.ldr .x .x25 .x19 alenO,imm .x9 15,.logic .and .x .x25 .x25 .x9]
abbrev aadCode (c : Callees) : Prog isa := .seq (.seq (.seq (j0 c) (oneAad c)) (.block generalAadOff)) (flush c 16)

private theorem off_ok {wn al : Nat} {C St W SP : Addr} {s : State} (e : Env wn C St W SP s)
    (slot : s.mem.readW (W+224#64) 64 = BitVec.ofNat 64 al) (ha : al<2^64) :
    WP isa (.block generalAadOff) s (fun t => t.gpr .x25 = BitVec.ofNat 64 (al%16) ∧ Regs [.x25,.x9] s t) := by
  have rd := e.perm.wR (d := 224) (n := 8) (by decide)
  refine WP.of_runBlock ⟨_,by arun [generalAadOff,e.x19,rd],?_⟩
  refine ⟨?_,by others_tac,rfl,rfl,rfl,rfl⟩
  simp only [gpr_write,ite_true,ite_false,reduceCtorEq,BitVec.setWidth_eq]
  rw [show s.mem.read (W+224#64) 8 = s.mem.readW (W+224#64) 64 from rfl,slot,
    show BitVec.setWidth 64 (15#16) <<< 0 = BitVec.ofNat 64 15 by decide,and15,toNat_ofNat_of_lt ha]

abbrev AadOut {wn nl al n : Nat} {C St W SP N A D : Addr} {s : State}
    (_ : FrontIn wn C St W SP s.gpr N A D nl al n s) (t : State) :=
  AadReady wn C St W SP (blockAt s.mem (C+240)) (bytesAt s.mem N nl) (bytesAt s.mem A al) s t

theorem aadCode_ok {wn nl al n : Nat} {C St W SP N A D : Addr} {s : State} (v : GcmImpl)
    (L : Lay wn C St W) (p : FrontIn wn C St W SP s.gpr N A D nl al n s) :
    WP isa (aadCode v.callees) s (AadOut p) := by
  have h := aadReady_ok L v p.env p.x23 p.x24 p.x26 p.x27 p.non p.aad rfl p.sA p.sL
    (H := blockAt s.mem (C+240)) (rest := .block []) (fun _ f => WP.block_nil f)
  exact (WP.seq_iff.mp (WP.assoc' (WP.assoc' (WP.assoc' h)))).mono fun _ => WP.block_nil_iff.mp

theorem aadCode_rel {wn nl al n : Nat} {C St W SP N A D : Addr} {s t : State} (v : GcmImpl)
    (L : Lay wn C St W) (p : FrontIn wn C St W SP s.gpr N A D nl al n s)
    (q : FrontIn wn C St W SP t.gpr N A D nl al n t) : RelCT isa (Eq2 s t) (aadCode v.callees) TT := by
  have front {u : State} (a : FrontIn wn C St W SP u.gpr N A D nl al n u) :=
    (WP.seq_iff.mp (WP.assoc' (aadFront_ok L v a.env a.kept a.x23 a.x24 a.x26 a.x27 a.non a.aad
      (H := blockAt u.mem (C+240)) rfl a.sA a.sL (rest := .block []) fun _ f => WP.block_nil f))).mono
      (fun _ => WP.block_nil_iff.mp)
  apply RelCT.assoc'
  refine rel_seq (nonceAad_rel L v p q) (front p) (front q) fun _ _ f g => ?_
  have a := (slot_kept f.frame (slots_frontFrame L) (d := 224) (by decide) (by decide)).trans p.sL
  have b := (slot_kept g.frame (slots_frontFrame L) (d := 224) (by decide) (by decide)).trans q.sL
  refine rel_seq (rel_taint [.x19] (f.env.sp.trans g.env.sp.symm) (by agree_tac [f.env.x19,g.env.x19])
    ⟨_,by taint_decide⟩) (off_ok f.env a p.aad.lt) (off_ok g.env b q.aad.lt) fun _ _ ⟨h,r⟩ ⟨j,z⟩ => ?_
  exact flush_rel L v (.inr rfl) (f.env.of_regs r) (g.env.of_regs z) (fun _ _ => rfl) (fun _ _ => rfl) h j
    (Nat.mod_lt _ (by decide))
end VG.Proof.AesGcm.AArch64.DirectGather

/-! Relational proof of tag generation, the direct tag store, and register restoration. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather

open VG VG.AArch64 VG.Impl.AesGcm.AArch64

theorem finalCode_rel {wn R : Nat} {Ctx W SP Tg : Addr} {s t : State}
    (v : GcmImpl) (L : Lay wn Ctx (W+16) W) (a : Env wn Ctx (W+16) W SP s)
    (b : Env wn Ctx (W+16) W SP t)
    (sa : s.gpr .x22 = BitVec.ofNat 64 R) (sb : t.gpr .x22 = BitVec.ofNat 64 R)
    (hR : R=10 ∨ R=12 ∨ R=14)
    (ta : s.mem.readW (W+248) 64 = Tg) (tb : t.mem.readW (W+248) 64 = Tg)
    (hv : v.ctr.scratch ≤ wn-512) : RelCT isa (Eq2 s t) (finalCode v.callees) TT := by
  have prep {u : State} (e : Env wn Ctx (W+16) W SP u) :=
    finPrep_ok e.x19 (covers_left e.perm.w) (al := (u.mem.readW (W+224) 64).toNat) (n := (u.mem.readW (W+240) 64).toNat)
      (by simp) (by simp) L.hWn
  refine rel_seq (rel_taint [.x19] (a.sp.trans b.sp.symm) (by agree_tac [a.x19,b.x19]) ⟨_,by taint_decide⟩)
    (prep a) (prep b) fun u w ⟨_,_,ra⟩ ⟨_,_,rb⟩ => ?_
  have ea := a.of_regs ra
  have eb := b.of_regs rb
  have rA := (ra.others _ (by decide : Reg.x22 ∉ [Reg.x26,.x27])).trans sa
  have rB := (rb.others _ (by decide : Reg.x22 ∉ [Reg.x26,.x27])).trans sb
  have oa : u.gpr .x25 = BitVec.ofNat 64 (u.gpr .x25).toNat := by simp
  have ob : w.gpr .x25 = BitVec.ofNat 64 (w.gpr .x25).toNat := by simp
  refine rel_seq (tag_rel L v (.inl rfl) ea eb (fun _ _ => rfl) (fun _ _ => rfl) rA rB hR oa ob hv)
    (tag_ok L v (.inl rfl) ea (fun _ _ => rfl) rA hR oa hv)
    (tag_ok L v (.inl rfl) eb (fun _ _ => rfl) rB hR ob hv) fun _ _ ga gb => ?_
  rw [List.append_assoc]
  apply RelCT.block_split
  refine rel_seq (rel_taint [.x19] (ga.env.sp.trans gb.env.sp.symm) (by agree_tac [ga.env.x19,gb.env.x19])
    ⟨_,by taint_decide⟩)
    (ldr28_ok ga.env ((scratch_slot (scratchFrame_tag ga.frame) L.hWn.2 (d := 248) (by decide) (by decide)).trans
      (ra.mem ▸ ta))) (ldr28_ok gb.env ((scratch_slot (scratchFrame_tag gb.frame) L.hWn.2 (d := 248)
      (by decide) (by decide)).trans (rb.mem ▸ tb))) fun _ _ ⟨x,rx⟩ ⟨y,ry⟩ => ?_
  have ea' := ga.env.of_regs rx
  have eb' := gb.env.of_regs ry
  exact rel_taint [.x19,.x28] (ea'.sp.trans eb'.sp.symm) (by agree_tac [ea'.x19,eb'.x19,x,y]) ⟨_,by taint_decide⟩

end VG.Proof.AesGcm.AArch64.DirectGather

/-! The final hash reads the public suffix after the last interleaved batch. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Gcm (blockAt)
variable {wn n : Nat} {Ctx St W SP D : Addr}

theorem remainderMid {s : State} (e : Env wn Ctx St W SP s) (src : s.gpr .x23 = D)
    (len : s.gpr .x24 = BitVec.ofNat 64 n) (data : DataOk wn St W s D n) :
    AbsMid wn Ctx St W SP s.gpr 16 (blockAt s.mem (Ctx+240)) [] D n (s.gpr .x25).toNat s.mem 0 s :=
  ⟨e,fun _ _ => rfl,Nat.zero_le _,by simpa using src,by simpa using len,by simp,data,rfl,
    fun ha => by simpa [Spec.Aes.bytesAt] using ha,.inr rfl,Frame.refl _ _⟩

theorem absorbRemainder_rel (v : GcmImpl) {s t : State} (L : Lay wn Ctx St W) (ea : Env wn Ctx St W SP s)
    (eb : Env wn Ctx St W SP t) (sa : s.gpr .x23 = D) (sb : t.gpr .x23 = D)
    (la : s.gpr .x24 = BitVec.ofNat 64 n) (lb : t.gpr .x24 = BitVec.ofNat 64 n)
    (da : DataOk wn St W s D n) (db : DataOk wn St W t D n) :
    RelCT isa (Eq2 s t) (absorbAl v.callees 16) TT := by
  let p := remainderMid ea sa la da
  let q := remainderMid eb sb lb db
  refine rel_seq (rel_taint [.x19,.x20,.x21,.x23,.x24] (ea.sp.trans eb.sp.symm)
    (by agree_tac [ea.x19,eb.x19,ea.x20,eb.x20,ea.x21,eb.x21,sa,sb,la,lb]) ⟨_,by taint_decide⟩)
    (absSeg2_ok L (.inr rfl) p) (absSeg2_ok L (.inr rfl) q) fun _ _ x y => ?_
  refine rel_seq (rel_gh v.gh x.call y.call (x.env.sp.trans y.env.sp.symm))
    (absCall2_ok L (.inr rfl) v x) (absCall2_ok L (.inr rfl) v y) fun _ _ ⟨k,_⟩ ⟨l,_⟩ => ?_
  exact rel_taint [.x20,.x23,.x24] (k.env.sp.trans l.env.sp.symm)
    (by agree_tac [k.env.x20,l.env.x20,k.x23,l.x23,k.x24,l.x24]) ⟨_,by taint_decide⟩

abbrev suffixStart : List Instr :=
  [.ldr .x .x23 .x19 Impl.AesGcm.AArch64.DirectGather.hashO, .sub .x .x24 .x26 .x23]

theorem suffixStart_ok {j : Nat} {O : Addr} {s : State} (he : Env wn Ctx St W SP s) (hb : 16*j ≤ n) (hn : n < 2^64)
    (x26 : s.gpr .x26 = O + BitVec.ofNat 64 n) (slot : s.mem.readW (W+352) 64 = O + BitVec.ofNat 64 (16*j)) :
    WP isa (.block suffixStart) s fun t => t.gpr .x23 = O+BitVec.ofNat 64 (16*j) ∧
      t.gpr .x24 = BitVec.ofNat 64 (n-16*j) ∧ Regs [.x23,.x24] s t := by
  have w := he.perm.wR (d := 352) (n := 8) (by decide)
  refine WP.of_runBlock ⟨_, by arun [suffixStart,he.x19,Impl.AesGcm.AArch64.DirectGather.hashO,w],?_⟩
  have load : s.mem.read (W+352#64) 8 = O+BitVec.ofNat 64 (16*j) := slot
  refine ⟨by simp [gpr_write,load],?_,by others_tac,rfl,rfl,rfl,rfl⟩
  simp only [gpr_write,ite_true,ite_false,reduceCtorEq,BitVec.setWidth_eq,load,x26]
  rw [Offset.add_sub_add_left,ofNat_sub hb hn]

theorem tailCode_rel (v : GcmImpl) {j : Nat} {O : Addr} {s t : State} (L : Lay wn Ctx St W)
    (ea : Env wn Ctx St W SP s) (eb : Env wn Ctx St W SP t)
    (da : DataOk wn St W s O n) (db : DataOk wn St W t O n) (hb : 16*j ≤ n)
    (oa : s.gpr .x26 = O+BitVec.ofNat 64 n) (ob : t.gpr .x26 = O+BitVec.ofNat 64 n)
    (pa : s.mem.readW (W+352) 64 = O+BitVec.ofNat 64 (16*j))
    (pb : t.mem.readW (W+352) 64 = O+BitVec.ofNat 64 (16*j)) :
    RelCT isa (Eq2 s t) (tailCode v.callees) TT := by
  refine rel_seq (rel_taint [.x19] (ea.sp.trans eb.sp.symm) (by agree_tac [ea.x19,eb.x19]) ⟨_,by taint_decide⟩)
    (suffixStart_ok ea hb da.lt oa pa) (suffixStart_ok eb hb db.lt ob pb) fun _ _ ⟨p,l,r⟩ ⟨q,m,g⟩ => ?_
  have e := ea.of_regs r
  have f := eb.of_regs g
  have d := (da.drop hb).of_eq r.rd r.wr
  have d' := (db.drop hb).of_eq g.rd g.wr
  refine rel_seq (absorbRemainder_rel v L e f p q l m d d')
    (absorbRemainder_ok L v e p l d rfl (x := []) rfl) (absorbRemainder_ok L v f q m d' rfl (x := []) rfl)
    fun a b ⟨c,x⟩ ⟨z,y⟩ => ?_
  have move (u : State) : WP isa (.block [mov .x25 .x24]) u fun w => w.gpr .x25 = u.gpr .x24 ∧ Regs [.x25] u w := by
    refine WP.of_runBlock ⟨_,by arun [],?_⟩
    exact ⟨by simp [gpr_write],by others_tac,rfl,rfl,rfl,rfl⟩
  refine rel_seq (rel_taint [] (c.env.sp.trans z.env.sp.symm) (by agree_tac []) ⟨_,by taint_decide⟩)
    (move a) (move b) fun _ _ ⟨ax,ar⟩ ⟨by_,br⟩ => ?_
  exact flush_rel L v (.inr rfl) (c.env.of_regs ar) (z.env.of_regs br) (fun _ _ => rfl) (fun _ _ => rfl)
    (ax.trans x) (by_.trans y) (Nat.mod_lt _ (by decide))

end VG.Proof.AesGcm.AArch64.DirectGather

/-! Two general gather calls with the same public arguments and descriptors
take the same branches and access the same addresses throughout. -/
@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather
open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (blockAt)
open VG.Proof.Gcm.AArch64.Stitch (GatherLaws)

private theorem setupFrame {wn : Nat} {o s a : State} (e : GeneralEntry o s wn) (st : BodyEntry o s wn a) :
    Frame [Gather.stkR o] o.mem a.mem := by
  have f : Frame [Gather.stkR o] o.mem s.mem := e.frame.sub fun r h => by
    obtain rfl := List.mem_singleton.mp h
    exact ⟨_,List.mem_singleton_self _,fun x hx => genStack_sub o e.bound x (Region.sub_prefix (by omega : 32 ≤ wn+32) x hx)⟩
  exact f.trans (st.frame.sub fun r h => ⟨_,List.mem_singleton_self _,List.mem_singleton.mp h ▸ genWork_sub o e.bound⟩)

private abbrev PublicFront (wn : Nat) (o s a : State) := FrontIn wn (Gather.K o) (genState o wn) (genWork o wn)
  s.sp a.gpr (Gather.Nn o) (Gather.Ad o) (Gather.Dst o) (Gather.NL o) (Gather.AL o) (Gather.L o) a

private theorem frontIn {wn : Nat} {o s a : State} (e : GeneralEntry o s wn) (hw : 768 ≤ wn) (st : BodyEntry o s wn a) :
    PublicFront wn o s a := by
  have buf := buffers_of e hw (setupFrame e st) st.rd st.wr
  exact ⟨st.env,fun _ _ => rfl,st.x23,by simpa using st.x24,by simpa using st.x26,st.x27,
    buf.nonce,buf.aad,st.aad,by simpa using st.alen,st.dst,st.len⟩

private theorem aadFromOriginal {wn : Nat} {o s a b : State} (e : GeneralEntry o s wn) (st : BodyEntry o s wn a)
    (p : PublicFront wn o s a) (q : AadOut p b) : GeneralAadReady o s wn a b := by
  have f := setupFrame e st
  have apart {r : Region} (h : (Gather.stkR o).Disjoint r) : ∀ k ∈ [Gather.stkR o], r.Disjoint k :=
    fun k hk => List.mem_singleton.mp hk ▸ h.symm
  have H : blockAt a.mem (Gather.K o+240) = generalH o :=
    blockAt_frame f fun k hk => (apart e.lay.bk k hk).sub_left (Lay.ctxSub (by decide))
  have V : bytesAt a.mem (Gather.Nn o) (Gather.NL o) = generalIv o :=
    bytesAt_frame f (apart e.lay.bn) (Nat.le_of_lt (o.gpr .x3).isLt)
  have A : bytesAt a.mem (Gather.Ad o) (Gather.AL o) = generalAad o :=
    bytesAt_frame f (apart e.lay.ba) (Nat.le_of_lt (o.gpr .x5).isLt)
  simpa only [AadOut,H,V,A] using q

private theorem textSetupRun {wn : Nat} {o s a b : State} (hw : 768 ≤ wn) (hi : wn ≤ 2560)
    (st : BodyEntry o s wn a) (f : GeneralAadReady o s wn a b) :
    WP isa (.block textSetup) b (GeneralTextSetup o wn b) := by
  have fr := scratchFrame_Aad f.frame hw
  have slots (d : Nat) (h : 128 ≤ d) (le : d+8 ≤ 512) := scratch_slot fr hi h le
  exact textSetup_ok f.env ((slots 336 (by decide) (by decide)).trans st.desc)
    ((slots 344 (by decide) (by decide)).trans st.count) ((slots 232 (by decide) (by decide)).trans st.dst)

private theorem frontGather_rel {o p s t : State} {wn : Nat} (a : GeneralEntry o s wn) (b : GeneralEntry p t wn)
    (v : GcmImpl) (hw : 768 ≤ wn) (pub : Gather.gatherPub o p) (stitch : Bool)
    (suffix : Prog isa)
    (next : ∀ i j k l x y, BodyEntry o s wn i → BodyEntry p t wn j → GeneralAadReady o s wn i k →
      GeneralAadReady p t wn j l → GeneralTextSetup o wn k x → GeneralTextSetup p wn l y →
      RelCT isa (Eq2 x y) (.seq (Impl.AesGcm.AArch64.DirectGather.pieces v.callees stitch) suffix) TT) :
    RelCT isa (Eq2 s t) (.seq (.block (oneEntry 24 ++ gatherSlots ++ stashArg 16)) <|
      .seq (j0 v.callees) <| .seq (oneAad v.callees) <| .seq (.block generalAadOff) <| .seq (flush v.callees 16) <|
      .seq (Impl.AesGcm.AArch64.DirectGather.text v.callees stitch) suffix) TT := by
  obtain ⟨q0,_,q2,q3,q4,q5,_,_,sp,_,d,len,_,_⟩ := pub
  have sp' : s.sp = t.sp := by simp only [a.sp,b.sp,genBase,sp]
  refine rel_seq (generalSetup_rel a b sp) (generalSetup_ok a hw) (generalSetup_ok b hw) fun i j u w => ?_
  have f := frontIn a hw u
  have g := frontIn b hw w
  have g' : FrontIn wn (Gather.K o) (genState o wn) (genWork o wn) s.sp j.gpr (Gather.Nn o)
      (Gather.Ad o) (Gather.Dst o) (Gather.NL o) (Gather.AL o) (Gather.L o) j := by
    simpa only [PublicFront,Gather.K,Gather.Nn,Gather.Ad,Gather.Dst,Gather.NL,Gather.AL,Gather.L,
      genState,genWork,genBase,q0,q2,q3,q4,q5,sp,sp',d,len] using g
  apply VG.RelCT.assoc
  apply VG.RelCT.assoc
  apply VG.RelCT.assoc
  refine rel_seq (aadCode_rel v (genLay a hw) f g') (aadCode_ok v (genLay a hw) f) (aadCode_ok v (genLay b hw) g)
    fun k l m n => ?_
  have r := aadFromOriginal a u f m
  have z := aadFromOriginal b w g n
  have wrk : genWork o wn = genWork p wn := by simp only [genWork,genBase,sp]
  apply RelCT.assoc'
  refine rel_seq (rel_taint [.x19] (by rw [r.env.sp,z.env.sp,sp']) (by agree_tac [r.env.x19,z.env.x19,wrk])
    ⟨_,by taint_decide⟩) (textSetupRun hw a.bound u r) (textSetupRun hw b.bound w z) (fun x y => next i j k l x y u w r z)

private theorem tailThen {P Q : State → State → Prop} {a b c d e : Prog isa}
    (h : RelCT isa P (.seq (.seq a (.seq b (.seq c d))) e) Q) :
    RelCT isa P (.seq a (.seq b (.seq c (.seq d e)))) Q := by
  intro s t _ _ _ _ p x y
  cases x with | seq a₁ x => cases x with | seq b₁ x => cases x with | seq c₁ x => cases x with | seq d₁ e₁ =>
  cases y with | seq a₂ y => cases y with | seq b₂ y => cases y with | seq c₂ y => cases y with | seq d₂ e₂ =>
  have z := h _ _ _ _ _ _ p (.seq (.seq a₁ (.seq b₁ (.seq c₁ d₁))) e₁)
    (.seq (.seq a₂ (.seq b₂ (.seq c₂ d₂))) e₂)
  simpa only [List.append_assoc] using z

private abbrev finalIn (a : Generic.TextArgs) (Tg : Addr) (u : State) :=
  Env a.Wn a.Ctx a.St a.W a.SP u ∧ u.gpr .x22 = BitVec.ofNat 64 a.R ∧ u.mem.readW (a.W+248) 64 = Tg

private theorem suffix_rel {v : GcmImpl} {stitch : Bool} {a : Generic.TextArgs} {iv : Spec.Gcm.Block}
    {s t : State} {Tg : Addr} (pa : Generic.PiecesPre a s) (pb : Generic.PiecesPre (a.withIcb iv) t)
    (d : Generic.PublicDesc a s t) (hSt : a.St = a.W+16) (hv : v.ctr.scratch ≤ a.Wn-512)
    (gh : stitch=true → GatherLaws)
    (sa : ∀ j u, Generic.TextAt a s a.count j u → WP isa (tailCode v.callees) u (finalIn a Tg))
    (sb : ∀ j u, Generic.TextAt (a.withIcb iv) t a.count j u → WP isa (tailCode v.callees) u (finalIn a Tg)) :
    RelCT isa (Eq2 s t) (.seq (Impl.AesGcm.AArch64.DirectGather.pieces v.callees stitch) <|
      .seq (.block [.ldr .x .x23 .x19 Impl.AesGcm.AArch64.DirectGather.hashO,.sub .x .x24 .x26 .x23]) <|
      .seq (absorbAl v.callees 16) <| .seq (.block [mov .x25 .x24]) <| .seq (flush v.callees 16) (finalCode v.callees)) TT := by
  have len : a.total s = (a.withIcb iv).total t := Gather.gl_agree d (Nat.le_refl a.count)
  have hash := Generic.hashCount_eq (iv := iv) stitch d (Nat.le_refl a.count)
  refine rel_seq (Generic.pieces_rel v stitch pa pb d hv gh) (Generic.pieces_exact v stitch pa hv gh)
    (Generic.pieces_exact v stitch pb hv gh) fun u w x y => ?_
  apply tailThen
  have m : DataOk a.Wn a.St a.W u a.dst (a.total s) := pa.dst.ok.of_eq x.rd x.wr
  have n : DataOk a.Wn a.St a.W w a.dst (a.total s) := len ▸ pb.dst.ok.of_eq y.rd y.wr
  have yw : w.gpr .x26 = Generic.atOff a.dst (a.total s) := len ▸ y.dst
  have yh : w.mem.readW (a.W+352) 64 = Generic.atOff a.dst (16*Generic.hashCount stitch a s a.count) :=
    hash ▸ y.hashPtr
  refine rel_seq (tailCode_rel v pa.lay x.env y.env m n x.hashBound x.dst yw x.hashPtr yh)
    (sa _ _ x) (sb _ _ y) fun _ _ ⟨ea,ra,ta⟩ ⟨eb,rb,tb⟩ => ?_
  exact finalCode_rel v (hSt ▸ pa.lay) (hSt ▸ ea) (hSt ▸ eb) ra rb pa.rounds ta tb hv

private theorem descBeforeText {o s : State} (e : Gather.Lay .plain o) (f : Frame [Gather.stkR o] o.mem s.mem)
    {i : Nat} (h : i < Gather.Cnt o*16) (lt : i<2^64) :
    o.mem (Gather.Src o+BitVec.ofNat 64 i) = s.mem (Gather.Src o+BitVec.ofNat 64 i) := by
  exact inputsAgree e f _ (List.mem_cons_self ..) _ (Offset.contains_base _ (by
    change i+1 ≤ Gather.Cnt o * 16; omega) lt)

private theorem finishRun {wn j : Nat} {o s a b c t : State} (v : GcmImpl) (e : GeneralEntry o s wn) (hw : 768 ≤ wn)
    (st : BodyEntry o s wn a) (f : GeneralAadReady o s wn a b) (z : GeneralTextSetup o wn b c)
    (total : (generalArgs o s wn).total c = Gather.L o) (p : Generic.TextAt (generalArgs o s wn) c (Gather.Cnt o) j t) :
    WP isa (tailCode v.callees) t (finalIn (generalArgs o s wn) (Gather.Tg o)) :=
  (generalTail_ok v e hw st f z p).mono fun _ ⟨env,x22,_,frame,_,_⟩ =>
    ⟨env,x22.trans p.x22,(generalFinSlot (d := 248) e hw f z total p frame (by decide) (by decide)).trans st.tag⟩

theorem generalBody_rel {o p s t : State} {wn : Nat} (v : GcmImpl) (stitch : Bool)
    (a : GeneralEntry o s wn) (b : GeneralEntry p t wn) (pub : Gather.gatherPub o p)
    (hw : 768 ≤ wn) (hv : v.ctr.scratch ≤ wn-512) (gh : stitch = true → GatherLaws) :
    RelCT isa (Eq2 s t) (Impl.AesGcm.AArch64.DirectGather.body v.callees stitch) TT := by
  refine frontGather_rel a b v hw pub stitch _ fun _ _ _ _ x y st₁ st₂ r₁ r₂ z₁ z₂ => ?_
  obtain ⟨pr,total,frame⟩ := generalPiecesPre a hw st₁ r₁ z₁
  obtain ⟨qr,total',frame'⟩ := generalPiecesPre b hw st₂ r₂ z₂
  obtain ⟨q0,q1,_,_,_,_,q6,q7,sp,_,dst,_,tg,pubDs⟩ := pub
  have sp' : s.sp = t.sp := by simp only [a.sp,b.sp,genBase,sp]
  let args := generalArgs o s wn
  let args' := generalArgs p t wn
  have eqArgs : args.withIcb args'.icb = args' := by
    simp only [args,args',generalArgs,Generic.TextArgs.withIcb,Gather.K,genState,genWork,genBase,
      Gather.Src,Gather.Cnt,Gather.Dst,q0,q1,sp,sp',q6,q7,dst]
  have d : Generic.PublicDesc args x y := by
    intro i hi
    have lt := pr.descLt
    have bound : i < 2^64 := by
      change i < Gather.Cnt o*16 at hi; change 16*Gather.Cnt o < 2^64 at lt; omega
    have first := descBeforeText a.lay frame hi bound
    have hi' : i < Gather.Cnt p*16 := by simpa only [args,generalArgs,Gather.Cnt,q7] using hi
    have second := descBeforeText b.lay frame' hi' bound
    exact first.symm.trans ((pubDs i hi).trans (by simpa only [Gather.Src,← q6] using second))
  have qr' : Generic.PiecesPre (args.withIcb args'.icb) y := by rw [eqArgs]; exact qr
  refine suffix_rel (Tg := Gather.Tg o) pr qr' d rfl hv gh
    (fun _ _ w => finishRun v a hw st₁ r₁ z₁ total w) fun j u w => ?_
  have w' : Generic.TextAt args' y args'.count j u := by
    rw [← eqArgs]; exact w
  have fin := finishRun v b hw st₂ r₂ z₂ total' w'
  have same : finalIn args (Gather.Tg o) = finalIn args' (Gather.Tg p) := by
    rw [← eqArgs]; simp only [Generic.TextArgs.withIcb,Gather.Tg,tg]
  exact same ▸ fin
end VG.Proof.AesGcm.AArch64.DirectGather
