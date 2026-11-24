module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.StandaloneEntry
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.StandaloneEncrypt
import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.PaddedCT
import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
public import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Standalone

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Standalone
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Gcm (Block blockAt blocks ctxH inc32 ghash)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (padA)
open VG.Impl.AesGcm.AArch64.Contiguous.Standalone (entry padded)
variable {wn : Nat} {W : Addr} {s u t : State}

abbrev nonce (s : State) := bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat
abbrev aadBytes (s : State) := bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat
abbrev J (s : State) := Spec.Gcm.j0 (ctxH s.mem (s.gpr .x0)) (nonce s)
abbrev aadHash (s : State) := ghash (ctxH s.mem (s.gpr .x0)) (blocks (padA (aadBytes s)))

structure FrontOut (wn : Nat) (W : Addr) (s t : State) : Prop where
  input : EncIn wn (s.gpr .x1).toNat (stackArg s 0).toNat (s.gpr .x0) (W+16#64) W s.sp
    (s.gpr .x6) (s.gpr .x7) (inc32 (J s)) (aadHash s) t
  j : blockAt t.mem (W+16#64) = J s
  alen : t.mem.readW (W+224#64) 64 = s.gpr .x5
  len : t.mem.readW (W+240#64) 64 = stackArg s 0
  tag : t.mem.readW (W+248#64) 64 = stackArg s 1
  x28 : t.gpr .x28 = stackArg s 1
  saved : SavedAt t.mem W s
  frame : Frame [workR wn W] s.mem t.mem
  rd : t.rd=s.rd
  wr : t.wr=s.wr

theorem jArgs (c : Inner wn W s) (e : Entry wn W s u) :
    J0In wn (s.gpr .x0) (W+16#64) W s.sp u.gpr (ctxH s.mem (s.gpr .x0)) (s.gpr .x2) (s.gpr .x3).toNat u := by
  have hc := c.lay.cw'.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))
  exact ⟨e.env,fun _ _ => rfl,e.x23,by simpa using e.x24,by simpa using e.x26,e.x27,c.iv.of_eq e.rd e.wr,
    blockAt_frame e.frame (by simpa only [List.mem_singleton,forall_eq] using hc)⟩

abbrev aadLoads : List Instr := [.ldr .x .x23 .x19 aadO,.ldr .x .x24 .x19 alenO]

theorem aadLoads_ok {n : Nat} {Ctx St SP A : Addr} (env : Env wn Ctx St W SP s)
    (ptr : s.mem.readW (W+216#64) 64=A) (len : s.mem.readW (W+224#64) 64=BitVec.ofNat 64 n) :
    WP isa (.block aadLoads) s fun t => t.gpr .x23=A ∧ t.gpr .x24=BitVec.ofNat 64 n ∧ Regs [.x23,.x24] s t := by
  have r := env.perm.wR (d := 216) (n := 8) (by decide)
  have l := env.perm.wR (d := 224) (n := 8) (by decide)
  have p : s.mem.read (W+216#64) 8=A := ptr
  have n' : s.mem.read (W+224#64) 8=BitVec.ofNat 64 n := len
  refine WP.of_runBlock ⟨_,by arun [aadLoads,env.x19,aadO,alenO,r,l,p,n'],?_,?_,?_⟩
  · simp [gpr_write]
  · simp [gpr_write]
  · exact ⟨by others_tac,rfl,rfl,rfl,rfl⟩

abbrev jf (s u : State) (W : Addr) (wn : Nat) (z : State) :=
  J0Out wn (s.gpr .x0) (W+16#64) W s.sp u.gpr (ctxH s.mem (s.gpr .x0)) (nonce s) u.mem z

theorem runJ (v : GcmImpl) (c : Inner wn W s) (e : Entry wn W s u) :
    WP isa (j0 v.callees) u (jf s u W wn) := by
  have bytes := bytesAt_frame e.frame (by simpa only [List.mem_singleton,forall_eq] using c.iv.w) (Nat.le_of_lt c.iv.lt)
  simpa only [jf,nonce,bytes] using j0_ok c.lay v (jArgs c e)

theorem loadJ {z : State} (c : Inner wn W s) (e : Entry wn W s u) (q : jf s u W wn z) :
    WP isa (.block aadLoads) z fun t => t.gpr .x23=s.gpr .x4 ∧ t.gpr .x24=s.gpr .x5 ∧ Regs [.x23,.x24] z t := by
  have ptr := (slot_kept q.frame (slots_j0Frame c.lay) (d := 216) (by decide) (by decide)).trans e.aad
  have len := (slot_kept q.frame (slots_j0Frame c.lay) (d := 224) (by decide) (by decide)).trans e.alen
  simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using aadLoads_ok (n := (s.gpr .x5).toNat) q.env ptr (by simpa using len)

abbrev padFrame (St W : Addr) := absFrame St W 16 ++ tFrame St W 16
theorem pad_sub (St W : Addr) : ∀ r ∈ padFrame St W, ∃ q ∈ j0Frame St W, r.Sub q := by
  intro r h
  simp only [padFrame,absFrame,tFrame,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact ⟨⟨St,80⟩,.head _,Offset.sub_base _ (by decide)⟩ | exact ⟨_,by simp [j0Frame],fun _ h => h⟩

theorem slot_jf {C St : Addr} (L : Lay wn C St W) {d : Nat} (lo : 112≤d) (hi : d+8≤512) :
    ∀ r ∈ j0Frame St W, (slotR W d).Disjoint r := by
  have bounds := L.hWn
  intro r h
  simp only [j0Frame,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl
  · simpa using (L.st_wn (a := 0) (n := 80) (d := d) (k := 8) (by decide) (.inr ⟨by omega,by omega⟩)).symm
  · exact Offset.disjoint W (.inr (by omega)) (by omega) (by decide)
  · exact Offset.disjoint W (.inl hi) (by omega) (by decide)

theorem pad_blk {C St : Addr} (L : Lay wn C St W) {d : Nat} (pos : d=0 ∨ d=48) :
    ∀ r ∈ padFrame St W, (⟨St+BitVec.ofNat 64 d,16⟩:Region).Disjoint r := by
  have bounds := L.hWn
  intro r h
  simp only [padFrame,absFrame,tFrame,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at h
  have hd : d+16≤80 := by omega
  have st (k : Nat) (hk : d+16≤k ∨ k+16≤d) (endK : k+16≤80) := L.st_st (a := d) (n := 16) (d := k) (k := 16) hk hd endK
  have wk (k len : Nat) (start : 96≤k) (endK : k+len≤wn) := L.st_wn (a := d) (n := 16) (d := k) (k := len) hd (.inr ⟨start,endK⟩)
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl
  · exact st 16 (by omega) (by decide)
  · exact st 32 (by omega) (by decide)
  · exact wk 512 256 (by decide) (by omega)
  · exact st 16 (by omega) (by decide)
  · exact wk 96 16 (by decide) (by omega)
  · exact wk 512 256 (by decide) (by omega)

abbrev frontCode (v : Calls) : Prog isa :=
  .seq (.block entry) (.seq (j0 v.callees) (.seq (.block aadLoads) (padded v.callees)))

theorem front_then_ok {v : Calls} {tail : Prog isa} {Q : State → Prop}
    (h : WP isa (.seq (frontCode v) tail) s Q) :
    WP isa (.seq (.block entry) (.seq (j0 v.callees) (.seq (.block aadLoads) (.seq (padded v.callees) tail)))) s Q := by
  simpa only [frontCode,WP.seq_iff (M := isa)] using h

theorem front_then_rel {v : Calls} {tail : Prog isa}
    (h : RelCT isa (Eq2 s t) (.seq (frontCode v) tail) TT) :
    RelCT isa (Eq2 s t) (.seq (.block entry) (.seq (j0 v.callees) (.seq (.block aadLoads) (.seq (padded v.callees) tail)))) TT := by
  intro a b tr ur x y pub aa bb
  cases aa with | seq a₁ aa =>
    cases aa with | seq a₂ aa =>
      cases aa with | seq a₃ aa =>
        cases aa with | seq a₄ az =>
          cases bb with | seq b₁ bb =>
            cases bb with | seq b₂ bb =>
              cases bb with | seq b₃ bb =>
                cases bb with | seq b₄ bz =>
                  have eq := h _ _ _ _ _ _ pub (.seq (.seq a₁ (.seq a₂ (.seq a₃ a₄))) az) (.seq (.seq b₁ (.seq b₂ (.seq b₃ b₄))) bz)
                  simpa only [List.append_assoc] using eq

theorem front_ok (v : GcmImpl) (c : Inner wn W s) :
    WP isa (frontCode v.calls) s (FrontOut wn W s) := by
  refine WP.seq ((entry_ok c).mono ?_)
  intro u e
  refine WP.seq ((WP.with_rdwr (runJ v c e)).mono ?_)
  intro z ⟨j,jr,jw⟩
  refine WP.seq ((loadJ c e j).mono ?_)
  intro a ⟨a23,a24,ar⟩
  have L := c.lay
  have permR := ar.rd.trans (jr.trans e.rd)
  have permW := ar.wr.trans (jw.trans e.wr)
  have aData := c.aad.of_eq permR permW
  have y := Proof.Gcm.absorbed_nil (b := W+16#64+32#64) (ctxH s.mem (s.gpr .x0)) ((congrArg (fun m => blockAt m _) ar.mem).trans j.y)
  have key := (congrArg (fun m => blockAt m _) ar.mem).trans j.hH
  have n : a.gpr .x24=BitVec.ofNat 64 (s.gpr .x5).toNat := by simpa using a24
  refine (WP.with_rdwr (padded_ok L v (j.env.of_regs ar) (j.kept.of_others ar.others) a23 n aData key (by decide) y)).mono ?_
  intro b ⟨p,pr,pw⟩
  have mr : Frame (j0Frame (W+16#64) W) u.mem b.mem :=
    j.frame.trans (by rw [← ar.mem]; exact p.frame.sub (pad_sub _ _))
  have ws (q : Region) (hq : q ∈ j0Frame (W+16#64) W) : q.Sub (workR wn W) :=
    frontFrame_work W L.hWn q (List.mem_append_left _ hq)
  have ff : Frame [workR wn W] s.mem b.mem := e.frame.trans (mr.sub (fun q hq => ⟨_,.head _,ws q hq⟩))
  have rd := pr.trans permR
  have wr := pw.trans permW
  have slot (d : Nat) (hd : 112≤d) (hd' : d+8≤512) := mr.readW (r := slotR W d) (a := W+BitVec.ofNat 64 d) (w := 64) (Region.contains_self _ _) (slot_jf L hd hd') (by decide)
  have cb := (blockAt_frame p.frame (pad_blk L (d := 48) (.inr rfl))).trans ((congrArg (fun m => blockAt m _) ar.mem).trans j.cb)
  have init : blockAt b.mem (W+16#64) = J s := by
    have := blockAt_frame p.frame (pad_blk L (d := 0) (.inl rfl))
    simpa using this.trans ((congrArg (fun m => blockAt m _) ar.mem).trans (by simpa using j.j0))
  have fA : Frame [workR wn W] s.mem a.mem := by
    rw [ar.mem]
    exact e.frame.trans (j.frame.sub (fun q hq => ⟨_,.head _,ws q hq⟩))
  have A : bytesAt a.mem (s.gpr .x4) (s.gpr .x5).toNat = aadBytes s :=
    bytesAt_frame fA (by simpa only [List.mem_singleton,forall_eq] using c.aad.w) (Nat.le_of_lt c.aad.lt)
  have absorbed := p.hash.1
  simp only [List.nil_append,A] at absorbed
  change blockAt b.mem _ = ghash _ (blocks ((padA (aadBytes s)).take (Proof.Gcm.whole (padA (aadBytes s)).length))) at absorbed
  rw [Proof.Gcm.whole_of_mod (Proof.Gcm.length_padA_mod _),List.take_length] at absorbed
  refine ⟨⟨p.env,c.nr,by simpa using (p.kept .x22 (by decide)).trans e.x22,c.src.of_eq rd wr,c.dst.of_eq rd wr,c.mode,
    (slot 232 (by decide) (by decide)).trans e.src,by simpa using (slot 240 (by decide) (by decide)).trans e.len,
    (slot 336 (by decide) (by decide)).trans e.dst,Proof.Gcm.ctr_zero _ _ _ _ cb,absorbed⟩,init,
    (slot 224 (by decide) (by decide)).trans e.alen,(slot 240 (by decide) (by decide)).trans e.len,
    (slot 248 (by decide) (by decide)).trans e.tag,(p.kept .x28 (by decide)).trans e.x28,
    e.saved.frame mr (saved_j0Frame L),ff,rd,wr⟩

theorem front_rel (v : GcmImpl) (ca : Inner wn W s) (cb : Inner wn W t) (pub : onePub 2 s t) :
    RelCT isa (Eq2 s t) (frontCode v.calls) TT := by
  obtain ⟨ctx,_,iv,nl,aad,al,_,_,sp,_⟩ := pub
  refine rel_seq (entry_rel ca cb sp) (entry_ok ca) (entry_ok cb) ?_
  intro u w ea eb
  have ia := jArgs ca ea
  have ib := jArgs cb eb
  rw [←ctx,←sp,←iv,←nl] at ib
  refine rel_seq (j0_rel ca.lay v ia ib) (WP.with_rdwr (runJ v ca ea)) (WP.with_rdwr (runJ v cb eb)) ?_
  intro x z ⟨ja,ra,wa⟩ ⟨jb,rb,wb⟩
  refine rel_seq (rel_taint [.x19] (ja.env.sp.trans (sp.trans jb.env.sp.symm)) (by agree_tac [ja.env.x19,jb.env.x19])
    ⟨_,by taint_decide⟩) (loadJ ca ea ja) (loadJ cb eb jb) ?_
  intro a b ⟨pa,na,ar⟩ ⟨pb,nb,br⟩
  have env := jb.env.of_regs br
  have data := cb.aad.of_eq (br.rd.trans (rb.trans eb.rd)) (br.wr.trans (wb.trans eb.wr))
  rw [←ctx,←sp] at env
  rw [←aad,←al] at data
  rw [←aad] at pb
  rw [←al] at nb
  exact padded_rel ca.lay v (ja.env.of_regs ar) env pa pb (by simpa using na) (by simpa using nb)
    (ca.aad.of_eq (ar.rd.trans (ra.trans ea.rd)) (ar.wr.trans (wa.trans ea.wr))) data

end VG.Proof.AesGcm.AArch64.Contiguous.Standalone
