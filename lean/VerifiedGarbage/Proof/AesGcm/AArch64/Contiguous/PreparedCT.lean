module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.PreparedSeal
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.BatchCT
import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GenericAlignedCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.SealPw
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Prepared
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Finish

/-! The lengths, key size and addresses determine the trace of the prepared
seal. The two runs may have different keys, plaintexts and ciphertexts. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Prepared

open VG VG.AArch64 VG.Impl.AesGcm.AArch64 VG.Impl.AesGcm.AArch64.Contiguous
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint)
open VG.Proof.Gcm.AArch64.Pmull (MulKey)
open VG.Spec.Gcm (Block)

theorem final_rel {wn R n j : Nat} {Ctx W SP O Tg : Addr} {a b : State} {H H' : Block} {al bl : Nat}
    (v : GcmImpl) (mk : MulKey) (L : Lay wn Ctx (word W 16) W)
    (ea : Env wn Ctx (word W 16) W SP a) (eb : Env wn Ctx (word W 16) W SP b)
    (da : DataOk wn (word W 16) W a O n) (db : DataOk wn (word W 16) W b O n)
    (ka : Fast.KeyAt H a.mem W) (kb : Fast.KeyAt H' b.mem W)
    (hj : j ≤ n) (hl : n-j <16) (ha : al < 2^64) (hb : bl < 2^64)
    (aa : a.mem.readW (word W alenO) 64 = BitVec.ofNat 64 al) (ab : b.mem.readW (word W alenO) 64 = BitVec.ofNat 64 bl)
    (ra : a.gpr .x22 = BitVec.ofNat 64 R) (rb : b.gpr .x22 = BitVec.ofNat 64 R) (rounds : R=10 ∨ R=12 ∨ R=14)
    (pa : a.gpr .x23 = word O j) (pb : b.gpr .x23 = word O j)
    (la : a.gpr .x24 = BitVec.ofNat 64 (n-j)) (lb : b.gpr .x24 = BitVec.ofNat 64 (n-j))
    (na : a.gpr .x26 = BitVec.ofNat 64 n) (nb : b.gpr .x26 = BitVec.ofNat 64 n)
    (ta : a.gpr .x28 = Tg) (tb : b.gpr .x28 = Tg) (hv : v.ctr.scratch ≤ wn-512) :
    RelCT isa (Eq2 a b) (finalPart v.callees) TT := by
  refine rel_seq (rel_taint [.x19,.x20,.x21,.x23,.x24,.x26] (ea.sp.trans eb.sp.symm)
    (by agree_tac [ea.x19,eb.x19,ea.x20,eb.x20,ea.x21,eb.x21,pa,pb,la,lb,na,nb]) ⟨_,by taint_decide⟩)
    (finish_ok mk L ea da ka hj hl ha aa ra rounds pa la na)
    (finish_ok mk L eb db kb hj hl hb ab rb rounds pb lb nb) ?_
  intro u z ⟨_,_,uk,up,_⟩ ⟨_,_,zk,zp,_⟩
  refine rel_seq (rel_ctrLe v.ctr hv up.call zp.call (up.env.sp.trans zp.env.sp.symm))
    (tagCall_ok L v (.inl rfl) up hv) (tagCall_ok L v (.inl rfl) zp hv) ?_
  intro t w ht hw
  exact rel_taint [.x19,.x28] (ht.env.sp.trans hw.env.sp.symm)
    (by agree_tac [ht.env.x19,hw.env.x19,ht.kept .x28 (by decide),hw.kept .x28 (by decide),uk,zk,ta,tb]) ⟨_,by taint_decide⟩

theorem auth_rel {wn n : Nat} {Ctx St W SP O P : Addr} {a b : State}
    (v : GcmImpl) (g : GhashWithImpl) (fused : Bool) (L : Lay wn Ctx St W)
    (ea : Env wn Ctx St W SP a) (eb : Env wn Ctx St W SP b)
    (da : DataOk wn St W a O n) (db : DataOk wn St W b O n)
    (oa : a.gpr .x27 = word O (done fused n)) (ob : b.gpr .x27 = word O (done fused n))
    (na : a.mem.readW (word W lenO) 64 = BitVec.ofNat 64 n) (nb : b.mem.readW (word W lenO) 64 = BitVec.ofNat 64 n)
    (pa : GhWCall a Ctx (word St 16) (word W 512) P) (pb : GhWCall b Ctx (word St 16) (word W 512) P)
    (sa : a.mem.readW (word a.sp 16) 64 = P) (sb : b.mem.readW (word b.sp 16) 64 = P)
    (ra : InRegions (a.rd++a.wr) (word a.sp 16) 8) (rb : InRegions (b.rd++b.wr) (word b.sp 16) 8) :
    RelCT isa (Eq2 a b) (.seq (.block (authRemainder fused)) (Impl.AesGcm.AArch64.Fast.pwSel v.callees 16 g.fn)) TT := by
  refine rel_seq (rel_taint [.x19,.x20,.x21,.x27] (ea.sp.trans eb.sp.symm)
    (by agree_tac [ea.x19,eb.x19,ea.x20,eb.x20,ea.x21,eb.x21,oa,ob]) (by cases fused <;> exact ⟨_,by taint_decide⟩))
    (WP.with_rdwr (authCallArgs (x := []) fused L ea da oa na rfl (by decide)))
    (WP.with_rdwr (authCallArgs (x := []) fused L eb db ob nb rfl (by decide))) ?_
  intro u z ⟨⟨_,_,_,hu,mu⟩,rd,wr⟩ ⟨⟨_,_,_,hz,mz⟩,rd',wr'⟩
  have su := hu.env.sp.trans ea.sp.symm
  have sz := hz.env.sp.trans eb.sp.symm
  exact pwSel_rel v g (k := 16) (by decide)
    (by rw [su,mu]; exact sa) (by rw [su,rd,wr]; exact ra)
    (by rw [sz,mz]; exact sb) (by rw [sz,rd',wr']; exact rb)
    hu.call ⟨by rw [rd,wr]; exact pa.reads,pa.yp,pa.sp,mu ▸ pa.repr⟩
    hz.call ⟨by rw [rd',wr']; exact pb.reads,pb.yp,pb.sp,mz ▸ pb.repr⟩ (hu.env.sp.trans hz.env.sp.symm)

theorem enc_rel {wn R n : Nat} {Ctx W D O P : Addr} {a b : State} {aa ai ba bi : List Byte}
    (v : GcmImpl) (fused : Bool) (gh : Proof.Gcm.AArch64.Stitch.Gh8Ok) (L : Lay wn Ctx (word W 16) W)
    (x : Ready wn R n Ctx W D O P aa ai a) (y : Ready wn R n Ctx W D O P ba bi b)
    (sp : a.sp = b.sp) (hn : fused = true → 128 ≤ n) (hv : v.ctr.scratch ≤ wn-512) :
    RelCT isa (Eq2 a b) (encPart v.callees fused (!v.stitch)) TT := by
  have start {u : State} {m iv : List Byte} (q : Ready wn R n Ctx W D O P m iv u) :=
    prefix_ok fused (!v.stitch) L q.env gh q.rates q.x22 q.x23 q.x26 q.src q.dst q.mode hn q.powers q.pw q.pRead q.sourceSlot
      q.dstSlot q.cb q.y (by simpa only [paddedAad,List.length_append,Proof.Gcm.length_zeros] using Proof.Gcm.length_pad_mod m.length)
  have batch : RelCT isa (Eq2 a b) (if fused then batches (!v.stitch) else .block []) TT := by
    cases fused
    · change RelCT isa (Eq2 a b) (.block []) TT
      exact rel_taint [] sp (by agree_tac []) ⟨.block [] 256,by decide⟩
    · refine batches_rel (!v.stitch) x.env (sp ▸ y.env) ?_ x.x26 x.src.lt x.powers y.powers x.pw y.pw x.pRead y.pRead x.dstSlot y.dstSlot
      intro r hr ne
      simp only [Fast.stRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact (ne rfl).elim
      · exact x.env.x19.trans y.env.x19.symm
      · exact x.env.x20.trans y.env.x20.symm
      · exact x.env.x21.trans y.env.x21.symm
      · exact x.x22.trans y.x22.symm
      · exact x.x23.trans y.x23.symm
      · exact x.x26.trans y.x26.symm
  refine rel_seq batch (start x) (start y) ?_
  intro u z f h
  have slot {s u : State} {m iv : List Byte} (q : Ready wn R n Ctx W D O P m iv s)
      (f : Prefix wn R n (done fused n) Ctx (word W 16) W s.sp D O (paddedAad m) (Spec.Gcm.inc32 (Spec.Gcm.j0 (Spec.Gcm.ctxH s.mem Ctx) iv)) s u) :
      u.mem.readW (word W dstO) 64 = O :=
    ((prefix_writes (done_le fused n) L.hWn.1 f.frame).readW (r := slotR W dstO) (Region.contains_self _ _)
      (writes_slot L (by decide) (by decide) q.dst.ok) (by decide)).trans q.dstSlot
  have setup {s u : State} {m iv : List Byte} (q : Ready wn R n Ctx W D O P m iv s)
      (f : Prefix wn R n (done fused n) Ctx (word W 16) W s.sp D O (paddedAad m) (Spec.Gcm.inc32 (Spec.Gcm.j0 (Spec.Gcm.ctxH s.mem Ctx) iv)) s u) :=
    remainder_ok fused f.x23 f.x26 q.src.lt f.env.x19 (f.env.perm.wR (by decide)) (slot q f)
  refine rel_seq (rel_taint [.x19] (f.env.sp.trans (sp.trans h.env.sp.symm)) (by agree_tac [f.env.x19,h.env.x19])
    (by cases fused <;> exact ⟨_,by taint_decide⟩)) (setup x f) (setup y h) ?_
  intro s t fs ht
  have build {s u t : State} {m iv : List Byte} (q : Ready wn R n Ctx W D O P m iv s)
      (f : Prefix wn R n (done fused n) Ctx (word W 16) W s.sp D O (paddedAad m) (Spec.Gcm.inc32 (Spec.Gcm.j0 (Spec.Gcm.ctxH s.mem Ctx) iv)) s u)
      (r : TailArgs fused n D O u t) : CrInG wn true Ctx (word W 16) W s.sp t.gpr R (done fused n)
         (word D (done fused n)) (word O (done fused n)) (n-done fused n) t := by
    have n22 := f.x22.trans q.x22
    refine r.crIn f.env ?_ ?_ (q.src.of_eq f.rd f.wr) (q.dst.of_eq f.rd f.wr) q.mode
    · rw [n22]; rcases q.rates with e|e|e <;> rw [e] <;> decide
    · rw [n22,toNat_ofNat_of_lt (by rcases q.rates with e|e|e <;> rw [e] <;> decide)]
  exact DirectGather.Generic.aligned_rel L v (build x f fs) (sp ▸ build y h ht) (done_mod ..) hv

theorem record_rel {wn R n : Nat} {Ctx W D O P : Addr} {a b : State} {aa ai ba bi : List Byte}
    (v : GcmImpl) (g : GhashWithImpl) (fused : Bool) (gh : Proof.Gcm.AArch64.Stitch.Gh8Ok) (mk : MulKey)
    (L : Lay wn Ctx (word W 16) W)
    (x : Ready wn R n Ctx W D O P aa ai a) (y : Ready wn R n Ctx W D O P ba bi b)
    (ext : External wn n W O P a) (ext' : External wn n W O P b)
    (sp : a.sp = b.sp) (tag : a.gpr .x28 = b.gpr .x28) (hla : aa.length < 2^64) (hlb : ba.length < 2^64)
    (hn : fused = true → 128 ≤ n) (hv : v.ctr.scratch ≤ wn-512) :
    RelCT isa (Eq2 a b) (.seq (if fused then batches (!v.stitch) else .block []) <| .seq (.block (remainder fused)) <|
      .seq (Impl.AesGcm.AArch64.DirectGather.aligned v.callees) <| .seq (.block (authRemainder fused)) <|
      .seq (Impl.AesGcm.AArch64.Fast.pwSel v.callees 16 g.fn) <|
      .seq (.block (Impl.AesGcm.AArch64.Fast.hReload ++ Impl.Gcm.AArch64.Pmull.loadRev Impl.Gcm.AArch64.Pmull.Y .x20 16 ++
        [mov .x13 .x24,mov .x12 .x23])) <| .seq Impl.AesGcm.AArch64.Fast.padMulT <|
      .seq (.block Impl.AesGcm.AArch64.Fast.lensTag) <| .seq (ctrCall v.callees) <| .seq (.block tagOut) (.block restore)) TT := by
  apply Fast.RelCT.seq_assoc3
  refine rel_seq (enc_rel v fused gh L x y sp hn hv) (encPart_ok v fused gh L x hn hv)
    (encPart_ok v fused gh L y hn hv) ?_
  intro u w f h
  obtain ⟨nu,_,_,pu,su,ru⟩ := f.authInput fused L x ext
  obtain ⟨nw,_,_,pw,sw,rw'⟩ := h.authInput fused L y ext'
  apply Fast.RelCT.seq_assoc
  refine rel_seq (auth_rel v g fused L f.env (sp ▸ h.env) (x.dst.ok.of_eq f.rd f.wr) (y.dst.ok.of_eq h.rd h.wr)
    f.x27 h.x27 nu nw pu pw su sw ru rw') (authenticate_ok v g fused L x ext f) (authenticate_ok v g fused L y ext' h) ?_
  intro i j m k
  have inputs {a t : State} {aad nonce : List Byte} {z : Nat} (q : Ready wn R n Ctx W D O P aad nonce a)
      (h : Auth wn R n z Ctx W D O aad nonce a t) :
      Fast.KeyAt (Spec.Gcm.ctxH a.mem Ctx) t.mem W ∧ t.mem.readW (word W alenO) 64 = BitVec.ofNat 64 aad.length :=
    ⟨q.key.frame h.frame (writes_slot L (by decide) (by decide) q.dst.ok),
      (h.frame.readW (r := slotR W alenO) (Region.contains_self _ _) (writes_slot L (by decide) (by decide) q.dst.ok) (by decide)).trans q.aadSlot⟩
  obtain ⟨ki,li⟩ := inputs x m
  obtain ⟨kj,lj⟩ := inputs y k
  apply Fast.RelCT.seq_assoc3
  exact final_rel v mk L m.env (sp ▸ k.env) (x.dst.ok.of_eq m.rd m.wr) (y.dst.ok.of_eq k.rd k.wr)
    ki kj m.bound m.last hla hlb li lj (m.x22.trans x.x22) (k.x22.trans y.x22) x.rates m.x23 k.x23 m.x24 k.x24 m.x26 k.x26
    m.x28 (k.x28.trans tag.symm) hv

end VG.Proof.AesGcm.AArch64.Contiguous.Prepared
