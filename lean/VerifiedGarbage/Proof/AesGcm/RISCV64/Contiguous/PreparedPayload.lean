module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.PreparedAuth
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.PayloadCT
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.AesGcm.RISCV64.Contiguous

/-! # A single authentication pass for either layout and both tag finishing paths -/

public section
namespace VG.Proof.AesGcm.RISCV64.Contiguous
open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64 VG.Impl.AesGcm.RISCV64.Contiguous VG.Impl.Gcm.RISCV64.Prepared
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_seq rel_taint)

private theorem envTaint {V : Reg → BitVec 64} {sp : Addr} {c : Prog isa} (rs : List Reg)
    (pub : ∀ r∈rs,r∈frozen) {hint : VG.Taint.Hint taint.T}
    (check : (taint.check (Taint.ofRegs rs) c hint).isSome=true) : CT (Env V sp) c :=
  CT.taint rs (fun _ _ a b => ⟨a.sp.trans b.sp.symm,fun r hr => (a.fr r (pub r hr)).trans (b.fr r (pub r hr)).symm⟩) check

private theorem tagFinish_ct {V : Reg → BitVec 64} {sp bk : Addr} {tail : Prog isa} (L : Lay (V .s2) (V .s1) (V .s0))
    (last : CT (Env V sp) tail) :
    CT (AuthEnv V sp bk) (.seq (.block [mov .s4 .s10,mov .s6 .s11]) (.seq (lensWith preparedInvocation 16) tail)) := by
  refine CT.seq (J:=AuthEnv V sp bk) ((envTaint [.s10,.s11] (by decide) (by taint_decide)).mono fun s v => v.1)
    (fun s ⟨e,q⟩ => ?_) ?_
  · refine Steps.wp_mv fun v a => Steps.wp_mv fun u b => WP.block_nil ?_
    have kt : Keeps s u := ⟨b.mem.trans a.mem,b.rd.trans a.rd,b.wr.trans a.wr,b.sp.trans a.sp⟩
    exact ⟨e.keep (fun r hr => (b.other _ (by revert r;decide)).trans (a.other _ (by revert r;decide)))
      kt.sp kt.rd kt.wr,q.kept kt⟩
  refine CT.seq (J:=Env V sp)
    (preparedCT fun _ _ ⟨e,q⟩ ⟨j,k⟩ => preparedLens_rel (.inr rfl) ⟨V,rfl,rfl,rfl,e⟩
      ⟨V,rfl,rfl,rfl,j⟩ q.temp_nonce k.temp_nonce)
    (fun s ⟨e,q⟩ => WP.mono (lens_ok_with L (.inr rfl) e rfl q.temp_nonce.action) fun _ h => h.1) last

private theorem authenticatePrepared {V : Reg → BitVec 64} {sp bk D : Addr} {s t : State} {tail : Prog isa}
    (L : Lay (V .s2) (V .s1) (V .s0)) (a : Env V sp s) (b : Env V sp t)
    (ds : DataOk (V .s1) (V .s0) s D (V .s11).toNat) (dt : DataOk (V .s1) (V .s0) t D (V .s11).toNat)
    (ss : s.mem.readW (V .s0+BitVec.ofNat 64 dataO) 64=D) (st : t.mem.readW (V .s0+BitVec.ofNat 64 dataO) 64=D)
    (p : nonceScope V sp bk s) (q : nonceScope V sp bk t) (last : CT (AuthEnv V sp bk) tail) :
    RelCT isa (Eq2 s t) (.seq (.block dataArgs) (.seq (absorbWith preparedInvocation 16)
      (.seq (.block [.logicImm .and .s6 .s11 15]) (.seq (flushWith preparedInvocation 16) tail)))) TT := by
  have args {u : State} (e : Env V sp u) (rd : DataOk (V .s1) (V .s0) u D (V .s11).toNat)
      (slot : u.mem.readW (V .s0+BitVec.ofNat 64 dataO) 64=D) (sc : nonceScope V sp bk u) :
      WP isa (.block dataArgs) u (AuthIn V sp bk D .s11) := by
    refine WP.mono (dataArgs_ok e L.wal slot) fun v ⟨r4,r5,r6,regs,k⟩ => ⟨⟨_,?_,r4,r5,r6,rd.of_eq k.rd k.wr k.sp,rfl⟩,sc.kept k⟩
    exact e.keep (fun r hr => regs r (by revert r;decide) (by revert r;decide) (by revert r;decide)) k.sp k.rd k.wr
  have fin : CT (AuthRem V sp bk .s11) (.seq (flushWith preparedInvocation 16) tail) :=
    CT.seq (preparedFlush_ct L) (fun _ h => preparedFlush_wp L h) last
  have auth := preparedAuth_ct (D:=D) L (.inr rfl) fin
  refine rel_seq (rel_taint [.s0] (a.sp.trans b.sp.symm) (fun r hr =>
    by obtain rfl := List.mem_singleton.mp hr;rw [a.s0,b.s0]) (by taint_decide))
    (args a ds ss p) (args b dt st q) fun u v eu ev =>
      RelCT.mono auth (fun x y ⟨hx,hy⟩ => by subst x y;exact ⟨eu,ev⟩) (fun _ _ _ => trivial)

abbrev payloadScope (V : Reg → BitVec 64) (sp bk D : Addr) :=
  HashScope (V .s2+BitVec.ofNat 64 240) bk (sealWrites (V .s1) (V .s0) D sp (V .s11).toNat)

theorem preparedShort_rel {V : Reg → BitVec 64} {sp bk X D : Addr} {R : Nat} {ha hb : Spec.Gcm.Block}
    {a b : List Byte} {s t : State} (L : Lay (V .s2) (V .s1) (V .s0))
    (p : PayloadIn V sp X D R ha a s) (q : PayloadIn V sp X D R hb b t) (small : (V .s11).toNat≤240)
    (ps : payloadScope V sp bk D s) (qs : payloadScope V sp bk D t) :
    RelCT isa (Eq2 s t) (shortPayloadWith preparedInvocation) TT := by
  have run {v : State} {H : Spec.Gcm.Block} {aad : List Byte} (h : PayloadIn V sp X D R H aad v) :=
    maskData_wp h.env L h.src h.dst (n := (V .s11).toNat) (by simpa using h.len) small h.read h.write h.buffers h.roundsReg h.rounds h.keys
  apply RelCT.assoc
  refine rel_seq (maskData_rel L p q small) (run p) (run q)
    fun u v ⟨eu,ku,fu,_,_⟩ ⟨ev,kv,fv,_,_⟩ => authenticatePrepared L eu ev
      (p.write.ok.of_eq ku.rd ku.wr ku.sp) (q.write.ok.of_eq kv.rd kv.wr kv.sp)
      ((data_slot L p.write fu).trans p.slot) ((data_slot L q.write fv).trans q.slot)
      ((ps.after ku (fu.sub data_sealSub)).narrow j0_sealSub)
      ((qs.after kv (fv.sub data_sealSub)).narrow j0_sealSub) ?_
  exact tagFinish_ct L (envTaint [.s0,.s1] (by decide) (by taint_decide))

theorem preparedLong_rel {V : Reg → BitVec 64} {sp bk X D : Addr} {R : Nat} {ha hb : Spec.Gcm.Block}
    {a b : List Byte} {s t : State} (L : Lay (V .s2) (V .s1) (V .s0))
    (p : PayloadIn V sp X D R ha a s) (q : PayloadIn V sp X D R hb b t)
    (ps : payloadScope V sp bk D s) (qs : payloadScope V sp bk D t) :
    RelCT isa (Eq2 s t) (longPayloadWith preparedInvocation) TT := by
  have ss {v : State} {H : Spec.Gcm.Block} {aad : List Byte} (h : PayloadIn V sp X D R H aad v) :
      CrMB true true (V .s7) (V .s2) (V .s1) (V .s0) sp R X D (V .s11).toNat 0 0 v :=
    ⟨V,_,0,v.mem,rfl,rfl,rfl,rfl,h.start,fun _ => ⟨rfl,h.keys⟩⟩
  have rc : RelCT isa (Eq2 s t) (.seq (cryptWholeB true true) (cryptTailB true true)) TT :=
    RelCT.mono (longCtr_ct L) (fun x y ⟨hx,hy⟩ => by subst x y;exact ⟨ss p,ss q⟩) (fun _ _ _ => trivial)
  apply RelCT.assoc
  refine rel_seq rc (p.crypt L) (q.crypt L) fun u v ⟨ou,ru,wu⟩ ⟨ov,rv,wv⟩ => ?_
  have su := ou.env.sp.trans p.env.sp.symm
  have sv := ov.env.sp.trans q.env.sp.symm
  refine authenticatePrepared L ou.env ov.env (p.write.ok.of_eq ru wu su) (q.write.ok.of_eq rv wv sv)
    ((slot_keep ou.frame (slot_crFrame L p.write (by decide))).trans p.slot)
    ((slot_keep ov.frame (slot_crFrame L q.write (by decide))).trans q.slot)
    ((ps.after ⟨ru,wu,su⟩ (ou.frame.sub crypt_sealSub)).narrow j0_sealSub)
    ((qs.after ⟨rv,wv,sv⟩ (ov.frame.sub crypt_sealSub)).narrow j0_sealSub) ?_
  exact tagFinish_ct L (envTaint [.s0,.s1,.s3,.s7] (by decide) (by taint_decide))

end VG.Proof.AesGcm.RISCV64.Contiguous
