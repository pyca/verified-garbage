module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.PreparedNonce
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.AesGcm.RISCV64

/-! # Shared authentication of associated data or ciphertext using the prepared table -/

public section
namespace VG.Proof.AesGcm.RISCV64
open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64 VG.Impl.Gcm.RISCV64.Prepared
open VG.Spec.Gcm (blockAt)
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_seq rel_taint rel_ite)

abbrev AuthIn (V : Reg → BitVec 64) (sp bk D : Addr) (r : Reg) (s : State) :=
  (∃ H,AbsIn V sp 16 H [] D (V r).toNat s) ∧ nonceScope V sp bk s

abbrev AuthEnv (V : Reg → BitVec 64) (sp bk : Addr) (s : State) :=
  Env V sp s ∧ nonceScope V sp bk s

abbrev AuthRem (V : Reg → BitVec 64) (sp bk : Addr) (r : Reg) (s : State) :=
  AuthEnv V sp bk s ∧ s.gpr .s6=BitVec.ofNat 64 ((V r).toNat%16)

theorem preparedAuth_ct {V : Reg → BitVec 64} {sp bk D : Addr} {r : Reg} {tail : Prog isa}
    (L : Lay (V .s2) (V .s1) (V .s0)) (reg : r=.s10 ∨ r=.s11)
    (done : CT (AuthRem V sp bk r) tail) :
    CT (AuthIn V sp bk D r) (.seq (absorbWith preparedInvocation 16) (.seq (.block [.logicImm .and .s6 r 15]) tail)) := by
  refine CT.seq (J:=AuthEnv V sp bk) (preparedCT fun _ _ ⟨⟨H,a⟩,q⟩ ⟨⟨H',b⟩,k⟩ =>
    preparedAbsorb_rel L (.inr rfl) ⟨V,H,[],rfl,rfl,rfl,rfl,a⟩ ⟨V,H',[],rfl,rfl,rfl,rfl,b⟩ q k)
    (fun s ⟨⟨_,a⟩,q⟩ => WP.mono (WP.with_rdwr (absorbFresh_ok_with L (.inr rfl) a rfl
      (FramedHashAction.now q.action))) fun t ⟨v,rd,wr,stack⟩ =>
        ⟨v.env,q.after ⟨rd,wr,stack⟩ (v.frame.sub abs16_j0)⟩) ?_
  refine CT.seq (J:=AuthRem V sp bk r) ?_ (fun s ⟨e,q⟩ => ?_) done
  · have agree (f : r∈frozen) : ∀ s t, AuthEnv V sp bk s → AuthEnv V sp bk t →
        s.sp=t.sp ∧ ∀ k∈[r],s.gpr k=t.gpr k := by
      intro s t a b
      exact ⟨a.1.sp.trans b.1.sp.symm,fun k hk => by obtain rfl := List.mem_singleton.mp hk;rw [a.1.fr _ f,b.1.fr _ f]⟩
    rcases reg with rfl|rfl
    · exact CT.taint [.s10] (agree (by decide)) (by taint_decide)
    · exact CT.taint [.s11] (agree (by decide)) (by taint_decide)
  · refine Steps.wp_andi (by decide) fun t op => WP.block_nil ?_
    have f : r∈frozen := by rcases reg with rfl|rfl <;> decide
    refine ⟨⟨e.keep (fun k hk => op.other k (by revert k;decide)) op.sp op.rd op.wr,q.kept ⟨op.mem,op.rd,op.wr,op.sp⟩⟩,?_⟩
    rw [op.gpr,e.fr r f,show BitVec.ofInt 64 15=BitVec.ofNat 64 15 from rfl,and15]

theorem preparedFlush_ct {V : Reg → BitVec 64} {sp bk : Addr} {r : Reg}
    (L : Lay (V .s2) (V .s1) (V .s0)) : CT (AuthRem V sp bk r) (flushWith preparedInvocation 16) :=
  preparedCT fun _ _ ⟨⟨e,q⟩,n⟩ ⟨⟨j,k⟩,m⟩ => preparedFlush_rel L (.inr rfl) (Nat.mod_lt _ (by decide))
    ⟨V,rfl,rfl,rfl,e⟩ ⟨V,rfl,rfl,rfl,j⟩ n m q.temp_nonce k.temp_nonce

theorem preparedFlush_wp {V : Reg → BitVec 64} {sp bk : Addr} {r : Reg} {s : State}
    (L : Lay (V .s2) (V .s1) (V .s0)) (h : AuthRem V sp bk r s) :
    WP isa (flushWith preparedInvocation 16) s (AuthEnv V sp bk) := by
  obtain ⟨⟨e,q⟩,rem⟩ := h
  refine WP.mono (WP.with_rdwr (flush_ok_with L (.inr rfl) (x:=List.replicate (V r).toNat 0) ⟨e,rfl⟩
    (by simpa using rem) q.temp_nonce.action)) fun t ⟨v,rd,wr,stack⟩ => ⟨v.env,q.after ⟨rd,wr,stack⟩ (v.frame.sub t16_j0)⟩

theorem preparedAad_rel {V : Reg → BitVec 64} {sp bk Np A : Addr} {n : Nat} {s t : State} {H H' : Spec.Gcm.Block}
    (L : Lay (V .s2) (V .s1) (V .s0)) (h : J0In V sp H Np n s) (j : J0In V sp H' Np n t)
    (d : DataOk (V .s1) (V .s0) s A (V .s10).toNat) (d' : DataOk (V .s1) (V .s0) t A (V .s10).toNat)
    (sl : s.mem.readW (V .s0+BitVec.ofNat 64 aadO) 64=A) (sl' : t.mem.readW (V .s0+BitVec.ofNat 64 aadO) 64=A)
    (q : nonceScope V sp bk s) (k : nonceScope V sp bk t) :
    RelCT isa (Eq2 s t) (oneAadWith preparedInvocation) TT := by
  let I := fun u => AuthEnv V sp bk u ∧ DataOk (V .s1) (V .s0) u A (V .s10).toNat ∧
    u.mem.readW (V .s0+BitVec.ofNat 64 aadO) 64=A
  have next {v : State} {key : Spec.Gcm.Block} (x : J0In V sp key Np n v)
      (r : DataOk (V .s1) (V .s0) v A (V .s10).toNat) (y : v.mem.readW (V .s0+BitVec.ofNat 64 aadO) 64=A)
      (sc : nonceScope V sp bk v) : WP isa (j0With preparedInvocation) v I :=
    WP.mono (WP.with_rdwr (j0_ok_with L x sc.action)) fun u ⟨out,rd,wr,st⟩ =>
      ⟨⟨out.env,sc.after ⟨rd,wr,st⟩ out.frame⟩,r.of_eq rd wr st,(slot_keep out.frame (slot_j0 L x.env.stk' (by decide))).trans y⟩
  have start := preparedJ0_ct (V:=V) (sp:=sp) (bk:=bk) (Np:=Np) L h.data.lt h.s7
  refine rel_seq (RelCT.mono start (fun i v ⟨rfl,rfl⟩ => ⟨⟨⟨H,h⟩,q⟩,⟨⟨H',j⟩,k⟩⟩) (fun _ _ _ => trivial))
      (next h d sl q) (next j d' sl' k) fun i v x y => ?_
  have st {u : State} (z : I u) : WP isa (.block [.load .d .s4 .s0 aadO,mov .s5 .s10,.li .s6 0]) u
      (AuthIn V sp bk A .s10) := by
    obtain ⟨⟨e,sc⟩,rd,slot⟩ := z
    refine WP.mono (aadArgs_ok L e slot) fun v ⟨r4,r5,r6,regs,keep⟩ =>
      ⟨⟨_,e.keep (fun r hr => regs r (by revert r;decide) (by revert r;decide) (by revert r;decide)) keep.sp keep.rd keep.wr,
        r4,r5,r6,rd.of_eq keep.rd keep.wr keep.sp,rfl⟩,sc.kept keep⟩
  refine rel_seq (rel_taint [.s0] (x.1.1.sp.trans y.1.1.sp.symm)
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr;rw [x.1.1.s0,y.1.1.s0]) (by taint_decide))
    (st x) (st y) fun u w xu yw => RelCT.mono (preparedAuth_ct (sp:=sp) (bk:=bk) (D:=A) L (.inl rfl) (preparedFlush_ct L))
      (fun a b ⟨ha,hb⟩ => by subst a b;exact ⟨xu,yw⟩) (fun _ _ _ => trivial)

end VG.Proof.AesGcm.RISCV64
