module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.PreparedAbsorb
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.PreparedPad
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTJ0
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.AesGcm.RISCV64

/-! # Two-run timing for arbitrary nonce lengths using the prepared table -/

public section
namespace VG.Proof.AesGcm.RISCV64
open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64 VG.Impl.Gcm.RISCV64.Prepared
open VG.Spec.Gcm (blockAt)
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_seq rel_taint rel_ite)

theorem preparedCT {I : State → Prop} {c : Prog isa}
    (h : ∀ s t, I s → I t → RelCT isa (Eq2 s t) c TT) : CT I c :=
  fun s t x y u v ⟨a,b⟩ e f => h s t a b s t x y u v ⟨rfl,rfl⟩ e f

abbrev nonceScope (V : Reg → BitVec 64) (sp bk : Addr) :=
  HashScope (V .s2+BitVec.ofNat 64 240) bk (j0Frame (V .s1) (V .s0) sp)

theorem HashScope.temp_nonce {V : Reg → BitVec 64} {sp bk : Addr} {s : State} (q : nonceScope V sp bk s) :
    HashScope (V .s2+BitVec.ofNat 64 240) bk (padRange (V .s0)) s :=
  q.narrow fun r hr => ⟨r,by obtain rfl := List.mem_singleton.mp hr;simp [j0Frame],fun _ a => a⟩

private abbrev PinEnv (V : Reg → BitVec 64) (sp bk : Addr) (s : State) :=
  Env V sp s ∧ nonceScope V sp bk s

theorem preparedJ0Hash_ct {V : Reg → BitVec 64} {sp bk Np : Addr} {n : Nat} (lay : Lay (V .s2) (V .s1) (V .s0))
    (hn : n<2^64) (vn : V .s7=BitVec.ofNat 64 n) :
    CT (fun s => (∃ H, J0In V sp H Np n s) ∧ nonceScope V sp bk s) (j0hashWith preparedInvocation) := by
  let F := fun s => (∃ H,AbsIn V sp 0 H [] Np n s) ∧ nonceScope V sp bk s
  refine CT.seq (J:=F) ?_ (fun s ⟨⟨H,h⟩,q⟩ => ?_) ?_
  · refine CT.taint [.s1] (fun s t ⟨⟨_,a⟩,_⟩ ⟨⟨_,b⟩,_⟩ => ⟨a.env.sp.trans b.env.sp.symm,?_⟩) (by taint_decide)
    intro r hr; obtain rfl := List.mem_singleton.mp hr; rw [a.env.s1,b.env.s1]
  · refine WP.mono (WP.with_rdwr (j0zero_ok lay h)) fun t ⟨⟨ab,_,_,fr⟩,rd,wr,stack⟩ =>
      ⟨⟨H,ab⟩,q.after ⟨rd,wr,stack⟩ (fr.sub ?_)⟩
    intro r hr; obtain rfl := List.mem_singleton.mp hr; exact ⟨_,List.mem_cons_self ..,Lay.stSub (by decide)⟩
  refine CT.seq (J:=PinEnv V sp bk) (preparedCT fun _ _ ⟨⟨H,a⟩,q⟩ ⟨⟨H',b⟩,k⟩ =>
    preparedAbsorb_rel lay (.inl rfl) ⟨V,H,[],rfl,rfl,rfl,rfl,a⟩ ⟨V,H',[],rfl,rfl,rfl,rfl,b⟩ q k)
    (fun s ⟨⟨H,a⟩,q⟩ => WP.mono (WP.with_rdwr (absorbFresh_ok_with lay (.inl rfl) a rfl
      (FramedHashAction.now q.action))) fun t ⟨out,rd,wr,stack⟩ =>
        ⟨out.env,q.after ⟨rd,wr,stack⟩ (abs_j0Frame out.frame)⟩) ?_
  refine CT.seq (J:=fun s => PinEnv V sp bk s ∧ s.gpr .s6=BitVec.ofNat 64 (n%16)) ?_ (fun s ⟨e,q⟩ => ?_) ?_
  · refine CT.taint [.s7] (fun s t ⟨e,_⟩ ⟨j,_⟩ => ⟨e.sp.trans j.sp.symm,?_⟩) (by taint_decide)
    intro r hr;obtain rfl := List.mem_singleton.mp hr; rw [e.fr _ (by decide),j.fr _ (by decide)]
  · have k := e.fr .s7 (by decide) |>.trans vn
    have modn := and15 (BitVec.ofNat 64 n)
    rw [toNat64 hn] at modn
    have step : WP isa (.block [.logicImm .and .s6 .s7 15]) s fun t =>
        t.gpr .s6=BitVec.ofNat 64 (n%16) ∧ (∀ r,r ≠ .s6 → t.gpr r=s.gpr r) ∧ Keeps s t := by
      crun [Int.reduceNatCast',k,modn];exact ⟨fun r a => by simp [a],⟨rfl,rfl,rfl,rfl⟩⟩
    exact WP.mono step fun t ⟨k6,rg,keep⟩ => ⟨⟨e.keep (fun r hr => rg r (by revert r;decide)) keep.sp keep.rd keep.wr,q.kept keep⟩,k6⟩
  refine CT.seq (J:=PinEnv V sp bk)
    (preparedCT fun _ _ ⟨⟨e,q⟩,k⟩ ⟨⟨j,b⟩,h⟩ => preparedFlush_rel lay (.inl rfl) (Nat.mod_lt _ (by decide))
      ⟨V,rfl,rfl,rfl,e⟩ ⟨V,rfl,rfl,rfl,j⟩ k h q.temp_nonce b.temp_nonce)
    (fun s ⟨⟨e,q⟩,k⟩ => ?_) ?_
  · refine WP.mono (WP.with_rdwr (flush_ok_with lay (.inl rfl) (x:=List.replicate n 0) ⟨e,rfl⟩
      (by simpa using k) q.temp_nonce.action)) fun t ⟨out,rd,wr,stack⟩ =>
        ⟨out.env,q.after ⟨rd,wr,stack⟩ (t_j0Frame out.frame)⟩
  refine CT.seq (J:=PinEnv V sp bk) ?_ (fun s ⟨e,q⟩ => ?_)
    (preparedCT fun _ _ ⟨e,q⟩ ⟨j,k⟩ => preparedLens_rel (.inl rfl)
      ⟨V,rfl,rfl,rfl,e⟩ ⟨V,rfl,rfl,rfl,j⟩ q.temp_nonce k.temp_nonce)
  · refine CT.taint [.s7] (fun s t ⟨e,_⟩ ⟨j,_⟩ => ⟨e.sp.trans j.sp.symm,?_⟩) (by taint_decide)
    intro r hr;obtain rfl := List.mem_singleton.mp hr; rw [e.fr _ (by decide),j.fr _ (by decide)]
  · have step : WP isa (.block [.li .s4 0,mov .s6 .s7]) s fun t =>
        (∀ r,r ≠ .s4 → r ≠ .s6 → t.gpr r=s.gpr r) ∧ Keeps s t := by
      crun [Int.reduceNatCast',mov]; exact ⟨fun r a b => by simp [a,b],⟨rfl,rfl,rfl,rfl⟩⟩
    exact WP.mono step fun t ⟨rg,keep⟩ => ⟨e.keep (fun r hr => rg r (by revert r;decide) (by revert r;decide))
        keep.sp keep.rd keep.wr,q.kept keep⟩

theorem preparedJ0_ct {V : Reg → BitVec 64} {sp bk Np : Addr} {n : Nat} (lay : Lay (V .s2) (V .s1) (V .s0))
    (hn : n<2^64) (vn : V .s7=BitVec.ofNat 64 n) :
    CT (fun s => (∃ H, J0In V sp H Np n s) ∧ nonceScope V sp bk s) (j0With preparedInvocation) := by
  let J := fun s => ((∃ H,J0In V sp H Np n s) ∧ nonceScope V sp bk s) ∧
    s.gpr .a2=BitVec.ofNat 64 n-BitVec.ofNat 64 12
  refine CT.seq (J:=J) ?_ (fun s ⟨⟨H,h⟩,q⟩ => ?_) ?_
  · refine CT.taint [.s5] (fun s t ⟨⟨_,a⟩,_⟩ ⟨⟨_,b⟩,_⟩ => ⟨a.env.sp.trans b.env.sp.symm,?_⟩) (by taint_decide)
    intro r hr;obtain rfl := List.mem_singleton.mp hr;rw [a.s5,b.s5]
  · have step : WP isa (.block [.addi .a2 .s5 (-12)]) s fun t =>
        t.gpr .a2=BitVec.ofNat 64 n-BitVec.ofNat 64 12 ∧ (∀ r,r ≠ .a2 → t.gpr r=s.gpr r) ∧ Keeps s t := by
      crun [Int.reduceNatCast',h.s5];exact ⟨fun r a => by simp [a],⟨rfl,rfl,rfl,rfl⟩⟩
    refine WP.mono step fun t ⟨diff,reg,k⟩ => ⟨⟨⟨H,?_,?_,?_,?_,h.s7,h.data.of_eq k.rd k.wr k.sp⟩,q.kept k⟩,diff⟩
    · exact h.env.keep (fun r hr => reg r (by revert r;decide)) k.sp k.rd k.wr
    · rw [k.mem];exact h.hH
    · rw [reg .s4 (by decide),h.s4]
    · rw [reg .s5 (by decide),h.s5]
  refine CT.seq (J:=Env V sp) ?_ (fun s ⟨⟨⟨H,h⟩,q⟩,diff⟩ => ?_) ?_
  · refine CT.ite (decide (n=12)) (fun s h => eval_subk h.2 hn (by decide))
      (fun _ => ?_) (fun _ => (preparedJ0Hash_ct lay hn vn).mono fun _ h => h.1)
    refine CT.taint [.s4,.s1] (fun s t ⟨⟨⟨_,a⟩,_⟩,_⟩ ⟨⟨⟨_,b⟩,_⟩,_⟩ => ⟨a.env.sp.trans b.env.sp.symm,?_⟩) (by taint_decide)
    intro r hr;rcases List.mem_cons.mp hr with rfl|hs
    · rw [a.s4,b.s4]
    · obtain rfl := List.mem_singleton.mp hs;rw [a.env.s1,b.env.s1]
  · refine WP.ite (decide (n=12)) (eval_subk diff hn (by decide)) (fun eq => ?_) fun ne => ?_
    · have hn12 : n=12 := by simpa using eq
      subst n;exact WP.mono (j012_ok lay h) fun _ mid => mid.env
    · exact WP.mono (j0hash_ok_with lay h (by simpa using ne) q.action) fun _ mid => mid.env
  · refine CT.taint [.s1] (fun s t e j => ⟨e.sp.trans j.sp.symm,?_⟩) (by taint_decide)
    intro r hr;obtain rfl := List.mem_singleton.mp hr;rw [e.s1,j.s1]

end VG.Proof.AesGcm.RISCV64
