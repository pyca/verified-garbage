module
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.BoundedCall
meta import VerifiedGarbage.Impl.AesGcm.X86_64.Short
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Crypt
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith

/-! The bounded helper needs only the key, IV, AAD, source spans, output and private workspace. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.Short
open VG VG.X86_64 VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)

def sourceRegions (P Q : Addr) (m n : Nat) : List Region :=
  ⟨P,m⟩ :: (if m < n then [⟨Q,n-m⟩] else [])

def spanState (s : State) (M : CtxMode) (K N A P Q D W : Addr) (nl al m n : Nat) : State :=
  s.withRegions ([⟨K,M.len⟩, ⟨N,nl⟩, ⟨A,al⟩] ++ sourceRegions P Q m n) [⟨D,n⟩,⟨W,2560⟩]

section
variable {M : CtxMode} {o s : State} {Ctx W SP Np A P Q D : Addr} {nl al n m k : Nat}
local notation "cut" x => spanState x M Ctx Np A P Q D W nl al m n

private theorem cut_perm (o : State) (hge : 256 ≤ M.len) : Perm Ctx (W+16#64) W (cut o) := by
  have w : Covers [⟨W,2560⟩] (cut o).wr := covers_of_mem (by simp [spanState,State.withRegions])
  refine ⟨?_,?_,w⟩
  · apply covers_prefix (k:=M.len) (covers_of_mem ?_) hge
    simp [spanState,State.withRegions]
  · exact covers_off w (d:=16) (by decide) (by decide)

theorem cut_ctx (C : OneCtx o k Ctx W SP Np A D nl al n) (hge : 256 ≤ M.len) :
    OneCtx (cut o) 0 Ctx W SP Np A D nl al n := by
  let o' := cut o
  have nc : Covers [⟨Np,nl⟩] (o'.rd++o'.wr) := covers_of_mem (by simp [o',spanState,State.withRegions])
  have ac : Covers [⟨A,al⟩] (o'.rd++o'.wr) := covers_of_mem (by simp [o',spanState,State.withRegions])
  have dc : Covers [⟨D,n⟩] o'.wr := covers_of_mem (by simp [o',spanState,State.withRegions])
  exact ⟨C.lay,cut_perm o hge,C.ww,fun _ h => by omega,
    C.dA.sub_left (Region.sub_prefix (by simp)),{ C.nonce with rd := nc },{ C.aad with rd := ac },
    ⟨{ C.data.ok with rd := covers_left dc },dc,C.data.ctx⟩,C.rD,C.rW,C.dE,C.dAD.sub_left (Region.sub_prefix (by simp)),
    C.rounds,C.t_c,C.t_w,C.t_d,C.sp24⟩

theorem cut_ext (X : CtxExt M Ctx (W+16#64) W SP D n o) : CtxExt M Ctx (W+16#64) W SP D n (cut o) :=
  { X with cov := covers_of_mem (by simp [spanState,State.withRegions]) }

theorem cut_entry (hge : 256 ≤ M.len) (E : OneEntry o Ctx W SP A D n s) :
    OneEntry (cut o) Ctx W SP A D n (cut s) :=
  { E with env := { E.env with perm := cut_perm s hge }, rd := rfl, wr := rfl }

theorem cut_geo (g : SpanLayout o P Q D W SP m n) : SpanLayout (cut o) P Q D W SP m n :=
  { g with leftRead := covers_of_mem (by simp [spanState,sourceRegions,State.withRegions]),
           rightRead := fun lt => covers_of_mem (by simp [spanState,sourceRegions,State.withRegions,lt]) }

theorem cut_writable (C : OneCtx o k Ctx W SP Np A D nl al n) (E : OneEntry o Ctx W SP A D n s) :
    Covers (cut s).wr s.wr := by
  rw [E.wr]
  exact Covers.pair C.data.wr C.perm.w

theorem cut_readable (C : OneCtx o k Ctx W SP Np A D nl al n)
    (X : CtxExt M Ctx (W+16#64) W SP D n o) (E : OneEntry o Ctx W SP A D n s)
    (g : SpanLayout o P Q D W SP m n) : Covers ((cut s).rd ++ (cut s).wr) (s.rd ++ s.wr) := by
  have rest := cut_writable (M:=M) (P:=P) (Q:=Q) (m:=m) C E
  rw [E.wr] at rest
  rw [E.rd,E.wr]
  apply covers_append _ (covers_left rest)
  refine Covers.cons X.cov (Covers.cons C.nonce.rd (Covers.cons C.aad.rd (Covers.cons g.leftRead ?_)))
  by_cases lt : m < n
  · simpa only [lt,ite_true] using g.rightRead lt
  · simpa only [lt,ite_false] using (covers_nil (ts:=o.rd++o.wr))

theorem cut_clear (C : OneCtx o k Ctx W SP Np A D nl al n) (X : CtxExt M Ctx (W+16#64) W SP D n o)
    (g : SpanLayout o P Q D W SP m n) (s : State) : Clear (hole SP) (cut s) := by
  let H : (hole SP).Sub (below SP 24) := below_sub (by decide : 8 ≤ 24) (by decide)
  intro r hr
  change r ∈ ([⟨Ctx,M.len⟩, ⟨Np,nl⟩, ⟨A,al⟩] ++ sourceRegions P Q m n) ++ [⟨D,n⟩,⟨W,2560⟩] at hr
  simp only [sourceRegions,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with ((rfl|rfl|rfl)|(rfl|hq))|(rfl|rfl)
  · exact X.ct.symm.sub_right H
  · exact C.nonce.stk.symm
  · exact C.aad.stk.symm
  · exact g.leftStack.sub_right H
  · split at hq
    next lt => rw [List.mem_singleton.mp hq]; exact (g.rightStack lt).sub_right H
    next => cases hq
  · exact C.t_d.symm.sub_right H
  · exact C.t_w.symm.sub_right H

/-- An execution of the outlined call and the corresponding trace of the inline body. -/
structure CallRun (s : State) (Q : State → Prop) : Prop where
  witness : ∃ tc a ti b, Exec isa (.call bounded.name bounded.code) s tc a ∧ Q a ∧
    Exec isa bounded.code s ti b ∧ Lifts (s.gpr .rsp - 8) (.call bounded.name bounded.code) tc ti

theorem run_cut (hF : ShortFacts) (C : OneCtx o k Ctx W SP Np A D nl al n)
    (X : CtxExt M Ctx (W+16#64) W SP D n o) (pow : PowOk M powersP ghashP)
    (E : OneEntry o Ctx W SP A D n s) (geo : SpanLayout o P Q D W SP m n)
    (hp : o.gpr .rdx = Np) (hl : (o.gpr .rcx).toNat = nl) (ha : (o.gpr .r9).toNat = al)
    (hs : IsShort nl al n) (args : SpanEntryArgs P Q m s) :
    CallRun s (SealPostFrom o Ctx W SP D n (o.gpr .rsi).toNat al (Spec.Gcm.ctxH o.mem Ctx)
      (Spec.Gcm.j0 (Spec.Gcm.ctxH o.mem Ctx) (bytesAt o.mem Np nl)) (bytesAt o.mem A al) (spanBytes o P Q m n)) := by
  have c' := cut_ctx (M:=M) (m:=m) (P:=P) (Q:=Q) C M.ge
  have e' := cut_entry (M:=M) (Np:=Np) (nl:=nl) (al:=al) (m:=m) (P:=P) (Q:=Q) M.ge E
  have run := bounded_ok hF c' (pow (cut_ext (P:=P) (Q:=Q) (m:=m) (Np:=Np) (A:=A) (nl:=nl) (al:=al) X)).choose_spec
    e' (cut_geo (M:=M) (Ctx:=Ctx) (Np:=Np) (nl:=nl) (A:=A) (al:=al) geo) hp hl ha hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 args.1 args.2.1 args.2.2
  have clear := cut_clear C X geo s
  obtain ⟨ti,b,ex,post⟩ := run
  have ck : (Code.call bounded.name bounded.code).InlineOk = true := by decide +kernel
  have ce : Clear (hole ((cut s).gpr .rsp)) (cut s) := E.rsp.symm ▸ clear
  obtain ⟨hv,unknown,tc,ec,_,lift⟩ := Exec.of_inline ck ex ce
  obtain ⟨w,ret,other,post'⟩ := bounded_call_ok (s := cut s) c' E.rsp clear (show WP isa bounded.code (cut s) _ from ⟨ti,b,ex,post⟩)
  obtain ⟨rfl,rfl⟩ := Exec.det ec other
  obtain ⟨env,_,_,saved,fr,ct,tag⟩ := post'
  have reads := cut_readable C X E geo
  have writes := cut_writable (M:=M) (m:=m) (P:=P) (Q:=Q) C E
  have cRun := Exec.widen ec reads writes
  have iRun := Exec.widen ex reads writes
  simp only [spanState,State.withRegions_withRegions] at cRun iRun
  rw [show s.withRegions s.rd s.wr = s from rfl] at cRun iRun
  refine ⟨_,_,_,_,cRun,?_,iRun,lift⟩
  refine ⟨?_,E.rd,E.wr,saved,fr,ct,tag⟩
  exact { env with perm := (C.perm.of_eq E.rd E.wr) }

theorem CallRun.wp {V : State → Prop} (h : CallRun s V) :
    WP isa (.call bounded.name bounded.code) s V := by
  obtain ⟨_,_,_,_,ec,post,_,_⟩ := h.witness
  exact ⟨_,_,ec,post⟩

theorem CallRun.rel {F : State → State → Prop} (runs : ∀ a b, F a b → CallRun a (fun _ => True) ∧ CallRun b (fun _ => True))
    (rsp : ∀ a b, F a b → a.gpr .rsp = b.gpr .rsp)
    (ct : RelCT isa F bounded.code (fun _ _ => True)) : RelCT isa F (.call bounded.name bounded.code) (fun _ _ => True) := by
  intro a b ta tb a' b' h aRun bRun
  obtain ⟨ra,rb⟩ := runs a b h
  obtain ⟨_,_,ia,_,ea,_,xa,la⟩ := ra.witness
  obtain ⟨_,_,ib,_,eb,_,xb,lb⟩ := rb.witness
  obtain ⟨rfl,_⟩ := Exec.det aRun ea
  obtain ⟨rfl,_⟩ := Exec.det bRun eb
  have eq := (ct _ _ _ _ _ _ h xa xb).1
  rw [eq,rsp _ _ h] at la
  exact ⟨la.unique lb,trivial⟩

theorem CallRun.mono {F G : State → Prop} (h : CallRun s F) (imp : ∀ u, F u → G u) : CallRun s G := by
  obtain ⟨_,_,_,_,ec,post,ei,leak⟩ := h.witness
  exact ⟨_,_,_,_,ec,imp _ post,ei,leak⟩

end
end VG.Proof.AesGcm.X86_64.Short
