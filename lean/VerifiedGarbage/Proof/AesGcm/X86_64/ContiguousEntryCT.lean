module
public import VerifiedGarbage.Proof.AesGcm.X86_64.ContiguousEntry
public import VerifiedGarbage.Proof.AesGcm.X86_64.ContiguousRunCT
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
public import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT
import VerifiedGarbage.Proof.AesGcm.X86_64.OneShot
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Impl.AesGcm.X86_64
/-! Leakage across the ten-argument ABI and its caller-provided scratch. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.ContiguousSeal
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open Short (rel_next)

def EntryPublic (s t : State) : Prop :=
  (∀ r ∈ [Reg.rdi,.rsi,.rdx,.rcx,.r8,.r9,.rsp], s.gpr r=t.gpr r) ∧ ∀ i, i<5 → stackArg s i=stackArg t i

theorem entry_start {M : CtxMode} {s : State} (p : EntryPre M s) :
    WP isa (.block (oneEntry 40 16 24)) s (OneEntry s (K s) (W s) (SP s) (s.gpr .r8) (D s) (N s)) :=
  (oneEntryAt_okL (id:=1) (il:=2) (wo:=40) (by decide) (by decide) p.ctx rfl rfl rfl rfl rfl rfl (p.ctx.args 4 (by decide))).mono
    fun _ ⟨h,_⟩ => h

theorem entry_tag {M : CtxMode} {body : Prog isa} (hw : RecordOk M body) {s u : State} (p : EntryPre M s)
    (E : OneEntry s (K s) (W s) (SP s) (s.gpr .r8) (D s) (N s) u) :
    WP isa body u (TagAt (K s) (W s+16#64) (W s) (SP s) .rsp 32 (T s)) := by
  refine (hw p.ctx p.ext p.geo p.nowrap rfl rfl E rfl rfl rfl).mono fun v ⟨env,rd,wr,_,frame,_⟩ => ?_
  have sub : Region.Sub ⟨SP s+32#64,8⟩ ⟨SP s+8#64,8*5⟩ := by
    rw [show 32#64 = (BitVec.ofNat 64 (8+24)) from rfl,← add_ofNat_assoc]; exact Offset.sub_base _ (by decide)
  refine ⟨env,?_,by rw [env.rsp,rd,wr]; exact p.ctx.args 3 (by decide)⟩
  rw [env.rsp,frame.readW (Region.contains_self _ _) (fun b hb => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl|rfl|rfl
    · exact p.ctx.dA.sub_left sub
    · exact p.ctx.dAD.sub_left sub
    · exact Offset.disjoint_below _ (n:=24) (d:=32) (k:=8) (by decide)) (by decide)]; rfl

theorem entry_ct {M : CtxMode} {body : Prog isa} (hw : RecordOk M body) (hc : RecordCT M body)
    {a b : State} (p : EntryPre M a) (q : EntryPre M b) (eq : EntryPublic a b) :
    RelCT isa (fun x y => x=a ∧ y=b)
      (.seq (.block (oneEntry 40 16 24)) (.seq body (.seq (.block (tagOut (at_ .rsp 32))) (.block restore)))) (fun _ _ => True) := by
  have k : K b=K a := (eq.1 _ (by decide)).symm
  have sp : SP b=SP a := (eq.1 _ (by decide)).symm
  have w : W b=W a := (eq.2 4 (by decide)).symm
  have src : S b=S a := (eq.2 0 (by decide)).symm
  have dst : D b=D a := (eq.2 1 (by decide)).symm
  have n : N b=N a := congrArg BitVec.toNat (eq.2 2 (by decide)).symm
  have tag : T b=T a := (eq.2 3 (by decide)).symm
  have ar : b.gpr .r8=a.gpr .r8 := (eq.1 _ (by decide)).symm
  have no : b.gpr .rdx=a.gpr .rdx := (eq.1 _ (by decide)).symm
  have nl : (b.gpr .rcx).toNat=(a.gpr .rcx).toNat := congrArg BitVec.toNat (eq.1 _ (by decide)).symm
  have al : (b.gpr .r9).toNat=(a.gpr .r9).toNat := congrArg BitVec.toNat (eq.1 _ (by decide)).symm
  have r : (b.gpr .rsi).toNat=(a.gpr .rsi).toNat := congrArg BitVec.toNat (eq.1 _ (by decide)).symm
  have recordInput {u : State} (g : EntryPre M u) : RecordInput M u (K u) (W u) (SP u) (u.gpr .rdx) (u.gpr .r8) (S u) (D u)
      (u.gpr .rcx).toNat (u.gpr .r9).toNat (N u) (u.gpr .rsi).toNat :=
    ⟨g.ctx,g.ext,g.geo,g.nowrap,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have qb := recordInput q
  rw [k,w,sp,no,ar,src,dst,nl,al,n,r] at qb
  have ea := entry_start p
  have eb := entry_start q
  rw [k,w,sp,ar,dst,n] at eb
  have wtb (s) (e : OneEntry b (K a) (W a) (SP a) (a.gpr .r8) (D a) (N a) s) :
      WP isa body s (TagAt (K a) (W a+16#64) (W a) (SP a) .rsp 32 (T a)) := by
    rw [← k,← w,← sp,← ar,← dst,← n] at e
    simpa only [k,w,sp,tag] using entry_tag hw q e
  have mid := rel_next (hc (recordInput p) qb) (fun _ e => entry_tag hw p e) wtb
  rw [oneEntry,List.append_assoc,List.append_assoc,List.append_assoc] at ea eb ⊢
  refine rel_reassoc_mid (fn_rel₂ (Ctx:=K a) (St:=W a+16#64) (W:=W a) (SP:=SP a) (k:=40)
    [.rdi,.rsi,.rdx,.rcx,.r8,.r9,.rsp] (by simp) ⟨_,by taint_decide⟩ eq.1 w.symm
    (p.ctx.args 4 (by decide)) (q.ctx.args 4 (by decide)) ⟨_,by taint_decide⟩ ea eb ?_)
  exact RelCT.seq (mid.mono (fun _ _ h => h.2) (fun _ _ h => h)) (tagOut_rel (b:=.rsp) (d:=32) (by simp) ⟨_,by taint_decide⟩ (fun _ _ h => h))

end VG.Proof.AesGcm.X86_64.ContiguousSeal
