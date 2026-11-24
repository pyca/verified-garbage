module
public import VerifiedGarbage.Proof.AesGcm.X86_64.ContiguousScalar
public import VerifiedGarbage.Proof.AesGcm.X86_64.ContiguousBounded
import VerifiedGarbage.Proof.AesGcm.X86_64.Seal
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Facts
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Gcm.Stream
/-! One contiguous record from AAD through ciphertext and authentication. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.ContiguousSeal
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph inc32 zeros padLen)
open VG.Spec.Aes (bytesAt)
open Split (SealRegions)
open Short (SpanLayout SealPostFrom)

def BulkOk (M : CtxMode) (program : Prog isa) (hash : Bool := true) : Prop :=
  ∀ {Ctx W SP S D : Addr} {R n : Nat} {s : State},
    SealRegions M Ctx W SP D S R n n s → ObPre M Ctx W SP R D n s →
    s.mem.readW (SP+8#64) 64=S → InRegions (s.rd++s.wr) (SP+8#64) 8 →
    (⟨SP+8#64,8⟩ : Region).Disjoint ⟨W,2560⟩ →
    WP isa program s fun t => ObPost Ctx W SP D n s t ∧ BlocksResult Ctx W R S D (n/16) s t hash

def FinishOk (M : CtxMode) (program : Prog isa) (hash : Bool := true) : Prop :=
  ∀ {Ctx W SP S D : Addr} {R n al : Nat} {s u : State} {H icb : Block} {a : List Byte},
    SealRegions M Ctx W SP D S R n n s → ObPre M Ctx W SP R D n s →
    ObPost Ctx W SP D n s u → BlocksResult Ctx W R S D (n/16) s u hash →
    blockAt s.mem (Ctx+240#64)=H → blockAt s.mem (cbA W)=icb →
    s.mem.readW (W+184#64) 64=BitVec.ofNat 64 al →
    Proof.Gcm.Absorbed s.mem (yA W) (W+16#64+32#64) H (a++zeros (padLen a.length)) →
    InRegions (s.rd++s.wr) (SP+8#64) 8 → u.mem.readW (SP+8#64) 64=S →
    (⟨SP+8#64,8⟩ : Region).Disjoint ⟨W,2560⟩ →
    InRegions (s.rd++s.wr) (SP+16#64) 8 → u.mem.readW (SP+16#64) 64=D →
    (⟨SP+16#64,8⟩ : Region).Disjoint ⟨D,n⟩ → (⟨SP+16#64,8⟩ : Region).Disjoint ⟨W,2560⟩ →
    WP isa program u (BodyPost Ctx W SP S D R n al H icb a s)

theorem body_ok {M : CtxMode} {aad bulk fin : Prog isa} {hash : Bool} (hb : BulkOk M bulk hash) (hf : FinishOk M fin hash)
    {s₀ s₁ : State} {Ctx W SP Np A S D : Addr} {nl al n : Nat}
    (C : OneCtx s₀ 5 Ctx W SP Np A D nl al n) (X : CtxExt M Ctx (W+16#64) W SP D n s₀)
    (geo : SpanLayout s₀ S S D W SP n n) (nowrap : S.toNat+n≤2^64)
    (ha : (s₀.gpr .r9).toNat=al) (src : s₀.mem.readW (SP+8#64) 64=S)
    (dst : s₀.mem.readW (SP+16#64) 64=D)
    (aad_ok : WP isa aad s₁ (OneMid s₀ Ctx W SP D n (ctxH s₀.mem Ctx)
      (bytesAt s₀.mem Np nl) (bytesAt s₀.mem A al) s₁.mem)) :
    WP isa (.seq aad (.seq bulk fin)) s₁ (SealPostFrom s₀ Ctx W SP D n (s₀.gpr .rsi).toNat al (ctxH s₀.mem Ctx)
      (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl)) (bytesAt s₀.mem A al) (bytesAt s₀.mem S n)) := by
  refine WP.seq (aad_ok.mono fun s₂ m => ?_)
  have dM {p : Addr} {k : Nat} (w : (⟨p,k⟩ : Region).Disjoint ⟨W,2560⟩) (sp : (⟨p,k⟩ : Region).Disjoint (below SP 8)) :
      ∀ b ∈ [(⟨W,2560⟩ : Region),below SP 8], (⟨p,k⟩ : Region).Disjoint b := by
    intro b hb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl|rfl <;> assumption
  have b8 := below_sub (sp:=SP) (a:=8) (b:=24) (by decide) (by decide)
  have ext := X.keep m.rd m.wr m.frame (dM X.cw (X.ct.sub_left b8).symm)
  have hd := C.data.of_eq m.rd m.wr
  have ob : ObPre M Ctx W SP (s₀.gpr .rsi).toNat D n s₂ :=
    ⟨m.env,m.rounds,m.dat,m.len,hd,C.t_c,C.t_w,C.t_d,C.sp24,ext⟩
  have reg : SealRegions M Ctx W SP D S (s₀.gpr .rsi).toNat n n s₂ :=
    ⟨m.env,C.lay,m.rounds,hd,by rw [m.rd,m.wr]; exact geo.leftRead,geo.leftWork,geo.leftAlias,
     nowrap,Nat.le_refl _,C.t_w,C.t_d,geo.leftStack.symm,X.ct,C.sp24,ext⟩
  have read : InRegions (s₂.rd++s₂.wr) (SP+8#64) 8 := by rw [m.rd,m.wr]; exact C.args 0 (by decide)
  have readD : InRegions (s₂.rd++s₂.wr) (SP+16#64) 8 := by rw [m.rd,m.wr]; exact C.args 1 (by decide)
  have sd : Region.Sub ⟨SP+16#64,8⟩ ⟨SP+8#64,8*5⟩ := by
    rw [show (16#64 : Addr)=BitVec.ofNat 64 (8+8) from rfl,← add_ofNat_assoc]; exact Offset.sub_base _ (by decide)
  have dw := C.dA.sub_left (Region.sub_prefix (show 8≤8*5 by decide))
  have dq := C.dAD.sub_left (Region.sub_prefix (show 8≤8*5 by decide))
  have ds := Offset.disjoint_below SP (n:=24) (d:=8) (k:=8) (by decide)
  have orig : s₂.mem.readW (SP+8#64) 64=S := by
    rw [m.frame.readW (Region.contains_self _ _) (dM dw (ds.sub_right b8)) (by decide),src]
  have dest : s₂.mem.readW (SP+16#64) 64=D := by
    rw [m.frame.readW (Region.contains_self _ _) (dM (C.dA.sub_left sd) ((Offset.disjoint_below SP (n:=24) (d:=16) (k:=8) (by decide)).sub_right b8)) (by decide),dst]
  have alen : s₂.mem.readW (W+184#64) 64=BitVec.ofNat 64 al := by rw [m.alen,← ha,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  refine WP.seq ((hb reg ob orig read dw).mono fun s₃ ⟨post,blocks⟩ => ?_)
  have orig' : s₃.mem.readW (SP+8#64) 64=S := by
    rw [post.frame.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
      · exact dw.sub_right (Lay.wSub (by decide))
      · rw [add_ofNat_assoc]; exact dw.sub_right (Lay.wSub (by decide))
      · rw [add_ofNat_assoc]; exact dw.sub_right (Lay.wSub (by decide))
      · exact dq.sub_right (Region.sub_prefix (by omega_arith))
      · exact dw.sub_right (Lay.wSub (by decide))
      · exact ds) (by decide),orig]
  have dest' : s₃.mem.readW (SP+16#64) 64=D := by
    rw [post.frame.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
      · exact (C.dA.sub_left sd).sub_right (Lay.wSub (by decide))
      · rw [add_ofNat_assoc]; exact (C.dA.sub_left sd).sub_right (Lay.wSub (by decide))
      · rw [add_ofNat_assoc]; exact (C.dA.sub_left sd).sub_right (Lay.wSub (by decide))
      · exact (C.dAD.sub_left sd).sub_right (Region.sub_prefix (by omega_arith))
      · exact (C.dA.sub_left sd).sub_right (Lay.wSub (by decide))
      · exact Offset.disjoint_below SP (by decide)) (by decide),dest]
  refine (hf reg ob post blocks m.hH m.cb alen m.abs read orig' dw readD dest' (C.dAD.sub_left sd) (C.dA.sub_left sd)).mono fun s₄ ⟨env,rd,wr,fr,ct,tag⟩ => ?_
  have kc : ciphOf s₂.mem Ctx (s₀.gpr .rsi).toNat = ctxCiph s₀.mem Ctx (s₀.gpr .rsi).toNat :=
    ciph_frame m.frame (dM C.lay.cw' C.lay.kc.symm) C.rounds
  have pt := bytesAt_frame m.frame (dM geo.leftWork (geo.leftStack.sub_right b8)) (by have := C.data.ok.lt; omega_arith)
  rw [kc,m.j0] at tag
  refine ⟨env,rd.trans m.rd,wr.trans m.wr,m.saved.frame fr (saved_oneFrameB C.lay C.dE C.t_w),?_,
    by rw [ct,kc,pt,Proof.Gcm.gctr_eq],tag⟩
  refine (m.frame.sub fun r hr => ?_).trans (fr.sub fun r hr => ?_)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact ⟨_,List.mem_cons_self ..,fun _ h => h⟩
    · exact ⟨below SP 24,by simp,b8⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl
    · exact ⟨_,List.mem_cons_self ..,Region.sub_prefix (by decide)⟩
    · exact ⟨_,List.mem_cons_self ..,Lay.wSub (by decide)⟩
    · exact ⟨_,List.mem_cons_self ..,Lay.wSub (by decide)⟩
    · exact ⟨⟨D,n⟩,by simp,fun _ h => h⟩
    · exact ⟨below SP 24,by simp,fun _ h => h⟩

end VG.Proof.AesGcm.X86_64.ContiguousSeal
