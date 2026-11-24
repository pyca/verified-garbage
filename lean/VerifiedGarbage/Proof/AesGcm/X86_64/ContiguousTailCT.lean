module
public import VerifiedGarbage.Proof.AesGcm.X86_64.ContiguousTail
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.SealFin
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.TailCT
public import VerifiedGarbage.Proof.AesGcm.X86_64.ContiguousScalar
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.CryptOk
import VerifiedGarbage.Proof.AesGcm.X86_64.Split.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.Crypt
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Impl.AesGcm.X86_64.Contiguous
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! Leakage for the final partial block with a public source and destination. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.ContiguousSeal
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Short (FinI rel_env_regs rel_next rel_piece keepsEnv)

structure TailI (Ctx W SP S D : Addr) (R n r : Nat) (s : State) extends FinI Ctx W SP D R r s where
  slot : InRegions (s.rd++s.wr) (SP+8#64) 8
  src : s.mem.readW (SP+8#64) 64=S
  total : s.mem.readW (W+192#64) 64=BitVec.ofNat 64 n
  apart : (⟨SP+8#64,8⟩ : Region).Disjoint ⟨W,2560⟩

theorem TailI.keep {Ctx W SP S D : Addr} {R n r : Nat} {s t : State}
    (h : TailI Ctx W SP S D R n r s)
    (g : ∀ k ∈ [Reg.r13,.r14,.r15,.rsp], t.gpr k=s.gpr k)
    (rd : t.rd=s.rd) (wr : t.wr=s.wr) (f : Frame [⟨W+1024#64,64⟩] s.mem t.mem) :
    TailI Ctx W SP S D R n r t := by
  refine ⟨h.toFinI.keep g rd wr f,by rw [rd,wr]; exact h.slot,?_,?_,h.apart⟩
  · rw [f.readW (r:=⟨SP+8#64,8⟩) (Region.contains_self _ _) (fun q hq => by
      obtain rfl := List.mem_singleton.mp hq; exact h.apart.sub_right (Lay.wSub (by decide))) (by decide),h.src]
  · rw [f.readW (r:=⟨W+192#64,8⟩) (Region.contains_self _ _) (fun q hq => by
      obtain rfl := List.mem_singleton.mp hq; exact Offset.disjoint W (.inl (by decide : 192+8≤1024)) (by decide) (by decide)) (by decide),h.total]

theorem finRestFrom_rel {ks : Prog isa} (hks : Short.KsOk ks) (hkr : Short.KsRel ks) {Ctx W SP S D : Addr}
    {R n r : Nat} (le : r≤n) (hR : R = 10 ∨ R = 12 ∨ R = 14) (hr : r < 2 ^ 64) :
    RelCT isa (fun s₁ s₂ => TailI Ctx W SP S D R n r s₁ ∧ TailI Ctx W SP S D R n r s₂)
      (.seq ks (.seq (.block [.mov .rax (.mem (at_ .r15 lenO)), .alu .test .rax (.reg .rax)])
        (.ite .e (.block (VG.Impl.AesGcm.X86_64.Short.finLens ++ VG.Impl.AesGcm.X86_64.Short.finGh1 ++ VG.Impl.AesGcm.X86_64.Short.tagK 0))
          (.seq (.block (VG.Impl.AesGcm.X86_64.Short.finTextArgs ++ Contiguous.regs .rbx)) (.seq (VG.Impl.AesGcm.X86_64.Short.xorText true .rbx) (.block (VG.Impl.AesGcm.X86_64.Short.finLens ++ VG.Impl.AesGcm.X86_64.Short.finGh2 ++ VG.Impl.AesGcm.X86_64.Short.tagK 0)))))))
      fun _ _ => True := by
  have wKs : ∀ s, TailI Ctx W SP S D R n r s → WP isa ks s (TailI Ctx W SP S D R n r) := fun s h =>
    WP.mono (hks s h.env h.rounds hR) fun _ ⟨_, _, f, g, rd, wr, _⟩ => h.keep (fun g' hg => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl <;> exact g _ (by decide) (by decide) (by decide)) rd wr f
  have wTest : ∀ s, TailI Ctx W SP S D R n r s → WP isa (.block [.mov .rax (.mem (at_ .r15 lenO)),
      .alu .test .rax (.reg .rax)]) s fun t => t.zf = some (decide (r = 0)) ∧ TailI Ctx W SP S D R n r t := fun s h =>
    WP.mono (Short.finTest_ok hr s h.env h.len) fun _ ⟨z, g, m, rd, wr, _⟩ => ⟨z, h.keep (fun g' hg => g _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl <;> decide)) rd wr (by rw [m]; exact Frame.refl _ _)⟩
  have wArgs : ∀ s, TailI Ctx W SP S D R n r s → WP isa (.block (VG.Impl.AesGcm.X86_64.Short.finTextArgs ++ Contiguous.regs .rbx)) s fun t =>
      t.gpr .rdi = W + BitVec.ofNat 64 512 ∧ t.gpr .rsi = D ∧ t.gpr .rdx = W + BitVec.ofNat 64 1040 ∧
        t.gpr .rcx = BitVec.ofNat 64 r ∧ t.gpr .rbx=S+BitVec.ofNat 64 (n-r) := fun s h => by
    obtain ⟨t,run,_,di,si,dx,cx,bx,_⟩ := vecArgs_ok h.env h.dat h.total h.len le h.slot h.src h.apart
    exact WP.of_runBlock ⟨t,run,di,si,dx,cx,bx⟩
  have k := rel_next ((hkr hR).mono (fun _ _ h => ⟨h.1.toFinI,h.2.toFinI⟩) (fun _ _ h => h)) wKs wKs
  have t := rel_next (rel_env_regs [] (fun _ h => h.env) (fun _ h => h.env) (fun _ _ _ _ _ hr => by cases hr)
    (c := .block [.mov .rax (.mem (at_ .r15 lenO)), .alu .test .rax (.reg .rax)]) ⟨_, by taint_decide⟩) wTest wTest
  have b₀ := rel_env_regs [] (F₁ := TailI Ctx W SP S D R n r) (F₂ := TailI Ctx W SP S D R n r) (fun _ h => h.env) (fun _ h => h.env)
    (fun _ _ _ _ _ hr => by cases hr) (c := .block (VG.Impl.AesGcm.X86_64.Short.finLens ++ VG.Impl.AesGcm.X86_64.Short.finGh1 ++ VG.Impl.AesGcm.X86_64.Short.tagK 0)) ⟨_, by taint_decide⟩
  have b₁ := rel_piece [.rdi, .rsi, .rdx, .rcx, .rbx] (F₁ := TailI Ctx W SP S D R n r) (F₂ := TailI Ctx W SP S D R n r)
    (fun _ h => h.env) (fun _ h => h.env) (keepsEnv (by decide +kernel)) ⟨_, by taint_decide⟩ wArgs wArgs
    (fun _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.2.2.2.1, h₂.2.2.2.1]
      · rw [h₁.2.2.2.2, h₂.2.2.2.2])
    (c := .seq (VG.Impl.AesGcm.X86_64.Short.xorText true .rbx) (.block (VG.Impl.AesGcm.X86_64.Short.finLens ++ VG.Impl.AesGcm.X86_64.Short.finGh2 ++ VG.Impl.AesGcm.X86_64.Short.tagK 0))) ⟨_, by taint_decide⟩
  refine RelCT.seq k (RelCT.seq t (rel_ite_e (fun _ _ h => by rw [h.1.1, h.2.1])
    (b₀.mono (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h)
    (b₁.mono (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h)))


theorem finishVec_ct (prepared wide : Bool) {Ctx W SP S D : Addr} {R n r : Nat} (le : r≤n)
    (hR : R=10 ∨ R=12 ∨ R=14) (hr : r<2^64) {F : State → Prop}
    (start : ∀ s, F s → TailI Ctx W SP S D R n r s)
    (power : ∀ s, F s → WP isa (.block (if prepared then VG.Impl.AesGcm.X86_64.Short.finPowP else
      VG.Impl.AesGcm.X86_64.Short.finPow)) s fun t => Env Ctx (W+16#64) W SP t ∧ t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr) :
    RelCT isa (fun x y => F x ∧ F y) (Contiguous.finishVec prepared wide) (fun _ _ => True) := by
  let k := if wide then VG.Impl.AesGcm.X86_64.Short.finKs else VG.Impl.AesGcm.X86_64.Short.finKsA
  have wk : Short.KsOk k := by cases wide <;> first | exact Short.finKsA_ksOk | exact Short.finKs_ksOk
  have rk : Short.KsRel k := by cases wide <;> first | exact Short.finKsA_rel | exact Short.finKs_rel
  have w (s) (hs : F s) := (power s hs).mono fun t ⟨env,m,rd,wr⟩ =>
    let h := start s hs
    show TailI Ctx W SP S D R n r t from ⟨⟨env,m ▸ h.rounds,m ▸ h.dat,m ▸ h.len⟩,by rw [rd,wr]; exact h.slot,
      m ▸ h.src,m ▸ h.total,h.apart⟩
  apply RelCT.seq (rel_next (rel_env_regs [] (fun s hs => (start s hs).env) (fun s hs => (start s hs).env)
    (fun _ _ _ _ _ h => by cases h) (by cases prepared <;> exact ⟨_,by taint_decide⟩)) w w)
  exact finRestFrom_rel wk rk le hR hr

structure ScalarI (Ctx W SP S D : Addr) (R al n r : Nat) (s : State) : Prop where
  tag : OneT Ctx W SP R al D r n s
  slot : InRegions (s.rd++s.wr) (SP+8#64) 8
  src : s.mem.readW (SP+8#64) 64=S
  input : DataOk (W+16#64) W SP s (S+BitVec.ofNat 64 (n-r)) r
  output : DataW Ctx (W+16#64) W SP s D r
  alias : S+BitVec.ofNat 64 (n-r)=D ∨ (⟨S+BitVec.ofNat 64 (n-r),r⟩ : Region).Disjoint ⟨D,r⟩

theorem finishScalar_ct (v : GcmImpl) {Ctx W SP S D : Addr} (L : Lay Ctx (W+16#64) W SP)
    {R al n r : Nat} (le : r≤n) (short : r<16) (dw : (⟨D,r⟩ : Region).Disjoint ⟨W,2560⟩) :
    RelCT isa (fun x y => ScalarI Ctx W SP S D R al n r x ∧ ScalarI Ctx W SP S D R al n r y)
      (Contiguous.finishScalar v.callees) (fun _ _ => True) := by
  let Q := S+BitVec.ofNat 64 (n-r)
  let T := OneT Ctx W SP R al D r n
  let F (s : State) := T s ∧ CrMid Ctx (W+16#64) W SP R 0 0 D r s.mem 0 s ∧
    TailSrc true (W+16#64) W SP s s.mem D 0 r Q ∧ s.gpr .rbx=Q
  have setup (s) (h : ScalarI Ctx W SP S D R al n r s) :
      WP isa (.block (Contiguous.regs .rbx ++ [.mov .r12 (.mem (at_ .r15 dataO)),.mov .rbp (.mem (at_ .r15 lenO))])) s F := by
    refine (scalarArgs_ok h.tag.env h.slot h.src h.tag.tlen h.tag.len h.tag.dat le).mono fun t ⟨ptr,dest,len,env,m,rd,wr⟩ => ?_
    have tag : T t := ⟨env,by rw [m]; exact h.tag.rounds,by rw [m]; exact h.tag.alen,
      by rw [m]; exact h.tag.dat,by rw [m]; exact h.tag.len,h.tag.dD.of_eq rd wr,by rw [m]; exact h.tag.tlen⟩
    refine ⟨tag,⟨env,Nat.zero_le _,by simpa using dest,by simpa using len,h.output.of_eq rd wr,tag.rounds,
      fun hc => by simpa using hc,fun _ => by simp [Spec.Aes.bytesAt,Proof.Gcm.xorKs],rfl,.inr (by decide),Frame.refl _ _⟩,?_,ptr⟩
    simp only [TailSrc,↓reduceIte,Nat.sub_zero]
    exact ⟨ptr,h.input.of_eq rd wr,by simpa using h.alias,trivial⟩
  have ctk : RelCT isa (fun x y => F x ∧ F y) (cryptTailG v.callees true) (fun _ _ => True) := by
    apply Split.rel_each
    intro x y ⟨a,b⟩
    exact (cryptTailG_rel v L true (Q:=Q) (icb₁:=0) (icb₂:=0) (m₁:=x.mem) (m₂:=y.mem) (P₁:=0) (P₂:=0)
      (R:=R) (D:=D) (n:=r) (j:=0)).mono (fun _ _ ⟨hx,hy⟩ => by
        subst hx; subst hy; exact ⟨⟨a.2.1,fun _ => a.2.2.2⟩,b.2.1,fun _ => b.2.2.2⟩) fun _ _ h => h
  have wk (s) (h : F s) : WP isa (cryptTailG v.callees true) s T := by
    refine (WP.with_rdwr (cryptTailG_ok v L true h.2.1 (by simpa using short) rfl h.2.2.1)).mono fun t ⟨out,rd,wr⟩ => ?_
    exact h.1.frame L out.env rd wr dw (crFrame_one out.frame)
  unfold Contiguous.finishScalar
  apply RelCT.seq (rel_next (rel_env_regs [] (fun _ h => h.tag.env) (fun _ h => h.tag.env)
    (fun _ _ _ _ _ h => by cases h) ⟨_,by taint_decide⟩) setup setup)
  exact RelCT.seq (rel_next ctk wk wk) (oneTag_relT v L (.inl rfl) dw)

end VG.Proof.AesGcm.X86_64.ContiguousSeal
