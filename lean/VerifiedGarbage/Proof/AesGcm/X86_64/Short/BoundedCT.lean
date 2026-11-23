module
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.BoundedSeal
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.BoundedText
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.CT
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.KeepReg
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Impl.AesGcm.X86_64.Short
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-! The two-span bounded seal branches and addresses memory only from public lengths and pointers. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.Short
open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxH Block)
section
variable {k : Nat} {s₀ s : State} {Ctx W SP Np A D P Q : Addr} {nl al n R m : Nat} {J : Block} {tl : BitVec 64}

/-- Registers holding the two plaintext spans after their normalization. -/
abbrev SpanArgs (P Q : Addr) (m : Nat) (s : State) :=
  s.gpr .rbx = P ∧ s.gpr .r12 = Q ∧ s.gpr .rbp = BitVec.ofNat 64 m

theorem boundedText_sj_frame (geo : SpanLayout s₀ P Q D W SP m n) (args : SpanArgs P Q m s) (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (hn5 : n < 512)
    (h32 : nb16 al + nb16 n < 32) (S : SM s₀ Ctx W SP A D R al n J tl s) :
    WP isa (.seq (.block textArgs) boundedText) s fun t => SM s₀ Ctx W SP A D R al n J tl t ∧ ZKeep [.xmm4] s t := by
  have dD := C.dE
  have h32' := h32
  simp only [nb16] at h32'
  have hlead : 4 * grp al n - (nb16 al + nb16 n + 1) < 4 := by simp only [grp, nb16]; omega_arith
  have hmp : 4 * grp al n = (4 * grp al n - (nb16 al + nb16 n + 1)) + nb16 al + nb16 n + 1 := by
    simp only [grp, nb16]; omega_arith
  have hnc : n ≤ 16 * nb16 n := by simp only [nb16]; omega_arith
  have hg8 : grp al n ≤ 8 := by simp only [grp, nb16]; omega_arith
  refine WP.seq ?_
  obtain ⟨s₁, run₁, di₁, si₁, dx₁, cx₁, g₁, m₁, rd₁, wr₁, z₁⟩ := textArgs_ok s S.env.r15 S.env.perm.w
    S.r296 S.r272 S.r200 S.r208 (by omega_arith)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have xp : XorPre true s₁ D (W + BitVec.ofNat 64 1040)
      (W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1) + nb16 al))) n :=
    ⟨si₁, dx₁, di₁, cx₁, by omega_arith, by rw [rd₁, wr₁, S.rd, S.wr]; exact C.data.ok.rd,
      by rw [rd₁, wr₁]; exact covers_left (S.env.perm.wC (by omega_arith)),
      by rw [wr₁, S.wr]; exact C.data.wr, fun _ => by rw [wr₁]; exact S.env.perm.wC (by omega_arith),
      dD.sub_right (Lay.wSub (by omega_arith)), fun _ => dD.sub_right (Lay.wSub (by omega_arith)),
      fun _ => Offset.disjoint W (.inr (by omega_arith)) (by omega_arith) (by omega_arith)⟩
  have gs : (⟨textSlot W al n,n⟩ : Region).Sub ⟨W,2560⟩ := Lay.wSub (by omega_arith)
  have sp : SpanPair s₁ P Q D (textSlot W al n) m n :=
    ⟨geo.first, (g₁ _ (by decide) (by decide) (by decide) (by decide)).trans args.1,
      (g₁ _ (by decide) (by decide) (by decide) (by decide)).trans args.2.1,
      (g₁ _ (by decide) (by decide) (by decide) (by decide)).trans args.2.2,
      by rw [rd₁,wr₁,S.rd,S.wr]; exact geo.leftRead,
      geo.leftAlias, geo.leftWork.sub_right gs,
      fun lt => by rw [rd₁,wr₁,S.rd,S.wr]; exact geo.rightRead lt,
      geo.rightAlias, fun lt => (geo.rightWork lt).sub_right gs⟩
  refine WP.mono (boundedText_ok xp sp) fun s₂ ⟨m₂,g₂,rd₂,wr₂,z₂⟩ => ?_
  have fX : Frame [⟨D,n⟩,⟨textSlot W al n,n⟩] s.mem s₂.mem := by
    rw [m₂,m₁]
    have fr := xw_frame true s.mem D (textSlot W al n) (List.zipWith (· ^^^ ·)
      (spanBytes s P Q m n) (bytesAt s.mem (W + BitVec.ofNat 64 1040) n))
    simpa only [List.length_zipWith,spanBytes_length _ _ _ geo.first,length_bytesAt,Nat.min_self] using fr
  refine ⟨S.keep dD fX (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (.inr (.inl fun _ h => h))
      · exact wk_G (by omega_arith))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        rw [g₂ _ (by simp),
          g₁ _ (by decide) (by decide) (by decide) (by decide)])
    (rd₂.trans rd₁) (wr₂.trans wr₁), fun r hr l hl => by rw [z₂ r hr l hl, z₁]⟩

private theorem boundedText_sj (C : OneCtx s₀ k Ctx W SP Np A D nl al n)
    (geo : SpanLayout s₀ P Q D W SP m n) (args : SpanArgs P Q m s)
    (hn : n < 512) (small : nb16 al + nb16 n < 32) (sj : SJ s₀ Ctx W SP A D R al n J tl s) :
    WP isa (.seq (.block textArgs) boundedText) s (SJ s₀ Ctx W SP A D R al n J tl) :=
  WP.mono (boundedText_sj_frame geo args C hn small sj.sm) fun _ ⟨sm,z⟩ =>
    ⟨sm, fun l hl => (z _ (by decide) l hl).trans (sj.z0 l hl),
      fun l hl => (z _ (by decide) l hl).trans (sj.z1 l hl)⟩

private theorem spanAfterArgs (sm : SM s₀ Ctx W SP A D R al n J tl s) (hs : SpanArgs P Q m s)
    (small : nb16 al + nb16 n < 32) :
    WP isa (.block textArgs) s fun t => SpanArgs P Q m t ∧ t.gpr .rdi = textSlot W al n ∧
      t.gpr .rsi = D ∧ t.gpr .rdx = W + BitVec.ofNat 64 1040 ∧ t.gpr .rcx = BitVec.ofNat 64 n := by
  have hg : 4 * grp al n - (nb16 al + nb16 n + 1) < 4 := by
    simp only [grp,nb16] at small ⊢
    omega_arith
  obtain ⟨t,run,di,si,dx,cx,regs,_⟩ := textArgs_ok s sm.env.r15 sm.env.perm.w sm.r296
    sm.r272 sm.r200 sm.r208 (by omega_using [hg,small])
  exact WP.of_runBlock ⟨t,run,⟨(regs _ (by decide) (by decide) (by decide) (by decide)).trans hs.1,
    (regs _ (by decide) (by decide) (by decide) (by decide)).trans hs.2.1,
    (regs _ (by decide) (by decide) (by decide) (by decide)).trans hs.2.2⟩,di,si,dx,cx⟩

private theorem boundedPayload_rel {o' : State} {J' : Block} {tl' : BitVec 64}
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (C' : OneCtx o' k Ctx W SP Np A D nl al n)
    (geo : SpanLayout s₀ P Q D W SP m n) (geo' : SpanLayout o' P Q D W SP m n)
    (hn : n < 512) (small : nb16 al + nb16 n < 32) :
    RelCT isa (fun a b => (SJ s₀ Ctx W SP A D R al n J tl a ∧ SpanArgs P Q m a) ∧
      (SJ o' Ctx W SP A D R al n J' tl' b ∧ SpanArgs P Q m b)) (.seq (.block textArgs) boundedText)
      (fun a b => SJ s₀ Ctx W SP A D R al n J tl a ∧ SJ o' Ctx W SP A D R al n J' tl' b) := by
  refine rel_next (rel_piece spanRegs (fun _ h => h.1.sm.env) (fun _ h => h.1.sm.env)
    (keepsEnv (by decide +kernel)) ⟨_, by taint_decide⟩
    (fun _ h => spanAfterArgs h.1.sm h.2 small) (fun _ h => spanAfterArgs h.1.sm h.2 small)
    (fun _ _ x y r hr => ?_) ⟨_, by taint_decide⟩)
    (fun _ h => boundedText_sj C geo h.2 hn small h.1) (fun _ h => boundedText_sj C' geo' h.2 hn small h.1)
  simp only [spanRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  exacts [x.1.1.trans y.1.1.symm, x.1.2.2.trans y.1.2.2.symm, x.1.2.1.trans y.1.2.1.symm,
    x.2.2.1.trans y.2.2.1.symm, x.2.2.2.1.trans y.2.2.2.1.symm, x.2.1.trans y.2.1.symm,
    x.2.2.2.2.trans y.2.2.2.2.symm]

abbrev SpanEntryArgs (P Q : Addr) (m : Nat) (s : State) :=
  s.gpr .rbx = P ∧ s.gpr .r11 = Q ∧ s.gpr .r10 = BitVec.ofNat 64 m

private theorem boundedStart_sj (C : OneCtx s₀ k Ctx W SP Np A D 12 al n)
    (E : OneEntry s₀ Ctx W SP A D n s) (args : SpanEntryArgs P Q m s) (hp : s₀.gpr .rdx = Np)
    (hl : (s₀.gpr .rcx).toNat = 12) (ha : (s₀.gpr .r9).toNat = al)
    (hal : al < 512) (hn : n < 512) :
    WP isa (.block (j012 ++ sizes ++ ([.mov .rbp (.reg .r10),.mov .r12 (.reg .r11)] : List Instr))) s fun t =>
      ∃ tl, SM s₀ Ctx W SP A D (s₀.gpr .rsi).toNat al n
        (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12)) tl t ∧ SpanArgs P Q m t := by
  obtain ⟨tr,u,e,S,_,_⟩ := shortStart_ok C E hp hl rfl ha hal hn
  let v := (u.setReg .rbp (u.gpr .r10)).setReg .r12 (u.gpr .r11)
  refine WP.block_append_iff.mpr ⟨tr,u,e,WP.of_runBlock ⟨v,by xrun [],s.mem.readW (W + BitVec.ofNat 64 224) 64,?_,?_,?_,?_⟩⟩
  · exact S.keep (s' := v) C.dE (rs := []) (Frame.refl _ _) (by simp)
      (fun r hr => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl <;> rfl) rfl rfl
  · exact (Exec.gpr_keeps (r := .rbx) (by decide +kernel) e).trans args.1
  · exact (Exec.gpr_keeps (r := .r11) (by decide +kernel) e).trans args.2.1
  · exact (Exec.gpr_keeps (r := .r10) (by decide +kernel) e).trans args.2.2

private theorem keepSpan {c : Prog isa} {a b : State} {tr : List Leak} (e : Exec isa c a tr b)
    (hk : [Reg.rbx, .r12, .rbp].all (fun r => KeepReg.keeps r c) = true)
    (h : SpanArgs P Q m a) : SpanArgs P Q m b := by
  have reg (r : Reg) (hr : r ∈ [Reg.rbx,.r12,.rbp]) := Exec.gpr_keeps (List.all_eq_true.mp hk r hr) e
  exact ⟨(reg .rbx (by decide)).trans h.1, (reg .r12 (by decide)).trans h.2.1, (reg .rbp (by decide)).trans h.2.2⟩

private theorem withSpans {F G F' G' : State → Prop} {c : Prog isa}
    (h : RelCT isa (fun a b => F a ∧ G b) c (fun a b => F' a ∧ G' b))
    (hk : [Reg.rbx,.r12,.rbp].all (fun r => KeepReg.keeps r c) = true) :
    RelCT isa (fun a b => (F a ∧ SpanArgs P Q m a) ∧ (G b ∧ SpanArgs P Q m b)) c
      (fun a b => (F' a ∧ SpanArgs P Q m a) ∧ (G' b ∧ SpanArgs P Q m b)) := by
  intro a b tr tr' x y hxy ex ey
  obtain ⟨eq,hx,hy⟩ := h _ _ _ _ _ _ ⟨hxy.1.1,hxy.2.1⟩ ex ey
  exact ⟨eq,⟨hx,keepSpan ex hk hxy.1.2⟩,hy,keepSpan ey hk hxy.2.2⟩

theorem bounded_rel {o' : State} {tm tm' : Mem → Mem} (hpc : PowCT powersP ghashP)
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (C' : OneCtx o' k Ctx W SP Np A D nl al n)
    (hpw : PowFrom powersP ghashP tm s₀ Ctx W SP D n) (hpw' : PowFrom powersP ghashP tm' o' Ctx W SP D n)
    (geo : SpanLayout s₀ P Q D W SP m n) (geo' : SpanLayout o' P Q D W SP m n)
    (hp : s₀.gpr .rdx = Np) (hl : (s₀.gpr .rcx).toNat = nl) (ha : (s₀.gpr .r9).toNat = al)
    (hR : (s₀.gpr .rsi).toNat = R) (hp' : o'.gpr .rdx = Np) (hl' : (o'.gpr .rcx).toNat = nl)
    (ha' : (o'.gpr .r9).toNat = al) (hR' : (o'.gpr .rsi).toNat = R) (hs : IsShort nl al n) :
    RelCT isa (fun a b => (OneEntry s₀ Ctx W SP A D n a ∧ SpanEntryArgs P Q m a) ∧
      (OneEntry o' Ctx W SP A D n b ∧ SpanEntryArgs P Q m b)) bounded.code fun _ _ => True := by
  obtain ⟨h12,hal,hn,small,-⟩ := hs
  subst h12
  have hRr : R = 10 ∨ R = 12 ∨ R = 14 := hR ▸ C.rounds
  let initial := j012 ++ sizes ++ [.mov .rbp (.reg .r10), .mov .r12 (.reg .r11)]
  have start := rel_next (rel_env_regs [.r12] (F₁ := fun a => OneEntry s₀ Ctx W SP A D n a ∧ SpanEntryArgs P Q m a)
    (F₂ := fun b => OneEntry o' Ctx W SP A D n b ∧ SpanEntryArgs P Q m b) (fun _ h => h.1.env)
    (fun _ h => h.1.env) (fun _ _ a b r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [a.1.r12,b.1.r12,hp,hp'])
    (c := .block initial) (by dsimp only [initial]; exact ⟨_,by taint_decide⟩))
    (fun _ h => boundedStart_sj C h.1 h.2 hp hl ha hal hn)
    (fun _ h => boundedStart_sj C' h.1 h.2 hp' hl' ha' hal hn)
  rw [hR,hR'] at start
  refine RelCT.seq start ((RelCT.exists_ (P := fun (ts : BitVec 64 × BitVec 64) a b =>
    (SM s₀ Ctx W SP A D R al n (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12)) ts.1 a ∧ SpanArgs P Q m a) ∧
    (SM o' Ctx W SP A D R al n (Spec.Gcm.j0 (ctxH o'.mem Ctx) (bytesAt o'.mem Np 12)) ts.2 b ∧ SpanArgs P Q m b)) fun _ => ?_).mono
    (fun _ _ ⟨⟨x,hx⟩,⟨y,hy⟩⟩ => ⟨(x,y),hx,hy⟩) (fun _ _ h => h))
  exact RelCT.seq (withSpans (pw_rel C C' hpc hpw hpw' small) (by decide +kernel))
    (RelCT.seq (withSpans (zeroG_rel C C') (by decide +kernel))
    (RelCT.seq (withSpans (copyA_rel C C' hal small) (by decide +kernel))
    (RelCT.seq (withSpans (keystream_rel C C' hRr small) (by decide +kernel))
    (RelCT.seq (boundedPayload_rel C C' geo geo' hn small)
    (RelCT.seq (RelCT.seq (lens_rel C C' hal hn small) (gh_rel C C' hpc.gh hpw.gh hpw'.gh small)) tagK_rel)))))

end
end VG.Proof.AesGcm.X86_64.Short
