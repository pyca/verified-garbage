import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarStep
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejParsePublic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideLoopTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFourLoopTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPhase
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejParse
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegment
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPublic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejRowStep
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBatch

/-! ## From `ResidentRejScalarTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

/-- Extraction may overread ignored bytes.  Its trace depends only on the input
and output cursors; candidate equality is re-established from the functional
three-byte extraction theorem before the next loop decision. -/
theorem scalarStep_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x2,.x3]))
    (.block (scalarChunk++rnAccept++([.mul .x .x16 .x4 .x5] : List Instr))) :=
  VG.Taint.constantTime (A := taint) (VG.AArch64.Taint.ofRegs [.x2,.x3])
    (fun _ _ _ _ h => h) (by taint_decide)

/-- Both executions take the same scalar iteration from equal meaningful input,
even when their original output buffers and ignored overread bytes differ. -/
theorem scalarLoopStep_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) (hd : d<n)
    (hc : (parsed σ b L d).length<256) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t)
      (.block (scalarChunk++rnAccept++([.mul .x .x16 .x4 .x5] : List Instr)))
      (fun s t => ParseInv σ b p n L (d+1) s ∧ ParseInv τ b p n L (d+1) t ∧
        s.gpr .x16=t.gpr .x16 ∧ s.gpr .x16=s.gpr .x4*s.gpr .x5 ∧
        t.gpr .x16=t.gpr .x4*t.gpr .x5) := by
  intro s t tr ur s' t' hp es et
  have he := hp.1.publicRegs hm hsp hp.2
  have ht' := scalarStep_ct s t tr ur s' t' trivial trivial
    ⟨he.1,fun r hr => he.2 r (by
      simp only [VG.AArch64.Taint.ofRegs,RegSet.mem_ofList,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> simp)⟩ es et
  obtain ⟨_,u,eu,hu⟩ := scalarLoopStep_ok hs hp.1 hd hc
  obtain ⟨_,v,ev,hv⟩ := scalarLoopStep_ok ht hp.2 hd (by rw [← parsed_eq hm (by omega) L]; exact hc)
  obtain ⟨_,rfl⟩ := Exec.det es eu
  obtain ⟨_,rfl⟩ := Exec.det et ev
  have hg := hu.1.publicRegs hm hsp hv.1
  exact ⟨ht',hu.1,hv.1,(by rw [hu.2,hv.2,hg.2 .x4 (by simp),hg.2 .x5 (by simp)]),hu.2,hv.2⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejWidePhaseTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def WideReady (σ : State) (b p : Addr) (n d : Nat) (L : List VG.Spec.MlDsa.Zq) (s : State) : Prop :=
  ParseInv σ b p n L d s ∧ s.gpr .x17=16 ∧
    s.gpr .x16=(if 16≤(s.gpr .x4).toNat ∧ 16≤(s.gpr .x5).toNat then 16 else 0)

theorem widePhase_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) :
    RelCT isa (fun s t => WideReady σ b p n d L s ∧ WideReady τ b p n d L t)
      (.ite (.zero .x .x16) (.block []) (.loop wideBody (.nonzero .x .x16)))
      (fun s t => ∃j,ParseInv σ b p n L j s ∧ ParseInv τ b p n L j t ∧ j%4=d%4) := by
  apply RelCT.ite
  · intro s t hp
    have hr := hp.1.1.publicRegs hm hsp hp.2.1
    rw [eval_zero,eval_zero,hp.1.2.2,hp.2.2.2,hr.2 .x4 (by simp),hr.2 .x5 (by simp)]
  · exact RelCT.block_nil (fun _ _ hp => ⟨d,hp.1.1.1,hp.1.2.1,rfl⟩)
  · intro s t tr ur s' t' hp es et
    have hg := hp.1.1.2.2
    rw [hp.1.1.1.x4,hp.1.1.1.x5] at hg
    have hgood : 16≤256-(parsed σ b L d).length ∧ 16≤n-d := by
      by_contra hn
      have he := hp.2
      rw [eval_zero,hg,ite_eq_right hn] at he
      contradiction
    exact wideLoop_relCT hs ht hm hsp (by omega) (by omega) _ _ _ _ _ _
      ⟨hp.1.1.1,hp.1.2.1,hp.1.1.2.1,hp.1.2.2.1⟩ es et

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejFourPhaseTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def FourReady (σ : State) (b p : Addr) (n d : Nat) (L : List VG.Spec.MlDsa.Zq) (s : State) : Prop :=
  ParseInv σ b p n L d s ∧ s.gpr .x17=4 ∧
    s.gpr .x16=(if 4≤(s.gpr .x4).toNat then s.gpr .x5 else 0)

theorem fourPhase_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) (hmod : d%4=n%4) :
    RelCT isa (fun s t => FourReady σ b p n d L s ∧ FourReady τ b p n d L t)
      (.ite (.zero .x .x16) (.block []) (.loop vectorBody (.nonzero .x .x16)))
      (fun s t => ∃j,ParseInv σ b p n L j s ∧ ParseInv τ b p n L j t  ) := by
  apply RelCT.ite
  · intro s t hp
    have hr := hp.1.1.publicRegs hm hsp hp.2.1
    rw [eval_zero,eval_zero,hp.1.2.2,hp.2.2.2,hr.2 .x4 (by simp),hr.2 .x5 (by simp)]
  · exact RelCT.block_nil (fun _ _ hp => ⟨d,hp.1.1.1,hp.1.2.1⟩)
  · intro s t tr ur s' t' hp es et
    have hg := hp.1.1.2.2
    rw [hp.1.1.1.x4] at hg
    have hcap : 4≤256-(parsed σ b L d).length := by
      by_contra hn
      have he := hp.2
      rw [eval_zero,hg,ite_eq_right hn] at he
      contradiction
    have hcount : n-d≠0 := by
      intro hn
      have hx : s.gpr .x5=0#64 := BitVec.eq_of_toNat_eq (hp.1.1.1.x5.trans hn)
      have he := hp.2
      rw [eval_zero,hg,ite_eq_left hcap,hx] at he
      contradiction
    have hb := hp.1.1.1.bound
    exact fourLoop_relCT hs ht hm hsp (by omega) hmod (by omega) _ _ _ _ _ _
      ⟨hp.1.1.1,hp.1.2.1,hp.1.1.2.1,hp.1.2.2.1⟩ es et

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejScalarLoopTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (eval_nonzero)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

private theorem guard_nonzero {s : State} (he : isa.eval (.nonzero .x .x16) s=some true)
    (hg : s.gpr .x16=s.gpr .x4*s.gpr .x5) :
    (s.gpr .x4).toNat≠0 ∧ (s.gpr .x5).toNat≠0 := by
  have hn : s.gpr .x16≠0#64 := by
    intro hz
    rw [eval_nonzero,hz] at he
    contradiction
  constructor
  · intro hz
    have hx : s.gpr .x4=0#64 := BitVec.eq_of_toNat_eq hz
    apply hn
    rw [hg,hx,BitVec.zero_mul]
  · intro hz
    have hx : s.gpr .x5=0#64 := BitVec.eq_of_toNat_eq hz
    apply hn
    rw [hg,hx,BitVec.mul_zero]

theorem scalarLoop_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) (hd : d<n)
    (hc : (parsed σ b L d).length<256) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t)
      (.loop (.block (scalarChunk++rnAccept++([.mul .x .x16 .x4 .x5] : List Instr)))
        (.nonzero .x .x16)) (fun _ _ => True) := by
  let I := fun m s t => ∃j,j<n ∧ (parsed σ b L j).length<256 ∧ n-j=m ∧
    ParseInv σ b p n L j s ∧ ParseInv τ b p n L j t
  have hstep : ∀m,RelCT isa (I m)
      (.block (scalarChunk++rnAccept++([.mul .x .x16 .x4 .x5] : List Instr)))
      (fun s t => isa.eval (.nonzero .x .x16) s=isa.eval (.nonzero .x .x16) t ∧
        (isa.eval (.nonzero .x .x16) s=some false → True) ∧
        (isa.eval (.nonzero .x .x16) s=some true → ∃m'<m,I m' s t)) := by
    intro m s t tr ur s' t' hp es et
    obtain ⟨j,hj,hc',rfl,hp⟩ := hp
    obtain ⟨htrace,ha,hb,heq,hga,hgb⟩ := scalarLoopStep_relCT hs ht hm hsp hj hc' _ _ _ _ _ _ hp es et
    refine ⟨htrace,by rw [eval_nonzero,eval_nonzero,heq],fun _ => trivial,?_⟩
    intro hcontinue
    obtain ⟨h4,h5⟩ := guard_nonzero hcontinue hga
    rw [ha.x4] at h4
    rw [ha.x5] at h5
    have hj' : j+1<n := by have := ha.bound; omega
    have hc'' : (parsed σ b L (j+1)).length<256 := by omega
    exact ⟨n-(j+1),by omega,j+1,hj',hc'',rfl,ha,hb⟩
  exact (RelCT.loop I hstep (n-d)).mono
    (fun _ _ hp => ⟨d,hd,hc,rfl,hp⟩) (fun _ _ h => h)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejScalarPhaseTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def ScalarReady (σ : State) (b p : Addr) (n d : Nat) (L : List VG.Spec.MlDsa.Zq) (s : State) : Prop :=
  ParseInv σ b p n L d s ∧ s.gpr .x16=s.gpr .x4*s.gpr .x5

theorem scalarBranch_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) :
    RelCT isa (fun s t => ScalarReady σ b p n d L s ∧ ScalarReady τ b p n d L t)
      (.ite (.zero .x .x16) (.block []) scalarLoop) (fun _ _ => True) := by
  apply RelCT.ite
  · intro s t hp
    have hr := hp.1.1.publicRegs hm hsp hp.2.1
    rw [eval_zero,eval_zero,hp.1.2,hp.2.2,hr.2 .x4 (by simp),hr.2 .x5 (by simp)]
  · exact RelCT.block_nil (fun _ _ _ => trivial)
  · intro s t tr ur s' t' hp es et
    have hnonzero : s.gpr .x16≠0#64 := by
      intro hz
      have hh := hp.2
      rw [eval_zero,hz] at hh
      contradiction
    have h4 : (s.gpr .x4).toNat≠0 := by
      intro hz
      apply hnonzero
      rw [hp.1.1.2,show s.gpr .x4=0#64 from BitVec.eq_of_toNat_eq hz,BitVec.zero_mul]
    have h5 : (s.gpr .x5).toNat≠0 := by
      intro hz
      apply hnonzero
      rw [hp.1.1.2,show s.gpr .x5=0#64 from BitVec.eq_of_toNat_eq hz,BitVec.mul_zero]
    rw [hp.1.1.1.x4] at h4
    rw [hp.1.1.1.x5] at h5
    have hb := hp.1.1.1.bound
    exact scalarLoop_relCT hs ht hm hsp (by omega) (by omega) _ _ _ _ _ _ ⟨hp.1.1.1,hp.1.2.1⟩ es et

private theorem scalarSetup_ok {σ s : State} {b p : Addr} {n d : Nat} {L : List VG.Spec.MlDsa.Zq}
    (h : ParseInv σ b p n L d s) :
    WP isa (.block [.mul .x .x16 .x4 .x5]) s (ScalarReady σ b p n d L) := by
  have hw : WP isa (.block [.mul .x .x16 .x4 .x5]) s fun t =>
      Only [.x16] s t ∧ t.gpr .x16=s.gpr .x4*s.gpr .x5 :=
    wp_mul fun t ht et => wp_nil ⟨ht,et⟩
  refine WP.mono (WP.keepV (by decide) hw) fun t ⟨⟨ht,hg⟩,hv⟩ => ?_
  exact ⟨h.of_control (ht.mono (by decide)) hv,by rw [ht.get .x4,ht.get .x5]; exact hg⟩

theorem scalarPhase_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t)
      (.seq (.block [.mul .x .x16 .x4 .x5])
        (.ite (.zero .x .x16) (.block []) scalarLoop)) (fun _ _ => True) := by
  apply RelCT.seq (R := fun s t => ScalarReady σ b p n d L s ∧ ScalarReady τ b p n d L t)
  · intro s t tr ur s' t' hp es et
    have hg := hp.1.publicRegs hm hsp hp.2
    have hct : RelCT isa (fun s t => s.sp=t.sp)
        (.block [.mul .x .x16 .x4 .x5]) (fun _ _ => True) :=
      RelCT.taint (A := taint) (Taint.ofRegs [])
        (fun _ _ h => ⟨h,by simp [Taint.ofRegs,RegSet.mem_ofList]⟩) (by taint_decide)
    obtain ⟨_,a,ea,ha⟩ := scalarSetup_ok hp.1
    obtain ⟨_,b,eb,hb⟩ := scalarSetup_ok hp.2
    obtain ⟨_,rfl⟩ := Exec.det es ea
    obtain ⟨_,rfl⟩ := Exec.det et eb
    exact ⟨(hct _ _ _ _ _ _ hg.1 es et).1,ha,hb⟩
  · exact scalarBranch_relCT hs ht hm hsp

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejControlTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

theorem control_pair {P Q R S : State → Prop} {c : Prog isa}
    (hsp : ∀s t,P s → Q t → s.sp=t.sp)
    (hl : ∀s,P s → WP isa c s R) (hr : ∀s,Q s → WP isa c s S)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (hc : (taint.check (Taint.ofRegs []) c hint).isSome=true) :
    RelCT isa (fun s t => P s ∧ Q t) c (fun s t => R s ∧ S t) := by
  have hh : RelCT isa (fun s t => P s ∧ Q t) c (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ h => ⟨hsp _ _ h.1 h.2,by simp [Taint.ofRegs,RegSet.mem_ofList]⟩) hc
  exact (hh.wp (fun _ _ h => ⟨hl _ h.1,hr _ h.2⟩)).mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem fourSetup_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hsp : σ.sp=τ.sp) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t)
      (.block (vectorSetup++guard))
      (fun s t => FourReady σ b p n d L s ∧ FourReady τ b p n d L t) :=
  control_pair (fun _ _ hs ht => hs.keep.sp.trans (hsp.trans ht.keep.sp.symm))
    (fun _ h => fourSetup_ok h) (fun _ h => fourSetup_ok h) (by taint_decide)

theorem wideControl_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hsp : σ.sp=τ.sp) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t)
      (.block (([.movz .x .x17 16 0] : List Instr)++wideGuard))
      (fun s t => WideReady σ b p n d L s ∧ WideReady τ b p n d L t) :=
  control_pair (fun _ _ hs ht => hs.keep.sp.trans (hsp.trans ht.keep.sp.symm))
    (fun _ h => wideControl_ok h) (fun _ h => wideControl_ok h) (by taint_decide)

theorem parseFour_relCT (v : Nat) {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) (hmod : d%4=n%4) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t)
      (parse4 v) (fun _ _ => True) := by
  unfold parse4
  apply RelCT.seq (fourSetup_relCT hsp)
  apply RelCT.seq (fourPhase_relCT hs ht hm hsp hmod)
  exact RelCT.exists_ (fun j => scalarPhase_relCT hs ht hm hsp (d := j))

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejParseTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def Start (s : State) (b p : Addr) (n : Nat) (L : List Zq) : Prop :=
  s.gpr .x2=b ∧ s.gpr .x3=coeffAddr p L.length ∧ (s.gpr .x4).toNat=256-L.length ∧
    (s.gpr .x5).toNat=n ∧ (s.gpr .x9).toNat=q ∧ Stored s.mem p L

theorem vectorSetup_start {σ : State} {b p : Addr} {n : Nat} {L : List Zq}
    (h : Start σ b p n L) : WP isa (.block vectorSetup) σ (ParseInv σ b p n L 0) := by
  refine WP.mono (vectorSetup_ok (s := σ) h.2.2.2.2.1) fun a ⟨ha,hc,_,h0,h10⟩ => ?_
  refine ⟨ha.only.keep.mono (by decide),by rw [ha.only.mem]; exact Frame.refl _ _,hc,
    Nat.zero_le _,?_,?_,?_,?_,h10,h0,?_⟩
  · rw [ha.only.get .x2,h.1]; exact (ptr_zero b).symm
  · rw [ha.only.get .x3]; exact h.2.1
  · rw [ha.only.get .x4]; exact h.2.2.1
  · rw [ha.only.get .x5]; exact h.2.2.2.1
  · rw [ha.only.mem]; exact h.2.2.2.2.2

theorem parse_relCT (v : Nat) {σ τ : State} {b p : Addr} {n : Nat} {L : List Zq}
    (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (ss : Start σ b p n L) (st : Start τ b p n L)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) (hmod : n%4=0) :
    RelCT isa (fun s t => s=σ ∧ t=τ) (parse v) (fun _ _ => True) := by
  unfold parse
  apply RelCT.seq (R := fun s t => WideReady σ b p n 0 L s ∧ WideReady τ b p n 0 L t)
  · rw [List.append_assoc]
    apply RelCT.block_append
    apply RelCT.seq (R := fun s t => ParseInv σ b p n L 0 s ∧ ParseInv τ b p n L 0 t)
    · exact control_pair (fun _ _ h1 h2 => by subst h1; subst h2; exact hsp)
        (fun s h => by subst s; exact vectorSetup_start ss)
        (fun t h => by subst t; exact vectorSetup_start st) (by taint_decide)
    · exact wideControl_relCT hsp
  · apply RelCT.seq (widePhase_relCT hs ht hm hsp)
    intro s t tr ur s' t' hp es et
    obtain ⟨j,hj,hk,hjm⟩ := hp
    exact parseFour_relCT v hs ht hm hsp (by rw [hjm,hmod]) _ _ _ _ _ _ ⟨hj,hk⟩ es et

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejSegmentTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

private theorem layout_only {s t : State} {b p : Addr} {n : Nat} {rs : List Reg}
    (h : StreamLayout s b p n) (ht : Only rs s t) : StreamLayout t b p n := by
  refine ⟨h.bound,?_,?_,?_,?_,h.disjoint⟩
  · intro j hj; rw [ht.rd,ht.wr]; exact h.read16 j hj
  · intro j hj; rw [ht.rd,ht.wr]; exact h.read4 j hj
  · intro j hj; rw [ht.wr]; exact h.write4 j hj
  · intro j hj; rw [ht.wr]; exact h.write16 j hj

/-- Segment timing needs equality only for the consumed candidate bytes, not
for preexisting output bytes or the ignored fourth byte of scalar loads. -/
theorem segment_relCT (v k off n : Nat) (hk : k<4) (ho : off<4096) (hn : n<65536)
    {hintSetup hintStore : VG.Taint.Hint VG.AArch64.Taint.T}
    (checkSetup : (taint.check (Taint.ofRegs [.x19,.x21]) (.block (setup k off n)) hintSetup).isSome=true)
    (checkStore : (taint.check (Taint.ofRegs [.x19])
      (.block [.str .x .x4 .x19 (counts+8*k)]) hintStore).isSome=true)
    {σ τ : State} {L : List Zq} (hL : L.length≤256) (hmod : n%4=0)
    (hsp : σ.sp=τ.sp) (h19 : σ.gpr .x19=τ.gpr .x19)
    (h21 : σ.gpr .x21=τ.gpr .x21)
    (hs : StreamLayout σ (segmentInput σ k off) (segmentOutput σ k) n)
    (ht : StreamLayout τ (segmentInput τ k off) (segmentOutput τ k) n)
    (hrs : InRegions (σ.rd++σ.wr) (countAddress σ k) 8)
    (hrt : InRegions (τ.rd++τ.wr) (countAddress τ k) 8)
    (hcs : (σ.mem.readW (countAddress σ k) 64).toNat=256-L.length)
    (hct : (τ.mem.readW (countAddress τ k) 64).toNat=256-L.length)
    (hss : Stored σ.mem (segmentOutput σ k) L)
    (hst : Stored τ.mem (segmentOutput τ k) L)
    (hm : InputEq σ τ (segmentInput σ k off) n) :
    RelCT isa (fun s t => s=σ ∧ t=τ) (segment v k off n) (fun _ _ => True) := by
  have hi : segmentInput τ k off=segmentInput σ k off := by simp only [segmentInput,h19]
  have hp : segmentOutput τ k=segmentOutput σ k := by simp only [segmentOutput,h21]
  let P (a : State) (s : State) :=
    Only [.x2,.x3,.x4,.x5,.x6,.x9,.x10] a s ∧
      Start s (segmentInput σ k off) (segmentOutput σ k) n L
  have ws : WP isa (.block (setup k off n)) σ (P σ) := by
    refine WP.mono (setup_ok k off n hk ho hn hL hrs hcs) fun s ⟨hh,h2,h3,h4,h5,h9⟩ => ?_
    exact ⟨hh,h2,h3,h4,h5,h9,by rw [hh.mem]; exact hss⟩
  have wt : WP isa (.block (setup k off n)) τ (P τ) := by
    refine WP.mono (setup_ok k off n hk ho hn hL hrt hct) fun s ⟨hh,h2,h3,h4,h5,h9⟩ => ?_
    rw [hi] at h2
    rw [hp] at h3
    exact ⟨hh,h2,h3,h4,h5,h9,by rw [hh.mem,←hp]; exact hst⟩
  unfold segment
  apply RelCT.seq (R := fun s t => P σ s ∧ P τ t)
  · have hc : RelCT isa (fun s t => s=σ ∧ t=τ) (.block (setup k off n)) (fun _ _ => True) :=
      RelCT.taint (A := taint) (Taint.ofRegs [.x19,.x21])
        (fun s t h => by
          rcases h with ⟨rfl,rfl⟩
          exact ⟨hsp,by simp [Taint.ofRegs,RegSet.mem_ofList,h19,h21]⟩) checkSetup
    exact (hc.wp (fun s t h => by rcases h with ⟨rfl,rfl⟩; exact ⟨ws,wt⟩)).mono
      (fun _ _ h => h) (fun _ _ h => h.2)
  · intro s t tr ur s' t' hh es et
    have ls := layout_only hs hh.1.1
    have lt := layout_only ht hh.2.1
    rw [hi,hp] at lt
    have im : InputEq s t (segmentInput σ k off) n := by
      intro i hb
      rw [hh.1.1.mem,hh.2.1.mem]
      exact hm i hb
    have sp : s.sp=t.sp := hh.1.1.sp.trans (hsp.trans hh.2.1.sp.symm)
    have wpS := parse_ok v ls hmod hL hh.1.2.1 hh.1.2.2.1 hh.1.2.2.2.1
      hh.1.2.2.2.2.1 hh.1.2.2.2.2.2.1 hh.1.2.2.2.2.2.2
    have wpT := parse_ok v lt hmod hL hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2.1
      hh.2.2.2.2.2.1 hh.2.2.2.2.2.2.1 hh.2.2.2.2.2.2.2
    have pc := (parse_relCT v ls lt hh.1.2 hh.2.2 im sp hmod).wp
      (fun a b h => by rcases h with ⟨rfl,rfl⟩; exact ⟨wpS,wpT⟩)
    apply RelCT.seq pc ?_ s t tr ur s' t' ⟨rfl,rfl⟩ es et
    exact RelCT.taint (A := taint) (Taint.ofRegs [.x19])
      (fun a b h => ⟨h.2.1.1.sp.trans (sp.trans h.2.2.1.sp.symm),by
        simp only [Taint.ofRegs,RegSet.mem_ofList,List.mem_singleton]
        intro r hr
        subst r
        rw [h.2.1.1.get .x19,h.2.2.1.get .x19,hh.1.1.get .x19,hh.2.1.get .x19]
        exact h19⟩) checkStore

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejRowTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Spec.MlDsa (Zq)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

 theorem Pub.rowResult {v k off n : Nat} {σ τ : State} (h : Pub v σ τ)
    (hk : k<v) (L : List Zq) : rowResult σ k off n L=rowResult τ k off n L := by
  have hb : streamBytes σ k off (3*n)=streamBytes τ k off (3*n) := by
    unfold streamBytes
    apply List.map_congr_left
    intro i hi
    exact h.byte hk _
  exact congrArg (VG.Proof.MlDsa.Sample.rnFold L) hb

theorem rowStep_relCT {v blocks k off n : Nat} {σ τ : State} {L : Nat → List Zq}
    (hp : Pre v σ) (hq : Pre v τ) (pub : Pub v σ τ) (hk : k<v)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (variant : Nat)
    {hintSetup hintStore : VG.Taint.Hint VG.AArch64.Taint.T}
    (checkSetup : (taint.check (Taint.ofRegs [.x19,.x21]) (.block (setup k off n)) hintSetup).isSome=true)
    (checkStore : (taint.check (Taint.ofRegs [.x19])
      (.block [.str .x .x4 .x19 (counts+8*k)]) hintStore).isSome=true) :
    RelCT isa (fun s t => Rows v blocks σ L s ∧ Rows v blocks τ L t)
      (segment variant k off n)
      (fun s t => Rows v blocks σ (updateRow L k (rowResult σ k off n (L k))) s ∧
        Rows v blocks τ (updateRow L k (rowResult σ k off n (L k))) t) := by
  have ct : RelCT isa (fun s t => Rows v blocks σ L s ∧ Rows v blocks τ L t)
      (segment variant k off n) (fun _ _ => True) := by
    intro s t tr ur s' t' h es et
    have hb : off+3*n≤1008 := by have:=h.1.blockBound; omega
    have crs : InRegions (s.rd++s.wr) (countAddress s k) 8 := by
      rw [segment_count_eq h.1.env]
      exact in_scr_rd hp h.1.env.wr (by unfold counts; have:=hp.streams; omega)
    have crt : InRegions (t.rd++t.wr) (countAddress t k) 8 := by
      rw [segment_count_eq h.2.env]
      exact in_scr_rd hq h.2.env.wr (by unfold counts; have:=hq.streams; omega)
    have hs19 : s.gpr .x19=t.gpr .x19 := by rw [h.1.env.x19,h.2.env.x19,pub.2.2.1]
    have hs21 : s.gpr .x21=t.gpr .x21 := by rw [h.1.env.x21,h.2.env.x21,pub.2.1]
    have hm : InputEq s t (segmentInput s k off) n := by
      rw [segment_input_eq h.1.env]
      exact rows_input_eq pub h.1 h.2 hk hn
    exact segment_relCT variant k off n (by have:=hp.streams; omega) (by omega) (by omega)
      checkSetup checkStore (h.1.length k hk) hmod
      (h.1.env.sp.trans (pub.2.2.2.1.trans h.2.env.sp.symm)) hs19 hs21
      (segment_layout hp h.1.env hk hb) (segment_layout hq h.2.env hk hb) crs crt
      (by rw [segment_count_eq h.1.env]; exact h.1.counts k hk)
      (by rw [segment_count_eq h.2.env]; exact h.2.counts k hk)
      (by rw [segment_output_eq h.1.env]; exact h.1.stored k hk)
      (by rw [segment_output_eq h.2.env]; exact h.2.stored k hk)
      hm _ _ _ _ _ _ ⟨rfl,rfl⟩ es et
  refine (ct.wp (fun s t h => ⟨rowStep_ok hp h.1 hk hn hmod variant,
    rowStep_ok hq h.2 hk hn hmod variant⟩)).mono (fun _ _ h => h) ?_
  intro s t h
  rw [←pub.rowResult hk (off := off) (n := n) (L k)] at h
  exact h.2

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejBatchTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Spec.MlDsa (Zq)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

structure SegmentChecks (k off n : Nat) where
  setupHint : VG.Taint.Hint VG.AArch64.Taint.T
  storeHint : VG.Taint.Hint VG.AArch64.Taint.T
  setup : (taint.check (Taint.ofRegs [.x19,.x21]) (.block (setup k off n)) setupHint).isSome=true
  store : (taint.check (Taint.ofRegs [.x19])
    (.block [.str .x .x4 .x19 (counts+8*k)]) storeHint).isSome=true

theorem batchFour_relCT {blocks off n : Nat} {σ τ : State} {L : Nat → List Zq}
    (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (variant : Nat)
    (checks : ∀k<4,SegmentChecks k off n) :
    RelCT isa (fun s t => Rows 4 blocks σ L s ∧ Rows 4 blocks τ L t)
      (Four.batch variant off n)
      (fun s t => Rows 4 blocks σ (fun k => rowResult σ k off n (L k)) s ∧
        Rows 4 blocks τ (fun k => rowResult σ k off n (L k)) t) := by
  unfold Four.batch
  refine RelCT.seq (rowStep_relCT hp hq pub (by decide : 0<4) hn hmod variant
    (checks 0 (by decide)).setup (checks 0 (by decide)).store) ?_
  refine RelCT.seq (rowStep_relCT hp hq pub (by decide : 1<4) hn hmod variant
    (checks 1 (by decide)).setup (checks 1 (by decide)).store) ?_
  refine RelCT.seq (rowStep_relCT hp hq pub (by decide : 2<4) hn hmod variant
    (checks 2 (by decide)).setup (checks 2 (by decide)).store) ?_
  refine (rowStep_relCT hp hq pub (by decide : 3<4) hn hmod variant
    (checks 3 (by decide)).setup (checks 3 (by decide)).store).mono (fun _ _ h => h) ?_
  intro s t h
  constructor
  · apply h.1.congr
    intro k hk
    rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 by omega) with rfl | rfl | rfl | rfl <;> rfl
  · apply h.2.congr
    intro k hk
    rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 by omega) with rfl | rfl | rfl | rfl <;> rfl

theorem batchTwo_relCT {blocks off n : Nat} {σ τ : State} {L : Nat → List Zq}
    (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (variant : Nat)
    (checks : ∀k<2,SegmentChecks k off n) :
    RelCT isa (fun s t => Rows 2 blocks σ L s ∧ Rows 2 blocks τ L t)
      (Two.batch variant off n)
      (fun s t => Rows 2 blocks σ (fun k => rowResult σ k off n (L k)) s ∧
        Rows 2 blocks τ (fun k => rowResult σ k off n (L k)) t) := by
  unfold Two.batch
  refine RelCT.seq (rowStep_relCT hp hq pub (by decide : 0<2) hn hmod variant
    (checks 0 (by decide)).setup (checks 0 (by decide)).store) ?_
  refine (rowStep_relCT hp hq pub (by decide : 1<2) hn hmod variant
    (checks 1 (by decide)).setup (checks 1 (by decide)).store).mono (fun _ _ h => h) ?_
  intro s t h
  constructor
  · apply h.1.congr
    intro k hk
    rcases (show k=0 ∨ k=1 by omega) with rfl | rfl <;> rfl
  · apply h.2.congr
    intro k hk
    rcases (show k=0 ∨ k=1 by omega) with rfl | rfl <;> rfl

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end
