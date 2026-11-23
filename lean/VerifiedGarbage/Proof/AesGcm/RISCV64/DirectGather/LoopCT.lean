module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.DirectGather.Loop
public import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.DirectGather.Loop
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-! # Constant time for direct encryption of a public list of descriptors -/

public section

namespace VG.Proof.AesGcm.RISCV64.DirectGather

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64 VG.Spec.Gcm
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_seq rel_taint rel_ite gl_succ)
open VG.Impl.AesGcm.RISCV64.DirectGather (pieces pieceArgs)

structure LoopPublic (a b : LoopArgs) : Prop where
  src : a.src = b.src
  dst : a.dst = b.dst
  count : a.count = b.count
  rounds : a.rounds = b.rounds
  key : a.c = b.c
  state : a.st = b.st
  work : a.w = b.w
  bs : a.b = b.b
  sp : a.sp = b.sp
  ptr : ∀ i < a.count, a.S i = b.S i
  len : ∀ i < a.count, a.n i = b.n i

theorem LoopPublic.doneEq {a b : LoopArgs} (g : LoopPublic a b) {i : Nat} (hi : i ≤ a.count) :
    a.doneBytes i = b.doneBytes i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    exact (gl_succ _ _ _).trans (((by rw [ih (by omega),g.len i (by omega)] : a.doneBytes i + a.n i = b.doneBytes i + b.n i).trans
      (gl_succ _ _ _).symm))

variable {a b : LoopArgs} {e f s t z : State} {i : Nat}

theorem cryptPublic (h : LoopInput a e) (hi : i < a.count) (u : LoopAt a e i s) (v : ArgsAfter a i s z) :
    CrIB true true a.b a.c a.st a.w a.sp a.rounds (a.S i) (a.out i) (a.n i) (a.doneBytes i%16) z :=
  ⟨stepRegs a i,a.icb,a.doneBytes i,rfl,rfl,rfl,rfl,cryptReady h hi u v,
    fun _ => ⟨rfl,h.bkSlice hi (argsFullFrame u v) (v.keep.rd.trans u.rd) (v.keep.wr.trans u.wr)⟩⟩

theorem step_rel (g : LoopPublic a b) (h : LoopInput a e) (k : LoopInput b f) (hi : i < a.count)
    (u : LoopAt a e i s) (v : LoopAt b f i t) : RelCT isa (Eq2 s t) stepCode TT := by
  have hj := g.count ▸ hi
  have x := u.env.choose_spec
  have y := v.env.choose_spec
  have rsp := x.sp.trans (g.sp.trans y.sp.symm)
  have r0 : s.gpr .s0 = t.gpr .s0 := x.s0.trans (g.work.trans y.s0.symm)
  have r8 : s.gpr .s8 = t.gpr .s8 := (x.fr .s8 (by decide)).trans
    ((congrArg (· + BitVec.ofNat 64 (16*i)) g.src).trans (y.fr .s8 (by decide)).symm)
  refine rel_seq (rel_taint [.s0,.s8] rsp ?_ (by taint_decide)) (args_wp h hi u) (args_wp k hj v)
    fun z w az aw => ?_
  · simpa only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true] using And.intro r0 r8
  have pa := cryptPublic h hi u az
  have pb := cryptPublic k hj v aw
  have sizes := g.doneEq (Nat.le_of_lt hi)
  have outs : a.out i=b.out i := by simp only [LoopArgs.out,g.dst,sizes]
  rw [← g.bs,← g.key,← g.state,← g.work,← g.sp,← g.rounds,← g.ptr i hi,← outs,← g.len i hi,← sizes] at pb
  refine rel_seq (RelCT.mono (cryptB_ct h.L) (fun _ _ hz => by
    obtain ⟨rfl,rfl⟩ := hz; exact ⟨pa,pb⟩) fun _ _ _ => trivial)
    (crypt_wp h hi u az) (crypt_wp k hj v aw) fun x' y' hx hy => ?_
  refine rel_taint [.s0] (hx.1.env.sp.trans (g.sp.trans hy.1.env.sp.symm)) ?_ (by taint_decide)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact hx.1.env.s0.trans (g.work.trans hy.1.env.s0.symm)

private abbrev StepPost (a : LoopArgs) (e : State) (i : Nat) (s : State) :=
  LoopAt a e (i+1) s ∧ s.gpr .t1 = BitVec.ofNat 64 (a.count-(i+1))

theorem pieces_rel (g : LoopPublic a b) (h : LoopInput a e) (k : LoopInput b f)
    (u : LoopAt a e 0 s) (v : LoopAt b f 0 t) : RelCT isa (Eq2 s t) pieces TT := by
  have x := u.env.choose_spec
  have y := v.env.choose_spec
  have rsp := x.sp.trans (g.sp.trans y.sp.symm)
  refine rel_seq (rel_taint [.s0] rsp ?_ (by taint_decide)) (countLoad_wp h u) (countLoad_wp k v)
    fun z w ⟨az,cz⟩ ⟨aw,cw⟩ => ?_
  · intro r hr; obtain rfl := List.mem_singleton.mp hr; exact x.s0.trans (g.work.trans y.s0.symm)
  rw [← g.count] at cw
  refine rel_ite (Steps.eval_zero_ofNat _ _ h.countLt cz) (Steps.eval_zero_ofNat _ _ h.countLt cw) ?_ (fun no => ?_)
  · intro _
    exact rel_taint [] (az.env.choose_spec.sp.trans (g.sp.trans aw.env.choose_spec.sp.symm)) (by simp) (by taint_decide)
  have ne : a.count ≠ 0 := by simpa using no
  refine (RelCT.loop (Q := TT) (fun n s t => ∃ i, n = a.count - i ∧ i < a.count ∧
    LoopAt a e i s ∧ LoopAt b f i t) (fun n => ?_) (a.count-0)).mono
    (fun z w ⟨hz,hw⟩ => by subst hz hw; exact ⟨0,rfl,by omega,az,aw⟩) fun _ _ hp => hp
  refine RelCT.exists_ fun i => ?_
  by_cases active : n = a.count-i ∧ i < a.count
  · obtain ⟨rfl,hi⟩ := active
    have hj := g.count ▸ hi
    have rel : RelCT isa (fun s t => LoopAt a e i s ∧ LoopAt b f i t) stepCode TT :=
      fun s t l m z w ⟨hs,ht⟩ => step_rel g h k hi hs ht s t l m z w ⟨rfl,rfl⟩
    refine (rel.wp (F₁ := StepPost a e i) (F₂ := StepPost b f i) (fun s t ⟨ps,pt⟩ =>
      ⟨step_wp h hi ps,step_wp k hj pt⟩)).mono (fun _ _ r => r.2.2) ?_
    rintro s t ⟨_,⟨hs,cs⟩,ht,ct⟩
    rw [← g.count] at ct
    have lim := h.countLt
    have ev₁ := Steps.eval_nonzero_ofNat _ _ (by omega : a.count-(i+1) < 2^64) cs
    have ev₂ := Steps.eval_nonzero_ofNat _ _ (by omega : a.count-(i+1) < 2^64) ct
    refine ⟨by rw [ev₁,ev₂],fun _ => trivial,fun next => ?_⟩
    rw [ev₁] at next
    have lt : i+1 < a.count := by simp at next; omega
    exact ⟨a.count-(i+1),by omega,i+1,rfl,lt,hs,ht⟩
  · exact RelCT.of_false fun _ _ r => active ⟨r.1,r.2.1⟩

end VG.Proof.AesGcm.RISCV64.DirectGather
