import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Call
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMaskTail
import VerifiedGarbage.Spec.MlDsa.CommitTail

/-! ## From `CommitTailCall.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64 VG.Spec.MlDsa

theorem callee65 {S : Nat} (hS : S<2^64) :
    CalleeOk S (Impl.MlDsa.AArch64.Sign.CommitTail.code 768 48)
      (commitTailContract AArch64.abi 768 48 S) :=
  CalleeOk.of_verified hS verified65 (by omega) (by
    have h : (Impl.MlDsa.AArch64.Sign.CommitTail.code 768 48).aarch64Depth=0 := by decide
    rw [h]; omega)

theorem callee87 {S : Nat} (hS : S<2^64) :
    CalleeOk S (Impl.MlDsa.AArch64.Sign.CommitTail.code 1024 64)
      (commitTailContract AArch64.abi 1024 64 S) :=
  CalleeOk.of_verified hS verified87 (by omega) (by
    have h : (Impl.MlDsa.AArch64.Sign.CommitTail.code 1024 64).aarch64Depth=0 := by decide
    rw [h]; omega)

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CachedHashPre.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc Arg)
open VG.Impl.MlDsa.AArch64.Sign.Cached (hashArgs)

def hashReads (p : Params) (s : State) : List Region :=
  [⟨pa s (.x26,0),64⟩,⟨pa s (sc oW1),p.k*w1Len p⟩,⟨pa s (sc oMS),64⟩]
def hashWrites (p : Params) (s : State) : List Region :=
  [⟨pa s (sc oCT),cLen p⟩,⟨pa s t1P,2048⟩,⟨pa s t4P,1024⟩]

theorem hash_pre {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87) {S : Nat} {s s1 : State}
    (L : Lay S (sgR p) (sgW p) s) (h1 : Args (hashArgs p) s s1) :
    (commitTailContract abi (p.k*w1Len p) (cLen p) S).pre
      (s1.callEntry.withRegions (hashReads p s) (hashWrites p s)) := by
  sig_pre [commitTailContract,commitTailSig,AArch64.abi,VG.AArch64.argRegs]
  rw [h1.ptr (r:=.x0) (p:=(.x26,0)) (by simp [hashArgs]),
    h1.ptr (r:=.x1) (p:=sc oW1) (by simp [hashArgs]),
    h1.ptr (r:=.x2) (p:=sc oCT) (by simp [hashArgs]),
    h1.ptr (r:=.x3) (p:=t1P) (by simp [hashArgs]),
    h1.ptr (r:=.x4) (p:=sc oMS) (by simp [hashArgs]),
    h1.ptr (r:=.x6) (p:=t4P) (by simp [hashArgs]),Args.sp h1]
  simp only [hashReads,hashWrites]
  and_intros
  all_goals first
    | with_reducible rfl
    | exact True.intro
    | exact wfP_of (Lay.spS L)
    | exact resv fun _ hr=>by
        rw [stackBelow_mem hr]
        refine conj_cons (L.stkD (p:=(.x26,0)) (l:=64) (by rcases hp with rfl|rfl <;> decide)) ?_
        refine conj_cons (L.stkD (p:=sc oW1) (l:=p.k*w1Len p) (by rcases hp with rfl|rfl <;> decide)) ?_
        refine conj_cons (L.stkD (p:=sc oCT) (l:=cLen p) (by rcases hp with rfl|rfl <;> decide)) ?_
        refine conj_cons (L.stkD (p:=t1P) (l:=2048) (by rcases hp with rfl|rfl <;> decide)) ?_
        refine conj_cons (L.stkD (p:=sc oMS) (l:=64) (by rcases hp with rfl|rfl <;> decide)) ?_
        exact conj_cons (L.stkD (p:=t4P) (l:=1024) (by rcases hp with rfl|rfl <;> decide)) conj_nil
    | exact Lay.disj L (by rcases hp with rfl|rfl <;> decide)
    | exact (Lay.disj L (by rcases hp with rfl|rfl <;> decide)).symm
    | exact Lay.nwp L (by rcases hp with rfl|rfl <;> decide)

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedHashGlue.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc Arg glue)
open VG.Impl.MlDsa.AArch64.Sign.Cached (hashArgs)
open VG.Proof.MlKem.AArch64 (Only wp_nil)

/-- The nonce lives in x9, which these seven argument moves preserve. -/
theorem hashGlue_ok (p : Params) (s : State) :
    WP isa (.block (glue (hashArgs p))) s (Args (hashArgs p) s) := by
  simp only [hashArgs,glue,Arg.instrs]
  refine lea_ok (by decide) 0 fun s0 h0 e0 => ?_
  refine lea_ok (by decide) oW1 fun s1 h1 e1 => ?_
  refine lea_ok (by decide) oCT fun s2 h2 e2 => ?_
  refine lea_ok (by decide) t1P.2 fun s3 h3 e3 => ?_
  refine lea_ok (by decide) oMS fun s4 h4 e4 => ?_
  refine lea_ok (by decide) 0 fun s5 h5 e5 => ?_
  refine lea_ok (by decide) t4P.2 fun s6 h6 e6 => ?_
  have h := (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6
  apply wp_nil
  refine ⟨⟨?_,h.mem⟩,h.keep.mono (by decide)⟩
  simp only [List.mem_cons,List.not_mem_nil,forall_eq_or_imp,false_implies,implies_true,and_true,
    Arg.val,pa]
  and_intros
  · rw [h6.get .x0 (by decide),h5.get .x0 (by decide),h4.get .x0 (by decide),
      h3.get .x0 (by decide),h2.get .x0 (by decide),h1.get .x0 (by decide),e0]
  · rw [h6.get .x1 (by decide),h5.get .x1 (by decide),h4.get .x1 (by decide),
      h3.get .x1 (by decide),h2.get .x1 (by decide),e1,h0.get .x28 (by decide)]
  · rw [h6.get .x2 (by decide),h5.get .x2 (by decide),h4.get .x2 (by decide),
      h3.get .x2 (by decide),e2,h1.get .x28 (by decide),h0.get .x28 (by decide)]
  · rw [h6.get .x3 (by decide),h5.get .x3 (by decide),h4.get .x3 (by decide),e3,
      h2.get .x28 (by decide),h1.get .x28 (by decide),h0.get .x28 (by decide)]
  · rw [h6.get .x4 (by decide),h5.get .x4 (by decide),e4,h3.get .x28 (by decide),
      h2.get .x28 (by decide),h1.get .x28 (by decide),h0.get .x28 (by decide)]
  · rw [h6.get .x5 (by decide),e5,h4.get .x9 (by decide),h3.get .x9 (by decide),
      h2.get .x9 (by decide),h1.get .x9 (by decide),h0.get .x9 (by decide)]
  · rw [e6,h5.get .x28 (by decide),h4.get .x28 (by decide),h3.get .x28 (by decide),
      h2.get .x28 (by decide),h1.get .x28 (by decide),h0.get .x28 (by decide)]

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedHashCall.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Sign.Cached (hashArgs)
open VG.Impl.MlDsa.AArch64.Call (callAt)

/-- Caller rule for the measured argument moves, including the nonce in x9. -/
theorem hashCall_ok {p : Params} {S : Nat} (hS : S<2^64)
    {n : String} {c : Prog isa} {k : Contract isa} (C : CalleeOk S c k)
    {s : State} {rd wr : List Region}
    (hpre : ∀ s1, Args (hashArgs p) s s1 → k.pre (s1.callEntry.withRegions rd wr))
    (hc : Covers (rd++wr) (s.rd++s.wr)) (hw : Covers wr s.wr) :
    WP isa (callAt n c (hashArgs p)) s fun s' => Post S s s' wr ∧
      ∃ s1, Args (hashArgs p) s s1 ∧
        k.post (s1.callEntry.withRegions rd wr) (s'.withRegions rd wr) := by
  refine WP.seq (WP.mono (hashGlue_ok p s) fun s1 h1 => ?_)
  have k1 := h1.2
  refine WP.callFV C.correct (hpre s1 h1) (by rw [k1.rd,k1.wr]; exact hc)
    (by rw [k1.wr]; exact hw)
    (fun s' hrd hwr hsp hf hcs hvcs hpost => ?_) (by have := C.fd; omega)
  refine ⟨⟨hrd.trans k1.rd,hwr.trans k1.wr,hsp.trans k1.sp,
    fun r hr h30 => by rw [hcs r hr h30,k1.gpr r (argRegs_pres r hr)],?_,
    fun r hr => (hvcs r hr).trans (k1.vcs r hr)⟩,s1,h1,hpost⟩
  rw [h1.1.2,k1.sp] at hf
  exact Frame.below_mono hf C.fd hS

theorem hash_cov {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87)
    {S : Nat} {s : State} (L : Lay S (sgR p) (sgW p) s) :
    Covers (hashReads p s ++ hashWrites p s) (s.rd++s.wr) ∧
    Covers (hashWrites p s) s.wr := by
  have hr : Covers (hashReads p s) (s.rd++s.wr) := by
    apply Covers.cons (L.cR (p:=(.x26,0)) (l:=64) (by rcases hp with rfl|rfl <;> decide))
    apply Covers.cons (L.cR (p:=Impl.MlDsa.AArch64.Call.sc Impl.MlDsa.AArch64.Sign.oW1)
      (l:=p.k*w1Len p) (by rcases hp with rfl|rfl <;> decide))
    exact L.cR (by rcases hp with rfl|rfl <;> decide)
  have hw : Covers (hashWrites p s) s.wr := by
    apply Covers.cons (L.cW (p:=Impl.MlDsa.AArch64.Call.sc Impl.MlDsa.AArch64.Sign.oCT)
      (l:=cLen p) (by rcases hp with rfl|rfl <;> decide))
    apply Covers.cons (L.cW (p:=Impl.MlDsa.AArch64.Sign.t1P) (l:=2048)
      (by rcases hp with rfl|rfl <;> decide))
    exact L.cW (by rcases hp with rfl|rfl <;> decide)
  exact ⟨Covers.append_left hr (Covers.right hw),hw⟩

theorem hashReady_ok {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87)
    {S : Nat} (hS : S<2^64) {s : State} (L : Lay S (sgR p) (sgW p) s) :
    WP isa (callAt (if p.ℓ=5 then "vg_mldsa_commit_tail65" else "vg_mldsa_commit_tail87")
      (Impl.MlDsa.AArch64.Sign.CommitTail.code (p.k*w1Len p) (cLen p)) (hashArgs p)) s
      (fun s' => Post S s s' (hashWrites p s) ∧
        ∃ s1, Args (hashArgs p) s s1 ∧
          (commitTailContract abi (p.k*w1Len p) (cLen p) S).post
            (s1.callEntry.withRegions (hashReads p s) (hashWrites p s))
            (s'.withRegions (hashReads p s) (hashWrites p s))) := by
  have C : CalleeOk S (Impl.MlDsa.AArch64.Sign.CommitTail.code (p.k*w1Len p) (cLen p))
      (commitTailContract abi (p.k*w1Len p) (cLen p) S) := by
    rcases hp with rfl|rfl
    · exact CommitTail.callee65 hS
    · exact CommitTail.callee87 hS
  exact hashCall_ok hS C (fun _ h1 => hash_pre hp L h1)
    (hash_cov hp L).1 (hash_cov hp L).2

end VG.Proof.MlDsa.AArch64.Sign.Cached

end
