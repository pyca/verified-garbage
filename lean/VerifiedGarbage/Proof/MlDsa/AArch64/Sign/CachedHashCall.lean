import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedHashGlue
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailCall

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
