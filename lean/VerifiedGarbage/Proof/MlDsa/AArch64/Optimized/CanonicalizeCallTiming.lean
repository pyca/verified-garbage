import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CanonicalizeVerified

/-! ## From `CanonicalizeCall.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.Response (canonicalize)

abbrev canonicalizeArgs (f : Ptr) : List (Reg × Arg) := [(.x0,.ptr f)]

theorem canonicalize_callee (S : Nat) : CalleeOk S canonicalize (canonicalizeContract abi) := by
  refine ⟨canonicalize_verified.1,canonicalize_verified.2.1,?_⟩
  change 0≤S
  exact Nat.zero_le _

theorem canonicalizeAt_pre {s s1 : State} {f : Ptr}
    (hfit : (pa s f).toNat+1024≤2^64) (hf : CenteredReduced s.mem (pa s f))
    (h1 : Args (canonicalizeArgs f) s s1) :
    (canonicalizeContract abi).pre (s1.callEntry.withRegions [] [⟨pa s f,1024⟩]) := by
  sig_pre [canonicalizeContract,canonicalizeSig,abi,argRegs]
  rw [Args.r0 h1,Args.mem h1]
  simp only [Arg.val]
  sig_and_intros
  all_goals first | rfl | exact hf | exact hfit | decide

theorem canonicalizeAt_ok {S : Nat} (hS : S<2^64) {nm : String} {s : State} {f : Ptr}
    (hfok : (Arg.ptr f).Ok) (hfit : (pa s f).toNat+1024≤2^64)
    (hf : CenteredReduced s.mem (pa s f))
    (hc : Covers ([]++[⟨pa s f,1024⟩]) (s.rd++s.wr)) (hw : Covers [⟨pa s f,1024⟩] s.wr) :
    WP isa (callAt nm canonicalize (canonicalizeArgs f)) s fun t =>
      Post S s t [⟨pa s f,1024⟩] ∧ PolyIs t.mem (pa s f) (signedPolyAt s.mem (pa s f)) := by
  have hok : ∀a∈canonicalizeArgs f,a.2.Ok ∧ a.1∈argRegs := by
    simp only [canonicalizeArgs,List.mem_singleton]
    intro a ha; subst a; exact ⟨hfok,by change Reg.x0∈argRegs; decide⟩
  refine WP.mono (callAt_ok hS (canonicalize_callee S) hok (by simp)
    (fun s1 h1 => canonicalizeAt_pre hfit hf h1) hc hw) fun t ⟨hp,s1,h1,hpost⟩ => ⟨hp,?_⟩
  sig_post [canonicalizeContract,canonicalizeSig,abi,argRegs] at hpost
  rw [Args.r0 h1,Args.mem h1] at hpost
  exact hpost

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `CanonicalizeCallTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.Response (canonicalize)

structure CanonicalizeCallReady (f : Ptr) (s : State) : Prop where
  fit : (pa s f).toNat+1024≤2^64
  centered : CenteredReduced s.mem (pa s f)
  readable : Covers ([]++[⟨pa s f,1024⟩]) (s.rd++s.wr)
  writable : Covers [⟨pa s f,1024⟩] s.wr

/-- Calling the accepted-output conversion reveals only the buffer address
and stack pointer, never the signs or values of its coefficients. -/
theorem canonicalizeAt_tr {S : Nat} {nm : String} {f : Ptr} (hfok : (Arg.ptr f).Ok)
    {Q : State → State → Prop}
    (hQ : ∀x y,Q x y → CanonicalizeCallReady f x ∧ CanonicalizeCallReady f y ∧
      pa x f=pa y f ∧ x.sp=y.sp) :
    RelCT isa Q (callAt nm canonicalize (canonicalizeArgs f)) fun _ _ => True := by
  have hok : ∀a∈canonicalizeArgs f,a.2.Ok ∧ a.1∈argRegs := by
    simp only [canonicalizeArgs,List.mem_singleton]
    intro a ha; subst a; exact ⟨hfok,by change Reg.x0∈argRegs; decide⟩
  refine callAt_tr (canonicalize_callee S) hok (by simp) fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨rx,ry,ep,esp⟩ := hQ x y hp
  refine ⟨[],[⟨pa x f,1024⟩],canonicalizeAt_pre rx.fit rx.centered h1,?_,?_,
    rx.readable,rx.writable,?_,?_⟩
  · rw [ep]; exact canonicalizeAt_pre ry.fit ry.centered h2
  · sig_pub [canonicalizeContract,canonicalizeSig,abi,argRegs]
    rw [Args.r0 h1,Args.r0 h2,Args.sp h1,Args.sp h2]
    exact ⟨esp,ep⟩
  · rw [ep]; exact ry.readable
  · rw [ep]; exact ry.writable

end VG.Proof.MlDsa.AArch64.Optimized.Response

end
