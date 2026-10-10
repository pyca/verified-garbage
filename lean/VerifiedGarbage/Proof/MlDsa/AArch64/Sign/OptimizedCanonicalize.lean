import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.LazyInv
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedOutput
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CanonicalizeCallTiming

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.AArch64.Optimized

/-- Accepted norm bounds supply the strictly centered conversion precondition. -/
theorem centered_of_signed {m : Mem} {p : Addr} {f : Poly} {lo hi : Int}
    (h : SignedPolyIs m p f lo hi) (hl : -(q:Int)<lo) (hh : hi<(q:Int)) :
    CenteredReduced m p := by
  intro i hn
  have := h.bound i hn
  omega

theorem value_of_signed {m : Mem} {p : Addr} {f : Poly} {lo hi : Int}
    (h : SignedPolyIs m p f lo hi) : signedPolyAt m p=f := by
  apply Vector.ext
  intro i hi
  simp only [signedPolyAt,Vector.getElem_ofFn]
  simpa only [getElem!_pos f i hi] using h.value i hi

/-- Convert an accepted signed polynomial in its existing writable slot;
all surrounding signer state is retained by the call frame. -/
theorem canonicalizeAt_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {p : Ptr} {f : Poly} {lo hi : Int}
    (hr : inB (rbs++wbs) p 1024=true) (hw : inB wbs p 1024=true)
    (hf : SignedPolyIs s.mem (pa s p) f lo hi) (hl : -(q:Int)<lo) (hh : hi<(q:Int)) :
    WP isa (callAt "vg_mldsa_canonicalize_signed"
      VG.Impl.MlDsa.AArch64.Optimized.Response.canonicalize (Response.canonicalizeArgs p)) s fun t =>
      PPostB S s t [(p,1024)] ∧ t.gpr .x24=s.gpr .x24 ∧ PolyIs t.mem (pa s p) f := by
  refine WP.mono (Response.canonicalizeAt_ok L.s64 (ptr_ok (L.ptrBs hr)) (L.nwp hr)
    (centered_of_signed hf hl hh) (L.cR hr) (L.cW hw)) fun t ⟨hp,hv⟩ => ?_
  exact ⟨hp.b,hp.cs .x24 (by decide) (by decide),by simpa only [value_of_signed hf] using hv⟩

open VG.Impl.MlDsa.AArch64.Sign

def canonicalizeZChk (p : Params) (r : Nat) : Bool :=
  inB (sgR p++sgW p) (yP p r) 1024 && inB (sgW p) (yP p r) 1024 &&
  stChk p [(yP p r,1024)]

theorem canonicalizeZChk_ok {p : Params} (hp : Ok3 p) :
    ∀r<p.ℓ,canonicalizeZChk p r=true := by
  rcases hp with rfl | rfl | rfl <;> decide +kernel

theorem canonicalizeZ_rooted {p : Params} {S : Nat} {σ s : State} {r : Nat} {f : Poly}
    {lo hi : Int} (hc : canonicalizeZChk p r=true) (hs : RootedSt p S σ s)
    (hf : SignedPolyIs s.mem (pa s (yP p r)) f lo hi)
    (hl : -(q:Int)<lo) (hh : hi<(q:Int)) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.canonicalizeZ p r) s fun t =>
      RootedSt p S σ t ∧ t.gpr .x24=s.gpr .x24 ∧ PolyIs t.mem (pa t (yP p r)) f := by
  simp only [canonicalizeZChk,Bool.and_eq_true] at hc
  obtain ⟨⟨hr,hw⟩,hst⟩ := hc
  refine WP.mono_syms (canonicalizeAt_layout hs.1.lay hr hw hf hl hh) fun t ⟨hp,h24,hv⟩ hy => ?_
  refine ⟨hs.step hp hy hst (by simpa using hw),h24,?_⟩
  rw [hp.pa (hs.1.lay.ptrBs hr)]
  exact hv

end VG.Proof.MlDsa.AArch64.Sign
