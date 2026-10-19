module

public import VerifiedGarbage.Proof.Bignum.AArch64.WindowCall
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowCall
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowCall
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Impl.Rsa.AArch64.WindowCall
open VG.Proof.Bignum.AArch64.WindowFive

/-- Calls change neither the working-space relation nor its public width.
This proof does not assume a valid inverse or canonical operands. -/
theorem call_ct {body : Prog isa} {name : String}
    (hc : RelCT isa (Two RawWindowPre) body fun _ _ => True) :
    RelCT isa (Two RawWindowPre) (.call name body) fun s t => s.sp = t.sp := by
  intro s t ts tt s' t' hp es et
  have sp : s'.sp = t'.sp := by
    obtain ⟨_, _, _, hsp⟩ := hp
    rw [(Exec.rdwr es).2.2, (Exec.rdwr et).2.2, hsp]
  have hentry : Two RawWindowPre s.callEntry t.callEntry := by
    obtain ⟨L,hs,ht,hsp⟩ := hp
    have entry : ∀ {a : State}, RawWindowPre L a → RawWindowPre L a.callEntry := by
      rintro a ⟨mi,X,Xc,v,hc,tab,hy,hw,hw',hv,hn⟩
      exact ⟨mi,X,Xc,v,context_callEntry hc,tab,hy,hw,hw',hv,hn⟩
    exact ⟨L,entry hs,entry ht,hsp⟩
  cases es with
  | call hs eb hr =>
    cases et with
    | call ht eb' hr' =>
      rw [call_callEntry, Option.some.injEq] at hs ht
      subst hs ht
      obtain ⟨he, _⟩ := hc _ _ _ _ _ _ hentry eb eb'
      exact ⟨by simpa only [isa, List.map_nil, List.nil_append, List.append_nil] using he, sp⟩

theorem restore_ct :
    RelCT isa (fun s t => s.sp = t.sp) (.block restore) fun _ _ => True := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [])
  · intro s t h
    refine ⟨h, ?_⟩
    intro r hr
    have := RegSet.mem_ofList.mp hr
    contradiction
  · exact (by taint_decide)

theorem wrapper_ct {body : Prog isa} {name : String}
    (hc : RelCT isa (Two RawWindowPre) body fun _ _ => True) :
    RelCT isa (Two RawWindowPre) (VG.Impl.Rsa.AArch64.WindowCall.call name body) fun _ _ => True := by
  unfold VG.Impl.Rsa.AArch64.WindowCall.call
  refine RelCT.seq (two_piece (Ψ := RawWindowPre) [] (fun _ _ _ _ _ _ h => by cases h)
    (by taint_decide) ?_) (RelCT.seq (call_ct hc) restore_ct)
  intro L s ⟨mi,X,Xc,v,hctx,tab,hy,hw,hw',hv,hn⟩
  refine WP.mono (save_ok s) fun t ⟨hm,_,kt⟩ => ?_
  have hf : Frm (off L.B L.o) (crtWinRanges L.wx) s.mem t.mem := hm.symm ▸ Frm.refl _ _ _
  exact ⟨mi,X,Xc,v,hctx.of_win hf kt.wr (kt.gpr .x0 (by simp)),
    hm.symm ▸ tab,hm.symm ▸ hy,hw,hw',hv,hm.symm ▸ hn⟩

/-- The caller's link register is separate from the nested square's link lane. -/
def outlined (W : Window) (name : String)
    (hv : ∀ i ∈ instrs W.code, vdstOf i ≠ some .v7) : Window :=
  ⟨VG.Impl.Rsa.AArch64.WindowCall.call name W.code,call_ok W hv,wrapper_ct W.ct⟩

end VG.Proof.Bignum.AArch64.WindowCall
