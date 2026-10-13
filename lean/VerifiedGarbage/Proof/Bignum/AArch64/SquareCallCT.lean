module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
meta import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section

namespace VG.Proof.Bignum.AArch64.SquareCall
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Impl.Bignum.AArch64.SquareCall

/-- Calls change neither the working-space relation nor its public width.
This proof does not assume a valid inverse or canonical operands. -/
theorem call_ct {body : Prog isa} {name : String}
    (hc : RelCT isa (Two GoodW) body fun _ _ => True) :
    RelCT isa (Two GoodW) (.call name body) fun s t => s.sp = t.sp := by
  intro s t ts tt s' t' hp es et
  have sp : s'.sp = t'.sp := by
    obtain ⟨_, _, _, hsp⟩ := hp
    rw [(Exec.rdwr es).2.2, (Exec.rdwr et).2.2, hsp]
  have hentry : Two GoodW s.callEntry t.callEntry := by
    obtain ⟨L, ⟨mi, hg, hz⟩, ⟨mi', hg', hz'⟩, hsp⟩ := hp
    exact ⟨L, ⟨mi, good_callEntry hg, hz⟩, ⟨mi', good_callEntry hg', hz'⟩, hsp⟩
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
    (hc : RelCT isa (Two GoodW) body fun _ _ => True) :
    RelCT isa (Two GoodW) (VG.Impl.Bignum.AArch64.SquareCall.call name body) fun _ _ => True := by
  unfold VG.Impl.Bignum.AArch64.SquareCall.call
  refine RelCT.seq (two_piece (Ψ := GoodW) [] (fun _ _ _ _ _ _ h => by cases h)
    (by taint_decide) ?_) (RelCT.seq (call_ct hc) restore_ct)
  intro L s ⟨minv, hg, hz⟩
  exact WP.mono (save_ok s) fun t ⟨hm, _, hk⟩ =>
    ⟨minv, ⟨hg.scr.congr hk.wr, (hk.gpr .x0 (by simp)).trans hg.x0, hm ▸ hg.hdr⟩, hz⟩

end VG.Proof.Bignum.AArch64.SquareCall
