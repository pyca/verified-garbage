module
public import VerifiedGarbage.Impl.Bignum.AArch64.SquareCall
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Impl.Bignum.AArch64
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcMont
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Impl.Bignum.AArch64
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

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
