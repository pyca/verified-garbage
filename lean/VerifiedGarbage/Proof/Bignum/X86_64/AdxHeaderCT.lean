module

public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderSave
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Impl.Bignum.X86_64.AdxRect8
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderCopy
import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderFrame
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Digit
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Word
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Impl.Bignum.X86_64.AdxRect8
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderCopy
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderFrame
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Digit
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Word
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! Saving and restoring header words uses only the public scratch layout. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxHeader
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

def Pads (L : Ws) (s : State) : Prop :=
  s.gpr .rdi = L.B ∧ s.gpr .r8 = off L.B (slot L.w aAcc) ∧ s.gpr .r9 = off L.B (highPad L.w)

theorem pads_pins : Pins Pads [.rdi,.r8,.r9] := by
  rintro L s t ⟨ds,ls,hs⟩ ⟨dt,lt,ht⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ds.trans dt.symm
  · exact ls.trans lt.symm
  · exact hs.trans ht.symm

theorem bases_fw (L : Ws) (s : State) (h : GoodW L s) :
    WP isa (.block AdxHeader.bases) s (Pads L) := by
  obtain ⟨mi,hg,hZ⟩ := h
  exact WP.mono (bases_ok hg.scr hg.rdi hg.hdr hZ) fun _ ⟨lo,hi,_,kt⟩ =>
    ⟨(kt.gpr (by decide)).trans hg.rdi,lo,hi⟩

theorem save_ct : RelCT isa (Two GoodW) AdxHeader.save (fun _ _ => True) := by
  unfold AdxHeader.save
  exact RelCT.seq (two_piece [.rdi] pins_goodW (by taint_decide) bases_fw)
    (two_taint [.rdi,.r8,.r9] pads_pins (by taint_decide))

theorem restore_ct : RelCT isa (Two GoodW) AdxHeader.restore (fun _ _ => True) := by
  unfold AdxHeader.restore
  exact RelCT.seq (two_piece [.rdi] pins_goodW (by taint_decide) bases_fw)
    (two_taint [.rdi,.r8,.r9] pads_pins (by taint_decide))

theorem clear_ct : RelCT isa (Two GoodW) AdxHeader.clear (fun _ _ => True) := by
  unfold AdxHeader.clear
  exact RelCT.seq (two_piece [.rdi] pins_goodW (by taint_decide) bases_fw)
    (two_taint [.rdi,.r8,.r9] pads_pins (by taint_decide))

end VG.Proof.Bignum.X86_64.AdxHeader
