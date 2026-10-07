import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderFrame
import VerifiedGarbage.Proof.Bignum.X86_64.Mont

/-! Saving and restoring header words uses only the public scratch layout. -/
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

end VG.Proof.Bignum.X86_64.AdxHeader
