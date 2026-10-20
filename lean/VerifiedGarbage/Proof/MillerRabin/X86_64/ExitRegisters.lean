module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Teardown
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Stack
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Offset

/-! # All six saved registers and the stack pointer return to their caller -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Impl.MillerRabin.X86_64

theorem exited_registers {s t : State} {writes : List Region}
    (hs : 120 ≤ (s.gpr .rsp).toNat)
    (hd : ∀ r ∈ writes, Region.Disjoint ⟨s.gpr .rsp - 112#64, 112⟩ r)
    (hf : Frame writes (entered s).mem t.mem)
    (hsp : t.gpr .rsp = (entered s).gpr .rsp)
    (hbx : t.gpr .rbx = (entered s).mem.readW ((entered s).gpr .rsp + 104#64) 64)
    (h12 : t.gpr .r12 = (entered s).mem.readW ((entered s).gpr .rsp + 96#64) 64)
    (h13 : t.gpr .r13 = (entered s).mem.readW ((entered s).gpr .rsp + 88#64) 64)
    (h14 : t.gpr .r14 = (entered s).mem.readW ((entered s).gpr .rsp + 80#64) 64)
    (h15 : t.gpr .r15 = (entered s).mem.readW ((entered s).gpr .rsp + 72#64) 64) :
    ∀ r ∈ calleeSaved, (exited t).gpr r = s.gpr r := by
  have hbp : t.mem.readW (t.gpr .rsp) 64 = s.gpr .rbp := by
    rw [hsp, entered_rsp]
    refine Eq.trans ?_ (entered_rbp s hs)
    apply hf.readW (r := ⟨s.gpr .rsp - 112#64, 112⟩)
    · simpa only [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using
        Offset.contains_base (s.gpr .rsp - 112#64) (d := 0) (n := 8) (k := 112) (by decide) (by decide)
    · exact hd
    · decide
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · rw [exited_gpr _ (by decide) (by decide) (by decide), hbx]
    exact entered_saved_at s hs (j := 0) (by decide +kernel)
  · exact (exited_rbp t).trans hbp
  · rw [exited_rsp, hsp, entered_rsp]
    bv_omega
  · rw [exited_gpr _ (by decide) (by decide) (by decide), h12]
    exact entered_saved_at s hs (j := 1) (by decide +kernel)
  · rw [exited_gpr _ (by decide) (by decide) (by decide), h13]
    exact entered_saved_at s hs (j := 2) (by decide +kernel)
  · rw [exited_gpr _ (by decide) (by decide) (by decide), h14]
    exact entered_saved_at s hs (j := 3) (by decide +kernel)
  · rw [exited_gpr _ (by decide) (by decide) (by decide), h15]
    exact entered_saved_at s hs (j := 4) (by decide +kernel)

end VG.Proof.MillerRabin.X86_64
