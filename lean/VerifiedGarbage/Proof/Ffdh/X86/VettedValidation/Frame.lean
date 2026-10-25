module

public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Geometry
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.CallLay

/-! Prefix writes stay in the original scratch buffer and the balanced four-byte symbol frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Bignum.X86

def writes (s : State) : List Region := [scratch s, below (s.gpr .esp) 4]

theorem symbol_sub {s : State} (h : contract.pre s) :
    Region.Sub (below (s.gpr .esp) 4) ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := by
  have low := stack_low h
  unfold below
  rw [VG.X86.Taint.sub_setWidth (by omega)]
  exact Offset.sub_below _ (by decide) (by decide)

theorem args_separate {s : State} (h : contract.pre s) :
    ∀ r ∈ writes s, (⟨argAddr s 0, 20⟩ : Region).Disjoint r := by
  intro r hr
  simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (geometry h).scratchArgs.symm
  · have g := geometry h
    have pointer : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
      addr_eq (by have := stack_bound h; omega)
    rw [pointer, below, VG.X86.Taint.sub_setWidth (by have := stack_low h; omega)]
    exact (Offset.disjoint_below_above _ (by decide)).symm

theorem domain_separate {s : State} (h : contract.pre s) :
    ∀ r ∈ writes s, (⟨byteAddr (arg s 0), (arg s 1).toNat⟩ : Region).Disjoint r := by
  intro r hr
  simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (geometry h).domScratch
  · have belowDom : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint
        ⟨byteAddr (arg s 0), (arg s 1).toNat⟩ := (geometry h).belowDom
    exact (belowDom.sub_left (symbol_sub h)).symm

theorem return_separate {s : State} (h : contract.pre s) :
    ∀ r ∈ writes s, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (geometry h).retScratch
  · rw [below, VG.X86.Taint.sub_setWidth (by have := stack_low h; omega)]
    simpa only [BitVec.add_zero] using
      (Offset.disjoint_below_above ((s.gpr .esp).setWidth 64) (m := 4) (a := 0) (l := 4) (by decide)).symm

theorem args_frame {s t : State} (h : contract.pre s) (sp : t.gpr .esp = s.gpr .esp)
    (F : Frame (writes s) s.mem t.mem) : ∀ i < 5, arg t i = arg s i := by
  intro i hi
  unfold arg argAddr
  rw [sp]
  have pointer : (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 =
      argAddr s 0 + BitVec.ofNat 64 (4 * i) := by
    have top := stack_bound h
    change addr (s.gpr .esp) (4 + 4 * i) = _
    rw [addr_eq (x := s.gpr .esp) (k := 4 + 4 * i) (by omega)]
    change _ = addr (s.gpr .esp) 4 + _
    rw [addr_eq (by omega), BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact F.readW (r := ⟨argAddr s 0, 20⟩) (by rw [pointer]; exact Offset.contains_base _ (by omega) (by omega))
    (args_separate h) (by decide)

theorem domain_frame {s t : State} (h : contract.pre s) (args : ∀ i < 5, arg t i = arg s i)
    (F : Frame (writes s) s.mem t.mem) : domain t = domain s := by
  unfold domain
  rw [args 0 (by decide), args 1 (by decide)]
  exact VG.Proof.Rsa.rsa_bytes_frame F (by have := (arg s 1).isLt; omega) (domain_separate h)

end VG.Proof.Ffdh.X86.VettedValidation
