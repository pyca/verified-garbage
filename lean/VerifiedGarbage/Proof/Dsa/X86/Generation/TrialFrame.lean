module

public import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.MulArgs
import VerifiedGarbage.Proof.Framework.Offset

/-! The trial loop borrows six words in the parent's argument-sized frame. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Impl.Mont.X86

structure TrialFrame (sp : BitVec 32) (s : State) : Prop where
  stack : s.gpr .esp = sp
  fits : sp.toNat + 36 ≤ 2 ^ 32
  writable : (⟨sp.setWidth 64, 36⟩ : Region) ∈ s.wr

def trialSlot (m : Mem) (sp : BitVec 32) (i : Nat) : BitVec 32 :=
  m.readW (sp.setWidth 64 + BitVec.ofNat 64 (4 * i)) 32

theorem TrialFrame.keep {sp : BitVec 32} {s t : State} {rs : List Reg}
    (h : TrialFrame sp s) (K : Keeps rs s t) (stack : .esp ∉ rs) : TrialFrame sp t :=
  ⟨(K.1 .esp stack).trans h.stack, h.fits, K.2.2 ▸ h.writable⟩

theorem TrialFrame.read {sp : BitVec 32} {s : State} (h : TrialFrame sp s) {i : Nat} (hi : i < 9) :
    readSrc s (.mem (at_ .esp (4 * i))) = some (trialSlot s.mem sp i) := by
  obtain ⟨ea, wr⟩ := VG.Proof.Bignum.X86.PublicRt.frame_store
    (congrArg (BitVec.setWidth 64) h.stack) (h.stack ▸ h.fits) h.writable (by omega : 4 * i + 4 ≤ 36)
  show s.load32 (s.ea (at_ .esp (4 * i))) = _
  have rd : InRegions (s.rd ++ s.wr) (sp.setWidth 64 + BitVec.ofNat 64 (4 * i)) 4 := by
    obtain ⟨r, member, contains⟩ := wr
    exact ⟨r, List.mem_append_right _ member, contains⟩
  rw [ea, State.load32, ite_eq_left_iff.mpr fun hn => absurd rd hn]
  rfl

theorem TrialFrame.store {sp : BitVec 32} {s : State} (h : TrialFrame sp s) {i : Nat} (hi : i < 9) (r : Reg) :
    WP isa (.block [.store (at_ .esp (4 * i)) r]) s fun t =>
      TrialFrame sp t ∧ Keeps [] s t ∧
      Frame [⟨sp.setWidth 64, 36⟩] s.mem t.mem ∧
      trialSlot t.mem sp i = s.gpr r ∧
      ∀ j < 9, j ≠ i → trialSlot t.mem sp j = trialSlot s.mem sp j := by
  obtain ⟨ea, wr⟩ := VG.Proof.Bignum.X86.PublicRt.frame_store
    (congrArg (BitVec.setWidth 64) h.stack) (h.stack ▸ h.fits) h.writable (by omega : 4 * i + 4 ≤ 36)
  refine wp_storeS ea wr fun t T => WP.block_nil ?_
  refine ⟨h.keep (T.keeps []) (by simp), T.keeps [], ?_, ?_, ?_⟩
  · rw [T.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega : 4 * i + 4 ≤ 36) (by omega))
  · rw [trialSlot, T.mem]
    exact Mem.readW_writeW_self32 _ _ _
  · intro j hj ne
    rw [trialSlot, T.mem]
    exact VG.Proof.Bignum.X86.PublicRt.frame_other _ _ _ (by omega) (by omega) (by omega)

end VG.Proof.Dsa.X86.Generation
