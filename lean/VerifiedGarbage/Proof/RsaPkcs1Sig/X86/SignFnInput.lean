module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignContext
public import VerifiedGarbage.Proof.Dsa.X86.RandomContext

/-! # Entry state and preserved saved-register words for checked private RSA -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Proof.Rsa.X86.PrivChecked VG.Impl.RsaPkcs1Sig.X86.Sign VG.Proof.Bignum.X86
open VG.Proof.Dsa.X86 (allocated freed allocated_esp freed_esp)

def savedRegisters : List Reg := [.ebx, .ebp, .esi, .edi]
def entered (s : State) : State := allocated VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes (pushed savedRegisters s)

structure FnInput (g : Geometry) (bs : Fin 8 → List Byte) (s : State) : Prop where
  stackFit : sigStack ≤ (s.gpr .esp).toNat
  context : Context g bs (entered s)
  returnSeparate : ∀ r ∈ bodyWrites g, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r

theorem FnInput.savedSp {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : FnInput g bs s) :
    (pushed savedRegisters s).gpr .esp = g.stack + BitVec.ofNat 32 VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes := by
  rw [← h.context.sp]
  exact (BitVec.sub_add_cancel _ _).symm

theorem savedRegion_separate {g : Geometry} (h : g.Valid) :
    ∀ r ∈ bodyWrites g, g.savedRegion.Disjoint r := by
  intro r hr
  simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.innerSaved.symm
  · unfold Geometry.savedRegion Geometry.calleeRegion VG.X86.below
    rw [h.stackBase, Offset.add_add]
    exact Offset.disjoint_base _ (by decide : calleeBytes ≤ calleeBytes + VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes)
      (by decide : calleeBytes + VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 16 ≤ 2 ^ 64)
  · exact h.stackOutput.sub_left h.savedSub
  · exact h.stackWorkspace.sub_left h.savedSub

theorem FnInput.savedWord {g : Geometry} {bs : Fin 8 → List Byte} {s t : State}
    (h : FnInput g bs s) (frame : Frame (bodyWrites g) (entered s).mem t.mem)
    (i : Nat) (hi : i < 4) :
    t.mem.readW (((pushed savedRegisters s).gpr .esp + BitVec.ofNat 32 (4 * i)).setWidth 64) 32 =
      s.gpr (savedRegisters[3 - i]'(by simp only [savedRegisters, List.length_cons, List.length_nil]; omega)) := by
  have initial := pushed_word (s := s) (rs := savedRegisters) (by decide)
    (by have := h.stackFit; change 16 ≤ _; unfold sigStack at this; omega) hi
  have address : ((pushed savedRegisters s).gpr .esp + BitVec.ofNat 32 (4 * i)).setWidth 64 =
      g.savedRegion.base + BitVec.ofNat 64 (4 * i) := by
    rw [h.savedSp, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    change byteAddr (g.stack + BitVec.ofNat 32 (VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 4 * i)) = _
    rw [h.context.valid.offsetAddr (by unfold VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes; omega)]
    exact (Offset.add_add _ _ _).symm
  rw [address] at initial ⊢
  exact (frame.readW (r := g.savedRegion)
    (Offset.contains_base _ (by omega : 4 * i + 32 / 8 ≤ 16) (by omega))
    (savedRegion_separate h.context.valid) (by decide)).trans initial
end VG.Proof.RsaPkcs1Sig.X86.Sgn
