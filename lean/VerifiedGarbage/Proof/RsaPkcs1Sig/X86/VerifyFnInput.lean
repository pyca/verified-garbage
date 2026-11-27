module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyContext
public import VerifiedGarbage.Proof.Dsa.X86.RandomContext
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyRegions
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyPublicCall
import VerifiedGarbage.Proof.Dsa.X86.RandomSignCorrect
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Weierstrass.PointContract

/-! ### `RsaPkcs1Sig.X86.VerifyNoSp`, which the modules that import this one used -/

section

/-! # Verification uses its two stack frames without changing their pointers -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Verify

theorem body_noSp (v : PublicImpl) : NoSp (body v.name v.code) := by
  unfold body
  exact .seq' (.of_all (by decide +kernel)) (.ite' (.of_all (by decide +kernel))
    (.seq' (.of_all (by decide +kernel)) (.seq' (.call' v.noSp) (.of_all (by decide +kernel)))))

theorem allocation_noSp (v : PublicImpl) :
    NoSp (.frame (.alloc frameBytes) (body v.name v.code) (.free frameBytes)) := by
  intro i hi
  simp only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | hi) | rfl
  · rfl
  · exact body_noSp v i hi
  · rfl

theorem inner_noSp (v : PublicImpl) :
    NoSp (.seq (.frame (.alloc frameBytes) (body v.name v.code) (.free frameBytes))
      (.block VG.Impl.RsaPkcs1Sig.X86.Sign.restore)) :=
  .seq' (allocation_noSp v) (.of_all (by decide +kernel))

end VG.Proof.RsaPkcs1Sig.X86.Ver

end

end

/-! # Entry state and preserved saved-register words for checked private RSA -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Proof.Rsa.X86.PrivChecked VG.Impl.RsaPkcs1Sig.X86.Verify VG.Proof.Bignum.X86
open VG.Proof.Dsa.X86 (allocated freed allocated_esp freed_esp)

def savedRegisters : List Reg := [.ebx, .ebp, .esi, .edi]
def entered (s : State) : State := allocated VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes (pushed savedRegisters s)

structure FnInput (g : Geometry) (bs : Fin 5 → List Byte) (s : State) : Prop where
  stackFit : verifyStack ≤ (s.gpr .esp).toNat
  context : Context g bs (entered s)
  returnSeparate : ∀ r ∈ bodyWrites g, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r

theorem FnInput.savedSp {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : FnInput g bs s) :
    (pushed savedRegisters s).gpr .esp = g.stack + BitVec.ofNat 32 VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes := by
  rw [← h.context.sp]
  exact (BitVec.sub_add_cancel _ _).symm

/-- The frame reserved below the saved registers is `innerRegion`. -/
theorem FnInput.innerBelow {g : Geometry} {bs : Fin 5 → List Byte} {s : State} (h : FnInput g bs s) :
    below ((pushed savedRegisters s).gpr .esp) VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes = g.innerRegion := by
  show (⟨((pushed savedRegisters s).gpr .esp - BitVec.ofNat 32 VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes).setWidth 64, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes⟩ : Region) =
    ⟨byteAddr g.stack, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes⟩
  rw [← allocated_esp, show (allocated VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes (pushed savedRegisters s)).gpr .esp = g.stack from h.context.sp]
  rfl

/-- The saved registers' words are `savedRegion`. -/
theorem FnInput.savedBelow {g : Geometry} {bs : Fin 5 → List Byte} {s : State} (h : FnInput g bs s) :
    below (s.gpr .esp) (4 * savedRegisters.length) = g.savedRegion := by
  show (⟨(s.gpr .esp - BitVec.ofNat 32 (4 * savedRegisters.length)).setWidth 64, 4 * savedRegisters.length⟩ :
    Region) = ⟨byteAddr g.stack + BitVec.ofNat 64 VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes, 16⟩
  rw [← pushed_esp, h.savedSp]
  exact congrArg (fun a => Region.mk a 16) (h.context.valid.offsetAddr (by decide))

theorem savedRegion_separate {g : Geometry} (h : g.Valid) :
    ∀ r ∈ bodyWrites g, g.savedRegion.Disjoint r := by
  intro r hr
  simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.innerSaved.symm
  · unfold Geometry.savedRegion Geometry.calleeRegion VG.X86.below
    rw [h.stackBase, Offset.add_add]
    exact Offset.disjoint_base _ (by decide : 100 ≤ 100 + VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes)
      (by decide : 100 + VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 16 ≤ 2 ^ 64)
  · exact h.stackWorkspace.sub_left h.savedSub

theorem FnInput.savedWord {g : Geometry} {bs : Fin 5 → List Byte} {s t : State}
    (h : FnInput g bs s) (frame : Frame (bodyWrites g) (entered s).mem t.mem)
    (i : Nat) (hi : i < 4) :
    t.mem.readW (((pushed savedRegisters s).gpr .esp + BitVec.ofNat 32 (4 * i)).setWidth 64) 32 =
      s.gpr (savedRegisters[3 - i]'(by simp only [savedRegisters, List.length_cons, List.length_nil]; omega_using [])) := by
  have initial := pushed_word (s := s) (rs := savedRegisters) (by decide)
    (by have := h.stackFit; change 16 ≤ _; unfold verifyStack at this; omega_using [this]) hi
  have address : ((pushed savedRegisters s).gpr .esp + BitVec.ofNat 32 (4 * i)).setWidth 64 =
      g.savedRegion.base + BitVec.ofNat 64 (4 * i) := by
    rw [h.savedSp, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    change byteAddr (g.stack + BitVec.ofNat 32 (VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 4 * i)) = _
    rw [h.context.valid.offsetAddr (by unfold VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes; omega_using [hi])]
    exact (Offset.add_add _ _ _).symm
  rw [address] at initial ⊢
  exact (frame.readW (r := g.savedRegion)
    (Offset.contains_base _ (by omega_using [hi] : 4 * i + 32 / 8 ≤ 16) (by omega_using [hi]))
    (savedRegion_separate h.context.valid) (by decide)).trans initial
end VG.Proof.RsaPkcs1Sig.X86.Ver
