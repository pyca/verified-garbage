module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Top1
import VerifiedGarbage.Proof.Framework.Omega
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A candidate on ARMv7: the body's start (`entry_ok`)

After the push, with the regions `xRegs`, the entry: the start `In` of the
body. The frame and the round's frame below it are the 112 bytes below the
caller's stack pointer (`cF`), at offsets of `cF`'s base (`fB`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

/-- The state the entry runs from. -/
abbrev sx (s : State) : State := (pcPushed s).withRegions s.rd (xRegs s)

/-- `cF`'s base. -/
abbrev fB (s : State) : Addr := State.addr s.sp - 112#64

section
variable {s t : State}

theorem CIn.spP (h : CIn s) : State.addr (mkP s).sp = fB s + BitVec.ofNat 64 56 := by
  show State.addr (s.sp - BitVec.ofNat 32 56) = _
  rw [FrameStack.addr_sub' (by have := h.spLo; omega), Offset.sub_ofNat_eq _ (show 56 ≤ 112 by decide)]

theorem spA_eq (s : State) : stackArgAddr s 0 = fB s + BitVec.ofNat 64 112 := by
  rw [show fB s = State.addr s.sp - BitVec.ofNat 64 112 from rfl, BitVec.sub_add_cancel]
  simp [stackArgAddr]

theorem CIn.argAddr (h : CIn s) {i : Nat} (hi : i < 7) :
    off (State.addr (mkP s).sp) (56 + 4 * i) = stackArgAddr s i := by
  have := h.spLo; have := h.spHi
  show off (State.addr (s.sp - BitVec.ofNat 32 56)) (56 + 4 * i) = _
  simp only [stackArgAddr, off]
  rw [FrameStack.addr_sub' (by omega), addr_add (by omega), ← Offset.add_add, BitVec.sub_add_cancel]

theorem CIn.frSub (h : CIn s) : Region.Sub (mkP s).rFr (cF s) := by
  show Region.Sub ⟨State.addr (mkP s).sp, 56⟩ ⟨fB s, 112⟩
  rw [h.spP]; exact Offset.sub_base _ (by decide)

theorem CIn.rcSub (h : CIn s) : Region.Sub (mkP s).rC (cF s) := by
  have := h.spLo
  show Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 56), 56⟩ ⟨fB s, 112⟩
  rw [BitVec.sub_sub, ← BitVec.ofNat_add, FrameStack.addr_sub' (by omega)]
  simpa using Offset.sub_base (fB s) (d := 0) (n := 56) (k := 112) (by decide)

theorem CIn.disjF (h : CIn s) {r : Region} (h1 : r.Disjoint (cF s)) (h2 : r.Disjoint (cA s)) :
    r.Disjoint (mkP s).rF := by
  show r.Disjoint ⟨State.addr (mkP s).sp, 84⟩
  rw [h.spP]
  intro x hx hc
  have e1 := (Offset.lt_iff x (fB s) (d := 56) (n := 84) (by decide)).mp (by simp only [Region.Contains] at hc; omega)
  by_cases hlt : (x - fB s).toNat < 112
  · exact h1 x hx (by show (x - fB s).toNat + 1 ≤ 112; omega)
  · refine h2 x hx ?_
    simp only [Region.Contains]
    rw [spA_eq s]
    have := (Offset.lt_iff x (fB s) (d := 112) (n := 28) (by decide)).mpr ⟨by omega, by omega⟩
    omega

/-- Memory after the push and the entry: changed only in the frames. -/
theorem CIn.tFrame (h : CIn s) (mem : t.mem = (pcPushed s).mem.writeW (off (State.addr (mkP s).sp) 48) (s.gpr .r0)) :
    Frame [cF s] s.mem t.mem := by
  have f := FrameStack.pushed_frameA (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (s := s) (by have := h.spLo; simp only [List.length_cons, List.length_nil]; omega)
  have e : FrameStack.belowA s.sp (4 * 14) = (mkP s).rFr := rfl
  rw [show [Reg.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr].length = 14 from rfl, e] at f
  have w : Frame [(mkP s).rFr] (pcPushed s).mem t.mem := by
    rw [mem]
    refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
    show (⟨State.addr (mkP s).sp, 56⟩ : Region).Contains (State.addr (mkP s).sp + BitVec.ofNat 64 48) (32 / 8)
    exact Offset.contains_base _ (by decide) (by decide)
  have sub : ∀ r ∈ [(mkP s).rFr], ∃ r' ∈ [cF s], Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, h.frSub⟩
  exact (f.sub sub).trans (w.sub sub)

theorem CIn.bytesT (h : CIn s) (mem : t.mem = (pcPushed s).mem.writeW (off (State.addr (mkP s).sp) 48) (s.gpr .r0))
    {R : Region} (hR : (cF s).Disjoint R) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len :=
  VG.Proof.Rsa.Arm.CrtValues.bytes_frame (h.tFrame mem) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hR.symm) hl

end

end VG.Proof.RsaKeyGen.Arm.Cand
