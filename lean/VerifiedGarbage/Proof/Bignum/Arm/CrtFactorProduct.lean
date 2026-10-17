module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductStart
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Exact factor multiplication, including buffer initialization -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem crt_factorProduct_ok (s : State) {base : BitVec 32} {size o a b cp cq w : Nat} {coefficient : Bool}
    (h : CrtProductInput base size o a b cp cq w s coefficient) :
    WP isa (factorProduct coefficient) s fun t =>
      val32 t.mem (State.addr base) o (2 * w + 2 * w + 2) =
        val32 s.mem (State.addr base) a (2 * w) * val32 s.mem (State.addr base) b (2 * w) ∧
      Outs (State.addr base) [(128, 20), (o, 4 * (2 * w + 2 * w + 2))] s.mem t.mem ∧
      t.gpr .r0 = base ∧ Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have nowrap := h.workspace.nowrap
  have aFits := h.aFits
  have bFits := h.bFits
  have aHeader := h.aHeader
  have bHeader := h.bHeader
  rw [factorProduct, WP.seq_iff]
  refine WP.mono (crt_productClear_ready s h) ?_
  rintro u ⟨inputU, zeroU, outsideU, frameU, restU⟩
  have aU := outsideU.val32 (d := a) (k := 2 * w) h.separateA.symm (by omega)
  have bU := outsideU.val32 (d := b) (k := 2 * w) h.separateB.symm (by omega)
  rw [WP.seq_iff]
  refine WP.mono (crt_productArgs_ready u inputU zeroU) ?_
  rintro v ⟨start, outsideV, frameV, restV⟩
  have aV := outsideV.val32 (d := a) (k := 2 * w) (by omega) (by omega)
  have bV := outsideV.val32 (d := b) (k := 2 * w) (by omega) (by omega)
  have initial := start.initial
  have p := initial.aPtr
  have out := initial.oPtr
  have count := initial.count
  have zero := initial.value
  simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, val32, Nat.zero_mul] at p out count zero
  refine WP.mono (wideProduct_ok v start.context initial.ptr p initial.bPtr out count initial.width zero) ?_
  rintro t ⟨value, outsideT, ptrT, frameT, restT⟩
  rw [aV, bV, aU, bU] at value
  have widened : Outs (State.addr base) [(128, 20), (o, 4 * (2 * w + 2 * w + 2))] v.mem t.mem := by
    intro x hx
    apply outsideT x
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have hfirst := hx (128, 20) (by simp)
      omega
    · exact hx _ (by simp)
  exact ⟨value, (Outs.of_outside outsideU (by simp)).trans ((Outs.of_outside outsideV (by simp)).trans widened),
    ptrT, frameU.trans (frameV.trans frameT), restU.trans ((restV.mono (by simp [roundClobbers])).trans restT)⟩

end VG.Proof.Bignum.Arm
