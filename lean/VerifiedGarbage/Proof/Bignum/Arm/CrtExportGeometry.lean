module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtOutputArgs
public import VerifiedGarbage.Proof.Bignum.Arm.ExportBufferMasked
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Export the wide reconstruction using the original output buffer and acceptance bit -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont

theorem CrtShared.product_address {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) :
    State.addr (crtProduct g.base g.words) = off (State.addr g.base) (productOffset g.words) ∧
    (crtProduct g.base g.words).toNat = g.base.toNat + productOffset g.words := by
  have size := h.buffers.storageFits
  have nowrap := h.buffers.workspace.nowrap
  have fit : g.base.toNat + productOffset g.words < 2 ^ 32 := by
    simp only [totalBytes, narrowOffset, modulusOffset, compareOffset, productBytes, productWords] at size
    omega
  refine ⟨addr_add (by omega), ?_⟩
  simp only [crtProduct, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : productOffset g.words < 2 ^ 32), Nat.mod_eq_of_lt fit]

theorem CrtShared.product_read {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) :
    (s.mem.read (State.addr (crtProduct g.base g.words)) (4 * (4 * g.words + 2))).toNat =
      val32 s.mem (State.addr g.base) (productOffset g.words) (4 * g.words + 2) := by
  rw [h.product_address.1, read_eq_val32]

theorem CrtShared.export_input {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {accepted : Bool}
    (h : CrtShared g bs s) (source : s.gpr .r1 = crtProduct g.base g.words)
    (output : s.gpr .r4 = g.output) (count : s.gpr .r6 = BitVec.ofNat 32 g.length)
    (flag : s.mem.readW (off (State.addr s.sp) 48) 32 = BitVec.ofNat 32 accepted.toNat)
    (valueFits : accepted = true → val32 s.mem (State.addr g.base) (productOffset g.words) (4 * g.words + 2) < 2 ^ (8 * g.length)) :
    ExportBufferInput (crtProduct g.base g.words) g.output (4 * (4 * g.words + 2)) g.length accepted s := by
  have width := (crt_width_valid h.buffers.lengthValid).2.2
  have length := h.buffers.lengthValid
  have size := h.buffers.storageFits
  have nowrap := h.buffers.workspace.nowrap
  have productFit : productOffset g.words + g.length ≤ g.size := by
    simp only [totalBytes, narrowOffset, modulusOffset, compareOffset, productBytes, productWords] at size
    change g.length ≤ 8 * g.words at width
    omega
  have sub : Region.Sub ⟨State.addr (crtProduct g.base g.words), g.length⟩ ⟨State.addr g.base, g.size⟩ := by
    rw [h.product_address.1]; exact Offset.sub_base _ productFit
  refine ⟨by have := length.1; omega, by change g.length ≤ 8 * g.words at width; omega,
    by rw [h.product_address.2]; omega, h.buffers.outputFits, by have := length.2; omega,
    ?_, h.buffers.write, h.buffers.outputSeparate.sub_left sub, source, output, count,
    ?_, by have := h.stack.nowrap; omega, h.stack.read (by decide),
    h.buffers.outputStack.symm.sub_left (Offset.sub_base _ (by decide)), flag⟩
  · rw [h.product_address.1]
    exact ⟨_, List.mem_append_right _ h.buffers.workspace.writable, Offset.contains_base _ productFit (by omega)⟩
  · rw [h.product_read]; exact valueFits

end VG.Proof.Bignum.Arm
