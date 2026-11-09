module

public import VerifiedGarbage.Proof.RsaPss.Arm.CtSel
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.RsaPss.Arm.Step
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtSel
meta import VerifiedGarbage.Proof.Mgf1.Basic
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
meta import VerifiedGarbage.Proof.RsaPss.Arm.Step

/-!
# RSASSA-PSS and RSAES-OAEP on ARMv7: facts for MGF1 and the slots

What MGF1's proofs (`Proof/RsaOaep/Arm/Mgf.lean`) need of the slots, of
the counter's bytes and of the hash function (`PssHash.valid`), and the
stack of a streaming function's frame (`below_low`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.MdStream (Md)

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- The hash function as MGF1 takes it has digests of `hLen` bytes. -/
theorem PssHash.valid : Proof.Mgf1.Valid h.G := by
  refine ⟨by rw [h.glen]; exact h.D_pos, fun x => ?_⟩
  rw [h.hash, h.ok.hash, List.length_take, Md.hash, h.md.digest_length, h.glen]
  exact Nat.min_eq_left h.D_le


/-- A slot is in what the body may write. -/
theorem slotW (hg : Geo L scr) {d : Nat} (hd : d + 4 ≤ frameBytes) : ∃ R ∈ L.W, Region.Sub (slotR L d) R :=
  ⟨L.FR, List.mem_cons_self, Offset.sub_base _ (by rw [hg.F]; exact hd)⟩


/-- Two slots apart. -/
theorem slotSep {d e : Nat} (hd : d + 4 ≤ frameBytes) (he : e + 4 ≤ frameBytes) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (slotR L d).Disjoint (slotR L e) :=
  Lay.fr_sep h (by unfold frameBytes at hd; omega) (by unfold frameBytes at he; omega)


/-- A word's bits as a mask. -/
theorem selW (a b : BitVec 32) (c : Prop) [Decidable c] : b ^^^ ((a ^^^ b) &&& maskOf c) = if c then a else b := by
  by_cases hc : c
  · simp only [maskOf, hc, ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm a b, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · simp [maskOf, hc]


/-- The counter's bytes. -/
theorem i2osp4_getD (c j : Nat) (hj : j < 4) :
    (Spec.Rsa.i2osp c 4).getD j 0 = BitVec.ofNat 8 (c / 256 ^ (3 - j)) := by
  simp [Spec.Rsa.i2osp, List.getD_eq_getElem?_getD, hj]


theorem i2osp4_length (c : Nat) : (Spec.Rsa.i2osp c 4).length = 4 := by simp [Spec.Rsa.i2osp]


/-- A slot read after a write of another. -/
theorem slot_ww (m : Mem) {d e : Nat} (v : BitVec 32) (hd : d + 4 ≤ frameBytes) (he : e + 4 ≤ frameBytes)
    (h : d + 4 ≤ e ∨ e + 4 ≤ d) : (m.writeW (L.fr e) v).readW (L.fr d) 32 = m.readW (L.fr d) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by unfold frameBytes at hd; omega) (by unfold frameBytes at he; omega))
    (by decide)


theorem ctrPut_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1])
    (.block ctrPut) hc).isSome = true := ⟨_, by taint_decide⟩


theorem shr0 (c : Nat) : (BitVec.ofNat 32 c).setWidth 8 = BitVec.ofNat 8 (c / 256 ^ 0) := by
  rw [Nat.pow_zero, Nat.div_one]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega


theorem bit_z (p : Prop) [Decidable p] : ((if p then (1 : BitVec 32) else 0) - 0 == 0) = decide (¬ p) := by
  by_cases hp : p <;> simp [hp]


/-- The 16 bytes below the stack pointer, where a streaming function's frame
goes, are in our callees' stack. -/
theorem below_low (hg : Geo L scr) {σ s : State} (hc : Ctx L scr σ s) :
    Region.Sub (Pbkdf2.Stream.Arm.below s) L.LOW := by
  have hC := hg.C16
  have hB := hc.st.ok.B56
  rw [Pbkdf2.Stream.Arm.below, hc.st.sp]
  show Region.Sub ⟨State.addr L.B - BitVec.ofNat 64 16, 16⟩ ⟨State.addr L.B - BitVec.ofNat 64 L.C, L.C⟩
  exact Offset.sub_below _ hC (by omega)

end VG.Proof.RsaPss.Arm
