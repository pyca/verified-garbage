module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyFinal
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.KeySub
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Impl.Rsa.X86.Inverse
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.Rsa.X86.KeyScalar

/-! ### `RsaKeyGen.X86.KeySaveSlot`, which this module and modules that import it used -/

section

/-! # Copy a public-exponent stage's status to a persistent header slot -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot

theorem saveSlot_ok {s : State} {B : Addr} {Z n N a d : Nat} (h : Ws s B Z n N)
    (ha : a + 4 ≤ hdr) (hd : d + 4 ≤ hdr) :
    WP isa (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc a)),
      .store (VG.Impl.Mont.X86.sc d) .eax]) s fun t =>
      Ws t B Z n N ∧ Keep B n [] [d] s.mem t.mem ∧
      slot t.mem B d = slot s.mem B a ∧ Keeps [.eax] s t := by
  have head := h.hdr_le
  refine wp_movS (readSrc_sc h.workspace (by omega_using [ha, head])) fun u U _ => ?_
  refine WP.mono (store_slot (h.rest U.keeps) hd .eax) fun t ⟨ht, Ot, value, Kt⟩ => ?_
  refine ⟨ht, ?_, ?_, U.keeps.trans (Kt.mono (by decide))⟩
  · simpa only [U.mem] using Ot
  · rw [value, U.gpr]

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyBorrowMask`, which this module and modules that import it used -/

section

/-! # Combine a comparison borrow with the private-inverse existence bit -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem borrow_mask (b f : BitVec 32) (bb : b.toNat ≤ 1) (bf : f.toNat ≤ 1) :
    (((1 : BitVec 32) - b) &&& f).toNat = if b.toNat = 0 ∧ f.toNat = 1 then 1 else 0 := by
  rcases VG.Proof.Rsa.KeyBits32.bit_cases bb with rfl | rfl <;>
    rcases VG.Proof.Rsa.KeyBits32.bit_cases bf with rfl | rfl <;> decide

theorem borrowMask_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (borrow : (s.gpr .ebx).toNat ≤ 1) (flag : slot s.mem B kFlag ≤ 1) :
    WP isa (.block borrowMask) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [] [kOk] s.mem t.mem ∧
      slot t.mem B kOk = (if (s.gpr .ebx).toNat = 0 ∧ slot s.mem B kFlag = 1 then 1 else 0) ∧
      Keeps [.eax] s t := by
  have head := h.hdr_le
  unfold borrowMask
  refine wp_movS rfl fun u U _ => wp_subS rfl fun v V _ => ?_
  have hv := (h.rest U.keeps).rest V.keeps
  refine wp_logicS (.inl rfl) (readSrc_sc hv.workspace
    (by unfold kFlag VG.Impl.Rsa.X86.Keys.hdr at *; omega_using [head])) fun w W => ?_
  have K : Keeps [.eax] s w := (U.keeps.trans V.keeps).trans W.keeps
  have hw := h.rest K
  have memory : w.mem = s.mem := W.mem.trans (V.mem.trans U.mem)
  have value : w.gpr .eax = ((1 : BitVec 32) - s.gpr .ebx) &&& s.mem.readW (off B kFlag) 32 := by
    rw [W.gpr, V.gpr, U.gpr, U.other _ (by decide), V.mem, U.mem]
    rfl
  refine wp_storeS (hw.workspace.ea (by unfold kOk VG.Impl.Rsa.X86.Keys.hdr at *; omega_using [head]))
    (hw.workspace.write (by unfold kOk VG.Impl.Rsa.X86.Keys.hdr at *; omega_using [head]))
    fun t T => WP.block_nil ?_
  refine ⟨hw.rest (T.keeps []), ?_, ?_, K.trans (T.keeps _)⟩
  · rw [T.mem, memory]
    exact Keep.of_slot (writeW32_outside _ _ _ (by decide)) (by simp)
  · unfold slot
    rw [T.mem, memory, w32_write_self, value, borrow_mask _ _ borrow flag]

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # Native public-exponent range checks -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem exponentUpper_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa (.block exponentUpper) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [] [kFlag] s.mem t.mem ∧
      slot t.mem B kFlag = (if val32 s.mem B kEv 2 < 2 ^ 33 then 1 else 0) ∧ Keeps [.eax] s t := by
  have head := h.hdr_le
  unfold exponentUpper
  refine wp_movS (readSrc_sc h.workspace (by unfold kEvHi hdr at *; omega_using [head])) fun u U _ => ?_
  refine wp_cmpi fun v V carry _ => ?_
  refine wp_sbb_self carry fun w W => ?_
  refine wp_andi fun a A => ?_
  have K : Keeps [.eax] s a := ((U.keeps.trans (V.keeps _)).trans W.keeps).trans A.keeps
  have ha := h.rest K
  refine wp_storeS (ha.workspace.ea (by unfold kFlag hdr at *; omega_using [head]))
    (ha.workspace.write (by unfold kFlag hdr at *; omega_using [head])) fun t T => WP.block_nil ?_
  have memory : a.mem = s.mem := A.mem.trans (W.mem.trans (V.mem.trans U.mem))
  have value : (a.gpr .eax).toNat = (if w32 s.mem B kEvHi < 2 then 1 else 0) := by
    rw [A.gpr, W.gpr, U.gpr]
    change ((if decide (w32 s.mem B kEvHi < 2) then BitVec.allOnes 32 else 0#32) &&& (1 : BitVec 32)).toNat = _
    simp only [decide_eq_true_eq]
    split <;> rfl
  have upper : w32 s.mem B kEvHi < 2 ↔ val32 s.mem B kEv 2 < 2 ^ 33 := by
    have lo := (s.mem.readW (off B kEv) 32).isLt
    change w32 s.mem B kEv < 2 ^ 32 at lo
    change w32 s.mem B kEvHi < 2 ↔ w32 s.mem B kEv + 2 ^ 32 * w32 s.mem B kEvHi < 2 ^ 33
    omega_using [lo]
  refine ⟨ha.rest (T.keeps []), ?_, ?_, K.trans (T.keeps _)⟩
  · rw [T.mem, memory]
    exact Keep.of_slot (writeW32_outside _ _ _ (by decide)) (by simp)
  · unfold slot
    rw [T.mem, memory, w32_write_self, value]
    simp only [upper]

end VG.Proof.RsaKeyGen.X86.Key
