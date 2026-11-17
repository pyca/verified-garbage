module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.KeyScalar
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Rsa.KeyBits32

/-! ### `RsaKeyGen.X86.KeyDTrivial`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyNotSlot`, which this module and modules that import it used -/

section

/-! # Complement a native header bit -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem not_bit (x : BitVec 32) (bit : x.toNat ≤ 1) :
    ((1 : BitVec 32) - x).toNat = 1 - x.toNat := by
  rcases VG.Proof.Rsa.KeyBits32.bit_cases bit with rfl | rfl <;> decide

theorem notSlot_ok {s : State} {B : Addr} {Z n N out input : Nat} (h : Ws s B Z n N)
    (ho : out + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) (hi : input + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr)
    (bit : slot s.mem B input ≤ 1) :
    WP isa (.block (notSlot out input)) s fun t =>
      Ws t B Z n N ∧ Keep B n [] [out] s.mem t.mem ∧
      slot t.mem B out = 1 - slot s.mem B input ∧ Keeps [.eax] s t := by
  have head := h.hdr_le
  unfold notSlot
  refine wp_movS rfl fun u U _ => ?_
  have hu := h.rest U.keeps
  refine wp_subS (readSrc_sc hu.workspace (by omega_using [hi, head])) fun v V _ => ?_
  have hv := hu.rest V.keeps
  refine wp_storeS (hv.workspace.ea (by omega_using [ho, head])) (hv.workspace.write (by omega_using [ho, head])) fun t T => WP.block_nil ?_
  have K : Keeps [.eax] s t := (U.keeps.trans V.keeps).trans (T.keeps _)
  refine ⟨h.rest K, ?_, ?_, K⟩
  · rw [T.mem, V.mem, U.mem]
    exact Keep.of_slot (writeW32_outside _ _ _ (by unfold VG.Impl.Rsa.X86.Keys.hdr at ho; omega_using [ho])) (by simp)
  · unfold slot
    rw [T.mem, V.mem, U.mem, w32_write_self, V.gpr, U.gpr, U.mem, not_bit _ bit]

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # Handle public exponents zero and one, including degenerate LCMs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem dZero_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa dZero s fun t => Ws t B Z n 32 ∧ Keep B n [] [kOk] s.mem t.mem ∧
      slot t.mem B kOk = 0 ∧ Keeps [.eax] s t := by
  have head := h.hdr_le
  unfold dZero
  refine wp_movS rfl fun u U _ => ?_
  have hu := h.rest U.keeps
  refine wp_storeS (hu.workspace.ea (by unfold kOk hdr at *; omega_using [head]))
    (hu.workspace.write (by unfold kOk hdr at *; omega_using [head])) fun t T => WP.block_nil ?_
  refine ⟨hu.rest (T.keeps []), ?_, ?_, U.keeps.trans (T.keeps _)⟩
  · rw [T.mem, U.mem]
    exact Keep.of_slot (writeW32_outside _ _ _ (by decide)) (by simp)
  · unfold slot
    rw [T.mem, U.mem, w32_write_self, U.gpr]
    rfl

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # Retry clears the export mask and returns the specified status two -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem retry_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa retry s fun t =>
      Ws t B Z n 32 ∧ Keep B n [] [kOk, kStatus] s.mem t.mem ∧
      slot t.mem B kOk = 0 ∧ slot t.mem B kStatus = 2 ∧ Keeps [.eax] s t := by
  change WP isa (.block ([.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc kOk) .eax] ++
    [.mov .eax (.imm 2), .store (VG.Impl.Mont.X86.sc kStatus) .eax])) s _
  refine WP.block_append (WP.mono (dZero_ok h) fun u ⟨hu, Ou, mask, Ku⟩ => ?_)
  refine wp_movS rfl fun v V _ => ?_
  refine WP.mono (store_slot (hu.rest V.keeps) (by decide) .eax)
    fun t ⟨ht, Ot, status, Kt⟩ => ?_
  rw [V.mem] at Ot
  rw [V.gpr] at status
  refine ⟨ht, Ou.join Ot (js := []) (ds := [kOk, kStatus]), ?_, status,
    Ku.trans (V.keeps.trans (Kt.mono (by decide)))⟩
  exact (Ot.slot (by decide) (by decide)).trans mask

end VG.Proof.RsaKeyGen.X86.Key
