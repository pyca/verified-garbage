module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.Mont.X86.Instr

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
  refine wp_subS (readSrc_sc hu.workspace (by omega)) fun v V _ => ?_
  have hv := hu.rest V.keeps
  refine wp_storeS (hv.workspace.ea (by omega)) (hv.workspace.write (by omega)) fun t T => WP.block_nil ?_
  have K : Keeps [.eax] s t := (U.keeps.trans V.keeps).trans (T.keeps _)
  refine ⟨h.rest K, ?_, ?_, K⟩
  · rw [T.mem, V.mem, U.mem]
    exact Keep.of_slot (writeW32_outside _ _ _ (by unfold VG.Impl.Rsa.X86.Keys.hdr at ho; omega)) (by simp)
  · unfold slot
    rw [T.mem, V.mem, U.mem, w32_write_self, V.gpr, U.gpr, U.mem, not_bit _ bit]

end VG.Proof.RsaKeyGen.X86.Key
