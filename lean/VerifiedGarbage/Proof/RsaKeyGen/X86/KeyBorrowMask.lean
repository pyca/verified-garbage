module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.Mont.X86.Instr

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
    (by unfold kFlag VG.Impl.Rsa.X86.Keys.hdr at *; omega)) fun w W => ?_
  have K : Keeps [.eax] s w := (U.keeps.trans V.keeps).trans W.keeps
  have hw := h.rest K
  have memory : w.mem = s.mem := W.mem.trans (V.mem.trans U.mem)
  have value : w.gpr .eax = ((1 : BitVec 32) - s.gpr .ebx) &&& s.mem.readW (off B kFlag) 32 := by
    rw [W.gpr, V.gpr, U.gpr, U.other _ (by decide), V.mem, U.mem]
    rfl
  refine wp_storeS (hw.workspace.ea (by unfold kOk VG.Impl.Rsa.X86.Keys.hdr at *; omega))
    (hw.workspace.write (by unfold kOk VG.Impl.Rsa.X86.Keys.hdr at *; omega))
    fun t T => WP.block_nil ?_
  refine ⟨hw.rest (T.keeps []), ?_, ?_, K.trans (T.keeps _)⟩
  · rw [T.mem, memory]
    exact Keep.of_slot (writeW32_outside _ _ _ (by decide)) (by simp)
  · unfold slot
    rw [T.mem, memory, w32_write_self, value, borrow_mask _ _ borrow flag]

end VG.Proof.RsaKeyGen.X86.Key
