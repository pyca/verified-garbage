module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyLcm
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEven
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Form a secret modulus-validity bit from a borrow and parity -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem odd_mask (b x : BitVec 32) (bit : b.toNat ≤ 1) :
    (((1 : BitVec 32) - b) &&& x &&& (1 : BitVec 32)).toNat =
      if b.toNat = 0 then x.toNat % 2 else 0 := by
  rcases VG.Proof.Rsa.KeyBits32.bit_cases bit with hb | hb
  · rw [hb]
    change (((1 : BitVec 32) &&& x) &&& (1 : BitVec 32)).toNat = x.toNat % 2
    rw [BitVec.and_comm (1 : BitVec 32) x, BitVec.and_assoc, BitVec.and_self]
    exact VG.Proof.Rsa.KeyBits32.bv_and_one x
  · rw [hb]
    change ((0#32 &&& x) &&& (1 : BitVec 32)).toNat = 0
    simp only [BitVec.zero_and, BitVec.toNat_zero]

theorem oddFlag_ok {s : State} {B : Addr} {Z n input : Nat}
    (h : Ws s B Z n 32) (hi : input < 32) (bit : (s.gpr .ebx).toNat ≤ 1) :
    WP isa (.block (oddFlag n input)) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [] [kFlag] s.mem t.mem ∧
      slot t.mem B kFlag = (if (s.gpr .ebx).toNat = 0 then num s.mem B n input % 2 else 0) ∧
      Keeps [.eax] s t := by
  have fit := h.arr_fit hi
  have head := h.hdr_le
  unfold oddFlag
  refine wp_movS rfl fun u U _ => wp_subS rfl fun v V _ => ?_
  have hv := (h.rest U.keeps).rest V.keeps
  refine wp_logicS (.inl rfl) (readSrc_sc hv.workspace
    (by change arr n input + 4 ≤ Z; unfold S at fit; omega)) fun w W => ?_
  refine wp_logicS (.inl rfl) rfl fun x X => ?_
  have K : Keeps [.eax] s x := ((U.keeps.trans V.keeps).trans W.keeps).trans X.keeps
  have hx := h.rest K
  have memory : x.mem = s.mem := X.mem.trans (W.mem.trans (V.mem.trans U.mem))
  have value : x.gpr .eax = ((1 : BitVec 32) - s.gpr .ebx) &&&
      s.mem.readW (off B (arr n input)) 32 &&& (1 : BitVec 32) := by
    rw [X.gpr, W.gpr, V.gpr, U.gpr, U.other _ (by decide), V.mem, U.mem]
    rfl
  refine wp_storeS (hx.workspace.ea (by unfold kFlag VG.Impl.Rsa.X86.Keys.hdr at *; omega))
    (hx.workspace.write (by unfold kFlag VG.Impl.Rsa.X86.Keys.hdr at *; omega))
    fun t T => WP.block_nil ?_
  refine ⟨hx.rest (T.keeps []), ?_, ?_, K.trans (T.keeps _)⟩
  · rw [T.mem, memory]
    exact Keep.of_slot (writeW32_outside _ _ _ (by decide)) (by simp)
  · unfold slot
    rw [T.mem, memory, w32_write_self, value, odd_mask _ _ bit, num_parity _ _ h.wpos input]

end VG.Proof.RsaKeyGen.X86.Key
