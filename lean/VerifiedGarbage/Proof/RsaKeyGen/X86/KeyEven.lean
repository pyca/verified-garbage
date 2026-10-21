module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyPrimes
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.Mont.X86.ExponentShift
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The secret selection bit for a common RSA LCM halving -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem num_parity (m : Mem) (B : Addr) {n : Nat} (positive : 0 < n) (j : Nat) :
    num m B n j % 2 = w32 m B (arr n j) % 2 := by
  cases n with
  | zero => omega
  | succ n => exact VG.Proof.Mont.X86.Dynamic.val32_parity m B (arr (n + 1) j) n

theorem even_bit (x y : BitVec 32) :
    (((x ||| y) &&& (1 : BitVec 32)) ^^^ (1 : BitVec 32)).toNat =
      if x.toNat % 2 = 0 ∧ y.toNat % 2 = 0 then 1 else 0 := by
  rw [BitVec.and_or_distrib_right]
  have bx : (x &&& (1 : BitVec 32)).toNat ≤ 1 := by
    rw [VG.Proof.Rsa.KeyBits32.bv_and_one]
    omega
  have by' : (y &&& (1 : BitVec 32)).toNat ≤ 1 := by
    rw [VG.Proof.Rsa.KeyBits32.bv_and_one]
    omega
  rw [VG.Proof.Rsa.KeyBits32.bv_nor_bits bx by',
    VG.Proof.Rsa.KeyBits32.bv_and_one, VG.Proof.Rsa.KeyBits32.bv_and_one]

theorem bothEven_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa (.block (bothEven n)) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [] [kFlag] s.mem t.mem ∧
      slot t.mem B kFlag =
        (if num s.mem B n aU % 2 = 0 ∧ num s.mem B n aV % 2 = 0 then 1 else 0) ∧
      Keeps [.eax] s t := by
  have fu := h.arr_fit (j := aU) (by decide)
  have fv := h.arr_fit (j := aV) (by decide)
  have head := h.hdr_le
  unfold bothEven
  refine wp_movS (readSrc_sc h.workspace (by change arr n aU + 4 ≤ Z; unfold S at fu; omega)) fun u U _ => ?_
  have hu := h.workspace.of_keeps U.keeps (by decide)
  refine wp_orS (readSrc_sc hu (by change arr n aV + 4 ≤ Z; unfold S at fv; omega)) fun v V => ?_
  refine wp_logicS (.inl rfl) rfl fun w W => ?_
  refine wp_logicS (.inr rfl) rfl fun x X => ?_
  have K : Keeps [.eax] s x := ((U.keeps.trans V.keeps).trans W.keeps).trans X.keeps
  have hx := h.rest K
  have mem : x.mem = s.mem := X.mem.trans (W.mem.trans (V.mem.trans U.mem))
  have reg : x.gpr .eax =
      ((s.mem.readW (off B (arr n aU)) 32 ||| s.mem.readW (off B (arr n aV)) 32) &&&
        (1 : BitVec 32)) ^^^ (1 : BitVec 32) := by
    rw [X.gpr, W.gpr, V.gpr, U.gpr, U.mem]
    rfl
  refine wp_storeS (hx.workspace.ea (by unfold kFlag VG.Impl.Rsa.X86.Keys.hdr at *; omega))
    (hx.workspace.write (by unfold kFlag VG.Impl.Rsa.X86.Keys.hdr at *; omega))
    fun t T => WP.block_nil ?_
  refine ⟨hx.rest (T.keeps []), ?_, ?_, K.trans (T.keeps _)⟩
  · rw [T.mem, mem]
    exact Keep.of_slot (writeW32_outside _ _ _ (by decide)) (by simp)
  · unfold slot
    rw [T.mem, mem, w32_write_self, reg, even_bit,
      num_parity _ _ h.wpos aU, num_parity _ _ h.wpos aV]

end VG.Proof.RsaKeyGen.X86.Key
