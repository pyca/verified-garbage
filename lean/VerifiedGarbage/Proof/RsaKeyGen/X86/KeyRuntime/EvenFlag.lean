module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Scalar
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace

/-! # Negating the runtime parity bit uses the existing header frame -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num Keep slot)
open VG.Impl.RsaKeyGen.X86.Key (kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem evenFlag_ok {s : State} {B : Addr} {Z n input : Nat}
    (h : Ws s B Z n 32) (hi : input < 32) :
    WP isa (evenFlag input) s fun t => Ws t B Z n 32 ∧ Keep B n [] [kFlag] s.mem t.mem ∧
      slot t.mem B kFlag = (if num s.mem B n input % 2 = 0 then 1 else 0) ∧
      Keeps [.eax, .edx] s t := by
  unfold evenFlag
  refine WP.seq (WP.mono (bitOf_ok h hi (by decide)) fun u ⟨hu, Ou, flag, Ku⟩ => ?_)
  refine wp_movS (readSrc_sc hu.old.workspace (d := kFlag) (by have := hu.hdr_le; unfold VG.Impl.Rsa.X86.Keys.hdr at this; unfold kFlag; omega))
    fun v V _ => wp_logicS (.inr rfl) rfl fun w W => ?_
  have K : Keeps [.eax, .edx] u w := (V.keeps.trans W.keeps).mono (by decide)
  have memory : w.mem = u.mem := W.mem.trans V.mem
  have hw := hu.keep K (by rw [memory]; exact Outside.refl _ _ _ _)
  refine WP.mono (store_slot hw (d := kFlag) (by decide) .eax) fun t ⟨ht, Ot, result, Kt⟩ => ?_
  rw [memory] at Ot
  refine ⟨ht, Ou.trans Ot, ?_, Ku.trans (K.trans (Kt.mono (by decide)))⟩
  rw [result, W.gpr, V.gpr]
  have bit : (u.mem.readW (off B kFlag) 32).toNat ≤ 1 := by
    change slot u.mem B kFlag ≤ 1
    rw [flag]; omega
  change (u.mem.readW (off B kFlag) 32 ^^^ (1 : BitVec 32)).toNat = _
  rw [VG.Proof.Rsa.KeyBits32.bv_xor_bits bit (by decide)]
  change (slot u.mem B kFlag + 1) % 2 = _
  rw [flag]
  have remainder := Nat.mod_lt (num s.mem B n input) (by decide : 0 < 2)
  split <;> omega

end VG.Proof.RsaKeyGen.X86.KeyRuntime
