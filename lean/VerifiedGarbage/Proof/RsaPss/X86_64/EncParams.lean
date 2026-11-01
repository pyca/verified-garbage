module

import VerifiedGarbage.Proof.RsaPss.X86_64.Params
public import VerifiedGarbage.Impl.RsaPss.X86_64.Encoding
public import VerifiedGarbage.Proof.RsaPss.EncodingContract
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaPss.X86_64.Basic

/-!
# EMSA-PSS's encoding and its check on x86-64: the parameters

`maskBits` stores the mask `0xFF >>> (8 emLen - emBits)` and `lo = 0` to
their slots (`maskBits_ok`); `fitH` sets CF iff `emLen < hLen + 2`
(`fitH_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off)

theorem shr_ff_table : ∀ z < 8, (BitVec.setWidth 64 (0xFF#32) >>> z : BitVec 64) =
    BitVec.setWidth 64 ((0xFF : Byte) >>> z) := by decide

/-- The mask's shift count: `8 emLen - emBits`, at most 7. -/
theorem emLength_z {b : Nat} : 8 * Spec.RsaPss.emLength b - b < 8 ∧ b ≤ 8 * Spec.RsaPss.emLength b := by
  unfold Spec.RsaPss.emLength; omega

theorem maskBits_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {r : Reg} (hra : r ≠ .rax) {b : Nat}
    (hk : W 17 = BitVec.ofNat 64 (Spec.RsaPss.emLength b)) (hb : u.gpr r = BitVec.ofNat 64 b)
    (hb2 : b ≤ Proof.RsaPss.maxEmBits) :
    WP isa (.block (maskBits r)) u fun u' => Lay u' F S ∧ Keep [.rax, .rcx] u u' ∧
      Rep u'.mem F S V (upd (upd W 25 (BitVec.setWidth 64 ((0xFF : Byte) >>> (8 * Spec.RsaPss.emLength b - b))))
        26 0) ∧
      u'.mem = (u.mem.writeW (off F sC) (BitVec.setWidth 64 ((0xFF : Byte) >>> (8 * Spec.RsaPss.emLength b - b)))).writeW
        (off F sLo) (0 : BitVec 64) := by
  have G := L.geo
  obtain ⟨hz, hle⟩ := emLength_z (b := b)
  have hE : Spec.RsaPss.emLength b ≤ 1024 := by unfold Spec.RsaPss.emLength Proof.RsaPss.maxEmBits at *; omega
  have R1 := R.wf G (k := 25) (by decide) (BitVec.setWidth 64 ((0xFF : Byte) >>> (8 * Spec.RsaPss.emLength b - b)))
  have R2 := R1.wf G (k := 26) (by decide) 0
  rw [show off F (8 * 25) = off F sC from rfl] at R1 R2
  rw [show off F (8 * 26) = off F sLo from rfl] at R2
  have hsh : BitVec.ofNat 64 (Spec.RsaPss.emLength b) <<< 3 - BitVec.ofNat 64 b =
      BitVec.ofNat 64 (8 * Spec.RsaPss.emLength b - b) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_twoPow]
    have : b < 2 ^ 64 := by unfold Proof.RsaPss.maxEmBits at hb2; omega
    rw [Nat.mod_eq_of_lt (show Spec.RsaPss.emLength b < 2 ^ 64 by omega), Nat.mod_eq_of_lt this]
    omega
  have hzt : (BitVec.ofNat 64 (8 * Spec.RsaPss.emLength b - b)).toNat % 64 = 8 * Spec.RsaPss.emLength b - b := by
    rw [BitVec.toNat_ofNat]; omega
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun u' => u'.mem = (u.mem.writeW (off F sC)
      (BitVec.setWidth 64 ((0xFF : Byte) >>> (8 * Spec.RsaPss.emLength b - b)))).writeW (off F sLo) (0 : BitVec 64))
      ?_ rfl) fun u' ⟨hm, k⟩ => ?_
  · xrun [maskBits, ea_sp, L.rsp, L.ld (d := sK) (by decide), L.st (d := sC) (by decide),
      L.st (d := sLo) (by decide), R.rd (d := sK) 17 rfl (by decide), hk, hb, ifn hra, execShiftCl,
      VarShiftOp.eval, hsh, hzt, shr_ff_table _ hz]
    rfl
  refine ⟨L.congr (k.gpr (by decide)) k.2.2 ?_, k, hm ▸ R2, hm⟩
  have h1 := R2.fr 21 (by decide)
  rw [← hm] at h1
  rw [slot_eq sScr 21 rfl, slot_eq sScr 21 rfl, h1, R.fr 21 (by decide)]
  simp [upd]

theorem fitH_ok {H : Impl.Pbkdf2.Md.X86_64.Hash} (hD : H.D + 2 < 2 ^ 31) {u : State} {F S : Addr}
    (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem F S V W) {k : Nat}
    (hk : W 17 = BitVec.ofNat 64 k) (hk2 : k < 2 ^ 32) :
    WP isa (.block (fitH H)) u fun u' => Keep [.rax] u u' ∧ u'.mem = u.mem ∧
      u'.gpr .rax = BitVec.ofNat 64 k ∧ u'.cf = some (decide (k < H.D + 2)) := by
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem ∧ u'.gpr .rax = BitVec.ofNat 64 k ∧
    u'.cf = some (decide (k < H.D + 2))) ?_ rfl) fun u' ⟨h, k⟩ => ⟨k, h⟩
  xrun [fitH, ea_sp, L.rsp, L.ld (d := sK) (by decide), R.rd (d := sK) 17 rfl (by decide), hk,
    VG.Proof.MlKem.X86_64.sx_ofNat hD]
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

end VG.Proof.RsaPss.X86_64
