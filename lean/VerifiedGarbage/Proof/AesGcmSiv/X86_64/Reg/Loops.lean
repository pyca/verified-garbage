module

public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Reg.Crypt
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Loops
import VerifiedGarbage.Proof.Gcm.X86_64.Rev
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Keys
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.GcmSiv.Spec
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# AES-GCM-SIV in registers on x86-64: the loops on the data's 256-byte groups

Untrusted: everything here is checked by Lean. `sealL` and `openL`
(`Impl/AesGcmSiv/X86_64Reg.lean`) run the loops of
`Impl/AesGcmSiv/X86_64Stitch.lean` on the data's groups of sixteen blocks,
for any loops that meet their contracts (`Stitch.LoopsOk`), which take `H`,
`Y` and the counter block in memory: the code before a loop stores them
(`putYH_ok`, `ctrArgs`), and the code after it takes POLYVAL's and counter
mode's registers up again from where the loop left them (`back_ok`,
`ctrBack`), for the rest of the data.
-/

-- separate module: the loops on the groups, apart from the pieces they run between

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSivReg.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64Reg
open VG.Impl.AesGcmSiv.X86_64 (akO bO hO yO cmO tagO skO roundsO dataO lenO aadO alenO)
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ghashFrom blockAt)
open VG.Proof.AesGcmSiv.X86_64 (add_ofNat_assoc)
open VG.Proof.Gcm.X86_64.Pclmul (Only constImm_ok)
open VG.Proof.AesGcmSiv.X86_64 (Stitch.LoopsOk Stitch.HPre Stitch.HPost Stitch.SPre Stitch.CPost Stitch.DPost)

/-! ## Arithmetic -/

theorem shr8shl4 {a : Nat} (ha : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 8 <<< 4 = BitVec.ofNat 64 (16 * (a / 256)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

theorem shr8shl8 {a : Nat} (ha : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 8 <<< 8 = BitVec.ofNat 64 (256 * (a / 256)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

theorem and255 (x : BitVec 64) : x &&& (BitVec.ofNat 32 255).signExtend 64 = BitVec.ofNat 64 (x.toNat % 256) := by
  rw [Proof.AesGcm.X86_64.imm_eq (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 255) (by decide),
    show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega_arith

theorem pad16_append {a b : List Byte} (ha : a.length % 16 = 0) :
    Spec.GcmSiv.pad16 (a ++ b) = a ++ Spec.GcmSiv.pad16 b := by
  simp only [Spec.GcmSiv.pad16, List.length_append, List.append_assoc]
  congr 3; omega_arith

/-! ## `Y` and `H`, to and from memory -/

/-- `putYH`: `Y` and `H` at `W + 80` and `W + 64`, in GHASH's order. -/
theorem putYH_ok (F : MulFacts) {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t) :
    WP isa (.block putYH) t fun t' =>
      blockAt t'.mem (W + BitVec.ofNat 64 80) = t.xmm .xmm2 ∧
      blockAt t'.mem (W + BitVec.ofNat 64 64) = hOf t.mem W ∧
      Frame [⟨W + BitVec.ofNat 64 64, 32⟩] t.mem t'.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r := by
  have h15 := E.r15
  simp only [putYH, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (constImm_ok .xmm0 Impl.Gcm.X86_64.Pclmul.revMask t (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  have h15₁ : s₁.gpr .r15 = W := by rw [o₁.gpr _ (by decide)]; exact h15
  have w₁ : InRegions s₁.wr (W + BitVec.ofNat 64 80) 16 := by rw [o₁.wr]; exact E.perm.wW (by decide)
  obtain ⟨s₂, run₂, m₂, g₂, rd₂, wr₂⟩ : ∃ s₂ : State, runBlock isa
      [.xop (.bin .pshufb .xmm2 .xmm0), .movdquStore (at_ .r15 yO) .xmm2] s₁ = some s₂ ∧
      s₂.mem = s₁.mem.writeW (W + BitVec.ofNat 64 80)
        (XBinOp.eval .pshufb (s₁.xmm .xmm2) Proof.Gcm.X86_64.revMask) ∧
      s₂.gpr = s₁.gpr ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [h15₁, w₁], ?_, ?_, ?_, ?_⟩
    · simp only [mem_setXmm, xmm_setXmm_self, c₁]
      rfl
    all_goals rfl
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have E₂ : Env K W SP s₂ := E.keep (fun r hr => by
    rw [g₂, o₁.gpr r (by rintro rfl; simp at hr)]) (rd₂.trans o₁.rd) (wr₂.trans o₁.wr)
  rw [WP.block_append_iff]
  refine WP.mono (hkey_ok7 (F := F) E₂) fun s₃ ⟨_, _, m₃, rd₃, wr₃, sv₃, x7₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (constImm_ok .xmm0 Impl.Gcm.X86_64.Pclmul.revMask s₃ (by decide)) fun s₄ ⟨c₄, o₄⟩ => ?_
  have h15₄ : s₄.gpr .r15 = W := by rw [o₄.gpr _ (by decide), sv₃ _ (by decide)]; exact E₂.r15
  have w₄ : InRegions s₄.wr (W + BitVec.ofNat 64 64) 16 := by
    rw [o₄.wr, wr₃]; exact E₂.perm.wW (by decide)
  obtain ⟨s₅, run₅, m₅, g₅, rd₅, wr₅⟩ : ∃ s₅ : State, runBlock isa
      [.xop (.bin .pshufb .xmm7 .xmm0), .movdquStore (at_ .r15 hO) .xmm7] s₄ = some s₅ ∧
      s₅.mem = s₄.mem.writeW (W + BitVec.ofNat 64 64)
        (XBinOp.eval .pshufb (s₄.xmm .xmm7) Proof.Gcm.X86_64.revMask) ∧
      s₅.gpr = s₄.gpr ∧ s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr := by
    refine ⟨_, by xrun [h15₄, w₄], ?_, ?_, ?_, ?_⟩
    · simp only [mem_setXmm, xmm_setXmm_self, c₄]
      rfl
    all_goals rfl
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have hw := L.ww
  have f₂ : Frame [⟨W + BitVec.ofNat 64 64, 32⟩] t.mem s₂.mem := by
    rw [m₂, o₁.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by decide) (by decide) (by decide))
  have f₅ : Frame [⟨W + BitVec.ofNat 64 64, 32⟩] t.mem s₅.mem := by
    rw [m₅, o₄.mem, m₃]
    exact f₂.writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by decide) (by decide) (by decide))
  have hH : hOf s₂.mem W = hOf t.mem W := by
    show GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt s₂.mem _ 16)) = _
    rw [Proof.AesGcm.X86_64.bytesAt_frame f₂ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact L.w_w (.inl (by decide)) (by decide) (by decide)) (by decide)]
  refine ⟨?_, ?_, f₅, by rw [rd₅, o₄.rd, rd₃, rd₂, o₁.rd], by rw [wr₅, o₄.wr, wr₃, wr₂, o₁.wr], fun r hr => ?_⟩
  · rw [m₅, Proof.Gcm.X86_64.blockAt_eq, Mem.readW_writeW_sep
      (Offset.sep _ (.inr (by decide)) (by decide) (by decide)) (by decide), o₄.mem, m₃, m₂,
      ← Proof.Gcm.X86_64.blockAt_eq, Proof.Gcm.X86_64.blockAt_store, o₁.xmm _ (by decide)]
  · rw [m₅, Proof.Gcm.X86_64.blockAt_store, o₄.xmm _ (by decide), x7₃, hH]
  · have hne : r ≠ .rax := by rintro rfl; exact absurd hr (by decide)
    rw [g₅, o₄.gpr r hne, sv₃ r hr, g₂, o₁.gpr r hne]

end VG.Proof.AesGcmSivReg.X86_64
