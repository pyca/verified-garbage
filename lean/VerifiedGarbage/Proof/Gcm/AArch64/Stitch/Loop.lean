module

public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Steps
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Weave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.CallLay

/-!
# Interleaved counter mode and GHASH on AArch64: the loops

Untrusted: everything here is checked by Lean. One iteration (`body_ok`):
batch `c` encrypted (or decrypted) while batch `h` is hashed, woven
(`parts_ok`, the parts independent by `Weave.lean`), then stored;
`seal`'s (`c = h + 1`) hashes the ciphertext the previous iteration stored,
`open`'s (`c = h`) the batch as it was. The setup (`setup_ok`), the loops for
any number of rounds (`encLoop_ok`, `decLoop_ok`) and the end (`finish_ok`)
make `enc` and `dec` meet `EPost` and `DPost` (`enc_ok`, `dec_ok`).
-/

@[expose] public section

namespace VG.Proof.Gcm.AArch64.Stitch

open VG VG.AArch64
open VG.AArch64.RegUpd (v_setV_self v_setV_of_ne gpr_setV mem_setV rd_setV wr_setV sp_setV v_write
  gpr_write gpr_write_self gpr_write_of_ne mem_write rd_write wr_write sp_write)
open VG.Proof.Aes.AArch64 (DataInv keyStream)
open VG.Proof.Aes.AArch64.Aese (Fr vbyte_readW inRegions_wr exec_strq)
open VG.Proof.Gcm.AArch64.Pmull (ext8 VOnly rev64b_read)
open VG.Spec.Gcm (Block blockAt blocksAt inc32 aesWith ghashFrom ctr32)
open VG.Impl.Gcm.AArch64.Stitch

/-! ## The pointer and the count -/

theorem adv_ok {s₀ : State} {u : State} {h c : Nat} (hc : c < nb s₀)
    (hx9 : u.gpr .x9 = dp s₀ + BitVec.ofNat 64 (128 * h))
    (hx11 : u.gpr .x11 = BitVec.ofNat 64 (nb s₀ - c)) :
    WP isa (.block [.addImm .x .x9 .x9 128, .subImm .x .x11 .x11 1]) u fun u' =>
      u'.gpr .x9 = dp s₀ + BitVec.ofNat 64 (128 * (h + 1)) ∧
      u'.gpr .x11 = BitVec.ofNat 64 (nb s₀ - (c + 1)) ∧
      (∀ r, r ≠ .x9 → r ≠ .x11 → u'.gpr r = u.gpr r) ∧ u'.v = u.v ∧ u'.mem = u.mem ∧
      u'.sp = u.sp ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  rw [WP.block_cons_iff]
  refine ⟨_, exec_addImm_x (imm := 128) (by decide), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  refine ⟨?_, ?_, fun r h9 h11 => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · rw [gpr_write_of_ne _ _ _ (by decide), gpr_write_self, BitVec.setWidth_eq]
    simp only [State.read, BitVec.setWidth_eq, hx9]
    rw [Offset.add_add_eq _ (show 128 * h + 128 = 128 * (h + 1) by omega)]
  · rw [gpr_write_self, BitVec.setWidth_eq]
    simp only [State.read, BitVec.setWidth_eq, gpr_write_of_ne _ _ _ (show Reg.x11 ≠ Reg.x9 by decide), hx11]
    rw [Offset.ofNat_sub_ofNat (by omega), show nb s₀ - c - 1 = nb s₀ - (c + 1) by omega]
  · rw [gpr_write_of_ne _ _ _ h11, gpr_write_of_ne _ _ _ h9]

/-! ## One iteration -/

theorem body_ok {s₀ : State} (hp : KPre s₀) (gh : Gh8Ok) {hb : Nat → Block} {c h o : Nat}
    (hc : c < nb s₀) (hh : h < nb s₀) (hho : 128 * h + o = 128 * c) (ho : o = 0 ∨ o = 128)
    {s : State} (hI : LInv s₀ hb c h s)
    (hhb : ∀ j < 8, blockAt s.mem (dp s₀ + BitVec.ofNat 64 (16 * (8 * h + j))) = hb (8 * h + j)) :
    WP isa (.block (parts (rounds s₀) o ++ stores o ++
      ([.addImm .x .x9 .x9 128, .subImm .x .x11 .x11 1] : List Instr))) s (LInv s₀ hb (c + 1) (h + 1)) := by
  have ho' : o ≤ 128 := by omega
  have ho16 : o % 16 = 0 := by omega
  rw [List.append_assoc, WP.block_append_iff]
  refine parts_ok hp.rounds ho ?_
  refine WP.mono (aesStep hp hI hc hho ho' ho16) fun t ⟨hv, x10t, frt⟩ => ?_
  have gt : ∀ r, r ≠ .x10 → r ≠ .x12 → t.gpr r = s.gpr r := fun r h1 h2 => frt.gpr r (by simp [h1, h2])
  refine WP.mono (ghStep hp gh (hb := hb) (t := t) (by rw [frt.v _ (by decide), hI.y])
    (by rw [frt.v _ (by decide), hI.cr]) (by rw [gt _ (by decide) (by decide), hI.x9]) hh
    (by rw [gt _ (by decide) (by decide), hI.gpr _ (by decide)])
    (by rw [frt.rd, frt.wr, hI.rd, hI.wr]) (by rw [frt.mem]; exact hI.frame)
    (fun j hj => by rw [frt.mem]; exact hhb j hj)) fun u ⟨hy, ou⟩ => ?_
  rw [WP.block_append_iff]
  have gu : ∀ r, r ≠ .x10 → r ≠ .x12 → u.gpr r = s.gpr r := fun r h1 h2 => by rw [ou.gpr, gt r h1 h2]
  refine WP.mono (stores_ok hp hc ho' ho16 u (by rw [gu _ (by decide) (by decide), hI.x9,
      Offset.add_add_eq _ hho]) (by rw [ou.mem, frt.mem]; exact hI.data) (by rw [ou.wr, frt.wr, hI.wr])
    (fun j hj tt htt => by rw [ou.v _ (by unfold breg; split <;> decide)]; exact hv j hj tt htt))
    fun u₁ ⟨d₁, f₁, g₁, v₁, sp₁, rd₁, wr₁⟩ => ?_
  refine WP.mono (adv_ok (h := h) hc (by rw [g₁, gu _ (by decide) (by decide), hI.x9])
    (by rw [g₁, gu _ (by decide) (by decide), hI.x11])) fun u' ⟨x9', x11', g', v', m', sp', rd', wr'⟩ => ?_
  have gall : ∀ r, r ≠ .x9 → r ≠ .x11 → u'.gpr r = u.gpr r := fun r h9 h11 => by rw [g' r h9 h11, g₁]
  refine ⟨by omega, x9', ?_, x11', fun r hr => ?_, ?_, ?_, by rw [m']; exact d₁, ?_, ?_, ?_, ?_⟩
  · simp only [State.read] at x10t ⊢
    rw [gall _ (by decide) (by decide), ou.gpr]; exact x10t
  · simp only [kRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gall r hr.1 hr.2.2.1, gu r hr.2.1 hr.2.2.2.1, hI.gpr r (by simp [kRegs, hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])]
  · rw [v', v₁, hy]
  · rw [v', v₁, ou.v C (by decide), frt.v C (by decide), hI.cr]
  · rw [m']
    have : s.mem = u.mem := by rw [ou.mem, frt.mem]
    exact hI.frame.trans (this ▸ f₁)
  · rw [sp', sp₁, ou.sp, frt.sp, hI.sp]
  · rw [rd', rd₁, ou.rd, frt.rd, hI.rd]
  · rw [wr', wr₁, ou.wr, frt.wr, hI.wr]

end VG.Proof.Gcm.AArch64.Stitch
