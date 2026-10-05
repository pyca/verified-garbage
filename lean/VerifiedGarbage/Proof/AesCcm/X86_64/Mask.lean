import VerifiedGarbage.Proof.AesCcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Mask

/-!
# AES-CCM on x86-64: masking the data (`mask`)

Untrusted: everything here is checked by Lean. `mask` ANDs every byte of the
data with `0 − ok`, for `ok` 1 or 0: the data stays if the tags were equal,
and is zeroed if not (`mask_ok`): its first block loads the data, its
length and the mask, and `maskTail` (`Proof/AesGcm/X86_64/Mask.lean`) masks
the data.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Proof.AesGcm.X86_64 (in_of_covers succ_ofNat MInv maskTail_wp ofNat_shr4)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (zeros)

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else zeros j).length = j := by
  cases c <;> simp [zeros, length_bytesAt]

/-- Every byte of the data ANDed with `0 − ok`. -/
theorem mask_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (S : Slots W R N A D nl al n tl s.mem) (hD : Buf K W SP s D n) (hDw : Covers [⟨D, n⟩] s.wr) {c : Bool}
    (hok : s.mem.readW (W + BitVec.ofNat 64 224) 64 = if c then 1 else 0) :
    WP isa mask s fun s' => Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = writeBytes s.mem D (if c then bytesAt s.mem D n else zeros n) := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have r₃ := E.perm.wR (show 224 + 8 ≤ 2560 by decide)
  have hn := hD.lt
  have hd := S.data
  have hl := S.len
  obtain ⟨s₁, run₁, m₁, h12₁, hbp₁, h11₁, r10₁, rcx₁, zf₁, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .r11 (imm 0),
        .alu .sub .r11 (.mem (at_ .r15 okO)), .mov32 .r10 (imm 0), .mov .rcx (.reg .rbp),
        .shift .shr .rcx 4, .alu .test .rcx (.reg .rcx)] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .r12 = D ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧
      s₁.gpr .r11 = 0 - (if c then 1 else 0) ∧ s₁.gpr .r10 = BitVec.ofNat 64 0 ∧
      s₁.gpr .rcx = BitVec.ofNat 64 (n / 16) ∧ s₁.zf = some (decide (n / 16 = 0)) ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp], s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [h15, r₁, r₂, r₃, execShift], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hd]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hl]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hok]; rfl
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hl, ofNat_shr4 hn]
    · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false,
        reduceCtorEq, hl, ofNat_shr4 hn, and_self_beq (show n / 16 < 2 ^ 64 by omega)]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  have E₁ : Env K W SP s₁ := E.keep g₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.mono (maskTail_wp hn (by rw [rd₁, wr₁]; exact hD.rd) (by rw [wr₁]; exact hDw) h12₁ h11₁ hbp₁ r10₁ rcx₁
    zf₁) fun t ht => ?_
  refine ⟨E₁.keep (fun r hr => ht.keep r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    ht.rd ht.wr, by rw [ht.rd, rd₁], by rw [ht.wr, wr₁], ?_⟩
  rw [ht.mem, m₁]
  rfl

end VG.Proof.AesCcm.X86_64
