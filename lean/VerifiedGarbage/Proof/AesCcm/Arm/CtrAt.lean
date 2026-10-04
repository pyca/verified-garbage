import VerifiedGarbage.Proof.AesCcm.Arm.Ctrs

/-!
# AES-CCM on ARMv7: a counter block `Ctrᵢ` (`ctrAt`)

Untrusted: everything here is checked by Lean. `ctrAt` copies `Ctr₀` from
`W + 48` to `W + 64`, its last word ORed with `[i]₃₂` (`rev` of `i`, in
`r0`): `Ctrᵢ`, for `i < 2^(8 min(q, 4))` (`ctrAt_ok`,
`Proof.AesCcm.ctrBlock_split`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4 store4)
open VG.Proof.AesGcm.Arm (mem_store store32_eq gpr_store rd_store wr_store sp_store encodable_of_decide sepW
  bytes_words store4_eq add_ofNat_assoc)

section
variable {k w sp : BitVec 32} {R q1 : Nat} (L : Lay k w sp)
include L

/-- `ctrAt`: `Ctrᵢ` at `W + 64`, from `Ctr₀` at `W + 48`. -/
theorem ctrAt_ok {s : State} (he : Env k w sp R q1 s) {nonce : List Byte} (h7 : 7 ≤ nonce.length)
    (h13 : nonce.length ≤ 13) (hc : bytesAt s.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    {i : Nat} (h0 : s.gpr .r0 = BitVec.ofNat 32 i) (hi : i < 256 ^ min (15 - nonce.length) 4) :
    ∃ s', runBlock isa ctrAt s = some s' ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce i ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 64, 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h11 := he.r11
  have hi4 : i < 2 ^ 32 := Nat.lt_of_lt_of_le hi (by
    rw [show (2 : Nat) ^ 32 = 256 ^ 4 from rfl]; exact Nat.pow_le_pow_right (by decide) (by omega))
  have r₀ := he.perm.wR (show 48 + 4 ≤ 2560 by decide)
  have r₁ := he.perm.wR (show 52 + 4 ≤ 2560 by decide)
  have r₂ := he.perm.wR (show 56 + 4 ≤ 2560 by decide)
  have r₃ := he.perm.wR (show 60 + 4 ≤ 2560 by decide)
  have w₀ := he.perm.wW (show 64 + 4 ≤ 2560 by decide)
  have w₁ := he.perm.wW (show 68 + 4 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 72 + 4 ≤ 2560 by decide)
  have w₃ := he.perm.wW (show 76 + 4 ≤ 2560 by decide)
  have q : ∀ a d, a + 4 ≤ d → d + 4 ≤ 2560 →
      (⟨State.addr w + BitVec.ofNat 64 a, 4⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, 4⟩ :=
    fun a d h₁ h₂ => L.w_w (.inl h₁) (by omega) h₂
  have p₁ := fun m v => sepW (m := m) (v := v) (q 52 64 (by decide) (by decide))
  have p₂ := fun m v => sepW (m := m) (v := v) (q 56 64 (by decide) (by decide))
  have p₃ := fun m v => sepW (m := m) (v := v) (q 56 68 (by decide) (by decide))
  have p₄ := fun m v => sepW (m := m) (v := v) (q 60 64 (by decide) (by decide))
  have p₅ := fun m v => sepW (m := m) (v := v) (q 60 68 (by decide) (by decide))
  have p₆ := fun m v => sepW (m := m) (v := v) (q 60 72 (by decide) (by decide))
  have e := fun d (hd : d < 2560) => L.wA (d := d) hd
  let m := s.mem
  let W := State.addr w
  have hm : ∃ s', runBlock isa ctrAt s = some s' ∧
      s'.mem = store4 m (W + BitVec.ofNat 64 64) (m.readW (W + BitVec.ofNat 64 48) 32)
        (m.readW (W + BitVec.ofNat 64 52) 32) (m.readW (W + BitVec.ofNat 64 56) 32)
        (m.readW (W + BitVec.ofNat 64 60) 32 ||| rev (BitVec.ofNat 32 i)) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    refine ⟨_, by simp only [ctrAt, c0O, c1O]; arun [h11, h0, e, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, p₁, p₂, p₃,
      p₄, p₅, p₆], ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc, m, W]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals exact ⟨rfl, rfl, rfl⟩
  obtain ⟨s', run, hm', g, rd, wr, sp⟩ := hm
  refine ⟨s', run, ?_, by rw [hm']; exact Proof.Cmac.frame_store4 _ _ _ _ _, g, rd, wr, sp⟩
  -- The words of `Ctr₀`.
  have hw := hc
  rw [bytes_words] at hw
  simp only [add_ofNat_assoc] at hw
  have l := Proof.Cmac.length_le4
  have hl : (le4 (m.readW (W + BitVec.ofNat 64 48) 32) ++ le4 (m.readW (W + BitVec.ofNat 64 52) 32) ++
      le4 (m.readW (W + BitVec.ofNat 64 56) 32)).length = 12 := by simp [l]
  rw [hm', Proof.Cmac.bytesAt_store4, ctrBlock_split h7 h13 hi, ← hw, le4_or, le4_rev_ofNat hi4,
    List.take_left' hl, List.drop_left' hl]

end

end VG.Proof.AesCcm.Arm
