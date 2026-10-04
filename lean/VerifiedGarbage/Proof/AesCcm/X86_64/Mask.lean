import VerifiedGarbage.Proof.AesCcm.X86_64.Run

/-!
# AES-CCM on x86-64: masking the data (`mask`)

Untrusted: everything here is checked by Lean. `mask` ANDs every byte of the
data with `0 − ok`, for `ok` 1 or 0: the data stays if the tags were equal,
and is zeroed if not (`mask_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Proof.AesGcm.X86_64 (in_of_covers succ_ofNat)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (zeros)

theorem mask_byte (b : Byte) (c : Bool) :
    ((b.setWidth 64 &&& ((0 : BitVec 64) - (if c then 1 else 0))).setWidth 8) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 64) else 0) = 1 from rfl,
      show (0 : BitVec 64) - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
    simp

theorem maskStep_ok (s : State) {P : Addr} {j L : Nat} {c : Bool} (h12 : s.gpr .r12 = P)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 j) (h11 : s.gpr .r11 = 0 - (if c then 1 else 0))
    (hbp : s.gpr .rbp = BitVec.ofNat 64 L)
    (rq : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 j) 1) (wq : InRegions s.wr (P + BitVec.ofNat 64 j) 1) :
    ∃ s', runBlock isa [.movzx8 .rax maskByte, .alu .and .rax (.reg .r11), .store8 maskByte .rax,
        .alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .rbp)] s = some s' ∧
      s'.mem = s.mem.writeW (P + BitVec.ofNat 64 j) ((if c then s.mem (P + BitVec.ofNat 64 j) else 0 : Byte)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 j + 1 ∧
      s'.zf = some (BitVec.ofNat 64 j + 1 - BitVec.ofNat 64 L == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea : s.gpr .r12 + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = P + BitVec.ofNat 64 j := by
    rw [h12, h10, BitVec.mul_one]; simp
  refine ⟨_, by crun [maskByte, ea, rq, wq], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, h11, mask_byte]
  · simp [gpr_setReg, h10]
  · simp [h10, hbp]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  all_goals rfl

theorem bytesAt_succ (m : Mem) (p : Addr) (i : Nat) :
    bytesAt m p (i + 1) = bytesAt m p i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp [bytesAt, List.range_succ]

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else zeros j).length = j := by
  cases c <;> simp [zeros, length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else zeros (j + 1)) =
      (if c then bytesAt m P j else zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [zeros, bytesAt_succ, List.replicate_succ']

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
  obtain ⟨s₁, run₁, m₁, h12₁, hbp₁, h11₁, r10₁, zf₁, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .r11 (imm 0),
        .alu .sub .r11 (.mem (at_ .r15 okO)), .mov32 .r10 (imm 0), .alu .test .rbp (.reg .rbp)] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .r12 = D ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧
      s₁.gpr .r11 = 0 - (if c then 1 else 0) ∧ s₁.gpr .r10 = BitVec.ofNat 64 0 ∧ s₁.zf = some (decide (n = 0)) ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp], s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [h15, r₁, r₂, r₃], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hd]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hl]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hok]; rfl
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hl, and_self_beq hn]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  have E₁ : Env K W SP s₁ := E.keep g₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (eval_e zf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hn0 : n = 0 := of_decide_eq_true hb
    subst hn0
    refine ⟨E₁, rd₁, wr₁, ?_⟩
    rw [m₁]
    cases c <;> simp [bytesAt, zeros, writeBytes_nil]
  have hn0 : 0 < n := Nat.pos_of_ne_zero (of_decide_eq_false hb)
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ t.gpr .r10 = BitVec.ofNat 64 j ∧
      t.mem = writeBytes s.mem D (if c then bytesAt s.mem D j else zeros j) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → t.gpr r = s₁.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hn0, r10₁, by rw [m₁]; cases c <;> simp [bytesAt, zeros, writeBytes_nil],
      fun r _ _ => rfl, rd₁, wr₁⟩
  rintro k t ⟨j, rfl, hj, r10, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := maskStep_ok t (P := D) (j := j) (L := n) (c := c)
    (by rw [g _ (by decide) (by decide), h12₁]) r10 (by rw [g _ (by decide) (by decide), h11₁])
    (by rw [g _ (by decide) (by decide), hbp₁]) (by rw [rd, wr]; exact in_of_covers hD.rd hj hn)
    (by rw [wr]; exact in_of_covers hDw hj hn)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨D, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (D + BitVec.ofNat 64 j) = s.mem (D + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat D (show j < 2 ^ 64 by omega)] at hcon; omega
  have hmem : t'.mem = writeBytes s.mem D (if c then bytesAt s.mem D (j + 1) else zeros (j + 1)) := by
    rw [mem', hq, mem, mask_succ, writeBytes_snoc _ _ _ _ (by rw [length_mask]; omega), length_mask]
  have hz : t'.zf = some (decide (j + 1 = n)) := by
    rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have gg : ∀ r, r ≠ .rax → r ≠ .r10 → t'.gpr r = s₁.gpr r := fun r h₁ h₂ => by rw [g' r h₁ h₂, g r h₁ h₂]
  have E' : Env K W SP t' := E₁.keep (fun r hr => gg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    (by rw [rd', rd, rd₁]) (by rw [wr', wr, wr₁])
  by_cases he : j + 1 = n
  · left
    exact ⟨(eval_ne hz).trans (by simp [he]), E', by rw [rd', rd], by rw [wr', wr], by rw [hmem, he]⟩
  · right
    refine ⟨(eval_ne hz).trans (by simp [he]), n - (j + 1), by omega, j + 1, rfl, by omega, by rw [r10', succ_ofNat],
      hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

end VG.Proof.AesCcm.X86_64
