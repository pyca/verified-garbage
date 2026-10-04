import VerifiedGarbage.Proof.AesOcb.X86_64.Whole

/-!
# AES-OCB on x86-64: the rest of the data XORed with `Pad` (`xorPad`)

Untrusted: everything here is checked by Lean. `xorPad` XORs the `r` bytes
at `rbx` with the first `r` bytes of the block at `W + tmpO`, a byte at a
time, counting up in `rcx` (`xorPad_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm.X86_64 (runBlock_append toNat_ofNat_of_lt eval_e eval_ne length_bytesAt)
open VG.Proof.AesGcm.X86_64 (in_of_covers succ_ofNat bytesAt_succ)

theorem xor_byte (a b : Byte) : ((a.setWidth 64 ^^^ b.setWidth 64).setWidth 8 : Byte) = a ^^^ b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_xor]
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by have := a.isLt; omega), Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega)]
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow a.isLt b.isLt)

theorem ea_index_disp (s : State) {b i : Reg} {B : Addr} {j d : Nat} (hb : s.gpr b = B)
    (hi : s.gpr i = BitVec.ofNat 64 j) :
    s.gpr b + s.gpr i * BitVec.ofNat 64 1 + BitVec.ofInt 64 (d : Int) = B + BitVec.ofNat 64 d + BitVec.ofNat 64 j := by
  rw [hb, hi, BitVec.mul_one, Proof.AesCcm.X86_64.offset_nat, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 j)]

theorem xor_snoc (xs ys : List Byte) (hl : xs.length = ys.length) (a b : Byte) :
    Spec.Ocb.xor (xs ++ [a]) (ys ++ [b]) = Spec.Ocb.xor xs ys ++ [a ^^^ b] := by
  simp [Spec.Ocb.xor, List.zipWith_append hl]

theorem length_xor_bytes (m : Mem) (p q : Addr) (j : Nat) : (Spec.Ocb.xor (bytesAt m p j) (bytesAt m q j)).length = j := by
  simp [Spec.Ocb.xor, length_bytesAt]

/-- One step of `xorPad`. -/
theorem xorStep_ok (s : State) {P T : Addr} {j r : Nat} (h3 : s.gpr .rbx = P) (h15 : s.gpr .r15 = T)
    (h1 : s.gpr .rcx = BitVec.ofNat 64 j) (h12 : s.gpr .r12 = BitVec.ofNat 64 r)
    (rP : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 j) 1) (wP : InRegions s.wr (P + BitVec.ofNat 64 j) 1)
    (rT : InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 112 + BitVec.ofNat 64 j) 1) :
    ∃ s', runBlock isa [.movzx8 .rax { base := .rbx, index := some .rcx },
        .movzx8 .rdx { base := .r15, index := some .rcx, disp := tmpO }, .alu .xor .rax (.reg .rdx),
        .store8 { base := .rbx, index := some .rcx } .rax, addi .rcx 1, .alu .cmp .rcx (.reg .r12)] s = some s' ∧
      s'.mem = s.mem.writeW (P + BitVec.ofNat 64 j)
        (s.mem (P + BitVec.ofNat 64 j) ^^^ s.mem (T + BitVec.ofNat 64 112 + BitVec.ofNat 64 j)) ∧
      s'.gpr .rcx = BitVec.ofNat 64 (j + 1) ∧
      s'.zf = some (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 r == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea₁ := ea_index s h3 h1
  have ea₂ : s.gpr .r15 + s.gpr .rcx * BitVec.ofNat 64 1 + BitVec.ofNat 64 112 =
      T + BitVec.ofNat 64 112 + BitVec.ofNat 64 j := ea_index_disp s (d := 112) h15 h1
  refine ⟨_, by orun [ea₁, ea₂, rP, wP, rT], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, xor_byte]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h1, sext1, ← BitVec.ofNat_add]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h1, h12, sext1,
      ← BitVec.ofNat_add]
  · intro r h₁ h₂ h₃; simp only [gpr_setReg, gpr_arithFlags, h₁, h₂, h₃, ite_false]
  all_goals rfl

/-- `xorPad`: the `r` bytes at `P` (in `rbx`), `0 < r < 16`, XORed with the
first `r` bytes at `W + tmpO`. -/
theorem xorPad_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {P : Addr} {r : Nat} (hr : 0 < r) (hr' : r < 16)
    (h3 : s.gpr .rbx = P) (h12 : s.gpr .r12 = BitVec.ofNat 64 r) (hP : DBuf K W SP s P r) :
    WP isa xorPad s fun t => t.mem = writeBytes s.mem P
        (Spec.Ocb.xor (bytesAt s.mem P r) (bytesAt s.mem (W + BitVec.ofNat 64 112) r)) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨s₁, run₁, rcx₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov .rcx (.imm 0)] s = some s₁ ∧
      s₁.gpr .rcx = BitVec.ofNat 64 0 ∧ (∀ r, r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by orun [], ?_, fun r h => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, BitVec.xor_self, sext0]
    · simp only [gpr_setReg, gpr_arithFlags, h, ite_false]
    all_goals rfl
  unfold xorPad
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hT : ∀ j < r, InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 112 + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [Offset.add_add]; exact E.perm.wR (by omega)
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (u : State) => ∃ j, k = r - j ∧ j < r ∧ u.gpr .rcx = BitVec.ofNat 64 j ∧
      u.mem = writeBytes s.mem P (Spec.Ocb.xor (bytesAt s.mem P j) (bytesAt s.mem (W + BitVec.ofNat 64 112) j)) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr) ?_ (r - 0) _
    ⟨0, rfl, hr, rcx₁, by rw [m₁]; simp [bytesAt, Spec.Ocb.xor, writeBytes_nil], fun r _ _ h => g₁ r h, rd₁, wr₁⟩
  rintro k u ⟨j, rfl, hj, rcx, mem, g, rd, wr⟩
  obtain ⟨u', run', mem', rcx', zf', g', rd', wr'⟩ := xorStep_ok u (P := P) (T := W) (j := j) (r := r)
    (by rw [g _ (by decide) (by decide) (by decide), h3]) (by rw [g _ (by decide) (by decide) (by decide), E.r15]) rcx
    (by rw [g _ (by decide) (by decide) (by decide), h12]) (by rw [rd, wr]; exact in_of_covers hP.rd hj hP.lt)
    (by rw [wr]; exact in_of_covers hP.wr hj hP.lt) (by rw [rd, wr]; exact hT j hj)
  refine WP.of_runBlock ⟨u', run', ?_⟩
  have fr : Frame [⟨P, j⟩] s.mem u.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [length_xor_bytes]; exact contains_pre _ (by omega))
  have hq : u.mem (P + BitVec.ofNat 64 j) = s.mem (P + BitVec.ofNat 64 j) :=
    fr _ fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat P (show j < 2 ^ 64 by omega)] at hc; omega
  have hqT : u.mem (W + BitVec.ofNat 64 112 + BitVec.ofNat 64 j) = s.mem (W + BitVec.ofNat 64 112 + BitVec.ofNat 64 j) :=
    fr _ fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      have hdis : (⟨P, r⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 112 + BitVec.ofNat 64 j, 1⟩ := by
        rw [Offset.add_add]; exact hP.w.sub_right (Lay.wSub (by omega))
      exact hdis.sub_left (Region.sub_prefix (by omega)) _ hc (Region.contains_self _ _)
  have hmem : u'.mem = writeBytes s.mem P (Spec.Ocb.xor (bytesAt s.mem P (j + 1)) (bytesAt s.mem (W + BitVec.ofNat 64 112) (j + 1))) := by
    rw [mem', hq, hqT, mem, bytesAt_succ, bytesAt_succ, xor_snoc _ _ (by simp [length_bytesAt]),
      writeBytes_snoc _ _ _ _ (by rw [length_xor_bytes]; omega), length_xor_bytes]
  have hz : u'.zf = some (decide (j + 1 = r)) := by
    rw [zf', Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have gg : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → u'.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by
    rw [g' r h₁ h₂ h₃, g r h₁ h₂ h₃]
  by_cases he : j + 1 = r
  · left
    exact ⟨(eval_ne hz).trans (by simp [he]), by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · right
    exact ⟨(eval_ne hz).trans (by simp [he]), r - (j + 1), by omega, j + 1, rfl, by omega, rcx', hmem, gg,
      by rw [rd', rd], by rw [wr', wr]⟩

end VG.Proof.AesOcb.X86_64
