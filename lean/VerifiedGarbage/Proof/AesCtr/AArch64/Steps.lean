import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.AesCbc.AArch64.Body
import VerifiedGarbage.Impl.AesCtr.AArch64

/-!
# AES-CTR on AArch64: the code between the calls

The straight-line pieces of an iteration, run once each: the number of
blocks of the call (`count`, `min left (2³² − lo32 t)`), its arguments
(`args`), the advance past them with the counter's last 32 bits read back
(`adv`), and the carry into the first 96 bits (`carry`, whose block is
`t + 2³²`).
-/

namespace VG.Proof.AesCtr.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCtr.AArch64
open VG.Impl.AesCbc.AArch64 (mov cOff)
open VG.Spec.Aes (bytesAt)

theorem read4 (m : Mem) (a : Addr) : m.read a 4 = m.readW a 32 := by
  simp [Mem.readW]

theorem countA_ok (s : State) {Q : Addr} (hq : s.gpr .x21 = Q)
    (rq : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 12) 4) :
    ∃ s', runBlock isa [.ldr .w .x9 .x21 12, .rev32 .x9 .x9] s = some s' ∧
      s'.gpr .x9 = (rv32 (s.mem.readW (Q + BitVec.ofNat 64 12) 32)).setWidth 64 ∧
      (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by crun [read4, hq, rq], ?_⟩
  refine ⟨?_, fun r hr => by simp [gpr_write, hr], rfl, rfl, rfl, rfl⟩
  simp only [gpr_write, ite_true]
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  rfl

theorem countB1_ok (s : State) {c : BitVec 32} (h9 : s.gpr .x9 = c.setWidth 64) :
    ∃ s', runBlock isa [.movz .x .x10 1 2, .sub .x .x10 .x10 .x9] s = some s' ∧
      s'.gpr .x10 = 0x100000000 - c.setWidth 64 ∧
      (∀ r, r ≠ .x10 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by crun [], ?_⟩
  refine ⟨?_, fun r hr => by simp [gpr_write, hr], rfl, rfl, rfl, rfl⟩
  simp only [gpr_write, ↓reduceIte, BitVec.setWidth_eq, h9]
  rfl

theorem countB2_ok (s : State) {a b : BitVec 64} (h23 : s.gpr .x23 = a) (h10 : s.gpr .x10 = b) :
    ∃ s', runBlock isa [.subs .x .x11 .x23 .x10, .csel .x .x10 .x10 .x23] s = some s' ∧
      s'.gpr .x10 = (if a.toNat < b.toNat then a else b) ∧
      (∀ r, r ≠ .x10 → r ≠ .x11 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [gpr_addWithCarry, c_addWithCarry, mem_addWithCarry, rd_addWithCarry, wr_addWithCarry,
    sp_addWithCarry], ?_⟩
  refine ⟨?_, fun r h₁ h₂ => by simp [gpr_write, gpr_addWithCarry, h₁, h₂], rfl, rfl, rfl, rfl⟩
  simp only [gpr_write, ↓reduceIte, h23, h10, BitVec.setWidth_eq]
  have hn : (~~~b).toNat = 2 ^ 64 - 1 - b.toNat := by rw [BitVec.toNat_not]
  have hb := b.isLt
  by_cases h : a.toNat < b.toNat
  · have hc : ¬2 ^ 64 ≤ a.toNat + (~~~b).toNat + (true).toNat := by rw [hn, Bool.toNat_true]; omega
    simp only [hc, h, decide_false, Bool.false_eq_true, ↓reduceIte]
  · have hc : 2 ^ 64 ≤ a.toNat + (~~~b).toNat + (true).toNat := by rw [hn, Bool.toNat_true]; omega
    simp only [hc, h, decide_true, ↓reduceIte]

theorem args_ok (s : State) :
    ∃ s', runBlock isa args s = some s' ∧
      s'.gpr .x0 = s.gpr .x19 ∧ s'.gpr .x1 = s.gpr .x20 ∧ s'.gpr .x2 = s.gpr .x21 ∧
      s'.gpr .x3 = s.gpr .x22 ∧ s'.gpr .x4 = s.gpr .x10 ∧ s'.gpr .x5 = s.gpr .x24 ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by crun [args], ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    by simp [gpr_write], by simp [gpr_write], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]

theorem store_ok (s : State) {S : Addr} (hs : s.gpr .x24 = S) (ws : InRegions s.wr (S + BitVec.ofNat 64 2048) 8) :
    ∃ s', runBlock isa [.str .x .x10 .x24 cOff] s = some s' ∧ s'.gpr = s.gpr ∧ s'.sp = s.sp ∧
      s'.mem = s.mem.writeW (S + BitVec.ofNat 64 2048) (s.gpr .x10) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [cOff, hs, ws], ?_⟩
  refine ⟨rfl, rfl, ?_, rfl, rfl⟩
  simp only [Mem.writeW, BitVec.setWidth_eq]

theorem advA_ok (s : State) {S P : Addr} {left m : Nat} (hs : s.gpr .x24 = S) (h22 : s.gpr .x22 = P)
    (h23 : s.gpr .x23 = BitVec.ofNat 64 left) (hm : s.mem.readW (S + BitVec.ofNat 64 2048) 64 = BitVec.ofNat 64 m)
    (hml : m ≤ left) (h16 : 16 * m < 2 ^ 64)
    (rs : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 2048) 8) :
    ∃ s', runBlock isa [.ldr .x .x9 .x24 cOff, .sub .x .x23 .x23 .x9, .lsl .x .x9 .x9 4,
        .add .x .x22 .x22 .x9] s = some s' ∧
      s'.gpr .x23 = BitVec.ofNat 64 (left - m) ∧ s'.gpr .x22 = P + BitVec.ofNat 64 (16 * m) ∧
      (∀ r, r ≠ .x9 → r ≠ .x22 → r ≠ .x23 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [cOff, hs, rs], ?_⟩
  refine ⟨?_, ?_, fun r h₁ h₂ h₃ => by simp [gpr_write, h₁, h₂, h₃], rfl, rfl, rfl, rfl⟩
  · simp only [gpr_write, reduceCtorEq, ↓reduceIte, h23, hm, BitVec.setWidth_eq]
    rw [Offset.ofNat_sub_ofNat hml]
  · simp only [gpr_write, ↓reduceIte, h22, hm, BitVec.setWidth_eq]
    congr 1
    apply BitVec.eq_of_toNat_eq
    have hm' : m < 2 ^ 64 := by omega
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm', Nat.shiftLeft_eq]
    omega

theorem advB_ok (s : State) {Q : Addr} (hq : s.gpr .x21 = Q)
    (rq : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 12) 4) :
    ∃ s', runBlock isa [.ldr .w .x9 .x21 12] s = some s' ∧
      s'.read .w .x9 = s.mem.readW (Q + BitVec.ofNat 64 12) 32 ∧
      (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by crun [read4, hq, rq], ?_⟩
  refine ⟨?_, fun r hr => by simp [gpr_write, hr], rfl, rfl, rfl, rfl⟩
  simp only [State.read, gpr_write, ite_true]
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

/-- The counter block plus `2³²`: a carry into its first 96 bits. -/
theorem carry_ok (s : State) {Q : Addr} (hq : s.gpr .x21 = Q)
    (r0 : InRegions (s.rd ++ s.wr) Q 8) (r8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (w0 : InRegions s.wr Q 8) (w8 : InRegions s.wr (Q + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa carry s = some s' ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      bytesAt s'.mem Q 16 = Spec.Ctr.ofNat (Spec.Ctr.toNat (bytesAt s.mem Q 16) + 2 ^ 32) 16 ∧
      Frame [⟨Q, 16⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [carry, gpr_addWithCarry, c_addWithCarry, c_write, mem_addWithCarry, rd_addWithCarry,
    wr_addWithCarry, sp_addWithCarry, hq, r0, r8, w0, w8], ?_⟩
  refine ⟨fun r h₁ h₂ h₃ h₄ => by simp [gpr_write, gpr_addWithCarry, h₁, h₂, h₃, h₄], rfl, ?_, ?_, rfl, rfl⟩
  · have e : ((1 : BitVec 16).setWidth 64 <<< 32 : BitVec 64).toNat = 2 ^ 32 := by decide
    have r : ∀ x, rv64 x = rev64 x := fun _ => rfl
    apply AesCtr.add_words64
    · rw [r]
      generalize rev64 (s.mem.readW (Q + BitVec.ofNat 64 8) 64) = L
      rw [BitVec.toNat_add, BitVec.toNat_add, e, Bool.toNat_false, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero,
        Nat.mod_mod]
    · rw [r, r]
      generalize rev64 (s.mem.readW (Q + BitVec.ofNat 64 8) 64) = L
      generalize rev64 (s.mem.readW Q 64) = H
      have hL := L.isLt
      have e₀ : ((0 : BitVec 16).setWidth 64 <<< 0 : BitVec 64).toNat = 0 := by decide
      rw [BitVec.toNat_add, BitVec.toNat_add, e₀, e, BitVec.toNat_ofNat]
      by_cases h : 2 ^ 64 ≤ L.toNat + 2 ^ 32 + (false).toNat
      · rw [decide_eq_true h]
        simp only [Bool.toNat_false, Bool.toNat_true] at h ⊢
        rw [show (L.toNat + 2 ^ 32) / 2 ^ 64 = 1 by omega]
        omega
      · rw [decide_eq_false h]
        simp only [Bool.toNat_false] at h ⊢
        rw [show (L.toNat + 2 ^ 32) / 2 ^ 64 = 0 by omega]
        omega
  · refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base Q (d := 8) (n := 8) (k := 16) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ ?_
    simpa using Offset.contains_base Q (d := 0) (n := 8) (k := 16) (by decide) (by decide)

end VG.Proof.AesCtr.AArch64
