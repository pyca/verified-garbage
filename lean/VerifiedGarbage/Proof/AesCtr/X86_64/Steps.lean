import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.AesCbc.X86_64.Body
import VerifiedGarbage.Impl.AesCtr.X86_64

/-!
# AES-CTR on x86-64: the code between the calls

The straight-line pieces of an iteration, run once each: the number of
blocks of the call (`count`, `min left (2³² − lo32 t)`), its arguments
(`args`), the advance past them with ZF set if the counter's last 32 bits
wrapped around (`adv`), and the carry into the first 96 bits (`carry`, whose
block is `t + 2³²`: `carryMem_bytes`).
-/

namespace VG.Proof.AesCtr.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCtr.X86_64
open VG.Impl.AesCbc.X86_64 (at_ cOff)
open VG.Proof.AesCbc.X86_64 (offset_nat)
open VG.Spec.Aes (bytesAt)

/-- The last 32 bits of the counter block at `Q`, as read and byte-reversed. -/
theorem lo32_bytesAt (m : Mem) (Q : Addr) :
    AesCtr.lo32 (bytesAt m Q 16) = (rv32 (m.readW (Q + BitVec.ofNat 64 12) 32)).toNat := by
  rw [AesCtr.lo32, show (16 : Nat) = 12 + 4 from rfl, AesCtr.bytesAt_append, AesCtr.toNat_append,
    AesCtr.bytesAt_rv32, AesCtr.toNat_ofNat, AesCtr.length_ofNat]
  have := (rv32 (m.readW (Q + BitVec.ofNat 64 12) 32)).isLt
  simp only [Nat.reducePow] at this ⊢
  omega

theorem countA_ok (s : State) {Q : Addr} (hq : s.gpr .r12 = Q)
    (rq : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 12) 4) :
    ∃ s', runBlock isa [.mov32 .rax (.mem (at_ .r12 12)), .bswap32 .rax] s = some s' ∧
      s'.gpr .rax = (rv32 (s.mem.readW (Q + BitVec.ofNat 64 12) 32)).setWidth 64 ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [runBlock_cons, at_, exec, readSrc32, State.load32, State.ea, offset_nat, State.setReg32, hq, rq]
    rfl, ?_⟩
  refine ⟨?_, fun r hr => by simp [gpr_setReg, State.setReg32, hr], rfl, rfl, rfl⟩
  simp only [gpr_setReg, ite_true, State.setReg32]
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  rfl

theorem sub32_toNat (c : BitVec 32) : (0x100000000 - c.setWidth 64 : BitVec 64).toNat = 2 ^ 32 - c.toNat := by
  have hc := c.isLt
  have h1 : (c.setWidth 64).toNat = c.toNat := by simp [BitVec.toNat_setWidth]; omega
  have h2 : (0x100000000 : BitVec 64).toNat = 2 ^ 32 := rfl
  rw [BitVec.toNat_sub, h1, h2]
  omega

theorem countB1_ok (s : State) {c : BitVec 32} (ha : s.gpr .rax = c.setWidth 64) :
    ∃ s', runBlock isa [.movImm64 .rcx 0x100000000, .alu .sub .rcx (.reg .rax)] s = some s' ∧
      s'.gpr .rcx = 0x100000000 - c.setWidth 64 ∧
      (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
    exact rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, ha]
  · intro r hr; simp [gpr_setReg, hr]
  all_goals rfl

theorem countB2_ok (s : State) {a b : BitVec 64} (h14 : s.gpr .r14 = a) (hc : s.gpr .rcx = b) :
    ∃ s', runBlock isa [.alu .cmp .r14 (.reg .rcx), .cmov .b .rcx (.reg .r14)] s = some s' ∧
      s'.gpr .rcx = (if a.toNat < b.toNat then a else b) ∧
      (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, execCmov, eval,
      cf_arithFlags, Option.bind_some, Option.map_some]
    exact rfl, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases h : a.toNat < b.toNat <;> simp [gpr_setReg, h14, hc, h]
  · intro r hr
    by_cases h : (s.gpr .r14).toNat < (s.gpr .rcx).toNat <;> simp [gpr_setReg, hr, h]
  all_goals
    by_cases h : (s.gpr .r14).toNat < (s.gpr .rcx).toNat <;> simp [h] <;> rfl

/-- The counter block plus `2³²`: a carry into its first 96 bits. -/
theorem carry_ok (s : State) {Q : Addr} (hq : s.gpr .r12 = Q)
    (r0 : InRegions (s.rd ++ s.wr) Q 8) (r8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (w0 : InRegions s.wr Q 8) (w8 : InRegions s.wr (Q + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa carry s = some s' ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      bytesAt s'.mem Q 16 = Spec.Ctr.ofNat (Spec.Ctr.toNat (bytesAt s.mem Q 16) + 2 ^ 32) 16 ∧
      Frame [⟨Q, 16⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, carry, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.store64, State.ea, offset_nat, execAlu, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, cf_setReg, cf_arithFlags, hq, BitVec.add_zero, r0, r8, w0, w8]
    exact rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro r h₁ h₂ h₃
    simp [gpr_setReg, h₁, h₂, h₃]
  · have e : (4294967296 : BitVec 64).toNat = 2 ^ 32 := rfl
    apply AesCtr.add_words64
    · rw [BitVec.toNat_add, e]; rfl
    · rw [show ∀ x, rv64 x = bswap64 x from fun _ => rfl, show ∀ x, rv64 x = bswap64 x from fun _ => rfl]
      generalize bswap64 (s.mem.readW (Q + BitVec.ofNat 64 8) 64) = L
      generalize bswap64 (s.mem.readW Q 64) = H
      have hL := L.isLt
      rw [BitVec.toNat_add, BitVec.toNat_add, e]
      have e₀ : (BitVec.signExtend 64 (0 : BitVec 32)).toNat = 0 := rfl
      rw [e₀]
      by_cases h : 2 ^ 64 ≤ L.toNat + 2 ^ 32
      · rw [show (L.toNat + 2 ^ 32) / 2 ^ 64 = 1 by omega]
        simp only [h, decide_true, BitVec.ofBool_true]
        have e₁ : (BitVec.setWidth 64 (1 : BitVec 1)).toNat = 1 := rfl
        rw [e₁]
        omega
      · rw [show (L.toNat + 2 ^ 32) / 2 ^ 64 = 0 by omega]
        simp only [h, decide_false, BitVec.ofBool_false]
        have e₁ : (BitVec.setWidth 64 (0 : BitVec 1)).toNat = 0 := rfl
        rw [e₁]
        omega
  · exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base Q (d := 8) (n := 8) (k := 16) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (by simpa using Offset.contains_base Q (d := 0) (n := 8) (k := 16) (by decide) (by decide))
  all_goals rfl


theorem args_ok (s : State) :
    ∃ s', runBlock isa args s = some s' ∧
      s'.gpr .rdi = s.gpr .rbx ∧ s'.gpr .rsi = s.gpr .rbp ∧ s'.gpr .rdx = s.gpr .r12 ∧
      s'.gpr .r8 = s.gpr .rcx ∧ s'.gpr .rcx = s.gpr .r13 ∧ s'.gpr .r9 = s.gpr .r15 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [args, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]; rfl, ?_⟩
  refine ⟨by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg],
    by simp [gpr_setReg], by simp [gpr_setReg], fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]

end VG.Proof.AesCtr.X86_64
