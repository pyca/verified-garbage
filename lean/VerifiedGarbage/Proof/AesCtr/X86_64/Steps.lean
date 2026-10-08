import VerifiedGarbage.Proof.AesCtr.Inc
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.AesCbc.X86_64.Body
import VerifiedGarbage.Impl.AesCtr.X86_64

/-!
# AES-CTR on x86-64: the code between the calls

The straight-line pieces of a block, run once each: the copy of the counter
block and the arguments of the call on it (`args`), the output block XORed
into the data block (`xorOut`), and the increment of the counter block
(`incr`, whose block is `Spec.Ctr.inc` of the one it read: `incr_bytes`).
-/

namespace VG.Proof.AesCtr.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCtr.X86_64
open VG.Impl.AesCbc.X86_64 (copy at_ cOff)
open VG.Proof.AesCbc (xorMem)
open VG.Proof.AesCbc.X86_64 (offset_nat)
open VG.Spec.Aes (bytesAt)

/-- The arguments of the call on the copy of the counter block. -/
def args : List Instr :=
  [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15), .alu .add .rdx (.imm cOff),
   .mov32 .rcx (.imm 1), .mov .r8 (.reg .r15)]

theorem pre_eq : pre = copy .r15 cOff .r12 0 ++ args := rfl

theorem args_ok (s : State) :
    ∃ s', runBlock isa args s = some s' ∧
      s'.gpr .rdi = s.gpr .rbx ∧ s'.gpr .rsi = s.gpr .rbp ∧
      s'.gpr .rdx = s.gpr .r15 + BitVec.ofNat 64 2048 ∧
      s'.gpr .rcx = 1 ∧ s'.gpr .r8 = s.gpr .r15 ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [args, cOff, runBlock_cons, runStep_some, exec, execAlu, readSrc, Option.map_some,
      Option.bind_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, State.setReg32]

/-- The block at `r13` XORed with the one in the scratch buffer. -/
theorem xorOut_ok (s : State) {P Q : Addr} (hp : s.gpr .r13 = P) (hq : s.gpr .r15 + BitVec.ofNat 64 2048 = Q)
    (hq8 : s.gpr .r15 + BitVec.ofNat 64 (2048 + 8) = Q + BitVec.ofNat 64 8)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rp8 : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 8) 8)
    (rq : InRegions (s.rd ++ s.wr) Q 8) (rq8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (wp : InRegions s.wr P 8) (wp8 : InRegions s.wr (P + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa xorOut s = some s' ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = xorMem s.mem P Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, xorOut, cOff, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc, State.load64, State.store64, State.ea, offset_nat, execAlu, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, hp, hq, hq8, BitVec.add_zero, rp, rp8, rq, rq8, wp, wp8]
    rfl, ?_⟩
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp [gpr_setReg, hr]

/-- The memory after `incr` on the block at `Q`. -/
def incMem (m : Mem) (Q : Addr) : Mem :=
  let lo := bswap64 (m.readW (Q + BitVec.ofNat 64 8) 64) + 1
  let hi := bswap64 (m.readW Q 64) + 0 +
    (BitVec.ofBool (decide (2 ^ 64 ≤ (bswap64 (m.readW (Q + BitVec.ofNat 64 8) 64)).toNat + 1))).setWidth 64
  (m.writeW (Q + BitVec.ofNat 64 8) (bswap64 lo)).writeW Q (bswap64 hi)

theorem incr_ok (s : State) {Q : Addr} (hq : s.gpr .r12 = Q)
    (r0 : InRegions (s.rd ++ s.wr) Q 8) (r8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (w0 : InRegions s.wr Q 8) (w8 : InRegions s.wr (Q + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa incr s = some s' ∧ (∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem = incMem s.mem Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, incr, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.store64, State.ea, offset_nat, execAlu, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, cf_setReg, cf_arithFlags, hq, BitVec.add_zero, r0, r8, w0, w8]
    rfl, ?_⟩
  refine ⟨fun r h₁ h₂ => ?_, rfl, rfl, rfl⟩
  simp [gpr_setReg, h₁, h₂]

theorem incMem_bytes (m : Mem) (Q : Addr) : bytesAt (incMem m Q) Q 16 = Spec.Ctr.inc (bytesAt m Q 16) := by
  have hL := (bswap64 (m.readW (Q + BitVec.ofNat 64 8) 64)).isLt
  have hH := (bswap64 (m.readW Q 64)).isLt
  apply AesCtr.inc_words64
  · show (bswap64 _ + 1).toNat = ((bswap64 _).toNat + 1) % 2 ^ 64
    rw [BitVec.toNat_add]; rfl
  · show (bswap64 _ + 0 + _).toNat = ((bswap64 _).toNat + ((bswap64 _).toNat + 1) / 2 ^ 64) % 2 ^ 64
    generalize bswap64 (m.readW (Q + BitVec.ofNat 64 8) 64) = L at *
    generalize bswap64 (m.readW Q 64) = H at *
    rw [BitVec.toNat_add, BitVec.toNat_add]
    by_cases h : 2 ^ 64 ≤ L.toNat + 1
    · rw [show (L.toNat + 1) / 2 ^ 64 = 1 by omega]
      simp only [h, decide_true, BitVec.ofBool_true]
      have e₀ : (0 : BitVec 64).toNat = 0 := rfl
      have e₁ : (BitVec.setWidth 64 (1 : BitVec 1)).toNat = 1 := rfl
      rw [e₀, e₁]
      omega
    · rw [show (L.toNat + 1) / 2 ^ 64 = 0 by omega]
      simp only [h, decide_false, BitVec.ofBool_false]
      have e₀ : (0 : BitVec 64).toNat = 0 := rfl
      have e₁ : (BitVec.setWidth 64 (0 : BitVec 1)).toNat = 0 := rfl
      rw [e₀, e₁]
      omega

theorem incMem_frame (m : Mem) (Q : Addr) : Frame [⟨Q, 16⟩] m (incMem m Q) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains_base Q (d := 8) (n := 8) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (by simpa using Offset.contains_base Q (d := 0) (n := 8) (k := 16) (by decide) (by decide))

end VG.Proof.AesCtr.X86_64
