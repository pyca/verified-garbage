import VerifiedGarbage.Proof.AesOcb.X86_64.Run
import VerifiedGarbage.Proof.CmacAes.X86_64.Dbl

/-!
# AES-OCB on x86-64: blocks of `W`, two words at a time

Untrusted: everything here is checked by Lean. `zero16`, `copy16`, `xor16`
and `dbl` write a block of `W` (`BlkStep`; `dbl`, at any address in a
register): zeros, a copy, the XOR with a block and `double` of a block
(`zero16_ok`, `copy16_ok`, `xor16_ok`, `dbl_ok`), as blocks of memory
(`blockAtMem`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Ocb (Block blockAtMem double)
open VG.Proof.Cmac (le8 le8_readW xor_words bytesAt_store2)
open VG.Proof.AesCcm.X86_64 (in_left)

/-- What a step writing the block at `W + d` does: it writes only there,
the block `v`, and keeps the registers but `clob`. -/
structure BlkStep (W : Addr) (d : Nat) (v : Block) (clob : List Reg) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 d, 16⟩] s.mem s'.mem
  val : blockAtMem s'.mem (W + BitVec.ofNat 64 d) = v
  gpr : ∀ r, r ∉ clob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem frame_store2 (m : Mem) (p : Addr) (w₀ w₁ : BitVec 64) :
    Frame [⟨p, 16⟩] m ((m.writeW p w₀).writeW (p + BitVec.ofNat 64 8) w₁) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (by simpa using Offset.contains p (d := 0) (n := 8) (e := 0) (k := 16) (by decide) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _
    (by simpa using Offset.contains p (d := 8) (n := 8) (e := 0) (k := 16) (by decide) (by decide) (by decide))

theorem blockAtMem_store2 (m : Mem) (p : Addr) (w₀ w₁ : BitVec 64) :
    blockAtMem ((m.writeW p w₀).writeW (p + BitVec.ofNat 64 8) w₁) p = Spec.Ocb.ofBytes (le8 w₀ ++ le8 w₁) := by
  rw [blockAtMem, bytesAt_store2]

/-- The two words of a block, XORed with those of another, are the XOR of
the blocks. -/
theorem blockAtMem_xor_words (m : Mem) (p q : Addr) :
    Spec.Ocb.ofBytes (le8 (m.readW p 64 ^^^ m.readW q 64) ++
      le8 (m.readW (p + BitVec.ofNat 64 8) 64 ^^^ m.readW (q + BitVec.ofNat 64 8) 64)) =
      blockAtMem m p ^^^ blockAtMem m q := by
  rw [xor_words, ← Proof.Ocb.xor_eq, Proof.Ocb.ofBytes_xor (by simp [Spec.Aes.bytesAt])
    (by simp [Spec.Aes.bytesAt])]
  rfl

theorem blockAtMem_words (m : Mem) (p : Addr) :
    Spec.Ocb.ofBytes (le8 (m.readW p 64) ++ le8 (m.readW (p + BitVec.ofNat 64 8) 64)) = blockAtMem m p := by
  rw [le8_readW, le8_readW, ← Proof.Cmac.bytesAt_split]; rfl

theorem blockAtMem_zero : Spec.Ocb.ofBytes (le8 0 ++ le8 0) = 0 := by decide

theorem addr8 (p : Addr) (d : Nat) : p + BitVec.ofNat 64 d + BitVec.ofNat 64 8 = p + BitVec.ofNat 64 (d + 8) :=
  Offset.add_add p d 8

/-- `zero16 d`: `W + d ← 0`. -/
theorem zero16_ok {W : Addr} {s : State} {d : Nat} (h15 : s.gpr .r15 = W)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    ∃ s', runBlock isa (zero16 d) s = some s' ∧ BlkStep W d 0 [.rax] s s' := by
  refine ⟨_, by orun [zero16, h15, w₀, w₁], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl⟩
  · simp only [mem_setReg, mem_arithFlags, BitVec.xor_self]; rw [← addr8 W d]; exact frame_store2 _ _ _ _
  · simp only [mem_setReg, mem_arithFlags, BitVec.xor_self]; rw [← addr8 W d, blockAtMem_store2]; decide
  · simp only [List.mem_singleton] at hr
    simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]

/-- `copy16 a d`: `W + d ← W + a`. -/
theorem copy16_ok {W : Addr} {s : State} {a d : Nat} (h15 : s.gpr .r15 = W)
    (r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 a) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (a + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    ∃ s', runBlock isa (copy16 a d) s = some s' ∧
      BlkStep W d (blockAtMem s.mem (W + BitVec.ofNat 64 a)) [.rax, .rdx] s s' := by
  refine ⟨_, by orun [copy16, h15, r₀, r₁, w₀, w₁], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl⟩
  · simp only [mem_setReg]; rw [← addr8 W d]; exact frame_store2 _ _ _ _
  · simp only [mem_setReg]; rw [← addr8 W d, blockAtMem_store2, ← addr8 W a, blockAtMem_words]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2, ite_false]

/-- `xor16 b a d`: `W + d ← W + d ⊕ (B + a)`, `B` in `b`. -/
theorem xor16_ok {W B : Addr} {s : State} {b : Reg} {a d : Nat} (h15 : s.gpr .r15 = W) (hb : s.gpr b = B)
    (hba : b ≠ .rax) (hbd : b ≠ .rdx)
    (r₀ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 a) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (a + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    ∃ s', runBlock isa (xor16 b a d) s = some s' ∧
      BlkStep W d (blockAtMem s.mem (W + BitVec.ofNat 64 d) ^^^ blockAtMem s.mem (B + BitVec.ofNat 64 a))
        [.rax, .rdx] s s' := by
  have v₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) 8 := in_left w₀
  have v₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (d + 8)) 8 := in_left w₁
  refine ⟨_, by orun [xor16, h15, hb, hba, hbd, r₀, r₁, v₀, v₁, w₀, w₁], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl⟩
  · simp only [mem_setReg, mem_arithFlags]; rw [← addr8 W d]; exact frame_store2 _ _ _ _
  · simp only [mem_setReg, mem_arithFlags]
    rw [← addr8 W d, blockAtMem_store2, ← addr8 B a, blockAtMem_xor_words]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2, ite_false]

theorem mask87 : BitVec.signExtend 64 (0x87 : BitVec 32) = BitVec.ofNat 64 135 := by decide

/-- `double` of the block at `p`, from its byte-reversed words. -/
theorem dbl_mem (m : Mem) (p : Addr) :
    let hi := bswap64 (m.readW p 64)
    let lo := bswap64 (m.readW (p + BitVec.ofNat 64 8) 64)
    Spec.Ocb.ofBytes (le8 (bswap64 ((hi + hi) ||| (lo >>> 63))) ++
      le8 (bswap64 ((lo + lo) ^^^ (((0 : BitVec 64) - (hi >>> 63)) &&& BitVec.ofNat 64 135)))) =
      double (blockAtMem m p) := by
  intro hi lo
  rw [Proof.CmacAes.X86_64.le8_bswap, ← Proof.Ocb.toBytes_eq, Proof.Ocb.ofBytes_toBytes, ← mask87,
    Proof.CmacAes.X86_64.dbl_words, Proof.Ocb.double_eq]
  congr 1
  have e0 : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p
  show hi ++ lo = Spec.Gcm.blockAt m p
  rw [← Proof.Gcm.X86_64.blockAt_bswap, e0]

/-- `dbl b a o d`: `O + d ← double(B + a)`, `B` in `b` and `O` in `o`. -/
theorem dbl_ok {W B : Addr} {s : State} {b o : Reg} {a d : Nat} (h15 : s.gpr o = W) (hb : s.gpr b = B)
    (hba : b ≠ .rax) (hoa : o ≠ .rax) (hod : o ≠ .rdx) (hoc : o ≠ .rcx) (ho8 : o ≠ .r8)
    (r₀ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 a) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (a + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    ∃ s', runBlock isa (dbl b a o d) s = some s' ∧
      BlkStep W d (double (blockAtMem s.mem (B + BitVec.ofNat 64 a))) [.rax, .rdx, .rcx, .r8] s s' := by
  refine ⟨_, by orun [dbl, h15, hb, hba, hoa, hod, hoc, ho8, r₀, r₁, w₀, w₁], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags]; rw [← addr8 W d]; exact frame_store2 _ _ _ _
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags, BitVec.xor_self]
    rw [← addr8 W d, blockAtMem_store2, ← addr8 B a]
    exact dbl_mem _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

end VG.Proof.AesOcb.X86_64
