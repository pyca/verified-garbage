import VerifiedGarbage.Proof.AesOcb.AArch64.Env
import VerifiedGarbage.Proof.CmacAes.AArch64.Subkeys

/-!
# AES-OCB on AArch64: blocks of `W`, two words at a time

Untrusted: everything here is checked by Lean. `zero16`, `copy16`, `xor16`
and `dbl` write a block of `W` (`BlkStep`): zeros, a copy, the XOR with a
block and `double` of a block (`zero16_ok`, `copy16_ok`, `xor16_ok`,
`dbl_ok`), as blocks of memory (`blockAtMem`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Ocb (Block blockAtMem double)
open VG.Proof.Cmac (le8 le8_readW xor_words bytesAt_store2)
open VG.Proof.AesGcm.AArch64 (in_left)

/-- What a step writing the block at `W + d` does: it writes only there,
the block `v`, and keeps the registers but `clob`. -/
structure BlkStep (W : Addr) (d : Nat) (v : Block) (clob : List Reg) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 d, 16⟩] s.mem s'.mem
  val : blockAtMem s'.mem (W + BitVec.ofNat 64 d) = v
  gpr : ∀ r, r ∉ clob → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

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

theorem addr8 (p : Addr) (d : Nat) : p + BitVec.ofNat 64 d + BitVec.ofNat 64 8 = p + BitVec.ofNat 64 (d + 8) :=
  Offset.add_add p d 8

theorem imm0 : BitVec.setWidth 64 (BitVec.ofNat 16 0) <<< (16 * 0) = (0 : BitVec 64) := by decide

/-- `zero16 d`: `W + d ← 0`. -/
theorem zero16_ok {W : Addr} {s : State} {d : Nat} (hd : d % 8 = 0 ∧ d + 8 < 32768) (h19 : s.gpr .x19 = W)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    ∃ s', runBlock isa (zero16 d) s = some s' ∧ BlkStep W d 0 [.x9] s s' := by
  refine ⟨_, by orun [zero16, h19, w₀, w₁, hd.1, Nat.add_mod_right, show d < 32768 by omega, hd.2], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [imm0]; rw [← addr8 W d]; exact Proof.Cmac.frame_store2 _ _ _
  · simp only [imm0]; rw [← addr8 W d, blockAtMem_store2]; decide
  · simp only [List.mem_singleton] at hr
    simp only [gpr_write, hr, ite_false]

/-- `copy16 a d`: `W + d ← W + a`. -/
theorem copy16_ok {W : Addr} {s : State} {a d : Nat} (ha : a % 8 = 0 ∧ a + 8 < 32768)
    (hd : d % 8 = 0 ∧ d + 8 < 32768) (h19 : s.gpr .x19 = W)
    (r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 a) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (a + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    ∃ s', runBlock isa (copy16 a d) s = some s' ∧
      BlkStep W d (blockAtMem s.mem (W + BitVec.ofNat 64 a)) [.x9, .x10] s s' := by
  refine ⟨_, by orun [copy16, h19, r₀, r₁, w₀, w₁, ha.1, hd.1, Nat.add_mod_right, show a < 32768 by omega,
    show d < 32768 by omega, ha.2, hd.2], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [← addr8 W d]; exact Proof.Cmac.frame_store2 _ _ _
  · rw [← addr8 W d, blockAtMem_store2, ← addr8 W a, blockAtMem_words]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2, ite_false]

/-- `xor16 b a d`: `W + d ← W + d ⊕ (B + a)`, `B` in `b`. -/
theorem xor16_ok {W B : Addr} {s : State} {b : Reg} {a d : Nat} (ha : a % 8 = 0 ∧ a + 8 < 32768)
    (hd : d % 8 = 0 ∧ d + 8 < 32768) (h19 : s.gpr .x19 = W) (hb : s.gpr b = B)
    (hb9 : b ≠ .x9) (hb10 : b ≠ .x10) (hb11 : b ≠ .x11)
    (r₀ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 a) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (a + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    ∃ s', runBlock isa (xor16 b a d) s = some s' ∧
      BlkStep W d (blockAtMem s.mem (W + BitVec.ofNat 64 d) ^^^ blockAtMem s.mem (B + BitVec.ofNat 64 a))
        [.x9, .x10, .x11, .x12] s s' := by
  have v₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) 8 := in_left w₀
  have v₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (d + 8)) 8 := in_left w₁
  refine ⟨_, by orun [xor16, h19, hb, hb9, hb10, hb11, r₀, r₁, v₀, v₁, w₀, w₁, ha.1, hd.1, Nat.add_mod_right,
    show a < 32768 by omega, show d < 32768 by omega, ha.2, hd.2], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [← addr8 W d]; exact Proof.Cmac.frame_store2 _ _ _
  · rw [← addr8 W d, blockAtMem_store2, ← addr8 B a, blockAtMem_xor_words]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- `double` of the block at `p`, from its byte-reversed words. -/
theorem dbl_mem (m : Mem) (p : Addr) :
    let hi := rev64 (m.readW p 64)
    let lo := rev64 (m.readW (p + BitVec.ofNat 64 8) 64)
    Spec.Ocb.ofBytes (le8 (rev64 (Proof.CmacAes.AArch64.dblHi hi lo)) ++
      le8 (rev64 (Proof.CmacAes.AArch64.dblLo hi lo))) = double (blockAtMem m p) := by
  intro hi lo
  rw [Proof.CmacAes.AArch64.le8_rev, ← Proof.Ocb.toBytes_eq, Proof.Ocb.ofBytes_toBytes,
    Proof.CmacAes.AArch64.dbl_words, Proof.Ocb.double_eq]
  congr 1
  have e0 : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p
  have := Proof.Gcm.AArch64.blockAt_rev m p
  rw [e0] at this
  exact this

/-- `dbl b a d`: `W + d ← double(B + a)`, `B` in `b`. -/
theorem dbl_ok {W B : Addr} {s : State} {b : Reg} {a d : Nat} (ha : a % 8 = 0 ∧ a + 8 < 32768)
    (hd : d % 8 = 0 ∧ d + 8 < 32768) (h19 : s.gpr .x19 = W) (hb : s.gpr b = B) (hb9 : b ≠ .x9)
    (r₀ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 a) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (a + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    ∃ s', runBlock isa (dbl b a d) s = some s' ∧
      BlkStep W d (double (blockAtMem s.mem (B + BitVec.ofNat 64 a))) [.x9, .x10, .x11, .x12, .x13] s s' := by
  refine ⟨_, by orun [dbl, h19, hb, hb9, r₀, r₁, w₀, w₁, ha.1, hd.1, Nat.add_mod_right,
    show a < 32768 by omega, show d < 32768 by omega, ha.2, hd.2], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [← addr8 W d]; exact Proof.Cmac.frame_store2 _ _ _
  · rw [← addr8 W d, blockAtMem_store2, ← addr8 B a]
    exact dbl_mem _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

end VG.Proof.AesOcb.AArch64
