module

public import VerifiedGarbage.Impl.AesXts.PPC64LEUnit
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Loop
public import VerifiedGarbage.Proof.AesXts.Unit
public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.AesXts.PPC64LE.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Cmac.Mem
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.AesCbc.PPC64LE
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.AesCbc.Spec
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Aes
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# XTS-AES of data units on PPC64LE: the code between the calls

Each straight-line piece of `encrypt` and `decrypt`, run once, with the
registers and memory it leaves, and the swap loop (`swap_wp`), which leaves
`swapMem` (`Proof/AesXts/Unit.lean`). None of them changes the stack
pointer (`Exec.sp`).
-/

@[expose] public section

namespace VG.Proof.AesXts.PPC64LE.Unit

open VG VG.PPC64LE VG.Impl.AesXts.PPC64LEUnit
open VG.Impl.AesCbc.PPC64LE (mov copy)
open VG.Proof.AesXts.Unit (swapMem swapMem_step swapMem_lo swapMem_hi)
open VG.Spec.Aes (bytesAt)

theorem preserved_ne (r : Reg) (hr : r ∈ preserved) :
    r ≠ .r0 ∧ r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧
      r ≠ .r11 ∧ r ≠ .r12 := by
  revert hr; cases r <;> decide

theorem shr4 (x : BitVec 64) : x >>> 4 = BitVec.ofNat 64 (x.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := x.isLt; omega)]

theorem shr4_shl4 (x : BitVec 64) : (x >>> 4) <<< 4 = BitVec.ofNat 64 (16 * (x.toNat / 16)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  simp only [Nat.reducePow]
  omega

theorem read1 (m : Mem) (a : Addr) : m.read a 1 = m a := by
  have := Mem.extractLsb'_read m a (n := 1) (j := 0) (by decide)
  rw [BitVec.add_zero] at this
  rw [← this]
  exact (BitVec.extractLsb'_eq_self (x := m.read a 1)).symm

theorem write1 (m : Mem) (a : Addr) (v : BitVec (8 * 1)) : m.write a 1 v = m.writeW a v := by
  simp [Mem.writeW]

theorem byte_rt (b : Byte) : (b.setWidth 64).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `lbz t, off(n)`. -/
theorem wp_lbz {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' t ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.lbz t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t ((s.mem a).setWidth 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_lbz hn ho (by rw [ha]; exact hin), ha, read1]

/-- `stb t, off(n)`. -/
theorem wp_stb {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.stb t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 8) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl⟩)
  rw [exec_stb hn ho (by rw [ha]; exact hout), ha, write1]

end

/-! ## Registers only -/

theorem setup_wp (s : State) :
    WP isa (.block setup) s fun s' =>
      s'.gpr .r14 = s.gpr .r3 ∧ s'.gpr .r15 = s.gpr .r5 ∧ s'.gpr .r17 = s.gpr .r7 ∧
      s'.gpr .r18 = s.gpr .r8 ∧ s'.gpr .r19 = s.gpr .r9 ∧
      (∀ r, r ≠ .r14 → r ≠ .r15 → r ≠ .r17 → r ≠ .r18 → r ≠ .r19 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold setup mov
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_mr fun s₃ u₃ => wp_mr fun s₄ u₄ =>
    wp_mr fun s₅ u₅ => wp_nil ⟨?_, ?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ h₅ => ?_, ?_, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide)]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide)]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]
  · rw [u₅.other _ h₅, u₄.other _ h₄, u₃.other _ h₃, u₂.other _ h₂, u₁.other _ h₁]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

theorem tArgs_wp (s : State) :
    WP isa (.block tArgs) s fun s' =>
      s'.gpr .r3 = s.gpr .r4 ∧ s'.gpr .r4 = s.gpr .r15 ∧
      s'.gpr .r5 = s.gpr .r19 + BitVec.ofNat 64 zO ∧ s'.gpr .r6 = s.gpr .r19 + BitVec.ofNat 64 tO ∧
      s'.gpr .r7 = BitVec.ofNat 64 1 ∧ s'.gpr .r8 = s.gpr .r19 ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold tArgs mov
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_addi (by decide) (by decide) fun s₃ u₃ =>
    wp_addi (by decide) (by decide) fun s₄ u₄ => wp_li (by decide) fun s₅ u₅ => wp_mr fun s₆ u₆ =>
    wp_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.gpr]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · obtain ⟨-, h3, h4, h5, h6, h7, h8, -⟩ := preserved_ne r hr
    rw [u₆.other _ h8, u₅.other _ h7, u₄.other _ h6, u₃.other _ h5, u₂.other _ h4, u₁.other _ h3]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

theorem argsAll_wp' (s : State) :
    WP isa (.block argsAll) s fun s' =>
      s'.gpr .r3 = s.gpr .r14 ∧ s'.gpr .r4 = s.gpr .r15 ∧
      s'.gpr .r5 = s.gpr .r19 + BitVec.ofNat 64 tO ∧ s'.gpr .r6 = s.gpr .r17 ∧
      s'.gpr .r7 = BitVec.ofNat 64 ((s.gpr .r18).toNat / 16) ∧ s'.gpr .r8 = s.gpr .r19 ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold argsAll mov
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_addi (by decide) (by decide) fun s₃ u₃ =>
    wp_mr fun s₄ u₄ => wp_lsr (by decide) fun s₅ u₅ => wp_mr fun s₆ u₆ =>
    wp_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), shr4]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · obtain ⟨-, h3, h4, h5, h6, h7, h8, -⟩ := preserved_ne r hr
    rw [u₆.other _ h8, u₅.other _ h7, u₄.other _ h6, u₃.other _ h5, u₂.other _ h4, u₁.other _ h3]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

theorem argsHead_wp' (s : State) (hm : 1 ≤ (s.gpr .r18).toNat / 16) :
    WP isa (.block argsHead) s fun s' =>
      s'.gpr .r3 = s.gpr .r14 ∧ s'.gpr .r4 = s.gpr .r15 ∧
      s'.gpr .r5 = s.gpr .r19 + BitVec.ofNat 64 tO ∧ s'.gpr .r6 = s.gpr .r17 ∧
      s'.gpr .r7 = BitVec.ofNat 64 ((s.gpr .r18).toNat / 16 - 1) ∧ s'.gpr .r8 = s.gpr .r19 ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [argsHead, WP.block_append_iff]
  refine WP.mono (argsAll_wp' s) fun s₁ ⟨r3, r4, r5, r6, r7, r8, cs, mem, rd, wr⟩ =>
    wp_subi (by decide) (by decide) fun s₂ u₂ => wp_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [u₂.other _ (by decide), r3]
  · rw [u₂.other _ (by decide), r4]
  · rw [u₂.other _ (by decide), r5]
  · rw [u₂.other _ (by decide), r6]
  · rw [u₂.gpr, r7]; exact Offset.ofNat_sub_ofNat hm
  · rw [u₂.other _ (by decide), r8]
  · rw [u₂.other _ (preserved_ne r hr).2.2.2.2.2.1, cs r hr]
  · rw [u₂.mem, mem]
  · rw [u₂.rd, rd]
  · rw [u₂.wr, wr]

theorem split_wp' (s : State) :
    WP isa (.block split) s fun s' =>
      s'.gpr .r10 = BitVec.ofNat 64 (16 * ((s.gpr .r18).toNat / 16)) ∧
      s'.gpr .r11 = BitVec.ofNat 64 ((s.gpr .r18).toNat % 16) ∧
      (∀ r, r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e : s.gpr .r18 - BitVec.ofNat 64 (16 * ((s.gpr .r18).toNat / 16)) =
      BitVec.ofNat 64 ((s.gpr .r18).toNat % 16) := by
    apply BitVec.eq_of_toNat_eq
    have := (s.gpr .r18).isLt
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * _) (by omega),
      Nat.mod_eq_of_lt (a := _ % 16) (by omega)]
    omega
  unfold split
  refine wp_lsr (by decide) fun s₁ u₁ => wp_lsl (by decide) fun s₂ u₂ => wp_sub fun s₃ u₃ =>
    wp_nil ⟨?_, ?_, fun r h₁ h₂ => ?_, ?_, ?_, ?_⟩
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, shr4_shl4]
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), u₂.gpr, u₁.gpr, shr4_shl4, e]
  · rw [u₃.other _ h₂, u₂.other _ h₁, u₁.other _ h₁]
  · rw [u₃.mem, u₂.mem, u₁.mem]
  · rw [u₃.rd, u₂.rd, u₁.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr]

theorem lastAddr_wp' (s : State) :
    WP isa (.block lastAddr) s fun s' => s'.gpr .r12 = s.gpr .r17 + s.gpr .r10 - BitVec.ofNat 64 16 ∧
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold lastAddr
  refine wp_add fun s₁ u₁ => wp_subi (by decide) (by decide) fun s₂ u₂ =>
    wp_nil ⟨?_, fun r h => ?_, ?_, ?_, ?_⟩
  · rw [u₂.gpr, u₁.gpr]
  · rw [u₂.other _ h, u₁.other _ h]
  · rw [u₂.mem, u₁.mem]
  · rw [u₂.rd, u₁.rd]
  · rw [u₂.wr, u₁.wr]

/-- The last whole block, from the bytes of the whole blocks. -/
theorem last_eq (p : Addr) {m : Nat} (hm : 1 ≤ m) :
    p + BitVec.ofNat 64 (16 * m) - BitVec.ofNat 64 16 = p + BitVec.ofNat 64 (16 * (m - 1)) := by
  rw [show 16 * m = 16 * (m - 1) + 16 by omega, ← Offset.add_add]
  exact BitVec.add_sub_cancel _ _

theorem argsL_wp' (s : State) {o : Nat} (ho : o < 2 ^ 15) :
    WP isa (.block (argsL o)) s fun s' =>
      s'.gpr .r3 = s.gpr .r14 ∧ s'.gpr .r4 = s.gpr .r15 ∧
      s'.gpr .r5 = s.gpr .r19 + BitVec.ofNat 64 o ∧ s'.gpr .r6 = s.gpr .r17 + s.gpr .r10 - BitVec.ofNat 64 16 ∧
      s'.gpr .r7 = BitVec.ofNat 64 1 ∧ s'.gpr .r8 = s.gpr .r19 ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold argsL mov
  refine wp_add fun s₁ u₁ => wp_subi (by decide) (by decide) fun s₂ u₂ => wp_mr fun s₃ u₃ =>
    wp_mr fun s₄ u₄ => wp_addi (by decide) ho fun s₅ u₅ => wp_li (by decide) fun s₆ u₆ =>
    wp_mr fun s₇ u₇ => wp_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.gpr]
  · rw [u₇.other _ (by decide), u₆.gpr]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · obtain ⟨-, h3, h4, h5, h6, h7, h8, -⟩ := preserved_ne r hr
    rw [u₇.other _ h8, u₆.other _ h7, u₅.other _ h5, u₄.other _ h4, u₃.other _ h3, u₂.other _ h6,
      u₁.other _ h6]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-! ## Memory -/

/-- The memory after zeroing the block at `c`. -/
def zero2 (m : Mem) (c : Addr) : Mem := (m.writeW c (0 : BitVec 64)).writeW (c + BitVec.ofNat 64 8) (0 : BitVec 64)

theorem zero2_frame (m : Mem) (c : Addr) : Frame [⟨c, 16⟩] m (zero2 m c) := AesCbc.frame_store2 _ _ _

theorem zero2_bytes (m : Mem) (c : Addr) : bytesAt (zero2 m c) c 16 = List.replicate 16 0 := by
  rw [zero2, Proof.Cmac.bytesAt_store2]; decide

theorem zeroZ_wp (s : State) {Z : Addr} (hz : s.gpr .r19 + BitVec.ofNat 64 zO = Z)
    (hz8 : s.gpr .r19 + BitVec.ofNat 64 (zO + 8) = Z + BitVec.ofNat 64 8)
    (w0 : InRegions s.wr Z 8) (w8 : InRegions s.wr (Z + BitVec.ofNat 64 8) 8) :
    WP isa (.block zeroZ) s fun s' => (∀ r, r ≠ .r9 → s'.gpr r = s.gpr r) ∧
      s'.mem = zero2 s.mem Z ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold zeroZ
  refine wp_li (by decide) fun s₁ u₁ => ?_
  refine wp_std (by decide) (by decide) (by rw [u₁.other _ (by decide), hz]) (by rw [u₁.wr]; exact w0)
    fun s₂ u₂ => ?_
  refine wp_std (by decide) (by decide) (by rw [u₂.gpr, u₁.other _ (by decide), hz8])
    (by rw [u₂.wr, u₁.wr]; exact w8) fun s₃ u₃ => wp_nil ⟨fun r h => ?_, ?_, ?_, ?_⟩
  · rw [u₃.gpr, u₂.gpr, u₁.other _ h]
  · rw [u₃.mem, u₂.gpr, u₂.mem, u₁.gpr, u₁.mem]; rfl
  · rw [u₃.rd, u₂.rd, u₁.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr]

/-! ## The swap -/

theorem swapStep_wp (s : State) {L : Addr} {k b : Nat} (hx : s.gpr .r12 = L + BitVec.ofNat 64 k)
    (hc : s.gpr .r11 = BitVec.ofNat 64 b) (hb : 1 ≤ b)
    (w₀ : InRegions s.wr (L + BitVec.ofNat 64 k) 1) (w₁ : InRegions s.wr (L + BitVec.ofNat 64 (16 + k)) 1) :
    WP isa (.block swapBody) s fun s' =>
      s'.mem = (s.mem.writeW (L + BitVec.ofNat 64 k) (s.mem (L + BitVec.ofNat 64 (16 + k)))).writeW
        (L + BitVec.ofNat 64 (16 + k)) (s.mem (L + BitVec.ofNat 64 k)) ∧
      s'.gpr .r12 = L + BitVec.ofNat 64 (k + 1) ∧ s'.gpr .r11 = BitVec.ofNat 64 (b - 1) ∧
      (∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r11 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₀ : InRegions (s.rd ++ s.wr) (L + BitVec.ofNat 64 k) 1 :=
    let ⟨r, hr, c⟩ := w₀; ⟨r, List.mem_append_right _ hr, c⟩
  have r₁ : InRegions (s.rd ++ s.wr) (L + BitVec.ofNat 64 (16 + k)) 1 :=
    let ⟨r, hr, c⟩ := w₁; ⟨r, List.mem_append_right _ hr, c⟩
  have e16 : L + BitVec.ofNat 64 k + BitVec.ofNat 64 16 = L + BitVec.ofNat 64 (16 + k) := by
    rw [Offset.add_add, Nat.add_comm]
  unfold swapBody
  refine wp_lbz (a := L + BitVec.ofNat 64 k) (by decide) (by decide) (by rw [hx]; simp) r₀ fun s₁ u₁ => ?_
  refine wp_lbz (a := L + BitVec.ofNat 64 (16 + k)) (by decide) (by decide) (by rw [u₁.other _ (by decide), hx, e16])
    (by rw [u₁.rd, u₁.wr]; exact r₁) fun s₂ u₂ => ?_
  refine wp_stb (a := L + BitVec.ofNat 64 k) (by decide) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hx]; simp)
    (by rw [u₂.wr, u₁.wr]; exact w₀) fun s₃ u₃ => ?_
  refine wp_stb (a := L + BitVec.ofNat 64 (16 + k)) (by decide) (by decide)
    (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hx, e16])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact w₁) fun s₄ u₄ => ?_
  refine wp_addi (by decide) (by decide) fun s₅ u₅ => wp_subi (by decide) (by decide) fun s₆ u₆ =>
    wp_nil ⟨?_, ?_, ?_, fun r h₈ h₉ h₁₁ h₁₂ => ?_, ?_, ?_⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₃.mem, u₂.gpr, u₂.other _ (by decide : Reg.r8 ≠ .r9), u₂.mem,
      u₁.gpr, u₁.mem, byte_rt, byte_rt]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hx,
      Offset.add_add]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hc]
    exact Offset.ofNat_sub_ofNat hb
  · rw [u₆.other _ h₁₁, u₅.other _ h₁₂, u₄.gpr, u₃.gpr, u₂.other _ h₉, u₁.other _ h₈]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

theorem swap_wp (s : State) {L : Addr} {b : Nat} (hb₀ : 0 < b) (hb : b < 16) (hx : s.gpr .r12 = L)
    (hc : s.gpr .r11 = BitVec.ofNat 64 b) (hw : ∀ i < 16 + b, InRegions s.wr (L + BitVec.ofNat 64 i) 1) :
    WP isa swap s fun s' => s'.mem = swapMem s.mem L b ∧
      (∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r11 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block swapBody) (c := .nonzero .d .r11)
    (fun (n : Nat) (t : State) => ∃ k, n = b - k ∧ k < b ∧ t.gpr .r12 = L + BitVec.ofNat 64 k ∧
      t.gpr .r11 = BitVec.ofNat 64 (b - k) ∧ t.mem = swapMem s.mem L k ∧
      (∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r11 → r ≠ .r12 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧
      t.wr = s.wr) ?_ (b - 0) _
    ⟨0, rfl, hb₀, by rw [hx, BitVec.add_zero], hc, (Proof.AesXts.Unit.swapMem_zero _ _).symm,
      fun _ _ _ _ _ => rfl, rfl, rfl⟩
  rintro n t ⟨k, rfl, hk, x12, x11, mem, g, rd, wr⟩
  refine WP.mono (swapStep_wp t (k := k) (b := b - k) x12 x11 (by omega) (by rw [wr]; exact hw k (by omega))
    (by rw [wr]; exact hw (16 + k) (by omega))) fun t' ⟨mem', x12', x11', g', rd', wr'⟩ => ?_
  have hmem : t'.mem = swapMem s.mem L (k + 1) := by
    rw [mem', mem, swapMem_lo _ _ (Nat.le_refl k) (by omega), swapMem_hi _ _ (Nat.le_refl k) (by omega),
      swapMem_step _ _ (by omega)]
  have hz := eval_nonzero_ofNat' t' .r11 (k := b - k - 1) (by omega) x11'
  have gg : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r11 → r ≠ .r12 → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ h₄ => by
    rw [g' r h₁ h₂ h₃ h₄, g r h₁ h₂ h₃ h₄]
  by_cases he : k + 1 = b
  · left
    refine ⟨by rw [hz]; simp [show b - k - 1 = 0 by omega], by rw [hmem, he], gg, by rw [rd', rd],
      by rw [wr', wr]⟩
  · right
    refine ⟨by rw [hz]; simp [show b - k - 1 ≠ 0 by omega], b - (k + 1), by omega, k + 1, rfl, by omega, x12',
      by rw [x11', show b - k - 1 = b - (k + 1) by omega], hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

/-! ## The next tweak -/

theorem nextT_wp (s : State) {T Z : Addr} (ht : s.gpr .r19 + BitVec.ofNat 64 tO = T)
    (ht8 : s.gpr .r19 + BitVec.ofNat 64 (tO + 8) = T + BitVec.ofNat 64 8)
    (hz : s.gpr .r19 + BitVec.ofNat 64 zO = Z) (hz8 : s.gpr .r19 + BitVec.ofNat 64 (zO + 8) = Z + BitVec.ofNat 64 8)
    (hd : (⟨Z, 16⟩ : Region).Disjoint ⟨T, 16⟩)
    (r0 : InRegions (s.rd ++ s.wr) T 8) (r8 : InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 8) 8)
    (w0 : InRegions s.wr Z 8) (w8 : InRegions s.wr (Z + BitVec.ofNat 64 8) 8) :
    WP isa (.block nextT) s fun s' =>
      (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → r ≠ .r16 → s'.gpr r = s.gpr r) ∧
      Frame [⟨Z, 16⟩] s.mem s'.mem ∧ bytesAt s'.mem Z 16 = Spec.Xts.mulAlpha (bytesAt s.mem T 16) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have rz0 : InRegions (s.rd ++ s.wr) Z 8 := let ⟨r, hr, c⟩ := w0; ⟨r, List.mem_append_right _ hr, c⟩
  have rz8 : InRegions (s.rd ++ s.wr) (Z + BitVec.ofNat 64 8) 8 :=
    let ⟨r, hr, c⟩ := w8; ⟨r, List.mem_append_right _ hr, c⟩
  rw [nextT, List.append_assoc, List.singleton_append]
  refine wp_addi (by decide) (by decide) fun s₁ u₁ => ?_
  have g19 : s₁.gpr .r19 = s.gpr .r19 := u₁.other _ (by decide)
  refine AesCbc.PPC64LE.copy_wp (dst := .r19) (src := .r19) (d := zO) (e := tO) (P := Z) (Q := T)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [g19, hz]) (by rw [g19, hz8]) (by rw [g19, ht]) (by rw [g19, ht8])
    (by rw [u₁.rd, u₁.wr]; exact r0) (by rw [u₁.rd, u₁.wr]; exact r8)
    (by rw [u₁.wr]; exact w0) (by rw [u₁.wr]; exact w8) fun s₂ g₂ mem₂ rd₂ wr₂ => ?_
  rw [← List.append_nil Impl.AesXts.PPC64LE.mulA]
  refine Proof.AesXts.PPC64LE.mulA_wp (Q := Z) (by rw [g₂ _ (by decide), u₁.gpr, hz])
    (by rw [rd₂, wr₂, u₁.rd, u₁.wr]; exact rz0) (by rw [rd₂, wr₂, u₁.rd, u₁.wr]; exact rz8)
    (by rw [wr₂, u₁.wr]; exact w0) (by rw [wr₂, u₁.wr]; exact w8) fun s₃ g₃ mem₃ rd₃ wr₃ => wp_nil ?_
  refine ⟨fun r h₉ h₁₀ h₁₁ h₁₂ h₁₆ => ?_, ?_, ?_, by rw [rd₃, rd₂, u₁.rd], by rw [wr₃, wr₂, u₁.wr]⟩
  · rw [g₃ r h₉ h₁₀ h₁₁ h₁₂, g₂ r h₉, u₁.other _ h₁₆]
  · rw [mem₃, mem₂, u₁.mem]
    exact (AesCbc.copyMem_frame _ _ _).trans (Proof.AesXts.PPC64LE.alphaMem_frame _ _)
  · rw [mem₃, Proof.AesXts.PPC64LE.alphaMem_bytes, mem₂, AesCbc.copyMem_bytes _ hd, u₁.mem]

end VG.Proof.AesXts.PPC64LE.Unit
