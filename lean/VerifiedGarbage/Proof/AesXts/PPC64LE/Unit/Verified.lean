module

public import VerifiedGarbage.Impl.AesXts.PPC64LEUnit
public import VerifiedGarbage.Spec.Xts.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.AesXts.PPC64LE.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.AesXts.Unit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
import VerifiedGarbage.Proof.AesCbc.Mem
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Loop
public import VerifiedGarbage.Spec.Xts
public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.AesXts.Spec
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.AesXts.PPC64LE.Steps
import VerifiedGarbage.Proof.Cmac.Mem
public import VerifiedGarbage.Impl.AesCbc.PPC64LE
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.AesCbc.Spec
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Aes
meta import VerifiedGarbage.Proof.AesXts.Unit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.AesCbc.Mem
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.Loop
meta import VerifiedGarbage.Impl.AesXts.PPC64LEUnit
meta import VerifiedGarbage.Spec.Xts
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.AesXts.Spec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Xts.Contract
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.TCB.PPC64LE.Isa
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.AesXts.PPC64LE.Steps
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Impl.AesCbc.PPC64LE
meta import VerifiedGarbage.Proof.Aes.SboxSpec
meta import VerifiedGarbage.Proof.AesCbc.Spec
meta import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
meta import VerifiedGarbage.Proof.Framework.Inline
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Call
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Spec.Aes
meta import VerifiedGarbage.TCB.PPC64LE.Target

/-! ### `AesXts.PPC64LE.Unit.CT`, which only this module used -/

section

/-! ### `AesXts.PPC64LE.Unit.Dec`, which this module and modules that import it used -/

section

/-! ### `AesXts.PPC64LE.Unit.Enc`, which this module and modules that import it used -/

section

/-! ### `AesXts.PPC64LE.Unit.Steps`, which this module and modules that import it used -/

section

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
    Nat.mod_eq_of_lt (by have := x.isLt; omega_using [])]

theorem shr4_shl4 (x : BitVec 64) : (x >>> 4) <<< 4 = BitVec.ofNat 64 (16 * (x.toNat / 16)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [])]
  simp only [Nat.reducePow]
  omega_using []

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
  omega_using []

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
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * _) (by omega_using []),
      Nat.mod_eq_of_lt (a := _ % 16) (by omega_using [])]
    omega_using []
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
  rw [show 16 * m = 16 * (m - 1) + 16 by omega_using [hm], ← Offset.add_add]
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
  refine WP.mono (swapStep_wp t (k := k) (b := b - k) x12 x11 (by omega_using [hk]) (by rw [wr]; exact hw k (by omega_using [hk]))
    (by rw [wr]; exact hw (16 + k) (by omega_using [hk]))) fun t' ⟨mem', x12', x11', g', rd', wr'⟩ => ?_
  have hmem : t'.mem = swapMem s.mem L (k + 1) := by
    rw [mem', mem, swapMem_lo _ _ (Nat.le_refl k) (by omega_using [hb, hk]), swapMem_hi _ _ (Nat.le_refl k) (by omega_using [hb, hk]),
      swapMem_step _ _ (by omega_using [hb, hk])]
  have hz := eval_nonzero_ofNat' t' .r11 (k := b - k - 1) (by omega_using [hb]) x11'
  have gg : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r11 → r ≠ .r12 → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ h₄ => by
    rw [g' r h₁ h₂ h₃ h₄, g r h₁ h₂ h₃ h₄]
  by_cases he : k + 1 = b
  · left
    refine ⟨by rw [hz]; simp [show b - k - 1 = 0 by omega_using [he]], by rw [hmem, he], gg, by rw [rd', rd],
      by rw [wr', wr]⟩
  · right
    refine ⟨by rw [hz]; simp [show b - k - 1 ≠ 0 by omega_using [hk, he]], b - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hk, he], x12',
      by rw [x11', show b - k - 1 = b - (k + 1) by omega_using []], hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

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

end

end

/-! ### `AesXts.PPC64LE.Unit.Pre`, which this module and modules that import it used -/

section

/-! ### `AesXts.PPC64LE.Unit.Contract`, which this module and modules that import it used -/

section

/-!
# XTS-AES of data units on PPC64LE: the contract the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Xts/Contract.lean`, which imply `unitPPC64LE`
(`Verified.lean`): `(schedule = r3, tweak_schedule = r4, rounds = r5,
i = r6, data = r7, len = r8, scratch = r9)`. A call (`bl`) stores nothing in
memory, so no stack is used.

`UPre` names the facts of the precondition; the regions of the scratch
buffer (`tR`, `zR`, `wkR`, the slots of the saved registers) are apart from
each other and from everything else, as on AArch64
(`Proof/AesXts/AArch64/Unit/Enc.lean`).
-/

@[expose] public section

namespace VG.Proof.AesXts.PPC64LE.Unit

open VG VG.PPC64LE
open VG.Spec.Aes (bytesAt)

section
variable (s : State)

abbrev W : Addr := s.gpr .r3
abbrev K : Addr := s.gpr .r4
abbrev R : Nat := (s.gpr .r5).toNat
abbrev I : Addr := s.gpr .r6
abbrev D : Addr := s.gpr .r7
abbrev Len : Nat := (s.gpr .r8).toNat
abbrev S : Addr := s.gpr .r9

abbrev schR : Region := ⟨W s, 240⟩
abbrev tschR : Region := ⟨K s, 240⟩
abbrev iR : Region := ⟨I s, 16⟩
abbrev dataR : Region := ⟨D s, Len s⟩
abbrev scrR : Region := ⟨S s, 2432⟩

/-- The tweak, the second tweak, and the working space of the calls, in the
scratch buffer. -/
abbrev tR : Region := ⟨S s + BitVec.ofNat 64 Impl.AesXts.PPC64LEUnit.tO, 16⟩
abbrev zR : Region := ⟨S s + BitVec.ofNat 64 Impl.AesXts.PPC64LEUnit.zO, 16⟩
abbrev wkR : Region := ⟨S s, 2176⟩

/-- The number of whole blocks, the bytes after them, and the last whole block. -/
abbrev M : Nat := Len s / 16
abbrev B : Nat := Len s % 16
abbrev L : Addr := D s + BitVec.ofNat 64 (16 * (M s - 1))

end

/-- What the functions need: the permissions, the buffers apart, `rounds`
of 10, 12 or 14, and a data unit of 16 bytes to 2²⁰ blocks. -/
def unitPre (s : State) : Prop :=
  s.rd = [schR s, tschR s, iR s] ∧ s.wr = [dataR s, scrR s] ∧
    (schR s).Disjoint (dataR s) ∧ (schR s).Disjoint (scrR s) ∧ (tschR s).Disjoint (dataR s) ∧
    (tschR s).Disjoint (scrR s) ∧ (iR s).Disjoint (dataR s) ∧ (iR s).Disjoint (scrR s) ∧
    (dataR s).Disjoint (scrR s) ∧
    (I s).toNat + 16 ≤ 2 ^ 64 ∧ (D s).toNat + Len s ≤ 2 ^ 64 ∧ (S s).toNat + 2432 ≤ 2 ^ 64 ∧
    (R s = 10 ∨ R s = 12 ∨ R s = 14) ∧ 16 ≤ Len s ∧ Len s ≤ 16 * Spec.Xts.maxBlocks

/-- XTS-AES of the data unit in a direction. -/
def xtsOf : Bool → List Byte → List Byte → List Byte → Option (List Byte)
  | true => Spec.Xts.aesXtsEncrypt
  | false => Spec.Xts.aesXtsDecrypt

def unitPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.sp = s₂.sp

/-- `vg_aes_xts_encrypt_unit` (`enc`) or `vg_aes_xts_decrypt_unit`. -/
def unitPPC64LE (enc : Bool) : Contract isa where
  pre := unitPre
  post s s' := ∀ key, Spec.Xts.KeySchedules s.mem (s.gpr .r3) (s.gpr .r4) (s.gpr .r5).toNat key →
    xtsOf enc key (bytesAt s.mem (s.gpr .r6) 16) (bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) =
      some (bytesAt s'.mem (s.gpr .r7) (s.gpr .r8).toNat)
  pub := unitPub

/-- The precondition, by name. -/
structure UPre (s : State) : Prop where
  rd : s.rd = [schR s, tschR s, iR s]
  wr : s.wr = [dataR s, scrR s]
  sch_data : (schR s).Disjoint (dataR s)
  sch_scr : (schR s).Disjoint (scrR s)
  tsch_data : (tschR s).Disjoint (dataR s)
  tsch_scr : (tschR s).Disjoint (scrR s)
  i_data : (iR s).Disjoint (dataR s)
  i_scr : (iR s).Disjoint (scrR s)
  data_scr : (dataR s).Disjoint (scrR s)
  i_wrap : (I s).toNat + 16 ≤ 2 ^ 64
  data_wrap : (D s).toNat + Len s ≤ 2 ^ 64
  scr_wrap : (S s).toNat + 2432 ≤ 2 ^ 64
  rounds : R s = 10 ∨ R s = 12 ∨ R s = 14
  len_lo : 16 ≤ Len s
  len_hi : Len s ≤ 16 * Spec.Xts.maxBlocks

theorem UPre.of {s : State} (h : unitPre s) : UPre s :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩

/-! ## Regions -/

theorem sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x h => h₂ x (h₁ x h)

section
variable {s : State} (hp : UPre s)
include hp

theorem UPre.m_pos : 1 ≤ M s := by have := hp.len_lo; simp only [M]; omega_using [this]

omit hp in
theorem len_eq (s : State) : Len s = 16 * M s + B s := by simp only [M, B]; omega_using []

omit hp in
theorem scr_sub {d n : Nat} (h : d + n ≤ 2432) : Region.Sub ⟨S s + BitVec.ofNat 64 d, n⟩ (scrR s) :=
  Offset.sub_base _ h

omit hp in
theorem data_sub {d n : Nat} (h : d + n ≤ Len s) : Region.Sub ⟨D s + BitVec.ofNat 64 d, n⟩ (dataR s) :=
  Offset.sub_base _ h

omit hp in
theorem wk_sub : Region.Sub (wkR s) (scrR s) := Region.sub_prefix (by decide)

theorem UPre.t_wk : (tR s).Disjoint (wkR s) :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; simp only [Impl.AesXts.PPC64LEUnit.tO]; omega_using [])

theorem UPre.z_wk : (zR s).Disjoint (wkR s) :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; simp only [Impl.AesXts.PPC64LEUnit.zO]; omega_using [])

theorem UPre.t_z : (tR s).Disjoint (zR s) :=
  Offset.disjoint _ (by simp only [Impl.AesXts.PPC64LEUnit.tO, Impl.AesXts.PPC64LEUnit.zO]; omega_using [])
    (by have := hp.scr_wrap; simp only [Impl.AesXts.PPC64LEUnit.tO]; omega_using [])
    (by have := hp.scr_wrap; simp only [Impl.AesXts.PPC64LEUnit.zO]; omega_using [])

omit hp in
/-- The slots of the saved registers. -/
theorem slot_sub (d : Nat) (h₁ : 2208 ≤ d) (h₂ : d + 8 ≤ 2264) :
    Region.Sub ⟨S s + BitVec.ofNat 64 d, 8⟩ ⟨S s + BitVec.ofNat 64 2208, 56⟩ :=
  Offset.sub _ h₁ (by omega_using [h₂])

/-- Everything the code writes but the slots lies within the data or the
first 2208 bytes of the scratch buffer. -/
theorem UPre.slots_disj {r : Region} (hr : Region.Sub r (dataR s) ∨ Region.Sub r ⟨S s, 2208⟩) :
    (⟨S s + BitVec.ofNat 64 2208, 56⟩ : Region).Disjoint r := by
  have slot : Region.Sub ⟨S s + BitVec.ofNat 64 2208, 56⟩ (scrR s) := scr_sub (by decide)
  rcases hr with h | h
  · exact (hp.data_scr.symm.sub_left slot).sub_right h
  · exact (Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega_using [])).sub_right h

omit hp in
theorem t_sub : Region.Sub (tR s) ⟨S s, 2208⟩ := Offset.sub_base _ (by decide)
omit hp in
theorem z_sub : Region.Sub (zR s) ⟨S s, 2208⟩ := Offset.sub_base _ (by decide)
omit hp in
theorem s_sub : Region.Sub ⟨S s, 2208⟩ (scrR s) := Region.sub_prefix (by decide)

theorem UPre.l_sub : Region.Sub ⟨L s, 16⟩ (dataR s) := data_sub (by have := len_eq s; have := hp.m_pos; omega_arith)

theorem UPre.l_wrap : (L s).toNat + 16 ≤ 2 ^ 64 := by
  have := hp.data_wrap; have := len_eq s; have := hp.m_pos
  rw [L, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * (M s - 1)) (by omega),
    Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

end

/-! ## The parts of the data unit -/

section
variable {s : State} (hp : UPre s)
include hp

theorem UPre.wrapD : (D s).toNat + 16 * M s + B s ≤ 2 ^ 64 := by
  have := hp.data_wrap; have := len_eq s; omega_arith

omit hp in
theorem blocks_sub {N : Nat} (h : N ≤ M s) : Region.Sub ⟨D s, 16 * N⟩ (dataR s) :=
  Region.sub_prefix (by have := len_eq s; omega_using [h, this])

theorem UPre.lb_sub : Region.Sub ⟨L s, 16 + B s⟩ (dataR s) :=
  data_sub (by have := len_eq s; have := hp.m_pos; omega_arith)

theorem UPre.tl_eq : L s + 16 = D s + BitVec.ofNat 64 (16 * M s) := by
  rw [L, Proof.AesXts.Unit.add16, show 16 * (M s - 1) + 16 = 16 * M s by have := hp.m_pos; omega_using [this]]

theorem UPre.tl_sub : Region.Sub ⟨L s + 16, B s⟩ (dataR s) := by
  rw [hp.tl_eq]; exact data_sub (by have := len_eq s; omega_using [this])

theorem UPre.hd_lb : (⟨D s, 16 * (M s - 1)⟩ : Region).Disjoint ⟨L s, 16 + B s⟩ :=
  Offset.base_disjoint _ (Nat.le_refl _) (by have := hp.wrapD; have := hp.m_pos; omega_arith)

theorem UPre.hd_l : (⟨D s, 16 * (M s - 1)⟩ : Region).Disjoint ⟨L s, 16⟩ :=
  hp.hd_lb.sub_right (Region.sub_prefix (by omega_using []))

theorem UPre.hd_tl : (⟨D s, 16 * (M s - 1)⟩ : Region).Disjoint ⟨L s + 16, B s⟩ := by
  rw [hp.tl_eq]
  exact Offset.base_disjoint _ (by omega_using []) (by have := hp.wrapD; omega_using [this])

omit hp in
theorem tl_l : (⟨L s + 16, B s⟩ : Region).Disjoint ⟨L s, 16⟩ :=
  Offset.disjoint_base (L s) (d := 16) (n := B s) (k := 16) (Nat.le_refl _) (by simp only [B]; omega_using [])

theorem UPre.tl_blocks : (⟨L s + 16, B s⟩ : Region).Disjoint ⟨D s, 16 * M s⟩ := by
  rw [hp.tl_eq]
  exact Offset.disjoint_base _ (Nat.le_refl _) (by have := hp.wrapD; omega_using [this])

theorem UPre.l_hd : (⟨L s, 16⟩ : Region).Disjoint ⟨D s, 16 * (M s - 1)⟩ := hp.hd_l.symm

end

end VG.Proof.AesXts.PPC64LE.Unit

end

end

/-! ### `AesXts.PPC64LE.Unit.Call`, which this module and modules that import it used -/

section

/-!
# XTS-AES of data units on PPC64LE: a call of a whole-block function

`xts_call`: a call of `vg_aes_xts_encrypt` or `vg_aes_xts_decrypt` (`enc`
true or false) on `N` blocks at `D`, from the tweak at `T`, with working
space `S`, from its contract (`WP.call`): the blocks are then XTS of them,
the tweak the one after them, and only the tweak, the blocks and `S` change.
`xts_rel`: such calls, with the same arguments in both runs, are constant
time.
-/

@[expose] public section

namespace VG.Proof.AesXts.PPC64LE.Unit

open VG VG.PPC64LE
open VG.Proof.AesCbc.PPC64LE (modePPC64LE toNat_rounds)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesXts.Unit (blocks_bytesAt)
open VG.Spec.Aes (bytesAt)

/-- What a call of a whole-block function on `N` blocks needs. -/
structure XPre (s : State) (W T D S : Addr) (N R : Nat) : Prop where
  r3 : s.gpr .r3 = W
  r4 : s.gpr .r4 = BitVec.ofNat 64 R
  r5 : s.gpr .r5 = T
  r6 : s.gpr .r6 = D
  r7 : s.gpr .r7 = BitVec.ofNat 64 N
  r8 : s.gpr .r8 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  n : N < 2 ^ 60
  wt : (⟨W, 240⟩ : Region).Disjoint ⟨T, 16⟩
  wd : (⟨W, 240⟩ : Region).Disjoint ⟨D, 16 * N⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2176⟩
  td : (⟨T, 16⟩ : Region).Disjoint ⟨D, 16 * N⟩
  ts : (⟨T, 16⟩ : Region).Disjoint ⟨S, 2176⟩
  ds : (⟨D, 16 * N⟩ : Region).Disjoint ⟨S, 2176⟩
  wrapT : T.toNat + 16 ≤ 2 ^ 64
  wrapD : D.toNat + 16 * N ≤ 2 ^ 64
  wrapS : S.toNat + 2176 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩] ++ [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩] s.wr

/-- What a call of a whole-block function on `N` blocks leaves. -/
structure XPost (enc : Bool) (s : State) (W T D S : Addr) (N R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩] s.mem s'.mem
  out : Spec.Cbc.blocksAt s'.mem D N =
    Spec.Xts.crypt (ciphOf enc R (bytesAt s.mem W (16 * (R + 1)))) (bytesAt s.mem T 16)
      (Spec.Cbc.blocksAt s.mem D N)
  tw : bytesAt s'.mem T 16 = Spec.Xts.next (bytesAt s.mem T 16) N

theorem toNat_n {N : Nat} (h : N < 2 ^ 60) : (BitVec.ofNat 64 N).toNat = N := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [h])

theorem ce3 (s : State) : s.callEntry.gpr .r3 = s.gpr .r3 := s.callEntry_gpr (by decide)
theorem ce4 (s : State) : s.callEntry.gpr .r4 = s.gpr .r4 := s.callEntry_gpr (by decide)
theorem ce5 (s : State) : s.callEntry.gpr .r5 = s.gpr .r5 := s.callEntry_gpr (by decide)
theorem ce6 (s : State) : s.callEntry.gpr .r6 = s.gpr .r6 := s.callEntry_gpr (by decide)
theorem ce7 (s : State) : s.callEntry.gpr .r7 = s.gpr .r7 := s.callEntry_gpr (by decide)
theorem ce8 (s : State) : s.callEntry.gpr .r8 = s.gpr .r8 := s.callEntry_gpr (by decide)

/-- The whole-block function's precondition, on entry to a call with the
regions it is given. -/
theorem XPre.mode_pre {enc : Bool} {s : State} {W T D S : Addr} {N R : Nat} (h : XPre s W T D S N R) :
    (modePPC64LE (AesXts.xtsMode enc)).pre
      (s.callEntry.withRegions [⟨W, 240⟩] [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_n h.n
  simp only [modePPC64LE, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce3, ce4, ce5, ce6, ce7, ce8, h.r3, h.r4, h.r5, h.r6, h.r7, h.r8, hR, hN]
  exact ⟨trivial, trivial, h.wt, h.wd, h.ws, h.td, h.ts, h.ds, h.wrapT, h.wrapD, h.wrapS, h.rounds⟩

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) (hn : 16 * n ≤ 2 ^ 64) :
    Spec.Cbc.blocksAt m' p n = Spec.Cbc.blocksAt m p n := by
  rw [← blocks_bytesAt, ← blocks_bytesAt, Proof.Cmac.bytesAt_frame hf hd hn]

theorem xts_call (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (modePPC64LE (AesXts.xtsMode enc)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modePPC64LE (AesXts.xtsMode enc)).post s s')
    (nf : c.noFrames = true)
    {s : State} {W T D S : Addr} {N R : Nat} (h : XPre s W T D S N R) :
    WP isa (.call n c) s (XPost enc s W T D S N R) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_n h.n
  refine WP.call (k := modePPC64LE (AesXts.xtsMode enc)) ok (rd := [⟨W, 240⟩])
    (wr := [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩]) h.mode_pre h.reads h.writes ?_ nf
  intro s' hrd hwr hsp hf hsaved _ hpost
  simp only [modePPC64LE, AesXts.xtsMode, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    ce3, ce4, ce5, ce6, ce7, h.r3, h.r4, h.r5, h.r6, h.r7, hR, hN,
    Proof.AesXts.Unit.length_blocksAt] at hpost
  exact ⟨hrd, hwr, hsp, hsaved, hf, hpost.1, hpost.2⟩

/-- A call, with a contract whose regions may differ between the runs. -/
theorem relCT_callEx {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (s₁.callEntry.withRegions rd₁ wr₁) ∧ k.pre (s₂.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (s₁.rd ++ s₁.wr) ∧ Covers wr₁ s₁.wr ∧
      Covers (rd₂ ++ wr₂) (s₂.rd ++ s₂.wr) ∧ Covers wr₂ s₂.wr) :
    RelCT isa P (.call n c) fun _ _ => True := by
  refine regionModel.relCT_call hv hct fun s₁ s₂ e₁ e₂ hp h₁ h₂ => ?_
  rw [call_callEntry, Option.some.injEq] at h₁ h₂
  subst h₁ h₂
  obtain ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂⟩ := hP _ _ hp
  exact ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂, rfl, fun _ _ _ _ _ _ => rfl⟩

/-- Calls of a whole-block function, with the same arguments in both runs,
are constant time. -/
theorem xts_rel (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (modePPC64LE (AesXts.xtsMode enc)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modePPC64LE (AesXts.xtsMode enc)).post s s')
    (ct : ConstantTime isa (modePPC64LE (AesXts.xtsMode enc)).pre (modePPC64LE (AesXts.xtsMode enc)).pub c)
    {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W T D S : Addr, ∃ N R : Nat,
      XPre s₁ W T D S N R ∧ XPre s₂ W T D S N R ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call n c) fun _ _ => True := by
  refine relCT_callEx ok ct fun s₁ s₂ hp => ?_
  obtain ⟨W, T, D, S, N, R, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.mode_pre (enc := enc), h₂.mode_pre (enc := enc), ?_, h₁.reads, h₁.writes, h₂.reads,
    h₂.writes⟩
  simp only [modePPC64LE, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    ce3, ce4, ce5, ce6, ce7, ce8, h₁.r3, h₁.r4, h₁.r5, h₁.r6, h₁.r7, h₁.r8, h₂.r3, h₂.r4, h₂.r5, h₂.r6,
    h₂.r7, h₂.r8, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesXts.PPC64LE.Unit

end

end

/-!
# XTS-AES of data units on PPC64LE: the arguments of each call

The five calls of a whole-block function the functions make, each with
`XPre` from the precondition (`UPre`), for a state with the permissions
of the entry state and the call's arguments in its registers:

* `xpre_tweak`: the tweak value `i`, copied to the tweak (`tR`), enciphered
  with `tweak_schedule` from the zero second tweak (`zR`);
* `xpre_blocks`: the first `N` whole blocks of the data, from the tweak;
* `xpre_last`: the last whole block (`L`), from the tweak (`o = tO`) or from
  the second tweak (`o = zO`).
-/

@[expose] public section

namespace VG.Proof.AesXts.PPC64LE.Unit

open VG VG.PPC64LE
open VG.Impl.AesXts.PPC64LEUnit (tO zO)

theorem wrap_off (p : Addr) {d n k : Nat} (h : p.toNat + k ≤ 2 ^ 64) (hd : d + n ≤ k) (hn : 0 < n := by decide) :
    (p + BitVec.ofNat 64 d).toNat + n ≤ 2 ^ 64 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_using [h, hd, hn]), Nat.mod_eq_of_lt (by omega_using [h, hd, hn])]
  omega_using [h, hd]

section
variable {s₀ s : State} (hp : UPre s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
include hp hrd hwr

theorem xpre_tweak (r3 : s.gpr .r3 = K s₀) (r4 : s.gpr .r4 = BitVec.ofNat 64 (R s₀))
    (r5 : s.gpr .r5 = S s₀ + BitVec.ofNat 64 zO) (r6 : s.gpr .r6 = S s₀ + BitVec.ofNat 64 tO)
    (r7 : s.gpr .r7 = BitVec.ofNat 64 1) (r8 : s.gpr .r8 = S s₀) :
    XPre s (K s₀) (S s₀ + BitVec.ofNat 64 zO) (S s₀ + BitVec.ofNat 64 tO) (S s₀) 1 (R s₀) where
  r3 := r3
  r4 := r4
  r5 := r5
  r6 := r6
  r7 := r7
  r8 := r8
  rounds := hp.rounds
  n := by decide
  wt := hp.tsch_scr.sub_right (sub_trans z_sub s_sub)
  wd := hp.tsch_scr.sub_right (sub_trans t_sub s_sub)
  ws := hp.tsch_scr.sub_right wk_sub
  td := hp.t_z.symm
  ts := hp.z_wk
  ds := hp.t_wk
  wrapT := wrap_off _ hp.scr_wrap (by decide)
  wrapD := wrap_off _ hp.scr_wrap (by decide)
  wrapS := by have := hp.scr_wrap; omega_using [this]
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨tschR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, zO, rfl, by simp [zO]⟩
    · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scrR s₀, by simp, zO, rfl, by simp [zO]⟩
    · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

theorem xpre_blocks {N : Nat} (hN : 16 * N ≤ Len s₀) (r3 : s.gpr .r3 = W s₀)
    (r4 : s.gpr .r4 = BitVec.ofNat 64 (R s₀)) (r5 : s.gpr .r5 = S s₀ + BitVec.ofNat 64 tO)
    (r6 : s.gpr .r6 = D s₀) (r7 : s.gpr .r7 = BitVec.ofNat 64 N) (r8 : s.gpr .r8 = S s₀) :
    XPre s (W s₀) (S s₀ + BitVec.ofNat 64 tO) (D s₀) (S s₀) N (R s₀) where
  r3 := r3
  r4 := r4
  r5 := r5
  r6 := r6
  r7 := r7
  r8 := r8
  rounds := hp.rounds
  n := by have := hp.len_hi; simp only [Spec.Xts.maxBlocks] at this; omega_using [hN, this]
  wt := hp.sch_scr.sub_right (sub_trans t_sub s_sub)
  wd := hp.sch_data.sub_right (Region.sub_prefix hN)
  ws := hp.sch_scr.sub_right wk_sub
  td := (hp.data_scr.symm.sub_left (sub_trans t_sub s_sub)).sub_right (Region.sub_prefix hN)
  ts := hp.t_wk
  ds := (hp.data_scr.sub_left (Region.sub_prefix hN)).sub_right wk_sub
  wrapT := wrap_off _ hp.scr_wrap (by decide)
  wrapD := by have := hp.data_wrap; omega_using [hN, this]
  wrapS := by have := hp.scr_wrap; omega_using [this]
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
    · exact ⟨dataR s₀, by simp, 0, by simp, by simpa using hN⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
    · exact ⟨dataR s₀, by simp, 0, by simp, by simpa using hN⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

theorem xpre_last {o : Nat} (ho : o = tO ∨ o = zO) (r3 : s.gpr .r3 = W s₀)
    (r4 : s.gpr .r4 = BitVec.ofNat 64 (R s₀)) (r5 : s.gpr .r5 = S s₀ + BitVec.ofNat 64 o)
    (r6 : s.gpr .r6 = L s₀) (r7 : s.gpr .r7 = BitVec.ofNat 64 1) (r8 : s.gpr .r8 = S s₀) :
    XPre s (W s₀) (S s₀ + BitVec.ofNat 64 o) (L s₀) (S s₀) 1 (R s₀) := by
  have oS : Region.Sub ⟨S s₀ + BitVec.ofNat 64 o, 16⟩ ⟨S s₀, 2208⟩ := by
    rcases ho with rfl | rfl
    · exact t_sub
    · exact z_sub
  have oW : (⟨S s₀ + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint (wkR s₀) := by
    rcases ho with rfl | rfl
    · exact hp.t_wk
    · exact hp.z_wk
  have ol : o + 16 ≤ 2432 := by rcases ho with rfl | rfl <;> decide
  have lS : Region.Sub ⟨L s₀, 16 * 1⟩ (dataR s₀) := hp.l_sub
  exact {
    r3 := r3
    r4 := r4
    r5 := r5
    r6 := r6
    r7 := r7
    r8 := r8
    rounds := hp.rounds
    n := by decide
    wt := hp.sch_scr.sub_right (sub_trans oS s_sub)
    wd := hp.sch_data.sub_right lS
    ws := hp.sch_scr.sub_right wk_sub
    td := (hp.data_scr.symm.sub_left (sub_trans oS s_sub)).sub_right lS
    ts := oW
    ds := (hp.data_scr.sub_left lS).sub_right wk_sub
    wrapT := wrap_off _ hp.scr_wrap ol
    wrapD := hp.l_wrap
    wrapS := by have := hp.scr_wrap; omega_using [this]
    reads := by
      rw [hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨scrR s₀, by simp, o, rfl, by simpa using ol⟩
      · exact ⟨dataR s₀, by simp, 16 * (M s₀ - 1), rfl, by
          have := len_eq s₀; have := hp.m_pos; simp only [M, B] at *; omega_using [this]⟩
      · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
    writes := by
      rw [hwr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, o, rfl, by simpa using ol⟩
      · exact ⟨dataR s₀, by simp, 16 * (M s₀ - 1), rfl, by
          have := len_eq s₀; have := hp.m_pos; simp only [M, B] at *; omega_using [this]⟩
      · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩ }

end

end VG.Proof.AesXts.PPC64LE.Unit

end

end

/-! ### `AesXts.PPC64LE.Unit.Run`, which only this module used -/

section

/-!
# XTS-AES of data units on PPC64LE: the tweak, and what every piece keeps

As on AArch64 (`Proof/AesXts/AArch64/Unit/Run.lean`). `Inv`: between the
calls the code keeps its arguments in `r14`, `r15`, `r17`, `r18` and `r19`,
its caller's other nonvolatile registers, the saved registers and its return
address in their slots, and changes memory only in the data and the scratch
buffer (`Inv.step`, for any code whose frame is in those). `tweak_wp`: the
prologue and the call enciphering the tweak value leave
`T = AES-enc(Key2, i)` in the tweak (`TwPost`). `fin_wp`: the epilogue
restores the registers and the return address. No code changes the stack
pointer (`wp_sp`).
-/

@[expose] public section

namespace VG.Proof.AesXts.PPC64LE.Unit

open VG VG.PPC64LE VG.Impl.AesXts.PPC64LEUnit
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.PPC64LE (modePPC64LE)
open VG.Spec.Aes (bytesAt)

section
variable (s₀ : State)

/-- The tweak and the second tweak. -/
abbrev Tp : Addr := S s₀ + BitVec.ofNat 64 tO
abbrev Zp : Addr := S s₀ + BitVec.ofNat 64 zO

/-- `T = AES-enc(Key2, i)`. -/
abbrev t0 : List Byte :=
  Spec.Cbc.aesWith (R s₀) (bytesAt s₀.mem (K s₀) (16 * (R s₀ + 1))) (bytesAt s₀.mem (I s₀) 16)

/-- `AES-enc(Key1, ·)` (`enc`) or `AES-dec(Key1, ·)`. -/
abbrev ciph (enc : Bool) : Spec.Cbc.Cipher := ciphOf enc (R s₀) (bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)))

/-- The slots: the return address (through `r0`) and the registers. -/
abbrev saveL : List (Reg × Nat) := (.r0, lrOff) :: saved

/-- What the slots hold: the registers on entry, and the return address. -/
abbrev saveG : Reg → BitVec 64 := (s₀.write .r0 s₀.lr).gpr

end

theorem save_eq : save = .mflr .r0 :: Spill.saveCode .r9 saveL := rfl

theorem restore_eq : restore = Spill.restoreCode .r19 saveL ++ ([.mtlr .r0] : List Instr) := rfl

/-- The registers the code saves. -/
abbrev vars : List Reg := [.r14, .r15, .r16, .r17, .r18, .r19]

/-- Code keeps the stack pointer. -/
theorem wp_sp {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.sp = s.sp := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.sp he⟩

/-- What the code keeps between the calls. -/
structure Inv (s₀ s : State) : Prop where
  r14 : s.gpr .r14 = W s₀
  r15 : s.gpr .r15 = s₀.gpr .r5
  r17 : s.gpr .r17 = D s₀
  r18 : s.gpr .r18 = s₀.gpr .r8
  r19 : s.gpr .r19 = S s₀
  rest : ∀ r ∈ preserved, r ∉ vars → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dataR s₀, scrR s₀] s₀.mem s.mem
  saved : Spill.Saved (S s₀) (saveG s₀) saveL s.mem

theorem saved_bound : ∀ p ∈ saveL, 2208 ≤ p.2 ∧ p.2 + 8 ≤ 2264 := by decide

theorem r4_ofNat (s₀ : State) : BitVec.ofNat 64 (R s₀) = s₀.gpr .r5 := by
  rw [R, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem cS (s₀ : State) (d n : Nat) (h : d + n ≤ 2432) : (scrR s₀).Contains (S s₀ + BitVec.ofNat 64 d) n :=
  Offset.contains_base _ h (by omega_using [h])

theorem in_rw {rs : List Region} {r : Region} {a : Addr} {n : Nat} (hr : r ∈ rs) (h : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, h⟩

theorem preserved_ne16 {r : Reg} (hv : r ∉ vars) : r ≠ .r16 := fun e => hv (by simp [e])

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- `Inv` across code that keeps the nonvolatile registers (but `r16`) and
writes only within `rs`, each in the data or the first 2208 bytes of the
scratch buffer. -/
theorem Inv.step {s s' : State} (h : Inv s₀ s) {rs : List Region}
    (hrs : ∀ r ∈ rs, Region.Sub r (dataR s₀) ∨ Region.Sub r ⟨S s₀, 2208⟩)
    (hf : Frame rs s.mem s'.mem) (hg : ∀ r ∈ preserved, r ≠ .r16 → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv s₀ s' where
  r14 := by rw [hg _ (by decide) (by decide), h.r14]
  r15 := by rw [hg _ (by decide) (by decide), h.r15]
  r17 := by rw [hg _ (by decide) (by decide), h.r17]
  r18 := by rw [hg _ (by decide) (by decide), h.r18]
  r19 := by rw [hg _ (by decide) (by decide), h.r19]
  rest r hr hv := by rw [hg r hr (preserved_ne16 hv), h.rest r hr hv]
  sp := by rw [hsp, h.sp]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  frame := h.frame.trans (hf.sub fun r hr => by
    rcases hrs r hr with h | h
    · exact ⟨dataR s₀, by simp, h⟩
    · exact ⟨scrR s₀, by simp, sub_trans h s_sub⟩)
  saved := h.saved.frame hf fun p hp' r hr =>
    (hp.slots_disj (hrs r hr)).sub_left (slot_sub p.2 (saved_bound p hp').1 (saved_bound p hp').2)

/-- `Inv` across code that keeps the registers it pins and memory. -/
theorem Inv.regs {s s' : State} (h : Inv s₀ s) (hg : ∀ r ∈ preserved, r ≠ .r16 → s'.gpr r = s.gpr r)
    (hsp : s'.sp = s.sp) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv s₀ s' :=
  Inv.step hp h (rs := []) (fun _ h => by simp at h) (by rw [hm]; exact Frame.refl _ _) hg hsp hrd hwr

/-- `Inv` across a call of a whole-block function. -/
theorem Inv.call {enc : Bool} {s s' : State} (h : Inv s₀ s) {Wk T Dd : Addr} {N Rr : Nat}
    (hT : Region.Sub ⟨T, 16⟩ ⟨S s₀, 2208⟩)
    (hD : Region.Sub ⟨Dd, 16 * N⟩ (dataR s₀) ∨ Region.Sub ⟨Dd, 16 * N⟩ ⟨S s₀, 2208⟩)
    (hc : XPost enc s Wk T Dd (S s₀) N Rr s') : Inv s₀ s' :=
  Inv.step hp h (rs := [⟨T, 16⟩, ⟨Dd, 16 * N⟩, ⟨S s₀, 2176⟩]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inr hT
      · exact hD
      · exact .inr (Region.sub_prefix (by decide)))
    hc.frame (fun r hr _ => hc.saved r hr) hc.sp hc.rd hc.wr

/-! ## The prologue -/

/-- Before the call enciphering the tweak value. -/
structure ProPost (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (K s₀) (Zp s₀) (Tp s₀) (S s₀) 1 (R s₀)
  frame : Frame [scrR s₀] s₀.mem s.mem
  ti : bytesAt s.mem (Tp s₀) 16 = bytesAt s₀.mem (I s₀) 16
  z : bytesAt s.mem (Zp s₀) 16 = List.replicate 16 0

theorem pro_wp : WP isa (.block pro) s₀ (ProPost s₀) := by
  refine WP.mono (wp_sp (Q := fun s => s.sp = s₀.sp → ProPost s₀ s) ?_) fun s ⟨h, hsp⟩ => h hsp
  rw [pro, save_eq]
  simp only [List.append_assoc, List.cons_append]
  refine WP.cons exec_mflr (Spill.save_ok (b := .r9) (l := saveL) (by decide) (by decide) (fun p hp' => ?_) ?_)
  · have := saved_bound p hp'
    show InRegions s₀.wr (S s₀ + BitVec.ofNat 64 p.2) 8
    rw [hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by omega_using [this]))
  rw [WP.block_append_iff]
  generalize hs₂ : ({ (s₀.write .r0 s₀.lr) with
    mem := (Spill.saveMem (s₀.write .r0 s₀.lr).mem ((s₀.write .r0 s₀.lr).gpr .r9) (s₀.write .r0 s₀.lr).gpr
      saveL) } : State) = s₂
  have g₀ (r : Reg) (hr : r ≠ .r0) : (s₀.write .r0 s₀.lr).gpr r = s₀.gpr r := by simp [State.write, hr]
  have gpr₂ (r : Reg) (hr : r ≠ .r0) : s₂.gpr r = s₀.gpr r := by rw [← hs₂]; exact g₀ r hr
  obtain rd₂ : s₂.rd = s₀.rd := by rw [← hs₂]; rfl
  obtain wr₂ : s₂.wr = s₀.wr := by rw [← hs₂]; rfl
  obtain mem₂ : s₂.mem = Spill.saveMem s₀.mem (S s₀) (saveG s₀) saveL := by
    rw [← hs₂]; show Spill.saveMem _ _ _ _ = _; rw [g₀ .r9 (by decide)]; rfl
  refine WP.mono (setup_wp s₂) fun s₃ ⟨r14₃, r15₃, r17₃, r18₃, r19₃, g₃, mem₃', rd₃', wr₃'⟩ => ?_
  rw [gpr₂ _ (by decide)] at r14₃ r15₃ r17₃ r18₃ r19₃
  obtain mem₃ : s₃.mem = Spill.saveMem s₀.mem (S s₀) (saveG s₀) saveL := by rw [mem₃', mem₂]
  obtain rd₃ : s₃.rd = s₀.rd := by rw [rd₃', rd₂]
  obtain wr₃ : s₃.wr = s₀.wr := by rw [wr₃', wr₂]
  obtain k₃ : ∀ r, r ≠ .r0 → r ≠ .r14 → r ≠ .r15 → r ≠ .r17 → r ≠ .r18 → r ≠ .r19 → s₃.gpr r = s₀.gpr r :=
    fun r h₀ h₁ h₂ h₃ h₄ h₅ => by rw [g₃ r h₁ h₂ h₃ h₄ h₅, gpr₂ r h₀]
  obtain rdwr₃ : s₃.rd ++ s₃.wr = [schR s₀, tschR s₀, iR s₀, dataR s₀, scrR s₀] := by
    rw [rd₃, wr₃, hp.rd, hp.wr]; rfl
  obtain wr₃'' : s₃.wr = [dataR s₀, scrR s₀] := by rw [wr₃]; exact hp.wr
  obtain cI0 : (iR s₀).Contains (I s₀) 8 := by
    simpa using Offset.contains_base (I s₀) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
  obtain r6₃ : s₃.gpr .r6 = I s₀ := k₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine AesCbc.PPC64LE.copy_wp (dst := .r19) (src := .r6) (d := tO) (e := 0) (P := Tp s₀) (Q := I s₀)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [r19₃]) (by rw [r19₃, ← Offset.add_add]) (by rw [r6₃]; simp) (by rw [r6₃])
    (by rw [rdwr₃]; exact in_rw (r := iR s₀) (by simp) cI0)
    (by rw [rdwr₃]; exact in_rw (r := iR s₀) (by simp) (Offset.contains_base _ (by decide) (by decide)))
    (by rw [wr₃'']; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [tO])))
    (by rw [wr₃'', Offset.add_add]; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [tO])))
    fun s₄ g₄ mem₄ rd₄ wr₄ => ?_
  rw [WP.block_append_iff]
  obtain wr₄' : s₄.wr = [dataR s₀, scrR s₀] := by rw [wr₄, wr₃'']
  refine WP.mono (zeroZ_wp s₄ (Z := Zp s₀) (by rw [g₄ _ (by decide), r19₃])
    (by rw [g₄ _ (by decide), r19₃, ← Offset.add_add])
    (by rw [wr₄']; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [zO])))
    (by rw [wr₄', Offset.add_add]; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [zO]))))
    fun s₅ ⟨g₅, mem₅, rd₅, wr₅⟩ => ?_
  refine WP.mono (tArgs_wp s₅) fun s₆ ⟨r3₆, r4₆, r5₆, r6₆, r7₆, r8₆, cs₆, mem₆, rd₆, wr₆⟩ hsp => ?_
  -- The registers.
  obtain k₅ : ∀ r, r ≠ .r9 → s₅.gpr r = s₃.gpr r := fun r h => by rw [g₅ r h, g₄ r h]
  obtain r19₅ : s₅.gpr .r19 = S s₀ := by rw [k₅ _ (by decide), r19₃]
  have cs (r : Reg) (hr : r ∈ preserved) : s₆.gpr r = s₃.gpr r := by
    rw [cs₆ r hr, k₅ r (preserved_ne r hr).2.2.2.2.2.2.2.1]
  obtain rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅, rd₄, rd₃]
  obtain wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅, wr₄, wr₃]
  -- The memory.
  obtain f₃ : Frame [scrR s₀] s₀.mem s₃.mem := by
    rw [mem₃]
    exact (Spill.saveMem_frame_base (n := 2264) (fun p hp' => (saved_bound p hp').2) (by decide) s₀.mem (S s₀)
      _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
  obtain f₄ : Frame [⟨Tp s₀, 16⟩] s₃.mem s₄.mem := by rw [mem₄]; exact AesCbc.copyMem_frame _ _ _
  obtain f₅ : Frame [⟨Zp s₀, 16⟩] s₄.mem s₅.mem := by rw [mem₅]; exact zero2_frame _ _
  obtain frame : Frame [scrR s₀] s₀.mem s₆.mem := by
    rw [mem₆]
    refine f₃.trans ((f₄.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, scr_sub (by simp [tO])⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, scr_sub (by simp [zO])⟩
  obtain sv₃ : Spill.Saved (S s₀) (saveG s₀) saveL s₃.mem := by
    rw [mem₃]; exact Spill.saveMem_saved (by decide) _ _ _
  obtain sdisj : ∀ (r : Region), Region.Sub r ⟨S s₀, 2208⟩ → ∀ p ∈ saveL, ∀ r' ∈ [r],
      Region.Disjoint ⟨S s₀ + BitVec.ofNat 64 p.2, 8⟩ r' := fun r hr p hp' r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact (hp.slots_disj (.inr hr)).sub_left (slot_sub p.2 (saved_bound p hp').1 (saved_bound p hp').2)
  obtain sv₆ : Spill.Saved (S s₀) (saveG s₀) saveL s₆.mem := by
    rw [mem₆]; exact (sv₃.frame f₄ (sdisj _ t_sub)).frame f₅ (sdisj _ z_sub)
  refine ⟨⟨by rw [cs _ (by decide), r14₃], by rw [cs _ (by decide), r15₃], by rw [cs _ (by decide), r17₃],
    by rw [cs _ (by decide), r18₃], by rw [cs _ (by decide), r19₃], fun r hr hv => ?_, hsp, rd₆', wr₆',
    frame.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩, sv₆⟩, ?_, frame, ?_, ?_⟩
  · simp only [vars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
    obtain ⟨h14, h15, -, h17, h18, h19⟩ := hv
    rw [cs r hr]
    exact k₃ r (preserved_ne r hr).1 h14 h15 h17 h18 h19
  · refine xpre_tweak hp rd₆' wr₆' ?_ ?_ (by rw [r5₆, r19₅]) (by rw [r6₆, r19₅]) r7₆ (by rw [r8₆, r19₅])
    · rw [r3₆, k₅ _ (by decide), k₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [r4₆, k₅ _ (by decide), r15₃, r4_ofNat]
  · rw [mem₆, mem₅, Proof.Cmac.bytesAt_frame (zero2_frame _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.t_z) (by decide), mem₄,
      AesCbc.copyMem_bytes _ (hp.i_scr.symm.sub_left (scr_sub (by simp [tO]))),
      Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.i_scr) (by decide)]
  · rw [mem₆, mem₅, zero2_bytes]

/-! ## The tweak -/

/-- After the call enciphering the tweak value. -/
structure TwPost (s₀ s : State) : Prop where
  inv : Inv s₀ s
  frame : Frame [scrR s₀] s₀.mem s.mem
  t : bytesAt s.mem (Tp s₀) 16 = t0 s₀

theorem UPre.sched_frame {s : State} {rs : List Region} (hf : Frame rs s₀.mem s.mem)
    (hd : ∀ r ∈ rs, r = dataR s₀ ∨ r = scrR s₀ ∨ Region.Sub r (dataR s₀)) :
    bytesAt s.mem (W s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)) := by
  obtain hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega_using [hRb])
  rcases hd r hr with rfl | rfl | h
  · exact hp.sch_data.sub_left (Region.sub_prefix hRb)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hRb)
  · exact (hp.sch_data.sub_left (Region.sub_prefix hRb)).sub_right h

/-- A whole-block function, verified. -/
abbrev XtsOk (enc : Bool) (c : Prog isa) : Prop :=
  ∀ s, (modePPC64LE (AesXts.xtsMode enc)).pre s →
    ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modePPC64LE (AesXts.xtsMode enc)).post s s'

/-- The call enciphering the tweak value. -/
theorem tcall_wp {n : String} {c : Prog isa} (ok : XtsOk true c) (nf : c.noFrames = true) {s₂ : State}
    (h₂ : ProPost s₀ s₂) : WP isa (.call n c) s₂ (TwPost s₀) := by
  refine WP.mono (xts_call true ok nf h₂.pre) fun s₃ c => ?_
  obtain hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  obtain eK : bytesAt s₂.mem (K s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (K s₀) (16 * (R s₀ + 1)) :=
    Proof.Cmac.bytesAt_frame h₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.tsch_scr.sub_left (Region.sub_prefix hRb)) (by omega_using [hRb])
  refine ⟨Inv.call hp h₂.inv z_sub (.inr t_sub) c, ?_, ?_⟩
  · refine (h₂.frame.sub fun r hr => ?_).trans (c.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, sub_trans z_sub s_sub⟩
      · exact ⟨scrR s₀, by simp, sub_trans t_sub s_sub⟩
      · exact ⟨scrR s₀, by simp, wk_sub⟩
  · have := Proof.AesXts.Unit.tweak_of (R := R s₀) (w := bytesAt s₂.mem (K s₀) (16 * (R s₀ + 1))) c.out h₂.z
    rw [this, h₂.ti, eK]

theorem tweak_wp (ok : XtsOk true Impl.AesXts.PPC64LE.encrypt)
    (nf : Impl.AesXts.PPC64LE.encrypt.noFrames = true) : WP isa tweak s₀ (TwPost s₀) :=
  WP.seq (WP.mono (pro_wp hp) fun _ h₂ => tcall_wp hp ok nf h₂)

/-! ## A call on whole blocks from the tweak -/

/-- After the call on the first `N` whole blocks from the tweak `T`. -/
structure AllPost (enc : Bool) (s₀ : State) (N : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  out : Spec.Cbc.blocksAt s.mem (D s₀) N =
    Spec.Xts.crypt (ciph s₀ enc) (t0 s₀) (Spec.Cbc.blocksAt s₀.mem (D s₀) N)
  tw : bytesAt s.mem (Tp s₀) 16 = Spec.Xts.next (t0 s₀) N
  frame : Frame [⟨D s₀, 16 * N⟩, scrR s₀] s₀.mem s.mem

theorem blocks_call (enc : Bool) {n : String} {c : Prog isa} (ok : XtsOk enc c)
    (nf : c.noFrames = true) {N : Nat} (hN : 16 * N ≤ Len s₀) {s : State} (h : TwPost s₀ s)
    (hpre : XPre s (W s₀) (Tp s₀) (D s₀) (S s₀) N (R s₀)) :
    WP isa (.call n c) s (AllPost enc s₀ N) := by
  refine WP.mono (xts_call enc ok nf hpre) fun s' x => ?_
  obtain dS : Region.Sub ⟨D s₀, 16 * N⟩ (dataR s₀) := Region.sub_prefix hN
  obtain eW := hp.sched_frame (h.inv.frame) (fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp)
  obtain eD : Spec.Cbc.blocksAt s.mem (D s₀) N = Spec.Cbc.blocksAt s₀.mem (D s₀) N :=
    blocksAt_frame h.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact hp.data_scr.sub_left dS) (by have := hp.data_wrap; omega_using [hN, this])
  refine ⟨Inv.call hp h.inv t_sub (.inl dS) x, ?_, ?_, ?_⟩
  · rw [x.out, eW, h.t, eD]
  · rw [x.tw, h.t]
  · refine (h.frame.sub fun r hr => ?_).trans (x.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact ⟨scrR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, sub_trans t_sub s_sub⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, wk_sub⟩

/-- `TwPost` across code that keeps the nonvolatile registers and memory. -/
theorem TwPost.keep {s s' : State} (h : TwPost s₀ s) (hg : ∀ r ∈ preserved, s'.gpr r = s.gpr r)
    (hsp : s'.sp = s.sp) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : TwPost s₀ s' where
  inv := Inv.regs hp h.inv (fun r hr _ => hg r hr) hsp hm hrd hwr
  frame := by rw [hm]; exact h.frame
  t := by rw [hm]; exact h.t

/-! ## The epilogue -/

/-- The nonvolatile registers and the return address restored. -/
def Restored (s₀ s' : State) : Prop := (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr

theorem fin_wp {s : State} (h : Inv s₀ s) :
    WP isa (.block restore) s fun s' => Restored s₀ s' ∧ s'.mem = s.mem := by
  obtain rdwr : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  rw [restore_eq]
  refine Spill.restore_ok (b := .r19) (l := saveL) (by decide) h.r19 (by decide) (by decide)
    (fun p hp' => ?_) h.saved fun s₃ r₃ => ?_
  · have := saved_bound p hp'
    rw [rdwr, hp.rd, hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by omega_using [this]))
  refine WP.cons exec_mtlr (wp_nil ⟨⟨fun r hr => ?_, ?_⟩, r₃.mem⟩)
  · show s₃.gpr r = _
    obtain h0 : saveG s₀ r = s₀.gpr r := ite_eq_right_iff.mpr fun h => absurd h (preserved_ne r hr).1
    rw [r₃.gpr_of (r := r) ?_, h0]
    by_cases hv : r ∈ vars
    · left
      simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · right; rw [h.rest r hr hv, h0]
  · show s₃.gpr .r0 = _
    rw [r₃.gpr (.r0, lrOff) (by decide)]; rfl

/-! ## Bytes of the data a call keeps -/

/-- The bytes of a part `X` of the data that a call on other blocks keeps. -/
theorem call_keeps {enc : Bool} {s s' : State} {Wk T Dd : Addr} {N Rr : Nat} {X : Region}
    (hX : Region.Sub X (dataR s₀)) (hXD : X.Disjoint ⟨Dd, 16 * N⟩) (hT : Region.Sub ⟨T, 16⟩ (scrR s₀))
    (c : XPost enc s Wk T Dd (S s₀) N Rr s') (hn : X.len ≤ 2 ^ 64) :
    bytesAt s'.mem X.base X.len = bytesAt s.mem X.base X.len :=
  Proof.Cmac.bytesAt_frame c.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.data_scr.sub_left hX).sub_right hT
    · exact hXD
    · exact (hp.data_scr.sub_left hX).sub_right wk_sub) hn

end

end VG.Proof.AesXts.PPC64LE.Unit

end

end


/-!
# XTS-AES of data units on PPC64LE: encryption

As on AArch64 (`Proof/AesXts/AArch64/Unit/Enc.lean`). `encrypt_wp`: the
tweak, the call on the whole blocks, and for a partial block the swap and
the call on the last whole block, then the epilogue. The data unit is
`encWith` of the cipher and the tweak, which is `aesXtsEncrypt` of any key
whose schedules are given (`unit_post`).
-/

@[expose] public section

namespace VG.Proof.AesXts.PPC64LE.Unit

open VG VG.PPC64LE VG.Impl.AesXts.PPC64LEUnit
open VG.Proof.AesXts.Unit (swapMem encWith decWith)
open VG.Spec.Aes (bytesAt)

/-- The data unit's result in a direction. -/
def withOf : Bool → Spec.Cbc.Cipher → List Byte → List Byte → List Byte
  | true => encWith
  | false => decWith

/-- What each branch leaves before the epilogue. -/
structure Fin (enc : Bool) (s₀ s : State) : Prop where
  inv : Inv s₀ s
  data : bytesAt s.mem (D s₀) (Len s₀) =
    withOf enc (ciph s₀ enc) (t0 s₀) (bytesAt s₀.mem (D s₀) (Len s₀))

/-- The memory of `AllPost`. -/
def AllMem (enc : Bool) (s₀ : State) (N : Nat) (m : Mem) : Prop :=
  Spec.Cbc.blocksAt m (D s₀) N = Spec.Xts.crypt (ciph s₀ enc) (t0 s₀) (Spec.Cbc.blocksAt s₀.mem (D s₀) N) ∧
    bytesAt m (Tp s₀) 16 = Spec.Xts.next (t0 s₀) N ∧ Frame [⟨D s₀, 16 * N⟩, scrR s₀] s₀.mem m

theorem AllPost.mem {enc : Bool} {s₀ : State} {N : Nat} {s : State} (h : AllPost enc s₀ N s) :
    AllMem enc s₀ N s.mem :=
  ⟨h.out, h.tw, h.frame⟩

/-- Before a call on the first `N` whole blocks from the tweak. -/
structure BlocksReady (s₀ : State) (N : Nat) (s : State) : Prop where
  tw : TwPost s₀ s
  pre : XPre s (W s₀) (Tp s₀) (D s₀) (S s₀) N (R s₀)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem AllPost.keep {enc : Bool} {N : Nat} {s s' : State} (h : AllPost enc s₀ N s)
    (hg : ∀ r ∈ preserved, r ≠ .r16 → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : AllPost enc s₀ N s' where
  inv := Inv.regs hp h.inv hg hsp hm hrd hwr
  out := by rw [hm]; exact h.out
  tw := by rw [hm]; exact h.tw
  frame := by rw [hm]; exact h.frame

/-- After `split`, following the call on the whole blocks. -/
structure SplitPost (enc : Bool) (s₀ : State) (N : Nat) (s : State) : Prop where
  all : AllPost enc s₀ N s
  r10 : s.gpr .r10 = BitVec.ofNat 64 (16 * M s₀)
  r11 : s.gpr .r11 = BitVec.ofNat 64 (B s₀)

/-- `r17 + r10 − 16` is the last whole block. -/
theorem last_of {s : State} (h17 : s.gpr .r17 = D s₀) (h10 : s.gpr .r10 = BitVec.ofNat 64 (16 * M s₀)) :
    s.gpr .r17 + s.gpr .r10 - BitVec.ofNat 64 16 = L s₀ := by
  rw [h17, h10, last_eq _ hp.m_pos]

/-- Before the call on the last whole block, from the tweak at offset `o`:
the bytes after the whole blocks swapped with the last whole block's first. -/
structure LastReady (o : Nat) (s₀ s : State) (m : Mem) : Prop where
  inv : Inv s₀ s
  pre : XPre s (W s₀) (S s₀ + BitVec.ofNat 64 o) (L s₀) (S s₀) 1 (R s₀)
  mem : s.mem = swapMem m (L s₀) (B s₀)

/-- The swap, and the arguments of the call on the last whole block. -/
theorem steal_wp {o : Nat} (ho : o = tO ∨ o = zO) {s : State} (hi : Inv s₀ s)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 (16 * M s₀)) (h11 : s.gpr .r11 = BitVec.ofNat 64 (B s₀))
    (h12 : s.gpr .r12 = L s₀) (hB : B s₀ ≠ 0) :
    WP isa (.seq swap (.block (argsL o))) s fun s' => LastReady o s₀ s' s.mem := by
  obtain hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  obtain wr' : s.wr = [dataR s₀, scrR s₀] := by rw [hi.wr, hp.wr]
  refine WP.seq (WP.mono (wp_sp (swap_wp s (Nat.pos_of_ne_zero hB) hb h12 h11 (fun i hi' => by
      rw [wr']
      exact in_rw (r := dataR s₀) (by simp)
        (hp.lb_sub _ (Offset.contains_base (L s₀) (d := i) (n := 1) (k := 16 + B s₀) (by omega_using [hi']) (by omega_using [hb, hi']))))))
    fun s₂ ⟨⟨mem₂, g₂, rd₂, wr₂⟩, sp₂⟩ => ?_)
  refine WP.mono (wp_sp (argsL_wp' s₂ (o := o) (by rcases ho with rfl | rfl <;> decide)))
    fun s₃ ⟨⟨r3₃, r4₃, r5₃, r6₃, r7₃, r8₃, cs₃, mem₃, rd₃, wr₃⟩, sp₃⟩ => ?_
  have k₂ (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s.gpr r := by
    obtain ⟨-, -, -, -, -, -, h8, h9, -, h11, h12⟩ := preserved_ne r hr
    exact g₂ r h8 h9 h11 h12
  obtain inv₂ : Inv s₀ s₂ := Inv.step hp hi (rs := [⟨L s₀, 16 + B s₀⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inl hp.lb_sub)
    (by rw [mem₂]; exact Proof.AesXts.Unit.swapMem_frame _ _ _) (fun r hr _ => k₂ r hr) sp₂ rd₂ wr₂
  obtain inv₃ : Inv s₀ s₃ := Inv.regs hp inv₂ (fun r hr _ => cs₃ r hr) sp₃ mem₃ rd₃ wr₃
  refine ⟨inv₃, xpre_last hp inv₃.rd inv₃.wr ho (by rw [r3₃, inv₂.r14])
    (by rw [r4₃, inv₂.r15, r4_ofNat]) (by rw [r5₃, inv₂.r19]) ?_ r7₃ (by rw [r8₃, inv₂.r19]),
    by rw [mem₃, mem₂]⟩
  rw [r6₃, g₂ _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide)
    (by decide)]
  exact last_of hp hi.r17 h10

/-- The call on the last whole block, and the data unit's ciphertext. -/
theorem encLastCall_wp (ok : XtsOk true Impl.AesXts.PPC64LE.encrypt)
    (nf : Impl.AesXts.PPC64LE.encrypt.noFrames = true)
    {s : State} {m : Mem} (h : LastReady tO s₀ s m) (hm : AllMem true s₀ (M s₀) m) (hB : B s₀ ≠ 0) :
    WP isa encCall s (Fin true s₀) := by
  obtain hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  obtain ⟨hout, htw, hfr⟩ := hm
  refine WP.mono (xts_call true ok nf h.pre) fun s₄ c => ?_
  obtain sw := Proof.AesXts.Unit.swapMem_frame m (L s₀) (B s₀)
  refine ⟨Inv.call hp h.inv t_sub (.inl hp.l_sub) c, ?_⟩
  rw [len_eq s₀]
  refine Proof.AesXts.Unit.enc_steal hp.m_pos (Nat.pos_of_ne_zero hB) hb hout ?_ ⟨?_, ?_, ?_⟩
  · exact Proof.Cmac.bytesAt_frame hfr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.tl_blocks
      · exact hp.data_scr.sub_left hp.tl_sub) (by omega_using [hb])
  · rw [Proof.AesXts.Unit.crypt_one_of c.out,
      hp.sched_frame h.inv.frame (fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp), h.mem,
      Proof.Cmac.bytesAt_frame sw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_scr.symm.sub_left (sub_trans t_sub s_sub)).sub_right hp.lb_sub) (by decide), htw]
  · rw [call_keeps hp (X := ⟨D s₀, 16 * (M s₀ - 1)⟩) (blocks_sub (by omega_using [])) hp.hd_l
      (sub_trans t_sub s_sub) c (by dsimp only; have := hp.wrapD; omega_using [this]), h.mem]
    exact Proof.Cmac.bytesAt_frame sw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.hd_lb) (by dsimp only; have := hp.wrapD; omega_using [this])
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub tl_l (sub_trans t_sub s_sub) c
      (by dsimp only; omega_using [hb]), h.mem]

/-- The last whole block's address, after `split`. -/
theorem lastAddr_wp {s : State} (hi : Inv s₀ s) (h10 : s.gpr .r10 = BitVec.ofNat 64 (16 * M s₀)) :
    WP isa (.block lastAddr) s fun s' => s'.gpr .r12 = L s₀ ∧ (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.mono (wp_sp (lastAddr_wp' s)) fun _ ⟨⟨r12, g, mem, rd, wr⟩, sp⟩ =>
    ⟨by rw [r12]; exact last_of hp hi.r17 h10, g, sp, mem, rd, wr⟩

omit hp in
theorem keep_r12 {s s' : State} (hg : ∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) :
    ∀ r ∈ preserved, r ≠ .r16 → s'.gpr r = s.gpr r :=
  fun r hr _ => hg r (preserved_ne r hr).2.2.2.2.2.2.2.2.2.2

/-- Before the call on the last whole block of encryption: `Cₘ` and `PP`
swapped into place. -/
def EncLast (s₀ s : State) : Prop := ∃ m, AllMem true s₀ (M s₀) m ∧ LastReady tO s₀ s m

theorem encLast_wp {s : State} (h : SplitPost true s₀ (M s₀) s) (hB : B s₀ ≠ 0) :
    WP isa (.seq (.seq (.block lastAddr) swap) (.block (argsL tO))) s (EncLast s₀) := by
  refine WP.assoc' (WP.seq (WP.mono (lastAddr_wp hp h.all.inv h.r10) fun s₁ ⟨r12₁, g₁, sp₁, mem₁, rd₁, wr₁⟩ => ?_))
  obtain h₁ := AllPost.keep hp h.all (keep_r12 g₁) sp₁ mem₁ rd₁ wr₁
  exact WP.mono (steal_wp hp (.inl rfl) h₁.inv (by rw [g₁ _ (by decide), h.r10])
    (by rw [g₁ _ (by decide), h.r11]) r12₁ hB) fun _ h₂ => ⟨_, h₁.mem, h₂⟩

/-- The steal of encryption: `Cₘ` and `PP` swapped into place, and `PP`
enciphered with the tweak of block `M`. -/
theorem encSteal_wp (ok : XtsOk true Impl.AesXts.PPC64LE.encrypt)
    (nf : Impl.AesXts.PPC64LE.encrypt.noFrames = true)
    {s : State} (h : SplitPost true s₀ (M s₀) s) (hB : B s₀ ≠ 0) :
    WP isa encSteal s (Fin true s₀) :=
  WP.assoc (WP.assoc (WP.seq (WP.mono (encLast_wp hp h hB) fun _ ⟨_, hm, h'⟩ =>
    encLastCall_wp hp ok nf h' hm hB)))

/-- The postcondition, from the bytes of the data unit. -/
theorem unit_post {enc : Bool} {s' : State}
    (hd : bytesAt s'.mem (D s₀) (Len s₀) = withOf enc (ciph s₀ enc) (t0 s₀) (bytesAt s₀.mem (D s₀) (Len s₀))) :
    (unitPPC64LE enc).post s₀ s' := by
  intro key hk
  obtain hk' := Proof.AesXts.Unit.keys_of (bytesAt s₀.mem (I s₀) 16) hk
  obtain hl : 16 ≤ (bytesAt s₀.mem (D s₀) (Len s₀)).length := by
    rw [Proof.AesXts.Unit.length_bytesAt]; exact hp.len_lo
  cases enc
  · rw [xtsOf, Proof.AesXts.Unit.aesXtsDecrypt_eq hk' hl, hd]; rfl
  · rw [xtsOf, Proof.AesXts.Unit.aesXtsEncrypt_eq hk' hl, hd]; rfl

omit hp in
/-- After `split`: the bytes of the whole blocks in `r10`, and the bytes
after them in `r11`. -/
theorem split_wp {s : State} (h : Inv s₀ s) :
    WP isa (.block split) s fun s' => s'.gpr .r10 = BitVec.ofNat 64 (16 * M s₀) ∧
      s'.gpr .r11 = BitVec.ofNat 64 (B s₀) ∧ (∀ r, r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.mono (wp_sp (split_wp' s)) fun _ ⟨⟨r10, r11, g, mem, rd, wr⟩, sp⟩ =>
    ⟨by rw [r10, h.r18], by rw [r11, h.r18], g, sp, mem, rd, wr⟩

omit hp in
theorem keep_r10r11 {s s' : State} (hg : ∀ r, r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) :
    ∀ r ∈ preserved, r ≠ .r16 → s'.gpr r = s.gpr r :=
  fun r hr _ => hg r (preserved_ne r hr).2.2.2.2.2.2.2.2.1 (preserved_ne r hr).2.2.2.2.2.2.2.2.2.1

/-- The arguments of the call on the whole blocks. -/
theorem argsAll_wp {s : State} (h : TwPost s₀ s) : WP isa (.block argsAll) s (BlocksReady s₀ (M s₀)) :=
  WP.mono (wp_sp (argsAll_wp' s)) fun s₂ ⟨⟨r3₂, r4₂, r5₂, r6₂, r7₂, r8₂, cs₂, mem₂, rd₂, wr₂⟩, sp₂⟩ =>
    have h₂ := TwPost.keep hp h cs₂ sp₂ mem₂ rd₂ wr₂
    ⟨h₂, xpre_blocks hp h₂.inv.rd h₂.inv.wr (N := M s₀)
      (by rw [len_eq s₀]; omega_using []) (by rw [r3₂, h.inv.r14]) (by rw [r4₂, h.inv.r15, r4_ofNat])
      (by rw [r5₂, h.inv.r19]) (by rw [r6₂, h.inv.r17]) (by rw [r7₂, h.inv.r18]) (by rw [r8₂, h.inv.r19])⟩

theorem splitAll_wp {enc : Bool} {N : Nat} {s : State} (h : AllPost enc s₀ N s) :
    WP isa (.block split) s (SplitPost enc s₀ N) :=
  WP.mono (split_wp h.inv) fun _ ⟨r10, r11, g, sp, mem, rd, wr⟩ =>
    ⟨AllPost.keep hp h (keep_r10r11 g) sp mem rd wr, r10, r11⟩

omit hp in
/-- The data unit of whole blocks, after the call on all of them. -/
theorem whole_fin {enc : Bool} {s : State} (h : AllPost enc s₀ (M s₀) s) (hb : B s₀ = 0) : Fin enc s₀ s := by
  refine ⟨h.inv, ?_⟩
  rw [show Len s₀ = 16 * M s₀ by rw [len_eq s₀, hb, Nat.add_zero]]
  cases enc
  · exact Proof.AesXts.Unit.dec_whole h.out
  · exact Proof.AesXts.Unit.enc_whole h.out

omit hp in
theorem eval_b {s : State} (h : s.gpr .r11 = BitVec.ofNat 64 (B s₀)) :
    isa.eval (.zero .d .r11) s = some (decide (B s₀ = 0)) :=
  eval_zero_ofNat s .r11 (by have : B s₀ < 16 := Nat.mod_lt _ (by decide); omega_using [this]) h

theorem encrypt_wp (ok : XtsOk true Impl.AesXts.PPC64LE.encrypt)
    (nf : Impl.AesXts.PPC64LE.encrypt.noFrames = true) :
    WP isa Impl.AesXts.PPC64LEUnit.encrypt s₀ fun s' => Restored s₀ s' ∧ (unitPPC64LE true).post s₀ s' := by
  refine WP.seq (WP.mono (tweak_wp hp ok nf) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (argsAll_wp hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (blocks_call hp true ok nf (by rw [len_eq s₀]; omega_using []) h₂.tw h₂.pre) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (splitAll_wp hp h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (WP.ite (decide (B s₀ = 0)) (eval_b h₄.r11)
    (fun hb => WP.block_nil (whole_fin h₄.all (by simpa using hb)))
    (fun hb => encSteal_wp hp ok nf h₄ (by simpa using hb))) fun s₅ h₅ => ?_)
  exact WP.mono (fin_wp hp h₅.inv) fun s' ⟨g, m⟩ => ⟨g, unit_post hp (by rw [m]; exact h₅.data)⟩

end

end VG.Proof.AesXts.PPC64LE.Unit

end

end

/-!
# XTS-AES of data units on PPC64LE: decryption

As on AArch64 (`Proof/AesXts/AArch64/Unit/Dec.lean`). `decrypt_wp`: the
tweak, then without a partial block the call on the whole blocks; with one,
the call on all but the last whole block, the tweak of block `M` (`nextT`),
the call on the last whole block from it, the swap, and the call on the
last whole block from the tweak of block `M - 1`; then the epilogue.
-/

@[expose] public section

namespace VG.Proof.AesXts.PPC64LE.Unit

open VG VG.PPC64LE VG.Impl.AesXts.PPC64LEUnit
open VG.Proof.AesXts.Unit (swapMem encWith decWith)
open VG.Spec.Aes (bytesAt)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- Before the call on the last whole block from the tweak of block `M`,
which is at `zO`. -/
structure DecL1 (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (W s₀) (Zp s₀) (L s₀) (S s₀) 1 (R s₀)
  mem : ∃ m, AllMem false s₀ (M s₀ - 1) m ∧ Frame [⟨Zp s₀, 16⟩] m s.mem ∧
    bytesAt s.mem (Zp s₀) 16 = Spec.Xts.mulAlpha (bytesAt m (Tp s₀) 16)

/-- The memory after the call on the last whole block from the tweak of
block `M`: `PP` there, from the memory `m` after the first `M - 1` blocks. -/
def DecMem (s₀ : State) (m₅ : Mem) : Prop :=
  ∃ m, AllMem false s₀ (M s₀ - 1) m ∧
    bytesAt m₅ (L s₀) 16 = Spec.Xts.block (ciph s₀ false) (Spec.Xts.next (t0 s₀) (M s₀)) (bytesAt m (L s₀) 16) ∧
    bytesAt m₅ (D s₀) (16 * (M s₀ - 1)) = bytesAt m (D s₀) (16 * (M s₀ - 1)) ∧
    bytesAt m₅ (L s₀ + 16) (B s₀) = bytesAt m (L s₀ + 16) (B s₀) ∧
    bytesAt m₅ (Tp s₀) 16 = Spec.Xts.next (t0 s₀) (M s₀ - 1)

/-- After the call on the last whole block from the tweak of block `M`. -/
structure DecL2 (s₀ s : State) : Prop where
  inv : Inv s₀ s
  mem : DecMem s₀ s.mem

/-- The arguments of the call on all but the last whole block. -/
theorem argsHead_wp {s : State} (h : TwPost s₀ s) : WP isa (.block argsHead) s (BlocksReady s₀ (M s₀ - 1)) := by
  have hm := hp.m_pos
  refine WP.mono (wp_sp (argsHead_wp' s (by rw [h.inv.r18]; exact hm)))
    fun s₁ ⟨⟨r3₁, r4₁, r5₁, r6₁, r7₁, r8₁, cs₁, mem₁, rd₁, wr₁⟩, sp₁⟩ => ?_
  have h₁ := TwPost.keep hp h cs₁ sp₁ mem₁ rd₁ wr₁
  exact ⟨h₁, xpre_blocks hp h₁.inv.rd h₁.inv.wr (N := M s₀ - 1)
    (by rw [len_eq s₀]; omega_using []) (by rw [r3₁, h.inv.r14]) (by rw [r4₁, h.inv.r15, r4_ofNat])
    (by rw [r5₁, h.inv.r19]) (by rw [r6₁, h.inv.r17]) (by rw [r7₁, h.inv.r18]) (by rw [r8₁, h.inv.r19])⟩

/-- The tweak of block `M`, at `zO`, and the arguments of the call on the
last whole block from it. -/
theorem decL1_wp {s₂ : State} (h₂ : AllPost false s₀ (M s₀ - 1) s₂) :
    WP isa (.block (nextT ++ split ++ argsL zO)) s₂ (DecL1 s₀) := by
  have wr₂ : s₂.wr = [dataR s₀, scrR s₀] := by rw [h₂.inv.wr, hp.wr]
  have rdwr₂ : s₂.rd ++ s₂.wr = [schR s₀, tschR s₀, iR s₀, dataR s₀, scrR s₀] := by
    rw [h₂.inv.rd, h₂.inv.wr, hp.rd, hp.wr]; rfl
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (wp_sp (nextT_wp s₂ (T := Tp s₀) (Z := Zp s₀) (by rw [h₂.inv.r19])
    (by rw [h₂.inv.r19, ← Offset.add_add]) (by rw [h₂.inv.r19]) (by rw [h₂.inv.r19, ← Offset.add_add])
    hp.t_z.symm
    (by rw [rdwr₂]; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [tO])))
    (by rw [rdwr₂, Offset.add_add]; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [tO])))
    (by rw [wr₂]; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [zO])))
    (by rw [wr₂, Offset.add_add]; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [zO])))))
    fun s₃ ⟨⟨g₃, f₃, z₃, rd₃, wr₃⟩, sp₃⟩ => ?_
  have inv₃ : Inv s₀ s₃ := Inv.step hp h₂.inv (rs := [⟨Zp s₀, 16⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inr z_sub) f₃
    (fun r hr h16 => by
      obtain ⟨-, -, -, -, -, -, -, h9, h10, h11, h12⟩ := preserved_ne r hr
      exact g₃ r h9 h10 h11 h12 h16) sp₃ rd₃ wr₃
  rw [WP.block_append_iff]
  refine WP.mono (split_wp inv₃) fun s₄ ⟨r10₄, _, g₄, sp₄, mem₄, rd₄, wr₄⟩ => ?_
  refine WP.mono (wp_sp (argsL_wp' s₄ (o := zO) (by decide)))
    fun s₆ ⟨⟨r3₆, r4₆, r5₆, r6₆, r7₆, r8₆, cs₆, mem₆, rd₆, wr₆⟩, sp₆⟩ => ?_
  have inv₄ : Inv s₀ s₄ := Inv.regs hp inv₃ (keep_r10r11 g₄) sp₄ mem₄ rd₄ wr₄
  have inv₆ : Inv s₀ s₆ := Inv.regs hp inv₄ (fun r hr _ => cs₆ r hr) sp₆ mem₆ rd₆ wr₆
  have m₆ : s₆.mem = s₃.mem := by rw [mem₆, mem₄]
  refine ⟨inv₆, xpre_last hp inv₆.rd inv₆.wr (.inr rfl) (by rw [r3₆, inv₄.r14])
    (by rw [r4₆, inv₄.r15, r4_ofNat]) (by rw [r5₆, inv₄.r19]) (by rw [r6₆]; exact last_of hp inv₄.r17 r10₄) r7₆
    (by rw [r8₆, inv₄.r19]),
    ⟨s₂.mem, h₂.mem, by rw [m₆]; exact f₃, by rw [m₆]; exact z₃⟩⟩

/-- The call on the last whole block from the tweak of block `M`. -/
theorem decL2_wp (ok : XtsOk false Impl.AesXts.PPC64LE.decrypt)
    (nf : Impl.AesXts.PPC64LE.decrypt.noFrames = true) {s : State} (h : DecL1 s₀ s) :
    WP isa decCall s (DecL2 s₀) := by
  have hm := hp.m_pos
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  obtain ⟨m, ⟨hout, htw, hfr⟩, f₃, z₃⟩ := h.mem
  refine WP.mono (xts_call false ok nf h.pre) fun s₇ c₇ => ?_
  have tL : Region.Sub ⟨Tp s₀, 16⟩ (scrR s₀) := sub_trans t_sub s_sub
  have zL : Region.Sub ⟨Zp s₀, 16⟩ (scrR s₀) := sub_trans z_sub s_sub
  have eW := hp.sched_frame h.inv.frame (fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp)
  refine ⟨Inv.call hp h.inv z_sub (.inl hp.l_sub) c₇, m, ⟨hout, htw, hfr⟩, ?_, ?_, ?_, ?_⟩
  · rw [Proof.AesXts.Unit.crypt_one_of c₇.out, eW, z₃, htw, ← Proof.AesXts.next_succ,
      Nat.sub_add_cancel hm,
      Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_scr.sub_left hp.l_sub).sub_right zL) (by decide)]
  · rw [call_keeps hp (X := ⟨D s₀, 16 * (M s₀ - 1)⟩) (blocks_sub (by omega_using [])) hp.hd_l zL c₇
      (by dsimp only; have := hp.wrapD; omega_using [this])]
    exact Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_left (blocks_sub (by omega_using []))).sub_right zL) (by dsimp only; have := hp.wrapD; omega_using [this])
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub tl_l zL c₇ (by dsimp only; omega_using [hb])]
    exact Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_left hp.tl_sub).sub_right zL) (by dsimp only; omega_using [hb])
  · rw [Proof.Cmac.bytesAt_frame c₇.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.t_z
        · exact (hp.data_scr.symm.sub_left tL).sub_right hp.l_sub
        · exact hp.t_wk) (by decide),
      Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.t_z) (by decide), htw]

/-- The call on the last whole block from the tweak of block `M - 1`, and
the data unit's plaintext. -/
theorem decLast_wp (ok : XtsOk false Impl.AesXts.PPC64LE.decrypt)
    (nf : Impl.AesXts.PPC64LE.decrypt.noFrames = true)
    {s : State} {m₅ : Mem} (h : LastReady tO s₀ s m₅) (hm₅ : DecMem s₀ m₅) (hB : B s₀ ≠ 0) :
    WP isa decCall s (Fin false s₀) := by
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  have hm := hp.m_pos
  obtain ⟨m, ⟨hout, htw, hfr⟩, h5L, h5H, h5T, tw₅⟩ := hm₅
  refine WP.mono (xts_call false ok nf h.pre) fun s₁₂ c₁₂ => ?_
  refine ⟨Inv.call hp h.inv t_sub (.inl hp.l_sub) c₁₂, ?_⟩
  have sw := Proof.AesXts.Unit.swapMem_frame m₅ (L s₀) (B s₀)
  have tL : Region.Sub ⟨Tp s₀, 16⟩ (scrR s₀) := sub_trans t_sub s_sub
  have eW' := hp.sched_frame h.inv.frame (fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp)
  rw [len_eq s₀]
  refine Proof.AesXts.Unit.dec_steal (m₃ := m) (m₅ := m₅) hm (Nat.pos_of_ne_zero hB) hb hout
    ⟨?_, ?_⟩ ⟨h5L, h5H, h5T⟩ ⟨?_, ?_, ?_⟩
  · exact Proof.Cmac.bytesAt_frame hfr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.l_hd
      · exact hp.data_scr.sub_left hp.l_sub) (by decide)
  · exact Proof.Cmac.bytesAt_frame hfr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.hd_tl.symm
      · exact hp.data_scr.sub_left hp.tl_sub) (by omega_using [hb])
  · rw [Proof.AesXts.Unit.crypt_one_of c₁₂.out, eW', h.mem,
      Proof.Cmac.bytesAt_frame sw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_scr.symm.sub_left tL).sub_right hp.lb_sub) (by decide), tw₅]
  · rw [call_keeps hp (X := ⟨D s₀, 16 * (M s₀ - 1)⟩) (blocks_sub (by omega_using [])) hp.hd_l tL c₁₂
      (by dsimp only; have := hp.wrapD; omega_using [this]), h.mem]
    exact Proof.Cmac.bytesAt_frame sw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.hd_lb) (by dsimp only; have := hp.wrapD; omega_using [this])
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub tl_l tL c₁₂ (by dsimp only; omega_using [hb]), h.mem]

/-- Before the call on the last whole block from the tweak of block `M - 1`:
`Pₘ` and `CC` swapped into place. -/
def DecL3 (s₀ s : State) : Prop := ∃ m₅, DecMem s₀ m₅ ∧ LastReady tO s₀ s m₅

/-- The swap, after the call from the tweak of block `M`. -/
theorem decL3_wp {s : State} (h : DecL2 s₀ s) (hB : B s₀ ≠ 0) :
    WP isa (.seq (.seq (.block (split ++ lastAddr)) swap) (.block (argsL tO))) s (DecL3 s₀) := by
  refine WP.assoc' (WP.seq ?_)
  rw [WP.block_append_iff]
  refine WP.mono (split_wp h.inv) fun s₈ ⟨r10₈, r11₈, g₈, sp₈, mem₈, rd₈, wr₈⟩ => ?_
  have inv₈ : Inv s₀ s₈ := Inv.regs hp h.inv (keep_r10r11 g₈) sp₈ mem₈ rd₈ wr₈
  refine WP.mono (lastAddr_wp hp inv₈ r10₈) fun s₉ ⟨r12₉, g₉, sp₉, mem₉, rd₉, wr₉⟩ => ?_
  have inv₉ : Inv s₀ s₉ := Inv.regs hp inv₈ (keep_r12 g₉) sp₉ mem₉ rd₉ wr₉
  exact WP.mono (steal_wp hp (.inl rfl) inv₉ (by rw [g₉ _ (by decide), r10₈])
    (by rw [g₉ _ (by decide), r11₈]) r12₉ hB) fun _ h₂ => ⟨_, by rw [mem₉, mem₈]; exact h.mem, h₂⟩

/-- The steal of decryption, after the tweak. -/
theorem decSteal_wp (ok : XtsOk false Impl.AesXts.PPC64LE.decrypt)
    (nf : Impl.AesXts.PPC64LE.decrypt.noFrames = true)
    {s : State} (h : TwPost s₀ s) (hB : B s₀ ≠ 0) :
    WP isa decSteal s (Fin false s₀) := by
  refine WP.seq (WP.mono (argsHead_wp hp h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (blocks_call hp false ok nf (by rw [len_eq s₀]; omega_using []) h₁.tw h₁.pre) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (decL1_wp hp h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (decL2_wp hp ok nf h₃) fun s₄ h₄ => ?_)
  exact WP.assoc (WP.assoc (WP.seq (WP.mono (decL3_wp hp h₄ hB) fun _ ⟨_, hm, h'⟩ => decLast_wp hp ok nf h' hm hB)))

theorem split_tw_wp {s : State} (h : TwPost s₀ s) :
    WP isa (.block split) s fun s' => TwPost s₀ s' ∧ s'.gpr .r11 = BitVec.ofNat 64 (B s₀) :=
  WP.mono (split_wp h.inv) fun _ ⟨_, r11₂, g₂, sp₂, mem₂, rd₂, wr₂⟩ =>
    ⟨TwPost.keep hp h (fun r hr => g₂ r (preserved_ne r hr).2.2.2.2.2.2.2.2.1
      (preserved_ne r hr).2.2.2.2.2.2.2.2.2.1) sp₂ mem₂ rd₂ wr₂, r11₂⟩

theorem decrypt_wp (okE : XtsOk true Impl.AesXts.PPC64LE.encrypt)
    (nfE : Impl.AesXts.PPC64LE.encrypt.noFrames = true)
    (okD : XtsOk false Impl.AesXts.PPC64LE.decrypt) (nfD : Impl.AesXts.PPC64LE.decrypt.noFrames = true) :
    WP isa Impl.AesXts.PPC64LEUnit.decrypt s₀ fun s' => Restored s₀ s' ∧ (unitPPC64LE false).post s₀ s' := by
  refine WP.seq (WP.mono (tweak_wp hp okE nfE) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (split_tw_wp hp h₁) fun s₂ ⟨h₂, r11₂⟩ => ?_)
  refine WP.seq (WP.mono (WP.ite (decide (B s₀ = 0)) (eval_b r11₂) (fun hb => ?_)
    (fun hb => decSteal_wp hp okD nfD h₂ (by simpa using hb))) fun s₅ h₅ => ?_)
  · refine WP.seq (WP.mono (argsAll_wp hp h₂) fun s₃ h₃ => ?_)
    exact WP.mono (blocks_call hp false okD nfD (by rw [len_eq s₀]; omega_using []) h₃.tw h₃.pre)
      fun s₄ h₄ => whole_fin h₄ (by simpa using hb)
  · exact WP.mono (fin_wp hp h₅.inv) fun s' ⟨g, m⟩ => ⟨g, unit_post hp (by rw [m]; exact h₅.data)⟩

end

end VG.Proof.AesXts.PPC64LE.Unit

end

end

/-!
# XTS-AES of data units on PPC64LE: constant time

As on AArch64 (`Proof/AesXts/AArch64/Unit/CT.lean`): two runs from states
that agree on the public arguments are related piece by piece (`RelCT`),
from the correctness proof's states between the pieces: the taint analysis
covers the code between the calls (the swap's loop with them), from the
registers the states pin to public values (`Inv.agree`), each call is
constant time by its callee's proof (`xcall_rel`), and the one branch, on
whether there is a partial block, agrees in both runs.
-/

@[expose] public section

namespace VG.Proof.AesXts.PPC64LE.Unit

open VG VG.PPC64LE VG.Impl.AesXts.PPC64LEUnit
open VG.Proof.AesCbc.PPC64LE (modePPC64LE)

/-- A piece of code the taint analysis checks from the registers `rs`, which
agree in two runs (as do the stack pointers), with what each run reaches. -/
theorem taint_rel {P : State → State → Prop} {c : Prog isa} {F₁ F₂ : State → Prop} (rs : List Reg)
    (ht : ∃ h, (taint.check (Taint.ofRegs rs) c h).isSome = true)
    (hsp : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp) (ha : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hw : ∀ s₁ s₂, P s₁ s₂ → WP isa c s₁ F₁ ∧ WP isa c s₂ F₂) :
    RelCT isa P c fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂ := by
  obtain ⟨_, ht⟩ := ht
  exact ((RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun x y hp => ⟨hsp x y hp, fun r h' => ha x y hp r (Taint.mem_ofRegs.mp h')⟩) ht).wp hw).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-- A whole-block function, constant time. -/
abbrev XtsCt (enc : Bool) (c : Prog isa) : Prop :=
  ConstantTime isa (modePPC64LE (AesXts.xtsMode enc)).pre (modePPC64LE (AesXts.xtsMode enc)).pub c

/-- A call of a whole-block function, with the same arguments in both runs,
and what each run leaves. -/
theorem xcall_rel (enc : Bool) {n : String} {c : Prog isa} (ok : XtsOk enc c) (ct : XtsCt enc c)
    {P : State → State → Prop} {F₁ F₂ : State → Prop}
    (hx : ∀ s₁ s₂, P s₁ s₂ → ∃ W T D S : Addr, ∃ N R : Nat,
      XPre s₁ W T D S N R ∧ XPre s₂ W T D S N R ∧ s₁.sp = s₂.sp)
    (hw : ∀ s₁ s₂, P s₁ s₂ → WP isa (.call n c) s₁ F₁ ∧ WP isa (.call n c) s₂ F₂) :
    RelCT isa P (.call n c) fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂ :=
  ((xts_rel enc ok ct hx).wp hw).mono (fun _ _ h => h) fun _ _ h => h.2

/-- The registers the states pin to public values. -/
abbrev pubRegs : List Reg := [.r14, .r15, .r17, .r18, .r19]

section
variable {s₀ s₀' : State} (hq : unitPub s₀ s₀')
include hq

theorem pub_W : W s₀ = W s₀' := hq.1
theorem pub_K : K s₀ = K s₀' := hq.2.1
theorem pub_r5 : s₀.gpr .r5 = s₀'.gpr .r5 := hq.2.2.1
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_r5 hq]
theorem pub_D : D s₀ = D s₀' := hq.2.2.2.2.1
theorem pub_r8 : s₀.gpr .r8 = s₀'.gpr .r8 := hq.2.2.2.2.2.1
theorem pub_S : S s₀ = S s₀' := hq.2.2.2.2.2.2.1
theorem pub_sp : s₀.sp = s₀'.sp := hq.2.2.2.2.2.2.2
theorem pub_M : M s₀ = M s₀' := by rw [M, M, Len, Len, pub_r8 hq]
theorem pub_B : B s₀ = B s₀' := by rw [B, B, Len, Len, pub_r8 hq]
theorem pub_L : L s₀ = L s₀' := by rw [L, L, pub_D hq, pub_M hq]
theorem pub_Tp : Tp s₀ = Tp s₀' := by simp only [Tp, pub_S hq]
theorem pub_Zp : Zp s₀ = Zp s₀' := by simp only [Zp, pub_S hq]

theorem Inv.agree {s₁ s₂ : State} (h₁ : Inv s₀ s₁) (h₂ : Inv s₀' s₂) : ∀ r ∈ pubRegs, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h₁.r14, h₂.r14, pub_W hq]
  · rw [h₁.r15, h₂.r15, pub_r5 hq]
  · rw [h₁.r17, h₂.r17, pub_D hq]
  · rw [h₁.r18, h₂.r18, pub_r8 hq]
  · rw [h₁.r19, h₂.r19, pub_S hq]

theorem Inv.sp_eq {s₁ s₂ : State} (h₁ : Inv s₀ s₁) (h₂ : Inv s₀' s₂) : s₁.sp = s₂.sp := by
  rw [h₁.sp, h₂.sp, pub_sp hq]

omit hq in
/-- Agreement on the public registers and more. -/
theorem agree_cons {s₁ s₂ : State} {rs : List Reg} (h : ∀ r ∈ pubRegs, s₁.gpr r = s₂.gpr r)
    (h' : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : ∀ r ∈ rs ++ pubRegs, s₁.gpr r = s₂.gpr r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h' r hr
  · exact h r hr

end

/-! ## Taint checks -/

theorem pro_taint : ∃ h, (taint.check (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9])
    (.block pro) h).isSome = true := ⟨_, by taint_decide⟩

theorem argsAll_taint : ∃ h, (taint.check (Taint.ofRegs pubRegs) (.block argsAll) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem argsHead_taint : ∃ h, (taint.check (Taint.ofRegs pubRegs) (.block argsHead) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem split_taint : ∃ h, (taint.check (Taint.ofRegs pubRegs) (.block split) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem encLast_taint : ∃ h, (taint.check (Taint.ofRegs (([.r10, .r11] : List Reg) ++ pubRegs))
    (.seq (.seq (.block lastAddr) swap) (.block (argsL tO))) h).isSome = true := ⟨_, by taint_decide⟩

theorem decL1_taint : ∃ h, (taint.check (Taint.ofRegs pubRegs)
    (.block (nextT ++ split ++ argsL zO)) h).isSome = true := ⟨_, by taint_decide⟩

theorem decL3_taint : ∃ h, (taint.check (Taint.ofRegs pubRegs)
    (.seq (.seq (.block (split ++ lastAddr)) swap) (.block (argsL tO))) h).isSome = true := ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (taint.check (Taint.ofRegs [.r19]) (.block restore) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-! ## The two runs -/

section
variable {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : unitPub s₀ s₀')
include hp hp' hq

theorem tweak_rel (ok : XtsOk true Impl.AesXts.PPC64LE.encrypt)
    (nf : Impl.AesXts.PPC64LE.encrypt.noFrames = true) (ct : XtsCt true Impl.AesXts.PPC64LE.encrypt) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') tweak fun a b => TwPost s₀ a ∧ TwPost s₀' b := by
  have p := taint_rel [.r3, .r4, .r5, .r6, .r7, .r8, .r9] pro_taint (P := fun a b => a = s₀ ∧ b = s₀')
    (fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact pub_sp hq)
    (fun a b h r hr => by
      obtain ⟨rfl, rfl⟩ := h
      have hq' := hq
      obtain ⟨h3, h4, h5, h6, h7, h8, h9, _⟩ := hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5
      · exact h6
      · exact h7
      · exact h8
      · exact h9)
    (F₁ := ProPost s₀) (F₂ := ProPost s₀') fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨pro_wp hp, pro_wp hp'⟩
  have c := xcall_rel true ok ct (n := "vg_aes_xts_encrypt") (P := fun a b => ProPost s₀ a ∧ ProPost s₀' b)
    (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
      rw [pub_K hq, pub_Zp hq, pub_Tp hq, pub_S hq, pub_R hq]; exact h.2.pre, Inv.sp_eq hq h.1.inv h.2.inv⟩)
    (F₁ := TwPost s₀) (F₂ := TwPost s₀')
    (fun a b h => ⟨tcall_wp hp ok nf h.1, tcall_wp hp' ok nf h.2⟩)
  exact p.seq c

theorem blocks_rel (enc : Bool) {n : String} {c : Prog isa} (ok : XtsOk enc c) (ct : XtsCt enc c)
    (nf : c.noFrames = true) {N N' : Nat} (hN : 16 * N ≤ Len s₀) (hN' : 16 * N' ≤ Len s₀')
    (hNN : N = N') :
    RelCT isa (fun a b => BlocksReady s₀ N a ∧ BlocksReady s₀' N' b) (.call n c)
      fun a b => AllPost enc s₀ N a ∧ AllPost enc s₀' N' b :=
  xcall_rel enc ok ct
    (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
      rw [pub_W hq, pub_Tp hq, pub_D hq, pub_S hq, hNN, pub_R hq]; exact h.2.pre,
      Inv.sp_eq hq h.1.tw.inv h.2.tw.inv⟩)
    fun a b h => ⟨blocks_call hp enc ok nf hN h.1.tw h.1.pre, blocks_call hp' enc ok nf hN' h.2.tw h.2.pre⟩

theorem restore_rel {enc : Bool} :
    RelCT isa (fun a b => Fin enc s₀ a ∧ Fin enc s₀' b) (.block restore) fun _ _ => True :=
  (taint_rel [.r19] restore_taint (P := fun a b => Fin enc s₀ a ∧ Fin enc s₀' b)
    (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
    (fun a b h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.inv.r19, h.2.inv.r19, pub_S hq])
    (F₁ := fun _ => True) (F₂ := fun _ => True)
    fun a b h => ⟨WP.mono (fin_wp hp h.1.inv) fun _ _ => trivial, WP.mono (fin_wp hp' h.2.inv) fun _ _ => trivial⟩).mono
    (fun _ _ h => h) fun _ _ _ => trivial

omit hp hp' in
theorem eval_eq {s₁ s₂ : State} (h₁ : s₁.gpr .r11 = BitVec.ofNat 64 (B s₀))
    (h₂ : s₂.gpr .r11 = BitVec.ofNat 64 (B s₀')) : isa.eval (.zero .d .r11) s₁ = isa.eval (.zero .d .r11) s₂ := by
  rw [eval_b h₁, eval_b h₂, pub_B hq]

theorem encrypt_rel (ok : XtsOk true Impl.AesXts.PPC64LE.encrypt)
    (nf : Impl.AesXts.PPC64LE.encrypt.noFrames = true) (ct : XtsCt true Impl.AesXts.PPC64LE.encrypt) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') Impl.AesXts.PPC64LEUnit.encrypt fun _ _ => True := by
  have hM := pub_M hq
  have t := tweak_rel hp hp' hq ok nf ct
  have a := taint_rel pubRegs argsAll_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
    (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
    (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := BlocksReady s₀ (M s₀)) (F₂ := BlocksReady s₀' (M s₀'))
    fun a b h => ⟨argsAll_wp hp h.1, argsAll_wp hp' h.2⟩
  have c := blocks_rel hp hp' hq true ok ct nf (by rw [len_eq s₀]; omega_using []) (by rw [len_eq s₀']; omega_using []) hM
    (n := "vg_aes_xts_encrypt")
  have sp := taint_rel pubRegs split_taint (P := fun a b => AllPost true s₀ (M s₀) a ∧ AllPost true s₀' (M s₀') b)
    (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
    (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := SplitPost true s₀ (M s₀))
    (F₂ := SplitPost true s₀' (M s₀')) fun a b h => ⟨splitAll_wp hp h.1, splitAll_wp hp' h.2⟩
  have br : RelCT isa (fun a b => SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b)
      (.ite (.zero .d .r11) (.block []) encSteal) fun a b => Fin true s₀ a ∧ Fin true s₀' b := by
    refine RelCT.ite (fun a b h => eval_eq hq h.1.r11 h.2.r11) ?_ ?_
    · refine RelCT.block_nil fun a b h => ?_
      have hb : B s₀ = 0 := by
        have := h.2; rw [eval_b h.1.1.r11] at this; simpa using this
      exact ⟨whole_fin h.1.1.all hb, whole_fin h.1.2.all (by rw [← pub_B hq]; exact hb)⟩
    · refine (RelCT.exists_ (P := fun (_ : B s₀ ≠ 0) a b =>
          SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b) fun hB => ?_).mono
        (fun a b h => ⟨by have := h.2; rw [eval_b h.1.1.r11] at this; simpa using this, h.1⟩)
        fun _ _ h => h
      have hB' : B s₀' ≠ 0 := by rw [← pub_B hq]; exact hB
      refine RelCT.assoc (RelCT.assoc ?_)
      have l := taint_rel ([.r10, .r11] ++ pubRegs) encLast_taint
        (P := fun a b => SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b)
        (fun a b h => Inv.sp_eq hq h.1.all.inv h.2.all.inv)
        (fun a b h => agree_cons (Inv.agree hq h.1.all.inv h.2.all.inv) fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [h.1.r10, h.2.r10, hM]
          · rw [h.1.r11, h.2.r11, pub_B hq])
        (F₁ := EncLast s₀) (F₂ := EncLast s₀') fun a b h => ⟨encLast_wp hp h.1 hB, encLast_wp hp' h.2 hB'⟩
      have c := xcall_rel true ok ct (n := "vg_aes_xts_encrypt") (P := fun a b => EncLast s₀ a ∧ EncLast s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.choose_spec.2.pre, by
          rw [pub_W hq, pub_L hq, pub_S hq, pub_R hq]; exact h.2.choose_spec.2.pre,
          Inv.sp_eq hq h.1.choose_spec.2.inv h.2.choose_spec.2.inv⟩)
        (F₁ := Fin true s₀) (F₂ := Fin true s₀')
        fun a b h => ⟨encLastCall_wp hp ok nf h.1.choose_spec.2 h.1.choose_spec.1 hB,
          encLastCall_wp hp' ok nf h.2.choose_spec.2 h.2.choose_spec.1 hB'⟩
      exact l.seq c
  exact t.seq (a.seq (c.seq (sp.seq (br.seq (restore_rel hp hp' hq)))))

theorem decrypt_rel (okE : XtsOk true Impl.AesXts.PPC64LE.encrypt)
    (nfE : Impl.AesXts.PPC64LE.encrypt.noFrames = true) (ctE : XtsCt true Impl.AesXts.PPC64LE.encrypt)
    (okD : XtsOk false Impl.AesXts.PPC64LE.decrypt) (nfD : Impl.AesXts.PPC64LE.decrypt.noFrames = true)
    (ctD : XtsCt false Impl.AesXts.PPC64LE.decrypt) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') Impl.AesXts.PPC64LEUnit.decrypt fun _ _ => True := by
  have hM := pub_M hq
  have t := tweak_rel hp hp' hq okE nfE ctE
  have sp := taint_rel pubRegs split_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
    (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
    (fun a b h => Inv.agree hq h.1.inv h.2.inv)
    (F₁ := fun s => TwPost s₀ s ∧ s.gpr .r11 = BitVec.ofNat 64 (B s₀))
    (F₂ := fun s => TwPost s₀' s ∧ s.gpr .r11 = BitVec.ofNat 64 (B s₀'))
    fun a b h => ⟨split_tw_wp hp h.1, split_tw_wp hp' h.2⟩
  have br : RelCT isa (fun a b => (TwPost s₀ a ∧ a.gpr .r11 = BitVec.ofNat 64 (B s₀)) ∧
      (TwPost s₀' b ∧ b.gpr .r11 = BitVec.ofNat 64 (B s₀')))
      (.ite (.zero .d .r11) (.seq (.block argsAll) decCall) decSteal)
      fun a b => Fin false s₀ a ∧ Fin false s₀' b := by
    refine RelCT.ite (fun a b h => eval_eq hq h.1.2 h.2.2) ?_ ?_
    · refine (RelCT.exists_ (P := fun (_ : B s₀ = 0) a b => TwPost s₀ a ∧ TwPost s₀' b) fun hb => ?_).mono
        (fun a b h => ⟨by have := h.2; rw [eval_b h.1.1.2] at this; simpa using this,
          h.1.1.1, h.1.2.1⟩) fun _ _ h => h
      have hb' : B s₀' = 0 := by rw [← pub_B hq]; exact hb
      have a := taint_rel pubRegs argsAll_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
        (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := BlocksReady s₀ (M s₀))
        (F₂ := BlocksReady s₀' (M s₀')) fun a b h => ⟨argsAll_wp hp h.1, argsAll_wp hp' h.2⟩
      have c := blocks_rel hp hp' hq false okD ctD nfD (by rw [len_eq s₀]; omega_using [])
        (by rw [len_eq s₀']; omega_using []) hM (n := "vg_aes_xts_decrypt")
      exact a.seq (c.mono (fun _ _ h => h) fun _ _ h => ⟨whole_fin h.1 hb, whole_fin h.2 hb'⟩)
    · refine (RelCT.exists_ (P := fun (_ : B s₀ ≠ 0) a b => TwPost s₀ a ∧ TwPost s₀' b) fun hB => ?_).mono
        (fun a b h => ⟨by have := h.2; rw [eval_b h.1.1.2] at this; simpa using this,
          h.1.1.1, h.1.2.1⟩) fun _ _ h => h
      have hB' : B s₀' ≠ 0 := by rw [← pub_B hq]; exact hB
      have a := taint_rel pubRegs argsHead_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
        (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := BlocksReady s₀ (M s₀ - 1))
        (F₂ := BlocksReady s₀' (M s₀' - 1)) fun a b h => ⟨argsHead_wp hp h.1, argsHead_wp hp' h.2⟩
      have c₁ := blocks_rel hp hp' hq false okD ctD nfD (N := M s₀ - 1)
        (N' := M s₀' - 1) (by rw [len_eq s₀]; omega_using []) (by rw [len_eq s₀']; omega_using []) (by rw [hM])
        (n := "vg_aes_xts_decrypt")
      have l₁ := taint_rel pubRegs decL1_taint
        (P := fun a b => AllPost false s₀ (M s₀ - 1) a ∧ AllPost false s₀' (M s₀' - 1) b)
        (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := DecL1 s₀) (F₂ := DecL1 s₀')
        fun a b h => ⟨decL1_wp hp h.1, decL1_wp hp' h.2⟩
      have c₂ := xcall_rel false okD ctD (n := "vg_aes_xts_decrypt") (P := fun a b => DecL1 s₀ a ∧ DecL1 s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
          rw [pub_W hq, pub_Zp hq, pub_L hq, pub_S hq, pub_R hq]; exact h.2.pre,
          Inv.sp_eq hq h.1.inv h.2.inv⟩)
        (F₁ := DecL2 s₀) (F₂ := DecL2 s₀') fun a b h => ⟨decL2_wp hp okD nfD h.1, decL2_wp hp' okD nfD h.2⟩
      have l₃ := taint_rel pubRegs decL3_taint (P := fun a b => DecL2 s₀ a ∧ DecL2 s₀' b)
        (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := DecL3 s₀) (F₂ := DecL3 s₀')
        fun a b h => ⟨decL3_wp hp h.1 hB, decL3_wp hp' h.2 hB'⟩
      have c₃ := xcall_rel false okD ctD (n := "vg_aes_xts_decrypt") (P := fun a b => DecL3 s₀ a ∧ DecL3 s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.choose_spec.2.pre, by
          rw [pub_W hq, pub_L hq, pub_S hq, pub_R hq]; exact h.2.choose_spec.2.pre,
          Inv.sp_eq hq h.1.choose_spec.2.inv h.2.choose_spec.2.inv⟩)
        (F₁ := Fin false s₀) (F₂ := Fin false s₀')
        fun a b h => ⟨decLast_wp hp okD nfD h.1.choose_spec.2 h.1.choose_spec.1 hB,
          decLast_wp hp' okD nfD h.2.choose_spec.2 h.2.choose_spec.1 hB'⟩
      exact a.seq (c₁.seq (l₁.seq (c₂.seq (RelCT.assoc (RelCT.assoc (l₃.seq c₃))))))
  exact t.seq (sp.seq (br.seq (restore_rel hp hp' hq)))

end

theorem encrypt_ct (ok : XtsOk true Impl.AesXts.PPC64LE.encrypt)
    (nf : Impl.AesXts.PPC64LE.encrypt.noFrames = true) (ct : XtsCt true Impl.AesXts.PPC64LE.encrypt) :
    ConstantTime isa (unitPPC64LE true).pre (unitPPC64LE true).pub Impl.AesXts.PPC64LEUnit.encrypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (encrypt_rel (UPre.of h₁) (UPre.of h₂) hq ok nf ct _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem decrypt_ct (okE : XtsOk true Impl.AesXts.PPC64LE.encrypt)
    (nfE : Impl.AesXts.PPC64LE.encrypt.noFrames = true) (ctE : XtsCt true Impl.AesXts.PPC64LE.encrypt)
    (okD : XtsOk false Impl.AesXts.PPC64LE.decrypt) (nfD : Impl.AesXts.PPC64LE.decrypt.noFrames = true)
    (ctD : XtsCt false Impl.AesXts.PPC64LE.decrypt) :
    ConstantTime isa (unitPPC64LE false).pre (unitPPC64LE false).pub Impl.AesXts.PPC64LEUnit.decrypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (decrypt_rel (UPre.of h₁) (UPre.of h₂) hq okE nfE ctE okD nfD ctD _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesXts.PPC64LE.Unit

end

end

/-!
# XTS-AES of data units on PPC64LE: `Verified`

`vg_aes_xts_encrypt_unit` and `vg_aes_xts_decrypt_unit` meet `unitPPC64LE`
(`encrypt_wp`, `decrypt_wp`, `encrypt_ct`, `decrypt_ct`), from the
whole-block functions' proofs (`Proof/AesXts/PPC64LE/Verified.lean`), and
so the shared contracts of `Spec/Xts/Contract.lean`.
-/

@[expose] public section

namespace VG.Proof.AesXts.PPC64LE.Unit

open VG VG.PPC64LE VG.Impl.AesXts.PPC64LEUnit

theorem encrypt_correct (s : State) (hs : (unitPPC64LE true).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (unitPPC64LE true).post s s' := by
  obtain ⟨t, s', he, ⟨hg, hlr⟩, hp⟩ := encrypt_wp (UPre.of hs) Proof.AesXts.PPC64LE.encrypt_correct
    Proof.AesXts.PPC64LE.encrypt_noFrames
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (unitPPC64LE false).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (unitPPC64LE false).post s s' := by
  obtain ⟨t, s', he, ⟨hg, hlr⟩, hp⟩ := decrypt_wp (UPre.of hs) Proof.AesXts.PPC64LE.encrypt_correct
    Proof.AesXts.PPC64LE.encrypt_noFrames Proof.AesXts.PPC64LE.decrypt_correct
    Proof.AesXts.PPC64LE.decrypt_noFrames
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

/-- A state satisfying the precondition: AES-128, a data unit of one block
at `0x4000`, and the scratch buffer at `0x5000`. -/
def unitSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 10 | .r6 => 0x3000 | .r7 => 0x4000 | .r8 => 16 | .r9 => 0x5000
    | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 240⟩, ⟨0x3000, 16⟩]
  wr := [⟨0x4000, 16⟩, ⟨0x5000, 2432⟩]

theorem encrypt_verified : Verified PPC64LE.target encrypt (Spec.Xts.aesEncryptUnitContract PPC64LE.abi) :=
  Verified.of_correct encrypt_correct
    (encrypt_ct Proof.AesXts.PPC64LE.encrypt_correct Proof.AesXts.PPC64LE.encrypt_noFrames
      Proof.AesXts.PPC64LE.encrypt_ct) (by
    sig_implies [Spec.Xts.aesEncryptUnitContract, Spec.Xts.aesUnitSig, Spec.Xts.aesUnitPre,
      Spec.Xts.aesEncryptUnitPost, unitPPC64LE, unitPre, unitPub, xtsOf, W, K, R, I, D, Len, S, schR, tschR, iR,
      dataR, scrR, PPC64LE.abi, PPC64LE.argRegs] [unitSat] using unitSat)

theorem decrypt_verified : Verified PPC64LE.target decrypt (Spec.Xts.aesDecryptUnitContract PPC64LE.abi) :=
  Verified.of_correct decrypt_correct
    (decrypt_ct Proof.AesXts.PPC64LE.encrypt_correct Proof.AesXts.PPC64LE.encrypt_noFrames
      Proof.AesXts.PPC64LE.encrypt_ct Proof.AesXts.PPC64LE.decrypt_correct Proof.AesXts.PPC64LE.decrypt_noFrames
      Proof.AesXts.PPC64LE.decrypt_ct) (by
    sig_implies [Spec.Xts.aesDecryptUnitContract, Spec.Xts.aesUnitSig, Spec.Xts.aesUnitPre,
      Spec.Xts.aesDecryptUnitPost, unitPPC64LE, unitPre, unitPub, xtsOf, W, K, R, I, D, Len, S, schR, tschR, iR,
      dataR, scrR, PPC64LE.abi, PPC64LE.argRegs] [unitSat] using unitSat)

end VG.Proof.AesXts.PPC64LE.Unit
