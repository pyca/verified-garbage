module

public import VerifiedGarbage.Impl.AesXts.RISCV64Unit
public import VerifiedGarbage.Proof.AesXts.Unit
public import VerifiedGarbage.Proof.AesXts.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Xts
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# XTS-AES of data units on RISC-V: the code between the calls

Each straight-line piece of `encrypt` and `decrypt`, run once, with the
registers and memory it leaves, and the swap loop (`swap_wp`), which leaves
`swapMem` (`Proof/AesXts/Unit.lean`), as on PPC64LE
(`Proof/AesXts/PPC64LE/Unit/Steps.lean`).
-/

@[expose] public section

namespace VG.Proof.AesXts.RISCV64.Unit

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesXts.RISCV64Unit
open VG.Impl.AesCbc.RISCV64 (mov)
open VG.Proof.AesXts.Unit (swapMem swapMem_step swapMem_lo swapMem_hi)
open VG.Spec.Aes (bytesAt)

/-- A callee-saved register is none of those that are not. -/
theorem pres_ne {r x : Reg} (hr : r ∈ preserved) (hx : x ∉ preserved) : r ≠ x :=
  fun e => hx (e ▸ hr)

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

theorem byte_rt (b : Byte) : (b.setWidth 64).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega

/-! ## Registers only -/

theorem setup_wp (s : State) :
    WP isa (.block setup) s fun s' =>
      s'.gpr .s1 = s.gpr .a0 ∧ s'.gpr .s2 = s.gpr .a2 ∧ s'.gpr .s4 = s.gpr .a4 ∧
      s'.gpr .s5 = s.gpr .a5 ∧ s'.gpr .s6 = s.gpr .a6 ∧
      (∀ r, r ≠ .s1 → r ≠ .s2 → r ≠ .s4 → r ≠ .s5 → r ≠ .s6 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold setup mov
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ =>
    wp_mv fun s₅ u₅ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ h₅ => ?_, ?_, ?_, ?_, ?_⟩
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
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

theorem tArgs_wp (s : State) :
    WP isa (.block tArgs) s fun s' =>
      s'.gpr .a0 = s.gpr .a1 ∧ s'.gpr .a1 = s.gpr .s2 ∧
      s'.gpr .a2 = s.gpr .s6 + BitVec.ofNat 64 zO ∧ s'.gpr .a3 = s.gpr .s6 + BitVec.ofNat 64 tO ∧
      s'.gpr .a4 = BitVec.ofNat 64 1 ∧ s'.gpr .a5 = s.gpr .s6 + BitVec.ofNat 64 wO ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold tArgs mov
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_addi (imm := zO) (by decide) fun s₃ u₃ =>
    wp_addi (imm := tO) (by decide) fun s₄ u₄ => wp_li (imm := 1) (by decide) fun s₅ u₅ =>
    wp_addi (imm := wO) (by decide) fun s₆ u₆ =>
    WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
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
  · rw [u₆.other _ (pres_ne hr (by decide)), u₅.other _ (pres_ne hr (by decide)),
      u₄.other _ (pres_ne hr (by decide)), u₃.other _ (pres_ne hr (by decide)),
      u₂.other _ (pres_ne hr (by decide)), u₁.other _ (pres_ne hr (by decide))]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

theorem argsAll_wp' (s : State) :
    WP isa (.block argsAll) s fun s' =>
      s'.gpr .a0 = s.gpr .s1 ∧ s'.gpr .a1 = s.gpr .s2 ∧
      s'.gpr .a2 = s.gpr .s6 + BitVec.ofNat 64 tO ∧ s'.gpr .a3 = s.gpr .s4 ∧
      s'.gpr .a4 = BitVec.ofNat 64 ((s.gpr .s5).toNat / 16) ∧ s'.gpr .a5 = s.gpr .s6 + BitVec.ofNat 64 wO ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold argsAll mov
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_addi (imm := tO) (by decide) fun s₃ u₃ =>
    wp_mv fun s₄ u₄ => wp_srl (by decide) fun s₅ u₅ => wp_addi (imm := wO) (by decide) fun s₆ u₆ =>
    WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
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
  · rw [u₆.other _ (pres_ne hr (by decide)), u₅.other _ (pres_ne hr (by decide)),
      u₄.other _ (pres_ne hr (by decide)), u₃.other _ (pres_ne hr (by decide)),
      u₂.other _ (pres_ne hr (by decide)), u₁.other _ (pres_ne hr (by decide))]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

theorem argsHead_wp' (s : State) (hm : 1 ≤ (s.gpr .s5).toNat / 16) :
    WP isa (.block argsHead) s fun s' =>
      s'.gpr .a0 = s.gpr .s1 ∧ s'.gpr .a1 = s.gpr .s2 ∧
      s'.gpr .a2 = s.gpr .s6 + BitVec.ofNat 64 tO ∧ s'.gpr .a3 = s.gpr .s4 ∧
      s'.gpr .a4 = BitVec.ofNat 64 ((s.gpr .s5).toNat / 16 - 1) ∧ s'.gpr .a5 = s.gpr .s6 + BitVec.ofNat 64 wO ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  rw [argsHead, WP.block_append_iff]
  refine WP.mono (argsAll_wp' s) fun s₁ ⟨a0, a1, a2, a3, a4, a5, cs, mem, rd, wr, sp⟩ =>
    wp_subi (imm := 1) (by decide) fun s₂ u₂ =>
    WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₂.other _ (by decide), a0]
  · rw [u₂.other _ (by decide), a1]
  · rw [u₂.other _ (by decide), a2]
  · rw [u₂.other _ (by decide), a3]
  · rw [u₂.gpr, a4]; exact Offset.ofNat_sub_ofNat hm
  · rw [u₂.other _ (by decide), a5]
  · rw [u₂.other _ (pres_ne hr (by decide)), cs r hr]
  · rw [u₂.mem, mem]
  · rw [u₂.rd, rd]
  · rw [u₂.wr, wr]
  · rw [u₂.sp, sp]

theorem split_wp' (s : State) :
    WP isa (.block split) s fun s' =>
      s'.gpr .t1 = BitVec.ofNat 64 (16 * ((s.gpr .s5).toNat / 16)) ∧
      s'.gpr .t2 = BitVec.ofNat 64 ((s.gpr .s5).toNat % 16) ∧
      (∀ r, r ≠ .t1 → r ≠ .t2 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have e : s.gpr .s5 - BitVec.ofNat 64 (16 * ((s.gpr .s5).toNat / 16)) =
      BitVec.ofNat 64 ((s.gpr .s5).toNat % 16) := by
    apply BitVec.eq_of_toNat_eq
    have := (s.gpr .s5).isLt
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * _) (by omega),
      Nat.mod_eq_of_lt (a := _ % 16) (by omega)]
    omega
  unfold split
  refine wp_srl (by decide) fun s₁ u₁ => wp_sll (by decide) fun s₂ u₂ => wp_sub fun s₃ u₃ =>
    WP.block_nil ⟨?_, ?_, fun r h₁ h₂ => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, shr4_shl4]
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), u₂.gpr, u₁.gpr, shr4_shl4, e]
  · rw [u₃.other _ h₂, u₂.other _ h₁, u₁.other _ h₁]
  · rw [u₃.mem, u₂.mem, u₁.mem]
  · rw [u₃.rd, u₂.rd, u₁.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr]
  · rw [u₃.sp, u₂.sp, u₁.sp]

theorem lastAddr_wp' (s : State) :
    WP isa (.block lastAddr) s fun s' => s'.gpr .t3 = s.gpr .s4 + s.gpr .t1 - BitVec.ofNat 64 16 ∧
      (∀ r, r ≠ .t3 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold lastAddr
  refine wp_add fun s₁ u₁ => wp_subi (imm := 16) (by decide) fun s₂ u₂ =>
    WP.block_nil ⟨?_, fun r h => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₂.gpr, u₁.gpr]
  · rw [u₂.other _ h, u₁.other _ h]
  · rw [u₂.mem, u₁.mem]
  · rw [u₂.rd, u₁.rd]
  · rw [u₂.wr, u₁.wr]
  · rw [u₂.sp, u₁.sp]

/-- The last whole block, from the bytes of the whole blocks. -/
theorem last_eq (p : Addr) {m : Nat} (hm : 1 ≤ m) :
    p + BitVec.ofNat 64 (16 * m) - BitVec.ofNat 64 16 = p + BitVec.ofNat 64 (16 * (m - 1)) := by
  rw [show 16 * m = 16 * (m - 1) + 16 by omega, ← Offset.add_add]
  exact BitVec.add_sub_cancel _ _

theorem argsL_wp' (s : State) {o : Nat} (ho : o < 2048) :
    WP isa (.block (argsL o)) s fun s' =>
      s'.gpr .a0 = s.gpr .s1 ∧ s'.gpr .a1 = s.gpr .s2 ∧
      s'.gpr .a2 = s.gpr .s6 + BitVec.ofNat 64 o ∧ s'.gpr .a3 = s.gpr .s4 + s.gpr .t1 - BitVec.ofNat 64 16 ∧
      s'.gpr .a4 = BitVec.ofNat 64 1 ∧ s'.gpr .a5 = s.gpr .s6 + BitVec.ofNat 64 wO ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold argsL mov
  refine wp_add fun s₁ u₁ => wp_subi (imm := 16) (by decide) fun s₂ u₂ => wp_mv fun s₃ u₃ =>
    wp_mv fun s₄ u₄ => wp_addi ho fun s₅ u₅ => wp_li (imm := 1) (by decide) fun s₆ u₆ =>
    wp_addi (imm := wO) (by decide) fun s₇ u₇ =>
    WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
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
  · rw [u₇.other _ (pres_ne hr (by decide)), u₆.other _ (pres_ne hr (by decide)),
      u₅.other _ (pres_ne hr (by decide)), u₄.other _ (pres_ne hr (by decide)),
      u₃.other _ (pres_ne hr (by decide)), u₂.other _ (pres_ne hr (by decide)),
      u₁.other _ (pres_ne hr (by decide))]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-! ## Memory -/

theorem zeroZ_wp (s : State) {Z : Addr} (hz : s.gpr .s6 + BitVec.ofNat 64 zO = Z)
    (hw : ∀ i < 16, InRegions s.wr (Z + BitVec.ofNat 64 i) 1) :
    WP isa (.block zeroZ) s fun s' => (∀ r, r ≠ .t1 → s'.gpr r = s.gpr r) ∧
      bytesAt s'.mem Z 16 = List.replicate 16 0 ∧ Frame [⟨Z, 16⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have ez (i : Nat) : s.gpr .s6 + BitVec.ofNat 64 (zO + i) = Z + BitVec.ofNat 64 i := by
    rw [← hz, Offset.add_add]
  refine WP.mono (Bytes.storeBytes_ok (tmp := .t1) (dst := .s6) (doff := zO) (bs := List.replicate 16 0)
    (by decide) (by decide) (by decide) fun i hi => by rw [ez]; exact hw i (by simpa using hi))
    fun s' h => ⟨h.gpr, ?_, ?_, h.rd, h.wr, h.sp⟩
  · apply List.ext_getElem (by simp [bytesAt])
    intro j h₁ _
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    have := h.stored j (by simpa using h₁)
    rw [ez] at this
    simp only [bytesAt, List.getElem_map, List.getElem_range, this, List.getElem_replicate,
      List.getD_eq_getElem?_getD, List.getElem?_replicate, h₁, ite_true, Option.getD_some]
    rfl
  · have := h.frame
    rwa [hz, List.length_replicate] at this

/-! ## The swap -/

theorem swapStep_wp (s : State) {L : Addr} {k b : Nat} (hx : s.gpr .t3 = L + BitVec.ofNat 64 k)
    (hc : s.gpr .t2 = BitVec.ofNat 64 b) (hb : 1 ≤ b)
    (w₀ : InRegions s.wr (L + BitVec.ofNat 64 k) 1) (w₁ : InRegions s.wr (L + BitVec.ofNat 64 (16 + k)) 1) :
    WP isa (.block swapBody) s fun s' =>
      s'.mem = (s.mem.writeW (L + BitVec.ofNat 64 k) (s.mem (L + BitVec.ofNat 64 (16 + k)))).writeW
        (L + BitVec.ofNat 64 (16 + k)) (s.mem (L + BitVec.ofNat 64 k)) ∧
      s'.gpr .t3 = L + BitVec.ofNat 64 (k + 1) ∧ s'.gpr .t2 = BitVec.ofNat 64 (b - 1) ∧
      (∀ r, r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have r₀ : InRegions (s.rd ++ s.wr) (L + BitVec.ofNat 64 k) 1 :=
    let ⟨r, hr, c⟩ := w₀; ⟨r, List.mem_append_right _ hr, c⟩
  have r₁ : InRegions (s.rd ++ s.wr) (L + BitVec.ofNat 64 (16 + k)) 1 :=
    let ⟨r, hr, c⟩ := w₁; ⟨r, List.mem_append_right _ hr, c⟩
  have e16 : L + BitVec.ofNat 64 k + BitVec.ofNat 64 16 = L + BitVec.ofNat 64 (16 + k) := by
    rw [Offset.add_add, Nat.add_comm]
  unfold swapBody
  refine wp_lbu (a := L + BitVec.ofNat 64 k) (by decide) (by rw [hx]; simp) r₀ fun s₁ u₁ => ?_
  refine wp_lbu (a := L + BitVec.ofNat 64 (16 + k)) (by decide) (by rw [u₁.other _ (by decide), hx, e16])
    (by rw [u₁.rd, u₁.wr]; exact r₁) fun s₂ u₂ => ?_
  refine wp_sb (a := L + BitVec.ofNat 64 k) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hx]; simp)
    (by rw [u₂.wr, u₁.wr]; exact w₀) fun s₃ u₃ => ?_
  refine wp_sb (a := L + BitVec.ofNat 64 (16 + k)) (by decide)
    (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hx, e16])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact w₁) fun s₄ u₄ => ?_
  refine wp_addi (imm := 1) (by decide) fun s₅ u₅ => wp_subi (imm := 1) (by decide) fun s₆ u₆ =>
    WP.block_nil ⟨?_, ?_, ?_, fun r h₂ h₃ h₄ h₅ => ?_, ?_, ?_, ?_⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₃.mem, u₂.gpr, u₂.other _ (by decide : Reg.t4 ≠ .t5), u₂.mem,
      u₁.gpr, u₁.mem, byte_rt, byte_rt]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hx,
      Offset.add_add]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hc]
    exact Offset.ofNat_sub_ofNat hb
  · rw [u₆.other _ h₂, u₅.other _ h₃, u₄.gpr, u₃.gpr, u₂.other _ h₅, u₁.other _ h₄]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

theorem swap_wp (s : State) {L : Addr} {b : Nat} (hb₀ : 0 < b) (hb : b < 16) (hx : s.gpr .t3 = L)
    (hc : s.gpr .t2 = BitVec.ofNat 64 b) (hw : ∀ i < 16 + b, InRegions s.wr (L + BitVec.ofNat 64 i) 1) :
    WP isa swap s fun s' => s'.mem = swapMem s.mem L b ∧
      (∀ r, r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine WP.loop (M := isa) (body := .block swapBody) (c := .nonzero .t2)
    (fun (n : Nat) (t : State) => ∃ k, n = b - k ∧ k < b ∧ t.gpr .t3 = L + BitVec.ofNat 64 k ∧
      t.gpr .t2 = BitVec.ofNat 64 (b - k) ∧ t.mem = swapMem s.mem L k ∧
      (∀ r, r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.sp = s.sp) ?_ (b - 0) _
    ⟨0, rfl, hb₀, by rw [hx, BitVec.add_zero], hc, (Proof.AesXts.Unit.swapMem_zero _ _).symm,
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro n t ⟨k, rfl, hk, x3, x2, mem, g, rd, wr, sp⟩
  refine WP.mono (swapStep_wp t (k := k) (b := b - k) x3 x2 (by omega) (by rw [wr]; exact hw k (by omega))
    (by rw [wr]; exact hw (16 + k) (by omega))) fun t' ⟨mem', x3', x2', g', rd', wr', sp'⟩ => ?_
  have hmem : t'.mem = swapMem s.mem L (k + 1) := by
    rw [mem', mem, swapMem_lo _ _ (Nat.le_refl k) (by omega), swapMem_hi _ _ (Nat.le_refl k) (by omega),
      swapMem_step _ _ (by omega)]
  have hz := eval_nonzero_ofNat t' .t2 (k := b - k - 1) (by omega) x2'
  have gg : ∀ r, r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ h₄ => by
    rw [g' r h₁ h₂ h₃ h₄, g r h₁ h₂ h₃ h₄]
  by_cases he : k + 1 = b
  · left
    refine ⟨by rw [hz]; simp [show b - k - 1 = 0 by omega], by rw [hmem, he], gg, by rw [rd', rd],
      by rw [wr', wr], by rw [sp', sp]⟩
  · right
    refine ⟨by rw [hz]; simp [show b - k - 1 ≠ 0 by omega], b - (k + 1), by omega, k + 1, rfl, by omega, x3',
      by rw [x2', show b - k - 1 = b - (k + 1) by omega], hmem, gg, by rw [rd', rd], by rw [wr', wr],
      by rw [sp', sp]⟩

/-! ## The next tweak -/

theorem nextT_wp (s : State) {T Z : Addr} (ht : s.gpr .s6 + BitVec.ofNat 64 tO = T)
    (hz : s.gpr .s6 + BitVec.ofNat 64 zO = Z) (hd : (⟨Z, 16⟩ : Region).Disjoint ⟨T, 16⟩)
    (rT : ∀ i < 16, InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 i) 1)
    (wZ : ∀ i < 16, InRegions s.wr (Z + BitVec.ofNat 64 i) 1)
    (inR : ∀ d, d + 4 ≤ 16 → InRegions (s.rd ++ s.wr) (Z + BitVec.ofNat 64 d) 4)
    (inW : ∀ d, d + 4 ≤ 16 → InRegions s.wr (Z + BitVec.ofNat 64 d) 4) :
    WP isa (.block nextT) s fun s' =>
      (∀ r, r ∉ AesXts.RISCV64.mulRegs → r ≠ .s3 → s'.gpr r = s.gpr r) ∧ s'.gpr .s3 = Z ∧
      Frame [⟨Z, 16⟩] s.mem s'.mem ∧ bytesAt s'.mem Z 16 = Spec.Xts.mulAlpha (bytesAt s.mem T 16) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have et (i : Nat) : s.gpr .s6 + BitVec.ofNat 64 (tO + i) = T + BitVec.ofNat 64 i := by
    rw [← ht, Offset.add_add]
  have ez (i : Nat) : s.gpr .s6 + BitVec.ofNat 64 (zO + i) = Z + BitVec.ofNat 64 i := by
    rw [← hz, Offset.add_add]
  rw [nextT, List.singleton_append]
  refine wp_addi (imm := zO) (by decide) fun s₁ u₁ => ?_
  have g6 : s₁.gpr .s6 = s.gpr .s6 := u₁.other _ (by decide)
  rw [List.append_eq, WP.block_append_iff]
  refine WP.mono (Bytes.copyBytes_ok (s := s₁) (tmp := .t3) (src := .s6) (dst := .s6) (soff := tO)
    (doff := zO) (n := 16) (by decide) (by decide) (by decide) (by decide)
    (fun i hi => by rw [g6, et, u₁.rd, u₁.wr]; exact rT i hi)
    (fun i hi => by rw [g6, ez, u₁.wr]; exact wZ i hi)
    (fun i hi hc => by
      rw [g6, hz, et] at hc
      exact hd _ hc (Offset.contains_base _ (by omega) (by omega)))) fun s₂ h₂ => ?_
  have hb₂ : bytesAt s₂.mem Z 16 = bytesAt s.mem T 16 := by
    apply List.ext_getElem (by simp [bytesAt])
    intro j h₁ _
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    have := h₂.copied j h₁
    rw [g6, ez, et, u₁.mem] at this
    simp [bytesAt, this]
  have f₂ : Frame [⟨Z, 16⟩] s.mem s₂.mem := by
    have := h₂.frame
    rwa [g6, hz, u₁.mem] at this
  have s3₂ : s₂.gpr .s3 = Z := by rw [h₂.gpr _ (by decide), u₁.gpr, hz]
  rw [← List.append_nil Impl.AesXts.RISCV64.mulA]
  refine AesXts.RISCV64.mulA_wp s3₂ (by rw [h₂.rd, h₂.wr, u₁.rd, u₁.wr]; exact inR)
    (by rw [h₂.wr, u₁.wr]; exact inW) fun s₃ g₃ b₃ f₃ rd₃ wr₃ sp₃ => WP.block_nil ?_
  refine ⟨fun r h₁ h₂' => ?_, by rw [g₃ _ (by decide), s3₂], f₂.trans f₃, by rw [b₃, hb₂],
    by rw [rd₃, h₂.rd, u₁.rd], by rw [wr₃, h₂.wr, u₁.wr], by rw [sp₃, h₂.sp, u₁.sp]⟩
  have h3 : r ≠ .t3 := fun e => h₁ (by rw [e]; decide)
  rw [g₃ r h₁, h₂.gpr r h3, u₁.other r h₂']

end VG.Proof.AesXts.RISCV64.Unit
