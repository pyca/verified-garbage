module

public import VerifiedGarbage.Spec.Cmac.Contract
public import VerifiedGarbage.Proof.Framework.X86.ArgTaint
import VerifiedGarbage.Proof.CmacAes.X86.UpdateCorrect
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Spec.Cmac.Contract
meta import VerifiedGarbage.Proof.Framework.X86.ArgTaint
meta import VerifiedGarbage.Proof.CmacAes.X86.UpdateCorrect
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.CmacAes.X86.UpdateCT
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.CmacAes.X86.UpdateCT
meta import VerifiedGarbage.Proof.Cmac.Block
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.CmacAes.X86.UpdateLoop
meta import VerifiedGarbage.Proof.CmacAes.X86.UpdateLoop
public import VerifiedGarbage.Proof.Cmac.Dbl32
meta import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.SpTest
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.SpTest
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-! ### `CmacAes.X86.Subkeys`, which this module and modules that import it used -/

section

@[expose] public section

section

/-!
# AES-CMAC on x86: doubling a block in four 32-bit words

`dbl src dst` loads a block as four byte-reversed words (`bswap`), the block
as a big-endian integer (`Cmac.ofBytes_rev4`), doubles the integer a word at a
time (`Cmac.dbl_words4`, shifting by `add r, r`), and stores the words
byte-reversed again (`Cmac.le4_rev4`).
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.MdStream.X86 (Upd Mupd wp_mov wp_movi wp_movm wp_store wp_add wp_sub wp_andi wp_or wp_shr wp_bswap)

theorem bswap_eq (a : BitVec 32) : bswap a = byteRev32 a := rfl

theorem add_self_shl (x : BitVec 32) : x + x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega_arith

/-- The memory after `dbl src dst`, with `ebx` pointing at `A`. -/
def dblMem (m : Mem) (A : Addr) (src dst : Nat) : Mem :=
  let P := A + BitVec.ofNat 64 src
  let b₀ := byteRev32 (m.readW P 32)
  let b₁ := byteRev32 (m.readW (P + BitVec.ofNat 64 4) 32)
  let b₂ := byteRev32 (m.readW (P + BitVec.ofNat 64 8) 32)
  let b₃ := byteRev32 (m.readW (P + BitVec.ofNat 64 12) 32)
  Proof.Cmac.store4 m (A + BitVec.ofNat 64 dst) (byteRev32 (Proof.Cmac.dblW0 b₀ b₁))
    (byteRev32 (Proof.Cmac.dblW0 b₁ b₂)) (byteRev32 (Proof.Cmac.dblW0 b₂ b₃)) (byteRev32 (Proof.Cmac.dblW3 b₀ b₃))

theorem dblMem_frame (m : Mem) (A : Addr) (src dst : Nat) :
    Frame [⟨A + BitVec.ofNat 64 dst, 16⟩] m (dblMem m A src dst) :=
  Proof.Cmac.frame_store4 _ _ _ _ _

theorem dblMem_bytes (m : Mem) (A : Addr) (src dst : Nat) :
    Spec.Aes.bytesAt (dblMem m A src dst) (A + BitVec.ofNat 64 dst) 16 =
      Spec.Cmac.dbl 16 (Spec.Aes.bytesAt m (A + BitVec.ofNat 64 src) 16) := by
  simp only [dblMem]
  rw [Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_rev4, Proof.Cmac.dbl_words4,
    Proof.Cmac.dbl_eq (Proof.Cmac.bytesAt_length _ _ _), Proof.Cmac.ofBytes_rev4]

/-- `dbl src dst`, with `ebx` pointing at `K`. -/
theorem dbl_wp {is : List Instr} {s : State} {Q : State → Prop} {K : BitVec 32} {src dst : Nat}
    (hb : s.gpr .ebx = K) (fs : K.toNat + src + 16 ≤ 2 ^ 32) (fd : K.toNat + dst + 16 ≤ 2 ^ 32)
    (rS : Covers [⟨K.setWidth 64 + BitVec.ofNat 64 src, 16⟩] (s.rd ++ s.wr))
    (wD : Covers [⟨K.setWidth 64 + BitVec.ofNat 64 dst, 16⟩] s.wr)
    (k : ∀ s', (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → r ≠ .ebp → s'.gpr r = s.gpr r) →
      s'.mem = dblMem s.mem (K.setWidth 64) src dst → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (dbl src dst ++ is)) s Q := by
  simp only [dbl, List.cons_append, List.nil_append]
  refine wp_movm (a := K.setWidth 64 + BitVec.ofNat 64 src) (by rw [ea_at', hb]; exact addr_eq (by omega_arith))
    (in_word0 rS) fun s₁ u₁ => ?_
  refine wp_movm (a := K.setWidth 64 + BitVec.ofNat 64 src + BitVec.ofNat 64 4)
    (by rw [ea_at', u₁.other _ (by decide), hb]; exact addr_word 4 fs (by decide))
    (by rw [u₁.rd, u₁.wr]; exact in_word rS (by decide)) fun s₂ u₂ => ?_
  refine wp_movm (a := K.setWidth 64 + BitVec.ofNat 64 src + BitVec.ofNat 64 8)
    (by rw [ea_at', u₂.other _ (by decide), u₁.other _ (by decide), hb]; exact addr_word 8 fs (by decide))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact in_word rS (by decide)) fun s₃ u₃ => ?_
  refine wp_movm (a := K.setWidth 64 + BitVec.ofNat 64 src + BitVec.ofNat 64 12)
    (by rw [ea_at', u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hb]
        exact addr_word 12 fs (by decide))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact in_word rS (by decide)) fun s₄ u₄ => ?_
  refine wp_bswap fun s₅ u₅ => wp_bswap fun s₆ u₆ => wp_bswap fun s₇ u₇ => wp_bswap fun s₈ u₈ => ?_
  refine wp_mov fun s₉ u₉ => wp_shr (by decide) fun s₁₀ u₁₀ => wp_movi fun s₁₁ u₁₁ =>
    wp_sub fun s₁₂ u₁₂ _ => wp_andi fun s₁₃ u₁₃ => ?_
  refine wp_add fun s₁₄ u₁₄ => wp_mov fun s₁₅ u₁₅ => wp_shr (by decide) fun s₁₆ u₁₆ => wp_or fun s₁₇ u₁₇ => ?_
  refine wp_add fun s₁₈ u₁₈ => wp_mov fun s₁₉ u₁₉ => wp_shr (by decide) fun s₂₀ u₂₀ => wp_or fun s₂₁ u₂₁ => ?_
  refine wp_add fun s₂₂ u₂₂ => wp_mov fun s₂₃ u₂₃ => wp_shr (by decide) fun s₂₄ u₂₄ => wp_or fun s₂₅ u₂₅ => ?_
  refine wp_add fun s₂₆ u₂₆ => wp_xor fun s₂₇ u₂₇ => ?_
  refine wp_bswap fun s₂₈ u₂₈ => wp_bswap fun s₂₉ u₂₉ => wp_bswap fun s₃₀ u₃₀ => wp_bswap fun s₃₁ u₃₁ => ?_
  obtain g : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → r ≠ .ebp → s₃₁.gpr r = s.gpr r :=
    fun r ha hc hd hs hi hp => by
      rw [u₃₁.other _ hs, u₃₀.other _ hd, u₂₉.other _ hc, u₂₈.other _ ha, u₂₇.other _ hs, u₂₆.other _ hs,
        u₂₅.other _ hd, u₂₄.other _ hi, u₂₃.other _ hi, u₂₂.other _ hd, u₂₁.other _ hc, u₂₀.other _ hi,
        u₁₉.other _ hi, u₁₈.other _ hc, u₁₇.other _ ha, u₁₆.other _ hi, u₁₅.other _ hi, u₁₄.other _ ha,
        u₁₃.other _ hp, u₁₂.other _ hp, u₁₁.other _ hp, u₁₀.other _ hi, u₉.other _ hi, u₈.other _ hs,
        u₇.other _ hd, u₆.other _ hc, u₅.other _ ha, u₄.other _ hs, u₃.other _ hd, u₂.other _ hc, u₁.other _ ha]
  obtain gb : s₃₁.gpr .ebx = K := by
    rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hb]
  obtain m31 : s₃₁.mem = s.mem := by
    rw [u₃₁.mem, u₃₀.mem, u₂₉.mem, u₂₈.mem, u₂₇.mem, u₂₆.mem, u₂₅.mem, u₂₄.mem, u₂₃.mem, u₂₂.mem, u₂₁.mem,
      u₂₀.mem, u₁₉.mem, u₁₈.mem, u₁₇.mem, u₁₆.mem, u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem,
      u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain rd31 : s₃₁.rd = s.rd := by
    rw [u₃₁.rd, u₃₀.rd, u₂₉.rd, u₂₈.rd, u₂₇.rd, u₂₆.rd, u₂₅.rd, u₂₄.rd, u₂₃.rd, u₂₂.rd, u₂₁.rd,
      u₂₀.rd, u₁₉.rd, u₁₈.rd, u₁₇.rd, u₁₆.rd, u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd,
      u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr31 : s₃₁.wr = s.wr := by
    rw [u₃₁.wr, u₃₀.wr, u₂₉.wr, u₂₈.wr, u₂₇.wr, u₂₆.wr, u₂₅.wr, u₂₄.wr, u₂₃.wr, u₂₂.wr, u₂₁.wr,
      u₂₀.wr, u₁₉.wr, u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr, u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr,
      u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  -- The four words, byte-reversed.
  obtain b₀ : s₈.gpr .eax = byteRev32 (s.mem.readW (K.setWidth 64 + BitVec.ofNat 64 src) 32) := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, bswap_eq]
  obtain b₁ : s₈.gpr .ecx = byteRev32 (s.mem.readW (K.setWidth 64 + BitVec.ofNat 64 src + BitVec.ofNat 64 4) 32) := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.mem, bswap_eq]
  obtain b₂ : s₈.gpr .edx = byteRev32 (s.mem.readW (K.setWidth 64 + BitVec.ofNat 64 src + BitVec.ofNat 64 8) 32) := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.mem, u₁.mem, bswap_eq]
  obtain b₃ : s₈.gpr .esi = byteRev32 (s.mem.readW (K.setWidth 64 + BitVec.ofNat 64 src + BitVec.ofNat 64 12) 32) := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem,
      u₁.mem, bswap_eq]
  obtain v : s₃₁.gpr .eax = byteRev32 (Proof.Cmac.dblW0 (s₈.gpr .eax) (s₈.gpr .ecx)) ∧
      s₃₁.gpr .ecx = byteRev32 (Proof.Cmac.dblW0 (s₈.gpr .ecx) (s₈.gpr .edx)) ∧
      s₃₁.gpr .edx = byteRev32 (Proof.Cmac.dblW0 (s₈.gpr .edx) (s₈.gpr .esi)) ∧
      s₃₁.gpr .esi = byteRev32 (Proof.Cmac.dblW3 (s₈.gpr .eax) (s₈.gpr .esi)) := by
    simp (disch := decide) only [u₃₁.gpr, u₃₁.other, u₃₀.gpr, u₃₀.other, u₂₉.gpr, u₂₉.other, u₂₈.gpr, u₂₈.other, u₂₇.gpr, u₂₇.other, u₂₆.gpr, u₂₆.other, u₂₅.gpr, u₂₅.other, u₂₄.gpr, u₂₄.other, u₂₃.gpr, u₂₃.other, u₂₂.gpr, u₂₂.other, u₂₁.gpr, u₂₁.other, u₂₀.gpr, u₂₀.other, u₁₉.gpr, u₁₉.other, u₁₈.gpr, u₁₈.other, u₁₇.gpr, u₁₇.other, u₁₆.gpr, u₁₆.other, u₁₅.gpr, u₁₅.other, u₁₄.gpr, u₁₄.other, u₁₃.gpr, u₁₃.other, u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other,
      bswap_eq, add_self_shl, Proof.Cmac.dblW0, Proof.Cmac.dblW3, and_self]
  obtain ⟨v₀, v₁, v₂, v₃⟩ := v
  refine wp_store (a := K.setWidth 64 + BitVec.ofNat 64 dst) (by rw [ea_at', gb]; exact addr_eq (by omega_arith))
    (by rw [wr31]; exact in_word0 wD) fun s₃₂ v₃₂ => ?_
  refine wp_store (a := K.setWidth 64 + BitVec.ofNat 64 dst + BitVec.ofNat 64 4)
    (by rw [ea_at', v₃₂.gpr, gb]; exact addr_word 4 fd (by decide))
    (by rw [v₃₂.wr, wr31]; exact in_word wD (by decide)) fun s₃₃ v₃₃ => ?_
  refine wp_store (a := K.setWidth 64 + BitVec.ofNat 64 dst + BitVec.ofNat 64 8)
    (by rw [ea_at', v₃₃.gpr, v₃₂.gpr, gb]; exact addr_word 8 fd (by decide))
    (by rw [v₃₃.wr, v₃₂.wr, wr31]; exact in_word wD (by decide)) fun s₃₄ v₃₄ => ?_
  refine wp_store (a := K.setWidth 64 + BitVec.ofNat 64 dst + BitVec.ofNat 64 12)
    (by rw [ea_at', v₃₄.gpr, v₃₃.gpr, v₃₂.gpr, gb]; exact addr_word 12 fd (by decide))
    (by rw [v₃₄.wr, v₃₃.wr, v₃₂.wr, wr31]; exact in_word wD (by decide)) fun s₃₅ v₃₅ => k s₃₅ ?_ ?_ ?_ ?_
  · intro r ha hc hd hs hi hp
    rw [v₃₅.gpr, v₃₄.gpr, v₃₃.gpr, v₃₂.gpr, g r ha hc hd hs hi hp]
  · rw [v₃₅.mem, v₃₄.mem, v₃₃.mem, v₃₂.mem, v₃₄.gpr, v₃₃.gpr, v₃₂.gpr, m31, v₀, v₁, v₂, v₃, b₀, b₁, b₂, b₃]
    rfl
  · rw [v₃₅.rd, v₃₄.rd, v₃₃.rd, v₃₂.rd, rd31]
  · rw [v₃₅.wr, v₃₄.wr, v₃₃.wr, v₃₂.wr, wr31]

end VG.Proof.CmacAes.X86

end

/-!
# AES-CMAC on x86: `vg_cmac_aes_subkeys`

`L = CIPH_K(0)` is computed into the first block of the subkeys (a zero
counter block and a zero data block), then doubled there (`K1`) and into the
second block (`K2`). Only the subkeys, the scratch buffer and the 28 bytes
below `esp` change, so the stack arguments, which are reloaded from the stack,
and the return address are intact.
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.Aes.X86 (Ctr32Impl)

variable (v : Ctr32Impl)
open VG.Proof.MdStream.X86 (Upd wp_mov wp_movi wp_addi)

section
variable (s₀ : State)

/-- The subkeys. -/
abbrev Kb : BitVec 32 := arg s₀ 2
/-- The scratch buffer. -/
abbrev Sc : BitVec 32 := arg s₀ 3

abbrev kR : Region := ⟨(Kb s₀).setWidth 64, 32⟩
abbrev scR : Region := ⟨(Sc s₀).setWidth 64, 2176⟩
abbrev kArgsR : Region := ⟨argAddr s₀ 0, 16⟩

/-- The regions the function writes, with the stack below it. -/
abbrev SBig : List Region := [kR s₀, scR s₀, stkR s₀]

/-- The memory after saving the registers in the scratch buffer. -/
def sSaved : Mem := Spill.saveMem s₀.mem ((Sc s₀).setWidth 64 + BitVec.ofNat 64 ·) s₀.gpr saved

/-- The memory before the call. -/
def sPreMem : Mem :=
  Proof.Cmac.zero4 (Proof.Cmac.zero4 (sSaved s₀) ((Sc s₀).setWidth 64 + BitVec.ofNat 64 2048)) ((Kb s₀).setWidth 64)

end

/-- The precondition, by name. -/
structure SPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀, kArgsR s₀]
  wr : s₀.wr = [kR s₀, scR s₀]
  sch_k : (schR s₀).Disjoint (kR s₀)
  sch_scr : (schR s₀).Disjoint (scR s₀)
  k_scr : (kR s₀).Disjoint (scR s₀)
  args_k : (kArgsR s₀).Disjoint (kR s₀)
  args_scr : (kArgsR s₀).Disjoint (scR s₀)
  ret_k : (retR s₀).Disjoint (kR s₀)
  ret_scr : (retR s₀).Disjoint (scR s₀)
  b_sch : (stkR s₀).Disjoint (schR s₀)
  b_k : (stkR s₀).Disjoint (kR s₀)
  b_scr : (stkR s₀).Disjoint (scR s₀)
  sch_fit : (W s₀).toNat + 240 ≤ 2 ^ 32
  k_fit : (Kb s₀).toNat + 32 ≤ 2 ^ 32
  scr_fit : (Sc s₀).toNat + 2176 ≤ 2 ^ 32
  esp32 : 32 ≤ (E s₀).toNat
  esp_fit : (E s₀).toNat + 20 ≤ 2 ^ 32
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem SPre.of {s₀ : State} (h : subkeysX86.pre s₀) : SPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r⟩

/-! ## Addresses and regions -/

theorem ret_stk (s₀ : State) : (retR s₀).Disjoint (stkR s₀) := by
  have := Offset.disjoint_below_above ((E s₀).setWidth 64) (m := 32) (a := 0) (l := 4) (by decide)
  rw [add0] at this
  exact this.symm

theorem sSaved_frame (s₀ : State) : Frame [scR s₀] s₀.mem (sSaved s₀) :=
  Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p hp =>
    have := saved_bound p hp; Offset.contains_base _ (by omega_arith) (by omega_arith)

section
variable {s₀ : State} (hp : SPre s₀)
include hp

theorem SPre.below_eq : below (E s₀) 32 = stkR s₀ := by
  simp only [below]; rw [Taint.sub_setWidth hp.esp32]

theorem SPre.argA {i : Nat} (hi : i < 4) : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have : (s₀.gpr .esp).toNat + 20 ≤ 2 ^ 32 := hp.esp_fit
  simp only [argAddr]
  rw [show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * i) from rfl,
    show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * 0) from rfl,
    addr_eq (by omega_arith), addr_eq (by omega_arith), Offset.add_add]

theorem SPre.arg_sub {i : Nat} (hi : i < 4) : Region.Sub ⟨argAddr s₀ i, 4⟩ (kArgsR s₀) := by
  rw [hp.argA hi]; exact Offset.sub_base _ (by omega_arith)

theorem SPre.arg_in {i : Nat} (hi : i < 4) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 := by
  refine ⟨kArgsR s₀, by simp [hp.rd], ?_⟩
  rw [hp.argA hi]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)

theorem SPre.args_stk : (kArgsR s₀).Disjoint (stkR s₀) := by
  have : (s₀.gpr .esp).toNat + 20 ≤ 2 ^ 32 := hp.esp_fit
  obtain e : argAddr s₀ 0 = (E s₀).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega_arith)
  show Region.Disjoint ⟨argAddr s₀ 0, 16⟩ _
  rw [e]; exact (Offset.disjoint_below_above _ (by decide)).symm

/-- The stack arguments are unchanged where only `SBig` changes. -/
theorem SPre.arg_keep {m : Mem} (hf : Frame (SBig s₀) s₀.mem m) {i : Nat} (hi : i < 4) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.args_k.sub_left (hp.arg_sub hi)
    · exact hp.args_scr.sub_left (hp.arg_sub hi)
    · exact hp.args_stk.sub_left (hp.arg_sub hi)) (by decide)

theorem SPre.sched_bytes {m : Mem} (hf : Frame (SBig s₀) s₀.mem m) :
    Spec.Aes.bytesAt m ((W s₀).setWidth 64) (16 * (R s₀ + 1)) =
      Spec.Aes.bytesAt s₀.mem ((W s₀).setWidth 64) (16 * (R s₀ + 1)) := by
  obtain hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_arith
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.sch_k.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)
  · exact hp.b_sch.symm.sub_left (Region.sub_prefix hR)

theorem SPre.ret_keep {m : Mem} (hf : Frame (SBig s₀) s₀.mem m) :
    m.readW ((E s₀).setWidth 64) 32 = s₀.mem.readW ((E s₀).setWidth 64) 32 :=
  hf.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_k
    · exact hp.ret_scr
    · exact ret_stk s₀) (by decide)

theorem SPre.cA : (Sc s₀ + BitVec.ofNat 32 2048).setWidth 64 = (Sc s₀).setWidth 64 + BitVec.ofNat 64 2048 :=
  addr_eq (by have := hp.scr_fit; omega_arith)

end

/-- The frame of the code that changes only the subkeys, the scratch buffer
but the saved registers, and the stack below `esp`. -/
theorem sbig_of {s₀ : State} {m : Mem}
    (hf : Frame [kR s₀, ⟨(Sc s₀).setWidth 64, 2064⟩, stkR s₀] (sSaved s₀) m) : Frame (SBig s₀) s₀.mem m :=
  ((sSaved_frame s₀).mono (by simp)).trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨kR s₀, by simp, fun _ h => h⟩
    · exact ⟨scR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)

/-! ## Before the call -/

/-- What the code before the call leaves. -/
structure SAfter (s₀ s : State) : Prop where
  pre : CtrPre s (W s₀) (Sc s₀ + BitVec.ofNat 32 2048) (Kb s₀) (Sc s₀) (R s₀)
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = sPreMem s₀

theorem subkeysPre_eq : subkeysPre = .mov .eax (argOp 3) :: (saved.map (fun p => Instr.store (at_ .eax p.2) p.1) ++
    (.mov .ebp (.reg .eax) :: .mov .ebx (argOp 2) :: (zero4 .ebp 2048 ++ (zero4 .ebx 0 ++ ctrArgs)))) := rfl

theorem sPreMem_frame (s₀ : State) :
    Frame [kR s₀, ⟨(Sc s₀).setWidth 64, 2064⟩, stkR s₀] (sSaved s₀) (sPreMem s₀) :=
  ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨(Sc s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩).trans
  ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨kR s₀, by simp, Region.sub_prefix (by decide)⟩)

theorem spre_wp {s₀ : State} (hp : SPre s₀) : WP isa (.block subkeysPre) s₀ (SAfter s₀) := by
  have hsc := hp.scr_fit
  have hk := hp.k_fit
  have cA := hp.cA
  rw [subkeysPre_eq]
  refine wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  have h₁ : s₁.gpr .eax = Sc s₀ := u₁.gpr
  refine Spill.save_ofNat_ok saved saved_fits (by rw [h₁]; omega_arith) (fun p hp' => ?_) fun s₂ u₂ => ?_
  · have hb := saved_bound p hp'
    rw [h₁, u₁.wr, hp.wr]
    exact ⟨scR s₀, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain hm₂ : s₂.mem = sSaved s₀ := by
    rw [u₂.mem, u₁.mem, h₁, sSaved]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (saved_ne_eax p hp')
  obtain esp₂ : s₂.gpr .esp = E s₀ := by rw [u₂.gpr, u₁.other _ (by decide)]
  obtain rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]
  obtain big₂ : Frame (SBig s₀) s₀.mem s₂.mem := by rw [hm₂]; exact (sSaved_frame s₀).mono (by simp)
  refine wp_mov fun s₃ u₃ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), esp₂])
    (by rw [u₃.rd, u₃.wr, rw₂]; exact hp.arg_in (by decide))
    (by rw [u₃.mem]; exact hp.arg_keep big₂ (by decide)) fun s₄ u₄ => ?_
  obtain p₄ : s₄.gpr .ebp = Sc s₀ := by rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, h₁]
  have b₄ : s₄.gpr .ebx = Kb s₀ := u₄.gpr
  obtain w₄ : s₄.wr = s₀.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine zero4_ok (b := .ebp) (d := 2048) (by decide) (by rw [p₄]; omega_arith) ?_ fun s₅ g₅ m₅ rd₅ wr₅ => ?_
  · rw [p₄, w₄, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR s₀, by simp, 2048, rfl, by simp⟩
  obtain b₅ : s₅.gpr .ebx = Kb s₀ := by rw [g₅ _ (by decide), b₄]
  refine zero4_ok (b := .ebx) (d := 0) (by decide) (by rw [b₅]; omega_arith) ?_ fun s₆ g₆ m₆ rd₆ wr₆ => ?_
  · rw [b₅, add0, wr₅, w₄, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨kR s₀, by simp, 0, by simp, by simp⟩
  obtain esp₆ : s₆.gpr .esp = E s₀ := by
    rw [g₆ _ (by decide), g₅ _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂]
  obtain mem₆ : s₆.mem = sPreMem s₀ := by
    rw [m₆, b₅, add0, m₅, p₄, u₄.mem, u₃.mem, hm₂]; rfl
  obtain big₆ : Frame (SBig s₀) s₀.mem s₆.mem := by rw [mem₆]; exact sbig_of (sPreMem_frame s₀)
  obtain rw₆ : s₆.rd ++ s₆.wr = s₀.rd ++ s₀.wr := by rw [rd₆, wr₆, rd₅, wr₅, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rw₂]
  rw [ctrArgs_eq]
  refine wp_arg (s₀ := s₀) esp₆ (by rw [rw₆]; exact hp.arg_in (by decide)) (hp.arg_keep big₆ (by decide))
    fun s₇ u₇ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₇.other _ (by decide), esp₆])
    (by rw [u₇.rd, u₇.wr, rw₆]; exact hp.arg_in (by decide))
    (by rw [u₇.mem]; exact hp.arg_keep big₆ (by decide)) fun s₈ u₈ => ?_
  refine wp_mov fun s₉ u₉ => wp_addi fun s₁₀ u₁₀ => wp_movi fun s₁₁ u₁₁ => WP.block_nil ?_
  obtain keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₁₁.gpr r = s₆.gpr r := fun r ha hc hd hi => by
    rw [u₁₁.other _ hi, u₁₀.other _ hd, u₉.other _ hd, u₈.other _ hc, u₇.other _ ha]
  obtain p₆ : s₆.gpr .ebp = Sc s₀ := by rw [g₆ _ (by decide), g₅ _ (by decide), p₄]
  obtain b₆ : s₆.gpr .ebx = Kb s₀ := by rw [g₆ _ (by decide), b₅]
  obtain sp₁₁ : s₁₁.gpr .esp = E s₀ := by rw [keep _ (by decide) (by decide) (by decide) (by decide), esp₆]
  obtain rd₁₁ : s₁₁.rd = s₀.rd := by rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, rd₆, rd₅, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr₁₁ : s₁₁.wr = s₀.wr := by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆, wr₅, w₄]
  obtain mem₁₁ : s₁₁.mem = sPreMem s₀ := by rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, mem₆]
  obtain hb : below (s₁₁.gpr .esp) 32 = stkR s₀ := by rw [sp₁₁]; exact hp.below_eq
  refine ⟨⟨?_, ?_, ?_, ?_, u₁₁.gpr, ?_, hp.rounds, by rw [sp₁₁]; exact hp.esp32, ?_,
    hp.sch_k.sub_right (Region.sub_prefix (by decide)), hp.sch_scr.sub_right (Region.sub_prefix (by decide)),
    ?_, ?_, (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)),
    by rw [hb]; exact hp.b_sch, ?_, by rw [hb]; exact hp.b_k.sub_right (Region.sub_prefix (by decide)),
    by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide)), hp.sch_fit, ?_, by omega_arith, by omega_arith,
    ?_, ?_, ?_⟩, sp₁₁, rd₁₁, wr₁₁, mem₁₁⟩
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr]
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr]; exact arg_ofNat s₀ 1
  · rw [u₁₁.other _ (by decide), u₁₀.gpr, u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), p₆]
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), b₆]
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), p₆]
  · rw [cA]; exact hp.sch_scr.sub_right (Offset.sub_base _ (by decide))
  · rw [cA]
    exact (hp.k_scr.symm.sub_left (Offset.sub_base _ (by decide))).sub_right (Region.sub_prefix (by decide))
  · rw [cA]; exact Offset.disjoint_base _ (by decide) (by omega_arith)
  · rw [hb, cA]; exact hp.b_scr.sub_right (Offset.sub_base _ (by decide))
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
      Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  · rw [rd₁₁, wr₁₁, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
  · rw [wr₁₁, hp.wr, cA]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scR s₀, by simp, 2048, rfl, by simp⟩
    · exact ⟨kR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · rw [mem₁₁, sPreMem]; exact Proof.Cmac.zero4_bytes _ _

/-! ## The call, the doubling and the restore -/

theorem subkeysPost_eq : subkeysPost = dbl 0 0 ++ (dbl 0 16 ++ (.mov .eax (argOp 3) ::
    (saved.map fun p => Instr.mov p.1 (.mem (at_ .eax p.2))) ++ [])) := rfl

theorem subkeys_wp {s₀ : State} (h0 : subkeysX86.pre s₀) :
    WP isa (subkeys v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ subkeysX86.post s₀ s' := by
  obtain hp := SPre.of h0
  have hk := hp.k_fit
  have hsc := hp.scr_fit
  have hR := hp.rounds
  obtain hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hR with h | h | h <;> omega_arith
  have cA := hp.cA
  obtain cK : ∀ d n, d + n ≤ 32 → Covers [⟨(Kb s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩] s₀.wr := fun d n h => by
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨kR s₀, by simp, d, rfl, h⟩
  obtain cKr : ∀ d n, d + n ≤ 32 → Covers [⟨(Kb s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) :=
    fun d n h a k hi => by
      obtain ⟨r, hr, hc⟩ := cK d n h a k hi; exact ⟨r, List.mem_append_right _ hr, hc⟩
  unfold subkeys
  refine WP.seq (WP.mono (spre_wp hp) fun s₁ a => ?_)
  refine WP.seq (WP.mono (ctr_call v a.pre) fun s₂ h₂ => ?_)
  obtain hb : below (s₁.gpr .esp) 32 = stkR s₀ := by rw [a.esp]; exact hp.below_eq
  -- The memory after the call.
  obtain f₂ : Frame [kR s₀, ⟨(Sc s₀).setWidth 64, 2064⟩, stkR s₀] (sPreMem s₀) s₂.mem := by
    have fr := h₂.frame
    rw [hb, cA, a.mem] at fr
    exact fr.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨(Sc s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨kR s₀, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨⟨(Sc s₀).setWidth 64, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  obtain fr₂ := (sPreMem_frame s₀).trans f₂
  obtain kC : (⟨(Kb s₀).setWidth 64, 16⟩ : Region).Disjoint ⟨(Sc s₀).setWidth 64 + BitVec.ofNat 64 2048, 16⟩ :=
    (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
  obtain zC : Spec.Aes.bytesAt (sPreMem s₀) ((Sc s₀).setWidth 64 + BitVec.ofNat 64 2048) 16 = Spec.Cmac.zeros 16 := by
    rw [sPreMem, Proof.Cmac.zero4, Proof.Cmac.bytesAt_frame16 (Proof.Cmac.frame_store4 _ _ _ _ _) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact kC.symm)]
    exact Proof.Cmac.zero4_bytes _ _
  obtain L : Spec.Aes.bytesAt s₂.mem ((Kb s₀).setWidth 64) 16 = ciph s₀ (Spec.Cmac.zeros 16) := by
    have out := h₂.out
    rw [hp.sched_bytes (by rw [a.mem]; exact sbig_of (sPreMem_frame s₀)), cA, a.mem, zC] at out
    exact out
  obtain b₂ : s₂.gpr .ebx = Kb s₀ := by rw [h₂.saved .ebx (by simp [calleeSaved]), a.pre.ebx]
  obtain rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, a.rd, a.wr]
  obtain wr₂ : s₂.wr = s₀.wr := by rw [h₂.wr, a.wr]
  -- The doubling.
  rw [subkeysPost_eq]
  refine dbl_wp b₂ (by omega_arith) (by omega_arith) (by rw [rdwr₂]; exact cKr 0 16 (by decide))
    (by rw [wr₂]; exact cK 0 16 (by decide)) fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  obtain b₃ : s₃.gpr .ebx = Kb s₀ := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b₂]
  refine dbl_wp b₃ (by omega_arith) (by omega_arith) (by rw [rd₃, wr₃, rdwr₂]; exact cKr 0 16 (by decide))
    (by rw [wr₃, wr₂]; exact cK 16 16 (by decide)) fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  obtain f₄ : Frame [kR s₀, ⟨(Sc s₀).setWidth 64, 2064⟩, stkR s₀] (sSaved s₀) s₄.mem := by
    refine fr₂.trans (((dblMem_frame _ _ _ _).sub fun r hr => ?_).trans ((dblMem_frame _ _ _ _).sub fun r hr => ?_))
      |> fun h => by rw [m₄, m₃]; exact h
    all_goals simp only [List.mem_singleton] at hr; subst hr
    · exact ⟨kR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨kR s₀, by simp, Offset.sub_base _ (by decide)⟩
  obtain big₄ := sbig_of f₄
  obtain esp₄ : s₄.gpr .esp = E s₀ := by
    rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      h₂.saved .esp (by simp [calleeSaved]), a.esp]
  obtain rdwr₄ : s₄.rd ++ s₄.wr = s₀.rd ++ s₀.wr := by rw [rd₄, wr₄, rd₃, wr₃, rdwr₂]
  -- The restore.
  refine wp_arg (s₀ := s₀) esp₄ (by rw [rdwr₄]; exact hp.arg_in (by decide)) (hp.arg_keep big₄ (by decide))
    fun s₅ u₅ => ?_
  obtain sl : ∀ r d, (r, d) ∈ saved → s₄.mem.readW ((Sc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r := by
    intro r d hrd
    obtain hb := saved_bound _ hrd
    rw [f₄.readW (r := ⟨(Sc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.k_scr.symm.sub_left (Offset.sub_base _ (by omega_arith))
      · exact Offset.disjoint_base _ hb.1 (by omega_arith)
      · exact hp.b_scr.symm.sub_left (Offset.sub_base _ (by omega_arith))) (by decide)]
    exact saveMem_slot _ _ _ hrd
  have hsc' : (arg s₀ 3).toNat + 2176 ≤ 2 ^ 32 := hsc
  refine Spill.restore_ofNat_ok saved saved_fits (by rw [u₅.gpr]; omega_arith) saved_ne_eax (fun p hp' => ?_)
    (fun p hp' => by rw [u₅.gpr, u₅.mem]; exact sl p.1 p.2 hp') fun s₆ r₆ => WP.block_nil ?_
  · have hb := saved_bound p hp'
    rw [u₅.gpr, u₅.rd, u₅.wr, rdwr₄, hp.rd, hp.wr]
    exact ⟨scR s₀, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine ⟨⟨r₆.abi (by decide) (by decide) (by rw [u₅.other _ (by decide), esp₄]), ?_⟩, ?_⟩
  · rw [r₆.mem, u₅.mem]; exact hp.ret_keep big₄
  · show Spec.Aes.bytesAt s₆.mem ((Kb s₀).setWidth 64) 32 = _
    obtain b₃' : Spec.Aes.bytesAt s₃.mem ((Kb s₀).setWidth 64) 16 =
        Spec.Cmac.dbl 16 (Spec.Aes.bytesAt s₂.mem ((Kb s₀).setWidth 64) 16) := by
      have := dblMem_bytes s₂.mem ((Kb s₀).setWidth 64) 0 0
      rw [add0] at this; rw [m₃, this]
    obtain lo : Spec.Aes.bytesAt s₄.mem ((Kb s₀).setWidth 64) 16 = Spec.Aes.bytesAt s₃.mem ((Kb s₀).setWidth 64) 16 := by
      rw [m₄]
      exact Proof.Cmac.bytesAt_frame16 (dblMem_frame _ _ _ _) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.disjoint_base _ (by decide) (by omega_arith)).symm
    obtain hi : Spec.Aes.bytesAt s₄.mem ((Kb s₀).setWidth 64 + BitVec.ofNat 64 16) 16 =
        Spec.Cmac.dbl 16 (Spec.Aes.bytesAt s₃.mem ((Kb s₀).setWidth 64) 16) := by
      have := dblMem_bytes s₃.mem ((Kb s₀).setWidth 64) 0 16
      rw [add0] at this; rw [m₄, this]
    rw [r₆.mem, u₅.mem, Proof.Cmac.bytesAt_32, lo, hi, b₃', L]
    rfl

end VG.Proof.CmacAes.X86

end

end

/-! ### `CmacAes.X86.FinalizeCT`, which this module and modules that import it used -/

section

/-! ### `CmacAes.X86.Finalize`, which this module and modules that import it used -/

section

/-!
# AES-CMAC on x86: `vg_cmac_aes_finalize`, the last block

The steps that form the last block `Mₙ` (§6.2 step 4) in the counter block,
before the chaining value is XORed in: `Mₙ* ⊕ K1` for a complete block
(`full_wp`), else `Mₙ*` copied a byte at a time onto zeros (`copy_wp`), `0x80`
after it, and the block XORed with `K2` (`partial_wp`). The arguments are
those of `vg_cmac_aes_update` but `last` (`Dp`) and `last_len` (`N`), so its
abbreviations serve.
-/

@[expose] public section

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.Aes.X86 (Ctr32Impl)

variable (v : Ctr32Impl)
open VG.Proof.MdStream.X86 (Upd Mupd Fupd wp_mov wp_movi wp_addi wp_subi wp_cmpi wp_test wp_movzx8 wp_store8
  eval_e eval_ne ofNat_beq_zero sub_ofNat)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame)

section
variable (s₀ : State)

/-- The key: the schedule and the subkeys `K1` and `K2` after it. -/
abbrev keyR : Region := ⟨(W s₀).setWidth 64, 272⟩
/-- The last bytes `Mₙ*`. -/
abbrev lastR : Region := ⟨(Dp s₀).setWidth 64, N s₀⟩

/-- The last block `Mₙ` (§6.2 step 4), from the key and the last bytes. -/
abbrev mn : List Byte :=
  Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt s₀.mem ((W s₀).setWidth 64 + BitVec.ofNat 64 240) 16)
    (Spec.Aes.bytesAt s₀.mem ((W s₀).setWidth 64 + BitVec.ofNat 64 256) 16)
    (Spec.Aes.bytesAt s₀.mem ((Dp s₀).setWidth 64) (N s₀))

/-- The counter block. -/
abbrev Ca : Addr := (S s₀).setWidth 64 + BitVec.ofNat 64 2048

end

/-- The precondition, by name. -/
structure FPre (s₀ : State) : Prop where
  rd : s₀.rd = [keyR s₀, lastR s₀, argsR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  key_st : (keyR s₀).Disjoint (stR s₀)
  key_scr : (keyR s₀).Disjoint (scrR s₀)
  last_st : (lastR s₀).Disjoint (stR s₀)
  last_scr : (lastR s₀).Disjoint (scrR s₀)
  st_scr : (stR s₀).Disjoint (scrR s₀)
  args_st : (argsR s₀).Disjoint (stR s₀)
  args_scr : (argsR s₀).Disjoint (scrR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)
  b_key : (stkR s₀).Disjoint (keyR s₀)
  b_last : (stkR s₀).Disjoint (lastR s₀)
  b_st : (stkR s₀).Disjoint (stR s₀)
  b_scr : (stkR s₀).Disjoint (scrR s₀)
  key_fit : (W s₀).toNat + 272 ≤ 2 ^ 32
  st_fit : (St s₀).toNat + 16 ≤ 2 ^ 32
  last_fit : (Dp s₀).toNat + N s₀ ≤ 2 ^ 32
  scr_fit : (S s₀).toNat + 2176 ≤ 2 ^ 32
  esp32 : 32 ≤ (E s₀).toNat
  esp_fit : (E s₀).toNat + 28 ≤ 2 ^ 32
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14
  len : N s₀ ≤ 16

theorem FPre.of {s₀ : State} (h : finalizeX86.pre s₀) : FPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x⟩

theorem in_cov {rs : List Region} {a : Addr} {n : Nat} (h : Covers [⟨a, n⟩] rs) : InRegions rs a n :=
  h _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

section
variable {s₀ : State} (hp : FPre s₀)
include hp

theorem FPre.below_eq : below (E s₀) 32 = stkR s₀ := by
  simp only [below]; rw [Taint.sub_setWidth hp.esp32]

theorem FPre.argA {i : Nat} (hi : i < 6) : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.esp_fit
  simp only [argAddr]
  rw [show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * i) from rfl,
    show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * 0) from rfl,
    addr_eq (by omega_arith), addr_eq (by omega_arith), Offset.add_add]

theorem FPre.arg_sub {i : Nat} (hi : i < 6) : Region.Sub ⟨argAddr s₀ i, 4⟩ (argsR s₀) := by
  rw [hp.argA hi]; exact Offset.sub_base _ (by omega_arith)

theorem FPre.arg_in {i : Nat} (hi : i < 6) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 := by
  refine ⟨argsR s₀, by simp [hp.rd], ?_⟩
  rw [hp.argA hi]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)

theorem FPre.args_stk : (argsR s₀).Disjoint (stkR s₀) := by
  have : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.esp_fit
  obtain e : argAddr s₀ 0 = (E s₀).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega_arith)
  show Region.Disjoint ⟨argAddr s₀ 0, 24⟩ _
  rw [e]; exact (Offset.disjoint_below_above _ (by decide)).symm

/-- The stack arguments are unchanged where only `Big` changes. -/
theorem FPre.arg_keep {m : Mem} (hf : Frame (Big s₀) s₀.mem m) {i : Nat} (hi : i < 6) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.args_st.sub_left (hp.arg_sub hi)
    · exact hp.args_scr.sub_left (hp.arg_sub hi)
    · exact hp.args_stk.sub_left (hp.arg_sub hi)) (by decide)

theorem FPre.cS {d n : Nat} (h : d + n ≤ 2176) :
    Covers [⟨(S s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩] s₀.wr := by
  rw [hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, d, rfl, h⟩

theorem FPre.cKey {d n : Nat} (h : d + n ≤ 272) :
    Covers [⟨(W s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) := by
  rw [hp.rd]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨keyR s₀, by simp, d, rfl, h⟩

theorem FPre.cLast {d n : Nat} (h : d + n ≤ N s₀) :
    Covers [⟨(Dp s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) := by
  rw [hp.rd]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨lastR s₀, by simp, d, rfl, h⟩

theorem FPre.ca_key {d n : Nat} (h : d + n ≤ 272) :
    (⟨Ca s₀, 16⟩ : Region).Disjoint ⟨(W s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩ :=
  (hp.key_scr.symm.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ h)

theorem FPre.ca_last : (⟨Ca s₀, 16⟩ : Region).Disjoint (lastR s₀) :=
  hp.last_scr.symm.sub_left (Offset.sub_base _ (by decide))

theorem FPre.cA : (S s₀ + BitVec.ofNat 32 2048).setWidth 64 = Ca s₀ :=
  addr_eq (by have := hp.scr_fit; omega_arith)

theorem FPre.key_bytes {d : Nat} (h : d + 16 ≤ 272) :
    Spec.Aes.bytesAt (savedMem s₀) ((W s₀).setWidth 64 + BitVec.ofNat 64 d) 16 =
      Spec.Aes.bytesAt s₀.mem ((W s₀).setWidth 64 + BitVec.ofNat 64 d) 16 :=
  Proof.Cmac.bytesAt_frame16 (savedMem_frame s₀) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.key_scr.sub_left (Offset.sub_base _ h)

theorem FPre.last_bytes : Spec.Aes.bytesAt (savedMem s₀) ((Dp s₀).setWidth 64) (N s₀) =
    Spec.Aes.bytesAt s₀.mem ((Dp s₀).setWidth 64) (N s₀) :=
  Proof.Cmac.bytesAt_frame (savedMem_frame s₀) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.last_scr) (by have := hp.len; omega_arith)

end

/-! ## Saving the registers -/

theorem finSave_eq : finSave = .mov .eax (argOp 5) :: (saved.map (fun p => Instr.store (at_ .eax p.2) p.1) ++
    ([.mov .ebp (.reg .eax), .mov .ecx (argOp 4), .alu .cmp .ecx (.imm 16)] : List Instr)) := rfl

/-- What `finSave` leaves. -/
structure FS (s₀ s : State) : Prop where
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .ebp → s.gpr r = s₀.gpr r
  ecx : s.gpr .ecx = BitVec.ofNat 32 (N s₀)
  ebp : s.gpr .ebp = S s₀
  zf : s.zf = some (decide (N s₀ = 16))
  mem : s.mem = savedMem s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finSave_wp {s₀ : State} (hp : FPre s₀) : WP isa (.block finSave) s₀ (FS s₀) := by
  have hsc := hp.scr_fit
  rw [finSave_eq]
  refine wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  have h₁ : s₁.gpr .eax = S s₀ := u₁.gpr
  refine Spill.save_ofNat_ok saved saved_fits (by rw [h₁]; omega_arith) (fun p hp' => ?_) fun s₂ u₂ => ?_
  · have hb := saved_bound p hp'
    rw [h₁, u₁.wr, hp.wr]
    exact ⟨scrR s₀, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain hm₂ : s₂.mem = savedMem s₀ := by
    rw [u₂.mem, u₁.mem, h₁, savedMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (saved_ne_eax p hp')
  obtain esp₂ : s₂.gpr .esp = s₀.gpr .esp := by rw [u₂.gpr, u₁.other _ (by decide)]
  obtain rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]
  refine wp_mov fun s₃ u₃ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), esp₂])
    (by rw [u₃.rd, u₃.wr, rw₂]; exact hp.arg_in (by decide))
    (by rw [u₃.mem, hm₂]; exact hp.arg_keep (savedMem_big s₀) (by decide)) fun s₄ u₄ => ?_
  refine wp_cmpi fun s₅ f₅ _ z₅ => WP.block_nil ⟨fun r ha hc hb => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₅.gpr, u₄.other _ hc, u₃.other _ hb, u₂.gpr, u₁.other _ ha]
  · rw [f₅.gpr, u₄.gpr]; exact arg_ofNat s₀ 4
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr, h₁]
  · rw [z₅, u₄.gpr, arg_ofNat s₀ 4, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl,
      MdStream.X86.sub_beq (arg s₀ 4).isLt (by decide)]
  · rw [f₅.mem, u₄.mem, u₃.mem, hm₂]
  · rw [f₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [f₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-! ## The last block -/

/-- What the branch on the length leaves: `Mₙ` in the counter block. -/
structure BPost (s₀ s : State) : Prop where
  ebp : s.gpr .ebp = S s₀
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨Ca s₀, 16⟩] (savedMem s₀) s.mem
  blk : Spec.Aes.bytesAt s.mem (Ca s₀) 16 = mn s₀

theorem full_eq : full = .mov .ebx (argOp 3) :: .mov .edx (argOp 0) :: (xor4 .ebx .edx .ebp 0 240 2048 ++ []) := rfl

theorem full_wp {s₀ : State} (hp : FPre s₀) (hL : N s₀ = 16) {s : State} (h : FS s₀ s) :
    WP isa (.block full) s (BPost s₀) := by
  have sf := hp.scr_fit
  have kf := hp.key_fit
  have lf := hp.last_fit
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  obtain esp : s.gpr .esp = E s₀ := h.keep _ (by decide) (by decide) (by decide)
  rw [full_eq]
  refine wp_arg (s₀ := s₀) esp (by rw [hrw]; exact hp.arg_in (by decide))
    (by rw [h.mem]; exact hp.arg_keep (savedMem_big s₀) (by decide)) fun s₁ u₁ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), esp])
    (by rw [u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₁.mem, h.mem]; exact hp.arg_keep (savedMem_big s₀) (by decide)) fun s₂ u₂ => ?_
  obtain b₂ : s₂.gpr .ebx = Dp s₀ := by rw [u₂.other _ (by decide), u₁.gpr]
  have d₂ : s₂.gpr .edx = W s₀ := u₂.gpr
  obtain p₂ : s₂.gpr .ebp = S s₀ := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.ebp]
  obtain rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]
  obtain w₂ : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr, h.wr]
  obtain lf' : (Dp s₀).toNat + 16 ≤ 2 ^ 32 := by rw [← hL]; exact lf
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [b₂]; omega_arith) (by rw [d₂]; omega_arith) (by rw [p₂]; omega_arith)
    (by rw [b₂, rw₂]; exact hp.cLast (by omega_arith)) (by rw [d₂, rw₂]; exact hp.cKey (by decide))
    (by rw [p₂, w₂]; exact hp.cS (by decide)) fun s₃ g₃ => WP.block_nil ?_
  refine ⟨by rw [g₃.gpr _ (by decide) (by decide), p₂],
    by rw [g₃.gpr _ (by decide) (by decide), u₂.other _ (by decide), u₁.other _ (by decide), esp],
    by rw [g₃.rd, u₂.rd, u₁.rd, h.rd], by rw [g₃.wr, w₂], ?_, ?_⟩
  · rw [g₃.mem, p₂, u₂.mem, u₁.mem, h.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  · rw [g₃.mem, p₂, b₂, d₂, u₂.mem, u₁.mem, h.mem, add0, Proof.Cmac.xor4Mem_bytes _
      (Proof.Cmac.Sep4.of_disjoint (hp.ca_last.sub_right (Region.sub_prefix (by omega_arith))))
      (Proof.Cmac.Sep4.of_disjoint (hp.ca_key (by decide))), hp.key_bytes (by decide)]
    have lb := hp.last_bytes
    rw [hL] at lb
    rw [lb]
    simp only [mn, Spec.Cmac.lastBlock, Proof.Cmac.bytesAt_length, hL, ite_true]
    exact Proof.Cmac.xor_comm _ _

/-! ## Copying the last bytes -/

theorem byte_rt32 (b : BitVec 8) : (b.setWidth 32).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega_arith

theorem addr_at {p : BitVec 32} {i : Nat} (h : p.toNat + i < 2 ^ 32) :
    addr (p + BitVec.ofNat 32 i) 0 = p.setWidth 64 + BitVec.ofNat 64 i := by
  simp only [addr, add0']; exact addr_eq h

theorem copy_wp {s : State} {p c : BitVec 32} {L : Nat} (hL₀ : 0 < L) (hL : L ≤ 16)
    (hsi : s.gpr .esi = p) (hdi : s.gpr .edi = c) (hcx : s.gpr .ecx = BitVec.ofNat 32 L)
    (fp : p.toNat + L ≤ 2 ^ 32) (fc : c.toNat + 16 ≤ 2 ^ 32)
    (hr : Covers [⟨p.setWidth 64, L⟩] (s.rd ++ s.wr)) (hw : Covers [⟨c.setWidth 64, 16⟩] s.wr)
    (hd : (⟨p.setWidth 64, L⟩ : Region).Disjoint ⟨c.setWidth 64, 16⟩) :
    WP isa copy s fun s' =>
      s'.mem = writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) L) ∧
      s'.gpr .edi = c + BitVec.ofNat 32 L ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block [.movzx8 .eax (at_ .esi 0), .store8 (at_ .edi 0) .al,
      .alu .add .esi (.imm 1), .alu .add .edi (.imm 1), .alu .sub .ecx (.imm 1)]) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .esi = p + BitVec.ofNat 32 i ∧
      t.gpr .edi = c + BitVec.ofNat 32 i ∧ t.gpr .ecx = BitVec.ofNat 32 (L - i) ∧
      t.mem = writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) i) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL₀, by rw [hsi, add0'], by rw [hdi, add0'], by rw [hcx, Nat.sub_zero],
      by simp [Spec.Aes.bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl⟩
  rintro n t ⟨i, rfl, hi, xsi, xdi, xcx, mem, g, rd, wr⟩
  refine wp_movzx8 (a := p.setWidth 64 + BitVec.ofNat 64 i) (by rw [ea_at', xsi]; exact addr_at (by omega_arith))
    (by rw [rd, wr]; exact hr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    fun t₁ u₁ => ?_
  refine wp_store8 (a := c.setWidth 64 + BitVec.ofNat 64 i)
    (by rw [ea_at', u₁.other _ (by decide), xdi]; exact addr_at (by omega_arith))
    (by rw [u₁.wr, wr]; exact hw _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    fun t₂ v₂ => ?_
  refine wp_addi fun t₃ u₃ => wp_addi fun t₄ u₄ => wp_subi fun t₅ u₅ z₅ => WP.block_nil ?_
  obtain hlen : (Spec.Aes.bytesAt s.mem (p.setWidth 64) i).length = i := Proof.Cmac.bytesAt_length _ _ _
  obtain hx : writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) i)
      (p.setWidth 64 + BitVec.ofNat 64 i) = s.mem (p.setWidth 64 + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem (c.setWidth 64) _ (R := ⟨c.setWidth 64, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) (Region.sub_prefix (by omega_arith) _ hcon)
  have al : t₁.gpr Reg8.al.reg = (t.mem (p.setWidth 64 + BitVec.ofNat 64 i)).setWidth 32 := u₁.gpr
  obtain hmem : t₅.mem = writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) (i + 1)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, v₂.mem, al, u₁.mem, mem, byte_rt32, hx, Proof.Cmac.bytesAt_succ,
      writeBytes_snoc s.mem _ _ _ (by rw [hlen]; omega_arith), hlen]
  obtain cx₄ : t₄.gpr .ecx = BitVec.ofNat 32 (L - i) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), xcx]
  obtain xcx' : t₅.gpr .ecx = BitVec.ofNat 32 (L - (i + 1)) := by
    rw [u₅.gpr, cx₄, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_arith), Nat.sub_sub]
  obtain ev : isa.eval .ne t₅ = some !decide (L - (i + 1) = 0) := by
    show VG.X86.eval .ne t₅ = _
    rw [eval_ne, z₅, cx₄, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_arith), Nat.sub_sub,
      ofNat_beq_zero (by omega_arith)]
    rfl
  obtain gg : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → t₅.gpr r = s.gpr r := fun r ha hc hs hd' => by
    rw [u₅.other _ hc, u₄.other _ hd', u₃.other _ hs, v₂.gpr, u₁.other _ ha, g r ha hc hs hd']
  obtain xdi' : t₅.gpr .edi = c + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), xdi,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  obtain xsi' : t₅.gpr .esi = p + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, v₂.gpr, u₁.other _ (by decide), xsi,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  obtain rd' : t₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, v₂.rd, u₁.rd, rd]
  obtain wr' : t₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, v₂.wr, u₁.wr, wr]
  by_cases he : i + 1 = L
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [xdi', he], gg, rd', wr'⟩
  · right
    exact ⟨by rw [ev]; simp; omega_arith, L - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, xsi', xdi', xcx', hmem, gg,
      rd', wr'⟩

/-! ## A partial last block -/

theorem zero_eq : zero = zero4 .ebp 2048 ++ ([.mov .edi (.reg .ebp), .alu .add .edi (.imm (BitVec.ofNat 32 2048)),
    .mov .esi (argOp 3), .mov .ecx (argOp 4), .alu .test .ecx (.reg .ecx)] : List Instr) := rfl

theorem padK2_eq : padK2 = .mov .eax (.imm 0x80) :: .store8 (at_ .edi 0) .al :: .mov .edx (argOp 0) ::
    (xor4 .ebp .edx .ebp 2048 256 2048 ++ []) := rfl

theorem b80 : ((0x80 : BitVec 32).setWidth 8 : Byte) = 0x80 := by decide

theorem partial_wp {s₀ : State} (hp : FPre s₀) (hL : N s₀ < 16) {s : State} (h : FS s₀ s) :
    WP isa partialBlock s (BPost s₀) := by
  have sf := hp.scr_fit
  have sf' : (arg s₀ 5).toNat + 2176 ≤ 2 ^ 32 := sf
  have kf := hp.key_fit
  have lf := hp.last_fit
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have cA := hp.cA
  -- Zero the counter block.
  refine WP.seq ?_
  rw [zero_eq]
  refine zero4_ok (b := .ebp) (d := 2048) (by decide) (by rw [h.ebp]; omega_arith)
    (by rw [h.ebp, h.wr]; exact hp.cS (by decide)) fun s₁ g₁ m₁ rd₁ wr₁ => ?_
  obtain p₁ : s₁.gpr .ebp = S s₀ := by rw [g₁ _ (by decide), h.ebp]
  obtain esp₁ : s₁.gpr .esp = E s₀ := by rw [g₁ _ (by decide), h.keep _ (by decide) (by decide) (by decide)]
  obtain fz : Frame [⟨Ca s₀, 16⟩] (savedMem s₀) (Proof.Cmac.zero4 (savedMem s₀) (Ca s₀)) :=
    Proof.Cmac.frame_store4 _ _ _ _ _
  obtain mem₁ : s₁.mem = Proof.Cmac.zero4 (savedMem s₀) (Ca s₀) := by rw [m₁, h.ebp, h.mem]
  obtain big₁ : Frame (Big s₀) s₀.mem s₁.mem := by
    rw [mem₁]
    exact (savedMem_big s₀).trans (fz.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩)
  obtain rw₁ : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [rd₁, wr₁, hrw]
  refine wp_mov fun s₂ u₂ => wp_addi fun s₃ u₃ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), esp₁])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, rw₁]; exact hp.arg_in (by decide))
    (by rw [u₃.mem, u₂.mem]; exact hp.arg_keep big₁ (by decide)) fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), esp₁])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, rw₁]; exact hp.arg_in (by decide))
    (by rw [u₄.mem, u₃.mem, u₂.mem]; exact hp.arg_keep big₁ (by decide)) fun s₅ u₅ => ?_
  refine wp_test fun s₆ f₆ z₆ => WP.block_nil ?_
  obtain k₆ : ∀ r, r ≠ .ecx → r ≠ .esi → r ≠ .edi → s₆.gpr r = s₁.gpr r := fun r hc hs hd => by
    rw [f₆.gpr, u₅.other _ hc, u₄.other _ hs, u₃.other _ hd, u₂.other _ hd]
  obtain edi₆ : s₆.gpr .edi = S s₀ + BitVec.ofNat 32 2048 := by
    rw [f₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, p₁]
  obtain esi₆ : s₆.gpr .esi = Dp s₀ := by rw [f₆.gpr, u₅.other _ (by decide), u₄.gpr]
  obtain ecx₆ : s₆.gpr .ecx = BitVec.ofNat 32 (N s₀) := by rw [f₆.gpr, u₅.gpr]; exact arg_ofNat s₀ 4
  obtain mem₆ : s₆.mem = Proof.Cmac.zero4 (savedMem s₀) (Ca s₀) := by
    rw [f₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, mem₁]
  obtain rd₆ : s₆.rd = s₀.rd := by rw [f₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁, h.rd]
  obtain wr₆ : s₆.wr = s₀.wr := by rw [f₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁, h.wr]
  obtain ev : isa.eval .e s₆ = some (decide (N s₀ = 0)) := by
    show VG.X86.eval .e s₆ = _
    rw [eval_e, z₆, u₅.gpr, arg_ofNat s₀ 4, ofNat_and_self_beq (arg s₀ 4).isLt]
  obtain lastZ : Spec.Aes.bytesAt (Proof.Cmac.zero4 (savedMem s₀) (Ca s₀)) ((Dp s₀).setWidth 64) (N s₀) =
      Spec.Aes.bytesAt s₀.mem ((Dp s₀).setWidth 64) (N s₀) := by
    rw [Proof.Cmac.bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.ca_last.symm) (by omega_arith), hp.last_bytes]
  -- Copy the last bytes.
  refine WP.seq (WP.mono (Q := fun (s₇ : State) =>
      s₇.mem = writeBytes (Proof.Cmac.zero4 (savedMem s₀) (Ca s₀)) (Ca s₀)
        (Spec.Aes.bytesAt s₀.mem ((Dp s₀).setWidth 64) (N s₀)) ∧
      s₇.gpr .edi = S s₀ + BitVec.ofNat 32 (2048 + N s₀) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → s₇.gpr r = s₆.gpr r) ∧
      s₇.rd = s₀.rd ∧ s₇.wr = s₀.wr) ?_ fun s₇ h₇ => ?_)
  · by_cases hL0 : N s₀ = 0
    · refine WP.ite true (by rw [ev]; simp [hL0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      refine ⟨by rw [mem₆, hL0]; simp [Spec.Aes.bytesAt, writeBytes_nil], by rw [edi₆, hL0],
        fun _ _ _ _ _ => rfl, rd₆, wr₆⟩
    · refine WP.ite false (by rw [ev]; simp [hL0]) (fun h => by cases h) fun _ => ?_
      obtain hr := hp.cLast (d := 0) (n := N s₀) (by omega_arith)
      rw [add0] at hr
      refine WP.mono (copy_wp (p := Dp s₀) (c := S s₀ + BitVec.ofNat 32 2048) (L := N s₀) (by omega_arith) (by omega_arith)
        esi₆ edi₆ ecx₆ lf
        (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
          Nat.mod_eq_of_lt (by omega_arith)]; omega_arith)
        (by rw [rd₆, wr₆]; exact hr) (by rw [cA, wr₆]; exact hp.cS (by decide))
        (by rw [cA]; exact hp.ca_last.symm)) ?_
      rintro s₇ ⟨m₇, di₇, g₇, rd₇, wr₇⟩
      exact ⟨by rw [m₇, mem₆, cA, lastZ], by rw [di₇, Offset.add_add], g₇, by rw [rd₇, rd₆], by rw [wr₇, wr₆]⟩
  · obtain ⟨m₇, di₇, g₇, rd₇, wr₇⟩ := h₇
    rw [padK2_eq]
    refine wp_movi fun s₈ u₈ => ?_
    refine wp_store8 (a := Ca s₀ + BitVec.ofNat 64 (N s₀))
      (by
        rw [ea_at', u₈.other _ (by decide), di₇, addr_at (by omega_arith)]
        show _ = (S s₀).setWidth 64 + BitVec.ofNat 64 2048 + BitVec.ofNat 64 (N s₀)
        rw [Offset.add_add])
      (by
        rw [u₈.wr, wr₇]
        show InRegions s₀.wr ((S s₀).setWidth 64 + BitVec.ofNat 64 2048 + BitVec.ofNat 64 (N s₀)) 1
        rw [Offset.add_add]
        exact in_cov (hp.cS (d := 2048 + N s₀) (n := 1) (by omega_arith))) fun s₉ v₉ => ?_
    obtain g₉ : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → s₉.gpr r = s₁.gpr r := fun r ha hc hs hd => by
      rw [v₉.gpr, u₈.other _ ha, g₇ r ha hc hs hd, k₆ r hc hs hd]
    obtain esp₉ : s₉.gpr .esp = E s₀ := by
      rw [g₉ _ (by decide) (by decide) (by decide) (by decide), esp₁]
    obtain rw₉ : s₉.rd ++ s₉.wr = s₀.rd ++ s₀.wr := by rw [v₉.rd, v₉.wr, u₈.rd, u₈.wr, rd₇, wr₇]
    obtain hlen : (Spec.Aes.bytesAt s₀.mem ((Dp s₀).setWidth 64) (N s₀)).length = N s₀ :=
      Proof.Cmac.bytesAt_length _ _ _
    obtain m₉ : s₉.mem = (writeBytes (Proof.Cmac.zero4 (savedMem s₀) (Ca s₀)) (Ca s₀)
        (Spec.Aes.bytesAt s₀.mem ((Dp s₀).setWidth 64) (N s₀))).writeW (Ca s₀ + BitVec.ofNat 64 (N s₀))
        (0x80 : Byte) := by
      have : s₈.gpr Reg8.al.reg = 0x80 := u₈.gpr
      rw [v₉.mem, this, u₈.mem, m₇, b80]
    obtain fW : Frame [⟨Ca s₀, 16⟩] (savedMem s₀) s₉.mem := by
      rw [m₉]
      refine (fz.trans (writeBytes_frame _ _ _ ?_)).trans
        ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith)))
      rw [hlen]; simpa using Offset.contains_base (Ca s₀) (d := 0) (n := N s₀) (k := 16) (by omega_arith) (by decide)
    obtain big₉ : Frame (Big s₀) s₀.mem s₉.mem :=
      (savedMem_big s₀).trans (fW.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩)
    refine wp_arg (s₀ := s₀) esp₉ (by rw [rw₉]; exact hp.arg_in (by decide)) (hp.arg_keep big₉ (by decide))
      fun s₁₀ u₁₀ => ?_
    obtain p₁₀ : s₁₀.gpr .ebp = S s₀ := by
      rw [u₁₀.other _ (by decide), g₉ _ (by decide) (by decide) (by decide) (by decide), p₁]
    have d₁₀ : s₁₀.gpr .edx = W s₀ := u₁₀.gpr
    obtain rw₁₀ : s₁₀.rd ++ s₁₀.wr = s₀.rd ++ s₀.wr := by rw [u₁₀.rd, u₁₀.wr, rw₉]
    obtain w₁₀ : s₁₀.wr = s₀.wr := by rw [u₁₀.wr, v₉.wr, u₈.wr, wr₇]
    refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [p₁₀]; omega_arith) (by rw [d₁₀]; omega_arith) (by rw [p₁₀]; omega_arith)
      (by
        rw [p₁₀, rw₁₀]
        exact fun a n hi => (hp.cS (d := 2048) (n := 16) (by decide)) a n hi |>
          fun ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩)
      (by rw [d₁₀, rw₁₀]; exact hp.cKey (by decide)) (by rw [p₁₀, w₁₀]; exact hp.cS (by decide))
      fun s₁₁ g₁₁ => WP.block_nil ?_
    obtain pad : Spec.Aes.bytesAt s₉.mem (Ca s₀) 16 =
        Spec.Aes.bytesAt s₀.mem ((Dp s₀).setWidth 64) (N s₀) ++ [0x80] ++ Spec.Cmac.zeros (16 - N s₀ - 1) := by
      have := Proof.Cmac.padded_bytes (Proof.Cmac.zero4 (savedMem s₀) (Ca s₀)) (Ca s₀)
        (Spec.Aes.bytesAt s₀.mem ((Dp s₀).setWidth 64) (N s₀)) (by rw [hlen]; exact hL)
        (Proof.Cmac.zero4_bytes _ _)
      rw [hlen] at this
      rw [m₉]; exact this
    obtain k2 : Spec.Aes.bytesAt s₉.mem ((W s₀).setWidth 64 + BitVec.ofNat 64 256) 16 =
        Spec.Aes.bytesAt s₀.mem ((W s₀).setWidth 64 + BitVec.ofNat 64 256) 16 := by
      rw [Proof.Cmac.bytesAt_frame16 fW (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hp.ca_key (by decide)).symm), hp.key_bytes (by decide)]
    refine ⟨by rw [g₁₁.gpr _ (by decide) (by decide), p₁₀],
      by rw [g₁₁.gpr _ (by decide) (by decide), u₁₀.other _ (by decide), esp₉],
      by rw [g₁₁.rd, u₁₀.rd, v₉.rd, u₈.rd, rd₇], by rw [g₁₁.wr, w₁₀], ?_, ?_⟩
    · rw [g₁₁.mem, p₁₀, u₁₀.mem]; exact fW.trans (Proof.Cmac.xor4Mem_frame _ _ _ _)
    · rw [g₁₁.mem, p₁₀, d₁₀, u₁₀.mem, Proof.Cmac.xor4Mem_bytes _ (Proof.Cmac.Sep4.self _)
        (Proof.Cmac.Sep4.of_disjoint (hp.ca_key (by decide))), pad, k2]
      simp only [mn, Spec.Cmac.lastBlock, hlen, show N s₀ ≠ 16 by omega_arith, ite_false]
      exact Proof.Cmac.xor_comm _ _

end VG.Proof.CmacAes.X86

end

end

@[expose] public section

section

/-!
# AES-CMAC on x86: `vg_cmac_aes_finalize` is correct

Before the call, the counter block holds `Mₙ ⊕ C`, for the last block `Mₙ` of
§6.2 step 4 and the chaining value `C` at `state`, and the state is zeroed;
the call leaves `CIPH_K(C ⊕ Mₙ)` there, the MAC (`Cmac.macFull_split`).
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.Aes.X86 (Ctr32Impl)

variable (v : Ctr32Impl)
open VG.Proof.MdStream.X86 (Upd wp_mov wp_movi wp_addi eval_e)

/-! ## Up to the call -/

/-- What the code before the call leaves. -/
structure FMid (s₀ s : State) : Prop where
  pre : CtrPre s (W s₀) (S s₀ + BitVec.ofNat 32 2048) (St s₀) (S s₀) (R s₀)
  blk : Spec.Aes.bytesAt s.mem (Ca s₀) 16 =
    Spec.Cmac.xor (mn s₀) (Spec.Aes.bytesAt s₀.mem ((St s₀).setWidth 64) 16)
  frame : Frame [⟨Ca s₀, 16⟩, stR s₀] (savedMem s₀) s.mem
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finArgs_eq : finArgs = .mov .ebx (argOp 2) :: (xor4 .ebp .ebx .ebp 2048 0 2048 ++ (zero4 .ebx 0 ++ ctrArgs)) :=
  rfl

theorem finArgs_wp {s₀ : State} (hp : FPre s₀) {s : State} (h : BPost s₀ s) :
    WP isa (.block finArgs) s (FMid s₀) := by
  have sf := hp.scr_fit
  have tf := hp.st_fit
  have hR := hp.rounds
  have cA := hp.cA
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  obtain cSt : (⟨Ca s₀, 16⟩ : Region).Disjoint (stR s₀) := hp.st_scr.symm.sub_left (Offset.sub_base _ (by decide))
  obtain wSt : Covers [stR s₀] s₀.wr := by
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
  obtain big : Frame (Big s₀) s₀.mem s.mem :=
    (savedMem_big s₀).trans (h.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩)
  rw [finArgs_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (hp.arg_keep big (by decide))
    fun s₁ u₁ => ?_
  have b₁ : s₁.gpr .ebx = St s₀ := u₁.gpr
  obtain p₁ : s₁.gpr .ebp = S s₀ := by rw [u₁.other _ (by decide), h.ebp]
  obtain rw₁ : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [u₁.rd, u₁.wr, hrw]
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [p₁]; omega_using [sf]) (by rw [b₁]; omega_using [tf]) (by rw [p₁]; omega_using [sf])
    (by
      rw [p₁, rw₁]
      exact fun a n hi => (hp.cS (d := 2048) (n := 16) (by decide)) a n hi |>
        fun ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩)
    (by
      rw [b₁, add0, rw₁]
      exact fun a n hi => wSt a n hi |> fun ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [p₁, u₁.wr, h.wr]; exact hp.cS (by decide)) fun s₂ g₂ => ?_
  obtain b₂ : s₂.gpr .ebx = St s₀ := by rw [g₂.gpr _ (by decide) (by decide), b₁]
  refine zero4_ok (by decide) (by rw [b₂]; omega_using [tf]) (by rw [b₂, add0, g₂.wr, u₁.wr, h.wr]; exact wSt)
    fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  obtain esp₃ : s₃.gpr .esp = E s₀ := by
    rw [g₃ _ (by decide), g₂.gpr _ (by decide) (by decide), u₁.other _ (by decide), h.esp]
  obtain rd₃' : s₃.rd = s₀.rd := by rw [rd₃, g₂.rd, u₁.rd, h.rd]
  obtain wr₃' : s₃.wr = s₀.wr := by rw [wr₃, g₂.wr, u₁.wr, h.wr]
  obtain mem₃ : s₃.mem = Proof.Cmac.zero4 (Proof.Cmac.xor4Mem s.mem (Ca s₀) (Ca s₀) ((St s₀).setWidth 64))
      ((St s₀).setWidth 64) := by
    rw [m₃, b₂, add0, g₂.mem, p₁, b₁, add0, u₁.mem]
  obtain fr₃ : Frame [⟨Ca s₀, 16⟩, stR s₀] (savedMem s₀) s₃.mem := by
    rw [mem₃]
    exact ((h.frame.trans (Proof.Cmac.xor4Mem_frame _ _ _ _)).mono (by simp)).trans
      ((Proof.Cmac.frame_store4 _ _ _ _ _).mono (by simp))
  obtain big₃ : Frame (Big s₀) s₀.mem s₃.mem :=
    (savedMem_big s₀).trans (fr₃.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨stR s₀, by simp, fun _ h => h⟩)
  rw [ctrArgs_eq]
  refine wp_arg (s₀ := s₀) esp₃ (by rw [rd₃', wr₃']; exact hp.arg_in (by decide)) (hp.arg_keep big₃ (by decide))
    fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₄.other _ (by decide), esp₃])
    (by rw [u₄.rd, u₄.wr, rd₃', wr₃']; exact hp.arg_in (by decide))
    (by rw [u₄.mem]; exact hp.arg_keep big₃ (by decide)) fun s₅ u₅ => ?_
  refine wp_mov fun s₆ u₆ => wp_addi fun s₇ u₇ => wp_movi fun s₈ u₈ => WP.block_nil ?_
  obtain keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₈.gpr r = s₃.gpr r := fun r ha hc hd hi => by
    rw [u₈.other _ hi, u₇.other _ hd, u₆.other _ hd, u₅.other _ hc, u₄.other _ ha]
  obtain p₃ : s₃.gpr .ebp = S s₀ := by rw [g₃ _ (by decide), g₂.gpr _ (by decide) (by decide), p₁]
  obtain b₃ : s₃.gpr .ebx = St s₀ := by rw [g₃ _ (by decide), b₂]
  obtain sp₈ : s₈.gpr .esp = E s₀ := by rw [keep _ (by decide) (by decide) (by decide) (by decide), esp₃]
  obtain rd₈ : s₈.rd = s₀.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃']
  obtain wr₈ : s₈.wr = s₀.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃']
  obtain mem₈ : s₈.mem = s₃.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  obtain hb : below (s₈.gpr .esp) 32 = stkR s₀ := by rw [sp₈]; exact hp.below_eq
  obtain stS : Spec.Aes.bytesAt s.mem ((St s₀).setWidth 64) 16 =
      Spec.Aes.bytesAt s₀.mem ((St s₀).setWidth 64) 16 :=
    Proof.Cmac.bytesAt_frame16 ((savedMem_frame s₀).trans (h.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩)) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.st_scr
  refine ⟨⟨?_, ?_, ?_, ?_, u₈.gpr, ?_, hR, by rw [sp₈]; exact hp.esp32, ?_,
    hp.key_st.sub_left (Region.sub_prefix (by decide)),
    (hp.key_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)),
    by rw [cA]; exact cSt, by rw [cA]; exact Offset.disjoint_base _ (by decide) (by omega_using []),
    hp.st_scr.sub_right (Region.sub_prefix (by decide)),
    by rw [hb]; exact hp.b_key.sub_right (Region.sub_prefix (by decide)),
    by rw [hb, cA]; exact hp.b_scr.sub_right (Offset.sub_base _ (by decide)), by rw [hb]; exact hp.b_st,
    by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide)), by have := hp.key_fit; omega_using [this], ?_, tf,
    by omega_using [sf], ?_, ?_, ?_⟩, ?_, ?_, sp₈, rd₈, wr₈⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]; exact arg_ofNat s₀ 1
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), p₃]
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), b₃]
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), p₃]
  · rw [cA]; exact (hp.ca_key (d := 0) (n := 240) (by decide)).symm |> fun d => by simpa using d
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
      Nat.mod_eq_of_lt (by omega_using [sf])]; omega_using [sf]
  · rw [rd₈, wr₈, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨keyR s₀, by simp, 0, by simp, by simp⟩
  · rw [wr₈, hp.wr, cA]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  · rw [mem₈, mem₃]; exact Proof.Cmac.zero4_bytes _ _
  · rw [mem₈, mem₃, Proof.Cmac.zero4, Proof.Cmac.bytesAt_frame16 (Proof.Cmac.frame_store4 _ _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cSt),
      Proof.Cmac.xor4Mem_bytes _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint cSt), h.blk, stS]
  · rw [mem₈]; exact fr₃

theorem finPre_wp {s₀ : State} (hp : FPre s₀) : WP isa finPre s₀ (FMid s₀) := by
  refine WP.seq (WP.mono (finSave_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := BPost s₀) ?_ fun _ h => finArgs_wp hp h)
  obtain ev : isa.eval .e s₁ = some (decide (N s₀ = 16)) := by
    show VG.X86.eval .e s₁ = _; rw [eval_e, h₁.zf]
  by_cases hL : N s₀ = 16
  · exact WP.ite true (by rw [ev]; simp [hL]) (fun _ => full_wp hp hL h₁) (fun h => by cases h)
  · exact WP.ite false (by rw [ev]; simp [hL]) (fun h => by cases h)
      (fun _ => partial_wp hp (by have := hp.len; omega_using [hL, this]) h₁)

/-! ## The whole function -/

theorem finalize_wp {s₀ : State} (h0 : finalizeX86.pre s₀) :
    WP isa (finalize v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ finalizeX86.post s₀ s' := by
  obtain hp := FPre.of h0
  have hR := hp.rounds
  obtain hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hR with h | h | h <;> omega_using [h]
  have hsc : (arg s₀ 5).toNat + 2176 ≤ 2 ^ 32 := hp.scr_fit
  have cA := hp.cA
  unfold finalize
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (ctr_call v h₁.pre) fun s₂ h₂ => ?_)
  obtain hb : below (s₁.gpr .esp) 32 = stkR s₀ := by rw [h₁.esp]; exact hp.below_eq
  obtain f₁ : Frame [stR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) s₁.mem :=
    h₁.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
  obtain f₂ : Frame [stR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) s₂.mem := by
    have fr := h₂.frame
    rw [hb, cA] at fr
    refine f₁.trans (fr.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  obtain big₁ := UPre.big_of f₁
  obtain big₂ := UPre.big_of f₂
  obtain esp₂ : s₂.gpr .esp = E s₀ := by rw [h₂.saved .esp (by simp [calleeSaved]), h₁.esp]
  obtain rdwr₂ : s₂.rd ++ s₂.wr = [keyR s₀, lastR s₀, argsR s₀, stR s₀, scrR s₀] := by
    rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, hp.rd, hp.wr]; rfl
  obtain hrw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]
  obtain sl : ∀ r d, (r, d) ∈ saved → s₂.mem.readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r := by
    intro r d hrd
    obtain hb := saved_bound _ hrd
    rw [f₂.readW (r := ⟨(S s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.st_scr.symm.sub_left (UPre.scr_sub (by omega))
      · exact Offset.disjoint_base _ hb.1 (by omega)
      · exact hp.b_scr.symm.sub_left (UPre.scr_sub (by omega))) (by decide), savedMem_slot s₀ hrd]
  obtain sch : Spec.Aes.bytesAt s₁.mem ((W s₀).setWidth 64) (16 * (R s₀ + 1)) =
      Spec.Aes.bytesAt s₀.mem ((W s₀).setWidth 64) (16 * (R s₀ + 1)) :=
    Proof.Cmac.bytesAt_frame big₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.key_st.sub_left (Region.sub_prefix (by omega_using [hR]))
      · exact hp.key_scr.sub_left (Region.sub_prefix (by omega_using [hR]))
      · exact hp.b_key.symm.sub_left (Region.sub_prefix (by omega_using [hR]))) (by omega_using [hR])
  rw [restore_eq]
  refine wp_arg (s₀ := s₀) esp₂ (by rw [hrw₂]; exact hp.arg_in (by decide)) (hp.arg_keep big₂ (by decide))
    fun s₃ u₃ => ?_
  refine Spill.restore_ofNat_ok saved saved_fits (by rw [u₃.gpr]; omega_using [hsc]) saved_ne_eax (fun p hp' => ?_)
    (fun p hp' => by rw [u₃.gpr, u₃.mem]; exact sl p.1 p.2 hp') fun s₄ r₄ => WP.block_nil ?_
  · have hb := saved_bound p hp'
    rw [u₃.gpr, u₃.rd, u₃.wr, rdwr₂]
    exact ⟨scrR s₀, by simp, Offset.contains_base _ (by omega_using [hb]) (by omega_using [hb])⟩
  refine ⟨⟨r₄.abi (by decide) (by decide) (by rw [u₃.other _ (by decide), esp₂]), ?_⟩, ?_⟩
  · rw [r₄.mem, u₃.mem]
    obtain rs : (retR s₀).Disjoint (stkR s₀) := by
      have := Offset.disjoint_below_above ((E s₀).setWidth 64) (m := 32) (a := 0) (l := 4) (by decide)
      rw [add0] at this
      exact this.symm
    exact big₂.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.ret_st
      · exact hp.ret_scr
      · exact rs) (by decide)
  · intro hk msg hm hne hst
    have hk' : Spec.Aes.bytesAt s₀.mem ((W s₀).setWidth 64 + BitVec.ofNat 64 240) 32 =
        (Spec.Cmac.subkeys (ciph s₀) 16).1 ++ (Spec.Cmac.subkeys (ciph s₀) 16).2 := hk
    obtain ⟨e1, e2⟩ := Proof.Cmac.k1k2 (Proof.Cmac.subkeys_aes_length _ _) hk'
    show Spec.Aes.bytesAt s₄.mem ((St s₀).setWidth 64) 16 = _
    rw [r₄.mem, u₃.mem, h₂.out, sch, cA, h₁.blk, mn, e1, e2, hst,
      Proof.Cmac.macFull_split _ hm (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
        (by rw [Proof.Cmac.bytesAt_length]; exact hne), Proof.Cmac.xor_comm]

end VG.Proof.CmacAes.X86

end

/-!
# AES-CMAC on x86: `vg_cmac_aes_finalize` is constant time

The code before the call is checked by the taint analysis, from `esp` and the
stack arguments (its branches and the copy loop depend only on `last_len`),
the call of `vg_aes_ctr32_to`, in its frame, is constant time by its own proof
(`ctr_rel`), its arguments pinned by the correctness proof (`FMid`), and the
restore after it by the taint analysis again.
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.Aes.X86 (Ctr32Impl)

variable (v : Ctr32Impl)

theorem FPre.argsOut {s₀ : State} (hp : FPre s₀) {s : State} (hesp : s.gpr .esp = E s₀) (hwr : s.wr = s₀.wr) :
    ArgsOut 6 s := by
  have hs : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.esp_fit
  refine ⟨by rw [hesp]; omega, ?_⟩
  rw [hwr, hp.wr, hesp]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_st hp.args_st
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_scr hp.args_scr

/-- Two runs agree on `esp`, the stack arguments and the registers `rs`. -/
theorem fagree {s₀ s₀' : State} (hq : finalizeX86.pub s₀ s₀') (hp : FPre s₀) (hp' : FPre s₀') {rs : List Reg}
    {s₁ s₂ : State} (h₁ : Pt s₀ s₁) (h₂ : Pt s₀' s₂) (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.X86.Taint.Agree (argTaint rs (4 + 4 * 6)) s₁ s₂ :=
  agree_argTaint hr (by rw [h₁.esp, h₂.esp]; exact hq.1) (hp.argsOut h₁.esp h₁.wr) (hp'.argsOut h₂.esp h₂.wr)
    fun i hi => by rw [arg_cur (h₁.esp) (h₁.args i hi), arg_cur (h₂.esp) (h₂.args i hi), hq.2 i hi]

theorem FMid.f {s₀ s : State} (h : FMid s₀ s) :
    Frame [stR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) s.mem :=
  h.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨stR s₀, by simp, fun _ h => h⟩

theorem fcall_after {s₀ : State} (hp : FPre s₀) {s : State} (h : FMid s₀ s) : WP isa (ctrCall v.callee) s (Pt s₀) :=
  WP.mono (ctr_call v h.pre) fun s' hc => by
    obtain hb : below (s.gpr .esp) 32 = stkR s₀ := by rw [h.esp]; exact hp.below_eq
    have fr := hc.frame
    rw [hb, hp.cA] at fr
    obtain big := UPre.big_of (h.f.trans (fr.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩))
    exact ⟨by rw [hc.saved .esp (by simp [calleeSaved]), h.esp], by rw [hc.wr, h.wr],
      fun _ hi => hp.arg_keep big hi⟩

theorem finalize_rel {s₀ s₀' : State} (h0 : finalizeX86.pre s₀) (h0' : finalizeX86.pre s₀')
    (hq : finalizeX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (finalize v.callee) fun _ _ => True := by
  obtain hp := FPre.of h0
  obtain hp' := FPre.of h0'
  obtain eW : W s₀ = W s₀' := hq.2 0 (by decide)
  obtain eR : R s₀ = R s₀' := by rw [R, R, hq.2 1 (by decide)]
  obtain eSt : St s₀ = St s₀' := hq.2 2 (by decide)
  obtain eS : S s₀ = S s₀' := hq.2 5 (by decide)
  obtain pt₀ : ∀ {t : State}, Pt t t := ⟨rfl, rfl, fun _ _ => rfl⟩
  obtain a := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 6))
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact fagree hq hp hp' pt₀ pt₀ fun r hr => by simp at hr)
    (c := finPre) (by taint_decide)).wp (F₁ := FMid s₀) (F₂ := FMid s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨finPre_wp hp, finPre_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  obtain c := ((ctr_rel v (E := E s₀) (P := fun s₁ s₂ => FMid s₀ s₁ ∧ FMid s₀' s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, by rw [eW, eS, eSt, eR]; exact h.2.pre, h.1.esp, h.2.esp.trans hq.1.symm⟩).wp
      (F₁ := Pt s₀) (F₂ := Pt s₀') fun _ _ h => ⟨fcall_after v hp h.1, fcall_after v hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  obtain b := RelCT.taint (A := taint) (P := fun s₁ s₂ => Pt s₀ s₁ ∧ Pt s₀' s₂) (argTaint [] (4 + 4 * 6))
    (fun _ _ h => fagree hq hp hp' h.1 h.2 fun r hr => by simp at hr)
    (c := .block (restore 5)) (by taint_decide)
  exact a.seq (c.seq b)

theorem finalize_ct : ConstantTime isa finalizeX86.pre finalizeX86.pub (finalize v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finalize_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.X86

end

end

@[expose] public section

section

/-!
# AES-CMAC on x86: `vg_cmac_aes_subkeys` is constant time

The code before the call is checked by the taint analysis from `esp` and the
stack arguments (which nothing writes, `argTaint`), the call of
`vg_aes_ctr32_to`, in its frame, is constant time by its own proof (`ctr_rel`),
and the code after it by the taint analysis again, from `esp`, the stack
arguments and `ebx` (the subkeys, which the correctness proof pins).
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.Aes.X86 (Ctr32Impl)

variable (v : Ctr32Impl)

theorem SPre.argsOut {s₀ : State} (hp : SPre s₀) {s : State} (hesp : s.gpr .esp = E s₀) (hwr : s.wr = s₀.wr) :
    ArgsOut 4 s := by
  have hs : (s₀.gpr .esp).toNat + 20 ≤ 2 ^ 32 := hp.esp_fit
  refine ⟨by rw [hesp]; omega, ?_⟩
  rw [hwr, hp.wr, hesp]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_k hp.args_k
  · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_scr hp.args_scr

/-- What two runs agree on at a point between the calls. -/
structure SPt (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = E s₀
  wr : s.wr = s₀.wr
  args : ∀ i < 4, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i

section
variable {s₀ s₀' : State} (hq : subkeysX86.pub s₀ s₀')
include hq

theorem spub_arg {i : Nat} (hi : i < 4) : arg s₀ i = arg s₀' i := hq.2 i hi

/-- Two runs agree on `esp`, the stack arguments and the registers `rs`. -/
theorem SPt.agree (hp : SPre s₀) (hp' : SPre s₀') {rs : List Reg} {s₁ s₂ : State} (h₁ : SPt s₀ s₁)
    (h₂ : SPt s₀' s₂) (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.X86.Taint.Agree (argTaint rs (4 + 4 * 4)) s₁ s₂ :=
  agree_argTaint hr (by rw [h₁.esp, h₂.esp]; exact hq.1) (hp.argsOut h₁.esp h₁.wr) (hp'.argsOut h₂.esp h₂.wr)
    fun i hi => by rw [arg_cur (h₁.esp) (h₁.args i hi), arg_cur (h₂.esp) (h₂.args i hi), spub_arg hq hi]

end

/-- What is known after the call. -/
structure SPost (s₀ : State) (s : State) : Prop where
  ebx : s.gpr .ebx = Kb s₀
  pt : SPt s₀ s

theorem spost_wp {s₀ : State} (hp : SPre s₀) {s : State} (h : SAfter s₀ s) : WP isa (ctrCall v.callee) s (SPost s₀) :=
  WP.mono (ctr_call v h.pre) fun s' hc => by
    have hb : below (s.gpr .esp) 32 = stkR s₀ := by rw [h.esp]; exact hp.below_eq
    have fr := hc.frame
    rw [hb, hp.cA, h.mem] at fr
    have big : Frame (SBig s₀) s₀.mem s'.mem := (sbig_of (sPreMem_frame s₀)).trans (fr.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨scR s₀, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨kR s₀, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨scR s₀, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
    exact ⟨by rw [hc.saved .ebx (by simp [calleeSaved]), h.pre.ebx],
      ⟨by rw [hc.saved .esp (by simp [calleeSaved]), h.esp], by rw [hc.wr, h.wr], fun _ hi => hp.arg_keep big hi⟩⟩

theorem subkeys_rel {s₀ s₀' : State} (h0 : subkeysX86.pre s₀) (h0' : subkeysX86.pre s₀')
    (hq : subkeysX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (subkeys v.callee) fun _ _ => True := by
  have hp := SPre.of h0
  have hp' := SPre.of h0'
  have eW : W s₀ = W s₀' := spub_arg hq (by decide)
  have eR : R s₀ = R s₀' := by rw [R, R, spub_arg hq (by decide)]
  have eK : Kb s₀ = Kb s₀' := spub_arg hq (by decide)
  have eS : Sc s₀ = Sc s₀' := spub_arg hq (by decide)
  have pt₀ : ∀ {t : State}, SPt t t := ⟨rfl, rfl, fun _ _ => rfl⟩
  have a := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 4))
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact SPt.agree hq hp hp' pt₀ pt₀ fun r hr => by simp at hr)
    (c := .block subkeysPre) (by taint_decide)).wp (F₁ := SAfter s₀) (F₂ := SAfter s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨spre_wp hp, spre_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have c := ((ctr_rel v (E := E s₀) (P := fun s₁ s₂ => SAfter s₀ s₁ ∧ SAfter s₀' s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, by rw [eW, eS, eK, eR]; exact h.2.pre, h.1.esp, h.2.esp.trans hq.1.symm⟩).wp
      (F₁ := SPost s₀) (F₂ := SPost s₀') fun _ _ h => ⟨spost_wp v hp h.1, spost_wp v hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => SPost s₀ s₁ ∧ SPost s₀' s₂) (argTaint [.ebx] (4 + 4 * 4))
    (fun _ _ h => SPt.agree hq hp hp' h.1.pt h.2.pt fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.ebx, h.2.ebx, eK])
    (c := .block subkeysPost) (by taint_decide)
  exact a.seq (c.seq b)

theorem subkeys_ct : ConstantTime isa subkeysX86.pre subkeysX86.pub (subkeys v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (subkeys_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.X86

end

/-!
# AES-CMAC on x86: `Verified`

Correctness and constant time, a state satisfying each precondition, and the
shared contracts of `Spec/Cmac/Contract.lean`, with 32 bytes of stack: each
call of `vg_aes_ctr32_to` pushes its seven arguments and the return address.
`vg_cmac_aes_update` with AES-NI uses none of them.
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.Aes.X86 (Ctr32Impl)

variable (v : Ctr32Impl)

theorem callee_nosp_all : v.callee.code.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => by
    have h := v.nosp i hi
    simp only [h, Bool.not_false]

theorem subkeys_nosp : NoSp (subkeys v.callee) := by
  apply NoSp.of_all
  simp only [subkeys, ctrCall, Code.allInstrs, callee_nosp_all v]
  decide +kernel

theorem subkeys_stack : stackUse (subkeys v.callee) = 32 := by
  simp only [subkeys, ctrCall, stackUse, v.stack]
  decide +kernel

theorem subkeys_spSafe : (subkeys v.callee).all (fun i => !isa.writesSp i) = true := by
  simp only [subkeys, ctrCall, Code.all, v.spSafe]
  decide +kernel

theorem update_nosp : NoSp (update v.callee) := by
  unfold update
  split
  · exact NoSp.of_all (by lit_decide)
  · apply NoSp.of_all
    simp only [updateCalls, body, ctrCall, Code.allInstrs, callee_nosp_all v]
    decide +kernel

theorem update_stack : stackUse (update v.callee) ≤ 32 := by
  unfold update
  split
  · exact Nat.le_trans (Nat.le_of_eq (by lit_decide : stackUse updateNi = 0)) (Nat.zero_le _)
  · simp only [updateCalls, body, ctrCall, stackUse, v.stack]
    decide +kernel

theorem update_spSafe : (update v.callee).all (fun i => !isa.writesSp i) = true := by
  unfold update
  split
  · exact Code.all_of_spTest (by lit_decide)
  · simp only [updateCalls, body, ctrCall, Code.all, v.spSafe]
    decide +kernel

theorem finalize_nosp : NoSp (finalize v.callee) := by
  apply NoSp.of_all
  simp only [finalize, finPre, partialBlock, copy, ctrCall, Code.allInstrs, callee_nosp_all v]
  decide +kernel

theorem finalize_stack : stackUse (finalize v.callee) = 32 := by
  simp only [finalize, finPre, partialBlock, copy, ctrCall, stackUse, v.stack]
  decide +kernel

theorem finalize_spSafe : (finalize v.callee).all (fun i => !isa.writesSp i) = true := by
  simp only [finalize, finPre, partialBlock, copy, ctrCall, Code.all, v.spSafe]
  decide +kernel

end VG.Proof.CmacAes.X86
