module

public import VerifiedGarbage.Spec.Cmac.Contract
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.CmacAes.Arm.UpdateCorrect
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Spec.Cmac.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Cmac.Block
meta import VerifiedGarbage.Proof.CmacAes.Arm.UpdateCorrect
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.CmacAes.Arm.UpdateLoop
meta import VerifiedGarbage.Proof.CmacAes.Arm.UpdateLoop
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Cmac.Dbl32
meta import VerifiedGarbage.Proof.Cmac.Dbl32

/-! ### `CmacAes.Arm.Subkeys`, which this module and modules that import it used -/

section

@[expose] public section

section

/-!
# AES-CMAC on ARMv7: doubling a block in four 32-bit words

`dbl src dst` loads a block as four byte-reversed words (`rev`), the block as
a big-endian integer (`Cmac.ofBytes_rev4`), doubles the integer a word at a
time (`Cmac.dbl_words4`), and stores the words byte-reversed again
(`Cmac.le4_rev4`).
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd op2_imm op2_reg op2_lsr op2_lsl wp_mov wp_sub wp_and wp_orr wp_rev wp_ldr wp_str)

theorem rev_eq (a : BitVec 32) : rev a = byteRev32 a := rfl

/-- The memory after `dbl src dst`, with `r6` pointing at `A`. -/
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

/-- `dbl src dst`, with `r6` pointing at `K`. -/
theorem dbl_wp {is : List Instr} {s : State} {Q : State → Prop} {K : BitVec 32} {src dst : Nat}
    (h6 : s.gpr .r6 = K) (hs : src + 12 < 4096) (hd : dst + 12 < 4096)
    (fs : K.toNat + src + 16 ≤ 2 ^ 32) (fd : K.toNat + dst + 16 ≤ 2 ^ 32)
    (rS : Covers [⟨State.addr K + BitVec.ofNat 64 src, 16⟩] (s.rd ++ s.wr))
    (wD : Covers [⟨State.addr K + BitVec.ofNat 64 dst, 16⟩] s.wr)
    (k : ∀ s', (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → s'.gpr r = s.gpr r) →
      s'.mem = dblMem s.mem (State.addr K) src dst → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      WP isa (.block is) s' Q) :
    WP isa (.block (dbl src dst ++ is)) s Q := by
  simp only [dbl, List.cons_append, List.nil_append]
  refine wp_ldr (a := State.addr K + BitVec.ofNat 64 src) (by omega_arith) (by rw [h6]; exact addr_add (by omega_arith))
    (in_word0 rS) fun s₁ u₁ => ?_
  refine wp_ldr (a := State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 4) (by omega_arith)
    (by rw [u₁.other _ (by decide), h6]; exact addr_word 4 fs (by decide))
    (by rw [u₁.rd, u₁.wr]; exact in_word rS (by decide)) fun s₂ u₂ => ?_
  refine wp_ldr (a := State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 8) (by omega_arith)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h6]; exact addr_word 8 fs (by decide))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact in_word rS (by decide)) fun s₃ u₃ => ?_
  refine wp_ldr (a := State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 12) (by omega_arith)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h6]
        exact addr_word 12 fs (by decide))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact in_word rS (by decide)) fun s₄ u₄ => ?_
  refine wp_rev fun s₅ u₅ => wp_rev fun s₆ u₆ => wp_rev fun s₇ u₇ => wp_rev fun s₈ u₈ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₉ u₉ => wp_mov (op2_imm (by decide)) fun s₁₀ u₁₀ =>
    wp_sub (op2_reg _ _) fun s₁₁ u₁₁ => wp_and (op2_imm (by decide)) fun s₁₂ u₁₂ => ?_
  refine wp_mov (op2_lsl (by decide)) fun s₁₃ u₁₃ => wp_orr (op2_lsr (by decide)) fun s₁₄ u₁₄ =>
    wp_mov (op2_lsl (by decide)) fun s₁₅ u₁₅ => wp_orr (op2_lsr (by decide)) fun s₁₆ u₁₆ =>
    wp_mov (op2_lsl (by decide)) fun s₁₇ u₁₇ => wp_orr (op2_lsr (by decide)) fun s₁₈ u₁₈ =>
    wp_mov (op2_lsl (by decide)) fun s₁₉ u₁₉ => wp_eor (op2_reg _ _) fun s₂₀ u₂₀ => ?_
  refine wp_rev fun s₂₁ u₂₁ => wp_rev fun s₂₂ u₂₂ => wp_rev fun s₂₃ u₂₃ => wp_rev fun s₂₄ u₂₄ => ?_
  obtain g : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → s₂₄.gpr r = s.gpr r :=
    fun r h0 h1 h2 h3 h4 h12 => by
      rw [u₂₄.other _ h3, u₂₃.other _ h2, u₂₂.other _ h1, u₂₁.other _ h0, u₂₀.other _ h3, u₁₉.other _ h3,
        u₁₈.other _ h2, u₁₇.other _ h2, u₁₆.other _ h1, u₁₅.other _ h1, u₁₄.other _ h0, u₁₃.other _ h0,
        u₁₂.other _ h12, u₁₁.other _ h12, u₁₀.other _ h4, u₉.other _ h12, u₈.other _ h3, u₇.other _ h2,
        u₆.other _ h1, u₅.other _ h0, u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, u₁.other _ h0]
  obtain g6 : s₂₄.gpr .r6 = K := by
    rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h6]
  obtain m24 : s₂₄.mem = s.mem := by
    rw [u₂₄.mem, u₂₃.mem, u₂₂.mem, u₂₁.mem, u₂₀.mem, u₁₉.mem, u₁₈.mem, u₁₇.mem, u₁₆.mem, u₁₅.mem, u₁₄.mem,
      u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem,
      u₁.mem]
  obtain rd24 : s₂₄.rd = s.rd := by
    rw [u₂₄.rd, u₂₃.rd, u₂₂.rd, u₂₁.rd, u₂₀.rd, u₁₉.rd, u₁₈.rd, u₁₇.rd, u₁₆.rd, u₁₅.rd, u₁₄.rd, u₁₃.rd,
      u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr24 : s₂₄.wr = s.wr := by
    rw [u₂₄.wr, u₂₃.wr, u₂₂.wr, u₂₁.wr, u₂₀.wr, u₁₉.wr, u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr, u₁₄.wr, u₁₃.wr,
      u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain sp24 : s₂₄.sp = s.sp := by
    rw [u₂₄.sp, u₂₃.sp, u₂₂.sp, u₂₁.sp, u₂₀.sp, u₁₉.sp, u₁₈.sp, u₁₇.sp, u₁₆.sp, u₁₅.sp, u₁₄.sp, u₁₃.sp,
      u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  -- The four words.
  have w₀ : s₁.gpr .r0 = s.mem.readW (State.addr K + BitVec.ofNat 64 src) 32 := u₁.gpr
  obtain w₁ : s₂.gpr .r1 = s.mem.readW (State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 4) 32 := by
    rw [u₂.gpr, u₁.mem]
  obtain w₂ : s₃.gpr .r2 = s.mem.readW (State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 8) 32 := by
    rw [u₃.gpr, u₂.mem, u₁.mem]
  obtain w₃ : s₄.gpr .r3 = s.mem.readW (State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 12) 32 := by
    rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem]
  obtain b₀ : s₈.gpr .r0 = byteRev32 (s.mem.readW (State.addr K + BitVec.ofNat 64 src) 32) := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), w₀, rev_eq]
  obtain b₁ : s₈.gpr .r1 = byteRev32 (s.mem.readW (State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 4) 32) := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), w₁, rev_eq]
  obtain b₂ : s₈.gpr .r2 = byteRev32 (s.mem.readW (State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 8) 32) := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      w₂, rev_eq]
  obtain b₃ : s₈.gpr .r3 = byteRev32 (s.mem.readW (State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 12) 32) := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), w₃, rev_eq]
  obtain mask : s₁₂.gpr .r12 = ((0 : BitVec 32) - (s₈.gpr .r0 >>> 31)) &&& 0x87 := by
    rw [u₁₂.gpr, u₁₁.gpr, u₁₀.gpr, u₁₀.other _ (by decide), u₉.gpr]
  obtain v₀ : s₂₄.gpr .r0 = byteRev32 (Proof.Cmac.dblW0 (s₈.gpr .r0) (s₈.gpr .r1)) := by
    rw [u₂₄.other _ (by decide), u₂₃.other _ (by decide), u₂₂.other _ (by decide), u₂₁.gpr, rev_eq,
      u₂₀.other _ (by decide), u₁₉.other _ (by decide), u₁₈.other _ (by decide), u₁₇.other _ (by decide),
      u₁₆.other _ (by decide), u₁₅.other _ (by decide), u₁₄.gpr, u₁₃.gpr, u₁₃.other _ (by decide),
      u₁₂.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₉.other _ (by decide)]
    rfl
  obtain v₁ : s₂₄.gpr .r1 = byteRev32 (Proof.Cmac.dblW0 (s₈.gpr .r1) (s₈.gpr .r2)) := by
    rw [u₂₄.other _ (by decide), u₂₃.other _ (by decide), u₂₂.gpr, rev_eq, u₂₁.other _ (by decide),
      u₂₀.other _ (by decide), u₁₉.other _ (by decide), u₁₈.other _ (by decide), u₁₇.other _ (by decide),
      u₁₆.gpr, u₁₅.gpr, u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₄.other _ (by decide),
      u₁₃.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₂.other _ (by decide),
      u₁₁.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₉.other _ (by decide)]
    rfl
  obtain v₂ : s₂₄.gpr .r2 = byteRev32 (Proof.Cmac.dblW0 (s₈.gpr .r2) (s₈.gpr .r3)) := by
    rw [u₂₄.other _ (by decide), u₂₃.gpr, rev_eq, u₂₂.other _ (by decide), u₂₁.other _ (by decide),
      u₂₀.other _ (by decide), u₁₉.other _ (by decide), u₁₈.gpr, u₁₇.gpr, u₁₇.other _ (by decide),
      u₁₆.other _ (by decide), u₁₆.other _ (by decide), u₁₅.other _ (by decide), u₁₅.other _ (by decide),
      u₁₄.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₃.other _ (by decide),
      u₁₂.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₉.other _ (by decide)]
    rfl
  obtain v₃ : s₂₄.gpr .r3 = byteRev32 (Proof.Cmac.dblW3 (s₈.gpr .r0) (s₈.gpr .r3)) := by
    rw [u₂₄.gpr, rev_eq, u₂₃.other _ (by decide), u₂₂.other _ (by decide), u₂₁.other _ (by decide), u₂₀.gpr,
      u₁₉.gpr, u₁₉.other _ (by decide), u₁₈.other _ (by decide), u₁₈.other _ (by decide), u₁₇.other _ (by decide),
      u₁₇.other _ (by decide), u₁₆.other _ (by decide), u₁₆.other _ (by decide), u₁₅.other _ (by decide),
      u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide),
      u₁₃.other _ (by decide), mask, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide)]
    rfl
  refine wp_str (a := State.addr K + BitVec.ofNat 64 dst) (by omega_arith) (by rw [g6]; exact addr_add (by omega_arith))
    (by rw [wr24]; exact in_word0 wD) fun s₂₅ v₂₅ => ?_
  refine wp_str (a := State.addr K + BitVec.ofNat 64 dst + BitVec.ofNat 64 4) (by omega_arith)
    (by rw [v₂₅.gpr, g6]; exact addr_word 4 fd (by decide))
    (by rw [v₂₅.wr, wr24]; exact in_word wD (by decide)) fun s₂₆ v₂₆ => ?_
  refine wp_str (a := State.addr K + BitVec.ofNat 64 dst + BitVec.ofNat 64 8) (by omega_arith)
    (by rw [v₂₆.gpr, v₂₅.gpr, g6]; exact addr_word 8 fd (by decide))
    (by rw [v₂₆.wr, v₂₅.wr, wr24]; exact in_word wD (by decide)) fun s₂₇ v₂₇ => ?_
  refine wp_str (a := State.addr K + BitVec.ofNat 64 dst + BitVec.ofNat 64 12) (by omega_arith)
    (by rw [v₂₇.gpr, v₂₆.gpr, v₂₅.gpr, g6]; exact addr_word 12 fd (by decide))
    (by rw [v₂₇.wr, v₂₆.wr, v₂₅.wr, wr24]; exact in_word wD (by decide)) fun s₂₈ v₂₈ => k s₂₈ ?_ ?_ ?_ ?_ ?_
  · intro r h0 h1 h2 h3 h4 h12
    rw [v₂₈.gpr, v₂₇.gpr, v₂₆.gpr, v₂₅.gpr, g r h0 h1 h2 h3 h4 h12]
  · rw [v₂₈.mem, v₂₇.mem, v₂₆.mem, v₂₅.mem, v₂₇.gpr, v₂₆.gpr, v₂₅.gpr, m24, v₀, v₁, v₂, v₃, b₀, b₁, b₂, b₃]
    rfl
  · rw [v₂₈.rd, v₂₇.rd, v₂₆.rd, v₂₅.rd, rd24]
  · rw [v₂₈.wr, v₂₇.wr, v₂₆.wr, v₂₅.wr, wr24]
  · rw [v₂₈.sp, v₂₇.sp, v₂₆.sp, v₂₅.sp, sp24]

end VG.Proof.CmacAes.Arm

end

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_subkeys`

`L = CIPH_K(0)` is computed into the first block of the subkeys (a zero
counter block and a zero data block), then doubled there (`K1`) and into the
second block (`K2`).
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd op2_imm op2_reg wp_mov wp_add wp_ldr saveMem saveList_ok saveMem_frame
  readW_writeW_save)

section
variable (s₀ : State)

/-- The subkeys. -/
abbrev Kb : BitVec 32 := s₀.gpr .r2
/-- The scratch buffer. -/
abbrev Sc : BitVec 32 := s₀.gpr .r3

abbrev kR : Region := ⟨State.addr (Kb s₀), 32⟩
abbrev scR : Region := ⟨State.addr (Sc s₀), 2176⟩

end

/-- The precondition, by name. -/
structure SPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀]
  wr : s₀.wr = [kR s₀, scR s₀]
  sch_k : (schR s₀).Disjoint (kR s₀)
  sch_scr : (schR s₀).Disjoint (scR s₀)
  k_scr : (kR s₀).Disjoint (scR s₀)
  b_sch : (belowR s₀).Disjoint (schR s₀)
  b_k : (belowR s₀).Disjoint (kR s₀)
  b_scr : (belowR s₀).Disjoint (scR s₀)
  sch_fit : (W s₀).toNat + 240 ≤ 2 ^ 32
  k_fit : (Kb s₀).toNat + 32 ≤ 2 ^ 32
  scr_fit : (Sc s₀).toNat + 2176 ≤ 2 ^ 32
  sp8 : 8 ≤ s₀.sp.toNat
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem SPre.of {s₀ : State} (h : subkeysArm.pre s₀) : SPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩

/-- The registers `subkeys` saves, and where. -/
def saved4 : List (Reg × Nat) := [(.r4, 2064), (.r5, 2068), (.r6, 2072), (.lr, 2076)]

theorem subkeysPre_eq : subkeysPre = saved4.map (fun p => Instr.str p.1 .r3 p.2) ++
    (.mov .r6 (.reg .r2) :: .mov .r5 (.reg .r3) :: .mov .r12 (.imm 0) :: (zeroBlk .r12 .r3 2048 ++
      (zeroBlk .r12 .r2 0 ++ ([.dp .add .r2 .r5 (.imm (BitVec.ofNat 32 2048)), .mov .r3 (.reg .r6),
        .mov .r4 (.imm 1)] : List Instr)))) := rfl

theorem subkeysPost_eq : subkeysPost = dbl 0 0 ++ (dbl 0 16 ++
    ([(.r4, 2064), (.r6, 2072), (.lr, 2076)].map (fun (p : Reg × Nat) => Instr.ldr p.1 .r5 p.2) ++
      ([.ldr .r5 .r5 2068] : List Instr))) := rfl

theorem saved4_slot (m : Mem) (B : Addr) (g : Reg → BitVec 32) {r : Reg} {d : Nat} (h : (r, d) ∈ saved4) :
    (saveMem m B g saved4).readW (B + BitVec.ofNat 64 d) 32 = g r :=
  Spill.saveMem_saved (lo := 2064) (hi := 2080) B g m saved4 (by decide) (r, d) h

/-- The memory before the call. -/
def preMem (s₀ : State) : Mem :=
  Proof.Cmac.zero4 (Proof.Cmac.zero4 (saveMem s₀.mem (State.addr (Sc s₀)) s₀.gpr saved4)
    (State.addr (Sc s₀) + BitVec.ofNat 64 2048)) (State.addr (Kb s₀))

/-- What the code before the call leaves. -/
structure SAfter (s₀ s : State) : Prop where
  pre : CallPre s (W s₀) (Sc s₀ + BitVec.ofNat 32 2048) (Kb s₀) (Sc s₀) (R s₀) .r4 .r5
  keep : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r12 → s.gpr r = s₀.gpr r
  r5 : s.gpr .r5 = Sc s₀
  r6 : s.gpr .r6 = Kb s₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = preMem s₀

theorem pre_wp {s₀ : State} (hp : SPre s₀) : WP isa (.block subkeysPre) s₀ (SAfter s₀) := by
  have kf := hp.k_fit
  have sf := hp.scr_fit
  have sf' : (s₀.gpr .r3).toNat + 2176 ≤ 2 ^ 32 := sf
  have hR := hp.rounds
  obtain hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hR with h | h | h <;> omega_arith
  obtain cK : ∀ d n, d + n ≤ 32 → Covers [⟨State.addr (Kb s₀) + BitVec.ofNat 64 d, n⟩] s₀.wr := fun d n h => by
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨kR s₀, by simp, d, rfl, h⟩
  obtain cS : ∀ d n, d + n ≤ 2176 → Covers [⟨State.addr (Sc s₀) + BitVec.ofNat 64 d, n⟩] s₀.wr := fun d n h => by
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR s₀, by simp, d, rfl, h⟩
  obtain rw' : ∀ {rs a n}, Covers rs s₀.wr → InRegions rs a n → InRegions (s₀.rd ++ s₀.wr) a n :=
    fun h hi => by obtain ⟨r, hr, hc⟩ := h _ _ hi; exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain cKr : ∀ d n, d + n ≤ 32 → Covers [⟨State.addr (Kb s₀) + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) :=
    fun d n h a k hi => rw' (cK d n h) hi
  obtain aS : ∀ {d}, d < 2176 → State.addr (Sc s₀ + BitVec.ofNat 32 d) = State.addr (Sc s₀) + BitVec.ofNat 64 d :=
    fun _ => addr_add (by omega_arith)
  -- Before the call.
  rw [subkeysPre_eq]
  refine saveList_ok saved4 s₀ _ (fun p hp' => ?_) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  · have hb : 2064 ≤ p.2 ∧ p.2 + 4 ≤ 2080 := by
      simp only [saved4, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl <;> decide
    exact ⟨by omega_arith, by omega_arith, cS p.2 4 (by omega_arith) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩⟩
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ =>
    wp_mov (op2_imm (by decide)) fun s₄ u₄ => ?_
  obtain r3₄ : s₄.gpr .r3 = Sc s₀ := by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  refine Proof.CmacAes.Arm.zeroBlk_ok u₄.gpr (by decide) (by rw [r3₄]; omega_arith)
    (by rw [r3₄, u₄.wr, u₃.wr, u₂.wr, wr₁]; exact cS 2048 16 (by decide)) fun s₅ G₅ m₅ rd₅ wr₅ sp₅ => ?_
  obtain r2₅ : s₅.gpr .r2 = Kb s₀ := by
    rw [G₅, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  refine Proof.CmacAes.Arm.zeroBlk_ok (by rw [G₅, u₄.gpr]) (by decide) (by rw [r2₅]; omega_arith)
    (by rw [r2₅, add0, wr₅, u₄.wr, u₃.wr, u₂.wr, wr₁]; simpa using cK 0 16 (by decide))
    fun s₆ G₆ m₆ rd₆ wr₆ sp₆ => ?_
  refine wp_add (op2_imm (by decide)) fun s₇ u₇ => wp_mov (op2_reg _ _) fun s₈ u₈ =>
    wp_mov (op2_imm (by decide)) fun s₉ u₉ => WP.block_nil ?_
  obtain keep₉ : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r12 → s₉.gpr r = s₀.gpr r :=
    fun r h2 h3 h4 h5 h6 h12 => by
      rw [u₉.other _ h4, u₈.other _ h3, u₇.other _ h2, G₆, G₅, u₄.other _ h12, u₃.other _ h5, u₂.other _ h6, g₁]
  obtain r5₉ : s₉.gpr .r5 = Sc s₀ := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), G₆, G₅, u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), g₁]
  obtain r6₉ : s₉.gpr .r6 = Kb s₀ := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), G₆, G₅, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, g₁]
  obtain sp₉ : s₉.sp = s₀.sp := by rw [u₉.sp, u₈.sp, u₇.sp, sp₆, sp₅, u₄.sp, u₃.sp, u₂.sp, sp₁]
  obtain rd₉ : s₉.rd = s₀.rd := by rw [u₉.rd, u₈.rd, u₇.rd, rd₆, rd₅, u₄.rd, u₃.rd, u₂.rd, rd₁]
  obtain wr₉ : s₉.wr = s₀.wr := by rw [u₉.wr, u₈.wr, u₇.wr, wr₆, wr₅, u₄.wr, u₃.wr, u₂.wr, wr₁]
  obtain mem₉ : s₉.mem = preMem s₀ := by
    rw [u₉.mem, u₈.mem, u₇.mem, m₆, r2₅, add0, m₅, r3₄, u₄.mem, u₃.mem, u₂.mem, m₁]; rfl
  -- The memory before the call.
  obtain cA : State.addr (Sc s₀ + BitVec.ofNat 32 2048) = State.addr (Sc s₀) + BitVec.ofNat 64 2048 := aS (by decide)
  obtain kC : (⟨State.addr (Kb s₀), 16⟩ : Region).Disjoint ⟨State.addr (Sc s₀) + BitVec.ofNat 64 2048, 16⟩ :=
    (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
  obtain hb : below s₉ = belowR s₀ := by rw [below, sp₉]; rfl
  obtain pre : CallPre s₉ (W s₀) (Sc s₀ + BitVec.ofNat 32 2048) (Kb s₀) (Sc s₀) (R s₀) .r4 .r5 :=
    { r0 := keep₉ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      r1 := by
        rw [keep₉ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [R]
      r2 := by
        rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, G₆, G₅, u₄.other _ (by decide), u₃.gpr,
          u₂.other _ (by decide), g₁]
      r3 := by rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), G₆, G₅, u₄.other _ (by decide),
          u₃.other _ (by decide), u₂.gpr, g₁]
      hra := u₉.gpr
      hrb := r5₉
      regs := by decide
      rounds := hR
      hsp := by rw [sp₉]; exact hp.sp8
      wc := by rw [cA]; exact hp.sch_scr.sub_right (Offset.sub_base _ (by decide))
      wd := hp.sch_k.sub_right (Region.sub_prefix (by decide))
      ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
      cd := by rw [cA]; exact kC.symm
      cs := by rw [cA]; exact Offset.disjoint_base _ (by decide) (by omega_arith)
      ds := (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      bw := by rw [hb]; exact hp.b_sch
      bc := by rw [hb, cA]; exact hp.b_scr.sub_right (Offset.sub_base _ (by decide))
      bd := by rw [hb]; exact hp.b_k.sub_right (Region.sub_prefix (by decide))
      bs := by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide))
      hW := hp.sch_fit
      hC := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
          Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
      hD := by omega_arith
      hS := by omega_arith
      reads := by
        rw [rd₉, wr₉, hp.rd]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
      writes := by
        rw [wr₉, hp.wr, cA]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨scR s₀, by simp, 2048, rfl, by simp⟩
        · exact ⟨kR s₀, by simp, 0, by simp, by simp⟩
        · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
      zero := by rw [mem₉, preMem]; exact Proof.Cmac.zero4_bytes _ _ }
  exact ⟨pre, keep₉, r5₉, r6₉, sp₉, rd₉, wr₉, mem₉⟩

theorem subkeys_wp {s₀ : State} (h0 : subkeysArm.pre s₀) :
    WP isa subkeys s₀ fun s' => abiPreserved s₀ s' ∧ subkeysArm.post s₀ s' := by
  obtain hp := SPre.of h0
  have kf := hp.k_fit
  have sf := hp.scr_fit
  have sf' : (s₀.gpr .r3).toNat + 2176 ≤ 2 ^ 32 := sf
  have hR := hp.rounds
  obtain hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hR with h | h | h <;> omega_arith
  obtain cK : ∀ d n, d + n ≤ 32 → Covers [⟨State.addr (Kb s₀) + BitVec.ofNat 64 d, n⟩] s₀.wr := fun d n h => by
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨kR s₀, by simp, d, rfl, h⟩
  obtain cS : ∀ d n, d + n ≤ 2176 → Covers [⟨State.addr (Sc s₀) + BitVec.ofNat 64 d, n⟩] s₀.wr := fun d n h => by
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR s₀, by simp, d, rfl, h⟩
  obtain rw' : ∀ {rs a n}, Covers rs s₀.wr → InRegions rs a n → InRegions (s₀.rd ++ s₀.wr) a n :=
    fun h hi => by obtain ⟨r, hr, hc⟩ := h _ _ hi; exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain cKr : ∀ d n, d + n ≤ 32 → Covers [⟨State.addr (Kb s₀) + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) :=
    fun d n h a k hi => rw' (cK d n h) hi
  obtain aS : ∀ {d}, d < 2176 → State.addr (Sc s₀ + BitVec.ofNat 32 d) = State.addr (Sc s₀) + BitVec.ofNat 64 d :=
    fun _ => addr_add (by omega_arith)
  unfold subkeys
  refine WP.seq (WP.mono (pre_wp hp) fun s₉ a => ?_)
  obtain ⟨pre, keep₉, r5₉, r6₉, sp₉, rd₉, wr₉, mem₉⟩ := a
  -- The memory before the call.
  obtain cA : State.addr (Sc s₀ + BitVec.ofNat 32 2048) = State.addr (Sc s₀) + BitVec.ofNat 64 2048 := aS (by decide)
  obtain kC : (⟨State.addr (Kb s₀), 16⟩ : Region).Disjoint ⟨State.addr (Sc s₀) + BitVec.ofNat 64 2048, 16⟩ :=
    (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
  obtain f₉ : Frame [scR s₀, kR s₀] s₀.mem s₉.mem := by
    rw [mem₉, preMem]
    refine (((saveMem_frame _ _ _ (L := 2176) (by decide) saved4 (by decide)).sub fun r hr => ?_).trans
      ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ?_)).trans
      ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ?_) <;>
    simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨scR s₀, by simp, fun _ h => h⟩
    · exact ⟨scR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨kR s₀, by simp, Region.sub_prefix (by decide)⟩
  obtain zC : Spec.Aes.bytesAt s₉.mem (State.addr (Sc s₀) + BitVec.ofNat 64 2048) 16 = Spec.Cmac.zeros 16 := by
    rw [mem₉, preMem, Proof.Cmac.zero4, Proof.Cmac.bytesAt_frame16 (Proof.Cmac.frame_store4 _ _ _ _ _) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact kC.symm)]
    exact Proof.Cmac.zero4_bytes _ _
  obtain hb : below s₉ = belowR s₀ := by rw [below, sp₉]; rfl
  -- The call.
  refine WP.seq (WP.mono (ctr_call pre) fun s₁₀ h₁₀ => ?_)
  have sv (r : Reg) (hr : r ∈ preserved) (hlr : r ≠ .lr) : s₁₀.gpr r = s₉.gpr r := h₁₀.saved r hr hlr
  obtain r6₁₀ : s₁₀.gpr .r6 = Kb s₀ := by rw [sv .r6 (by simp [preserved]) (by decide), r6₉]
  obtain rdwr₁₀ : s₁₀.rd ++ s₁₀.wr = s₀.rd ++ s₀.wr := by rw [h₁₀.rd, h₁₀.wr, rd₉, wr₉]
  obtain wr₁₀ : s₁₀.wr = s₀.wr := by rw [h₁₀.wr, wr₉]
  obtain L : Spec.Aes.bytesAt s₁₀.mem (State.addr (Kb s₀)) 16 = ciph s₀ (Spec.Cmac.zeros 16) := by
    rw [h₁₀.out, cA, zC, Proof.Cmac.bytesAt_frame f₉ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.sch_scr.sub_left (Region.sub_prefix hRb)
      · exact hp.sch_k.sub_left (Region.sub_prefix hRb)) (by omega_arith)]
  -- After the call.
  rw [subkeysPost_eq]
  refine dbl_wp r6₁₀ (by decide) (by decide) (by omega_arith) (by omega_arith)
    (by rw [rdwr₁₀]; exact cKr 0 16 (by decide)) (by rw [wr₁₀]; exact cK 0 16 (by decide))
    fun s₁₁ g₁₁ m₁₁ rd₁₁ wr₁₁ sp₁₁ => ?_
  obtain r6₁₁ : s₁₁.gpr .r6 = Kb s₀ := by
    rw [g₁₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r6₁₀]
  refine dbl_wp r6₁₁ (by decide) (by decide) (by omega_arith) (by omega_arith)
    (by rw [rd₁₁, wr₁₁, rdwr₁₀]; exact cKr 0 16 (by decide)) (by rw [wr₁₁, wr₁₀]; exact cK 16 16 (by decide))
    fun s₁₂ g₁₂ m₁₂ rd₁₂ wr₁₂ sp₁₂ => ?_
  obtain k₁₂ : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → s₁₂.gpr r = s₁₀.gpr r :=
    fun r h0 h1 h2 h3 h4 h12 => by rw [g₁₂ r h0 h1 h2 h3 h4 h12, g₁₁ r h0 h1 h2 h3 h4 h12]
  obtain r5₁₂ : s₁₂.gpr .r5 = Sc s₀ := by
    rw [k₁₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      sv .r5 (by simp [preserved]) (by decide), r5₉]
  obtain rdwr₁₂ : s₁₂.rd ++ s₁₂.wr = s₀.rd ++ s₀.wr := by rw [rd₁₂, wr₁₂, rd₁₁, wr₁₁, rdwr₁₀]
  obtain inS : ∀ d, d + 4 ≤ 2176 → InRegions (s₁₂.rd ++ s₁₂.wr) (State.addr (Sc s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by
      rw [rdwr₁₂]
      exact rw' (cS d 4 hd) ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  refine Spill.restoreList_ok [(.r4, 2064), (.r6, 2072), (.lr, 2076)] s₁₂ _ (by decide) (fun p hp' => ?_)
    fun s₁₃ ld₁₃ ho₁₃ m₁₃ rd₁₃ wr₁₃ sp₁₃ => ?_
  · have hb : 2064 ≤ p.2 ∧ p.2 + 4 ≤ 2080 ∧ p.1 ≠ .r5 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl <;> decide
    exact ⟨hb.2.2, by omega, by rw [r5₁₂]; omega, by rw [r5₁₂]; exact inS _ (by omega)⟩
  refine wp_ldr (a := State.addr (Sc s₀) + BitVec.ofNat 64 2068) (by decide)
    (by rw [ho₁₃ _ (by decide), r5₁₂]; exact aS (by decide))
    (by rw [rd₁₃, wr₁₃]; exact inS _ (by decide)) fun s₁₄ u₁₄ => WP.block_nil ?_
  -- The slots.
  obtain slotD : ∀ d, 2064 ≤ d → d + 4 ≤ 2080 →
      ∀ r ∈ [⟨State.addr (Sc s₀ + BitVec.ofNat 32 2048), 16⟩, ⟨State.addr (Kb s₀), 16⟩,
        ⟨State.addr (Sc s₀), 2048⟩, below s₉], (⟨State.addr (Sc s₀) + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint r := by
    intro d h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [cA]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    · exact (hp.k_scr.symm.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Region.sub_prefix (by decide))
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · rw [hb]; exact hp.b_scr.symm.sub_left (Offset.sub_base _ (by omega_arith))
  obtain slotK : ∀ d, 2064 ≤ d → d + 4 ≤ 2080 → ∀ e, e ≤ 16 →
      (⟨State.addr (Sc s₀) + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint ⟨State.addr (Kb s₀) + BitVec.ofNat 64 e, 16⟩ :=
    fun d h₁ h₂ e he => (hp.k_scr.symm.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))
  obtain slot : ∀ r d, (r, d) ∈ saved4 → s₁₂.mem.readW (State.addr (Sc s₀) + BitVec.ofNat 64 d) 32 = s₀.gpr r := by
    intro r d hrd
    obtain hd : 2064 ≤ d ∧ d + 4 ≤ 2080 := by
      simp only [saved4, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrd
      omega
    rw [m₁₂, dblMem_frame _ _ _ _ |>.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact slotK d hd.1 hd.2 16 (by decide)) (by decide),
      m₁₁, dblMem_frame _ _ _ _ |>.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact slotK d hd.1 hd.2 0 (by decide)) (by decide),
      h₁₀.frame.readW (Region.contains_self _ _) (slotD d hd.1 hd.2) (by decide), mem₉, preMem,
      Proof.Cmac.zero4, Proof.Cmac.readW_store4_of_sep _ _ _ _
        ((hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by omega_arith))),
      Proof.Cmac.zero4, Proof.Cmac.readW_store4_of_sep _ _ _ _ (Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)),
      saved4_slot _ _ _ hrd]
  refine ⟨⟨fun r hr => ?_, by rw [u₁₄.sp, sp₁₃, sp₁₂, sp₁₁, h₁₀.sp, sp₉]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₁₄.other _ (by decide), ld₁₃ (.r4, 2064) (by simp), r5₁₂, slot .r4 2064 (by decide)]
    · rw [u₁₄.gpr, m₁₃, slot .r5 2068 (by decide)]
    · rw [u₁₄.other _ (by decide), ld₁₃ (.r6, 2072) (by simp), r5₁₂, slot .r6 2072 (by decide)]
    all_goals first
      | rw [u₁₄.other _ (by decide), ld₁₃ (.lr, 2076) (by simp), r5₁₂, slot .lr 2076 (by decide)]
      | rw [u₁₄.other _ (by decide), ho₁₃ _ (by decide),
          k₁₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          sv _ (by simp [preserved]) (by decide),
          keep₉ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  · show Spec.Aes.bytesAt s₁₄.mem (State.addr (Kb s₀)) 32 = _
    obtain b₁₁ : Spec.Aes.bytesAt s₁₁.mem (State.addr (Kb s₀)) 16 =
        Spec.Cmac.dbl 16 (Spec.Aes.bytesAt s₁₀.mem (State.addr (Kb s₀)) 16) := by
      have := dblMem_bytes s₁₀.mem (State.addr (Kb s₀)) 0 0
      rw [add0] at this; rw [m₁₁, this]
    obtain lo : Spec.Aes.bytesAt s₁₂.mem (State.addr (Kb s₀)) 16 = Spec.Aes.bytesAt s₁₁.mem (State.addr (Kb s₀)) 16 := by
      rw [m₁₂]
      exact Proof.Cmac.bytesAt_frame16 (dblMem_frame _ _ _ _) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.disjoint_base _ (by decide) (by omega_arith)).symm
    obtain hi : Spec.Aes.bytesAt s₁₂.mem (State.addr (Kb s₀) + BitVec.ofNat 64 16) 16 =
        Spec.Cmac.dbl 16 (Spec.Aes.bytesAt s₁₁.mem (State.addr (Kb s₀)) 16) := by
      have := dblMem_bytes s₁₁.mem (State.addr (Kb s₀)) 0 16
      rw [add0] at this; rw [m₁₂, this]
    rw [u₁₄.mem, m₁₃, Proof.Cmac.bytesAt_32, lo, hi, b₁₁, L]
    rfl

end VG.Proof.CmacAes.Arm

end

end

/-! ### `CmacAes.Arm.Finalize`, which this module and modules that import it used -/

section

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_finalize`, the last block

The steps that form the last block `Mₙ` (§6.2 step 4) in the counter block,
before the chaining value is XORed in: `Mₙ* ⊕ K1` for a complete block
(`full_wp`), else `Mₙ*` copied a byte at a time onto zeros (`copy_wp`), `0x80`
after it, and the block XORed with `K2` (`partial_wp`).
-/

@[expose] public section

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_subs wp_cmp wp_ldr wp_ldrb wp_strb
  wp_ldrSp saveMem saveList_ok saveMem_frame readW_writeW_save eval_eq eval_ne sub_beq ofNat_beq_zero sub_ofNat)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame)

section
variable (s₀ : State)

/-- The key: the schedule and the subkeys `K1` and `K2` after it. -/
abbrev keyR : Region := ⟨State.addr (W s₀), 272⟩
/-- The last bytes `Mₙ*`. -/
abbrev lastR : Region := ⟨State.addr (Dp s₀), N s₀⟩

/-- The last block `Mₙ` (§6.2 step 4), from the key and the last bytes. -/
abbrev mn : List Byte :=
  Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt s₀.mem (State.addr (W s₀) + BitVec.ofNat 64 240) 16)
    (Spec.Aes.bytesAt s₀.mem (State.addr (W s₀) + BitVec.ofNat 64 256) 16)
    (Spec.Aes.bytesAt s₀.mem (State.addr (Dp s₀)) (N s₀))

/-- The counter block. -/
abbrev Ca : Addr := State.addr (S s₀) + BitVec.ofNat 64 2048

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
  st_args : (stR s₀).Disjoint (argsR s₀)
  scr_args : (scrR s₀).Disjoint (argsR s₀)
  b_key : (belowR s₀).Disjoint (keyR s₀)
  b_last : (belowR s₀).Disjoint (lastR s₀)
  b_st : (belowR s₀).Disjoint (stR s₀)
  b_scr : (belowR s₀).Disjoint (scrR s₀)
  key_fit : (W s₀).toNat + 272 ≤ 2 ^ 32
  st_fit : (St s₀).toNat + 16 ≤ 2 ^ 32
  last_fit : (Dp s₀).toNat + N s₀ ≤ 2 ^ 32
  scr_fit : (S s₀).toNat + 2176 ≤ 2 ^ 32
  sp8 : 8 ≤ s₀.sp.toNat
  sp_fit : s₀.sp.toNat + 8 ≤ 2 ^ 32
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14
  len : N s₀ ≤ 16

theorem FPre.of {s₀ : State} (h : finalizeArm.pre s₀) : FPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v⟩

section
variable {s₀ : State} (hp : FPre s₀)
include hp

theorem FPre.arg1 : stackArgAddr s₀ 1 = stackArgAddr s₀ 0 + BitVec.ofNat 64 4 := by
  have := hp.sp_fit
  simp only [stackArgAddr]
  rw [addr_add (by omega_arith), addr_add (by omega_arith)]
  simp

theorem FPre.arg_in {k : Nat} (hk : k < 2) : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 := by
  refine ⟨argsR s₀, by simp [hp.rd], ?_⟩
  rcases (by omega_arith : k = 0 ∨ k = 1) with rfl | rfl
  · simpa using Offset.contains_base (stackArgAddr s₀ 0) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
  · rw [hp.arg1]; exact Offset.contains_base _ (by decide) (by decide)

theorem FPre.cS {d n : Nat} (h : d + n ≤ 2176) :
    Covers [⟨State.addr (S s₀) + BitVec.ofNat 64 d, n⟩] s₀.wr := by
  rw [hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, d, rfl, h⟩

theorem FPre.cKey {d n : Nat} (h : d + n ≤ 272) :
    Covers [⟨State.addr (W s₀) + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) := by
  rw [hp.rd]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨keyR s₀, by simp, d, rfl, h⟩

theorem FPre.cLast {d n : Nat} (h : d + n ≤ N s₀) :
    Covers [⟨State.addr (Dp s₀) + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) := by
  rw [hp.rd]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨lastR s₀, by simp, d, rfl, h⟩

theorem FPre.ca_key {d n : Nat} (h : d + n ≤ 272) :
    (⟨Ca s₀, 16⟩ : Region).Disjoint ⟨State.addr (W s₀) + BitVec.ofNat 64 d, n⟩ :=
  (hp.key_scr.symm.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ h)

theorem FPre.ca_last : (⟨Ca s₀, 16⟩ : Region).Disjoint (lastR s₀) :=
  hp.last_scr.symm.sub_left (Offset.sub_base _ (by decide))

end

theorem in_of_cov {rs : List Region} {a : Addr} {n : Nat} (h : Covers [⟨a, n⟩] rs) : InRegions rs a n :=
  h _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

/-! ## Saving the registers -/

/-- The registers `finalize` saves, and where. -/
def fsaved : List (Reg × Nat) := [(.r4, 2064), (.r5, 2068), (.lr, 2072)]

/-- The memory after saving them. -/
def fsMem (s₀ : State) : Mem := saveMem s₀.mem (State.addr (S s₀)) s₀.gpr fsaved

theorem finSave_eq : finSave = .ldrSp .r12 4 :: (fsaved.map (fun p => Instr.str p.1 .r12 p.2) ++
    ([.mov .r5 (.reg .r12), .ldrSp .r4 0, .cmp .r4 (.imm 16)] : List Instr)) := rfl

theorem fsMem_frame (s₀ : State) : Frame [scrR s₀] s₀.mem (fsMem s₀) :=
  saveMem_frame _ _ _ (by decide) fsaved (by decide)

theorem fsMem_slot (s₀ : State) {r : Reg} {d : Nat} (h : (r, d) ∈ fsaved) :
    (fsMem s₀).readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
  Spill.saveMem_saved (lo := 2064) (hi := 2076) (State.addr (S s₀)) s₀.gpr s₀.mem fsaved (by decide) (r, d) h

/-- What `finSave` leaves. -/
structure FS (s₀ s : State) : Prop where
  keep : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → s.gpr r = s₀.gpr r
  r4 : s.gpr .r4 = BitVec.ofNat 32 (N s₀)
  r5 : s.gpr .r5 = S s₀
  z : s.z = decide (N s₀ = 16)
  mem : s.mem = fsMem s₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finSave_wp {s₀ : State} (hp : FPre s₀) : WP isa (.block finSave) s₀ (FS s₀) := by
  have hsc := hp.scr_fit
  rw [finSave_eq]
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl (hp.arg_in (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = S s₀ := u₁.gpr
  refine saveList_ok fsaved s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have hb : 2064 ≤ p.2 ∧ p.2 + 4 ≤ 2076 := by
      simp only [fsaved, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl <;> decide
    rw [h12, u₁.wr]
    exact ⟨by omega_arith, by omega_arith, in_of_cov (hp.cS (d := p.2) (n := 4) (by omega_arith))⟩
  obtain hm₂ : s₂.mem = fsMem s₀ := by
    rw [m₂, u₁.mem, h12, fsMem]
    exact saveMem_congr _ _ _ fun p hp' => u₁.other _ (by
      simp only [fsaved, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl <;> decide)
  obtain harg : s₂.mem.readW (stackArgAddr s₀ 0) 32 = stackArg s₀ 0 := by
    rw [hm₂]
    exact (fsMem_frame s₀).readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.scr_args.symm.sub_left UPre.arg_sub) (by decide)
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact hp.arg_in (by decide)) fun s₄ u₄ => ?_
  refine wp_cmp (op2_imm (by decide)) fun s₅ f₅ z₅ => WP.block_nil ?_
  obtain a0 : stackArg s₀ 0 = BitVec.ofNat 32 (N s₀) := by simp [N]
  obtain r4 : s₅.gpr .r4 = BitVec.ofNat 32 (N s₀) := by rw [f₅.gpr, u₄.gpr, u₃.mem, harg, a0]
  refine ⟨fun r h4 h5 h12' => ?_, r4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₅.gpr, u₄.other _ h4, u₃.other _ h5, g₂, u₁.other _ h12']
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, g₂, h12]
  · rw [z₅, show s₄.gpr .r4 = s₅.gpr .r4 from (congrFun f₅.gpr _).symm, r4,
      show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, sub_beq (by have := hp.len; omega_arith) (by decide)]
  · rw [f₅.mem, u₄.mem, u₃.mem, hm₂]
  · rw [f₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  · rw [f₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  · rw [f₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]

/-! ## The last block -/

/-- What the branch on the length leaves: `Mₙ` in the counter block. -/
structure BPost (s₀ s : State) : Prop where
  keep : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → r ≠ .lr → s.gpr r = s₀.gpr r
  r5 : s.gpr .r5 = S s₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨Ca s₀, 16⟩] (fsMem s₀) s.mem
  blk : Spec.Aes.bytesAt s.mem (Ca s₀) 16 = mn s₀

section
variable {s₀ : State} (hp : FPre s₀)
include hp

theorem FPre.key_bytes {d : Nat} (h : d + 16 ≤ 272) :
    Spec.Aes.bytesAt (fsMem s₀) (State.addr (W s₀) + BitVec.ofNat 64 d) 16 =
      Spec.Aes.bytesAt s₀.mem (State.addr (W s₀) + BitVec.ofNat 64 d) 16 :=
  Proof.Cmac.bytesAt_frame16 (fsMem_frame s₀) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.key_scr.sub_left (Offset.sub_base _ h)

theorem FPre.last_bytes : Spec.Aes.bytesAt (fsMem s₀) (State.addr (Dp s₀)) (N s₀) =
    Spec.Aes.bytesAt s₀.mem (State.addr (Dp s₀)) (N s₀) :=
  Proof.Cmac.bytesAt_frame (fsMem_frame s₀) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.last_scr) (by have := hp.len; omega_arith)

end

theorem full_eq : full = xorBlk .r12 .lr .r3 .r0 .r5 0 240 2048 ++ [] := rfl

theorem full_wp {s₀ : State} (hp : FPre s₀) (hL : N s₀ = 16) {s : State} (h : FS s₀ s) :
    WP isa (.block full) s (BPost s₀) := by
  have sf := hp.scr_fit
  have kf := hp.key_fit
  have lf := hp.last_fit
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  obtain r3 : s.gpr .r3 = Dp s₀ := h.keep _ (by decide) (by decide) (by decide)
  obtain r0 : s.gpr .r0 = W s₀ := h.keep _ (by decide) (by decide) (by decide)
  rw [full_eq]
  refine xorBlk_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [r3]; omega_arith) (by rw [r0]; omega_arith) (by rw [h.r5]; omega_arith)
    (by rw [r3, add0, hrw]; exact hp.cLast (d := 0) (n := 16) (by omega_arith) |> fun c => by simpa using c)
    (by rw [r0, hrw]; exact hp.cKey (by decide)) (by rw [h.r5, h.wr]; exact hp.cS (by decide))
    fun s' g' => WP.block_nil ?_
  refine ⟨fun r h3 h4 h5 h12 hlr => by rw [g'.gpr r h12 hlr, h.keep r h4 h5 h12], by rw [g'.gpr _ (by decide)
    (by decide), h.r5], by rw [g'.sp, h.sp], by rw [g'.rd, h.rd], by rw [g'.wr, h.wr], ?_, ?_⟩
  · rw [g'.mem, h.mem, h.r5]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  · rw [g'.mem, h.mem, h.r5, r3, r0, add0, Proof.Cmac.xor4Mem_bytes _
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

theorem copy_wp {s : State} {p c : BitVec 32} {L : Nat} (hL₀ : 0 < L) (hL : L ≤ 16)
    (h3 : s.gpr .r3 = p) (hlr : s.gpr .lr = c) (h4 : s.gpr .r4 = BitVec.ofNat 32 L)
    (fp : p.toNat + L ≤ 2 ^ 32) (fc : c.toNat + 16 ≤ 2 ^ 32)
    (hr : Covers [⟨State.addr p, L⟩] (s.rd ++ s.wr)) (hw : Covers [⟨State.addr c, 16⟩] s.wr)
    (hd : (⟨State.addr p, L⟩ : Region).Disjoint ⟨State.addr c, 16⟩) :
    WP isa copy s fun s' =>
      s'.mem = writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) L) ∧
      s'.gpr .lr = c + BitVec.ofNat 32 L ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block [.ldrb .r12 .r3 0, .strb .r12 .lr 0, .dp .add .r3 .r3 (.imm 1),
      .dp .add .lr .lr (.imm 1), .subs .r4 .r4 (.imm 1)]) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .r3 = p + BitVec.ofNat 32 i ∧
      t.gpr .lr = c + BitVec.ofNat 32 i ∧ t.gpr .r4 = BitVec.ofNat 32 (L - i) ∧
      t.mem = writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) i) ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → r ≠ .lr → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL₀, by rw [h3]; exact (BitVec.add_zero p).symm, by rw [hlr]; exact (BitVec.add_zero c).symm, by rw [h4, Nat.sub_zero],
      by simp [Spec.Aes.bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro n t ⟨i, rfl, hi, x3, xlr, x4, mem, g, sp, rd, wr⟩
  obtain aP : State.addr (p + BitVec.ofNat 32 i) = State.addr p + BitVec.ofNat 64 i := addr_add (by omega_arith)
  obtain aC : State.addr (c + BitVec.ofNat 32 i) = State.addr c + BitVec.ofNat 64 i := addr_add (by omega_arith)
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 i) (by decide) (by rw [x3, BitVec.add_zero, aP])
    (by rw [rd, wr]; exact hr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    fun t₁ u₁ => ?_
  refine wp_strb (a := State.addr c + BitVec.ofNat 64 i) (by decide)
    (by rw [u₁.other _ (by decide), xlr, BitVec.add_zero, aC])
    (by rw [u₁.wr, wr]; exact hw _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    fun t₂ v₂ => ?_
  refine wp_add (op2_imm (by decide)) fun t₃ u₃ => wp_add (op2_imm (by decide)) fun t₄ u₄ =>
    wp_subs (op2_imm (by decide)) fun t₅ u₅ z₅ => WP.block_nil ?_
  obtain hlen : (Spec.Aes.bytesAt s.mem (State.addr p) i).length = i := Proof.Cmac.bytesAt_length _ _ _
  obtain hx : writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) i) (State.addr p + BitVec.ofNat 64 i) =
      s.mem (State.addr p + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem (State.addr c) _ (R := ⟨State.addr c, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) (Region.sub_prefix (by omega_arith) _ hcon)
  obtain hmem : t₅.mem = writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) (i + 1)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, v₂.mem, u₁.gpr, u₁.mem, mem, byte_rt32, hx, Proof.Cmac.bytesAt_succ,
      writeBytes_snoc s.mem _ _ _ (by rw [hlen]; omega_arith), hlen]
  obtain x4' : t₅.gpr .r4 = BitVec.ofNat 32 (L - (i + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x4,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_arith)]; rfl
  obtain ev : isa.eval .ne t₅ = some !decide (L - (i + 1) = 0) := by
    show VG.Arm.eval .ne t₅ = _
    rw [eval_ne, z₅, u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x4,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_arith), Nat.sub_sub,
      ofNat_beq_zero (by omega_arith)]
  obtain gg : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → r ≠ .lr → t₅.gpr r = s.gpr r := fun r h₃ h₄ h₁₂ hl => by
    rw [u₅.other _ h₄, u₄.other _ hl, u₃.other _ h₃, v₂.gpr, u₁.other _ h₁₂, g r h₃ h₄ h₁₂ hl]
  obtain xlr' : t₅.gpr .lr = c + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), xlr,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  obtain x3' : t₅.gpr .r3 = p + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, v₂.gpr, u₁.other _ (by decide), x3,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  obtain sp' : t₅.sp = s.sp := by rw [u₅.sp, u₄.sp, u₃.sp, v₂.sp, u₁.sp, sp]
  obtain rd' : t₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, v₂.rd, u₁.rd, rd]
  obtain wr' : t₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, v₂.wr, u₁.wr, wr]
  by_cases he : i + 1 = L
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [xlr', he], gg, sp', rd', wr'⟩
  · right
    exact ⟨by rw [ev]; simp; omega_arith, L - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, x3', xlr', x4', hmem, gg,
      sp', rd', wr'⟩

/-! ## A partial last block -/

theorem zero_eq : zero = .mov .r12 (.imm 0) :: (zeroBlk .r12 .r5 2048 ++
    ([.dp .add .lr .r5 (.imm (BitVec.ofNat 32 2048)), .cmp .r4 (.imm 0)] : List Instr)) := rfl

theorem padK2_eq : padK2 = .mov .r12 (.imm 0x80) :: .strb .r12 .lr 0 ::
    (xorBlk .r12 .lr .r5 .r0 .r5 2048 256 2048 ++ []) := rfl

theorem b80 : ((0x80 : BitVec 32).setWidth 8 : Byte) = 0x80 := by decide

theorem partial_wp {s₀ : State} (hp : FPre s₀) (hL : N s₀ < 16) {s : State} (h : FS s₀ s) :
    WP isa partialBlock s (BPost s₀) := by
  have sf := hp.scr_fit
  have kf := hp.key_fit
  have lf := hp.last_fit
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  obtain cA : State.addr (S s₀ + BitVec.ofNat 32 2048) = Ca s₀ := addr_add (by omega_arith)
  -- Zero the counter block.
  refine WP.seq ?_
  rw [zero_eq]
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  refine Proof.CmacAes.Arm.zeroBlk_ok u₁.gpr (by decide) (by rw [u₁.other _ (by decide), h.r5]; omega_arith)
    (by rw [u₁.other _ (by decide), h.r5, u₁.wr, h.wr]; exact hp.cS (by decide)) fun s₂ G₂ m₂ rd₂ wr₂ sp₂ => ?_
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_cmp (op2_imm (by decide)) fun s₄ f₄ z₄ => WP.block_nil ?_
  obtain r5₂ : s₂.gpr .r5 = S s₀ := by rw [G₂, u₁.other _ (by decide), h.r5]
  obtain mem₄ : s₄.mem = Proof.Cmac.zero4 (fsMem s₀) (Ca s₀) := by
    rw [f₄.mem, u₃.mem, m₂, u₁.other _ (by decide), h.r5, u₁.mem, h.mem]
  obtain k₄ : ∀ r, r ≠ .r12 → r ≠ .lr → s₄.gpr r = s.gpr r := fun r h12 hlr => by
    rw [f₄.gpr, u₃.other _ hlr, G₂, u₁.other _ h12]
  obtain lr₄ : s₄.gpr .lr = S s₀ + BitVec.ofNat 32 2048 := by rw [f₄.gpr, u₃.gpr, r5₂]
  obtain r4₄ : s₄.gpr .r4 = BitVec.ofNat 32 (N s₀) := by
    rw [k₄ _ (by decide) (by decide), h.r4]
  obtain sp₄ : s₄.sp = s.sp := by rw [f₄.sp, u₃.sp, sp₂, u₁.sp]
  obtain rd₄ : s₄.rd = s.rd := by rw [f₄.rd, u₃.rd, rd₂, u₁.rd]
  obtain wr₄ : s₄.wr = s.wr := by rw [f₄.wr, u₃.wr, wr₂, u₁.wr]
  obtain ev : isa.eval .eq s₄ = some (decide (N s₀ = 0)) := by
    show VG.Arm.eval .eq s₄ = _
    rw [eval_eq, z₄, show s₃.gpr .r4 = s₄.gpr .r4 from (congrFun f₄.gpr _).symm, r4₄,
      MdStream.Arm.cmp0 (by omega_arith)]
  obtain fz : Frame [⟨Ca s₀, 16⟩] (fsMem s₀) (Proof.Cmac.zero4 (fsMem s₀) (Ca s₀)) :=
    Proof.Cmac.frame_store4 _ _ _ _ _
  obtain lastZ : Spec.Aes.bytesAt (Proof.Cmac.zero4 (fsMem s₀) (Ca s₀)) (State.addr (Dp s₀)) (N s₀) =
      Spec.Aes.bytesAt s₀.mem (State.addr (Dp s₀)) (N s₀) := by
    rw [Proof.Cmac.bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.ca_last.symm) (by omega_arith), hp.last_bytes]
  obtain keyZ : Spec.Aes.bytesAt (Proof.Cmac.zero4 (fsMem s₀) (Ca s₀)) (State.addr (W s₀) + BitVec.ofNat 64 256) 16 =
      Spec.Aes.bytesAt s₀.mem (State.addr (W s₀) + BitVec.ofNat 64 256) 16 := by
    rw [Proof.Cmac.bytesAt_frame16 fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hp.ca_key (by decide)).symm), hp.key_bytes (by decide)]
  -- Copy the last bytes.
  refine WP.seq (WP.mono (Q := fun (s₅ : State) =>
      s₅.mem = writeBytes (Proof.Cmac.zero4 (fsMem s₀) (Ca s₀)) (Ca s₀)
        (Spec.Aes.bytesAt s₀.mem (State.addr (Dp s₀)) (N s₀)) ∧
      s₅.gpr .lr = S s₀ + BitVec.ofNat 32 (2048 + N s₀) ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → r ≠ .lr → s₅.gpr r = s.gpr r) ∧
      s₅.sp = s.sp ∧ s₅.rd = s.rd ∧ s₅.wr = s.wr) ?_ fun s₅ h₅ => ?_)
  · by_cases hL0 : N s₀ = 0
    · refine WP.ite true (by rw [ev]; simp [hL0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      refine ⟨by rw [mem₄, hL0]; simp [Spec.Aes.bytesAt, writeBytes_nil], by rw [lr₄, hL0], fun r h₃ h₄ h₁₂ hl =>
        k₄ r h₁₂ hl, sp₄, rd₄, wr₄⟩
    · refine WP.ite false (by rw [ev]; simp [hL0]) (fun h => by cases h) fun _ => ?_
      refine WP.mono (copy_wp (p := Dp s₀) (c := S s₀ + BitVec.ofNat 32 2048) (L := N s₀) (by omega_arith) (by omega_arith)
        (by rw [k₄ _ (by decide) (by decide), h.keep _ (by decide) (by decide) (by decide)]) lr₄ r4₄ lf
        (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
          Nat.mod_eq_of_lt (by omega_arith)]; omega_arith)
        (by rw [rd₄, wr₄, hrw]; simpa using hp.cLast (d := 0) (n := N s₀) (by omega_arith))
        (by rw [cA, wr₄, h.wr]; exact hp.cS (by decide)) (by rw [cA]; exact hp.ca_last.symm)) ?_
      rintro s₅ ⟨m₅, lr₅, g₅, sp₅, rd₅, wr₅⟩
      refine ⟨by rw [m₅, mem₄, cA, lastZ], by rw [lr₅, Offset.add_add], fun r h₃ h₄ h₁₂ hl => by
        rw [g₅ r h₃ h₄ h₁₂ hl, k₄ r h₁₂ hl], by rw [sp₅, sp₄], by rw [rd₅, rd₄], by rw [wr₅, wr₄]⟩
  · obtain ⟨m₅, lr₅, g₅, sp₅, rd₅, wr₅⟩ := h₅
    rw [padK2_eq]
    obtain aL : State.addr (S s₀ + BitVec.ofNat 32 (2048 + N s₀)) = Ca s₀ + BitVec.ofNat 64 (N s₀) := by
      rw [addr_add (by omega_arith), Offset.add_add]
    refine wp_mov (op2_imm (by decide)) fun s₆ u₆ => ?_
    refine wp_strb (a := Ca s₀ + BitVec.ofNat 64 (N s₀)) (by decide)
      (by rw [u₆.other _ (by decide), lr₅, BitVec.add_zero, aL])
      (by
        rw [u₆.wr, wr₅, h.wr]
        show InRegions s₀.wr (State.addr (S s₀) + BitVec.ofNat 64 2048 + BitVec.ofNat 64 (N s₀)) 1
        rw [Offset.add_add]
        exact in_of_cov (hp.cS (d := 2048 + N s₀) (n := 1) (by omega_arith))) fun s₇ v₇ => ?_
    obtain g₇ : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → r ≠ .lr → s₇.gpr r = s.gpr r := fun r h₃ h₄ h₁₂ hl => by
      rw [v₇.gpr, u₆.other _ h₁₂, g₅ r h₃ h₄ h₁₂ hl]
    obtain r5₇ : s₇.gpr .r5 = S s₀ := by
      rw [g₇ _ (by decide) (by decide) (by decide) (by decide), h.r5]
    obtain r0₇ : s₇.gpr .r0 = W s₀ := by
      rw [g₇ _ (by decide) (by decide) (by decide) (by decide), h.keep _ (by decide) (by decide) (by decide)]
    obtain hlen : (Spec.Aes.bytesAt s₀.mem (State.addr (Dp s₀)) (N s₀)).length = N s₀ :=
      Proof.Cmac.bytesAt_length _ _ _
    obtain m₇ : s₇.mem = (writeBytes (Proof.Cmac.zero4 (fsMem s₀) (Ca s₀)) (Ca s₀)
        (Spec.Aes.bytesAt s₀.mem (State.addr (Dp s₀)) (N s₀))).writeW (Ca s₀ + BitVec.ofNat 64 (N s₀))
        (0x80 : Byte) := by
      rw [v₇.mem, u₆.gpr, u₆.mem, m₅, b80]
    refine xorBlk_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by rw [r5₇]; omega_arith) (by rw [r0₇]; omega_arith) (by rw [r5₇]; omega_arith)
      (by rw [r5₇, v₇.rd, v₇.wr, u₆.rd, u₆.wr, rd₅, wr₅, hrw]
          exact fun a n hi => (hp.cS (d := 2048) (n := 16) (by decide)) a n hi |>
            fun ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩)
      (by rw [r0₇, v₇.rd, v₇.wr, u₆.rd, u₆.wr, rd₅, wr₅, hrw]; exact hp.cKey (by decide))
      (by rw [r5₇, v₇.wr, u₆.wr, wr₅, h.wr]; exact hp.cS (by decide)) fun s₈ g₈ => WP.block_nil ?_
    obtain fW : Frame [⟨Ca s₀, 16⟩] (fsMem s₀) s₇.mem := by
      rw [m₇]
      refine (fz.trans (writeBytes_frame _ _ _ ?_)).trans
        ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith)))
      rw [hlen]; simpa using Offset.contains_base (Ca s₀) (d := 0) (n := N s₀) (k := 16) (by omega_arith) (by decide)
    obtain pad : Spec.Aes.bytesAt s₇.mem (Ca s₀) 16 =
        Spec.Aes.bytesAt s₀.mem (State.addr (Dp s₀)) (N s₀) ++ [0x80] ++ Spec.Cmac.zeros (16 - N s₀ - 1) := by
      have := Proof.Cmac.padded_bytes (Proof.Cmac.zero4 (fsMem s₀) (Ca s₀)) (Ca s₀)
        (Spec.Aes.bytesAt s₀.mem (State.addr (Dp s₀)) (N s₀)) (by rw [hlen]; exact hL)
        (Proof.Cmac.zero4_bytes _ _)
      rw [hlen] at this
      rw [m₇]; exact this
    obtain k2 : Spec.Aes.bytesAt s₇.mem (State.addr (W s₀) + BitVec.ofNat 64 256) 16 =
        Spec.Aes.bytesAt s₀.mem (State.addr (W s₀) + BitVec.ofNat 64 256) 16 := by
      rw [Proof.Cmac.bytesAt_frame16 fW (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hp.ca_key (by decide)).symm), hp.key_bytes (by decide)]
    refine ⟨fun r h₃ h₄ h₅ h₁₂ hl => by rw [g₈.gpr r h₁₂ hl, g₇ r h₃ h₄ h₁₂ hl, h.keep r h₄ h₅ h₁₂],
      by rw [g₈.gpr _ (by decide) (by decide), r5₇], by rw [g₈.sp, v₇.sp, u₆.sp, sp₅, h.sp],
      by rw [g₈.rd, v₇.rd, u₆.rd, rd₅, h.rd], by rw [g₈.wr, v₇.wr, u₆.wr, wr₅, h.wr], ?_, ?_⟩
    · rw [g₈.mem, r5₇]; exact fW.trans (Proof.Cmac.xor4Mem_frame _ _ _ _)
    · rw [g₈.mem, r5₇, r0₇, Proof.Cmac.xor4Mem_bytes _ (Proof.Cmac.Sep4.self _)
        (Proof.Cmac.Sep4.of_disjoint (hp.ca_key (by decide))), pad, k2]
      simp only [mn, Spec.Cmac.lastBlock, hlen, show N s₀ ≠ 16 by omega_arith, ite_false]
      exact Proof.Cmac.xor_comm _ _

end VG.Proof.CmacAes.Arm

end

end

/-! ### `CmacAes.Arm.UpdateCT`, which this module and modules that import it used -/

section

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_update` is constant time

The taint analysis does not analyse frames, so two runs from states that agree
on the public arguments are related piece by piece (`RelCT`): the taint
analysis covers the code between the calls, from the public arguments for the
prologue and from the registers the correctness proof pins to them (`LInv`)
afterwards, and the call that bitslices the round keys and each call of
`vg_aes_encrypt_blocks_keyed`, in its frame, are constant time by their own
proofs (`Proof.Aes.Arm.keysCall_rel`, `kblk_rel`), both runs having the
round keys in the working space (`KInv`).
-/

@[expose] public section

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (eval_eq eval_ne)
open VG.Impl.Aes.Arm (keyedFrame keysCall)
open VG.Proof.Aes (KeysIn)
open VG.Proof.Aes.Arm (schedAt kblk_call kblk_rel)
open VG.Proof.AesOcb.Arm (BlkCall)

/-- The registers holding our variables in the loop. -/
abbrev vars : List Reg := [.r4, .r5, .r6, .r7, .r8, .r10]

section
variable {s₀ s₀' : State} (hq : updateArm.pub s₀ s₀')
include hq

theorem pub_sp : s₀.sp = s₀'.sp := hq.1
theorem pub_W : W s₀ = W s₀' := hq.2.1
theorem pub_r1 : s₀.gpr .r1 = s₀'.gpr .r1 := hq.2.2.1
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_r1 hq]
theorem pub_St : St s₀ = St s₀' := hq.2.2.2.1
theorem pub_Dp : Dp s₀ = Dp s₀' := hq.2.2.2.2.1
theorem pub_N : N s₀ = N s₀' := by rw [N, N, hq.2.2.2.2.2.1]
theorem pub_S : S s₀ = S s₀' := hq.2.2.2.2.2.2

/-- The registers the invariant pins agree in both runs. -/
theorem LInv.agree {k : Nat} {s₁ s₂ : State} (h₁ : LInv s₀ k s₁) (h₂ : LInv s₀' k s₂) :
    ∀ r ∈ vars, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.r4, h₂.r4, pub_W hq]
  · rw [h₁.r5, h₂.r5, pub_r1 hq]
  · rw [h₁.r6, h₂.r6, pub_St hq]
  · rw [h₁.r7, h₂.r7, pub_Dp hq]
  · rw [h₁.r8, h₂.r8, pub_N hq]
  · rw [h₁.r10, h₂.r10, pub_S hq]

end

/-! ## One block -/

/-- What is known between the code before the call and the call. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  pre : BlkCall s (W s₀) (St s₀) (S s₀) (R s₀) 1
  r7 : s.gpr .r7 = Dp s₀ + BitVec.ofNat 32 (16 * k)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (N s₀ - k)
  sp : s.sp = s₀.sp
  keys : KeysIn s.mem (S s₀) (R s₀) (schedAt s.mem (W s₀) (R s₀))

theorem bodyMid_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : KInv s₀ k s) :
    WP isa (.block (chainIn ++ updArgs)) s (Mid s₀ k) :=
  WP.mono (bodyA_wp hp hk h.1) fun _ hb =>
    ⟨hb.pre, by rw [hb.keep .r7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.1.r7],
      by rw [hb.keep .r8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.1.r8],
      by rw [hb.sp, h.1.sp], (hb.keys hp h.1 h.2).2⟩

/-- What is known after the call. -/
structure After (s₀ : State) (k : Nat) (s : State) : Prop where
  r7 : s.gpr .r7 = Dp s₀ + BitVec.ofNat 32 (16 * k)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (N s₀ - k)

theorem call_after {s₀ : State} {k : Nat} {s : State} (h : Mid s₀ k s) :
    WP isa keyedFrame s (After s₀ k) :=
  WP.mono (kblk_call h.pre h.keys) fun _ hc =>
    ⟨by rw [hc.1.saved .r7 (by simp [preserved]) (by decide), h.r7],
      by rw [hc.1.saved .r8 (by simp [preserved]) (by decide), h.r8]⟩

/-- The relation before a block, in two runs. -/
def BRel (s₀ s₀' : State) (k : Nat) (s₁ s₂ : State) : Prop :=
  (k < N s₀ ∧ KInv s₀ k s₁) ∧ (k < N s₀' ∧ KInv s₀' k s₂)

theorem body_ct {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : updateArm.pub s₀ s₀') (k : Nat) :
    RelCT isa (BRel s₀ s₀' k) body fun _ _ => True := by
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r7, .r8]) (.block advance) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := rel_agree (F := fun s => k < N s₀ ∧ KInv s₀ k s) (F' := fun s => k < N s₀' ∧ KInv s₀' k s)
    (G := Mid s₀ k) (G' := Mid s₀' k) (Taint.ofRegs vars)
    (fun _ _ h h' => Taint.agree_ofRegs (LInv.agree hq h.2.1 h'.2.1)) ⟨_, by taint_decide⟩
    (fun _ h => bodyMid_wp hp h.1 h.2) (fun _ h => bodyMid_wp hp' h.1 h.2)
  have c := rel_wp (F := Mid s₀ k) (F' := Mid s₀' k) (G := After s₀ k) (G' := After s₀' k)
    (kblk_rel fun s₁ s₂ h => ⟨W s₀, St s₀, S s₀, R s₀, 1, h.1.pre,
      by rw [pub_W hq, pub_St hq, pub_S hq, pub_R hq]; exact h.2.pre,
      by rw [h.1.sp, h.2.sp, pub_sp hq], h.1.keys,
      by rw [pub_W hq, pub_S hq, pub_R hq]; exact h.2.keys⟩)
    (fun _ h => call_after h) (fun _ h => call_after h)
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => After s₀ k s₁ ∧ After s₀' k s₂) (Taint.ofRegs [.r7, .r8])
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.r7, h.2.r7, pub_Dp hq]
      · rw [h.1.r8, h.2.r8, pub_N hq]) hB
  exact a.seq (c.seq b)

/-! ## The loop -/

/-- The loop's relation, with the number of iterations left. -/
def LRel (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ BRel s₀ s₀' k s₁ s₂

theorem loop_ct {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : updateArm.pub s₀ s₀') (n : Nat) :
    RelCT isa (LRel s₀ s₀' n) (.loop body .ne) fun s₁ s₂ => KInv s₀ (N s₀) s₁ ∧ KInv s₀' (N s₀') s₂ := by
  refine RelCT.loop (M := isa) (LRel s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : LRel s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  have ct := (body_ct hp hp' hq k).wp
    (F₁ := fun (s : State) => (KInv s₀ (k + 1) s ∧ s.z = decide (N s₀ - (k + 1) = 0)) ∧ k < N s₀)
    (F₂ := fun (s : State) => KInv s₀' (k + 1) s ∧ s.z = decide (N s₀' - (k + 1) = 0))
    fun _ _ h => ⟨WP.mono (body_ok hp h.1.1 h.1.2) fun _ r => ⟨r, h.1.1⟩, body_ok hp' h.2.1 h.2.2⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, ⟨⟨l₁, z₁⟩, hk⟩, ⟨l₂, z₂⟩⟩ => ?_
  have e₁ : isa.eval .ne s₁ = some !decide (N s₀ - (k + 1) = 0) := by
    show VG.Arm.eval .ne s₁ = _; rw [eval_ne, z₁]
  have e₂ : isa.eval .ne s₂ = some !decide (N s₀ - (k + 1) = 0) := by
    show VG.Arm.eval .ne s₂ = _; rw [eval_ne, z₂, ← hN]
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : N s₀ = k + 1 := by
      have : N s₀ - (k + 1) = 0 := by simpa using hf
      omega_using [hk, this]
    exact ⟨h0 ▸ l₁, by rw [← hN, h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : N s₀ - (k + 1) ≠ 0 := by simpa using ht
    exact ⟨N s₀ - (k + 1), by omega_using [hk], k + 1, rfl, ⟨by omega_using [h0], l₁⟩, ⟨by omega_using [hN, h0], l₂⟩⟩

/-! ## The whole function -/

theorem update_rel {s₀ s₀' : State} (h0 : updateArm.pre s₀) (h0' : updateArm.pre s₀')
    (hq : updateArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') update fun _ _ => True := by
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  obtain ⟨_, hpro⟩ : ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] 8) (.block (save ++ setup)) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hepi⟩ : ∃ h, (taint.check (Taint.ofRegs [.r10]) (.block restore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hnil⟩ : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have hN := pub_N hq
  have hsp := pub_sp hq
  have wfA : ∀ {s : State}, UPre s →
      s.sp.toNat + 8 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 8⟩ r := fun {s} h => by
    have e : (⟨State.addr s.sp, 8⟩ : Region) = argsR s := by simp [stackArgAddr]
    refine ⟨h.sp_fit, ?_⟩
    rw [e, h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact h.st_args.symm
    · exact h.scr_args.symm
  have pro := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀')
    (G := fun s => LInv s₀ 0 s ∧ s.z = decide (N s₀ = 0)) (G' := fun s => LInv s₀' 0 s ∧ s.z = decide (N s₀' = 0))
    (argTaint [.r0, .r1, .r2, .r3] 8)
    (fun s s' e e' => by
      subst e e'
      refine agree_argTaint (fun r hr => ?_) hsp (wfA hp) (wfA hp')
        (argMem_of (j := 2) hsp hp.sp_fit fun i hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hq.2.1
        · exact hq.2.2.1
        · exact hq.2.2.2.1
        · exact hq.2.2.2.2.1
      · rcases (by omega_using [hi] : i = 0 ∨ i = 1) with rfl | rfl
        · exact hq.2.2.2.2.2.1
        · exact hq.2.2.2.2.2.2) ⟨_, hpro⟩
    (fun s e => by rw [e]; exact prologue_wp hp) (fun s e => by rw [e]; exact prologue_wp hp')
  have ev {s : State} (h : s.z = decide (N s₀ = 0)) : isa.eval .eq s = some (decide (N s₀ = 0)) := by
    show VG.Arm.eval .eq s = _; rw [eval_eq, h]
  have ev' {s : State} (h : s.z = decide (N s₀' = 0)) : isa.eval .eq s = some (decide (N s₀ = 0)) := by
    show VG.Arm.eval .eq s = _; rw [eval_eq, h, hN]
  have nil := RelCT.taint (A := taint)
    (P := fun a b => ((LInv s₀ 0 a ∧ a.z = decide (N s₀ = 0)) ∧ (LInv s₀' 0 b ∧ b.z = decide (N s₀' = 0))) ∧
      isa.eval .eq a = some true) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr)
    hnil
  have mid : RelCT isa (fun a b => (LInv s₀ 0 a ∧ a.z = decide (N s₀ = 0)) ∧ (LInv s₀' 0 b ∧ b.z = decide (N s₀' = 0)))
      (.ite .eq (.block []) (.seq keysCall (.loop body .ne)))
      (fun a b => LInv s₀ (N s₀) a ∧ LInv s₀' (N s₀') b) := by
    refine RelCT.ite (fun a b h => by rw [ev h.1.2, ev' h.2.2]) ?_ ?_
    · refine (nil.wp (F₁ := LInv s₀ (N s₀)) (F₂ := LInv s₀' (N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N s₀ = 0 := by
        have := h.2; rw [ev h.1.1.2] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2.1)⟩
    · have keys := rel_wp (F := fun a => (LInv s₀ 0 a ∧ a.z = decide (N s₀ = 0)) ∧ N s₀ ≠ 0)
        (F' := fun b => LInv s₀' 0 b) (G := fun a => KInv s₀ 0 a ∧ N s₀ ≠ 0) (G' := KInv s₀' 0)
        (Proof.Aes.Arm.keysCall_rel fun _ _ h => ⟨W s₀, S s₀, R s₀, h.1.1.1.keysArgs hp,
          by rw [pub_W hq, pub_S hq, pub_R hq]; exact h.2.keysArgs hp'⟩)
        (fun _ h => WP.mono (keysCall_wp hp h.1.1) fun _ h' => ⟨h', h.2⟩) (fun _ h => keysCall_wp hp' h)
      refine (keys.seq ((loop_ct hp hp' hq (N s₀ - 0)).mono
        (fun a b h => ⟨0, rfl, ⟨by have := h.1.2; omega, h.1.1⟩, ⟨by have := h.1.2; omega, h.2⟩⟩)
        fun _ _ h => ⟨h.1.1, h.2.1⟩)).mono (fun a b h => ⟨⟨h.1.1, ?_⟩, h.1.2.1⟩) fun _ _ h => h
      have := h.2; rw [ev h.1.1.2] at this
      simpa using this
  have epi := RelCT.taint (A := taint) (P := fun a b => LInv s₀ (N s₀) a ∧ LInv s₀' (N s₀') b)
    (Taint.ofRegs [.r10]) (fun a b h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.r10, h.2.r10, pub_S hq]) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h).seq (mid.seq epi)

theorem update_ct : ConstantTime isa updateArm.pre updateArm.pub update :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (update_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Arm

end

end

@[expose] public section

section

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_subkeys` is constant time

The code before the call and after it is checked by the taint analysis, from
the registers the correctness proof pins (the arguments, then `r5` and `r6`);
the call of `vg_aes_ctr32`, in its frame, is constant time by its own proof
(`ctr_rel`).
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm

/-- What is known after the call. -/
structure SPost (s₀ : State) (s : State) : Prop where
  r5 : s.gpr .r5 = Sc s₀
  r6 : s.gpr .r6 = Kb s₀

theorem spost_wp {s₀ s : State} (h : SAfter s₀ s) : WP isa (ctrCall .r4 .r5) s (SPost s₀) :=
  WP.mono (ctr_call h.pre) fun _ hc =>
    ⟨by rw [hc.saved .r5 (by simp [preserved]) (by decide), h.r5],
      by rw [hc.saved .r6 (by simp [preserved]) (by decide), h.r6]⟩

theorem subkeys_rel {s₀ s₀' : State} (h0 : subkeysArm.pre s₀) (h0' : subkeysArm.pre s₀')
    (hq : subkeysArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') subkeys fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄⟩ := hq
  obtain hp := SPre.of h0
  obtain hp' := SPre.of h0'
  have eW : W s₀' = W s₀ := q₁.symm
  obtain eR : R s₀' = R s₀ := by rw [R, R, q₂]
  have eK : Kb s₀' = Kb s₀ := q₃.symm
  have eS : Sc s₀' = Sc s₀ := q₄.symm
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.r0, .r1, .r2, .r3]) (.block subkeysPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r5, .r6]) (.block subkeysPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := SAfter s₀) (G' := SAfter s₀')
    (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun s s' e e' => by
      subst e e'
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) ⟨_, hA⟩
    (fun s e => by rw [e]; exact pre_wp hp) (fun s e => by rw [e]; exact pre_wp hp')
  obtain c := rel_wp (F := SAfter s₀) (F' := SAfter s₀') (G := SPost s₀) (G' := SPost s₀')
    (ctr_rel (sp₀ := s₀.sp) fun s₁ s₂ h =>
      ⟨h.1.pre, by have := h.2.pre; rwa [eW, eS, eK, eR] at this, h.1.sp, h.2.sp.trans q₀.symm⟩)
    (fun _ h => spost_wp h) (fun _ h => spost_wp h)
  obtain b := RelCT.taint (A := taint) (P := fun s₁ s₂ => SPost s₀ s₁ ∧ SPost s₀' s₂) (Taint.ofRegs [.r5, .r6])
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.r5, h.2.r5, eS]
      · rw [h.1.r6, h.2.r6, eK]) hB
  exact a.seq (c.seq b)

theorem subkeys_ct : ConstantTime isa subkeysArm.pre subkeysArm.pub subkeys :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (subkeys_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Arm

end

section

section

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_finalize` is correct

Before the call, the counter block holds `Mₙ ⊕ C`, for the last block `Mₙ` of
§6.2 step 4 and the chaining value `C` at `state`, and the state is zeroed;
the call leaves `CIPH_K(C ⊕ Mₙ)` there (`finalize_raw_wp`, whatever the
32 bytes after the key schedule hold, as AES-SIV's key context needs), and
that is the MAC when they are the subkeys of its cipher (`finalize_wp`,
`Cmac.macFull_split`).
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd op2_imm op2_reg wp_mov wp_add wp_ldr eval_eq)

/-! ## Up to the call -/

/-- What the code before the call leaves. -/
structure FMid (s₀ s : State) : Prop where
  pre : CallPre s (W s₀) (S s₀ + BitVec.ofNat 32 2048) (St s₀) (S s₀) (R s₀) .r4 .r5
  blk : Spec.Aes.bytesAt s.mem (Ca s₀) 16 =
    Spec.Cmac.xor (mn s₀) (Spec.Aes.bytesAt s₀.mem (State.addr (St s₀)) 16)
  frame : Frame [⟨Ca s₀, 16⟩, stR s₀] (fsMem s₀) s.mem
  r5 : s.gpr .r5 = S s₀
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .lr → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finArgs_eq : finArgs = xorBlk .r12 .lr .r5 .r2 .r5 2048 0 2048 ++
    (.mov .r12 (.imm 0) :: (zeroBlk .r12 .r2 0 ++
      ([.mov .r3 (.reg .r2), .dp .add .r2 .r5 (.imm (BitVec.ofNat 32 2048)), .mov .r4 (.imm 1)] :
        List Instr))) := rfl

theorem preserved_ne {r : Reg} (hr : r ∈ preserved) : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem finArgs_wp {s₀ : State} (hp : FPre s₀) {s : State} (h : BPost s₀ s) :
    WP isa (.block finArgs) s (FMid s₀) := by
  have sf := hp.scr_fit
  have tf := hp.st_fit
  have hR := hp.rounds
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  obtain r2 : s.gpr .r2 = St s₀ := h.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain cA : State.addr (S s₀ + BitVec.ofNat 32 2048) = Ca s₀ := addr_add (by omega_arith)
  obtain cSt : (⟨Ca s₀, 16⟩ : Region).Disjoint (stR s₀) := hp.st_scr.symm.sub_left (Offset.sub_base _ (by decide))
  obtain wSt : Covers [stR s₀] s₀.wr := by
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
  rw [finArgs_eq]
  refine xorBlk_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [h.r5]; omega_arith) (by rw [r2]; omega_arith) (by rw [h.r5]; omega_arith)
    (by
      rw [h.r5, hrw]
      exact fun a n hi => (hp.cS (d := 2048) (n := 16) (by decide)) a n hi |>
        fun ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩)
    (by
      rw [r2, add0, hrw]
      exact fun a n hi => wSt a n hi |> fun ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [h.r5, h.wr]; exact hp.cS (by decide)) fun s₁ g₁ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  obtain r2₂ : s₂.gpr .r2 = St s₀ := by rw [u₂.other _ (by decide), g₁.gpr _ (by decide) (by decide), r2]
  refine Proof.CmacAes.Arm.zeroBlk_ok u₂.gpr (by decide) (by rw [r2₂]; omega_arith)
    (by rw [r2₂, add0, u₂.wr, g₁.wr, h.wr]; exact wSt) fun s₃ G₃ m₃ rd₃ wr₃ sp₃ => ?_
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => wp_add (op2_imm (by decide)) fun s₅ u₅ =>
    wp_mov (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
  obtain keep : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → r ≠ .lr → s₆.gpr r = s.gpr r :=
    fun r h2 h3 h4 h12 hlr => by
      rw [u₆.other _ h4, u₅.other _ h2, u₄.other _ h3, G₃, u₂.other _ h12, g₁.gpr _ h12 hlr]
  obtain r5₆ : s₆.gpr .r5 = S s₀ := by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r5]
  obtain sp₆ : s₆.sp = s₀.sp := by rw [u₆.sp, u₅.sp, u₄.sp, sp₃, u₂.sp, g₁.sp, h.sp]
  obtain rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, rd₃, u₂.rd, g₁.rd, h.rd]
  obtain wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, wr₃, u₂.wr, g₁.wr, h.wr]
  obtain mem₆ : s₆.mem = Proof.Cmac.zero4 (Proof.Cmac.xor4Mem s.mem (Ca s₀) (Ca s₀) (State.addr (St s₀)))
      (State.addr (St s₀)) := by
    rw [u₆.mem, u₅.mem, u₄.mem, m₃, r2₂, add0, u₂.mem, g₁.mem, h.r5, r2, add0]
  obtain hb : below s₆ = belowR s₀ := by rw [below, sp₆]; rfl
  obtain stS : Spec.Aes.bytesAt s.mem (State.addr (St s₀)) 16 = Spec.Aes.bytesAt s₀.mem (State.addr (St s₀)) 16 :=
    Proof.Cmac.bytesAt_frame16 ((fsMem_frame s₀).trans (h.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩)) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.st_scr
  refine ⟨?_, ?_, ?_, r5₆, fun r hr h4 h5 hlr => ?_, sp₆, rd₆, wr₆⟩
  · exact
    { r0 := by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide),
          h.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)]
      r1 := by
        rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide),
          h.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [R]
      r2 := by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), G₃, u₂.other _ (by decide),
          g₁.gpr _ (by decide) (by decide), h.r5]
      r3 := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, G₃, r2₂]
      hra := u₆.gpr
      hrb := r5₆
      regs := by decide
      rounds := hR
      hsp := by rw [sp₆]; exact hp.sp8
      wc := by rw [cA]; exact (hp.ca_key (d := 0) (n := 240) (by decide)).symm |> fun d => by simpa using d
      wd := hp.key_st.sub_left (Region.sub_prefix (by decide))
      ws := (hp.key_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      cd := by rw [cA]; exact cSt
      cs := by rw [cA]; exact Offset.disjoint_base _ (by decide) (by omega_arith)
      ds := hp.st_scr.sub_right (Region.sub_prefix (by decide))
      bw := by rw [hb]; exact hp.b_key.sub_right (Region.sub_prefix (by decide))
      bc := by rw [hb, cA]; exact hp.b_scr.sub_right (Offset.sub_base _ (by decide))
      bd := by rw [hb]; exact hp.b_st
      bs := by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide))
      hW := by have := hp.key_fit; omega_arith
      hC := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
          Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
      hD := tf
      hS := by omega_arith
      reads := by
        rw [rd₆, wr₆, hp.rd]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨keyR s₀, by simp, 0, by simp, by simp⟩
      writes := by
        rw [wr₆, hp.wr, cA]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
        · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
        · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
      zero := by rw [mem₆]; exact Proof.Cmac.zero4_bytes _ _ }
  · rw [mem₆, Proof.Cmac.zero4, Proof.Cmac.bytesAt_frame16 (Proof.Cmac.frame_store4 _ _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cSt),
      Proof.Cmac.xor4Mem_bytes _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint cSt), h.blk, stS]
  · rw [mem₆]
    refine ((h.frame.trans (Proof.Cmac.xor4Mem_frame _ _ _ _)).mono (by simp)).trans
      ((Proof.Cmac.frame_store4 _ _ _ _ _).mono (by simp))
  · have hne := preserved_ne hr
    rw [keep r hne.2.2.1 hne.2.2.2.1 h4 hne.2.2.2.2 hlr, h.keep r hne.2.2.2.1 h4 h5 hne.2.2.2.2 hlr]

theorem finPre_wp {s₀ : State} (hp : FPre s₀) : WP isa finPre s₀ (FMid s₀) := by
  refine WP.seq (WP.mono (finSave_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := BPost s₀) ?_ fun _ h => finArgs_wp hp h)
  obtain ev : isa.eval .eq s₁ = some (decide (N s₀ = 16)) := by
    show VG.Arm.eval .eq s₁ = _; rw [eval_eq, h₁.z]
  by_cases hL : N s₀ = 16
  · exact WP.ite true (by rw [ev]; simp [hL]) (fun _ => full_wp hp hL h₁) (fun h => by cases h)
  · exact WP.ite false (by rw [ev]; simp [hL]) (fun h => by cases h)
      (fun _ => partial_wp hp (by have := hp.len; omega_arith) h₁)

/-! ## The whole function -/

/-- What `vg_cmac_aes_finalize` leaves in the state, from the subkeys after
the key schedule, whatever they are. -/
def finalizeRaw (s₀ s' : State) : Prop :=
  Spec.Aes.bytesAt s'.mem (State.addr (St s₀)) 16 =
    ciph s₀ (Spec.Cmac.xor (mn s₀) (Spec.Aes.bytesAt s₀.mem (State.addr (St s₀)) 16))

/-- `finalizeArm` with `finalizeRaw` as its postcondition. -/
def finalizeRawArm : Contract isa := { finalizeArm with post := finalizeRaw }

theorem finalize_raw_wp {s₀ : State} (h0 : finalizeArm.pre s₀) :
    WP isa finalize s₀ fun s' => abiPreserved s₀ s' ∧ finalizeRaw s₀ s' := by
  obtain hp := FPre.of h0
  have hR := hp.rounds
  obtain hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hR with h | h | h <;> omega_arith
  have sf := hp.scr_fit
  obtain cA : State.addr (S s₀ + BitVec.ofNat 32 2048) = Ca s₀ := addr_add (by omega_arith)
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (ctr_call h₁.pre) fun s₂ h₂ => ?_)
  obtain r5₂ : s₂.gpr .r5 = S s₀ := by rw [h₂.saved .r5 (by simp [preserved]) (by decide), h₁.r5]
  obtain rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]
  obtain inS : ∀ d, d + 4 ≤ 2176 → InRegions (s₂.rd ++ s₂.wr) (State.addr (S s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by
      rw [rdwr₂]
      obtain ⟨r, hr, hc⟩ := in_of_cov (hp.cS (d := d) (n := 4) hd)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [show ([.ldr .r4 .r5 2064, .ldr .lr .r5 2072, .ldr .r5 .r5 2068] : List Instr) =
    [(.r4, 2064), (.lr, 2072)].map (fun (p : Reg × Nat) => Instr.ldr p.1 .r5 p.2) ++ [.ldr .r5 .r5 2068] from rfl]
  refine Spill.restoreList_ok [(.r4, 2064), (.lr, 2072)] s₂ _ (by decide) (fun p hp' => ?_)
    fun s₃ ld₃ ho₃ m₃ rd₃ wr₃ sp₃ => ?_
  · have hb : 2064 ≤ p.2 ∧ p.2 + 4 ≤ 2076 ∧ p.1 ≠ .r5 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl <;> decide
    exact ⟨hb.2.2, by omega, by rw [r5₂]; omega, by rw [r5₂]; exact inS _ (by omega)⟩
  refine wp_ldr (a := State.addr (S s₀) + BitVec.ofNat 64 2068) (by decide)
    (by rw [ho₃ _ (by decide), r5₂]; exact addr_add (by omega_arith))
    (by rw [rd₃, wr₃]; exact inS _ (by decide)) fun s₄ u₄ => WP.block_nil ?_
  -- The slots, which nothing after the save writes.
  obtain slot : ∀ r d, (r, d) ∈ fsaved → s₂.mem.readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 = s₀.gpr r := by
    intro r d hrd
    obtain hd : 2064 ≤ d ∧ d + 4 ≤ 2076 := by
      simp only [fsaved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrd
      omega
    rw [h₂.frame.readW (r := ⟨State.addr (S s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [cA]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
        · exact hp.st_scr.symm.sub_left (Offset.sub_base _ (by omega_arith))
        · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
        · rw [below, h₁.sp]; exact hp.b_scr.symm.sub_left (Offset.sub_base _ (by omega_arith))) (by decide),
      h₁.frame.readW (r := ⟨State.addr (S s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
        · exact hp.st_scr.symm.sub_left (Offset.sub_base _ (by omega_arith))) (by decide),
      fsMem_slot s₀ hrd]
  obtain sch : Spec.Aes.bytesAt s₁.mem (State.addr (W s₀)) (16 * (R s₀ + 1)) =
      Spec.Aes.bytesAt s₀.mem (State.addr (W s₀)) (16 * (R s₀ + 1)) := by
    obtain f : Frame [scrR s₀, stR s₀] s₀.mem s₁.mem :=
      (((fsMem_frame s₀).mono (by simp)).trans (h₁.frame.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
        · exact ⟨stR s₀, by simp, fun _ h => h⟩))
    exact Proof.Cmac.bytesAt_frame f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.key_scr.sub_left (Region.sub_prefix (by omega_arith))
      · exact hp.key_st.sub_left (Region.sub_prefix (by omega_arith))) (by omega_arith)
  refine ⟨⟨fun r hr => ?_, by rw [u₄.sp, sp₃, h₂.sp, h₁.sp]⟩, ?_⟩
  · by_cases h4 : r = .r4
    · subst h4; rw [u₄.other _ (by decide), ld₃ (.r4, 2064) (by simp), r5₂, slot .r4 2064 (by decide)]
    by_cases h5 : r = .r5
    · subst h5; rw [u₄.gpr, m₃, slot .r5 2068 (by decide)]
    by_cases hlr : r = .lr
    · subst hlr; rw [u₄.other _ (by decide), ld₃ (.lr, 2072) (by simp), r5₂, slot .lr 2072 (by decide)]
    rw [u₄.other _ h5, ho₃ _ (by simp [h4, hlr]), h₂.saved r hr hlr, h₁.keep r hr h4 h5 hlr]
  · show Spec.Aes.bytesAt s₄.mem (State.addr (St s₀)) 16 = _
    rw [u₄.mem, m₃, h₂.out, sch, cA, h₁.blk]

theorem finalize_wp {s₀ : State} (h0 : finalizeArm.pre s₀) :
    WP isa finalize s₀ fun s' => abiPreserved s₀ s' ∧ finalizeArm.post s₀ s' := by
  obtain hp := FPre.of h0
  refine WP.mono (finalize_raw_wp h0) fun s' ⟨ab, raw⟩ => ⟨ab, fun hk msg hm hne hst => ?_⟩
  have hk' : Spec.Aes.bytesAt s₀.mem (State.addr (W s₀) + BitVec.ofNat 64 240) 32 =
      (Spec.Cmac.subkeys (ciph s₀) 16).1 ++ (Spec.Cmac.subkeys (ciph s₀) 16).2 := hk
  obtain ⟨e1, e2⟩ := Proof.Cmac.k1k2 (Proof.Cmac.subkeys_aes_length _ _) hk'
  show Spec.Aes.bytesAt s'.mem (State.addr (St s₀)) 16 = _
  rw [raw, mn, e1, e2, hst,
    Proof.Cmac.macFull_split _ hm (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
      (by rw [Proof.Cmac.bytesAt_length]; exact hne), Proof.Cmac.xor_comm]

end VG.Proof.CmacAes.Arm

end

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_finalize` is constant time

The code before the call is checked by the taint analysis, from the public
arguments (its branches and the copy loop depend only on `last_len`), the call
of `vg_aes_ctr32`, in its frame, is constant time by its own proof
(`ctr_rel`), its arguments pinned by the correctness proof (`FMid`), and the
restore after it by the taint analysis again, from `r5` (the scratch buffer).
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm

/-- The restore after the call. -/
abbrev finEnd : List Instr := [.ldr .r4 .r5 2064, .ldr .lr .r5 2072, .ldr .r5 .r5 2068]

theorem finalize_rel {s₀ s₀' : State} (h0 : finalizeArm.pre s₀) (h0' : finalizeArm.pre s₀')
    (hq : finalizeArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') finalize fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, q₅, q₆⟩ := hq
  obtain hp := FPre.of h0
  obtain hp' := FPre.of h0'
  have eW : W s₀' = W s₀ := q₁.symm
  obtain eR : R s₀' = R s₀ := by rw [R, R, q₂]
  have eSt : St s₀' = St s₀ := q₃.symm
  have eS : S s₀' = S s₀ := q₆.symm
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] 8) finPre h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r5]) (.block finEnd) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain wfA : ∀ {s : State}, FPre s →
      s.sp.toNat + 8 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 8⟩ r := fun {s} h => by
    obtain e : (⟨State.addr s.sp, 8⟩ : Region) = argsR s := by simp [stackArgAddr]
    refine ⟨h.sp_fit, ?_⟩
    rw [e, h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact h.st_args.symm
    · exact h.scr_args.symm
  obtain a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := FMid s₀) (G' := FMid s₀')
    (argTaint [.r0, .r1, .r2, .r3] 8)
    (fun s s' e e' => by
      subst e e'
      refine agree_argTaint (fun r hr => ?_) q₀ (wfA hp) (wfA hp')
        (argMem_of (j := 2) q₀ hp.sp_fit fun i hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
      · rcases (by omega_arith : i = 0 ∨ i = 1) with rfl | rfl
        · exact q₅
        · exact q₆) ⟨_, hA⟩
    (fun s e => by rw [e]; exact finPre_wp hp) (fun s e => by rw [e]; exact finPre_wp hp')
  obtain c := rel_wp (F := FMid s₀) (F' := FMid s₀') (G := fun s => s.gpr .r5 = S s₀)
    (G' := fun s => s.gpr .r5 = S s₀')
    (ctr_rel (sp₀ := s₀.sp) fun s₁ s₂ h =>
      ⟨h.1.pre, by have := h.2.pre; rwa [eW, eS, eSt, eR] at this, h.1.sp, h.2.sp.trans q₀.symm⟩)
    (fun _ h => WP.mono (ctr_call h.pre) fun _ hc => by rw [hc.saved .r5 (by simp [preserved]) (by decide), h.r5])
    (fun _ h => WP.mono (ctr_call h.pre) fun _ hc => by rw [hc.saved .r5 (by simp [preserved]) (by decide), h.r5])
  obtain b := RelCT.taint (A := taint) (P := fun s₁ s₂ => s₁.gpr .r5 = S s₀ ∧ s₂.gpr .r5 = S s₀')
    (Taint.ofRegs [.r5]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1, h.2, eS]) hB
  exact a.seq (c.seq b)

theorem finalize_ct : ConstantTime isa finalizeArm.pre finalizeArm.pub finalize :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finalize_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Arm

end
