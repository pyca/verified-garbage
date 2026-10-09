import VerifiedGarbage.Proof.CmacAes.Arm.UpdateCorrect
import VerifiedGarbage.Proof.CmacAes.Arm.Words
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Cmac.Dbl

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
  have g : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → s₂₄.gpr r = s.gpr r :=
    fun r h0 h1 h2 h3 h4 h12 => by
      rw [u₂₄.other _ h3, u₂₃.other _ h2, u₂₂.other _ h1, u₂₁.other _ h0, u₂₀.other _ h3, u₁₉.other _ h3,
        u₁₈.other _ h2, u₁₇.other _ h2, u₁₆.other _ h1, u₁₅.other _ h1, u₁₄.other _ h0, u₁₃.other _ h0,
        u₁₂.other _ h12, u₁₁.other _ h12, u₁₀.other _ h4, u₉.other _ h12, u₈.other _ h3, u₇.other _ h2,
        u₆.other _ h1, u₅.other _ h0, u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, u₁.other _ h0]
  have g6 : s₂₄.gpr .r6 = K := by
    rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h6]
  have m24 : s₂₄.mem = s.mem := by
    rw [u₂₄.mem, u₂₃.mem, u₂₂.mem, u₂₁.mem, u₂₀.mem, u₁₉.mem, u₁₈.mem, u₁₇.mem, u₁₆.mem, u₁₅.mem, u₁₄.mem,
      u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem,
      u₁.mem]
  have rd24 : s₂₄.rd = s.rd := by
    rw [u₂₄.rd, u₂₃.rd, u₂₂.rd, u₂₁.rd, u₂₀.rd, u₁₉.rd, u₁₈.rd, u₁₇.rd, u₁₆.rd, u₁₅.rd, u₁₄.rd, u₁₃.rd,
      u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr24 : s₂₄.wr = s.wr := by
    rw [u₂₄.wr, u₂₃.wr, u₂₂.wr, u₂₁.wr, u₂₀.wr, u₁₉.wr, u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr, u₁₄.wr, u₁₃.wr,
      u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have sp24 : s₂₄.sp = s.sp := by
    rw [u₂₄.sp, u₂₃.sp, u₂₂.sp, u₂₁.sp, u₂₀.sp, u₁₉.sp, u₁₈.sp, u₁₇.sp, u₁₆.sp, u₁₅.sp, u₁₄.sp, u₁₃.sp,
      u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  -- The four words.
  have w₀ : s₁.gpr .r0 = s.mem.readW (State.addr K + BitVec.ofNat 64 src) 32 := u₁.gpr
  have w₁ : s₂.gpr .r1 = s.mem.readW (State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 4) 32 := by
    rw [u₂.gpr, u₁.mem]
  have w₂ : s₃.gpr .r2 = s.mem.readW (State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 8) 32 := by
    rw [u₃.gpr, u₂.mem, u₁.mem]
  have w₃ : s₄.gpr .r3 = s.mem.readW (State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 12) 32 := by
    rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem]
  have b₀ : s₈.gpr .r0 = byteRev32 (s.mem.readW (State.addr K + BitVec.ofNat 64 src) 32) := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), w₀, rev_eq]
  have b₁ : s₈.gpr .r1 = byteRev32 (s.mem.readW (State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 4) 32) := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), w₁, rev_eq]
  have b₂ : s₈.gpr .r2 = byteRev32 (s.mem.readW (State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 8) 32) := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      w₂, rev_eq]
  have b₃ : s₈.gpr .r3 = byteRev32 (s.mem.readW (State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 12) 32) := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), w₃, rev_eq]
  have mask : s₁₂.gpr .r12 = ((0 : BitVec 32) - (s₈.gpr .r0 >>> 31)) &&& 0x87 := by
    rw [u₁₂.gpr, u₁₁.gpr, u₁₀.gpr, u₁₀.other _ (by decide), u₉.gpr]
  have v₀ : s₂₄.gpr .r0 = byteRev32 (Proof.Cmac.dblW0 (s₈.gpr .r0) (s₈.gpr .r1)) := by
    rw [u₂₄.other _ (by decide), u₂₃.other _ (by decide), u₂₂.other _ (by decide), u₂₁.gpr, rev_eq,
      u₂₀.other _ (by decide), u₁₉.other _ (by decide), u₁₈.other _ (by decide), u₁₇.other _ (by decide),
      u₁₆.other _ (by decide), u₁₅.other _ (by decide), u₁₄.gpr, u₁₃.gpr, u₁₃.other _ (by decide),
      u₁₂.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₉.other _ (by decide)]
    rfl
  have v₁ : s₂₄.gpr .r1 = byteRev32 (Proof.Cmac.dblW0 (s₈.gpr .r1) (s₈.gpr .r2)) := by
    rw [u₂₄.other _ (by decide), u₂₃.other _ (by decide), u₂₂.gpr, rev_eq, u₂₁.other _ (by decide),
      u₂₀.other _ (by decide), u₁₉.other _ (by decide), u₁₈.other _ (by decide), u₁₇.other _ (by decide),
      u₁₆.gpr, u₁₅.gpr, u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₄.other _ (by decide),
      u₁₃.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₂.other _ (by decide),
      u₁₁.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₉.other _ (by decide)]
    rfl
  have v₂ : s₂₄.gpr .r2 = byteRev32 (Proof.Cmac.dblW0 (s₈.gpr .r2) (s₈.gpr .r3)) := by
    rw [u₂₄.other _ (by decide), u₂₃.gpr, rev_eq, u₂₂.other _ (by decide), u₂₁.other _ (by decide),
      u₂₀.other _ (by decide), u₁₉.other _ (by decide), u₁₈.gpr, u₁₇.gpr, u₁₇.other _ (by decide),
      u₁₆.other _ (by decide), u₁₆.other _ (by decide), u₁₅.other _ (by decide), u₁₅.other _ (by decide),
      u₁₄.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₃.other _ (by decide),
      u₁₂.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₉.other _ (by decide)]
    rfl
  have v₃ : s₂₄.gpr .r3 = byteRev32 (Proof.Cmac.dblW3 (s₈.gpr .r0) (s₈.gpr .r3)) := by
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
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hR with h | h | h <;> omega_arith
  have cK : ∀ d n, d + n ≤ 32 → Covers [⟨State.addr (Kb s₀) + BitVec.ofNat 64 d, n⟩] s₀.wr := fun d n h => by
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨kR s₀, by simp, d, rfl, h⟩
  have cS : ∀ d n, d + n ≤ 2176 → Covers [⟨State.addr (Sc s₀) + BitVec.ofNat 64 d, n⟩] s₀.wr := fun d n h => by
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR s₀, by simp, d, rfl, h⟩
  have rw' : ∀ {rs a n}, Covers rs s₀.wr → InRegions rs a n → InRegions (s₀.rd ++ s₀.wr) a n :=
    fun h hi => by obtain ⟨r, hr, hc⟩ := h _ _ hi; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have cKr : ∀ d n, d + n ≤ 32 → Covers [⟨State.addr (Kb s₀) + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) :=
    fun d n h a k hi => rw' (cK d n h) hi
  have aS : ∀ {d}, d < 2176 → State.addr (Sc s₀ + BitVec.ofNat 32 d) = State.addr (Sc s₀) + BitVec.ofNat 64 d :=
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
  have r3₄ : s₄.gpr .r3 = Sc s₀ := by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  refine Proof.CmacAes.Arm.zeroBlk_ok u₄.gpr (by decide) (by rw [r3₄]; omega_arith)
    (by rw [r3₄, u₄.wr, u₃.wr, u₂.wr, wr₁]; exact cS 2048 16 (by decide)) fun s₅ G₅ m₅ rd₅ wr₅ sp₅ => ?_
  have r2₅ : s₅.gpr .r2 = Kb s₀ := by
    rw [G₅, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  refine Proof.CmacAes.Arm.zeroBlk_ok (by rw [G₅, u₄.gpr]) (by decide) (by rw [r2₅]; omega_arith)
    (by rw [r2₅, add0, wr₅, u₄.wr, u₃.wr, u₂.wr, wr₁]; simpa using cK 0 16 (by decide))
    fun s₆ G₆ m₆ rd₆ wr₆ sp₆ => ?_
  refine wp_add (op2_imm (by decide)) fun s₇ u₇ => wp_mov (op2_reg _ _) fun s₈ u₈ =>
    wp_mov (op2_imm (by decide)) fun s₉ u₉ => WP.block_nil ?_
  have keep₉ : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r12 → s₉.gpr r = s₀.gpr r :=
    fun r h2 h3 h4 h5 h6 h12 => by
      rw [u₉.other _ h4, u₈.other _ h3, u₇.other _ h2, G₆, G₅, u₄.other _ h12, u₃.other _ h5, u₂.other _ h6, g₁]
  have r5₉ : s₉.gpr .r5 = Sc s₀ := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), G₆, G₅, u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), g₁]
  have r6₉ : s₉.gpr .r6 = Kb s₀ := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), G₆, G₅, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, g₁]
  have sp₉ : s₉.sp = s₀.sp := by rw [u₉.sp, u₈.sp, u₇.sp, sp₆, sp₅, u₄.sp, u₃.sp, u₂.sp, sp₁]
  have rd₉ : s₉.rd = s₀.rd := by rw [u₉.rd, u₈.rd, u₇.rd, rd₆, rd₅, u₄.rd, u₃.rd, u₂.rd, rd₁]
  have wr₉ : s₉.wr = s₀.wr := by rw [u₉.wr, u₈.wr, u₇.wr, wr₆, wr₅, u₄.wr, u₃.wr, u₂.wr, wr₁]
  have mem₉ : s₉.mem = preMem s₀ := by
    rw [u₉.mem, u₈.mem, u₇.mem, m₆, r2₅, add0, m₅, r3₄, u₄.mem, u₃.mem, u₂.mem, m₁]; rfl
  -- The memory before the call.
  have cA : State.addr (Sc s₀ + BitVec.ofNat 32 2048) = State.addr (Sc s₀) + BitVec.ofNat 64 2048 := aS (by decide)
  have kC : (⟨State.addr (Kb s₀), 16⟩ : Region).Disjoint ⟨State.addr (Sc s₀) + BitVec.ofNat 64 2048, 16⟩ :=
    (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
  have hb : below s₉ = belowR s₀ := by rw [below, sp₉]; rfl
  have pre : CallPre s₉ (W s₀) (Sc s₀ + BitVec.ofNat 32 2048) (Kb s₀) (Sc s₀) (R s₀) .r4 .r5 :=
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
  have hp := SPre.of h0
  have kf := hp.k_fit
  have sf := hp.scr_fit
  have sf' : (s₀.gpr .r3).toNat + 2176 ≤ 2 ^ 32 := sf
  have hR := hp.rounds
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hR with h | h | h <;> omega_arith
  have cK : ∀ d n, d + n ≤ 32 → Covers [⟨State.addr (Kb s₀) + BitVec.ofNat 64 d, n⟩] s₀.wr := fun d n h => by
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨kR s₀, by simp, d, rfl, h⟩
  have cS : ∀ d n, d + n ≤ 2176 → Covers [⟨State.addr (Sc s₀) + BitVec.ofNat 64 d, n⟩] s₀.wr := fun d n h => by
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR s₀, by simp, d, rfl, h⟩
  have rw' : ∀ {rs a n}, Covers rs s₀.wr → InRegions rs a n → InRegions (s₀.rd ++ s₀.wr) a n :=
    fun h hi => by obtain ⟨r, hr, hc⟩ := h _ _ hi; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have cKr : ∀ d n, d + n ≤ 32 → Covers [⟨State.addr (Kb s₀) + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) :=
    fun d n h a k hi => rw' (cK d n h) hi
  have aS : ∀ {d}, d < 2176 → State.addr (Sc s₀ + BitVec.ofNat 32 d) = State.addr (Sc s₀) + BitVec.ofNat 64 d :=
    fun _ => addr_add (by omega_arith)
  unfold subkeys
  refine WP.seq (WP.mono (pre_wp hp) fun s₉ a => ?_)
  obtain ⟨pre, keep₉, r5₉, r6₉, sp₉, rd₉, wr₉, mem₉⟩ := a
  -- The memory before the call.
  have cA : State.addr (Sc s₀ + BitVec.ofNat 32 2048) = State.addr (Sc s₀) + BitVec.ofNat 64 2048 := aS (by decide)
  have kC : (⟨State.addr (Kb s₀), 16⟩ : Region).Disjoint ⟨State.addr (Sc s₀) + BitVec.ofNat 64 2048, 16⟩ :=
    (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
  have f₉ : Frame [scR s₀, kR s₀] s₀.mem s₉.mem := by
    rw [mem₉, preMem]
    refine (((saveMem_frame _ _ _ (L := 2176) (by decide) saved4 (by decide)).sub fun r hr => ?_).trans
      ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ?_)).trans
      ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ?_) <;>
    simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨scR s₀, by simp, fun _ h => h⟩
    · exact ⟨scR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨kR s₀, by simp, Region.sub_prefix (by decide)⟩
  have zC : Spec.Aes.bytesAt s₉.mem (State.addr (Sc s₀) + BitVec.ofNat 64 2048) 16 = Spec.Cmac.zeros 16 := by
    rw [mem₉, preMem, Proof.Cmac.zero4, Proof.Cmac.bytesAt_frame16 (Proof.Cmac.frame_store4 _ _ _ _ _) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact kC.symm)]
    exact Proof.Cmac.zero4_bytes _ _
  have hb : below s₉ = belowR s₀ := by rw [below, sp₉]; rfl
  -- The call.
  refine WP.seq (WP.mono (ctr_call pre) fun s₁₀ h₁₀ => ?_)
  have sv (r : Reg) (hr : r ∈ preserved) (hlr : r ≠ .lr) : s₁₀.gpr r = s₉.gpr r := h₁₀.saved r hr hlr
  have r6₁₀ : s₁₀.gpr .r6 = Kb s₀ := by rw [sv .r6 (by simp [preserved]) (by decide), r6₉]
  have rdwr₁₀ : s₁₀.rd ++ s₁₀.wr = s₀.rd ++ s₀.wr := by rw [h₁₀.rd, h₁₀.wr, rd₉, wr₉]
  have wr₁₀ : s₁₀.wr = s₀.wr := by rw [h₁₀.wr, wr₉]
  have L : Spec.Aes.bytesAt s₁₀.mem (State.addr (Kb s₀)) 16 = ciph s₀ (Spec.Cmac.zeros 16) := by
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
  have r6₁₁ : s₁₁.gpr .r6 = Kb s₀ := by
    rw [g₁₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r6₁₀]
  refine dbl_wp r6₁₁ (by decide) (by decide) (by omega_arith) (by omega_arith)
    (by rw [rd₁₁, wr₁₁, rdwr₁₀]; exact cKr 0 16 (by decide)) (by rw [wr₁₁, wr₁₀]; exact cK 16 16 (by decide))
    fun s₁₂ g₁₂ m₁₂ rd₁₂ wr₁₂ sp₁₂ => ?_
  have k₁₂ : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → s₁₂.gpr r = s₁₀.gpr r :=
    fun r h0 h1 h2 h3 h4 h12 => by rw [g₁₂ r h0 h1 h2 h3 h4 h12, g₁₁ r h0 h1 h2 h3 h4 h12]
  have r5₁₂ : s₁₂.gpr .r5 = Sc s₀ := by
    rw [k₁₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      sv .r5 (by simp [preserved]) (by decide), r5₉]
  have rdwr₁₂ : s₁₂.rd ++ s₁₂.wr = s₀.rd ++ s₀.wr := by rw [rd₁₂, wr₁₂, rd₁₁, wr₁₁, rdwr₁₀]
  have inS : ∀ d, d + 4 ≤ 2176 → InRegions (s₁₂.rd ++ s₁₂.wr) (State.addr (Sc s₀) + BitVec.ofNat 64 d) 4 :=
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
  have slotD : ∀ d, 2064 ≤ d → d + 4 ≤ 2080 →
      ∀ r ∈ [⟨State.addr (Sc s₀ + BitVec.ofNat 32 2048), 16⟩, ⟨State.addr (Kb s₀), 16⟩,
        ⟨State.addr (Sc s₀), 2048⟩, below s₉], (⟨State.addr (Sc s₀) + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint r := by
    intro d h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [cA]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    · exact (hp.k_scr.symm.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Region.sub_prefix (by decide))
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · rw [hb]; exact hp.b_scr.symm.sub_left (Offset.sub_base _ (by omega_arith))
  have slotK : ∀ d, 2064 ≤ d → d + 4 ≤ 2080 → ∀ e, e ≤ 16 →
      (⟨State.addr (Sc s₀) + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint ⟨State.addr (Kb s₀) + BitVec.ofNat 64 e, 16⟩ :=
    fun d h₁ h₂ e he => (hp.k_scr.symm.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))
  have slot : ∀ r d, (r, d) ∈ saved4 → s₁₂.mem.readW (State.addr (Sc s₀) + BitVec.ofNat 64 d) 32 = s₀.gpr r := by
    intro r d hrd
    have hd : 2064 ≤ d ∧ d + 4 ≤ 2080 := by
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
    have b₁₁ : Spec.Aes.bytesAt s₁₁.mem (State.addr (Kb s₀)) 16 =
        Spec.Cmac.dbl 16 (Spec.Aes.bytesAt s₁₀.mem (State.addr (Kb s₀)) 16) := by
      have := dblMem_bytes s₁₀.mem (State.addr (Kb s₀)) 0 0
      rw [add0] at this; rw [m₁₁, this]
    have lo : Spec.Aes.bytesAt s₁₂.mem (State.addr (Kb s₀)) 16 = Spec.Aes.bytesAt s₁₁.mem (State.addr (Kb s₀)) 16 := by
      rw [m₁₂]
      exact Proof.Cmac.bytesAt_frame16 (dblMem_frame _ _ _ _) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.disjoint_base _ (by decide) (by omega_arith)).symm
    have hi : Spec.Aes.bytesAt s₁₂.mem (State.addr (Kb s₀) + BitVec.ofNat 64 16) 16 =
        Spec.Cmac.dbl 16 (Spec.Aes.bytesAt s₁₁.mem (State.addr (Kb s₀)) 16) := by
      have := dblMem_bytes s₁₁.mem (State.addr (Kb s₀)) 0 16
      rw [add0] at this; rw [m₁₂, this]
    rw [u₁₄.mem, m₁₃, Proof.Cmac.bytesAt_32, lo, hi, b₁₁, L]
    rfl

end VG.Proof.CmacAes.Arm
