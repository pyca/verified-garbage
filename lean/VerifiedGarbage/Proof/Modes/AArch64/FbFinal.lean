module

public import VerifiedGarbage.Impl.Modes.AArch64.FbFinal
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Modes.AArch64.FbLoop
public import VerifiedGarbage.Proof.Modes.FbFinal
public import VerifiedGarbage.Proof.Modes.AArch64.Fb
import VerifiedGarbage.Proof.Modes.AArch64.Cfb8Steps
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Modes.AArch64.Xor
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Modes.AArch64.Ctr
import VerifiedGarbage.Proof.Modes.AArch64.Words

/-!
# OFB and CFB of a message's last piece on AArch64, for any core

`fbFinal_wp`: `c.fbFinal mo r ivR`, for a core `c` with `BlockSpec c` whose
cipher is the forward cipher `CIPH_K`, its arguments in the registers `r`,
and the IV's address kept in `ivR` (which the core keeps: `KeepsReg`),
replaces the `len` bytes at `D` with the mode's output, byte `i` that of
`fbOut` of its block, under the key `k` that its key arguments give, from
the IV at `P`, and the IV with the block to continue from (`fbNextF`); it
keeps the callee-saved registers `x19`–`x28`, and writes nothing but the
scratch buffer, the data and the IV. As `fb_wp` (`Fb.lean`), and as on
x86-64 (`Proof/Modes/X86_64/FbFinal.lean`); `Proof/Modes/FbFinal.lean`
states these as the specification's.

The partial segment (`xorLoop_wp`, as `Proof/Modes/X86_64/FbFinal.lean`):
from the block at `K` (in `x9`) and the `r > 0` bytes left at `R` (in `Rd`,
their count in `Rl`), the loop of `xorByte` XORs each byte of the block into
the byte at the same offset of `R`, and changes memory only there; it ends
with `Rl` zero.

The loop (`fbSeg_wp`, `fbFinalLoop_wp`, as
`Proof/Modes/X86_64/FbFinal.lean`): one segment enciphers its input block
`Iⱼ` in the buffer (`BlockSpec.crypt_wp`), giving `Oⱼ`; `x8 := leftReg >> lg`
is zero exactly when fewer than `L` bytes are left (`lsr_beq`,
`two_pow_fbLg`). If a whole block of the `len` bytes is left, it makes the
block `fbOut` and the buffer `Iⱼ₊₁` (`fbIn`), as `fb`'s (`fbBlock_wp`); if
`r < L` bytes are left, it XORs the first `r` bytes of `Oⱼ` into them, which
are then those of `fbOut j`, and leaves `Oⱼ` in the buffer. Blocks are
`L = 8 bw` bytes.
-/

@[expose] public section

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Modes (FbMode)
open VG.Impl.Aes.AArch64 (sb movR ldS stS eorR)
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeW8_apply)

/-! ## The partial segment -/

/-- What the loop works on: the block at `K`, the `r` bytes at `R`, the
registers `Rd` and `Rl`. -/
structure XPre (s₀ : State) (K R : Addr) (r : Nat) (Rd Rl : Reg) : Prop where
  small : r < 2 ^ 64
  disj : Region.Disjoint ⟨K, r⟩ ⟨R, r⟩
  rdK : ∀ q < r, InRegions (s₀.rd ++ s₀.wr) (K + BitVec.ofNat 64 q) 1
  wrR : ∀ q < r, InRegions s₀.wr (R + BitVec.ofNat 64 q) 1
  dl : Rd ≠ Rl
  d9 : Rd ≠ .x9 ∧ Rl ≠ .x9
  d6 : Rd ≠ .x6 ∧ Rl ≠ .x6
  d7 : Rd ≠ .x7 ∧ Rl ≠ .x7

/-- The loop, before byte `j`. -/
structure XInv (s₀ : State) (K R : Addr) (r : Nat) (Rd Rl : Reg) (j : Nat) (s : State) : Prop where
  x9 : s.gpr .x9 = K + BitVec.ofNat 64 j
  dat : s.gpr Rd = R + BitVec.ofNat 64 j
  left : s.gpr Rl = BitVec.ofNat 64 (r - j)
  lt : j < r
  data : ∀ q < r, s.mem (R + BitVec.ofNat 64 q) =
    if q < j then s₀.mem (R + BitVec.ofNat 64 q) ^^^ s₀.mem (K + BitVec.ofNat 64 q) else s₀.mem (R + BitVec.ofNat 64 q)
  frame : Frame [⟨R, r⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  gpr : ∀ x, x ≠ .x9 → x ≠ .x6 → x ≠ .x7 → x ≠ Rd → x ≠ Rl → s.gpr x = s₀.gpr x

/-- The loop, done. -/
structure XDone (s₀ : State) (K R : Addr) (r : Nat) (Rd Rl : Reg) (s : State) : Prop where
  left : s.gpr Rl = 0
  data : ∀ q < r, s.mem (R + BitVec.ofNat 64 q) = s₀.mem (R + BitVec.ofNat 64 q) ^^^ s₀.mem (K + BitVec.ofNat 64 q)
  frame : Frame [⟨R, r⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  gpr : ∀ x, x ≠ .x9 → x ≠ .x6 → x ≠ .x7 → x ≠ Rd → x ≠ Rl → s.gpr x = s₀.gpr x

theorem writeByte_frame (m : Mem) (A : Addr) (b : Byte) : Frame [⟨A, 1⟩] m (m.writeW A b) := fun x hx => by
  rw [writeW8_apply, ite_eq_right (fun h => hx _ List.mem_cons_self (by
    subst h; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega))]

/-- One fewer byte left, as a bit vector. -/
theorem ofNat_sub_one {r j : Nat} (hj : j < r) :
    BitVec.ofNat 64 (r - j) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (r - (j + 1)) := by
  rw [show r - j = (r - (j + 1)) + 1 by omega, BitVec.ofNat_add]
  exact BitVec.add_sub_cancel _ 1#64

theorem xorByte_wp {s₀ : State} {K R : Addr} {r : Nat} {Rd Rl : Reg} (hp : XPre s₀ K R r Rd Rl) {j : Nat} {s : State}
    (hi : XInv s₀ K R r Rd Rl j s) :
    WP isa (.block (xorByte Rd Rl)) s fun s' =>
      (isa.eval (.nonzero .x Rl) s' = some false ∧ XDone s₀ K R r Rd Rl s') ∨
      (isa.eval (.nonzero .x Rl) s' = some true ∧ XInv s₀ K R r Rd Rl (j + 1) s') := by
  have hj := hi.lt
  have hr := hp.small
  have p0 : ∀ X : Addr, X + BitVec.ofNat 64 0 = X := fun X => by simp
  have rK : InRegions (s.rd ++ s.wr) (s.gpr .x9 + BitVec.ofNat 64 0) 1 := by
    rw [hi.rd, hi.wr, hi.x9, p0]; exact hp.rdK j hj
  obtain ⟨s₁, e₁, g₁, o₁, m₁, rd₁, wr₁⟩ := ldrb_ok s .x6 .x9 (off := 0) (by decide) rK
  have rR : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr Rd + BitVec.ofNat 64 0) 1 := by
    rw [rd₁, wr₁, hi.rd, hi.wr, o₁ _ hp.d6.1, hi.dat, p0]
    exact inRd (hp.wrR j hj)
  obtain ⟨s₂, e₂, g₂, o₂, m₂, rd₂, wr₂⟩ := ldrb_ok s₁ .x7 Rd (off := 0) (by decide) rR
  obtain ⟨s₃, e₃, g₃, o₃, m₃, rd₃, wr₃⟩ := eor_ok s₂ .x7 .x7 .x6
  have wR : InRegions s₃.wr (s₃.gpr Rd + BitVec.ofNat 64 0) 1 := by
    rw [wr₃, wr₂, wr₁, hi.wr, o₃ _ hp.d7.1, o₂ _ hp.d7.1, o₁ _ hp.d6.1, hi.dat, p0]
    exact hp.wrR j hj
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := strb_ok s₃ Rd .x7 (off := 0) (by decide) wR
  obtain ⟨s₅, e₅, g₅, o₅, m₅, rd₅, wr₅⟩ := addImm_ok s₄ .x9 .x9 (v := 1) (by decide)
  obtain ⟨s₆, e₆, g₆, o₆, m₆, rd₆, wr₆⟩ := addImm_ok s₅ Rd Rd (v := 1) (by decide)
  obtain ⟨s₇, e₇, g₇, o₇, m₇, rd₇, wr₇⟩ := subImm_ok s₆ Rl Rl (v := 1) (by decide)
  have run : runBlock isa (xorByte Rd Rl) s = some s₇ := by
    have h : xorByte Rd Rl = [.ldrb .x6 .x9 0] ++ ([.ldrb .x7 Rd 0] ++ ([eorR .x7 .x7 .x6] ++
        ([.strb .x7 Rd 0] ++ ([.addImm .x .x9 .x9 1] ++ ([.addImm .x Rd Rd 1] ++ [.subImm .x Rl Rl 1]))))) := rfl
    rw [h, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some, runBlock_app, e₆,
      Option.bind_some, e₇]
  refine WP.of_runBlock ⟨s₇, run, ?_⟩
  -- Registers.
  have gR : ∀ x, x ≠ .x9 → x ≠ .x6 → x ≠ .x7 → x ≠ Rd → x ≠ Rl → s₇.gpr x = s.gpr x := fun x h1 h2 h3 h4 h5 => by
    rw [o₇ _ h5, o₆ _ h4, o₅ _ h1, g₄, o₃ _ h3, o₂ _ h3, o₁ _ h2]
  have dat₄ : s₄.gpr Rd = R + BitVec.ofNat 64 j := by
    rw [g₄, o₃ _ hp.d7.1, o₂ _ hp.d7.1, o₁ _ hp.d6.1, hi.dat]
  have x9₇ : s₇.gpr .x9 = K + BitVec.ofNat 64 (j + 1) := by
    rw [o₇ _ (Ne.symm hp.d9.2), o₆ _ (Ne.symm hp.d9.1), g₅, g₄, o₃ _ (by decide), o₂ _ (by decide),
      o₁ _ (by decide), hi.x9]
    exact VG.Offset.add_add K j 1
  have dat₇ : s₇.gpr Rd = R + BitVec.ofNat 64 (j + 1) := by
    rw [o₇ _ hp.dl, g₆, o₅ _ hp.d9.1, dat₄]
    exact VG.Offset.add_add R j 1
  have left₇ : s₇.gpr Rl = BitVec.ofNat 64 (r - (j + 1)) := by
    rw [g₇, o₆ _ (Ne.symm hp.dl), o₅ _ hp.d9.2, g₄, o₃ _ hp.d7.2, o₂ _ hp.d7.2, o₁ _ hp.d6.2, hi.left]
    exact ofNat_sub_one hj
  -- Memory.
  have mem₇ : s₇.mem = s.mem.writeW (R + BitVec.ofNat 64 j)
      (s.mem (R + BitVec.ofNat 64 j) ^^^ s.mem (K + BitVec.ofNat 64 j)) := by
    rw [m₇, m₆, m₅, m₄, m₃, m₂, m₁, g₃, o₃ Rd hp.d7.1, g₂, o₂ .x6 (by decide), g₁, o₂ Rd hp.d7.1, o₁ Rd hp.d6.1,
      hi.dat, hi.x9, p0, p0, setWidth_xor_byte, m₁]
  have hRj : Region.Sub ⟨R + BitVec.ofNat 64 j, 1⟩ ⟨R, r⟩ := VG.Offset.sub_base R (by omega)
  have hK : ∀ q < r, s.mem (K + BitVec.ofNat 64 q) = s₀.mem (K + BitVec.ofNat 64 q) := fun q hq =>
    hi.frame.bytes (R := ⟨K, r⟩) (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact hp.disj)
      (show r ≤ 2 ^ 64 by omega) hq
  have data₇ : ∀ q < r, s₇.mem (R + BitVec.ofNat 64 q) =
      if q < j + 1 then s₀.mem (R + BitVec.ofNat 64 q) ^^^ s₀.mem (K + BitVec.ofNat 64 q)
      else s₀.mem (R + BitVec.ofNat 64 q) := fun q hq => by
    rw [mem₇, writeW8_apply]
    by_cases hqj : q = j
    · subst hqj
      rw [ite_eq_left rfl, ite_eq_left (Nat.lt_succ_self _), hi.data q hq, ite_eq_right (Nat.lt_irrefl _), hK q hq]
    · have hne : R + BitVec.ofNat 64 q ≠ R + BitVec.ofNat 64 j := fun h => hqj (by
        have := congrArg BitVec.toNat ((BitVec.add_right_inj R).mp h)
        simp only [BitVec.toNat_ofNat] at this
        rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this)
      rw [ite_eq_right hne, hi.data q hq]
      by_cases h1 : q < j
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
      · rw [ite_eq_right h1, ite_eq_right (by omega)]
  have fr₇ : Frame [⟨R, r⟩] s₀.mem s₇.mem := by
    rw [mem₇]
    exact hi.frame.trans ((writeByte_frame _ _ _).sub fun x hx => ⟨⟨R, r⟩, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hx; subst hx; exact hRj⟩)
  have rd₇' : s₇.rd = s₀.rd := by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd]
  have wr₇' : s₇.wr = s₀.wr := by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr]
  have gpr₇ : ∀ x, x ≠ .x9 → x ≠ .x6 → x ≠ .x7 → x ≠ Rd → x ≠ Rl → s₇.gpr x = s₀.gpr x :=
    fun x h1 h2 h3 h4 h5 => by rw [gR x h1 h2 h3 h4 h5, hi.gpr x h1 h2 h3 h4 h5]
  have hz : isa.eval (.nonzero .x Rl) s₇ = some !(decide (j + 1 = r)) := by
    rw [eval_nonzero, left₇, ofNat_beq_zero (by omega),
      decide_eq_decide.mpr (show r - (j + 1) = 0 ↔ j + 1 = r by omega)]
  by_cases hdone : j + 1 = r
  · refine .inl ⟨by rw [hz, decide_eq_true hdone]; rfl,
      by rw [left₇, show r - (j + 1) = 0 by omega]; rfl, fun q hq => ?_, fr₇, rd₇', wr₇', gpr₇⟩
    rw [data₇ q hq, ite_eq_left (by omega)]
  · exact .inr ⟨by rw [hz, decide_eq_false hdone]; rfl, x9₇, dat₇, left₇, by omega, data₇, fr₇, rd₇', wr₇', gpr₇⟩

/-- The XOR loop, from its first byte. -/
theorem xorLoop_wp {s₀ : State} {K R : Addr} {r : Nat} {Rd Rl : Reg} (hp : XPre s₀ K R r Rd Rl)
    (h0 : XInv s₀ K R r Rd Rl 0 s₀) :
    WP isa (.loop (.block (xorByte Rd Rl)) (.nonzero .x Rl)) s₀ (XDone s₀ K R r Rd Rl) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = r - j ∧ XInv s₀ K R r Rd Rl j s) (fun m s hs => ?_) r s₀
    ⟨0, by simp, h0⟩
  obtain ⟨j, rfl, hj⟩ := hs
  refine WP.mono (xorByte_wp hp hj) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · exact .inr ⟨z, r - (j + 1), by have := d.lt; have := hj.lt; omega, j + 1, rfl, d⟩

/-! ## The loop -/

variable {c : Core}

/-- `x8 := leftReg >> lg` tests for fewer than a block's `8 bw` bytes. -/
theorem two_pow_fbLg (h0 : 0 < c.bw) (h2 : c.bw ≤ 2) : 2 ^ c.fbLg = 8 * c.bw := by
  have : ∀ b < 3, 0 < b → 2 ^ (2 + b) = 8 * b := by decide
  exact this c.bw (by omega) h0

/-- What the loop works on: the scratch buffer at `B`, the `len` bytes at
`D`. -/
structure FPre (c : Core) (s₀ : State) (B D : Addr) (len : Nat) : Prop where
  scr : ScrIn s₀ B c.total
  dat : (⟨D, len⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨D, len⟩ ⟨B, 8 * c.total⟩
  fitD : D.toNat + len ≤ 2 ^ 64
  small : len < 2 ^ 64

/-- The loop, before segment `j`; `m₀` is the memory on entry, `iv` the IV. -/
structure FInvF (cs : BlockSpec c) (mo : FbMode) (ivR : Reg) (s₀ : State) (m₀ : Mem) (B D : Addr) (len : Nat)
    (k : cs.Key) (iv : List Byte) (j : Nat) (s : State) : Prop where
  base : s.gpr sb = B
  ready : cs.Ready s B k
  saved : ∀ i < 10, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  dataR : s.gpr c.dataReg = D + BitVec.ofNat 64 (8 * c.bw * j)
  leftR : s.gpr c.leftReg = BitVec.ofNat 64 (len - 8 * c.bw * j)
  lt : 8 * c.bw * j < len
  buf : ∀ u < 8 * c.bw, s.mem (B + BitVec.ofNat 64 (8 * c.buf) + BitVec.ofNat 64 u) =
    (fbIn mo (8 * c.bw) (cs.cipher k) m₀ D iv j).getD u 0
  data : ∀ i < len, s.mem (D + BitVec.ofNat 64 i) =
    if i < 8 * c.bw * j then (fbOut mo (8 * c.bw) (cs.cipher k) m₀ D iv (i / (8 * c.bw))).getD (i % (8 * c.bw)) 0
    else m₀ (D + BitVec.ofNat 64 i)
  frame : Frame [⟨B, 8 * c.total⟩, ⟨D, len⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ivK : s.gpr ivR = s₀.gpr ivR

/-- The loop, done. -/
structure FDoneF (cs : BlockSpec c) (mo : FbMode) (ivR : Reg) (s₀ : State) (m₀ : Mem) (B D : Addr) (len : Nat)
    (k : cs.Key) (iv : List Byte) (s : State) : Prop where
  base : s.gpr sb = B
  saved : ∀ i < 10, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  buf : ∀ u < 8 * c.bw, s.mem (B + BitVec.ofNat 64 (8 * c.buf) + BitVec.ofNat 64 u) =
    (fbNextF mo (8 * c.bw) (cs.cipher k) m₀ D iv len).getD u 0
  data : ∀ i < len, s.mem (D + BitVec.ofNat 64 i) =
    (fbOut mo (8 * c.bw) (cs.cipher k) m₀ D iv (i / (8 * c.bw))).getD (i % (8 * c.bw)) 0
  frame : Frame [⟨B, 8 * c.total⟩, ⟨D, len⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ivK : s.gpr ivR = s₀.gpr ivR

theorem fbSeg_wp (cs : BlockSpec c) (mo : FbMode) {ivR : Reg} (hivR : ivR ∉ modeRegs c) {s₀ : State} {m₀ : Mem}
    {B D : Addr} {len : Nat} {k : cs.Key} {iv : List Byte} (hiv : iv.length = 8 * c.bw) (hp : FPre c s₀ B D len)
    (hsc : KeepsReg ivR c.crypt) {j : Nat} {s : State} (hi : FInvF cs mo ivR s₀ m₀ B D len k iv j s) :
    WP isa (c.fbSeg mo) s fun s' =>
      (isa.eval (.nonzero .x c.leftReg) s' = some false ∧ FDoneF cs mo ivR s₀ m₀ B D len k iv s') ∨
      (isa.eval (.nonzero .x c.leftReg) s' = some true ∧ FInvF cs mo ivR s₀ m₀ B D len k iv (j + 1) s') := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hbI := hL.bufImm
  have hG0 := hL.G_pos
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hj := hi.lt
  have hL0 : 0 < 8 * c.bw := by omega_arith
  have hLG : 8 * c.bw ≤ 8 * c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  have hGb : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  have hj1 : 8 * c.bw * (j + 1) = 8 * c.bw * j + 8 * c.bw := Nat.mul_succ _ _
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨down, dsb, -⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨lown, lsb, -⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨d6, d7, d8, d9, -⟩ := not_own down
  obtain ⟨l6, l7, l8, l9, -⟩ := not_own lown
  obtain ⟨iown, idr, ilr⟩ := of_not_modeRegs hivR
  obtain ⟨i6, i7, i8, i9, -⟩ := not_own iown
  have hlen64 : len ≤ 2 ^ 64 := by omega_arith
  have hsmall := hp.small
  let ciph := cs.cipher k
  let A := D + BitVec.ofNat 64 (8 * c.bw * j)
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  have hwS : (⟨B, 8 * c.total⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr.wr
  have hwD : (⟨D, len⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have subT : Region.Sub ⟨T, 8 * c.bw⟩ ⟨B, 8 * c.total⟩ := VG.Offset.sub_base B (by omega_arith)
  have subTbuf : Region.Sub ⟨T, 8 * c.bw⟩ (blkRegion c B) := Region.sub_prefix hLG
  have subCore : Region.Sub (coreRegion c B) ⟨B, 8 * c.total⟩ := Region.sub_prefix (by omega_arith)
  have dDS : ∀ {r : Region}, Region.Sub r ⟨B, 8 * c.total⟩ → Region.Disjoint ⟨D, len⟩ r :=
    fun h => hp.sep.sub_right h
  have hw : ∀ w, 8 * c.bw * j + 8 * w = 8 * (c.bw * j + w) := fun w => by rw [Nat.mul_add, Nat.mul_assoc]
  have inT : ∀ w < c.bw, InRegions s.wr (T + BitVec.ofNat 64 (8 * w)) 8 := fun w hw' =>
    ⟨_, hwS, by rw [addr_add]; exact VG.Offset.contains_base B (by omega_arith) (by omega_arith)⟩
  -- Enciphered.
  unfold Core.fbSeg
  refine WP.seq (WP.mono (WP.keepReg hsc (cs.crypt_wp hi.base ⟨hwS, hfit⟩ hi.ready))
    fun s₂ ⟨⟨base₂, dr₂, lr₂, ready₂, f₂, ks₂, rd₂, wr₂⟩, i₂⟩ => ?_)
  have eT : blkAddr c B 0 = T := by simp only [blkAddr, T, Nat.mul_zero, Nat.add_zero]
  have hin : bytesAt s.mem T (8 * c.bw) = fbIn mo (8 * c.bw) ciph m₀ D iv j := by
    apply List.ext_getElem (by
      simp only [bytesAt, List.length_map, List.length_range]; rw [fbIn_length (cs.cipher_len k) m₀ D hiv])
    intro u h1 _
    have hu : u < 8 * c.bw := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [hi.buf u hu, List.getElem_eq_getD 0]
  have E₂ : ∀ u < 8 * c.bw, s₂.mem (T + BitVec.ofNat 64 u) = (ciph (fbIn mo (8 * c.bw) ciph m₀ D iv j)).getD u 0 :=
    fun u hu => by rw [← bytesAt_getD s₂.mem T hu, ← eT, ks₂ 0 hG0, eT, hin]
  have D₂ : ∀ i < len, s₂.mem (D + BitVec.ofNat 64 i) = s.mem (D + BitVec.ofNat 64 i) := fun i hi' =>
    f₂.bytes (R := ⟨D, len⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact dDS subCore) hlen64 hi'
  have mA : ∀ u, 8 * c.bw * j + u < len → s.mem (A + BitVec.ofNat 64 u) = m₀ (A + BitVec.ofNat 64 u) := fun u hu => by
    rw [addr_add, hi.data _ hu, ite_eq_right (by omega_arith)]
  have D₂' : ∀ u, 8 * c.bw * j + u < len → s₂.mem (A + BitVec.ofNat 64 u) = s.mem (A + BitVec.ofNat 64 u) :=
    fun u hu => by rw [addr_add]; exact D₂ _ hu
  -- Whether a whole block is left.
  have hleft : s₂.gpr c.leftReg = BitVec.ofNat 64 (len - 8 * c.bw * j) := by rw [lr₂, hi.leftR]
  obtain ⟨s₃, e₃, x8₃, g₃, m₃, rd₃, wr₃⟩ := lsr_ok s₂ .x8 c.leftReg (sh := c.fbLg)
    (by simp only [Core.fbLg]; omega_arith)
  have hz₃ : isa.eval (.zero .x .x8) s₃ = some (decide (len - 8 * c.bw * j < 8 * c.bw)) := by
    rw [eval_zero, x8₃, hleft, lsr_beq (by omega_arith), two_pow_fbLg hbw0 hbw2]
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  have sy₃ : s₃.syms = s₂.syms := runBlock_syms e₃
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₂, hi.rd]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂, hi.wr]
  have data₃ : s₃.gpr c.dataReg = A := by rw [g₃ _ d8, dr₂, hi.dataR]
  have base₃ : s₃.gpr sb = B := by rw [g₃ _ (by decide), base₂]
  -- The slots: none of the core's, nor in the data or the buffer's first block.
  have slotOut : ∀ i < 10, ∀ {R : Region}, (Region.Sub R ⟨D, len⟩ ∨ R = ⟨T, 8 * c.bw⟩ ∨
      R = coreRegion c B) → Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ R := fun i hi10 R hR => by
    rcases hR with h | rfl | rfl
    · exact ((dDS (VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.total by
        omega_arith))).sub_left h).symm
    · exact VG.Offset.disjoint B (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
    · exact VG.Offset.disjoint_base B (by omega_arith) (by omega_arith)
  have saved₂ : ∀ i < 10, s₂.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64 :=
    fun i hi10 => by
      rw [← hi.saved i hi10]
      exact f₂.readW (Region.contains_self _ _) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact slotOut i hi10 (.inr (.inr rfl))) (by decide)
  have fr₂ : Frame [⟨B, 8 * c.total⟩, ⟨D, len⟩] s₀.mem s₂.mem :=
    hi.frame.trans (f₂.sub fun x hx => ⟨_, List.mem_cons_self, by
      simp only [List.mem_singleton] at hx; subst hx; exact subCore⟩)
  refine WP.ite (decide (len - 8 * c.bw * j < 8 * c.bw)) hz₃ (fun hb => ?_) (fun hb => ?_)
  · -- A partial segment: `r` bytes.
    have hb' : len - 8 * c.bw * j < 8 * c.bw := by simpa using hb
    let r := len - 8 * c.bw * j
    have hr0 : 0 < r := by omega_arith
    have hdiv : len / (8 * c.bw) = j := by
      rw [show len = 8 * c.bw * j + r by omega_arith]; exact idx_div hb'
    have hmod : len % (8 * c.bw) = r := by
      rw [show len = 8 * c.bw * j + r by omega_arith]; exact idx_mod hb'
    obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := addImm_ok s₃ .x9 sb (v := 8 * c.buf) hbI
    have x9₄ : s₄.gpr .x9 = T := by rw [a₄, base₃]
    have g₄ : ∀ x, x ≠ .x9 → x ≠ .x8 → s₄.gpr x = s₂.gpr x := fun x h1 h2 => by rw [o₄ x h1, g₃ x h2]
    have mem₄ : s₄.mem = s₂.mem := by rw [m₄, m₃]
    have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rd₃']
    have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₃']
    have subTr : Region.Sub ⟨T, r⟩ ⟨T, 8 * c.bw⟩ := Region.sub_prefix (by omega_arith)
    have subAr : Region.Sub ⟨A, r⟩ ⟨D, len⟩ := VG.Offset.sub_base D (by omega_arith)
    have hxp : XPre s₄ T A r c.dataReg c.leftReg :=
      { small := by omega_arith
        disj := ((dDS subT).sub_left subAr).sub_right subTr |>.symm
        rdK := fun q hq => by
          rw [rd₄', wr₄']
          exact inRd ⟨_, hp.scr.wr, by
            rw [addr_add]; exact VG.Offset.contains_base B (by omega_arith) (by omega_arith)⟩
        wrR := fun q hq => by
          rw [wr₄']
          exact ⟨_, hp.dat, by rw [addr_add]; exact VG.Offset.contains_base D (by omega_arith) (by omega_arith)⟩
        dl := hdl
        d9 := ⟨d9, l9⟩
        d6 := ⟨d6, l6⟩
        d7 := ⟨d7, l7⟩ }
    have hx0 : XInv s₄ T A r c.dataReg c.leftReg 0 s₄ :=
      { x9 := by rw [x9₄]; simp
        dat := by rw [g₄ _ d9 d8, dr₂, hi.dataR]; simp [A]
        left := by rw [g₄ _ l9 l8, hleft, Nat.sub_zero]
        lt := hr0
        data := fun q hq => by rw [ite_eq_right (Nat.not_lt_zero _)]
        frame := Frame.refl _ _
        rd := rfl
        wr := rfl
        gpr := fun _ _ _ _ _ _ => rfl }
    refine WP.seq (WP.of_runBlock ⟨s₄, e₄, WP.mono (xorLoop_wp hxp hx0) fun s₅ d₅ => .inl ⟨by
      rw [eval_nonzero, d₅.left]; rfl, ?_⟩⟩)
    have f₅ : Frame [⟨A, r⟩] s₂.mem s₅.mem := by rw [← mem₄]; exact d₅.frame
    have g₅ : ∀ x, x ≠ .x9 → x ≠ .x6 → x ≠ .x7 → x ≠ .x8 → x ≠ c.dataReg → x ≠ c.leftReg →
        s₅.gpr x = s₂.gpr x :=
      fun x h1 h2 h3 h4 h5 h6 => by rw [d₅.gpr x h1 h2 h3 h5 h6, g₄ x h1 h4]
    have kT : ∀ u < 8 * c.bw, s₅.mem (T + BitVec.ofNat 64 u) = s₂.mem (T + BitVec.ofNat 64 u) := fun u hu =>
      f₅.bytes (R := ⟨T, 8 * c.bw⟩) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact ((dDS subT).sub_left subAr).symm)
        (show 8 * c.bw ≤ 2 ^ 64 by omega_arith) hu
    refine ⟨by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (Ne.symm dsb) (Ne.symm lsb), base₂],
      fun i hi10 => ?_, fun u hu => ?_, fun i hi' => ?_, ?_, by rw [d₅.rd, rd₄'], by rw [d₅.wr, wr₄'],
      by rw [g₅ _ i9 i6 i7 i8 idr ilr, i₂, hi.ivK]⟩
    · rw [← saved₂ i hi10]
      exact f₅.readW (Region.contains_self _ _) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact slotOut i hi10 (.inl subAr)) (by decide)
    · rw [kT u hu, E₂ u hu, fbNextF, ite_eq_right (by rw [hmod]; omega_arith), hdiv]
    · by_cases hlt : i < 8 * c.bw * j
      · have out : ∀ R ∈ [(⟨A, r⟩ : Region)], ¬ R.Contains (D + BitVec.ofNat 64 i) 1 := fun R hR => by
          simp only [List.mem_singleton] at hR; subst hR
          exact not_contains_off D (.inl hlt) (by omega_arith) hr0 (by omega_arith)
        rw [f₅ _ out, D₂ i hi', hi.data i hi', ite_eq_left hlt]
      · obtain ⟨q, rfl⟩ : ∃ q, i = 8 * c.bw * j + q := ⟨i - 8 * c.bw * j, by omega_arith⟩
        have hq : q < r := by omega_arith
        have e := d₅.data q hq
        rw [mem₄] at e
        rw [← addr_add, e, idx_div (by omega_arith), idx_mod (by omega_arith), D₂' q (by omega_arith),
          mA q (by omega_arith), fbOut_getD mo (cs.cipher_len k) m₀ D iv j (by omega_arith), E₂ q (by omega_arith),
          addr_add]
    · exact fr₂.trans (f₅.sub fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, subAr⟩)
  · -- A whole block.
    have hb' : 8 * c.bw ≤ len - 8 * c.bw * j := by simpa using hb
    have hjl : 8 * c.bw * j + 8 * c.bw ≤ len := by omega_arith
    have subA : Region.Sub ⟨A, 8 * c.bw⟩ ⟨D, len⟩ := VG.Offset.sub_base D hjl
    have dAT : Region.Disjoint ⟨A, 8 * c.bw⟩ ⟨T, 8 * c.bw⟩ := (dDS subT).sub_left subA
    have inA : ∀ w < c.bw, InRegions s.wr (A + BitVec.ofNat 64 (8 * w)) 8 := fun w hw' =>
      ⟨_, hwD, by rw [addr_add]; exact VG.Offset.contains_base D (by omega_arith) (by omega_arith)⟩
    refine WP.block_append (WP.mono_syms (fbOp_wp mo (by omega_arith) (by omega_arith) data₃ (by rw [base₃]) d6 d7
      (fun w hw' => by rw [wr₃, wr₂]; exact inA w hw') (fun w hw' => by rw [wr₃, wr₂]; exact inT w hw') dAT
      (by omega_arith)) fun s₃a ⟨g₃a, rd₃a, wr₃a, mA₃, mT₃, f₃a⟩ sy₃a => ?_)
    obtain ⟨s₃b, e₃b, a₃b, o₃b, m₃b, rd₃b, wr₃b⟩ := addImm_ok s₃a c.dataReg c.dataReg (v := 8 * c.bw)
      (by omega_arith)
    obtain ⟨s₄, e₄, l₄, o₄, m₄, rd₄, wr₄⟩ := subImm_ok s₃b c.leftReg c.leftReg (v := 8 * c.bw) (by omega_arith)
    refine WP.of_runBlock ⟨s₄, by
      rw [Core.fbNextBytes, show ([.addImm .x c.dataReg c.dataReg (8 * c.bw),
        .subImm .x c.leftReg c.leftReg (8 * c.bw)] : List Instr) =
        [.addImm .x c.dataReg c.dataReg (8 * c.bw)] ++ [.subImm .x c.leftReg c.leftReg (8 * c.bw)] from rfl,
        runBlock_app, e₃b, Option.bind_some, e₄], ?_⟩
    have keep₄ : ∀ x, x ≠ .x6 → x ≠ .x7 → x ≠ .x8 → x ≠ c.dataReg → x ≠ c.leftReg → s₄.gpr x = s₂.gpr x :=
      fun x h1 h2 h3 h4 h5 => by rw [o₄ x h5, o₃b x h4, g₃a x h1 h2, g₃ x h3]
    have left₃ : s₃b.gpr c.leftReg = BitVec.ofNat 64 (len - 8 * c.bw * j) := by
      rw [o₃b _ (Ne.symm hdl), g₃a _ l6 l7, g₃ _ l8, hleft]
    have left₄ : s₄.gpr c.leftReg = BitVec.ofNat 64 (len - 8 * c.bw * (j + 1)) := by
      rw [l₄, left₃, VG.Offset.ofNat_sub_ofNat hb', hj1, Nat.sub_sub]
    have hz₄ : isa.eval (.nonzero .x c.leftReg) s₄ = some !(decide (8 * c.bw * (j + 1) = len)) := by
      rw [eval_nonzero, left₄, ofNat_beq_zero (by omega_arith),
        decide_eq_decide.mpr (show len - 8 * c.bw * (j + 1) = 0 ↔ 8 * c.bw * (j + 1) = len by omega_arith)]
    have hAL : A + BitVec.ofNat 64 (8 * c.bw) = D + BitVec.ofNat 64 (8 * c.bw * (j + 1)) := by rw [addr_add, hj1]
    have data₄ : s₄.gpr c.dataReg = D + BitVec.ofNat 64 (8 * c.bw * (j + 1)) := by
      rw [o₄ _ hdl, a₃b, g₃a _ d6 d7, data₃, hAL]
    have mem₄ : s₄.mem = s₃a.mem := by rw [m₄, m₃b]
    have base₄ : s₄.gpr sb = B := by
      rw [keep₄ _ (by decide) (by decide) (by decide) (Ne.symm dsb) (Ne.symm lsb), base₂]
    have ivK₄ : s₄.gpr ivR = s₀.gpr ivR := by rw [keep₄ _ i6 i7 i8 idr ilr, i₂, hi.ivK]
    have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rd₃b, rd₃a, rd₃']
    have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₃b, wr₃a, wr₃']
    have f₃ : Frame [⟨A, 8 * c.bw⟩, ⟨T, 8 * c.bw⟩] s₂.mem s₄.mem := by rw [mem₄, ← m₃]; exact f₃a
    have saved₄ : ∀ i < 10, s₄.mem.readW (wordAddr B (c.slots + i)) 64 =
        s₀.mem.readW (wordAddr B (c.slots + i)) 64 := fun i hi10 => by
      rw [← saved₂ i hi10]
      exact f₃.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact slotOut i hi10 (.inl subA)
        · exact slotOut i hi10 (.inr (.inl rfl))) (by decide)
    have fr₄ : Frame [⟨B, 8 * c.total⟩, ⟨D, len⟩] s₀.mem s₄.mem :=
      fr₂.trans (f₃.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, subA⟩
        · exact ⟨_, List.mem_cons_self, subT⟩)
    have ready₄ : cs.Ready s₄ B k := cs.ready_frame ready₂ f₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl ((dDS subCore).sub_left subA).symm
      · exact .inr subTbuf)
      ⟨fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, by rw [wr₂]; exact hwD, subA⟩
        · exact ⟨_, by rw [wr₂]; exact hwS, subT⟩,
        by rw [rd₄, rd₃b, rd₃a, rd₃], by rw [wr₄, wr₃b, wr₃a, wr₃],
        by rw [runBlock_syms e₄, runBlock_syms e₃b, sy₃a, sy₃]⟩
      fun r hr => by
      obtain ⟨h1, h2, h3⟩ := of_not_modeRegs hr
      obtain ⟨n6, n7, n8, -⟩ := not_own h1
      exact keep₄ r n6 n7 n8 h2 h3
    have buf₄ : ∀ u < 8 * c.bw, s₄.mem (T + BitVec.ofNat 64 u) =
        (fbIn mo (8 * c.bw) ciph m₀ D iv (j + 1)).getD u 0 := fun u hu => by
      rw [mem₄, mT₃ u hu, m₃, E₂ u hu, D₂' u (by omega_arith), mA u (by omega_arith),
        fbIn_succ_getD mo (cs.cipher_len k) m₀ D iv j hu, addr_add]
    have data₄' : ∀ i < len, s₄.mem (D + BitVec.ofNat 64 i) =
        if i < 8 * c.bw * (j + 1) then (fbOut mo (8 * c.bw) ciph m₀ D iv (i / (8 * c.bw))).getD (i % (8 * c.bw)) 0
        else m₀ (D + BitVec.ofNat 64 i) := fun i hi' => by
      by_cases hin : 8 * c.bw * j ≤ i ∧ i < 8 * c.bw * (j + 1)
      · obtain ⟨q, rfl⟩ : ∃ q, i = 8 * c.bw * j + q := ⟨i - 8 * c.bw * j, by omega_arith⟩
        have hq : q < 8 * c.bw := by omega_arith
        rw [ite_eq_left hin.2, idx_div hq, idx_mod hq, fbOut_getD mo (cs.cipher_len k) m₀ D iv j hq, mem₄, ← addr_add,
          mA₃ q hq, m₃, E₂ q hq, D₂' q (by omega_arith), mA q (by omega_arith)]
      · have out : ∀ R ∈ [(⟨A, 8 * c.bw⟩ : Region), ⟨T, 8 * c.bw⟩],
            ¬ R.Contains (D + BitVec.ofNat 64 i) 1 := fun R hR => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
          rcases hR with rfl | rfl
          · exact not_contains_off D (by omega_arith) (by omega_arith) hL0 (by omega_arith)
          · exact fun hc => dDS subT _ (VG.Offset.contains_base D (by omega_arith) (by omega_arith)) hc
        rw [mem₄, f₃a _ out, m₃, D₂ i hi', hi.data i hi']
        by_cases h3 : i < 8 * c.bw * j
        · rw [ite_eq_left h3, ite_eq_left (by omega_arith)]
        · rw [ite_eq_right h3, ite_eq_right (by omega_arith)]
    by_cases hdone : 8 * c.bw * (j + 1) = len
    · refine .inl ⟨by rw [hz₄, decide_eq_true hdone]; rfl, base₄, saved₄, fun u hu => ?_,
        fun i hi' => by rw [data₄' i hi', ite_eq_left (by omega_arith)], fr₄, rd₄', wr₄', ivK₄⟩
      have hmod : len % (8 * c.bw) = 0 := by rw [← hdone]; exact Nat.mul_mod_right _ _
      have hdiv : len / (8 * c.bw) = j + 1 := by rw [← hdone]; exact Nat.mul_div_cancel_left _ hL0
      rw [buf₄ u hu, fbNextF, ite_eq_left hmod, hdiv]
    · exact .inr ⟨by rw [hz₄, decide_eq_false hdone]; rfl, base₄, ready₄, saved₄, data₄, left₄, by omega_arith,
        buf₄, data₄', fr₄, rd₄', wr₄', ivK₄⟩

/-- The loop. -/
theorem fbFinalLoop_wp (cs : BlockSpec c) (mo : FbMode) {ivR : Reg} (hivR : ivR ∉ modeRegs c) {s₀ : State}
    {m₀ : Mem} {B D : Addr} {len : Nat} {k : cs.Key} {iv : List Byte} (hiv : iv.length = 8 * c.bw)
    (hp : FPre c s₀ B D len) (hsc : KeepsReg ivR c.crypt) {s : State}
    (hi : FInvF cs mo ivR s₀ m₀ B D len k iv 0 s) :
    WP isa (.loop (c.fbSeg mo) (.nonzero .x c.leftReg)) s (FDoneF cs mo ivR s₀ m₀ B D len k iv) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = len - 8 * c.bw * j ∧ FInvF cs mo ivR s₀ m₀ B D len k iv j s)
    (fun m s hs => ?_) len s ⟨0, by simp, hi⟩
  obtain ⟨j, rfl, hj⟩ := hs
  have hbw0 := cs.layout.bw_pos
  refine WP.mono (fbSeg_wp cs mo hivR hiv hp hsc hj) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · exact .inr ⟨z, len - 8 * c.bw * (j + 1), by
      have := d.lt; have := hj.lt; rw [Nat.mul_succ]; omega, j + 1, rfl, d⟩

/-! ## The whole function -/

theorem fbFinal_wp (cs : BlockSpec c) (mo : FbMode) {r : CtrRegs} (hr : RegsOk r) (hdn : c.dataReg ≠ r.n)
    {ivR : Reg} (hiv : IvRegOk c r ivR) {s₀ : State} {B P D : Addr} {len : Nat} {k : cs.Key}
    (hB : s₀.gpr r.scr = B) (hP : s₀.gpr r.ctr = P) (hD : s₀.gpr r.data = D) (hn : (s₀.gpr r.n).toNat = len)
    (hs : ScrIn s₀ B c.total) (hwP : (⟨P, 8 * c.bw⟩ : Region) ∈ s₀.wr) (hwD : (⟨D, len⟩ : Region) ∈ s₀.wr)
    (sPS : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨B, 8 * c.total⟩) (sDS : Region.Disjoint ⟨D, len⟩ ⟨B, 8 * c.total⟩)
    (sPD : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨D, len⟩) (fitD : D.toNat + len ≤ 2 ^ 64)
    (hk : cs.KeyArgs s₀ [⟨B, 8 * c.total⟩] k) (hsc : KeepsReg ivR c.prepare ∧ KeepsReg ivR c.crypt) :
    WP isa (c.fbFinal mo r ivR) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Core.savedRegs.getD i .x19) = s₀.gpr (Core.savedRegs.getD i .x19)) ∧
      (∀ i < len, s'.mem (D + BitVec.ofNat 64 i) =
        (fbOut mo (8 * c.bw) (cs.cipher k) s₀.mem D (bytesAt s₀.mem P (8 * c.bw)) (i / (8 * c.bw))).getD
          (i % (8 * c.bw)) 0) ∧
      bytesAt s'.mem P (8 * c.bw) = fbNextF mo (8 * c.bw) (cs.cipher k) s₀.mem D (bytesAt s₀.mem P (8 * c.bw)) len ∧
      Frame [⟨B, 8 * c.total⟩, ⟨D, len⟩, ⟨P, 8 * c.bw⟩] s₀.mem s'.mem ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hbI := hL.bufImm
  have hG0 := hL.G_pos
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hL0 : 0 < 8 * c.bw := by omega_arith
  have hLG : 8 * c.bw ≤ 8 * c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  have hGb : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  have hn64 : len ≤ 2 ^ 64 := by omega_arith
  have hsmall : len < 2 ^ 64 := by rw [← hn]; exact (s₀.gpr r.n).isLt
  have hN : 8 * c.total < 2 ^ 64 := by omega_arith
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨down, dsb, dk⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨lown, lsb, lk⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨d6, d7, -⟩ := not_own down
  obtain ⟨l6, l7, -⟩ := not_own lown
  obtain ⟨cs', c6, c7, -⟩ := not_setupRegs hr.ctr
  obtain ⟨ds', dd6, dd7, -⟩ := not_setupRegs hr.data
  obtain ⟨ns', n6, n7, -⟩ := not_setupRegs hr.n
  obtain ⟨iown, idr, ilr⟩ := of_not_modeRegs hiv.mode
  obtain ⟨i6, i7, -⟩ := not_own iown
  obtain ⟨isb, -, -, -⟩ := not_setupRegs hiv.setup
  let S : Region := ⟨B, 8 * c.total⟩
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  have subMode : Region.Sub (modeRegion c B) S := VG.Offset.sub_base B (by omega_arith)
  have subCore : Region.Sub (coreRegion c B) S := Region.sub_prefix (by omega_arith)
  have subT : Region.Sub ⟨T, (8 * c.bw)⟩ S := VG.Offset.sub_base B (by omega_arith)
  have subTbuf : Region.Sub ⟨T, (8 * c.bw)⟩ (blkRegion c B) := Region.sub_prefix hLG
  have dTP : Region.Disjoint ⟨T, (8 * c.bw)⟩ ⟨P, (8 * c.bw)⟩ := (sPS.sub_right subT).symm
  have dDcore : ∀ x ∈ [coreRegion c B], Region.Disjoint ⟨D, len⟩ x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact sDS.sub_right subCore
  have dPcore : ∀ x ∈ [coreRegion c B], Region.Disjoint ⟨P, (8 * c.bw)⟩ x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact sPS.sub_right subCore
  have inS : ∀ {d m : Nat}, d + m ≤ 8 * c.total → InRegions s₀.wr (B + BitVec.ofNat 64 d) m := fun h =>
    ⟨_, hs.wr, VG.Offset.contains_base B h (by omega_arith)⟩
  -- The mode's slots: none of the core's, nor in the data or at the IV.
  have slotIn : ∀ i < 10, Region.Sub ⟨wordAddr B (c.slots + i), 8⟩ S := fun i hi =>
    VG.Offset.sub_base B (by omega_arith)
  have slotCore : ∀ i < 10, Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ (coreRegion c B) := fun i hi =>
    VG.Offset.disjoint_base B (by omega_arith) (by omega_arith)
  have slotT : ∀ i < 10, Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ ⟨T, (8 * c.bw)⟩ := fun i hi =>
    VG.Offset.disjoint B (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  -- The entry.
  obtain ⟨sE, eE, bE, svE, fE, gE, rdE, wrE⟩ := entry_ok hsm hroom s₀ hB hs
  obtain ⟨sS, eS, xS, gS, mS, rdS, wrS⟩ := movR_ok sE ivR r.ctr
  obtain ⟨sA, eA, drA, lrA, gA, mA, rdA, wrA⟩ := ctrArgs_ok sS r hdn hdl
  unfold Core.fbFinal
  refine WP.seq (WP.of_runBlock ⟨sA, by
    rw [Core.fbEntry, runBlock_app, runBlock_app, eE, Option.bind_some, eS, Option.bind_some, eA], ?_⟩)
  have gA' : ∀ x, x ≠ sb → x ≠ ivR → x ≠ c.dataReg → x ≠ c.leftReg → sA.gpr x = s₀.gpr x :=
    fun x h1 h2 h3 h4 => by rw [gA x h3 h4, gS x h2, gE x h1]
  have bA : sA.gpr sb = B := by rw [gA _ (Ne.symm dsb) (Ne.symm lsb), gS _ (Ne.symm isb), bE]
  have ivA : sA.gpr ivR = P := by rw [gA _ idr ilr, xS, gE _ cs', hP]
  have rdA' : sA.rd = s₀.rd := by rw [rdA, rdS, rdE]
  have wrA' : sA.wr = s₀.wr := by rw [wrA, wrS, wrE]
  have fA : Frame [S] s₀.mem sA.mem := by
    rw [mA, mS]
    exact fE.sub fun x hx => ⟨S, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hx; subst hx; exact subMode⟩
  have svA : ∀ i < 10, sA.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.gpr (Core.savedRegs.getD i .x19) :=
    fun i hi => by rw [mA, mS, svE i hi]
  have kr := keyRegs_ne cs.keyRegs_ok
  have hkA : cs.KeyArgs sA [S] k :=
    cs.keyArgs_congr hk (fun x hx => gA' x (not_setupRegs (kr x hx)).1 (fun e => hiv.key (e ▸ hx))
      (fun e => dk (e ▸ hx)) (fun e => lk (e ▸ hx))) rdA' wrA'
      (by rw [runBlock_syms eA, runBlock_syms eS, runBlock_syms eE]) fA
  -- The key.
  refine WP.seq (WP.mono (WP.keepReg hsc.1 (cs.prepare_wp bA ⟨by rw [wrA']; exact hs.wr, hs.fit⟩
    List.mem_cons_self hkA)) fun s₄ ⟨⟨ready₄, b₄, dr₄, lr₄, f₄, rd₄, wr₄⟩, iv₄⟩ => ?_)
  have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rdA']
  have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wrA']
  have ivR₄ : s₄.gpr ivR = P := by rw [iv₄, ivA]
  have sv₄ : ∀ i < 10, s₄.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.gpr (Core.savedRegs.getD i .x19) :=
    fun i hi => by
      rw [← svA i hi]
      exact f₄.readW (Region.contains_self _ _) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact slotCore i hi) (by decide)
  -- The IV to the buffer.
  refine WP.seq (WP.mono_syms (copyN_wp (k := c.bw) (t := .x6) (u := .x6) (rd := sb) (rs := ivR) (od := 8 * c.buf)
    (os := 0) (P := T) (Q := P)
    ⟨by rw [b₄], by rw [ivR₄]; simp, by decide, Ne.symm i6, by decide, Ne.symm i6, by omega_arith, by decide,
      by omega_arith, by omega_arith, fun w hw => by rw [wr₄', addr_add]; exact inS (by omega_arith),
      fun w hw => by
        rw [rd₄', wr₄']
        exact inRd ⟨_, hwP, VG.Offset.contains_base P (by omega_arith) (by omega_arith)⟩,
      dTP, by omega_arith⟩) fun s₅ h₅ sy₅ => ?_)
  have g₅ : ∀ x, x ≠ .x6 → s₅.gpr x = s₄.gpr x := fun x h => h₅.regs x h h
  have mem₅ : s₅.mem = over s₄.mem T (8 * c.bw) fun i => s₄.mem (P + BitVec.ofNat 64 i) := h₅.mem
  have f₅ : Frame [⟨T, (8 * c.bw)⟩] s₄.mem s₅.mem := by rw [mem₅]; exact over_frame _ _ _ _
  have b₅ : s₅.gpr sb = B := by rw [g₅ _ (by decide), b₄]
  have ivR₅ : s₅.gpr ivR = P := by rw [g₅ _ i6, ivR₄]
  have rd₅' : s₅.rd = s₀.rd := by rw [h₅.rd, rd₄']
  have wr₅' : s₅.wr = s₀.wr := by rw [h₅.wr, wr₄']
  have left₅ : s₅.gpr c.leftReg = s₀.gpr r.n := by
    rw [g₅ _ l6, lr₄, lrA, gS _ (Ne.symm hiv.n), gE _ ns']
  have hz₅ : isa.eval (.zero .x c.leftReg) s₅ = some (decide (len = 0)) := by
    rw [eval_zero, left₅]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  have sv₅ : ∀ i < 10, s₅.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.gpr (Core.savedRegs.getD i .x19) :=
    fun i hi => by
      rw [← sv₄ i hi]
      exact f₅.readW (Region.contains_self _ _) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact slotT i hi) (by decide)
  -- The memory before the loop: the IV and the data as on entry.
  have m₄P : ∀ u < (8 * c.bw), s₄.mem (P + BitVec.ofNat 64 u) = s₀.mem (P + BitVec.ofNat 64 u) := fun u hu => by
    rw [f₄.bytes (R := ⟨P, (8 * c.bw)⟩) dPcore (show 8 * c.bw ≤ 2 ^ 64 by omega_arith) hu]
    exact fA.bytes (R := ⟨P, (8 * c.bw)⟩) (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact sPS)
      (show 8 * c.bw ≤ 2 ^ 64 by omega_arith) hu
  have m₅D : ∀ i < len, s₅.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) := fun i hi => by
    rw [f₅.bytes (R := ⟨D, len⟩) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact sDS.sub_right subT) hn64 hi,
      f₄.bytes (R := ⟨D, len⟩) dDcore hn64 hi]
    exact fA.bytes (R := ⟨D, len⟩) (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact sDS)
      hn64 hi
  let iv := bytesAt s₀.mem P (8 * c.bw)
  have hivl : iv.length = (8 * c.bw) := by simp [iv, bytesAt]
  have buf₅ : ∀ u < (8 * c.bw), s₅.mem (B + BitVec.ofNat 64 (8 * c.buf) + BitVec.ofNat 64 u) =
      (fbIn mo (8 * c.bw) (cs.cipher k) s₀.mem D iv 0).getD u 0 := fun u hu => by
    rw [mem₅, over_at hu (by omega_arith), m₄P u hu, fbIn, bytesAt_getD _ _ hu]
  have hp : FPre c s₅ B D len :=
    ⟨⟨by rw [wr₅']; exact hs.wr, hs.fit⟩, by rw [wr₅']; exact hwD, sDS, fitD, hsmall⟩
  have fr₅ : Frame [S] s₀.mem s₅.mem :=
    fA.trans ((f₄.sub fun x hx => ⟨S, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hx; subst hx; exact subCore⟩).trans
      (f₅.sub fun x hx => ⟨S, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hx; subst hx; exact subT⟩))
  -- The segments.
  refine WP.seq (WP.mono (M := isa) (Q := FDoneF cs mo ivR s₅ s₀.mem B D len k iv)
    (WP.ite (decide (len = 0)) hz₅ (fun h0 => ?_) (fun h0 => ?_)) fun s₆ d₆ => ?_)
  · have hn0 : len = 0 := by simpa using h0
    refine WP.block_nil ⟨b₅, fun _ _ => rfl, fun u hu => ?_, fun i hi' => by omega_arith, Frame.refl _ _, rfl, rfl,
      rfl⟩
    rw [hn0, fbNextF, ite_eq_left (Nat.zero_mod _), Nat.zero_div]; exact buf₅ u hu
  · have hn0 : len ≠ 0 := by simpa using h0
    refine fbFinalLoop_wp cs mo hiv.mode hivl hp hsc.2 ⟨b₅, cs.ready_frame ready₄ f₅ (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact .inr subTbuf)
        ⟨fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; exact ⟨S, by rw [wr₄']; exact hs.wr, subT⟩,
          h₅.rd, h₅.wr, sy₅⟩
        (fun x hx => by obtain ⟨h1, -, -⟩ := of_not_modeRegs hx; exact g₅ x (not_own h1).1),
      fun _ _ => rfl, ?_, ?_, by omega_arith, buf₅, fun i hi' => ?_, Frame.refl _ _, rfl, rfl, rfl⟩
    · rw [g₅ _ d6, dr₄, drA, gS _ (Ne.symm hiv.data), gE _ ds', hD]; simp
    · rw [left₅, Nat.mul_zero, Nat.sub_zero, ← hn]; simp
    · rw [ite_eq_right (by omega_arith)]; exact m₅D _ hi'
  -- The block to continue from back to the IV.
  have rd₆ : s₆.rd = s₀.rd := by rw [d₆.rd, rd₅']
  have wr₆ : s₆.wr = s₀.wr := by rw [d₆.wr, wr₅']
  have ivR₆ : s₆.gpr ivR = P := by rw [d₆.ivK, ivR₅]
  refine WP.block_append (WP.mono (copyN_wp (k := c.bw) (t := .x6) (u := .x6) (rd := ivR) (rs := sb) (od := 0)
    (os := 8 * c.buf) (P := P) (Q := T)
    ⟨by rw [ivR₆]; simp, by rw [d₆.base], Ne.symm i6, by decide, Ne.symm i6, by decide, by decide, by omega_arith,
      by omega_arith, by omega_arith,
      fun w hw => by rw [wr₆]; exact ⟨_, hwP, VG.Offset.contains_base P (by omega_arith) (by omega_arith)⟩,
      fun w hw => by
        rw [rd₆, wr₆, addr_add]
        exact inRd (inS (by omega_arith)),
      dTP.symm, by omega_arith⟩) fun s₇ h₇ => ?_)
  have mem₇ : s₇.mem = over s₆.mem P (8 * c.bw) fun i => s₆.mem (T + BitVec.ofNat 64 i) := h₇.mem
  have f₇ : Frame [⟨P, (8 * c.bw)⟩] s₆.mem s₇.mem := by rw [mem₇]; exact over_frame _ _ _ _
  have b₇ : s₇.gpr sb = B := by rw [h₇.regs _ (by decide) (by decide), d₆.base]
  have hsv : ∀ i < 10, Core.savedRegs.getD i .x19 ≠ sb := by decide
  have hinj : ∀ i < 10, ∀ j < 10, Core.savedRegs.getD i .x19 = Core.savedRegs.getD j .x19 → i = j := by decide
  obtain ⟨s₈, e₈, v₈, -, m₈, rd₈, wr₈⟩ := loads_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .x19) 10 s₇
    b₇ hsv hinj (by omega_arith) (fun i hi' => by
      rw [h₇.rd, h₇.wr, rd₆, wr₆]
      exact inRd (slot_wr hs.wr hN (by omega_arith)))
  refine WP.of_runBlock ⟨s₈, e₈, fun i hi' => ?_, ?_, ?_, ?_, by rw [rd₈, h₇.rd, rd₆],
    by rw [wr₈, h₇.wr, wr₆]⟩
  · rw [v₈ i hi', f₇.readW (Region.contains_self _ _) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact ((sPS.sub_right (slotIn i hi')).symm)) (by decide), d₆.saved i hi', sv₅ i hi']
  · intro i hi
    rw [m₈, f₇.bytes (R := ⟨D, len⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact sPD.symm) hn64 hi]
    exact d₆.data i hi
  · rw [m₈]
    apply List.ext_getElem (by
      rw [fbNextF_length (iv := bytesAt s₀.mem P (8 * c.bw)) (cs.cipher_len k) _ _ (by simp [bytesAt])]
      simp [bytesAt])
    intro u h1 _
    have hu : u < (8 * c.bw) := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [mem₇, over_at hu (by omega_arith), d₆.buf u hu, List.getElem_eq_getD 0]
    rfl
  · rw [m₈]
    refine ((fr₅.mono fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_self).trans
      (d₆.frame.mono fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self)).trans
      (f₇.mono fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

end VG.Proof.Modes.AArch64
