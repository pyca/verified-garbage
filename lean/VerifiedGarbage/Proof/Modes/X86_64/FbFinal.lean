module

public import VerifiedGarbage.Impl.Modes.X86_64.FbFinal
public import VerifiedGarbage.Proof.Modes.X86_64.Cfb8Steps
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Modes.X86_64.FbLoop
public import VerifiedGarbage.Proof.Modes.FbFinal
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Proof.Modes.X86_64.Words
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Modes.X86_64.Fb
import VerifiedGarbage.Proof.Modes.X86_64.Ctr
import VerifiedGarbage.Proof.Modes.X86_64.CbcGroup

/-!
# OFB and CFB of a message's last piece on x86-64, for any core

`fbFinal_wp`: `c.fbFinal mo r`, for a core `c` with `BlockSpec c` whose
cipher is the forward cipher `CIPH_K`, and its arguments in the registers
`r`, replaces the `len` bytes at `D` with the mode's output, byte `i` that
of `fbOut` of its block, under the key `k` that its key arguments give, from
the IV at `P`, and the IV with the block to continue from (`fbNextF`); it
keeps the callee-saved registers, and writes nothing but the scratch
buffer, the data and the IV. `Proof/Modes/FbFinal.lean` states these as the
specification's.
-/

@[expose] public section

/-! ## OFB and CFB of a message's last piece on x86-64: the partial segment

`xorLoop_wp`: from the block at `K` (in `rax`) and the `r > 0` bytes left at
`R` (in `Rd`, their count in `Rl`), the loop of `xorByte` XORs each byte of
the block into the byte at the same offset of `R`, and changes memory only
there.
-/

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.WriteBytes (writeW8_apply)

/-- What the loop works on: the block at `K`, the `r` bytes at `R`, the
registers `Rd` and `Rl`. -/
structure XPre (s₀ : State) (K R : Addr) (r : Nat) (Rd Rl : Reg) : Prop where
  small : r < 2 ^ 64
  disj : Region.Disjoint ⟨K, r⟩ ⟨R, r⟩
  rdK : ∀ q < r, InRegions (s₀.rd ++ s₀.wr) (K + BitVec.ofNat 64 q) 1
  wrR : ∀ q < r, InRegions s₀.wr (R + BitVec.ofNat 64 q) 1
  dl : Rd ≠ Rl
  dRax : Rd ≠ .rax ∧ Rl ≠ .rax
  dR10 : Rd ≠ .r10 ∧ Rl ≠ .r10
  dRcx : Rd ≠ .rcx ∧ Rl ≠ .rcx

/-- The loop, before byte `j`. -/
structure XInv (s₀ : State) (K R : Addr) (r : Nat) (Rd Rl : Reg) (j : Nat) (s : State) : Prop where
  rax : s.gpr .rax = K + BitVec.ofNat 64 j
  dat : s.gpr Rd = R + BitVec.ofNat 64 j
  left : s.gpr Rl = BitVec.ofNat 64 (r - j)
  lt : j < r
  data : ∀ q < r, s.mem (R + BitVec.ofNat 64 q) =
    if q < j then s₀.mem (R + BitVec.ofNat 64 q) ^^^ s₀.mem (K + BitVec.ofNat 64 q) else s₀.mem (R + BitVec.ofNat 64 q)
  frame : Frame [⟨R, r⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  gpr : ∀ x, x ≠ .rax → x ≠ .r10 → x ≠ .rcx → x ≠ Rd → x ≠ Rl → s.gpr x = s₀.gpr x

/-- The loop, done. -/
structure XDone (s₀ : State) (K R : Addr) (r : Nat) (Rd Rl : Reg) (s : State) : Prop where
  zf : s.zf = some true
  data : ∀ q < r, s.mem (R + BitVec.ofNat 64 q) = s₀.mem (R + BitVec.ofNat 64 q) ^^^ s₀.mem (K + BitVec.ofNat 64 q)
  frame : Frame [⟨R, r⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  gpr : ∀ x, x ≠ .rax → x ≠ .r10 → x ≠ .rcx → x ≠ Rd → x ≠ Rl → s.gpr x = s₀.gpr x

theorem one_signExtend : (1 : BitVec 32).signExtend 64 = 1 := by decide

theorem writeByte_frame (m : Mem) (A : Addr) (b : Byte) : Frame [⟨A, 1⟩] m (m.writeW A b) := fun x hx => by
  rw [writeW8_apply, ite_eq_right (fun h => hx _ List.mem_cons_self (by
    subst h; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega))]

/-- One fewer byte left, as a bit vector. -/
theorem ofNat_sub_one {r j : Nat} (hj : j < r) :
    BitVec.ofNat 64 (r - j) - 1 = BitVec.ofNat 64 (r - (j + 1)) := by
  rw [show r - j = (r - (j + 1)) + 1 by omega, BitVec.ofNat_add]
  exact BitVec.add_sub_cancel _ 1#64

theorem xorByte_wp {s₀ : State} {K R : Addr} {r : Nat} {Rd Rl : Reg} (hp : XPre s₀ K R r Rd Rl) {j : Nat} {s : State}
    (hi : XInv s₀ K R r Rd Rl j s) :
    WP isa (.block (xorByte Rd Rl)) s fun s' => XDone s₀ K R r Rd Rl s' ∨
      (s'.zf = some false ∧ XInv s₀ K R r Rd Rl (j + 1) s') := by
  have hj := hi.lt
  have hr := hp.small
  have rK : InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofNat 64 0) 1 := by
    rw [hi.rd, hi.wr, hi.rax, BitVec.add_zero]; exact hp.rdK j hj
  obtain ⟨s₁, e₁, g₁, o₁, m₁, rd₁, wr₁⟩ := ld8_ok s .r10 .rax 0 rK
  have rR : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr Rd + BitVec.ofNat 64 0) 1 := by
    rw [rd₁, wr₁, hi.rd, hi.wr, o₁ _ hp.dR10.1, hi.dat, BitVec.add_zero]
    exact inRd (hp.wrR j hj)
  obtain ⟨s₂, e₂, g₂, o₂, m₂, rd₂, wr₂⟩ := ld8_ok s₁ .rcx Rd 0 rR
  obtain ⟨s₃, e₃, g₃, o₃, m₃, rd₃, wr₃⟩ := xorRR_ok s₂ .rcx .r10
  have wR : InRegions s₃.wr (s₃.gpr Rd + BitVec.ofNat 64 0) 1 := by
    rw [wr₃, wr₂, wr₁, hi.wr, o₃ _ hp.dRcx.1, o₂ _ hp.dRcx.1, o₁ _ hp.dR10.1, hi.dat, BitVec.add_zero]
    exact hp.wrR j hj
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := st8_ok s₃ Rd .rcx 0 wR
  obtain ⟨s₅, e₅, g₅, o₅, m₅, rd₅, wr₅⟩ := addImm_ok s₄ .rax 1
  obtain ⟨s₆, e₆, g₆, o₆, m₆, rd₆, wr₆⟩ := addImm_ok s₅ Rd 1
  obtain ⟨s₇, e₇, g₇, z₇, o₇, m₇, rd₇, wr₇⟩ := subImm_ok s₆ Rl 1
  have run : runBlock isa (xorByte Rd Rl) s = some s₇ := by
    have h : xorByte Rd Rl = [.movzx8 .r10 (at_ .rax 0)] ++ [.movzx8 .rcx (at_ Rd 0)] ++
        [.alu .xor .rcx (.reg .r10)] ++ [.store8 (at_ Rd 0) .rcx] ++ [.alu .add .rax (.imm 1)] ++
        [.alu .add Rd (.imm 1)] ++ [.alu .sub Rl (.imm 1)] := rfl
    rw [h, runBlock_app, runBlock_app, runBlock_app, runBlock_app, runBlock_app, runBlock_app, e₁, Option.bind_some,
      e₂, Option.bind_some, e₃, Option.bind_some, e₄, Option.bind_some, e₅, Option.bind_some, e₆, Option.bind_some, e₇]
  refine WP.of_runBlock ⟨s₇, run, ?_⟩
  -- Registers.
  have gR : ∀ x, x ≠ .rax → x ≠ .r10 → x ≠ .rcx → x ≠ Rd → x ≠ Rl → s₇.gpr x = s.gpr x := fun x h1 h2 h3 h4 h5 => by
    rw [o₇ _ h5, o₆ _ h4, o₅ _ h1, g₄, o₃ _ h3, o₂ _ h3, o₁ _ h2]
  have dat₄ : s₄.gpr Rd = R + BitVec.ofNat 64 j := by
    rw [g₄, o₃ _ hp.dRcx.1, o₂ _ hp.dRcx.1, o₁ _ hp.dR10.1, hi.dat]
  have rax₇ : s₇.gpr .rax = K + BitVec.ofNat 64 (j + 1) := by
    rw [o₇ _ (Ne.symm hp.dRax.2), o₆ _ (Ne.symm hp.dRax.1), g₅, g₄, o₃ _ (by decide), o₂ _ (by decide),
      o₁ _ (by decide), hi.rax, one_signExtend]
    exact VG.Offset.add_add K j 1
  have dat₇ : s₇.gpr Rd = R + BitVec.ofNat 64 (j + 1) := by
    rw [o₇ _ hp.dl, g₆, o₅ _ hp.dRax.1, dat₄, one_signExtend]
    exact VG.Offset.add_add R j 1
  have left₇ : s₇.gpr Rl = BitVec.ofNat 64 (r - (j + 1)) := by
    rw [g₇, o₆ _ (Ne.symm hp.dl), o₅ _ hp.dRax.2, g₄, o₃ _ hp.dRcx.2, o₂ _ hp.dRcx.2, o₁ _ hp.dR10.2, hi.left,
      one_signExtend]
    exact ofNat_sub_one hj
  -- Memory.
  have mem₇ : s₇.mem = s.mem.writeW (R + BitVec.ofNat 64 j)
      (s.mem (R + BitVec.ofNat 64 j) ^^^ s.mem (K + BitVec.ofNat 64 j)) := by
    rw [m₇, m₆, m₅, m₄, g₃, o₃ Rd hp.dRcx.1, g₂, o₂ .r10 (by decide), g₁, o₂ Rd hp.dRcx.1, o₁ Rd hp.dR10.1, m₃, m₂,
      m₁, hi.dat, hi.rax, BitVec.add_zero, BitVec.add_zero, setWidth_xor_byte]
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
  have rd₇ : s₇.rd = s₀.rd := by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd]
  have wr₇ : s₇.wr = s₀.wr := by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr]
  have gpr₇ : ∀ x, x ≠ .rax → x ≠ .r10 → x ≠ .rcx → x ≠ Rd → x ≠ Rl → s₇.gpr x = s₀.gpr x :=
    fun x h1 h2 h3 h4 h5 => by rw [gR x h1 h2 h3 h4 h5, hi.gpr x h1 h2 h3 h4 h5]
  have hz : s₇.zf = some (decide (j + 1 = r)) := by
    rw [z₇, o₆ _ (Ne.symm hp.dl), o₅ _ hp.dRax.2, g₄, o₃ _ hp.dRcx.2, o₂ _ hp.dRcx.2, o₁ _ hp.dR10.2, hi.left,
      one_signExtend, ofNat_sub_one hj]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega : r - (j + 1) < 2 ^ 64)] at this
      have h0 : (0 : BitVec 64).toNat = 0 := rfl
      omega
    · intro h
      rw [show r - (j + 1) = 0 by omega]; rfl
  by_cases hdone : j + 1 = r
  · refine .inl ⟨by rw [hz, decide_eq_true hdone], fun q hq => ?_, fr₇, rd₇, wr₇, gpr₇⟩
    rw [data₇ q hq, ite_eq_left (by omega)]
  · exact .inr ⟨by rw [hz, decide_eq_false hdone], rax₇, dat₇, left₇, by omega, data₇, fr₇, rd₇, wr₇, gpr₇⟩

/-- The XOR loop, from its first byte. -/
theorem xorLoop_wp {s₀ : State} {K R : Addr} {r : Nat} {Rd Rl : Reg} (hp : XPre s₀ K R r Rd Rl)
    (h0 : XInv s₀ K R r Rd Rl 0 s₀) :
    WP isa (.loop (.block (xorByte Rd Rl)) .ne) s₀ (XDone s₀ K R r Rd Rl) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = r - j ∧ XInv s₀ K R r Rd Rl j s) (fun m s hs => ?_) r s₀
    ⟨0, by simp, h0⟩
  obtain ⟨j, rfl, hj⟩ := hs
  refine WP.mono (xorByte_wp hp hj) fun s' h => ?_
  rcases h with d | ⟨z, d⟩
  · exact .inl ⟨by simp [X86_64.eval, d.zf], d⟩
  · exact .inr ⟨by simp [X86_64.eval, z], r - (j + 1), by have := d.lt; have := hj.lt; omega, j + 1, rfl, d⟩

end VG.Proof.Modes.X86_64

/-! ## OFB and CFB of a message's last piece on x86-64, for any core: the loop

`fbSeg_wp`: one segment of `fbFinal`'s loop enciphers its input block `Iⱼ`
in the buffer (`BlockSpec.crypt_wp`), giving `Oⱼ`; if a whole block of the
`len` bytes is left, it makes the block `fbOut` and the buffer `Iⱼ₊₁`
(`fbIn`), as `fb`'s (`fbBlock_wp`); if `r < L` bytes are left, it XORs the
first `r` bytes of `Oⱼ` into them (`xorLoop_wp`), which are then those of
`fbOut j`, and leaves `Oⱼ` in the buffer. Blocks are `L = 8 bw` bytes.
-/

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Modes (FbMode)
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

/-- What the loop works on: the scratch buffer at `B`, the `len` bytes at
`D`. -/
structure FPre (c : Core) (s₀ : State) (B D : Addr) (len : Nat) : Prop where
  scr : ScrIn s₀ B c.ctrSlots
  dat : (⟨D, len⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨D, len⟩ ⟨B, 8 * c.ctrSlots⟩
  fitD : D.toNat + len ≤ 2 ^ 64
  small : len < 2 ^ 64
  stk : StkOk c s₀

/-- The loop, before segment `j`; `m₀` is the memory on entry, `iv` the IV. -/
structure FInvF (cs : BlockSpec c) (mo : FbMode) (s₀ : State) (m₀ : Mem) (B D : Addr) (len : Nat) (k : cs.Key)
    (iv : List Byte) (j : Nat) (s : State) : Prop where
  base : s.gpr sb = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  ready : cs.Ready s B k
  saved : ∀ i < 7, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  dataR : s.gpr c.dataReg = D + BitVec.ofNat 64 (8 * c.bw * j)
  leftR : s.gpr c.leftReg = BitVec.ofNat 64 (len - 8 * c.bw * j)
  lt : 8 * c.bw * j < len
  buf : ∀ u < 8 * c.bw, s.mem (B + BitVec.ofNat 64 (8 * c.buf) + BitVec.ofNat 64 u) =
    (fbIn mo (8 * c.bw) (cs.cipher k) m₀ D iv j).getD u 0
  data : ∀ i < len, s.mem (D + BitVec.ofNat 64 i) =
    if i < 8 * c.bw * j then (fbOut mo (8 * c.bw) (cs.cipher k) m₀ D iv (i / (8 * c.bw))).getD (i % (8 * c.bw)) 0
    else m₀ (D + BitVec.ofNat 64 i)
  frame : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, len⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  xmm : s.xmm Core.ivX = s₀.xmm Core.ivX

/-- The loop, done. -/
structure FDoneF (cs : BlockSpec c) (mo : FbMode) (s₀ : State) (m₀ : Mem) (B D : Addr) (len : Nat) (k : cs.Key)
    (iv : List Byte) (s : State) : Prop where
  base : s.gpr sb = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  saved : ∀ i < 7, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  buf : ∀ u < 8 * c.bw, s.mem (B + BitVec.ofNat 64 (8 * c.buf) + BitVec.ofNat 64 u) =
    (fbNextF mo (8 * c.bw) (cs.cipher k) m₀ D iv len).getD u 0
  data : ∀ i < len, s.mem (D + BitVec.ofNat 64 i) =
    (fbOut mo (8 * c.bw) (cs.cipher k) m₀ D iv (i / (8 * c.bw))).getD (i % (8 * c.bw)) 0
  frame : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, len⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  xmm : s.xmm Core.ivX = s₀.xmm Core.ivX

/-- The partial segment's code is scalar. -/
theorem fbTail_scal (c : Core) :
    scalCode (.seq (.block c.fbTailStart) (.loop (.block (xorByte c.dataReg c.leftReg)) .ne)) = true := rfl

theorem fbSeg_wp (cs : BlockSpec c) (mo : FbMode) {s₀ : State} {m₀ : Mem} {B D : Addr} {len : Nat} {k : cs.Key}
    {iv : List Byte} (hiv : iv.length = 8 * c.bw) (hp : FPre c s₀ B D len) (hsc : KeepsIv c.crypt)
    (hz : (s₀.xmm Core.ivX).extractLsb' 64 64 = 0) {j : Nat} {s : State}
    (hi : FInvF cs mo s₀ m₀ B D len k iv j s) :
    WP isa (c.fbSeg mo) s fun s' => (s'.zf = some true ∧ FDoneF cs mo s₀ m₀ B D len k iv s') ∨
      (s'.zf = some false ∧ FInvF cs mo s₀ m₀ B D len k iv (j + 1) s') := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
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
  obtain ⟨da, -, dc, -, d10, dsb, dsp, -⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨la, -, lc, -, l10, lsb, lsp, -⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  have hlen64 : len ≤ 2 ^ 64 := by omega_arith
  have hsmall := hp.small
  let ciph := cs.cipher k
  let A := D + BitVec.ofNat 64 (8 * c.bw * j)
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  have hwS : (⟨B, 8 * c.ctrSlots⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr.wr
  have hwD : (⟨D, len⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have subT : Region.Sub ⟨T, 8 * c.bw⟩ ⟨B, 8 * c.ctrSlots⟩ :=
    VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega_arith)
  have subTbuf : Region.Sub ⟨T, 8 * c.bw⟩ (blkRegion c B) := Region.sub_prefix hLG
  have subCore : Region.Sub (coreRegion c B) ⟨B, 8 * c.ctrSlots⟩ :=
    Region.sub_prefix (by simp only [Core.ctrSlots]; omega_arith)
  have dDS : ∀ {r : Region}, Region.Sub r ⟨B, 8 * c.ctrSlots⟩ → Region.Disjoint ⟨D, len⟩ r :=
    fun h => hp.sep.sub_right h
  have hw : ∀ w, 8 * c.bw * j + 8 * w = 8 * (c.bw * j + w) := fun w => by rw [Nat.mul_add, Nat.mul_assoc]
  have inT : ∀ w < c.bw, InRegions s.wr (T + BitVec.ofNat 64 (8 * w)) 8 := fun w hw' =>
    ⟨_, hwS, by rw [addr_add]; exact VG.Offset.contains_base B (by simp only [Core.ctrSlots]; omega_arith) (by omega_arith)⟩
  -- Enciphered.
  unfold Core.fbSeg
  refine WP.seq (WP.mono (WP.keepIv hsc (by rw [hi.xmm]; exact hz) (cs.crypt_wp hi.base ⟨hwS, hfit⟩ hi.ready))
    fun s₂ ⟨⟨base₂, rsp₂, dr₂, lr₂, ready₂, f₂, ks₂, rd₂, wr₂⟩, x₂⟩ => ?_)
  rw [hi.rsp] at f₂
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
    f₂.bytes (R := ⟨D, len⟩) (hp.stk.coreFrame_disj (dDS subCore) ⟨_, hp.dat, fun _ h => h⟩) hlen64 hi'
  have mA : ∀ u, 8 * c.bw * j + u < len → s.mem (A + BitVec.ofNat 64 u) = m₀ (A + BitVec.ofNat 64 u) := fun u hu => by
    rw [addr_add, hi.data _ hu, ite_eq_right (by omega_arith)]
  have D₂' : ∀ u, 8 * c.bw * j + u < len → s₂.mem (A + BitVec.ofNat 64 u) = s.mem (A + BitVec.ofNat 64 u) :=
    fun u hu => by rw [addr_add]; exact D₂ _ hu
  -- Whether a whole block is left.
  have hleft : s₂.gpr c.leftReg = BitVec.ofNat 64 (len - 8 * c.bw * j) := by rw [lr₂, hi.leftR]
  obtain ⟨s₃, e₃, cf₃, g₃, m₃, rd₃, wr₃⟩ := cmpImm_ok s₂ c.leftReg (BitVec.ofNat 32 (8 * c.bw)) (K := 8 * c.bw) hleft
    (by omega_arith) (by rw [signExtend_small (by omega_arith)]; simp only [BitVec.toNat_ofNat]; omega_arith)
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  have x₃ : s₃.xmm Core.ivX = s₀.xmm Core.ivX := by rw [runBlock_vec rfl e₃, x₂, hi.xmm]
  have sy₃ : s₃.syms = s₂.syms := runBlock_syms e₃
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₂, hi.rd]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂, hi.wr]
  have data₃ : s₃.gpr c.dataReg = A := by rw [g₃, dr₂, hi.dataR]
  have base₃ : s₃.gpr sb = B := by rw [g₃, base₂]
  -- The slots: none of the core's, nor in the data or the buffer's first block.
  have slotOut : ∀ i < 7, ∀ {R : Region}, (Region.Sub R ⟨D, len⟩ ∨ R = ⟨T, 8 * c.bw⟩ ∨
      R = coreRegion c B) → Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ R := fun i hi7 R hR => by
    rcases hR with h | rfl | rfl
    · exact ((dDS (VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.ctrSlots by
        simp only [Core.ctrSlots]; omega_arith))).sub_left h).symm
    · exact VG.Offset.disjoint B (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
    · exact VG.Offset.disjoint_base B (by omega_arith) (by omega_arith)
  have saved₂ : ∀ i < 7, s₂.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64 :=
    fun i hi7 => by
      rw [← hi.saved i hi7]
      exact f₂.readW (Region.contains_self _ _) (hp.stk.coreFrame_disj (slotOut i hi7 (.inr (.inr rfl)))
        ⟨_, hp.scr.wr, VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.ctrSlots by
          simp only [Core.ctrSlots]; omega_arith)⟩) (by decide)
  have fr₂ : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, len⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s₂.mem :=
    hi.frame.trans (f₂.sub (coreFrame_sub ⟨_, List.mem_cons_self, subCore⟩))
  refine WP.ite (decide (len - 8 * c.bw * j < 8 * c.bw)) (by simp [X86_64.eval, cf₃]) (fun hb => ?_) (fun hb => ?_)
  · -- A partial segment: `r` bytes.
    have hb' : len - 8 * c.bw * j < 8 * c.bw := by simpa using hb
    let r := len - 8 * c.bw * j
    have hr0 : 0 < r := by omega_arith
    have hdiv : len / (8 * c.bw) = j := by
      rw [show len = 8 * c.bw * j + r by omega_arith]; exact idx_div hb'
    have hmod : len % (8 * c.bw) = r := by
      rw [show len = 8 * c.bw * j + r by omega_arith]; exact idx_mod hb'
    obtain ⟨s₄a, e₄a, a₄a, o₄a, m₄a, rd₄a, wr₄a⟩ := movR_ok s₃ .rax sb
    obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := addImm_ok s₄a .rax (BitVec.ofNat 32 (8 * c.buf))
    have run₄ : runBlock isa c.fbTailStart s₃ = some s₄ := by
      rw [Core.fbTailStart, show ([.mov .rax (.reg sb), .alu .add .rax (.imm (BitVec.ofNat 32 (8 * c.buf)))] :
        List Instr) = [movR .rax sb] ++ [.alu .add .rax (.imm (BitVec.ofNat 32 (8 * c.buf)))] from rfl,
        runBlock_app, e₄a, Option.bind_some, e₄]
    have rax₄ : s₄.gpr .rax = T := by rw [a₄, a₄a, base₃, signExtend_small (by omega_arith)]
    have g₄ : ∀ x, x ≠ .rax → s₄.gpr x = s₃.gpr x := fun x h => by rw [o₄ x h, o₄a x h]
    have mem₄ : s₄.mem = s₂.mem := by rw [m₄, m₄a, m₃]
    have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rd₄a, rd₃']
    have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₄a, wr₃']
    have subTr : Region.Sub ⟨T, r⟩ ⟨T, 8 * c.bw⟩ := Region.sub_prefix (by omega_arith)
    have subAr : Region.Sub ⟨A, r⟩ ⟨D, len⟩ := VG.Offset.sub_base D (by omega_arith)
    have hxp : XPre s₄ T A r c.dataReg c.leftReg :=
      { small := by omega_arith
        disj := ((dDS subT).sub_left subAr).sub_right subTr |>.symm
        rdK := fun q hq => by
          rw [rd₄', wr₄']
          exact inRd ⟨_, hp.scr.wr, by
            rw [addr_add]; exact VG.Offset.contains_base B (by simp only [Core.ctrSlots]; omega_arith) (by omega_arith)⟩
        wrR := fun q hq => by
          rw [wr₄']
          exact ⟨_, hp.dat, by rw [addr_add]; exact VG.Offset.contains_base D (by omega_arith) (by omega_arith)⟩
        dl := hdl
        dRax := ⟨da, la⟩
        dR10 := ⟨d10, l10⟩
        dRcx := ⟨dc, lc⟩ }
    have hx0 : XInv s₄ T A r c.dataReg c.leftReg 0 s₄ :=
      { rax := by rw [rax₄]; simp
        dat := by rw [g₄ _ da, data₃]; simp
        left := by rw [g₄ _ la, g₃, hleft, Nat.sub_zero]
        lt := hr0
        data := fun q hq => by rw [ite_eq_right (Nat.not_lt_zero _)]
        frame := Frame.refl _ _
        rd := rfl
        wr := rfl
        gpr := fun _ _ _ _ _ _ => rfl }
    refine WP.mono (WP.vecKeep (fbTail_scal c) (WP.seq (WP.of_runBlock ⟨s₄, run₄, xorLoop_wp hxp hx0⟩)))
      fun s₅ ⟨d₅, x₅, _⟩ => .inl ⟨d₅.zf, ?_⟩
    have f₅ : Frame [⟨A, r⟩] s₂.mem s₅.mem := by rw [← mem₄]; exact d₅.frame
    have g₅ : ∀ x, x ≠ .rax → x ≠ .r10 → x ≠ .rcx → x ≠ c.dataReg → x ≠ c.leftReg → s₅.gpr x = s₂.gpr x :=
      fun x h1 h2 h3 h4 h5 => by rw [d₅.gpr x h1 h2 h3 h4 h5, g₄ x h1, g₃]
    have kT : ∀ u < 8 * c.bw, s₅.mem (T + BitVec.ofNat 64 u) = s₂.mem (T + BitVec.ofNat 64 u) := fun u hu =>
      f₅.bytes (R := ⟨T, 8 * c.bw⟩) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact ((dDS subT).sub_left subAr).symm) (show 8 * c.bw ≤ 2 ^ 64 by omega_arith) hu
    refine ⟨by rw [g₅ _ (by decide) (by decide) (by decide) (Ne.symm dsb) (Ne.symm lsb), base₂],
      by rw [g₅ _ (by decide) (by decide) (by decide) (Ne.symm dsp) (Ne.symm lsp), rsp₂, hi.rsp],
      fun i hi7 => ?_, fun u hu => ?_, fun i hi' => ?_, ?_, by rw [d₅.rd, rd₄'], by rw [d₅.wr, wr₄'],
      by rw [x₅]; exact x₃⟩
    · rw [← saved₂ i hi7]
      exact f₅.readW (Region.contains_self _ _) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact slotOut i hi7 (.inl subAr)) (by decide)
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
    have hjl' : 8 * (c.bw * j) + 8 * c.bw ≤ len := by rw [← Nat.mul_assoc]; exact hjl
    have subA : Region.Sub ⟨A, 8 * c.bw⟩ ⟨D, len⟩ := VG.Offset.sub_base D hjl
    have dAT : Region.Disjoint ⟨A, 8 * c.bw⟩ ⟨T, 8 * c.bw⟩ := (dDS subT).sub_left subA
    have inA : ∀ w < c.bw, InRegions s.wr (A + BitVec.ofNat 64 (8 * w)) 8 := fun w hw' =>
      ⟨_, hwD, by rw [addr_add, hw]; exact VG.Offset.contains_base D (by omega_arith) (by omega_arith)⟩
    refine WP.block_append (WP.mono_syms (WP.vecKeep (fbOp_scal c mo) (fbOp_wp mo data₃ (by rw [base₃]) da
      (fun w hw' => by rw [wr₃, wr₂]; exact inA w hw') (fun w hw' => by rw [wr₃, wr₂]; exact inT w hw') dAT
      (by omega_arith))) fun s₃a ⟨⟨g₃a, rd₃a, wr₃a, mA₃, mT₃, f₃a⟩, x₃a, _⟩ sy₃a => ?_)
    obtain ⟨s₃b, e₃b, a₃b, o₃b, m₃b, rd₃b, wr₃b⟩ := addImm_ok s₃a c.dataReg (BitVec.ofNat 32 (8 * c.bw))
    obtain ⟨s₄, e₄, l₄, z₄, o₄, m₄, rd₄, wr₄⟩ := subImm_ok s₃b c.leftReg (BitVec.ofNat 32 (8 * c.bw))
    refine WP.of_runBlock ⟨s₄, by
      rw [Core.fbNextBytes, show ([.alu .add c.dataReg (.imm (BitVec.ofNat 32 (8 * c.bw))),
        .alu .sub c.leftReg (.imm (BitVec.ofNat 32 (8 * c.bw)))] : List Instr) =
        [.alu .add c.dataReg (.imm (BitVec.ofNat 32 (8 * c.bw)))] ++
          [.alu .sub c.leftReg (.imm (BitVec.ofNat 32 (8 * c.bw)))] from rfl,
        runBlock_app, e₃b, Option.bind_some, e₄], ?_⟩
    have keep₄ : ∀ x, x ≠ .rax → x ≠ c.dataReg → x ≠ c.leftReg → s₄.gpr x = s₂.gpr x := fun x h1 h2 h3 => by
      rw [o₄ x h3, o₃b x h2, g₃a x h1, g₃]
    have left₃ : s₃b.gpr c.leftReg = BitVec.ofNat 64 (len - 8 * c.bw * j) := by
      rw [o₃b _ (Ne.symm hdl), g₃a _ la, g₃, hleft]
    have hsx : (BitVec.ofNat 32 (8 * c.bw)).signExtend 64 = BitVec.ofNat 64 (8 * c.bw) := signExtend_small (by omega_arith)
    have left₄ : s₄.gpr c.leftReg = BitVec.ofNat 64 (len - 8 * c.bw * (j + 1)) := by
      rw [l₄, left₃, hsx, VG.Offset.ofNat_sub_ofNat hb', hj1, Nat.sub_sub]
    have hz₄ : s₄.zf = some (decide (8 * c.bw * (j + 1) = len)) := by
      rw [z₄, left₃, hsx, VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by omega_arith)]
      simp only [Option.some.injEq, decide_eq_decide]; omega_arith
    have hAL : A + BitVec.ofNat 64 (8 * c.bw) = D + BitVec.ofNat 64 (8 * c.bw * (j + 1)) := by rw [addr_add, hj1]
    have data₄ : s₄.gpr c.dataReg = D + BitVec.ofNat 64 (8 * c.bw * (j + 1)) := by
      rw [o₄ _ hdl, a₃b, g₃a _ da, data₃, hsx, hAL]
    have mem₄ : s₄.mem = s₃a.mem := by rw [m₄, m₃b]
    have xmm₄ : s₄.xmm Core.ivX = s₀.xmm Core.ivX := by
      rw [runBlock_vec rfl e₄, runBlock_vec rfl e₃b, x₃a, x₃]
    have base₄ : s₄.gpr sb = B := by rw [keep₄ _ (by decide) (Ne.symm dsb) (Ne.symm lsb), base₂]
    have rsp₄ : s₄.gpr .rsp = s₀.gpr .rsp := by
      rw [keep₄ _ (by decide) (Ne.symm dsp) (Ne.symm lsp), rsp₂, hi.rsp]
    have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rd₃b, rd₃a, rd₃']
    have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₃b, wr₃a, wr₃']
    have f₃ : Frame [⟨A, 8 * c.bw⟩, ⟨T, 8 * c.bw⟩] s₂.mem s₄.mem := by rw [mem₄, ← m₃]; exact f₃a
    have saved₄ : ∀ i < 7, s₄.mem.readW (wordAddr B (c.slots + i)) 64 =
        s₀.mem.readW (wordAddr B (c.slots + i)) 64 := fun i hi7 => by
      rw [← saved₂ i hi7]
      exact f₃.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact slotOut i hi7 (.inl subA)
        · exact slotOut i hi7 (.inr (.inl rfl))) (by decide)
    have fr₄ : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, len⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s₄.mem :=
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
      obtain ⟨h1, -, -, -, -, h6, h7⟩ := of_not_modeRegs hr; exact keep₄ r h1 h6 h7
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
    · refine .inl ⟨by rw [hz₄, decide_eq_true hdone], base₄, rsp₄, saved₄, fun u hu => ?_,
        fun i hi' => by rw [data₄' i hi', ite_eq_left (by omega_arith)], fr₄, rd₄', wr₄', xmm₄⟩
      have hmod : len % (8 * c.bw) = 0 := by rw [← hdone]; exact Nat.mul_mod_right _ _
      have hdiv : len / (8 * c.bw) = j + 1 := by rw [← hdone]; exact Nat.mul_div_cancel_left _ hL0
      rw [buf₄ u hu, fbNextF, ite_eq_left hmod, hdiv]
    · exact .inr ⟨by rw [hz₄, decide_eq_false hdone], base₄, rsp₄, ready₄, saved₄, data₄, left₄, by omega_arith,
        buf₄, data₄', fr₄, rd₄', wr₄', xmm₄⟩

/-- The loop. -/
theorem fbFinalLoop_wp (cs : BlockSpec c) (mo : FbMode) {s₀ : State} {m₀ : Mem} {B D : Addr} {len : Nat}
    {k : cs.Key} {iv : List Byte} (hiv : iv.length = 8 * c.bw) (hp : FPre c s₀ B D len) (hsc : KeepsIv c.crypt)
    (hz : (s₀.xmm Core.ivX).extractLsb' 64 64 = 0) {s : State} (hi : FInvF cs mo s₀ m₀ B D len k iv 0 s) :
    WP isa (.loop (c.fbSeg mo) .ne) s (FDoneF cs mo s₀ m₀ B D len k iv) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = len - 8 * c.bw * j ∧ FInvF cs mo s₀ m₀ B D len k iv j s)
    (fun m s hs => ?_) len s ⟨0, by simp, hi⟩
  obtain ⟨j, rfl, hj⟩ := hs
  have hbw0 := cs.layout.bw_pos
  refine WP.mono (fbSeg_wp cs mo hiv hp hsc hz hj) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨by simp [X86_64.eval, z], d⟩
  · exact .inr ⟨by simp [X86_64.eval, z], len - 8 * c.bw * (j + 1), by
      have := d.lt; have := hj.lt; rw [Nat.mul_succ]; omega, j + 1, rfl, d⟩

end VG.Proof.Modes.X86_64


namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Modes (FbMode)
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

theorem fbFinal_wp (cs : BlockSpec c) (mo : FbMode) {r : CtrRegs} (hr : RegsOk r) (hdn : c.dataReg ≠ r.n) {s₀ : State}
    {B P D : Addr} {len : Nat} {k : cs.Key} (hB : s₀.gpr r.scr = B) (hP : s₀.gpr r.ctr = P) (hD : s₀.gpr r.data = D)
    (hn : (s₀.gpr r.n).toNat = len) (hs : ScrIn s₀ B c.ctrSlots) (hwP : (⟨P, 8 * c.bw⟩ : Region) ∈ s₀.wr)
    (hwD : (⟨D, len⟩ : Region) ∈ s₀.wr) (sPS : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨B, 8 * c.ctrSlots⟩)
    (sDS : Region.Disjoint ⟨D, len⟩ ⟨B, 8 * c.ctrSlots⟩)
    (sPD : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨D, len⟩)
    (fitD : D.toNat + len ≤ 2 ^ 64) (hk : cs.KeyArgs s₀ [⟨B, 8 * c.ctrSlots⟩] k)
    (hsc : KeepsIv c.prepare ∧ KeepsIv c.crypt) (hstk : StkOk c s₀ := by exact Or.inl rfl) :
    WP isa (c.fbFinal mo r) s₀ fun s' => (∀ x ∈ calleeSaved, s'.gpr x = s₀.gpr x) ∧
      (∀ i < len, s'.mem (D + BitVec.ofNat 64 i) =
        (fbOut mo (8 * c.bw) (cs.cipher k) s₀.mem D (bytesAt s₀.mem P (8 * c.bw)) (i / (8 * c.bw))).getD
          (i % (8 * c.bw)) 0) ∧
      bytesAt s'.mem P (8 * c.bw) = fbNextF mo (8 * c.bw) (cs.cipher k) s₀.mem D (bytesAt s₀.mem P (8 * c.bw)) len ∧
      Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, len⟩, ⟨P, 8 * c.bw⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s'.mem ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hG0 := hL.G_pos
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hL0 : 0 < 8 * c.bw := by omega_arith
  have hLG : 8 * c.bw ≤ 8 * c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  have hGb : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  have hn64 : len ≤ 2 ^ 64 := by omega_arith
  have hsmall : len < 2 ^ 64 := by rw [← hn]; exact (s₀.gpr r.n).isLt
  have hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega_arith
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨da, db, -, dbp, -, dsb, dsp, dk⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨la, lb, -, lbp, -, lsb, lsp, lk⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  let S : Region := ⟨B, 8 * c.ctrSlots⟩
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  have subMode : Region.Sub (modeRegion c B) S := VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega_arith)
  have subCore : Region.Sub (coreRegion c B) S := Region.sub_prefix (by simp only [Core.ctrSlots]; omega_arith)
  have subT : Region.Sub ⟨T, (8 * c.bw)⟩ S := VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega_arith)
  have subTbuf : Region.Sub ⟨T, (8 * c.bw)⟩ (blkRegion c B) := Region.sub_prefix hLG
  have subTcore : Region.Sub ⟨T, (8 * c.bw)⟩ (coreRegion c B) := VG.Offset.sub_base B (by omega_arith)
  have dTP : Region.Disjoint ⟨T, (8 * c.bw)⟩ ⟨P, (8 * c.bw)⟩ := (sPS.sub_right subT).symm
  have dDcore : ∀ x ∈ coreFrame c B (s₀.gpr .rsp), Region.Disjoint ⟨D, len⟩ x :=
    hstk.coreFrame_disj (sDS.sub_right subCore) ⟨_, hwD, fun _ h => h⟩
  have dPcore : ∀ x ∈ coreFrame c B (s₀.gpr .rsp), Region.Disjoint ⟨P, (8 * c.bw)⟩ x :=
    hstk.coreFrame_disj (sPS.sub_right subCore) ⟨_, hwP, fun _ h => h⟩
  have inS : ∀ {d m : Nat}, d + m ≤ 8 * c.ctrSlots → InRegions s₀.wr (B + BitVec.ofNat 64 d) m := fun h =>
    ⟨_, hs.wr, VG.Offset.contains_base B h (by omega_arith)⟩
  -- The mode's 7 slots: none of the core's, nor in the data or at the IV.
  have slotIn : ∀ i < 7, Region.Sub ⟨wordAddr B (c.slots + i), 8⟩ S := fun i hi =>
    VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega_arith)
  have slotCore : ∀ i < 7, Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ (coreRegion c B) := fun i hi =>
    VG.Offset.disjoint_base B (by omega_arith) (by omega_arith)
  have slotT : ∀ i < 7, Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ ⟨T, (8 * c.bw)⟩ := fun i hi =>
    VG.Offset.disjoint B (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  -- The entry.
  obtain ⟨sE, eE, bE, svE, fE, gE, rdE, wrE⟩ := entry_ok hsm hroom s₀ hB hs
  obtain ⟨sS, eS, xS, gS, mS, rdS, wrS⟩ := movqX_ok sE Core.ivX r.ctr
  obtain ⟨sA, eA, drA, lrA, gA, mA, rdA, wrA⟩ := ctrArgs_ok sS r hdn hdl
  unfold Core.fbFinal
  refine WP.seq (WP.of_runBlock ⟨sA, by
    rw [Core.fbEntry, runBlock_app, runBlock_app, eE, Option.bind_some, eS, Option.bind_some, eA], ?_⟩)
  have gA' : ∀ x, x ≠ sb → x ≠ c.dataReg → x ≠ c.leftReg → sA.gpr x = s₀.gpr x := fun x h1 h2 h3 => by
    rw [gA x h2 h3, gS, gE x h1]
  have bA : sA.gpr sb = B := by rw [gA _ (Ne.symm dsb) (Ne.symm lsb), gS, bE]
  have rdA' : sA.rd = s₀.rd := by rw [rdA, rdS, rdE]
  have wrA' : sA.wr = s₀.wr := by rw [wrA, wrS, wrE]
  have fA : Frame [S] s₀.mem sA.mem := by
    rw [mA, mS]
    exact fE.sub fun x hx => ⟨S, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hx; subst hx; exact subMode⟩
  -- The callee-saved registers in their slots, and the IV's address in `ivX`.
  let sv : Nat → BitVec 64 := fun i => s₀.gpr (Core.savedRegs.getD i .rbx)
  have svA : ∀ i < 6, sA.mem.readW (wordAddr B (c.slots + i)) 64 = sv i := fun i hi => by
    rw [mA, mS, svE i hi]
  have xA : sA.xmm Core.ivX = (0 : BitVec 64) ++ P := by
    rw [runBlock_vec rfl eA, xS, gE _ hr.ctr.1, hP]
  have kr := keyRegs_ne cs.keyRegs_ok
  have hkA : cs.KeyArgs sA [S] k :=
    cs.keyArgs_congr hk (fun x hx => gA' x (kr x hx).1 (fun e => dk (e ▸ hx)) (fun e => lk (e ▸ hx))) rdA' wrA'
      (by rw [runBlock_syms eA, runBlock_syms eS, runBlock_syms eE]) fA
  -- The key.
  refine WP.seq (WP.mono (WP.keepIv hsc.1 (by rw [xA]; exact hi_zero_append _) (cs.prepare_wp bA ⟨by rw [wrA']; exact hs.wr, hs.fit⟩ List.mem_cons_self hkA))
    fun s₄ ⟨⟨ready₄, b₄, rsp₄, dr₄, lr₄, f₄, rd₄, wr₄⟩, x₄⟩ => ?_)
  rw [show sA.gpr .rsp = s₀.gpr .rsp from gA' _ (by decide) (Ne.symm dsp) (Ne.symm lsp)] at f₄
  have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rdA']
  have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wrA']
  have sv₄ : ∀ i < 6, s₄.mem.readW (wordAddr B (c.slots + i)) 64 = sv i := fun i hi => by
    rw [← svA i hi]
    exact f₄.readW (Region.contains_self _ _)
      (hstk.coreFrame_disj (slotCore i (by omega_arith)) ⟨_, hs.wr, slotIn i (by omega_arith)⟩) (by decide)
  -- The IV to the buffer.
  obtain ⟨s₅a, e₅a, ax₅a, o₅a, m₅a, rd₅a, wr₅a, x₅a⟩ := movqR_ok s₄ .rax Core.ivX
  have ax₅ : s₅a.gpr .rax = P := by rw [ax₅a, x₄, xA, extract_zero_append]
  refine WP.seq (WP.block_append (WP.block_append (WP.of_runBlock ⟨s₅a, e₅a, WP.mono_syms (WP.vecKeep
    (c := .block ((List.range c.bw).flatMap (copyW .rbp sb .rax (8 * c.buf) 0)))
    (flatMap_scal (copyW_scal _ _ _ _ _) _) (copyN_wp (k := c.bw)
    (t := .rbp) (rd := sb) (rs := .rax) (od := 8 * c.buf) (os := 0) (P := T) (Q := P)
    ⟨by rw [o₅a _ (by decide), b₄], by rw [ax₅]; simp, by decide, by decide,
      fun w hw => by rw [wr₅a, wr₄', addr_add]; exact inS (by simp only [Core.ctrSlots]; omega_arith),
      fun w hw => by
        rw [rd₅a, wr₅a, rd₄', wr₄']
        exact inRd ⟨_, hwP, VG.Offset.contains_base P (by omega_arith) (by omega_arith)⟩,
      dTP, by omega_arith⟩)) fun s₅b ⟨h₅b, x₅b, _⟩ sy₅b => ?_⟩)))
  obtain ⟨s₅, e₅, z₅, g₅, m₅, rd₅, wr₅⟩ := testSelf_ok s₅b c.leftReg
  refine WP.of_runBlock ⟨s₅, e₅, ?_⟩
  have x₅ : s₅.xmm Core.ivX = (0 : BitVec 64) ++ P := by rw [runBlock_vec rfl e₅, x₅b, x₅a, x₄, xA]
  have g₅' : ∀ x, x ≠ .rax → x ≠ .rbp → s₅.gpr x = s₄.gpr x := fun x h1 h2 => by
    rw [g₅, h₅b.regs x h2, o₅a x h1]
  have mem₅ : s₅.mem = over s₄.mem T (8 * c.bw) fun i => s₄.mem (P + BitVec.ofNat 64 i) := by
    rw [m₅, h₅b.mem, m₅a]
  have f₅ : Frame [⟨T, (8 * c.bw)⟩] s₄.mem s₅.mem := by rw [mem₅]; exact over_frame _ _ _ _
  have b₅ : s₅.gpr sb = B := by rw [g₅' _ (by decide) (by decide), b₄]
  have rsp₅ : s₅.gpr .rsp = s₀.gpr .rsp := by
    rw [g₅' _ (by decide) (by decide), rsp₄, gA' _ (by decide) (Ne.symm dsp) (Ne.symm lsp)]
  have rd₅' : s₅.rd = s₀.rd := by rw [rd₅, h₅b.rd, rd₅a, rd₄']
  have wr₅' : s₅.wr = s₀.wr := by rw [wr₅, h₅b.wr, wr₅a, wr₄']
  have left₅ : s₅.gpr c.leftReg = s₀.gpr r.n := by
    rw [g₅' _ la lbp, lr₄, lrA, gS, gE _ hr.n.1]
  have hz₅ : s₅.zf = some (decide (len = 0)) := by
    rw [z₅, ← g₅, left₅]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  have sv₅ : ∀ i < 6, s₅.mem.readW (wordAddr B (c.slots + i)) 64 = sv i := fun i hi => by
    rw [← sv₄ i hi]
    exact f₅.readW (Region.contains_self _ _) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact slotT i (by omega_arith)) (by decide)
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
  have hiv : iv.length = (8 * c.bw) := by simp [iv, bytesAt]
  have buf₅ : ∀ u < (8 * c.bw), s₅.mem (B + BitVec.ofNat 64 (8 * c.buf) + BitVec.ofNat 64 u) =
      (fbIn mo (8 * c.bw) (cs.cipher k) s₀.mem D iv 0).getD u 0 := fun u hu => by
    rw [mem₅, over_at hu (by omega_arith), m₄P u hu, fbIn, bytesAt_getD _ _ hu]
  have hp : FPre c s₅ B D len :=
    ⟨⟨by rw [wr₅']; exact hs.wr, hs.fit⟩, by rw [wr₅']; exact hwD, sDS, fitD, hsmall, hstk.congr rsp₅ wr₅'⟩
  have fr₅ : Frame (S :: stkList c (s₀.gpr .rsp)) s₀.mem s₅.mem :=
    (fA.mono fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_self).trans
      ((f₄.sub fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨S, List.mem_cons_self, subCore⟩
        · exact ⟨x, List.mem_cons_of_mem _ hx, fun _ h => h⟩).trans
      (f₅.sub fun x hx => ⟨S, List.mem_cons_self, by
        simp only [List.mem_singleton] at hx; subst hx; exact subT⟩))
  -- The blocks.
  refine WP.seq (WP.mono (M := isa) (Q := FDoneF cs mo s₅ s₀.mem B D len k iv)
    (WP.ite (decide (len = 0)) (by simp [X86_64.eval, hz₅]) (fun h0 => ?_) (fun h0 => ?_)) fun s₆ d₆ => ?_)
  · have hn0 : len = 0 := by simpa using h0
    refine WP.block_nil ⟨b₅, rfl, fun _ _ => rfl, fun u hu => ?_, fun i hi' => by omega_arith, Frame.refl _ _,
      rfl, rfl, rfl⟩
    rw [hn0, fbNextF, ite_eq_left (Nat.zero_mod _), Nat.zero_div]; exact buf₅ u hu
  · have hn0 : len ≠ 0 := by simpa using h0
    refine fbFinalLoop_wp cs mo hiv hp hsc.2 (by rw [x₅]; exact hi_zero_append _) ⟨b₅, rfl, cs.ready_frame ready₄ f₅ (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact .inr subTbuf)
        ⟨fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; exact ⟨S, by rw [wr₄']; exact hs.wr, subT⟩,
          by rw [rd₅, h₅b.rd, rd₅a], by rw [wr₅, h₅b.wr, wr₅a],
          by rw [runBlock_syms e₅, sy₅b, runBlock_syms e₅a]⟩
        (fun x hx => by obtain ⟨h1, -, -, h4, -, -, -⟩ := of_not_modeRegs hx; exact g₅' x h1 h4),
      fun _ _ => rfl, ?_, ?_, by omega_arith, buf₅, fun i hi' => ?_, Frame.refl _ _, rfl, rfl, rfl⟩
    · rw [g₅' _ da dbp, dr₄, drA, gS, gE _ hr.data.1, hD]; simp
    · rw [left₅, Nat.mul_zero, Nat.sub_zero, ← hn]; simp
    · rw [ite_eq_right (by omega_arith)]; exact m₅D _ hi'
  -- The block to continue from back to the IV.
  have hsv7 : ∀ i < 6, s₆.mem.readW (wordAddr B (c.slots + i)) 64 = sv i := fun i hi => by
    rw [d₆.saved i (by omega_arith), sv₅ i hi]
  have rd₆ : s₆.rd = s₀.rd := by rw [d₆.rd, rd₅']
  have wr₆ : s₆.wr = s₀.wr := by rw [d₆.wr, wr₅']
  obtain ⟨s₇a, e₇a, ax₇a, o₇a, m₇a, rd₇a, wr₇a, -⟩ := movqR_ok s₆ .rax Core.ivX
  have ax₇ : s₇a.gpr .rax = P := by rw [ax₇a, d₆.xmm, x₅, extract_zero_append]
  refine WP.block_append (WP.block_append (WP.of_runBlock ⟨s₇a, e₇a, WP.mono (copyN_wp (k := c.bw)
    (t := .rbp) (rd := .rax) (rs := sb) (od := 0) (os := 8 * c.buf) (P := P) (Q := T)
    ⟨by rw [ax₇]; simp, by rw [o₇a _ (by decide), d₆.base], by decide, by decide,
      fun w hw => by rw [wr₇a, wr₆]; exact ⟨_, hwP, VG.Offset.contains_base P (by omega_arith) (by omega_arith)⟩,
      fun w hw => by
        rw [rd₇a, wr₇a, rd₆, wr₆, addr_add]
        exact inRd (inS (by simp only [Core.ctrSlots]; omega_arith)),
      dTP.symm, by omega_arith⟩) fun s₇ h₇ => ?_⟩))
  have mem₇ : s₇.mem = over s₆.mem P (8 * c.bw) fun i => s₆.mem (T + BitVec.ofNat 64 i) := by rw [h₇.mem, m₇a]
  have f₇ : Frame [⟨P, (8 * c.bw)⟩] s₆.mem s₇.mem := by rw [mem₇]; exact over_frame _ _ _ _
  have b₇ : s₇.gpr sb = B := by rw [h₇.regs _ (by decide), o₇a _ (by decide), d₆.base]
  have hsv : ∀ i < 6, Core.savedRegs.getD i .rbx ≠ sb := by decide
  have hinj : ∀ i < 6, ∀ j < 6, Core.savedRegs.getD i .rbx = Core.savedRegs.getD j .rbx → i = j := by decide
  obtain ⟨s₈, e₈, v₈, o₈, m₈, rd₈, wr₈⟩ := loads_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .rbx) 6 s₇
    b₇ hsv hinj (fun i hi' => by
      rw [h₇.rd, h₇.wr, rd₇a, wr₇a, rd₆, wr₆]
      exact inRd (inS (by simp only [Core.ctrSlots]; omega_arith)))
  refine WP.of_runBlock ⟨s₈, e₈, fun x hx => ?_, ?_, ?_, ?_, by rw [rd₈, h₇.rd, rd₇a, rd₆],
    by rw [wr₈, h₇.wr, wr₇a, wr₆]⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hx
    have hsaved : ∀ i < 6, s₈.gpr (Core.savedRegs.getD i .rbx) = s₀.gpr (Core.savedRegs.getD i .rbx) :=
      fun i hi' => by
        rw [v₈ i hi', f₇.readW (Region.contains_self _ _) (fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx
          exact ((sPS.sub_right (slotIn i (by omega_arith))).symm)) (by decide), hsv7 i (by omega_arith)]
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsaved 0 (by decide)
    · exact hsaved 1 (by decide)
    · rw [o₈ _ (fun i hi' => by revert i; decide), h₇.regs _ (by decide), o₇a _ (by decide), d₆.rsp, rsp₅]
    · exact hsaved 2 (by decide)
    · exact hsaved 3 (by decide)
    · exact hsaved 4 (by decide)
    · exact hsaved 5 (by decide)
  · intro i hi
    rw [m₈, f₇.bytes (R := ⟨D, len⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact sPD.symm) hn64 hi]
    exact d₆.data i hi
  · rw [m₈]
    apply List.ext_getElem (by
      rw [fbNextF_length (iv := bytesAt s₀.mem P (8 * c.bw)) (cs.cipher_len k) _ _ (by simp [bytesAt])]; simp [bytesAt])
    intro u h1 _
    have hu : u < (8 * c.bw) := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [mem₇, over_at hu (by omega_arith), d₆.buf u hu, List.getElem_eq_getD 0]
    rfl
  · rw [m₈]
    refine ((fr₅.mono fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_cons_self
        · exact List.mem_append_right _ hx).trans
      (d₆.frame.mono fun x hx => by
        rw [rsp₅] at hx
        rcases List.mem_append.mp hx with hx | hx
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ List.mem_cons_self
        · exact List.mem_append_right _ hx)).trans
      (f₇.mono fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

end VG.Proof.Modes.X86_64
