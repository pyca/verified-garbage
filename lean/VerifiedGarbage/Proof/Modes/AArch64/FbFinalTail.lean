module

public import VerifiedGarbage.Impl.Modes.AArch64.FbFinal
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Modes.AArch64.Cfb8Steps
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Modes.AArch64.Xor
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# OFB and CFB of a message's last piece on AArch64: the partial segment

As on x86-64 (`Proof/Modes/X86_64/FbFinalTail.lean`). `xorLoop_wp`: from
the block at `K` (in `x9`) and the `r > 0` bytes left at `R` (in `Rd`, their
count in `Rl`), the loop of `xorByte` XORs each byte of the block into the
byte at the same offset of `R`, and changes memory only there; it ends with
`Rl` zero.
-/

@[expose] public section

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (eorR)
open VG.WriteBytes (writeW8_apply)

/-- What the loop works on: the block at `K`, the `r` bytes at `R`, the
registers `Rd` and `Rl`. -/
structure XPre (s₀ : State) (K R : Addr) (r : Nat) (Rd Rl : Reg) : Prop where
  pos : 0 < r
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

end VG.Proof.Modes.AArch64
