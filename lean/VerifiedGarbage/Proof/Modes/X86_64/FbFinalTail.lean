module

public import VerifiedGarbage.Impl.Modes.X86_64.FbFinal
public import VerifiedGarbage.Proof.Modes.X86_64.Cfb8Steps
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# OFB and CFB of a message's last piece on x86-64: the partial segment

`xorLoop_wp`: from the block at `K` (in `rax`) and the `r > 0` bytes left at
`R` (in `Rd`, their count in `Rl`), the loop of `xorByte` XORs each byte of
the block into the byte at the same offset of `R`, and changes memory only
there.
-/

@[expose] public section

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.WriteBytes (writeW8_apply)

/-- What the loop works on: the block at `K`, the `r` bytes at `R`, the
registers `Rd` and `Rl`. -/
structure XPre (s₀ : State) (K R : Addr) (r : Nat) (Rd Rl : Reg) : Prop where
  pos : 0 < r
  small : r < 2 ^ 64
  fitK : K.toNat + r ≤ 2 ^ 64
  fitR : R.toNat + r ≤ 2 ^ 64
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
