module

public import VerifiedGarbage.Proof.Ed448.X86.VerifyChecks
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.X86.ScalarStep
import VerifiedGarbage.Proof.X448.X86.Decode
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.X448.X86.Columns
import VerifiedGarbage.Proof.X448.X86.Freeze
import VerifiedGarbage.Proof.X25519.X86.Arith
import VerifiedGarbage.Proof.Framework.X86.Reduce
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Ed448 verification's equation on x86 (32-bit): `S < L`

`sCheck_ok`: the fourteen words of `S`'s low 448 bits plus those of `2^448 - L`
carry out of 448 bits exactly when they are at least `L`; with byte 56,
`BAD |= 0` exactly when `S < L`.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448.X86 VG.Proof.X448.X86
open VG.Impl.X448.X86 (slot X2 ACC ld st at_)
open VG.Proof.X25519.X86 (num num_succ num_congr num_lt PassRel)

/-- The words of the 56 bytes at `q`. -/
abbrev strW (m : Mem) (q : Addr) (k : Nat) : Nat := (m.readW (off q (4 * k)) 32).toNat

/-- The number of 57 bytes: the words of the first 56 and the last byte. -/
theorem decodeLE_bytes57 (m : Mem) (q : Addr) :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m q 57) =
      num (strW m q) 14 + 256 ^ 56 * (m (q + BitVec.ofNat 64 56)).toNat := by
  rw [Limbs16.bytesAt_57 m q, Proof.Ed448.decodeLE_append, Proof.Ed448.decodeLE_eq, Proof.Ed448.decodeLE_eq,
    show (56 : Nat) = 4 * 14 from rfl, bytes_num m q 14, Proof.X448.length_bytesAt]
  simp only [Proof.X25519.leNum, Nat.mul_zero, Nat.add_zero]

/-- The words of `2^448 - L`. -/
theorem num_kWord : num kWord 14 = 2 ^ 448 - Spec.Ed448.L := by decide +kernel

theorem kWord_lt : ∀ k < 14, kWord k < 2 ^ 32 := by decide +kernel

/-- The address of byte `src + j` at `esi`. -/
theorem ea_esi {s : State} {q : Addr} {src : Nat} (hq : (s.gpr .esi).setWidth 64 + BitVec.ofNat 64 src = q)
    {j : Nat} (hfit : (s.gpr .esi).toNat + src + j < 2 ^ 32) :
    s.ea (at_ .esi (src + j)) = q + BitVec.ofNat 64 j := by
  change addr (s.gpr .esi) (src + j) = _
  rw [addr_eq (by omega_using [hfit]), ← hq, Offset.add_add]

/-- One word of the sum: `mov`, then `adc` of an immediate. -/
theorem sLimb_ok {s : State} {q : Addr} (hq : (s.gpr .esi).setWidth 64 + BitVec.ofNat 64 57 = q)
    (hfit : (s.gpr .esi).toNat + 114 ≤ 2 ^ 32) {i : Nat} (hi : i < 14)
    (hr : InRegions (s.rd ++ s.wr) (off q (4 * i)) 4) {c : Bool} (hcf : s.cf = some c) :
    WP isa (.block (sLimb i)) s fun t => ∃ r : Nat, ∃ c' : Bool, r < 2 ^ 32 ∧ t.cf = some c' ∧
      strW s.mem q i + kWord i + c.toNat = r + 2 ^ 32 * c'.toNat ∧ t.mem = s.mem ∧ Keeps [.eax] s t := by
  have ea : s.ea (at_ .esi (57 + 4 * i)) = off q (4 * i) := ea_esi hq (by omega_using [hfit, hi])
  unfold sLimb
  refine WP.cons (t := s.setReg .eax (s.mem.readW (off q (4 * i)) 32))
    (by simp only [reduceExec, readSrc, ea, State.load32, hr, ite_true, Option.map_some]) ?_
  have u₁ := Upd.setReg s .eax (s.mem.readW (off q (4 * i)) 32)
  have f₁ : (s.setReg .eax (s.mem.readW (off q (4 * i)) 32)).cf = some c := hcf
  generalize s.setReg .eax (s.mem.readW (off q (4 * i)) 32) = s₁ at *
  refine Proof.X25519.X86.wp_adcC (y := BitVec.ofNat 32 (kWord i)) rfl f₁ fun t u₂ f₂ => WP.block_nil ?_
  have hw := (s.mem.readW (off q (4 * i)) 32).isLt
  have hk := kWord_lt i hi
  have hc : c.toNat ≤ 1 := by cases c <;> decide
  refine ⟨_, _, (t.gpr .eax).isLt, f₂, ?_, u₂.mem.trans u₁.mem,
    (u₁.rest (by simp)).trans ⟨fun r hr => u₂.other r (by simpa using hr), u₂.rd, u₂.wr⟩⟩
  rw [u₂.gpr, u₁.gpr, Proof.X25519.X86.add3_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk,
    Proof.X25519.X86.carry_toNat (by omega_using [hw, hk, hc])]
  exact (Nat.mod_add_div _ _).symm

/-- The sum's carry out, and the digits it leaves. -/
theorem sLimbs_ok {s : State} {q : Addr} (hq : (s.gpr .esi).setWidth 64 + BitVec.ofNat 64 57 = q)
    (hfit : (s.gpr .esi).toNat + 114 ≤ 2 ^ 32)
    (hr : ∀ k < 14, InRegions (s.rd ++ s.wr) (off q (4 * k)) 4) (hcf : s.cf = some false) :
    WP isa (.block ((List.range 14).flatMap sLimb)) s fun t => ∃ R : Nat, ∃ c : Bool, R < (2 ^ 32) ^ 14 ∧
      t.cf = some c ∧ num (strW s.mem q) 14 + num kWord 14 = R + (2 ^ 32) ^ 14 * c.toNat ∧ t.mem = s.mem ∧
      Keeps [.eax] s t := by
  let inv := fun n (t : State) => ∃ R : Nat, ∃ c : Bool, R < (2 ^ 32) ^ n ∧
      t.cf = some c ∧ num (strW s.mem q) n + num kWord n = R + (2 ^ 32) ^ n * c.toNat ∧ t.mem = s.mem ∧
      Keeps [.eax] s t
  refine wp_range_flatMap (M := isa) (N := 14) inv (fun n t hn ⟨R, c, hR, hc, hv, tm, tk⟩ => ?_) 14 (by decide) s
    ⟨0, false, by decide, hcf, rfl, rfl, Keeps.refl _ _⟩
  refine WP.mono (sLimb_ok (q := q) (by rw [tk.1 _ (by decide)]; exact hq) (by rw [tk.1 _ (by decide)]; exact hfit)
    hn (by rw [tk.2.1, tk.2.2]; exact hr n hn) hc) fun u ⟨r, c', hr', hc', hv', um, uk⟩ =>
      ⟨R + (2 ^ 32) ^ n * r, c', ?_, hc', ?_, um.trans tm, tk.trans uk⟩
  · have := Nat.mul_le_mul_left ((2 ^ 32) ^ n) (Nat.succ_le_of_lt hr')
    rw [Nat.mul_succ] at this
    rw [Nat.pow_succ (2 ^ 32) n]
    omega_using [hR, this]
  · rw [tm] at hv'
    have e := congrArg ((2 ^ 32) ^ n * ·) hv'
    simp only [Nat.mul_add] at e
    rw [num_succ, num_succ, Nat.pow_succ (2 ^ 32) n, Nat.mul_assoc ((2 ^ 32) ^ n)]
    omega_using [hv, e]

theorem sCheck_ok {s : State} {base q : Addr} (hs : Scr s base)
    (hq : (s.gpr .esi).setWidth 64 + BitVec.ofNat 64 57 = q) (hfit : (s.gpr .esi).toNat + 114 ≤ 2 ^ 32)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1)
    (hr4 : ∀ k < 14, InRegions (s.rd ++ s.wr) (off q (4 * k)) 4) :
    WP isa (.block sCheck) s fun t =>
      BadUpd (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem q 57) < Spec.Ed448.L) (word s.mem base BAD)
        (word t.mem base BAD) ∧ Outside base BAD 4 s.mem t.mem ∧ Keeps [.eax, .ecx] s t := by
  unfold sCheck
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (clearCarry_ok s) fun t₀ ⟨f₀, _, m₀, k₀⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sLimbs_ok (q := q) (by rw [k₀.1 _ (by decide)]; exact hq) (by rw [k₀.1 _ (by decide)]; exact hfit)
    (by rw [k₀.2.1, k₀.2.2]; exact hr4) f₀) fun t ⟨R, c, hR, tc, tv, tm, tk⟩ => ?_
  rw [m₀] at tv tm
  change WP isa (.block (([.alu .sbb .ecx (.reg .ecx)] : List Instr) ++ (([.movzx8 .eax (at_ .esi 113),
    .alu .or .eax (.reg .ecx)] : List Instr) ++ orBad .eax))) t _
  rw [WP.block_append_iff]
  refine WP.mono (freezeMask_ok tc) fun u ⟨uc, um, uk⟩ => ?_
  have k₀u : Keeps [.eax, .ecx] s u := (k₀.mono (by simp)).trans ((tk.mono (by simp)).trans (uk.mono (by simp)))
  have mu : u.mem = s.mem := um.trans tm
  have esi : u.gpr .esi = s.gpr .esi := k₀u.1 _ (by decide)
  refine wp_load8 (a := q + BitVec.ofNat 64 56)
    (by rw [show (113 : Nat) = 57 + 56 from rfl]; exact ea_esi (by rw [esi]; exact hq) (by rw [esi]; omega_using [hfit]))
    (by rw [k₀u.2.1, k₀u.2.2]; exact hr 56 (by decide)) fun v hv => ?_
  refine wp_alu (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) rfl fun w hw _ => ?_
  have p14 : ((2 : Nat) ^ 32) ^ 14 = 2 ^ 448 := by decide +kernel
  rw [num_kWord, p14] at tv
  rw [p14] at hR
  have yl : num (strW s.mem q) 14 < 2 ^ 448 := by
    rw [← p14]; exact num_lt fun _ _ => BitVec.isLt _
  have hchk := Proof.Ed448.sCheck_nat (b := (s.mem (q + BitVec.ofNat 64 56)).toNat) yl hR
    (show c.toNat ≤ 1 by cases c <;> decide) tv.symm
  rw [← decodeLE_bytes57] at hchk
  have e3 : w.gpr .eax = (s.mem (q + BitVec.ofNat 64 56)).setWidth 32 ||| mask c := by
    rw [hw.gpr]; change v.gpr .eax ||| v.gpr .ecx = _
    rw [hv.gpr, hv.other _ (by decide), mu, uc]
  have bt := (s.mem (q + BitVec.ofNat 64 56)).isLt
  have hw' : Scr w base := ((hs.of_keeps k₀u (by decide)).of_upd hv (by decide)).of_upd hw (by decide)
  refine WP.mono (orBad_ok (s := w) hw' (by decide)
    (P := Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem q 57) < Spec.Ed448.L) ?_)
    fun x ⟨xb, xm, xk⟩ => ⟨?_, ?_, ?_⟩
  · rw [e3, ← hchk]
    refine BitVec.or_eq_zero_iff.trans ?_
    refine and_comm.trans (and_congr (by cases c <;> decide) ⟨fun h1 => ?_, fun h2 => BitVec.eq_of_toNat_eq ?_⟩)
    · have := congrArg BitVec.toNat h1
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega_using [bt])] at this
      exact this
    · rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega_using [bt])]; exact h2
  · rw [hw.mem, hv.mem, mu] at xb
    exact xb
  · intro p h
    rw [xm p h, hw.mem, hv.mem, mu]
  · exact k₀u.trans ((hv.rest (by simp)).trans ((hw.rest (by simp)).trans (xk.mono (by simp))))

end VG.Proof.Ed448.X86
