module
import VerifiedGarbage.Proof.Framework.OmegaNear
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Out

import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CoreU
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# RSA with AVX512_IFMA on x86-64, any size: the multiplication

`amm_ok`: for each prime `p`, with its region at
`B + D p` (`B` in `rbx`), the numbers of `4 R` limbs of 52 bits at offsets
`a` and `b` multiplied and divided by `2^(52 S)` modulo the modulus at
`oM`, into offset `o`: below twice the modulus when both operands are, and
congruent to their product over `2^(52 S)`.

The numbers are in the stride layout: limb `j` at `Lay.off j`, read by
`limb`; `val52` is their value.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (ops se_ofNat off_add ofNat_toNat64 setOff ofs_rebase')

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- Limb `j` of the number at `B + d`. -/
abbrev limb (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (d j : Nat) : Nat := (word m B (d + l.off j)).toNat

/-- The number at `B + d`. -/
def val52 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (d : Nat) : Nat := lval (limb l m B d) l.L

/-- Limbs of a value below `2^(52 S)` from limb `S` on are zero. -/
theorem lval_trunc {b : Nat → Nat} {S : Nat} : ∀ n, S ≤ n → lval b n < 2 ^ (52 * S) → lval b n = lval b S
  | 0, h, _ => by rw [Nat.le_zero.1 h]
  | n + 1, h, hl => by
    rcases Nat.eq_or_lt_of_le h with rfl | h'
    · rfl
    rw [lval_succ] at hl ⊢
    have hp : 2 ^ (52 * S) ≤ 2 ^ (52 * n) := Nat.pow_le_pow_right (by decide) (by omega_near)
    have hz : b n = 0 := by
      rcases Nat.eq_zero_or_pos (b n) with h0 | h0
      · exact h0
      · have : 2 ^ (52 * n) ≤ b n * 2 ^ (52 * n) := Nat.le_mul_of_pos_left _ h0
        omega_near
    rw [hz, Nat.zero_mul, Nat.add_zero] at hl ⊢
    exact lval_trunc n (by omega_near) hl

theorem LayOk.D_ge (hl : LayOk l) : l.NB + 32 ≤ l.D := by
  rcases hl with rfl | rfl | rfl <;> decide

theorem AmmOk.D_ge (hl : AmmOk l) : l.NB + 32 ≤ l.D := by
  rcases hl with (rfl | rfl | rfl) | rfl | rfl | rfl <;> decide

/-- The CRT's layouts have the two primes' lanes. -/
theorem LayOk.nl (hl : LayOk l) : l.nl = 2 := by
  rcases hl with rfl | rfl | rfl <;> rfl

/-- A frame at `B + o` as one at `B`, for the lanes. -/
theorem OutN.rebaseN {B : Addr} {o n : Nat} {m m' : Mem} (h : OutN l (off B o) 0 n m m')
    (hn : o + l.D * (l.nl - 1) + n < 2 ^ 64) : OutN l B o n m m' := fun x hx => h x fun p hp => by
  have hDp := D_lane (l := l) hp
  rcases ofs_rebase' B x (o := o) (by omega_near) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases hx p hp with h3 | h3 <;> omega_near
  · omega_near

/-- A frame at `B + o` as one at `B`. -/
theorem Out2.rebase {B : Addr} {o n : Nat} {m m' : Mem} (h : Out2 l (off B o) 0 n m m')
    (hn : o + l.D + n < 2 ^ 64) : Out2 l B o n m m' := fun x hx => h x fun p hp => by
  have hDp : l.D * p ≤ l.D := by rcases (by omega_near : p = 0 ∨ p = 1) with rfl | rfl <;> simp
  rcases ofs_rebase' B x (o := o) (by omega_near) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases hx p hp with h3 | h3 <;> omega_near
  · omega_near

/-- A multiplication `c` (`ammCore`, or `ammCoreU`) with `r8`, `r9`, `r11` at offsets `a`, `b`, `o` of `B = rbx`. -/
theorem ammCoreSpecN_ok (hl : AmmOk l) {c : Prog isa} (hc : CoreOk l c) {s : State} {B : Addr} {Z o a b : Nat} {k : Nat → Nat}
    (hB : s.gpr .rbx = B) (r8₃ : s.gpr .r8 = off B a) (r9₃ : s.gpr .r9 = off B b) (r11₃ : s.gpr .r11 = off B o)
    (hs : Scr s B Z) (hZ : l.D * (l.nl - 1) + l.NB + 32 ≤ Z) (hZb : Z ≤ 2 ^ 63)
    (ho : o + l.D * (l.nl - 1) + l.NB ≤ Z) (ha : a + l.D * (l.nl - 1) + l.NB ≤ Z)
    (hb : b + l.D * (l.nl - 1) + l.NB ≤ Z)
    (hlt : ∀ p < l.nl, ∀ j < l.L, limb l s.mem B (l.D * p + a) j < 2 ^ 52 ∧ limb l s.mem B (l.D * p + b) j < 2 ^ 52 ∧
      limb l s.mem B (l.D * p + oM) j < 2 ^ 52)
    (hk : ∀ p < l.nl, ∀ t < 4, word s.mem B (l.D * p + l.oK0 + 8 * t) = BitVec.ofNat 64 (k p))
    (hklt : ∀ p < l.nl, k p < 2 ^ 52) (hk0 : ∀ p < l.nl, (limb l s.mem B (l.D * p + oM) 0 * k p + 1) % 2 ^ 52 = 0) :
    WP isa c s fun s' => (∀ p < l.nl,
      (∀ j < l.L, limb l s'.mem B (l.D * p + o) j < 2 ^ 52) ∧
      (val52 l s.mem B (l.D * p + a) < 2 * val52 l s.mem B (l.D * p + oM) →
        val52 l s.mem B (l.D * p + b) < 2 * val52 l s.mem B (l.D * p + oM) →
        4 * val52 l s.mem B (l.D * p + oM) ≤ 2 ^ (52 * l.S) →
        val52 l s'.mem B (l.D * p + o) < 2 * val52 l s.mem B (l.D * p + oM) ∧
        val52 l s'.mem B (l.D * p + o) * 2 ^ (52 * l.S) % val52 l s.mem B (l.D * p + oM) =
          val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) % val52 l s.mem B (l.D * p + oM))) ∧
      OutN l B o l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.gpr .r12 = mask52 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨hR, hR10⟩ := hl.bounds
  have hD := hl.D_bounds
  have hD' := hl.D_ge
  have hDn : l.D * (l.nl - 1) ≤ l.D := D_le hl (show l.nl - 1 < l.nl by have := hl.nl_le; omega_near)
  have hnD : l.nl * l.D = l.D * (l.nl - 1) + l.D := by
    have := hl.nl_le; rw [Nat.mul_comm, ← Nat.mul_succ]; congr 1; omega_near
  -- the operands, as functions of the limb index
  let A : Nat → Nat → Nat := fun p => limb l s.mem B (l.D * p + a)
  let Bl : Nat → Nat → Nat := fun p => limb l s.mem B (l.D * p + b)
  let M : Nat → Nat → Nat := fun p => limb l s.mem B (l.D * p + oM)
  have rdS : ∀ d n, 0 < n → d + n ≤ Z → InRegions (s.rd ++ s.wr) (off B d) n := fun d n hn hd =>
    let ⟨_, h, c⟩ := hs.region hd hn; ⟨_, List.mem_append_right _ h, c⟩
  have hoff : ∀ kk < l.R, ∀ t < 4, l.off (kk + l.R * t) = 32 * kk + 8 * t := fun kk hk t _ => by
    rw [Nat.add_comm, off_blk hR hk]
  have e : Env l (s.setReg .r10 (s.gpr .rbx)) A M k Bl := by
    refine ⟨fun p hp kk hk t ht => ?_, fun p hp kk hk t ht => ?_, fun p hp t ht => ?_, fun p hp q hq => ?_,
      fun p hp j hj => (hlt p hp j hj).1, fun p hp j hj => (hlt p hp j hj).2.2, hklt,
      fun p hp q hq => (hlt p hp q hq).2.1, fun d n hn hd => ?_, fun d n hn hd => ?_, fun d n hn hd => ?_⟩
    · rw [RegUpd.mem_setReg, RegUpd.gpr_setReg_of_ne _ _ (by decide), r8₃, off_add]
      show _ = BitVec.ofNat 64 (limb l s.mem B (l.D * p + a) (kk + l.R * t))
      rw [ofNat_toNat64, hoff kk hk t ht]
      exact congrArg (fun d => s.mem.readW (off B d) 64) (by omega_near)
    · rw [RegUpd.mem_setReg, RegUpd.gpr_setReg_self, hB]
      show _ = BitVec.ofNat 64 (limb l s.mem B (l.D * p + oM) (kk + l.R * t))
      rw [ofNat_toNat64, hoff kk hk t ht]
      exact congrArg (fun d => s.mem.readW (off B d) 64) (by simp only [oM]; omega_near)
    · rw [RegUpd.mem_setReg, RegUpd.gpr_setReg_self, hB]
      exact hk p hp t ht
    · rw [RegUpd.mem_setReg, RegUpd.gpr_setReg_of_ne _ _ (by decide), r9₃, off_add]
      show _ = BitVec.ofNat 64 (limb l s.mem B (l.D * p + b) q)
      rw [ofNat_toNat64]
      exact congrArg (fun d => s.mem.readW (off B d) 64) (by omega_near)
    · rw [RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_setReg_of_ne _ _ (by decide), r8₃, off_add]
      exact rdS _ n hn (by rw [show lim l .r8 = l.D * (l.nl - 1) + l.NB from rfl] at hd; omega_near)
    · rw [RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_setReg_of_ne _ _ (by decide), r9₃, off_add]
      exact rdS _ n hn (by
        rw [show lim l .r9 = l.D * (l.nl - 1) + 32 * (l.R - 1) + 8 from rfl] at hd; simp only [Lay.NB] at hb; omega_near)
    · rw [RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_setReg_self, hB]
      exact rdS _ n hn (by rw [show lim l .r10 = l.D * (l.nl - 1) + l.NB + 32 from rfl] at hd; omega_near)
  have hNB : 0 < l.NB := by simp only [Lay.NB]; omega_near
  have hs₃ : Scr s (off B o) (l.D * (l.nl - 1) + l.NB) := hs.sub (by omega_near) (by omega_near)
  refine WP.mono (hc e r11₃ hs₃) fun s' ⟨hw, _, hf, hg, h12, hrd, hwr, hx⟩ => ?_
  refine ⟨fun p hp => ?_, hf.rebaseN (by omega_near), hg, h12, hrd, hwr, hx⟩
  have hq : ∀ j < l.L, limb l s'.mem B (l.D * p + o) j = carried (lm l A M k Bl p l.S) j := fun j hj => by
    have := hw p hp j hj
    simp only [word, off_off] at this
    show (s'.mem.readW (off B _) 64).toNat = _
    rw [show l.D * p + o + l.off j = o + (l.D * p + l.off j) by omega_near, this, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := carried_lt (lm l A M k Bl p l.S) j; omega_near)]
  have hv : val52 l s'.mem B (l.D * p + o) = lval (carried (lm l A M k Bl p l.S)) l.L := by
    unfold val52; exact lval_congr hq
  refine ⟨fun j hj => (hq j hj) ▸ carried_lt _ j, fun hA' hB' hM' => ?_⟩
  have ok : Amm52N.Ok l.L (ops A M k p) :=
    ⟨fun j hj => (hlt p hp j hj).1, fun j hj => (hlt p hp j hj).2.2, hk0 p hp⟩
  have hst := hl.steps
  have he := Amm52N.steps_val (by simp only [Lay.L]; omega_near) ok (b := Bl p) (fun i hi => (hlt p hp i hi).2.1)
    (fun _ => 0) l.S hst.2.2.2.1
  have z : lval (fun _ => 0) l.L = 0 := by
    rw [show (fun _ : Nat => 0) = fun j => (fun _ : Nat => 0) j * 0 by funext; rfl, lval_mul, Nat.mul_zero]
  rw [z, Nat.zero_add] at he
  have hU : lval (Amm52N.stepsU l.L (ops A M k p) (Bl p) fun _ => 0) l.S < 2 ^ (52 * l.S) :=
    lval_lt fun j _ => lo_lt _ _
  have hcv := carried_val (lm l A M k Bl p l.S) l.L
  rw [hv]
  unfold val52 at hA' hB' hM' ⊢
  change lval (lm l A M k Bl p l.S) l.L * _ = lval (A p) l.L * lval (Bl p) l.S + lval (M p) l.L * _ at he
  change lval (A p) l.L < 2 * lval (M p) l.L at hA'
  change lval (Bl p) l.L < 2 * lval (M p) l.L at hB'
  change 4 * lval (M p) l.L ≤ _ at hM'
  have hbS : lval (Bl p) l.L = lval (Bl p) l.S := lval_trunc _ hst.2.2.2.1 (by omega_near)
  rw [hbS] at hB'
  have hSL : 2 ^ (52 * l.S) ≤ 2 ^ (52 * l.L) := Nat.pow_le_pow_right (by decide) (by omega_near)
  have hlt2 := amm_lt he hU hA' hB' hM'
  have hz : lval (lm l A M k Bl p l.S) l.L < 2 ^ (52 * l.L) := by
    generalize 2 ^ (52 * l.L) = R at hSL ⊢; generalize 2 ^ (52 * l.S) = R' at hM' hSL; omega_near
  rw [Amm52N.carryIn_zero hz] at hcv
  replace hcv : lval (carried (lm l A M k Bl p l.S)) l.L = lval (lm l A M k Bl p l.S) l.L := by
    generalize 2 ^ (52 * l.L) = R at hcv; omega_near
  rw [hcv]
  refine ⟨hlt2, ?_⟩
  rw [he, hbS, Nat.add_mul_mod_self_left]

/-- The layout's multiplication with `r8`, `r9`, `r11` at offsets `a`, `b`, `o` of `B = rbx`. -/
theorem ammCoreSpec_ok (hl : LayOk l) {s : State} {B : Addr} {o a b : Nat} {k : Nat → Nat}
    (hB : s.gpr .rbx = B) (r8₃ : s.gpr .r8 = off B a) (r9₃ : s.gpr .r9 = off B b) (r11₃ : s.gpr .r11 = off B o)
    (hs : Scr s B (2 * l.D))
    (ho : o + l.D + l.NB ≤ 2 * l.D) (ha : a + l.D + l.NB ≤ 2 * l.D) (hb : b + l.D + l.NB ≤ 2 * l.D)
    (hlt : ∀ p < 2, ∀ j < l.L, limb l s.mem B (l.D * p + a) j < 2 ^ 52 ∧ limb l s.mem B (l.D * p + b) j < 2 ^ 52 ∧
      limb l s.mem B (l.D * p + oM) j < 2 ^ 52)
    (hk : ∀ p < 2, ∀ t < 4, word s.mem B (l.D * p + l.oK0 + 8 * t) = BitVec.ofNat 64 (k p))
    (hklt : ∀ p < 2, k p < 2 ^ 52) (hk0 : ∀ p < 2, (limb l s.mem B (l.D * p + oM) 0 * k p + 1) % 2 ^ 52 = 0)
    (hA : ∀ p < 2, val52 l s.mem B (l.D * p + a) < 2 * val52 l s.mem B (l.D * p + oM))
    (hBv : ∀ p < 2, val52 l s.mem B (l.D * p + b) < 2 * val52 l s.mem B (l.D * p + oM))
    (hM : ∀ p < 2, 4 * val52 l s.mem B (l.D * p + oM) ≤ 2 ^ (52 * l.S)) :
    WP isa (ammMul l) s fun s' => (∀ p < 2,
      (∀ j < l.L, limb l s'.mem B (l.D * p + o) j < 2 ^ 52) ∧
      val52 l s'.mem B (l.D * p + o) < 2 * val52 l s.mem B (l.D * p + oM) ∧
      val52 l s'.mem B (l.D * p + o) * 2 ^ (52 * l.S) % val52 l s.mem B (l.D * p + oM) =
        val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) % val52 l s.mem B (l.D * p + oM)) ∧
      Out2 l B o l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hn := hl.nl
  have hD' := hl.amm.D_ge
  refine WP.mono (ammCoreSpecN_ok hl.amm (ammMul_core hl.amm) hB r8₃ r9₃ r11₃ hs (by rw [hn]; simp only [Nat.reduceSub, Nat.mul_one]; omega_near)
    (by have := hl.D_bounds; omega_near)
    (by rw [hn]; simpa using ho) (by rw [hn]; simpa using ha) (by rw [hn]; simpa using hb)
    (fun p hp => hlt p (by omega_near)) (fun p hp => hk p (by omega_near)) (fun p hp => hklt p (by omega_near))
    (fun p hp => hk0 p (by omega_near))) fun s' ⟨hv, hf, hg, _, hrd, hwr, hx⟩ =>
    ⟨fun p hp => let h := hv p (by omega_near); ⟨h.1, (h.2 (hA p hp) (hBv p hp) (hM p hp)).1,
      (h.2 (hA p hp) (hBv p hp) (hM p hp)).2⟩, hf.out2 hn, hg, hrd, hwr, hx⟩

/-- `[o] := [a] [b] / 2^(208 R)` for both primes. -/
theorem amm_ok (hl : LayOk l) {s : State} {B : Addr} {o a b : Nat} {k : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * l.D))
    (ho : o + l.D + l.NB ≤ 2 * l.D) (ha : a + l.D + l.NB ≤ 2 * l.D) (hb : b + l.D + l.NB ≤ 2 * l.D)
    (hlt : ∀ p < 2, ∀ j < l.L, limb l s.mem B (l.D * p + a) j < 2 ^ 52 ∧ limb l s.mem B (l.D * p + b) j < 2 ^ 52 ∧
      limb l s.mem B (l.D * p + oM) j < 2 ^ 52)
    (hk : ∀ p < 2, ∀ t < 4, word s.mem B (l.D * p + l.oK0 + 8 * t) = BitVec.ofNat 64 (k p))
    (hklt : ∀ p < 2, k p < 2 ^ 52) (hk0 : ∀ p < 2, (limb l s.mem B (l.D * p + oM) 0 * k p + 1) % 2 ^ 52 = 0)
    (hA : ∀ p < 2, val52 l s.mem B (l.D * p + a) < 2 * val52 l s.mem B (l.D * p + oM))
    (hBv : ∀ p < 2, val52 l s.mem B (l.D * p + b) < 2 * val52 l s.mem B (l.D * p + oM))
    (hM : ∀ p < 2, 4 * val52 l s.mem B (l.D * p + oM) ≤ 2 ^ (52 * l.S)) :
    WP isa (amm l o a b) s fun s' => (∀ p < 2,
      (∀ j < l.L, limb l s'.mem B (l.D * p + o) j < 2 ^ 52) ∧
      val52 l s'.mem B (l.D * p + o) < 2 * val52 l s.mem B (l.D * p + oM) ∧
      val52 l s'.mem B (l.D * p + o) * 2 ^ (52 * l.S) % val52 l s.mem B (l.D * p + oM) =
        val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) % val52 l s.mem B (l.D * p + oM)) ∧
      Out2 l B o l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hD : l.D + l.NB ≤ 2 ^ 20 := hl.D_bounds.2
  refine WP.seq ?_
  refine setOff (by omega_near) fun s₁ u₁ => setOff (by omega_near) fun s₂ u₂ =>
    setOff (by omega_near) fun s₃ u₃ => WP.block_nil ?_
  rw [u₁.other _ (by decide), hB] at u₂
  rw [u₂.other _ (by decide), u₁.other _ (by decide), hB] at u₃
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have r8₃ : s₃.gpr .r8 = off B a := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.self, hB]
  have r9₃ : s₃.gpr .r9 = off B b := by rw [u₃.other _ (by decide), u₂.self]
  have rbx₃ : s₃.gpr .rbx = B := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hB]
  have g₃ : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r11 → s₃.gpr r = s.gpr r := fun r h8 h9 h11 => by
    rw [u₃.other _ h11, u₂.other _ h9, u₁.other _ h8]
  rw [← m₃] at hlt hk hk0 hA hBv hM ⊢
  refine WP.mono (ammCoreSpec_ok hl rbx₃ r8₃ r9₃ u₃.self (hs.congr wr₃) ho ha hb hlt hk hklt hk0 hA hBv hM)
    fun s' ⟨hv, hf, hg, hrd, hwr, hx⟩ => ⟨hv, hf, fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 => ?_,
      hrd.trans rd₃, hwr.trans wr₃, by rw [hx, u₃.mxcsr, u₂.mxcsr, u₁.mxcsr]⟩
  rw [hg r h1 h2 h3 h4 h6 h7 h9, g₃ r h5 h6 h8]

end VG.Proof.Bignum.X86_64.Ifma
