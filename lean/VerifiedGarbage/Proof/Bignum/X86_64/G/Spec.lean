import VerifiedGarbage.Proof.Bignum.X86_64.G.Out
import VerifiedGarbage.Proof.Bignum.X86_64.AmmSpec

/-!
# RSA with AVX512_IFMA on x86-64, any size: the multiplication

`AmmSpec` for `CrtIfmaG` (`amm_ok`): for each prime `p`, with its region at
`B + D p` (`B` in `rbx`), the numbers of `4 R` limbs of 52 bits at offsets
`a` and `b` multiplied and divided by `2^(208 R)` modulo the modulus at
`oM`, into offset `o`: below twice the modulus when both operands are, and
congruent to their product over `2^(208 R)`.

The numbers are in the stride layout: limb `j` at `Lay.off j`, read by
`limb`; `val52` is their value.
-/

namespace VG.Proof.Bignum.X86_64.G

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off)
open VG.Impl.Rsa.X86_64.CrtIfmaG
open VG.Proof.Bignum.X86_64.AmmSym (ops se_ofNat off_add ofNat_toNat64 setOff ofs_rebase')

variable {l : Lay}

/-- Limb `j` of the number at `B + d`. -/
abbrev limb (l : Lay) (m : Mem) (B : Addr) (d j : Nat) : Nat := (word m B (d + l.off j)).toNat

/-- The number at `B + d`. -/
def val52 (l : Lay) (m : Mem) (B : Addr) (d : Nat) : Nat := lval (limb l m B d) l.L

theorem LayOk.D_ge (hl : LayOk l) : l.NB + 32 ≤ l.D := by
  rcases hl with rfl | rfl | rfl <;> decide

/-- A frame at `B + o` as one at `B`. -/
theorem Out2.rebase {B : Addr} {o n : Nat} {m m' : Mem} (h : Out2 l (off B o) 0 n m m')
    (hn : o + l.D + n < 2 ^ 64) : Out2 l B o n m m' := fun x hx => h x fun p hp => by
  have hDp : l.D * p ≤ l.D := by rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> simp
  rcases ofs_rebase' B x (o := o) (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases hx p hp with h3 | h3 <;> omega
  · omega

/-- `ammCore` with `r8`, `r9`, `r11` at offsets `a`, `b`, `o` of `B = rbx`. -/
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
    (hM : ∀ p < 2, 4 * val52 l s.mem B (l.D * p + oM) ≤ 2 ^ (52 * l.L)) :
    WP isa (ammCore l) s fun s' => (∀ p < 2,
      (∀ j < l.L, limb l s'.mem B (l.D * p + o) j < 2 ^ 52) ∧
      val52 l s'.mem B (l.D * p + o) < 2 * val52 l s.mem B (l.D * p + oM) ∧
      val52 l s'.mem B (l.D * p + o) * 2 ^ (52 * l.L) % val52 l s.mem B (l.D * p + oM) =
        val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) % val52 l s.mem B (l.D * p + oM)) ∧
      Out2 l B o l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨hR, hR10⟩ := hl.bounds
  have hD := hl.D_bounds
  have hD' := hl.D_ge
  -- the operands, as functions of the limb index
  let A : Nat → Nat → Nat := fun p => limb l s.mem B (l.D * p + a)
  let Bl : Nat → Nat → Nat := fun p => limb l s.mem B (l.D * p + b)
  let M : Nat → Nat → Nat := fun p => limb l s.mem B (l.D * p + oM)
  have rdS : ∀ d n, 0 < n → d + n ≤ 2 * l.D → InRegions (s.rd ++ s.wr) (off B d) n := fun d n hn hd =>
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
      exact congrArg (fun d => s.mem.readW (off B d) 64) (by omega)
    · rw [RegUpd.mem_setReg, RegUpd.gpr_setReg_self, hB]
      show _ = BitVec.ofNat 64 (limb l s.mem B (l.D * p + oM) (kk + l.R * t))
      rw [ofNat_toNat64, hoff kk hk t ht]
      exact congrArg (fun d => s.mem.readW (off B d) 64) (by simp only [oM]; omega)
    · rw [RegUpd.mem_setReg, RegUpd.gpr_setReg_self, hB]
      exact hk p hp t ht
    · rw [RegUpd.mem_setReg, RegUpd.gpr_setReg_of_ne _ _ (by decide), r9₃, off_add]
      show _ = BitVec.ofNat 64 (limb l s.mem B (l.D * p + b) q)
      rw [ofNat_toNat64]
      exact congrArg (fun d => s.mem.readW (off B d) 64) (by omega)
    · rw [RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_setReg_of_ne _ _ (by decide), r8₃, off_add]
      exact rdS _ n hn (by rw [show lim l .r8 = l.D + l.NB from rfl] at hd; omega)
    · rw [RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_setReg_of_ne _ _ (by decide), r9₃, off_add]
      exact rdS _ n hn (by
        rw [show lim l .r9 = l.D + 32 * (l.R - 1) + 8 from rfl] at hd; simp only [Lay.NB] at hb; omega)
    · rw [RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_setReg_self, hB]
      exact rdS _ n hn (by rw [show lim l .r10 = l.D + l.NB + 32 from rfl] at hd; omega)
  have hs₃ : Scr s (off B o) (l.D + l.NB) := hs.sub (by omega) (by omega)
  refine WP.mono (ammCore_ok hl e r11₃ hs₃) fun s' ⟨hw, hdx, hsi, hf, hg, hrd, hwr, hx⟩ => ?_
  refine ⟨fun p hp => ?_, hf.rebase (by omega), hg, hrd, hwr, hx⟩
  have hq : ∀ j < l.L, limb l s'.mem B (l.D * p + o) j = carried (lm l A M k Bl p l.L) j := fun j hj => by
    have := hw p hp j hj
    simp only [word, off_off] at this
    show (s'.mem.readW (off B _) 64).toNat = _
    rw [show l.D * p + o + l.off j = o + (l.D * p + l.off j) by omega, this, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := carried_lt (lm l A M k Bl p l.L) j; omega)]
  have hv : val52 l s'.mem B (l.D * p + o) = lval (carried (lm l A M k Bl p l.L)) l.L := by
    unfold val52; exact lval_congr hq
  have ok : Amm52N.Ok l.L (ops A M k p) :=
    ⟨fun j hj => (hlt p hp j hj).1, fun j hj => (hlt p hp j hj).2.2, hk0 p hp⟩
  obtain ⟨he, hU⟩ := Amm52N.amm_val (by simp only [Lay.L]; omega) ok (b := Bl p)
    fun i hi => (hlt p hp i hi).2.1
  have hcv := carried_val (lm l A M k Bl p l.L) l.L
  have hA' := hA p hp
  have hB' := hBv p hp
  have hM' := hM p hp
  rw [hv]
  unfold val52 at hA' hB' hM' ⊢
  change lval (lm l A M k Bl p l.L) l.L * _ = lval (A p) l.L * lval (Bl p) l.L + lval (M p) l.L * _ at he
  change lval (A p) l.L < 2 * lval (M p) l.L at hA'
  change lval (Bl p) l.L < 2 * lval (M p) l.L at hB'
  change 4 * lval (M p) l.L ≤ _ at hM'
  have hlt2 := amm_lt he hU hA' hB' hM'
  have hz : lval (lm l A M k Bl p l.L) l.L < 2 ^ (52 * l.L) := by
    generalize 2 ^ (52 * l.L) = R at hM' ⊢; omega
  rw [Amm52N.carryIn_zero hz] at hcv
  replace hcv : lval (carried (lm l A M k Bl p l.L)) l.L = lval (lm l A M k Bl p l.L) l.L := by
    generalize 2 ^ (52 * l.L) = R at hcv; omega
  rw [hcv]
  refine ⟨fun j hj => (hq j hj) ▸ carried_lt _ j, hlt2, ?_⟩
  rw [he, Nat.add_mul_mod_self_left]

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
    (hM : ∀ p < 2, 4 * val52 l s.mem B (l.D * p + oM) ≤ 2 ^ (52 * l.L)) :
    WP isa (amm l o a b) s fun s' => (∀ p < 2,
      (∀ j < l.L, limb l s'.mem B (l.D * p + o) j < 2 ^ 52) ∧
      val52 l s'.mem B (l.D * p + o) < 2 * val52 l s.mem B (l.D * p + oM) ∧
      val52 l s'.mem B (l.D * p + o) * 2 ^ (52 * l.L) % val52 l s.mem B (l.D * p + oM) =
        val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) % val52 l s.mem B (l.D * p + oM)) ∧
      Out2 l B o l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hD : l.D + l.NB ≤ 2 ^ 20 := hl.D_bounds.2
  refine WP.seq ?_
  refine setOff (by omega) fun s₁ u₁ => setOff (by omega) fun s₂ u₂ =>
    setOff (by omega) fun s₃ u₃ => WP.block_nil ?_
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

end VG.Proof.Bignum.X86_64.G
