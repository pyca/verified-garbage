import VerifiedGarbage.Proof.Bignum.X86_64.AmmOut

/-!
# RSA with AVX512_IFMA on x86-64: the multiplication

`amm o a b` (`amm_ok`): for each prime `p`, with its region at `B + D p`
(`B` in `rbx`), the numbers of twenty limbs of 52 bits at offsets `a` and
`b` multiplied and divided by `2¹⁰⁴⁰` modulo the modulus at `oM`, into
offset `o`: below twice the modulus when both operands are, and congruent
to their product over `2¹⁰⁴⁰`.

The numbers are in the vector layout: limb `j` at `off j`
(`CrtIfma.off`), read by `limb`; `val52` is their value.
-/

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum.X86_64 (off word ofs Outside off_off Scr)
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0 mask52)

/-- Limb `j` of the number at `B + d`. -/
abbrev limb (m : Mem) (B : Addr) (d j : Nat) : Nat := (word m B (d + VG.Impl.Rsa.X86_64.CrtIfma.off j)).toNat

/-- The number at `B + d`. -/
def val52 (m : Mem) (B : Addr) (d : Nat) : Nat := lval (limb m B d) 20

theorem se_ofNat {c : Nat} (h : c < 2 ^ 31) : BitVec.signExtend 64 (BitVec.ofNat 32 c) = BitVec.ofNat 64 c := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false (by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; simp; omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem off_add (B : Addr) (a d : Nat) : off B a + BitVec.ofNat 64 d = off B (a + d) := off_off B a d

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- `r := rbx + c`. -/
theorem setOff {s : State} {r : Reg} {c : Nat} {rest : List Instr} {Q : State → Prop} (hc : c < 2 ^ 31)
    (h : ∀ s', Upd s s' r (off (s.gpr .rbx) c) → WP isa (.block rest) s' Q) :
    WP isa (.block (.mov r (.reg .rbx) :: .alu .add r (.imm (BitVec.ofNat 32 c)) :: rest)) s Q := by
  rw [WP.block_cons_iff]
  refine ⟨s.setReg r (s.gpr .rbx), rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, h _ ⟨?_, fun r' hr' => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_self, se_ofNat hc]
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr', RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr']

theorem off_lim (j : Nat) : VG.Impl.Rsa.X86_64.CrtIfma.off j = 32 * (j % 5) + 8 * (j / 5) := by
  unfold VG.Impl.Rsa.X86_64.CrtIfma.off; omega

/-- `[o] := [a] [b] / 2¹⁰⁴⁰` for both primes. -/
theorem amm_ok {s : State} {B : Addr} {o a b : Nat} {k : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * D))
    (ho : o + D + 160 ≤ 2 * D) (ha : a + D + 160 ≤ 2 * D) (hb : b + D + 160 ≤ 2 * D)
    (hlt : ∀ p < 2, ∀ j < 20, limb s.mem B (D * p + a) j < 2 ^ 52 ∧ limb s.mem B (D * p + b) j < 2 ^ 52 ∧
      limb s.mem B (D * p + oM) j < 2 ^ 52)
    (hk : ∀ p < 2, ∀ t < 4, word s.mem B (D * p + oK0 + 8 * t) = BitVec.ofNat 64 (k p))
    (hklt : ∀ p < 2, k p < 2 ^ 52) (hk0 : ∀ p < 2, (limb s.mem B (D * p + oM) 0 * k p + 1) % 2 ^ 52 = 0)
    (hA : ∀ p < 2, val52 s.mem B (D * p + a) < 2 * val52 s.mem B (D * p + oM))
    (hBv : ∀ p < 2, val52 s.mem B (D * p + b) < 2 * val52 s.mem B (D * p + oM))
    (hM : ∀ p < 2, 4 * val52 s.mem B (D * p + oM) ≤ 2 ^ (52 * 20)) :
    WP isa (VG.Impl.Rsa.X86_64.CrtIfma.amm o a b) s fun s' => (∀ p < 2,
      (∀ j < 20, limb s'.mem B (D * p + o) j < 2 ^ 52) ∧
      val52 s'.mem B (D * p + o) < 2 * val52 s.mem B (D * p + oM) ∧
      val52 s'.mem B (D * p + o) * 2 ^ (52 * 20) % val52 s.mem B (D * p + oM) =
        val52 s.mem B (D * p + a) * val52 s.mem B (D * p + b) % val52 s.mem B (D * p + oM)) ∧
      Outside (off B o) 0 (D + 160) s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hD : D = 3872 := rfl
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
  -- the operands, as functions of the limb index
  let A : Nat → Nat → Nat := fun p => limb s.mem B (D * p + a)
  let Bl : Nat → Nat → Nat := fun p => limb s.mem B (D * p + b)
  let M : Nat → Nat → Nat := fun p => limb s.mem B (D * p + oM)
  have rdS : ∀ d n, 0 < n → d + n ≤ 2 * D → InRegions (s.rd ++ s.wr) (off B d) n := fun d n hn hd =>
    let ⟨_, h, c⟩ := hs.region hd hn; ⟨_, List.mem_append_right _ h, c⟩
  have e : Env (s₃.setReg .r10 (s₃.gpr .rbx)) A M k Bl := by
    refine ⟨fun p hp kk hk t ht => ?_, fun p hp kk hk t ht => ?_, fun p hp t ht => ?_, fun p hp l hl => ?_,
      fun p hp j hj => (hlt p hp j hj).1, fun p hp j hj => (hlt p hp j hj).2.2, hklt,
      fun p hp l hl => (hlt p hp l hl).2.1, fun d n hn hd => ?_, fun d n hn hd => ?_, fun d n hn hd => ?_⟩
    · rw [RegUpd.mem_setReg, RegUpd.gpr_setReg_of_ne _ _ (by decide), r8₃, m₃, off_add]
      show _ = BitVec.ofNat 64 (limb s.mem B (D * p + a) (kk + 5 * t))
      rw [ofNat_toNat64, off_lim _]
      exact congrArg (fun d => s.mem.readW (off B d) 64) (by omega)
    · rw [RegUpd.mem_setReg, RegUpd.gpr_setReg_self, rbx₃, m₃]
      show _ = BitVec.ofNat 64 (limb s.mem B (D * p + oM) (kk + 5 * t))
      rw [ofNat_toNat64, off_lim _]
      exact congrArg (fun d => s.mem.readW (off B d) 64) (by simp only [oM]; omega)
    · rw [RegUpd.mem_setReg, RegUpd.gpr_setReg_self, rbx₃, m₃]
      exact hk p hp t ht
    · rw [RegUpd.mem_setReg, RegUpd.gpr_setReg_of_ne _ _ (by decide), r9₃, m₃, off_add]
      show _ = BitVec.ofNat 64 (limb s.mem B (D * p + b) l)
      rw [ofNat_toNat64]
      exact congrArg (fun d => s.mem.readW (off B d) 64) (by omega)
    · rw [RegUpd.rd_setReg, RegUpd.wr_setReg, rd₃, wr₃, RegUpd.gpr_setReg_of_ne _ _ (by decide), r8₃, off_add]
      exact rdS _ n hn (by rw [show lim .r8 = D + 160 from rfl] at hd; omega)
    · rw [RegUpd.rd_setReg, RegUpd.wr_setReg, rd₃, wr₃, RegUpd.gpr_setReg_of_ne _ _ (by decide), r9₃, off_add]
      exact rdS _ n hn (by rw [show lim .r9 = D + 136 from rfl] at hd; omega)
    · rw [RegUpd.rd_setReg, RegUpd.wr_setReg, rd₃, wr₃, RegUpd.gpr_setReg_self, rbx₃]
      exact rdS _ n hn (by rw [show lim .r10 = D + 192 from rfl] at hd; omega)
  have hs₃ : Scr s₃ (off B o) (D + 160) := (hs.sub (by omega) (by omega)).congr wr₃
  refine WP.mono (ammCore_ok e u₃.self hs₃) fun s' ⟨hw, hdx, hsi, hf, hg, hrd, hwr, hx⟩ => ?_
  refine ⟨fun p hp => ?_, by rw [← m₃]; exact hf, fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 => ?_,
    hrd.trans rd₃, hwr.trans wr₃, by rw [hx, u₃.mxcsr, u₂.mxcsr, u₁.mxcsr]⟩
  · have hl : ∀ j < 20, limb s'.mem B (D * p + o) j = carried (lm A M k Bl p 20) j := fun j hj => by
      have := hw p hp j hj
      simp only [word, off_off] at this
      show (s'.mem.readW (off B _) 64).toNat = _
      rw [show D * p + o + VG.Impl.Rsa.X86_64.CrtIfma.off j = o + (D * p + VG.Impl.Rsa.X86_64.CrtIfma.off j) by
        omega, this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := carried_lt (lm A M k Bl p 20) j; omega)]
    have hv : val52 s'.mem B (D * p + o) = lval (carried (lm A M k Bl p 20)) 20 := by
      unfold val52; exact lval_congr hl
    have ok : (ops A M k p).Ok := ⟨fun j hj => (hlt p hp j hj).1, fun j hj => (hlt p hp j hj).2.2, hk0 p hp⟩
    obtain ⟨he, hU⟩ := amm_val ok (b := Bl p) fun i hi => (hlt p hp i hi).2.1
    have hcv := carried_val (lm A M k Bl p 20) 20
    have hA' := hA p hp
    have hB' := hBv p hp
    have hM' := hM p hp
    rw [hv]
    unfold val52 at hA' hB' hM' ⊢
    change lval (lm A M k Bl p 20) 20 * _ = lval (A p) 20 * lval (Bl p) 20 + lval (M p) 20 * _ at he
    change lval (A p) 20 < 2 * lval (M p) 20 at hA'
    change lval (Bl p) 20 < 2 * lval (M p) 20 at hB'
    change 4 * lval (M p) 20 ≤ _ at hM'
    have hlt2 := amm_lt he hU hA' hB' hM'
    have hz : lval (lm A M k Bl p 20) 20 < 2 ^ (52 * 20) := by
      generalize 2 ^ (52 * 20) = R at hM' ⊢; omega
    rw [carryIn_zero hz] at hcv
    replace hcv : lval (carried (lm A M k Bl p 20)) 20 = lval (lm A M k Bl p 20) 20 := by
      generalize 2 ^ (52 * 20) = R at hcv; omega
    rw [hcv]
    refine ⟨fun j hj => (hl j hj) ▸ carried_lt _ j, hlt2, ?_⟩
    rw [he, Nat.add_mul_mod_self_left]
  · rw [hg r h1 h2 h3 h4 h6 h7 h9, g₃ r h5 h6 h8]

end VG.Proof.Bignum.X86_64.AmmSym
