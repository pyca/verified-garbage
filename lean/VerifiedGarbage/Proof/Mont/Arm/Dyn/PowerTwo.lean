module

public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Context
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Zeros
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: one and powers of two

`one n out` writes 1 (`one_ok`), and `powerTwo` doubles it `bits` times,
counting in `lr` (`powerTwo_ok`), to `2^bits mod m`.
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str wp_ldr wp_dp wp_movw wp_subs op2_imm op2_reg dpVal)

theorem val32_zeros {m : Mem} {base : Addr} {d : Nat} :
    ∀ {k : Nat}, (∀ j < k, w32 m base (d + 4 * j) = 0) → val32 m base d k = 0
  | 0, _ => rfl
  | k + 1, h => by rw [val32_succ, val32_zeros fun j hj => h j (by omega), h k (by omega), Nat.mul_zero]

/-- `[out] = 1`, `2n` words. -/
theorem one_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {n out : Nat} (hn : 0 < n)
    (hout : out + 8 * n ≤ size) (h16 : out + 8 * n < 2 ^ 16) :
    WP isa (one n out) s fun t => Ws t base size ∧ val32 t.mem base out (2 * n) = 1 ∧
      Outside base out (8 * n) s.mem t.mem ∧ Rest [.r4, .r7, .r9, .r10] s t := by
  have hnw := hs.nowrap
  unfold one
  refine WP.seq (WP.mono (zeros_ok hs (o := out) (k := 2 * n) (by omega) (by omega) (by omega))
    fun t₀ ⟨w₀, Z₀, O₀, R₀⟩ => ?_)
  refine wp_ptr (d := .r10) (by decide) (by omega) fun t₁ u₁ => wp_mov (op2_imm (by decide)) fun t₂ u₂ => ?_
  have w₂ := (w₀.of_upd u₁ (by decide)).of_upd u₂ (by decide)
  refine wp_str (by decide) (w₂.ea (d := 0) (K := out)
    (by simp only [u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]) (by omega))
    (w₂.write (d := out + 0) (n := 4) (by omega)) fun t m => WP.block_nil ⟨w₂.of_mupd m, ?_, ?_, ?_⟩
  · rw [m.mem, u₂.mem, u₁.mem, Nat.add_zero, show 2 * n = 1 + (2 * n - 1) by omega, val32_append, val32, val32,
      w32_write_self, val32_zeros (k := 2 * n - 1) fun j hj => ?_]
    · simp only [u₂.gpr]; rfl
    · rw [w32_write_ne (size := size) hnw (by omega) (by omega) (by omega),
        show out + 4 * 1 + 4 * j = out + 4 * (1 + j) by omega, Z₀ (1 + j) (by omega)]
  · rw [m.mem, u₂.mem, u₁.mem, Nat.add_zero]
    rw [show 4 * (2 * n) = 8 * n by omega] at O₀
    exact O₀.trans ((writeW32_outside _ _ (d := out) _ (by omega)).mono (by omega) (by omega))
  · exact (R₀.mono (by decide)).trans ((((u₁.rest (by decide)).trans (u₂.rest (by decide)))).trans (m.rest _))

/-- A count down by one. -/
theorem ofNat_sub_one {k : Nat} (h0 : 0 < k) (h : k < 2 ^ 32) :
    BitVec.ofNat 32 k - (1 : BitVec 32) = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
  omega

/-- The invariant of `powerTwo` after `j` doublings. -/
structure PowInv (n m : Nat) (base : Addr) (size o bits : Nat) (s : State) (j : Nat) (u : State) : Prop where
  ctx : Context n m base size u
  val : val32 u.mem base (slot n o) (2 * n) = 2 ^ j % m
  mem : Outs base (opRanges n o) s.mem u.mem
  rest : Rest (.lr :: dclob) s u
  lr : u.gpr .lr = BitVec.ofNat 32 (bits - j)

/-- `[slot o] = 2^bits mod m`, for `0 < bits < 2¹⁶`, doubling one. -/
theorem powerTwo_ok {n m size o bits : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (ho : 6 ≤ o ∧ o < 12) (hb : 0 < bits) (hb16 : bits < 2 ^ 16) :
    WP isa (powerTwo (contextMod n) (accS n) (slot n o) bits) s fun t => Context n m base size t ∧
      val32 t.mem base (slot n o) (2 * n) = 2 ^ bits % m ∧ Outs base (opRanges n o) s.mem t.mem ∧
      Rest (.lr :: dclob) s t := by
  have bo := slot_bound (n := n) ho.2
  have sz := h.size_le
  have sm := h.small
  have hm1 := h.gt_one
  unfold powerTwo
  refine WP.seq (WP.mono (one_ok h.ws (n := (contextMod n).n) (out := slot n o) h.n0
    (by simp only [contextMod, stride] at *; omega) (by simp only [contextMod, stride] at *; omega))
    fun t₀ ⟨w₀, V₀, O₀, R₀⟩ => ?_)
  have K₀ : OpKeep n base o s t₀ := ⟨R₀.mono (by decide), Outs.of_outside O₀ (by simp [contextMod])⟩
  have c₀ := h.keep (by omega) w₀ K₀
  refine WP.seq (wp_movw fun t₁ u₁ => WP.block_nil ?_)
  have I0 : PowInv n m base size o bits s 0 t₁ := by
    refine ⟨⟨w₀.of_upd u₁ (by decide), c₀.size_le, c₀.small, c₀.n0, by rw [u₁.mem]; exact c₀.modulus, c₀.gt_one,
      by rw [u₁.mem]; exact c₀.inverse⟩, ?_, ?_, ?_, ?_⟩
    · rw [u₁.mem, show (contextMod n).n = n from rfl] at *; rw [V₀, Nat.pow_zero, Nat.mod_eq_of_lt hm1]
    · rw [u₁.mem]; exact K₀.mem
    · exact (K₀.rest.mono (by decide)).trans (u₁.rest (by decide))
    · rw [u₁.gpr, Nat.sub_zero, movw_ofNat hb16]
  refine WP.loop (M := isa) (fun r u => ∃ j, r = bits - j ∧ j < bits ∧ PowInv n m base size o bits s j u) ?_ bits t₁
    ⟨0, rfl, hb, I0⟩
  rintro r u ⟨j, rfl, hj, I⟩
  have hv : val32 u.mem base (slot n o) (2 * n) < m := by rw [I.val]; exact Nat.mod_lt _ (by omega)
  refine WP.seq (WP.mono (context_add_ok I.ctx ho ho ho hv hv) fun u₁ ⟨c₁, K₁, V₁⟩ => ?_)
  refine wp_subs (VG.Proof.X25519.Arm.op2_imm (encodable_lt (n := 1) (by decide))) fun u₂ v₂ z₂ => WP.block_nil ?_
  have I' : PowInv n m base size o bits s (j + 1) u₂ := by
    refine ⟨⟨c₁.ws.of_upd v₂ (by decide), c₁.size_le, c₁.small, c₁.n0, by rw [v₂.mem]; exact c₁.modulus, c₁.gt_one,
      by rw [v₂.mem]; exact c₁.inverse⟩, ?_, ?_, ?_, ?_⟩
    · rw [v₂.mem, V₁, I.val, ← Nat.add_mod, Nat.pow_succ, Nat.mul_two]
    · rw [v₂.mem]; exact I.mem.trans K₁.mem
    · exact (I.rest.trans (K₁.rest.mono (by decide))).trans (v₂.rest (by decide))
    · rw [v₂.gpr, K₁.rest.gpr .lr (by decide), I.lr, ofNat_sub_one (by omega) (by omega)]
      congr 1
  have hz : u₂.z = decide (j + 1 = bits) := by
    rw [z₂, K₁.rest.gpr .lr (by decide), I.lr, ofNat_sub_one (by omega) (by omega),
      VG.Proof.X25519.Arm.ofNat_beq_zero (by omega)]
    simp only [decide_eq_decide]
    omega
  by_cases hj1 : j + 1 = bits
  · exact .inl ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_true hj1]; rfl,
      I'.ctx, by rw [I'.val, hj1], I'.mem, I'.rest⟩
  · exact .inr ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_false hj1]; rfl, bits - (j + 1), by omega,
      j + 1, rfl, by omega, I'⟩

end VG.Proof.Mont.Arm.Dyn
