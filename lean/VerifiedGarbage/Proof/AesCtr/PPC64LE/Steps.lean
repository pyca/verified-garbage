module

public import VerifiedGarbage.Impl.AesCtr.PPC64LE
public import VerifiedGarbage.Proof.AesCtr.Inc
public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# AES-CTR on PPC64LE: the code between the calls

The straight-line pieces of an iteration, each run in continuation-passing
style: the number of blocks of the call (`count`, `min left (2³² − c)`,
selected by a mask: `sel_min`), the advance past them with the last 32 bits
of the counter block in `r9` (`adv`), and the carry into the first 96 bits
(`carry`, whose block is `t + 2³²`, by `AesCtr.add_words64`; the carry out
of the second half is `1` iff its upper half is 0: `carry_bit`).
-/

@[expose] public section

namespace VG.Proof.AesCtr.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCtr.PPC64LE
open VG.Proof.AesCtr (rv32 rv64)
open VG.Spec.Aes (bytesAt)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `ldbrx t, a, b`. -/
theorem wp_ldbrx {t a b : Reg} {ea : Addr} (hn : a ≠ .r0) (hea : s.gpr a + s.gpr b = ea)
    (hin : InRegions (s.rd ++ s.wr) ea 8)
    (k : ∀ s', Upd s s' t (rv64 (s.mem.readW ea 64)) → WP isa (.block is) s' Q) :
    WP isa (.block (.loadRev .d t a b :: is)) s Q := by
  refine WP.cons (s' := s.write t (rv64 (s.mem.readW ea 64))) ?_ (k _ (Upd.write _ _ _))
  rw [exec_loadRev_d hn (by rw [hea]; exact hin), hea]
  rfl

/-- `stdbrx t, a, b`. -/
theorem wp_stdbrx {t a b : Reg} {ea : Addr} (hn : a ≠ .r0) (hea : s.gpr a + s.gpr b = ea)
    (hout : InRegions s.wr ea 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW ea (rv64 (s.gpr t))) → WP isa (.block is) s' Q) :
    WP isa (.block (.storeRev .d t a b :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW ea (rv64 (s.gpr t)) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl⟩)
  rw [exec_storeRev_d hn (by rw [hea]; exact hout), hea]
  rfl

end

theorem rev32_eq (a : BitVec 32) : rev32 a = rv32 a := rfl

/-- The smaller of `a` and `b`, both below `2⁶³`, selected by a mask made
from the sign of their difference. -/
theorem sel_min (a b : BitVec 64) (ha : a.toNat < 2 ^ 63) (hb : b.toNat < 2 ^ 63) :
    b ^^^ ((a ^^^ b) &&& (0#64 - ((a - b) >>> 63))) = if a.toNat < b.toNat then a else b := by
  by_cases h : a.toNat < b.toNat
  · have e : (a - b) >>> 63 = 1#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
      have : (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 = 2 ^ 64 - b.toNat + a.toNat := Nat.mod_eq_of_lt (by omega)
      rw [this]; simp only [BitVec.toNat_ofNat]; omega
    simp only [h, ↓reduceIte]
    rw [e, show (0#64 : BitVec 64) - 1#64 = BitVec.allOnes 64 by decide, BitVec.and_allOnes,
      BitVec.xor_comm a b, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · have e : (a - b) >>> 63 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
      have : (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 = a.toNat - b.toNat := by omega
      rw [this]; simp only [BitVec.toNat_ofNat]; omega
    simp only [h, ↓reduceIte]
    rw [e, show (0#64 : BitVec 64) - 0#64 = 0#64 by decide, BitVec.and_zero, BitVec.xor_zero]

/-- The carry out of `L + 2³²`: `1` iff the sum's upper half is 0. -/
theorem carry_bit (L : BitVec 64) :
    ((((L + BitVec.ofNat 64 (2 ^ 32)) >>> 32) - BitVec.ofNat 64 1) >>> 63).toNat =
      (L.toNat + 2 ^ 32) / 2 ^ 64 := by
  have hL := L.isLt
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_add,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  simp only [BitVec.toNat_ofNat]
  by_cases h : 2 ^ 64 ≤ L.toNat + 2 ^ 32
  · have e₁ : (L.toNat + 2 ^ 32 % 2 ^ 64) % 2 ^ 64 = L.toNat + 2 ^ 32 - 2 ^ 64 := by omega
    rw [e₁, show (L.toNat + 2 ^ 32 - 2 ^ 64) / 2 ^ 32 = 0 by omega]
    omega
  · have e₁ : (L.toNat + 2 ^ 32 % 2 ^ 64) % 2 ^ 64 = L.toNat + 2 ^ 32 := by omega
    rw [e₁]
    have : 1 ≤ (L.toNat + 2 ^ 32) / 2 ^ 32 := by omega
    have : (L.toNat + 2 ^ 32) / 2 ^ 32 < 2 ^ 32 := by omega
    omega

/-- `2³² − c`, for a 32-bit `c`. -/
theorem rem_toNat (c : BitVec 32) : (1#64 <<< 32 - c.setWidth 64).toNat = 2 ^ 32 - c.toNat := by
  have hc := c.isLt
  have h1 : (c.setWidth 64).toNat = c.toNat := by simp [BitVec.toNat_setWidth]; omega
  have h2 : (1#64 <<< 32).toNat = 2 ^ 32 := by decide
  rw [BitVec.toNat_sub, h1, h2]
  omega

/-- The blocks of the call: `min left (2³² − c)`, with `c` the last 32 bits
of the counter block, in `r10` and in the slot at `S + 2048`. -/
theorem count_wp {s : State} {Q S : Addr} {left : Nat} {rest : List Instr} {Φ : State → Prop}
    (h16 : s.gpr .r16 = Q) (h18 : s.gpr .r18 = BitVec.ofNat 64 left) (hl : left < 2 ^ 63)
    (h19 : s.gpr .r19 = S) (rq : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 12) 4)
    (ws : InRegions s.wr (S + BitVec.ofNat 64 2048) 8)
    (k : ∀ s', s'.gpr .r10 =
        BitVec.ofNat 64 (min left (2 ^ 32 - (rv32 (s.mem.readW (Q + BitVec.ofNat 64 12) 32)).toNat)) →
      (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem.writeW (S + BitVec.ofNat 64 2048) (s'.gpr .r10) → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block rest) s' Φ) :
    WP isa (.block (count ++ rest)) s Φ := by
  simp only [count, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s₁ u₁ => ?_
  refine wp_lwbrx (ea := Q + BitVec.ofNat 64 12) (by decide) (by rw [u₁.gpr, u₁.other _ (by decide), h16])
    (by rw [u₁.rd, u₁.wr]; exact rq) fun s₂ u₂ => ?_
  refine wp_li (by decide) fun s₃ u₃ => wp_lsl (by decide) fun s₄ u₄ => wp_sub fun s₅ u₅ => ?_
  refine wp_sub fun s₆ u₆ => wp_lsr (by decide) fun s₇ u₇ => wp_li (by decide) fun s₈ u₈ => ?_
  refine wp_sub fun s₉ u₉ => wp_xor fun s₁₀ u₁₀ => wp_and fun s₁₁ u₁₁ => wp_xor fun s₁₂ u₁₂ => ?_
  have g₁₂ (r : Reg) (h9 : r ≠ .r9) (h10 : r ≠ .r10) (h11 : r ≠ .r11) (h12 : r ≠ .r12) :
      s₁₂.gpr r = s.gpr r := by
    rw [u₁₂.other _ h10, u₁₁.other _ h12, u₁₀.other _ h12, u₉.other _ h11, u₈.other _ h12, u₇.other _ h11,
      u₆.other _ h11, u₅.other _ h10, u₄.other _ h10, u₃.other _ h10, u₂.other _ h9, u₁.other _ h10]
  have mem₁₂ : s₁₂.mem = s.mem := by
    rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  -- The value.
  generalize hc : rv32 (s.mem.readW (Q + BitVec.ofNat 64 12) 32) = c
  have hr9 : s₂.gpr .r9 = c.setWidth 64 := by rw [u₂.gpr, u₁.mem, rev32_eq, hc]
  have hrem : s₅.gpr .r10 = 1#64 <<< 32 - c.setWidth 64 := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₄.other .r9 (by decide), u₃.other .r9 (by decide), hr9]
  have h18₅ : s₅.gpr .r18 = BitVec.ofNat 64 left := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h18]
  have hmask : s₉.gpr .r11 = 0#64 - ((BitVec.ofNat 64 left - (1#64 <<< 32 - c.setWidth 64)) >>> 63) := by
    rw [u₉.gpr, u₈.gpr, u₈.other .r11 (by decide), u₇.gpr, u₆.gpr, h18₅, hrem]
  have hval : s₁₂.gpr .r10 = BitVec.ofNat 64 (min left (2 ^ 32 - c.toNat)) := by
    rw [u₁₂.gpr, u₁₁.gpr, u₁₁.other .r10 (by decide), u₁₀.gpr, u₁₀.other .r10 (by decide),
      u₁₀.other .r11 (by decide), u₉.other .r18 (by decide), u₉.other .r10 (by decide), hmask,
      u₈.other .r18 (by decide), u₈.other .r10 (by decide), u₇.other .r18 (by decide), u₇.other .r10 (by decide),
      u₆.other .r18 (by decide), u₆.other .r10 (by decide), h18₅, hrem]
    have hl' : (BitVec.ofNat 64 left).toNat = left := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have hr := rem_toNat c
    rw [sel_min (BitVec.ofNat 64 left) (1#64 <<< 32 - c.setWidth 64) (by rw [hl']; omega)
      (by rw [hr]; omega), hl', hr]
    by_cases h : left < 2 ^ 32 - c.toNat
    · simp only [h, ↓reduceIte]; rw [Nat.min_eq_left (Nat.le_of_lt h)]
    · simp only [h, ↓reduceIte]; rw [Nat.min_eq_right (show 2 ^ 32 - c.toNat ≤ left by omega)]
      apply BitVec.eq_of_toNat_eq
      rw [hr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := c.isLt; omega)]
  refine wp_std (a := S + BitVec.ofNat 64 2048) (by decide) (by decide)
    (by show s₁₂.gpr .r19 + BitVec.ofNat 64 2048 = _
        rw [g₁₂ .r19 (by decide) (by decide) (by decide) (by decide), h19])
    (by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact ws)
    fun s₁₃ u₁₃ => k s₁₃ (by rw [u₁₃.gpr, hval, ← hc]) (fun r h9 h10 h11 h12 => by rw [u₁₃.gpr, g₁₂ r h9 h10 h11 h12])
      (by rw [u₁₃.mem, u₁₃.gpr, mem₁₂]) (by
        rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
      (by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])

/-- On past the call's `m` blocks, with the last 32 bits of the counter
block in `r9`. -/
theorem adv_wp {s : State} {Q S P : Addr} {left m : Nat} {Φ : State → Prop}
    (h16 : s.gpr .r16 = Q) (h17 : s.gpr .r17 = P) (h18 : s.gpr .r18 = BitVec.ofNat 64 left)
    (h19 : s.gpr .r19 = S) (hm : s.mem.readW (S + BitVec.ofNat 64 2048) 64 = BitVec.ofNat 64 m)
    (hml : m ≤ left) (h16m : 16 * m < 2 ^ 64)
    (rs : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 2048) 8)
    (rq : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 12) 4)
    (k : ∀ s', s'.gpr .r18 = BitVec.ofNat 64 (left - m) → s'.gpr .r17 = P + BitVec.ofNat 64 (16 * m) →
      s'.gpr .r9 = (rv32 (s.mem.readW (Q + BitVec.ofNat 64 12) 32)).setWidth 64 →
      (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r17 → r ≠ .r18 → s'.gpr r = s.gpr r) → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → Φ s') :
    WP isa (.block adv) s Φ := by
  unfold adv
  refine wp_ld (a := S + BitVec.ofNat 64 2048) (by decide) (by decide)
    (by show s.gpr .r19 + BitVec.ofNat 64 2048 = _; rw [h19]) rs fun s₁ u₁ => ?_
  refine wp_sub fun s₂ u₂ => wp_lsl (by decide) fun s₃ u₃ => wp_add fun s₄ u₄ => ?_
  refine wp_li (by decide) fun s₅ u₅ => ?_
  refine wp_lwbrx (ea := Q + BitVec.ofNat 64 12) (by decide)
    (by rw [u₅.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h16])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rq)
    fun s₆ u₆ => wp_nil ?_
  have r9₁ : s₁.gpr .r9 = BitVec.ofNat 64 m := by rw [u₁.gpr, hm]
  have mem₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine k s₆ ?_ ?_ ?_ (fun r h9 h10 h17 h18 => ?_) ?_ ?_ ?_
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide), r9₁, h18, Offset.ofNat_sub_ofNat hml]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h17, r9₁]
    congr 1
    apply BitVec.eq_of_toNat_eq
    have hm' : m < 2 ^ 64 := by omega
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm',
      Nat.shiftLeft_eq]
    omega
  · rw [u₆.gpr, mem₅, rev32_eq]
  · rw [u₆.other _ h9, u₅.other _ h10, u₄.other _ h17, u₃.other _ h9, u₂.other _ h18, u₁.other _ h9]
  · rw [u₆.mem, mem₅]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-- The counter block plus `2³²`: a carry into its first 96 bits. -/
theorem carry_wp {s : State} {Q : Addr} {Φ : State → Prop} (h16 : s.gpr .r16 = Q)
    (r0 : InRegions (s.rd ++ s.wr) Q 8) (r8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (w0 : InRegions s.wr Q 8) (w8 : InRegions s.wr (Q + BitVec.ofNat 64 8) 8)
    (k : ∀ s', (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) →
      bytesAt s'.mem Q 16 = Spec.Ctr.ofNat (Spec.Ctr.toNat (bytesAt s.mem Q 16) + 2 ^ 32) 16 →
      Frame [⟨Q, 16⟩] s.mem s'.mem → s'.rd = s.rd → s'.wr = s.wr → Φ s') :
    WP isa (.block carry) s Φ := by
  unfold carry
  refine wp_li (by decide) fun s₁ u₁ => ?_
  have q₁ : s₁.gpr .r16 = Q := by rw [u₁.other _ (by decide), h16]
  refine wp_ldbrx (ea := Q + BitVec.ofNat 64 8) (by decide) (by rw [q₁, u₁.gpr])
    (by rw [u₁.rd, u₁.wr]; exact r8) fun s₂ u₂ => ?_
  refine wp_li (by decide) fun s₃ u₃ => wp_lsl (by decide) fun s₄ u₄ => wp_add fun s₅ u₅ => ?_
  have g₅ (r : Reg) (h9 : r ≠ .r9) (h11 : r ≠ .r11) : s₅.gpr r = s₁.gpr r := by
    rw [u₅.other _ h9, u₄.other _ h11, u₃.other _ h11, u₂.other _ h9]
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have lo : s₅.gpr .r9 = rv64 (s.mem.readW (Q + BitVec.ofNat 64 8) 64) + BitVec.ofNat 64 (2 ^ 32) := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₄.other .r9 (by decide), u₃.other .r9 (by decide), u₂.gpr, u₁.mem]
    rfl
  refine wp_stdbrx (ea := Q + BitVec.ofNat 64 8) (by decide)
    (by rw [g₅ _ (by decide) (by decide), q₁, g₅ _ (by decide) (by decide), u₁.gpr])
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact w8) fun s₆ u₆ => ?_
  refine wp_lsr (by decide) fun s₇ u₇ => wp_subi (by decide) (by decide) fun s₈ u₈ => ?_
  refine wp_lsr (by decide) fun s₉ u₉ => wp_li (by decide) fun s₁₀ u₁₀ => ?_
  have q₁₀ : s₁₀.gpr .r16 = Q := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.gpr, g₅ _ (by decide) (by decide), q₁]
  have m₁₀ : s₁₀.mem = s.mem.writeW (Q + BitVec.ofNat 64 8) (rv64 (s₅.gpr .r9)) := by
    rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅]
  refine wp_ldbrx (ea := Q) (by decide) (by rw [q₁₀, u₁₀.gpr]; simp)
    (by rw [u₁₀.rd, u₁₀.wr, u₉.rd, u₉.wr, u₈.rd, u₈.wr, u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr,
      u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact r0) fun s₁₁ u₁₁ => ?_
  refine wp_add fun s₁₂ u₁₂ => ?_
  refine wp_stdbrx (ea := Q) (by decide)
    (by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), q₁₀, u₁₂.other _ (by decide),
      u₁₁.other _ (by decide), u₁₀.gpr]; simp)
    (by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact w0)
    fun s₁₃ u₁₃ => wp_nil ?_
  -- The high word read back, past the write of the low one.
  have hsep : (s.mem.writeW (Q + BitVec.ofNat 64 8) (rv64 (s₅.gpr .r9))).readW Q 64 = s.mem.readW Q 64 := by
    have hs : Mem.Sep Q (64 / 8) (Q + BitVec.ofNat 64 8) (64 / 8) := by
      have := Offset.sep Q (d := 0) (n := 8) (e := 8) (k := 8) (by decide) (by decide) (by decide)
      simpa using this
    exact Mem.readW_writeW_sep hs (by decide)
  have cbit : (s₉.gpr .r9).toNat = ((rv64 (s.mem.readW (Q + BitVec.ofNat 64 8) 64)).toNat + 2 ^ 32) / 2 ^ 64 := by
    rw [u₉.gpr, u₈.gpr, u₇.gpr, u₆.gpr, lo]
    exact carry_bit _
  have hi : s₁₂.gpr .r11 = rv64 (s.mem.readW Q 64) + s₉.gpr .r9 := by
    rw [u₁₂.gpr, u₁₁.gpr, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅, hsep,
      u₁₁.other .r9 (by decide), u₁₀.other .r9 (by decide)]
  refine k s₁₃ (fun r h9 h10 h11 => ?_) ?_ ?_ ?_ ?_
  · rw [u₁₃.gpr, u₁₂.other _ h11, u₁₁.other _ h11, u₁₀.other _ h10, u₉.other _ h9, u₈.other _ h9,
      u₇.other _ h9, u₆.gpr, g₅ r h9 h11, u₁.other _ h10]
  · rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, m₁₀]
    refine AesCtr.add_words64 s.mem Q _ _ (2 ^ 32) ?_ ?_
    · rw [lo, BitVec.toNat_add]; rfl
    · rw [hi, BitVec.toNat_add, cbit]
  · rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, m₁₀]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base Q (d := 8) (n := 8) (k := 16) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (by simpa using Offset.contains_base Q (d := 0) (n := 8) (k := 16) (by decide) (by decide))
  · rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

end VG.Proof.AesCtr.PPC64LE
