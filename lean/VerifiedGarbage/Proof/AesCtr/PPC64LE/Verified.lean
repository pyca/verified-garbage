module

public import VerifiedGarbage.Proof.AesCtr.Rounds
public import VerifiedGarbage.Impl.AesCtr.PPC64LE
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Loop
public import VerifiedGarbage.Proof.AesCtr.Spec
public import VerifiedGarbage.Spec.Ctr.Contract
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Verified
public import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.AesCtr.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Ctr
public import VerifiedGarbage.Proof.AesCtr.Inc
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.AesCtr.PPC64LE.Call
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.Loop
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.AesCtr.Spec
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Impl.AesCtr.PPC64LE
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Spec.Ctr
meta import VerifiedGarbage.Proof.AesCtr.Inc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-! ### `AesCtr.PPC64LE.CT`, which this module and modules that import it used -/

section

/-! ### `AesCtr.PPC64LE.Iter`, which this module and modules that import it used -/

section

/-! ### `AesCtr.PPC64LE.Body`, which this module and modules that import it used -/

section

/-! ### `AesCtr.PPC64LE.Steps`, which this module and modules that import it used -/

section

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
      have : (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 = 2 ^ 64 - b.toNat + a.toNat := Nat.mod_eq_of_lt (by omega_using [h])
      rw [this]; simp only [BitVec.toNat_ofNat]; omega_using [hb, h]
    simp only [h, ↓reduceIte]
    rw [e, show (0#64 : BitVec 64) - 1#64 = BitVec.allOnes 64 by decide, BitVec.and_allOnes,
      BitVec.xor_comm a b, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · have e : (a - b) >>> 63 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
      have : (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 = a.toNat - b.toNat := by omega_using [h]
      rw [this]; simp only [BitVec.toNat_ofNat]; omega_using [ha]
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
  · have e₁ : (L.toNat + 2 ^ 32 % 2 ^ 64) % 2 ^ 64 = L.toNat + 2 ^ 32 - 2 ^ 64 := by omega_using [h]
    rw [e₁, show (L.toNat + 2 ^ 32 - 2 ^ 64) / 2 ^ 32 = 0 by omega_using []]
    omega_using [h]
  · have e₁ : (L.toNat + 2 ^ 32 % 2 ^ 64) % 2 ^ 64 = L.toNat + 2 ^ 32 := by omega_using [h]
    rw [e₁]
    have : 1 ≤ (L.toNat + 2 ^ 32) / 2 ^ 32 := by omega_using []
    have : (L.toNat + 2 ^ 32) / 2 ^ 32 < 2 ^ 32 := by omega_using [h]
    omega_using [h]

/-- `2³² − c`, for a 32-bit `c`. -/
theorem rem_toNat (c : BitVec 32) : (1#64 <<< 32 - c.setWidth 64).toNat = 2 ^ 32 - c.toNat := by
  have hc := c.isLt
  have h1 : (c.setWidth 64).toNat = c.toNat := by simp [BitVec.toNat_setWidth]; omega_using []
  have h2 : (1#64 <<< 32).toNat = 2 ^ 32 := by decide
  rw [BitVec.toNat_sub, h1, h2]
  omega_using []

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
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hl])
    have hr := rem_toNat c
    rw [sel_min (BitVec.ofNat 64 left) (1#64 <<< 32 - c.setWidth 64) (by rw [hl']; omega_using [hl])
      (by rw [hr]; omega_using []), hl', hr]
    by_cases h : left < 2 ^ 32 - c.toNat
    · simp only [h, ↓reduceIte]; rw [Nat.min_eq_left (Nat.le_of_lt h)]
    · simp only [h, ↓reduceIte]; rw [Nat.min_eq_right (show 2 ^ 32 - c.toNat ≤ left by omega_using [h])]
      apply BitVec.eq_of_toNat_eq
      rw [hr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := c.isLt; omega_using [])]
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
    have hm' : m < 2 ^ 64 := by omega_using [h16m]
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm',
      Nat.shiftLeft_eq]
    omega_using []
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

end

end

/-!
# AES-CTR on PPC64LE: the code before the call

As on x86-64 (`Proof/AesCtr/X86_64/Verified.lean`): the blocks of the call after
`k` blocks (`mOf`), what is left but no further than where the last 32 bits
of the counter block wrap around, and `pre_wp`: the code before the call
sets up a call of `vg_aes_ctr32` on them (`CtrCall`), with their number in
the scratch buffer, from AES-CBC's loop invariant for `ctrMode`
(`Proof/AesCbc/PPC64LE/Loop.lean`).
-/

@[expose] public section

namespace VG.Proof.AesCtr.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCtr.PPC64LE
open VG.Impl.AesCbc.PPC64LE (mov)
open VG.Proof.AesCbc (Mode)
open VG.Proof.AesCbc.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (next toNat ofNat)

/-- The blocks of the call after `k` blocks: what is left, but no further
than where the last 32 bits of the counter block wrap around. -/
def mOf (s₀ : State) (k : Nat) : Nat := min (N s₀ - k) (2 ^ 32 - (toNat (iv0 s₀) + k) % 2 ^ 32)

theorem length_iv0 (s₀ : State) : (iv0 s₀).length = 16 := Proof.Cmac.bytesAt_length _ _ _

theorem mOf_pos {s₀ : State} {k : Nat} (hk : k < N s₀) : 0 < mOf s₀ k := by
  unfold mOf; have := Nat.mod_lt (toNat (iv0 s₀) + k) (show 0 < 2 ^ 32 by decide); omega_using [hk]

theorem mOf_le (s₀ : State) (k : Nat) : mOf s₀ k ≤ N s₀ - k := Nat.min_le_left _ _

theorem lo32_mOf (s₀ : State) (k : Nat) : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k ≤ 2 ^ 32 := by
  rw [AesCtr.lo32_next (length_iv0 s₀)]; unfold mOf; omega_using []

theorem chainK_ctr (s₀ : State) {k : Nat} (hk : k ≤ N s₀) : chainK AesCtr.ctrMode s₀ k = next (iv0 s₀) k := by
  rw [chainK, AesCtr.ctrMode_chain, List.length_take, Proof.AesCbc.length_blocksAt, Nat.min_eq_left hk]

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.N_le : N s₀ ≤ 2 ^ 60 := by
  have := hp.data_wrap; omega_using [this]

theorem UPre.seg_wrap {k m : Nat} (hk : k < N s₀) (hkm : k + m ≤ N s₀) : (blk s₀ k).toNat + 16 * m ≤ 2 ^ 64 := by
  have := hp.data_wrap
  have : (blk s₀ k).toNat = (Dp s₀).toNat + 16 * k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * k) (by omega_using [hk, this]),
      Nat.mod_eq_of_lt (by omega_using [hk, this])]
  omega_arith

omit hp in
theorem UPre.seg_sub {k m : Nat} (hkm : k + m ≤ N s₀) : Region.Sub ⟨blk s₀ k, 16 * m⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega_using [hkm])

/-- The arguments of the call after `k` blocks. -/
theorem UPre.ctrCall {k : Nat} (hk : k < N s₀) {s : State}
    (r3 : s.gpr .r3 = W s₀) (r4 : s.gpr .r4 = s₀.gpr .r4) (r5 : s.gpr .r5 = Iv s₀)
    (r6 : s.gpr .r6 = blk s₀ k) (r7 : s.gpr .r7 = BitVec.ofNat 64 (mOf s₀ k)) (r8 : s.gpr .r8 = S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CtrCall s (W s₀) (Iv s₀) (blk s₀ k) (S s₀) (R s₀) (mOf s₀ k) where
  r3 := r3
  r4 := by rw [r4, r4_ofNat]
  r5 := r5
  r6 := r6
  r7 := r7
  r8 := r8
  rounds := hp.rounds
  wrap := UPre.seg_wrap hp hk (by have := mOf_le s₀ k; omega_using [hk, this])
  kc := hp.sch_iv
  kd := hp.sch_data.sub_right (UPre.seg_sub (s₀ := s₀) (by have := mOf_le s₀ k; omega_using [hk, this]))
  ks := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  cd := hp.iv_data.sub_right (UPre.seg_sub (s₀ := s₀) (by have := mOf_le s₀ k; omega_using [hk, this]))
  cs := hp.iv_scr.sub_right (Region.sub_prefix (by decide))
  ds := (hp.data_scr.sub_left (UPre.seg_sub (s₀ := s₀) (by have := mOf_le s₀ k; omega_using [hk, this]))).sub_right
    (Region.sub_prefix (by decide))
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨ivR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; have := mOf_le s₀ k; omega_using [hk, this]⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; have := mOf_le s₀ k; omega_using [hk, this]⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

/-- What the code before the call leaves. -/
structure Pre (s₀ : State) (k : Nat) (s s₁ : State) : Prop where
  call : CtrCall s₁ (W s₀) (Iv s₀) (blk s₀ k) (S s₀) (R s₀) (mOf s₀ k)
  saved : ∀ r ∈ preserved, s₁.gpr r = s.gpr r
  mem : s₁.mem = s.mem.writeW (S s₀ + BitVec.ofNat 64 2048) (BitVec.ofNat 64 (mOf s₀ k))
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

omit hp in
theorem preserved_ne' {r : Reg} (hr : r ∈ preserved) :
    r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧
      r ≠ .r12 := by
  revert hr; cases r <;> decide

theorem pre_wp {k : Nat} (hk : k < N s₀) {s : State} (h : LInv AesCtr.ctrMode s₀ k s) :
    WP isa (.block (count ++ args)) s (Pre s₀ k s) := by
  have hR : s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  have hNl := UPre.N_le hp
  refine count_wp (Q := Iv s₀) (S := S s₀) (left := N s₀ - k) h.r16 h.r18 (by omega_using [hNl]) h.r19
    (by rw [hR]; exact in_rw (r := ivR s₀) (by simp) (Offset.contains_base _ (by decide) (by decide)))
    (by rw [hW]; exact in_rw (by simp) cSv0) fun s₁ r10₁ g₁ mem₁ rd₁ wr₁ => ?_
  -- The number of blocks.
  have hiv : bytesAt s.mem (Iv s₀) 16 = next (iv0 s₀) k := by rw [h.iv, chainK_ctr s₀ (by omega_using [hk])]
  have hlo := AesCtr.lo32_bytesAt s.mem (Iv s₀)
  rw [hiv, AesCtr.lo32_next (length_iv0 s₀)] at hlo
  have hm : s₁.gpr .r10 = BitVec.ofNat 64 (mOf s₀ k) := by rw [r10₁, ← hlo]; rfl
  unfold args mov
  refine wp_mr fun s₂ u₂ => wp_mr fun s₃ u₃ => wp_mr fun s₄ u₄ => wp_mr fun s₅ u₅ => ?_
  refine wp_mr fun s₆ u₆ => wp_mr fun s₇ u₇ => wp_nil ?_
  have g (r : Reg) (hr : r ∈ preserved) : s₇.gpr r = s.gpr r := by
    obtain ⟨h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := preserved_ne' hr
    rw [u₇.other _ h8, u₆.other _ h7, u₅.other _ h6, u₄.other _ h5, u₃.other _ h4, u₂.other _ h3,
      g₁ r h9 h10 h11 h12]
  have g₁' (r : Reg) (hr : r ∈ preserved) : s₁.gpr r = s.gpr r := by
    obtain ⟨-, -, -, -, -, -, h9, h10, h11, h12⟩ := preserved_ne' hr
    exact g₁ r h9 h10 h11 h12
  refine ⟨UPre.ctrCall hp hk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, g, ?_, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, g₁' .r14 (by decide), h.r14]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), g₁' .r15 (by decide), h.r15]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), g₁' .r16 (by decide), h.r16]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁' .r17 (by decide), h.r17]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), hm]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁' .r19 (by decide), h.r19]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁, h.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁, h.wr]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, mem₁, hm]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]

end

end VG.Proof.AesCtr.PPC64LE

end

end

/-!
# AES-CTR on PPC64LE: one iteration, and the loop

As on x86-64 (`Proof/AesCtr/X86_64/Verified.lean`): `iter_wp`, one run of
`body` takes AES-CBC's loop invariant for `ctrMode` from `k` blocks to
`k + mOf s₀ k`. The call gives CTR's output on its blocks
(`AesCtr.ctr32_crypt`), and the counter block it leaves, with the carry into
the first 96 bits if its last 32 bits wrapped around, is CTR's
(`AesCtr.ctr32_next`, `AesCtr.ctr32_wrap`, `AesCtr.carry_next`).
-/

@[expose] public section

namespace VG.Proof.AesCtr.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCtr.PPC64LE
open VG.Proof.AesCbc (Mode)
open VG.Proof.AesCbc.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (next toNat ofNat)

/-- What the call leaves, after `k` blocks. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  r14 : s.gpr .r14 = W s₀
  r15 : s.gpr .r15 = s₀.gpr .r4
  r16 : s.gpr .r16 = Iv s₀
  r17 : s.gpr .r17 = blk s₀ k
  r18 : s.gpr .r18 = BitVec.ofNat 64 (N s₀ - k)
  r19 : s.gpr .r19 = S s₀
  keep : ∀ r ∈ preserved, r ∉ vars → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩] (savedMem s₀) s.mem
  slot : s.mem.readW (S s₀ + BitVec.ofNat 64 2048) 64 = BitVec.ofNat 64 (mOf s₀ k)
  data : Spec.Cbc.blocksAt s.mem (Dp s₀) (N s₀) =
    outK AesCtr.ctrMode s₀ (k + mOf s₀ k) ++ (blks s₀).drop (k + mOf s₀ k)
  /-- The counter block: `t + k + m`, less `2³²` if its last 32 bits
  wrapped around. -/
  iv : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k < 2 ^ 32 →
    bytesAt s.mem (Iv s₀) 16 = next (iv0 s₀) (k + mOf s₀ k)
  ivw : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32 →
    bytesAt s.mem (Iv s₀) 16 = ofNat (toNat (next (iv0 s₀) k) + mOf s₀ k - 2 ^ 32) 16

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- The call, after the code before it. -/
theorem mid_wp {k : Nat} (hk : k < N s₀) {s s₁ : State} (h : LInv AesCtr.ctrMode s₀ k s)
    (a : Pre s₀ k s s₁) : WP isa ctrCall s₁ (Mid s₀ k) := by
  refine WP.mono (ctr_call a.call) fun s₂ c => ?_
  have g (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s.gpr r := by rw [c.saved r hr, a.saved r hr]
  obtain hm0 := mOf_pos hk
  obtain hle := mOf_le s₀ k
  have hdw := hp.data_wrap
  have hsw := hp.scr_wrap
  generalize hmd : mOf s₀ k = m at hm0 hle a c
  -- The memory before the call: the slot written.
  obtain f₁ : Frame [⟨S s₀ + BitVec.ofNat 64 2048, 8⟩] s.mem s₁.mem := by
    rw [a.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain slotSub : Region.Sub ⟨S s₀ + BitVec.ofNat 64 2048, 8⟩ ⟨S s₀, 2064⟩ := Offset.sub_base _ (by decide)
  obtain segSub : Region.Sub ⟨blk s₀ k, 16 * m⟩ (dataR s₀) := UPre.seg_sub (by omega_arith)
  have fc : Frame [⟨Iv s₀, 16⟩, ⟨blk s₀ k, 16 * m⟩, ⟨S s₀, 2048⟩] s₁.mem s₂.mem := c.frame
  obtain fAll : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩] s.mem s₂.mem :=
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, slotSub⟩).trans
    (fc.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨dataR s₀, by simp, segSub⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩)
  -- The slot after the call.
  obtain dSlot : ∀ r ∈ [⟨Iv s₀, 16⟩, ⟨blk s₀ k, 16 * m⟩, ⟨S s₀, 2048⟩],
      (⟨S s₀ + BitVec.ofNat 64 2048, 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.iv_scr.symm.sub_left (UPre.scr_sub (by decide))
    · exact (hp.data_scr.symm.sub_left (UPre.scr_sub (by decide))).sub_right segSub
    · exact Offset.disjoint_base _ (by decide) (by omega_arith)
  obtain slot : s₂.mem.readW (S s₀ + BitVec.ofNat 64 2048) 64 = BitVec.ofNat 64 m := by
    rw [fc.readW (r := ⟨S s₀ + BitVec.ofNat 64 2048, 8⟩) (Region.contains_self _ _) dSlot (by decide),
      a.mem, Mem.readW_writeW_self64, hmd]
  -- The data and the counter block before the call.
  obtain hiv : bytesAt s.mem (Iv s₀) 16 = next (iv0 s₀) k := by rw [h.iv, chainK_ctr s₀ (by omega_arith)]
  obtain ivIn : bytesAt s₁.mem (Iv s₀) 16 = next (iv0 s₀) k := by
    rw [Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.iv_scr.sub_right (UPre.scr_sub (by decide))) (by decide), hiv]
  obtain big₁ : Frame (Big s₀) s₀.mem s₁.mem := (UPre.big_of h.frame).trans (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩)
  obtain sched : bytesAt s₁.mem (W s₀) (16 * (R s₀ + 1)) = wK s₀ := UPre.sched_bytes hp big₁
  obtain hlen : (blks s₀).length = N s₀ := Proof.AesCbc.length_blocksAt _ _ _
  -- Blocks outside the call's.
  have outside (j : Nat) (hj : j < N s₀) (ho : j < k ∨ k + m ≤ j) :
      ∀ r ∈ [⟨S s₀ + BitVec.ofNat 64 2048, 8⟩, ⟨Iv s₀, 16⟩, ⟨blk s₀ k, 16 * m⟩, ⟨S s₀, 2048⟩],
        (⟨Dp s₀ + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint r := by
    intro r hr
    obtain dj : Region.Sub ⟨Dp s₀ + BitVec.ofNat 64 (16 * j), 16⟩ (dataR s₀) := Offset.sub_base _ (by omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hp.data_scr.sub_left dj).sub_right (UPre.scr_sub (by decide))
    · exact (hp.iv_data.symm.sub_left dj)
    · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    · exact (hp.data_scr.sub_left dj).sub_right (Region.sub_prefix (by decide))
  have keepBlocks {p : Addr} {a n : Nat} (hp' : p = Dp s₀ + BitVec.ofNat 64 (16 * a)) (hn : a + n ≤ N s₀)
      (ho : a + n ≤ k ∨ k + m ≤ a) : Spec.Cbc.blocksAt s₂.mem p n = Spec.Cbc.blocksAt s.mem p n := by
    subst hp'
    obtain hd : ∀ j < n, ∀ r ∈ [⟨S s₀ + BitVec.ofNat 64 2048, 8⟩, ⟨Iv s₀, 16⟩, ⟨blk s₀ k, 16 * m⟩,
        ⟨S s₀, 2048⟩], (⟨Dp s₀ + BitVec.ofNat 64 (16 * a) + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint r :=
      fun j hj => by
        rw [Offset.add_add, show 16 * a + 16 * j = 16 * (a + j) by omega_arith]
        exact outside (a + j) (by omega_arith) (by omega_arith)
    rw [AesCtr.blocksAt_frame fc (fun j hj r hr => hd j hj r (List.mem_cons_of_mem _ hr)),
      AesCtr.blocksAt_frame f₁ (fun j hj r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hd j hj _ (by simp))]
  have dataS := h.data
  rw [outK, AesCtr.ctrMode_out] at dataS
  -- The call's blocks.
  obtain segIn : Spec.Cbc.blocksAt s₁.mem (blk s₀ k) m = ((blks s₀).drop k).take m := by
    rw [AesCtr.blocksAt_frame f₁ (fun j hj r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [Offset.add_add, show 16 * k + 16 * j = 16 * (k + j) by omega_arith]
      exact (hp.data_scr.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (UPre.scr_sub (by decide))),
      ← AesCtr.blocksAt_take _ _ (show m ≤ N s₀ - k by omega_arith), ← AesCtr.blocksAt_drop _ _ (by omega_arith), dataS,
      List.drop_left' (by rw [AesCtr.length_crypt, List.length_take, hlen, Nat.min_eq_left (by omega_arith)])]
  obtain seg := AesCtr.ctr32_crypt (k := m) (by rw [ivIn, ← hmd]; exact lo32_mOf s₀ k) c.out
  rw [sched, ivIn, segIn] at seg
  have hctr := c.ctr
  rw [show Spec.Gcm.blockAt s₁.mem (Iv s₀) = Spec.Gcm.ofBytes (bytesAt s₁.mem (Iv s₀) 16) from rfl] at hctr
  refine ⟨by rw [g .r14 (by decide), h.r14], by rw [g .r15 (by decide), h.r15],
    by rw [g .r16 (by decide), h.r16], by rw [g .r17 (by decide), h.r17],
    by rw [g .r18 (by decide), h.r18], by rw [g .r19 (by decide), h.r19],
    fun r hr hv => by rw [g r hr, h.keep r hr hv], by rw [c.rd, a.rd, h.rd], by rw [c.wr, a.wr, h.wr],
    h.frame.trans fAll, by rw [hmd]; exact slot, ?_, ?_, ?_⟩
  · -- The data: the first `k` blocks and those after the call's as they were, and the call's.
    obtain hlc : (Spec.Ctr.crypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀) ((blks s₀).take k)).length = k := by
      rw [AesCtr.length_crypt, List.length_take, hlen, Nat.min_eq_left (by omega_arith)]
    obtain hA : Spec.Cbc.blocksAt s.mem (Dp s₀) k =
        Spec.Ctr.crypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀) ((blks s₀).take k) := by
      rw [← AesCtr.blocksAt_take _ _ (show k ≤ N s₀ by omega_arith), dataS, List.take_left' hlc]
    obtain hC : Spec.Cbc.blocksAt s.mem (Dp s₀ + BitVec.ofNat 64 (16 * (k + m))) (N s₀ - (k + m)) =
        (blks s₀).drop (k + m) := by
      rw [← AesCtr.blocksAt_drop _ _ (show k + m ≤ N s₀ by omega_arith), dataS]
      conv => lhs; rw [show k + m = (Spec.Ctr.crypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀)
        ((blks s₀).take k)).length + m by rw [hlc]]
      rw [List.drop_append, List.drop_eq_nil_of_le (by omega_arith), List.nil_append, hlc, Nat.add_sub_cancel_left]
      exact List.drop_drop
    rw [hmd, AesCtr.blocksAt_three s₂.mem (Dp s₀) (a := k) (b := m) (by omega_arith),
      keepBlocks (a := 0) (by simp) (by omega_arith) (by omega_arith), keepBlocks (a := k + m) rfl (by omega_arith) (by omega_arith),
      show Dp s₀ + BitVec.ofNat 64 (16 * k) = blk s₀ k from rfl, seg, hA, hC, outK, AesCtr.ctrMode_out]
    exact AesCtr.crypt_step _ _ _ (by omega_arith)
  · intro hw
    rw [hmd] at hw
    rw [hmd, AesCtr.ctr32_next (by rw [ivIn]; omega_arith) c.ctr, ivIn, AesCtr.next_add]
  · intro hw
    rw [hmd] at hw
    rw [hmd, AesCtr.ctr32_wrap (by rw [ivIn]; omega_arith) c.ctr, ivIn]

/-- The invariant after `k + m` blocks, from the facts the iteration ends with. -/
theorem finish {k m : Nat} (hkm : k + m ≤ N s₀) {s s' : State} (h : Mid s₀ k s) (hmd : mOf s₀ k = m)
    (g : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r17 → r ≠ .r18 → s'.gpr r = s.gpr r)
    (r17 : s'.gpr .r17 = blk s₀ (k + m)) (r18 : s'.gpr .r18 = BitVec.ofNat 64 (N s₀ - (k + m)))
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame [ivR s₀] s.mem s'.mem)
    (hiv : bytesAt s'.mem (Iv s₀) 16 = next (iv0 s₀) (k + m)) :
    LInv AesCtr.ctrMode s₀ (k + m) s' where
  r14 := by rw [g .r14 (by decide) (by decide) (by decide) (by decide) (by decide), h.r14]
  r15 := by rw [g .r15 (by decide) (by decide) (by decide) (by decide) (by decide), h.r15]
  r16 := by rw [g .r16 (by decide) (by decide) (by decide) (by decide) (by decide), h.r16]
  r17 := r17
  r18 := r18
  r19 := by rw [g .r19 (by decide) (by decide) (by decide) (by decide) (by decide), h.r19]
  keep r hr hv := by
    obtain ⟨-, -, -, -, -, -, h9, h10, h11, -⟩ := preserved_ne' hr
    rw [g r h9 h10 h11 (fun e => hv (by simp [e])) (fun e => hv (by simp [e])), h.keep r hr hv]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  frame := h.frame.trans (hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨ivR s₀, by simp, fun _ h => h⟩)
  data := by
    rw [AesCtr.blocksAt_frame hf (fun j hj r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.iv_data.symm.sub_left (Offset.sub_base _ (by omega_arith))), h.data, hmd]
  iv := by rw [hiv, chainK_ctr s₀ hkm]

omit hp in
theorem setWidth_beq_zero (y : BitVec 32) : (y.setWidth 64 == 0) = (y == 0) := by
  have := y.isLt
  by_cases h : y = 0
  · subst h; rfl
  · have h' : y.setWidth 64 ≠ 0 := fun e => h (by
      obtain e' := congrArg BitVec.toNat e
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans y.isLt (by decide))] at e'
      exact BitVec.eq_of_toNat_eq e')
    rw [beq_eq_false_iff_ne.mpr h', beq_eq_false_iff_ne.mpr h]

/-- What `adv` leaves. -/
structure After (s₀ : State) (k : Nat) (s s₂ : State) : Prop where
  gpr : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r17 → r ≠ .r18 → s₂.gpr r = s.gpr r
  r17 : s₂.gpr .r17 = blk s₀ (k + mOf s₀ k)
  r18 : s₂.gpr .r18 = BitVec.ofNat 64 (N s₀ - (k + mOf s₀ k))
  mem : s₂.mem = s.mem
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  ev : isa.eval (.zero .d .r9) s₂ = some (decide (AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32))

/-- On past the call's blocks, with the wrap of the counter in `r9`. -/
theorem adv_wp' {k : Nat} (hk : k < N s₀) {s : State} (h : Mid s₀ k s) : WP isa (.block adv) s (After s₀ k s) := by
  obtain hm0 := mOf_pos hk
  obtain hle := mOf_le s₀ k
  obtain hlo := lo32_mOf s₀ k
  have hdw := hp.data_wrap
  obtain hR : s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  refine adv_wp (Q := Iv s₀) (S := S s₀) (P := blk s₀ k) (left := N s₀ - k) (m := mOf s₀ k)
    h.r16 h.r17 h.r18 h.r19 h.slot hle (by omega_arith) (by rw [hR]; exact in_rw (by simp) cSv0)
    (by rw [hR]; exact in_rw (r := ivR s₀) (by simp) (Offset.contains_base _ (by decide) (by decide)))
    fun s₂ r18₂ r17₂ r9₂ g₂ m₂ rd₂ wr₂ => ?_
  refine ⟨g₂, ?_, by rw [r18₂, Nat.sub_sub], m₂, rd₂, wr₂, ?_⟩
  · rw [r17₂, Offset.add_add, show 16 * k + 16 * mOf s₀ k = 16 * (k + mOf s₀ k) by omega_arith]
  obtain hb := AesCtr.toNat_lt (show (next (iv0 s₀) k).length = 16 by
    rw [AesCtr.next_eq (length_iv0 s₀)]; exact AesCtr.length_ofNat _ _)
  obtain hlo2 := AesCtr.lo32_bytesAt s.mem (Iv s₀)
  rw [eval_zero, r9₂, setWidth_beq_zero]
  by_cases hw : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32
  · have e := h.ivw hw
    rw [e, AesCtr.lo32, AesCtr.toNat_ofNat] at hlo2
    have hw' := hw
    unfold AesCtr.lo32 at hw'
    have : (AesCtr.rv32 (s.mem.readW (Iv s₀ + BitVec.ofNat 64 12) 32)).toNat = 0 := by rw [← hlo2]; omega_arith
    obtain h0 := BitVec.eq_of_toNat_eq (y := (0 : BitVec 32)) this
    simp [h0, hw]
  · have e := h.iv (by omega_arith)
    rw [e, AesCtr.lo32_next (length_iv0 s₀)] at hlo2
    rw [AesCtr.lo32_next (length_iv0 s₀)] at hw hlo
    have : (AesCtr.rv32 (s.mem.readW (Iv s₀ + BitVec.ofNat 64 12) 32)).toNat ≠ 0 := by rw [← hlo2]; omega_arith
    obtain h0 : AesCtr.rv32 (s.mem.readW (Iv s₀ + BitVec.ofNat 64 12) 32) ≠ 0 := fun h0 => this (by rw [h0]; rfl)
    rw [AesCtr.lo32_next (length_iv0 s₀)]
    simp only [hw, decide_false, Option.some.injEq, beq_eq_false_iff_ne]
    exact h0

/-- The carry if the counter wrapped around. -/
theorem fin_wp {k : Nat} (hk : k < N s₀) {s s₂ : State} (h : Mid s₀ k s) (a : After s₀ k s s₂) :
    WP isa (.ite (.zero .d .r9) (.block carry) (.block [])) s₂ (LInv AesCtr.ctrMode s₀ (k + mOf s₀ k)) := by
  obtain hm0 := mOf_pos hk
  obtain hle := mOf_le s₀ k
  obtain hR : s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  obtain hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  obtain r16₂ : s₂.gpr .r16 = Iv s₀ := by rw [a.gpr _ (by decide) (by decide) (by decide) (by decide), h.r16]
  by_cases hw : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32
  · refine WP.ite true (by rw [a.ev]; simp [hw]) (fun _ => ?_) (fun h => by cases h)
    refine carry_wp r16₂
      (by rw [a.rd, a.wr, hR]; exact in_rw (r := ivR s₀) (by simp) cIv0)
      (by rw [a.rd, a.wr, hR]; exact in_rw (r := ivR s₀) (by simp) cIv8)
      (by rw [a.wr, hW]; exact in_rw (r := ivR s₀) (by simp) cIv0)
      (by rw [a.wr, hW]; exact in_rw (r := ivR s₀) (by simp) cIv8)
      fun s₃ g₃ bytes₃ f₃ rd₃ wr₃ => ?_
    refine finish hp (by omega_arith) h rfl
      (fun r h9 h10 h11 h17 h18 => by rw [g₃ r h9 h10 h11, a.gpr r h9 h10 h17 h18])
      (by rw [g₃ _ (by decide) (by decide) (by decide), a.r17])
      (by rw [g₃ _ (by decide) (by decide) (by decide), a.r18])
      (by rw [rd₃, a.rd]) (by rw [wr₃, a.wr]) (by rw [← a.mem]; exact f₃) ?_
    rw [bytes₃, a.mem, h.ivw hw]
    exact AesCtr.carry_next (length_iv0 s₀) hw
  · refine WP.ite false (by rw [a.ev]; simp [hw]) (fun h => by cases h) (fun _ => WP.block_nil ?_)
    exact finish hp (by omega_arith) h rfl (fun r h9 h10 _ h17 h18 => a.gpr r h9 h10 h17 h18) a.r17 a.r18
      a.rd a.wr (by rw [a.mem]; exact Frame.refl _ _)
      (by rw [a.mem, h.iv (by have := lo32_mOf s₀ k; omega_arith)])

/-- One iteration. -/
theorem iter_wp {k : Nat} (hk : k < N s₀) {s : State} (h : LInv AesCtr.ctrMode s₀ k s) :
    WP isa body s (LInv AesCtr.ctrMode s₀ (k + mOf s₀ k)) :=
  WP.seq (WP.mono (pre_wp hp hk h) fun _ a =>
    WP.seq (WP.mono (mid_wp hp hk h a) fun _ hm =>
      WP.seq (WP.mono (adv_wp' hp hk hm) fun _ a => fin_wp hp hk hm a)))

/-- The loop, from `k` blocks to all of them. -/
theorem loop_wp {k : Nat} (hk : k < N s₀) {s : State} (h : LInv AesCtr.ctrMode s₀ k s) :
    WP isa (.loop body (.nonzero .d .r18)) s (LInv AesCtr.ctrMode s₀ (N s₀)) := by
  obtain hN := (s₀.gpr .r7).isLt
  refine WP.loop (M := isa) (body := body) (c := .nonzero .d .r18) (Q := LInv AesCtr.ctrMode s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv AesCtr.ctrMode s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨j, rfl, hj, h⟩
  refine WP.mono (iter_wp hp hj h) fun s' h' => ?_
  obtain hm0 := mOf_pos hj
  obtain hle := mOf_le s₀ j
  obtain ev := eval_nonzero_ofNat' s' .r18 (k := N s₀ - (j + mOf s₀ j))
    (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hN) h'.r18
  by_cases hz' : j + mOf s₀ j = N s₀
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_⟩
    rwa [← hz']
  · right
    refine ⟨by rw [ev]; simp; omega_arith, N s₀ - (j + mOf s₀ j), by omega_arith, j + mOf s₀ j, rfl, by omega_arith, h'⟩

end

/-- The whole function. -/
theorem crypt_wp {s₀ : State} (h0 : (modePPC64LE AesCtr.ctrMode).pre s₀) :
    WP isa crypt s₀ (Done AesCtr.ctrMode s₀) :=
  ends_wp h0 fun hp hN _ h => loop_wp hp hN h

end VG.Proof.AesCtr.PPC64LE

end

end

/-!
# AES-CTR on PPC64LE: constant time

As on x86-64 (`Proof/AesCtr/X86_64/Verified.lean`): two runs from states that
agree on the public arguments and on the last 32 bits of the counter block
(`ctrPub`, which the contract's `leak` declares) are related piece by piece
(`RelCT`): the taint analysis covers the code between the call and the
branches, from the registers the correctness proof pins to the public
arguments and the stack pointer; the call is constant time by its own proof
(`ctr_rel`), with the same arguments in both runs, since the number of blocks
it takes depends only on the public data (`mOf_eq`); and the branches (the
carry, the loop) are on facts the correctness proof gives in terms of the
public data (`After.ev`, `iter_wp`).
-/

@[expose] public section

namespace VG.Proof.AesCtr.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCtr.PPC64LE
open VG.Proof.AesCbc.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (next toNat)

/-- What two runs agree on: the public arguments, and the last 32 bits of the
counter block. -/
def ctrPub (s₀ s₀' : State) : Prop :=
  (modePPC64LE AesCtr.ctrMode).pub s₀ s₀' ∧ AesCtr.lo32 (iv0 s₀) = AesCtr.lo32 (iv0 s₀')

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs vars) (.block (count ++ args)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem adv_taint : ∃ h, (taint.check (Taint.ofRegs [.r16, .r17, .r18, .r19]) (.block adv) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem carry_taint : ∃ h, (taint.check (Taint.ofRegs [.r16]) (.block carry) h).isSome = true :=
  ⟨_, by taint_decide⟩

section
variable {s₀ s₀' : State} (hq : (modePPC64LE AesCtr.ctrMode).pub s₀ s₀')
  (hl : AesCtr.lo32 (iv0 s₀) = AesCtr.lo32 (iv0 s₀'))
include hq hl

omit hq in
theorem lo32_next_eq (k : Nat) : AesCtr.lo32 (next (iv0 s₀) k) = AesCtr.lo32 (next (iv0 s₀') k) := by
  rw [AesCtr.lo32_next (length_iv0 _), AesCtr.lo32_next (length_iv0 _)]
  unfold AesCtr.lo32 at hl
  omega_using [hl]

theorem mOf_eq (k : Nat) : mOf s₀ k = mOf s₀' k := by
  have e := lo32_next_eq hl k
  rw [AesCtr.lo32_next (length_iv0 _), AesCtr.lo32_next (length_iv0 _)] at e
  unfold mOf
  rw [e, pub_N hq]

/-- One iteration, in two runs. -/
theorem body_rel (hp : UPre s₀) (hp' : UPre s₀') {k : Nat} (hk : k < N s₀) :
    RelCT isa (fun a b => LS AesCtr.ctrMode s₀ k a ∧ LS AesCtr.ctrMode s₀' k b) body
      fun a b => LS AesCtr.ctrMode s₀ (k + mOf s₀ k) a ∧ LS AesCtr.ctrMode s₀' (k + mOf s₀' k) b := by
  have hk' : k < N s₀' := by rw [← pub_N hq]; exact hk
  obtain ⟨_, t1⟩ := pre_taint
  obtain ⟨_, t3⟩ := adv_taint
  obtain ⟨_, tc⟩ := carry_taint
  obtain ⟨_, tn⟩ := nil_taint
  -- The code before the call.
  have p1 := (taintRegs (P := fun a b => LS AesCtr.ctrMode s₀ k a ∧ LS AesCtr.ctrMode s₀' k b) vars
    (fun _ _ h => ⟨by rw [h.1.2, h.2.2, pub_sp hq], LInv.agree hq h.1.1 h.2.1⟩) t1).wp
    (F₁ := fun (s₁ : State) => ∃ s, LS AesCtr.ctrMode s₀ k s ∧ Pre s₀ k s s₁ ∧ s₁.sp = s.sp)
    (F₂ := fun (s₁ : State) => ∃ s, LS AesCtr.ctrMode s₀' k s ∧ Pre s₀' k s s₁ ∧ s₁.sp = s.sp)
    fun a b h => ⟨WP.mono (wp_sp (pre_wp hp hk h.1.1)) fun _ ⟨x, e⟩ => ⟨a, h.1, x, e⟩,
      WP.mono (wp_sp (pre_wp hp' hk' h.2.1)) fun _ ⟨x, e⟩ => ⟨b, h.2, x, e⟩⟩
  -- The call, with the same arguments in both runs.
  have p2 := (ctr_rel (K := W s₀) (C := Iv s₀) (D := blk s₀ k) (S := S s₀) (R := R s₀) (n := mOf s₀ k)
    (P := fun a b => (∃ s, LS AesCtr.ctrMode s₀ k s ∧ Pre s₀ k s a ∧ a.sp = s.sp) ∧
      (∃ s, LS AesCtr.ctrMode s₀' k s ∧ Pre s₀' k s b ∧ b.sp = s.sp)) fun a b h => by
    obtain ⟨⟨s, hs, pa, ea⟩, ⟨t, ht, pb, eb⟩⟩ := h
    refine ⟨pa.call, ?_, by rw [ea, eb, hs.2, ht.2, pub_sp hq]⟩
    rw [pub_W hq, pub_Iv hq, pub_blk hq, pub_S hq, pub_R hq, mOf_eq hq hl]; exact pb.call).wp
    (F₁ := fun (s : State) => Mid s₀ k s ∧ s.sp = s₀.sp) (F₂ := fun (s : State) => Mid s₀' k s ∧ s.sp = s₀'.sp) fun a b h => by
      obtain ⟨⟨s, hs, pa, ea⟩, ⟨t, ht, pb, eb⟩⟩ := h
      exact ⟨WP.mono (wp_sp (mid_wp hp hk hs.1 pa)) fun _ ⟨x, e⟩ => ⟨x, e.trans (ea.trans hs.2)⟩,
        WP.mono (wp_sp (mid_wp hp' hk' ht.1 pb)) fun _ ⟨x, e⟩ => ⟨x, e.trans (eb.trans ht.2)⟩⟩
  -- On past the call's blocks.
  have p3 := (taintRegs (P := fun a b => (Mid s₀ k a ∧ a.sp = s₀.sp) ∧ (Mid s₀' k b ∧ b.sp = s₀'.sp))
    [.r16, .r17, .r18, .r19] (fun a b h => ⟨by rw [h.1.2, h.2.2, pub_sp hq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.1.1.r16, h.2.1.r16, pub_Iv hq]
      · rw [h.1.1.r17, h.2.1.r17, pub_blk hq]
      · rw [h.1.1.r18, h.2.1.r18, pub_N hq]
      · rw [h.1.1.r19, h.2.1.r19, pub_S hq]⟩) t3).wp
    (F₁ := fun (s₂ : State) => ∃ s, (Mid s₀ k s ∧ s.sp = s₀.sp) ∧ After s₀ k s s₂ ∧ s₂.sp = s.sp)
    (F₂ := fun (s₂ : State) => ∃ s, (Mid s₀' k s ∧ s.sp = s₀'.sp) ∧ After s₀' k s s₂ ∧ s₂.sp = s.sp)
    fun a b h => ⟨WP.mono (wp_sp (adv_wp' hp hk h.1.1)) fun _ ⟨x, e⟩ => ⟨a, h.1, x, e⟩,
      WP.mono (wp_sp (adv_wp' hp' hk' h.2.1)) fun _ ⟨x, e⟩ => ⟨b, h.2, x, e⟩⟩
  -- The carry if the counter wrapped around in both runs.
  have p4 : RelCT isa (fun a b => (∃ s, (Mid s₀ k s ∧ s.sp = s₀.sp) ∧ After s₀ k s a ∧ a.sp = s.sp) ∧
      (∃ s, (Mid s₀' k s ∧ s.sp = s₀'.sp) ∧ After s₀' k s b ∧ b.sp = s.sp))
      (.ite (.zero .d .r9) (.block carry) (.block [])) fun _ _ => True := by
    refine RelCT.ite (fun a b h => ?_) (taintRegs [.r16] (fun a b h => ?_) tc)
      (taintRegs [] (fun a b h => ?_) tn)
    · obtain ⟨⟨s, hs, xa, -⟩, ⟨t, ht, xb, -⟩⟩ := h
      rw [xa.ev, xb.ev, lo32_next_eq hl, mOf_eq hq hl]
    · obtain ⟨⟨⟨s, hs, xa, ea⟩, ⟨t, ht, xb, eb⟩⟩, _⟩ := h
      refine ⟨by rw [ea, eb, hs.2, ht.2, pub_sp hq], fun r hr => ?_⟩
      simp only [List.mem_singleton] at hr; subst hr
      rw [xa.gpr _ (by decide) (by decide) (by decide) (by decide),
        xb.gpr _ (by decide) (by decide) (by decide) (by decide), hs.1.r16, ht.1.r16, pub_Iv hq]
    · obtain ⟨⟨⟨s, hs, xa, ea⟩, ⟨t, ht, xb, eb⟩⟩, _⟩ := h
      exact ⟨by rw [ea, eb, hs.2, ht.2, pub_sp hq], fun r hr => by simp at hr⟩
  have p5 := p4.wp (F₁ := LS AesCtr.ctrMode s₀ (k + mOf s₀ k)) (F₂ := LS AesCtr.ctrMode s₀' (k + mOf s₀' k))
    fun a b h => by
      obtain ⟨⟨s, hs, xa, ea⟩, ⟨t, ht, xb, eb⟩⟩ := h
      exact ⟨WP.mono (wp_sp (fin_wp hp hk hs.1 xa)) fun _ ⟨x, e⟩ => ⟨x, e.trans (ea.trans hs.2)⟩,
        WP.mono (wp_sp (fin_wp hp' hk' ht.1 xb)) fun _ ⟨x, e⟩ => ⟨x, e.trans (eb.trans ht.2)⟩⟩
  exact (p1.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((p2.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((p3.mono (fun _ _ h => h) fun _ _ h => h.2).seq (p5.mono (fun _ _ h => h) fun _ _ h => h.2)))

/-- The loop's relation, with the number of blocks left. -/
def CRel (s₀ s₀' : State) (n : Nat) (a b : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ LS AesCtr.ctrMode s₀ k a ∧ LS AesCtr.ctrMode s₀' k b

theorem loop_rel (hp : UPre s₀) (hp' : UPre s₀') (n : Nat) :
    RelCT isa (CRel s₀ s₀' n) (.loop body (.nonzero .d .r18))
      fun a b => LS AesCtr.ctrMode s₀ (N s₀) a ∧ LS AesCtr.ctrMode s₀' (N s₀') b := by
  refine RelCT.loop (M := isa) (CRel s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  have hb₀ := (s₀.gpr .r7).isLt
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : CRel s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k < N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  have hm := mOf_eq hq hl k
  have hm0 := mOf_pos hk
  have hle := mOf_le s₀ k
  refine (body_rel hq hl hp hp' hk).mono (fun _ _ h => ⟨h.2.2.1, h.2.2.2⟩) fun s₁ s₂ ⟨l₁, l₂⟩ => ?_
  rw [← hm] at l₂
  have bd : N s₀ - (k + mOf s₀ k) < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hb₀
  have e₁ := eval_nonzero_ofNat' s₁ .r18 bd l₁.1.r18
  have e₂ := eval_nonzero_ofNat' s₂ .r18 (k := N s₀ - (k + mOf s₀ k)) bd (by rw [l₂.1.r18, hN])
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : k + mOf s₀ k = N s₀ := by
      have : N s₀ - (k + mOf s₀ k) = 0 := by simpa using hf
      omega_using [hk, hle, this]
    exact ⟨h0 ▸ l₁, by rw [← hN, ← h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : N s₀ - (k + mOf s₀ k) ≠ 0 := by simpa using ht
    exact ⟨N s₀ - (k + mOf s₀ k), by omega_using [hk, hm0], k + mOf s₀ k, rfl, by omega_using [h0], l₁, l₂⟩

end

/-- The whole function, in two runs that agree on the public data. -/
theorem crypt_rel {s₀ s₀' : State} (h0 : (modePPC64LE AesCtr.ctrMode).pre s₀)
    (h0' : (modePPC64LE AesCtr.ctrMode).pre s₀') (hq : ctrPub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') crypt fun _ _ => True :=
  ends_rel h0 h0' hq.1 fun hp hp' hN =>
    (loop_rel hq.1 hq.2 hp hp' (N s₀ - 0)).mono (fun _ _ h => ⟨0, rfl, hN, h.1, h.2⟩) fun _ _ h => h

theorem crypt_ct : ConstantTime isa (modePPC64LE AesCtr.ctrMode).pre ctrPub crypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (crypt_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesCtr.PPC64LE

end

end

/-!
# AES-CTR on PPC64LE: `Verified`

Correctness and constant time, from `crypt_wp` and `crypt_ct`, a state
satisfying the precondition, and the shared contract of
`Spec/Ctr/Contract.lean` (with no stack: a call stores nothing in memory),
whose `leak` (the counter block's last four bytes) gives the agreement on
the last 32 bits of the counter block `crypt_ct` assumes (`ctrPub`).
-/

@[expose] public section

namespace VG.Proof.AesCtr.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCtr.PPC64LE
open VG.Proof.AesCbc.PPC64LE

theorem crypt_correct (s : State) (hs : (modePPC64LE AesCtr.ctrMode).pre s) :
    ∃ t s', Exec isa crypt s t s' ∧ abiPreserved s s' ∧ (modePPC64LE AesCtr.ctrMode).post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := crypt_wp hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem crypt_verified : Verified PPC64LE.target crypt (Proof.AesCtr.roundsContract PPC64LE.abi) :=
  Verified.of_correct (k := { modePPC64LE AesCtr.ctrMode with pub := ctrPub }) crypt_correct crypt_ct
    { pre := by sig_implies_pre [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, modePPC64LE, PPC64LE.abi,
        PPC64LE.argRegs]
      -- `ctrMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, modePPC64LE, AesCtr.ctrMode, PPC64LE.abi,
          PPC64LE.argRegs]
        sig_reduce [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, modePPC64LE, AesCtr.ctrMode, PPC64LE.abi,
          PPC64LE.argRegs] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by
        have hm : ∀ s₁ s₂, (Proof.AesCtr.roundsContract PPC64LE.abi).pre s₁ → (Proof.AesCtr.roundsContract PPC64LE.abi).pre s₂ →
            (Proof.AesCtr.roundsContract PPC64LE.abi).pub s₁ s₂ → (modePPC64LE AesCtr.ctrMode).pub s₁ s₂ := by
          sig_implies_pub [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, modePPC64LE, PPC64LE.abi, PPC64LE.argRegs]
        intro s₁ s₂ h₁ h₂ h
        refine ⟨hm s₁ s₂ h₁ h₂ h, ?_⟩
        sig_pub [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, Spec.Ctr.ctrLeak, PPC64LE.abi, PPC64LE.argRegs] at h
        sig_split h
        exact AesCtr.lo32_of_leak (Proof.Cmac.bytesAt_length _ _ _) (Proof.Cmac.bytesAt_length _ _ _)
          (by assumption)
      sat := by sig_implies_sat [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, modePPC64LE, PPC64LE.abi,
        PPC64LE.argRegs] [sat] using sat }

end VG.Proof.AesCtr.PPC64LE
