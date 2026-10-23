module

public import VerifiedGarbage.Impl.AesCfb8.PPC64LE
public import VerifiedGarbage.Proof.AesCfb8.Mem
public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# AES-CFB8 on PPC64LE: the code between the calls

The straight-line pieces of a byte, each run in continuation-passing style:
the data byte XORed with the first byte of the enciphered block (`encByte`,
`decByte`), and the input block shifted (`shift`), its two words each
becoming their upper seven bytes with the next byte above them, the memory
AArch64's `extr` leaves (`shiftMemX`, `Proof/AesCfb8/Mem.lean`, by
`extr_eq`).
-/

@[expose] public section

namespace VG.Proof.AesCfb8.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCfb8.PPC64LE
open VG.Impl.AesCbc.PPC64LE (cOff)

theorem read1 (m : Mem) (a : Addr) : m.read a 1 = m a := by
  have := Mem.extractLsb'_read m a (n := 1) (j := 0) (by decide)
  rw [BitVec.add_zero] at this
  rw [← this]
  exact (BitVec.extractLsb'_eq_self (x := m.read a 1)).symm

theorem write1 (m : Mem) (a : Addr) (v : BitVec (8 * 1)) : m.write a 1 v = m.writeW a v := by
  simp [Mem.writeW]

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `lbz t, off(n)`. -/
theorem wp_lbz {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' t ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.lbz t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t ((s.mem a).setWidth 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_lbz hn ho (by rw [ha]; exact hin), ha, read1]

/-- `stb t, off(n)`. -/
theorem wp_stb {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.stb t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 8) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl⟩)
  rw [exec_stb hn ho (by rw [ha]; exact hout), ha, write1]

/-- `or d, n, m`. -/
theorem wp_or {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

end

/-- The byte instructions of `encPost`. -/
def encByte : List Instr :=
  [.lbz .r9 .r17 0, .lbz .r10 .r19 cOff, .logic .xor .r9 .r9 .r10, .stb .r9 .r17 0]

/-- The byte instructions of `decPost`. -/
def decByte : List Instr :=
  [.lbz .r9 .r17 0, .lbz .r10 .r19 cOff, .logic .xor .r10 .r10 .r9, .stb .r10 .r17 0]

theorem encPost_eq : encPost = encByte ++ (shift ++ advance) := rfl

theorem decPost_eq : decPost = decByte ++ (shift ++ advance) := rfl

theorem zext_xor (a b : Byte) : a.setWidth 64 ^^^ b.setWidth 64 = (a ^^^ b).setWidth 64 := by
  ext i hi; simp

theorem low_zext (a : Byte) : (a.setWidth 64).setWidth 8 = a := by
  ext i hi; simp

theorem encByte_wp {s : State} {P T : Addr} {rest : List Instr} {Φ : State → Prop}
    (hp : s.gpr .r17 = P) (ht : s.gpr .r19 + BitVec.ofNat 64 2048 = T)
    (rP : InRegions (s.rd ++ s.wr) P 1) (rT : InRegions (s.rd ++ s.wr) T 1) (wP : InRegions s.wr P 1)
    (k : ∀ s', s'.gpr .r9 = (s.mem P ^^^ s.mem T).setWidth 64 →
      (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem.writeW P (s.mem P ^^^ s.mem T) → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block rest) s' Φ) :
    WP isa (.block (encByte ++ rest)) s Φ := by
  simp only [encByte, List.cons_append, List.nil_append]
  refine wp_lbz (a := P) (by decide) (by decide) (by rw [hp]; simp) rP fun s₁ u₁ => ?_
  refine wp_lbz (a := T) (by decide) (by decide) (by rw [u₁.other _ (by decide)]; exact ht)
    (by rw [u₁.rd, u₁.wr]; exact rT) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  have v₃ : s₃.gpr .r9 = (s.mem P ^^^ s.mem T).setWidth 64 := by
    rw [u₃.gpr, u₂.other _ (by decide), u₂.gpr, u₁.gpr, u₁.mem, zext_xor]
  refine wp_stb (a := P) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hp]; simp)
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact wP) fun s₄ u₄ => ?_
  refine k s₄ (by rw [u₄.gpr, v₃]) (fun r h9 h10 => ?_) ?_ ?_ ?_
  · rw [u₄.gpr, u₃.other _ h9, u₂.other _ h10, u₁.other _ h9]
  · rw [u₄.mem, v₃, low_zext, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]

theorem decByte_wp {s : State} {P T : Addr} {rest : List Instr} {Φ : State → Prop}
    (hp : s.gpr .r17 = P) (ht : s.gpr .r19 + BitVec.ofNat 64 2048 = T)
    (rP : InRegions (s.rd ++ s.wr) P 1) (rT : InRegions (s.rd ++ s.wr) T 1) (wP : InRegions s.wr P 1)
    (k : ∀ s', s'.gpr .r9 = (s.mem P).setWidth 64 →
      (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem.writeW P (s.mem T ^^^ s.mem P) → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block rest) s' Φ) :
    WP isa (.block (decByte ++ rest)) s Φ := by
  simp only [decByte, List.cons_append, List.nil_append]
  refine wp_lbz (a := P) (by decide) (by decide) (by rw [hp]; simp) rP fun s₁ u₁ => ?_
  refine wp_lbz (a := T) (by decide) (by decide) (by rw [u₁.other _ (by decide)]; exact ht)
    (by rw [u₁.rd, u₁.wr]; exact rT) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  have v₃ : s₃.gpr .r10 = (s.mem T ^^^ s.mem P).setWidth 64 := by
    rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, u₁.mem, zext_xor]
  refine wp_stb (a := P) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hp]; simp)
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact wP) fun s₄ u₄ => ?_
  refine k s₄ (by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr])
    (fun r h9 h10 => ?_) ?_ ?_ ?_
  · rw [u₄.gpr, u₃.other _ h10, u₂.other _ h10, u₁.other _ h9]
  · rw [u₄.mem, v₃, low_zext, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-- `extr`'s result: the 64 bits of `x : y` above bit 8. -/
theorem extr_eq (x y : BitVec 64) : (x ++ y).extractLsb' 8 64 = (y >>> 8) ||| (x <<< 56) := by
  ext i hi
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append, BitVec.getElem_or,
    BitVec.getElem_ushiftRight, BitVec.getElem_shiftLeft]
  by_cases h : 8 + i < 64
  · have h' : i < 56 := by omega
    simp [h, h']
  · have h' : ¬ i < 56 := by omega
    simp only [h, h', ↓reduceIte, decide_false, Bool.not_false, Bool.true_and]
    rw [BitVec.getLsbD_of_ge y (8 + i) (by omega), Bool.false_or, BitVec.getLsbD_eq_getElem (by omega)]
    congr 1; omega

/-- The input block at `Q` shifted left by a byte, with the byte in `r9`
shifted in. -/
theorem shift_wp {s : State} {Q : Addr} {c : Byte} {rest : List Instr} {Φ : State → Prop}
    (hq : s.gpr .r16 = Q) (hc : s.gpr .r9 = c.setWidth 64)
    (r0 : InRegions (s.rd ++ s.wr) Q 8) (r8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (w0 : InRegions s.wr Q 8) (w8 : InRegions s.wr (Q + BitVec.ofNat 64 8) 8)
    (k : ∀ s', (∀ r, r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → s'.gpr r = s.gpr r) →
      s'.mem = AesCfb8.shiftMemX s.mem Q c → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block rest) s' Φ) :
    WP isa (.block (shift ++ rest)) s Φ := by
  simp only [shift, List.cons_append, List.nil_append]
  refine wp_ld (a := Q) (by decide) (by decide) (by rw [hq]; simp) r0 fun s₁ u₁ => ?_
  refine wp_ld (a := Q + BitVec.ofNat 64 8) (by decide) (by decide) (by rw [u₁.other _ (by decide), hq])
    (by rw [u₁.rd, u₁.wr]; exact r8) fun s₂ u₂ => ?_
  refine wp_lsr (by decide) fun s₃ u₃ => wp_lsl (by decide) fun s₄ u₄ => wp_or fun s₅ u₅ => ?_
  refine wp_lsr (by decide) fun s₆ u₆ => wp_lsl (by decide) fun s₇ u₇ => wp_or fun s₈ u₈ => ?_
  have q₈ : s₈.gpr .r16 = Q := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hq]
  have m₈ : s₈.mem = s.mem := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have w₀ : s₈.gpr .r10 = (s.mem.readW (Q + BitVec.ofNat 64 8) 64 ++ s.mem.readW Q 64).extractLsb' 8 64 := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr,
      u₄.other .r10 (by decide), u₃.gpr, u₃.other .r11 (by decide), u₂.gpr, u₂.other .r10 (by decide),
      u₁.gpr, u₁.mem, extr_eq]
  have w₁ : s₈.gpr .r11 = (c.setWidth 64 ++ s.mem.readW (Q + BitVec.ofNat 64 8) 64).extractLsb' 8 64 := by
    rw [u₈.gpr, u₇.gpr, u₇.other .r11 (by decide), u₆.gpr, u₆.other .r9 (by decide),
      u₅.other .r11 (by decide), u₅.other .r9 (by decide), u₄.other .r11 (by decide), u₄.other .r9 (by decide),
      u₃.other .r11 (by decide), u₃.other .r9 (by decide), u₂.gpr, u₂.other .r9 (by decide),
      u₁.other .r9 (by decide), u₁.mem, hc, extr_eq]
  refine wp_std (a := Q) (by decide) (by decide) (by rw [q₈]; simp)
    (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact w0) fun s₉ u₉ => ?_
  refine wp_std (a := Q + BitVec.ofNat 64 8) (by decide) (by decide) (by rw [u₉.gpr, q₈])
    (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact w8) fun s₁₀ u₁₀ => ?_
  refine k s₁₀ (fun r h10 h11 h12 => ?_) ?_ ?_ ?_
  · rw [u₁₀.gpr, u₉.gpr, u₈.other _ h11, u₇.other _ h12, u₆.other _ h11, u₅.other _ h10,
      u₄.other _ h12, u₃.other _ h10, u₂.other _ h11, u₁.other _ h10]
  · rw [u₁₀.mem, u₉.gpr, u₉.mem, m₈, w₀, w₁]; rfl
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

end VG.Proof.AesCfb8.PPC64LE
