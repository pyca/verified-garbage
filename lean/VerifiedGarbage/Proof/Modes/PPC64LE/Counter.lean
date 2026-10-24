module

import VerifiedGarbage.Proof.AesCtr.Inc
public import VerifiedGarbage.Impl.Modes.PPC64LE.Counter
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Ctr
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# CTR on PPC64LE: the increments

`incAt` run once, with its memory as explicit writes (`incMem`): the
counter's two doublewords, loaded byte-reversed, the second plus 1 and the
first plus the carry out of it (`1 - nz`, `nz_toNat`), stored byte-reversed.
`incMem_apply`: the block it writes is `Spec.Ctr.inc` of the one it read.
`inc32At`, GCM's `inc₃₂` of a counter block's last word, likewise
(`inc32Mem`, `inc32Mem_apply`): the big-endian word plus 1, modulo 2³².
-/

@[expose] public section

namespace VG.Proof.Modes.PPC64LE.Counter

open VG VG.PPC64LE VG.Impl.Modes.PPC64LE
open VG.Spec.Aes (bytesAt)

section
variable {is : List Instr} {s : State} {P : State → Prop}

/-- `ldbrx t, a, b`. -/
private theorem wp_ldbrx {t a b : Reg} {ea : Addr} (hn : a ≠ .r0) (hea : s.gpr a + s.gpr b = ea)
    (hin : InRegions (s.rd ++ s.wr) ea 8)
    (k : ∀ s', Upd s s' t (rev64 (s.mem.readW ea 64)) → WP isa (.block is) s' P) :
    WP isa (.block (.loadRev .d t a b :: is)) s P := by
  refine WP.cons (s' := s.write t (rev64 (s.mem.readW ea 64))) ?_ (k _ (Upd.write _ _ _))
  rw [exec_loadRev_d hn (by rw [hea]; exact hin), hea]

/-- `stdbrx t, a, b`. -/
private theorem wp_stdbrx {t a b : Reg} {ea : Addr} (hn : a ≠ .r0) (hea : s.gpr a + s.gpr b = ea)
    (hout : InRegions s.wr ea 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW ea (rev64 (s.gpr t))) → WP isa (.block is) s' P) :
    WP isa (.block (.storeRev .d t a b :: is)) s P := by
  refine WP.cons (s' := { s with mem := s.mem.writeW ea (rev64 (s.gpr t)) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl⟩)
  rw [exec_storeRev_d hn (by rw [hea]; exact hout), hea]

/-- `or d, n, m`. -/
private theorem wp_or {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' P) :
    WP isa (.block (.logic .or d n m :: is)) s P :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

end

/-! ## The 128-bit increment -/

/-- `1` iff `x` is nonzero, as `incAt` computes it. -/
abbrev nz (x : BitVec 64) : BitVec 64 := ((0 - x) ||| x) >>> 63

theorem nz_toNat (x : BitVec 64) : (nz x).toNat = if x.toNat = 0 then 0 else 1 := by
  have hx := x.isLt
  have hor := ((0 - x) ||| x).isLt
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  split
  · rename_i h
    have e : x = 0 := BitVec.eq_of_toNat_eq (by simpa using h)
    subst e
    rfl
  · rename_i h
    have hn : (0 - x).toNat = 2 ^ 64 - x.toNat := by
      have e0 : (0 : BitVec 64).toNat = 0 := rfl
      rw [BitVec.toNat_sub, e0]; omega
    have h1 : x.toNat ≤ ((0 - x) ||| x).toNat := by rw [BitVec.toNat_or]; exact Nat.right_le_or
    have h2 : (0 - x).toNat ≤ ((0 - x) ||| x).toNat := by rw [BitVec.toNat_or]; exact Nat.left_le_or
    omega

/-- The memory after `incAt` on the block at `Q`. -/
def incMem (m : Mem) (Q : Addr) : Mem :=
  let lo := rev64 (m.readW (Q + BitVec.ofNat 64 8) 64) + 1
  let hi := rev64 (m.readW Q 64) + 1 - nz lo
  (m.writeW (Q + BitVec.ofNat 64 8) (rev64 lo)).writeW Q (rev64 hi)

theorem inc_wp {base : Reg} {off : Nat} (hb : base ≠ .r0) (h8 : base ≠ .r8) (h9 : base ≠ .r9)
    (ho : off + 8 < 2 ^ 15) {s : State} {Q : Addr} (ha : s.gpr base + BitVec.ofNat 64 off = Q)
    (hr : InRegions (s.rd ++ s.wr) Q 8) (hr8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (hw : InRegions s.wr Q 8) (hw8 : InRegions s.wr (Q + BitVec.ofNat 64 8) 8)
    {is : List Instr} {P : State → Prop}
    (k : ∀ s', s'.mem = incMem s.mem Q → (∀ r, r ≠ .r8 → r ≠ .r9 → s'.gpr r = s.gpr r) →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' P) :
    WP isa (.block (incAt base off ++ is)) s P := by
  have a8 : s.gpr base + BitVec.ofNat 64 (off + 8) = Q + BitVec.ofNat 64 8 := by
    rw [← ha, VG.Offset.add_add]
  have sp : (s.mem.writeW (Q + BitVec.ofNat 64 8) (rev64 (rev64 (s.mem.readW (Q + BitVec.ofNat 64 8) 64) + 1))).readW
      Q 64 = s.mem.readW Q 64 := by
    have := Mem.readW_writeW_sep (m := s.mem) (w := 64) (w' := 64)
      (v := rev64 (rev64 (s.mem.readW (Q + BitVec.ofNat 64 8) 64) + 1))
      (VG.Offset.sep Q (d := 0) (n := 8) (e := 8) (k := 8) (by decide) (by decide) (by decide)) (by decide)
    simpa using this
  simp only [incAt, List.cons_append]
  refine wp_li (by omega) fun s₁ u₁ => ?_
  refine wp_ldbrx (t := .r8) (a := base) (b := .r9) (ea := Q + BitVec.ofNat 64 8) hb (by rw [u₁.gpr, u₁.other _ h9]; exact a8) (by rw [u₁.rd, u₁.wr]; exact hr8)
    fun s₂ u₂ => ?_
  refine wp_addi (by decide) (by decide) fun s₃ u₃ => ?_
  have b₃ : s₃.gpr base + s₃.gpr .r9 = Q + BitVec.ofNat 64 8 := by
    rw [u₃.other _ h8, u₂.other _ h8, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, u₁.other _ h9]
    exact a8
  refine wp_stdbrx (t := .r8) hb b₃ (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hw8) fun s₄ u₄ => ?_
  refine wp_li (by decide) fun s₅ u₅ => ?_
  refine wp_sub fun s₆ u₆ => ?_
  refine wp_or fun s₇ u₇ => ?_
  refine wp_lsr (by decide) fun s₈ u₈ => ?_
  refine wp_li (by omega) fun s₉ u₉ => ?_
  have gb : ∀ {t : State}, (∀ r, r ≠ .r8 → r ≠ .r9 → t.gpr r = s.gpr r) → t.gpr base = s.gpr base :=
    fun ht => ht _ h8 h9
  have g₉ : ∀ r, r ≠ .r8 → r ≠ .r9 → s₉.gpr r = s.gpr r := fun r a b => by
    rw [u₉.other r a, u₈.other r b, u₇.other r b, u₆.other r b, u₅.other r b, u₄.gpr, u₃.other r a,
      u₂.other r a, u₁.other r b]
  have m₉ : s₉.mem = s.mem.writeW (Q + BitVec.ofNat 64 8) (rev64 (rev64 (s.mem.readW (Q + BitVec.ofNat 64 8) 64) + 1)) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₃.mem, u₂.gpr, u₂.mem, u₁.mem]
    rfl
  refine wp_ldbrx (t := .r8) (a := base) (b := .r8) (ea := Q) hb (by rw [u₉.gpr, gb g₉]; exact ha)
    (by rw [u₉.rd, u₉.wr, u₈.rd, u₈.wr, u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr,
      u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hr) fun s₁₀ u₁₀ => ?_
  refine wp_addi (by decide) (by decide) fun s₁₁ u₁₁ => ?_
  refine wp_sub fun s₁₂ u₁₂ => ?_
  refine wp_li (by omega) fun s₁₃ u₁₃ => ?_
  have g₁₂ : ∀ r, r ≠ .r8 → r ≠ .r9 → s₁₂.gpr r = s.gpr r := fun r a b => by
    rw [u₁₂.other r a, u₁₁.other r a, u₁₀.other r a, g₉ r a b]
  refine wp_stdbrx (t := .r8) (a := base) (b := .r9) (ea := Q) hb (by rw [u₁₃.gpr, u₁₃.other _ h9, gb g₁₂]; exact ha)
    (by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
        exact hw) fun s₁₄ u₁₄ => ?_
  refine k s₁₄ ?_ (fun r a b => by rw [u₁₄.gpr, u₁₃.other r b, g₁₂ r a b])
    (by rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  have r8₁₂ : s₁₂.gpr .r8 = rev64 (s.mem.readW Q 64) + 1 -
      nz (rev64 (s.mem.readW (Q + BitVec.ofNat 64 8) 64) + 1) := by
    simp (disch := decide) only [u₁₂.gpr, u₁₁.gpr, u₁₀.gpr, u₁₁.other, u₁₀.other, m₉, sp, u₉.other, u₈.gpr,
      u₇.gpr, u₆.gpr, u₅.gpr, u₆.other, u₅.other, u₄.gpr, u₃.gpr, u₂.gpr, u₁.mem]
    rfl
  rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, m₉, u₁₃.other _ (by decide), r8₁₂]
  rfl

/-- The counter's bytes after `incAt`: `Spec.Ctr.inc` of those before. -/
theorem incMem_bytes (m : Mem) (Q : Addr) : bytesAt (incMem m Q) Q 16 = Spec.Ctr.inc (bytesAt m Q 16) := by
  have hl := (rev64 (m.readW (Q + BitVec.ofNat 64 8) 64)).isLt
  apply AesCtr.inc_words64
  · show (AesCtr.rv64 _ + 1).toNat = _
    rw [BitVec.toNat_add]; rfl
  · show (AesCtr.rv64 _ + 1 - nz (AesCtr.rv64 _ + 1)).toNat = _
    have e1 : (1 : BitVec 64).toNat = 1 := rfl
    have hz := nz_toNat (AesCtr.rv64 (m.readW (Q + BitVec.ofNat 64 8) 64) + 1)
    rw [BitVec.toNat_add, e1] at hz
    have hh := (AesCtr.rv64 (m.readW Q 64)).isLt
    have hl' := (AesCtr.rv64 (m.readW (Q + BitVec.ofNat 64 8) 64)).isLt
    rw [BitVec.toNat_sub, BitVec.toNat_add, e1, hz]
    split <;> (simp only [Nat.reducePow] at *; omega)

theorem incMem_frame (m : Mem) (Q : Addr) : Frame [⟨Q, 16⟩] m (incMem m Q) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (VG.Offset.contains_base Q (d := 8) (n := 8) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (by simpa using VG.Offset.contains_base Q (d := 0) (n := 8) (k := 16) (by decide) (by decide))

/-- The counter's bytes, with every other byte unchanged. -/
theorem incMem_apply (m : Mem) (Q x : Addr) :
    incMem m Q x = if (x - Q).toNat < 16 then
      (Spec.Ctr.inc (bytesAt m Q 16)).getD (x - Q).toNat 0 else m x := by
  split
  · rename_i hi
    have e := congrArg (fun bs : List Byte => bs.getD (x - Q).toNat 0) (incMem_bytes m Q)
    simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some] at e
    have ex : Q + BitVec.ofNat 64 (x - Q).toNat = x := by bv_omega
    rwa [ex] at e
  · rename_i hi
    exact incMem_frame m Q x (by
      intro r hr hc
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Region.Contains] at hc
      omega)

/-! ## GCM's `inc₃₂` -/

/-- The memory after `inc32At` on the word at `Q`. -/
def inc32Mem (m : Mem) (Q : Addr) : Mem :=
  m.writeW Q (rev32 (((rev32 (m.readW Q 32)).setWidth 64 + 1).setWidth 32))

theorem inc32_wp {base : Reg} {off : Nat} (hb : base ≠ .r0) (h8 : base ≠ .r8) (h9 : base ≠ .r9)
    (ho : off < 2 ^ 15) {s : State} {Q : Addr} (ha : s.gpr base + BitVec.ofNat 64 off = Q)
    (hr : InRegions (s.rd ++ s.wr) Q 4) (hw : InRegions s.wr Q 4) {is : List Instr} {P : State → Prop}
    (k : ∀ s', s'.mem = inc32Mem s.mem Q → (∀ r, r ≠ .r8 → r ≠ .r9 → s'.gpr r = s.gpr r) →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' P) :
    WP isa (.block (inc32At base off ++ is)) s P := by
  simp only [inc32At, List.cons_append]
  refine wp_li ho fun s₁ u₁ => ?_
  refine wp_lwbrx (t := .r8) (a := base) (b := .r9) (ea := Q) hb (by rw [u₁.gpr, u₁.other _ h9]; exact ha) (by rw [u₁.rd, u₁.wr]; exact hr)
    fun s₂ u₂ => ?_
  refine wp_addi (by decide) (by decide) fun s₃ u₃ => ?_
  have b₃ : s₃.gpr base + s₃.gpr .r9 = Q := by
    rw [u₃.other _ h8, u₂.other _ h8, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, u₁.other _ h9]
    exact ha
  refine wp_stwbrx (t := .r8) hb b₃ (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hw) fun s₄ u₄ => ?_
  refine k s₄ ?_ (fun r a b => by rw [u₄.gpr, u₃.other r a, u₂.other r a, u₁.other r b])
    (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  rw [u₄.mem, u₃.mem, u₂.mem, u₃.gpr, u₂.gpr, u₁.mem]
  rfl

theorem setWidth_add_one (x : BitVec 32) : ((x.setWidth 64 + 1).setWidth 32) = x + 1 := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  have e1 : (1 : BitVec 64).toNat = 1 := rfl
  have e2 : (1 : BitVec 32).toNat = 1 := rfl
  rw [e1, e2]
  simp only [Nat.reducePow] at *
  omega

/-- The word `inc32At` writes: the big-endian number it held, plus 1,
modulo 2³². -/
theorem inc32Mem_bytes (m : Mem) (Q : Addr) :
    bytesAt (inc32Mem m Q) Q 4 = Spec.Ctr.ofNat (Spec.Ctr.toNat (bytesAt m Q 4) + 1) 4 := by
  have e : inc32Mem m Q = m.writeW Q (AesCtr.rv32 (AesCtr.rv32 (m.readW Q 32) + 1)) := by
    rw [inc32Mem, setWidth_add_one]; rfl
  rw [e, AesCtr.bytesAt_writeW_rv32, AesCtr.bytesAt_rv32, AesCtr.toNat_ofNat]
  apply AesCtr.ofNat_congr
  have := (AesCtr.rv32 (m.readW Q 32)).isLt
  have e₁ : (1 : BitVec 32).toNat = 1 := rfl
  rw [BitVec.toNat_add, e₁]
  simp only [Nat.reducePow]
  omega

theorem inc32Mem_frame (m : Mem) (Q : Addr) : Frame [⟨Q, 4⟩] m (inc32Mem m Q) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (by simpa using VG.Offset.contains_base Q (d := 0) (n := 4) (k := 4) (by decide) (by decide))

/-- The word's bytes, with every other byte unchanged. -/
theorem inc32Mem_apply (m : Mem) (Q x : Addr) :
    inc32Mem m Q x = if (x - Q).toNat < 4 then
      (Spec.Ctr.ofNat (Spec.Ctr.toNat (bytesAt m Q 4) + 1) 4).getD (x - Q).toNat 0 else m x := by
  split
  · rename_i hi
    have e := congrArg (fun bs : List Byte => bs.getD (x - Q).toNat 0) (inc32Mem_bytes m Q)
    simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some] at e
    have ex : Q + BitVec.ofNat 64 (x - Q).toNat = x := by bv_omega
    rw [ex] at e
    rw [e]
    simp only [bytesAt, List.getD_eq_getElem?_getD]
  · rename_i hi
    exact inc32Mem_frame m Q x (by
      intro r hr hc
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Region.Contains] at hc
      omega)

end VG.Proof.Modes.PPC64LE.Counter
