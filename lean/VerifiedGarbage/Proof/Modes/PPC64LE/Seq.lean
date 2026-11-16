module

public import VerifiedGarbage.Proof.Modes.PPC64LE.Core
public import VerifiedGarbage.Impl.Modes.PPC64LE.Seq
public import VerifiedGarbage.Proof.Modes.Ops
public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.ByteStep
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesCtr.Inc
public import VerifiedGarbage.Impl.Modes.PPC64LE.Counter
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Ctr
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Impl.Modes.PPC64LE.Wide
public import VerifiedGarbage.Proof.Modes.Steps
public import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.TCB.PPC64LE.Target

/-! ### `Modes.PPC64LE.Step`, which only this module used -/

section

/-! ### `Modes.PPC64LE.Ops`, which only this module used -/

section

/-! ### `Modes.PPC64LE.Counter`, which only this module used -/

section

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
  obtain hor := ((0 - x) ||| x).isLt
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  split
  · rename_i h
    obtain e : x = 0 := BitVec.eq_of_toNat_eq (by simpa using h)
    subst e
    rfl
  · rename_i h
    obtain hn : (0 - x).toNat = 2 ^ 64 - x.toNat := by
      have e0 : (0 : BitVec 64).toNat = 0 := rfl
      rw [BitVec.toNat_sub, e0]; omega_using [h]
    obtain h1 : x.toNat ≤ ((0 - x) ||| x).toNat := by rw [BitVec.toNat_or]; exact Nat.right_le_or
    obtain h2 : (0 - x).toNat ≤ ((0 - x) ||| x).toNat := by rw [BitVec.toNat_or]; exact Nat.left_le_or
    omega_using [hn, h1, h2]

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
  obtain a8 : s.gpr base + BitVec.ofNat 64 (off + 8) = Q + BitVec.ofNat 64 8 := by
    rw [← ha, VG.Offset.add_add]
  obtain sp : (s.mem.writeW (Q + BitVec.ofNat 64 8) (rev64 (rev64 (s.mem.readW (Q + BitVec.ofNat 64 8) 64) + 1))).readW
      Q 64 = s.mem.readW Q 64 := by
    have := Mem.readW_writeW_sep (m := s.mem) (w := 64) (w' := 64)
      (v := rev64 (rev64 (s.mem.readW (Q + BitVec.ofNat 64 8) 64) + 1))
      (VG.Offset.sep Q (d := 0) (n := 8) (e := 8) (k := 8) (by decide) (by decide) (by decide)) (by decide)
    simpa using this
  simp only [incAt, List.cons_append]
  refine wp_li (by omega_using [ho]) fun s₁ u₁ => ?_
  refine wp_ldbrx (t := .r8) (a := base) (b := .r9) (ea := Q + BitVec.ofNat 64 8) hb (by rw [u₁.gpr, u₁.other _ h9]; exact a8) (by rw [u₁.rd, u₁.wr]; exact hr8)
    fun s₂ u₂ => ?_
  refine wp_addi (by decide) (by decide) fun s₃ u₃ => ?_
  obtain b₃ : s₃.gpr base + s₃.gpr .r9 = Q + BitVec.ofNat 64 8 := by
    rw [u₃.other _ h8, u₂.other _ h8, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, u₁.other _ h9]
    exact a8
  refine wp_stdbrx (t := .r8) hb b₃ (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hw8) fun s₄ u₄ => ?_
  refine wp_li (by decide) fun s₅ u₅ => ?_
  refine wp_sub fun s₆ u₆ => ?_
  refine wp_or fun s₇ u₇ => ?_
  refine wp_lsr (by decide) fun s₈ u₈ => ?_
  refine wp_li (by omega_using [ho]) fun s₉ u₉ => ?_
  obtain gb : ∀ {t : State}, (∀ r, r ≠ .r8 → r ≠ .r9 → t.gpr r = s.gpr r) → t.gpr base = s.gpr base :=
    fun ht => ht _ h8 h9
  obtain g₉ : ∀ r, r ≠ .r8 → r ≠ .r9 → s₉.gpr r = s.gpr r := fun r a b => by
    rw [u₉.other r a, u₈.other r b, u₇.other r b, u₆.other r b, u₅.other r b, u₄.gpr, u₃.other r a,
      u₂.other r a, u₁.other r b]
  obtain m₉ : s₉.mem = s.mem.writeW (Q + BitVec.ofNat 64 8) (rev64 (rev64 (s.mem.readW (Q + BitVec.ofNat 64 8) 64) + 1)) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₃.mem, u₂.gpr, u₂.mem, u₁.mem]
    rfl
  refine wp_ldbrx (t := .r8) (a := base) (b := .r8) (ea := Q) hb (by rw [u₉.gpr, gb g₉]; exact ha)
    (by rw [u₉.rd, u₉.wr, u₈.rd, u₈.wr, u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr,
      u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hr) fun s₁₀ u₁₀ => ?_
  refine wp_addi (by decide) (by decide) fun s₁₁ u₁₁ => ?_
  refine wp_sub fun s₁₂ u₁₂ => ?_
  refine wp_li (by omega_using [ho]) fun s₁₃ u₁₃ => ?_
  obtain g₁₂ : ∀ r, r ≠ .r8 → r ≠ .r9 → s₁₂.gpr r = s.gpr r := fun r a b => by
    rw [u₁₂.other r a, u₁₁.other r a, u₁₀.other r a, g₉ r a b]
  refine wp_stdbrx (t := .r8) (a := base) (b := .r9) (ea := Q) hb (by rw [u₁₃.gpr, u₁₃.other _ h9, gb g₁₂]; exact ha)
    (by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
        exact hw) fun s₁₄ u₁₄ => ?_
  refine k s₁₄ ?_ (fun r a b => by rw [u₁₄.gpr, u₁₃.other r b, g₁₂ r a b])
    (by rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  obtain r8₁₂ : s₁₂.gpr .r8 = rev64 (s.mem.readW Q 64) + 1 -
      nz (rev64 (s.mem.readW (Q + BitVec.ofNat 64 8) 64) + 1) := by
    simp (disch := decide) only [u₁₂.gpr, u₁₁.gpr, u₁₀.gpr, u₁₁.other, u₁₀.other, m₉, sp, u₉.other, u₈.gpr,
      u₇.gpr, u₆.gpr, u₅.gpr, u₆.other, u₅.other, u₄.gpr, u₃.gpr, u₂.gpr, u₁.mem]
    rfl
  rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, m₉, u₁₃.other _ (by decide), r8₁₂]
  rfl

/-- The counter's bytes after `incAt`: `Spec.Ctr.inc` of those before. -/
theorem incMem_bytes (m : Mem) (Q : Addr) : bytesAt (incMem m Q) Q 16 = Spec.Ctr.inc (bytesAt m Q 16) := by
  obtain hl := (rev64 (m.readW (Q + BitVec.ofNat 64 8) 64)).isLt
  apply AesCtr.inc_words64
  · show (AesCtr.rv64 _ + 1).toNat = _
    rw [BitVec.toNat_add]; rfl
  · show (AesCtr.rv64 _ + 1 - nz (AesCtr.rv64 _ + 1)).toNat = _
    have e1 : (1 : BitVec 64).toNat = 1 := rfl
    obtain hz := nz_toNat (AesCtr.rv64 (m.readW (Q + BitVec.ofNat 64 8) 64) + 1)
    rw [BitVec.toNat_add, e1] at hz
    obtain hh := (AesCtr.rv64 (m.readW Q 64)).isLt
    obtain hl' := (AesCtr.rv64 (m.readW (Q + BitVec.ofNat 64 8) 64)).isLt
    rw [BitVec.toNat_sub, BitVec.toNat_add, e1, hz]
    split <;> (simp only [Nat.reducePow] at *; omega_arith)

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
    obtain e := congrArg (fun bs : List Byte => bs.getD (x - Q).toNat 0) (incMem_bytes m Q)
    simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some] at e
    obtain ex : Q + BitVec.ofNat 64 (x - Q).toNat = x := by bv_omega_arith
    rwa [ex] at e
  · rename_i hi
    exact incMem_frame m Q x (by
      intro r hr hc
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Region.Contains] at hc
      omega_using [hi, hc])

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
  obtain b₃ : s₃.gpr base + s₃.gpr .r9 = Q := by
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
  omega_using []

/-- The word `inc32At` writes: the big-endian number it held, plus 1,
modulo 2³². -/
theorem inc32Mem_bytes (m : Mem) (Q : Addr) :
    bytesAt (inc32Mem m Q) Q 4 = Spec.Ctr.ofNat (Spec.Ctr.toNat (bytesAt m Q 4) + 1) 4 := by
  obtain e : inc32Mem m Q = m.writeW Q (AesCtr.rv32 (AesCtr.rv32 (m.readW Q 32) + 1)) := by
    rw [inc32Mem, setWidth_add_one]; rfl
  rw [e, AesCtr.bytesAt_writeW_rv32, AesCtr.bytesAt_rv32, AesCtr.toNat_ofNat]
  apply AesCtr.ofNat_congr
  have := (AesCtr.rv32 (m.readW Q 32)).isLt
  have e₁ : (1 : BitVec 32).toNat = 1 := rfl
  rw [BitVec.toNat_add, e₁]
  simp only [Nat.reducePow]
  omega_using []

theorem inc32Mem_frame (m : Mem) (Q : Addr) : Frame [⟨Q, 4⟩] m (inc32Mem m Q) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (by simpa using VG.Offset.contains_base Q (d := 0) (n := 4) (k := 4) (by decide) (by decide))

/-- The word's bytes, with every other byte unchanged. -/
theorem inc32Mem_apply (m : Mem) (Q x : Addr) :
    inc32Mem m Q x = if (x - Q).toNat < 4 then
      (Spec.Ctr.ofNat (Spec.Ctr.toNat (bytesAt m Q 4) + 1) 4).getD (x - Q).toNat 0 else m x := by
  split
  · rename_i hi
    obtain e := congrArg (fun bs : List Byte => bs.getD (x - Q).toNat 0) (inc32Mem_bytes m Q)
    simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some] at e
    obtain ex : Q + BitVec.ofNat 64 (x - Q).toNat = x := by bv_omega_arith
    rw [ex] at e
    rw [e]
    simp only [bytesAt, List.getD_eq_getElem?_getD]
  · rename_i hi
    exact inc32Mem_frame m Q x (by
      intro r hr hc
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Region.Contains] at hc
      omega_using [hi, hc])

end VG.Proof.Modes.PPC64LE.Counter

end

end


/-!
# The modes' operations on PPC64LE

`opsCode_wp`: the code of a list of operations (`Core.opsCode`) does to
the bytes of the three areas in memory what `applyOps` says (with the
areas' contents read from memory, `cont`), and changes nothing else in
memory, and no register but `r8` and `r9`. It needs each area's address
(`AreasOk.ea`: the base register and displacement of the area give the
address `A l` plus the offset, with an encodable displacement), readable
and writable bytes, and areas apart from each other. The operations are
copies and XORs (`opCode_wp_plain`) and the counters' increments
(`Proof/Modes/PPC64LE/Counter.lean`).
-/

@[expose] public section

namespace VG.Proof.Modes.PPC64LE

open VG VG.PPC64LE VG.Impl.Modes VG.Impl.Modes.PPC64LE
open VG.Spec.Aes (bytesAt)

/-- The areas' contents, from memory: byte `i` of area `l` at `A l + i`. -/
def cont (A : Loc → Addr) (m : Mem) : Areas := fun l i => m (A l + BitVec.ofNat 64 i)

/-- The areas of the step, of lengths `len`, at `A` in `s`: each operand's
address, readable (or writable) and apart. -/
structure AreasOk (c : Core) (s : State) (len : Loc → Nat) (A : Loc → Addr) (ws : List Loc) : Prop where
  ea : ∀ l off, off < len l →
    s.gpr (c.loc l).1 + BitVec.ofNat 64 ((c.loc l).2 + off) = A l + BitVec.ofNat 64 off
  disp : ∀ l off, off < len l → (c.loc l).2 + off < 2 ^ 15
  rd : ∀ l off w, 0 < w → off + w ≤ len l → InRegions (s.rd ++ s.wr) (A l + BitVec.ofNat 64 off) w
  wr : ∀ l ∈ ws, ∀ off w, 0 < w → off + w ≤ len l → InRegions s.wr (A l + BitVec.ofNat 64 off) w
  apart : ∀ l l', l ≠ l' → Region.Disjoint ⟨A l, len l⟩ ⟨A l', len l'⟩
  fit : ∀ l, len l < 2 ^ 32

theorem AreasOk.congr {c : Core} {s s' : State} {len : Loc → Nat} {A : Loc → Addr} {ws : List Loc}
    (h : AreasOk c s len A ws) (hg : ∀ l, s'.gpr (c.loc l).1 = s.gpr (c.loc l).1) (hr : s'.rd = s.rd)
    (hw : s'.wr = s.wr) : AreasOk c s' len A ws :=
  ⟨fun l off ho => by rw [hg l]; exact h.ea l off ho, h.disp,
    fun l off w hw0 ho => by rw [hr, hw]; exact h.rd l off w hw0 ho,
    fun l hl off w hw0 ho => by rw [hw]; exact h.wr l hl off w hw0 ho, h.apart, h.fit⟩

/-- Every area. -/
def allLocs : List Loc := [.dat, .chn, .buf]

theorem mem_allLocs (l : Loc) : l ∈ allLocs := by cases l <;> simp [allLocs]

/-- An operation that is a copy or an XOR, not an increment. -/
def Plain (o : Op) : Prop := o.inc = false ∧ o.inc32 = false

/-- Memory after `o`: its destination's bytes are `Op.val` of the areas. -/
def opMem (A : Loc → Addr) (o : Op) (m : Mem) : Mem := fun x =>
  if (x - (A o.dst + BitVec.ofNat 64 o.dOff)).toNat < o.width then
    o.val (cont A m) (x - (A o.dst + BitVec.ofNat 64 o.dOff)).toNat
  else m x

theorem write4_apply (m : Mem) (a x : Addr) (v : BitVec 32) :
    m.writeW a v x = if (x - a).toNat < 4 then v.extractLsb' (8 * (x - a).toNat) 8 else m x := by
  simp only [Mem.writeW, Mem.write]
  rfl

theorem byte_xor (u v : BitVec 32) (t : Nat) :
    (u ^^^ v).extractLsb' (8 * t) 8 = u.extractLsb' (8 * t) 8 ^^^ v.extractLsb' (8 * t) 8 := by
  ext j hj
  simp

theorem setWidth_xor8 (u v : Byte) : (u.setWidth 64 ^^^ v.setWidth 64).setWidth 8 = u ^^^ v := by
  ext j hj
  simp

theorem setWidth_xor32 (u v : BitVec 32) : (u.setWidth 64 ^^^ v.setWidth 64).setWidth 32 = u ^^^ v := by
  ext j hj
  simp

theorem setWidth32_64 (u : BitVec 32) : (u.setWidth 64).setWidth 32 = u := by
  ext j hj
  simp

theorem width_pos (o : Op) : 0 < o.width := by
  unfold Op.width; split <;> (try split) <;> (try split) <;> decide

theorem loc_ne (c : Core) (l : Loc) : (c.loc l).1 ≠ .r8 ∧ (c.loc l).1 ≠ .r9 ∧ (c.loc l).1 ≠ .r0 := by
  cases l <;> simp [Core.loc, sb]

/-! ## One operation -/

theorem opCode_wp_plain (c : Core) {len : Loc → Nat} {A : Loc → Addr} {ws : List Loc} {o : Op}
    (hpl : Plain o) (ho : o.InBounds len)
    (hdst : o.dst ∈ ws) {s : State} (h : AreasOk c s len A ws) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.mem = opMem A o s.mem → (∀ r, r ≠ .r8 → r ≠ .r9 → s'.gpr r = s.gpr r) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (c.opCode o ++ is)) s Q := by
  obtain ⟨hd, hs, hx⟩ := ho
  obtain ⟨hinc, hi32⟩ := hpl
  obtain hw0 := width_pos o
  -- Each base register, through writes of `r8` and `r9`.
  obtain keep : ∀ {t : State}, (∀ r, r ≠ .r8 → r ≠ .r9 → t.gpr r = s.gpr r) → ∀ l,
      t.gpr (c.loc l).1 = s.gpr (c.loc l).1 := fun ht l => ht _ (loc_ne c l).1 (loc_ne c l).2.1
  obtain eaD := h.ea o.dst o.dOff (by omega_arith)
  obtain eaS := h.ea o.src o.sOff (by omega_arith)
  obtain dD := h.disp o.dst o.dOff (by omega_arith)
  obtain dS := h.disp o.src o.sOff (by omega_arith)
  obtain nD := (loc_ne c o.dst).2.2
  obtain nS := (loc_ne c o.src).2.2
  simp only [Core.opCode, hinc, hi32, Bool.false_eq_true, ite_false]
  cases hwd : o.wide
  · -- A byte.
    obtain hW : o.width = 1 := by simp [Op.width, hinc, hi32, hwd]
    rw [hW] at hd hs hx
    simp only [Bool.false_eq_true, ite_false]
    cases hxr : o.xr with
    | none =>
      simp only [List.nil_append, List.cons_append]
      refine wp_lbz nS dS eaS (h.rd _ _ _ (by decide) hs) fun s₁ u₁ => ?_
      refine wp_stb (a := A o.dst + BitVec.ofNat 64 o.dOff) nD dD (by rw [keep (fun r h1 _ => u₁.other r h1) o.dst]; exact eaD)
        (by rw [u₁.wr]; exact h.wr _ hdst _ _ (by decide) hd) fun s₂ u₂ => ?_
      refine k s₂ ?_ (fun r h1 _ => by rw [u₂.gpr, u₁.other r h1]) (by rw [u₂.rd, u₁.rd])
        (by rw [u₂.wr, u₁.wr])
      funext x
      rw [u₂.mem, u₁.mem, u₁.gpr, setWidth8_64, write1_apply]
      simp only [opMem, hW, Op.val, hinc, hi32, Bool.false_eq_true, ite_false, hxr, cont, byte_xor_zero]
      split
      · rename_i hlt; rw [show (x - (A o.dst + BitVec.ofNat 64 o.dOff)).toNat = 0 by omega_arith, Nat.add_zero]
      · rfl
    | some p =>
      obtain ⟨l, off⟩ := p
      obtain hx' := hx l off hxr
      obtain eaX := h.ea l off (by omega_arith)
      obtain dX := h.disp l off (by omega_arith)
      simp only [List.cons_append]
      refine wp_lbz nS dS eaS (h.rd _ _ _ (by decide) hs) fun s₁ u₁ => ?_
      refine wp_lbz (a := A l + BitVec.ofNat 64 off) (loc_ne c l).2.2 dX (by rw [keep (fun r h1 _ => u₁.other r h1) l]; exact eaX)
        (by rw [u₁.rd, u₁.wr]; exact h.rd _ _ _ (by decide) hx') fun s₂ u₂ => ?_
      refine wp_xor fun s₃ u₃ => ?_
      refine wp_stb (a := A o.dst + BitVec.ofNat 64 o.dOff) nD dD (by
          rw [keep (fun r h1 h2 => by rw [u₃.other r h1, u₂.other r h2, u₁.other r h1]) o.dst]
          exact eaD)
        (by rw [u₃.wr, u₂.wr, u₁.wr]; exact h.wr _ hdst _ _ (by decide) hd) fun s₄ u₄ => ?_
      refine k s₄ ?_ (fun r h1 h2 => by rw [u₄.gpr, u₃.other r h1, u₂.other r h2, u₁.other r h1])
        (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
      funext x
      rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem,
        setWidth_xor8, write1_apply]
      simp only [opMem, hW, Op.val, hinc, hi32, Bool.false_eq_true, ite_false, hxr, cont]
      split
      · rename_i hlt; rw [show (x - (A o.dst + BitVec.ofNat 64 o.dOff)).toNat = 0 by omega_arith,
          Nat.add_zero, Nat.add_zero]
      · rfl
  · -- A word.
    obtain hW : o.width = 4 := by simp [Op.width, hinc, hi32, hwd]
    rw [hW] at hd hs hx
    simp only [ite_true]
    cases hxr : o.xr with
    | none =>
      simp only [List.nil_append, List.cons_append]
      refine wp_lwz nS dS eaS (h.rd _ _ _ (by decide) hs) fun s₁ u₁ => ?_
      refine wp_stw (a := A o.dst + BitVec.ofNat 64 o.dOff) nD dD (by rw [keep (fun r h1 _ => u₁.other r h1) o.dst]; exact eaD)
        (by rw [u₁.wr]; exact h.wr _ hdst _ _ (by decide) hd) fun s₂ u₂ => ?_
      refine k s₂ ?_ (fun r h1 _ => by rw [u₂.gpr, u₁.other r h1]) (by rw [u₂.rd, u₁.rd])
        (by rw [u₂.wr, u₁.wr])
      funext x
      rw [u₂.mem, u₁.mem, u₁.gpr, setWidth32_64, write4_apply]
      simp only [opMem, hW, Op.val, hinc, hi32, Bool.false_eq_true, ite_false, hxr, cont, byte_xor_zero]
      split
      · rename_i hlt; rw [← Mem.readW_byte s.mem _ hlt, VG.Offset.add_add]
      · rfl
    | some p =>
      obtain ⟨l, off⟩ := p
      obtain hx' := hx l off hxr
      obtain eaX := h.ea l off (by omega_arith)
      obtain dX := h.disp l off (by omega_arith)
      simp only [List.cons_append]
      refine wp_lwz nS dS eaS (h.rd _ _ _ (by decide) hs) fun s₁ u₁ => ?_
      refine wp_lwz (a := A l + BitVec.ofNat 64 off) (loc_ne c l).2.2 dX (by rw [keep (fun r h1 _ => u₁.other r h1) l]; exact eaX)
        (by rw [u₁.rd, u₁.wr]; exact h.rd _ _ _ (by decide) hx') fun s₂ u₂ => ?_
      refine wp_xor fun s₃ u₃ => ?_
      refine wp_stw (a := A o.dst + BitVec.ofNat 64 o.dOff) nD dD (by
          rw [keep (fun r h1 h2 => by rw [u₃.other r h1, u₂.other r h2, u₁.other r h1]) o.dst]
          exact eaD)
        (by rw [u₃.wr, u₂.wr, u₁.wr]; exact h.wr _ hdst _ _ (by decide) hd) fun s₄ u₄ => ?_
      refine k s₄ ?_ (fun r h1 h2 => by rw [u₄.gpr, u₃.other r h1, u₂.other r h2, u₁.other r h1])
        (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
      funext x
      rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem,
        setWidth_xor32, write4_apply]
      simp only [opMem, hW, Op.val, hinc, hi32, Bool.false_eq_true, ite_false, hxr, cont]
      split
      · rename_i hlt; rw [byte_xor, ← Mem.readW_byte s.mem _ hlt, ← Mem.readW_byte s.mem _ hlt,
          VG.Offset.add_add, VG.Offset.add_add]
      · rfl

/-- Any operation: a copy or an XOR (`opCode_wp_plain`), or an increment
(`Counter.inc_wp`, `Counter.inc32_wp`). -/
theorem opCode_wp (c : Core) {len : Loc → Nat} {A : Loc → Addr} {ws : List Loc} {o : Op}
    (ho : o.InBounds len)
    (hdst : o.dst ∈ ws) {s : State} (h : AreasOk c s len A ws) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.mem = opMem A o s.mem → (∀ r, r ≠ .r8 → r ≠ .r9 → s'.gpr r = s.gpr r) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (c.opCode o ++ is)) s Q := by
  have hd := ho.1
  obtain nD := loc_ne c o.dst
  have eb (n : Nat) : bytesAt s.mem (A o.dst + BitVec.ofNat 64 o.dOff) n =
      (List.range n).map fun i => cont A s.mem o.dst (o.dOff + i) := by
    simp only [bytesAt, cont, VG.Offset.add_add]
  cases hinc : o.inc
  · cases hi32 : o.inc32
    · exact opCode_wp_plain c ⟨hinc, hi32⟩ ho hdst h k
    · -- GCM's `inc₃₂`.
      obtain hW : o.width = 4 := by simp [Op.width, hinc, hi32]
      rw [hW] at hd
      simp only [Core.opCode, hinc, hi32, Bool.false_eq_true, ite_false, ite_true]
      refine Counter.inc32_wp nD.2.2 nD.1 nD.2.1 (h.disp o.dst o.dOff (by omega_arith)) (h.ea o.dst o.dOff (by omega_arith))
        (h.rd _ _ _ (by decide) hd) (h.wr _ hdst _ _ (by decide) hd) fun s' m' g' rd' wr' => k s' ?_ g' rd' wr'
      rw [m']
      funext x
      rw [Counter.inc32Mem_apply, eb]
      simp only [opMem, hW, Op.val, hinc, hi32, Bool.false_eq_true, ite_false, ite_true]
  · -- The 128-bit increment.
    obtain hW : o.width = 16 := by simp [Op.width, hinc]
    rw [hW] at hd
    simp only [Core.opCode, hinc, ite_true]
    obtain hdisp := h.disp o.dst (o.dOff + 8) (by omega_arith)
    refine Counter.inc_wp nD.2.2 nD.1 nD.2.1 (by omega_arith) (h.ea o.dst o.dOff (by omega_arith))
      (h.rd _ _ _ (by decide) (by omega_arith)) (by rw [VG.Offset.add_add]; exact h.rd _ _ _ (by decide) (by omega_arith))
      (h.wr _ hdst _ _ (by decide) (by omega_arith)) (by rw [VG.Offset.add_add]; exact h.wr _ hdst _ _ (by decide) (by omega_arith))
      fun s' m' g' rd' wr' => k s' ?_ g' rd' wr'
    rw [m']
    funext x
    rw [Counter.incMem_apply, eb]
    simp only [opMem, hW, Op.val, hinc, ite_true]

/-! ## Areas -/

/-- The regions of the areas `ws`. -/
def areaRegions (len : Loc → Nat) (A : Loc → Addr) (ws : List Loc) : List Region :=
  ws.map fun l => ⟨A l, len l⟩

theorem sub_self_add (p : Addr) {i : Nat} (hi : i < 2 ^ 64) : (p + BitVec.ofNat 64 i - p).toNat = i := by
  rw [VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

theorem contains_area {p : Addr} {n i : Nat} (hi : i < n) (hn : n ≤ 2 ^ 64) :
    (⟨p, n⟩ : Region).Contains (p + BitVec.ofNat 64 i) 1 := by
  simp only [Region.Contains]; rw [sub_self_add p (by omega_arith)]; omega_arith

/-- A byte the destination of `o` writes is in its area. -/
theorem in_dst {len : Loc → Nat} {A : Loc → Addr} {o : Op} (ho : o.InBounds len) (hfit : len o.dst < 2 ^ 32)
    {x : Addr} (hx : (x - (A o.dst + BitVec.ofNat 64 o.dOff)).toNat < o.width) :
    (⟨A o.dst, len o.dst⟩ : Region).Contains x 1 := by
  have := (VG.Offset.lt_iff x (A o.dst) (d := o.dOff) (n := o.width) (by have := ho.1; omega_arith)).mp hx
  simp only [Region.Contains]; have := ho.1; omega_arith

theorem opMem_frame {len : Loc → Nat} {A : Loc → Addr} {ws : List Loc} {o : Op} (ho : o.InBounds len)
    (hdst : o.dst ∈ ws) (hfit : ∀ l, len l < 2 ^ 32) (m : Mem) :
    Frame (areaRegions len A ws) m (opMem A o m) := by
  intro x hx
  simp only [opMem]
  rw [ite_eq_right fun h => hx _ (List.mem_map.mpr ⟨_, hdst, rfl⟩) (in_dst ho (hfit _) h)]

theorem opMem_cont {c : Core} {s : State} {len : Loc → Nat} {A : Loc → Addr} {ws : List Loc}
    (h : AreasOk c s len A ws) {o : Op}
    (ho : o.InBounds len) (m : Mem) : Agree len (cont A (opMem A o m)) (o.apply (cont A m)) := by
  intro l i hi
  obtain hl := h.fit l
  simp only [cont, opMem, Op.apply]
  by_cases hd : l = o.dst
  · subst hd
    obtain e := VG.Offset.lt_iff (A o.dst + BitVec.ofNat 64 i) (A o.dst) (d := o.dOff) (n := o.width)
      (by have := ho.1; omega_arith)
    rw [sub_self_add _ (by omega_arith)] at e
    by_cases hc : o.dOff ≤ i ∧ i < o.dOff + o.width
    · rw [ite_eq_left (e.mpr hc), ite_eq_left ⟨rfl, hc⟩]
      congr 1
      rw [← VG.Offset.add_add_eq (A o.dst) (Nat.add_sub_cancel' hc.1), sub_self_add _ (by omega_arith)]
    · rw [ite_eq_right (fun h' => hc (e.mp h')), ite_eq_right (fun h' => hc h'.2)]
  · rw [ite_eq_right (fun h' => h.apart l o.dst hd _ (contains_area hi (by omega_arith)) (in_dst ho (h.fit _) h')),
      ite_eq_right (fun h' => hd h'.1)]

/-! ## Lists of operations -/

theorem opsCode_wp (c : Core) {len : Loc → Nat} {A : Loc → Addr} {ws : List Loc} :
    ∀ {os : List Op}, (∀ o ∈ os, o.InBounds len ∧ o.dst ∈ ws) → ∀ {s : State},
    AreasOk c s len A ws → ∀ {is : List Instr} {Q : State → Prop},
    (∀ s', Agree len (cont A s'.mem) (applyOps os (cont A s.mem)) →
      Frame (areaRegions len A ws) s.mem s'.mem →
      (∀ r, r ≠ .r8 → r ≠ .r9 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block is) s' Q) →
    WP isa (.block (c.opsCode os ++ is)) s Q
  | [], _, s, _, is, Q, k => by
    simpa [Core.opsCode] using k s (fun _ _ _ => rfl) (Frame.refl _ _) (fun _ _ _ => rfl) rfl rfl
  | o :: os, hb, s, h, is, Q, k => by
    obtain ho := (hb o List.mem_cons_self)
    rw [show c.opsCode (o :: os) ++ is = c.opCode o ++ (c.opsCode os ++ is) by
      simp [Core.opsCode, List.append_assoc]]
    refine opCode_wp c ho.1 ho.2 h fun s₁ m₁ g₁ rd₁ wr₁ => ?_
    obtain h₁ : AreasOk c s₁ len A ws :=
      h.congr (fun l => g₁ _ (loc_ne c l).1 (loc_ne c l).2.1) rd₁ wr₁
    refine opsCode_wp c (fun o' ho' => hb o' (List.mem_cons_of_mem _ ho')) h₁
      fun s' a' f' g' rd' wr' => ?_
    refine k s' (fun l i hi => ?_) ?_ (fun r h1 h2 => by rw [g' r h1 h2, g₁ r h1 h2])
      (by rw [rd', rd₁]) (by rw [wr', wr₁])
    · rw [a' l i hi, applyOps_cons]
      refine applyOps_agree (fun o' ho' => (hb o' (List.mem_cons_of_mem _ ho')).1)
        (fun l' i' hi' => ?_) l i hi
      rw [m₁]; exact opMem_cont h ho.1 _ l' i' hi'
    · rw [m₁] at f'; exact (opMem_frame ho.1 ho.2 h.fit _).trans f'

end VG.Proof.Modes.PPC64LE

end

end


/-!
# One step of a mode on PPC64LE

`body_wp`: one run of the loop's body (`Core.body`) takes the invariant
(`Inv`) from `j` steps done to `j + 1`. After `j` steps, the data are the
outputs of the mode's step function `F` on the first `j` input steps
followed by the other inputs, the chaining value is `F`'s after them, the
data pointer and the steps left are in `r31` and `r30`, and the key is
ready. The step's three areas (`areas`) are the data's step `j`, the
chaining value's slots and the first `bl` bytes of the core's buffer;
`pre` and `post` are `opsCode_wp`, the block cipher `crypt_wp`, which
enciphers the buffer's bytes as `ciphB` (`BufCipher`), and
`ComputesB M L bl ciphB F` relates them to `F`.

A step takes `d` from `r30`, which holds `n₀ - d j` after `j` steps: one
block a step (`body_wp`, `loop_wp`: `bl = 4 bw`, `d = 1`, `n₀ = n`), or a
group of `2 ^ lg` blocks (`loopWide_wp`: `bl = 4 bw 2 ^ lg`, `d = 2 ^ lg`,
`n = n₀ / d`), the loop going on while `r8 = r30 >> lg` is not zero, as on
RISC-V (`Proof/Modes/RISCV64/Step.lean`). The key is ready for the regions
`W`, which hold the data and the scratch buffer.
-/

@[expose] public section

namespace VG.Proof.Modes.PPC64LE

open VG VG.PPC64LE VG.Impl.Modes VG.Impl.Modes.PPC64LE
open VG.Spec.Aes (bytesAt)

variable {c : Core}

/-- The areas' lengths: a step's data, a block of `4 bw` bytes, and the
buffer's first `bl` bytes. -/
def lens (c : Core) (st bl : Nat) : Loc → Nat
  | .dat => st
  | .chn => 4 * c.bw
  | .buf => bl

/-- The areas' addresses, for step `j` of the data at `D`. -/
def areas (c : Core) (B D : Addr) (st j : Nat) : Loc → Addr
  | .dat => D + BitVec.ofNat 64 (st * j)
  | .chn => slotA B c.chnSlot
  | .buf => slotA B c.buf

/-- The data. -/
abbrev dataRegion (D : Addr) (st n : Nat) : Region := ⟨D, st * n⟩

/-- The data of step `j`. -/
abbrev datRegion (D : Addr) (st j : Nat) : Region := ⟨D + BitVec.ofNat 64 (st * j), st⟩

/-- The chaining value's slots. -/
abbrev chnRegion (c : Core) (B : Addr) : Region := ⟨slotA B c.chnSlot, 4 * c.bw⟩

/-- The whole scratch buffer. -/
abbrev scrRegion (c : Core) (B : Addr) : Region := ⟨B, 8 * c.total⟩

/-- What a run keeps fixed: the scratch buffer at `B`, the data at `D` of `n`
steps of `st` bytes, the buffer's `bl` bytes a step uses, the regions `W`
the key is ready for, the count `n₀ - d j` in `r30`, and the layout. -/
structure Fixed (c : Core) (s₀ : State) (B D : Addr) (n st bl : Nat) (W : List Region) (n₀ d : Nat) :
    Prop where
  scr : ScrIn s₀ B c.total
  dataW : ∀ o w, 0 < w → o + w ≤ st * n → InRegions s₀.wr (D + BitVec.ofNat 64 o) w
  dataFit : D.toNat + st * n ≤ 2 ^ 64
  dataScr : Region.Disjoint (dataRegion D st n) (scrRegion c B)
  nFit : n₀ < 2 ^ 64
  cnt : d * n ≤ n₀
  dec : d ≤ 2 ^ 15
  step : 0 < st ∧ st < 2 ^ 15
  buf : 0 < bl ∧ bl ≤ 4 * c.bw * c.G
  dataIn : ∃ r ∈ W, Region.Sub (dataRegion D st n) r
  scrIn : scrRegion c B ∈ W
  layout : Layout c

/-- Every access within a writable region of the data is permitted. -/
theorem dataW_of_mem {wr : List Region} {D : Addr} {len : Nat} (hm : (⟨D, len⟩ : Region) ∈ wr)
    (hD : D.toNat + len ≤ 2 ^ 64) {o w : Nat} (hw : 0 < w) (ho : o + w ≤ len) :
    InRegions wr (D + BitVec.ofNat 64 o) w :=
  ⟨_, hm, VG.Offset.contains_base _ (by omega_using [ho]) (by omega_using [hD, ho, hw])⟩

/-- The regions a mode writes: the data and the scratch buffer. -/
abbrev wrs (c : Core) (B D : Addr) (n st : Nat) : List Region := [dataRegion D st n, scrRegion c B]

/-- The regions a run changes. -/
abbrev big (c : Core) (B D : Addr) (n st : Nat) : List Region :=
  [coreRegion c B, chnRegion c B, dataRegion D st n]

/-- The invariant after `j` of the `n` steps from the inputs `xs` and the
chaining value `c0`. -/
structure Inv (cs : CoreSpec c) (s₀ : State) (B D : Addr) (n st : Nat) (W : List Region) (n₀ d : Nat)
    (k : cs.Key) (F : StepFn) (c0 : List Byte) (xs : List (List Byte)) (j : Nat) (s : State) : Prop where
  b : s.gpr sb = B
  keep : ∀ r ∈ kept, r ≠ .r30 → r ≠ .r31 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  dp : s.gpr .r31 = D + BitVec.ofNat 64 (st * j)
  np : s.gpr .r30 = BitVec.ofNat 64 (n₀ - d * j)
  ready : cs.Ready s B W k
  data : chunksAt st s.mem D n = (run F c0 (xs.take j)).1 ++ xs.drop j
  chn : bytesAt s.mem (slotA B c.chnSlot) (4 * c.bw) = (run F c0 (xs.take j)).2
  frame : Frame (big c B D n st) s₀.mem s.mem

/-- After all `n` steps from the state `s₂`, by whatever loops: the data are
`F`'s outputs on the inputs `xs` from `c0`, the chaining value `F`'s last,
the scratch buffer's base and the registers the caller expects kept, and
memory changed only in `big`. -/
structure Done (s₂ : State) (B D : Addr) (n st : Nat) (F : StepFn) (c0 : List Byte) (xs : List (List Byte))
    (s : State) : Prop where
  b : s.gpr sb = B
  keep : ∀ r ∈ kept, r ≠ .r30 → r ≠ .r31 → s.gpr r = s₂.gpr r
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  data : chunksAt st s.mem D n = (run F c0 xs).1
  chn : bytesAt s.mem (slotA B c.chnSlot) (4 * c.bw) = (run F c0 xs).2
  frame : Frame (big c B D n st) s₂.mem s.mem

theorem Inv.done {cs : CoreSpec c} {s₀ : State} {B D : Addr} {n st : Nat} {W : List Region} {n₀ d : Nat}
    {k : cs.Key} {F : StepFn} {c0 : List Byte} {xs : List (List Byte)} {s : State}
    (hI : Inv cs s₀ B D n st W n₀ d k F c0 xs n s) (hxs : xs.length = n) : Done (c := c) s₀ B D n st F c0 xs s := by
  refine ⟨hI.b, hI.keep, hI.rd, hI.wr, ?_, ?_, hI.frame⟩
  · rw [hI.data, List.take_of_length_le (by omega_using [hxs]), List.drop_of_length_le (by omega_using [hxs]), List.append_nil]
  · rw [hI.chn, List.take_of_length_le (by omega_using [hxs])]

/-! ## Areas -/

theorem rd_agree {len : Loc → Nat} {a a' : Areas} (h : Agree len a a') {l : Loc} {n : Nat} (hn : n ≤ len l) :
    rd a l n = rd a' l n :=
  List.map_congr_left fun i hi => h l i (by have := List.mem_range.mp hi; omega_using [hn, this])

theorem cryptBuf_agree {len : Loc → Nat} {n : Nat} (hn : n ≤ len .buf) (ciph : Spec.Cbc.Cipher) {a a' : Areas}
    (h : Agree len a a') : Agree len (cryptBuf n ciph a) (cryptBuf n ciph a') := by
  intro l i hi
  simp only [cryptBuf]
  split
  · rename_i hl; subst hl; rw [rd_agree h hn]
  · exact h l i hi

theorem Agree.trans {len : Loc → Nat} {a b c : Areas} (h₁ : Agree len a b) (h₂ : Agree len b c) :
    Agree len a c := fun l i hi => (h₁ l i hi).trans (h₂ l i hi)

/-- `omega_arith`, with the mode's slots unfolded. -/
local macro "slot_omega" : tactic =>
  `(tactic| plain_simp_names ((try simp only [Core.chnSlot, Core.lrSlot, Core.savedSlot]); omega_arith))

theorem slot_contains {B : Addr} {total d n : Nat} (ht : 8 * total < 2 ^ 15)
    (h : d + n ≤ 8 * total) :
    (⟨B, 8 * total⟩ : Region).Contains (B + BitVec.ofNat 64 d) n :=
  VG.Offset.contains_base _ h (by omega_using [ht, h])

theorem slot_sub {B : Addr} {total d n : Nat} (h : d + n ≤ 8 * total) :
    Region.Sub ⟨B + BitVec.ofNat 64 d, n⟩ ⟨B, 8 * total⟩ :=
  VG.Offset.sub_base _ h

/-- The buffer's bytes a step uses, within the core's slots. -/
theorem Fixed.buf_le {s₀ : State} {B D : Addr} {n st bl : Nat} {W : List Region} {n₀ d : Nat}
    (hF : Fixed c s₀ B D n st bl W n₀ d) : 8 * c.buf + bl ≤ 8 * c.slots :=
  Nat.le_trans (Nat.add_le_add_left hF.buf.2 _) hF.layout.buf_le

/-- Every byte of the areas at step `j`, as the code addresses them. -/
theorem areasOk {s₀ s : State} {B D : Addr} {n st bl : Nat} {W : List Region} {n₀ d j : Nat}
    (hF : Fixed c s₀ B D n st bl W n₀ d) (hj : j < n)
    (hb : s.gpr sb = B) (hdp : s.gpr .r31 = D + BitVec.ofNat 64 (st * j)) (hwr : s.wr = s₀.wr) :
    AreasOk c s (lens c st bl) (areas c B D st j) allLocs := by
  have hL := hF.layout
  have hfit := hF.scr.fit
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hdisp := hL.disp
  have hst := hF.step
  have hD := hF.dataFit
  obtain hjn : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  obtain hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_using [h]
  have hb4 : 8 * c.buf + bl ≤ 8 * c.slots := hF.buf_le
  obtain hW : ∀ l off w, 0 < w → off + w ≤ lens c st bl l →
      InRegions s.wr (areas c B D st j l + BitVec.ofNat 64 off) w := by
    intro l off w hw0 ho
    rw [hwr]
    cases l
    · simp only [lens, areas] at ho ⊢
      rw [VG.Offset.add_add]; exact hF.dataW _ _ hw0 (by omega_using [hjn, ho])
    · simp only [lens, areas] at ho ⊢
      refine ⟨_, hF.scr.wr, ?_⟩
      rw [VG.Offset.add_add]; exact slot_contains hdisp (by slot_omega)
    · simp only [lens, areas] at ho ⊢
      refine ⟨_, hF.scr.wr, ?_⟩
      rw [VG.Offset.add_add]; exact slot_contains hdisp (by omega_using [hroom, hb4, ho])
  refine ⟨fun l off ho => ?_, fun l off ho => ?_, fun l off w hw0 ho => ?_, fun l _ off w hw0 ho => hW l off w hw0 ho,
    fun l l' hne => ?_, fun l => ?_⟩
  · cases l
    · simp only [Core.loc, lens, areas] at ho ⊢
      rw [hdp, Nat.zero_add]
    · simp only [Core.loc, lens, areas] at ho ⊢
      rw [hb, VG.Offset.add_add]
    · simp only [Core.loc, lens, areas] at ho ⊢
      rw [hb, VG.Offset.add_add]
  · cases l
    · simp only [Core.loc, lens] at ho ⊢; omega_using [ho, hst]
    · simp only [Core.loc, lens] at ho ⊢; slot_omega
    · simp only [Core.loc, lens] at ho ⊢; omega_using [ho, hb4, hroom, hdisp]
  · obtain ⟨r, hr, hc⟩ := hW l off w hw0 ho
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · have dD : ∀ d m, d + m ≤ 8 * c.total →
        Region.Disjoint ⟨D + BitVec.ofNat 64 (st * j), st⟩ ⟨B + BitVec.ofNat 64 d, m⟩ :=
      fun d m h => (hF.dataScr.sub_left (VG.Offset.sub_base _ hjn)).sub_right (slot_sub h)
    obtain dCB : Region.Disjoint ⟨slotA B c.chnSlot, 4 * c.bw⟩ ⟨slotA B c.buf, bl⟩ :=
      VG.Offset.disjoint _ (.inr (by slot_omega)) (by slot_omega) (by omega_using [hdisp, hroom, hb4])
    cases l <;> cases l' <;> simp only [ne_eq, not_true_eq_false] at hne <;> simp only [lens, areas]
    · exact dD _ _ (by slot_omega)
    · exact dD _ _ (by omega_using [hroom, hb4])
    · exact (dD _ _ (by slot_omega)).symm
    · exact dCB
    · exact (dD _ _ (by omega_using [hroom, hb4])).symm
    · exact dCB.symm
  · cases l <;> simp only [lens] <;> omega_using [hst, hbw, hb4, hdisp, hroom]

/-! ## The regions of a step -/

/-- The regions a step's operations and core change: the data of the step,
the core's slots and the chaining value. -/
abbrev fine (c : Core) (B D : Addr) (st j : Nat) : List Region :=
  [datRegion D st j, coreRegion c B, chnRegion c B]

/-- What a step needs of the regions. -/
structure Regs (c : Core) (B D : Addr) (n st bl : Nat) (W : List Region) (j : Nat) : Prop where
  areasFine : ∀ r ∈ areaRegions (lens c st bl) (areas c B D st j) allLocs, ∃ r' ∈ fine c B D st j, Region.Sub r r'
  areasW : ∀ r ∈ areaRegions (lens c st bl) (areas c B D st j) allLocs, ∃ r' ∈ W, Region.Sub r r'
  areasCore : ∀ r ∈ areaRegions (lens c st bl) (areas c B D st j) allLocs,
    Region.Disjoint (coreRegion c B) r ∨ Region.Sub r (blkRegion c B)
  chnCore : Region.Disjoint (chnRegion c B) (coreRegion c B)
  datCore : Region.Disjoint (datRegion D st j) (coreRegion c B)
  datData : Region.Sub (datRegion D st j) (dataRegion D st n)
  dataCore : Region.Disjoint (dataRegion D st n) (coreRegion c B)
  dataChn : Region.Disjoint (dataRegion D st n) (chnRegion c B)
  toBig : ∀ r ∈ fine c B D st j, ∃ r' ∈ big c B D n st, Region.Sub r r'

theorem regs {s₀ : State} {B D : Addr} {n st bl : Nat} {W : List Region} {n₀ d j : Nat}
    (hF : Fixed c s₀ B D n st bl W n₀ d) (hj : j < n) :
    Regs c B D n st bl W j := by
  have hL := hF.layout
  have hfit := hF.scr.fit
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hG := hL.G_pos
  obtain hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_using [h]
  obtain hjn : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  obtain subDat : Region.Sub (datRegion D st j) (dataRegion D st n) := VG.Offset.sub_base _ hjn
  have hb4 : 8 * c.buf + bl ≤ 8 * c.slots := hF.buf_le
  obtain subBuf : Region.Sub ⟨slotA B c.buf, bl⟩ (coreRegion c B) :=
    VG.Offset.sub_base _ hb4
  obtain subBlk : Region.Sub ⟨slotA B c.buf, bl⟩ (blkRegion c B) := Region.sub_prefix hF.buf.2
  obtain chnScr : Region.Sub (chnRegion c B) (scrRegion c B) := VG.Offset.sub_base _ (by slot_omega)
  obtain coreScr : Region.Sub (coreRegion c B) (scrRegion c B) := Region.sub_prefix (by slot_omega)
  obtain chnCore : Region.Disjoint (chnRegion c B) (coreRegion c B) :=
    VG.Offset.disjoint_base _ (by slot_omega) (by slot_omega)
  obtain datCore : Region.Disjoint (datRegion D st j) (coreRegion c B) :=
    (hF.dataScr.sub_left subDat).sub_right coreScr
  obtain m1 : ∀ {a b : Region} {l : List Region}, b ∈ a :: b :: l := List.mem_cons_of_mem _ List.mem_cons_self
  obtain m2 : ∀ {a b c' : Region} {l : List Region}, c' ∈ a :: b :: c' :: l :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  refine ⟨fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, chnCore, datCore, subDat,
    hF.dataScr.sub_right coreScr, hF.dataScr.sub_right chnScr, fun r hr => ?_⟩
  · simp only [areaRegions, allLocs, List.map, areas, lens, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, m2, fun _ h => h⟩
    · exact ⟨_, m1, subBuf⟩
  · simp only [areaRegions, allLocs, List.map, areas, lens, List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain ⟨rD, hrD, sD⟩ := hF.dataIn
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, hrD, fun x hx => sD x (subDat x hx)⟩
    · exact ⟨_, hF.scrIn, chnScr⟩
    · exact ⟨_, hF.scrIn, fun x hx => coreScr x (subBuf x hx)⟩
  · simp only [areaRegions, allLocs, List.map, areas, lens, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl datCore.symm
    · exact .inl chnCore.symm
    · exact .inr subBlk
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, m2, subDat⟩
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, m1, fun _ h => h⟩

/-! ## The stages of a step -/

/-- In the middle of a step from `s`: the areas agree with `a`, the key is
ready, the mode's registers are kept, and memory has changed only in `fine`
since `s`. -/
structure Mid (cs : CoreSpec c) (s₀ : State) (B D : Addr) (st bl : Nat) (W : List Region) (j : Nat)
    (k : cs.Key) (s : State) (a : Areas) (s' : State) : Prop where
  b : s'.gpr sb = B
  kept : ∀ r ∈ kept, s'.gpr r = s.gpr r
  rd : s'.rd = s₀.rd
  wr : s'.wr = s₀.wr
  ready : cs.Ready s' B W k
  agree : Agree (lens c st bl) (cont (areas c B D st j) s'.mem) a
  frame : Frame (fine c B D st j) s.mem s'.mem

theorem mem_kept {r : Reg} (h : r = .r3 ∨ r = .r29 ∨ r = .r30 ∨ r = .r31) : r ∈ kept := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-- The operations' registers are not kept. -/
theorem kept_ne : ∀ r ∈ kept, r ≠ .r8 ∧ r ≠ .r9 := by decide

/-- The operations' hypotheses, for `opsCode_wp`. -/
theorem ops_ok {len : Loc → Nat} {os : List Op} (h : ∀ o ∈ os, o.InBounds len) :
    ∀ o ∈ os, o.InBounds len ∧ o.dst ∈ allLocs :=
  fun o ho => ⟨h o ho, mem_allLocs _⟩

section
variable (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {B D : Addr} {n st bl : Nat}
  {W : List Region} {n₀ d : Nat} {k : cs.Key} {c0 : List Byte} {xs : List (List Byte)}

theorem pre_wp (hF : Fixed c s₀ B D n st bl W n₀ d)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c st bl)) {j : Nat} (hj : j < n) {s : State}
    (hI : Inv cs s₀ B D n st W n₀ d k F c0 xs j s) :
    WP isa (.block (c.opsCode M.pre)) s
      (Mid cs s₀ B D st bl W j k s (applyOps M.pre (cont (areas c B D st j) s.mem))) := by
  obtain hR := regs hF hj
  obtain hA : AreasOk c s (lens c st bl) (areas c B D st j) allLocs := areasOk hF hj hI.b hI.dp hI.wr
  rw [← List.append_nil (c.opsCode M.pre)]
  refine VG.PPC64LE.WP.of_syms (opsCode_wp c (ops_ok hpre) hA fun s₂ a₂ f₂ g₂ rd₂ wr₂ => wp_nil fun sy₂ => ?_)
  exact ⟨by rw [g₂ _ (by decide) (by decide)]; exact hI.b,
    fun r hr => g₂ r (kept_ne r hr).1 (kept_ne r hr).2,
    by rw [rd₂, hI.rd], by rw [wr₂, hI.wr],
    cs.ready_frame hI.ready (fun r hr _ _ _ => g₂ r (kept_ne r hr).1 (kept_ne r hr).2) rd₂ wr₂ sy₂ f₂
      hR.areasW hR.areasCore, a₂,
    f₂.sub hR.areasFine⟩

end

theorem bytesAt_getD (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

theorem blkAddr_zero (c : Core) (B : Addr) : blkAddr c B 0 = slotA B c.buf := by
  simp only [blkAddr, Nat.mul_zero, BitVec.add_zero]

/-- The core's block cipher, as the cipher `ciphB` on the buffer's first `bl`
bytes: what `crypt_wp` gives of the buffer's blocks determines them. -/
def BufCipher (c : Core) (ciph ciphB : Spec.Cbc.Cipher) (bl : Nat) : Prop :=
  ∀ (B : Addr) (m m' : Mem), (∀ j < c.G, bytesAt m' (blkAddr c B j) (4 * c.bw) =
    ciph (bytesAt m (blkAddr c B j) (4 * c.bw))) →
    bytesAt m' (slotA B c.buf) bl = ciphB (bytesAt m (slotA B c.buf) bl)

/-- One block: the cipher on the buffer's first block. -/
theorem bufCipher_one (hG : 0 < c.G) (ciph : Spec.Cbc.Cipher) : BufCipher c ciph ciph (4 * c.bw) :=
  fun B m m' h => by have e := h 0 hG; rwa [blkAddr_zero] at e

section
variable (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {B D : Addr} {n st bl : Nat}
  {W : List Region} {n₀ d : Nat} {k : cs.Key} {c0 : List Byte} {xs : List (List Byte)}

theorem crypt_step (hF : Fixed c s₀ B D n st bl W n₀ d) {ciphB : Spec.Cbc.Cipher}
    (hB : BufCipher c (cs.cipher k) ciphB bl) {j : Nat} (hj : j < n) {s s₂ : State} {a : Areas}
    (hm : Mid cs s₀ B D st bl W j k s a s₂) :
    WP isa c.crypt s₂ (Mid cs s₀ B D st bl W j k s (cryptBuf bl ciphB a)) := by
  obtain hR := regs hF hj
  have hst := hF.step
  obtain hbw : c.bw ≤ 4 := by rcases hF.layout.bw with h | h <;> omega_using [h]
  refine WP.mono (cs.crypt_wp hm.b ⟨by rw [hm.wr]; exact hF.scr.wr, hF.scr.fit⟩ hm.ready)
    fun s₃ ⟨b₃, kept₃, ready₃, f₃, enc₃, rd₃, wr₃⟩ => ?_
  refine ⟨b₃, fun r hr => by rw [kept₃ r hr, hm.kept r hr], by rw [rd₃, hm.rd], by rw [wr₃, hm.wr], ready₃, ?_,
    hm.frame.trans (f₃.sub fun r hr => ⟨r, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)⟩
  refine Agree.trans (b := cryptBuf bl ciphB (cont (areas c B D st j) s₂.mem)) ?_
    (cryptBuf_agree (by simp [lens]) _ hm.agree)
  intro l i hi
  cases l
  · simp only [cryptBuf, cont, areas, lens] at hi ⊢
    exact f₃.bytes (R := datRegion D st j) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact hR.datCore) (by show st ≤ 2 ^ 64; omega_using [hst]) hi
  · simp only [cryptBuf, cont, areas, lens] at hi ⊢
    exact f₃.bytes (R := chnRegion c B) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact hR.chnCore) (by show 4 * c.bw ≤ 2 ^ 64; omega_using [hbw]) hi
  · simp only [lens] at hi
    obtain e := hB B s₂.mem s₃.mem enc₃
    simp only [cryptBuf, cont, areas, ite_true]
    rw [← bytesAt_getD s₃.mem (slotA B c.buf) hi, e]
    rfl

end

theorem chunksAt_getElem {L : Nat} {m : Mem} {p : Addr} {n j : Nat} (hj : j < n) :
    (chunksAt L m p n)[j]'(by rw [chunksAt_length]; exact hj) = bytesAt m (p + BitVec.ofNat 64 (L * j)) L := by
  simp [chunksAt]

/-- Input step `j`, from the invariant. -/
theorem Inv.input {cs : CoreSpec c} {s₀ : State} {B D : Addr} {n st : Nat} {W : List Region} {n₀ d : Nat}
    {k : cs.Key} {F : StepFn} {c0 : List Byte} {xs : List (List Byte)} {j : Nat} {s : State}
    (hI : Inv cs s₀ B D n st W n₀ d k F c0 xs j s) (hxs : xs.length = n) (hj : j < n) :
    bytesAt s.mem (D + BitVec.ofNat 64 (st * j)) st = xs[j]'(by omega_using [hxs, hj]) := by
  obtain hl : (run F c0 (xs.take j)).1.length = j := by rw [run_length, List.length_take]; omega_using [hxs, hj]
  obtain e := congrArg (·[j]?) hI.data
  simp only [List.getElem?_append_right (Nat.le_of_eq hl), hl, Nat.sub_self, List.getElem?_drop, Nat.add_zero] at e
  rw [List.getElem?_eq_getElem (by rw [chunksAt_length]; exact hj), List.getElem?_eq_getElem (by omega_using [hxs, hj]),
    chunksAt_getElem hj] at e
  exact Option.some.inj e

theorem ofNat_pred64 {k : Nat} (h : 1 ≤ k) : BitVec.ofNat 64 k - BitVec.ofNat 64 1 = BitVec.ofNat 64 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_using [h]

theorem ofNat_sub64 {a b : Nat} (h : b ≤ a) : BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have := Nat.mod_le a (2 ^ 64)
  by_cases hb : b < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hb]
    by_cases ha : a < 2 ^ 64
    · rw [Nat.mod_eq_of_lt ha]; omega_using [h, hb]
    · omega_using [h, hb]
  · omega_using [h]

/-- What the instructions `ex` after a step's count do: change only `r8`,
establishing `X`. -/
def ExOk (ex : List Instr) (X : State → Prop) : Prop :=
  ∀ t, WP isa (.block ex) t fun t' => (∀ r, r ≠ .r8 → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧
    t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.syms = t.syms ∧ X t'

theorem exOk_nil : ExOk [] fun _ => True := fun _ => wp_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, trivial⟩

section
variable (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {B D : Addr} {n st bl : Nat}
  {W : List Region} {n₀ d : Nat} {k : cs.Key} {c0 : List Byte} {xs : List (List Byte)}

theorem post_wp (hF : Fixed c s₀ B D n st bl W n₀ d) (hM : M.step = st) {ciphB : Spec.Cbc.Cipher}
    (hpost : ∀ o ∈ M.post, o.InBounds (lens c st bl)) (hcomp : ComputesB M (4 * c.bw) bl ciphB F)
    {ex : List Instr} {X : State → Prop} (hex : ExOk ex X)
    (hxs : xs.length = n) {j : Nat} (hj : j < n) {s s₃ : State} (hI : Inv cs s₀ B D n st W n₀ d k F c0 xs j s)
    (hm : Mid cs s₀ B D st bl W j k s (cryptBuf bl ciphB
      (applyOps M.pre (cont (areas c B D st j) s.mem))) s₃) :
    WP isa (.block (c.opsCode M.post ++ (.addi .r31 .r31 M.step :: .subi .r30 .r30 d :: ex))) s₃
      fun s' => Inv cs s₀ B D n st W n₀ d k F c0 xs (j + 1) s' ∧ X s' := by
  obtain hR := regs hF hj
  have hL := hF.layout
  have hst := hF.step
  have hDf := hF.dataFit
  obtain hcnt : d * j + d ≤ n₀ := by rw [← Nat.mul_succ]; exact Nat.le_trans (Nat.mul_le_mul_left _ hj) hF.cnt
  obtain hjn : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  obtain k₃ : ∀ r, r = .r3 ∨ r = .r29 ∨ r = .r30 ∨ r = .r31 → s₃.gpr r = s.gpr r :=
    fun r hr => hm.kept r (mem_kept hr)
  obtain dp₃ : s₃.gpr .r31 = D + BitVec.ofNat 64 (st * j) := by rw [k₃ _ (by simp), hI.dp]
  obtain np₃ : s₃.gpr .r30 = BitVec.ofNat 64 (n₀ - d * j) := by rw [k₃ _ (by simp), hI.np]
  obtain hA : AreasOk c s₃ (lens c st bl) (areas c B D st j) allLocs := areasOk hF hj hm.b dp₃ hm.wr
  refine VG.PPC64LE.WP.of_syms (opsCode_wp c (ops_ok hpost) hA fun s₅ a₅ f₅ g₅ rd₅ wr₅ => ?_)
  refine wp_addi (by decide) (by omega_using [hM, hst]) fun s₆ u₆ =>
    wp_subi (by decide) hF.dec fun s₇ u₇ => WP.mono (hex s₇) fun s₈ ⟨g₈, m₈, rd₈, wr₈, sy₈', x₈⟩ sy₈ => ⟨?_, x₈⟩
  obtain g₇ : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r30 → r ≠ .r31 → s₈.gpr r = s₃.gpr r := fun r h1 h2 h3 h4 => by
    rw [g₈ r h1, u₇.other r h3, u₆.other r h4, g₅ r h1 h2]
  obtain m₇ : s₈.mem = s₅.mem := by rw [m₈, u₇.mem, u₆.mem]
  obtain r31₅ : s₅.gpr .r31 = D + BitVec.ofNat 64 (st * j) := by rw [g₅ _ (by decide) (by decide), dp₃]
  obtain r30₅ : s₅.gpr .r30 = BitVec.ofNat 64 (n₀ - d * j) := by rw [g₅ _ (by decide) (by decide), np₃]
  have sy₇ : s₈.syms = s₃.syms := sy₈
  -- The step's outputs.
  let A := areas c B D st j
  obtain hstep : Agree (lens c st bl) (cont A s₅.mem) (stepA M bl ciphB (cont A s.mem)) :=
    Agree.trans a₅ (applyOps_agree hpost hm.agree)
  obtain ⟨hc1, hc2⟩ := hcomp (cont A s.mem)
  rw [hM] at hc1 hc2
  obtain xj : rd (cont A s.mem) .dat st = xs[j]'(by omega_using [hxs, hj]) := hI.input hxs hj
  have cj : rd (cont A s.mem) .chn (4 * c.bw) = (run F c0 (xs.take j)).2 := hI.chn
  rw [xj, cj] at hc1 hc2
  obtain out₅ : bytesAt s₅.mem (D + BitVec.ofNat 64 (st * j)) st =
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).1 := by
    rw [← hc1]; exact rd_agree hstep (l := .dat) (Nat.le_refl _)
  obtain chn₅ : bytesAt s₅.mem (slotA B c.chnSlot) (4 * c.bw) =
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).2 := by
    rw [← hc2]; exact rd_agree hstep (l := .chn) (Nat.le_refl _)
  obtain all : Frame (fine c B D st j) s.mem s₅.mem := hm.frame.trans (f₅.sub hR.areasFine)
  obtain hrun : run F c0 (xs.take (j + 1)) = ((run F c0 (xs.take j)).1 ++
      [(F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).1],
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).2) := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega_using [hxs, hj]), Option.toList_some, run_snoc]
  refine ⟨by rw [g₇ _ (by decide) (by decide) (by decide) (by decide)]; exact hm.b,
    fun r hr h30 h31 => by
      rw [g₇ r (kept_ne r hr).1 (kept_ne r hr).2 h30 h31, hm.kept r hr, hI.keep r hr h30 h31],
    by rw [rd₈, u₇.rd, u₆.rd, rd₅, hm.rd], by rw [wr₈, u₇.wr, u₆.wr, wr₅, hm.wr], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g₈ _ (by decide), u₇.other _ (by decide), u₆.gpr, r31₅, VG.Offset.add_add, hM, Nat.mul_succ]
  · rw [g₈ _ (by decide), u₇.gpr, u₆.other _ (by decide), r30₅, ofNat_sub64 (by omega_using [hcnt]), Nat.mul_succ]
    congr 1; omega_using [hcnt]
  · exact cs.ready_frame hm.ready (fun r hr _ h30 h31 => g₇ r (kept_ne r hr).1 (kept_ne r hr).2 h30 h31)
      (by rw [rd₈, u₇.rd, u₆.rd, rd₅]) (by rw [wr₈, u₇.wr, u₆.wr, wr₅]) sy₇ (by rw [m₇]; exact f₅)
      hR.areasW hR.areasCore
  · rw [m₇, chunksAt_set (j := j) (fun i hi hout => ?_), hI.data, out₅, run_set F c0 (by omega_using [hxs, hj])]
    refine all _ fun r hr hcon => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp only [Region.Contains] at hcon
      obtain e := (VG.Offset.lt_iff (D + BitVec.ofNat 64 i) D (d := st * j) (n := st)
        (by omega_using [hDf, hjn])).mp (by omega_using [hcon])
      rw [sub_self_add _ (by omega_using [hDf, hi])] at e
      omega_using [hout, e]
    · exact hR.dataCore _ (contains_area hi (by omega_using [hDf])) hcon
    · exact hR.dataChn _ (contains_area hi (by omega_using [hDf])) hcon
  · rw [m₇, chn₅, hrun]
  · rw [m₇]; exact hI.frame.trans (all.sub hR.toBig)

/-! ## The step and the loop -/

/-- A step: `pre`, the core, `post`, the count, and `ex`. -/
theorem step_wp (hF : Fixed c s₀ B D n st bl W n₀ d) (hM : M.step = st) {ciphB : Spec.Cbc.Cipher}
    (hB : BufCipher c (cs.cipher k) ciphB bl)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c st bl)) (hpost : ∀ o ∈ M.post, o.InBounds (lens c st bl))
    (hcomp : ComputesB M (4 * c.bw) bl ciphB F) {ex : List Instr} {X : State → Prop} (hex : ExOk ex X)
    (hxs : xs.length = n) {j : Nat} (hj : j < n) {s : State}
    (hI : Inv cs s₀ B D n st W n₀ d k F c0 xs j s) :
    WP isa (.seq (.block (c.opsCode M.pre)) (.seq c.crypt
      (.block (c.opsCode M.post ++ (.addi .r31 .r31 M.step :: .subi .r30 .r30 d :: ex))))) s
      fun s' => Inv cs s₀ B D n st W n₀ d k F c0 xs (j + 1) s' ∧ X s' :=
  WP.seq (WP.mono (pre_wp cs hF hpre hj hI) fun _ h₂ =>
    WP.seq (WP.mono (crypt_step cs hF hB hj h₂) fun _ h₃ => post_wp cs hF hM hpost hcomp hex hxs hj hI h₃))

theorem body_wp (hF : Fixed c s₀ B D n st (4 * c.bw) W n₀ 1) (hM : M.step = st)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c st (4 * c.bw))) (hpost : ∀ o ∈ M.post, o.InBounds (lens c st (4 * c.bw)))
    (hcomp : Computes M (4 * c.bw) (cs.cipher k) F) (hxs : xs.length = n) {j : Nat} (hj : j < n) {s : State}
    (hI : Inv cs s₀ B D n st W n₀ 1 k F c0 xs j s) :
    WP isa (c.body M) s (Inv cs s₀ B D n st W n₀ 1 k F c0 xs (j + 1)) :=
  WP.mono (step_wp cs hF hM (bufCipher_one hF.layout.G_pos _) hpre hpost hcomp exOk_nil hxs hj hI) fun _ h => h.1

theorem loop_wp (hF : Fixed c s₀ B D n st (4 * c.bw) W n 1) (hM : M.step = st)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c st (4 * c.bw))) (hpost : ∀ o ∈ M.post, o.InBounds (lens c st (4 * c.bw)))
    (hcomp : Computes M (4 * c.bw) (cs.cipher k) F) (hxs : xs.length = n) {s : State}
    (hI : Inv cs s₀ B D n st W n 1 k F c0 xs 0 s) :
    WP isa (c.steps M) s (Inv cs s₀ B D n st W n 1 k F c0 xs n) := by
  have hn64 := hF.nFit
  obtain ev : ∀ {j t}, j ≤ n → t.gpr .r30 = BitVec.ofNat 64 (n - 1 * j) →
      isa.eval (.nonzero .d .r30) t = some (decide (n - 1 * j ≠ 0)) := fun hj h =>
    eval_nonzero_ofNat' _ _ (by omega_using [hn64, hj]) h
  unfold Core.steps
  by_cases hn : n = 0
  · subst hn
    exact WP.ite true (by rw [eval_zero_ofNat s .r30 (by decide) hI.np]; rfl) (fun _ => wp_nil hI)
      (fun h => by cases h)
  refine WP.ite false (by rw [eval_zero_ofNat s .r30 (by omega_using [hn64]) hI.np]; simp [hn])
    (fun h => by cases h) fun _ => ?_
  refine WP.loop (M := isa) (body := c.body M) (c := .nonzero .d .r30) (Q := Inv cs s₀ B D n st W n 1 k F c0 xs n)
    (fun (m : Nat) (t : State) => ∃ j, m = n - j ∧ j < n ∧ Inv cs s₀ B D n st W n 1 k F c0 xs j t)
    ?_ n s ⟨0, by omega_using [], by omega_using [hn], hI⟩
  rintro _ t ⟨j, rfl, hj, h⟩
  refine WP.mono (body_wp cs hF hM hpre hpost hcomp hxs hj h) fun t' h' => ?_
  obtain e := ev (j := j + 1) (by omega_using [hj]) h'.np
  by_cases he : j + 1 = n
  · left; exact ⟨by rw [e]; simp [he], he ▸ h'⟩
  · right; exact ⟨by rw [e]; simp; omega_using [hj, he], n - (j + 1), by omega_using [hj, he], j + 1, rfl,
      by omega_using [hj, he], h'⟩

end

/-! ## A group of blocks a step -/

/-- `r8` is `r30 >> lg`: whether a group of `2 ^ lg` blocks is left. -/
def GroupsLeft (lg : Nat) (t : State) : Prop := t.gpr .r8 = t.gpr .r30 >>> lg

theorem exOk_groupsLeft {lg : Nat} (h : lg < 64) : ExOk [Core.groupsLeft lg] (GroupsLeft lg) :=
  fun t => VG.PPC64LE.WP.of_syms (wp_lsr h fun t' u => wp_nil fun sy =>
    ⟨fun r hr => u.other r hr, u.mem, u.rd, u.wr, sy, by
      simp only [GroupsLeft, u.gpr, u.other _ (show Reg.r30 ≠ .r8 by decide)]⟩)

theorem ushiftRight_ofNat {x lg : Nat} (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 x >>> lg = BitVec.ofNat 64 (x / 2 ^ lg) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)]

section
variable (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {B D : Addr} {n st bl : Nat}
  {W : List Region} {n₀ : Nat} {k : cs.Key} {c0 : List Byte} {xs : List (List Byte)}

/-- The steps of `2 ^ lg` blocks, `n = n₀ / 2 ^ lg` of them. -/
theorem loopWide_wp {lg : Nat} (hlg : lg < 64) (hF : Fixed c s₀ B D n st bl W n₀ (2 ^ lg))
    (hn : n = n₀ / 2 ^ lg) (hM : M.step = st) {ciphB : Spec.Cbc.Cipher}
    (hB : BufCipher c (cs.cipher k) ciphB bl)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c st bl)) (hpost : ∀ o ∈ M.post, o.InBounds (lens c st bl))
    (hcomp : ComputesB M (4 * c.bw) bl ciphB F) (hxs : xs.length = n) {s : State}
    (hI : Inv cs s₀ B D n st W n₀ (2 ^ lg) k F c0 xs 0 s) :
    WP isa (c.loopWide M lg) s (Inv cs s₀ B D n st W n₀ (2 ^ lg) k F c0 xs n) := by
  have hn64 := hF.nFit
  -- After `j` steps, `r8` says whether `j < n`.
  obtain ev : ∀ {j : Nat} {t : State}, j ≤ n → t.gpr .r30 = BitVec.ofNat 64 (n₀ - 2 ^ lg * j) →
      GroupsLeft lg t → isa.eval (.nonzero .d .r8) t = some (decide (j < n)) ∧
        isa.eval (.zero .d .r8) t = some (decide (n ≤ j)) := fun {j t} hj h3 hg => by
    obtain hq : (n₀ - 2 ^ lg * j) / 2 ^ lg = n - j := by rw [Nat.sub_mul_div, hn]
    obtain h0 : t.gpr .r8 = BitVec.ofNat 64 (n - j) := by
      rw [hg, h3, ushiftRight_ofNat (by omega_using [hn64]), hq]
    obtain hlt : n - j < 2 ^ 64 := by
      have : n ≤ n₀ := by rw [hn]; exact Nat.div_le_self _ _
      omega_using [hn64, this]
    rw [eval_nonzero_ofNat' _ _ hlt h0, eval_zero_ofNat _ _ hlt h0]
    exact ⟨congrArg some (decide_eq_decide.mpr ⟨fun h => by omega_using [h], fun h => by omega_using [h]⟩),
      congrArg some (decide_eq_decide.mpr ⟨fun h => by omega_using [h, hj], fun h => by omega_using [h]⟩)⟩
  unfold Core.loopWide
  refine WP.seq (VG.PPC64LE.WP.of_syms (wp_lsr hlg fun s₁ u₁ => wp_nil fun sy₁ => ?_))
  obtain hI₁ : Inv cs s₀ B D n st W n₀ (2 ^ lg) k F c0 xs 0 s₁ :=
    ⟨by rw [u₁.other _ (by decide)]; exact hI.b,
      fun r hr h3 h2 => by rw [u₁.other r (kept_ne r hr).1]; exact hI.keep r hr h3 h2,
      by rw [u₁.rd, hI.rd], by rw [u₁.wr, hI.wr], by rw [u₁.other _ (by decide)]; exact hI.dp,
      by rw [u₁.other _ (by decide)]; exact hI.np,
      cs.ready_frame (rs := []) hI.ready (fun r hr _ _ _ => u₁.other r (kept_ne r hr).1) u₁.rd u₁.wr sy₁
        (by rw [u₁.mem]; exact Frame.refl _ _) (fun _ h => nomatch h) (fun _ h => nomatch h),
      by rw [u₁.mem]; exact hI.data, by rw [u₁.mem]; exact hI.chn, by rw [u₁.mem]; exact hI.frame⟩
  obtain g₁ : GroupsLeft lg s₁ := by simp only [GroupsLeft, u₁.gpr, u₁.other _ (show Reg.r30 ≠ .r8 by decide)]
  obtain ⟨-, ez⟩ := ev (Nat.zero_le _) hI₁.np g₁
  by_cases hn0 : n = 0
  · subst hn0
    exact WP.ite true (by rw [ez]; rfl) (fun _ => wp_nil hI₁) (fun h => by cases h)
  refine WP.ite false (by rw [ez]; simp; omega_using [hn0]) (fun h => by cases h) fun _ => ?_
  refine WP.loop (M := isa) (body := c.bodyWide M lg) (c := .nonzero .d .r8)
    (Q := Inv cs s₀ B D n st W n₀ (2 ^ lg) k F c0 xs n)
    (fun (m : Nat) (t : State) => ∃ j, m = n - j ∧ j < n ∧ Inv cs s₀ B D n st W n₀ (2 ^ lg) k F c0 xs j t)
    ?_ n s₁ ⟨0, by omega_using [], by omega_using [hn0], hI₁⟩
  rintro _ t ⟨j, rfl, hj, h⟩
  refine WP.mono (step_wp cs hF hM hB hpre hpost hcomp (exOk_groupsLeft hlg) hxs hj h) fun t' ⟨h', g'⟩ => ?_
  obtain ⟨e, -⟩ := ev (j := j + 1) (by omega_using [hj]) h'.np g'
  by_cases he : j + 1 = n
  · left; exact ⟨by rw [e]; simp [he], he ▸ h'⟩
  · right; exact ⟨by rw [e]; simp; omega_using [hj, he], n - (j + 1), by omega_using [hj, he], j + 1, rfl,
      by omega_using [hj, he], h'⟩

end

end VG.Proof.Modes.PPC64LE

end

end


/-!
# A mode on PPC64LE, for any core: the whole function

`seq_wp`: `c.seq M`, for a core `c` with `CoreSpec c` and a mode `M` whose
operations compute the step function `F` (`Computes`), with its arguments in
registers (`f(key = r3, iv = r4, data = r5, n = r6, scratch = r7)`),
replaces the `n` steps of data at `data` with the outputs of `F` from the
IV, and (if `M.ivOut`) the IV with the last chaining value; it keeps the
registers the caller expects preserved, the stack pointer and the return
address. Each mode's and cipher's contract follows from it.

Both are `seqWith_changes_wp` for the loops of `Core.seq`, `Core.steps M`
(`steps_ok`): the function around any loops that take all the steps
(`LoopsOk`), as `Core.seq2`'s do too (`Wide.lean`).
-/

@[expose] public section

namespace VG.Proof.Modes.PPC64LE

open VG VG.PPC64LE VG.Impl.Modes VG.Impl.Modes.PPC64LE
open VG.Spec.Aes (bytesAt)

variable {c : Core} {M : Mode}

section
variable (s₀ : State)

abbrev P : Addr := s₀.gpr .r4
abbrev Dp : Addr := s₀.gpr .r5
abbrev N : Nat := (s₀.gpr .r6).toNat
abbrev S : Addr := s₀.gpr .r7

abbrev ivR (c : Core) : Region := ⟨P s₀, 4 * c.bw⟩

end

/-- What the function needs on entry: the IV readable (and writable, apart
from the data, if the mode writes it back), the data and the scratch buffer
writable, none wrapping around, and the scratch buffer apart from the IV and
the data. -/
structure SeqPre (c : Core) (M : Mode) (s₀ : State) : Prop where
  scr : ScrIn s₀ (S s₀) c.total
  ivRd : ivR s₀ c ∈ s₀.rd ++ s₀.wr
  ivWr : M.ivOut = true → ivR s₀ c ∈ s₀.wr
  ivFit : (P s₀).toNat + 4 * c.bw ≤ 2 ^ 64
  dataW : dataRegion (Dp s₀) M.step (N s₀) ∈ s₀.wr
  dataFit : (Dp s₀).toNat + M.step * N s₀ ≤ 2 ^ 64
  dataScr : Region.Disjoint (dataRegion (Dp s₀) M.step (N s₀)) (scrRegion c (S s₀))
  ivScr : Region.Disjoint (ivR s₀ c) (scrRegion c (S s₀))
  ivData : M.ivOut = true → Region.Disjoint (ivR s₀ c) (dataRegion (Dp s₀) M.step (N s₀))
  step : 0 < M.step ∧ M.step ≤ 4 * c.bw
  layout : Layout c

/-! ## Instructions -/

theorem range3_map {α : Type} (f : Nat → α) : (List.range 3).map f = [f 0, f 1, f 2] := rfl

theorem wp_mflr {is : List Instr} {s : State} {Q : State → Prop} {d : Reg}
    (k : ∀ s', Upd s s' d s.lr → WP isa (.block is) s' Q) : WP isa (.block (.mflr d :: is)) s Q :=
  WP.cons exec_mflr (k _ (Upd.write _ _ _))

theorem wp_mtlr {is : List Instr} {s : State} {Q : State → Prop} {r : Reg}
    (k : WP isa (.block is) { s with lr := s.gpr r } Q) : WP isa (.block (.mtlr r :: is)) s Q :=
  WP.cons exec_mtlr k

/-- `Q` of the state after `c`, which may assume `c` kept the stack pointer
(`Exec.sp`). -/
theorem WP.sp_intro {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa c s fun s' => s'.sp = s.sp → Q s') : WP isa c s Q := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq (Exec.sp he)⟩

theorem readW_sep64 {m : Mem} {a b : Addr} {v : BitVec 64} (h : Region.Disjoint ⟨a, 8⟩ ⟨b, 8⟩) :
    (m.writeW b v).readW a 64 = m.readW a 64 :=
  Mem.readW_writeW_sep (fun x h1 h2 => h x (by simp only [Region.Contains]; omega_using [h1])
    (by simp only [Region.Contains]; omega_using [h2])) (by decide)

/-! ## The slots -/

/-- The mode's slots. -/
abbrev modeR (c : Core) (B : Addr) : Region := ⟨slotA B c.slots, 48⟩

/-- `omega_arith`, with the mode's slots unfolded. -/
local macro "slot_omega" : tactic =>
  `(tactic| plain_simp_names ((try simp only [Core.chnSlot, Core.lrSlot, Core.savedSlot]); omega_arith))

theorem buf_le4 (hL : Layout c) : 8 * c.buf + 4 * c.bw ≤ 8 * c.slots :=
  Nat.le_trans (Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hL.G_pos) _) hL.buf_le

theorem bw_le (hL : Layout c) : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_using [h]

/-- Two different slots are apart. -/
theorem slot_sep {B : Addr} {total i j : Nat} (ht : 8 * total < 2 ^ 15) (hi : i < total) (hj : j < total)
    (hne : i ≠ j) : Region.Disjoint ⟨slotA B i, 8⟩ ⟨slotA B j, 8⟩ :=
  VG.Offset.disjoint _ (by omega_using [hne]) (by omega_using [ht, hi]) (by omega_using [ht, hj])

/-- A slot of the scratch buffer is writable. -/
theorem slot_inW {s : State} {B : Addr} {total k : Nat} (hS : ScrIn s B total) (ht : 8 * total < 2 ^ 15)
    (hk : k < total) : InRegions s.wr (slotA B k) 8 :=
  ⟨_, hS.wr, slot_contains ht (by omega_using [hk])⟩

/-- A slot of the scratch buffer is readable. -/
theorem slot_in {s : State} {B : Addr} {total k : Nat} (hS : ScrIn s B total) (ht : 8 * total < 2 ^ 15)
    (hk : k < total) : InRegions (s.rd ++ s.wr) (slotA B k) 8 :=
  ⟨_, List.mem_append_right _ hS.wr, slot_contains ht (by omega_using [hk])⟩

/-- A slot of the mode, in its slots. -/
theorem slot_mode {B : Addr} {i : Nat} (hL : Layout c) (hi : c.slots ≤ i) (hi' : i + 1 ≤ c.slots + 6) :
    (modeR c B).Contains (slotA B i) (64 / 8) :=
  VG.Offset.contains _ (by omega_using [hi]) (by omega_using [hi']) (by have := hL.disp; have := hL.room; omega_arith)

/-! ## The IV's copies -/

/-- The areas of the IV's copies: the IV as the data. -/
def ivAreas (c : Core) (P B : Addr) : Loc → Addr
  | .dat => P
  | .chn => slotA B c.chnSlot
  | .buf => slotA B c.buf

theorem ivAreasOk {s₀ s : State} (hp : SeqPre c M s₀) (hb : s.gpr sb = S s₀) (h31 : s.gpr .r31 = P s₀)
    (hrd : s.rd = s₀.rd) (hw : s.wr = s₀.wr) {ws : List Loc} (hws : ∀ l ∈ ws, l = .dat → ivR s₀ c ∈ s₀.wr) :
    AreasOk c s (fun _ => 4 * c.bw) (ivAreas c (P s₀) (S s₀)) ws := by
  have hL := hp.layout
  have hroom := hL.room
  have hdisp := hL.disp
  obtain hbw := bw_le hL
  obtain hb4 := buf_le4 hL
  have hP := hp.ivFit
  obtain inScr : ∀ d w, d + w ≤ 8 * c.total → InRegions s₀.wr (S s₀ + BitVec.ofNat 64 d) w :=
    fun d w h => ⟨_, hp.scr.wr, slot_contains hdisp h⟩
  refine ⟨fun l off ho => ?_, fun l off ho => ?_, fun l off w hw0 ho => ?_, fun l hl off w hw0 ho => ?_,
    fun l l' hne => ?_, fun _ => by omega_arith⟩
  · cases l
    · simp only [Core.loc, ivAreas] at ho ⊢; rw [h31, Nat.zero_add]
    · simp only [Core.loc, ivAreas] at ho ⊢; rw [hb, VG.Offset.add_add]
    · simp only [Core.loc, ivAreas] at ho ⊢; rw [hb, VG.Offset.add_add]
  · cases l <;> simp only [Core.loc] at ho ⊢ <;> slot_omega
  · rw [hrd, hw]
    cases l
    · exact ⟨_, hp.ivRd, VG.Offset.contains_base _ ho (by omega_arith)⟩
    · obtain ⟨r, hr, hc⟩ := inScr (8 * c.chnSlot + off) w (by slot_omega)
      refine ⟨r, List.mem_append_right _ hr, ?_⟩
      simp only [ivAreas]; rw [VG.Offset.add_add]; exact hc
    · obtain ⟨r, hr, hc⟩ := inScr (8 * c.buf + off) w (by omega_arith)
      refine ⟨r, List.mem_append_right _ hr, ?_⟩
      simp only [ivAreas]; rw [VG.Offset.add_add]; exact hc
  · rw [hw]
    cases l
    · exact ⟨_, hws _ hl rfl, VG.Offset.contains_base _ ho (by omega_arith)⟩
    · simp only [ivAreas]; rw [VG.Offset.add_add]; exact inScr _ _ (by slot_omega)
    · simp only [ivAreas]; rw [VG.Offset.add_add]; exact inScr _ _ (by omega_arith)
  · have dIv : ∀ d, d + 4 * c.bw ≤ 8 * c.total →
        Region.Disjoint (ivR s₀ c) ⟨S s₀ + BitVec.ofNat 64 d, 4 * c.bw⟩ :=
      fun d h => hp.ivScr.sub_right (slot_sub h)
    obtain dCB : Region.Disjoint ⟨slotA (S s₀) c.chnSlot, 4 * c.bw⟩ ⟨slotA (S s₀) c.buf, 4 * c.bw⟩ :=
      VG.Offset.disjoint _ (.inr (by slot_omega)) (by slot_omega) (by omega_arith)
    cases l <;> cases l' <;> simp only [ne_eq, not_true_eq_false] at hne <;> simp only [ivAreas]
    · exact dIv _ (by slot_omega)
    · exact dIv _ (by omega_arith)
    · exact (dIv _ (by slot_omega)).symm
    · exact dCB
    · exact (dIv _ (by omega_arith)).symm
    · exact dCB.symm

theorem copyBlk_ok {bw : Nat} {dst src : Loc} {ws : List Loc} (hd : dst ∈ ws) {len : Loc → Nat}
    (hl : ∀ l, len l = 4 * bw) : ∀ o ∈ copyBlk bw dst src, o.InBounds len ∧ o.dst ∈ ws := by
  intro o ho
  simp only [copyBlk, List.mem_map, List.mem_range] at ho
  obtain ⟨w, hw, rfl⟩ := ho
  refine ⟨⟨?_, ?_, fun _ _ h => by cases h⟩, hd⟩ <;>
    simp only [Op.width, Bool.false_eq_true, ite_false, ite_true, hl] <;> omega_using [hw]

/-! ## The entry -/

/-- After the entry: the scratch buffer at `sb`, the mode's state in `r29`–`r31`,
the caller's `r29`–`r31` and the return address in their slots, the IV in
the chaining value's. -/
structure Entered (c : Core) (s₀ s : State) : Prop where
  b : s.gpr sb = S s₀
  r29 : s.gpr .r29 = P s₀
  r30 : s.gpr .r30 = s₀.gpr .r6
  r31 : s.gpr .r31 = Dp s₀
  keep : ∀ r ∈ kept, r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : ∀ i < 3, s.mem.readW (slotA (S s₀) (c.savedSlot i)) 64 = s₀.gpr (Core.savedRegs.getD i .r29)
  lr : s.mem.readW (slotA (S s₀) c.lrSlot) 64 = s₀.lr
  chn : bytesAt s.mem (slotA (S s₀) c.chnSlot) (4 * c.bw) = bytesAt s₀.mem (P s₀) (4 * c.bw)
  frame : Frame [modeR c (S s₀)] s₀.mem s.mem

/-- The registers the entry writes are not kept, but for `r29`–`r31`. -/
theorem kept_ne_entry : ∀ r ∈ kept, r ≠ .r0 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r8 ∧ r ≠ .r9 := by decide

theorem entry_wp {s₀ : State} (hp : SeqPre c M s₀) :
    WP isa (.block (c.entry ++ c.ivIn)) s₀ (Entered c s₀) := by
  have hL := hp.layout
  have hroom := hL.room
  have hdisp := hL.disp
  obtain hbw := bw_le hL
  have hS := hp.scr
  obtain hlr : c.lrSlot < c.total := by slot_omega
  obtain hsv : ∀ i < 3, c.savedSlot i < c.total := fun i hi => by slot_omega
  simp only [Core.entry, Core.ivIn, range3_map, Core.savedRegs, List.getD_cons_zero, List.getD_cons_succ,
    List.cons_append, List.nil_append, mov]
  refine wp_mflr fun s₁ u₁ => ?_
  refine wp_std (a := slotA (S s₀) c.lrSlot) (by decide) ⟨by slot_omega, by slot_omega⟩
    (by rw [u₁.other _ (by decide)]) (by rw [u₁.wr]; exact slot_inW hS hdisp hlr) fun s₂ u₂ => ?_
  refine wp_std (a := slotA (S s₀) (c.savedSlot 0)) (by decide) ⟨by slot_omega, by slot_omega⟩
    (by rw [u₂.gpr, u₁.other _ (by decide)]) (by rw [u₂.wr, u₁.wr]; exact slot_inW hS hdisp (hsv 0 (by decide)))
    fun s₃ u₃ => ?_
  refine wp_std (a := slotA (S s₀) (c.savedSlot 1)) (by decide) ⟨by slot_omega, by slot_omega⟩
    (by rw [u₃.gpr, u₂.gpr, u₁.other _ (by decide)])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact slot_inW hS hdisp (hsv 1 (by decide))) fun s₄ u₄ => ?_
  refine wp_std (a := slotA (S s₀) (c.savedSlot 2)) (by decide) ⟨by slot_omega, by slot_omega⟩
    (by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide)])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact slot_inW hS hdisp (hsv 2 (by decide))) fun s₅ u₅ => ?_
  obtain g₅ : s₅.gpr = s₁.gpr := by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]
  have v₁ : ∀ r, r ≠ .r0 → s₁.gpr r = s₀.gpr r := u₁.other
  obtain m₅ : s₅.mem = (((s₀.mem.writeW (slotA (S s₀) c.lrSlot) s₀.lr).writeW (slotA (S s₀) (c.savedSlot 0))
      (s₀.gpr .r29)).writeW (slotA (S s₀) (c.savedSlot 1)) (s₀.gpr .r30)).writeW (slotA (S s₀) (c.savedSlot 2))
      (s₀.gpr .r31) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr,
      v₁ .r29 (by decide), v₁ .r30 (by decide), v₁ .r31 (by decide)]
  refine wp_mr fun s₆ u₆ => wp_mr fun s₇ u₇ => wp_mr fun s₈ u₈ => wp_mr fun s₉ u₉ => wp_mr fun s₁₀ u₁₀ => ?_
  obtain m₁₀ : s₁₀.mem = s₅.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  obtain rd₁₀ : s₁₀.rd = s₀.rd := by rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr₁₀ : s₁₀.wr = s₀.wr := by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain b₁₀ : s₁₀.gpr sb = S s₀ := by
    rw [show sb = .r5 from rfl] at u₁₀ ⊢
    rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      g₅, v₁ _ (by decide)]
  obtain r31₁₀ : s₁₀.gpr .r31 = P s₀ := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide),
      g₅, v₁ _ (by decide)]
  obtain r6₁₀ : s₁₀.gpr .r6 = Dp s₀ := by
    rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      g₅, v₁ _ (by decide)]
  obtain r29₁₀ : s₁₀.gpr .r29 = P s₀ := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr,
      g₅, v₁ _ (by decide)]
  obtain r30₁₀ : s₁₀.gpr .r30 = s₀.gpr .r6 := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide),
      g₅, v₁ _ (by decide)]
  obtain keep₁₀ : ∀ r ∈ kept, r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → s₁₀.gpr r = s₀.gpr r := fun r hr h29 h30 h31 => by
    obtain h := kept_ne_entry r hr
    rw [u₁₀.other r h.2.1, u₉.other r h.2.2.1, u₈.other r h31, u₇.other r h30, u₆.other r h29, g₅, v₁ r h.1]
  -- The saved values.
  obtain sep : ∀ i j, i < c.total → j < c.total → i ≠ j →
      Region.Disjoint ⟨slotA (S s₀) i, 8⟩ ⟨slotA (S s₀) j, 8⟩ := fun i j hi hj hne => slot_sep hdisp hi hj hne
  obtain sv₅ : ∀ i < 3, s₅.mem.readW (slotA (S s₀) (c.savedSlot i)) 64 = s₀.gpr (Core.savedRegs.getD i .r29) := by
    intro i hi
    rw [m₅]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega_arith) with rfl | rfl | rfl
    · rw [readW_sep64 (sep _ _ (hsv 0 (by decide)) (hsv 2 (by decide)) (by slot_omega)),
        readW_sep64 (sep _ _ (hsv 0 (by decide)) (hsv 1 (by decide)) (by slot_omega)), Mem.readW_writeW_self64]; rfl
    · rw [readW_sep64 (sep _ _ (hsv 1 (by decide)) (hsv 2 (by decide)) (by slot_omega)),
        Mem.readW_writeW_self64]; rfl
    · rw [Mem.readW_writeW_self64]; rfl
  obtain lr₅ : s₅.mem.readW (slotA (S s₀) c.lrSlot) 64 = s₀.lr := by
    rw [m₅, readW_sep64 (sep _ _ hlr (hsv 2 (by decide)) (by slot_omega)),
      readW_sep64 (sep _ _ hlr (hsv 1 (by decide)) (by slot_omega)),
      readW_sep64 (sep _ _ hlr (hsv 0 (by decide)) (by slot_omega)), Mem.readW_writeW_self64]
  obtain f₅ : Frame [modeR c (S s₀)] s₀.mem s₅.mem := by
    rw [m₅]
    exact ((((Frame.refl _ _).writeW List.mem_cons_self _ (slot_mode hL (by slot_omega) (by slot_omega))).writeW
      List.mem_cons_self _ (slot_mode hL (by slot_omega) (by slot_omega))).writeW List.mem_cons_self _
      (slot_mode hL (by slot_omega) (by slot_omega))).writeW List.mem_cons_self _
      (slot_mode hL (by slot_omega) (by slot_omega))
  -- The IV to the chaining value.
  refine opsCode_wp c (ws := [.chn]) (copyBlk_ok (List.mem_singleton_self _) fun _ => rfl)
    (ivAreasOk hp b₁₀ r31₁₀ rd₁₀ wr₁₀ (fun l hl e => by simp at hl; subst hl; cases e))
    fun s₁₁ a₁₁ f₁₁ g₁₁ rd₁₁ wr₁₁ => wp_mr fun s₁₂ u₁₂ => wp_nil ?_
  rw [m₁₀] at a₁₁ f₁₁
  obtain chnOnly : ∀ {R : Region}, R.Disjoint (chnRegion c (S s₀)) →
      ∀ r ∈ areaRegions (fun _ => 4 * c.bw) (ivAreas c (P s₀) (S s₀)) [.chn], R.Disjoint r := fun h r hr => by
    simp only [areaRegions, ivAreas, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h
  obtain g : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r31 → s₁₂.gpr r = s₁₀.gpr r := fun r h8 h9 h31 => by
    rw [u₁₂.other r h31, g₁₁ r h8 h9]
  refine ⟨by rw [g _ (by decide) (by decide) (by decide)]; exact b₁₀,
    by rw [g _ (by decide) (by decide) (by decide)]; exact r29₁₀,
    by rw [g _ (by decide) (by decide) (by decide)]; exact r30₁₀,
    by rw [u₁₂.gpr, g₁₁ _ (by decide) (by decide), r6₁₀],
    fun r hr h29 h30 h31 => by
      rw [g r (kept_ne_entry r hr).2.2.2.1 (kept_ne_entry r hr).2.2.2.2 h31, keep₁₀ r hr h29 h30 h31],
    by rw [u₁₂.rd, rd₁₁, rd₁₀], by rw [u₁₂.wr, wr₁₁, wr₁₀], fun i hi => ?_, ?_, ?_, ?_⟩
  · rw [u₁₂.mem, ← sv₅ i hi]
    exact f₁₁.readW (Region.contains_self _ _) (chnOnly
      (VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega))) (by decide)
  · rw [u₁₂.mem, ← lr₅]
    exact f₁₁.readW (Region.contains_self _ _) (chnOnly
      (VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega))) (by decide)
  · refine List.map_congr_left fun i hi => ?_
    obtain hi := List.mem_range.mp hi
    obtain e := a₁₁ .chn i hi
    simp only [cont, ivAreas] at e
    rw [u₁₂.mem, e, copyBlk_apply (by decide), ite_eq_left ⟨rfl, hi⟩]
    exact f₅.bytes (R := ivR s₀ c) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.ivScr.sub_right (VG.Offset.sub_base _ (by slot_omega))) (by show 4 * c.bw ≤ 2 ^ 64; omega_arith) hi
  · rw [u₁₂.mem]
    refine f₅.trans (f₁₁.sub fun r hr => ?_)
    simp only [areaRegions, ivAreas, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨_, List.mem_singleton_self _, VG.Offset.sub _ (by slot_omega) (by slot_omega)⟩

/-! ## The exit -/

theorem restore_wp {s₀ t : State} (hp : SeqPre c M s₀) (hb : t.gpr sb = S s₀) (hwr : t.wr = s₀.wr)
    (hsv : ∀ i < 3, t.mem.readW (slotA (S s₀) (c.savedSlot i)) 64 = s₀.gpr (Core.savedRegs.getD i .r29))
    (hlr : t.mem.readW (slotA (S s₀) c.lrSlot) 64 = s₀.lr) {Q : State → Prop}
    (k : ∀ t', t'.gpr .r29 = s₀.gpr .r29 → t'.gpr .r30 = s₀.gpr .r30 → t'.gpr .r31 = s₀.gpr .r31 →
      t'.lr = s₀.lr → (∀ r, r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → r ≠ .r0 → t'.gpr r = t.gpr r) →
      t'.mem = t.mem → Q t') :
    WP isa (.block c.restore) t Q := by
  have hL := hp.layout
  have hroom := hL.room
  have hdisp := hL.disp
  obtain hS : ScrIn t (S s₀) c.total := ⟨by rw [hwr]; exact hp.scr.wr, hp.scr.fit⟩
  obtain hlrs : c.lrSlot < c.total := by slot_omega
  obtain hsv' : ∀ i < 3, c.savedSlot i < c.total := fun i hi => by slot_omega
  simp only [Core.restore, range3_map, Core.savedRegs, List.getD_cons_zero, List.getD_cons_succ,
    List.cons_append, List.nil_append]
  refine wp_ld (a := slotA (S s₀) (c.savedSlot 0)) (by decide) ⟨by slot_omega, by slot_omega⟩
    (by rw [hb]) (slot_in hS hdisp (hsv' 0 (by decide))) fun t₁ u₁ => ?_
  refine wp_ld (a := slotA (S s₀) (c.savedSlot 1)) (by decide) ⟨by slot_omega, by slot_omega⟩
    (by rw [u₁.other _ (by decide), hb]) (by rw [u₁.rd, u₁.wr]; exact slot_in hS hdisp (hsv' 1 (by decide)))
    fun t₂ u₂ => ?_
  refine wp_ld (a := slotA (S s₀) (c.savedSlot 2)) (by decide) ⟨by slot_omega, by slot_omega⟩
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hb])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact slot_in hS hdisp (hsv' 2 (by decide))) fun t₃ u₃ => ?_
  refine wp_ld (a := slotA (S s₀) c.lrSlot) (by decide) ⟨by slot_omega, by slot_omega⟩
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hb])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact slot_in hS hdisp hlrs) fun t₄ u₄ => ?_
  refine wp_mtlr (wp_nil ?_)
  obtain mm : t₃.mem = t.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine k _ ?_ ?_ ?_ ?_ (fun r h29 h30 h31 h0 => ?_) (by show t₄.mem = t.mem; rw [u₄.mem, mm])
  · show t₄.gpr .r29 = _
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hsv 0 (by decide)]; rfl
  · show t₄.gpr .r30 = _
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, hsv 1 (by decide)]; rfl
  · show t₄.gpr .r31 = _
    rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, hsv 2 (by decide)]; rfl
  · show t₄.gpr .r0 = _
    rw [u₄.gpr, mm, hlr]
  · show t₄.gpr r = _
    rw [u₄.other r h0, u₃.other r h31, u₂.other r h30, u₁.other r h29]

/-! ## The setup -/

theorem chunksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {D : Addr} {st n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint (dataRegion D st n) r) (hn : st * n ≤ 2 ^ 64) :
    chunksAt st m' D n = chunksAt st m D n := by
  refine List.map_congr_left fun j hj => List.map_congr_left fun u hu => ?_
  obtain hj := List.mem_range.mp hj
  obtain hu := List.mem_range.mp hu
  have : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  rw [VG.Offset.add_add]
  exact hf.bytes (R := dataRegion D st n) hd hn (by show st * j + u < st * n; omega_arith)

/-- The inputs: the data's steps and the IV, on entry. -/
abbrev xs0 (M : Mode) (s₀ : State) : List (List Byte) := chunksAt M.step s₀.mem (Dp s₀) (N s₀)
abbrev iv0 (c : Core) (s₀ : State) : List Byte := bytesAt s₀.mem (P s₀) (4 * c.bw)

/-- The regions the mode writes, on entry. -/
abbrev wrs0 (c : Core) (M : Mode) (s₀ : State) : List Region := wrs c (S s₀) (Dp s₀) (N s₀) M.step

/-- After the setup, at the loop. -/
structure SetUp (cs : CoreSpec c) (M : Mode) (F : StepFn) (k : cs.Key) (s₀ s : State) : Prop where
  fixed : Fixed c s (S s₀) (Dp s₀) (N s₀) M.step (4 * c.bw) (wrs0 c M s₀) (N s₀) 1
  inv : Inv cs s (S s₀) (Dp s₀) (N s₀) M.step (wrs0 c M s₀) (N s₀) 1 k F (iv0 c s₀) (xs0 M s₀) 0 s
  keep : ∀ r ∈ kept, r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → s.gpr r = s₀.gpr r
  r29 : s.gpr .r29 = P s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : ∀ i < 3, s.mem.readW (slotA (S s₀) (c.savedSlot i)) 64 = s₀.gpr (Core.savedRegs.getD i .r29)
  lr : s.mem.readW (slotA (S s₀) c.lrSlot) 64 = s₀.lr
  frame : Frame [modeR c (S s₀), coreRegion c (S s₀)] s₀.mem s.mem

theorem setup_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {k : cs.Key} (hp : SeqPre c M s₀)
    (hk : cs.KeyArgs s₀ (wrs0 c M s₀) k) :
    WP isa (.seq (.block (c.entry ++ c.ivIn)) c.prepare) s₀ (SetUp cs M F k s₀) := by
  have hL := hp.layout
  have hfit := hp.scr.fit
  have hroom := hL.room
  have hdisp := hL.disp
  obtain hbw := bw_le hL
  obtain hb4 := buf_le4 hL
  obtain modeScr : Region.Sub (modeR c (S s₀)) (scrRegion c (S s₀)) := VG.Offset.sub_base _ (by omega_arith)
  obtain coreScr : Region.Sub (coreRegion c (S s₀)) (scrRegion c (S s₀)) := Region.sub_prefix (by omega_arith)
  refine WP.seq (VG.PPC64LE.WP.of_syms (WP.mono (entry_wp hp) fun s₁ h₁ sy₁ => ?_))
  obtain hS₁ : ScrIn s₁ (S s₀) c.total := ⟨by rw [h₁.wr]; exact hp.scr.wr, hfit⟩
  obtain m1 : ∀ {a b : Region} {l : List Region}, b ∈ a :: b :: l := List.mem_cons_of_mem _ List.mem_cons_self
  refine WP.mono (cs.prepare_wp h₁.b hS₁ m1
    (cs.keyArgs_congr hk h₁.keep h₁.rd h₁.wr sy₁
      (h₁.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, m1, modeScr⟩)))
    fun s₂ ⟨ready₂, b₂, kept₂, f₂, rd₂, wr₂⟩ => ?_
  have kp : ∀ r, r ∈ kept → s₂.gpr r = s₁.gpr r := kept₂
  obtain f₀₂ : Frame [modeR c (S s₀), coreRegion c (S s₀)] s₀.mem s₂.mem :=
    (h₁.frame.mono (by simp)).trans (f₂.mono (by simp))
  obtain dataOut : ∀ r ∈ [modeR c (S s₀), coreRegion c (S s₀)],
      Region.Disjoint (dataRegion (Dp s₀) M.step (N s₀)) r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dataScr.sub_right modeScr
    · exact hp.dataScr.sub_right coreScr
  obtain modeOut : ∀ {R : Region}, Region.Sub R (modeR c (S s₀)) → ∀ r ∈ [coreRegion c (S s₀)], R.Disjoint r :=
    fun hsub r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (VG.Offset.disjoint_base _ (by slot_omega) (by omega_arith)).sub_left hsub
  refine ⟨⟨⟨by rw [wr₂, h₁.wr]; exact hp.scr.wr, hfit⟩,
      fun o w hw ho => by rw [wr₂, h₁.wr]; exact dataW_of_mem hp.dataW hp.dataFit hw ho, hp.dataFit, hp.dataScr,
      (s₀.gpr .r6).isLt, by omega_arith, by decide, ⟨hp.step.1, by have := hp.step.2; omega_arith⟩,
      ⟨by rcases hL.bw with h | h <;> omega_using [h], Nat.le_mul_of_pos_right _ hL.G_pos⟩,
      ⟨_, List.mem_cons_self, fun _ h => h⟩, List.mem_cons_of_mem _ List.mem_cons_self, hL⟩,
    ⟨b₂, fun _ _ _ _ => rfl, rfl, rfl, ?_, ?_, ready₂, ?_, ?_, Frame.refl _ _⟩,
    fun r hr h29 h30 h31 => by rw [kp r hr, h₁.keep r hr h29 h30 h31],
    by rw [kp _ (by decide), h₁.r29], by rw [rd₂, h₁.rd], by rw [wr₂, h₁.wr], fun i hi => ?_, ?_, f₀₂⟩
  · rw [kp _ (by decide), h₁.r31, Nat.mul_zero]; exact (BitVec.add_zero _).symm
  · rw [kp _ (by decide), h₁.r30, Nat.mul_zero, Nat.sub_zero]; simp only [N, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [chunksAt_frame f₀₂ dataOut (by have := hp.dataFit; omega_arith)]
    simp only [List.take_zero, run, List.nil_append, List.drop_zero]
  · simp only [List.take_zero, run]
    rw [iv0, ← h₁.chn]
    refine List.map_congr_left fun i hi => f₂.bytes (R := chnRegion c (S s₀))
      (modeOut (VG.Offset.sub _ (by slot_omega) (by slot_omega))) (by show 4 * c.bw ≤ 2 ^ 64; omega_arith)
      (List.mem_range.mp hi)
  · rw [← h₁.saved i hi]
    exact f₂.readW (Region.contains_self _ _) (modeOut (VG.Offset.sub _ (by slot_omega) (by slot_omega)))
      (by decide)
  · rw [← h₁.lr]
    exact f₂.readW (Region.contains_self _ _) (modeOut (VG.Offset.sub _ (by slot_omega) (by slot_omega)))
      (by decide)

/-! ## The function -/

/-- What the function changes besides the registers: memory only in the
core's and the mode's slots, the data and the IV; and it leaves the scratch
buffer's address in `sb`. -/
structure Changes (c : Core) (M : Mode) (s₀ s' : State) : Prop where
  sb : s'.gpr sb = S s₀
  frame : Frame [coreRegion c (S s₀), modeR c (S s₀), dataRegion (Dp s₀) M.step (N s₀), ivR s₀ c] s₀.mem s'.mem

/-- What the code `loops` must do, from the state after the key, with the
mode's first step to take: all of them (`Done`). -/
def LoopsOk (cs : CoreSpec c) (M : Mode) (F : StepFn) (s₀ : State) (k : cs.Key) (loops : Prog isa) : Prop :=
  ∀ s₂, Fixed c s₂ (S s₀) (Dp s₀) (N s₀) M.step (4 * c.bw) (wrs0 c M s₀) (N s₀) 1 →
    Inv cs s₂ (S s₀) (Dp s₀) (N s₀) M.step (wrs0 c M s₀) (N s₀) 1 k F (iv0 c s₀) (xs0 M s₀) 0 s₂ →
    WP isa loops s₂ (Done (c := c) s₂ (S s₀) (Dp s₀) (N s₀) M.step F (iv0 c s₀) (xs0 M s₀))

/-- The function around the loops `loops`, and what it changes (`Changes`). -/
theorem seqWith_changes_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {k : cs.Key} {loops : Prog isa}
    (hp : SeqPre c M s₀) (hloops : LoopsOk cs M F s₀ k loops) (hk : cs.KeyArgs s₀ (wrs0 c M s₀) k) :
    WP isa (c.seqWith loops M.ivOut) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt M.step s'.mem (Dp s₀) (N s₀) = (run F (iv0 c s₀) (xs0 M s₀)).1 ∧
      (M.ivOut = true → bytesAt s'.mem (P s₀) (4 * c.bw) = (run F (iv0 c s₀) (xs0 M s₀)).2) ∧
      Changes c M s₀ s' := by
  have hL := hp.layout
  have hfit := hp.scr.fit
  have hroom := hL.room
  have hdisp := hL.disp
  obtain hbw := bw_le hL
  obtain hb4 := buf_le4 hL
  obtain modeScr : Region.Sub (modeR c (S s₀)) (scrRegion c (S s₀)) := VG.Offset.sub_base _ (by omega_arith)
  obtain coreScr : Region.Sub (coreRegion c (S s₀)) (scrRegion c (S s₀)) := Region.sub_prefix (by omega_arith)
  obtain chnScr : Region.Sub (chnRegion c (S s₀)) (scrRegion c (S s₀)) := VG.Offset.sub_base _ (by slot_omega)
  obtain hsu := setup_wp cs (F := F) hp hk
  rw [WP.seq_iff] at hsu
  refine WP.sp_intro ?_
  unfold Core.seqWith
  refine WP.seq (WP.mono hsu fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono h₁ fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (hloops s₃ h₃.fixed h₃.inv) fun s₄ h₄ => ?_)
  -- What the run so far changed.
  obtain slotOut : ∀ {R : Region}, Region.Sub R (modeR c (S s₀)) → Region.Disjoint R (chnRegion c (S s₀)) →
      ∀ r ∈ big c (S s₀) (Dp s₀) (N s₀) M.step, R.Disjoint r := fun hsub hc r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (VG.Offset.disjoint_base _ (by slot_omega) (by omega_arith)).sub_left hsub
    · exact hc
    · exact (hp.dataScr.sub_right modeScr).symm.sub_left hsub
  obtain sv₄ : ∀ i < 3, s₄.mem.readW (slotA (S s₀) (c.savedSlot i)) 64 = s₀.gpr (Core.savedRegs.getD i .r29) :=
    fun i hi => by
      rw [← h₃.saved i hi]
      exact h₄.frame.readW (Region.contains_self _ _) (slotOut (VG.Offset.sub _ (by slot_omega) (by slot_omega))
        (VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega))) (by decide)
  obtain lr₄ : s₄.mem.readW (slotA (S s₀) c.lrSlot) 64 = s₀.lr := by
    rw [← h₃.lr]
    exact h₄.frame.readW (Region.contains_self _ _) (slotOut (VG.Offset.sub _ (by slot_omega) (by slot_omega))
      (VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega))) (by decide)
  have data₄ : chunksAt M.step s₄.mem (Dp s₀) (N s₀) = (run F (iv0 c s₀) (xs0 M s₀)).1 := h₄.data
  obtain keep₄ : ∀ r ∈ kept, r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → s₄.gpr r = s₀.gpr r :=
    fun r hr h29 h30 h31 => by rw [h₄.keep r hr h30 h31, h₃.keep r hr h29 h30 h31]
  obtain r29₄ : s₄.gpr .r29 = P s₀ := by rw [h₄.keep _ (by decide) (by decide) (by decide), h₃.r29]
  obtain rd₄ : s₄.rd = s₀.rd := by rw [h₄.rd, h₃.rd]
  obtain wr₄ : s₄.wr = s₀.wr := by rw [h₄.wr, h₃.wr]
  obtain abi : ∀ t : State, t.sp = s₀.sp → t.lr = s₀.lr → t.gpr .r29 = s₀.gpr .r29 → t.gpr .r30 = s₀.gpr .r30 →
      t.gpr .r31 = s₀.gpr .r31 → (∀ r ∈ kept, r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → t.gpr r = s₀.gpr r) →
      abiPreserved s₀ t := fun t hsp hlr h29 h30 h31 hk => ⟨fun r hr => by
        by_cases e29 : r = .r29
        · subst e29; exact h29
        by_cases e30 : r = .r30
        · subst e30; exact h30
        by_cases e31 : r = .r31
        · subst e31; exact h31
        exact hk r (List.mem_cons_of_mem _ hr) e29 e30 e31, hsp, hlr⟩
  obtain ne0 : ∀ r ∈ kept, r ≠ .r0 := fun r hr => (kept_ne_entry r hr).1
  obtain fr₄ : Frame [coreRegion c (S s₀), modeR c (S s₀), dataRegion (Dp s₀) M.step (N s₀), ivR s₀ c]
      s₀.mem s₄.mem := by
    refine (h₃.frame.mono (by simp)).trans (h₄.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨modeR c (S s₀), by simp, VG.Offset.sub _ (by slot_omega) (by slot_omega)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  obtain r0ne : Reg.r5 ≠ .r29 ∧ Reg.r5 ≠ .r30 ∧ Reg.r5 ≠ .r31 ∧ Reg.r5 ≠ .r0 := by decide
  cases hiv : M.ivOut
  · rw [show (if false = true then c.ivBack else []) ++ c.restore = c.restore by simp]
    refine restore_wp hp h₄.b wr₄ sv₄ lr₄ fun t g29 g30 g31 glr g m hsp =>
      And.intro (abi t hsp glr g29 g30 g31 fun r hr h29 h30 h31 => by
          rw [g r h29 h30 h31 (ne0 r hr), keep₄ r hr h29 h30 h31])
        (And.intro (by rw [m, data₄]) (And.intro (fun h => by cases h)
          ⟨by show t.gpr .r5 = _; rw [g _ r0ne.1 r0ne.2.1 r0ne.2.2.1 r0ne.2.2.2]; exact h₄.b,
            by rw [m]; exact fr₄⟩))
  · rw [show (if true = true then c.ivBack else []) ++ c.restore =
      mov .r31 .r29 :: (c.opsCode (copyBlk c.bw .dat .chn) ++ c.restore) by simp [Core.ivBack]]
    refine wp_mr fun s₅ u₅ => ?_
    obtain b₅ : s₅.gpr sb = S s₀ := by rw [u₅.other _ (by decide)]; exact h₄.b
    refine opsCode_wp c (ws := [.dat]) (copyBlk_ok (List.mem_singleton_self _) fun _ => rfl)
      (ivAreasOk hp b₅ (by rw [u₅.gpr, r29₄]) (by rw [u₅.rd, rd₄]) (by rw [u₅.wr, wr₄])
        (fun _ _ _ => hp.ivWr hiv)) fun s₆ a₆ f₆ g₆ rd₆ wr₆ => ?_
    rw [u₅.mem] at a₆ f₆
    obtain ivOnly : ∀ {R : Region}, R.Disjoint (ivR s₀ c) → ∀ r ∈ areaRegions (fun _ => 4 * c.bw)
        (ivAreas c (P s₀) (S s₀)) [.dat], R.Disjoint r := fun h r hr => by
      simp only [areaRegions, ivAreas, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact h
    obtain scrIv : ∀ {R : Region}, Region.Sub R (scrRegion c (S s₀)) → R.Disjoint (ivR s₀ c) :=
      fun h => (hp.ivScr.sub_right h).symm
    obtain sv₆ : ∀ i < 3, s₆.mem.readW (slotA (S s₀) (c.savedSlot i)) 64 = s₀.gpr (Core.savedRegs.getD i .r29) :=
      fun i hi => by
        rw [← sv₄ i hi]
        exact f₆.readW (Region.contains_self _ _)
          (ivOnly (scrIv (VG.Offset.sub_base _ (by slot_omega)))) (by decide)
    obtain lr₆ : s₆.mem.readW (slotA (S s₀) c.lrSlot) 64 = s₀.lr := by
      rw [← lr₄]
      exact f₆.readW (Region.contains_self _ _) (ivOnly (scrIv (VG.Offset.sub_base _ (by slot_omega)))) (by decide)
    obtain g₆' : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r31 → s₆.gpr r = s₄.gpr r := fun r h8 h9 h31 => by
      rw [g₆ r h8 h9, u₅.other r h31]
    refine restore_wp hp (by rw [g₆' _ (by decide) (by decide) (by decide)]; exact h₄.b)
      (by rw [wr₆, u₅.wr, wr₄]) sv₆ lr₆ fun t g29 g30 g31 glr g m hsp =>
        ⟨abi t hsp glr g29 g30 g31 fun r hr h29 h30 h31 => by
          rw [g r h29 h30 h31 (ne0 r hr), g₆' r (kept_ne r hr).1 (kept_ne r hr).2 h31, keep₄ r hr h29 h30 h31],
          ?_, fun _ => ?_, ⟨?_, ?_⟩⟩
    · rw [m, chunksAt_frame f₆ (ivOnly (hp.ivData hiv).symm) (by have := hp.dataFit; omega_arith), data₄]
    · rw [m]
      have hc := h₄.chn
      rw [← hc]
      refine List.map_congr_left fun i hi => ?_
      obtain hi := List.mem_range.mp hi
      obtain e₆ := a₆ .dat i hi
      simp only [cont, ivAreas] at e₆
      rw [e₆, copyBlk_apply (by decide), ite_eq_left ⟨rfl, hi⟩]
      rfl
    · show t.gpr .r5 = _
      rw [g _ r0ne.1 r0ne.2.1 r0ne.2.2.1 r0ne.2.2.2, g₆' _ (by decide) (by decide) (by decide)]; exact h₄.b
    · rw [m]
      refine fr₄.trans (f₆.sub fun r hr => ?_)
      simp only [areaRegions, ivAreas, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact ⟨_, by simp, fun _ h => h⟩

/-- One step at a time. -/
theorem steps_ok (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {k : cs.Key}
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c M.step (4 * c.bw)))
    (hpost : ∀ o ∈ M.post, o.InBounds (lens c M.step (4 * c.bw)))
    (hcomp : Computes M (4 * c.bw) (cs.cipher k) F) : LoopsOk cs M F s₀ k (c.steps M) := fun _ hFx hI =>
  WP.mono (loop_wp cs hFx rfl hpre hpost hcomp (chunksAt_length _ _ _ _) hI) fun _ h =>
    h.done (chunksAt_length _ _ _ _)

/-- `seq_wp`, and what the function changes (`Changes`). -/
theorem seq_changes_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {k : cs.Key} (hp : SeqPre c M s₀)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c M.step (4 * c.bw)))
    (hpost : ∀ o ∈ M.post, o.InBounds (lens c M.step (4 * c.bw)))
    (hcomp : Computes M (4 * c.bw) (cs.cipher k) F) (hk : cs.KeyArgs s₀ (wrs0 c M s₀) k) :
    WP isa (c.seq M) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt M.step s'.mem (Dp s₀) (N s₀) = (run F (iv0 c s₀) (xs0 M s₀)).1 ∧
      (M.ivOut = true → bytesAt s'.mem (P s₀) (4 * c.bw) = (run F (iv0 c s₀) (xs0 M s₀)).2) ∧
      Changes c M s₀ s' :=
  seqWith_changes_wp cs hp (steps_ok cs hpre hpost hcomp) hk

theorem seq_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {k : cs.Key} (hp : SeqPre c M s₀)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c M.step (4 * c.bw)))
    (hpost : ∀ o ∈ M.post, o.InBounds (lens c M.step (4 * c.bw)))
    (hcomp : Computes M (4 * c.bw) (cs.cipher k) F) (hk : cs.KeyArgs s₀ (wrs0 c M s₀) k) :
    WP isa (c.seq M) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt M.step s'.mem (Dp s₀) (N s₀) = (run F (iv0 c s₀) (xs0 M s₀)).1 ∧
      (M.ivOut = true → bytesAt s'.mem (P s₀) (4 * c.bw) = (run F (iv0 c s₀) (xs0 M s₀)).2) :=
  WP.mono (seq_changes_wp cs hp hpre hpost hcomp hk) fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

end VG.Proof.Modes.PPC64LE
