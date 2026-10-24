module

public import VerifiedGarbage.Proof.Rc2.PPC64LE.Scan
public import VerifiedGarbage.Proof.Rc2.Table
public import VerifiedGarbage.Impl.Rc2.PPC64LE.ExpandKey
import VerifiedGarbage.Proof.Rc2.PPC64LE.Lookup
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep

/-!
# RC2 on PPC64LE: the steps of key expansion

`piLookup_run`: the scan of PITABLE in the working space leaves `pi q` in
`r11`. Each step of the loops (`copy_run`, `fill_run`, `reduce_run`,
`descend_run`) stores one byte of `L`.
-/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE

theorem piRegs : ScanRegs .r7 .r15 := ⟨by decide, by decide, by decide, by decide, by decide, by decide,
  by decide, by decide, by decide⟩

/-- The scan of PITABLE at `r7`. -/
theorem piLookup_run (s : State) {W : Addr} (hW : s.gpr .r7 = W) (hq : (s.gpr .r10).toNat < 256)
    (hr : ∀ k < 32, InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (8 * k)) 8) (hP : Proof.Rc2.PiHeld s.mem W) :
    WP isa piLookup s fun t =>
      t.gpr .r11 = (Spec.Rc2.pi ((s.gpr .r10).setWidth 8)).setWidth 64 ∧
      Keep [.r0, .r11, .r12, .r15] s t ∧ t.mem = s.mem := by
  refine WP.mono (scan_run piRegs s hW (rows := 32) (by decide) (lanes := [0, 1, 2]) (by decide) (by decide)
    (bits := 8) (by decide) hq (rotSum_byte _) hr) fun t ⟨t11, tk, tm⟩ => ⟨?_, tk, tm⟩
  have e : W + s.gpr .r10 = W + BitVec.ofNat 64 (s.gpr .r10).toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [t11, entry_byte, e, hP.byte hq]
  refine congrArg (BitVec.setWidth 64) ?_
  simp only [Spec.Rc2.pi, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt hq]

theorem lo8_ext (b : BitVec 8) : (b.setWidth 64).setWidth 8 = b :=
  BitVec.setWidth_setWidth_of_le _ (by decide) |>.trans (BitVec.setWidth_eq b)

theorem copy_run (s : State) (hr : InRegions (s.rd ++ s.wr) (s.gpr .r3 + s.gpr .r8) 1)
    (hw : InRegions s.wr (s.gpr .r6 + s.gpr .r8) 1) :
    WP isa (.block copyKey) s fun t =>
      t.gpr .r8 = s.gpr .r8 + 1 ∧ t.gpr .r0 = s.gpr .r8 + 1 - s.gpr .r4 ∧
      t.mem = s.mem.writeW (s.gpr .r6 + s.gpr .r8) (s.mem (s.gpr .r3 + s.gpr .r8)) ∧
      Keep [.r0, .r8, .r9, .r12] s t := by
  refine WP.mono (WP.keep [.r0, .r8, .r9, .r12] (c := .block copyKey) (Q := fun t =>
      t.gpr .r8 = s.gpr .r8 + 1 ∧ t.gpr .r0 = s.gpr .r8 + 1 - s.gpr .r4 ∧
      t.mem = s.mem.writeW (s.gpr .r6 + s.gpr .r8) (s.mem (s.gpr .r3 + s.gpr .r8))) ?_
    (by simp [writesOnly, Code.allInstrs_eq, instrs, copyKey, dstOf]) rfl) fun t ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
  unfold copyKey
  rrun [hr, hw, lo8_ext]

theorem ext_lt (b : BitVec 8) : (b.setWidth 64).toNat < 256 := by
  rw [BitVec.toNat_setWidth]; have := b.isLt; omega

theorem ext_and (a : BitVec 8) (y : BitVec 64) : a.setWidth 64 &&& y = (a &&& y.setWidth 8).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth]
  by_cases h : i < 8
  · simp [h, hi]
  · simp [h, BitVec.getLsbD_of_ge a i (by omega)]

theorem ext_xor (a b : BitVec 8) : a.setWidth 64 ^^^ b.setWidth 64 = (a ^^^ b).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_setWidth]
  by_cases h : i < 8
  · simp [h, hi]
  · simp [BitVec.getLsbD_of_ge a i (by omega), BitVec.getLsbD_of_ge b i (by omega)]

theorem ext_add (a b : BitVec 8) : ((a.setWidth 64 + b.setWidth 64) <<< 56) >>> 56 = (a + b).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt; have hb := b.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_setWidth,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show a.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show a.toNat + b.toNat < 2 ^ 64 by omega)]
  omega

/-- The registers the steps of key expansion write. -/
abbrev keyTemps : List Reg := [.r0, .r8, .r9, .r10, .r11, .r12, .r15]

/-- The scan's environment: PITABLE at `W` in the working space at `r7`. -/
structure PiEnv (W : Addr) (s : State) : Prop where
  r7 : s.gpr .r7 = W
  rd : ∀ k < 32, InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (8 * k)) 8
  held : Proof.Rc2.PiHeld s.mem W

theorem PiEnv.keep {W : Addr} {s t : State} (E : PiEnv W s) {rs : List Reg} (k : Keep rs s t)
    (h7 : Reg.r7 ∉ rs) (hm : t.mem = s.mem) : PiEnv W t :=
  ⟨by rw [k.gpr h7]; exact E.r7, fun j hj => by rw [k.2.1, k.2.2]; exact E.rd j hj, by rw [hm]; exact E.held⟩

/-- A byte through the scan and into `L[i]`: the scan and `storeKey`. -/
theorem piStore_run (s : State) {W : Addr} (E : PiEnv W s) (hq : (s.gpr .r10).toNat < 256)
    (hw : InRegions s.wr (s.gpr .r6 + s.gpr .r8) 1) :
    WP isa (.seq piLookup (.block storeKey)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .r6 + s.gpr .r8) (Spec.Rc2.pi ((s.gpr .r10).setWidth 8)) ∧
      Keep [.r0, .r11, .r12, .r15, .r9] s t := by
  apply WP.seq
  refine WP.mono (piLookup_run s E.r7 hq E.rd E.held) fun t₁ ⟨a₁, k₁, m₁⟩ => ?_
  have h6 : t₁.gpr .r6 = s.gpr .r6 := k₁.gpr (by decide)
  have h8 : t₁.gpr .r8 = s.gpr .r8 := k₁.gpr (by decide)
  refine WP.mono (WP.keep [.r9] (c := .block storeKey) (Q := fun t =>
      t.mem = t₁.mem.writeW (t₁.gpr .r6 + t₁.gpr .r8) ((t₁.gpr .r11).setWidth 8)) ?_
    (by simp [writesOnly, Code.allInstrs_eq, instrs, storeKey, dstOf]) rfl) fun t ⟨a, k⟩ =>
      ⟨by rw [a, a₁, m₁, h6, h8, lo8_ext], (k₁.trans k).mono (by simp)⟩
  unfold storeKey
  rrun [show InRegions t₁.wr (t₁.gpr .r6 + t₁.gpr .r8) 1 by rw [k₁.2.2, h6, h8]; exact hw]

theorem fill_run (s : State) {W : Addr} (E : PiEnv W s)
    (hlo : InRegions (s.rd ++ s.wr) (s.gpr .r6 + s.gpr .r8 - 1#64) 1)
    (hhi : InRegions (s.rd ++ s.wr) (s.gpr .r6 + (s.gpr .r8 - s.gpr .r4)) 1)
    (hw : InRegions s.wr (s.gpr .r6 + s.gpr .r8) 1) :
    WP isa fillKey s fun t =>
      t.gpr .r8 = s.gpr .r8 + 1 ∧ t.gpr .r0 = s.gpr .r8 + 1 - 128#64 ∧
      t.mem = s.mem.writeW (s.gpr .r6 + s.gpr .r8)
        (Spec.Rc2.pi (s.mem (s.gpr .r6 + s.gpr .r8 - 1#64) + s.mem (s.gpr .r6 + (s.gpr .r8 - s.gpr .r4)))) ∧
      Keep keyTemps s t := by
  unfold fillKey
  apply WP.seq
  refine WP.mono (WP.keep [.r9, .r10, .r11] (c := .block fillInput) (Q := fun t =>
      t.gpr .r10 = (s.mem (s.gpr .r6 + s.gpr .r8 - 1#64) + s.mem (s.gpr .r6 + (s.gpr .r8 - s.gpr .r4))).setWidth 64 ∧
      t.mem = s.mem) (by unfold fillInput mask; rrun [hlo, hhi, ext_add])
    (by simp [writesOnly, Code.allInstrs_eq, instrs, fillInput, mask, dstOf]) rfl) fun t₁ ⟨⟨a₁, m₁⟩, k₁⟩ => ?_
  have h6 : t₁.gpr .r6 = s.gpr .r6 := k₁.gpr (by decide)
  have h8 : t₁.gpr .r8 = s.gpr .r8 := k₁.gpr (by decide)
  apply WP.seq
  refine WP.mono (piLookup_run t₁ (E.keep k₁ (by decide) m₁).r7 (by rw [a₁]; exact ext_lt _)
    (E.keep k₁ (by decide) m₁).rd (E.keep k₁ (by decide) m₁).held) fun t₂ ⟨a₂, k₂, m₂⟩ => ?_
  have h6' : t₂.gpr .r6 = s.gpr .r6 := by rw [k₂.gpr (by decide), h6]
  have h8' : t₂.gpr .r8 = s.gpr .r8 := by rw [k₂.gpr (by decide), h8]
  refine WP.mono (WP.keep [.r0, .r8, .r9] (c := .block fillFinish) (Q := fun t =>
      t.gpr .r8 = t₂.gpr .r8 + 1 ∧ t.gpr .r0 = t₂.gpr .r8 + 1 - 128#64 ∧
      t.mem = t₂.mem.writeW (t₂.gpr .r6 + t₂.gpr .r8) ((t₂.gpr .r11).setWidth 8)) ?_
    (by simp [writesOnly, Code.allInstrs_eq, instrs, fillFinish, storeKey, dstOf]) rfl)
    fun t ⟨⟨a, b, c⟩, k⟩ => ⟨by rw [a, h8'], by rw [b, h8'], by rw [c, a₂, m₂, m₁, h6', h8', a₁, lo8_ext, lo8_ext],
      ((k₁.trans k₂).trans k).mono (by simp)⟩
  unfold fillFinish storeKey
  rrun [show InRegions t₂.wr (t₂.gpr .r6 + t₂.gpr .r8) 1 by rw [k₂.2.2, k₁.2.2, h6', h8']; exact hw]

theorem reduce_run (s : State) {W : Addr} (E : PiEnv W s) (hr : InRegions (s.rd ++ s.wr) (s.gpr .r6 + s.gpr .r8) 1)
    (hw : InRegions s.wr (s.gpr .r6 + s.gpr .r8) 1) :
    WP isa reduceKey s fun t =>
      t.mem = s.mem.writeW (s.gpr .r6 + s.gpr .r8)
        (Spec.Rc2.pi (s.mem (s.gpr .r6 + s.gpr .r8) &&& (s.gpr .r12).setWidth 8)) ∧
      Keep [.r0, .r9, .r10, .r11, .r12, .r15] s t := by
  unfold reduceKey
  apply WP.seq
  refine WP.mono (WP.keep [.r9, .r10] (c := .block reduceInput) (Q := fun t =>
      t.gpr .r10 = (s.mem (s.gpr .r6 + s.gpr .r8) &&& (s.gpr .r12).setWidth 8).setWidth 64 ∧
      t.mem = s.mem) (by unfold reduceInput; rrun [hr, ext_and])
    (by simp [writesOnly, Code.allInstrs_eq, instrs, reduceInput, dstOf]) rfl) fun t₁ ⟨⟨a₁, m₁⟩, k₁⟩ => ?_
  have h6 : t₁.gpr .r6 = s.gpr .r6 := k₁.gpr (by decide)
  have h8 : t₁.gpr .r8 = s.gpr .r8 := k₁.gpr (by decide)
  refine WP.mono (piStore_run t₁ (E.keep k₁ (by decide) m₁) (by rw [a₁]; exact ext_lt _)
    (by rw [k₁.2.2, h6, h8]; exact hw)) fun t ⟨a, k⟩ =>
      ⟨by rw [a, m₁, h6, h8, a₁, lo8_ext], (k₁.trans k).mono (by simp)⟩

theorem descend_run (s : State) {W : Addr} (E : PiEnv W s)
    (hlo : InRegions (s.rd ++ s.wr) (s.gpr .r6 + (s.gpr .r8 - 1#64) + 1#64) 1)
    (hhi : InRegions (s.rd ++ s.wr) (s.gpr .r6 + (s.gpr .r8 - 1#64 + s.gpr .r14)) 1)
    (hw : InRegions s.wr (s.gpr .r6 + (s.gpr .r8 - 1#64)) 1) :
    WP isa descendKey s fun t =>
      t.gpr .r8 = s.gpr .r8 - 1#64 ∧
      t.mem = s.mem.writeW (s.gpr .r6 + (s.gpr .r8 - 1#64))
        (Spec.Rc2.pi (s.mem (s.gpr .r6 + (s.gpr .r8 - 1#64) + 1#64) ^^^
          s.mem (s.gpr .r6 + (s.gpr .r8 - 1#64 + s.gpr .r14)))) ∧
      Keep keyTemps s t := by
  unfold descendKey
  apply WP.seq
  refine WP.mono (WP.keep [.r8, .r9, .r10, .r11] (c := .block descendInput) (Q := fun t =>
      t.gpr .r8 = s.gpr .r8 - 1#64 ∧
      t.gpr .r10 = (s.mem (s.gpr .r6 + (s.gpr .r8 - 1#64) + 1#64) ^^^
        s.mem (s.gpr .r6 + (s.gpr .r8 - 1#64 + s.gpr .r14))).setWidth 64 ∧
      t.mem = s.mem) (by unfold descendInput; rrun [hlo, hhi, ext_xor])
    (by simp [writesOnly, Code.allInstrs_eq, instrs, descendInput, dstOf]) rfl) fun t₁ ⟨⟨i₁, a₁, m₁⟩, k₁⟩ => ?_
  have h6 : t₁.gpr .r6 = s.gpr .r6 := k₁.gpr (by decide)
  refine WP.mono (piStore_run t₁ (E.keep k₁ (by decide) m₁) (by rw [a₁]; exact ext_lt _)
    (by rw [k₁.2.2, h6, i₁]; exact hw)) fun t ⟨a, k⟩ =>
      ⟨by rw [k.gpr (by decide), i₁], by rw [a, m₁, h6, i₁, a₁, lo8_ext], (k₁.trans k).mono (by simp)⟩

end VG.Proof.Rc2.PPC64LE
