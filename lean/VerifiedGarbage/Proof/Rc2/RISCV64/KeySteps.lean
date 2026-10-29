module

public import VerifiedGarbage.Proof.Rc2.RISCV64.Scan
public import VerifiedGarbage.Proof.Rc2.Table
public import VerifiedGarbage.Impl.Rc2.RISCV64.ExpandKey
import VerifiedGarbage.Proof.Rc2.RISCV64.Lookup
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep

/-!
# RC2 on RISC-V: the steps of key expansion

`piLookup_run`: the scan of PITABLE in the working space leaves `pi q` in
`t1`. Each step of the loops (`copy_run`, `fill_run`, `reduce_run`,
`descend_run`) stores one byte of `L`.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64

theorem piRegs : ScanRegs .a4 .t3 := ⟨by decide, by decide, by decide, by decide, by decide, by decide,
  by decide, by decide, by decide⟩

/-- The scan of PITABLE at `a4`. -/
theorem piLookup_run (s : State) {W : Addr} (hW : s.gpr .a4 = W) (hal : W.toNat % 8 = 0) (hq : (s.gpr .t0).toNat < 256)
    (hr : ∀ k < 32, InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (8 * k)) 8) (hP : Proof.Rc2.PiHeld s.mem W) :
    WP isa piLookup s fun t =>
      t.gpr .t1 = (Spec.Rc2.pi ((s.gpr .t0).setWidth 8)).setWidth 64 ∧
      Keep [.a7, .t1, .t2, .t3] s t ∧ t.mem = s.mem := by
  refine WP.mono (scan_run piRegs s hW hal (rows := 32) (by decide) (lanes := [0, 1, 2]) (by decide)
    (bits := 8) (by decide) hq (shiftSum_byte _) hr) fun t ⟨t11, tk, tm⟩ => ⟨?_, tk, tm⟩
  have e : W + s.gpr .t0 = W + BitVec.ofNat 64 (s.gpr .t0).toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [t11, entry_byte, e, hP.byte hq]
  refine congrArg (BitVec.setWidth 64) ?_
  simp only [Spec.Rc2.pi, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt hq]

theorem lo8_ext (b : BitVec 8) : (b.setWidth 64).setWidth 8 = b :=
  BitVec.setWidth_setWidth_of_le _ (by decide) |>.trans (BitVec.setWidth_eq b)

theorem copy_run (s : State) (hr : InRegions (s.rd ++ s.wr) (s.gpr .a0 + s.gpr .a5) 1)
    (hw : InRegions s.wr (s.gpr .a3 + s.gpr .a5) 1) :
    WP isa (.block copyKey) s fun t =>
      t.gpr .a5 = s.gpr .a5 + 1#64 ∧ t.gpr .a7 = s.gpr .a5 + 1#64 - s.gpr .a1 ∧
      t.mem = s.mem.writeW (s.gpr .a3 + s.gpr .a5) (s.mem (s.gpr .a0 + s.gpr .a5)) ∧
      Keep [.a7, .a5, .a6, .t2] s t := by
  refine WP.mono (WP.keep [.a7, .a5, .a6, .t2] (c := .block copyKey) (Q := fun t =>
      t.gpr .a5 = s.gpr .a5 + 1#64 ∧ t.gpr .a7 = s.gpr .a5 + 1#64 - s.gpr .a1 ∧
      t.mem = s.mem.writeW (s.gpr .a3 + s.gpr .a5) (s.mem (s.gpr .a0 + s.gpr .a5))) ?_
    (by rfl) rfl) fun t ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
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
abbrev keyTemps : List Reg := [.a7, .a5, .a6, .t0, .t1, .t2, .t3]

/-- The scan's environment: PITABLE at `W` in the working space at `a4`. -/
structure PiEnv (W : Addr) (s : State) : Prop where
  a4 : s.gpr .a4 = W
  al : W.toNat % 8 = 0
  rd : ∀ k < 32, InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (8 * k)) 8
  held : Proof.Rc2.PiHeld s.mem W

theorem PiEnv.keep {W : Addr} {s t : State} (E : PiEnv W s) {rs : List Reg} (k : Keep rs s t)
    (h7 : Reg.a4 ∉ rs) (hm : t.mem = s.mem) : PiEnv W t :=
  ⟨by rw [k.gpr h7]; exact E.a4, E.al, fun j hj => by rw [k.2.1, k.2.2]; exact E.rd j hj, by rw [hm]; exact E.held⟩

/-- A byte through the scan and into `L[i]`: the scan and `storeKey`. -/
theorem piStore_run (s : State) {W : Addr} (E : PiEnv W s) (hq : (s.gpr .t0).toNat < 256)
    (hw : InRegions s.wr (s.gpr .a3 + s.gpr .a5) 1) :
    WP isa (.seq piLookup (.block storeKey)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .a3 + s.gpr .a5) (Spec.Rc2.pi ((s.gpr .t0).setWidth 8)) ∧
      Keep [.a7, .t1, .t2, .t3, .a6] s t := by
  apply WP.seq
  refine WP.mono (piLookup_run s E.a4 E.al hq E.rd E.held) fun t₁ ⟨a₁, k₁, m₁⟩ => ?_
  have h6 : t₁.gpr .a3 = s.gpr .a3 := k₁.gpr (by decide)
  have h8 : t₁.gpr .a5 = s.gpr .a5 := k₁.gpr (by decide)
  refine WP.mono (WP.keep [.a6] (c := .block storeKey) (Q := fun t =>
      t.mem = t₁.mem.writeW (t₁.gpr .a3 + t₁.gpr .a5) ((t₁.gpr .t1).setWidth 8)) ?_
    (by rfl) rfl) fun t ⟨a, k⟩ =>
      ⟨by rw [a, a₁, m₁, h6, h8, lo8_ext], (k₁.trans k).mono (by simp)⟩
  unfold storeKey
  rrun [show InRegions t₁.wr (t₁.gpr .a3 + t₁.gpr .a5) 1 by rw [k₁.2.2, h6, h8]; exact hw]

theorem fill_run (s : State) {W : Addr} (E : PiEnv W s)
    (hlo : InRegions (s.rd ++ s.wr) (s.gpr .a3 + s.gpr .a5 - 1#64) 1)
    (hhi : InRegions (s.rd ++ s.wr) (s.gpr .a3 + (s.gpr .a5 - s.gpr .a1)) 1)
    (hw : InRegions s.wr (s.gpr .a3 + s.gpr .a5) 1) :
    WP isa fillKey s fun t =>
      t.gpr .a5 = s.gpr .a5 + 1#64 ∧ t.gpr .a7 = s.gpr .a5 + 1#64 - 128#64 ∧
      t.mem = s.mem.writeW (s.gpr .a3 + s.gpr .a5)
        (Spec.Rc2.pi (s.mem (s.gpr .a3 + s.gpr .a5 - 1#64) + s.mem (s.gpr .a3 + (s.gpr .a5 - s.gpr .a1)))) ∧
      Keep keyTemps s t := by
  unfold fillKey
  apply WP.seq
  refine WP.mono (WP.keep [.a6, .t0, .t1] (c := .block fillInput) (Q := fun t =>
      t.gpr .t0 = (s.mem (s.gpr .a3 + s.gpr .a5 - 1#64) + s.mem (s.gpr .a3 + (s.gpr .a5 - s.gpr .a1))).setWidth 64 ∧
      t.mem = s.mem) (by unfold fillInput mask; rrun [hlo, hhi, ext_add])
    (by rfl) rfl) fun t₁ ⟨⟨a₁, m₁⟩, k₁⟩ => ?_
  have h6 : t₁.gpr .a3 = s.gpr .a3 := k₁.gpr (by decide)
  have h8 : t₁.gpr .a5 = s.gpr .a5 := k₁.gpr (by decide)
  apply WP.seq
  refine WP.mono (piLookup_run t₁ (E.keep k₁ (by decide) m₁).a4 E.al (by rw [a₁]; exact ext_lt _)
    (E.keep k₁ (by decide) m₁).rd (E.keep k₁ (by decide) m₁).held) fun t₂ ⟨a₂, k₂, m₂⟩ => ?_
  have h6' : t₂.gpr .a3 = s.gpr .a3 := by rw [k₂.gpr (by decide), h6]
  have h8' : t₂.gpr .a5 = s.gpr .a5 := by rw [k₂.gpr (by decide), h8]
  refine WP.mono (WP.keep [.a7, .a5, .a6] (c := .block fillFinish) (Q := fun t =>
      t.gpr .a5 = t₂.gpr .a5 + 1#64 ∧ t.gpr .a7 = t₂.gpr .a5 + 1#64 - 128#64 ∧
      t.mem = t₂.mem.writeW (t₂.gpr .a3 + t₂.gpr .a5) ((t₂.gpr .t1).setWidth 8)) ?_
    (by rfl) rfl)
    fun t ⟨⟨a, b, c⟩, k⟩ => ⟨by rw [a, h8'], by rw [b, h8'], by rw [c, a₂, m₂, m₁, h6', h8', a₁, lo8_ext, lo8_ext],
      ((k₁.trans k₂).trans k).mono (by simp)⟩
  unfold fillFinish storeKey
  rrun [show InRegions t₂.wr (t₂.gpr .a3 + t₂.gpr .a5) 1 by rw [k₂.2.2, k₁.2.2, h6', h8']; exact hw]

theorem reduce_run (s : State) {W : Addr} (E : PiEnv W s) (hr : InRegions (s.rd ++ s.wr) (s.gpr .a3 + s.gpr .a5) 1)
    (hw : InRegions s.wr (s.gpr .a3 + s.gpr .a5) 1) :
    WP isa reduceKey s fun t =>
      t.mem = s.mem.writeW (s.gpr .a3 + s.gpr .a5)
        (Spec.Rc2.pi (s.mem (s.gpr .a3 + s.gpr .a5) &&& (s.gpr .t2).setWidth 8)) ∧
      Keep [.a7, .a6, .t0, .t1, .t2, .t3] s t := by
  unfold reduceKey
  apply WP.seq
  refine WP.mono (WP.keep [.a6, .t0] (c := .block reduceInput) (Q := fun t =>
      t.gpr .t0 = (s.mem (s.gpr .a3 + s.gpr .a5) &&& (s.gpr .t2).setWidth 8).setWidth 64 ∧
      t.mem = s.mem) (by unfold reduceInput; rrun [hr, ext_and])
    (by rfl) rfl) fun t₁ ⟨⟨a₁, m₁⟩, k₁⟩ => ?_
  have h6 : t₁.gpr .a3 = s.gpr .a3 := k₁.gpr (by decide)
  have h8 : t₁.gpr .a5 = s.gpr .a5 := k₁.gpr (by decide)
  refine WP.mono (piStore_run t₁ (E.keep k₁ (by decide) m₁) (by rw [a₁]; exact ext_lt _)
    (by rw [k₁.2.2, h6, h8]; exact hw)) fun t ⟨a, k⟩ =>
      ⟨by rw [a, m₁, h6, h8, a₁, lo8_ext], (k₁.trans k).mono (by simp)⟩

theorem descend_run (s : State) {W : Addr} (E : PiEnv W s)
    (hlo : InRegions (s.rd ++ s.wr) (s.gpr .a3 + (s.gpr .a5 - 1#64) + 1#64) 1)
    (hhi : InRegions (s.rd ++ s.wr) (s.gpr .a3 + (s.gpr .a5 - 1#64 + s.gpr .t4)) 1)
    (hw : InRegions s.wr (s.gpr .a3 + (s.gpr .a5 - 1#64)) 1) :
    WP isa descendKey s fun t =>
      t.gpr .a5 = s.gpr .a5 - 1#64 ∧
      t.mem = s.mem.writeW (s.gpr .a3 + (s.gpr .a5 - 1#64))
        (Spec.Rc2.pi (s.mem (s.gpr .a3 + (s.gpr .a5 - 1#64) + 1#64) ^^^
          s.mem (s.gpr .a3 + (s.gpr .a5 - 1#64 + s.gpr .t4)))) ∧
      Keep keyTemps s t := by
  unfold descendKey
  apply WP.seq
  refine WP.mono (WP.keep [.a5, .a6, .t0, .t1] (c := .block descendInput) (Q := fun t =>
      t.gpr .a5 = s.gpr .a5 - 1#64 ∧
      t.gpr .t0 = (s.mem (s.gpr .a3 + (s.gpr .a5 - 1#64) + 1#64) ^^^
        s.mem (s.gpr .a3 + (s.gpr .a5 - 1#64 + s.gpr .t4))).setWidth 64 ∧
      t.mem = s.mem) (by unfold descendInput; rrun [hlo, hhi, ext_xor])
    (by rfl) rfl) fun t₁ ⟨⟨i₁, a₁, m₁⟩, k₁⟩ => ?_
  have h6 : t₁.gpr .a3 = s.gpr .a3 := k₁.gpr (by decide)
  refine WP.mono (piStore_run t₁ (E.keep k₁ (by decide) m₁) (by rw [a₁]; exact ext_lt _)
    (by rw [k₁.2.2, h6, i₁]; exact hw)) fun t ⟨a, k⟩ =>
      ⟨by rw [k.gpr (by decide), i₁], by rw [a, m₁, h6, i₁, a₁, lo8_ext], (k₁.trans k).mono (by simp)⟩

end VG.Proof.Rc2.RISCV64
