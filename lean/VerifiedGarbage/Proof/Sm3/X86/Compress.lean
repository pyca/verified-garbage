module

public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Framework.X86.RegUpd
public import VerifiedGarbage.Proof.Sm3.Spec
public import VerifiedGarbage.Impl.Sm3.X86
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Sm3.X86.Contract
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm3.X86.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Spill
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Sm3.Spec
meta import VerifiedGarbage.Impl.Sm3.X86
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Sm3.X86.Contract
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Sm3.X86.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# SM3 compression function on x86 (32-bit): the message expansion and the iterations
-/

@[expose] public section

namespace VG.Proof.Sm3.X86

open VG VG.X86 VG.Impl.Sm3.X86
open VG.Spec.Sm3 (HashValue Word Block W p0 p1 ff gg)

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

/-! ## The registers and offsets of an iteration -/

theorem abx_add (k : Nat) : abx (k + 3) = abx k := by simp only [abx, Nat.add_mod_right]

theorem efy_add (k : Nat) : efy (k + 3) = efy k := by simp only [efy, Nat.add_mod_right]

/-- The registers follow each other: the new `A` and `E` are in the temporaries,
and the registers of `B` and `F` are the next temporaries. -/
theorem regs_succ (t : Nat) :
    ra (t + 1) = rx t ∧ rb (t + 1) = ra t ∧ re (t + 1) = ry t ∧ rf (t + 1) = re t := by
  simp only [ra, rb, rx, re, rf, ry, abx_add, efy_add, and_self]

/-- The registers of an iteration are six, and none is `esi` or `esp` (stated for
each pair in both orders, for rewriting). -/
theorem regs_ne (t : Nat) :
    [ra t, rb t, re t, rf t, rx t, ry t, .esi, .esp].Pairwise (· ≠ ·) ∧
    [.esp, .esi, ry t, rx t, rf t, re t, rb t, ra t].Pairwise (· ≠ ·) := by
  simp only [ra, rb, rx, re, rf, ry, abx, efy]
  rw [show (t + 1) % 3 = (t % 3 + 1) % 3 by omega_using [],
    show (t + 2) % 3 = (t % 3 + 2) % 3 by omega_using []]
  have := Nat.mod_lt t (show 3 > 0 by decide)
  generalize t % 3 = c at *
  revert this; revert c; decide

theorem cd_add (k : Nat) : cd (k + 2) = cd k := by simp only [cd, Nat.add_mod_right]

theorem cd_lt (k : Nat) : 64 ≤ cd k ∧ cd k + 4 ≤ 72 := by simp only [cd]; omega_using []

theorem gh_lt (k : Nat) : 72 ≤ gh k ∧ gh k + 4 ≤ 84 := by simp only [gh]; omega_using []

/-- `C`, `D`, `G`, `H` and the free word of an iteration are separate words of the scratch
buffer, after the window (stated for each pair in both orders, for rewriting). -/
theorem round_sep (t : Nat) :
    (∀ x ∈ [cd (t + 1), cd t, gh (t + 1), gh t, gh (t + 2)], 64 ≤ x ∧ x + 4 ≤ 112) ∧
    [cd (t + 1), cd t, gh (t + 1), gh t, gh (t + 2)].Pairwise (fun x y => x + 4 ≤ y ∨ y + 4 ≤ x) ∧
    [gh (t + 2), gh t, gh (t + 1), cd t, cd (t + 1)].Pairwise fun x y => x + 4 ≤ y ∨ y + 4 ≤ x := by
  simp only [cd, gh]
  rw [show (t + 1) % 2 = (t % 2 + 1) % 2 by omega_using [],
    show (t + 1) % 3 = (t % 3 + 1) % 3 by omega_using [],
    show (t + 2) % 3 = (t % 3 + 2) % 3 by omega_using []]
  have h2 := Nat.mod_lt t (show 2 > 0 by decide)
  have h3 := Nat.mod_lt t (show 3 > 0 by decide)
  generalize t % 2 = c at *
  generalize t % 3 = e at *
  revert h3; revert e; revert h2; revert c; decide

/-- The registers `v` of iteration `t`: `A`, `B`, `E`, `F` in registers, and `C`, `D`,
`G`, `H` in the scratch buffer `scr`. -/
def Vars (t : Nat) (scr : BitVec 32) (s : State) (v : HashValue) : Prop :=
  s.gpr (ra t) = v[0] ∧ s.gpr (rb t) = v[1] ∧
  s.mem.readW (addr scr (cd (t + 1))) 32 = v[2] ∧ s.mem.readW (addr scr (cd t)) 32 = v[3] ∧
  s.gpr (re t) = v[4] ∧ s.gpr (rf t) = v[5] ∧
  s.mem.readW (addr scr (gh (t + 1))) 32 = v[6] ∧ s.mem.readW (addr scr (gh t)) 32 = v[7]

/-- The scratch pointer and `esp`: never written by the iterations. -/
def pubRegs : List Reg := [.esi, .esp]

/-- Facts about the scratch buffer at `scr`, for a memory access `[scr + d]`. -/
structure Scratch (s : State) (scr : BitVec 32) : Prop where
  fits : scr.toNat + 112 ≤ 2 ^ 32
  rd : ∀ d, d + 4 ≤ 112 → InRegions (s.rd ++ s.wr) (addr scr d) 4
  wr : ∀ d, d + 4 ≤ 112 → InRegions s.wr (addr scr d) 4

theorem scr_sep {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) {d e : Nat} (hd : d + 4 ≤ 112)
    (he : e + 4 ≤ 112) (hde : d + 4 ≤ e ∨ e + 4 ≤ d) : Mem.Sep (addr scr e) 4 (addr scr d) 4 := by
  rw [addr_eq (by bdd_omega), addr_eq (by bdd_omega)]
  exact Offset.sep _ (by bdd_omega) (by bdd_omega) (by bdd_omega)

/-- Reading `[scr + e]` after writing `[scr + d]`. -/
theorem readW_writeW_scr {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) (m : Mem) (x : Word)
    {d e : Nat} (hd : d + 4 ≤ 112) (he : e + 4 ≤ 112) (hde : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (addr scr d) x).readW (addr scr e) 32 = m.readW (addr scr e) 32 :=
  Mem.readW_writeW_sep (scr_sep h hd he hde) (by decide)

theorem slot_lt (j : Nat) : slot j + 4 ≤ 64 := by simp only [slot]; omega_using []

/-! ## What an iteration computes -/

/-- Bit `i` of a rotated word. -/
theorem getLsbD_ror (x : Word) (r : Nat) {i : Nat} (hi : i < 32) :
    (x.rotateRight r).getLsbD i = x.getLsbD ((i + r) % 32) := by
  rw [BitVec.getLsbD_rotateRight]
  have := Nat.mod_lt r (show 32 > 0 by decide)
  split
  · exact congrArg x.getLsbD (by omega_arith)
  · rw [decide_eq_true hi, Bool.true_and]; exact congrArg x.getLsbD (by omega_arith)

/-- Two rotations right, as one by less than 32. -/
theorem ror_ror (x : Word) (a b c : Nat) (h : (a + b) % 32 = c % 32) :
    (x.rotateRight a).rotateRight b = x.rotateRight c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_ror _ _ hi, getLsbD_ror _ _ (Nat.mod_lt _ (by decide)), getLsbD_ror _ _ hi]
  exact congrArg x.getLsbD (by omega_using [h])

theorem ror_17_24 (x : Word) : (x.rotateRight 17).rotateRight 24 = x.rotateRight 9 :=
  ror_ror x _ _ _ (by decide)

theorem ror_23_24 (x : Word) : (x.rotateRight 23).rotateRight 24 = x.rotateRight 15 :=
  ror_ror x _ _ _ (by decide)

/-- `B` after `xor b, a` twice. -/
theorem xor_cancel (x y : Word) : x ^^^ y ^^^ y = x := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- `FF_j` for `16 ≤ j`, as the code computes it. -/
theorem maj_xor (x y z : Word) :
    x &&& y ||| x &&& z ||| y &&& z = (z ^^^ y) &&& (y ^^^ x) ^^^ y := by
  ext i; simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_xor]
  cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

/-- `FF_j`, as the code computes it. -/
def ffC (lo : Bool) (a b c : Word) : Word :=
  if lo then a ^^^ b ^^^ c else (c ^^^ b) &&& (b ^^^ a) ^^^ b

/-- `GG_j`, as the code computes it. -/
def ggC (lo : Bool) (e f g : Word) : Word :=
  if lo then f ^^^ g ^^^ e else (f ^^^ g) &&& e ^^^ g

/-- `SS1`, as the code computes it. -/
def ss1C (T a e : Word) : Word := (a.rotateRight 20 + T + e).rotateRight 25

/-- `TT1`, as the code computes it. -/
def tt1C (lo : Bool) (T : Word) (v : HashValue) (w w₄ : Word) : Word :=
  (w ^^^ w₄) + v[3] + ffC lo v[0] v[1] v[2] + (v[0].rotateRight 20 ^^^ ss1C T v[0] v[4])

/-- `TT2`, as the code computes it. -/
def tt2C (lo : Bool) (T : Word) (v : HashValue) (w : Word) : Word :=
  ss1C T v[0] v[4] + (v[7] + w) + ggC lo v[4] v[5] v[6]

/-- `P_0`, as the code computes it. -/
def p0C (x : Word) : Word := x ^^^ x.rotateRight 23 ^^^ (x.rotateRight 23).rotateRight 24

theorem tt1C_eq (t : Nat) (v : HashValue) (w w₄ : Word) :
    tt1C (decide (t < 16)) (tj t) v w w₄ = (roundW v t w w₄)[0] := by
  rw [roundW_0, tt1C, ss1C, ffC, tj, Spec.Sm3.ff, rotl12, rotl7]
  generalize v[0] = a; generalize v[1] = b; generalize v[2] = c; generalize v[3] = d
  generalize v[4] = e
  by_cases ht : t < 16
  · simp only [ht, decide_true, ↓reduceIte]
    simp only [ac]
  · simp only [ht, decide_false, ↓reduceIte, Bool.false_eq_true, maj_xor]
    simp only [ac]

theorem p0C_eq (t : Nat) (v : HashValue) (w w₄ : Word) :
    p0C (tt2C (decide (t < 16)) (tj t) v w) = (roundW v t w w₄)[4] := by
  rw [roundW_4, p0C, ror_23_24, Spec.Sm3.p0, rotl9, rotl17]
  obtain e : tt2C (decide (t < 16)) (tj t) v w =
      gg t v[4] v[5] v[6] + v[7] +
        (v[0].rotateLeft 12 + v[4] + (Spec.Sm3.T t).rotateLeft (t % 32)).rotateLeft 7 + w := by
    rw [tt2C, ss1C, ggC, tj, Spec.Sm3.gg, rotl12, rotl7]
    generalize v[0] = a; generalize v[4] = b; generalize v[5] = c; generalize v[6] = d
    generalize v[7] = e
    by_cases ht : t < 16
    · simp only [ht, decide_true, ↓reduceIte]
      simp only [ac]
    · simp only [ht, decide_false, ↓reduceIte, Bool.false_eq_true, ch_eq]
      simp only [ac]
  rw [e]

/-- The symbolic execution of an iteration, of either shape, for any registers `a … y` and
offsets `c … n` of the registers (which `regs_ne` and `round_sep` say are different registers
and separate words). -/
theorem roundAt_ok (lo : Bool) (T : BitVec 32) (wo wo₄ : Nat) (a b e f x y : Reg) (c d g h n : Nat)
    (s : State) (v : HashValue) (w w₄ : Word) (scr : BitVec 32) (hS : Scratch s scr)
    (hreg : [a, b, e, f, x, y, .esi, .esp].Pairwise (· ≠ ·) ∧
      [.esp, .esi, y, x, f, e, b, a].Pairwise (· ≠ ·))
    (hsep : (∀ o ∈ [c, d, g, h, n], 64 ≤ o ∧ o + 4 ≤ 112) ∧
      [c, d, g, h, n].Pairwise (fun p q => p + 4 ≤ q ∨ q + 4 ≤ p) ∧
      [n, h, g, d, c].Pairwise fun p q => p + 4 ≤ q ∨ q + 4 ≤ p)
    (hwo : wo + 4 ≤ 64) (hwo₄ : wo₄ + 4 ≤ 64) (hesi : s.gpr .esi = scr)
    (ha : s.gpr a = v[0]) (hb : s.gpr b = v[1]) (hc : s.mem.readW (addr scr c) 32 = v[2])
    (hd : s.mem.readW (addr scr d) 32 = v[3]) (he : s.gpr e = v[4]) (hf : s.gpr f = v[5])
    (hg : s.mem.readW (addr scr g) 32 = v[6]) (hh : s.mem.readW (addr scr h) 32 = v[7])
    (hw : s.mem.readW (addr scr wo) 32 = w) (hw₄ : s.mem.readW (addr scr wo₄) 32 = w₄) :
    WP isa (.block (roundAt lo T wo wo₄ a b e f x y c d g h n)) s fun s' =>
      s'.gpr x = tt1C lo T v w w₄ ∧ s'.gpr a = v[0] ∧
      s'.gpr y = p0C (tt2C lo T v w) ∧ s'.gpr e = v[4] ∧
      s'.mem = (s.mem.writeW (addr scr d) (v[1].rotateRight 23)).writeW (addr scr n)
        (v[5].rotateRight 13) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp := by
  obtain hin := hS.rd; have hout := hS.wr
  obtain hrw := readW_writeW_scr hS.fits
  obtain hiw₄ : InRegions (s.rd ++ s.wr) (addr scr wo₄) 4 := hin wo₄ (by bdd_omega)
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, false_implies, implies_true, List.Pairwise.nil, and_true, or_false,
    forall_eq, ne_eq] at hreg hsep
  obtain ⟨⟨⟨hc1, hc2⟩, ⟨hd1, hd2⟩, ⟨hg1, hg2⟩, ⟨hh1, hh2⟩, hn1, hn2⟩, hsep⟩ := hsep
  obtain hwd : d + 4 ≤ wo ∨ wo + 4 ≤ d := .inr (by bdd_omega)
  obtain hwn : n + 4 ≤ wo ∨ wo + 4 ≤ n := .inr (by bdd_omega)
  obtain hwl : wo + 4 ≤ 112 := by bdd_omega
  apply WP.of_runBlock
  cases lo <;>
  simp only
    [Impl.Sm3.X86.roundAt, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append,
    tt1C, tt2C, p0C, ss1C, ffC, ggC, xor_cancel,
    hreg, hsep, hc2, hd2, hg2, hh2, hn2, hwd, hwn, hwl,
    runBlock_cons, runBlock_nil, runStep_some, exec, execAlu, execShift, readSrc, ea_at, sc,
    RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags,
    RegUpd.wr_setFlags, Nat.reduceLeDiff, Nat.reduceEqDiff, and_self, not_false_eq_true,
    State.load32, State.store32,
    hesi, hin, hout, hiw₄, hrw, ha, hb, hc, hd, he, hf, hg, hh, hw,
    hw₄, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']

/-- An iteration: the registers of the next one, and what it wrote. -/
theorem round_ok (t : Nat) (s : State) (v : HashValue) (w w₄ : Word) (scr : BitVec 32)
    (hS : Scratch s scr) (hv : Vars t scr s v) (hesi : s.gpr .esi = scr)
    (hw : s.mem.readW (addr scr (slot t)) 32 = w) (hw₄ : s.mem.readW (addr scr (slot (t + 4))) 32 = w₄) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) scr s' (roundW v t w w₄) ∧
      s'.mem = (s.mem.writeW (addr scr (cd t)) (v[1].rotateRight 23)).writeW (addr scr (gh (t + 2)))
        (v[5].rotateRight 13) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  obtain hsep := round_sep t
  refine WP.mono (roundAt_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s v w w₄ scr hS (regs_ne t) hsep
    (slot_lt t) (slot_lt (t + 4)) hesi h0 h1 h2 h3 h4 h5 h6 h7 hw hw₄)
    fun s' ⟨hx, ha, hy, he, hm, hrd, hwr, hsi, hsp⟩ => ?_
  obtain ⟨e0, e1, e4, e5⟩ := regs_succ t
  obtain hrw := readW_writeW_scr hS.fits
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, false_implies, implies_true, List.Pairwise.nil, and_true, or_false,
    forall_eq] at hsep
  obtain ⟨⟨⟨hc1, hc2⟩, ⟨hd1, hd2⟩, ⟨hg1, hg2⟩, ⟨hh1, hh2⟩, hn1, hn2⟩, hs₁, hs₂⟩ := hsep
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hm, hrd, hwr, fun r hr => ?_⟩
  · rw [e0, hx, tt1C_eq]
  · rw [e1, ha, roundW_1]
  · rw [show t + 1 + 1 = t + 2 from rfl, cd_add, hm, hrw _ _ hn2 hd2 (by bdd_omega),
      Mem.readW_writeW_self32, roundW_2, rotl9]
  · rw [hm, hrw _ _ hn2 hc2 (by bdd_omega), hrw _ _ hd2 hc2 (by bdd_omega), h2, roundW_3]
  · rw [e4, hy, p0C_eq]
  · rw [e5, he, roundW_5]
  · rw [show t + 1 + 1 = t + 2 from rfl, hm, Mem.readW_writeW_self32, roundW_6, rotl19]
  · rw [hm, hrw _ _ hn2 hg2 (by bdd_omega), hrw _ _ hd2 hg2 (by bdd_omega), h6, roundW_7]
  · simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hsi
    · exact hsp

/-- `W_i` for `16 ≤ i`, from the 16 words before it in the window, with any two
temporaries. -/
theorem expand_ok (x y : Reg) (i : Nat) (s : State) (M : Block) (scr : BitVec 32)
    (hS : Scratch s scr) (hxy : ¬x = y ∧ ¬y = x ∧ ¬x = .esi ∧ ¬y = .esi ∧ ¬Reg.esi = x ∧ ¬Reg.esi = y)
    (hesi : s.gpr .esi = scr) (hi : 16 ≤ i)
    (hwin : ∀ j, j < i → i ≤ j + 16 → s.mem.readW (addr scr (slot j)) 32 = W M j) :
    WP isa (.block (expand x y i)) s fun s' =>
      s'.mem = s.mem.writeW (addr scr (slot i)) (W M i) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r, ¬r = x → ¬r = y → s'.gpr r = s.gpr r := by
  obtain hin : ∀ j, InRegions (s.rd ++ s.wr) (addr scr (slot j)) 4 :=
    fun j => hS.rd _ (by have := slot_lt j; omega_using [this])
  obtain hout : ∀ j, InRegions s.wr (addr scr (slot j)) 4 :=
    fun j => hS.wr _ (by have := slot_lt j; omega_using [this])
  obtain ⟨x1, x2, -, -, x5, x6⟩ := hxy
  obtain e16 := hwin (i - 16) (by bdd_omega) (by bdd_omega)
  obtain e9 := hwin (i - 9) (by bdd_omega) (by bdd_omega)
  obtain e3 := hwin (i - 3) (by bdd_omega) (by bdd_omega)
  obtain e13 := hwin (i - 13) (by bdd_omega) (by bdd_omega)
  obtain e6 := hwin (i - 6) (by bdd_omega) (by bdd_omega)
  rw [show slot (i - 16) = slot i by simp only [slot]; omega_using [hi]] at e16
  rw [show slot (i - 9) = slot (i + 7) by simp only [slot]; omega_using [hi]] at e9
  rw [show slot (i - 3) = slot (i + 13) by simp only [slot]; omega_using [hi]] at e3
  rw [show slot (i - 13) = slot (i + 3) by simp only [slot]; omega_using [hi]] at e13
  rw [show slot (i - 6) = slot (i + 10) by simp only [slot]; omega_using [hi]] at e6
  obtain hW := W_ge M (j := i) hi
  rw [Spec.Sm3.p1, rotl15 (W M (i - 3)), rotl7, rotl15, rotl23] at hW
  apply WP.of_runBlock
  simp only [Impl.Sm3.X86.expand, sc, runBlock_cons, runBlock_nil, runStep_some, exec, execAlu,
    execShift, readSrc, ea_at, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg,
    RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags,
    RegUpd.wr_setFlags, Nat.reduceLeDiff, Nat.reduceEqDiff, and_self,
    not_false_eq_true, State.load32, State.store32, hesi, hin, hout,
    x1, x2, x5, x6, ror_17_24,
    ite_true, ite_false, e16, e9, e3, e13, e6, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨by rw [hW], trivial, trivial, fun r hx hy => ?_⟩
  simp only [RegUpd.gpr_setReg_of_ne, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hx, hy,
    not_false_eq_true]

/-! ## The 64 iterations -/

/-- The part of the scratch buffer a block's code writes: the window, the registers, and
the block pointer and the count. -/
abbrev workRegion (scr : BitVec 32) : Region := ⟨scr.setWidth 64, 96⟩

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem work_contains {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) {d : Nat} (hd : d + 4 ≤ 96) :
    (workRegion scr).Contains (addr scr d) (32 / 8) := by
  rw [addr_eq (by bdd_omega)]; exact contains_offset hd (by bdd_omega)

theorem Scratch.congr {s s' : State} {scr : BitVec 32} (h : Scratch s scr) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Scratch s' scr :=
  ⟨h.fits, by rw [hrd, hwr]; exact h.rd, by rw [hwr]; exact h.wr⟩

/-- The number of words of the message expansion computed before iteration `t`: those of
the block, then `W_{j+7}` in each iteration `9 ≤ j ≤ 60`. -/
def nw (t : Nat) : Nat := if t < 10 then 16 else if t < 62 then t + 7 else 68

theorem nw_ahead {t : Nat} (h : 9 ≤ t ∧ t ≤ 60) : nw t = t + 7 ∧ nw (t + 1) = t + 7 + 1 := by
  simp only [nw]; (repeat' split) <;> omega

theorem nw_rest {t : Nat} (h : ¬(9 ≤ t ∧ t ≤ 60)) : nw (t + 1) = nw t := by
  simp only [nw]; (repeat' split) <;> omega

theorem nw_bounds (t : Nat) (ht : t < 64) : t + 4 < nw (t + 1) ∧ nw (t + 1) ≤ t + 16 := by
  simp only [nw]; (repeat' split) <;> omega

/-- What holds during the iterations, relative to the state `sB` at their
start: the registers `V` are those of iteration `t`, the window holds
`W_j` for the 16 words `j` before `i`, and the rest of the scratch buffer is as it was. -/
structure Inv (V : HashValue) (M : Block) (scr : BitVec 32) (sB : State) (t i : Nat) (s : State) :
    Prop where
  vars : Vars t scr s V
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame [workRegion scr] sB.mem s.mem
  win : ∀ j < i, i ≤ j + 16 → s.mem.readW (addr scr (slot j)) 32 = W M j
  keep : ∀ d, 84 ≤ d → d + 4 ≤ 112 → s.mem.readW (addr scr d) 32 = sB.mem.readW (addr scr d) 32

/-- Before iteration `t`. -/
abbrev RInv (H : HashValue) (M : Block) (scr : BitVec 32) (sB : State) (t : Nat) : State → Prop :=
  Inv (Spec.Sm3.rounds H M t) M scr sB t (nw t)

section
variable {H : HashValue} {M : Block} {scr : BitVec 32} {sB : State}
  (hS : Scratch sB scr) (hesi : sB.gpr .esi = scr)
include hS hesi

theorem expand_inv {V : HashValue} {t i : Nat} {s : State} (hs : Inv V M scr sB t i s)
    (hi : 16 ≤ i) : WP isa (.block (expand (rx t) (ry t) i)) s (Inv V M scr sB t (i + 1)) := by
  have hfits := hS.fits
  obtain hreg := regs_ne t
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, false_implies, implies_true, List.Pairwise.nil, and_true, or_false,
    forall_eq, ne_eq] at hreg
  refine WP.mono (expand_ok (rx t) (ry t) i s M scr (hS.congr hs.rd hs.wr)
    (by simp only [hreg, not_false_eq_true, and_self])
    ((hs.pub .esi (by decide)).trans hesi) hi (fun _ => hs.win _)) fun s₁ ⟨hm₁, hrd₁, hwr₁, hr₁⟩ => ?_
  obtain hslot := slot_lt i
  obtain rw₁ : ∀ d, 64 ≤ d → d + 4 ≤ 112 →
      s₁.mem.readW (addr scr d) 32 = s.mem.readW (addr scr d) 32 := fun d h1 h2 => by
    rw [hm₁, readW_writeW_scr hfits _ _ (by bdd_omega) h2 (.inl (by bdd_omega))]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hs.vars
  obtain c1 := cd_lt (t + 1); have c0 := cd_lt t
  obtain g1 := gh_lt (t + 1); have g0 := gh_lt t
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun r hr => ?_, by rw [hrd₁, hs.rd],
    by rw [hwr₁, hs.wr], ?_, ?_, fun d h1 h2 => by rw [rw₁ d (by bdd_omega) h2, hs.keep d h1 h2]⟩
  · rw [hr₁ _ (by simp only [hreg, not_false_eq_true]) (by simp only [hreg, not_false_eq_true]), h0]
  · rw [hr₁ _ (by simp only [hreg, not_false_eq_true]) (by simp only [hreg, not_false_eq_true]), h1]
  · rw [rw₁ _ (by bdd_omega) (by bdd_omega), h2]
  · rw [rw₁ _ (by bdd_omega) (by bdd_omega), h3]
  · rw [hr₁ _ (by simp only [hreg, not_false_eq_true]) (by simp only [hreg, not_false_eq_true]), h4]
  · rw [hr₁ _ (by simp only [hreg, not_false_eq_true]) (by simp only [hreg, not_false_eq_true]), h5]
  · rw [rw₁ _ (by bdd_omega) (by bdd_omega), h6]
  · rw [rw₁ _ (by bdd_omega) (by bdd_omega), h7]
  · simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hr₁ _ (by simp only [hreg, not_false_eq_true]) (by simp only [hreg, not_false_eq_true]),
        hs.pub _ (by decide)]
    · rw [hr₁ _ (by simp only [hreg, not_false_eq_true]) (by simp only [hreg, not_false_eq_true]),
        hs.pub _ (by decide)]
  · rw [hm₁]
    exact hs.frame.writeW (List.mem_singleton_self _) _ (work_contains hfits (by bdd_omega))
  · intro j hj hj'
    obtain hsj := slot_lt j
    rw [hm₁]
    by_cases hji : j = i
    · subst hji; exact Mem.readW_writeW_self32 _ _ _
    · rw [readW_writeW_scr hfits _ _ (by bdd_omega) (by bdd_omega) ?_]
      · exact hs.win j (by bdd_omega) (by bdd_omega)
      · simp only [slot] at hsj hslot ⊢; omega_using [hj, hj', hji]

theorem rounds_ok (h0 : Vars 0 scr sB H)
    (hwin : ∀ j < 16, sB.mem.readW (addr scr (slot j)) 32 = W M j) :
    ∀ t ≤ 64, WP isa (rounds t) sB (RInv H M scr sB t) := by
  have hfits := hS.fits
  intro t ht
  induction t with
  | zero =>
    exact WP.block_nil (M := isa)
      ⟨h0, fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun j hj _ => hwin j hj, fun _ _ _ => rfl⟩
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by bdd_omega)) fun s hs => ?_)
    obtain ⟨hb1, hb2⟩ := nw_bounds t (by bdd_omega)
    -- the message expansion, if any
    obtain h₁ : WP isa (.block (ahead t)) s (Inv (Spec.Sm3.rounds H M t) M scr sB t (nw (t + 1))) := by
      by_cases ha : 9 ≤ t ∧ t ≤ 60
      · obtain ⟨e1, e2⟩ := nw_ahead ha
        rw [ahead, ite_eq_left_of_eq_true _ _ (eq_true ha), e2]
        exact expand_inv hS hesi (e1 ▸ hs) (by bdd_omega)
      · rw [ahead, ite_eq_right_of_eq_false _ _ (eq_false ha), nw_rest ha]
        exact WP.block_nil (M := isa) hs
    rw [WP.block_append_iff]
    refine WP.mono h₁ fun s₁ h₁ => ?_
    obtain hesi₁ : s₁.gpr .esi = scr := (h₁.pub .esi (by decide)).trans hesi
    refine WP.mono (round_ok t s₁ _ (W M t) (W M (t + 4)) scr (hS.congr h₁.rd h₁.wr) h₁.vars hesi₁
      (h₁.win t (by bdd_omega) (by bdd_omega)) (h₁.win (t + 4) (by bdd_omega) (by bdd_omega)))
      fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hr₂⟩ => ?_
    obtain c0 := cd_lt t
    obtain g2 := gh_lt (t + 2)
    obtain rw₂ : ∀ d, d + 4 ≤ 64 ∨ 84 ≤ d → d + 4 ≤ 112 →
        s₂.mem.readW (addr scr d) 32 = s₁.mem.readW (addr scr d) 32 := fun d h1 h2 => by
      rw [hm₂, readW_writeW_scr hfits _ _ (by bdd_omega) h2 (by bdd_omega),
        readW_writeW_scr hfits _ _ (by bdd_omega) h2 (by bdd_omega)]
    refine ⟨?_, fun r hr => by rw [hr₂ r hr, h₁.pub r hr], by rw [hrd₂, h₁.rd],
      by rw [hwr₂, h₁.wr], ?_, fun j hj hj' => ?_,
      fun d h1 h2 => by rw [rw₂ d (.inr h1) h2, h₁.keep d h1 h2]⟩
    · rw [rounds_succ, round_eq]; exact hv₂
    · rw [hm₂]
      exact ((h₁.frame.writeW (List.mem_singleton_self _) _ (work_contains hfits (by bdd_omega))).writeW
        (List.mem_singleton_self _) _ (work_contains hfits (by bdd_omega)))
    · have hsj := slot_lt j
      rw [rw₂ _ (.inl hsj) (by bdd_omega)]
      exact h₁.win j hj hj'

end

end VG.Proof.Sm3.X86

/-!
# SM3 compression function on x86 (32-bit): the whole function
-/

namespace VG.Proof.Sm3.X86

open VG VG.X86 VG.Impl.Sm3.X86
open VG.Spec.Sm3 (HashValue Word Block W stateAt blockAt compressBlocks compress parseBlock)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev bp : BitVec 32 := arg s₀ 1
abbrev nb : Nat := (arg s₀ 2).toNat
abbrev scr : BitVec 32 := arg s₀ 3
abbrev stR : Region := ⟨(st s₀).setWidth 64, 32⟩
abbrev blR : Region := ⟨(bp s₀).setWidth 64, 64 * nb s₀⟩
abbrev scrR : Region := ⟨(scr s₀).setWidth 64, 112⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
abbrev H₀ : HashValue := stateAt s₀.mem ((st s₀).setWidth 64)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : BitVec 32 := bp s₀ + BitVec.ofNat 32 (64 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem ((bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i))

/-- The address of word `k` of the hash value. -/
abbrev stAddr (k : Nat) : Addr := addr (st s₀) (4 * k)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀, argR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)
  arg_st : (argR s₀).Disjoint (stR s₀)
  arg_scr : (argR s₀).Disjoint (scrR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)
  st_fits : (st s₀).toNat + 32 ≤ 2 ^ 32
  blk_fits : (bp s₀).toNat + 64 * nb s₀ ≤ 2 ^ 32
  scr_fits : (scr s₀).toNat + 112 ≤ 2 ^ 32
  esp_fits : (esp₀ s₀).toNat + 20 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.Sm3.compressX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem contains_sub {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64)
    {a : Addr} (ha : a = base + BitVec.ofNat 64 off) : (⟨base, len⟩ : Region).Contains a n := by
  subst ha; exact contains_offset h ho

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem stAddr_eq {k : Nat} (hk : k < 8) :
    stAddr s₀ k = (st s₀).setWidth 64 + BitVec.ofNat 64 (4 * k) :=
  addr_eq (by have := h.st_fits; omega_using [hk, this])

theorem argAddr_eq {d : Nat} (hd : d < 20) :
    addr (esp₀ s₀) d = (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := h.esp_fits; omega_using [hd, this])

theorem blkAddr_eq {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    addr (blkAddr s₀ i) (4 * t) =
      (bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 (4 * t) := by
  have := h.blk_fits
  rw [addr_eq (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := (bp s₀).isLt; omega_arith)]
  obtain e : (blkAddr s₀ i).setWidth 64 = (bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i) := by
    have := addr_eq (x := bp s₀) (k := 64 * i) (by bdd_omega)
    simpa only [addr] using this
  rw [e]

theorem scr_eq {d : Nat} (hd : d < 112) :
    addr (scr s₀) d = (scr s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := h.scr_fits; omega_using [hd, this])

theorem scratch : Scratch s₀ (scr s₀) :=
  ⟨h.scr_fits, fun d hd => ⟨scrR s₀, by simp [h.wr], contains_sub hd (by bdd_omega) (h.scr_eq (by bdd_omega))⟩,
    fun d hd => ⟨scrR s₀, by simp [h.wr], contains_sub hd (by bdd_omega) (h.scr_eq (by bdd_omega))⟩⟩

theorem arg_contains {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 20) :
    (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  simp only [Region.Contains, argAddr]
  rw [show (esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (esp₀ s₀) 4 from rfl,
    h.argAddr_eq (by bdd_omega), h.argAddr_eq (by bdd_omega)]
  have := h.esp_fits
  rw [Offset.add_sub_add _ hd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by bdd_omega)]
  omega_using [hd']

theorem in_arg {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 20) :
    InRegions (s₀.rd ++ s₀.wr) (addr (esp₀ s₀) d) 4 :=
  ⟨argR s₀, by simp [h.rd], h.arg_contains hd hd'⟩

/-- An argument slot is inside the argument region. -/
theorem arg_sub {i : Nat} (hi : i < 4) : Region.Sub ⟨argAddr s₀ i, 4⟩ (argR s₀) := by
  simp only [argR, argAddr]
  rw [show (esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (esp₀ s₀) 4 from rfl,
    h.argAddr_eq (by bdd_omega),
    show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (esp₀ s₀) (4 + 4 * i)
    from rfl, h.argAddr_eq (by bdd_omega)]
  exact Offset.sub _ (by bdd_omega) (by bdd_omega)

/-- The arguments are unchanged while only the state and the scratch buffer are written. -/
theorem arg_frame {m : Mem} (hf : Frame [stR s₀, scrR s₀] s₀.mem m) {i : Nat} (hi : i < 4) :
    m.readW (addr (esp₀ s₀) (4 + 4 * i)) 32 = arg s₀ i := by
  refine (hf.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) ?_ (by decide))
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨h.arg_st.sub_left (h.arg_sub hi), h.arg_scr.sub_left (h.arg_sub hi)⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (addr (blkAddr s₀ i) (4 * t)) 4 := by
  have := h.blk_fits
  rw [h.blkAddr_eq hi ht, show (bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 (4 * t) =
    (bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i + 4 * t) from Offset.add_add _ _ _]
  exact contains_offset (by bdd_omega) (by bdd_omega)

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (addr (blkAddr s₀ i) (4 * t)) 4 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

theorem st_sep {s₀ : State} (hp : Pre s₀) {d e : Nat} (hd : d + 4 ≤ 32) (he : e + 4 ≤ 32)
    (hde : d + 4 ≤ e ∨ e + 4 ≤ d) : Mem.Sep (addr (st s₀) d) 4 (addr (st s₀) e) 4 := by
  rw [addr_eq (by have := hp.st_fits; omega_using [hd, this]), addr_eq (by have := hp.st_fits; omega_using [he, this])]
  exact Offset.sep _ hde (by bdd_omega) (by bdd_omega)

/-- Reading the hash value at offset `d` after writing it at offset `e`. -/
theorem readW_writeW_st {s₀ : State} (hp : Pre s₀) (m : Mem) (v : Word) {d e : Nat}
    (hd : d + 4 ≤ 32) (he : e + 4 ≤ 32) (hde : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (addr (st s₀) e) v).readW (addr (st s₀) d) 32 = m.readW (addr (st s₀) d) 32 :=
  Mem.readW_writeW_sep (st_sep hp hd he hde) (by decide)

theorem st_eq {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : d < 32) :
    addr (st s₀) d = (st s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.st_fits; omega_using [hd, this])

theorem st_scr_sep {s₀ : State} (hp : Pre s₀) {e d : Nat} (he : e + 4 ≤ 32) (hd : d + 4 ≤ 112) :
    Mem.Sep (addr (st s₀) e) 4 (addr (scr s₀) d) 4 :=
  hp.st_scr.sep (contains_sub he (by bdd_omega) (st_eq hp (by bdd_omega)))
    (contains_sub hd (by bdd_omega) (hp.scr_eq (by bdd_omega)))

/-- Reading the hash value after writing the scratch buffer. -/
theorem readW_writeW_scr_st {s₀ : State} (hp : Pre s₀) (m : Mem) (v : Word) {e d : Nat}
    (he : e + 4 ≤ 32) (hd : d + 4 ≤ 112) :
    (m.writeW (addr (scr s₀) d) v).readW (addr (st s₀) e) 32 = m.readW (addr (st s₀) e) 32 :=
  Mem.readW_writeW_sep (st_scr_sep hp he hd) (by decide)

/-- Reading the scratch buffer after writing the hash value. -/
theorem readW_writeW_st_scr {s₀ : State} (hp : Pre s₀) (m : Mem) (v : Word) {e d : Nat}
    (he : e + 4 ≤ 32) (hd : d + 4 ≤ 112) :
    (m.writeW (addr (st s₀) e) v).readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 :=
  Mem.readW_writeW_sep (fun x h₁ h₂ => st_scr_sep hp he hd x h₂ h₁) (by decide)

theorem in_st {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : d + 4 ≤ 32) :
    InRegions (s₀.rd ++ s₀.wr) (addr (st s₀) d) 4 :=
  ⟨stR s₀, by simp [hp.wr], contains_sub hd (by bdd_omega) (st_eq hp (by bdd_omega))⟩

theorem out_st {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : d + 4 ≤ 32) :
    InRegions s₀.wr (addr (st s₀) d) 4 :=
  ⟨stR s₀, by simp [hp.wr], contains_sub hd (by bdd_omega) (st_eq hp (by bdd_omega))⟩

theorem stateAt_eq {m : Mem} {s₀ : State} (hp : Pre s₀) {v : HashValue}
    (h : ∀ k : Nat, (hk : k < 8) → m.readW (stAddr s₀ k) 32 = v[k]) :
    stateAt m ((st s₀).setWidth 64) = v := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  rw [← hp.stAddr_eq hk]; exact h k hk

theorem stateAt_get {s₀ : State} (hp : Pre s₀) (m : Mem) {k : Nat} (hk : k < 8) :
    (stateAt m ((st s₀).setWidth 64))[k] = m.readW (stAddr s₀ k) 32 := by
  simp only [stateAt, Vector.getElem_ofFn, hp.stAddr_eq hk]

/-! ## The loop invariant -/

/-- The callee-saved registers and their slots in the scratch buffer. -/
def compressSaved : Spill.Slots := [(.ebx, 96), (.esi, 100), (.edi, 104), (.ebp, 108)]

theorem compressSaved_fits : Spill.Fits 112 compressSaved := by decide

/-- The callee-saved registers are saved in the scratch buffer. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (addr (scr s₀)) s₀.gpr compressSaved

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  esi : s.gpr .esi = scr s₀
  esp : s.gpr .esp = esp₀ s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt s.mem ((st s₀).setWidth 64) =
    compressBlocks (H₀ s₀) s₀.mem ((bp s₀).setWidth 64) i
  saved : Saved s₀ s.mem

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  edi : s.gpr .edi = blkAddr s₀ i
  ebp : s.gpr .ebp = BitVec.ofNat 32 (nb s₀ - i)

/-! ## One block -/

/-- The registers at the start of the iterations. -/
theorem vars0 (scr : BitVec 32) (s : State) (v : HashValue) : Vars 0 scr s v ↔
    s.gpr .eax = v[0] ∧ s.gpr .ebx = v[1] ∧
    s.mem.readW (addr scr 68) 32 = v[2] ∧ s.mem.readW (addr scr 64) 32 = v[3] ∧
    s.gpr .ecx = v[4] ∧ s.gpr .edx = v[5] ∧
    s.mem.readW (addr scr 76) 32 = v[6] ∧ s.mem.readW (addr scr 72) 32 = v[7] := Iff.rfl

/-- The registers after the 64 iterations. -/
theorem vars64 (scr : BitVec 32) (s : State) (v : HashValue) : Vars 64 scr s v ↔
    s.gpr .ebp = v[0] ∧ s.gpr .eax = v[1] ∧
    s.mem.readW (addr scr 68) 32 = v[2] ∧ s.mem.readW (addr scr 64) 32 = v[3] ∧
    s.gpr .edi = v[4] ∧ s.gpr .ecx = v[5] ∧
    s.mem.readW (addr scr 80) 32 = v[6] ∧ s.mem.readW (addr scr 76) 32 = v[7] := Iff.rfl

/-- Words `0 … j-1` of the copy. -/
def copyTo (j : Nat) : List Instr := (List.range j).flatMap copyWord

theorem copyTo_succ (j : Nat) : copyTo (j + 1) = copyTo j ++ copyWord j := by
  simp [copyTo, List.range_succ, List.flatMap_append]

theorem copyWord_ok (i : Nat) {s : State} {p q : BitVec 32} (hedi : s.gpr .edi = p)
    (hesi : s.gpr .esi = q) (hi : InRegions (s.rd ++ s.wr) (addr p (4 * i)) 4)
    (ho : InRegions s.wr (addr q (slot i)) 4) :
    WP isa (.block (copyWord i)) s fun s' =>
      s'.mem = s.mem.writeW (addr q (slot i)) (bswap (s.mem.readW (addr p (4 * i)) 32)) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [copyWord, runBlock_cons, runBlock_nil, runStep_some, exec, readSrc,
    ea_at, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, not_false_eq_true, reduceCtorEq,
    State.load32, State.store32, hedi, hesi, hi, ho, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => by simp only [RegUpd.gpr_setReg_of_ne, hr, not_false_eq_true],
    trivial, trivial⟩

theorem copyTo_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hedi : s.gpr .edi = blkAddr s₀ i) (hesi : s.gpr .esi = scr s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr)
    (hblk : ∀ m, Frame [workRegion (scr s₀)] s.mem m → ∀ t : Nat, t < 16 →
      bswap (m.readW (addr (blkAddr s₀ i) (4 * t)) 32) = W (blk s₀ i) t) :
    ∀ j ≤ 16, WP isa (.block (copyTo j)) s fun s' =>
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [workRegion (scr s₀)] s.mem s'.mem ∧
      ∀ t < j, s'.mem.readW (addr (scr s₀) (slot t)) 32 = W (blk s₀ i) t
  | 0, _ => WP.block_nil (M := isa)
      ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun t ht => absurd ht (by bdd_omega)⟩
  | j + 1, hj => by
    have hfits := hp.scr_fits
    rw [copyTo_succ, WP.block_append_iff]
    refine WP.mono (copyTo_ok hp hi hedi hesi hrd hwr hblk j (by bdd_omega))
      fun s₁ ⟨hr₁, hrd₁, hwr₁, hf₁, hw₁⟩ => ?_
    obtain hsj := slot_lt j
    refine WP.mono (copyWord_ok j (p := blkAddr s₀ i) (q := scr s₀)
      (by rw [hr₁ .edi (by decide), hedi]) (by rw [hr₁ .esi (by decide), hesi])
      (by rw [hrd₁, hwr₁, hrd, hwr]; exact hp.in_blk hi (by bdd_omega))
      (by rw [hwr₁, hwr]; exact hp.scratch.wr _ (by bdd_omega))) fun s₂ ⟨hm₂, hr₂, hrd₂, hwr₂⟩ => ?_
    rw [hblk _ hf₁ j (by bdd_omega)] at hm₂
    refine ⟨fun r hr => by rw [hr₂ r hr, hr₁ r hr], by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁], ?_,
      fun t ht => ?_⟩
    · rw [hm₂]
      exact hf₁.writeW (List.mem_singleton_self _) _ (work_contains hfits (by bdd_omega))
    · obtain hst := slot_lt t
      rw [hm₂]
      by_cases htj : t = j
      · subst htj; exact Mem.readW_writeW_self32 _ _ _
      · rw [readW_writeW_scr hfits _ _ (by bdd_omega) (by bdd_omega) ?_]
        · exact hw₁ t (by bdd_omega)
        · simp only [slot] at hst hsj ⊢; omega_using [ht, hj, htj]

theorem spilled_fits : Spill.Fits 112 spilled := by decide

theorem spilled_ge : ∀ p ∈ spilled, 84 ≤ p.2 ∧ p.2 + 4 ≤ 96 := by decide

theorem load_eq : load = [
    .mov .edi (.mem ⟨.esp, 4⟩),
    .mov .eax (.mem ⟨.edi, 8⟩), .store ⟨.esi, 68⟩ .eax,
    .mov .eax (.mem ⟨.edi, 12⟩), .store ⟨.esi, 64⟩ .eax,
    .mov .eax (.mem ⟨.edi, 24⟩), .store ⟨.esi, 76⟩ .eax,
    .mov .eax (.mem ⟨.edi, 28⟩), .store ⟨.esi, 72⟩ .eax,
    .mov .eax (.mem ⟨.edi, 0⟩), .mov .ebx (.mem ⟨.edi, 4⟩),
    .mov .ecx (.mem ⟨.edi, 16⟩), .mov .edx (.mem ⟨.edi, 20⟩)] := by
  decide

theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hesp : s.gpr .esp = esp₀ s₀)
    (hesi : s.gpr .esi = scr s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (harg : s.mem.readW (addr (esp₀ s₀) 4) 32 = st s₀) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 (scr s₀) s₁ (stateAt s.mem ((st s₀).setWidth 64)) ∧
      Frame [workRegion (scr s₀)] s.mem s₁.mem ∧
      (∀ d, d + 4 ≤ 64 ∨ 84 ≤ d → d + 4 ≤ 112 →
        s₁.mem.readW (addr (scr s₀) d) 32 = s.mem.readW (addr (scr s₀) d) 32) ∧
      (∀ r ∈ pubRegs, s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have hfits := hp.scr_fits
  obtain ia : InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) 4) 4 := by
    rw [hrd, hwr]; exact hp.in_arg (by bdd_omega) (by bdd_omega)
  obtain his : ∀ d, d + 4 ≤ 32 → InRegions (s.rd ++ s.wr) (addr (st s₀) d) 4 := fun d hd => by
    rw [hrd, hwr]; exact in_st hp hd
  obtain hos : ∀ d, d + 4 ≤ 112 → InRegions s.wr (addr (scr s₀) d) 4 := fun d hd => by
    rw [hwr]; exact hp.scratch.wr d hd
  obtain hrs := readW_writeW_scr_st hp
  -- the code, with what it reads
  obtain h₁ : WP isa (.block load) s fun s₁ =>
      s₁.mem = (((s.mem.writeW (addr (scr s₀) 68) (s.mem.readW (addr (st s₀) 8) 32)).writeW
        (addr (scr s₀) 64) (s.mem.readW (addr (st s₀) 12) 32)).writeW
        (addr (scr s₀) 76) (s.mem.readW (addr (st s₀) 24) 32)).writeW
        (addr (scr s₀) 72) (s.mem.readW (addr (st s₀) 28) 32) ∧
      s₁.gpr .eax = s.mem.readW (addr (st s₀) 0) 32 ∧ s₁.gpr .ebx = s.mem.readW (addr (st s₀) 4) 32 ∧
      s₁.gpr .ecx = s.mem.readW (addr (st s₀) 16) 32 ∧
      s₁.gpr .edx = s.mem.readW (addr (st s₀) 20) 32 ∧
      s₁.gpr .esi = s.gpr .esi ∧ s₁.gpr .esp = s.gpr .esp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    rw [load_eq]
    apply WP.of_runBlock
    simp only [runBlock_cons, runBlock_nil, runStep_some, exec, readSrc, ea_mk,
      RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg, RegUpd.rd_setReg,
      RegUpd.wr_setReg, Nat.reduceLeDiff, and_self, not_false_eq_true, reduceCtorEq,
      State.load32, State.store32, ite_true, hesp, hesi, ia, harg, his, hos, hrs,
      Option.map_some, Option.some.injEq, exists_eq_left']
  refine WP.mono h₁ fun s₁ ⟨hm, h0, h1, h4, h5, hsi, hsp, hrd₁, hwr₁⟩ => ?_
  obtain hrw := readW_writeW_scr hfits
  obtain c : ∀ d, d + 4 ≤ 96 → (workRegion (scr s₀)).Contains (addr (scr s₀) d) (32 / 8) :=
    fun d hd => work_contains hfits hd
  obtain mm := List.mem_singleton_self (workRegion (scr s₀))
  refine ⟨?_, ?_, fun d h1 h2 => ?_, fun r hr => ?_, hrd₁, hwr₁⟩
  · rw [vars0, hm]
    simp only [stateAt_get hp _ (show 0 < 8 by decide),
      stateAt_get hp _ (show 1 < 8 by decide), stateAt_get hp _ (show 2 < 8 by decide),
      stateAt_get hp _ (show 3 < 8 by decide), stateAt_get hp _ (show 4 < 8 by decide),
      stateAt_get hp _ (show 5 < 8 by decide), stateAt_get hp _ (show 6 < 8 by decide),
      stateAt_get hp _ (show 7 < 8 by decide), stAddr, Nat.reduceMul]
    refine ⟨h0, h1, ?_, ?_, h4, h5, ?_, ?_⟩ <;>
    simp (disch := decide) only [Mem.readW_writeW_self32, hrw]
  · rw [hm]
    exact ((((Frame.refl _ _).writeW mm _ (c 68 (by bdd_omega))).writeW mm _ (c 64 (by bdd_omega))).writeW
      mm _ (c 76 (by bdd_omega))).writeW mm _ (c 72 (by bdd_omega))
  · rw [hm, hrw _ _ (by bdd_omega) h2 (by bdd_omega), hrw _ _ (by bdd_omega) h2 (by bdd_omega),
      hrw _ _ (by bdd_omega) h2 (by bdd_omega), hrw _ _ (by bdd_omega) h2 (by bdd_omega)]
  · simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hsi
    · exact hsp

/-- Eight words written in order to the hash value. -/
def writeState (s₀ : State) (m : Mem) (v : HashValue) : Mem :=
  let a := addr (st s₀)
  ((((((((m.writeW (a 0) v[0]).writeW (a 4) v[1]).writeW (a 8) v[2]).writeW (a 12) v[3]).writeW
    (a 16) v[4]).writeW (a 20) v[5]).writeW (a 24) v[6]).writeW (a 28) v[7])

theorem stateAt_writeState {s₀ : State} (hp : Pre s₀) (m : Mem) (v : HashValue) :
    stateAt (writeState s₀ m v) ((st s₀).setWidth 64) = v := by
  apply stateAt_eq hp
  intro k hk
  simp only [writeState, stAddr]
  rcases (by bdd_omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with h | h | h | h | h | h | h | h <;> subst h <;>
  simp (disch := decide) only [Nat.reduceMul, Mem.readW_writeW_self32,
    readW_writeW_st hp]

theorem frame_writeState {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Frame [stR s₀] m m')
    (v : HashValue) : Frame [stR s₀] m (writeState s₀ m' v) := by
  have c : ∀ d, d + 4 ≤ 32 → (stR s₀).Contains (addr (st s₀) d) (32 / 8) :=
    fun d hd => contains_sub hd (by bdd_omega) (st_eq hp (by bdd_omega))
  simp only [writeState]
  refine (((((((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 4 ?_)).writeW ?_ _ (c 8 ?_)).writeW ?_ _
    (c 12 ?_)).writeW ?_ _ (c 16 ?_)).writeW ?_ _ (c 20 ?_)).writeW ?_ _ (c 24 ?_)).writeW ?_ _
    (c 28 ?_) <;>
  simp

theorem update_eq : update ++ advance = [
    .mov .ebx (.mem ⟨.esp, 4⟩),
    .alu .xor .ebp (.mem ⟨.ebx, 0⟩), .store ⟨.ebx, 0⟩ .ebp,
    .alu .xor .eax (.mem ⟨.ebx, 4⟩), .store ⟨.ebx, 4⟩ .eax,
    .mov .edx (.mem ⟨.esi, 68⟩), .alu .xor .edx (.mem ⟨.ebx, 8⟩), .store ⟨.ebx, 8⟩ .edx,
    .mov .edx (.mem ⟨.esi, 64⟩), .alu .xor .edx (.mem ⟨.ebx, 12⟩), .store ⟨.ebx, 12⟩ .edx,
    .alu .xor .edi (.mem ⟨.ebx, 16⟩), .store ⟨.ebx, 16⟩ .edi,
    .alu .xor .ecx (.mem ⟨.ebx, 20⟩), .store ⟨.ebx, 20⟩ .ecx,
    .mov .edx (.mem ⟨.esi, 80⟩), .alu .xor .edx (.mem ⟨.ebx, 24⟩), .store ⟨.ebx, 24⟩ .edx,
    .mov .edx (.mem ⟨.esi, 76⟩), .alu .xor .edx (.mem ⟨.ebx, 28⟩), .store ⟨.ebx, 28⟩ .edx,
    .mov .edi (.mem ⟨.esi, 84⟩), .mov .ebp (.mem ⟨.esi, 88⟩),
    .alu .add .edi (.imm 64), .alu .sub .ebp (.imm 1)] := by
  decide

theorem update_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) {p c : BitVec 32}
    (hv : Vars 64 (scr s₀) s V) (hesp : s.gpr .esp = esp₀ s₀) (hesi : s.gpr .esi = scr s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (harg : s.mem.readW (addr (esp₀ s₀) 4) 32 = st s₀)
    (hH : ∀ k : Nat, (hk : k < 8) → s.mem.readW (stAddr s₀ k) 32 = H[k])
    (hedi : s.mem.readW (addr (scr s₀) 84) 32 = p) (hebp : s.mem.readW (addr (scr s₀) 88) 32 = c) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = writeState s₀ s.mem (Vector.zipWith (· ^^^ ·) V H) ∧
      s'.gpr .edi = p + 64 ∧ s'.gpr .ebp = c - 1 ∧
      s'.zf = some (c - 1 == 0) ∧
      s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ia : InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) 4) 4 := by
    rw [hrd, hwr]; exact hp.in_arg (by bdd_omega) (by bdd_omega)
  obtain his : ∀ d, d + 4 ≤ 32 → InRegions (s.rd ++ s.wr) (addr (st s₀) d) 4 := fun d hd => by
    rw [hrd, hwr]; exact in_st hp hd
  obtain hos : ∀ d, d + 4 ≤ 32 → InRegions s.wr (addr (st s₀) d) 4 := fun d hd => by
    rw [hwr]; exact out_st hp hd
  obtain hic : ∀ d, d + 4 ≤ 112 → InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 := fun d hd => by
    rw [hrd, hwr]; exact hp.scratch.rd d hd
  obtain hrs := readW_writeW_st_scr hp
  obtain hrr := readW_writeW_st hp
  rw [vars64] at hv
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := hv
  obtain m0 : s.mem.readW (addr (st s₀) 0) 32 = H[0]'(by decide) := hH 0 (by decide)
  obtain m1 : s.mem.readW (addr (st s₀) 4) 32 = H[1]'(by decide) := hH 1 (by decide)
  obtain m2 : s.mem.readW (addr (st s₀) 8) 32 = H[2]'(by decide) := hH 2 (by decide)
  obtain m3 : s.mem.readW (addr (st s₀) 12) 32 = H[3]'(by decide) := hH 3 (by decide)
  obtain m4 : s.mem.readW (addr (st s₀) 16) 32 = H[4]'(by decide) := hH 4 (by decide)
  obtain m5 : s.mem.readW (addr (st s₀) 20) 32 = H[5]'(by decide) := hH 5 (by decide)
  obtain m6 : s.mem.readW (addr (st s₀) 24) 32 = H[6]'(by decide) := hH 6 (by decide)
  obtain m7 : s.mem.readW (addr (st s₀) 28) 32 = H[7]'(by decide) := hH 7 (by decide)
  rw [update_eq]
  apply WP.of_runBlock
  simp only [runBlock_cons, runBlock_nil, runStep_some, exec, execAlu, readSrc, ea_mk,
    RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.zf_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags,
    Nat.reduceLeDiff, and_self, or_true, not_false_eq_true, reduceCtorEq,
    State.load32, State.store32, ite_true, hesp, hesi, ia, harg, his, hos, hic, hrs, hrr,
    v0, v1, v2, v3, v4, v5, v6, v7, m0, m1, m2, m3, m4, m5, m6, m7, hedi, hebp,
    writeState, Vector.getElem_zipWith,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']

theorem saved_frame {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame [workRegion (scr s₀)] m m' ∨ Frame [stR s₀] m m') : Saved s₀ m' := by
  obtain key : ∀ d : Nat, 96 ≤ d → d + 4 ≤ 112 →
      m'.readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 := by
    intro d hd hd'
    obtain hc : (⟨addr (scr s₀) d, 4⟩ : Region).Contains (addr (scr s₀) d) (32 / 8) :=
      Region.contains_self _ _
    rcases hf with hf | hf
    · refine hf.readW hc ?_ (by decide)
      simp only [List.mem_singleton, forall_eq]
      rw [hp.scr_eq (by bdd_omega)]
      exact Offset.disjoint_base _ (by bdd_omega) (by bdd_omega)
    · refine hf.readW hc ?_ (by decide)
      simp only [List.mem_singleton, forall_eq]
      refine Region.Disjoint.sub_left hp.st_scr.symm ?_
      rw [hp.scr_eq (by bdd_omega)]
      exact Offset.sub_base _ (by bdd_omega)
  exact h.of_readW fun p hp' => key _ (by revert p hp'; decide) (compressSaved_fits.1 p hp')

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (hp : Pre s₀) {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    bswap (s₀.mem.readW (addr (blkAddr s₀ i) (4 * t)) 32) = W (blk s₀ i) t := by
  rw [hp.blkAddr_eq hi ht, W_lt _ ht, bswap_readW]
  simp only [blk, blockAt, parseBlock]
  generalize (bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i) = a
  rw [show a + BitVec.ofNat 64 (4 * t) + 1 = a + BitVec.ofNat 64 (4 * t + 1) from Offset.add_add _ _ 1,
    show a + BitVec.ofNat 64 (4 * t + 1) + 1 = a + BitVec.ofNat 64 (4 * t + 2) from Offset.add_add _ _ 1,
    show a + BitVec.ofNat 64 (4 * t + 2) + 1 = a + BitVec.ofNat 64 (4 * t + 3) from Offset.add_add _ _ 1]

theorem work_sub (p : BitVec 32) : Region.Sub (workRegion p) ⟨p.setWidth 64, 112⟩ :=
  Region.sub_prefix (by bdd_omega)

theorem harg_of {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [stR s₀, scrR s₀] s₀.mem m) :
    m.readW (addr (esp₀ s₀) 4) 32 = st s₀ :=
  hp.arg_frame hf (i := 0) (by decide)

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  have hfits := hp.scr_fits
  obtain hwork : ∀ r' ∈ [workRegion (scr s₀)], (blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (work_sub _)
  obtain hst : ∀ r' ∈ [workRegion (scr s₀)], (stR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.st_scr (work_sub _)
  obtain hblk : ∀ m, Frame [workRegion (scr s₀)] s.mem m → ∀ t : Nat, t < 16 →
      bswap (m.readW (addr (blkAddr s₀ i) (4 * t)) 32) = W (blk s₀ i) t := by
    intro m hm t ht
    rw [hm.readW (hp.blk_contains hi ht) hwork (by decide),
      hL.frame.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word hp hi ht
  obtain hsub : ∀ r ∈ [workRegion (scr s₀)], ∃ r' ∈ [stR s₀, scrR s₀], Region.Sub r r' :=
    fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact work_sub _⟩
  refine WP.seq ?_
  -- the block, into the window
  rw [show copy ++ spill ++ load = copyTo 16 ++ (Spill.saveCode .esi spilled ++ load) from
    List.append_assoc _ _ _, WP.block_append_iff]
  refine WP.mono (copyTo_ok hp hi hL.edi hL.esi hL.rd hL.wr hblk 16 (Nat.le_refl _))
    fun s₁ ⟨hr₁, hrd₁, hwr₁, hf₁, hw₁⟩ => ?_
  obtain hesi₁ : s₁.gpr .esi = scr s₀ := (hr₁ _ (by decide)).trans hL.esi
  -- the block pointer and the count, into the scratch buffer
  refine Spill.save_ok spilled (fun p h => by
    rw [hesi₁, hwr₁, hL.wr]; exact hp.scratch.wr _ (spilled_fits.1 p h)) fun s₂ u₂ => ?_
  rw [hesi₁] at u₂
  obtain hsv₂ : Spill.Saved s₂.mem (addr (scr s₀)) s₁.gpr spilled := by
    rw [u₂.mem]; exact Spill.saveMem_saved_addr _ _ spilled_fits hfits
  obtain hedi₂ : s₂.mem.readW (addr (scr s₀) 84) 32 = blkAddr s₀ i :=
    (hsv₂ (.edi, 84) (by decide)).trans ((hr₁ _ (by decide)).trans hL.edi)
  obtain hebp₂ : s₂.mem.readW (addr (scr s₀) 88) 32 = BitVec.ofNat 32 (nb s₀ - i) :=
    (hsv₂ (.ebp, 88) (by decide)).trans ((hr₁ _ (by decide)).trans hL.ebp)
  obtain hf₂ : Frame [workRegion (scr s₀)] s₁.mem s₂.mem := by
    rw [u₂.mem]
    exact Spill.saveMem_frame (List.mem_singleton_self _) _ _ _ _
      fun p h => work_contains hfits (spilled_ge p h).2
  obtain hw₂ : ∀ t < 16, s₂.mem.readW (addr (scr s₀) (slot t)) 32 = W (blk s₀ i) t := fun t ht => by
    obtain hsl := slot_lt t
    rw [u₂.mem, Spill.saveMem_readW_of_sep _ _ (by decide) _ _ fun p h =>
      scr_sep hfits (d := p.2) (e := slot t) (by have := spilled_ge p h; bdd_omega) (by bdd_omega)
        (.inr (by have := spilled_ge p h; bdd_omega))]
    exact hw₁ t ht
  obtain hesp₂ : s₂.gpr .esp = esp₀ s₀ := by rw [u₂.gpr, hr₁ _ (by decide), hL.esp]
  obtain hesi₂ : s₂.gpr .esi = scr s₀ := by rw [u₂.gpr, hesi₁]
  obtain hrd₂ : s₂.rd = s₀.rd := by rw [u₂.rd, hrd₁, hL.rd]
  obtain hwr₂ : s₂.wr = s₀.wr := by rw [u₂.wr, hwr₁, hL.wr]
  obtain hfr₂ : Frame [workRegion (scr s₀)] s.mem s₂.mem := hf₁.trans hf₂
  obtain hH₂ : stateAt s₂.mem ((st s₀).setWidth 64) = stateAt s.mem ((st s₀).setWidth 64) :=
    stateAt_eq hp fun k hk => by
      rw [hfr₂.readW (contains_sub (by bdd_omega) (by bdd_omega) (hp.stAddr_eq hk)) hst (by decide),
        stateAt_get hp _ hk]
  -- the hash value, into the registers
  refine WP.mono (load_ok hp hesp₂ hesi₂ hrd₂ hwr₂ (harg_of hp (hL.frame.trans (hfr₂.sub hsub))))
    fun s₃ ⟨hv₃, hf₃, hk₃, hpub₃, hrd₃, hwr₃⟩ => ?_
  rw [hH₂] at hv₃
  refine WP.seq (WP.mono (rounds_ok (M := blk s₀ i) (sB := s₃)
    (hp.scratch.congr (hrd₃.trans hrd₂) (hwr₃.trans hwr₂)) ((hpub₃ .esi (by decide)).trans hesi₂) hv₃
    (fun j hj => by
      have hsl := slot_lt j
      rw [hk₃ _ (.inl hsl) (by bdd_omega)]; exact hw₂ j hj) 64 (Nat.le_refl _))
    fun s₄ hR => ?_)
  obtain hfr₄ : Frame [workRegion (scr s₀)] s.mem s₄.mem := (hfr₂.trans hf₃).trans hR.frame
  obtain hframe₄ : Frame [stR s₀, scrR s₀] s₀.mem s₄.mem := hL.frame.trans (hfr₄.sub hsub)
  obtain hesp₄ : s₄.gpr .esp = esp₀ s₀ := by
    rw [hR.pub .esp (by decide), hpub₃ .esp (by decide), hesp₂]
  obtain hesi₄ : s₄.gpr .esi = scr s₀ := by
    rw [hR.pub .esi (by decide), hpub₃ .esi (by decide), hesi₂]
  obtain hrd₄ : s₄.rd = s₀.rd := by rw [hR.rd, hrd₃, hrd₂]
  obtain hwr₄ : s₄.wr = s₀.wr := by rw [hR.wr, hwr₃, hwr₂]
  obtain hedi₄ : s₄.mem.readW (addr (scr s₀) 84) 32 = blkAddr s₀ i := by
    rw [hR.keep 84 (by bdd_omega) (by bdd_omega), hk₃ 84 (.inr (by bdd_omega)) (by bdd_omega), hedi₂]
  obtain hebp₄ : s₄.mem.readW (addr (scr s₀) 88) 32 = BitVec.ofNat 32 (nb s₀ - i) := by
    rw [hR.keep 88 (by bdd_omega) (by bdd_omega), hk₃ 88 (.inr (by bdd_omega)) (by bdd_omega), hebp₂]
  refine WP.mono (update_ok hp _ (stateAt s.mem ((st s₀).setWidth 64)) hR.vars hesp₄ hesi₄ hrd₄ hwr₄
    (harg_of hp hframe₄) (fun k hk => ?_) hedi₄ hebp₄) fun s₅ h₅ => ?_
  · rw [hfr₄.readW (contains_sub (by bdd_omega) (by bdd_omega) (hp.stAddr_eq hk)) hst (by decide),
      stateAt_get hp _ hk]
  obtain ⟨hm₅, hedi₅, hebp₅, hz₅, hesi₅, hesp₅, hrd₅, hwr₅⟩ := h₅
  obtain hnb : nb s₀ < 2 ^ 32 := (arg s₀ 2).isLt
  obtain hebp : BitVec.ofNat 32 (nb s₀ - i) - 1 = BitVec.ofNat 32 (nb s₀ - (i + 1)) := by
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      Offset.ofNat_sub_ofNat (by bdd_omega), Nat.sub_sub]
  obtain hframe : Frame [stR s₀, scrR s₀] s₀.mem s₅.mem := by
    refine hframe₄.trans ?_
    rw [hm₅]
    exact (frame_writeState hp (Frame.refl _ _) _).sub
      fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  obtain hcommon : ∀ j, j = i + 1 → Common s₀ j s₅ := by
    rintro j rfl
    refine ⟨by rw [hesi₅, hesi₄], by rw [hesp₅, hesp₄], by rw [hrd₅, hrd₄], by rw [hwr₅, hwr₄],
      hframe, ?_, ?_⟩
    · rw [hm₅, stateAt_writeState hp, compressBlocks_succ, ← hL.state]
      rfl
    · rw [hm₅]
      refine saved_frame hp ?_ (.inr (frame_writeState hp (Frame.refl _ _) _))
      exact saved_frame hp hL.saved (.inl hfr₄)
  obtain hev : eval .ne s₅ = some (!(BitVec.ofNat 32 (nb s₀ - (i + 1)) == 0)) := by
    simp only [eval, hz₅, hebp, Option.map_some]
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon _ rfl⟩
  · right
    obtain hne : nb s₀ - (i + 1) ≠ 0 := by bdd_omega
    obtain h0 : BitVec.ofNat 32 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      obtain h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by bdd_omega)] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by bdd_omega, { hcommon _ rfl with edi := ?_, ebp := ?_ }⟩
    · rw [hedi₅]
      exact (Offset.add_add _ _ 64).trans
        (congrArg (bp s₀ + ·) (congrArg (BitVec.ofNat _) (by bdd_omega)))
    · rw [hebp₅, hebp]

/-! ## Prologue and epilogue -/

theorem prologue_eq : prologue = .mov .eax (.mem ⟨.esp, 16⟩) :: (Spill.saveCode .eax compressSaved ++
    ([.mov .esi (.reg .eax), .mov .edi (.mem ⟨.esp, 8⟩), .mov .ebp (.mem ⟨.esp, 12⟩),
      .alu .test .ebp (.reg .ebp)] : List Instr)) := rfl

theorem epilogue_eq :
    epilogue = Spill.restoreCode .esi ([(.ebx, 96), (.edi, 104), (.ebp, 108)] ++ [(.esi, 100)]) ++ [] :=
  rfl

/-- The memory after the prologue. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (addr (scr s₀)) s₀.gpr compressSaved

theorem compressSaved_contains {s₀ : State} (hp : Pre s₀) : ∀ p ∈ compressSaved, (scrR s₀).Contains (addr (scr s₀) p.2) 4 :=
  fun p h => have := compressSaved_fits.1 p h; contains_sub (by bdd_omega) (by bdd_omega) (hp.scr_eq (by bdd_omega))

/-- Reading an argument after saving the registers. -/
theorem saveMem_arg {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 20) :
    (saveMem s₀).readW (addr (esp₀ s₀) d) 32 = s₀.mem.readW (addr (esp₀ s₀) d) 32 :=
  Spill.saveMem_readW_of_sep _ _ (by decide) _ _ fun p h =>
    hp.arg_scr.sep (hp.arg_contains hd hd') (compressSaved_contains hp p h)

theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block prologue) s₀ fun s₁ =>
      s₁.gpr .esi = scr s₀ ∧ s₁.gpr .edi = bp s₀ ∧ s₁.gpr .ebp = arg s₀ 2 ∧
      s₁.gpr .esp = esp₀ s₀ ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ ∧
      s₁.zf = some (arg s₀ 2 &&& arg s₀ 2 == 0) := by
  rw [prologue_eq]
  refine Wp.wp_ldm rfl (hp.in_arg (d := 16) (by bdd_omega) (by bdd_omega)) fun s₁ u₁ => ?_
  refine Spill.save_ok compressSaved (fun p h => by rw [u₁.gpr, u₁.wr]; exact hp.scratch.wr _ (compressSaved_fits.1 p h))
    fun s₂ u₂ => ?_
  obtain hm : s₂.mem = saveMem s₀ := by
    rw [u₂.mem, u₁.gpr, u₁.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => u₁.other _ (by revert p h; decide)
  obtain hesp : s₂.gpr .esp = esp₀ s₀ := by rw [u₂.gpr, u₁.other _ (by decide)]
  refine Wp.wp_mov fun s₃ u₃ => Wp.wp_ldm (by rw [u₃.other _ (by decide), hesp])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hp.in_arg (d := 8) (by bdd_omega) (by bdd_omega))
    fun s₄ u₄ => Wp.wp_ldm (by rw [u₄.other _ (by decide), u₃.other _ (by decide), hesp])
      (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
          exact hp.in_arg (d := 12) (by bdd_omega) (by bdd_omega))
    fun s₅ u₅ => Wp.wp_test fun s₆ f₆ z₆ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.gpr]; rfl
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.mem, hm, saveMem_arg hp (by bdd_omega) (by bdd_omega)]; rfl
  · rw [f₆.gpr, u₅.gpr, u₄.mem, u₃.mem, hm, saveMem_arg hp (by bdd_omega) (by bdd_omega)]; rfl
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), hesp]
  · rw [f₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [f₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [f₆.mem, u₅.mem, u₄.mem, u₃.mem, hm]
  · rw [z₆, u₅.gpr, u₄.mem, u₃.mem, hm, saveMem_arg hp (by bdd_omega) (by bdd_omega)]; rfl

theorem saveMem_saved {s₀ : State} (hp : Pre s₀) : Saved s₀ (saveMem s₀) :=
  Spill.saveMem_saved_addr _ _ compressSaved_fits hp.scr_fits

theorem saveMem_frame {s₀ : State} (hp : Pre s₀) : Frame [scrR s₀] s₀.mem (saveMem s₀) :=
  Spill.saveMem_frame List.mem_cons_self _ _ _ _ (compressSaved_contains hp)

theorem common_zero {s₀ : State} (hp : Pre s₀) {s₁ : State} (hesi : s₁.gpr .esi = scr s₀)
    (hesp : s₁.gpr .esp = esp₀ s₀) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr)
    (hm : s₁.mem = saveMem s₀) : Common s₀ 0 s₁ := by
  refine ⟨hesi, hesp, hrd, hwr, ?_, ?_, by rw [hm]; exact saveMem_saved hp⟩
  · rw [hm]; exact (saveMem_frame hp).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · rw [hm]
    apply stateAt_eq hp
    intro k hk
    rw [(saveMem_frame hp).readW (contains_sub (len := 32) (off := 4 * k) (by bdd_omega) (by bdd_omega)
      (hp.stAddr_eq hk))
      (by simpa using hp.st_scr) (by decide), ← stateAt_get hp _ hk]
    rfl

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hc : Common s₀ (nb s₀) s) :
    WP isa (.block epilogue) s fun s' =>
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧ s'.mem = s.mem := by
  rw [epilogue_eq]
  refine Spill.restoreBase_ok _ (by decide)
    (fun p h => by rw [hc.esi, hc.rd, hc.wr]; exact hp.scratch.rd _ (compressSaved_fits.1 p (by revert p h; decide)))
    (by rw [hc.esi]; exact hc.saved.sub (by decide)) fun s' u =>
      WP.block_nil ⟨u.abi (by decide) (by decide) hc.esp, u.mem⟩

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sm3.compressX86.post s₀ s' := by
  refine WP.seq (WP.mono (save_ok hp) fun s₁ ⟨hesi, hedi, hebp, hesp, hrd, hwr, hm, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc =>
    WP.mono (restore_ok hp hc) fun s' ⟨hr, hm'⟩ => ⟨⟨hr, ?_⟩, ?_⟩)
  rotate_left
  · rw [hm']
    refine hc.frame.readW (Region.contains_self _ _) ?_ (by decide)
    simpa using ⟨hp.ret_st, hp.ret_scr⟩
  · show stateAt s'.mem _ = _
    rw [hm']; exact hc.state
  obtain hc₀ := common_zero hp hesi hesp hrd hwr hm
  refine WP.ite (arg s₀ 2 &&& arg s₀ 2 == 0) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp only [BitVec.and_self, beq_iff_eq] at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    obtain hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by bdd_omega, i + 1, rfl, hi', hL'⟩
    obtain hL₀ : LInv s₀ 0 s₁ :=
      { hc₀ with
        edi := by rw [hedi]; simp [blkAddr]
        ebp := by rw [hebp]; simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

/-- Memory holding the arguments `0x1000, 0x2000, 0, 0x3000` at `0x4004`. -/
def satMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else if a = 0x4011 then 0x30 else 0

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 0⟩, ⟨0x4004, 16⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 112⟩]

theorem sat_pre : Proof.Sm3.compressX86.pre satState := by
  obtain a0 : arg satState 0 = 0x1000 := by decide
  obtain a1 : arg satState 1 = 0x2000 := by decide
  obtain a2 : arg satState 2 = 0 := by decide
  obtain a3 : arg satState 3 = 0x3000 := by decide
  obtain e : argAddr satState 0 = 0x4004 := by decide
  simp only [Proof.Sm3.compressX86, a0, a1, a2, a3, e]
  refine ⟨by decide, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide⟩ <;>
  first
  | exact Offset.disjoint_of_le (by decide) (by decide)
  | exact Region.Disjoint.symm (Offset.disjoint_of_le (by decide) (by decide))

/-- The taint analysis starts with the stack arguments public, and the words
holding `state` and `scratch` known to be the base addresses of the writable
regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [32, 112], argLen := 20, argBases := [(4, 0), (16, 1)] }

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  obtain hst := hp.st_fits; have hsc := hp.scr_fits; have hs := hp.esp_fits
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simpa [hp.wr] using hp.st_scr, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_arith
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by bdd_omega) hp.ret_st hp.arg_st
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by bdd_omega) hp.ret_scr hp.arg_scr
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sm3.compressX86.pre s₁)
    (h₂ : Proof.Sm3.compressX86.pre s₂) (hpub : Proof.Sm3.compressX86.pub s₁ s₂) :
    VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1, a2, a3⟩ := hpub
  obtain hp₁ := pre_of _ h₁; have hp₂ := pre_of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [stR, scrR, st, scr, a0, a3]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hp₁.esp_fits h4 hk, VG.X86.Taint.argByte_eq hp₂.esp_fits h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by bdd_omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by bdd_omega))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 ∨ (k - 4) / 4 = 2 ∨ (k - 4) / 4 = 3 := by bdd_omega
    rcases this with h | h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2
    · exact congrArg _ a3

theorem compress_verified :
    Verified X86.target Impl.Sm3.X86.compress Proof.Sm3.compressX86 :=
  ⟨fun s hs => correct (pre_of s hs),
    VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hpub => agree₀ h₁ h₂ hpub) (by native_taint_decide),
    ⟨satState, sat_pre⟩⟩

end VG.Proof.Sm3.X86
