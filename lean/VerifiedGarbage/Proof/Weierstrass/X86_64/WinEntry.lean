module

public import VerifiedGarbage.Proof.Weierstrass.Window
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Mont.X86_64.Ops
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Impl.Weierstrass.X86_64.Window
public import VerifiedGarbage.Proof.Weierstrass.WinLay
public import VerifiedGarbage.Proof.Weierstrass.Law3
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop

/-! ### `Weierstrass.X86_64.Window`, which this module and modules that import it used -/

section

/-!
# The window method on x86-64: the table and the additions

As on AArch64 (`Proof/Weierstrass/AArch64/Window.lean`): the table `[1 … 8]P`
(`build_ok`: `P`, then `[m + 1]P = [m]P + P` by the complete addition for
`a = -3`, `addT_ok`), and the addition of an entry to `R` (`winAdd_ok`: into
`D`, then copied). `WinEntry.lean` selects the entry of a digit, `WinQuad.lean`
multiplies `R` by 16, and `WinLoop.lean` is the loop.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

/-! ## The complete addition into `R` -/

/-- After a sum into `D` copied to `R`: `R` holds `v`, the sum's value. -/
structure SumPostW (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (v : Fe C × Fe C × Fe C)
    (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (clob K.M.n) s s'
  unch : Unch base ((winOther K).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n)]) s.mem s'.mem
  lt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p
  val : (tmv C K.M.n base s' K.R.x, tmv C K.M.n base s' K.R.y, tmv C K.M.n base s' K.R.z) = v

theorem winOther_mem {K : WinCfg} {x : Nat} (h : x ∈ winOther K) : x ∈ winSlots K := by
  simp only [winSlots, List.mem_append]; exact Or.inl (Or.inr h)

/-- `R` and `D`, written and apart. -/
theorem winRD {K : WinCfg} {size : Nat} (hL : WinLay K size) :
    (∀ x ∈ [K.R.x, K.R.y, K.R.z, K.D.x, K.D.y, K.D.z], x + 8 * K.M.n ≤ size) ∧
    (∀ x ∈ [K.R.x, K.R.y, K.R.z], ∀ y ∈ [K.R.x, K.R.y, K.R.z, K.D.x, K.D.y, K.D.z], x ≠ y →
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x) ∧
    (∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∉ [K.D.x, K.D.y, K.D.z]) ∧
    (K.R.x ≠ K.R.y ∧ K.R.x ≠ K.R.z ∧ K.R.y ≠ K.R.z) := by
  obtain ⟨rxy, rxz, ryz, hRD, -, -, -, -, -, -⟩ := hL.other_ne
  obtain hw : ∀ z ∈ [K.R.x, K.R.y, K.R.z, K.D.x, K.D.y, K.D.z], z ∈ winWs K := by
    intro z hz
    refine winOther_ws K z ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> win_mem
  refine ⟨fun x hx => hL.lay.le x (winWs_slots K x (hw x hx)),
    fun x hx y hy hxy => hL.apart₂ (hw x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h <;> simp [h])) (hw y hy) hxy, fun x hx hd => ?_, rxy, rxz, ryz⟩
  refine hRD x hx (List.mem_append_right _ ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl <;> simp [rcbW]

/-- A sum into `D` (the field program `ops`, writing `rcbW K.S K.D` and computing `v`),
then copied to `R`. -/
theorem winCopy_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    {ops : List FOp} {V : List Nat} {E' : Nat → Fe C} {v : Fe C × Fe C × Fe C}
    {s : State} (hs : Scr s base size)
    (W : WP isa (fprogB K.M ops).inline s fun s' => ProgKeep K.M base (rcbW K.S K.D) s s' ∧
      Inv K.M base size C.p (· ∈ winSlots K) ([K.D.x, K.D.y, K.D.z] ++ V) E' s' ∧
      (E' K.D.x, E' K.D.y, E' K.D.z) = v) :
    WP isa (Code.seq (fprogB K.M ops) (.block (copyPt K.M.n K.R K.D))).inline s (SumPostW K C base size v s) := by
  refine WP.seq ((WP.mono W fun s₁ h₁ => ?_))
  obtain ⟨k₁, I₁, v₁⟩ := h₁
  obtain ⟨hle, hap, hne, ho⟩ := winRD hL
  refine WP.mono (copyPt_ok (k₁.scr hs) hle hap hne ho) fun s₂ ⟨wx, wy, wz, k₂, U₂⟩ => ?_
  obtain hDx : K.D.x ∈ [K.D.x, K.D.y, K.D.z] ++ V := by simp
  obtain hDy : K.D.y ∈ [K.D.x, K.D.y, K.D.z] ++ V := by simp
  obtain hDz : K.D.z ∈ [K.D.x, K.D.y, K.D.z] ++ V := by simp
  refine ⟨(k₁.scr hs).of_keepRegs k₂ (by decide), ?_, ?_, ?_, ?_⟩
  · have c1 : ∀ r ∈ [Reg.rax], r ∈ clob K.M.n := by intro r hr; simp at hr; subst hr; simp [clob]
    exact (⟨k₁.gpr, k₁.rd, k₁.wr⟩ : KeepRegs (clob K.M.n) s s₁).trans (k₂.mono c1)
  · refine (k₁.unch.trans U₂).mono ?_
    intro w hw
    simp only [winOther, rcbW, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      List.cons_append, List.nil_append] at hw ⊢
    grind
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [wx]; exact I₁.lt _ hDx
    · rw [wy]; exact I₁.lt _ hDy
    · rw [wz]; exact I₁.lt _ hDz
  · rw [← v₁]
    show (toM _ _ _, toM _ _ _, toM _ _ _) = _
    rw [wx, wy, wz, I₁.val _ hDx, I₁.val _ hDy, I₁.val _ hDz]

/-- `R = R + E` by Algorithm 4 into `D`, then copied. -/
theorem winAdd_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {s : State} (hs : Scr s base size)
    (hM : ModOkW K.M size C.p s.mem base)
    (hlt : ∀ x ∈ rcbR K.S K.R K.E, wordsVal s.mem base x K.M.n < C.p) :
    WP isa (Code.seq (fprogB K.M (rcb3 K.S K.R K.E K.D)) (.block (copyPt K.M.n K.R K.D))).inline s
      (SumPostW K C base size (VG.Proof.Weierstrass.rcbAdd3 (tmv C K.M.n base s K.S.b3)
        (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
        (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z)) s) := by
  obtain hO : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.R K.E, x ∈ winSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact winOther_mem (List.mem_append_right _ hx)
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> win_mem
  obtain hI : Inv K.M base size C.p (· ∈ winSlots K) (rcbR K.S K.R K.E) (tmv C K.M.n base s) s :=
    ⟨hs, hM, fun x hx => hO x (List.mem_append_right _ hx), hlt, fun _ _ => rfl⟩
  exact winCopy_ok hL hs (rcb3_ok hL.lay hp (hL.rcbApart_D (Or.inr rfl)) hO hI (fun x hx => hx))

/-! ## The table -/

/-- What the window method reads and never writes, at the start: the curve's
`a` and `b`, zero, `P`, and the table of the bits of `k`. -/
structure WinFixed (K : WinCfg) (C : Curve) (base : Addr) (s₀ : State) (P : Point C) (k : Nat) :
    Prop where
  a : tmv C K.M.n base s₀ K.S.a = Fin.ofNat C.p C.a
  b : tmv C K.M.n base s₀ K.S.b3 = Fin.ofNat C.p C.b
  ro_lt : ∀ x ∈ winRo K, wordsVal s₀.mem base x K.M.n < C.p
  zero : wordsVal s₀.mem base K.zero K.M.n = 0
  pt : Rep C (tmv C K.M.n base s₀ K.P.x) (tmv C K.M.n base s₀ K.P.y) (tmv C K.M.n base s₀ K.P.z) P
  bits : ∀ t < 4 * K.J, s₀.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0

/-- A slot read only keeps its number. -/
theorem winRo_val {K : WinCfg} {size : Nat} (hL : WinLay K size) {base : Addr}
    {m m' : Mem} (hU : Unch base (winW K) m m') (hn : base.toNat + size ≤ 2 ^ 64) {x : Nat}
    (hx : x ∈ winRo K) : wordsVal m' base x K.M.n = wordsVal m base x K.M.n :=
  hU.wordsVal (hL.ro_w hx) (by have := hL.lay.le x (winRo_slots K x hx); omega_arith)

theorem winRo_tmv {K : WinCfg} {C : Curve} {size : Nat} (hL : WinLay K size)
    {base : Addr} {s s' : State} (hU : Unch base (winW K) s.mem s'.mem) (hn : base.toNat + size ≤ 2 ^ 64)
    {x : Nat} (hx : x ∈ winRo K) : tmv C K.M.n base s' x = tmv C K.M.n base s x := by
  show toM _ _ _ = toM _ _ _; rw [winRo_val hL hU hn hx]

/-- What the window method writes misses the modulus. -/
theorem winW_mo {K : WinCfg} {size : Nat} (hL : WinLay K size) {m : Nat} {mem : Mem} {base : Addr}
    (hM : ModOkW K.M size m mem base) :
    ∀ w ∈ winW K, K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo := by
  intro w hw
  simp only [winW, List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · have := hL.lay.mo y (winWs_slots K y hy); dsimp only; omega_arith
  · have := hM.sep; dsimp only; omega_arith

/-- Entries `[1 … m]P` of the table, each a representative by `Rp`. -/
def TblOkR (K : WinCfg) (C : Curve) (base : Addr) (Rp : Fe C → Fe C → Fe C → Point C → Prop)
    (P : Point C) (m : Nat) (s : State) : Prop :=
  ∀ j, 1 ≤ j → j ≤ m →
    (∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z], wordsVal s.mem base x K.M.n < C.p) ∧
    Rp (tmv C K.M.n base s (K.tblPt j).x) (tmv C K.M.n base s (K.tblPt j).y)
      (tmv C K.M.n base s (K.tblPt j).z) (mul j P)

/-- Entries `[1 … m]P` of the table, in projective coordinates. -/
def TblOk (K : WinCfg) (C : Curve) (base : Addr) (P : Point C) (m : Nat) (s : State) : Prop :=
  TblOkR K C base (Rep C) P m s

/-- The table's invariant: entries `[1 … m]P` built. -/
structure BuildInv (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (m : Nat) (s : State) : Prop where
  scr : Scr s base size
  keep : KeepRegs (powClob K.M.n) s₀ s
  unch : Unch base (winW K) s₀.mem s.mem
  mod : ModOkW K.M size C.p s.mem base
  tbl : TblOk K C base P m s

theorem tblPt_slots (K : WinCfg) {m : Nat} (h1 : 1 ≤ m) (h8 : m ≤ 8) :
    ∀ x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z], x ∈ winSlots K ∧ x ∈ winWs K := by
  intro x hx
  obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K h1 h8 x hx
  refine ⟨?_, winTbl_ws K hi⟩
  simp only [winSlots, List.mem_append]
  exact Or.inr (winTbl_mem K hi)

/-- The table's entries `[1 … m]P`, `E = [m]P`, and `rbx = 8 - m`: what holds
between the additions that build the table. -/
structure BuildInvE (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (m : Nat) (s : State) : Prop where
  inv : BuildInv K C base size P s₀ m s
  lt : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s.mem base x K.M.n < C.p
  rep : Rep C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z) (mul m P)
  rbx : s.gpr .rbx = BitVec.ofNat 64 (8 - m)

/-- `ZF` for `rbx = i`. -/
theorem cmpRbx_ok (s : State) {j i : Nat} (hi : i < 2 ^ 31) (hj : j < 2 ^ 63)
    (hb : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block [.alu .cmp .rbx (.imm (BitVec.ofNat 32 i))]) s fun t =>
      isa.eval .e t = some (decide (j = i)) ∧ Keeps [] s t := by
  obtain hse : BitVec.signExtend 64 (BitVec.ofNat 32 i) = BitVec.ofNat 64 i := by
    rw [BitVec.signExtend_eq_setWidth_of_msb_false (BitVec.msb_eq_false_iff_two_mul_lt.mpr (by
        rw [BitVec.toNat_ofNat]; omega_arith)),
      BitVec.setWidth_ofNat_of_le_of_lt (by decide) (by omega_arith)]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    Option.some.injEq, exists_eq_left', hb, hse]
  refine ⟨?_, fun r _ => rfl, rfl, rfl, rfl⟩
  show some (_ == 0) = _
  congr 1
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj]
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega_arith)]
  change _ = 0 ↔ _
  omega_arith

/-- The slots of entry `j` of the table, apart from those of entry `m ≠ j`. -/
theorem tbl_apart_entry {K : WinCfg} {j m : Nat} (hj1 : 1 ≤ j) (hj8 : j ≤ 8) (hm1 : 1 ≤ m) (hm8 : m ≤ 8)
    (hjm : j ≠ m) : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
      ∀ y ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z],
        x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := by
  intro x hx y hy
  obtain ⟨i, hi, rfl, hi₁, hi₂⟩ := tblPt_mem K hj1 hj8 x hx
  obtain ⟨i', hi', rfl, hi'₁, hi'₂⟩ := tblPt_mem K hm1 hm8 y hy
  exact winTbl_apart K (by omega_arith)

/-- What a copy from `D` into entry `m` of the table needs. -/
theorem copyD_tbl {K : WinCfg} {size : Nat} (hL : WinLay K size) {m : Nat} (hm1 : 1 ≤ m) (hm8 : m ≤ 8) :
    (∀ x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z, K.D.x, K.D.y, K.D.z], x + 8 * K.M.n ≤ size) ∧
    (∀ x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z],
      ∀ y ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z, K.D.x, K.D.y, K.D.z], x ≠ y →
        x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x) ∧
    (∀ x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z], x ∉ [K.D.x, K.D.y, K.D.z]) ∧
    ((K.tblPt m).x ≠ (K.tblPt m).y ∧ (K.tblPt m).x ≠ (K.tblPt m).z ∧ (K.tblPt m).y ≠ (K.tblPt m).z) := by
  obtain st := tblPt_slots K hm1 hm8
  obtain dO : ∀ y ∈ [K.D.x, K.D.y, K.D.z], y ∈ winOther K := by
    intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl <;> win_mem
  obtain sl : ∀ x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z, K.D.x, K.D.y, K.D.z], x ∈ winSlots K := by
    intro x hx
    rcases List.mem_append.mp (show x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z] ++
      [K.D.x, K.D.y, K.D.z] by simpa using hx) with h | h
    · exact (st x h).1
    · exact winOther_mem (dO x h)
  obtain td : ∀ x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z], ∀ y ∈ [K.D.x, K.D.y, K.D.z],
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := by
    intro x hx y hy
    obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K hm1 hm8 x hx
    exact (hL.tbl_apart (List.mem_append_right _ (dO y hy)) hi).symm
  obtain ne : (K.tblPt m).x ≠ (K.tblPt m).y ∧ (K.tblPt m).x ≠ (K.tblPt m).z ∧ (K.tblPt m).y ≠ (K.tblPt m).z := by
    rw [tblPt_x, tblPt_y, tblPt_z]
    exact ⟨hL.tbl_ne₂ (by omega_arith), hL.tbl_ne₂ (by omega_arith), hL.tbl_ne₂ (by omega_arith)⟩
  refine ⟨fun x hx => hL.lay.le x (sl x hx), fun x hx y hy hxy => ?_, fun x hx hy => ?_, ne⟩
  · rcases List.mem_append.mp (show y ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z] ++
      [K.D.x, K.D.y, K.D.z] by simpa using hy) with h | h
    · exact hL.apart₂ (st x hx).2 (st y h).2 hxy
    · exact td x hx y h
  · have := td x hx x hy
    have := hL.n0
    omega_arith

/-- `D` into entry `8 - i` of the table, for `rbx = i ≤ j ≤ 6`. -/
theorem storeEntry_ok {K : WinCfg} {size : Nat} (hL : WinLay K size) {base : Addr} {i : Nat} :
    ∀ (j : Nat) {s : State}, i ≤ j → j ≤ 6 → Scr s base size → s.gpr .rbx = BitVec.ofNat 64 i →
      WP isa (WinCfg.storeEntry K j) s fun t =>
        wordsVal t.mem base (K.tblPt (8 - i)).x K.M.n = wordsVal s.mem base K.D.x K.M.n ∧
        wordsVal t.mem base (K.tblPt (8 - i)).y K.M.n = wordsVal s.mem base K.D.y K.M.n ∧
        wordsVal t.mem base (K.tblPt (8 - i)).z K.M.n = wordsVal s.mem base K.D.z K.M.n ∧
        KeepRegs [.rax] s t ∧
        Unch base [((K.tblPt (8 - i)).x, 8 * K.M.n), ((K.tblPt (8 - i)).y, 8 * K.M.n),
          ((K.tblPt (8 - i)).z, 8 * K.M.n)] s.mem t.mem
  | 0, s, hi, _, hs, _ => by
    obtain rfl : i = 0 := by omega_arith
    rw [WinCfg.storeEntry]
    obtain ⟨a, c, d, e⟩ := copyD_tbl hL (m := 8) (by decide) (Nat.le_refl _)
    exact copyPt_ok hs a c d e
  | j + 1, s, hi, hj, hs, hb => by
    rw [WinCfg.storeEntry]
    refine WP.seq (WP.mono (cmpRbx_ok s (j := i) (i := j + 1) (by omega_arith) (by omega_arith) hb)
      fun t ⟨ev, kt⟩ => ?_)
    obtain hst := hs.of_keeps kt (by decide)
    have mt : t.mem = s.mem := kt.2.1
    obtain kt' : KeepRegs [.rax] s t := (Keeps.regs kt).mono fun r hr => by simp at hr
    refine WP.ite _ ev (fun he => ?_) (fun he => ?_)
    · obtain rfl : i = j + 1 := of_decide_eq_true he
      obtain ⟨a, c, d, e⟩ := copyD_tbl hL (m := 7 - j) (by omega_arith) (by omega_arith)
      rw [show 8 - (j + 1) = 7 - j by omega_arith]
      exact WP.mono (copyPt_ok hst a c d e) fun u ⟨e1, e2, e3, k, U⟩ =>
        ⟨by rw [e1, mt], by rw [e2, mt], by rw [e3, mt], kt'.trans k, by rw [← mt]; exact U⟩
    · have hne : i ≠ j + 1 := of_decide_eq_false he
      exact WP.mono (storeEntry_ok hL j (by omega_arith) (by omega_arith) hst ((kt.1 _ (by decide)).trans hb))
        fun u ⟨e1, e2, e3, k, U⟩ => ⟨by rw [e1, mt], by rw [e2, mt], by rw [e3, mt], kt'.trans k,
          by rw [← mt]; exact U⟩

/-- An entry of the table: `D = E + P` (`[m + 1]P`), `E = D`, and `D` into
entry `m + 1`. -/
theorem buildStep_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) {s₀ : State} (hF : WinFixed K C base s₀ P k) {m : Nat} (h1 : 1 ≤ m)
    (h7 : m ≤ 7) {s : State} (hI : BuildInvE K C base size P s₀ m s) :
    WP isa (WinCfg.buildStep K).inline s fun s' =>
      BuildInvE K C base size P s₀ (m + 1) s' ∧ s'.zf = some (decide (8 - (m + 1) = 0)) := by
  have hn := hI.inv.scr.nowrap
  rw [WinCfg.buildStep]
  refine WP.seq (WP.mono (decRbx_ok s (j := 8 - m) (by omega_using [h1, h7]) (by omega_using [h1, h7]) hI.rbx) fun s₁ ⟨x₁, k₁⟩ => ?_)
  obtain hs₁ := hI.inv.scr.of_keeps k₁ (by decide)
  have m₁ : s₁.mem = s.mem := k₁.2.1
  obtain tb : tmv C K.M.n base s₁ K.S.b3 = Fin.ofNat C.p C.b := by
    show toM _ _ _ = _; rw [m₁, winRo_val hL hI.inv.unch hn (by simp [winRo])]; exact hF.b
  obtain ro_lt : ∀ x ∈ winRo K, wordsVal s₁.mem base x K.M.n < C.p := fun x hx => by
    rw [m₁, winRo_val hL hI.inv.unch hn hx]; exact hF.ro_lt x hx
  obtain tP : ∀ x ∈ [K.P.x, K.P.y, K.P.z], tmv C K.M.n base s₁ x = tmv C K.M.n base s₀ x := by
    intro x hx; show toM _ _ _ = toM _ _ _; rw [m₁, winRo_val hL hI.inv.unch hn (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [winRo])]
  obtain hO : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.E K.P, x ∈ winSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact winOther_mem (List.mem_append_right _ hx)
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> win_mem
  obtain hlt : ∀ x ∈ rcbR K.S K.E K.P, wordsVal s₁.mem base x K.M.n < C.p := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ro_lt _ (by simp [winRo])
    · exact ro_lt _ (by simp [winRo])
    · rw [m₁]; exact hI.lt _ (by simp)
    · rw [m₁]; exact hI.lt _ (by simp)
    · rw [m₁]; exact hI.lt _ (by simp)
    · exact ro_lt _ (by simp [winRo])
    · exact ro_lt _ (by simp [winRo])
    · exact ro_lt _ (by simp [winRo])
  obtain hI₁ : Inv K.M base size C.p (· ∈ winSlots K) (rcbR K.S K.E K.P) (tmv C K.M.n base s₁) s₁ :=
    ⟨hs₁, by rw [m₁]; exact hI.inv.mod, fun x hx => hO x (List.mem_append_right _ hx), hlt,
      fun _ _ => rfl⟩
  obtain W := rcb3_ok hL.lay hp hL.rcbApart_EP hO hI₁ (fun x hx => hx)
  refine WP.seq ((WP.mono W fun s₂ ⟨k₂, I₂, v₂⟩ => ?_))
  -- `D` is `[m + 1]P`.
  obtain hox : K.D.x ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.E K.P := by simp
  obtain hoy : K.D.y ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.E K.P := by simp
  obtain hoz : K.D.z ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.E K.P := by simp
  obtain dlt : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s₂.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact I₂.lt _ hox
    · exact I₂.lt _ hoy
    · exact I₂.lt _ hoz
  obtain dRep : Rep C (tmv C K.M.n base s₂ K.D.x) (tmv C K.M.n base s₂ K.D.y) (tmv C K.M.n base s₂ K.D.z)
      (mul (m + 1) P) := by
    obtain hS : (tmv C K.M.n base s₂ K.D.x, tmv C K.M.n base s₂ K.D.y, tmv C K.M.n base s₂ K.D.z) =
        VG.Proof.Weierstrass.rcbAdd3 (tmv C K.M.n base s₁ K.S.b3)
          (tmv C K.M.n base s₁ K.E.x) (tmv C K.M.n base s₁ K.E.y) (tmv C K.M.n base s₁ K.E.z)
          (tmv C K.M.n base s₁ K.P.x) (tmv C K.M.n base s₁ K.P.y) (tmv C K.M.n base s₁ K.P.z) := by
      rw [← v₂]
      show (toM _ _ _, toM _ _ _, toM _ _ _) = _
      rw [I₂.val _ hox, I₂.val _ hoy, I₂.val _ hoz]
    rw [tb, tP K.P.x (by simp), tP K.P.y (by simp), tP K.P.z (by simp)] at hS
    obtain hE : Rep C (tmv C K.M.n base s₁ K.E.x) (tmv C K.M.n base s₁ K.E.y) (tmv C K.M.n base s₁ K.E.z)
        (mul m P) := by
      show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _; rw [m₁]; exact hI.rep
    obtain hPr : Rep C (tmv C K.M.n base s₀ K.P.x) (tmv C K.M.n base s₀ K.P.y)
        (tmv C K.M.n base s₀ K.P.z) (mul 1 P) := by rw [mul_one_pt]; exact hF.pt
    obtain hR := hC.add3 hM3 (hC.onCurve_mul hP m) (hC.onCurve_mul hP 1) hE hPr hS.symm
    rw [hC.add_mul_mul hP] at hR
    exact hR
  obtain hs₂ := k₂.scr hs₁
  have U₂ := k₂.unch
  -- `E = D`.
  obtain eO : ∀ y ∈ [K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z], y ∈ winOther K := by
    intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> win_mem
  obtain ⟨-, -, -, -, exy, exz, eyz, hED, -, -⟩ := hL.other_ne
  obtain hEd : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∉ [K.D.x, K.D.y, K.D.z] := by
    intro x hx hd
    refine hED x hx (List.mem_cons_of_mem _ ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> simp [rcbW]
  refine WP.seq (WP.mono (copyPt_ok hs₂ (o := K.E) (a := K.D) (n := K.M.n)
    (fun x hx => hL.lay.le x (winOther_mem (eO x hx)))
    (fun x hx y hy hxy => hL.apart₂ (winOther_ws K x (eO x (List.mem_append_left [K.D.x, K.D.y, K.D.z] hx)))
      (winOther_ws K y (eO y hy)) hxy) hEd ⟨exy, exz, eyz⟩) fun s₃ ⟨e1, e2, e3, k₃, U₃⟩ => ?_)
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  obtain x₃ : s₃.gpr .rbx = BitVec.ofNat 64 (7 - m) := by
    rw [k₃.gpr _ (by decide), k₂.gpr _ (rbx_not_clob _), x₁]; congr 1; omega_using [h1, h7]
  -- `D` into entry `m + 1`.
  refine WP.seq (WP.mono (storeEntry_ok hL (i := 7 - m) 6 (by omega_using [h1, h7]) (Nat.le_refl _) hs₃ x₃)
    fun s₄ ⟨f1, f2, f3, k₄, U₄⟩ => ?_)
  rw [show 8 - (7 - m) = m + 1 by omega_using [h1, h7]] at f1 f2 f3 U₄
  obtain hs₄ := hs₃.of_keepRegs k₄ (by decide)
  obtain x₄ : s₄.gpr .rbx = BitVec.ofNat 64 (7 - m) := by rw [k₄.gpr _ (by decide), x₃]
  refine WP.mono (testRbx_ok s₄ (j := 7 - m) (by omega_using [h1, h7]) x₄) fun s₅ ⟨z₅, k₅⟩ => ?_
  have m₅ : s₅.mem = s₄.mem := k₅.2.1
  obtain b64 : ∀ x ∈ winSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := hL.lay.le x hx; omega_using [this, hn]
  obtain sT := tblPt_slots K (m := m + 1) (by omega_using [h1, h7]) (by omega_using [h1, h7])
  -- `D` is kept by the copy into `E`, and `E` by the store.
  obtain dE : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s₃.mem base x K.M.n = wordsVal s₂.mem base x K.M.n := by
    intro x hx
    refine U₃.wordsVal (fun w hw => ?_) (b64 x (winOther_mem (eO x (List.mem_append_right [K.E.x, K.E.y, K.E.z] hx))))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    obtain hxE : ∀ y ∈ [K.E.x, K.E.y, K.E.z], x ≠ y := fun y hy hxy => hEd y hy (hxy ▸ hx)
    rcases hw with rfl | rfl | rfl <;> dsimp only <;>
      exact hL.apart₂ (winOther_ws K x (eO x (List.mem_append_right [K.E.x, K.E.y, K.E.z] hx)))
        (winOther_ws K _ (eO _ (by simp))) (hxE _ (by simp))
  obtain tE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s₄.mem base x K.M.n = wordsVal s₃.mem base x K.M.n := by
    intro x hx
    refine U₄.wordsVal (fun w hw => ?_) (b64 x (winOther_mem (eO x (List.mem_append_left [K.D.x, K.D.y, K.D.z] hx))))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    obtain hxo : x ∈ winRo K ++ winOther K := List.mem_append_right _ (eO x (List.mem_append_left [K.D.x, K.D.y, K.D.z] hx))
    rcases hw with rfl | rfl | rfl <;> dsimp only
    · obtain ⟨i, hi, e, -, -⟩ := tblPt_mem K (m := m + 1) (by omega_using [h1, h7]) (by omega_using [h1, h7]) _ (by simp : (K.tblPt (m + 1)).x ∈ _)
      rw [e]; exact hL.tbl_apart hxo hi
    · obtain ⟨i, hi, e, -, -⟩ := tblPt_mem K (m := m + 1) (by omega_using [h1, h7]) (by omega_using [h1, h7]) _ (by simp : (K.tblPt (m + 1)).y ∈ _)
      rw [e]; exact hL.tbl_apart hxo hi
    · obtain ⟨i, hi, e, -, -⟩ := tblPt_mem K (m := m + 1) (by omega_using [h1, h7]) (by omega_using [h1, h7]) _ (by simp : (K.tblPt (m + 1)).z ∈ _)
      rw [e]; exact hL.tbl_apart hxo hi
  obtain vEx : wordsVal s₅.mem base K.E.x K.M.n = wordsVal s₂.mem base K.D.x K.M.n := by
    rw [m₅, tE _ (by simp), e1]
  obtain vEy : wordsVal s₅.mem base K.E.y K.M.n = wordsVal s₂.mem base K.D.y K.M.n := by
    rw [m₅, tE _ (by simp), e2]
  obtain vEz : wordsVal s₅.mem base K.E.z K.M.n = wordsVal s₂.mem base K.D.z K.M.n := by
    rw [m₅, tE _ (by simp), e3]
  obtain vTx : wordsVal s₅.mem base (K.tblPt (m + 1)).x K.M.n = wordsVal s₂.mem base K.D.x K.M.n := by
    rw [m₅, f1, dE _ (by simp)]
  obtain vTy : wordsVal s₅.mem base (K.tblPt (m + 1)).y K.M.n = wordsVal s₂.mem base K.D.y K.M.n := by
    rw [m₅, f2, dE _ (by simp)]
  obtain vTz : wordsVal s₅.mem base (K.tblPt (m + 1)).z K.M.n = wordsVal s₂.mem base K.D.z K.M.n := by
    rw [m₅, f3, dE _ (by simp)]
  -- What the step writes: the addition's slots and temporary area, `E` and the entry.
  obtain UU := U₂.trans (U₃.trans U₄)
  obtain L2 : ∀ w ∈ (rcbW K.S K.D).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n)],
      w = (K.M.tmp, 8 * K.M.n) ∨ ∃ y ∈ winOther K, w = (y, 8 * K.M.n) := by
    intro w hw
    rcases List.mem_append.mp hw with h | h
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
      exact Or.inr ⟨y, List.mem_append_right _ hy, rfl⟩
    · exact Or.inl (List.mem_singleton.mp h)
  obtain L3 : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)],
      ∃ y ∈ winOther K, w = (y, 8 * K.M.n) := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact ⟨_, by win_mem, rfl⟩
    · exact ⟨_, by win_mem, rfl⟩
    · exact ⟨_, by win_mem, rfl⟩
  obtain L4 : ∀ w ∈ [((K.tblPt (m + 1)).x, 8 * K.M.n), ((K.tblPt (m + 1)).y, 8 * K.M.n),
      ((K.tblPt (m + 1)).z, 8 * K.M.n)], ∃ y ∈ [(K.tblPt (m + 1)).x, (K.tblPt (m + 1)).y,
        (K.tblPt (m + 1)).z], w = (y, 8 * K.M.n) := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact ⟨_, by simp, rfl⟩
    · exact ⟨_, by simp, rfl⟩
    · exact ⟨_, by simp, rfl⟩
  obtain split : ∀ {Q : Nat × Nat → Prop}, (w : Nat × Nat) →
      w ∈ (rcbW K.S K.D).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n)] ++
        ([(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] ++
          [((K.tblPt (m + 1)).x, 8 * K.M.n), ((K.tblPt (m + 1)).y, 8 * K.M.n),
            ((K.tblPt (m + 1)).z, 8 * K.M.n)]) →
      Q (K.M.tmp, 8 * K.M.n) → (∀ y ∈ winOther K, Q (y, 8 * K.M.n)) →
      (∀ y ∈ [(K.tblPt (m + 1)).x, (K.tblPt (m + 1)).y, (K.tblPt (m + 1)).z], Q (y, 8 * K.M.n)) → Q w := by
    intro Q w hw qt qo qT
    rcases List.mem_append.mp hw with h | h
    · rcases L2 w h with rfl | ⟨y, hy, rfl⟩
      · exact qt
      · exact qo y hy
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨y, hy, rfl⟩ := L3 w h; exact qo y hy
      · obtain ⟨y, hy, rfl⟩ := L4 w h; exact qT y hy
  obtain U : Unch base (winW K) s.mem s₅.mem := by
    rw [← m₁, m₅]
    refine UU.mono fun w hw => split w hw (by simp [winW])
      (fun y hy => by simp only [winW, List.mem_append, List.mem_map]; exact Or.inl ⟨y, winOther_ws K y hy, rfl⟩)
      (fun y hy => by simp only [winW, List.mem_append, List.mem_map]; exact Or.inl ⟨y, (sT y hy).2, rfl⟩)
  obtain keep : KeepRegs (powClob K.M.n) s s₅ := by
    obtain c1 : ∀ r ∈ [Reg.rax], r ∈ powClob K.M.n := by intro r hr; simp at hr; subst hr; simp [powClob, clob]
    exact (((Keeps.regs k₁).mono fun r hr => by simp at hr; simp [hr, powClob]).trans
      ((⟨fun r hr => k₂.gpr r fun h => hr (List.mem_cons_of_mem _ h), k₂.rd, k₂.wr⟩ :
        KeepRegs (powClob K.M.n) s₁ s₂).trans ((k₃.mono c1).trans ((k₄.mono c1).trans
          ((Keeps.regs k₅).mono fun r hr => by simp at hr)))))
  refine ⟨⟨⟨hs₄.of_keeps k₅ (by decide), hI.inv.keep.trans keep,
    (hI.inv.unch.trans U).mono fun w hw => by rcases List.mem_append.mp hw with h | h <;> exact h,
    hI.inv.mod.unch U (winW_mo hL hI.inv.mod) hn, fun j hj1 hjm => ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · rcases Nat.lt_or_ge j (m + 1) with hj | hj
    · -- An entry built before keeps its numbers.
      obtain Tj := hI.inv.tbl j hj1 (by omega_using [h1, h7, hj1, hjm, hj])
      obtain sj := tblPt_slots K (m := j) hj1 (by omega_using [h1, h7, hj1, hjm, hj])
      obtain e : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
          wordsVal s₅.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
        intro x hx
        rw [← m₁, m₅]
        obtain ⟨i, hi, hxi, -, -⟩ := tblPt_mem K hj1 (by omega_using [h1, h7, hj1, hjm, hj]) x hx
        refine UU.wordsVal (fun w hw => split (Q := fun w =>
            x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x) w hw
          (by rw [hxi]; exact hL.lay.tmp _ (by
            simp only [winSlots, List.mem_append]; exact Or.inr (winTbl_mem K hi)))
          (fun y hy => by rw [hxi]; exact (hL.tbl_apart (List.mem_append_right _ hy) hi).symm)
          (fun y hy => tbl_apart_entry (K := K) hj1 (by omega_using [h1, h7, hj1, hjm, hj]) (by omega_using [h1, h7, hj1, hjm, hj]) (by omega_using [h1, h7, hj1, hjm, hj]) (by omega_using [h1, h7, hj1, hjm, hj]) x hx
            y hy)) (b64 _ (sj _ hx).1)
      refine ⟨fun x hx => by rw [e x hx]; exact Tj.1 x hx, ?_⟩
      obtain ex : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
          tmv C K.M.n base s₅ x = tmv C K.M.n base s x := fun x hx => by
        show toM _ _ _ = toM _ _ _; rw [e x hx]
      rw [ex _ (by simp), ex _ (by simp), ex _ (by simp)]
      exact Tj.2
    · obtain rfl : j = m + 1 := by omega_using [hjm, hj]
      refine ⟨fun x hx => ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · rw [vTx]; exact dlt _ (by simp)
        · rw [vTy]; exact dlt _ (by simp)
        · rw [vTz]; exact dlt _ (by simp)
      · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
        rw [vTx, vTy, vTz]; exact dRep
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [vEx]; exact dlt _ (by simp)
    · rw [vEy]; exact dlt _ (by simp)
    · rw [vEz]; exact dlt _ (by simp)
  · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [vEx, vEy, vEz]; exact dRep
  · rw [k₅.1 _ (by decide), x₄]; congr 1; omega_using [h1, h7]
  · rw [z₅]; congr 1; simp only [decide_eq_decide]; omega_using [h1, h7]

/-- The table `[1 … 8]P`. -/
theorem build_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) {s : State} (hs : Scr s base size) (hM : ModOkW K.M size C.p s.mem base)
    (hF : WinFixed K C base s P k) :
    WP isa (WinCfg.build K).inline s (BuildInv K C base size P s 8) := by
  have hn := hs.nowrap
  obtain s1 := tblPt_slots K (m := 1) (Nat.le_refl _) (by omega_arith)
  obtain pRo : ∀ x ∈ [K.P.x, K.P.y, K.P.z], x ∈ winRo K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [winRo]
  obtain eO : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∈ winOther K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> win_mem
  obtain b64 : ∀ x ∈ winSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := hL.lay.le x hx; omega_arith
  -- `[1]P = P`.
  obtain tP : ∀ x ∈ [(K.tblPt 1).x, (K.tblPt 1).y, (K.tblPt 1).z], ∀ y ∈ [K.P.x, K.P.y, K.P.z],
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := by
    intro x hx y hy
    obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K (m := 1) (Nat.le_refl _) (by omega_arith) x hx
    exact (hL.tbl_apart (List.mem_append_left _ (pRo y hy)) hi).symm
  obtain ne1 : (K.tblPt 1).x ≠ (K.tblPt 1).y ∧ (K.tblPt 1).x ≠ (K.tblPt 1).z ∧
      (K.tblPt 1).y ≠ (K.tblPt 1).z := by
    rw [tblPt_x, tblPt_y, tblPt_z]
    exact ⟨hL.tbl_ne₂ (by omega_arith), hL.tbl_ne₂ (by omega_arith), hL.tbl_ne₂ (by omega_arith)⟩
  obtain slP : ∀ x ∈ [(K.tblPt 1).x, (K.tblPt 1).y, (K.tblPt 1).z, K.P.x, K.P.y, K.P.z], x ∈ winSlots K := by
    intro x hx
    rcases List.mem_append.mp (show x ∈ [(K.tblPt 1).x, (K.tblPt 1).y, (K.tblPt 1).z] ++
      [K.P.x, K.P.y, K.P.z] by simpa using hx) with h | h
    · exact (s1 x h).1
    · exact winRo_slots K x (pRo x h)
  rw [WinCfg.build]
  simp only [Code.inline]
  refine WP.seq ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (copyPt_ok hs (o := K.tblPt 1) (a := K.P) (n := K.M.n)
    (fun x hx => hL.lay.le x (slP x hx))
    (fun x hx y hy hxy => by
      rcases List.mem_append.mp (show y ∈ [(K.tblPt 1).x, (K.tblPt 1).y, (K.tblPt 1).z] ++
        [K.P.x, K.P.y, K.P.z] by simpa using hy) with h | h
      · exact hL.apart₂ (s1 x hx).2 (s1 y h).2 hxy
      · exact tP x hx y h)
    (fun x hx h => by have := tP x hx x h; have := hL.n0; omega_arith) ne1) fun s₁ ⟨a1, a2, a3, k₁, U₁⟩ => ?_
  obtain hs₁ := hs.of_keepRegs k₁ (by decide)
  -- `E = P`.
  obtain ⟨-, -, -, -, exy, exz, eyz, -⟩ := hL.other_ne
  obtain eP : ∀ x ∈ [K.E.x, K.E.y, K.E.z], ∀ y ∈ [K.P.x, K.P.y, K.P.z], x ≠ y := fun x hx y hy h =>
    hL.ro y (pRo y hy) (h ▸ eO x hx)
  obtain slE : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.P.x, K.P.y, K.P.z], x ∈ winSlots K := by
    intro x hx
    rcases List.mem_append.mp (show x ∈ [K.E.x, K.E.y, K.E.z] ++ [K.P.x, K.P.y, K.P.z] from hx) with h | h
    · exact winOther_mem (eO x h)
    · exact winRo_slots K x (pRo x h)
  rw [WP.block_append_iff]
  refine WP.mono (copyPt_ok hs₁ (o := K.E) (a := K.P) (n := K.M.n)
    (fun x hx => hL.lay.le x (slE x hx))
    (fun x hx y hy hxy => hL.lay.apart x y (slE x (List.mem_append_left [K.P.x, K.P.y, K.P.z] hx)) (slE y hy) hxy)
    (fun x hx h => eP x hx x h rfl) ⟨exy, exz, eyz⟩) fun s₂ ⟨c1, c2, c3, k₂, U₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (mov32Rbx_ok s₂ (j := 7) (by decide)) fun s₃ ⟨x₃, k₃⟩ => ?_
  -- The invariant for `[1]P`.
  obtain U : Unch base (winW K) s.mem s₃.mem := by
    rw [k₃.2.1]
    refine (U₁.trans U₂).mono fun w hw => ?_
    rcases List.mem_append.mp hw with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      simp only [winW, List.mem_append, List.mem_map]
      rcases h with rfl | rfl | rfl
      · exact Or.inl ⟨_, (s1 _ (by simp)).2, rfl⟩
      · exact Or.inl ⟨_, (s1 _ (by simp)).2, rfl⟩
      · exact Or.inl ⟨_, (s1 _ (by simp)).2, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      simp only [winW, List.mem_append, List.mem_map]
      rcases h with rfl | rfl | rfl
      · exact Or.inl ⟨_, winOther_ws K _ (eO _ (by simp)), rfl⟩
      · exact Or.inl ⟨_, winOther_ws K _ (eO _ (by simp)), rfl⟩
      · exact Or.inl ⟨_, winOther_ws K _ (eO _ (by simp)), rfl⟩
  have m₃ : s₃.mem = s₂.mem := k₃.2.1
  -- `[1]P` is kept by the copy into `E`.
  obtain kT : ∀ x ∈ [(K.tblPt 1).x, (K.tblPt 1).y, (K.tblPt 1).z],
      wordsVal s₃.mem base x K.M.n = wordsVal s₁.mem base x K.M.n := by
    intro x hx
    rw [m₃]
    refine U₂.wordsVal (fun w hw => ?_) (b64 x (s1 x hx).1)
    obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K (m := 1) (Nat.le_refl _) (by omega_arith) x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact (hL.tbl_apart (x := K.E.x) (List.mem_append_right _ (by win_mem)) hi).symm
    · exact (hL.tbl_apart (x := K.E.y) (List.mem_append_right _ (by win_mem)) hi).symm
    · exact (hL.tbl_apart (x := K.E.z) (List.mem_append_right _ (by win_mem)) hi).symm
  obtain kP : ∀ x ∈ [K.P.x, K.P.y, K.P.z], wordsVal s₁.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
    intro x hx
    refine U₁.wordsVal (fun w hw => ?_) (b64 x (winRo_slots K x (pRo x hx)))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;>
      exact (tP _ (by simp) x hx).symm
  obtain c1' : ∀ r ∈ [Reg.rax], r ∈ powClob K.M.n := by intro r hr; simp at hr; subst hr; simp [powClob, clob]
  obtain I₁ : BuildInvE K C base size P s 1 s₃ := by
    refine ⟨⟨hs₂.of_keeps k₃ (by decide), ((k₁.mono c1').trans (k₂.mono c1')).trans
      ((Keeps.regs k₃).mono fun r hr => by simp at hr; simp [hr, powClob]), U, hM.unch U (winW_mo hL hM) hn,
      fun j hj1 hj => ?_⟩, fun x hx => ?_, ?_, by rw [x₃]⟩
    · obtain rfl : j = 1 := by omega_arith
      refine ⟨fun x hx => ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · rw [kT _ (by simp), a1]; exact hF.ro_lt _ (by simp [winRo])
        · rw [kT _ (by simp), a2]; exact hF.ro_lt _ (by simp [winRo])
        · rw [kT _ (by simp), a3]; exact hF.ro_lt _ (by simp [winRo])
      · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
        rw [kT _ (by simp), kT _ (by simp), kT _ (by simp), a1, a2, a3, mul_one_pt]
        exact hF.pt
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rw [m₃]
      rcases hx with rfl | rfl | rfl
      · rw [c1, kP _ (by simp)]; exact hF.ro_lt _ (by simp [winRo])
      · rw [c2, kP _ (by simp)]; exact hF.ro_lt _ (by simp [winRo])
      · rw [c3, kP _ (by simp)]; exact hF.ro_lt _ (by simp [winRo])
    · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
      rw [m₃, c1, c2, c3, kP _ (by simp), kP _ (by simp), kP _ (by simp), mul_one_pt]
      exact hF.pt
  exact countLoop_ok (Inv := fun j t => BuildInvE K C base size P s (8 - j) t) (n := 7)
    (fun j t h1 h2 hi => WP.mono (buildStep_ok hL hp hC hM3 hP hF (m := 8 - j) (by omega_arith) (by omega_arith) hi)
      fun u ⟨I, z⟩ => ⟨by rw [show 8 - (j - 1) = 8 - j + 1 by omega_arith]; exact I,
        by rw [z]; congr 1; simp only [decide_eq_decide]; omega_arith⟩)
    (fun t hi => hi.inv) (by decide) I₁

end VG.Proof.Weierstrass.X86_64

end

end

/-!
# The window method on x86-64: the entry of a digit

Iteration `j` reads digit `j` as the comb reads its digits (`digit_ok` for
windows of 4 bits: `combWin 4 k j` is `nib k j`), selects the entry of its
magnitude `a` from the table at `rdx = rdi + tbl` (`winSelSetup_ok`) as the
comb selects one (`selLoad_ok`), its `⌈3 n / 2⌉` 16-byte pieces stored to `E`
(the last over the entry's last 16 bytes), so that `E` holds the point `[a]P`'s three coordinates, sets `y = R` for `a = 0`
(`ySel0_ok`, so that `E` is `(0 : 1 : 0)`), and negates `y` for a negative
digit as the comb does (`winEntry_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

theorem combWin_four (k i : Nat) : combWin 4 k i = nib k i := by
  unfold combWin nib; rw [Nat.pow_mul]

/-- `rdx = rdi + tbl`. -/
theorem winSelSetup_ok (K : WinCfg) (s : State) {base : Addr} (hd : s.gpr .rdi = base)
    (ht : K.tbl < 2 ^ 31) :
    WP isa (.block (WinCfg.selSetup K)) s fun t => t.gpr .rdx = base + BitVec.ofNat 64 K.tbl ∧
      Keeps [.rdx] s t ∧ t.xmm = s.xmm := by
  crun [WinCfg.selSetup, imm32_sext ht, hd, RegUpd.xmm_setReg, RegUpd.xmm_arithFlags]
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `y |= R` if the magnitude `r8 = a` is zero, word by word. -/
theorem ySel0_ok (K : WinCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (ha : a < 2 ^ 64) (h8 : s.gpr .r8 = BitVec.ofNat 64 a) (hy : K.E.y + 8 * K.M.n ≤ size) :
    WP isa (.block (WinCfg.ySel0 K)) s fun t =>
      (∀ i < K.M.n, word t.mem base (K.E.y + 8 * i) =
        (wordOf K.one i &&& bmask (decide (a = 0))) ||| word s.mem base (K.E.y + 8 * i)) ∧
      KeepRegs [.rax, .rcx] s t ∧ Outside base K.E.y (8 * K.M.n) s.mem t.mem := by
  unfold WinCfg.ySel0
  rw [WP.block_append_iff]
  refine WP.mono (isZero_ok s ha h8) fun s₁ ⟨c₁, k₁, _⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.mono (orSteps_ok K.M.n s₁ hs₁ c₁ hy) fun t ⟨e₂, k₂, O₂, _⟩ =>
    ⟨fun i hi => by rw [e₂ i hi, k₁.2.1], ((Keeps.regs k₁).mono (by decide)).trans (k₂.mono (by decide)),
      by rw [← k₁.2.1]; exact O₂⟩

/-- A change within `[o, o + 3 k)`, as within its three thirds. -/
theorem Unch.split3 {base : Addr} {o k : Nat} {m m' : Mem} (h : Unch base [(o, 3 * k)] m m') :
    Unch base [(o, k), (o + k, k), (o + 2 * k, k)] m m' := fun x hx => h x fun w hw => by
  simp only [List.mem_singleton] at hw; subst hw
  obtain h1 := hx _ (List.mem_cons_self ..)
  obtain h2 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  obtain h3 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  dsimp only at h1 h2 h3 ⊢; omega_using [h1, h2, h3]

/-- What the selection leaves: in `E`, entry `a`'s coordinates if `a ≥ 1`,
else `(0, R, 0)`. -/
structure WinSelPost (K : WinCfg) (base : Addr) (s : State) (a : Nat) (t : State) : Prop where
  x : wordsVal t.mem base K.E.x K.M.n = if 1 ≤ a then wordsVal s.mem base (K.tblPt a).x K.M.n else 0
  y : wordsVal t.mem base K.E.y K.M.n = if 1 ≤ a then wordsVal s.mem base (K.tblPt a).y K.M.n else K.one
  z : wordsVal t.mem base K.E.z K.M.n = if 1 ≤ a then wordsVal s.mem base (K.tblPt a).z K.M.n else 0
  keep : KeepRegs [.rax, .rcx, .rdx] s t
  unch : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] s.mem t.mem

/-- The entry of the magnitude `r8 = a ≤ 8` into `E`. -/
theorem winSelect_ok (K : WinCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hn : 1 ≤ K.M.n ∧ K.M.n ≤ 9) (ht : K.tbl < 2 ^ 31)
    (htb : K.tbl + 192 * K.M.n ≤ size) (hexy : K.E.y = K.E.x + 8 * K.M.n)
    (hexz : K.E.z = K.E.x + 16 * K.M.n) (hz : K.E.z + 8 * K.M.n ≤ size) (hone : K.one < 2 ^ (64 * K.M.n))
    {a : Nat} (h8 : s.gpr .r8 = BitVec.ofNat 64 a) (ha : a ≤ 8) :
    WP isa (.block (WinCfg.select K)) s (WinSelPost K base s a) := by
  have hnw := hs.nowrap
  have hnp : WinCfg.np K = (3 * K.M.n + 1) / 2 := rfl
  obtain hpo : ∀ c, WinCfg.po K c = if c + 1 < WinCfg.np K then 16 * c else 24 * K.M.n - 16 := fun _ => rfl
  obtain hpo16 : ∀ c < WinCfg.np K, WinCfg.po K c + 16 ≤ 24 * K.M.n := fun c hc => by
    rw [hpo]; rw [hnp] at hc ⊢; split <;> omega_arith
  obtain hlast : WinCfg.po K (WinCfg.np K - 1) = 24 * K.M.n - 16 := by
    rw [hpo, ite_eq_right_of_eq_false _ _ (eq_false (by omega_using []))]
  rw [WinCfg.select, List.append_assoc, WP.block_append_iff]
  refine WP.mono (winSelSetup_ok K s hs.rdi ht) fun s₁ ⟨x₁, k₁, _⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  obtain h8₁ : s₁.gpr .r8 = BitVec.ofNat 64 a := by rw [k₁.1 _ (by decide), h8]
  rw [WP.block_append_iff, selPassAt, WP.block_append_iff]
  -- Every piece is within its entry, and the entries within the table.
  obtain hr : ∀ e < 8, ∀ c < WinCfg.np K, InRegions (s₁.rd ++ s₁.wr)
      (base + BitVec.ofNat 64 K.tbl + BitVec.ofNat 64 (24 * K.M.n * e + WinCfg.po K c)) 16 := by
    intro e he c hc
    rw [Offset.add_add]
    have := hpo16 c hc
    have := Nat.mul_le_mul_left (24 * K.M.n) (show e + 1 ≤ 8 by omega_using [he])
    rw [Nat.mul_succ] at this
    exact ⟨_, List.mem_append_right _ (k₁.2.2.2 ▸ hs.wr), hs.contains (by omega_arith) (by decide)⟩
  refine WP.mono (selLoad_ok (st := 24 * K.M.n) (H := 8) (by rw [hnp]; omega_using [hn]) (by decide) (by omega_using [ha])
    h8₁ x₁ hr) fun s₂l ⟨a₂, k₂l, m₂l⟩ => ?_
  obtain hs₂l : Scr s₂l base size := hs₁.of_keepRegs k₂l (by decide)
  -- The pieces but the last are `16` bytes apart; the last ends the entry.
  rw [show WinCfg.np K = (WinCfg.np K - 1) + 1 by rw [hnp]; omega_using [hn], List.range_succ, List.map_append,
    List.map_singleton, WP.block_append_iff,
    List.map_congr_left (l := List.range (WinCfg.np K - 1))
      (g := fun c => Instr.movdquStore (sc (K.E.x + 16 * c)) (selAcc c)) fun c hc => by
        rw [List.mem_range] at hc; rw [hpo, ite_eq_left_of_eq_true _ _ (eq_true (by omega_using [hc]))]]
  refine WP.mono (storeAcc_ok (o := K.E.x) (WinCfg.np K - 1) s₂l hs₂l (by rw [hnp]; omega_using [hexz, hz]))
    fun s₂f ⟨a₃, O₃f, g₃, r₃, w₃, x₃⟩ => ?_
  obtain hs₂f : Scr s₂f base size := ⟨by rw [g₃]; exact hs₂l.rdi, by rw [w₃]; exact hs₂l.wr, hnw⟩
  refine WP.mono (store128_ok (d := K.E.x + WinCfg.po K (WinCfg.np K - 1)) s₂f hs₂f
    (by rw [hlast]; omega_using [hn, hexz, hz]) _) fun s₂ ⟨a₄, O₄, g₄, r₄, w₄, x₄⟩ => ?_
  obtain k₂ : KeepRegs [.rcx] s₁ s₂ :=
    ⟨fun r hr => by rw [g₄, g₃, k₂l.gpr r hr], by rw [r₄, r₃, k₂l.rd], by rw [w₄, w₃, k₂l.wr]⟩
  obtain O₂ : Outside base K.E.x (24 * K.M.n) s₁.mem s₂.mem := by
    rw [← m₂l]
    exact (O₃f.mono (Nat.le_refl _) (by rw [hnp]; omega_using [])).trans (O₄.mono (by omega_using []) (by rw [hlast]; omega_using [hn]))
  obtain hs₂ : Scr s₂ base size := hs₁.of_keepRegs k₂ (by decide)
  obtain h8₂ : s₂.gpr .r8 = BitVec.ofNat 64 a := by rw [k₂.gpr _ (by decide), h8₁]
  refine WP.mono (ySel0_ok K hs₂ (by omega_using [ha]) h8₂ (by omega_using [hexy, hexz, hz])) fun t ⟨ey, k₃, O₃⟩ => ?_
  obtain hX : ∀ d, word s.mem (base + BitVec.ofNat 64 K.tbl) d = word s.mem base (K.tbl + d) := fun d => by
    rw [Mont.word, Mont.word, off, off, Offset.add_add]
  -- The words of `E`, from the table at `s`.
  obtain hW : ∀ i < 3 * K.M.n, word s₂.mem base (K.E.x + 8 * i) =
      if 1 ≤ a ∧ a ≤ 8 then word s.mem base (K.tbl + 24 * K.M.n * (a - 1) + 8 * i) else 0 := by
    intro i hi
    obtain e₂ : ∀ c < WinCfg.np K, s₂l.xmm (selAcc c) =
        accVal s.mem (base + BitVec.ofNat 64 K.tbl) (24 * K.M.n) (WinCfg.po K) a 8 c := fun c hc => by
      rw [a₂ c hc, k₁.2.1]
    by_cases hi2 : 3 * K.M.n - 2 ≤ i
    · have h := a₄
      rw [x₃, e₂ _ (by rw [hnp]; omega_using [hi])] at h
      obtain w := accVal_word1 (q := i - (3 * K.M.n - 2)) h (by omega_using [hi])
      rw [hlast, show K.E.x + (24 * K.M.n - 16) + 8 * (i - (3 * K.M.n - 2)) = K.E.x + 8 * i by omega_using [hi2],
        hX] at w
      rw [w, show K.tbl + (24 * K.M.n * (a - 1) + (24 * K.M.n - 16) + 8 * (i - (3 * K.M.n - 2))) =
        K.tbl + 24 * K.M.n * (a - 1) + 8 * i by omega_using [hi2]]
    · have hc : i / 2 + 1 < WinCfg.np K := by rw [hnp]; omega_using [hi2]
      obtain h := a₃ (i / 2) (by omega_using [hc])
      rw [e₂ _ (by omega_using [hc])] at h
      obtain w := accVal_word1 (q := i % 2) h (Nat.mod_lt _ (by decide))
      rw [hpo, ite_eq_left_of_eq_true _ _ (eq_true hc), show K.E.x + 16 * (i / 2) + 8 * (i % 2) = K.E.x + 8 * i by omega_using [], hX] at w
      rw [O₄.word (by rw [hlast]; omega_using [hi2]) (by omega_using [hexz, hz, hnw, hi2]), w,
        show K.tbl + (24 * K.M.n * (a - 1) + 16 * (i / 2) + 8 * (i % 2)) =
          K.tbl + 24 * K.M.n * (a - 1) + 8 * i by omega_using []]
  obtain hxw : ∀ i < K.M.n, word t.mem base (K.E.x + 8 * i) = word s₂.mem base (K.E.x + 8 * i) := fun i hi =>
    O₃.word (by omega_using [hexy, hi]) (by omega_using [hexz, hz, hnw, hi])
  obtain hzw : ∀ i < K.M.n, word t.mem base (K.E.z + 8 * i) = word s₂.mem base (K.E.z + 8 * i) := fun i hi =>
    O₃.word (by omega_using [hexy, hexz]) (by omega_using [hz, hnw, hi])
  have tx : (K.tblPt a).x = K.tbl + 24 * K.M.n * (a - 1) := rfl
  have ty : (K.tblPt a).y = K.tbl + 24 * K.M.n * (a - 1) + 8 * K.M.n := rfl
  have tz : (K.tblPt a).z = K.tbl + 24 * K.M.n * (a - 1) + 16 * K.M.n := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_cases h1 : 1 ≤ a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), tx]
      exact wordsVal_congr₂ _ _ _ fun i hi => by
        rw [hxw i hi, hW i (by omega_using [hi]), ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, ha⟩)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      exact wordsVal_zeros fun i hi => by
        rw [hxw i hi, hW i (by omega_using [hi]), ite_eq_right_of_eq_false _ _ (eq_false (by omega_using [h1]))]
  · have hyw : ∀ i < K.M.n, word s₂.mem base (K.E.y + 8 * i) =
        if 1 ≤ a ∧ a ≤ 8 then word s.mem base (K.tbl + 24 * K.M.n * (a - 1) + 8 * K.M.n + 8 * i) else 0 :=
      fun i hi => by
        rw [hexy, show K.E.x + 8 * K.M.n + 8 * i = K.E.x + 8 * (K.M.n + i) by omega_using [], hW _ (by omega_using [hi]),
          show K.tbl + 24 * K.M.n * (a - 1) + 8 * (K.M.n + i) =
            K.tbl + 24 * K.M.n * (a - 1) + 8 * K.M.n + 8 * i by omega_using []]
    by_cases h1 : 1 ≤ a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ty]
      exact wordsVal_congr₂ _ _ _ fun i hi => by
        rw [ey i hi, hyw i hi, ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, ha⟩),
          decide_eq_false (show ¬ a = 0 by omega_using [h1]), bv_and_or_false]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      exact wordsVal_wordOf hone fun i hi => by
        rw [ey i hi, hyw i hi, ite_eq_right_of_eq_false _ _ (eq_false (by omega_using [h1])),
          decide_eq_true (show a = 0 by omega_using [h1]), bv_and_or_true, bv_or_zero]
  · have hzw' : ∀ i < K.M.n, word s₂.mem base (K.E.z + 8 * i) =
        if 1 ≤ a ∧ a ≤ 8 then word s.mem base (K.tbl + 24 * K.M.n * (a - 1) + 16 * K.M.n + 8 * i) else 0 :=
      fun i hi => by
        rw [hexz, show K.E.x + 16 * K.M.n + 8 * i = K.E.x + 8 * (2 * K.M.n + i) by omega_using [], hW _ (by omega_using [hi]),
          show K.tbl + 24 * K.M.n * (a - 1) + 8 * (2 * K.M.n + i) =
            K.tbl + 24 * K.M.n * (a - 1) + 16 * K.M.n + 8 * i by omega_using []]
    by_cases h1 : 1 ≤ a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), tz]
      exact wordsVal_congr₂ _ _ _ fun i hi => by
        rw [hzw i hi, hzw' i hi, ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, ha⟩)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      exact wordsVal_zeros fun i hi => by
        rw [hzw i hi, hzw' i hi, ite_eq_right_of_eq_false _ _ (eq_false (by omega_using [h1]))]
  · exact ((Keeps.regs k₁).mono (by decide)).trans ((k₂.mono (by decide)).trans (k₃.mono (by decide)))
  · rw [← k₁.2.1]
    obtain U₂ : Unch base [(K.E.x, 3 * (8 * K.M.n))] s₁.mem s₂.mem := by
      have := O₂.unch
      rwa [show 24 * K.M.n = 3 * (8 * K.M.n) by omega_using []] at this
    refine ((Unch.split3 U₂).trans O₃.unch).mono fun w hw => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with (rfl | rfl | rfl) | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (Prod.ext (by dsimp only; omega_using [hexy]) rfl))
    · exact Or.inr (Or.inr (Prod.ext (by dsimp only; omega_using [hexz]) rfl))
    · exact Or.inr (Or.inl rfl)

/-- After the selection and the negation: `E` represents the point of digit
`i` (by `Rp`), and only `E`, `-y` and the temporary area changed. -/
structure EntryPostR (K : WinCfg) (C : Curve) (base : Addr) (size : Nat)
    (Rp : Fe C → Fe C → Fe C → Point C → Prop) (P : Point C) (k i : Nat)
    (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (clob K.M.n) s s'
  unch : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n),
    (K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)] s.mem s'.mem
  lt : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s'.mem base x K.M.n < C.p
  rep : Rp (tmv C K.M.n base s' K.E.x) (tmv C K.M.n base s' K.E.y) (tmv C K.M.n base s' K.E.z)
    (winPt C P k i)

/-- `EntryPostR` in projective coordinates. -/
abbrev EntryPostW (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (k i : Nat)
    (s s' : State) : Prop := EntryPostR K C base size (Rep C) P k i s s'

theorem winE_mem {K : WinCfg} : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], x ∈ winOther K := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> win_mem

theorem mul_zero_pt' {C : Curve} (P : Point C) : mul 0 P = .infinity := by
  rw [Spec.Weierstrass.mul]; simp

/-- The layout facts the entry needs: `E`'s three slots adjacent, the table's
address an immediate, and at most nine words (the selection keeps an entry's
16-byte pieces in fourteen registers). -/
structure WinX (K : WinCfg) (size : Nat) : Prop where
  n : 1 ≤ K.M.n ∧ K.M.n ≤ 9
  tbl : K.tbl < 2 ^ 31
  exy : K.E.y = K.E.x + 8 * K.M.n
  exz : K.E.z = K.E.x + 16 * K.M.n

/-- The digit's magnitude, its entry from the table, and its `y` negated for a
negative digit. -/
theorem winEntryR_ok {K : WinCfg} {C : Curve} {base : Addr} {size k i : Nat} (hL : WinLay K size)
    (hX : WinX K size) {Rp : Fe C → Fe C → Fe C → Point C → Prop} (hRp0 : Rp 0 1 0 .infinity)
    (hRpNeg : ∀ {X Y Z : Fe C} {Q : Point C}, Rp X Y Z Q → Rp X (-Y) Z (negPt Q))
    {P : Point C} (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s : State} (hs : Scr s base size)
    (hM : ModOkW K.M size C.p s.mem base) (hi : i < K.J) (hx : s.gpr .rbx = BitVec.ofNat 64 i)
    (hbits : ∀ t < 4 * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0)
    (hz : wordsVal s.mem base K.zero K.M.n = 0) (hT : TblOkR K C base Rp P 8 s) :
    WP isa (.block ((WinCfg.tc K).digit ++ WinCfg.select K)) s fun s₂ =>
      WP isa (.block (WinCfg.tc K).negY) s₂ (EntryPostR K C base size Rp P k i s) := by
  have hn := hs.nowrap
  have hJ := hL.J
  have h0 := hL.n0
  obtain hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hone_lt
  obtain ⟨-, -, -, -, exy, exz, eyz, hEo, -, -⟩ := hL.other_ne
  obtain wE : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], x ∈ winWs K := fun x hx => winOther_ws K x (winE_mem x hx)
  obtain le : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], x + 8 * K.M.n ≤ size := fun x hx =>
    hL.lay.le x (winOther_mem (winE_mem x hx))
  obtain tmp : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], x + 8 * K.M.n ≤ K.M.tmp ∨ K.M.tmp + 8 * K.M.n ≤ x :=
    fun x hx => hL.lay.tmp x (winOther_mem (winE_mem x hx))
  obtain mo : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], x + 8 * K.M.n ≤ K.M.mo ∨ K.M.mo + 8 * K.M.n ≤ x :=
    fun x hx => hL.lay.mo x (winOther_mem (winE_mem x hx))
  obtain neN : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ≠ K.neg := fun x hx e => hEo x hx (by rw [e]; simp)
  obtain yneg := hL.apart₂ (wE K.E.y (by simp)) (wE K.neg (by simp)) (neN _ (by simp))
  obtain xneg := hL.apart₂ (wE K.E.x (by simp)) (wE K.neg (by simp)) (neN _ (by simp))
  obtain zneg := hL.apart₂ (wE K.E.z (by simp)) (wE K.neg (by simp)) (neN _ (by simp))
  obtain xy := hL.apart₂ (wE K.E.x (by simp)) (wE K.E.y (by simp)) exy
  obtain xz := hL.apart₂ (wE K.E.x (by simp)) (wE K.E.z (by simp)) exz
  obtain yz := hL.apart₂ (wE K.E.y (by simp)) (wE K.E.z (by simp)) eyz
  have hbs := hL.bits
  obtain hEx := le K.E.x (by simp)
  obtain hEy := le K.E.y (by simp)
  obtain hEz := le K.E.z (by simp)
  obtain hneg := le K.neg (by simp)
  obtain hzs : K.zero ∈ winSlots K := winRo_slots K _ (by simp [winRo])
  obtain hzl := hL.lay.le K.zero hzs
  -- The table's last slot bounds it.
  obtain htb : K.tbl + 192 * K.M.n ≤ size := by
    have := hL.lay.le _ (show K.tbl + 8 * K.M.n * 23 ∈ winSlots K by
      simp only [winSlots, List.mem_append]; exact Or.inr (winTbl_mem K (by decide)))
    omega_using [this]
  obtain hwi : 4 * i + 4 ≤ 4 * K.J := by omega_using [hi]
  rw [WP.block_append_iff]
  refine WP.mono (digit_ok (WinCfg.tc K) hs (k := k) (j := i) (N := 4 * K.J) (by show 1 ≤ 4; decide)
    (by show 4 < 9; decide) hwi
    hL.bits hx hbits) fun s₁ ⟨_, m₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  obtain hx₁ : s₁.gpr .rbx = BitVec.ofNat 64 i := by rw [k₁.1 _ (by decide), hx]
  obtain hw4 : combWin 4 k i = nib k i := combWin_four k i
  obtain hmag : magH 8 (nib k i) ≤ 8 := magH_le (by have := nib_lt k i; omega_using [this])
  obtain m₁' : s₁.gpr .r8 = BitVec.ofNat 64 (magH 8 (nib k i)) := by
    rw [m₁, show (WinCfg.tc K).H = 8 from rfl, show (WinCfg.tc K).w = 4 from rfl, hw4]
  refine WP.mono (winSelect_ok K hs₁ hX.n hX.tbl htb hX.exy hX.exz hEz (Nat.lt_trans hone_lt hpn) m₁' hmag)
    fun s₂ S₂ => ?_
  obtain ⟨ex₂, ey₂, ez₂, k₂, U₂⟩ := S₂
  rw [k₁.2.1] at ex₂ ey₂ ez₂ U₂
  generalize ha : magH 8 (nib k i) = a at ex₂ ey₂ ez₂ hmag
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  obtain hmoE : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)],
      K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo := fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · have := mo K.E.x (by simp); dsimp only; omega_using [this]
    · have := mo K.E.y (by simp); dsimp only; omega_using [this]
    · have := mo K.E.z (by simp); dsimp only; omega_using [this]
  obtain hM₂ : ModOkW K.M size C.p s₂.mem base := hM.unch U₂ hmoE hn
  obtain hz₂ : wordsVal s₂.mem base K.zero K.M.n = 0 := by
    obtain hzW := hL.ro_w (x := K.zero) (by simp [winRo])
    rw [U₂.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;>
        exact hzW _ (List.mem_append_left _ (List.mem_map_of_mem (wE _ (by simp))))) (by omega_using [hn, hzl]), hz]
  -- The entry's numbers, below `p`.
  obtain Ta := fun (h : 1 ≤ a) => hT a h hmag
  obtain hEy₂ : wordsVal s₂.mem base K.E.y K.M.n < C.p := by
    rw [ey₂]; split
    · exact (Ta ‹_›).1 _ (by simp)
    · exact hone_lt
  -- The negation.
  rw [TCombCfg.negY, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sub_ok hs₂ hM₂ (o := K.neg) (a := K.zero) (b := K.E.y) hneg hzl hEy
    (tmp _ (by simp)) (hL.lay.tmp _ hzs) (tmp _ (by simp)) (mo _ (by simp))
    (by rw [hz₂]; exact hp0) hEy₂) fun s₃ ⟨k₃, e₃⟩ => ?_
  obtain hs₃ : Scr s₃ base size := k₃.scr hs₂
  have U₃ := k₃.unch
  obtain hx₃ : s₃.gpr .rbx = BitVec.ofNat 64 i := by
    rw [k₃.gpr _ (rbx_not_clob _), k₂.gpr _ (by decide), hx₁]
  have hbW : ∀ w ∈ winW K, K.bits + 4 * K.J ≤ w.1 ∨ w.1 + w.2 ≤ K.bits := hL.bits_w
  obtain hbits₃ : ∀ t < 4 * K.J, s₃.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 := by
    intro t ht
    obtain hW : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], K.bits + 4 * K.J ≤ x ∨ x + 8 * K.M.n ≤ K.bits := fun x hx =>
      hbW _ (List.mem_append_left _ (List.mem_map_of_mem (wE x hx)))
    obtain hT' := hbW _ (List.mem_append_right _ (List.mem_singleton_self (K.M.tmp, 8 * K.M.n)))
    rw [U₃.byte (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · have := hW K.neg (by simp); dsimp only; omega_using [ht, this]
        · dsimp only at hT' ⊢; omega_using [ht, hT']) (by omega_using [hn, hbs, ht]),
      U₂.byte (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · have := hW K.E.x (by simp); dsimp only; omega_using [ht, this]
        · have := hW K.E.y (by simp); dsimp only; omega_using [ht, this]
        · have := hW K.E.z (by simp); dsimp only; omega_using [ht, this]) (by omega_using [hn, hbs, ht])]
    exact hbits t ht
  rw [WP.block_append_iff]
  refine WP.mono (signMask_ok (WinCfg.tc K) hs₃ (k := k) (j := i) (N := 4 * K.J) (by show 1 ≤ 4; decide)
    (by show 4 < 2 ^ 31; decide) hwi
    hL.bits hx₃ hbits₃) fun s₄ ⟨x₄, k₄⟩ => ?_
  obtain hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.mono (sel_ok (decide (combWin (WinCfg.tc K).w k i < 2 ^ ((WinCfg.tc K).w - 1))) K.M.n hs₄ x₄
    (o := K.E.y) (a := K.E.y) (b := K.neg) hEy hEy hneg (Or.inl (Nat.le_refl _)) (by omega_using [yneg]))
    fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  rw [show (WinCfg.tc K).w = 4 from rfl, hw4] at e₅
  -- The values.
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  obtain vx : wordsVal s₅.mem base K.E.x K.M.n = wordsVal s₂.mem base K.E.x K.M.n := by
    rw [O₅.wordsVal (by omega_using [xy]) (by omega_using [hn, hEx]), m₄, U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · dsimp only; omega_using [xneg]
      · have := tmp K.E.x (by simp); dsimp only; omega_using [this]) (by omega_using [hn, hEx])]
  obtain vz : wordsVal s₅.mem base K.E.z K.M.n = wordsVal s₂.mem base K.E.z K.M.n := by
    rw [O₅.wordsVal (by omega_using [yz]) (by omega_using [hn, hEz]), m₄, U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · dsimp only; omega_using [zneg]
      · have := tmp K.E.z (by simp); dsimp only; omega_using [this]) (by omega_using [hn, hEz])]
  obtain vy₃ : wordsVal s₃.mem base K.E.y K.M.n = wordsVal s₂.mem base K.E.y K.M.n :=
    U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · dsimp only; omega_using [yneg]
      · have := tmp K.E.y (by simp); dsimp only; omega_using [this]) (by omega_using [hn, hEy])
  obtain vy : wordsVal s₅.mem base K.E.y K.M.n = if decide (nib k i < 2 ^ (4 - 1)) then
      (0 + C.p - wordsVal s₂.mem base K.E.y K.M.n) % C.p else wordsVal s₂.mem base K.E.y K.M.n := by
    rw [e₅, m₄, e₃, hz₂, vy₃]
  -- The point the selected entry represents: `[a]P` (`O` for `0`).
  obtain hR : Rp (tmv C K.M.n base s₂ K.E.x) (tmv C K.M.n base s₂ K.E.y) (tmv C K.M.n base s₂ K.E.z)
      (mul a P) := by
    show Rp (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [ex₂, ey₂, ez₂]
    by_cases h1 : 1 ≤ a
    · simp only [h1, ↓reduceIte]
      exact (Ta h1).2
    · have h0 : a = 0 := by omega_using [h1]
      subst h0
      simp only [show ¬ 1 ≤ 0 by omega_using [], ↓reduceIte, toM_zero, hone, mul_zero_pt']
      exact hRp0
  obtain hcl : ∀ r ∈ [Reg.rax, .rcx, .rdx, .r8], r ∈ clob K.M.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp [clob]
    · simp [clob]
    · simp [clob]
    · exact r8_mem_clob _
  refine ⟨hs₄.of_keepRegs k₅ (by decide), ?_, ?_, ?_, ?_⟩
  · exact (((((Keeps.regs k₁).mono hcl).trans (k₂.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h]))).trans
      ⟨k₃.gpr, k₃.rd, k₃.wr⟩).trans ((Keeps.regs k₄).mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h]))).trans
      (k₅.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]))
  · refine ((U₂.trans (U₃.trans (m₄ ▸ O₅.unch))).mono ?_)
    intro w hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    grind
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [vx, ex₂]; split
      · exact (Ta ‹_›).1 _ (by simp)
      · exact hp0
    · rw [vy]; split
      · exact Nat.mod_lt _ hp0
      · exact hEy₂
    · rw [vz, ez₂]; split
      · exact (Ta ‹_›).1 _ (by simp)
      · exact hp0
  · have ex : tmv C K.M.n base s₅ K.E.x = tmv C K.M.n base s₂ K.E.x := by
      show toM _ _ _ = toM _ _ _; rw [vx]
    obtain ez : tmv C K.M.n base s₅ K.E.z = tmv C K.M.n base s₂ K.E.z := by
      show toM _ _ _ = toM _ _ _; rw [vz]
    rw [ex, ez]
    unfold winPt
    by_cases h8 : 8 ≤ nib k i
    · have hy : tmv C K.M.n base s₅ K.E.y = tmv C K.M.n base s₂ K.E.y := by
        show toM _ _ _ = toM _ _ _
        rw [vy, decide_eq_false (show ¬ nib k i < 2 ^ (4 - 1) by omega_using [h8])]; rfl
      rw [hy]
      simp only [h8, ↓reduceIte]
      have : a = nib k i - 8 := by rw [← ha, magH]; simp [h8]
      rw [this] at hR
      exact hR
    · have hy : tmv C K.M.n base s₅ K.E.y = -tmv C K.M.n base s₂ K.E.y := by
        show toM _ _ _ = -toM _ _ _
        rw [vy, decide_eq_true (show nib k i < 2 ^ (4 - 1) by omega_using [h8])]
        simp only [↓reduceIte]
        rw [toM_sub (by omega_using [hEy₂]), toM_zero]
        grind
      rw [hy]
      simp only [h8, ↓reduceIte]
      have : a = 8 - nib k i := by rw [← ha, magH]; simp [h8]
      rw [this] at hR
      exact hRpNeg hR

/-- `winEntryR_ok` in projective coordinates. -/
theorem winEntry_ok {K : WinCfg} {C : Curve} {base : Addr} {size k i : Nat} (hL : WinLay K size)
    (hX : WinX K size) (hC : Law C) {P : Point C} (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s : State} (hs : Scr s base size)
    (hM : ModOkW K.M size C.p s.mem base) (hi : i < K.J) (hx : s.gpr .rbx = BitVec.ofNat 64 i)
    (hbits : ∀ t < 4 * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0)
    (hz : wordsVal s.mem base K.zero K.M.n = 0) (hT : TblOk K C base P 8 s) :
    WP isa (.block ((WinCfg.tc K).digit ++ WinCfg.select K)) s fun s₂ =>
      WP isa (.block (WinCfg.tc K).negY) s₂ (EntryPostW K C base size P k i s) :=
  winEntryR_ok hL hX (rep_infinity' hC) Rep.negY hpn hone_lt hone hs hM hi hx hbits hz hT

end VG.Proof.Weierstrass.X86_64
