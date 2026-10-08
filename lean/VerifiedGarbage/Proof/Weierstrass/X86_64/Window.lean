import VerifiedGarbage.Impl.Weierstrass.X86_64.Window
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Weierstrass.WinLay
import VerifiedGarbage.Proof.Weierstrass.Window
import VerifiedGarbage.Proof.Weierstrass.Jac

/-!
# The window method on x86-64: the table and the additions

As on AArch64 (`Proof/Weierstrass/AArch64/Window.lean`): the table `[1 … 8]P`
(`build_ok`: `P`, then `[m + 1]P = [m]P + P` by the complete addition for
`a = -3`, `addT_ok`), and the addition of an entry to `R` (`winAdd_ok`: into
`D`, then copied). `WinEntry.lean` selects the entry of a digit, `WinQuad.lean`
multiplies `R` by 16, and `WinLoop.lean` is the loop.
-/

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
  have hw : ∀ z ∈ [K.R.x, K.R.y, K.R.z, K.D.x, K.D.y, K.D.z], z ∈ winWs K := by
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
  have hDx : K.D.x ∈ [K.D.x, K.D.y, K.D.z] ++ V := by simp
  have hDy : K.D.y ∈ [K.D.x, K.D.y, K.D.z] ++ V := by simp
  have hDz : K.D.z ∈ [K.D.x, K.D.y, K.D.z] ++ V := by simp
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
  have hO : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.R K.E, x ∈ winSlots K := by
    intro x hx
    simp only [rcbW, rcbR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> win_mem
  have hI : Inv K.M base size C.p (· ∈ winSlots K) (rcbR K.S K.R K.E) (tmv C K.M.n base s) s :=
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
  hU.wordsVal (hL.ro_w hx) (by have := hL.lay.le x (winRo_slots K x hx); omega)

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
  · have := hL.lay.mo y (winWs_slots K y hy); dsimp only; omega
  · have := hM.sep; dsimp only; omega

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

/-- The slots of entry `j` are apart from what the addition into entry
`m + 1 ≠ j` writes. -/
theorem tbl_apart_add {K : WinCfg} {size : Nat} (hL : WinLay K size) {j m : Nat} (hj1 : 1 ≤ j)
    (hj8 : j ≤ 8) (hm1 : 1 ≤ m + 1) (hm8 : m + 1 ≤ 8) (hjm : j ≠ m + 1) :
    ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
      ∀ w ∈ (rcbW K.S (K.tblPt (m + 1))).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n)],
        x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro x hx w hw
  obtain ⟨i, hi, rfl, hi₁, hi₂⟩ := tblPt_mem K hj1 hj8 x hx
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · have ets : rcbW K.S (K.tblPt (m + 1)) = [K.S.t0, K.S.t1, K.S.t2, K.S.t3, K.S.t4, K.S.t5] ++
        [(K.tblPt (m + 1)).x, (K.tblPt (m + 1)).y, (K.tblPt (m + 1)).z] := rfl
    rw [ets, List.mem_append] at hy
    dsimp only
    rcases hy with hy | hy
    · exact (hL.tbl_apart (rcbW_mem_other y hy) hi).symm
    · obtain ⟨i', hi', rfl, hi'₁, hi'₂⟩ := tblPt_mem K hm1 hm8 y hy
      exact winTbl_apart K (by omega)
  · exact hL.lay.tmp _ (by
      simp only [winSlots, List.mem_append]; exact Or.inr (winTbl_mem K hi))

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
  have hse : BitVec.signExtend 64 (BitVec.ofNat 32 i) = BitVec.ofNat 64 i := by
    rw [BitVec.signExtend_eq_setWidth_of_msb_false (BitVec.msb_eq_false_iff_two_mul_lt.mpr (by
        rw [BitVec.toNat_ofNat]; omega)),
      BitVec.setWidth_ofNat_of_le_of_lt (by decide) (by omega)]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    Option.some.injEq, exists_eq_left', hb, hse]
  refine ⟨?_, fun r _ => rfl, rfl, rfl, rfl⟩
  show some (_ == 0) = _
  congr 1
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj]
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega)]
  change _ = 0 ↔ _
  omega

/-- The slots of entry `j` of the table, apart from those of entry `m ≠ j`. -/
theorem tbl_apart_entry {K : WinCfg} {j m : Nat} (hj1 : 1 ≤ j) (hj8 : j ≤ 8) (hm1 : 1 ≤ m) (hm8 : m ≤ 8)
    (hjm : j ≠ m) : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
      ∀ y ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z],
        x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := by
  intro x hx y hy
  obtain ⟨i, hi, rfl, hi₁, hi₂⟩ := tblPt_mem K hj1 hj8 x hx
  obtain ⟨i', hi', rfl, hi'₁, hi'₂⟩ := tblPt_mem K hm1 hm8 y hy
  exact winTbl_apart K (by omega)

/-- What a copy from `D` into entry `m` of the table needs. -/
theorem copyD_tbl {K : WinCfg} {size : Nat} (hL : WinLay K size) {m : Nat} (hm1 : 1 ≤ m) (hm8 : m ≤ 8) :
    (∀ x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z, K.D.x, K.D.y, K.D.z], x + 8 * K.M.n ≤ size) ∧
    (∀ x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z],
      ∀ y ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z, K.D.x, K.D.y, K.D.z], x ≠ y →
        x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x) ∧
    (∀ x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z], x ∉ [K.D.x, K.D.y, K.D.z]) ∧
    ((K.tblPt m).x ≠ (K.tblPt m).y ∧ (K.tblPt m).x ≠ (K.tblPt m).z ∧ (K.tblPt m).y ≠ (K.tblPt m).z) := by
  have st := tblPt_slots K hm1 hm8
  have dO : ∀ y ∈ [K.D.x, K.D.y, K.D.z], y ∈ winOther K := by
    intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl <;> win_mem
  have sl : ∀ x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z, K.D.x, K.D.y, K.D.z], x ∈ winSlots K := by
    intro x hx
    rcases List.mem_append.mp (show x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z] ++
      [K.D.x, K.D.y, K.D.z] by simpa using hx) with h | h
    · exact (st x h).1
    · exact winOther_mem (dO x h)
  have td : ∀ x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z], ∀ y ∈ [K.D.x, K.D.y, K.D.z],
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := by
    intro x hx y hy
    obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K hm1 hm8 x hx
    exact (hL.tbl_apart (List.mem_append_right _ (dO y hy)) hi).symm
  have ne : (K.tblPt m).x ≠ (K.tblPt m).y ∧ (K.tblPt m).x ≠ (K.tblPt m).z ∧ (K.tblPt m).y ≠ (K.tblPt m).z := by
    rw [tblPt_x, tblPt_y, tblPt_z]
    exact ⟨hL.tbl_ne₂ (by omega), hL.tbl_ne₂ (by omega), hL.tbl_ne₂ (by omega)⟩
  refine ⟨fun x hx => hL.lay.le x (sl x hx), fun x hx y hy hxy => ?_, fun x hx hy => ?_, ne⟩
  · rcases List.mem_append.mp (show y ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z] ++
      [K.D.x, K.D.y, K.D.z] by simpa using hy) with h | h
    · exact hL.apart₂ (st x hx).2 (st y h).2 hxy
    · exact td x hx y h
  · have := td x hx x hy
    have := hL.n0
    omega

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
    obtain rfl : i = 0 := by omega
    rw [WinCfg.storeEntry]
    obtain ⟨a, c, d, e⟩ := copyD_tbl hL (m := 8) (by decide) (Nat.le_refl _)
    exact copyPt_ok hs a c d e
  | j + 1, s, hi, hj, hs, hb => by
    rw [WinCfg.storeEntry]
    refine WP.seq (WP.mono (cmpRbx_ok s (j := i) (i := j + 1) (by omega) (by omega) hb)
      fun t ⟨ev, kt⟩ => ?_)
    have hst := hs.of_keeps kt (by decide)
    have mt : t.mem = s.mem := kt.2.1
    have kt' : KeepRegs [.rax] s t := (Keeps.regs kt).mono fun r hr => by simp at hr
    refine WP.ite _ ev (fun he => ?_) (fun he => ?_)
    · obtain rfl : i = j + 1 := of_decide_eq_true he
      obtain ⟨a, c, d, e⟩ := copyD_tbl hL (m := 7 - j) (by omega) (by omega)
      rw [show 8 - (j + 1) = 7 - j by omega]
      exact WP.mono (copyPt_ok hst a c d e) fun u ⟨e1, e2, e3, k, U⟩ =>
        ⟨by rw [e1, mt], by rw [e2, mt], by rw [e3, mt], kt'.trans k, by rw [← mt]; exact U⟩
    · have hne : i ≠ j + 1 := of_decide_eq_false he
      exact WP.mono (storeEntry_ok hL j (by omega) (by omega) hst ((kt.1 _ (by decide)).trans hb))
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
  have hs₁ := hI.inv.scr.of_keeps k₁ (by decide)
  have m₁ : s₁.mem = s.mem := k₁.2.1
  have tb : tmv C K.M.n base s₁ K.S.b3 = Fin.ofNat C.p C.b := by
    show toM _ _ _ = _; rw [m₁, winRo_val hL hI.inv.unch hn (by simp [winRo])]; exact hF.b
  have ro_lt : ∀ x ∈ winRo K, wordsVal s₁.mem base x K.M.n < C.p := fun x hx => by
    rw [m₁, winRo_val hL hI.inv.unch hn hx]; exact hF.ro_lt x hx
  have tP : ∀ x ∈ [K.P.x, K.P.y, K.P.z], tmv C K.M.n base s₁ x = tmv C K.M.n base s₀ x := by
    intro x hx; show toM _ _ _ = toM _ _ _; rw [m₁, winRo_val hL hI.inv.unch hn (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [winRo])]
  have hO : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.E K.P, x ∈ winSlots K := by
    intro x hx
    simp only [rcbW, rcbR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> win_mem
  have hlt : ∀ x ∈ rcbR K.S K.E K.P, wordsVal s₁.mem base x K.M.n < C.p := by
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
  have hI₁ : Inv K.M base size C.p (· ∈ winSlots K) (rcbR K.S K.E K.P) (tmv C K.M.n base s₁) s₁ :=
    ⟨hs₁, by rw [m₁]; exact hI.inv.mod, fun x hx => hO x (List.mem_append_right _ hx), hlt,
      fun _ _ => rfl⟩
  have W := rcb3_ok hL.lay hp hL.rcbApart_EP hO hI₁ (fun x hx => hx)
  refine WP.seq ((WP.mono W fun s₂ ⟨k₂, I₂, v₂⟩ => ?_))
  -- `D` is `[m + 1]P`.
  have hox : K.D.x ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.E K.P := by simp
  have hoy : K.D.y ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.E K.P := by simp
  have hoz : K.D.z ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.E K.P := by simp
  have dlt : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s₂.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact I₂.lt _ hox
    · exact I₂.lt _ hoy
    · exact I₂.lt _ hoz
  have dRep : Rep C (tmv C K.M.n base s₂ K.D.x) (tmv C K.M.n base s₂ K.D.y) (tmv C K.M.n base s₂ K.D.z)
      (mul (m + 1) P) := by
    have hS : (tmv C K.M.n base s₂ K.D.x, tmv C K.M.n base s₂ K.D.y, tmv C K.M.n base s₂ K.D.z) =
        VG.Proof.Weierstrass.rcbAdd3 (tmv C K.M.n base s₁ K.S.b3)
          (tmv C K.M.n base s₁ K.E.x) (tmv C K.M.n base s₁ K.E.y) (tmv C K.M.n base s₁ K.E.z)
          (tmv C K.M.n base s₁ K.P.x) (tmv C K.M.n base s₁ K.P.y) (tmv C K.M.n base s₁ K.P.z) := by
      rw [← v₂]
      show (toM _ _ _, toM _ _ _, toM _ _ _) = _
      rw [I₂.val _ hox, I₂.val _ hoy, I₂.val _ hoz]
    rw [tb, tP K.P.x (by simp), tP K.P.y (by simp), tP K.P.z (by simp)] at hS
    have hE : Rep C (tmv C K.M.n base s₁ K.E.x) (tmv C K.M.n base s₁ K.E.y) (tmv C K.M.n base s₁ K.E.z)
        (mul m P) := by
      show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _; rw [m₁]; exact hI.rep
    have hPr : Rep C (tmv C K.M.n base s₀ K.P.x) (tmv C K.M.n base s₀ K.P.y)
        (tmv C K.M.n base s₀ K.P.z) (mul 1 P) := by rw [mul_one_pt]; exact hF.pt
    have hR := hC.add3 hM3 (hC.onCurve_mul hP m) (hC.onCurve_mul hP 1) hE hPr hS.symm
    rw [hC.add_mul_mul hP] at hR
    exact hR
  have hs₂ := k₂.scr hs₁
  have U₂ := k₂.unch
  -- `E = D`.
  have eO : ∀ y ∈ [K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z], y ∈ winOther K := by
    intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> win_mem
  obtain ⟨-, -, -, -, exy, exz, eyz, hED, -, -⟩ := hL.other_ne
  have hEd : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∉ [K.D.x, K.D.y, K.D.z] := by
    intro x hx hd
    refine hED x hx (List.mem_cons_of_mem _ ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> simp [rcbW]
  refine WP.seq (WP.mono (copyPt_ok hs₂ (o := K.E) (a := K.D) (n := K.M.n)
    (fun x hx => hL.lay.le x (winOther_mem (eO x hx)))
    (fun x hx y hy hxy => hL.apart₂ (winOther_ws K x (eO x (by simp at hx ⊢; omega_using [hx])))
      (winOther_ws K y (eO y hy)) hxy) hEd ⟨exy, exz, eyz⟩) fun s₃ ⟨e1, e2, e3, k₃, U₃⟩ => ?_)
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have x₃ : s₃.gpr .rbx = BitVec.ofNat 64 (7 - m) := by
    rw [k₃.gpr _ (by decide), k₂.gpr _ (rbx_not_clob _), x₁]; congr 1; omega_using [h1, h7]
  -- `D` into entry `m + 1`.
  refine WP.seq (WP.mono (storeEntry_ok hL (i := 7 - m) 6 (by omega_using [h1, h7]) (Nat.le_refl _) hs₃ x₃)
    fun s₄ ⟨f1, f2, f3, k₄, U₄⟩ => ?_)
  rw [show 8 - (7 - m) = m + 1 by omega_using [h1, h7]] at f1 f2 f3 U₄
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  have x₄ : s₄.gpr .rbx = BitVec.ofNat 64 (7 - m) := by rw [k₄.gpr _ (by decide), x₃]
  refine WP.mono (testRbx_ok s₄ (j := 7 - m) (by omega_using [h1, h7]) x₄) fun s₅ ⟨z₅, k₅⟩ => ?_
  have m₅ : s₅.mem = s₄.mem := k₅.2.1
  have b64 : ∀ x ∈ winSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := hL.lay.le x hx; omega_using [this, hn]
  have sT := tblPt_slots K (m := m + 1) (by omega_using [h1, h7]) (by omega_using [h1, h7])
  -- `D` is kept by the copy into `E`, and `E` by the store.
  have dE : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s₃.mem base x K.M.n = wordsVal s₂.mem base x K.M.n := by
    intro x hx
    refine U₃.wordsVal (fun w hw => ?_) (b64 x (winOther_mem (eO x (by simp at hx ⊢; omega_using [hx]))))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    have hxE : ∀ y ∈ [K.E.x, K.E.y, K.E.z], x ≠ y := fun y hy hxy => hEd y hy (hxy ▸ hx)
    rcases hw with rfl | rfl | rfl <;> dsimp only <;>
      exact hL.apart₂ (winOther_ws K x (eO x (by simp at hx ⊢; omega_using [hx])))
        (winOther_ws K _ (eO _ (by simp))) (hxE _ (by simp))
  have tE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s₄.mem base x K.M.n = wordsVal s₃.mem base x K.M.n := by
    intro x hx
    refine U₄.wordsVal (fun w hw => ?_) (b64 x (winOther_mem (eO x (by simp at hx ⊢; omega_using [hx]))))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    have hxo : x ∈ winRo K ++ winOther K := List.mem_append_right _ (eO x (by simp at hx ⊢; omega_using [hx]))
    rcases hw with rfl | rfl | rfl <;> dsimp only
    · obtain ⟨i, hi, e, -, -⟩ := tblPt_mem K (m := m + 1) (by omega_using [h1, h7]) (by omega_using [h1, h7]) _ (by simp : (K.tblPt (m + 1)).x ∈ _)
      rw [e]; exact hL.tbl_apart hxo hi
    · obtain ⟨i, hi, e, -, -⟩ := tblPt_mem K (m := m + 1) (by omega_using [h1, h7]) (by omega_using [h1, h7]) _ (by simp : (K.tblPt (m + 1)).y ∈ _)
      rw [e]; exact hL.tbl_apart hxo hi
    · obtain ⟨i, hi, e, -, -⟩ := tblPt_mem K (m := m + 1) (by omega_using [h1, h7]) (by omega_using [h1, h7]) _ (by simp : (K.tblPt (m + 1)).z ∈ _)
      rw [e]; exact hL.tbl_apart hxo hi
  have vEx : wordsVal s₅.mem base K.E.x K.M.n = wordsVal s₂.mem base K.D.x K.M.n := by
    rw [m₅, tE _ (by simp), e1]
  have vEy : wordsVal s₅.mem base K.E.y K.M.n = wordsVal s₂.mem base K.D.y K.M.n := by
    rw [m₅, tE _ (by simp), e2]
  have vEz : wordsVal s₅.mem base K.E.z K.M.n = wordsVal s₂.mem base K.D.z K.M.n := by
    rw [m₅, tE _ (by simp), e3]
  have vTx : wordsVal s₅.mem base (K.tblPt (m + 1)).x K.M.n = wordsVal s₂.mem base K.D.x K.M.n := by
    rw [m₅, f1, dE _ (by simp)]
  have vTy : wordsVal s₅.mem base (K.tblPt (m + 1)).y K.M.n = wordsVal s₂.mem base K.D.y K.M.n := by
    rw [m₅, f2, dE _ (by simp)]
  have vTz : wordsVal s₅.mem base (K.tblPt (m + 1)).z K.M.n = wordsVal s₂.mem base K.D.z K.M.n := by
    rw [m₅, f3, dE _ (by simp)]
  -- What the step writes: the addition's slots and temporary area, `E` and the entry.
  have UU := U₂.trans (U₃.trans U₄)
  have L2 : ∀ w ∈ (rcbW K.S K.D).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n)],
      w = (K.M.tmp, 8 * K.M.n) ∨ ∃ y ∈ winOther K, w = (y, 8 * K.M.n) := by
    intro w hw
    rcases List.mem_append.mp hw with h | h
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
      exact Or.inr ⟨y, List.mem_append_right _ hy, rfl⟩
    · exact Or.inl (List.mem_singleton.mp h)
  have L3 : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)],
      ∃ y ∈ winOther K, w = (y, 8 * K.M.n) := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact ⟨_, by win_mem, rfl⟩
    · exact ⟨_, by win_mem, rfl⟩
    · exact ⟨_, by win_mem, rfl⟩
  have L4 : ∀ w ∈ [((K.tblPt (m + 1)).x, 8 * K.M.n), ((K.tblPt (m + 1)).y, 8 * K.M.n),
      ((K.tblPt (m + 1)).z, 8 * K.M.n)], ∃ y ∈ [(K.tblPt (m + 1)).x, (K.tblPt (m + 1)).y,
        (K.tblPt (m + 1)).z], w = (y, 8 * K.M.n) := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact ⟨_, by simp, rfl⟩
    · exact ⟨_, by simp, rfl⟩
    · exact ⟨_, by simp, rfl⟩
  have split : ∀ {Q : Nat × Nat → Prop}, (w : Nat × Nat) →
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
  have U : Unch base (winW K) s.mem s₅.mem := by
    rw [← m₁, m₅]
    refine UU.mono fun w hw => split w hw (by simp [winW])
      (fun y hy => by simp only [winW, List.mem_append, List.mem_map]; exact Or.inl ⟨y, winOther_ws K y hy, rfl⟩)
      (fun y hy => by simp only [winW, List.mem_append, List.mem_map]; exact Or.inl ⟨y, (sT y hy).2, rfl⟩)
  have keep : KeepRegs (powClob K.M.n) s s₅ := by
    have c1 : ∀ r ∈ [Reg.rax], r ∈ powClob K.M.n := by intro r hr; simp at hr; subst hr; simp [powClob, clob]
    exact (((Keeps.regs k₁).mono fun r hr => by simp at hr; simp [hr, powClob]).trans
      ((⟨fun r hr => k₂.gpr r fun h => hr (List.mem_cons_of_mem _ h), k₂.rd, k₂.wr⟩ :
        KeepRegs (powClob K.M.n) s₁ s₂).trans ((k₃.mono c1).trans ((k₄.mono c1).trans
          ((Keeps.regs k₅).mono fun r hr => by simp at hr)))))
  refine ⟨⟨⟨hs₄.of_keeps k₅ (by decide), hI.inv.keep.trans keep,
    (hI.inv.unch.trans U).mono fun w hw => by rcases List.mem_append.mp hw with h | h <;> exact h,
    hI.inv.mod.unch U (winW_mo hL hI.inv.mod) hn, fun j hj1 hjm => ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · rcases Nat.lt_or_ge j (m + 1) with hj | hj
    · -- An entry built before keeps its numbers.
      have Tj := hI.inv.tbl j hj1 (by omega_using [h1, h7, hj1, hjm, hj])
      have sj := tblPt_slots K (m := j) hj1 (by omega_using [h1, h7, hj1, hjm, hj])
      have e : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
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
      have ex : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
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
  have s1 := tblPt_slots K (m := 1) (Nat.le_refl _) (by omega)
  have pRo : ∀ x ∈ [K.P.x, K.P.y, K.P.z], x ∈ winRo K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [winRo]
  have eO : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∈ winOther K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> win_mem
  have b64 : ∀ x ∈ winSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := hL.lay.le x hx; omega
  -- `[1]P = P`.
  have tP : ∀ x ∈ [(K.tblPt 1).x, (K.tblPt 1).y, (K.tblPt 1).z], ∀ y ∈ [K.P.x, K.P.y, K.P.z],
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := by
    intro x hx y hy
    obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K (m := 1) (Nat.le_refl _) (by omega) x hx
    exact (hL.tbl_apart (List.mem_append_left _ (pRo y hy)) hi).symm
  have ne1 : (K.tblPt 1).x ≠ (K.tblPt 1).y ∧ (K.tblPt 1).x ≠ (K.tblPt 1).z ∧
      (K.tblPt 1).y ≠ (K.tblPt 1).z := by
    rw [tblPt_x, tblPt_y, tblPt_z]
    exact ⟨hL.tbl_ne₂ (by omega), hL.tbl_ne₂ (by omega), hL.tbl_ne₂ (by omega)⟩
  have slP : ∀ x ∈ [(K.tblPt 1).x, (K.tblPt 1).y, (K.tblPt 1).z, K.P.x, K.P.y, K.P.z], x ∈ winSlots K := by
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
    (fun x hx h => by have := tP x hx x h; have := hL.n0; omega) ne1) fun s₁ ⟨a1, a2, a3, k₁, U₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  -- `E = P`.
  obtain ⟨-, -, -, -, exy, exz, eyz, -⟩ := hL.other_ne
  have eP : ∀ x ∈ [K.E.x, K.E.y, K.E.z], ∀ y ∈ [K.P.x, K.P.y, K.P.z], x ≠ y := fun x hx y hy h =>
    hL.ro y (pRo y hy) (h ▸ eO x hx)
  have slE : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.P.x, K.P.y, K.P.z], x ∈ winSlots K := by
    intro x hx
    rcases List.mem_append.mp (show x ∈ [K.E.x, K.E.y, K.E.z] ++ [K.P.x, K.P.y, K.P.z] by
      simpa using hx) with h | h
    · exact winOther_mem (eO x h)
    · exact winRo_slots K x (pRo x h)
  rw [WP.block_append_iff]
  refine WP.mono (copyPt_ok hs₁ (o := K.E) (a := K.P) (n := K.M.n)
    (fun x hx => hL.lay.le x (slE x hx))
    (fun x hx y hy hxy => hL.lay.apart x y (slE x (by simp at hx ⊢; omega)) (slE y hy) hxy)
    (fun x hx h => eP x hx x h rfl) ⟨exy, exz, eyz⟩) fun s₂ ⟨c1, c2, c3, k₂, U₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (mov32Rbx_ok s₂ (j := 7) (by decide)) fun s₃ ⟨x₃, k₃⟩ => ?_
  -- The invariant for `[1]P`.
  have U : Unch base (winW K) s.mem s₃.mem := by
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
  have kT : ∀ x ∈ [(K.tblPt 1).x, (K.tblPt 1).y, (K.tblPt 1).z],
      wordsVal s₃.mem base x K.M.n = wordsVal s₁.mem base x K.M.n := by
    intro x hx
    rw [m₃]
    refine U₂.wordsVal (fun w hw => ?_) (b64 x (s1 x hx).1)
    obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K (m := 1) (Nat.le_refl _) (by omega) x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact (hL.tbl_apart (x := K.E.x) (List.mem_append_right _ (by win_mem)) hi).symm
    · exact (hL.tbl_apart (x := K.E.y) (List.mem_append_right _ (by win_mem)) hi).symm
    · exact (hL.tbl_apart (x := K.E.z) (List.mem_append_right _ (by win_mem)) hi).symm
  have kP : ∀ x ∈ [K.P.x, K.P.y, K.P.z], wordsVal s₁.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
    intro x hx
    refine U₁.wordsVal (fun w hw => ?_) (b64 x (winRo_slots K x (pRo x hx)))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;>
      exact (tP _ (by simp) x hx).symm
  have c1' : ∀ r ∈ [Reg.rax], r ∈ powClob K.M.n := by intro r hr; simp at hr; subst hr; simp [powClob, clob]
  have I₁ : BuildInvE K C base size P s 1 s₃ := by
    refine ⟨⟨hs₂.of_keeps k₃ (by decide), ((k₁.mono c1').trans (k₂.mono c1')).trans
      ((Keeps.regs k₃).mono fun r hr => by simp at hr; simp [hr, powClob]), U, hM.unch U (winW_mo hL hM) hn,
      fun j hj1 hj => ?_⟩, fun x hx => ?_, ?_, by rw [x₃]⟩
    · obtain rfl : j = 1 := by omega
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
    (fun j t h1 h2 hi => WP.mono (buildStep_ok hL hp hC hM3 hP hF (m := 8 - j) (by omega) (by omega) hi)
      fun u ⟨I, z⟩ => ⟨by rw [show 8 - (j - 1) = 8 - j + 1 by omega]; exact I,
        by rw [z]; congr 1; simp only [decide_eq_decide]; omega⟩)
    (fun t hi => hi.inv) (by decide) I₁

end VG.Proof.Weierstrass.X86_64
