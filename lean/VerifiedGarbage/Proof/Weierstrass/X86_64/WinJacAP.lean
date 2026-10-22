module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacA
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacOddPSel
public import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacAP
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacEntryA
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacEntry
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacDbls
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacIter
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacStep
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacBuild
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJac
import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogI
import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelect
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJP
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.X25519.X86_64.Mem

/-!
# 5-bit windows with an affine table on x86-64, each selection woven into the addition before it

`JacWinCfg.windowAP K inv dbl` (`Impl/Weierstrass/X86_64/WinJacAP.lean`)
computes what `windowA` does (`winJacAP_ok`, as `winJacA_ok`): its loop keeps
digit `j - 1`'s entry in `T` at `rbx = j` (`JInvAP`). An iteration
(`jstepAP_ok`) doubles `R` five times, which writes neither `T` nor the
table; sets up digit `j - 2`'s selection (`prepA_ok`); computes `D = R + T`
while it selects (`maddJIW_ok`, with `SelA` as the side code's state, which
the addition's operations keep, writing only other slots); applies the masks
(`jmaddA_post`), which keep the vector registers (`weaveAOk`) and so the
selection; and stores and negates the entry (`storeA_ok`, `jselOutA`,
`jnegA_ok`). Digit `J - 2`'s entry is selected before the loop
(`jfirstAP_ok`), and digit `0`'s addition selects none (`jlastA_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-! ## The selection -/

/-- The selection of an entry's `X` and `Y`, its first `n` 16-byte pieces,
between the mixed addition's operations (`SelW`). -/
abbrev SelA (K : JacWinCfg) (base : Addr) (mem : Mem) (a e : Nat) (t : State) : Prop :=
  SelW K.avx2 K.tbl K.st K.M.n base mem a e t

theorem stA (K : JacWinCfg) : 16 * K.M.n ≤ K.st := by unfold JacWinCfg.st; omega

/-- What the other slots and the temporary area are apart from: the table's
slots. -/
theorem othW_tbl_apart (hL : JacWinLay K size) :
    ∀ w ∈ jwOthW K, ∀ i < 80, jg K i + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ jg K i := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hw
    exact other_tbl_apart hL ho _ (List.mem_cons_self ..)
  · rw [List.mem_singleton.mp hw]
    exact other_tbl_apart hL (o := K.R.x) (by jw_mem) _ (by simp)

/-- A field operation writing a slot but the grid's keeps the selection
(`maddJIW_ok`'s `hstab`). -/
theorem SelA.stab (hL : JacWinLay K size) {base : Addr} {mem : Mem} {a e o : Nat} (ho : o ∈ jwOther K)
    (hn : base.toNat + size ≤ 2 ^ 64) {t t' : State} (h : SelA K base mem a e t)
    (hk : OpKeep K.MI base o t t') (hx : t'.xmm = t.xmm) (hy : t'.ymmHi = t.ymmHi) :
    SelA K base mem a e t' := by
  have hg := hL.grid_le
  have := st16 K
  exact SelW.stab h hk.unch (fun w hw b hb => tbl_byte_apart hL (other_tbl_apart hL ho w hw) hb) (by omega)
    hx hy hk.rd hk.wr (hk.gpr _ (rdi_not_clob _))

theorem nMadd_pos (K : JacWinCfg) : 0 < K.nMadd := by
  rw [JacWinCfg.nMadd, maddJ_eq, ofN, List.length_map]; decide

/-- A part of the selection (`maddJIW_ok`'s `hside`): from entry
`chunkW nMadd i` to `chunkW nMadd (i + 1)`. -/
theorem selChunkA_ok (hL : JacWinLay K size) (hnp : 2 ≤ K.M.n ∧ K.M.n ≤ 10) {base : Addr} {mem : Mem} {a : Nat}
    (i : Nat) (hi : i < K.nMadd) {t : State} (h : SelA K base mem a (chunkW K.nMadd i) t) :
    WP isa (.block (K.selChunkA i)) t fun t' => SelA K base mem a (chunkW K.nMadd (i + 1)) t' ∧
      ForwardField.SideKeepF t t' := by
  have := st16 K
  have := hL.n6
  exact selChunkW_ok hnp (stA K) hL.tbl31 (by omega) i hi h

/-- Before digit `rbx = j`'s addition: digit `j - 1`'s magnitude `a` set up
for its selection, from `s`'s table. -/
theorem prepA_ok (hL : JacWinLay K size) (hnp : 2 ≤ K.M.n ∧ K.M.n ≤ 10) {base : Addr} {P : Point C}
    {s₀ : State} {k : Nat} (hF : JacWinFixed K C base s₀ P k) {s : State} {j : Nat} (hj1 : 1 ≤ j)
    (hjJ : j < K.J) (hf : JFrame K C base size s₀ s) (hb : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block K.prepA) s fun t =>
      SelA K base s.mem (magH 16 (Window5.nib (k + JacWinCfg.offset K.J) (j - 1))) 0 t ∧
        Keeps [.rax, .rcx, .rdx, .r8] s t := by
  have hs := hf.scr
  have hn := hs.nowrap
  have hJ := hL.J
  have hbl := hL.bits
  have hbits := hf.bits hL hF
  rw [JacWinCfg.prepA, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (decRbx_ok s hj1 (by omega) hb) fun s₁ ⟨b₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (digit_ok K.tc hs₁ (k := k + JacWinCfg.offset K.J) (j := j - 1) (N := 5 * K.J)
    (by show 1 ≤ 5; decide) (by show 5 < 9; decide) (by show 5 * (j - 1) + 5 ≤ 5 * K.J; omega)
    (by show K.bits + 5 * K.J ≤ size; omega) b₁ (fun t ht => by rw [k₁.2.1]; exact hbits t ht))
    fun s₂ ⟨_, r₂, k₂⟩ => ?_
  rw [show K.tc.w = 5 from rfl, Window5.combWin_five, show K.tc.H = 16 from rfl] at r₂
  rw [WP.block_append_iff]
  refine WP.mono (incRbxJ_ok s₂ (j := j - 1) (by rw [k₂.1 _ (by decide), b₁])) fun s₃ ⟨b₃, k₃, _, _⟩ => ?_
  have ha := magH_le (H := 16) (v := Window5.nib (k + JacWinCfg.offset K.J) (j - 1))
    (by have := Window5.nib_lt (k + JacWinCfg.offset K.J) (j - 1); omega)
  refine WP.mono (selSetW_ok hnp s₃ (tblX K base) K.st s.mem ha (by rw [k₃.1 _ (by decide), r₂]))
    fun t ⟨S, k₄⟩ => ⟨⟨ha, S, ?_, ?_, ?_⟩, ?_⟩
  · intro b _; rw [k₄.2.1, k₃.2.1, k₂.2.1, k₁.2.1]
  · have hg := hL.grid_le
    have := st16 K
    rw [k₄.2.2.2, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]
    exact ⟨_, List.mem_append_right _ hs.wr, hs.contains (d := K.tbl) (by omega) (by omega)⟩
  · rw [k₄.1 _ (by decide), k₃.1 _ (by decide), k₂.1 _ (by decide), k₁.1 _ (by decide)]; exact hs.rdi
  · refine ⟨fun r hr => ?_, by rw [k₄.2.1, k₃.2.1, k₂.2.1, k₁.2.1], by rw [k₄.2.2.1, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1],
      by rw [k₄.2.2.2, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k₄.1 r (by simp [hr.2.1])]
    by_cases hrb : r = .rbx
    · subst hrb; rw [b₃, hb, show j - 1 + 1 = j by omega]
    · rw [k₃.1 r (by simp [hrb]), k₂.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]), k₁.1 r (by simp [hrb])]

/-- The accumulators after the sixteen entries stored to `T`'s `X` and `Y`. -/
theorem storeA_ok (hL : JacWinLay K size) (hnp : 2 ≤ K.M.n ∧ K.M.n ≤ 10) {base : Addr} {mem : Mem} {a : Nat}
    {t : State} (hs : Scr t base size) (h : SelSW K.avx2 (tblX K base) K.st K.M.n mem a 16 t) :
    WP isa (.block (storeW K.avx2 K.T K.M.n)) t fun t' =>
      (∀ c < K.M.n, t'.mem.readW (off base (K.T + 16 * c)) 128 = accVal mem (tblX K base) K.st (16 * ·) a 16 c) ∧
      Outside base K.T (16 * K.M.n) t.mem t'.mem ∧ t'.gpr = t.gpr ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hT : K.T + 16 * K.M.n ≤ size := by
    have := hL.grid_le; rw [hL.T80]; unfold jg; omega
  exact storeW_ok hnp hs hT h

/-- `T`'s `X` and `Y` after `storeA_ok`: entry `a`'s, as in `mem`, or zero
for `a = 0`. -/
theorem jselOutA (hL : JacWinLay K size) {base : Addr} {mem mem' : Mem} {a : Nat} (ha : a ≤ 16)
    (h : ∀ c < K.M.n, mem'.readW (off base (K.T + 16 * c)) 128 = accVal mem (tblX K base) K.st (16 * ·) a 16 c) :
    ∀ c < 2, wordsVal mem' base (jg K (80 + c)) K.M.n =
      if 1 ≤ a then wordsVal mem base (jg K (5 * (a - 1) + c)) K.M.n else 0 := by
  have hT : K.T = jg K 80 := hL.T80
  intro c hc
  have hcn := Nat.mul_le_mul_left K.M.n (show c + 1 ≤ 2 by omega)
  rw [Nat.mul_succ] at hcn
  have eT : jg K (80 + c) = K.T + 8 * (K.M.n * c) := by
    rw [hT]; unfold jg; rw [Nat.mul_add, ← Nat.mul_assoc]; omega
  have hX : ∀ d, word mem (tblX K base) d = word mem base (K.tbl + d) := fun d => by
    rw [Mont.word, Mont.word, off, off, Offset.add_add]
  have hw : ∀ i < K.M.n, word mem' base (K.T + 8 * (K.M.n * c) + 8 * i) =
      if 1 ≤ a then word mem base (jg K (5 * (a - 1) + c) + 8 * i) else 0 := by
    intro i hi
    obtain ⟨c', q, hq, e⟩ : ∃ c' q, q < 2 ∧ K.M.n * c + i = 2 * c' + q :=
      ⟨(K.M.n * c + i) / 2, (K.M.n * c + i) % 2, Nat.mod_lt _ (by decide), by omega⟩
    have hc' : c' < K.M.n := by omega
    have w := accVal_word1 (h c' hc') hq
    rw [show K.T + 16 * c' + 8 * q = K.T + 8 * (K.M.n * c) + 8 * i by omega] at w
    rw [w]
    by_cases h1 : 1 ≤ a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, ha⟩), ite_eq_left_of_eq_true _ _ (eq_true h1), hX]
      congr 1; unfold jg JacWinCfg.st
      rw [show 40 * K.M.n * (a - 1) = 8 * K.M.n * (5 * (a - 1)) by
        rw [Nat.mul_assoc, Nat.mul_assoc, show 40 = 8 * 5 from rfl, Nat.mul_assoc, Nat.mul_left_comm 5],
        Nat.mul_add (8 * K.M.n), Nat.mul_assoc 8 K.M.n c, Nat.mul_assoc 8 K.M.n (5 * (a - 1))]
      omega
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false h1)]
  rw [eT]
  by_cases h1 : 1 ≤ a
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
    refine wordsVal_congr₂ _ _ _ fun i hi => ?_
    rw [hw i hi, ite_eq_left_of_eq_true _ _ (eq_true h1)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
    refine wordsVal_zeros fun i hi => ?_
    rw [hw i hi, ite_eq_right_of_eq_false _ _ (eq_false h1)]

/-! ## An iteration -/

/-- `T` holding digit `i`'s entry of the table of `k'`'s windows, with `Z`
one (`JEntA`'s facts). -/
structure JTA (K : JacWinCfg) (C : Curve) (base : Addr) (P : Point C) (k' i : Nat) (s : State) : Prop where
  lt : ∀ c < 3, wordsVal s.mem base (TS K c) K.M.n < C.p
  one : wordsVal s.mem base (TS K 2) K.M.n = K.one
  ent : 1 ≤ magH 16 (Window5.nib k' i) → InvJ C (tmv C K.M.n base s (TS K 0)) (tmv C K.M.n base s (TS K 1))
    (tmv C K.M.n base s (TS K 2)) (Window5.winPt C P k' i)

theorem JTA.congr {base : Addr} {P : Point C} {k' i : Nat} {s t : State} (h : JTA K C base P k' i s)
    (e : ∀ c < 3, wordsVal t.mem base (TS K c) K.M.n = wordsVal s.mem base (TS K c) K.M.n) :
    JTA K C base P k' i t := by
  have tv : ∀ c < 3, tmv C K.M.n base t (TS K c) = tmv C K.M.n base s (TS K c) := fun c hc => by
    show toM _ _ _ = toM _ _ _; rw [e c hc]
  exact ⟨fun c hc => by rw [e c hc]; exact h.lt c hc, by rw [e 2 (by decide)]; exact h.one,
    fun h1 => by rw [tv 0 (by decide), tv 1 (by decide), tv 2 (by decide)]; exact h.ent h1⟩

/-- The woven loop's invariant at `rbx = j`: `JInvA`, and digit `j - 1`'s
entry in `T`. -/
structure JInvAP (K : JacWinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (k j : Nat) (s : State) : Prop where
  inv : JInvA K C base size P s₀ k j s
  ent : JTA K C base P (k + JacWinCfg.offset K.J) (j - 1) s

/-- An iteration, `2 ≤ j < J`: `R = 32 R + [d_{j-1}]P`, with digit `j - 2`'s
entry selected meanwhile into `T`. -/
theorem jstepAP_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl) {P : Point C}
    (hP : onCurve C P = true) (hP0 : P ≠ .infinity) (hn17 : 17 ≤ C.n % 32) (hn64 : 64 ≤ C.n)
    (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    (hnp : 2 ≤ K.M.n ∧ K.M.n ≤ 10) (hsc : ∀ op ∈ maddJ K.S K.R K.E K.D, scalCode (opProg K.MI op) = true)
    (hmk : K.masksA.all scalarI = true)
    {base : Addr} {s₀ : State} {k : Nat} (hF : JacWinFixed K C base s₀ P k) {j : Nat}
    (hj2 : 2 ≤ j) (hjJ : j < K.J) {s : State} (hI : JInvAP K C base size P s₀ k j s) :
    WP isa (K.stepAP dbl).inline s fun s' => JInvAP K C base size P s₀ k (j - 1) s' ∧
      s'.zf = some (decide (j - 1 = 1)) := by
  obtain ⟨⟨hI, hO1⟩, T₀⟩ := hI
  obtain ⟨Q, hQ, hQe, R₀⟩ := hI.st
  have hn := R₀.fr.scr.nowrap
  have hJ := hL.J
  obtain ⟨tx, ty, -, -, -⟩ := hL.TS_eq
  obtain ⟨mx, my, -, -, -⟩ := hL.T_mem
  rw [JacWinCfg.stepAP]
  simp only [Code.inline]
  refine WP.seq (WP.mono (decRbx_ok s (by omega) (by omega) hI.rbx) fun s₁ ⟨b₁, k₁⟩ => ?_)
  have R₁ := R₀.rbxKeeps hL k₁
  have m₁ : s₁.mem = s.mem := k₁.2.1
  rw [← mul_one_pt Q] at R₁
  refine WP.seq (WP.mono (dbls_ok hL hC hD hQ (j := j - 1) (by omega) b₁ R₁) fun s₂ ⟨R₂, b₂, U₂⟩ => ?_)
  have O₂ : JTblOne K base s₂ := (show JTblOne K base s₁ from fun m h1 h16 => by
    rw [m₁]; exact hO1 m h1 h16).loopW hL (U₂.mono (jwOthW_loopW K)) hn
  have T₂ : JTA K C base P (k + JacWinCfg.offset K.J) (j - 1) s₂ := T₀.congr fun c hc => by
    rw [ts_othW hL U₂ hn c (by omega), m₁]
  -- Digit `j - 2`'s selection set up.
  refine WP.seq (WP.mono (prepA_ok hL hnp hF (j := j - 1) (by omega) (by omega) R₂.fr b₂) fun s₃ ⟨S₃, k₃⟩ => ?_)
  generalize ha : magH 16 (Window5.nib (k + JacWinCfg.offset K.J) (j - 1 - 1)) = a at S₃
  have m₃ : s₃.mem = s₂.mem := k₃.2.1
  have hs₃ := R₂.fr.scr.of_keeps k₃ (by decide)
  have F₃ := R₂.fr.next hL hs₃ ((Keeps.regs k₃).mono (sub_powClob (by decide))) (W := [])
    (by rw [m₃]; exact Unch.refl _ _ _) (by simp)
  have T₃ : JTA K C base P (k + JacWinCfg.offset K.J) (j - 1) s₃ := T₂.congr fun c _ => by rw [m₃]
  have hb₃ : s₃.gpr .rbx = BitVec.ofNat 64 (j - 1) := by rw [k₃.1 _ (by decide), b₂]
  -- `D = R + T`, the selection woven in.
  have V₃ : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y],
      x ∈ jwSlots K ∧ wordsVal s₃.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by jw_mem, by rw [m₃]; exact R₂.lt _ (by simp)⟩
    · exact ⟨by jw_mem, by rw [m₃]; exact R₂.lt _ (by simp)⟩
    · exact ⟨by jw_mem, by rw [m₃]; exact R₂.lt _ (by simp)⟩
    · exact ⟨mx, by rw [← tx]; exact T₃.lt 0 (by decide)⟩
    · exact ⟨my, by rw [← ty]; exact T₃.lt 1 (by decide)⟩
  have I₃ : Inv K.M base size C.p (· ∈ jwSlots K) [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y]
      (tmv C K.M.n base s₃) s₃ :=
    ⟨hs₃, F₃.mod, fun x hx => (V₃ x hx).1, fun x hx => (V₃ x hx).2, fun _ _ => rfl⟩
  have hSl : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.R K.E, x ∈ jwSlots K := by
    intro x hx
    simp only [rcbW, rcbR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rw [hL.Tx, hL.Ty, hL.Tz] at hx
    rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h]
    all_goals first
      | exact jg_mem (by decide) | jw_mem
  have hDo : ∀ x ∈ rcbW K.S K.D, x ∈ jwOther K := by
    intro x hx
    simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> jw_mem
  have hS₀ : SelA K base s₂.mem a (chunkW K.nMadd 0) s₃ := by rw [chunkW_zero]; exact S₃
  refine WP.seq (WP.mono (maddJIW_ok (M := K.MI) (hL.lay.inl true) hp hL.addApart hSl
    (SI := fun i t => SelA K base s₂.mem a (chunkW K.nMadd i) t) (N := K.nMadd)
    (fun i t hi h => (selChunkA_ok hL hnp i hi h).mono fun t' ⟨h', k'⟩ => ⟨h', k'.side⟩)
    (fun i o t t' ho h hk hx hy _ => SelA.stab hL (hDo o ho) hn h hk hx hy) hsc (i := 0)
    (Nat.le_of_eq (Nat.zero_add _)) (I₃.inl true) (fun x hx => hx) hS₀) fun s₅ ⟨k₅, I₅, v₅, S₅⟩ => ?_)
  have k₅' : ProgKeep K.M base (rcbW K.S K.D) s₃ s₅ := ProgKeep.of_inl (M := K.M) (b := true) k₅
  have U₅ : Unch base (jwOthW K) s₃.mem s₅.mem := (ProgKeep.unch k₅').mono fun w hw => by
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
      exact List.mem_append_left _ (List.mem_map_of_mem (hDo x hx))
    · exact List.mem_append_right _ hw
  rw [Nat.zero_add, show (maddJ K.S K.R K.E K.D).length = K.nMadd from rfl, chunkW_last (nMadd_pos K)] at S₅
  -- The masks, which keep the selection.
  rw [WP.block_append_iff]
  have hmk' : scalCode (.block (nzMask K.M.n K.R.z ++ selPt K.M.n K.D K.E K.D ++ K.tc.digit ++ eqMask 0 ++
      selPt K.M.n K.R K.D K.R) : Prog isa) = true := hmk
  refine WP.mono (WP.vecKeep hmk' (jmaddA_post hL hp hC hM3 hO hP hP0 hn17 hn64 hone hF (j := j) (by omega)
    (by omega) hQ hQe R₂ O₂ F₃ (by rw [m₃]; exact Unch.refl _ _ _) (fun _ _ => by rw [m₃]) hb₃ T₃.lt T₃.one
    T₃.ent k₅' (Inv.of_inl (M := K.M) (b := true) I₅) v₅)) fun s₆ ⟨⟨I₆, U₆⟩, x₆, y₆⟩ => ?_
  obtain ⟨⟨⟨Q', hQ', hQe', R₆⟩, b₆⟩, O₆⟩ := I₆
  have hs₆ := R₆.fr.scr
  have hg := hL.grid_le
  have h16 := st16 K
  have S₆ : SelA K base s₂.mem a 16 s₆ :=
    SelW.stab S₅ U₆ (fun w hw b hb => tbl_byte_apart hL (othW_tbl_apart hL w hw) hb) (by omega) x₆ y₆
      (by rw [R₆.fr.keep.rd, k₅.rd, F₃.keep.rd]) (by rw [R₆.fr.keep.wr, k₅.wr, F₃.keep.wr])
      (R₆.fr.scr.rdi.trans S₅.rdi.symm)
  have z₆ : wordsVal s₆.mem base (TS K 2) K.M.n = K.one := by
    rw [ts_othW hL U₆ hn 2 (by decide), ts_othW hL U₅ hn 2 (by decide)]; exact T₃.one
  -- The entry stored to `T`.
  rw [JacWinCfg.finA, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (storeA_ok hL hnp hs₆ S₆.sel) fun s₇ ⟨a₇, O₇, g₇, r₇, w₇⟩ => ?_
  have e₇ := jselOutA hL S₆.ha a₇
  have hs₇ : Scr s₇ base size := ⟨by rw [g₇]; exact hs₆.rdi, by rw [w₇]; exact hs₆.wr, hs₆.nowrap⟩
  have O₇' : Outside base (jg K 80) (40 * K.M.n) s₆.mem s₇.mem := by
    rw [← hL.T80]; exact O₇.mono (Nat.le_refl _) (by omega)
  have U₇ := outside_grid5 (b := 80) O₇'
  have hU₇W : ∀ w ∈ (List.range 5).map (fun c => (jg K (80 + c), 8 * K.M.n)), w ∈ jwLoopW K := by
    intro w hw; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw; exact T_loopW K (List.mem_range.mp hc)
  have F₇ := R₆.fr.next hL hs₇ ⟨fun r _ => by rw [g₇], r₇, w₇⟩ U₇ (fun w hw => jwLoopW_sub K w (hU₇W w hw))
  have R₇ := R₆.unchW hL F₇ U₇ hU₇W (R_T_apart hL)
  have Ot₇ := O₆.loopW hL (U₇.mono hU₇W) hn
  have z₇ : wordsVal s₇.mem base (jg K 82) K.M.n = K.one := by
    have hz := hL.le (jg_mem (K := K) (i := 82) (by decide))
    rw [O₇.wordsVal (Or.inr (by rw [hL.T80]; unfold jg; omega)) (by omega)]; exact z₆
  -- Its `Y` negated.
  rw [WP.block_append_iff]
  refine WP.mono (decRbx_ok s₇ (j := j - 1) (by omega) (by omega) (by rw [g₇, b₆])) fun s₈ ⟨b₈, k₈⟩ => ?_
  have hs₈ := hs₇.of_keeps k₈ (by decide)
  have m₈ : s₈.mem = s₇.mem := k₈.2.1
  have F₈ := F₇.next hL hs₈ ((Keeps.regs k₈).mono (sub_powClob (by decide))) (W := [])
    (by rw [m₈]; exact Unch.refl _ _ _) (by simp)
  have R₈ := R₇.rbxKeeps hL k₈
  rw [WP.block_append_iff]
  refine WP.mono (jnegA_ok hL hF hone_lt (j := j - 1 - 1) (by omega) R₂.tbl O₂ F₈ b₈ ha S₆.ha
    (fun c hc => by rw [m₈]; exact e₇ c hc) (by rw [m₈]; exact z₇)) fun s₉ ⟨F₉, U₉, kk₉, lt₉, one₉, ent₉⟩ => ?_
  have R₉ := R₈.unchW hL F₉ U₉ (neg_loopW K) (R_neg_apart hL)
  have Ot₉ := (show JTblOne K base s₈ from fun m h1 h16 => by rw [m₈]; exact Ot₇ m h1 h16).loopW hL
    (U₉.mono (neg_loopW K)) hn
  have b₉ : s₉.gpr .rbx = BitVec.ofNat 64 (j - 1 - 1) := by rw [kk₉.gpr _ (rbx_not_clob _), b₈]
  rw [show ([.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 1)] : List Instr) =
    [.alu .add .rbx (.imm 1)] ++ [.alu .cmp .rbx (.imm 1)] from rfl, WP.block_append_iff]
  refine WP.mono (incRbxJ_ok s₉ b₉) fun s₁₀ ⟨b₁₀, k₁₀, _, _⟩ => ?_
  refine WP.mono (cmpRbx1_ok s₁₀ (m := j - 1) (by omega) (by rw [b₁₀, show j - 1 - 1 + 1 = j - 1 by omega]))
    fun s₁₁ ⟨z₁₁, k₁₁⟩ => ?_
  have R₁₁ := (R₉.rbxKeeps hL k₁₀).rbxKeeps hL (k₁₁.mono (by simp))
  have m₁₁ : s₁₁.mem = s₉.mem := by rw [k₁₁.2.1, k₁₀.2.1]
  refine ⟨⟨⟨⟨⟨Q', hQ', hQe', R₁₁⟩, by rw [k₁₁.1 _ (by simp), b₁₀, show j - 1 - 1 + 1 = j - 1 by omega]⟩,
    fun m h1 h16 => by rw [m₁₁]; exact Ot₉ m h1 h16⟩, ?_⟩, z₁₁⟩
  exact (⟨lt₉, one₉, ent₉⟩ : JTA K C base P (k + JacWinCfg.offset K.J) (j - 1 - 1) s₉).congr fun c _ => by
    rw [m₁₁]

/-- `rbx = J - 1`, `R` the top digit's point, and digit `J - 2`'s entry in
`T`. -/
theorem jfirstAP_ok (hL : JacWinLay K size) (hC : Law C) {base : Addr} {P : Point C} (hP : onCurve C P = true)
    {s₀ s : State} {k : Nat} (hF : JacWinFixed K C base s₀ P k) (hpn : C.p < 2 ^ (64 * K.M.n))
    (hone_lt : K.one < C.p) (hJ2 : 2 ≤ K.J) (hkJ : k + JacWinCfg.offset K.J < 32 ^ K.J)
    (hf : JFrame K C base size s₀ s) (hT : JTblOk K C base P 16 s) (hO : JTblOne K base s) :
    WP isa (.block K.firstAP) s fun t => JInvAP K C base size P s₀ k (K.J - 1) t := by
  have hn := hf.scr.nowrap
  have hJ := hL.J
  rw [show K.firstAP = K.first ++ ([.alu .sub .rbx (.imm 1)] ++ ((K.tc.digit ++ K.selectA) ++
      (K.tc.negY ++ [.alu .add .rbx (.imm 1)]))) by simp only [JacWinCfg.firstAP, List.append_assoc],
    WP.block_append_iff]
  refine WP.mono (jfirst_ok hL hC hP hF hkJ hf hT) fun s₁ ⟨I₁, U₁⟩ => ?_
  obtain ⟨⟨Q, hQ, hQe, R₁⟩, b₁⟩ := I₁
  have O₁ := hO.loopW hL U₁ hn
  rw [WP.block_append_iff]
  refine WP.mono (decRbx_ok s₁ (j := K.J - 1) (by omega) (by omega) b₁) fun s₂ ⟨b₂, k₂⟩ => ?_
  have R₂ := R₁.rbxKeeps hL k₂
  have O₂ : JTblOne K base s₂ := fun m h1 h16 => by rw [k₂.2.1]; exact O₁ m h1 h16
  rw [WP.block_append_iff]
  refine WP.mono (jentryA_ok hL hF hpn hone_lt (j := K.J - 1 - 1) (by omega) R₂.fr R₂.tbl O₂ b₂) fun s₃ h₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono h₃ fun s₄ E₄ => ?_
  have R₄ := R₂.unchW hL E₄.fr E₄.unch (jent_loopW K) (R_ent_apart hL)
  have O₄ := O₂.loopW hL (E₄.unch.mono (jent_loopW K)) hn
  refine WP.mono (incRbxJ_ok s₄ (j := K.J - 1 - 1) (by rw [E₄.keep.gpr _ (rbx_not_clob _), b₂]))
    fun t ⟨b₅, k₅, _, _⟩ => ⟨⟨⟨⟨Q, hQ, hQe, R₄.rbxKeeps hL k₅⟩, by rw [b₅, show K.J - 1 - 1 + 1 = K.J - 1 by omega]⟩,
      fun m h1 h16 => by rw [k₅.2.1]; exact O₄ m h1 h16⟩,
      (⟨E₄.lt, E₄.one, E₄.ent⟩ : JTA K C base P (k + JacWinCfg.offset K.J) (K.J - 1 - 1) s₄).congr
        fun c _ => by rw [k₅.2.1]⟩

/-- The last iteration, `rbx = 1`: `R = 32 R + [d_0]P`. -/
theorem jlastA_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl) {P : Point C}
    (hP : onCurve C P = true) (hP0 : P ≠ .infinity) (hn17 : 17 ≤ C.n % 32) (hn64 : 64 ≤ C.n)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    {base : Addr} {s₀ : State} {k : Nat} (hF : JacWinFixed K C base s₀ P k) {s : State}
    (hI : JInvAP K C base size P s₀ k 1 s) :
    WP isa (K.lastA dbl).inline s fun s' => JInvA K C base size P s₀ k 0 s' := by
  obtain ⟨⟨hI, hO1⟩, T₀⟩ := hI
  obtain ⟨Q, hQ, hQe, R₀⟩ := hI.st
  have hn := R₀.fr.scr.nowrap
  have hJ := hL.J
  obtain ⟨tx, ty, -, -, -⟩ := hL.TS_eq
  obtain ⟨mx, my, -, -, -⟩ := hL.T_mem
  rw [JacWinCfg.lastA]
  simp only [Code.inline]
  refine WP.seq (WP.mono (decRbx_ok s (j := 1) (by omega) (by omega) hI.rbx) fun s₁ ⟨b₁, k₁⟩ => ?_)
  have R₁ := R₀.rbxKeeps hL k₁
  have m₁ : s₁.mem = s.mem := k₁.2.1
  rw [← mul_one_pt Q] at R₁
  refine WP.seq (WP.mono (dbls_ok hL hC hD hQ (j := 1 - 1) (by omega) b₁ R₁) fun s₂ ⟨R₂, b₂, U₂⟩ => ?_)
  have O₂ : JTblOne K base s₂ := (show JTblOne K base s₁ from fun m h1 h16 => by
    rw [m₁]; exact hO1 m h1 h16).loopW hL (U₂.mono (jwOthW_loopW K)) hn
  have T₂ : JTA K C base P (k + JacWinCfg.offset K.J) (1 - 1) s₂ := T₀.congr fun c hc => by
    rw [ts_othW hL U₂ hn c (by omega), m₁]
  have V₂ : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y],
      x ∈ jwSlots K ∧ wordsVal s₂.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by jw_mem, R₂.lt _ (by simp)⟩
    · exact ⟨by jw_mem, R₂.lt _ (by simp)⟩
    · exact ⟨by jw_mem, R₂.lt _ (by simp)⟩
    · exact ⟨mx, by rw [← tx]; exact T₂.lt 0 (by decide)⟩
    · exact ⟨my, by rw [← ty]; exact T₂.lt 1 (by decide)⟩
  have I₂ : Inv K.M base size C.p (· ∈ jwSlots K) [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y]
      (tmv C K.M.n base s₂) s₂ :=
    ⟨R₂.fr.scr, R₂.fr.mod, fun x hx => (V₂ x hx).1, fun x hx => (V₂ x hx).2, fun _ _ => rfl⟩
  rw [WP.block_append_iff]
  refine WP.mono (madd_ok hL hp I₂ (fun x hx => hx)) fun s₅ ⟨k₅, E₅, I₅, v₅⟩ => ?_
  exact WP.mono (jmaddA_post hL hp hC hM3 hO hP hP0 hn17 hn64 hone hF (j := 1) (by omega) (by omega) hQ hQe
    R₂ O₂ R₂.fr (Unch.refl _ _ _) (fun _ _ => rfl) b₂ T₂.lt T₂.one T₂.ent k₅ I₅ v₅) fun s₆ h => h.1

/-! ## The window method -/

/-- `winJacA_ok` for `windowAP`, the selections woven into the additions. -/
theorem winJacAP_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C)
    (hM3 : AM3 C) (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    (hn17 : 17 ≤ C.n % 32) (hn64 : 64 ≤ C.n) (hJ3 : 3 ≤ K.J) (hnp : 2 ≤ K.M.n ∧ K.M.n ≤ 10)
    (hsc : ∀ op ∈ maddJ K.S K.R K.E K.D, scalCode (opProg K.MI op) = true)
    (hmk : K.masksA.all scalarI = true) {P : Point C} (hP : onCurve C P = true) {k : Nat}
    (hkJ : k + JacWinCfg.offset K.J < 32 ^ K.J) {inv : Prog isa} {IW : List (Nat × Nat)} {base : Addr}
    (hI : InvSpecJ K C base size inv IW) {s₀ : State}
    (hs₀ : Scr s₀ base size) (hM₀ : ModOkW K.M size C.p s₀.mem base) (hF₀ : JacWinFixed K C base s₀ P k) :
    WP isa (K.windowAP inv dbl).inline s₀ fun s' => KeepRegs (invClob K.M.n) s₀ s' ∧
      Unch base (jwW K ++ IW) s₀.mem s'.mem ∧ ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      (k < C.n → Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y)
        (tmv C K.M.n base s' K.R.z) (mul k P)) := by
  have hn := hs₀.nowrap
  have hJ := hL.J
  have hP0 : P ≠ .infinity := by
    intro h
    have := hF₀.pt
    rw [h, hF₀.pz] at this
    exact hC.one_ne_zero this.2.2
  have pc : ∀ r ∈ powClob K.M.n, r ∈ invClob K.M.n := fun r h => List.mem_cons_of_mem _ h
  rw [JacWinCfg.windowAP]
  simp only [Code.inline]
  refine WP.seq (WP.mono (jbuild_ok hL hp hC hM3 hO hP hP0 (by omega) hs₀ hM₀ hF₀.toJacWinPt) fun s₁ ⟨F₁, T₁⟩ => ?_)
  refine WP.seq (WP.mono (normA_ok hL hp hC hpn hone_lt hone hI F₁.scr F₁.mod T₁)
    fun s ⟨hs, Kn, Un, hM, T₂, O₂⟩ => ?_)
  have U₀ : Unch base (jwW K ++ IW) s₀.mem s.mem := (F₁.unch.trans Un).mono fun w hw => by
    simp only [List.mem_append] at hw ⊢; rcases hw with hw | hw | hw <;> simp [hw]
  have hF : JacWinFixed K C base s P k := hF₀.unchA hL hI U₀ hn
  have K₀ : KeepRegs (invClob K.M.n) s₀ s := (F₁.keep.mono pc).trans Kn
  refine WP.seq (WP.mono (jfirstAP_ok hL hC hP hF hpn hone_lt (by omega) hkJ (JFrame.refl hs hM) T₂ O₂)
    fun s₂ I₂ => ?_)
  refine WP.seq (WP.mono (countLoop_ok (Q := fun t => JInvAP K C base size P s k 1 t)
    (Inv := fun i t => JInvAP K C base size P s k (i + 1) t) (n := K.J - 2)
    (fun i t h1 h2 hi => (jstepAP_ok hL hp hC hM3 hO hD hP hP0 hn17 hn64 hone_lt hone hnp hsc hmk hF
      (j := i + 1) (by omega) (by omega) hi).mono fun t' ⟨I', z'⟩ =>
        ⟨by rw [show i - 1 + 1 = i + 1 - 1 by omega]; exact I', by
          rw [z']; congr 1; exact decide_eq_decide.mpr (by omega)⟩)
    (fun _ h => h) (by omega) (by rw [show K.J - 2 + 1 = K.J - 1 by omega]; exact I₂)) fun s₃ I₃ => ?_)
  refine WP.seq (WP.mono (jlastA_ok hL hp hC hM3 hO hD hP hP0 hn17 hn64 hone hF I₃) fun s₄ I₄ => ?_)
  exact WP.mono (jfinA_ok hL hp hC hpn hone_lt hone hF I₄.1) fun s' ⟨k', u', m', l', r'⟩ =>
    ⟨K₀.trans (k'.mono pc), (U₀.trans u').mono fun w hw => by
      simp only [List.mem_append] at hw ⊢; rcases hw with (hw | hw) | hw <;> simp [hw], m', l', r'⟩

/-- `windowAW`, woven or not: `winJacA_ok`'s postcondition. -/
theorem winJacAW_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C)
    (hM3 : AM3 C) (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    (hn17 : 17 ≤ C.n % 32) (hn64 : 64 ≤ C.n) {P : Point C} (hP : onCurve C P = true) {k : Nat}
    (hkJ : k + JacWinCfg.offset K.J < 32 ^ K.J) {inv : Prog isa} {IW : List (Nat × Nat)} {base : Addr}
    (hI : InvSpecJ K C base size inv IW) {s₀ : State}
    (hs₀ : Scr s₀ base size) (hM₀ : ModOkW K.M size C.p s₀.mem base) (hF₀ : JacWinFixed K C base s₀ P k) :
    WP isa (K.windowAW inv dbl).inline s₀ fun s' => KeepRegs (invClob K.M.n) s₀ s' ∧
      Unch base (jwW K ++ IW) s₀.mem s'.mem ∧ ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      (k < C.n → Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y)
        (tmv C K.M.n base s' K.R.z) (mul k P)) := by
  unfold JacWinCfg.windowAW
  split
  · next hw =>
    simp only [JacWinCfg.weaveAOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hw
    obtain ⟨⟨⟨hJ3, hnp⟩, hsc⟩, hmk⟩ := hw
    exact winJacAP_ok hL hp hC hM3 hO hD hpn hone_lt hone hn17 hn64 hJ3 hnp hsc (List.all_eq_true.mpr hmk)
      hP hkJ hI hs₀ hM₀ hF₀
  · exact winJacA_ok hL hp hC hM3 hO hD hpn hone_lt hone hn17 hn64 hP hkJ hI hs₀ hM₀ hF₀

end VG.Proof.Weierstrass.X86_64
