module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacOddWin
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacOddPSel
public import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacOddP
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacEntry
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacBuild
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJP
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Weierstrass.X86_64.Pow
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacOddEntry
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacOddStep
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacOddBuild
public import VerifiedGarbage.Proof.Weierstrass.JacAdd

/-!
# Odd 5-bit windows on x86-64, each selection woven into the addition before it

`JacWinCfg.windowOP K dbl` (`Impl/Weierstrass/X86_64/WinJacOddP.lean`)
computes what `windowO` does (`winJacOP_ok`, as `winJacO_ok`): its loop keeps
digit `j - 1`'s entry in `T` at `rbx = j` (`JInvOP`). An iteration
(`jstepOP_ok`) doubles `R` five times, which writes neither `T` nor the
table; sets up digit `j - 2`'s selection (`selSetP_ok`); adds `T` to `R`
while it selects (`caddOI_ok`, with `SelP` as the side code's state, which
the addition's operations keep, writing only other slots); and stores and
negates the entry (`storeP_ok`, `jselOut`, `jnegO_ok`). Digit `J - 2`'s
entry is selected before the loop (`jfirstOP_ok`), and digit `0`'s addition
selects none (`jlastO_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-- The woven loop's invariant at `rbx = j`: `JInvO`, and digit `j - 1`'s
point with its powers in `T`. -/
structure JInvOP (K : JacWinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (k : Nat) (j : Nat) (s : State) : Prop where
  inv : JInvO K C base size P s₀ k j s
  ent : JPt C K.M.n base s (TS K) (OddWin.oddPt C P K.J k (j - 1))

/-- `T` survives writes to the other slots and the temporary area. -/
theorem JPt.othW (hL : JacWinLay K size) {base : Addr} {s t : State} {Q : Point C}
    (h : JPt C K.M.n base s (TS K) Q) (hU : Unch base (jwOthW K) s.mem t.mem) (hn : base.toNat + size ≤ 2 ^ 64) :
    JPt C K.M.n base t (TS K) Q :=
  h.congr fun c hc => hU.wordsVal (fun w hw => by
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hw
      exact (hL.jg_apart (List.mem_append_right _ ho) (i := 80 + c) (by omega_arith)).symm
    · rw [List.mem_singleton.mp hw]; exact hL.lay.tmp _ (jg_mem (by omega_arith)))
    (by show jg K (80 + c) + 8 * K.M.n ≤ 2 ^ 64; have := hL.le (jg_mem (K := K) (i := 80 + c) (by omega_arith)); omega_arith)

/-- What the addition writes are other slots. -/
theorem addOpsO_out (K : JacWinCfg) : ∀ op ∈ K.addOpsO, op.out ∈ rcbW K.S K.R := by
  intro op hop
  rw [JacWinCfg.addOpsO, CachedJac.ip_eq] at hop
  obtain ⟨op', hop', rfl⟩ := List.mem_map.mp hop
  rw [FOp.out_rename]
  exact CachedJac.ipσ_out _ _ _ _ _ (CachedJac.ipN_out op' hop')

theorem rcbW_other (K : JacWinCfg) : ∀ x ∈ rcbW K.S K.R, x ∈ jwOther K := by
  intro x hx
  simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> jw_mem

/-- `caddO_ok` with the side code `side i` after operation `i` (`programBI`). -/
theorem caddOI_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {base : Addr}
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv K.M base size C.p (· ∈ jwSlots K) V E s)
    (hV : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2, K.z2 + 8 * K.M.n], x ∈ V)
    (h2 : E K.z2 = E K.E.z * E K.E.z) (h3 : E (K.z2 + 8 * K.M.n) = E K.z2 * E K.E.z)
    {side : Nat → List Instr} {SI : Nat → State → Prop}
    (hside : ∀ i t, i < K.addOpsO.length → SI i t →
      WP isa (.block (side i)) t fun t' => SI (i + 1) t' ∧ ForwardField.SideKeepF t t')
    (hstab : ∀ i o t t', o ∈ rcbW K.S K.R → SI i t → OpKeep K.M base o t t' → t'.xmm = t.xmm →
      t'.ymmHi = t.ymmHi → t'.syms = t.syms → SI i t')
    (hsc : ∀ op ∈ K.addOpsO, (ForwardField.code K.M op).all scalarI = true ∧
      scalCode ((opCall? K.M op).getD (.block (ForwardField.code K.M op))) = true)
    (hS : SI 0 s) :
    WP isa (ForwardField.programBI K.M K.addOpsO side).inline s fun t =>
      ProgKeep K.M base (rcbW K.S K.R) s t ∧ (∃ E' : Nat → Fe C,
        Inv K.M base size C.p (· ∈ jwSlots K) ([K.R.x, K.R.y, K.R.z] ++ V) E' t ∧
        (E' K.R.x, E' K.R.y, E' K.R.z) =
          jacAddF (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y) (E K.E.z)) ∧
      SI K.addOpsO.length t := by
  have hA := hL.ipApart
  have hSl : ∀ x ∈ CachedJac.ipW K.S K.R ++ CachedJac.ipR K.M.n K.S K.E K.z2, x ∈ jwSlots K := by
    intro x hx
    simp only [CachedJac.ipW, CachedJac.ipR, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rw [hL.Tz3, hL.Tx, hL.Ty, hL.Tz, hL.Tz2] at hx
    rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h]
    all_goals first
      | exact jg_mem (by decide) | jw_mem
  have hr : readsOk K.addOpsO V = true := by
    rw [JacWinCfg.addOpsO, CachedJac.ip_eq]
    refine readsOk_mono (readsOk_rename (CachedJac.ipσ K.M.n K.S K.R K.E K.z2)
      (show readsOk (CachedJac.headIPN ++ CachedJac.tailIPN) [6, 7, 8, 11, 12, 13, 14, 15] = true by decide))
      fun x hx => hV x ?_
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with h | h | h | h | h | h | h | h <;> rw [h] <;>
      simp [CachedJac.ipσ, CachedJac.ipW, CachedJac.ipR]
  have hs : ∀ op ∈ K.addOpsO, ∀ x ∈ op.out :: op.ins, x ∈ jwSlots K := by
    rw [JacWinCfg.addOpsO, CachedJac.ip_eq]
    intro op hop x hx
    obtain ⟨op', _, rfl⟩ := List.mem_map.mp hop
    refine hSl x ?_
    cases op' <;> simp only [FOp.rename, FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil,
      or_false] at hx <;> rcases hx with rfl | rfl | rfl <;> exact CachedJac.ipσ_mem ..
  refine WP.mono (ForwardField.programBI_ok hL.lay hp hside hstab _ (addOpsO_out K) (Nat.le_refl _) hsc hI hS hs hr)
    fun t ⟨kt, it, st⟩ => ⟨kt.mono ?_, ⟨_, it.sub fun x hx => ?_, CachedJac.ip_run hA E h2 h3⟩, st⟩
  · intro x hx
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hx
    exact addOpsO_out K op hop
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · right
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [JacWinCfg.addOpsO, jacTail, FOp.out]
    · exact Or.inl hx

/-- `R = R + T` from `u` to `t` (`caddO_ok`'s or `caddOI_ok`'s facts), `R` a
triple of `[32 S_{i+1}]P`'s stand-in `Q` and `T` of digit `i`'s point: `R` a
triple of `[S_i]P`'s, and nothing written but other slots. -/
theorem addO_post (hL : JacWinLay K size) (hC : Law C) (hM3 : AM3 C) (hO : PrimeOrder C) {P : Point C}
    (hP : onCurve C P = true) (hP0 : P ≠ .infinity) (hn2 : C.n % 2 = 1) (hn64 : C.n % 64 < 33)
    (hnb : 128 ≤ C.n) {base : Addr} {s₀ u t : State} {k i : Nat} (hi : i + 1 < K.J)
    {Q : Point C} (hQ : onCurve C Q = true)
    (hQe : k % 2 = 1 ∧ k < C.n → Q = mul (32 * OddWin.oS K.J k (i + 1)) P)
    (F : JFrame K C base size s₀ u) (hT : JTblOkO K C base P 16 u)
    (hRep : InvJ C (tmv C K.M.n base u K.R.x) (tmv C K.M.n base u K.R.y) (tmv C K.M.n base u K.R.z) Q)
    (hE : JPt C K.M.n base u (TS K) (OddWin.oddPt C P K.J k i))
    (k₅ : ProgKeep K.M base (rcbW K.S K.R) u t) {V : List Nat} {E₅ : Nat → Fe C}
    (I₅ : Inv K.M base size C.p (· ∈ jwSlots K) ([K.R.x, K.R.y, K.R.z] ++ V) E₅ t)
    (v₅ : (E₅ K.R.x, E₅ K.R.y, E₅ K.R.z) = jacAddF (tmv C K.M.n base u K.R.x) (tmv C K.M.n base u K.R.y)
      (tmv C K.M.n base u K.R.z) (tmv C K.M.n base u K.E.x) (tmv C K.M.n base u K.E.y) (tmv C K.M.n base u K.E.z)) :
    (∃ Q' : Point C, onCurve C Q' = true ∧ (k % 2 = 1 ∧ k < C.n → Q' = mul (OddWin.oS K.J k i) P) ∧
      RStO K C base size P s₀ Q' t) ∧ Unch base (jwOthW K) u.mem t.mem := by
  have hn := F.scr.nowrap
  obtain ⟨tx, ty, tz, -, -⟩ := hL.TS_eq
  have U₅' : Unch base (jwOthW K) u.mem t.mem := (ProgKeep.unch k₅).mono fun w hw => by
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
      exact List.mem_append_left _ (List.mem_map_of_mem (rcbW_other K x hx))
    · exact List.mem_append_right _ hw
  have U₅ : Unch base (jwLoopW K) u.mem t.mem := U₅'.mono (jwOthW_loopW K)
  have F₅ := F.next hL (k₅.scr F.scr) k₅.regs U₅ (jwLoopW_sub K)
  have Rv : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base t x = E₅ x ∧
      wordsVal t.mem base x K.M.n < C.p := fun x hx => by
    have hm : x ∈ [K.R.x, K.R.y, K.R.z] ++ V := List.mem_append_left _ hx
    exact ⟨I₅.val x hm, I₅.lt x hm⟩
  obtain ⟨Q', hQ', hQe', hR⟩ := jstepO_pt hC hM3 hO hP hP0 hn2 hn64 hnb (k := k) (i := i) (J := K.J) hi hQ hQe hRep
    (Z2 := tmv C K.M.n base u K.E.z) (X2 := tmv C K.M.n base u K.E.x) (Y2 := tmv C K.M.n base u K.E.y)
    (by have J := hE.jac; rw [tx, ty, tz] at J; exact J) (by have J := hE.z; rw [tz] at J; exact J)
  have vx := congrArg Prod.fst v₅
  have vy := congrArg (fun p => p.2.1) v₅
  have vz := congrArg (fun p => p.2.2) v₅
  dsimp only at vx vy vz
  refine ⟨⟨Q', hQ', hQe', F₅, hT.loopW hL U₅ hn (by decide), fun x hx => (Rv x hx).2, ?_⟩, U₅'⟩
  rw [(Rv _ (by simp)).1, (Rv _ (by simp)).1, (Rv _ (by simp)).1, vx, vy, vz]
  exact hR

theorem chunkO_zero (K : JacWinCfg) : K.chunkO 0 = 0 := by
  rw [JacWinCfg.chunkO, Nat.mul_zero, Nat.zero_div]

theorem chunkO_last (K : JacWinCfg) (h : 0 < K.nAddO) : K.chunkO K.nAddO = 16 := by
  rw [JacWinCfg.chunkO, Nat.mul_div_cancel _ h]

/-- `ZF` for `m = 1`, with `rbx = m`. -/
theorem cmpRbx1_ok (s : State) {m : Nat} (hm : m < 2 ^ 63) (hb : s.gpr .rbx = BitVec.ofNat 64 m) :
    WP isa (.block [.alu .cmp .rbx (.imm 1)]) s fun t => t.zf = some (decide (m = 1)) ∧ Keeps [] s t := by
  have e : (BitVec.ofNat 64 m - BitVec.signExtend 64 (1 : BitVec 32) == 0) = decide (m = 1) := by
    have hse : BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 := by decide
    rw [hse]
    by_cases h : m = 1
    · subst h; decide
    · rw [decide_eq_false h, beq_eq_false_iff_ne]
      intro e
      exact h (by bv_omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    Option.some.injEq, exists_eq_left', hb, RegUpd.zf_arithFlags, e]
  refine ⟨trivial, fun r _ => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_arithFlags]

/-- Before digit `rbx = j`'s addition: digit `j - 1`'s entry `a` set up for
its selection, from `s`'s table. -/
theorem prepO_ok (hL : JacWinLay K size) (hn4 : K.M.n = 4) {base : Addr} {P : Point C} {s₀ : State} {k : Nat}
    (hF : JacWinFixedO K C base s₀ P k) {s : State} {j : Nat} (hj1 : 1 ≤ j) (hjJ : j < K.J)
    (hf : JFrame K C base size s₀ s) (hb : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block K.prepO) s fun t =>
      SelP K base s.mem (magO (Window5.nib (OddWin.oq K.J k) (j - 1))) 0 t ∧ Keeps [.rax, .rcx, .rdx, .r8] s t := by
  have hs := hf.scr
  have hn := hs.nowrap
  have hJ := hL.J
  have hbl := hL.bits
  have hbits := hf.bitsO hL hF
  rw [JacWinCfg.prepO, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (decRbx_ok s hj1 (by omega_arith) hb) fun s₁ ⟨b₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (digitO_ok K hs₁ (k := OddWin.oq K.J k) (j := j - 1) (N := 5 * K.J) (by omega_arith) (by omega_arith) b₁
    (fun t ht => by rw [k₁.2.1]; exact hbits t ht)) fun s₂ ⟨_, r₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (incRbxJ_ok s₂ (j := j - 1) (by rw [k₂.1 _ (by decide), b₁])) fun s₃ ⟨b₃, k₃, _, _⟩ => ?_
  have ha := magO_pos (Window5.nib_lt (OddWin.oq K.J k) (j - 1))
  refine WP.mono (selSetP_ok hL hn4 s₃ (base := base) s.mem ha.2 (by rw [k₃.1 _ (by decide), r₂]))
    fun t ⟨S, k₄⟩ => ⟨⟨ha.2, S, ?_, ?_, ?_⟩, ?_⟩
  · intro b _; rw [k₄.2.1, k₃.2.1, k₂.2.1, k₁.2.1]
  · have hg := hL.grid_le
    have := st16 K
    rw [k₄.2.2.2, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]
    exact ⟨_, List.mem_append_right _ hs.wr, hs.contains (d := K.tbl) (by omega_arith) (by omega_arith)⟩
  · rw [k₄.1 _ (by decide), k₃.1 _ (by decide), k₂.1 _ (by decide), k₁.1 _ (by decide)]; exact hs.rdi
  · refine ⟨fun r hr => ?_, by rw [k₄.2.1, k₃.2.1, k₂.2.1, k₁.2.1], by rw [k₄.2.2.1, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1],
      by rw [k₄.2.2.2, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k₄.1 r (by simp [hr.2.1])]
    by_cases hrb : r = .rbx
    · subst hrb; rw [b₃, hb, show j - 1 + 1 = j by omega_arith]
    · rw [k₃.1 r (by simp [hrb]), k₂.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]), k₁.1 r (by simp [hrb])]

theorem nAddO_pos (K : JacWinCfg) : 0 < K.nAddO := by
  rw [JacWinCfg.nAddO, JacWinCfg.addOpsO, CachedJac.ip_eq, List.length_map]; decide

/-- `R`'s state survives writes that miss `R` and keep the frame. -/
theorem RStO.unchW (hL : JacWinLay K size) {base : Addr} {P Q : Point C} {s₀ s t : State}
    (h : RStO K C base size P s₀ Q s) (F : JFrame K C base size s₀ t) {W : List (Nat × Nat)}
    (hU : Unch base W s.mem t.mem) (hW : ∀ w ∈ W, w ∈ jwLoopW K)
    (hR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], ∀ w ∈ W, x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x) :
    RStO K C base size P s₀ Q t := by
  have hn := h.fr.scr.nowrap
  have e : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal t.mem base x K.M.n = wordsVal s.mem base x K.M.n :=
    fun x hx => hU.wordsVal (hR x hx) (by
      have hxo : x ∈ jwOther K := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> jw_mem
      have := hL.le (other_mem hxo); omega_arith)
  have tv : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base t x = tmv C K.M.n base s x := fun x hx => by
    show toM _ _ _ = toM _ _ _; rw [e x hx]
  refine ⟨F, h.tbl.loopW hL (hU.mono hW) hn (by decide), fun x hx => by rw [e x hx]; exact h.lt x hx, ?_⟩
  rw [tv _ (by simp), tv _ (by simp), tv _ (by simp)]; exact h.rep

/-- `R`'s slots miss `T`'s. -/
theorem R_T_apart (hL : JacWinLay K size) :
    ∀ x ∈ [K.R.x, K.R.y, K.R.z], ∀ w ∈ (List.range 5).map (fun c => (jg K (80 + c), 8 * K.M.n)),
      x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro x hx w hw
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
  have hxo : x ∈ jwOther K := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> jw_mem
  exact hL.jg_apart (List.mem_append_right _ hxo) (by have := List.mem_range.mp hc; omega_arith)

/-- `R`'s slots miss what the negation writes. -/
theorem R_neg_apart (hL : JacWinLay K size) :
    ∀ x ∈ [K.R.x, K.R.y, K.R.z], ∀ w ∈ [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n), (jg K 81, 8 * K.M.n)],
      x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro x hx w hw
  have hxo : x ∈ jwOther K := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> jw_mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hL.ap_oth (i := 0) (j := 6) (by decide) (by decide) (by decide)
    · exact hL.ap_oth (i := 1) (j := 6) (by decide) (by decide) (by decide)
    · exact hL.ap_oth (i := 2) (j := 6) (by decide) (by decide) (by decide)
  · exact hL.lay.tmp x (other_mem hxo)
  · exact hL.jg_apart (List.mem_append_right _ hxo) (by decide)

theorem neg_loopW (K : JacWinCfg) :
    ∀ w ∈ [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n), (jg K 81, 8 * K.M.n)], w ∈ jwLoopW K := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact other_loopW (by jw_mem)
  · exact tmp_loopW
  · exact T_loopW K (show 1 < 5 by decide)

/-- An iteration, `2 ≤ j < J`: `R = 32 R + [d_{j-1}]P`, with digit `j - 2`'s
entry selected meanwhile into `T`. -/
theorem jstepOP_ok (hL : JacWinLay K size) (hn4 : K.M.n = 4) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C)
    (hM3 : AM3 C) (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl) {P : Point C}
    (hP : onCurve C P = true) (hP0 : P ≠ .infinity) (hn2 : C.n % 2 = 1) (hn64 : C.n % 64 < 33)
    (hnb : 128 ≤ C.n) {base : Addr} {s₀ : State} {k : Nat} (hF : JacWinFixedO K C base s₀ P k)
    (hsc : ∀ op ∈ K.addOpsO, (ForwardField.code K.M op).all scalarI = true ∧
      scalCode ((opCall? K.M op).getD (.block (ForwardField.code K.M op))) = true)
    {j : Nat} (hj2 : 2 ≤ j) (hjJ : j < K.J) {s : State} (hI : JInvOP K C base size P s₀ k j s) :
    WP isa (K.stepOP dbl).inline s fun s' => JInvOP K C base size P s₀ k (j - 1) s' ∧
      s'.zf = some (decide (j - 1 = 1)) := by
  obtain ⟨⟨⟨Q, hQ, hQe, R₀⟩, hb⟩, T₀⟩ := hI
  have hn := R₀.fr.scr.nowrap
  have hJ := hL.J
  obtain ⟨tx, ty, tz, t2, t3⟩ := hL.TS_eq
  obtain ⟨mx, my, mz, m2, m3⟩ := hL.T_mem
  obtain ⟨h10, h5, hst⟩ := np_four hL hn4
  rw [JacWinCfg.stepOP]
  simp only [Code.inline]
  refine WP.seq (WP.mono (decRbx_ok s (by omega_arith) (by omega_arith) hb) fun s₁ ⟨b₁, k₁⟩ => ?_)
  have R₁ := R₀.rbxKeeps hL k₁
  have T₁ : JPt C K.M.n base s₁ (TS K) (OddWin.oddPt C P K.J k (j - 1)) := T₀.congr fun c _ => by rw [k₁.2.1]
  rw [← mul_one_pt Q] at R₁
  refine WP.seq (WP.mono (dblsO_ok hL hC hD hQ (j := j - 1) (by omega_arith) b₁ R₁) fun s₂ ⟨R₂, b₂, U₂⟩ => ?_)
  have T₂ := T₁.othW hL U₂ hn
  -- Digit `j - 2`'s selection set up.
  refine WP.seq (WP.mono (prepO_ok hL hn4 hF (j := j - 1) (by omega_arith) (by omega_arith) R₂.fr b₂) fun s₃ ⟨S₃, k₃⟩ => ?_)
  have ha16 := magO_pos (Window5.nib_lt (OddWin.oq K.J k) (j - 1 - 1))
  generalize ha : magO (Window5.nib (OddWin.oq K.J k) (j - 1 - 1)) = a at S₃ ha16
  have m₃ : s₃.mem = s₂.mem := k₃.2.1
  have hs₃ := R₂.fr.scr.of_keeps k₃ (by decide)
  have F₃ := R₂.fr.next hL hs₃ ((Keeps.regs k₃).mono (sub_powClob (by decide))) (W := [])
    (by rw [m₃]; exact Unch.refl _ _ _) (by simp)
  have tv₃ : ∀ x, tmv C K.M.n base s₃ x = tmv C K.M.n base s₂ x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [m₃]
  have T₃ : JPt C K.M.n base s₃ (TS K) (OddWin.oddPt C P K.J k (j - 1)) := T₂.congr fun c _ => by rw [m₃]
  have hT₃ : JTblOkO K C base P 16 s₃ := fun m h1 hm => (R₂.tbl m h1 hm).congr fun c _ => by rw [m₃]
  -- `R = R + T`, the selection woven in.
  have V₃ : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2, K.z2 + 8 * K.M.n],
      x ∈ jwSlots K ∧ wordsVal s₃.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by jw_mem, by rw [m₃]; exact R₂.lt _ (by simp)⟩
    · exact ⟨by jw_mem, by rw [m₃]; exact R₂.lt _ (by simp)⟩
    · exact ⟨by jw_mem, by rw [m₃]; exact R₂.lt _ (by simp)⟩
    · exact ⟨mx, by rw [← tx]; exact T₃.lt 0 (by decide)⟩
    · exact ⟨my, by rw [← ty]; exact T₃.lt 1 (by decide)⟩
    · exact ⟨mz, by rw [← tz]; exact T₃.lt 2 (by decide)⟩
    · exact ⟨m2, by rw [← t2]; exact T₃.lt 3 (by decide)⟩
    · exact ⟨m3, by rw [← t3]; exact T₃.lt 4 (by decide)⟩
  have I₃ : Inv K.M base size C.p (· ∈ jwSlots K) [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2,
      K.z2 + 8 * K.M.n] (tmv C K.M.n base s₃) s₃ :=
    ⟨hs₃, F₃.mod, fun x hx => (V₃ x hx).1, fun x hx => (V₃ x hx).2, fun _ _ => rfl⟩
  have h2 := T₃.z2; have h3 := T₃.z3
  rw [t2, tz] at h2; rw [t3, t2, tz] at h3
  have hS₀ : SelP K base s₂.mem a (K.chunkO 0) s₃ := by rw [chunkO_zero]; exact S₃
  refine WP.seq (WP.mono (caddOI_ok hL hp I₃ (fun x hx => hx) h2 h3
    (SI := fun i t => SelP K base s₂.mem a (K.chunkO i) t)
    (fun i t hi h => selChunkO_ok hL hn4 i hi h)
    (fun i o t t' ho h hk hx hy _ => SelP.stab hL (rcbW_other K o ho) hn h hk hx hy) hsc hS₀)
    fun s₅ ⟨k₅, ⟨E₅, I₅, v₅⟩, S₅⟩ => ?_)
  obtain ⟨⟨Q', hQ', hQe', R₅⟩, U₅⟩ := addO_post hL hC hM3 hO hP hP0 hn2 hn64 hnb (k := k) (i := j - 1) (by omega_arith)
    (hC.onCurve_mul hQ 32) (fun hk => by rw [hQe hk, Window5.mul_mul hC hP, show j - 1 + 1 = j by omega_arith]) F₃ hT₃
    (by rw [tv₃, tv₃, tv₃]; exact R₂.rep) T₃ k₅ I₅ v₅
  have hs₅ := R₅.fr.scr
  have hb₅ : s₅.gpr .rbx = BitVec.ofNat 64 (j - 1) := by
    rw [k₅.gpr _ (rbx_not_clob _), k₃.1 _ (by decide), b₂]
  have S₅' : SelS K base s₂.mem a 16 s₅ := by
    have := S₅.sel; rw [show K.addOpsO.length = K.nAddO from rfl, chunkO_last K (nAddO_pos K)] at this; exact this
  -- The entry stored to `T`.
  rw [JacWinCfg.finO, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (storeP_ok hL hn4 hs₅ S₅') fun s₆ ⟨a₆, O₆, g₆, r₆, w₆⟩ => ?_
  have e₆ := jselOut hL hn4 (mem := s₂.mem) (mem' := s₆.mem) ⟨ha16.1, ha16.2⟩ a₆
  have T₆ : JPt C K.M.n base s₆ (TS K) (mul (2 * a - 1) P) := (R₂.tbl a ha16.1 ha16.2).congr fun c hc => e₆ c hc
  have hs₆ : Scr s₆ base size := ⟨by rw [g₆]; exact hs₅.rdi, by rw [w₆]; exact hs₅.wr, hs₅.nowrap⟩
  have O₆' : Outside base (jg K 80) (40 * K.M.n) s₅.mem s₆.mem := by
    rw [← hL.T80, show 40 * K.M.n = 16 * K.np16 by rw [h10, hn4]]; exact O₆
  have U₆ := outside_grid5 (b := 80) O₆'
  have hU₆W : ∀ w ∈ (List.range 5).map (fun c => (jg K (80 + c), 8 * K.M.n)), w ∈ jwLoopW K := by
    intro w hw; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw; exact T_loopW K (List.mem_range.mp hc)
  have F₆ := R₅.fr.next hL hs₆ ⟨fun r _ => by rw [g₆], r₆, w₆⟩ U₆ (fun w hw => jwLoopW_sub K w (hU₆W w hw))
  have R₆ := R₅.unchW hL F₆ U₆ hU₆W (R_T_apart hL)
  -- Its `Y` negated.
  rw [WP.block_append_iff]
  refine WP.mono (decRbx_ok s₆ (j := j - 1) (by omega_arith) (by omega_arith) (by rw [g₆, hb₅])) fun s₇ ⟨b₇, k₇⟩ => ?_
  have hs₇ := hs₆.of_keeps k₇ (by decide)
  have m₇ : s₇.mem = s₆.mem := k₇.2.1
  have F₇ := F₆.next hL hs₇ ((Keeps.regs k₇).mono (sub_powClob (by decide))) (W := [])
    (by rw [m₇]; exact Unch.refl _ _ _) (by simp)
  have R₇ := (R₆.rbxKeeps hL k₇)
  have T₇ : JPt C K.M.n base s₇ (TS K) (mul (2 * magO (Window5.nib (OddWin.oq K.J k) (j - 1 - 1)) - 1) P) := by
    rw [ha]; exact T₆.congr fun c _ => by rw [m₇]
  rw [WP.block_append_iff]
  refine WP.mono (jnegO_ok hL hF (j := j - 1 - 1) (by omega_arith) F₇ b₇ T₇) fun s₈ ⟨F₈, U₈, kk₈, P₈⟩ => ?_
  have R₈ := R₇.unchW hL F₈ U₈ (neg_loopW K) (R_neg_apart hL)
  have b₈ : s₈.gpr .rbx = BitVec.ofNat 64 (j - 1 - 1) := by rw [kk₈.gpr _ (rbx_not_clob _), b₇]
  rw [show ([.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 1)] : List Instr) =
    [.alu .add .rbx (.imm 1)] ++ [.alu .cmp .rbx (.imm 1)] from rfl, WP.block_append_iff]
  refine WP.mono (incRbxJ_ok s₈ b₈) fun s₉ ⟨b₉, k₉, _, _⟩ => ?_
  refine WP.mono (cmpRbx1_ok s₉ (m := j - 1) (by omega_arith) (by rw [b₉, show j - 1 - 1 + 1 = j - 1 by omega_arith]))
    fun s₁₀ ⟨z₁₀, k₁₀⟩ => ?_
  have R₁₀ := (R₈.rbxKeeps hL k₉).rbxKeeps hL (k₁₀.mono (by simp))
  refine ⟨⟨⟨⟨Q', hQ', hQe', R₁₀⟩, by rw [k₁₀.1 _ (by simp), b₉, show j - 1 - 1 + 1 = j - 1 by omega_arith]⟩, ?_⟩, z₁₀⟩
  exact P₈.congr fun c _ => by rw [k₁₀.2.1, k₉.2.1]

/-- `R`'s slots miss what the entry writes. -/
theorem R_ent_apart (hL : JacWinLay K size) :
    ∀ x ∈ [K.R.x, K.R.y, K.R.z], ∀ w ∈ (List.range 5).map (fun c => (jg K (80 + c), 8 * K.M.n)) ++
      [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)], x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro x hx w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact R_T_apart hL x hx w hw
  · exact R_neg_apart hL x hx w (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h))

/-- `rbx = J - 1`, `R = P`, and digit `J - 2`'s entry in `T`. -/
theorem jfirstOP_ok (hL : JacWinLay K size) {base : Addr} {P : Point C} (hP : onCurve C P = true)
    {s₀ s : State} {k : Nat} (hF : JacWinFixedO K C base s₀ P k) (hJ2 : 2 ≤ K.J)
    (hkJ : k ≤ 2 * 32 ^ (K.J - 1)) (hf : JFrame K C base size s₀ s) (hT : JTblOkO K C base P 16 s) :
    WP isa (.block K.firstOP) s fun t => JInvOP K C base size P s₀ k (K.J - 1) t := by
  have hn := hf.scr.nowrap
  have hJ := hL.J
  rw [show K.firstOP = K.firstO ++ ([.alu .sub .rbx (.imm 1)] ++ ((K.digitO ++ K.select) ++
      (K.tc.negY ++ [.alu .add .rbx (.imm 1)]))) by simp only [JacWinCfg.firstOP, List.append_assoc],
    WP.block_append_iff]
  refine WP.mono (jfirstO_ok hL hP hF (by omega_arith) hkJ hf hT) fun s₁ I₁ => ?_
  obtain ⟨⟨Q, hQ, hQe, R₁⟩, b₁⟩ := I₁
  rw [WP.block_append_iff]
  refine WP.mono (decRbx_ok s₁ (j := K.J - 1) (by omega_arith) (by omega_arith) b₁) fun s₂ ⟨b₂, k₂⟩ => ?_
  have R₂ := R₁.rbxKeeps hL k₂
  rw [WP.block_append_iff]
  refine WP.mono (jentryO_ok hL hF (j := K.J - 1 - 1) (by omega_arith) R₂.fr R₂.tbl b₂) fun s₃ h₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono h₃ fun s₄ E₄ => ?_
  have R₄ := R₂.unchW hL E₄.fr E₄.unch (jent_loopW K) (R_ent_apart hL)
  refine WP.mono (incRbxJ_ok s₄ (j := K.J - 1 - 1) (by rw [E₄.keep.gpr _ (rbx_not_clob _), b₂]))
    fun t ⟨b₅, k₅, _, _⟩ => ⟨⟨⟨Q, hQ, hQe, R₄.rbxKeeps hL k₅⟩, by rw [b₅, show K.J - 1 - 1 + 1 = K.J - 1 by omega_arith]⟩,
      E₄.ent.congr fun c _ => by rw [k₅.2.1]⟩

/-- The last iteration, `rbx = 1`: `R = 32 R + [d_0]P`. -/
theorem jlastO_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl) {P : Point C}
    (hP : onCurve C P = true) (hP0 : P ≠ .infinity) (hn2 : C.n % 2 = 1) (hn64 : C.n % 64 < 33)
    (hnb : 128 ≤ C.n) {base : Addr} {s₀ : State} {k : Nat} {s : State}
    (hI : JInvOP K C base size P s₀ k 1 s) :
    WP isa (K.lastO dbl).inline s fun s' => JInvO K C base size P s₀ k 0 s' := by
  obtain ⟨⟨⟨Q, hQ, hQe, R₀⟩, hb⟩, T₀⟩ := hI
  have hn := R₀.fr.scr.nowrap
  have hJ := hL.J
  obtain ⟨tx, ty, tz, t2, t3⟩ := hL.TS_eq
  obtain ⟨mx, my, mz, m2, m3⟩ := hL.T_mem
  rw [JacWinCfg.lastO]
  simp only [Code.inline]
  refine WP.seq (WP.mono (decRbx_ok s (j := 1) (by omega_arith) (by omega_arith) hb) fun s₁ ⟨b₁, k₁⟩ => ?_)
  have R₁ := R₀.rbxKeeps hL k₁
  have T₁ : JPt C K.M.n base s₁ (TS K) (OddWin.oddPt C P K.J k (1 - 1)) := T₀.congr fun c _ => by rw [k₁.2.1]
  rw [← mul_one_pt Q] at R₁
  refine WP.seq (WP.mono (dblsO_ok hL hC hD hQ (j := 1 - 1) (by omega_arith) b₁ R₁) fun s₂ ⟨R₂, b₂, U₂⟩ => ?_)
  have T₂ := T₁.othW hL U₂ hn
  have V₂ : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2, K.z2 + 8 * K.M.n],
      x ∈ jwSlots K ∧ wordsVal s₂.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by jw_mem, R₂.lt _ (by simp)⟩
    · exact ⟨by jw_mem, R₂.lt _ (by simp)⟩
    · exact ⟨by jw_mem, R₂.lt _ (by simp)⟩
    · exact ⟨mx, by rw [← tx]; exact T₂.lt 0 (by decide)⟩
    · exact ⟨my, by rw [← ty]; exact T₂.lt 1 (by decide)⟩
    · exact ⟨mz, by rw [← tz]; exact T₂.lt 2 (by decide)⟩
    · exact ⟨m2, by rw [← t2]; exact T₂.lt 3 (by decide)⟩
    · exact ⟨m3, by rw [← t3]; exact T₂.lt 4 (by decide)⟩
  have I₂ : Inv K.M base size C.p (· ∈ jwSlots K) [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2,
      K.z2 + 8 * K.M.n] (tmv C K.M.n base s₂) s₂ :=
    ⟨R₂.fr.scr, R₂.fr.mod, fun x hx => (V₂ x hx).1, fun x hx => (V₂ x hx).2, fun _ _ => rfl⟩
  have h2 := T₂.z2; have h3 := T₂.z3
  rw [t2, tz] at h2; rw [t3, t2, tz] at h3
  refine WP.mono (caddO_ok hL hp I₂ (fun x hx => hx) h2 h3) fun s₅ ⟨k₅, E₅, I₅, v₅⟩ => ?_
  obtain ⟨⟨Q', hQ', hQe', R₅⟩, -⟩ := addO_post hL hC hM3 hO hP hP0 hn2 hn64 hnb (k := k) (i := 0) (by omega_arith)
    (hC.onCurve_mul hQ 32) (fun hk => by rw [hQe hk, Window5.mul_mul hC hP]) R₂.fr R₂.tbl R₂.rep T₂ k₅ I₅ v₅
  exact ⟨⟨Q', hQ', hQe', R₅⟩, by rw [k₅.gpr _ (rbx_not_clob _), b₂]⟩

/-- `winJacO_ok` for `windowOP`, the selections woven into the additions:
`[k]P` into `R`, in projective coordinates, if `k` is odd and below `n`. -/
theorem winJacOP_ok (hL : JacWinLay K size) (hn4 : K.M.n = 4) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C)
    (hM3 : AM3 C) (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    (hn2 : C.n % 2 = 1) (hn64 : C.n % 64 < 33) (hnb : 128 ≤ C.n) (hJ3 : 3 ≤ K.J)
    (hsc : ∀ op ∈ K.addOpsO, (ForwardField.code K.M op).all scalarI = true ∧
      scalCode ((opCall? K.M op).getD (.block (ForwardField.code K.M op))) = true)
    {P : Point C} (hP : onCurve C P = true)
    {k : Nat} (hkJ : k ≤ 2 * 32 ^ (K.J - 1)) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW K.M size C.p s.mem base) (hF : JacWinFixedO K C base s P k) :
    WP isa (K.windowOP dbl).inline s fun s' => KeepRegs (powClob K.M.n) s s' ∧
      Unch base (jwW K) s.mem s'.mem ∧ ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      (k % 2 = 1 ∧ k < C.n → Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y)
        (tmv C K.M.n base s' K.R.z) (mul k P)) := by
  have hP0 := hF.ne_infinity hC
  rw [JacWinCfg.windowOP]
  simp only [Code.inline]
  refine WP.seq (WP.mono (jbuildO_ok hL hp hC hM3 hO hP hP0 (by omega_arith) hs hM hF.toJacWinPt)
    fun s₁ ⟨F₁, T₁⟩ => ?_)
  refine WP.seq (WP.mono (jfirstOP_ok hL hP hF (by omega_arith) hkJ F₁ T₁) fun s₂ I₂ => ?_)
  refine WP.seq (WP.mono (countLoop_ok (Q := fun t => JInvOP K C base size P s k 1 t)
    (Inv := fun i t => JInvOP K C base size P s k (i + 1) t) (n := K.J - 2)
    (fun i t h1 h2 hi => (jstepOP_ok hL hn4 hp hC hM3 hO hD hP hP0 hn2 hn64 hnb hF hsc (j := i + 1) (by omega_arith)
      (by omega_arith) hi).mono fun t' ⟨I', z'⟩ => ⟨by rw [show i - 1 + 1 = i + 1 - 1 by omega_arith]; exact I', by
        rw [z']; congr 1; exact decide_eq_decide.mpr (by omega_arith)⟩)
    (fun _ h => h) (by omega_arith) (by rw [show K.J - 2 + 1 = K.J - 1 by omega_arith]; exact I₂)) fun s₃ I₃ => ?_)
  refine WP.seq (WP.mono (jlastO_ok hL hp hC hM3 hO hD hP hP0 hn2 hn64 hnb I₃) fun s₄ I₄ => ?_)
  exact jfinO_ok hL hp hC hpn hone_lt hone hF I₄

/-- `windowOW`, woven or not: `winJacO_ok`'s postcondition. -/
theorem winJacOW_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C)
    (hM3 : AM3 C) (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    (hn2 : C.n % 2 = 1) (hn64 : C.n % 64 < 33) (hnb : 128 ≤ C.n) {P : Point C} (hP : onCurve C P = true)
    {k : Nat} (hkJ : k ≤ 2 * 32 ^ (K.J - 1)) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW K.M size C.p s.mem base) (hF : JacWinFixedO K C base s P k) :
    WP isa (K.windowOW dbl).inline s fun s' => KeepRegs (powClob K.M.n) s s' ∧
      Unch base (jwW K) s.mem s'.mem ∧ ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      (k % 2 = 1 ∧ k < C.n → Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y)
        (tmv C K.M.n base s' K.R.z) (mul k P)) := by
  unfold JacWinCfg.windowOW
  split
  · next hw =>
    simp only [JacWinCfg.weaveOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hw
    obtain ⟨⟨hn4, hJ3⟩, hsc⟩ := hw
    exact winJacOP_ok hL hn4 hp hC hM3 hO hD hpn hone_lt hone hn2 hn64 hnb hJ3
      (fun op hop => ⟨List.all_eq_true.mpr (hsc op hop).1, (hsc op hop).2⟩) hP hkJ hs hM hF
  · exact winJacO_ok hL hp hC hM3 hO hD hpn hone_lt hone hn2 hn64 hnb hP hkJ hs hM hF

end VG.Proof.Weierstrass.X86_64
