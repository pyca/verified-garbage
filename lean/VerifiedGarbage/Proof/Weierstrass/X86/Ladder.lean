import VerifiedGarbage.Proof.Weierstrass.X86.Pow

/-!
# Short Weierstrass curves on x86 (32-bit): the ladder

An iteration of `ladder L wk` computes `D = R + R` and `T = D + G` with the
complete addition (`rcb_ok`), and selects `T` into `R` if the scalar's bit
is set, else `D` (`ladderBody_ok`), for the scalar `k` whose bits are the
table at `L.bits`. `ladder_ok` takes the loop's invariant `Q j` on what `R`
holds, and that an iteration keeps it (`Step`): the callers' invariant is
that `R` represents `[k >>> j]P` (`step_rep`, in `Rep.lean`), and only they
need the group law and the algebra it is proven with. The multiplications'
accumulator at `wk` is above the ladder's slots and table (`LadWk`).
-/

namespace VG.Proof.Weierstrass.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass
open Spec.Weierstrass

/-- What a slot holding `x` stands for, modulo `C.p`. -/
abbrev tmv (C : Curve) (n : Nat) (base : Addr) (s : State) (x : Nat) : Fe C :=
  toM C.p (2 ^ (64 * n)) (wordsVal s.mem base x n)

/-- What the ladder writes: `ladW` and the multiplications' accumulator. -/
def ladWx (L : LadderCfg) (wk : Nat) : List (Nat × Nat) := ladW L ++ [(wk, accLen L.M)]

/-- The multiplications' accumulator at `wk`, in the working space above the
ladder's slots, modulus and table. -/
structure LadWk (L : LadderCfg) (size wk : Nat) : Prop where
  le : wk + accLen L.M ≤ size
  sl : ∀ x ∈ ladSlots L, x + 8 * L.M.n ≤ wk
  mo : L.M.mo + 8 * L.M.n ≤ wk
  tmp : L.M.tmp + 8 * L.M.n ≤ wk
  bits : L.bits + L.nbits ≤ wk

theorem LadWk.wk {L : LadderCfg} {size wk : Nat} (h : LadWk L size wk) :
    WkOk L.M size wk (· ∈ ladSlots L) := ⟨h.le, h.sl, h.mo, h.tmp⟩

theorem progW_ladWx {L : LadderCfg} {wk : Nat} {W : List Nat}
    (h : ∀ w ∈ W.map (·, 8 * L.M.n) ++ [(L.M.tmp, 8 * L.M.n)], w ∈ ladW L) :
    ∀ w ∈ progW L.M wk W, w ∈ ladWx L wk := by
  intro w hw
  simp only [progW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  simp only [ladWx, List.mem_append, List.mem_singleton]
  rcases hw with hw | hw | rfl
  · exact .inl (h w (List.mem_append_left _ hw))
  · exact .inl (h w (List.mem_append_right _ (by simp [hw])))
  · exact .inr rfl

/-- A slot the ladder does not write is apart from what it writes. -/
theorem _root_.VG.Proof.Weierstrass.LadLay.apart_wx {L : LadderCfg} {size wk : Nat} (hL : LadLay L size) (hW : LadWk L size wk) {x : Nat}
    (hx : x ∈ ladSlots L) (hxw : x ∉ ladWs L) :
    ∀ w ∈ ladWx L wk, x + 8 * L.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro w hw
  simp only [ladWx, List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | rfl
  · exact hL.apart_w hx hxw w hw
  · exact .inl (hW.sl x hx)

/-- That an iteration keeps the invariant `Q`: from `(X : Y : Z)` that
`Q (j + 1)` accepts, `Q j` accepts `T = D + G` if bit `j` of `k` is set, else
`D = (X : Y : Z) + (X : Y : Z)`, by the complete addition with the curve's
`a`, `3b` and `G` as the slots `L.S.a`, `L.S.b3` and `L.G` hold them. -/
def Step (L : LadderCfg) (C : Curve) (base : Addr) (s : State) (k : Nat)
    (Q : Nat → Fe C → Fe C → Fe C → Prop) : Prop :=
  ∀ j < L.nbits, ∀ X Y Z X2 Y2 Z2 X3 Y3 Z3 : Fe C, Q (j + 1) X Y Z →
    VG.Proof.Weierstrass.rcbAdd (tmv C L.M.n base s L.S.a) (tmv C L.M.n base s L.S.b3) X Y Z X Y Z =
      (X2, Y2, Z2) →
    VG.Proof.Weierstrass.rcbAdd (tmv C L.M.n base s L.S.a) (tmv C L.M.n base s L.S.b3) X2 Y2 Z2
      (tmv C L.M.n base s L.G.x) (tmv C L.M.n base s L.G.y) (tmv C L.M.n base s L.G.z) =
      (X3, Y3, Z3) →
    Q j (if k.testBit j then X3 else X2) (if k.testBit j then Y3 else Y2)
      (if k.testBit j then Z3 else Z2)

/-- The loop's invariant at `esi = j`: `Q j` accepts what `R` holds. -/
structure LadInv (L : LadderCfg) (wk : Nat) (C : Curve) (base : Addr) (size : Nat)
    (Q : Nat → Fe C → Fe C → Fe C → Prop) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  esi : s.gpr .esi = BitVec.ofNat 32 j
  keep : Keeps powClob s₀ s
  unch : Unch base (ladWx L wk) s₀.mem s.mem
  mod : ModOk L.M size C.p s.mem base
  lt : ∀ x ∈ [L.R.x, L.R.y, L.R.z], wordsVal s.mem base x L.M.n < C.p
  q : Q j (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y) (tmv C L.M.n base s L.R.z)

/-- After both additions: `D` and `T` hold `R + R` and `D + G`. -/
structure AddsPost (L : LadderCfg) (wk : Nat) (C : Curve) (base : Addr) (size : Nat) (E : Nat → Fe C)
    (s s' : State) : Prop where
  scr : Scr s' base size
  mod : ModOk L.M size C.p s'.mem base
  keep : Keeps clob s s'
  unch : Unch base (ladWx L wk) s.mem s'.mem
  lt : ∀ x ∈ [L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z], wordsVal s'.mem base x L.M.n < C.p
  vals : ∃ X2 Y2 Z2 X3 Y3 Z3 : Fe C,
    VG.Proof.Weierstrass.rcbAdd (E L.S.a) (E L.S.b3) (E L.R.x) (E L.R.y) (E L.R.z) (E L.R.x)
      (E L.R.y) (E L.R.z) = (X2, Y2, Z2) ∧
    VG.Proof.Weierstrass.rcbAdd (E L.S.a) (E L.S.b3) X2 Y2 Z2 (E L.G.x) (E L.G.y) (E L.G.z) =
      (X3, Y3, Z3) ∧
    tmv C L.M.n base s' L.D.x = X2 ∧ tmv C L.M.n base s' L.D.y = Y2 ∧
    tmv C L.M.n base s' L.D.z = Z2 ∧ tmv C L.M.n base s' L.T.x = X3 ∧
    tmv C L.M.n base s' L.T.y = Y3 ∧ tmv C L.M.n base s' L.T.z = Z3

theorem ProgKeep.keeps {M : Mod} {base : Addr} {wk : Nat} {W : List Nat} {s s' : State}
    (h : ProgKeep M base wk W s s') : Keeps clob s s' := ⟨h.gpr, h.rd, h.wr⟩

/-- The two additions, from a state holding `E` in the slots `ladR`. -/
theorem ladAdds_ok {L : LadderCfg} {wk : Nat} {C : Curve} {base : Addr} {size : Nat} (hL : LadLay L size)
    (hW : LadWk L size wk) (hp : UnitMod C.p (2 ^ (64 * L.M.n))) {E : Nat → Fe C} {s : State}
    (hI : Inv L.M base size C.p (· ∈ ladSlots L) (ladR L) E s) {rest : Prog isa}
    {Q : State → Prop} (h : ∀ s', AddsPost L wk C base size E s s' → WP isa rest s' Q) :
    WP isa (.seq (fprog L.M wk (rcb L.S L.R L.R L.D)) (.seq (fprog L.M wk (rcb L.S L.D L.G L.T)) rest))
      s Q := by
  refine WP.seq (WP.mono (rcb_ok hL.lay hW.wk hp hL.a1 (ladR_S₁ L) hI (ladR_V₁ L))
    fun s₂ ⟨k₂, I₂, t₂, n₂⟩ => ?_)
  refine WP.seq (WP.mono (rcb_ok hL.lay hW.wk hp hL.a2 (ladR_S₂ L) I₂ (ladR_V₂ L))
    fun s₃ ⟨k₃, I₃, t₃, n₃⟩ => h s₃ ?_)
  have hro : ∀ x ∈ ladRo L, x ∉ rcbW L.S L.D := fun x hx h =>
    hL.ro x hx (by simp only [ladWs, List.mem_append]; exact Or.inl (Or.inr h))
  have hDT : ∀ x ∈ [L.D.x, L.D.y, L.D.z], x ∉ rcbW L.S L.T := fun x hx =>
    hL.a2.apart x (by revert x; sub_list)
  have hD : ∀ x ∈ [L.D.x, L.D.y, L.D.z], x ∈ rcbW L.S L.T ++ (rcbW L.S L.D ++ ladR L) := by
    sub_list
  have hT : ∀ x ∈ [L.T.x, L.T.y, L.T.z], x ∈ rcbW L.S L.T ++ (rcbW L.S L.D ++ ladR L) := by
    sub_list
  refine ⟨k₃.scr (k₂.scr hI.scr), I₃.mod, k₂.keeps.trans k₃.keeps,
    (k₂.unch.trans k₃.unch).mono fun w hw => ?_, fun x hx => ?_, ?_⟩
  · rcases List.mem_append.mp hw with hw | hw
    · exact progW_ladWx mem_ladW_D w hw
    · exact progW_ladWx mem_ladW_T w hw
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    exact I₃.lt x (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> mem_list)
  · refine ⟨_, _, _, _, _, _, t₂.symm, ?_, (I₃.val L.D.x (hD L.D.x (by simp))).trans (n₃ L.D.x (hDT L.D.x (by simp))),
      (I₃.val L.D.y (hD L.D.y (by simp))).trans (n₃ L.D.y (hDT L.D.y (by simp))),
      (I₃.val L.D.z (hD L.D.z (by simp))).trans (n₃ L.D.z (hDT L.D.z (by simp))),
      I₃.val L.T.x (hT L.T.x (by simp)), I₃.val L.T.y (hT L.T.y (by simp)),
      I₃.val L.T.z (hT L.T.z (by simp))⟩
    rw [← n₂ L.S.a (hro L.S.a (by simp [ladRo])), ← n₂ L.S.b3 (hro L.S.b3 (by simp [ladRo])),
      ← n₂ L.G.x (hro L.G.x (by simp [ladRo])), ← n₂ L.G.y (hro L.G.y (by simp [ladRo])),
      ← n₂ L.G.z (hro L.G.z (by simp [ladRo]))]
    exact t₃.symm

/-- The mask of the bit, and `R = D` or `T` by it. -/
theorem ladSel_ok {L : LadderCfg} {wk : Nat} {base : Addr} {size : Nat} (hL : LadLay L size)
    (hW : LadWk L size wk) {s : State} (hs : Scr s base size) {t : Nat} (ht : t < L.nbits)
    (hesi : s.gpr .esi = BitVec.ofNat 32 t)
    {c : Bool} (hc : s.mem (off base (L.bits + t)) = if c then 1 else 0) :
    WP isa (.block (bitMask L.bits ++ selPt L.M.n L.R L.D L.T)) s
      fun s' => Scr s' base size ∧ s'.gpr .esi = BitVec.ofNat 32 t ∧
        Keeps [.eax, .ecx, .edx] s s' ∧
        Unch base [(L.R.x, 8 * L.M.n), (L.R.y, 8 * L.M.n), (L.R.z, 8 * L.M.n)] s.mem s'.mem ∧
        wordsVal s'.mem base L.R.x L.M.n =
          (if c then wordsVal s.mem base L.T.x L.M.n else wordsVal s.mem base L.D.x L.M.n) ∧
        wordsVal s'.mem base L.R.y L.M.n =
          (if c then wordsVal s.mem base L.T.y L.M.n else wordsVal s.mem base L.D.y L.M.n) ∧
        wordsVal s'.mem base L.R.z L.M.n =
          (if c then wordsVal s.mem base L.T.z L.M.n else wordsVal s.mem base L.D.z L.M.n) := by
  have hbl := hW.bits
  have hle := hW.le
  refine WP.block_append (WP.mono (bitMask_bool_ok hs hesi (by omega) hc) fun s₄ ⟨c₄, k₄, hm₄⟩ => ?_)
  have hs₄ := hs.of_keeps k₄ (by decide)
  have hap : ∀ x ∈ [L.R.x, L.R.y, L.R.z, L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z],
      ∀ y ∈ [L.R.x, L.R.y, L.R.z, L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z], x ≠ y →
      x + 8 * L.M.n ≤ y ∨ y + 8 * L.M.n ≤ x :=
    fun x hx y hy hxy => hL.lay.apart x y (ladPts_slots L x hx) (ladPts_slots L y hy) hxy
  obtain ⟨rxy, rxz, ryz⟩ := hL.rne
  refine WP.mono (selPt_ok hs₄ c c₄ (n := L.M.n) (o := L.R) (a := L.D) (b := L.T)
    (fun d hd => hL.lay.le d (ladPts_slots L d hd))
    ⟨hap L.R.x (by simp) L.R.y (by simp) rxy, hap L.R.x (by simp) L.R.z (by simp) rxz,
      hap L.R.y (by simp) L.R.z (by simp) ryz⟩
    (fun d hd e he => hap d (List.mem_append_left [L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z] hd) e
      (List.mem_append_right [L.R.x, L.R.y, L.R.z] he) fun h => hL.rdt d hd (h ▸ he)))
    fun s₅ ⟨ex₅, ey₅, ez₅, k₅, O₅⟩ => ?_
  refine ⟨hs₄.of_keeps k₅ (by decide), by rw [k₅.1 _ (by decide), k₄.1 _ (by decide), hesi],
    (k₄.mono (by decide)).widen k₅, by rw [← hm₄]; exact Outs.unch O₅,
    by rw [ex₅, hm₄], by rw [ey₅, hm₄], by rw [ez₅, hm₄]⟩

/-- An iteration. -/
theorem ladderBody_ok {L : LadderCfg} {wk : Nat} {C : Curve} {base : Addr} {size k : Nat}
    {Q : Nat → Fe C → Fe C → Fe C → Prop} (hL : LadLay L size) (hW : LadWk L size wk)
    (hp : UnitMod C.p (2 ^ (64 * L.M.n)))
    {s₀ : State} (hlt₀ : ∀ x ∈ ladRo L, wordsVal s₀.mem base x L.M.n < C.p)
    (hstep : Step L C base s₀ k Q)
    (hbits : ∀ t < L.nbits, s₀.mem (off base (L.bits + t)) = if k.testBit t then 1 else 0)
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ L.nbits) (hI : LadInv L wk C base size Q s₀ s j) :
    WP isa (ladderBody L wk) s fun s' =>
      LadInv L wk C base size Q s₀ s' (j - 1) ∧ s'.zf = some (decide (j - 1 = 0)) := by
  have hn := hI.scr.nowrap
  have hnb := hL.nbits
  -- The slots read only hold what they held at the start.
  have hro : ∀ x ∈ ladRo L, wordsVal s.mem base x L.M.n = wordsVal s₀.mem base x L.M.n :=
    fun x hx => hI.unch.wordsVal
      (hL.apart_wx hW (ladR_slots L x (mem_ladRo_ladR hx)) (hL.ro x hx))
      (by have := hL.lay.le x (ladR_slots L x (mem_ladRo_ladR hx)); omega)
  have hE : ∀ x ∈ ladRo L, tmv C L.M.n base s x = tmv C L.M.n base s₀ x := fun x hx => by
    rw [tmv, hro x hx]
  -- `esi -= 1`.
  rw [ladderBody]
  refine WP.seq (wp_decCounter hj hI.esi fun s₁ b₁ k₁ hm₁ => WP.block_nil ?_)
  have I₁ : Inv L.M base size C.p (· ∈ ladSlots L) (ladR L) (tmv C L.M.n base s) s₁ := by
    refine ⟨hI.scr.of_keeps k₁ (by decide), hm₁ ▸ hI.mod, ladR_slots L, fun x hx => ?_,
      fun x _ => by rw [tmv, hm₁]⟩
    rw [hm₁]
    simp only [ladR, List.mem_append] at hx
    rcases hx with hx | hx
    · rw [hro x hx]; exact hlt₀ x hx
    · exact hI.lt x hx
  -- The additions.
  refine ladAdds_ok hL hW hp I₁ fun s₃ A => ?_
  obtain ⟨X2, Y2, Z2, X3, Y3, Z3, h2, h3, dx, dy, dz, tx, ty, tz⟩ := A.vals
  have hU₃ : Unch base (ladWx L wk) s₀.mem s₃.mem := by
    refine (hI.unch.trans (by rw [← hm₁]; exact A.unch)).mono fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw <;> exact hw
  have hbyte : s₃.mem (off base (L.bits + (j - 1))) = if k.testBit (j - 1) then 1 else 0 := by
    have hbl := hW.bits
    have hle := hW.le
    rw [hU₃.byte (fun w hw => by
      simp only [ladWx, List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · have := hL.bits_w w hw; omega
      · simp only; omega) (by omega), hbits _ (by omega)]
  have hesi₃ : s₃.gpr .esi = BitVec.ofNat 32 (j - 1) := by
    rw [A.keep.1 _ esi_not_clob, b₁]
  have hstep := hstep (j - 1) (by omega) (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y)
    (tmv C L.M.n base s L.R.z) X2 Y2 Z2 X3 Y3 Z3 (by rw [Nat.sub_add_cancel hj]; exact hI.q)
    (by rw [← hE L.S.a (by simp [ladRo]), ← hE L.S.b3 (by simp [ladRo])]; exact h2)
    (by rw [← hE L.S.a (by simp [ladRo]), ← hE L.S.b3 (by simp [ladRo]), ← hE L.G.x (by simp [ladRo]),
        ← hE L.G.y (by simp [ladRo]), ← hE L.G.z (by simp [ladRo])]; exact h3)
  refine WP.block_append (WP.mono (ladSel_ok hL hW A.scr (by omega) hesi₃ hbyte)
    fun s' ⟨hs', b', k', U', ex, ey, ez⟩ => ?_)
  refine wp_testCounter (by omega) b' fun s'' f'' z'' => WP.block_nil ⟨⟨?_, by rw [f''.gpr, b'], ?_, ?_, ?_, ?_, ?_⟩, z''⟩
  · exact hs'.of_keeps (f''.keeps []) (by decide)
  · exact ((hI.keep.widen k₁).trans (A.keep.mono (by decide))).trans
      ((k'.mono (by decide)).trans (f''.keeps _))
  · rw [f''.mem]
    exact (hU₃.trans U').mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact List.mem_append_left _ (mem_ladW_R w hw)
  · have hM := A.mod
    have hmo := hL.lay.mo
    refine ⟨hM.n0, hM.n7, hM.mo, hM.tmp, hM.sep, ?_, hM.inv, hM.red⟩
    rw [f''.mem, U'.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact (hmo L.R.x (ladPts_slots L _ (by simp))).symm
      · exact (hmo L.R.y (ladPts_slots L _ (by simp))).symm
      · exact (hmo L.R.z (ladPts_slots L _ (by simp))).symm) (by have := A.scr.nowrap; have := hM.mo; omega)]
    exact hM.val
  · have hlt := A.lt
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt ⊢
    rw [f''.mem]
    refine ⟨?_, ?_, ?_⟩
    · rw [ex]; split
      · exact hlt.2.2.2.1
      · exact hlt.1
    · rw [ey]; split
      · exact hlt.2.2.2.2.1
      · exact hlt.2.1
    · rw [ez]; split
      · exact hlt.2.2.2.2.2
      · exact hlt.2.2.1
  · have hx : tmv C L.M.n base s'' L.R.x = if k.testBit (j - 1) then X3 else X2 := by
      show toM _ _ _ = _
      rw [f''.mem, ex]; split
      · exact tx
      · exact dx
    have hy : tmv C L.M.n base s'' L.R.y = if k.testBit (j - 1) then Y3 else Y2 := by
      show toM _ _ _ = _
      rw [f''.mem, ey]; split
      · exact ty
      · exact dy
    have hz : tmv C L.M.n base s'' L.R.z = if k.testBit (j - 1) then Z3 else Z2 := by
      show toM _ _ _ = _
      rw [f''.mem, ez]; split
      · exact tz
      · exact dz
    rw [hx, hy, hz]
    exact hstep

/-- `Q 0` accepts what `R` holds at the end, if `Q L.nbits` accepts what it
holds at the start and an iteration keeps `Q` (`Step`), for the scalar `k`
whose bits are the table at `L.bits`; only `powClob` and `ladWx` change. -/
theorem ladder_ok {L : LadderCfg} {wk : Nat} {C : Curve} {base : Addr} {size k : Nat}
    {Q : Nat → Fe C → Fe C → Fe C → Prop} (hL : LadLay L size) (hW : LadWk L size wk)
    (hp : UnitMod C.p (2 ^ (64 * L.M.n)))
    {s : State} (hs : Scr s base size) (hM : ModOk L.M size C.p s.mem base)
    (hlt : ∀ x ∈ ladR L, wordsVal s.mem base x L.M.n < C.p) (hstep : Step L C base s k Q)
    (hR : Q L.nbits (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y) (tmv C L.M.n base s L.R.z))
    (hbits : ∀ t < L.nbits, s.mem (off base (L.bits + t)) = if k.testBit t then 1 else 0) :
    WP isa (ladder L wk) s fun s' => Keeps powClob s s' ∧ Unch base (ladWx L wk) s.mem s'.mem ∧
      ModOk L.M size C.p s'.mem base ∧
      (∀ x ∈ [L.R.x, L.R.y, L.R.z], wordsVal s'.mem base x L.M.n < C.p) ∧
      Q 0 (tmv C L.M.n base s' L.R.x) (tmv C L.M.n base s' L.R.y) (tmv C L.M.n base s' L.R.z) := by
  have hnb := hL.nbits
  rw [ladder]
  refine WP.seq (wp_movS rfl fun s₁ u₁ _ => WP.block_nil ?_)
  have hm₁ : s₁.mem = s.mem := u₁.mem
  refine countLoop_ok (Inv := fun j s' => LadInv L wk C base size Q s s' j) (n := L.nbits)
    (fun j s' h1 h2 hi => ladderBody_ok hL hW hp (fun x hx => hlt x (mem_ladRo_ladR hx))
      hstep hbits h1 h2 hi)
    (fun s' hi => ⟨hi.keep, hi.unch, hi.mod, hi.lt, hi.q⟩)
    hnb.1 ?_
  refine ⟨hs.of_keeps u₁.keeps (by decide), u₁.gpr, u₁.keeps.mono (by decide),
    by rw [hm₁]; exact Unch.refl _ _ _, hm₁ ▸ hM,
    fun x hx => by rw [hm₁]; exact hlt x (List.mem_append_right _ hx), ?_⟩
  simp only [tmv, hm₁]
  exact hR

end VG.Proof.Weierstrass.X86
