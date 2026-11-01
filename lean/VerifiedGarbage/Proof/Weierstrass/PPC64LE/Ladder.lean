module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Fprog
public import VerifiedGarbage.Proof.Weierstrass.Rcb0
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow
public import VerifiedGarbage.Proof.Weierstrass.Layout
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Bits
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Loop
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The ladder, on PPC64LE

An iteration of `ladder L S` (`Impl/Weierstrass/PPC64LE.lean`) computes
`D = R + R` and `T = D + G` with the complete addition (`rcb_ok`), and
selects `T` into `R` if the scalar's bit is set, else `D`
(`ladderBody_ok`), for the scalar `k` whose bits are the table at `L.bits`,
as on 32-bit ARM (`Proof/Weierstrass/Arm/Ladder.lean`). `ladder_ok` takes the
loop's invariant `Q j` on what `R` holds, and that an iteration keeps it
(`Step`): the callers' invariant is that `R` represents `[k >>> j]P`
(`step_rep`, in `Rep.lean`), and only they need the group law. The field
arithmetic is calls of the functions of `S`, whose own working space is
above the ladder's slots (`LadLay` of `own n` bytes) and below its table
(`LadLayI`). This is the ladder of curves whose points do not fit the point
functions' slots (`ladderP`, for coordinates of more than 6 words).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Point

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Spec.Weierstrass (Curve Fe)

/-- What a slot holding `x` stands for, modulo `C.p`. -/
abbrev tmv (C : Curve) (n : Nat) (base : Addr) (s : State) (x : Nat) : Fe C :=
  toM C.p (2 ^ (64 * n)) (wordsVal s.mem base x n)

/-- That an iteration keeps the invariant `Q`: from `(X : Y : Z)` that
`Q (j + 1)` accepts, `Q j` accepts `T = D + G` if bit `j` of `k` is set, else
`D = (X : Y : Z) + (X : Y : Z)`, by the complete addition with the curve's
`a`, `3b` and `G` as the slots `L.S.a`, `L.S.b3` and `L.G` hold them (for
`a0`, by the formulas for `a = 0`). -/
def Step (L : LadderCfg) (C : Curve) (base : Addr) (s : State) (k : Nat)
    (Q : Nat → Fe C → Fe C → Fe C → Prop) (a0 : Bool := false) : Prop :=
  ∀ j < L.nbits, ∀ X Y Z X2 Y2 Z2 X3 Y3 Z3 : Fe C, Q (j + 1) X Y Z →
    ladDbl a0 (tmv C L.M.n base s L.S.a) (tmv C L.M.n base s L.S.b3) X Y Z = (X2, Y2, Z2) →
    ladAdd a0 (tmv C L.M.n base s L.S.a) (tmv C L.M.n base s L.S.b3) X2 Y2 Z2
      (tmv C L.M.n base s L.G.x) (tmv C L.M.n base s L.G.y) (tmv C L.M.n base s L.G.z) =
      (X3, Y3, Z3) →
    Q j (if k.testBit j then X3 else X2) (if k.testBit j then Y3 else Y2)
      (if k.testBit j then Z3 else Z2)

/-- What the ladder writes: `ladW` and the functions' own working space. -/
def ladWx (L : LadderCfg) : List (Nat × Nat) := ladW L ++ [(own L.M.n, 64 * L.M.n)]

/-- The ladder's slots: `LadLay` below the functions' own working space, at
multiples of 4, with the table of bits above it and its length an
immediate. -/
structure LadLayI (L : LadderCfg) : Prop where
  lay : LadLay L (own L.M.n) 8192
  al : ∀ x ∈ ladSlots L, x % 4 = 0
  bits : 4096 ≤ L.bits
  nbits : L.nbits < 2 ^ 15

theorem own_add (n : Nat) (h : 8 * n ≤ own n) : own n + 64 * n = 4096 := by
  simp only [own, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes] at h ⊢; omega

/-- A slot the ladder does not write is apart from what it writes. -/
theorem LadLayI.apart_wx {L : LadderCfg} (hL : LadLayI L) {x : Nat} (hx : x ∈ ladSlots L)
    (hxw : x ∉ ladWs L) : ∀ w ∈ ladWx L, x + 8 * L.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro w hw
  simp only [ladWx, List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | rfl
  · exact hL.lay.apart_w hx hxw w hw
  · exact .inl (hL.lay.lay.le x hx)

/-- The table of bits is apart from what the ladder writes. -/
theorem LadLayI.bits_wx {L : LadderCfg} (hL : LadLayI L) {t : Nat} (ht : t < L.nbits) :
    ∀ w ∈ ladWx L, L.bits + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ L.bits + t := by
  have hR := hL.lay.lay.le _ (ladPts_slots L L.R.x (by simp))
  have ho := own_add L.M.n (by omega)
  have hb := hL.bits
  intro w hw
  simp only [ladWx, List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | rfl
  · have := hL.lay.bits_w w hw; omega
  · simp only; omega

/-- The loop's invariant at `r31 = j`: `Q j` accepts what `R` holds. -/
structure LadInv (L : LadderCfg) (C : Curve) (base : Addr) (Q : Nat → Fe C → Fe C → Fe C → Prop)
    (s₀ s : State) (j : Nat) : Prop where
  ws : WsReg s base
  r31 : s.gpr .r31 = BitVec.ofNat 64 j
  keep : Rk powClob s₀ s
  unch : Unch base (ladWx L) s₀.mem s.mem
  lt : ∀ x ∈ [L.R.x, L.R.y, L.R.z], wordsVal s.mem base x L.M.n < C.p
  q : Q j (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y) (tmv C L.M.n base s L.R.z)

/-- After both additions: `D` and `T` hold `R + R` and `D + G`. -/
structure AddsPost (L : LadderCfg) (C : Curve) (base : Addr) (E : Nat → Fe C) (s s' : State) : Prop where
  ws : WsReg s' base
  keep : Rk fnClob s s'
  unch : Unch base (ladWx L) s.mem s'.mem
  lt : ∀ x ∈ [L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z], wordsVal s'.mem base x L.M.n < C.p
  vals : ∃ X2 Y2 Z2 X3 Y3 Z3 : Fe C,
    VG.Proof.Weierstrass.rcbAdd (E L.S.a) (E L.S.b3) (E L.R.x) (E L.R.y) (E L.R.z) (E L.R.x)
      (E L.R.y) (E L.R.z) = (X2, Y2, Z2) ∧
    VG.Proof.Weierstrass.rcbAdd (E L.S.a) (E L.S.b3) X2 Y2 Z2 (E L.G.x) (E L.G.y) (E L.G.z) =
      (X3, Y3, Z3) ∧
    tmv C L.M.n base s' L.D.x = X2 ∧ tmv C L.M.n base s' L.D.y = Y2 ∧
    tmv C L.M.n base s' L.D.z = Z2 ∧ tmv C L.M.n base s' L.T.x = X3 ∧
    tmv C L.M.n base s' L.T.y = Y3 ∧ tmv C L.M.n base s' L.T.z = Z3

/-- What a program writing the slots `W` of `ladWs`, through the functions,
changes of what the ladder writes. -/
theorem keep_unch {L : LadderCfg} {base : Addr} {W : List Nat} {s s' : State}
    (h : KeepR L.M.n (fun x => x) base W s s') (hW : ∀ w ∈ W, w ∈ ladWs L) :
    Unch base (ladWx L) s.mem s'.mem :=
  fun x hx => h.mem x fun r hr => hx r (by
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
    simp only [ladWx, ladW, List.mem_append, List.mem_map, List.mem_singleton]
    rcases hr with ⟨w, hw, rfl⟩ | rfl
    · exact .inl (.inl ⟨w, hW w hw, rfl⟩)
    · exact .inr rfl)

/-- The two additions, from a state holding `E` in the slots `ladR`. -/
theorem ladAdds_ok {L : LadderCfg} {C : Curve} {base : Addr} (hL : LadLayI L)
    {S : Impl.Weierstrass.Mont.Modulus} (hM : ModOk S.k S.m) (hkS : S.k = L.M.n) (hmS : S.m = C.p)
    (hp : UnitMod C.p (2 ^ (64 * L.M.n))) {E : Nat → Fe C} {s : State}
    (hI : Inv L.M.n base C.p (· ∈ ladSlots L) (ladR L) E s) {rest : Prog isa}
    {Q : State → Prop} (h : ∀ s', AddsPost L C base E s s' → WP isa rest s' Q) :
    WP isa (.seq (fprog S (rcb L.S L.R L.R L.D)) (.seq (fprog S (rcb L.S L.D L.G L.T)) rest))
      s Q := by
  obtain ⟨c, w, m', k', d⟩ := S
  dsimp only at hkS hmS hM ⊢
  subst hkS hmS
  have hL' := hL.lay
  refine WP.seq (WP.mono (rcb_ok (S' := ⟨c, w, C.p, L.M.n, d⟩) hM rfl hL'.lay hp hL'.a1 (ladR_S₁ L) hI
    (ladR_V₁ L)) fun s₂ ⟨k₂, I₂, t₂, n₂⟩ => ?_)
  refine WP.seq (WP.mono (rcb_ok (S' := ⟨c, w, C.p, L.M.n, d⟩) hM rfl hL'.lay hp hL'.a2 (ladR_S₂ L) I₂
    (ladR_V₂ L)) fun s₃ ⟨k₃, I₃, t₃, n₃⟩ => h s₃ ?_)
  have hro : ∀ x ∈ ladRo L, x ∉ rcbW L.S L.D := fun x hx h =>
    hL'.ro x hx (by simp only [ladWs, List.mem_append]; exact Or.inl (Or.inr h))
  have hDT : ∀ x ∈ [L.D.x, L.D.y, L.D.z], x ∉ rcbW L.S L.T := fun x hx =>
    hL'.a2.apart x (by revert x; sub_list)
  have hD : ∀ x ∈ [L.D.x, L.D.y, L.D.z], x ∈ rcbW L.S L.T ++ (rcbW L.S L.D ++ ladR L) := by
    sub_list
  have hT : ∀ x ∈ [L.T.x, L.T.y, L.T.z], x ∈ rcbW L.S L.T ++ (rcbW L.S L.D ++ ladR L) := by
    sub_list
  refine ⟨I₃.ws, ⟨fun r hr => (k₃.gpr r hr).trans (k₂.gpr r hr), k₃.rd.trans k₂.rd, k₃.wr.trans k₂.wr,
    k₃.sp.trans k₂.sp⟩, ((keep_unch k₂ fun w hw => ?_).trans (keep_unch k₃ fun w hw => ?_)).mono
      fun w hw => ?_, fun x hx => ?_, ?_⟩
  · simp only [ladWs, List.mem_append]; exact .inl (.inr hw)
  · simp only [ladWs, List.mem_append]; exact .inr hw
  · rcases List.mem_append.mp hw with hw | hw <;> exact hw
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
theorem ladSel_ok {L : LadderCfg} {base : Addr} (hL : LadLayI L) {s : State} (hw : WsReg s base)
    {t : Nat} (ht : t < L.nbits) (h31 : s.gpr .r31 = BitVec.ofNat 64 t)
    {c : Bool} (hc : s.mem (off base (L.bits + t)) = if c then 1 else 0) :
    WP isa (.block (bitMask L.bits ++ selPt L.M.n L.R L.D L.T)) s
      fun s' => Kp [.r4, .r5, .r10] s s' ∧
        Unch base [(L.R.x, 8 * L.M.n), (L.R.y, 8 * L.M.n), (L.R.z, 8 * L.M.n)] s.mem s'.mem ∧
        wordsVal s'.mem base L.R.x L.M.n =
          (if c then wordsVal s.mem base L.T.x L.M.n else wordsVal s.mem base L.D.x L.M.n) ∧
        wordsVal s'.mem base L.R.y L.M.n =
          (if c then wordsVal s.mem base L.T.y L.M.n else wordsVal s.mem base L.D.y L.M.n) ∧
        wordsVal s'.mem base L.R.z L.M.n =
          (if c then wordsVal s.mem base L.T.z L.M.n else wordsVal s.mem base L.D.z L.M.n) := by
  have hlb := hL.lay.bits
  have hx := hL.lay.lay.le _ (ladPts_slots L L.R.x (by simp))
  have ho := own_add L.M.n (by omega)
  refine wp_append (WP.mono (bitMask_bool_ok hw.ws hw.at3 h31 (by omega) (c := c) hc)
    fun s₄ ⟨c₄, k₄, hm₄⟩ => ?_)
  have hap : ∀ x ∈ [L.R.x, L.R.y, L.R.z, L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z],
      ∀ y ∈ [L.R.x, L.R.y, L.R.z, L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z], x ≠ y →
      x + 8 * L.M.n ≤ y ∨ y + 8 * L.M.n ≤ x :=
    fun x hx y hy hxy => hL.lay.lay.apart x y (ladPts_slots L x hx) (ladPts_slots L y hy) hxy
  obtain ⟨rxy, rxz, ryz⟩ := hL.lay.rne
  refine WP.mono (selPt_ok (k₄.ws hw.ws) (k₄.at hw.at3) c c₄ (n := L.M.n) (o := L.R) (a := L.D) (b := L.T)
    (fun d hd => hL.al d (ladPts_slots L d hd))
    (fun d hd => by have := hL.lay.lay.le d (ladPts_slots L d hd); omega)
    ⟨hap L.R.x (by simp) L.R.y (by simp) rxy, hap L.R.x (by simp) L.R.z (by simp) rxz,
      hap L.R.y (by simp) L.R.z (by simp) ryz⟩
    (fun d hd e he => hap d (List.mem_append_left [L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z] hd) e
      (List.mem_append_right [L.R.x, L.R.y, L.R.z] he) fun h => hL.lay.rdt d hd (h ▸ he)))
    fun s₅ ⟨ex₅, ey₅, ez₅, k₅, O₅⟩ => ?_
  refine ⟨k₄.trans (k₅.mono (by decide)), by rw [← hm₄]; exact O₅, by rw [ex₅, hm₄], by rw [ey₅, hm₄],
    by rw [ez₅, hm₄]⟩

section body
variable {L : LadderCfg} {C : Curve} {base : Addr}

/-- An iteration. -/
theorem ladderBody_ok {k : Nat} {Q : Nat → Fe C → Fe C → Fe C → Prop} {S : Impl.Weierstrass.Mont.Modulus}
    (hM : ModOk S.k S.m) (hkS : S.k = L.M.n) (hmS : S.m = C.p) (hp : UnitMod C.p (2 ^ (64 * L.M.n)))
    (hL : LadLayI L) {s₀ : State} (hlt₀ : ∀ x ∈ ladRo L, wordsVal s₀.mem base x L.M.n < C.p)
    (hstep : Step L C base s₀ k Q)
    (hbits : ∀ t < L.nbits, s₀.mem (off base (L.bits + t)) = if k.testBit t then 1 else 0)
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ L.nbits) (hI : LadInv L C base Q s₀ s j) :
    WP isa (ladderBody L S) s fun s' => LadInv L C base Q s₀ s' (j - 1) := by
  have hn := hI.ws.nowrap
  have hnb := hL.lay.nbits
  have hlb := hL.lay.bits
  -- The slots read only hold what they held at the start.
  have hro : ∀ x ∈ ladRo L, wordsVal s.mem base x L.M.n = wordsVal s₀.mem base x L.M.n :=
    fun x hx => hI.unch.wordsVal
      (hL.apart_wx (ladR_slots L x (mem_ladRo_ladR hx)) (hL.lay.ro x hx))
      (by have := hL.lay.lay.le x (ladR_slots L x (mem_ladRo_ladR hx)); have := own_lt L.M.n; omega)
  have hE : ∀ x ∈ ladRo L, tmv C L.M.n base s x = tmv C L.M.n base s₀ x := fun x hx => by
    rw [tmv, hro x hx]
  -- `r31 -= 1`.
  rw [ladderBody]
  refine WP.seq (wp_decCounter hj hI.r31 (WP.block_nil ?_))
  generalize hs₁ : s.write .r31 (BitVec.ofNat 64 (j - 1)) = s₁
  have K₁ : Kp [.r31] s s₁ := by rw [← hs₁]; exact Kp.write _ _ (by decide)
  have m₁ : s₁.mem = s.mem := by rw [← hs₁]; rfl
  have c₁ : s₁.gpr .r31 = BitVec.ofNat 64 (j - 1) := by rw [← hs₁]; simp only [write_gpr, ite_true]
  have I₁ : Inv L.M.n base C.p (· ∈ ladSlots L) (ladR L) (tmv C L.M.n base s) s₁ := by
    refine ⟨hI.ws.of_kp K₁, ladR_slots L, fun x hx => ?_, fun x _ => by rw [tmv, m₁]⟩
    rw [m₁]
    simp only [ladR, List.mem_append] at hx
    rcases hx with hx | hx
    · rw [hro x hx]; exact hlt₀ x hx
    · exact hI.lt x hx
  -- The additions.
  refine ladAdds_ok hL hM hkS hmS hp I₁ fun s₃ A => ?_
  obtain ⟨X2, Y2, Z2, X3, Y3, Z3, h2, h3, dx, dy, dz, tx, ty, tz⟩ := A.vals
  have hU₃ : Unch base (ladWx L) s₀.mem s₃.mem :=
    (hI.unch.trans (by rw [← m₁]; exact A.unch)).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw <;> exact hw
  have hbyte : s₃.mem (off base (L.bits + (j - 1))) = if k.testBit (j - 1) then 1 else 0 := by
    rw [hU₃.byte (hL.bits_wx (by omega)) (by omega), hbits _ (by omega)]
  have c₃ : s₃.gpr .r31 = BitVec.ofNat 64 (j - 1) := by rw [A.keep.g, c₁]
  have hstep := hstep (j - 1) (by omega) (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y)
    (tmv C L.M.n base s L.R.z) X2 Y2 Z2 X3 Y3 Z3 (by rw [Nat.sub_add_cancel hj]; exact hI.q)
    (by rw [← hE L.S.a (by simp [ladRo]), ← hE L.S.b3 (by simp [ladRo])]; exact h2)
    (by rw [← hE L.S.a (by simp [ladRo]), ← hE L.S.b3 (by simp [ladRo]), ← hE L.G.x (by simp [ladRo]),
        ← hE L.G.y (by simp [ladRo]), ← hE L.G.z (by simp [ladRo])]; exact h3)
  have K₃ : Rk powClob s₀ s₃ :=
    (hI.keep.trans (K₁.rk (rs' := powClob))).trans (A.keep.mono (rs' := powClob))
  refine WP.mono (ladSel_ok hL A.ws (by omega) c₃ hbyte) fun s' ⟨k', U', ex, ey, ez⟩ => ?_
  refine ⟨A.ws.of_kp k', by rw [k'.g, c₃], K₃.trans (k'.rk (rs' := powClob)), ?_, ?_, ?_⟩
  · exact (hU₃.trans U').mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact List.mem_append_left _ (mem_ladW_R w hw)
  · have hlt := A.lt
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt ⊢
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
  · have hx : tmv C L.M.n base s' L.R.x = if k.testBit (j - 1) then X3 else X2 := by
      show toM _ _ _ = _
      rw [ex]; split
      · exact tx
      · exact dx
    have hy : tmv C L.M.n base s' L.R.y = if k.testBit (j - 1) then Y3 else Y2 := by
      show toM _ _ _ = _
      rw [ey]; split
      · exact ty
      · exact dy
    have hz : tmv C L.M.n base s' L.R.z = if k.testBit (j - 1) then Z3 else Z2 := by
      show toM _ _ _ = _
      rw [ez]; split
      · exact tz
      · exact dz
    rw [hx, hy, hz]
    exact hstep

/-- `Q 0` accepts what `R` holds at the end, if `Q L.nbits` accepts what it
holds at the start and an iteration keeps `Q` (`Step`), for the scalar `k`
whose bits are the table at `L.bits`; only `powClob` and `ladWx` change. -/
theorem ladder_ok {k : Nat} {Q : Nat → Fe C → Fe C → Fe C → Prop} {S : Impl.Weierstrass.Mont.Modulus}
    (hM : ModOk S.k S.m) (hkS : S.k = L.M.n) (hmS : S.m = C.p) (hp : UnitMod C.p (2 ^ (64 * L.M.n)))
    (hL : LadLayI L) {s : State} (hs : WsReg s base)
    (hlt : ∀ x ∈ ladR L, wordsVal s.mem base x L.M.n < C.p) (hstep : Step L C base s k Q)
    (hR : Q L.nbits (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y) (tmv C L.M.n base s L.R.z))
    (hbits : ∀ t < L.nbits, s.mem (off base (L.bits + t)) = if k.testBit t then 1 else 0) :
    WP isa (ladder L S) s fun s' => Rk powClob s s' ∧ Unch base (ladWx L) s.mem s'.mem ∧
      (∀ x ∈ [L.R.x, L.R.y, L.R.z], wordsVal s'.mem base x L.M.n < C.p) ∧
      Q 0 (tmv C L.M.n base s' L.R.x) (tmv C L.M.n base s' L.R.y) (tmv C L.M.n base s' L.R.z) := by
  have hnb := hL.lay.nbits
  have hnb' := hL.nbits
  rw [ladder]
  refine WP.seq (wp_step (exec_li hnb') (WP.block_nil ?_))
  have K₁ : Kp [.r31] s (s.write .r31 (BitVec.ofNat 64 L.nbits)) := Kp.write _ _ (by decide)
  refine countLoop_ok (Inv := fun j s' => LadInv L C base Q s s' j) (n := L.nbits)
    (fun j s' hi => hi.r31)
    (fun j s' h1 h2 hi => ladderBody_ok hM hkS hmS hp hL (fun x hx => hlt x (mem_ladRo_ladR hx))
      hstep hbits h1 h2 hi)
    (fun s' hi => ⟨hi.keep, hi.unch, hi.lt, hi.q⟩) hnb.1 (by omega)
    ⟨hs.of_kp K₁, by simp only [write_gpr, ite_true], K₁.rk, Unch.refl _ _ _,
      fun x hx => hlt x (List.mem_append_right _ hx), hR⟩

end body

end VG.Proof.Weierstrass.PPC64LE.Point
