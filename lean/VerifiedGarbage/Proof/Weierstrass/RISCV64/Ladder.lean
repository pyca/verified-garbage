module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Fprog
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Copy
public import VerifiedGarbage.Proof.Weierstrass.Layout
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.Pow
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Exec

/-!
# The ladder, on RISC-V

An iteration of `ladder L F` (`Impl/Weierstrass/RISCV64.lean`) computes
`D = R + R` and `T = D + G` with the complete addition (`rcb_ok`), and
selects `T` into `R` if the scalar's bit is set, else `D`
(`ladderBody_ok`), for the scalar `k`, the number at `L.bits` whose bit
`bitMask` reads (`bitMask_ok`), as on PPC64LE
(`Proof/Weierstrass/PPC64LE/Ladder.lean`). `ladder_ok` takes the loop's
invariant `Q j` on what `R` holds, and that an iteration keeps it (`Step`):
the callers' invariant is that `R` represents `[k >>> j]P` (`step_rep`), and
only they need the group law. The field arithmetic is calls of the
functions of `F`, whose own working space is above the ladder's slots
(`LadLayR`).

`pow P F` leaves `[acc]` reading (in Montgomery form) as `[base]^e`, for the
exponent `e`, the number at `P.bits` (`pow_ok`): an iteration squares the
accumulator, multiplies it by the base into `[tmp]` and keeps that product if
the exponent's bit is set (`powBody_ok`), as on PPC64LE
(`Proof/Weierstrass/PPC64LE/Pow.lean`).
-/

-- separate module: curve-generic, and its proofs (about 3 s) build in parallel with those of
-- the field functions that its importer also imports

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.RISCV64 (Rest wp_and)
open VG.Spec.Weierstrass (Curve Fe Point)

/-! ## The counter and the bit -/

/-- What keeps the callee-saved registers but the counter. -/
structure Kc (s s' : State) : Prop where
  gpr : ∀ r ∈ preserved, r ≠ .s1 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Kc.refl (s : State) : Kc s s := ⟨fun _ _ _ => rfl, rfl, rfl, rfl⟩

theorem Kc.trans {s₁ s₂ s₃ : State} (h₁ : Kc s₁ s₂) (h₂ : Kc s₂ s₃) : Kc s₁ s₃ :=
  ⟨fun r hr h => (h₂.gpr r hr h).trans (h₁.gpr r hr h), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem Kp.kc {s s' : State} (h : Kp s s') : Kc s s' := ⟨fun r hr _ => h.gpr r hr, h.rd, h.wr, h.sp⟩

theorem Kc.of_rest {ws : List Reg} {s s' : State} (h : Rest ws s s') (hws : ∀ r ∈ ws, r ∉ preserved ∨ r = .s1 := by decide) :
    Kc s s' :=
  ⟨fun r hr hr1 => h.gpr r fun h' => (hws r h').elim (fun h => h hr) hr1, h.rd, h.wr, h.sp⟩

theorem WsReg.of_kc {s s' : State} {base : Addr} (h : WsReg s base) (k : Kc s s') : WsReg s' base :=
  ⟨(k.gpr _ (by decide) (by decide)).trans h.s0, k.wr ▸ h.wr, h.nowrap, h.al⟩

/-- A loop whose body takes the invariant from `j` to `j - 1`, with `s1 = j`
in the invariant, run from `n ≥ 1` (below `2⁶⁴`). -/
theorem countLoop_ok {body : Prog isa} {Inv : Nat → State → Prop} {Q : State → Prop} {n : Nat}
    (hr : ∀ j s, Inv j s → s.gpr .s1 = BitVec.ofNat 64 j)
    (hstep : ∀ j s, 1 ≤ j → j ≤ n → Inv j s → WP isa body s fun s' => Inv (j - 1) s')
    (hQ : ∀ s, Inv 0 s → Q s) (hn : 1 ≤ n) (hn64 : n < 2 ^ 64) {s : State} (hs : Inv n s) :
    WP isa (.loop body more) s Q := by
  refine WP.loop (M := isa) (fun j s => 1 ≤ j ∧ j ≤ n ∧ Inv j s) (fun j s ⟨h1, h2, hi⟩ => ?_) n s
    ⟨hn, Nat.le_refl _, hs⟩
  refine WP.mono (hstep j s h1 h2 hi) fun s' hi' => ?_
  have he := eval_nonzero_ofNat s' .s1 (k := j - 1) (by omega) (hr _ _ hi')
  by_cases hj : j - 1 = 0
  · exact .inl ⟨by rw [he]; simp [hj], hQ s' (by rw [hj] at hi'; exact hi')⟩
  · exact .inr ⟨by rw [he]; simp [hj], j - 1, by omega, by omega, by omega, hi'⟩

theorem ofNat_pred64 {j : Nat} (hj : 1 ≤ j) : BitVec.ofNat 64 j + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (j - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (BitVec.ofInt 64 (-1)).toNat = 2 ^ 64 - 1 from rfl]
  omega

/-- `s1 -= 1`. -/
theorem wp_decCounter {is : List Instr} {s : State} {Q : State → Prop} {j : Nat} (hj : 1 ≤ j)
    (hb : s.gpr .s1 = BitVec.ofNat 64 j)
    (k : ∀ s', Upd s s' .s1 (BitVec.ofNat 64 (j - 1)) → WP isa (.block is) s' Q) :
    WP isa (.block (decCounter :: is)) s Q := by
  refine WP.cons (exec_addi (by decide)) ?_
  rw [hb, ofNat_pred64 hj]; exact k _ (Upd.write _ _ _)

/-- `srl d, n, m`. -/
theorem wp_srlReg {d n m : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (s.gpr n >>> ((s.gpr m).toNat % 64)) → WP isa (.block is) s' Q) :
    WP isa (.block (.shiftReg .srl .d d n m :: is)) s Q :=
  WP.cons rfl (k _ (Upd.write _ _ _))

theorem and1 (w : BitVec 64) (i : Nat) :
    (w >>> i) &&& 1 = if w.toNat.testBit i then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod,
    Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (w.toNat / 2 ^ i) with h | h <;> simp [h]

theorem neg_bit (b : Bool) : (0 : BitVec 64) - (if b then 1 else 0) = if b then BitVec.allOnes 64 else 0 := by
  cases b <;> decide

/-- Bit `j` of a number of words is bit `j mod 64` of its word `j / 64`. -/
theorem testBit_wordsVal (m : Mem) (base : Addr) : ∀ (n src j : Nat), j < 64 * n →
    (word m base (src + 8 * (j / 64))).toNat.testBit (j % 64) = (wordsVal m base src n).testBit j
  | 0, _, _, h => by omega
  | n + 1, src, j, h => by
    rw [wordsVal, Nat.add_comm (word m base src).toNat, Nat.testBit_two_pow_mul_add _ (word m base src).isLt]
    by_cases hj : j < 64
    · rw [ite_eq_left_iff.mpr (fun h => absurd hj h), Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj, Nat.mul_zero,
        Nat.add_zero]
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hj), ← testBit_wordsVal m base n (src + 8) (j - 64) (by omega),
        show src + 8 * (j / 64) = src + 8 + 8 * ((j - 64) / 64) by omega, show j % 64 = (j - 64) % 64 by omega]

/-- `a7 = -bit` of bit `j = s1` of the `n`-word number at `src`. -/
theorem bitMask_ok {s : State} {base : Addr} (hw : WsReg s base) {src n j : Nat} (hj : j < 64 * n)
    (hj64 : j < 2 ^ 58) (h1 : s.gpr .s1 = BitVec.ofNat 64 j) (hsrc : src + 8 * n ≤ 2048) (hs8 : src % 8 = 0) :
    WP isa (.block (bitMask src)) s fun s' =>
      s'.gpr .a7 = maskOf ((wordsVal s.mem base src n).testBit j) ∧ Rest [.t0, .t1, .t2, .a7] s s' ∧
        s'.mem = s.mem := by
  have hn := hw.nowrap
  have hq : 8 * (j / 64) + 8 ≤ 8 * n := by
    have : j / 64 < n := Nat.div_lt_of_lt_mul (by omega)
    omega
  rw [bitMask]
  refine wp_srl (by decide) fun s₁ u₁ => wp_sll (by decide) fun s₂ u₂ => wp_add fun s₃ u₃ => ?_
  have e3 : s₃.gpr .t0 + BitVec.ofNat 64 src = off base (src + 8 * (j / 64)) := by
    rw [u₃.gpr, u₂.gpr, u₂.other .s0 (by decide), u₁.gpr, u₁.other .s0 (by decide), h1, hw.s0]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, off]
    rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 64)]
    omega
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have r₃ : Rest [.t0] s s₃ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (u₃.rest (by decide)))
  refine wp_ld (by omega) e3 (by simp only [off]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := hw.al; omega)
    ⟨_, List.mem_append_right _ (r₃.wr ▸ hw.wr), Offset.contains_base base (by omega) (by omega)⟩ fun s₄ u₄ => ?_
  refine wp_srlReg fun s₅ u₅ => wp_andi (imm := 1) (by decide) fun s₆ u₆ => ?_
  refine wp_li (imm := 0) (by decide) fun s₇ u₇ => wp_sub fun s₈ u₈ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [u₈.gpr, u₇.gpr, u₇.other .t1 (by decide), u₆.gpr, u₅.gpr, u₄.gpr,
      u₄.other .s1 (by decide), r₃.gpr .s1 (by decide), h1, m₃, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), show BitVec.ofInt 64 1 = 1 from rfl, and1,
      testBit_wordsVal s.mem base n src j hj, show BitVec.ofNat 64 0 = 0 from rfl, neg_bit]
  · exact (r₃.mono (by decide)).trans ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans
      ((u₆.rest (by decide)).trans ((u₇.rest (by decide)).trans (u₈.rest (by decide))))))
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃]

/-! ## The ladder -/

/-- What a slot holding `x` stands for, modulo `C.p`. -/
abbrev tmv (C : Curve) (n : Nat) (base : Addr) (s : State) (x : Nat) : Fe C :=
  toM C.p (2 ^ (64 * n)) (wordsVal s.mem base x n)

/-- That an iteration keeps the invariant `Q`: from `(X : Y : Z)` that
`Q (j + 1)` accepts, `Q j` accepts `T = D + G` if bit `j` of `k` is set, else
`D = (X : Y : Z) + (X : Y : Z)`, by the complete addition with the curve's
`a`, `3b` and `G` as the slots `L.S.a`, `L.S.b3` and `L.G` hold them. -/
def Step (L : LadderCfg) (C : Curve) (base : Addr) (s : State) (k : Nat)
    (Q : Nat → Fe C → Fe C → Fe C → Prop) : Prop :=
  ∀ j < L.nbits, ∀ X Y Z X2 Y2 Z2 X3 Y3 Z3 : Fe C, Q (j + 1) X Y Z →
    rcbAdd (tmv C L.M.n base s L.S.a) (tmv C L.M.n base s L.S.b3) X Y Z X Y Z = (X2, Y2, Z2) →
    rcbAdd (tmv C L.M.n base s L.S.a) (tmv C L.M.n base s L.S.b3) X2 Y2 Z2
      (tmv C L.M.n base s L.G.x) (tmv C L.M.n base s L.G.y) (tmv C L.M.n base s L.G.z) =
      (X3, Y3, Z3) →
    Q j (if k.testBit j then X3 else X2) (if k.testBit j then Y3 else Y2)
      (if k.testBit j then Z3 else Z2)

/-- The invariant of the group law: `R` represents `[k >>> j]P`, for the
point `P` that `G` represents, when the slots of `a` and `3b` hold the
curve's. -/
theorem step_rep {L : LadderCfg} {C : Curve} {base : Addr} {s : State} {k : Nat} {P : Point C}
    (hC : Law C) (hP : Spec.Weierstrass.onCurve C P = true)
    (ha : tmv C L.M.n base s L.S.a = Fin.ofNat C.p C.a)
    (hb : tmv C L.M.n base s L.S.b3 = Fin.ofNat C.p (3 * C.b))
    (hG : Rep C (tmv C L.M.n base s L.G.x) (tmv C L.M.n base s L.G.y) (tmv C L.M.n base s L.G.z) P) :
    Step L C base s k fun j X Y Z => Rep C X Y Z (Spec.Weierstrass.mul (k >>> j) P) := by
  intro j _ X Y Z X2 Y2 Z2 X3 Y3 Z3 hQ h2 h3
  rw [ha, hb] at h2 h3
  exact ladder_step hC hP hG hQ h2 h3

/-- What the ladder writes: `ladW` and the functions' own working space. -/
def ladWx (L : LadderCfg) : List (Nat × Nat) := ladW L ++ [(own L.M.n, 64 * L.M.n)]

/-- The ladder's slots: `LadLay` below the functions' own working space, at
multiples of 8 in the first 2048 bytes, and the scalar's slot (`L.bits`) too,
apart from what the ladder writes, with `L.nbits` of its bits, an immediate. -/
structure LadLayR (L : LadderCfg) : Prop where
  lay : LadLay L (own L.M.n) 8192
  al : ∀ x ∈ ladSlots L, x % 8 = 0
  short : ∀ x ∈ ladSlots L, x + 8 * L.M.n ≤ 2048
  kal : L.bits % 8 = 0
  kshort : L.bits + 8 * L.M.n ≤ 2048
  kw : ∀ w ∈ ladWx L, L.bits + 8 * L.M.n ≤ w.1 ∨ w.1 + w.2 ≤ L.bits
  nbits : L.nbits ≤ 64 * L.M.n
  nbits' : L.nbits < 2048
  n0 : 1 ≤ L.M.n

theorem own_add (n : Nat) (h : 8 * n ≤ own n) : own n + 64 * n = 4096 := by
  simp only [own, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes] at h ⊢; omega

/-- A slot the ladder does not write is apart from what it writes. -/
theorem LadLayR.apart_wx {L : LadderCfg} (hL : LadLayR L) {x : Nat} (hx : x ∈ ladSlots L)
    (hxw : x ∉ ladWs L) : ∀ w ∈ ladWx L, x + 8 * L.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro w hw
  simp only [ladWx, List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | rfl
  · exact hL.lay.apart_w hx hxw w hw
  · exact .inl (hL.lay.lay.le x hx)

theorem LadLayR.short' {L : LadderCfg} (hL : LadLayR L) : Short (· ∈ ladSlots L) :=
  fun x hx => by have := hL.short x hx; have := hL.n0; omega

/-- The loop's invariant at `s1 = j`: `Q j` accepts what `R` holds. -/
structure LadInv (L : LadderCfg) (C : Curve) (base : Addr) (Q : Nat → Fe C → Fe C → Fe C → Prop)
    (s₀ s : State) (j : Nat) : Prop where
  ws : WsReg s base
  ctr : s.gpr .s1 = BitVec.ofNat 64 j
  keep : Kc s₀ s
  unch : Unch base (ladWx L) s₀.mem s.mem
  lt : ∀ x ∈ [L.R.x, L.R.y, L.R.z], wordsVal s.mem base x L.M.n < C.p
  q : Q j (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y) (tmv C L.M.n base s L.R.z)

/-- After both additions: `D` and `T` hold `R + R` and `D + G`. -/
structure AddsPost (L : LadderCfg) (C : Curve) (base : Addr) (E : Nat → Fe C) (s s' : State) : Prop where
  ws : WsReg s' base
  keep : Kp s s'
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
    (h : KeepR L.M.n base W s s') (hW : ∀ w ∈ W, w ∈ ladWs L) :
    Unch base (ladWx L) s.mem s'.mem :=
  fun x hx => h.mem x fun r hr => hx r (by
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
    simp only [ladWx, ladW, List.mem_append, List.mem_map, List.mem_singleton]
    rcases hr with ⟨w, hw, rfl⟩ | rfl
    · exact .inl (.inl ⟨w, hW w hw, rfl⟩)
    · exact .inr rfl)

/-- The two additions, from a state holding `E` in the slots `ladR`. -/
theorem ladAdds_ok {L : LadderCfg} {C : Curve} {base : Addr} (hL : LadLayR L)
    {F : Field} (hF : FieldOk F) (hkS : F.S.k = L.M.n) (hmS : F.S.m = C.p)
    (hp : UnitMod C.p (2 ^ (64 * L.M.n))) {E : Nat → Fe C} {s : State}
    (hI : Inv L.M.n base C.p (· ∈ ladSlots L) (ladR L) E s) {rest : Prog isa}
    {Q : State → Prop} (h : ∀ s', AddsPost L C base E s s' → WP isa rest s' Q) :
    WP isa (.seq (fprog F (rcb L.S L.R L.R L.D)) (.seq (fprog F (rcb L.S L.D L.G L.T)) rest))
      s Q := by
  obtain ⟨⟨c, w, m', k', d⟩, fm, fa, fs⟩ := F
  dsimp only at hkS hmS hF ⊢
  subst hkS hmS
  have hL' := hL.lay
  have hS2 := hL.short'
  refine WP.seq (WP.mono (rcb_ok (F := ⟨⟨c, w, C.p, L.M.n, d⟩, fm, fa, fs⟩) hF rfl hL'.lay hS2 hp hL'.a1
    (ladR_S₁ L) hI (ladR_V₁ L)) fun s₂ ⟨k₂, I₂, t₂, n₂⟩ => ?_)
  refine WP.seq (WP.mono (rcb_ok (F := ⟨⟨c, w, C.p, L.M.n, d⟩, fm, fa, fs⟩) hF rfl hL'.lay hS2 hp hL'.a2
    (ladR_S₂ L) I₂ (ladR_V₂ L)) fun s₃ ⟨k₃, I₃, t₃, n₃⟩ => h s₃ ?_)
  have hro : ∀ x ∈ ladRo L, x ∉ rcbW L.S L.D := fun x hx h =>
    hL'.ro x hx (by simp only [ladWs, List.mem_append]; exact Or.inl (Or.inr h))
  have hDT : ∀ x ∈ [L.D.x, L.D.y, L.D.z], x ∉ rcbW L.S L.T := fun x hx =>
    hL'.a2.apart x (by revert x; sub_list)
  have hD : ∀ x ∈ [L.D.x, L.D.y, L.D.z], x ∈ rcbW L.S L.T ++ (rcbW L.S L.D ++ ladR L) := by
    sub_list
  have hT : ∀ x ∈ [L.T.x, L.T.y, L.T.z], x ∈ rcbW L.S L.T ++ (rcbW L.S L.D ++ ladR L) := by
    sub_list
  refine ⟨I₃.ws, k₂.kp.trans k₃.kp, ((keep_unch k₂ fun w hw => ?_).trans (keep_unch k₃ fun w hw => ?_)).mono
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
theorem ladSel_ok {L : LadderCfg} {base : Addr} (hL : LadLayR L) {s : State} (hw : WsReg s base)
    {t : Nat} (ht : t < L.nbits) (h1 : s.gpr .s1 = BitVec.ofNat 64 t) :
    WP isa (.block (bitMask L.bits ++ selPt L.M.n L.R L.D L.T)) s
      fun s' => Rest [.t0, .t1, .t2, .a7] s s' ∧
        Unch base [(L.R.x, 8 * L.M.n), (L.R.y, 8 * L.M.n), (L.R.z, 8 * L.M.n)] s.mem s'.mem ∧
        let c := (wordsVal s.mem base L.bits L.M.n).testBit t
        wordsVal s'.mem base L.R.x L.M.n =
          (if c then wordsVal s.mem base L.T.x L.M.n else wordsVal s.mem base L.D.x L.M.n) ∧
        wordsVal s'.mem base L.R.y L.M.n =
          (if c then wordsVal s.mem base L.T.y L.M.n else wordsVal s.mem base L.D.y L.M.n) ∧
        wordsVal s'.mem base L.R.z L.M.n =
          (if c then wordsVal s.mem base L.T.z L.M.n else wordsVal s.mem base L.D.z L.M.n) := by
  have hnb := hL.nbits
  have hnb' := hL.nbits'
  refine WP.block_append (WP.mono (bitMask_ok hw (src := L.bits) (n := L.M.n) (by omega) (by omega) h1
    hL.kshort hL.kal) fun s₄ ⟨c₄, k₄, hm₄⟩ => ?_)
  have hap : ∀ x ∈ [L.R.x, L.R.y, L.R.z, L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z],
      ∀ y ∈ [L.R.x, L.R.y, L.R.z, L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z], x ≠ y →
      x + 8 * L.M.n ≤ y ∨ y + 8 * L.M.n ≤ x :=
    fun x hx y hy hxy => hL.lay.lay.apart x y (ladPts_slots L x hx) (ladPts_slots L y hy) hxy
  obtain ⟨rxy, rxz, ryz⟩ := hL.lay.rne
  refine WP.mono (selPt_ok (hw.of_rest k₄) _ c₄ (n := L.M.n) (o := L.R) (a := L.D) (b := L.T)
    (fun d hd => hL.al d (ladPts_slots L d hd))
    (fun d hd => hL.short d (ladPts_slots L d hd))
    ⟨hap L.R.x (by simp) L.R.y (by simp) rxy, hap L.R.x (by simp) L.R.z (by simp) rxz,
      hap L.R.y (by simp) L.R.z (by simp) ryz⟩
    (fun d hd e he => hap d (List.mem_append_left [L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z] hd) e
      (List.mem_append_right [L.R.x, L.R.y, L.R.z] he) fun h => hL.lay.rdt d hd (h ▸ he)))
    fun s₅ ⟨ex₅, ey₅, ez₅, k₅, O₅⟩ => ?_
  refine ⟨k₄.trans (k₅.mono (by decide)), by rw [← hm₄]; exact O₅, by rw [ex₅, hm₄], by rw [ey₅, hm₄],
    by rw [ez₅, hm₄]⟩

section body
variable {L : LadderCfg} {C : Curve} {base : Addr}

/-- The scalar the ladder reads at the start of the run from `s₀`. -/
abbrev kOf (L : LadderCfg) (base : Addr) (s : State) : Nat := wordsVal s.mem base L.bits L.M.n

/-- An iteration. -/
theorem ladderBody_ok {Q : Nat → Fe C → Fe C → Fe C → Prop} {F : Field} (hF : FieldOk F)
    (hkS : F.S.k = L.M.n) (hmS : F.S.m = C.p) (hp : UnitMod C.p (2 ^ (64 * L.M.n)))
    (hL : LadLayR L) {s₀ : State} (hlt₀ : ∀ x ∈ ladRo L, wordsVal s₀.mem base x L.M.n < C.p)
    (hstep : Step L C base s₀ (kOf L base s₀) Q)
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ L.nbits) (hI : LadInv L C base Q s₀ s j) :
    WP isa (ladderBody L F) s fun s' => LadInv L C base Q s₀ s' (j - 1) := by
  have hn := hI.ws.nowrap
  have hnb := hL.nbits
  -- The slots read only hold what they held at the start.
  have hro : ∀ x ∈ ladRo L, wordsVal s.mem base x L.M.n = wordsVal s₀.mem base x L.M.n :=
    fun x hx => hI.unch.wordsVal
      (hL.apart_wx (ladR_slots L x (mem_ladRo_ladR hx)) (hL.lay.ro x hx))
      (by have := hL.lay.lay.le x (ladR_slots L x (mem_ladRo_ladR hx)); simp only [own,
        Impl.Weierstrass.Mont.ownAt] at this; omega)
  have hE : ∀ x ∈ ladRo L, tmv C L.M.n base s x = tmv C L.M.n base s₀ x := fun x hx => by
    rw [tmv, hro x hx]
  -- `s1 -= 1`.
  rw [ladderBody]
  refine WP.seq (wp_decCounter hj hI.ctr fun s₁ u₁ => WP.block_nil ?_)
  have K₁ : Kc s s₁ := Kc.of_rest (u₁.rest (ws := [.s1]) (by decide))
  have m₁ : s₁.mem = s.mem := u₁.mem
  have c₁ : s₁.gpr .s1 = BitVec.ofNat 64 (j - 1) := u₁.gpr
  have I₁ : Inv L.M.n base C.p (· ∈ ladSlots L) (ladR L) (tmv C L.M.n base s) s₁ := by
    refine ⟨hI.ws.of_kc K₁, ladR_slots L, fun x hx => ?_, fun x _ => by rw [tmv, m₁]⟩
    rw [m₁]
    simp only [ladR, List.mem_append] at hx
    rcases hx with hx | hx
    · rw [hro x hx]; exact hlt₀ x hx
    · exact hI.lt x hx
  -- The additions.
  refine ladAdds_ok hL hF hkS hmS hp I₁ fun s₃ A => ?_
  obtain ⟨X2, Y2, Z2, X3, Y3, Z3, h2, h3, dx, dy, dz, tx, ty, tz⟩ := A.vals
  have hU₃ : Unch base (ladWx L) s₀.mem s₃.mem :=
    (hI.unch.trans (by rw [← m₁]; exact A.unch)).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw <;> exact hw
  have hk₃ : wordsVal s₃.mem base L.bits L.M.n = kOf L base s₀ :=
    hU₃.wordsVal hL.kw (by have := hL.kshort; omega)
  have c₃ : s₃.gpr .s1 = BitVec.ofNat 64 (j - 1) := by rw [A.keep.gpr _ (by decide), c₁]
  have hstep := hstep (j - 1) (by omega) (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y)
    (tmv C L.M.n base s L.R.z) X2 Y2 Z2 X3 Y3 Z3 (by rw [Nat.sub_add_cancel hj]; exact hI.q)
    (by rw [← hE L.S.a (by simp [ladRo]), ← hE L.S.b3 (by simp [ladRo])]; exact h2)
    (by rw [← hE L.S.a (by simp [ladRo]), ← hE L.S.b3 (by simp [ladRo]), ← hE L.G.x (by simp [ladRo]),
        ← hE L.G.y (by simp [ladRo]), ← hE L.G.z (by simp [ladRo])]; exact h3)
  have K₃ : Kc s₀ s₃ := (hI.keep.trans K₁).trans A.keep.kc
  refine WP.mono (ladSel_ok hL A.ws (by omega) c₃) fun s' ⟨k', U', ex, ey, ez⟩ => ?_
  rw [hk₃] at ex ey ez
  refine ⟨A.ws.of_rest k', by rw [k'.gpr _ (by decide), c₃], K₃.trans (Kc.of_rest k'), ?_, ?_, ?_⟩
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
  · have hx : tmv C L.M.n base s' L.R.x = if (kOf L base s₀).testBit (j - 1) then X3 else X2 := by
      show toM _ _ _ = _
      rw [ex]; split
      · exact tx
      · exact dx
    have hy : tmv C L.M.n base s' L.R.y = if (kOf L base s₀).testBit (j - 1) then Y3 else Y2 := by
      show toM _ _ _ = _
      rw [ey]; split
      · exact ty
      · exact dy
    have hz : tmv C L.M.n base s' L.R.z = if (kOf L base s₀).testBit (j - 1) then Z3 else Z2 := by
      show toM _ _ _ = _
      rw [ez]; split
      · exact tz
      · exact dz
    rw [hx, hy, hz]
    exact hstep

/-- `Q 0` accepts what `R` holds at the end, if `Q L.nbits` accepts what it
holds at the start and an iteration keeps `Q` (`Step`), for the scalar `k`
at `L.bits`; only `s1`, caller-saved registers and `ladWx` change. -/
theorem ladder_ok {Q : Nat → Fe C → Fe C → Fe C → Prop} {F : Field} (hF : FieldOk F)
    (hkS : F.S.k = L.M.n) (hmS : F.S.m = C.p) (hp : UnitMod C.p (2 ^ (64 * L.M.n)))
    (hL : LadLayR L) {s : State} (hs : WsReg s base)
    (hlt : ∀ x ∈ ladR L, wordsVal s.mem base x L.M.n < C.p) (hstep : Step L C base s (kOf L base s) Q)
    (hR : Q L.nbits (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y) (tmv C L.M.n base s L.R.z)) :
    WP isa (ladder L F) s fun s' => Kc s s' ∧ Unch base (ladWx L) s.mem s'.mem ∧
      (∀ x ∈ [L.R.x, L.R.y, L.R.z], wordsVal s'.mem base x L.M.n < C.p) ∧
      Q 0 (tmv C L.M.n base s' L.R.x) (tmv C L.M.n base s' L.R.y) (tmv C L.M.n base s' L.R.z) := by
  have hnb := hL.lay.nbits
  have hnb' := hL.nbits'
  rw [ladder]
  refine WP.seq (wp_li hnb' fun s₁ u₁ => WP.block_nil ?_)
  have K₁ : Kc s s₁ := Kc.of_rest (u₁.rest (ws := [.s1]) (by decide))
  refine countLoop_ok (Inv := fun j s' => LadInv L C base Q s s' j) (n := L.nbits)
    (fun j s' hi => hi.ctr)
    (fun j s' h1 h2 hi => ladderBody_ok hF hkS hmS hp hL (fun x hx => hlt x (mem_ladRo_ladR hx))
      hstep h1 h2 hi)
    (fun s' hi => ⟨hi.keep, hi.unch, hi.lt, hi.q⟩) hnb.1 (by omega)
    ⟨hs.of_kc K₁, u₁.gpr, K₁, by rw [u₁.mem]; exact Unch.refl _ _ _,
      fun x hx => by rw [u₁.mem]; exact hlt x (List.mem_append_right _ hx), by
        simp only [tmv]; rw [u₁.mem]; exact hR⟩

end body

/-! ## Powers -/

/-- What a power writes, for numbers of `k` words: the accumulator, the
temporary and the functions' own working space. -/
def powWx (P : PowCfg) (k : Nat) : List (Nat × Nat) :=
  [(P.acc, 8 * k), (P.tmp, 8 * k), (own k, 64 * k)]

/-- Where a power's slots are, for numbers of `k` words: below the
functions' own working space and in the first 2048 bytes, at multiples of 8,
and what it reads apart from what it writes. -/
structure PowLayR (P : PowCfg) (k : Nat) : Prop where
  acc : P.acc + 8 * k ≤ own k
  tmp : P.tmp + 8 * k ≤ own k
  base : P.base + 8 * k ≤ own k
  one : P.one + 8 * k ≤ own k
  short : P.acc + 8 * k ≤ 2048 ∧ P.tmp + 8 * k ≤ 2048 ∧ P.base + 8 * k ≤ 2048 ∧ P.one + 8 * k ≤ 2048 ∧
    P.bits + 8 * k ≤ 2048
  nbits : 1 ≤ P.nbits ∧ P.nbits ≤ 64 * k ∧ P.nbits < 2048
  k1 : 1 ≤ k
  acc_tmp : P.acc + 8 * k ≤ P.tmp ∨ P.tmp + 8 * k ≤ P.acc
  acc_one : P.acc + 8 * k ≤ P.one ∨ P.one + 8 * k ≤ P.acc
  base_acc : P.base + 8 * k ≤ P.acc ∨ P.acc + 8 * k ≤ P.base
  base_tmp : P.base + 8 * k ≤ P.tmp ∨ P.tmp + 8 * k ≤ P.base
  bits_w : ∀ w ∈ powWx P k, P.bits + 8 * k ≤ w.1 ∨ w.1 + w.2 ≤ P.bits
  acc8 : P.acc % 8 = 0
  tmp8 : P.tmp % 8 = 0
  one8 : P.one % 8 = 0
  bits8 : P.bits % 8 = 0

/-- The loop's invariant at `s1 = j`: the accumulator reads as
`B^(e >>> j)`, for `B` what the base reads as at the start. -/
structure PowInv (P : PowCfg) (k : Nat) (base : Addr) (m e : Nat) [NeZero m] (s₀ s : State)
    (j : Nat) : Prop where
  ws : WsReg s base
  ctr : s.gpr .s1 = BitVec.ofNat 64 j
  keep : Kc s₀ s
  unch : Unch base (powWx P k) s₀.mem s.mem
  lt : wordsVal s.mem base P.acc k < m
  val : toM m (2 ^ (64 * k)) (wordsVal s.mem base P.acc k) =
    toM m (2 ^ (64 * k)) (wordsVal s₀.mem base P.base k) ^ (e >>> j)

/-- An iteration. -/
theorem powBody_ok {P : PowCfg} {F : Field} [NeZero F.S.m] (hF : FieldOk F)
    (hk : P.M.n = F.S.k) (hL : PowLayR P F.S.k) (hm : UnitMod F.S.m (2 ^ (64 * F.S.k))) {base : Addr}
    {s₀ : State} {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ P.nbits)
    (hI : PowInv P F.S.k base F.S.m (wordsVal s₀.mem base P.bits F.S.k) s₀ s j) :
    WP isa (powBody P F) s fun s' => PowInv P F.S.k base F.S.m (wordsVal s₀.mem base P.bits F.S.k) s₀ s' (j - 1) := by
  have hn := hI.ws.nowrap
  have := hL.acc; have := hL.tmp; have := hL.base
  have hsh := hL.short
  have hk1 := hL.k1
  have hnb := hL.nbits
  have hat := hL.acc_tmp
  have hba := hL.base_acc
  have hbt := hL.base_tmp
  have ho : own F.S.k + 64 * F.S.k = 4096 := own_add F.S.k (by omega)
  have hBs : wordsVal s.mem base P.base F.S.k = wordsVal s₀.mem base P.base F.S.k :=
    hI.unch.wordsVal (fun w hw => by
      simp only [powWx, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact hba
      · exact hbt
      · exact .inl hL.base) (by omega)
  -- `s1 -= 1` and `acc = acc²`.
  rw [powBody]
  refine WP.seq (wp_decCounter hj hI.ctr fun s₁ u₁ => WP.block_nil ?_)
  have K₁ : Kc s s₁ := Kc.of_rest (u₁.rest (ws := [.s1]) (by decide))
  have w₁ := hI.ws.of_kc K₁
  have m₁ : s₁.mem = s.mem := u₁.mem
  have c₁ : s₁.gpr .s1 = BitVec.ofNat 64 (j - 1) := u₁.gpr
  refine WP.seq (WP.mono (mulCall_ok hF w₁ hL.acc hL.acc hL.acc (by omega) (by omega) (by omega)
    (by rw [m₁]; exact hI.lt)) fun s₂ ⟨K₂, lt₂, e₂⟩ => ?_)
  have v₂ : toM F.S.m (2 ^ (64 * F.S.k)) (wordsVal s₂.mem base P.acc F.S.k) =
      toM F.S.m (2 ^ (64 * F.S.k)) (wordsVal s.mem base P.acc F.S.k) ^ 2 := by
    rw [toM_mul hm e₂, m₁, Lean.Grind.Semiring.pow_two]
  have U₂ : Unch base [(P.acc, 8 * F.S.k), (own F.S.k, 64 * F.S.k)] s.mem s₂.mem := by rw [← m₁]; exact K₂.mem
  have hB₂ : wordsVal s₂.mem base P.base F.S.k = wordsVal s₀.mem base P.base F.S.k := by
    rw [U₂.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hba
      · exact .inl hL.base) (by omega), hBs]
  -- `tmp = base · acc`.
  have w₂ := w₁.of_kp K₂.kp
  refine WP.seq (WP.mono (mulCall_ok hF w₂ hL.tmp hL.base hL.acc (by omega) (by omega) (by omega) lt₂)
    fun s₃ ⟨K₃, lt₃, e₃⟩ => ?_)
  have U₃ : Unch base [(P.tmp, 8 * F.S.k), (own F.S.k, 64 * F.S.k)] s₂.mem s₃.mem := K₃.mem
  have hA₃ : wordsVal s₃.mem base P.acc F.S.k = wordsVal s₂.mem base P.acc F.S.k :=
    U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hat
      · exact .inl hL.acc) (by omega)
  have v₃ : toM F.S.m (2 ^ (64 * F.S.k)) (wordsVal s₃.mem base P.tmp F.S.k) =
      toM F.S.m (2 ^ (64 * F.S.k)) (wordsVal s₂.mem base P.acc F.S.k) *
        toM F.S.m (2 ^ (64 * F.S.k)) (wordsVal s₀.mem base P.base F.S.k) := by
    rw [toM_mul hm e₃, hB₂, Lean.Grind.CommSemiring.mul_comm]
  -- The mask of bit `j - 1`, and the selection.
  have hU₃ : Unch base (powWx P F.S.k) s₀.mem s₃.mem := by
    refine ((hI.unch.trans U₂).trans U₃).mono fun w hw => ?_
    simp only [powWx, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with ((h | h | h) | h | h) | h | h <;> simp [h]
  have hE₃ : wordsVal s₃.mem base P.bits F.S.k = wordsVal s₀.mem base P.bits F.S.k :=
    hU₃.wordsVal hL.bits_w (by omega)
  have w₃ := w₂.of_kp K₃.kp
  have c₃ : s₃.gpr .s1 = BitVec.ofNat 64 (j - 1) := by rw [K₃.kp.gpr _ (by decide), K₂.kp.gpr _ (by decide), c₁]
  refine WP.block_append (WP.mono (bitMask_ok w₃ (src := P.bits) (n := F.S.k) (by omega) (by omega) c₃
    (by omega) hL.bits8) fun s₄ ⟨g₄, k₄, m₄⟩ => ?_)
  rw [hE₃] at g₄
  rw [hk]
  refine WP.mono (sel_ok ((wordsVal s₀.mem base P.bits F.S.k).testBit (j - 1)) F.S.k (w₃.of_rest k₄) g₄
    (o := P.acc) (a := P.acc) (b := P.tmp) hL.acc8 hL.acc8 hL.tmp8 (by omega) (by omega) (by omega)
    (Or.inl (Nat.le_refl _)) (by omega)) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have k₅' : Kc s₃ s₅ := (Kc.of_rest k₄).trans (Kc.of_rest k₅)
  refine ⟨w₃.of_kc k₅', by rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), c₃],
    ((hI.keep.trans K₁).trans K₂.kp.kc).trans (K₃.kp.kc.trans k₅'), fun x hx => ?_, ?_, ?_⟩
  · rw [O₅ x (hx _ (List.mem_cons_self ..)), m₄]
    exact hU₃ x hx
  · rw [e₅, m₄]
    split
    · exact lt₃
    · rw [hA₃]; exact lt₂
  · rw [e₅, m₄, pow_shiftRight _ _ (j - 1), Nat.sub_add_cancel hj, ← hI.val]
    split
    · rw [v₃, v₂]
    · rw [hA₃, v₂, Lean.Grind.Semiring.mul_one]

/-- `[acc] = [base]^e` in Montgomery form, for the exponent `e`, the number at
`P.bits`, below `2^nbits`; only `s1`, caller-saved registers and `powWx`
change. -/
theorem pow_ok {P : PowCfg} {F : Field} [NeZero F.S.m] (hF : FieldOk F)
    (hk : P.M.n = F.S.k) (hL : PowLayR P F.S.k) (hm : UnitMod F.S.m (2 ^ (64 * F.S.k))) {base : Addr}
    {s : State} (hs : WsReg s base) (hm0 : 0 < F.S.m)
    (hO : wordsVal s.mem base P.one F.S.k = 2 ^ (64 * F.S.k) % F.S.m)
    (he : wordsVal s.mem base P.bits F.S.k < 2 ^ P.nbits) :
    WP isa (pow P F) s fun s' => Kc s s' ∧ Unch base (powWx P F.S.k) s.mem s'.mem ∧
      wordsVal s'.mem base P.acc F.S.k < F.S.m ∧
      toM F.S.m (2 ^ (64 * F.S.k)) (wordsVal s'.mem base P.acc F.S.k) =
        toM F.S.m (2 ^ (64 * F.S.k)) (wordsVal s.mem base P.base F.S.k) ^ wordsVal s.mem base P.bits F.S.k := by
  have hn := hs.nowrap
  have hnb := hL.nbits
  have hsh := hL.short
  have := hL.acc; have := hL.one
  have hao := hL.acc_one
  have hba := hL.base_acc
  rw [pow, hk]
  refine WP.seq (WP.block_append (WP.mono (copy_ok F.S.k hs (o := P.acc) (a := P.one) hL.acc8 hL.one8
    (by omega) (by omega) (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ =>
      wp_li hnb.2.2 fun s₂ u₂ => WP.block_nil ?_))
  have K : Kc s s₂ := (Kc.of_rest k₁).trans (Kc.of_rest (u₂.rest (ws := [.s1]) (by decide)))
  have m₂ : s₂.mem = s₁.mem := u₂.mem
  have hE : wordsVal s₂.mem base P.bits F.S.k = wordsVal s.mem base P.bits F.S.k := by
    rw [m₂]; exact O₁.wordsVal (by have := hL.bits_w _ (List.mem_cons_self ..); exact this) (by omega)
  refine countLoop_ok (Inv := fun j s' => PowInv P F.S.k base F.S.m (wordsVal s₂.mem base P.bits F.S.k) s₂ s' j)
    (n := P.nbits)
    (fun j s' hi => hi.ctr) (fun j s' h1 h2 hi => powBody_ok hF hk hL hm h1 h2 hi)
    (fun s' hi => ?_) hnb.1 (by omega) ?_
  · have hB₂ : wordsVal s₂.mem base P.base F.S.k = wordsVal s.mem base P.base F.S.k := by
      rw [m₂, O₁.wordsVal (by omega) (by omega)]
    refine ⟨K.trans hi.keep, ?_, hi.lt, by rw [hi.val, Nat.shiftRight_zero, hB₂, hE]⟩
    exact (O₁.unch.trans (by rw [← m₂]; exact hi.unch)).mono fun w hw => by
      simp only [List.mem_append, List.mem_singleton] at hw
      rcases hw with rfl | hw
      · simp [powWx]
      · exact hw
  · have hv : wordsVal s₂.mem base P.acc F.S.k = wordsVal s.mem base P.one F.S.k := by rw [m₂, e₁]
    refine ⟨hs.of_kc K, u₂.gpr, Kc.refl _, Unch.refl _ _ _, ?_, ?_⟩
    · rw [hv, hO]; exact Nat.mod_lt _ hm0
    · rw [hv, hO, toM_one hm, hE, shiftRight_eq_zero he, Lean.Grind.Semiring.pow_zero]

end VG.Proof.Weierstrass.RISCV64
