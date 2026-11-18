module

public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Weierstrass.Arm.Window
import VerifiedGarbage.Proof.Weierstrass.JacAdd
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_<curve>_mul_public` on 32-bit ARM: constant time in its secrets

`vg_<curve>_mul_public` has no secret: its branches and the addresses it
reads depend on the number `k` and the point `P` it multiplies, which
verification's signature and public key determine. So two runs on the same
`k` and `P`, from the same working space, leak the same (`pubCall_ct`),
which the taint analysis cannot see: it does not follow `k` and `P` through
the memory.

The proof relates two runs (`RelCT`). Both satisfy the invariants of the
correctness proof (`Public.lean`) for the same `k` and `P` (`Det`), which
determine every branch: a digit of `k`, a position, or whether the Jacobian
addition adds two points (`Apart`, of the points alone:
`invJ_apart_iff`). Between the branches the code is straight-line pieces
(`pubPieces`), each constant time by the taint analysis from the registers
the invariants determine (`PubLeaves`): a curve's proof checks its pieces
(`PubLeaves.of_checks`, on the pieces in sequence, one literal).
-/

-- separate module: only the constant-time proofs of the curves' verifications import it, and the
-- correctness proofs need not check it again

@[expose] public section

namespace VG.Proof.Ecdsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.X25519.Arm (Rest wp_mov wp_cmp op2_imm op2_reg eval_ne eval_eq)
open VG.Proof.Ed25519

variable {c : Cfg}

/-! ## Two runs that satisfy one invariant -/

/-- Code that leaks the same from two states whose registers `rs` agree. -/
def LeafCT (rs : List Reg) (p : Prog isa) : Prop :=
  RelCT isa (fun x y => ∀ r ∈ rs, x.gpr r = y.gpr r) p fun _ _ => True

/-- By the taint analysis. -/
theorem LeafCT.check {rs : List Reg} {p : Prog isa} {hint : VG.Taint.Hint VG.Arm.Taint.T}
    (h : (VG.Arm.taint.check (VG.Arm.Taint.ofRegs rs) p hint).isSome = true) : LeafCT rs p :=
  RelCT.taint (A := VG.Arm.taint) (VG.Arm.Taint.ofRegs rs) (fun _ _ h => VG.Arm.Taint.agree_ofRegs h) h

/-- By the taint analysis of code with `umaal` (`taintU`). -/
theorem LeafCT.checkU {rs : List Reg} {p : Prog isa} {hint : VG.Taint.Hint VG.Arm.taintU.T}
    (h : (VG.Arm.taintU.check (VG.Arm.Taint.ofRegs rs) p hint).isSome = true) : LeafCT rs p :=
  RelCT.taint (A := VG.Arm.taintU) (VG.Arm.Taint.ofRegs rs) (fun _ _ h => VG.Arm.Taint.agree_ofRegs h) h

/-- Two runs of `p` from states that both satisfy `I` leak the same. -/
def Det (I : State → Prop) (p : Prog isa) : Prop :=
  RelCT isa (fun x y => I x ∧ I y) p fun _ _ => True

theorem Det.mono {I J : State → Prop} {p : Prog isa} (h : Det J p) (hi : ∀ s, I s → J s) : Det I p :=
  RelCT.mono h (fun _ _ h => ⟨hi _ h.1, hi _ h.2⟩) fun _ _ h => h

theorem Det.of_false {I : State → Prop} {p : Prog isa} (h : ∀ s, ¬I s) : Det I p :=
  RelCT.of_false fun _ _ hi => h _ hi.1

/-- A piece the taint analysis proves, from registers `I` determines. -/
theorem Det.leaf {I : State → Prop} {p : Prog isa} {rs : List Reg} (h : LeafCT rs p)
    (hr : ∀ x y, I x → I y → ∀ r ∈ rs, x.gpr r = y.gpr r) : Det I p :=
  RelCT.mono h (fun x y hi => hr x y hi.1 hi.2) fun _ _ h => h

/-- `a`, which takes `I` to `J`, then `b`. -/
theorem Det.seq {I J : State → Prop} {a b : Prog isa} (ha : Det I a) (hw : ∀ s, I s → WP isa a s J)
    (hb : Det J b) : Det I (.seq a b) :=
  RelCT.seq (RelCT.mono (RelCT.wp ha fun x y h => ⟨hw x h.1, hw y h.2⟩) (fun _ _ h => h) fun _ _ h => h.2) hb

/-- `a`, then `b` from any states. -/
theorem Det.seq_any {I : State → Prop} {a b : Prog isa} (ha : Det I a) (hb : Det (fun _ => True) b) :
    Det I (.seq a b) :=
  RelCT.seq (RelCT.mono ha (fun _ _ h => h) fun _ _ _ => ⟨trivial, trivial⟩) hb

/-- A branch on a condition `I` determines. -/
theorem Det.ite {I : State → Prop} {cnd : Cond} {t e : Prog isa}
    (hc : ∀ x y, I x → I y → isa.eval cnd x = isa.eval cnd y)
    (ht : Det (fun s => I s ∧ isa.eval cnd s = some true) t)
    (he : Det (fun s => I s ∧ isa.eval cnd s = some false) e) : Det I (.ite cnd t e) :=
  RelCT.ite (fun x y h => hc x y h.1 h.2)
    (RelCT.mono ht (fun x y h => ⟨⟨h.1.1, h.2⟩, h.1.2, (hc x y h.1.1 h.1.2).symm.trans h.2⟩) fun _ _ h => h)
    (RelCT.mono he (fun x y h => ⟨⟨h.1.1, h.2⟩, h.1.2, (hc x y h.1.1 h.1.2).symm.trans h.2⟩) fun _ _ h => h)

/-- A loop whose invariant `I n` determines whether it goes on (`b n`), to
`I (n - 1)`. -/
theorem Det.loop {body : Prog isa} {cnd : Cond} (I : Nat → State → Prop) (b : Nat → Bool)
    (hbody : ∀ n, Det (I n) body)
    (hw : ∀ n s, I n s → WP isa body s fun s' =>
      isa.eval cnd s' = some (b n) ∧ (b n = true → 0 < n ∧ I (n - 1) s'))
    (n : Nat) : Det (I n) (.loop body cnd) := by
  refine RelCT.loop (M := isa) (fun n x y => I n x ∧ I n y) (fun n => ?_) n
  refine RelCT.mono (RelCT.wp (hbody n) fun x y h => ⟨hw n x h.1, hw n y h.2⟩) (fun _ _ h => h)
    fun x y ⟨_, ⟨ex, nx⟩, ey, ny⟩ => ⟨ex.trans ey.symm, fun _ => trivial, fun ht => ?_⟩
  have hb : b n = true := Option.some.inj (ex.symm.trans ht)
  exact ⟨n - 1, Nat.sub_lt (nx hb).1 Nat.one_pos, (nx hb).2, (ny hb).2⟩

/-- A call, by its function from the states the call instruction leaves. -/
theorem relCT_call {name : String} {fn : Prog isa} {P : State → State → Prop}
    (h : RelCT isa (fun e₁ e₂ => ∃ s₁ s₂, P s₁ s₂ ∧ e₁ = s₁.callEntry ∧ e₂ = s₂.callEntry) fn
      fun _ _ => True) : RelCT isa P (.call name fn) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | call h₁ b₁ r₁ =>
    cases e₂ with
    | call h₂ b₂ r₂ =>
      rw [call_callEntry, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      obtain ⟨rfl, -⟩ := h _ _ _ _ _ _ ⟨_, _, hp, rfl, rfl⟩ b₁ b₂
      exact ⟨rfl, trivial⟩

/-! ## What the invariants determine -/

theorem addr_inj {a b : BitVec 32} (h : State.addr a = State.addr b) : a = b := by
  apply BitVec.eq_of_toNat_eq
  have e := congrArg BitVec.toNat h
  simp only [State.addr, BitVec.toNat_setWidth] at e
  rwa [Nat.mod_eq_of_lt (Nat.lt_trans a.isLt (by decide)),
    Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide))] at e

/-- The working space's register. -/
theorem scr_r12 {w : BitVec 32} {s : State} (h : Scr s (State.addr w) size) : s.gpr .r12 = w := addr_inj h.wb

theorem regs0 {x y : State} : ∀ r ∈ ([] : List Reg), x.gpr r = y.gpr r := fun _ h => nomatch h

theorem regs1 {x y : State} {a : Reg} (ha : x.gpr a = y.gpr a) : ∀ r ∈ [a], x.gpr r = y.gpr r := by
  intro r hr
  rw [List.mem_singleton.mp hr]; exact ha

theorem regs2 {x y : State} {a b : Reg} (ha : x.gpr a = y.gpr a) (hb : x.gpr b = y.gpr b) :
    ∀ r ∈ [a, b], x.gpr r = y.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [ha, hb]

/-- The working space's register of two runs. -/
theorem regs12 {w : BitVec 32} {x y : State} (hx : Scr x (State.addr w) size)
    (hy : Scr y (State.addr w) size) : ∀ r ∈ [Reg.r12], x.gpr r = y.gpr r :=
  regs1 ((scr_r12 hx).trans (scr_r12 hy).symm)

/-- `ne` after a comparison whose `Z` a proposition decides. -/
theorem eval_ne_of {s : State} {p q : Prop} [Decidable p] [Decidable q] (hz : s.z = decide p)
    (h : ¬p ↔ q) : isa.eval .ne s = some (decide q) := by
  rw [eval_ne, hz]
  by_cases hp : p
  · rw [decide_eq_true hp, decide_eq_false fun hq => h.mpr hq hp]; rfl
  · rw [decide_eq_false hp, decide_eq_true (h.mp hp)]; rfl

theorem not_of_eval_ne {s : State} {p : Prop} [Decidable p] (hz : s.z = decide p)
    (h : isa.eval .ne s = some true) : ¬p := by
  intro hp
  rw [eval_ne, hz, decide_eq_true hp] at h
  exact absurd h (by decide)

theorem bool_eq_of_iff {a b : Bool} {p : Prop} (ha : a = false ↔ p) (hb : b = false ↔ p) : a = b := by
  by_cases hp : p
  · rw [ha.mpr hp, hb.mpr hp]
  · cases a
    · exact absurd (ha.mp rfl) hp
    · cases b
      · exact absurd (hb.mp rfl) hp
      · rfl

/-! ## The points the Jacobian addition adds -/

/-- Neither point is the point at infinity, and their `x` differ: what
`pubAdd`'s branch tests. -/
def Apart {C : Curve} : Point C → Point C → Prop
  | .affine x₁ _, .affine x₂ _ => x₁ ≠ x₂
  | _, _ => False

/-- `pubAdd`'s test of `H` and of the two `Z`, on Jacobian triples of two
points, is of the points. -/
theorem invJ_apart_iff {C : Curve} (hC : Law C) {X1 Y1 Z1 X2 Y2 Z2 : Fe C} {P Q : Point C}
    (h1 : InvJ C X1 Y1 Z1 P) (h2 : InvJ C X2 Y2 Z2 Q) :
    ((X2 * (Z1 * Z1) - X1 * (Z2 * Z2) ≠ 0 ∧ Z1 ≠ 0) ∧ Z2 ≠ 0) ↔ Apart P Q := by
  cases P with
  | infinity =>
    have hz := (h1.z_zero_iff hC).mpr rfl
    cases Q <;> exact ⟨fun h => absurd hz h.1.2, fun h => h.elim⟩
  | affine x1 y1 =>
    cases Q with
    | infinity =>
      have hz := (h2.z_zero_iff hC).mpr rfl
      exact ⟨fun h => absurd hz h.2, fun h => h.elim⟩
    | affine x2 y2 =>
      have hz1 : Z1 ≠ 0 := fun e => nomatch (h1.z_zero_iff hC).mp e
      have hz2 : Z2 ≠ 0 := fun e => nomatch (h2.z_zero_iff hC).mp e
      obtain ⟨a1, -⟩ := h1.affine_coords hC
      obtain ⟨a2, -⟩ := h2.affine_coords hC
      show _ ↔ x1 ≠ x2
      constructor
      · intro h e
        exact h.1.1 (by rw [a1, a2, e]; grind)
      · intro hne
        refine ⟨⟨fun e => ?_, hz1⟩, hz2⟩
        have hd : x2 - x1 ≠ 0 := fun e' => hne (by grind)
        exact hC.mul_ne_zero hd (hC.mul_ne_zero (hC.mul_ne_zero hz1 hz1) (hC.mul_ne_zero hz2 hz2))
          (by rw [a1, a2] at e; grind)

/-- After `pubAddHead`, `Z` is clear if the Jacobian addition adds the two
points. -/
theorem AddMid.apart {base : Addr} {s s' : State} (M : AddMid c base false s s') (hc : CfgOk c)
    (hC : Law c.C) {A B : Point c.C} (h : AddPre c base A B s) : s'.z = false ↔ Apart A B := by
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  obtain hr := jacHeadN_run (fun y => tmv c.C c.n base s (pσ c (ppt false) (TX, TY, TZ) (ppt !false) y))
  have a3 : tmv c.C c.n base s' (pσ c (ppt false) (TX, TY, TZ) (ppt !false) 3) =
      fv c base s TX * (fv c base s DZ * fv c base s DZ) - fv c base s DX * (fv c base s TZ * fv c base s TZ) :=
    (M.vals 3 (Or.inr (by decide))).2.trans hr.2.1
  have e3 : sv c base s' T3 ≠ 0 ↔
      fv c base s TX * (fv c base s DZ * fv c base s DZ) - fv c base s DX * (fv c base s TZ * fv c base s TZ) ≠ 0 :=
    not_congr ((toM_eq_zero_iff hpR (M.vals 3 (Or.inr (by decide))).1).symm.trans (by rw [← a3]))
  have eD : sv c base s' DZ ≠ 0 ↔ fv c base s DZ ≠ 0 := by
    rw [M.eP DZ mem3₃]; exact not_congr (toM_eq_zero_iff hpR (h.ltD _ mem3₃)).symm
  have eT : sv c base s' TZ ≠ 0 ↔ fv c base s TZ ≠ 0 := by
    rw [M.eT TZ mem3₃]; exact not_congr (toM_eq_zero_iff hpR (h.ltT _ mem3₃)).symm
  rw [M.z, ← invJ_apart_iff hC h.repD h.repT, ← e3, ← eD, ← eT]
  simp only [Bool.not_eq_false', decide_eq_true_eq]
  rfl

/-! ## The straight-line pieces -/

/-- Pieces of code in sequence. -/
def pieces : List (Prog isa) → Prog isa
  | [] => .block []
  | p :: ps => .seq p (pieces ps)

/-- Piece `i` of `pieces`. -/
def piece : Prog isa → Nat → Prog isa
  | .seq a _, 0 => a
  | .seq _ b, i + 1 => piece b i
  | p, _ => p

/-- `vg_<curve>_mul_public`'s code between its branches. -/
def pubPieces (c : Cfg) : List (Prog isa) :=
  [.block (.mov wb (.reg .r0) :: c.mulSaved.map fun (r, d) => .str r wb d),
    c.pubTableInit,
    .block c.pubTableLoad,
    c.pubAddHead (c.pt DX DY DZ) (c.pt TX TY TZ),
    fprog c.SP (jacTail c.rcbSlots (c.pt DX DY DZ) (c.pt TX TY TZ) (c.pt RX RY RZ)) c.umaal,
    c.pubSlow (c.pt DX DY DZ) (c.pt TX TY TZ) (c.pt RX RY RZ),
    .block c.pubTableStore,
    bits (c.sl K) (bitsAt c.n 0) (8 * c.n),
    .block (recInit (bitsAt c.n 0)),
    .block (recNext c.pubBits),
    .block [.movw .r11 (BitVec.ofNat 16 c.pubBits)],
    .block (decCounter :: digitLoad (bitsAt c.n 0)),
    .block (c.pubEntry (c.pt RX RY RZ)),
    .block (Point.copyPt c.n (c.pt RX RY RZ) (c.pt ZERO ONEP ZERO)),
    c.pubStepHead,
    .block (c.pubEntry (c.pt TX TY TZ)),
    .block (Point.copyPt c.n (c.pt RX RY RZ) (c.pt DX DY DZ)),
    c.pubFinal,
    .seq (.block [.mov .r10 (.reg .lr)]) (.block (c.mulSaved.map fun (r, d) => .ldr r wb d)),
    .block recHead,
    .block recOpen,
    .block recGrow,
    .block [testCounter],
    .block [.cmp .r9 (.imm 0)],
    .block [.cmp .r9 (.reg .r9)],
    .block [.mov .lr (.reg .r10)]]

/-- Each of `pubPieces` leaks the same from states that agree on the
registers that hold the working space, a position or a digit. -/
structure PubLeaves (c : Cfg) : Prop where
  prologue : LeafCT [.r0] (.block (.mov wb (.reg .r0) :: c.mulSaved.map fun (r, d) => .str r wb d))
  tblInit : LeafCT [.r12] (c.pubTableInit)
  tblLoad : LeafCT [.r12] (.block c.pubTableLoad)
  addHead : LeafCT [.r12] (c.pubAddHead (c.pt DX DY DZ) (c.pt TX TY TZ))
  addTail : LeafCT [.r12] (fprog c.SP (jacTail c.rcbSlots (c.pt DX DY DZ) (c.pt TX TY TZ) (c.pt RX RY RZ)) c.umaal)
  addSlow : LeafCT [.r12] (c.pubSlow (c.pt DX DY DZ) (c.pt TX TY TZ) (c.pt RX RY RZ))
  tblStore : LeafCT [.r12, .r11] (.block c.pubTableStore)
  bits : LeafCT [.r12] (bits (c.sl K) (bitsAt c.n 0) (8 * c.n))
  recInit : LeafCT [.r12] (.block (recInit (bitsAt c.n 0)))
  recNext : LeafCT [] (.block (recNext c.pubBits))
  topInit : LeafCT [] (.block [.movw .r11 (BitVec.ofNat 16 c.pubBits)])
  topLoad : LeafCT [.r12, .r11] (.block (decCounter :: digitLoad (bitsAt c.n 0)))
  startEntry : LeafCT [.r12, .r9] (.block (c.pubEntry (c.pt RX RY RZ)))
  startZero : LeafCT [.r12] (.block (Point.copyPt c.n (c.pt RX RY RZ) (c.pt ZERO ONEP ZERO)))
  stepHead : LeafCT [.r12, .r11] (c.pubStepHead)
  stepEntry : LeafCT [.r12, .r9] (.block (c.pubEntry (c.pt TX TY TZ)))
  stepCopy : LeafCT [.r12] (.block (Point.copyPt c.n (c.pt RX RY RZ) (c.pt DX DY DZ)))
  final : LeafCT [.r12] (c.pubFinal)
  epilogue : LeafCT [.r12] (.seq (.block [.mov .r10 (.reg .lr)]) (.block (c.mulSaved.map fun (r, d) => .ldr r wb d)))
  recHead : LeafCT [.r6, .r9] (.block recHead)
  recOpen : LeafCT [] (.block recOpen)
  recGrow : LeafCT [.r2, .r3] (.block recGrow)
  test : LeafCT [] (.block [testCounter])
  cmpDigit : LeafCT [] (.block [.cmp .r9 (.imm 0)])
  cmpSelf : LeafCT [] (.block [.cmp .r9 (.reg .r9)])
  movLr : LeafCT [] (.block [.mov .lr (.reg .r10)])

/-- `PubLeaves`, by a taint analysis `A` of each of the pieces in sequence
`L`, which other pieces may follow: `taint`, or `taintU` for code with
`umaal`. -/
theorem PubLeaves.of_checks {A : VG.Taint isa} {τ : List Reg → A.T}
    (hA : ∀ (rs : List Reg) (x y : State), (∀ r ∈ rs, x.gpr r = y.gpr r) → A.Agree (τ rs) x y)
    {L : Prog isa} {extra : List (Prog isa)} (hL : L = pieces (pubPieces c ++ extra))
    {h0 : VG.Taint.Hint A.T} (e0 : (A.check (τ [.r0]) (piece L 0) h0).isSome = true)
    {h1 : VG.Taint.Hint A.T} (e1 : (A.check (τ [.r12]) (piece L 1) h1).isSome = true)
    {h2 : VG.Taint.Hint A.T} (e2 : (A.check (τ [.r12]) (piece L 2) h2).isSome = true)
    {h3 : VG.Taint.Hint A.T} (e3 : (A.check (τ [.r12]) (piece L 3) h3).isSome = true)
    {h4 : VG.Taint.Hint A.T} (e4 : (A.check (τ [.r12]) (piece L 4) h4).isSome = true)
    {h5 : VG.Taint.Hint A.T} (e5 : (A.check (τ [.r12]) (piece L 5) h5).isSome = true)
    {h6 : VG.Taint.Hint A.T} (e6 : (A.check (τ [.r12, .r11]) (piece L 6) h6).isSome = true)
    {h7 : VG.Taint.Hint A.T} (e7 : (A.check (τ [.r12]) (piece L 7) h7).isSome = true)
    {h8 : VG.Taint.Hint A.T} (e8 : (A.check (τ [.r12]) (piece L 8) h8).isSome = true)
    {h9 : VG.Taint.Hint A.T} (e9 : (A.check (τ []) (piece L 9) h9).isSome = true)
    {h10 : VG.Taint.Hint A.T} (e10 : (A.check (τ []) (piece L 10) h10).isSome = true)
    {h11 : VG.Taint.Hint A.T} (e11 : (A.check (τ [.r12, .r11]) (piece L 11) h11).isSome = true)
    {h12 : VG.Taint.Hint A.T} (e12 : (A.check (τ [.r12, .r9]) (piece L 12) h12).isSome = true)
    {h13 : VG.Taint.Hint A.T} (e13 : (A.check (τ [.r12]) (piece L 13) h13).isSome = true)
    {h14 : VG.Taint.Hint A.T} (e14 : (A.check (τ [.r12, .r11]) (piece L 14) h14).isSome = true)
    {h15 : VG.Taint.Hint A.T} (e15 : (A.check (τ [.r12, .r9]) (piece L 15) h15).isSome = true)
    {h16 : VG.Taint.Hint A.T} (e16 : (A.check (τ [.r12]) (piece L 16) h16).isSome = true)
    {h17 : VG.Taint.Hint A.T} (e17 : (A.check (τ [.r12]) (piece L 17) h17).isSome = true)
    {h18 : VG.Taint.Hint A.T} (e18 : (A.check (τ [.r12]) (piece L 18) h18).isSome = true)
    {h19 : VG.Taint.Hint A.T} (e19 : (A.check (τ [.r6, .r9]) (piece L 19) h19).isSome = true)
    {h20 : VG.Taint.Hint A.T} (e20 : (A.check (τ []) (piece L 20) h20).isSome = true)
    {h21 : VG.Taint.Hint A.T} (e21 : (A.check (τ [.r2, .r3]) (piece L 21) h21).isSome = true)
    {h22 : VG.Taint.Hint A.T} (e22 : (A.check (τ []) (piece L 22) h22).isSome = true)
    {h23 : VG.Taint.Hint A.T} (e23 : (A.check (τ []) (piece L 23) h23).isSome = true)
    {h24 : VG.Taint.Hint A.T} (e24 : (A.check (τ []) (piece L 24) h24).isSome = true)
    {h25 : VG.Taint.Hint A.T} (e25 : (A.check (τ []) (piece L 25) h25).isSome = true) :
    PubLeaves c := by
  subst hL
  exact ⟨RelCT.taint _ (hA _) e0, RelCT.taint _ (hA _) e1, RelCT.taint _ (hA _) e2, RelCT.taint _ (hA _) e3, RelCT.taint _ (hA _) e4, RelCT.taint _ (hA _) e5, RelCT.taint _ (hA _) e6, RelCT.taint _ (hA _) e7, RelCT.taint _ (hA _) e8, RelCT.taint _ (hA _) e9, RelCT.taint _ (hA _) e10, RelCT.taint _ (hA _) e11, RelCT.taint _ (hA _) e12, RelCT.taint _ (hA _) e13, RelCT.taint _ (hA _) e14, RelCT.taint _ (hA _) e15, RelCT.taint _ (hA _) e16, RelCT.taint _ (hA _) e17, RelCT.taint _ (hA _) e18, RelCT.taint _ (hA _) e19, RelCT.taint _ (hA _) e20, RelCT.taint _ (hA _) e21, RelCT.taint _ (hA _) e22, RelCT.taint _ (hA _) e23, RelCT.taint _ (hA _) e24, RelCT.taint _ (hA _) e25⟩

/-! ## The pieces put together -/

variable {w : BitVec 32}

/-- `pubAdd` on Jacobian triples of `A` and `B`: its branch is of the points. -/
theorem pubAdd_ct (hc : CfgOk c) (hC : Law c.C) (L : PubLeaves c) {A B : Point c.C} :
    Det (AddPre c (State.addr w) A B) (c.pubAdd (c.pt DX DY DZ) (c.pt TX TY TZ) (c.pt RX RY RZ)) := by
  rw [Cfg.pubAdd]
  refine Det.seq (J := fun s => Scr s (State.addr w) size ∧ (s.z = false ↔ Apart A B))
    (Det.leaf L.addHead fun _ _ hx hy => regs12 hx.ctx.scr hy.ctx.scr)
    (fun s h => WP.mono (pubAddHead_ok hc h.ctx false h.ltD h.ltT) fun _ M => ⟨M.ctx.scr, M.apart hc hC h⟩)
    (Det.ite (fun x y hx hy => by rw [eval_ne, eval_ne, bool_eq_of_iff hx.2 hy.2])
      (Det.leaf L.addTail fun _ _ hx hy => regs12 hx.1.1 hy.1.1)
      (Det.leaf L.addSlow fun _ _ hx hy => regs12 hx.1.1 hy.1.1))

/-- An entry of the table. -/
theorem pubTableStep_ct (hc : CfgOk c) (hC : Law c.C) {P : Point c.C} (hP : onCurve c.C P = true)
    (L : PubLeaves c) {e : Nat} :
    Det (fun s => ∃ s₀, PubBuildInv c (State.addr w) P s₀ s e) c.pubTableStep := by
  rw [Cfg.pubTableStep]
  refine Det.seq (J := fun s => AddPre c (State.addr w) (mul (2 * e - 1) P) (mul 2 P) s ∧
      s.gpr .r11 = BitVec.ofNat 32 e)
    (Det.leaf L.tblLoad fun _ _ ⟨_, hx⟩ ⟨_, hy⟩ => regs12 hx.ctx.scr hy.ctx.scr)
    (fun s ⟨_, I⟩ => WP.mono (pubTableLoad_ok hc I) fun _ M => ⟨M.addPre, M.r11⟩)
    (Det.seq (J := fun s => Scr s (State.addr w) size ∧ s.gpr .r11 = BitVec.ofNat 32 e)
      ((pubAdd_ct hc hC L).mono fun _ h => h.1)
      (fun s ⟨A, g⟩ => WP.mono (pubAdd_ok hc hC A.ctx false (hC.onCurve_mul hP _) (hC.onCurve_mul hP _)
        A.ltD A.ltT A.repD A.repT) fun s' ⟨K, U, _, _⟩ =>
          ⟨(A.ctx.next hc K (by decide) U (winW_winWr hc.n10)).scr, by rw [K.gpr _ r11_not_clob, g]⟩)
      (Det.leaf L.tblStore fun _ _ hx hy =>
        regs2 ((scr_r12 hx.1).trans (scr_r12 hy.1).symm) (hx.2.trans hy.2.symm)))

/-- The table. -/
theorem pubTable_ct (hc : CfgOk c) (hC : Law c.C) {P : Point c.C} (hP : onCurve c.C P = true)
    (L : PubLeaves c) {k : Nat} : Det (PubPre c (State.addr w) P k) c.pubTable := by
  rw [Cfg.pubTable]
  refine Det.seq (J := fun s => ∃ s₀, PubBuildInv c (State.addr w) P s₀ s 1)
    (Det.leaf L.tblInit fun _ _ hx hy => regs12 hx.ctx.scr hy.ctx.scr)
    (fun s h => WP.mono (pubTableInit_ok hc hC hP h.ctx h.ltx h.lty h.rep) fun _ I => ⟨s, I⟩) ?_
  refine (Det.loop (fun n s => 1 ≤ n ∧ n ≤ 7 ∧ ∃ s₀, PubBuildInv c (State.addr w) P s₀ s (8 - n))
    (fun n => decide (n ≠ 1)) (fun n => (pubTableStep_ct hc hC hP L).mono fun _ h => h.2.2)
    (fun n s ⟨h1, h7, s₀, I⟩ => ?_) 7).mono fun s h => ⟨by decide, by decide, h⟩
  refine WP.mono (pubTableStep_ok hc hC hP (by omega_using [h7]) (by omega_using [h1]) I)
    fun s' ⟨I', z⟩ => ⟨eval_ne_of z (by omega_using [h1, h7]), fun hb => ?_⟩
  have hn : n ≠ 1 := of_decide_eq_true hb
  refine ⟨by omega_using [h1], by omega_using [h1, hn], by omega_using [h7], s₀, ?_⟩
  rw [show 8 - (n - 1) = 8 - n + 1 by omega_using [h1, h7]]; exact I'

/-- The recoding: its branch is on whether a window is in hand, which the
number and the position determine. -/
theorem recode_ct (hc : CfgOk c) (L : PubLeaves c) {k : Nat} :
    Det (fun s => Scr s (State.addr w) size ∧ Far s (State.addr w) 8192 ∧
      ∀ t < c.pubBits, s.mem (off (State.addr w) (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0)
      (recode (bitsAt c.n 0) c.pubBits) := by
  have h7 := hc.n10
  have hN := pubBits_le hc
  have hN0 : 0 < c.pubBits := by have := hc.len8; unfold Cfg.pubBits; omega_using [this]
  have hb0 : bitsAt c.n 0 = 4096 := by rw [bitsAt_eq, Nat.mul_zero, Nat.add_zero]
  have hl : bitsAt c.n 0 + c.pubBits ≤ 8192 := by omega_using [hb0, hN, h7]
  have hnb : c.pubBits < 2 ^ 16 := by omega_using [hN, h7]
  have r12 : ∀ {s₀ s : State} {i : Nat}, Scr s₀ (State.addr w) size →
      RecInv (State.addr w) (bitsAt c.n 0) c.pubBits k s₀ i s → s.gpr .r12 = w := fun hs I =>
    (I.keep.gpr _ (by decide)).trans (scr_r12 hs)
  rw [recode]
  refine Det.seq (J := fun s => ∃ s₀, Scr s₀ (State.addr w) size ∧ Far s₀ (State.addr w) 8192 ∧
      RecInv (State.addr w) (bitsAt c.n 0) c.pubBits k s₀ 0 s)
    (Det.leaf L.recInit fun _ _ hx hy => regs12 hx.1 hy.1)
    (fun s ⟨hs, hf, hb⟩ => WP.mono (recInit_ok (by rw [hb0]; decide) hb) fun _ I => ⟨s, hs, hf, I⟩) ?_
  refine (Det.loop (fun n s => 1 ≤ n ∧ n ≤ c.pubBits ∧ ∃ s₀, Scr s₀ (State.addr w) size ∧
      Far s₀ (State.addr w) 8192 ∧ RecInv (State.addr w) (bitsAt c.n 0) c.pubBits k s₀ (c.pubBits - n) s)
    (fun n => decide (n ≠ 1)) (fun n => ?_) (fun n s ⟨h1, hn, s₀, hs, hf, I⟩ => ?_) c.pubBits).mono
    fun s h => ⟨hN0, Nat.le_refl _, by rwa [Nat.sub_self]⟩
  · by_cases hn : 1 ≤ n ∧ n ≤ c.pubBits
    swap
    · exact Det.of_false fun s h => hn ⟨h.1, h.2.1⟩
    have hi : c.pubBits - n < c.pubBits := by omega_using [hn.1, hn.2]
    refine Det.seq (J := fun s₃ => ∃ s₀ s, Scr s₀ (State.addr w) size ∧
        RecInv (State.addr w) (bitsAt c.n 0) c.pubBits k s₀ (c.pubBits - n) s ∧
        RecMid (bitsAt c.n 0) k (c.pubBits - n) s s₃)
      (Det.leaf L.recHead fun x y ⟨_, _, _, hx, _, Ix⟩ ⟨_, _, _, hy, _, Iy⟩ =>
        regs2 (by rw [Ix.r6, Iy.r6, r12 hx Ix, r12 hy Iy]) (Ix.r9.trans Iy.r9.symm))
      (fun s ⟨_, _, s₀, hs, hf, I⟩ => WP.mono (recHead_ok hs hf hl hi I) fun _ M => ⟨s₀, s, hs, I, M⟩)
      (Det.seq_any (Det.ite (fun x y ⟨_, _, _, _, Mx⟩ ⟨_, _, _, _, My⟩ => by rw [eval_eq, eval_eq, Mx.z, My.z])
          (Det.leaf L.recOpen fun _ _ _ _ => regs0)
          (Det.leaf L.recGrow fun x y ⟨⟨_, _, hx, Ix, Mx⟩, _⟩ ⟨⟨_, _, hy, Iy, My⟩, _⟩ => regs2
            (by rw [Mx.r2, My.r2, Mx.regs .r12 (by decide) (by decide), My.regs .r12 (by decide) (by decide),
              r12 hx Ix, r12 hy Iy])
            (by rw [Mx.regs .r3 (by decide) (by decide), My.regs .r3 (by decide) (by decide), Ix.r3, Iy.r3,
              r12 hx Ix, r12 hy Iy])))
        (Det.leaf L.recNext fun _ _ _ _ => regs0))
  · refine WP.mono (recStep_ok hs hf hl hnb (by omega_using [h1, hn]) I) fun s' ⟨I', z⟩ =>
      ⟨eval_ne_of z (by omega_using [h1, hn]), fun hb => ?_⟩
    have hn1 : n ≠ 1 := of_decide_eq_true hb
    refine ⟨by omega_using [h1], by omega_using [h1, hn1], by omega_using [hn], s₀, hs, hf, ?_⟩
    rw [show c.pubBits - (n - 1) = c.pubBits - n + 1 by omega_using [h1, hn]]; exact I'

/-- The search for the top digit: its branches are on the digits. -/
theorem pubTop_ct (hc : CfgOk c) (L : PubLeaves c) {P : Point c.C} {k : Nat} :
    Det (PubCtx c (State.addr w) P k) c.pubTop := by
  rw [Cfg.pubTop]
  refine Det.seq (J := fun t => ∃ s, PubCtx c (State.addr w) P k s ∧ TopInv c k s t c.pubBits)
    (Det.leaf L.topInit fun _ _ _ _ => regs0)
    (fun s h => WP.mono (pubTopInit_ok hc (k := k)) fun _ I => ⟨s, h, I⟩) ?_
  refine Det.loop (fun n t => ∃ s, PubCtx c (State.addr w) P k s ∧ TopInv c k s t n) (topMore c k)
    (fun n => ?_) (fun n t ⟨s, ctx, I⟩ => WP.mono (pubTopStep_ok hc ctx I) fun t' ⟨he, hm, _⟩ =>
      ⟨he, fun hb => ⟨Nat.lt_of_lt_of_le Nat.zero_lt_one I.h1, s, ctx, hm hb⟩⟩) c.pubBits
  rw [Cfg.pubTopStep]
  exact Det.seq (J := fun t₂ => ∃ s, TopMid c k s t₂ n)
    (Det.leaf L.topLoad fun x y ⟨_, cx, Ix⟩ ⟨_, cy, Iy⟩ => regs2
      (by rw [Ix.keep.gpr _ (by decide), Iy.keep.gpr _ (by decide), scr_r12 cx.scr, scr_r12 cy.scr])
      (Ix.r11.trans Iy.r11.symm))
    (fun t ⟨s, ctx, I⟩ => WP.mono (pubTopLoad_ok hc ctx I) fun _ M => ⟨s, M⟩)
    (Det.ite (fun x y ⟨_, Mx⟩ ⟨_, My⟩ => by rw [eval_eq, eval_eq, Mx.z, My.z])
      (Det.leaf L.test fun _ _ _ _ => regs0) (Det.leaf L.cmpSelf fun _ _ _ _ => regs0))

/-- The sum's start: its branch is on the top digit. -/
theorem pubStart_ct (L : PubLeaves c) {d : Nat} :
    Det (fun s => Scr s (State.addr w) size ∧ s.gpr .r9 = BitVec.ofNat 32 d) c.pubStart := by
  rw [Cfg.pubStart]
  exact Det.seq (J := fun s => Scr s (State.addr w) size ∧ s.gpr .r9 = BitVec.ofNat 32 d ∧
      s.z = (BitVec.ofNat 32 d - 0 == 0))
    (Det.leaf L.cmpDigit fun _ _ _ _ => regs0)
    (fun s ⟨hs, g⟩ => wp_cmp (op2_imm (by decide)) fun s₁ f₁ z₁ => WP.block_nil
      ⟨hs.of_rest (f₁.rest []) (by decide), by rw [f₁.gpr, g], by rw [z₁, g]⟩)
    (Det.ite (fun x y hx hy => by rw [eval_ne, eval_ne, hx.2.2, hy.2.2])
      (Det.leaf L.startEntry fun _ _ hx hy =>
        regs2 ((scr_r12 hx.1.1).trans (scr_r12 hy.1.1).symm) (hx.1.2.1.trans hy.1.2.1.symm))
      (Det.leaf L.startZero fun _ _ hx hy => regs12 hx.1.1 hy.1.1))

/-- A digit: its branch is on the digit. -/
theorem pubStep_ct (hc : CfgOk c) (hC : Law c.C) {P : Point c.C} (hP : onCurve c.C P = true)
    (L : PubLeaves c) {k j : Nat} (hj1 : 1 ≤ j) (hj : j ≤ c.pubBits) :
    Det (fun s => ∃ s₀, PubInv c (State.addr w) P k s₀ s j) c.pubStep := by
  rw [Cfg.pubStep]
  exact Det.seq (J := fun s => ∃ s₀, StepMid c (State.addr w) P k s₀ s j)
    (Det.leaf L.stepHead fun _ _ ⟨_, Ix⟩ ⟨_, Iy⟩ =>
      regs2 ((scr_r12 Ix.ctx.scr).trans (scr_r12 Iy.ctx.scr).symm) (Ix.r11.trans Iy.r11.symm))
    (fun s ⟨s₀, I⟩ => WP.mono (pubStepHead_ok hc hC hP hj1 hj I) fun _ M => ⟨s₀, M⟩)
    (Det.seq_any (Det.ite (fun x y ⟨_, Mx⟩ ⟨_, My⟩ => by rw [eval_ne, eval_ne, Mx.z, My.z])
        (Det.seq (J := AddPre c (State.addr w)
            (mul (2 * Slide.wsum (Slide.digits c.pubBits k) j (c.pubBits - j)) P)
            (mul (Slide.digits c.pubBits k (j - 1)) P))
          (Det.leaf L.stepEntry fun _ _ ⟨⟨_, Mx⟩, _⟩ ⟨⟨_, My⟩, _⟩ =>
            regs2 ((scr_r12 Mx.ctx.scr).trans (scr_r12 My.ctx.scr).symm) (Mx.r9.trans My.r9.symm))
          (fun s ⟨⟨_, M⟩, hne⟩ => WP.mono (pubStepEntry_ok hc M (not_of_eval_ne M.z hne)) fun _ h => h.1)
          (pubAdd_ct hc hC L))
        (Det.leaf L.stepCopy fun _ _ ⟨⟨_, Mx⟩, _⟩ ⟨⟨_, My⟩, _⟩ => regs12 Mx.ctx.scr My.ctx.scr))
      (Det.leaf L.test fun _ _ _ _ => regs0))

/-- The digits below the top one. -/
theorem pubLoop_ct (hc : CfgOk c) (hC : Law c.C) {P : Point c.C} (hP : onCurve c.C P = true)
    (L : PubLeaves c) {k : Nat} (n : Nat) :
    Det (fun s => 1 ≤ n ∧ n ≤ c.pubBits ∧ ∃ s₀, PubInv c (State.addr w) P k s₀ s n)
      (.loop c.pubStep .ne) := by
  refine Det.loop (fun n s => 1 ≤ n ∧ n ≤ c.pubBits ∧ ∃ s₀, PubInv c (State.addr w) P k s₀ s n)
    (fun n => decide (n - 1 ≠ 0)) (fun n => ?_) (fun n s ⟨h1, hn, s₀, I⟩ => ?_) n
  · by_cases h : 1 ≤ n ∧ n ≤ c.pubBits
    · exact (pubStep_ct hc hC hP L h.1 h.2).mono fun _ h => h.2.2
    · exact Det.of_false fun s hs => h ⟨hs.1, hs.2.1⟩
  · refine WP.mono (pubStep_ok hc hC hP h1 hn I) fun s' ⟨I', z⟩ => ⟨eval_ne_of z Iff.rfl, fun hb => ?_⟩
    have h0 : n - 1 ≠ 0 := of_decide_eq_true hb
    exact ⟨by omega_using [h1], by omega_using [h0], by omega_using [hn], s₀, I'⟩

theorem PubPre.same {base : Addr} {P : Point c.C} {k : Nat} {s s' : State} (h : PubPre c base P k s)
    (hc : CfgOk c) {rs : List Reg} (hr : Rest rs s s') (h12 : .r12 ∉ rs) (hm : s'.mem = s.mem) :
    PubPre c base P k s' :=
  ⟨h.ctx.same hc hr h12 hm, by show wordsVal s'.mem _ _ _ < _; rw [hm]; exact h.ltx,
    by show wordsVal s'.mem _ _ _ < _; rw [hm]; exact h.lty, by
      show Rep _ (toM _ _ (wordsVal s'.mem _ _ _)) (toM _ _ (wordsVal s'.mem _ _ _)) _ _
      rw [hm]; exact h.rep,
    by show wordsVal s'.mem _ _ _ = _; rw [hm]; exact h.kv, h.kb⟩

/-- `pubBody`. -/
theorem pubBody_ct (hc : CfgOk c) (hC : Law c.C) {P : Point c.C} (hP : onCurve c.C P = true)
    (L : PubLeaves c) {k : Nat} : Det (PubPre c (State.addr w) P k) c.pubBody := by
  have hN0 : 0 < c.pubBits := by have := hc.len8; unfold Cfg.pubBits; omega_using [this]
  rw [Cfg.pubBody]
  refine Det.seq (J := fun s => ∃ s₀, PubS1 c (State.addr w) P k s₀ s) (pubTable_ct hc hC hP L)
    (fun s h => WP.mono (pubS1_ok hc hC hP h) fun _ h₁ => ⟨s, h₁⟩) ?_
  refine Det.seq (J := fun s => ∃ s₀, PubS2 c (State.addr w) P k s₀ s)
    (Det.leaf L.bits fun _ _ ⟨_, hx⟩ ⟨_, hy⟩ => regs12 hx.1.scr hy.1.scr)
    (fun s ⟨s₀, h⟩ => WP.mono (pubS2_ok hc h) fun _ h₂ => ⟨s₀, h₂⟩) ?_
  refine Det.seq (J := fun s => ∃ s₀, PubS3 c (State.addr w) P k s₀ s)
    ((recode_ct hc L (k := k)).mono fun s ⟨_, h⟩ => ⟨h.1.scr, h.1.far, h.2.2.2.2⟩)
    (fun s ⟨s₀, h⟩ => WP.mono (pubS3_ok hc h) fun _ h₃ => ⟨s₀, h₃⟩) ?_
  refine Det.seq (J := fun s => ∃ s₀, PubS4 c (State.addr w) P k s₀ s)
    ((pubTop_ct hc L).mono fun s ⟨_, h⟩ => h.1)
    (fun s ⟨s₀, h⟩ => WP.mono (pubS4_ok hc h) fun _ h₄ => ⟨s₀, h₄⟩) ?_
  refine Det.seq (J := fun s => ∃ s₀, PubS5 c (State.addr w) P k s₀ s)
    ((pubStart_ct L).mono fun s ⟨_, h⟩ => ⟨h.1.1.scr, h.2.2⟩)
    (fun s ⟨s₀, h⟩ => WP.mono (pubS5_ok hc h) fun _ h₅ => ⟨s₀, h₅⟩) ?_
  refine Det.seq (J := fun s => ∃ s₀, PubInv c (State.addr w) P k s₀ s (pubTopPos c k) ∧
      s.z = decide (pubTopPos c k = 0))
    (Det.leaf L.test fun _ _ _ _ => regs0)
    (fun s ⟨s₀, h⟩ => WP.mono (pubS6_ok hc h) fun _ h₆ => ⟨s₀, h₆⟩) ?_
  exact Det.seq (J := fun s => Scr s (State.addr w) size)
    (Det.ite (fun x y ⟨_, _, zx⟩ ⟨_, _, zy⟩ => by rw [eval_ne, eval_ne, zx, zy])
      ((pubLoop_ct hc hC hP L (pubTopPos c k)).mono fun s ⟨⟨s₀, I, z⟩, hne⟩ =>
        ⟨Nat.pos_of_ne_zero (not_of_eval_ne z hne), Nat.le_of_lt (Slide.topPos_lt _ hN0), s₀, I⟩)
      (RelCT.block_nil fun _ _ _ => trivial))
    (fun s ⟨s₀, I, z⟩ => WP.mono (pubDigits_ok hc hC hP I z) fun _ I' => I'.ctx.scr)
    (Det.leaf L.final fun _ _ hx hy => regs12 hx hy)

/-- `vg_<curve>_mul_public`, on the same number and point from the same
working space. -/
theorem pubFn_ct (hc : CfgOk c) (hC : Law c.C) {P : Point c.C} (hP : onCurve c.C P = true)
    (L : PubLeaves c) {k : Nat} : Det (PubEntry c w P k) c.pubFn := by
  rw [Cfg.pubFn, Cfg.mulFnOf]
  refine Det.seq (J := PubPre c (State.addr w) P k)
    (Det.leaf L.prologue fun _ _ hx hy => regs1 (hx.r0.trans hy.r0.symm))
    (fun s h => pubPrologue_ok hc h) ?_
  refine Det.seq (J := PubPre c (State.addr w) P k) (Det.leaf L.movLr fun _ _ _ _ => regs0)
    (fun s h => wp_mov (op2_reg _ _) fun s₁ u₁ => WP.block_nil
      (h.same hc (u₁.rest (ws := [.lr]) (by simp)) (by decide) u₁.mem)) ?_
  exact Det.seq (J := fun s => Scr s (State.addr w) size) (pubBody_ct hc hC hP L)
    (fun s h => WP.mono (pubBody_ok hc hC h.ctx.scr h.ctx.far h.ctx.mp h.ctx.ap h.ctx.b3p h.ctx.zero
      h.ctx.onep h.ltx h.lty hP h.rep (by rw [h.kv]; exact h.kb)) fun s' ⟨K, _⟩ =>
        h.ctx.scr.of_rest K (by decide))
    (Det.leaf L.epilogue fun _ _ hx hy => regs12 hx hy)

/-- The call instruction keeps what `vg_<curve>_mul_public` is called with. -/
theorem PubEntry.callEntry {P : Point c.C} {k : Nat} {s : State} (h : PubEntry c w P k s) :
    PubEntry c w P k s.callEntry :=
  ⟨by rw [State.callEntry_gpr _ (by decide)]; exact h.r0, h.wr, ⟨h.far.wr, h.far.nowrap⟩, h.mp, h.ap,
    h.b3p, h.zero, h.onep, h.ltx, h.lty, h.rep, h.kv, h.kb⟩

/-- Two calls of `vg_<curve>_mul_public` on the same number and point, from
the same working space, leak the same. -/
theorem pubCall_ct (hc : CfgOk c) (hC : Law c.C) {P : Point c.C} (hP : onCurve c.C P = true)
    (L : PubLeaves c) (name : String) {k : Nat} :
    RelCT isa (fun x y => PubEntry c w P k x ∧ PubEntry c w P k y) (.call name c.pubFn) fun _ _ => True :=
  relCT_call (RelCT.mono (pubFn_ct hc hC hP L (k := k))
    (fun _ _ ⟨_, _, h, e₁, e₂⟩ => ⟨e₁ ▸ h.1.callEntry, e₂ ▸ h.2.callEntry⟩) fun _ _ h => h)

end VG.Proof.Ecdsa.Arm
