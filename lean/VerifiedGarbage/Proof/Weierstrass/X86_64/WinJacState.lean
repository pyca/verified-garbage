import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJ
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacSelect
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacOps
import VerifiedGarbage.Proof.Weierstrass.WinJacMath

/-!
# The Jacobian window method on x86-64: what holds between its steps

A point with its cached powers in five slots (`JPt`: Jacobian coordinates
`X`, `Y`, `Z ≠ 0`, then `Z²` and `Z³`), as `T` and each entry of the table
hold them (`TblOk`); what the method reads at the start (`JacWinFixed`); what
the method needs of the doubling it is given (`DblOk`); and the frame of the
whole method (`JFrame`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

/-- The five slots `o 0 … o 4` hold a Jacobian triple of `Q ≠ O` and its `Z²`, `Z³`. -/
structure JPt (C : Curve) (n : Nat) (base : Addr) (s : State) (o : Nat → Nat) (Q : Point C) : Prop where
  lt : ∀ c < 5, wordsVal s.mem base (o c) n < C.p
  jac : InvJ C (tmv C n base s (o 0)) (tmv C n base s (o 1)) (tmv C n base s (o 2)) Q
  z : tmv C n base s (o 2) ≠ 0
  z2 : tmv C n base s (o 3) = tmv C n base s (o 2) * tmv C n base s (o 2)
  z3 : tmv C n base s (o 4) = tmv C n base s (o 3) * tmv C n base s (o 2)

theorem JPt.congr {C : Curve} {n : Nat} {base : Addr} {s s' : State} {o o' : Nat → Nat} {Q : Point C}
    (h : JPt C n base s o Q) (he : ∀ c < 5, wordsVal s'.mem base (o' c) n = wordsVal s.mem base (o c) n) :
    JPt C n base s' o' Q := by
  have e : ∀ c < 5, tmv C n base s' (o' c) = tmv C n base s (o c) := fun c hc => by
    show toM _ _ _ = toM _ _ _; rw [he c hc]
  refine ⟨fun c hc => by rw [he c hc]; exact h.lt c hc, ?_, ?_, ?_, ?_⟩
  · rw [e 0 (by decide), e 1 (by decide), e 2 (by decide)]; exact h.jac
  · rw [e 2 (by decide)]; exact h.z
  · rw [e 3 (by decide), e 2 (by decide)]; exact h.z2
  · rw [e 4 (by decide), e 3 (by decide), e 2 (by decide)]; exact h.z3

/-- The slots of entry `m` of the table. -/
abbrev entS (K : JacWinCfg) (m : Nat) : Nat → Nat := fun c => jg K (5 * (m - 1) + c)

/-- `T`'s slots. -/
abbrev TS (K : JacWinCfg) : Nat → Nat := fun c => jg K (80 + c)

/-- Entries `1 … M` of the table hold `[m]P`. -/
def TblOk (K : JacWinCfg) (C : Curve) (base : Addr) (P : Point C) (M : Nat) (s : State) : Prop :=
  ∀ m, 1 ≤ m → m ≤ M → JPt C K.M.n base s (entS K m) (mul m P)

variable {K : JacWinCfg} {size : Nat}

/-- A grid slot apart from what is written survives. -/
theorem jgWord_unch (hL : JacWinLay K size) {base : Addr} {W : List (Nat × Nat)} {m m' : Mem}
    (hU : Unch base W m m') (hn : base.toNat + size ≤ 2 ^ 64) {i : Nat} (hi : i < 85)
    (hW : ∀ w ∈ W, jg K i + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ jg K i) :
    wordsVal m' base (jg K i) K.M.n = wordsVal m base (jg K i) K.M.n :=
  hU.wordsVal hW (by have := hL.le (jg_mem (K := K) hi); omega)

theorem TblOk.unch (hL : JacWinLay K size) {C : Curve} {base : Addr} {P : Point C} {M : Nat}
    {s s' : State} (hT : TblOk K C base P M s) {W : List (Nat × Nat)} (hU : Unch base W s.mem s'.mem)
    (hn : base.toNat + size ≤ 2 ^ 64) (hM : M ≤ 16)
    (hW : ∀ w ∈ W, ∀ i < 5 * M, jg K i + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ jg K i) :
    TblOk K C base P M s' := fun m h1 hm =>
  (hT m h1 hm).congr fun c hc => jgWord_unch hL hU hn (by omega) fun w hw => hW w hw _ (by omega)

theorem JPt.unchT (hL : JacWinLay K size) {C : Curve} {base : Addr} {Q : Point C} {s s' : State}
    (hT : JPt C K.M.n base s (TS K) Q) {W : List (Nat × Nat)} (hU : Unch base W s.mem s'.mem)
    (hn : base.toNat + size ≤ 2 ^ 64)
    (hW : ∀ w ∈ W, ∀ c < 5, jg K (80 + c) + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ jg K (80 + c)) :
    JPt C K.M.n base s' (TS K) Q :=
  hT.congr fun c hc => jgWord_unch hL hU hn (by omega) fun w hw => hW w hw c hc

/-- The loop writes nothing of the table. -/
theorem loopW_apart (hL : JacWinLay K size) {i : Nat} (hi : i < 80) :
    ∀ w ∈ jwLoopW K, jg K i + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ jg K i := by
  intro w hw
  simp only [jwLoopW, List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · rcases hy with hy | ⟨c, hc, rfl⟩
    · exact (hL.jg_apart (List.mem_append_right _ hy) (by omega)).symm
    · exact jg_apart K (by have := List.mem_range.mp hc; omega)
  · exact hL.lay.tmp _ (jg_mem (by omega))

/-- What the method reads and never writes, at the start: zero, `P` (affine:
`Z` is Montgomery's one), and the table of the bits of `k + offset J`. -/
structure JacWinFixed (K : JacWinCfg) (C : Curve) (base : Addr) (s₀ : State) (P : Point C) (k : Nat) :
    Prop where
  zero : wordsVal s₀.mem base K.zero K.M.n = 0
  ro_lt : ∀ x ∈ [K.P.x, K.P.y, K.P.z], wordsVal s₀.mem base x K.M.n < C.p
  pt : Rep C (tmv C K.M.n base s₀ K.P.x) (tmv C K.M.n base s₀ K.P.y) (tmv C K.M.n base s₀ K.P.z) P
  pz : tmv C K.M.n base s₀ K.P.z = 1
  bits : ∀ t < 5 * K.J, s₀.mem (off base (K.bits + t)) =
    if (k + JacWinCfg.offset K.J).testBit t then 1 else 0

/-- What the method needs of the doubling `dbl p`: from a Jacobian triple of
`Q` in `p`, a triple of `2 Q`, writing only the temporaries and `p`. -/
def DblOk (M : Mod) (S : RcbSlots) (C : Curve) (dbl : Pt → Prog isa) : Prop :=
  ∀ {base : Addr} {size : Nat} {Sl : Nat → Prop}, Lay M size Sl → ∀ {p : Pt}, (rcbW S p).Nodup →
    (∀ x ∈ rcbW S p, Sl x) → ∀ {E : Nat → Fe C} {s : State},
    Inv M base size C.p Sl [p.x, p.y, p.z] E s → ∀ {Q : Point C}, onCurve C Q = true →
    InvJ C (E p.x) (E p.y) (E p.z) Q →
    WP isa (dbl p) s fun t => ProgKeep M base (rcbW S p) s t ∧ ∃ E' : Nat → Fe C,
      Inv M base size C.p Sl [p.x, p.y, p.z] E' t ∧ InvJ C (E' p.x) (E' p.y) (E' p.z) (add Q Q)

/-- The method's frame from `s₀`. -/
structure JFrame (K : JacWinCfg) (C : Curve) (base : Addr) (size : Nat) (s₀ s : State) : Prop where
  scr : Scr s base size
  keep : KeepRegs (powClob K.M.n) s₀ s
  unch : Unch base (jwW K) s₀.mem s.mem
  mod : ModOkW K.M size C.p s.mem base

theorem JFrame.next (hL : JacWinLay K size) {C : Curve} {base : Addr} {s₀ s s' : State}
    (h : JFrame K C base size s₀ s) (hs : Scr s' base size) (hk : KeepRegs (powClob K.M.n) s s')
    {W : List (Nat × Nat)} (hU : Unch base W s.mem s'.mem) (hW : ∀ w ∈ W, w ∈ jwW K) :
    JFrame K C base size s₀ s' :=
  ⟨hs, h.keep.trans hk, (h.unch.trans (hU.mono hW)).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw <;> exact hw,
    h.mod.unch (hU.mono hW) (hL.w_mo h.mod) h.scr.nowrap⟩

theorem JFrame.ro (hL : JacWinLay K size) {C : Curve} {base : Addr} {s₀ s : State}
    (h : JFrame K C base size s₀ s) {x : Nat} (hx : x ∈ jwRo K) :
    wordsVal s.mem base x K.M.n = wordsVal s₀.mem base x K.M.n :=
  h.unch.wordsVal (hL.ro_w hx) (by have := hL.le (ro_mem hx); have := h.scr.nowrap; omega)

theorem JFrame.ro_tmv (hL : JacWinLay K size) {C : Curve} {base : Addr} {s₀ s : State}
    (h : JFrame K C base size s₀ s) {x : Nat} (hx : x ∈ jwRo K) :
    tmv C K.M.n base s x = tmv C K.M.n base s₀ x := by
  show toM _ _ _ = toM _ _ _; rw [h.ro hL hx]

theorem mem_jwW_ws {x : Nat} (h : x ∈ jwWs K) : (x, 8 * K.M.n) ∈ jwW K :=
  List.mem_append_left _ (List.mem_map.mpr ⟨x, h, rfl⟩)

theorem mem_jwW_tmp : (K.M.tmp, 8 * K.M.n) ∈ jwW K := List.mem_append_right _ (List.mem_singleton_self _)

/-- `x ∈ jwSlots`, `jwWs` for the named slots (by `jw_mem`, or a slot of `T`). -/
theorem JacWinLay.T_mem (hL : JacWinLay K size) :
    K.E.x ∈ jwSlots K ∧ K.E.y ∈ jwSlots K ∧ K.E.z ∈ jwSlots K ∧ K.z2 ∈ jwSlots K ∧
      K.z2 + 8 * K.M.n ∈ jwSlots K := by
  rw [hL.Tz3, hL.Tx, hL.Ty, hL.Tz, hL.Tz2]
  exact ⟨jg_mem (by decide), jg_mem (by decide), jg_mem (by decide), jg_mem (by decide), jg_mem (by decide)⟩

theorem JacWinLay.T_ws (hL : JacWinLay K size) :
    K.E.x ∈ jwWs K ∧ K.E.y ∈ jwWs K ∧ K.E.z ∈ jwWs K ∧ K.z2 ∈ jwWs K ∧ K.z2 + 8 * K.M.n ∈ jwWs K := by
  rw [hL.Tz3, hL.Tx, hL.Ty, hL.Tz, hL.Tz2]
  exact ⟨jg_ws (by decide), jg_ws (by decide), jg_ws (by decide), jg_ws (by decide), jg_ws (by decide)⟩

/-- `T`'s slots, written by the loop. -/
theorem T_loopW (K : JacWinCfg) {c : Nat} (hc : c < 5) :
    (jg K (80 + c), 8 * K.M.n) ∈ jwLoopW K :=
  List.mem_append_left _ (List.mem_map.mpr ⟨_, List.mem_append_right _
    (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩), rfl⟩)

theorem other_loopW {x : Nat} (h : x ∈ jwOther K) : (x, 8 * K.M.n) ∈ jwLoopW K :=
  List.mem_append_left _ (List.mem_map.mpr ⟨x, List.mem_append_left _ h, rfl⟩)

theorem tmp_loopW : (K.M.tmp, 8 * K.M.n) ∈ jwLoopW K := List.mem_append_right _ (List.mem_singleton_self _)

/-- `T`'s slots as the named ones. -/
theorem JacWinLay.TS_eq (hL : JacWinLay K size) :
    TS K 0 = K.E.x ∧ TS K 1 = K.E.y ∧ TS K 2 = K.E.z ∧ TS K 3 = K.z2 ∧ TS K 4 = K.z2 + 8 * K.M.n :=
  ⟨hL.Tx.symm, hL.Ty.symm, hL.Tz.symm, hL.Tz2.symm, hL.Tz3.symm⟩

/-- `ZF` for `rbx = i`. -/
theorem cmpRbxJ_ok (s : State) {j i : Nat} (hi : i < 2 ^ 31) (hj : j < 2 ^ 63)
    (hb : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block [.alu .cmp .rbx (.imm (BitVec.ofNat 32 i))]) s fun t =>
      t.zf = some (decide (j = i)) ∧ Keeps [] s t := by
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

/-- `rbx = j + c`. -/
theorem addRbx_ok (s : State) {j c : Nat} (hc : c < 2 ^ 31) (hb : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block [.alu .add .rbx (.imm (BitVec.ofNat 32 c))]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 (j + c) ∧ Keeps [.rbx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left', hb, imm32_sext hc]
  refine ⟨by rw [← BitVec.ofNat_add], fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem keepRegs_of_keeps {rs rs' : List Reg} {s s' : State} (h : Keeps rs s s')
    (hr : ∀ r ∈ rs, r ∈ rs') : KeepRegs rs' s s' := (Keeps.regs h).mono hr

end VG.Proof.Weierstrass.X86_64
