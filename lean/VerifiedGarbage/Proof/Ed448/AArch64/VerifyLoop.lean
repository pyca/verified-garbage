import VerifiedGarbage.Proof.Ed448.AArch64.BaseStep
import VerifiedGarbage.Proof.Ed448.VerifyFormulas
import VerifiedGarbage.Impl.Ed448.AArch64.VerifyEquation

/-!
# Ed448 verification's equation on AArch64: `[S]B + [k](-A)`

One iteration of `vloop` (`vstep_ok`), for the bits `t` of `S` (at `BITS`)
and of `k` (at `2 KOFF`): `Q` doubled, then `B` (slots 8–10) added and
swapped in by the first bit, and `-A` (slots 6, 7 and 10) by the second. The
loop's invariant (`VInv`): `Q` is the reference ladder's point after the bits
above `n` (`Proof.Ed448.vladder`).
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keep Keeps off contains_sc read1_eq Outside2 workRegs)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv cswapE opSwap decCounter_ok setCounter_ok)
open VG.Proof.Curve448.AArch64 (mask)
open VG.Impl.X448.AArch64 (BITS ACC slot)

/-- `x6` := the mask of the bit at `x3 + x19 + d1 + d2`. -/
theorem maskAt_ok {s : State} {base : Addr} (hs : Scr s base) {d1 d2 t : Nat} (hd1 : d1 < 4096)
    (hd2 : d2 < 4096) (hd : d1 + d2 + t < 8192)
    (hc : s.gpr .x19 = BitVec.ofNat 64 t) {b : Nat} (hb2 : b < 2)
    (hbit : s.mem (off base (d1 + d2 + t)) = BitVec.ofNat 8 b) :
    WP isa (.block (maskAt d1 d2)) s fun s' =>
      s'.gpr .x6 = mask (decide (b = 1)) ∧ (∀ r, r ∉ [Reg.x4, .x6, .x11] → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : InRegions (s.rd ++ s.wr) (off base (d1 + d2 + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by omega)⟩
  have enc : d2 % 1 = 0 ∧ d2 < 4096 * 1 := ⟨Nat.mod_one _, by omega⟩
  have ea : base + BitVec.ofNat 64 t + BitVec.ofNat 64 d1 + BitVec.ofNat 64 d2 = off base (d1 + d2 + t) := by
    rw [Offset.add_add, Offset.add_add]; congr 2; omega
  apply WP.of_runBlock
  simp only [maskAt, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Size.bits, Nat.reduceLT, Nat.reduceMul, BitVec.shiftLeft_zero, hd1,
    BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.mem_write, hc, hs.x3, addr, enc, and_self, ea, State.load,
    hin, read1_eq, hbit, Option.bind_some, Option.map_some, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  have ext : (BitVec.setWidth 32 (BitVec.ofNat 8 b)).setWidth 64 = (BitVec.ofNat 8 b).setWidth 64 := by
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> rfl
  have e0 : BitVec.setWidth 64 (0 : BitVec 16) = 0 := rfl
  simp only [ext, e0]
  refine ⟨mask_bit b hb2, fun r hr => ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2, ite_false]

/-- The slots after a swap of `T` into `Q`. -/
def swapEnv (sw : Bool) (e : Fin 22 → Spec.X448.Fe) : Fin 22 → Spec.X448.Fe :=
  opSwap 2 5 sw (opSwap 1 4 sw (opSwap 0 3 sw e))

/-- The slots after an iteration, for the bits `sw₁` (of `S`) and `sw₂` (of `k`). -/
def vstepEnv (sw₁ sw₂ : Bool) (e : Fin 22 → Spec.X448.Fe) : Fin 22 → Spec.X448.Fe :=
  swapEnv sw₂ (evalOps (addAt 6 7) (swapEnv sw₁ (evalOps (addAt 8 9) (evalOps (doubleAt 0 1 2) e))))

theorem pt_swap (sw : Bool) (e : Fin 22 → Spec.X448.Fe) :
    pt (swapEnv sw e) 0 1 2 = if sw then pt e 3 4 5 else pt e 0 1 2 := by
  cases sw <;> rfl

theorem swapEnv_keep (sw : Bool) (e : Fin 22 → Spec.X448.Fe) (i : Fin 22) (hi : 6 ≤ i.val) :
    swapEnv sw e i = e i := by
  have h0 : i ≠ 0 := fun h => by rw [h] at hi; exact absurd hi (by decide)
  have h1 : i ≠ 1 := fun h => by rw [h] at hi; exact absurd hi (by decide)
  have h2 : i ≠ 2 := fun h => by rw [h] at hi; exact absurd hi (by decide)
  have h3 : i ≠ 3 := fun h => by rw [h] at hi; exact absurd hi (by decide)
  have h4 : i ≠ 4 := fun h => by rw [h] at hi; exact absurd hi (by decide)
  have h5 : i ≠ 5 := fun h => by rw [h] at hi; exact absurd hi (by decide)
  simp only [swapEnv, opSwap, Function.update_of_ne h0, Function.update_of_ne h1, Function.update_of_ne h2,
    Function.update_of_ne h3, Function.update_of_ne h4, Function.update_of_ne h5]

theorem pt_congr {e e' : Fin 22 → Spec.X448.Fe} {a b c : Fin 22} (ha : e' a = e a) (hb : e' b = e b)
    (hc : e' c = e c) : pt e' a b c = pt e a b c := by
  simp only [pt, ha, hb, hc]

theorem vstepEnv_keep (sw₁ sw₂ : Bool) (e : Fin 22 → Spec.X448.Fe) (i : Fin 22) (hi : 6 ≤ i.val ∧ i.val < 12) :
    vstepEnv sw₁ sw₂ e i = e i := by
  rw [vstepEnv, swapEnv_keep _ _ _ hi.1, addAt_keep _ _ _ _ (Or.inr (Or.inl hi)), swapEnv_keep _ _ _ hi.1,
    addAt_keep _ _ _ _ (Or.inr (Or.inl hi)), doubleAt_keep0 _ _ (Or.inl ⟨by omega, hi.2⟩)]

theorem vstepEnv_pt (sw₁ sw₂ : Bool) (e : Fin 22 → Spec.X448.Fe) :
    pt (vstepEnv sw₁ sw₂ e) 0 1 2 =
      let r₁ := double (pt e 0 1 2)
      let r₂ := if sw₁ then addWith (e 11) r₁ (pt e 8 9 10) else r₁
      if sw₂ then addWith (e 11) r₂ (pt e 6 7 10) else r₂ := by
  unfold vstepEnv
  generalize he0 : evalOps (doubleAt 0 1 2) e = e0
  have p0 : pt e0 0 1 2 = double (pt e 0 1 2) := by rw [← he0, doubleAt_eval0]
  have k0 : ∀ i : Fin 22, 3 ≤ i.val ∧ i.val < 12 → e0 i = e i := fun i hi => by
    rw [← he0, doubleAt_keep0 _ _ (Or.inl hi)]
  generalize he1 : evalOps (addAt 8 9) e0 = e1
  have p1 : pt e1 3 4 5 = addWith (e0 11) (pt e0 0 1 2) (pt e0 8 9 10) := by rw [← he1, addAt_eval8]
  have q1 : pt e1 0 1 2 = pt e0 0 1 2 :=
    pt_congr (by rw [← he1, addAt_keep _ _ _ _ (Or.inl (by decide))])
      (by rw [← he1, addAt_keep _ _ _ _ (Or.inl (by decide))]) (by rw [← he1, addAt_keep _ _ _ _ (Or.inl (by decide))])
  have k1 : ∀ i : Fin 22, 6 ≤ i.val ∧ i.val < 12 → e1 i = e0 i := fun i hi => by
    rw [← he1, addAt_keep _ _ _ _ (Or.inr (Or.inl hi))]
  generalize he2 : swapEnv sw₁ e1 = e2
  have p2 : pt e2 0 1 2 = if sw₁ then pt e1 3 4 5 else pt e1 0 1 2 := by rw [← he2, pt_swap]
  have k2 : ∀ i : Fin 22, 6 ≤ i.val → e2 i = e1 i := fun i hi => by rw [← he2, swapEnv_keep _ _ _ hi]
  generalize he3 : evalOps (addAt 6 7) e2 = e3
  have p3 : pt e3 3 4 5 = addWith (e2 11) (pt e2 0 1 2) (pt e2 6 7 10) := by rw [← he3, addAt_eval6]
  have q3 : pt e3 0 1 2 = pt e2 0 1 2 :=
    pt_congr (by rw [← he3, addAt_keep _ _ _ _ (Or.inl (by decide))])
      (by rw [← he3, addAt_keep _ _ _ _ (Or.inl (by decide))]) (by rw [← he3, addAt_keep _ _ _ _ (Or.inl (by decide))])
  have e11 : e2 11 = e 11 := by rw [k2 11 (by decide), k1 11 (by decide), k0 11 (by decide)]
  have e11' : e0 11 = e 11 := k0 11 (by decide)
  have b8 : pt e0 8 9 10 = pt e 8 9 10 :=
    pt_congr (k0 8 (by decide)) (k0 9 (by decide)) (k0 10 (by decide))
  have a6 : pt e2 6 7 10 = pt e 6 7 10 :=
    pt_congr (by rw [k2 6 (by decide), k1 6 (by decide), k0 6 (by decide)])
      (by rw [k2 7 (by decide), k1 7 (by decide), k0 7 (by decide)])
      (by rw [k2 10 (by decide), k1 10 (by decide), k0 10 (by decide)])
  rw [pt_swap, p3, q3, p2, p1, q1, e11, e11', b8, a6, p0]

/-- `T` swapped into `Q` by the mask `x6`. -/
theorem swapT_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) {sw : Bool}
    (hc : s.gpr .x6 = mask sw) :
    WP isa (.block swapT) s fun s' => Keep base s s' ∧ BoundedEnv s'.mem base ∧
      E s'.mem base = swapEnv sw (E s.mem base) := by
  rw [swapT, List.append_assoc]
  exact swaps_ok hs hb hc

/-- One bit of both scalars: the reference ladder's point after the bits above
`t`, then after bit `t`. -/
theorem vladder_step {e : Fin 22 → Spec.X448.Fe} {S K t : Nat} {A : Spec.Ed448.Point} (ht : t < 456)
    (hr : pt e 0 1 2 = vladder S K A (456 - (t + 1)))
    (hq : pt e 8 9 10 = Spec.Ed448.basePoint) (ha : pt e 6 7 10 = A) (hd : e 11 = Spec.Ed448.d) :
    pt (vstepEnv (decide ((S >>> t) &&& 1 = 1)) (decide ((K >>> t) &&& 1 = 1)) e) 0 1 2 =
      vladder S K A (456 - t) := by
  rw [vstepEnv_pt, hd, hq, ha, hr, vladder_bit S K A ht]
  simp only [addWith_d]
  rfl

/-- An iteration, for the bits `t` of `S` (`b₁`) and of `k` (`b₂`). -/
theorem vstep_ok {s : State} {base : Addr} (hs : Scr s base) (hbd : BoundedEnv s.mem base) {t : Nat}
    (ht : t < 456) (hc : s.gpr .x19 = BitVec.ofNat 64 (t + 1)) {b₁ b₂ : Nat} (hb₁ : b₁ < 2) (hb₂ : b₂ < 2)
    (hbit₁ : s.mem (off base (0 + BITS + t)) = BitVec.ofNat 8 b₁)
    (hbit₂ : s.mem (off base (KOFF + KOFF + t)) = BitVec.ofNat 8 b₂) :
    WP isa vstep s fun s' =>
      s'.gpr .x19 = BitVec.ofNat 64 t ∧ (s'.gpr .x19 == 0) = decide (t = 0) ∧
      Keeps (.x19 :: workRegs) s s' ∧ BoundedEnv s'.mem base ∧
      Outside2 base 64 2816 ACC 512 s.mem s'.mem ∧
      E s'.mem base = vstepEnv (decide (b₁ = 1)) (decide (b₂ = 1)) (E s.mem base) := by
  have hout : ∀ d, (3072 ≤ d ∧ d < 3584 ∨ 4096 ≤ d) → d < 8192 → ∀ {m m' : Mem},
      Outside2 base 64 2816 ACC 512 m m' → m' (off base d) = m (off base d) := by
    intro d hd1 hd2 m m' h
    have hofs : VG.Proof.X448.AArch64.ofs base (off base d) = d := Mem.sub_ofNat_toNat base (by omega)
    exact h _ (by rw [hofs]; omega) (by rw [hofs]; simp only [ACC]; omega)
  rw [vstep, WP.seq_iff]
  refine WP.mono (decCounter_ok (by omega) hc) fun s1 ⟨c1, g1, m1, rd1, wr1, z1⟩ => ?_
  have hs1 : Scr s1 base :=
    ⟨(g1 _ (by decide)).trans hs.x3, (g1 _ (by decide)).trans hs.mask, wr1 ▸ hs.wr, hs.nowrap⟩
  have hb1 : BoundedEnv s1.mem base := m1 ▸ hbd
  rw [WP.seq_iff]
  refine WP.mono (field_ok _ (by decide) hs1 hb1) fun s2 ⟨k2, b2, e2⟩ => ?_
  have hs2 := k2.scr hs1
  rw [WP.seq_iff]
  refine WP.mono (field_ok _ (by decide) hs2 b2) fun s3 ⟨k3, b3, e3⟩ => ?_
  have hs3 := k3.scr hs2
  have k13 := k2.trans k3
  have c3 : s3.gpr .x19 = BitVec.ofNat 64 t := (k13.regs.1 _ (by decide)).trans c1
  have hbit3 : s3.mem (off base (0 + BITS + t)) = BitVec.ofNat 8 b₁ := by
    rw [hout _ (by simp only [BITS]; omega) (by simp only [BITS]; omega) k13.mem, m1]; exact hbit₁
  rw [WP.seq_iff, WP.block_append_iff]
  refine WP.mono (maskAt_ok hs3 (by decide) (by decide) (by simp only [BITS]; omega) c3 hb₁ hbit3)
    fun s4 ⟨x4, g4, m4, rd4, wr4⟩ => ?_
  have hs4 : Scr s4 base :=
    ⟨(g4 _ (by decide)).trans hs3.x3, (g4 _ (by decide)).trans hs3.mask, wr4 ▸ hs3.wr, hs3.nowrap⟩
  have b4 : BoundedEnv s4.mem base := m4 ▸ b3
  refine WP.mono (swapT_ok hs4 b4 x4) fun s5 ⟨k5, b5, e5⟩ => ?_
  have hs5 := k5.scr hs4
  rw [WP.seq_iff]
  refine WP.mono (field_ok _ (by decide) hs5 b5) fun s6 ⟨k6, b6, e6⟩ => ?_
  have hs6 := k6.scr hs5
  have c6 : s6.gpr .x19 = BitVec.ofNat 64 t := by
    rw [k6.regs.1 _ (by decide), k5.regs.1 _ (by decide), g4 _ (by decide)]; exact c3
  have hbit6 : s6.mem (off base (KOFF + KOFF + t)) = BitVec.ofNat 8 b₂ := by
    have h1 : 3072 ≤ KOFF + KOFF + t ∧ KOFF + KOFF + t < 3584 ∨ 4096 ≤ KOFF + KOFF + t := by
      simp only [KOFF]; omega
    have h2 : KOFF + KOFF + t < 8192 := by simp only [KOFF]; omega
    rw [hout _ h1 h2 k6.mem, hout _ h1 h2 k5.mem, m4, hout _ h1 h2 k13.mem, m1]; exact hbit₂
  rw [WP.block_append_iff]
  refine WP.mono (maskAt_ok hs6 (by decide) (by decide) (by simp only [KOFF]; omega) c6 hb₂ hbit6)
    fun s7 ⟨x7, g7, m7, rd7, wr7⟩ => ?_
  have hs7 : Scr s7 base :=
    ⟨(g7 _ (by decide)).trans hs6.x3, (g7 _ (by decide)).trans hs6.mask, wr7 ▸ hs6.wr, hs6.nowrap⟩
  have b7 : BoundedEnv s7.mem base := m7 ▸ b6
  refine WP.mono (swapT_ok hs7 b7 x7) fun s' ⟨k', b', e'⟩ => ?_
  have g' : s'.gpr .x19 = BitVec.ofNat 64 t := by
    rw [k'.regs.1 _ (by decide), g7 _ (by decide)]; exact c6
  refine ⟨g', by rw [g', ← c1]; exact z1, ?_, b', ?_, ?_⟩
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · have hw : r ∉ workRegs := fun h => hr (List.mem_cons_of_mem _ h)
      have h3 : r ∉ [Reg.x4, .x6, .x11] := fun h => hw (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl <;> decide)
      rw [k'.regs.1 r hw, g7 r h3, k6.regs.1 r hw, k5.regs.1 r hw, g4 r h3, k13.regs.1 r hw,
        g1 r (fun h => hr (h ▸ List.mem_cons_self))]
    · rw [k'.regs.2.1, rd7, k6.regs.2.1, k5.regs.2.1, rd4, k13.regs.2.1, rd1]
    · rw [k'.regs.2.2, wr7, k6.regs.2.2, k5.regs.2.2, wr4, k13.regs.2.2, wr1]
  · have q1 := k13.mem
    have q5 := k5.mem
    have q' := k'.mem
    rw [m1] at q1
    rw [m4] at q5
    rw [m7] at q'
    exact q1.trans (q5.trans (k6.mem.trans q'))
  · rw [e', m7, e6, e5, m4, e3, e2, m1]
    rfl

/-- The loop's invariant, after the bits above `n` of `S` and `k`. -/
structure VInv (base : Addr) (S K : Nat) (A : Spec.Ed448.Point) (s₀ : State) (n : Nat) (s : State) : Prop where
  scr : Scr s base
  bounded : BoundedEnv s.mem base
  x19 : s.gpr .x19 = BitVec.ofNat 64 n
  regs : Keeps (.x19 :: workRegs) s₀ s
  mem : Outside2 base 64 2816 ACC 512 s₀.mem s.mem
  q : pt (E s.mem base) 8 9 10 = Spec.Ed448.basePoint
  na : pt (E s.mem base) 6 7 10 = A
  d : E s.mem base 11 = Spec.Ed448.d
  rep : pt (E s.mem base) 0 1 2 = vladder S K A (456 - n)

theorem vloop_loop_ok {s₀ : State} {base : Addr} {S K : Nat} {A : Spec.Ed448.Point}
    (hbs : ∀ t < 456, s₀.mem (off base (0 + BITS + t)) = BitVec.ofNat 8 ((S >>> t) &&& 1))
    (hbk : ∀ t < 456, s₀.mem (off base (KOFF + KOFF + t)) = BitVec.ofNat 8 ((K >>> t) &&& 1)) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 456 → VInv base S K A s₀ n s →
      WP isa (.loop vstep (.nonzero .x .x19)) s fun s' => VInv base S K A s₀ 0 s' := by
  intro n s hn1 hn2 hi
  refine WP.loop (M := isa) (body := vstep) (c := .nonzero .x .x19)
    (Q := fun s' => VInv base S K A s₀ 0 s')
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 456 ∧ VInv base S K A s₀ m s) ?_ n s ⟨hn1, hn2, hi⟩
  rintro m s ⟨hm1, hm2, hi⟩
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  have hb1 : (S >>> t) &&& 1 < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hb2 : (K >>> t) &&& 1 < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hout : ∀ d, (3072 ≤ d ∧ d < 3584 ∨ 4096 ≤ d) → d < 8192 →
      s.mem (off base d) = s₀.mem (off base d) := by
    intro d hd1 hd2
    have hofs : VG.Proof.X448.AArch64.ofs base (off base d) = d := Mem.sub_ofNat_toNat base (by omega)
    exact hi.mem _ (by rw [hofs]; omega) (by rw [hofs]; simp only [ACC]; omega)
  have hbit1 : s.mem (off base (0 + BITS + t)) = BitVec.ofNat 8 ((S >>> t) &&& 1) := by
    rw [hout _ (by simp only [BITS]; omega) (by simp only [BITS]; omega)]
    exact hbs t (by omega)
  have hbit2 : s.mem (off base (KOFF + KOFF + t)) = BitVec.ofNat 8 ((K >>> t) &&& 1) := by
    rw [hout _ (by simp only [KOFF]; omega) (by simp only [KOFF]; omega)]
    exact hbk t (by omega)
  refine WP.mono (vstep_ok hi.scr hi.bounded (by omega) hi.x19 hb1 hb2 hbit1 hbit2)
    fun s' ⟨c', z', k', b', o', e'⟩ => ?_
  have kk : ∀ i : Fin 22, 6 ≤ i.val ∧ i.val < 12 → E s'.mem base i = E s.mem base i := fun i hi => by
    rw [e', vstepEnv_keep _ _ _ _ hi]
  have inv : VInv base S K A s₀ t s' := by
    refine ⟨hi.scr.of_keeps k' (by decide), b', c', hi.regs.trans k', hi.mem.trans o', ?_, ?_, ?_, ?_⟩
    · rw [pt_congr (kk 8 (by decide)) (kk 9 (by decide)) (kk 10 (by decide))]; exact hi.q
    · rw [pt_congr (kk 6 (by decide)) (kk 7 (by decide)) (kk 10 (by decide))]; exact hi.na
    · rw [kk 11 (by decide)]; exact hi.d
    · rw [e']; exact vladder_step (by omega) hi.rep hi.q hi.na hi.d
  simp only [eval, State.read, BitVec.setWidth_eq, bne, z']
  rcases Nat.eq_zero_or_pos t with h | h
  · subst h
    exact .inl ⟨rfl, inv⟩
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬t = 0), Bool.not_false], t, by omega,
      h, by omega, inv⟩

/-- The counter set to 456, then the loop. -/
theorem vloop_ok {s : State} {base : Addr} {S K : Nat} {A : Spec.Ed448.Point}
    (hbs : ∀ t < 456, s.mem (off base (0 + BITS + t)) = BitVec.ofNat 8 ((S >>> t) &&& 1))
    (hbk : ∀ t < 456, s.mem (off base (KOFF + KOFF + t)) = BitVec.ofNat 8 ((K >>> t) &&& 1))
    (hs : Scr s base) (hb : BoundedEnv s.mem base) (hq : pt (E s.mem base) 8 9 10 = Spec.Ed448.basePoint)
    (ha : pt (E s.mem base) 6 7 10 = A) (hd : E s.mem base 11 = Spec.Ed448.d)
    (hr : pt (E s.mem base) 0 1 2 = Spec.Ed448.identity) :
    WP isa vloop s fun s' => VInv base S K A s 0 s' := by
  rw [vloop, WP.seq_iff]
  refine WP.mono (setCounter_ok s 456 (by decide)) fun s₁ ⟨c₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  refine vloop_loop_ok (s₀ := s) hbs hbk 456 s₁ (by decide) (by decide)
    ⟨?_, m₁ ▸ hb, c₁, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨(g₁ _ (by decide)).trans hs.x3, (g₁ _ (by decide)).trans hs.mask, wr₁ ▸ hs.wr, hs.nowrap⟩
  · exact ⟨fun r hr => g₁ r (fun h => hr (h ▸ List.mem_cons_self)), rd₁, wr₁⟩
  · rw [m₁]; exact Outside2.refl _ _ _ _ _ _
  · rw [m₁]; exact hq
  · rw [m₁]; exact ha
  · rw [m₁]; exact hd
  · rw [m₁, Nat.sub_self]; exact hr

end VG.Proof.Ed448.AArch64
