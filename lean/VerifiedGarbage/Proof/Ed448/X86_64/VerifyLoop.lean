import VerifiedGarbage.Proof.Ed448.VerifyFormulas
import VerifiedGarbage.Proof.Ed448.X86_64.BaseField
import VerifiedGarbage.Impl.Ed448.X86_64.VerifyEquation
import VerifiedGarbage.Proof.Ed448.X86_64.BaseConst

/-!
# Ed448 verification's equation on x86-64: `[S]B + [k](-A)`

One iteration of `vloop` (`vstep_ok`), for the bits `t` of `S` (at `BITS`)
and of `k` (at `KBITS`), with any point operations that run the field
programs (`PointOk`): `Q` doubled, then `B` (slots 8–10) added and swapped in
by the first bit, and `-A` (slots 6, 7 and 10, copied into slots 8–9) by the
second, and `B` written back into slots 8–9. The loop's invariant (`VInv`):
`Q` is the reference ladder's point after the bits above `n`
(`Proof.Ed448.vladder`).
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64 VG.Proof.Ed448
open VG.Proof.X448.X86_64 (Scr Index Env E Keep FieldOk off contains_sc mask cswapE opSwap clob Outside
  copyOut_ok E_outside)
open VG.Impl.X448.X86_64 (BITS slot cswap copyOut W)

theorem ea_bitsAt {s : State} {base : Addr} (hr : s.gpr .rdi = base) {t : Nat}
    (hb : s.gpr .rbx = BitVec.ofNat 64 t) (o : Nat) :
    s.ea { base := .rdi, index := some .rbx, disp := (o : Int) } = off base (o + t) := by
  simp only [State.ea, hr, hb, off, BitVec.ofInt_natCast]
  rw [BitVec.mul_one, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm t o]

theorem maskAt_ok {s : State} {base : Addr} (hs : Scr s base) {o t : Nat} (ho : o + t < 8192)
    (hb : s.gpr .rbx = BitVec.ofNat 64 t) {b : Nat} (hb2 : b < 2)
    (hbit : s.mem (off base (o + t)) = BitVec.ofNat 8 b) :
    WP isa (.block (maskAt o)) s fun s' =>
      s'.gpr .rcx = mask (decide (b = 1)) ∧ (∀ r, r ∉ [Reg.rdx, .rcx] → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : InRegions (s.rd ++ s.wr) (off base (o + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by omega)⟩
  apply WP.of_runBlock
  simp only [maskAt, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
    State.load8, ea_bitsAt hs.rdi hb, hin, hbit, ite_true, State.setReg32, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, ite_false,
    reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨mask_bit b hb2, fun r hr => ?_, trivial, trivial, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2, ite_false]

/-- The slots after a swap of `T` into `Q`. -/
def swapEnv (sw : Bool) (e : Env) : Env := opSwap 2 5 sw (opSwap 1 4 sw (opSwap 0 3 sw e))

/-- The slots after `-A` is copied into slots 8–9. -/
def stageEnv (e : Env) : Env := Function.update (Function.update e 8 (e 6)) 9 (e 7)

/-- The slots after `B` is written back into slots 8–9. -/
def restoreEnv (e : Env) : Env :=
  Function.update (Function.update e 8 Spec.Ed448.basePoint.X) 9 Spec.Ed448.basePoint.Y

/-- The slots after an iteration, for the bits `sw₁` (of `S`) and `sw₂` (of `k`). -/
def vstepEnv (sw₁ sw₂ : Bool) (e : Env) : Env :=
  restoreEnv (swapEnv sw₂ (evalOps addAffineOps (stageEnv (swapEnv sw₁ (evalOps addAffineOps
    (evalOps doubleOps e))))))

theorem pt_swap (sw : Bool) (e : Env) :
    pt (swapEnv sw e) 0 1 2 = if sw then pt e 3 4 5 else pt e 0 1 2 := by
  cases sw <;> rfl

theorem pt_congr {e e' : Env} {a b c : Index} (ha : e' a = e a) (hb : e' b = e b) (hc : e' c = e c) :
    pt e' a b c = pt e a b c := by
  simp only [pt, ha, hb, hc]

theorem swapEnv_keep (sw : Bool) (e : Env) (i : Index) (hi : 6 ≤ i.val) : swapEnv sw e i = e i := by
  have h0 : i ≠ 0 := fun h => by rw [h] at hi; exact absurd hi (by decide)
  have h1 : i ≠ 1 := fun h => by rw [h] at hi; exact absurd hi (by decide)
  have h2 : i ≠ 2 := fun h => by rw [h] at hi; exact absurd hi (by decide)
  have h3 : i ≠ 3 := fun h => by rw [h] at hi; exact absurd hi (by decide)
  have h4 : i ≠ 4 := fun h => by rw [h] at hi; exact absurd hi (by decide)
  have h5 : i ≠ 5 := fun h => by rw [h] at hi; exact absurd hi (by decide)
  simp only [swapEnv, opSwap, Function.update_of_ne h0, Function.update_of_ne h1, Function.update_of_ne h2,
    Function.update_of_ne h3, Function.update_of_ne h4, Function.update_of_ne h5]

theorem stageEnv_keep (e : Env) (i : Index) (h8 : i ≠ 8) (h9 : i ≠ 9) : stageEnv e i = e i := by
  rw [stageEnv, Function.update_of_ne h9, Function.update_of_ne h8]

theorem restoreEnv_keep (e : Env) (i : Index) (h8 : i ≠ 8) (h9 : i ≠ 9) : restoreEnv e i = e i := by
  rw [restoreEnv, Function.update_of_ne h9, Function.update_of_ne h8]

/-- What an iteration keeps: slots 6, 7, 10 and 11, and `B`'s coordinates in slots 8–9. -/
theorem vstepEnv_keep (sw₁ sw₂ : Bool) (e : Env) :
    vstepEnv sw₁ sw₂ e 6 = e 6 ∧ vstepEnv sw₁ sw₂ e 7 = e 7 ∧ vstepEnv sw₁ sw₂ e 10 = e 10 ∧
      vstepEnv sw₁ sw₂ e 11 = e 11 ∧ vstepEnv sw₁ sw₂ e 8 = Spec.Ed448.basePoint.X ∧
      vstepEnv sw₁ sw₂ e 9 = Spec.Ed448.basePoint.Y := by
  have k : ∀ i : Index, (i = 6 ∨ i = 7 ∨ i = 10 ∨ i = 11) → vstepEnv sw₁ sw₂ e i = e i := by
    intro i hi
    have hv : 6 ≤ i.val ∧ i.val < 12 ∧ i ≠ 8 ∧ i ≠ 9 := by rcases hi with rfl | rfl | rfl | rfl <;> decide
    rw [vstepEnv, restoreEnv_keep _ _ hv.2.2.1 hv.2.2.2, swapEnv_keep _ _ _ hv.1,
      Point64.addAffineOps_keep _ _ (Or.inr (Or.inl ⟨hv.1, by omega⟩)), stageEnv_keep _ _ hv.2.2.1 hv.2.2.2,
      swapEnv_keep _ _ _ hv.1, Point64.addAffineOps_keep _ _ (Or.inr (Or.inl ⟨hv.1, by omega⟩)),
      doubleOps_keep _ _ (Or.inl ⟨by omega, hv.2.1⟩)]
  exact ⟨k 6 (by decide), k 7 (by decide), k 10 (by decide), k 11 (by decide), rfl, rfl⟩

theorem vstepEnv_pt (sw₁ sw₂ : Bool) (e : Env) :
    pt (vstepEnv sw₁ sw₂ e) 0 1 2 =
      let r₁ := Proof.Ed448.double (pt e 0 1 2)
      let r₂ := if sw₁ then Point64.addAffineWith (e 11) r₁ (e 8) (e 9) else r₁
      if sw₂ then Point64.addAffineWith (e 11) r₂ (e 6) (e 7) else r₂ := by
  unfold vstepEnv
  generalize he0 : evalOps doubleOps e = e0
  have p0 : pt e0 0 1 2 = Proof.Ed448.double (pt e 0 1 2) := by rw [← he0]; exact doubleOps_eval e
  have k0 : ∀ i : Index, 3 ≤ i.val ∧ i.val < 12 → e0 i = e i := fun i hi => by
    rw [← he0, doubleOps_keep _ _ (Or.inl hi)]
  generalize he1 : evalOps addAffineOps e0 = e1
  have p1 : pt e1 3 4 5 = Point64.addAffineWith (e0 11) (pt e0 0 1 2) (e0 8) (e0 9) := by
    rw [← he1, Point64.addAffineOps_eval, Point64.addWith_affine]
  have q1 : pt e1 0 1 2 = pt e0 0 1 2 :=
    pt_congr (by rw [← he1, Point64.addAffineOps_keep _ _ (Or.inl (by decide))])
      (by rw [← he1, Point64.addAffineOps_keep _ _ (Or.inl (by decide))])
      (by rw [← he1, Point64.addAffineOps_keep _ _ (Or.inl (by decide))])
  have k1 : ∀ i : Index, 6 ≤ i.val ∧ i.val < 12 → e1 i = e0 i := fun i hi => by
    rw [← he1, Point64.addAffineOps_keep _ _ (Or.inr (Or.inl ⟨hi.1, by omega⟩))]
  generalize he2 : stageEnv (swapEnv sw₁ e1) = e2
  have p2 : pt e2 0 1 2 = if sw₁ then pt e1 3 4 5 else pt e1 0 1 2 := by
    rw [← he2, pt_congr (stageEnv_keep _ 0 (by decide) (by decide)) (stageEnv_keep _ 1 (by decide) (by decide))
      (stageEnv_keep _ 2 (by decide) (by decide)), pt_swap]
  have k2 : ∀ i : Index, 6 ≤ i.val → i ≠ 8 → i ≠ 9 → e2 i = e1 i := fun i hi h8 h9 => by
    rw [← he2, stageEnv_keep _ _ h8 h9, swapEnv_keep _ _ _ hi]
  have e28 : e2 8 = e1 6 := by rw [← he2, stageEnv, Function.update_of_ne (by decide), Function.update_self,
    swapEnv_keep _ _ _ (by decide)]
  have e29 : e2 9 = e1 7 := by rw [← he2, stageEnv, Function.update_self, swapEnv_keep _ _ _ (by decide)]
  generalize he3 : evalOps addAffineOps e2 = e3
  have p3 : pt e3 3 4 5 = Point64.addAffineWith (e2 11) (pt e2 0 1 2) (e2 8) (e2 9) := by
    rw [← he3, Point64.addAffineOps_eval, Point64.addWith_affine]
  have q3 : pt e3 0 1 2 = pt e2 0 1 2 :=
    pt_congr (by rw [← he3, Point64.addAffineOps_keep _ _ (Or.inl (by decide))])
      (by rw [← he3, Point64.addAffineOps_keep _ _ (Or.inl (by decide))])
      (by rw [← he3, Point64.addAffineOps_keep _ _ (Or.inl (by decide))])
  have r : pt (restoreEnv (swapEnv sw₂ e3)) 0 1 2 = pt (swapEnv sw₂ e3) 0 1 2 :=
    pt_congr (restoreEnv_keep _ 0 (by decide) (by decide)) (restoreEnv_keep _ 1 (by decide) (by decide))
      (restoreEnv_keep _ 2 (by decide) (by decide))
  have e11 : e2 11 = e 11 := by
    rw [k2 11 (by decide) (by decide) (by decide), k1 11 (by decide), k0 11 (by decide)]
  have e11' : e0 11 = e 11 := k0 11 (by decide)
  rw [r, pt_swap, p3, q3, p2, p1, q1, e11, e11', e28, e29, k1 6 (by decide), k1 7 (by decide),
    k0 6 (by decide), k0 7 (by decide), k0 8 (by decide), k0 9 (by decide), p0]

variable {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld)

/-- `T` swapped into `Q` by the mask `rcx`. -/
theorem swapT_ok {s : State} {base : Addr} (hs : Scr s base) {sw : Bool} (hc : s.gpr .rcx = mask sw) :
    WP isa (.block swapT) s fun s' => Keep base s s' ∧ E s'.mem base = swapEnv sw (E s.mem base) := by
  rw [swapT, List.append_assoc, WP.block_append_iff]
  refine WP.mono (cswapE hs 0 3 (by decide) hc) fun s5 ⟨k5, c5, e5⟩ => ?_
  have hs5 := k5.scr hs
  rw [WP.block_append_iff]
  refine WP.mono (cswapE hs5 1 4 (by decide) (c5.trans hc)) fun s6 ⟨k6, c6, e6⟩ => ?_
  have hs6 := k6.scr hs5
  refine WP.mono (cswapE hs6 2 5 (by decide) (c6.trans (c5.trans hc))) fun s7 ⟨k7, _, e7⟩ => ?_
  exact ⟨(k5.trans k6).trans k7, by rw [e7, e6, e5]; rfl⟩

/-- Slot `j` copied into slot `i`. -/
theorem copySlot_ok {s : State} {base : Addr} (hs : Scr s base) (i j : Index) :
    WP isa (.block (copyOut (slot i.val) (slot j.val))) s fun t =>
      Keep base s t ∧ E t.mem base = Function.update (E s.mem base) i (E s.mem base j) := by
  have hW : ∀ x ∈ W, x ∈ clob := by decide
  have hi := Proof.X448.X86_64.slot_lt i
  have hj := Proof.X448.X86_64.slot_lt j
  have gi := Proof.X448.X86_64.slot_ge i
  simp only [Impl.X448.X86_64.ACC] at hi hj
  refine WP.mono (copyOut_ok hs (by omega) (by omega)) fun t ⟨ft, ot, gt, rdt, wrt⟩ =>
    ⟨⟨fun r hr => gt r (fun h => hr (hW r h)), rdt, wrt,
      ot.mono (by omega) (by omega)⟩, ?_⟩
  funext k
  by_cases hk : k = i
  · subst hk
    rw [Function.update_self]
    show VG.Proof.X448.toFe (Proof.X448.X86_64.fe t.mem base (slot k.val)) =
      VG.Proof.X448.toFe (Proof.X448.X86_64.fe s.mem base (slot j.val))
    rw [ft]
  · rw [Function.update_of_ne hk]
    exact E_outside ot k (Proof.X448.X86_64.slot_sep hk)

/-- A constant into slot `i`. -/
theorem constE_ok {s : State} {base : Addr} (hs : Scr s base) (i : Index) (v : Spec.X448.Fe)
    (hv : VG.Proof.X448.toFe (Proof.X448.X86_64.wv (words7 v.val)) = v) :
    WP isa (.block (constSlot i.val v)) s fun t =>
      Keep base s t ∧ E t.mem base = Function.update (E s.mem base) i v := by
  have hW : ∀ x ∈ W, x ∈ clob := by decide
  have hi := Proof.X448.X86_64.slot_lt i
  have gi := Proof.X448.X86_64.slot_ge i
  simp only [Impl.X448.X86_64.ACC] at hi
  exact WP.mono (constSlot_ok hs i v hv) fun t ⟨et, ot, gt, rdt, wrt⟩ =>
    ⟨⟨fun r hr => gt r (fun h => hr (hW r h)), rdt, wrt,
      ot.mono (by omega) (by omega)⟩, et⟩

theorem stageA_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block stageA) s fun t => Keep base s t ∧ E t.mem base = stageEnv (E s.mem base) := by
  rw [stageA, WP.block_append_iff]
  refine WP.mono (copySlot_ok hs 8 6) fun s1 ⟨k1, e1⟩ => ?_
  refine WP.mono (copySlot_ok (k1.scr hs) 9 7) fun t ⟨kt, et⟩ => ⟨k1.trans kt, ?_⟩
  rw [et, e1]; rfl

theorem restoreB_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block restoreB) s fun t => Keep base s t ∧ E t.mem base = restoreEnv (E s.mem base) := by
  rw [restoreB, WP.block_append_iff]
  refine WP.mono (constE_ok hs 8 _ cBx) fun s1 ⟨k1, e1⟩ => ?_
  refine WP.mono (constE_ok (k1.scr hs) 9 _ cBy) fun t ⟨kt, et⟩ => ⟨k1.trans kt, ?_⟩
  rw [et, e1]; rfl

variable {P : Point64.Ops} (hP : Point64.PointOk P)

include hP in
/-- An iteration, for the bits `t` of `S` (`b₁`) and of `k` (`b₂`). -/
theorem vstep_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t < 456)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (t + 1)) {b₁ b₂ : Nat} (hb₁ : b₁ < 2) (hb₂ : b₂ < 2)
    (hbit₁ : s.mem (off base (BITS + t)) = BitVec.ofNat 8 b₁)
    (hbit₂ : s.mem (off base (KBITS + t)) = BitVec.ofNat 8 b₂) :
    WP isa (vstep P) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 t ∧ s'.zf = some (decide (t = 0)) ∧
      (∀ r, r ∉ .rbx :: clob → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base 64 1584 s.mem s'.mem ∧
      E s'.mem base = vstepEnv (decide (b₁ = 1)) (decide (b₂ = 1)) (E s.mem base) := by
  rw [vstep]
  refine WP.seq (WP.mono (dec_ok s hb) fun s1 ⟨b1, g1, m1, rd1, wr1⟩ => ?_)
  have hs1 : Scr s1 base := ⟨(g1 _ (by decide)).trans hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  refine WP.seq (WP.mono (hP.dbl hs1) fun s2 ⟨k2, e2⟩ => ?_)
  have hs2 := k2.scr hs1
  refine WP.seq (WP.mono (hP.add hs2) fun s3 ⟨k3, e3⟩ => ?_)
  have hs3 := k3.scr hs2
  have b3 : s3.gpr .rbx = BitVec.ofNat 64 t := by
    rw [k3.gpr _ (by decide), k2.gpr _ (by decide)]; exact b1
  have hout : ∀ o, 2048 ≤ o → o + t < 8192 → Proof.X448.X86_64.ofs base (off base (o + t)) < 64 ∨
      64 + 1584 ≤ Proof.X448.X86_64.ofs base (off base (o + t)) := fun o h1 h2 =>
    Or.inr (by rw [Proof.X448.X86_64.ofs_off' base (by omega)]; omega)
  have hbit3 : s3.mem (off base (BITS + t)) = BitVec.ofNat 8 b₁ := by
    rw [k3.mem _ (hout BITS (by decide) (by simp only [BITS]; omega)),
      k2.mem _ (hout BITS (by decide) (by simp only [BITS]; omega)), m1, hbit₁]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (maskAt_ok hs3 (by simp only [BITS]; omega) b3 hb₁ hbit3) fun s4 ⟨c4, g4, m4, rd4, wr4⟩ => ?_
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide)).trans hs3.rdi, wr4 ▸ hs3.wr, hs3.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (swapT_ok hs4 c4) fun s5 ⟨k5, e5⟩ => ?_
  have hs5 := k5.scr hs4
  refine WP.mono (stageA_ok hs5) fun s5' ⟨k5', e5'⟩ => ?_
  have hs5' := k5'.scr hs5
  refine WP.seq (WP.mono (hP.add hs5') fun s6 ⟨k6, e6⟩ => ?_)
  have hs6 := k6.scr hs5'
  have b6 : s6.gpr .rbx = BitVec.ofNat 64 t := by
    rw [k6.gpr _ (by decide), k5'.gpr _ (by decide), k5.gpr _ (by decide), g4 _ (by decide)]; exact b3
  have hbit6 : s6.mem (off base (KBITS + t)) = BitVec.ofNat 8 b₂ := by
    rw [k6.mem _ (hout KBITS (by decide) (by simp only [KBITS]; omega)),
      k5'.mem _ (hout KBITS (by decide) (by simp only [KBITS]; omega)),
      k5.mem _ (hout KBITS (by decide) (by simp only [KBITS]; omega)), m4,
      k3.mem _ (hout KBITS (by decide) (by simp only [KBITS]; omega)),
      k2.mem _ (hout KBITS (by decide) (by simp only [KBITS]; omega)), m1, hbit₂]
  rw [WP.block_append_iff]
  refine WP.mono (maskAt_ok hs6 (by simp only [KBITS]; omega) b6 hb₂ hbit6) fun s7 ⟨c7, g7, m7, rd7, wr7⟩ => ?_
  have hs7 : Scr s7 base := ⟨(g7 _ (by decide)).trans hs6.rdi, wr7 ▸ hs6.wr, hs6.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (swapT_ok hs7 c7) fun s8 ⟨k8, e8⟩ => ?_
  have hs8 := k8.scr hs7
  rw [WP.block_append_iff]
  refine WP.mono (restoreB_ok hs8) fun s9 ⟨k9, e9⟩ => ?_
  have b9 : s9.gpr .rbx = BitVec.ofNat 64 t := by
    rw [k9.gpr _ (by decide), k8.gpr _ (by decide), g7 _ (by decide)]; exact b6
  refine WP.mono (testRbx_ok s9 t ht b9) fun s' ⟨z', g', m', rd', wr'⟩ => ?_
  refine ⟨(g' _).trans b9, z', fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, not_or] at hr
    have hdc : r ∉ [Reg.rdx, .rcx] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => hr.2 (h ▸ by decide), fun h => hr.2 (h ▸ by decide)⟩
    rw [g', k9.gpr r hr.2, k8.gpr r hr.2, g7 r hdc, k6.gpr r hr.2, k5'.gpr r hr.2, k5.gpr r hr.2, g4 r hdc,
      k3.gpr r hr.2, k2.gpr r hr.2, g1 r hr.1]
  · rw [rd', k9.rd, k8.rd, rd7, k6.rd, k5'.rd, k5.rd, rd4, k3.rd, k2.rd, rd1]
  · rw [wr', k9.wr, k8.wr, wr7, k6.wr, k5'.wr, k5.wr, wr4, k3.wr, k2.wr, wr1]
  · rw [m', ← m1]
    exact ((((k2.mem.trans k3.mem).trans (by rw [m4]; exact Outside.refl _ _ _ _)).trans
      ((k5.mem.trans k5'.mem).trans k6.mem)).trans (by rw [m7]; exact Outside.refl _ _ _ _)).trans
      (k8.mem.trans k9.mem)
  · rw [m', e9, e8, m7, e6, e5', e5, m4, e3, e2, m1]
    rfl

/-- One bit of both scalars: the reference ladder's point after the bits above
`t`, then after bit `t`. -/
theorem vladder_step {e : Env} {S K t : Nat} {A : Spec.Ed448.Point} (ht : t < 456)
    (hr : pt e 0 1 2 = vladder S K A (456 - (t + 1)))
    (hq : pt e 8 9 10 = Spec.Ed448.basePoint) (ha : pt e 6 7 10 = A) (hd : e 11 = Spec.Ed448.d) :
    pt (vstepEnv (decide ((S >>> t) &&& 1 = 1)) (decide ((K >>> t) &&& 1 = 1)) e) 0 1 2 =
      vladder S K A (456 - t) := by
  have h10 : e 10 = 1 := (congrArg Spec.Ed448.Point.Z hq).trans rfl
  have hq' : (⟨e 8, e 9, 1⟩ : Spec.Ed448.Point) = Spec.Ed448.basePoint := by rw [← h10]; exact hq
  have ha' : (⟨e 6, e 7, 1⟩ : Spec.Ed448.Point) = A := by rw [← h10]; exact ha
  rw [vstepEnv_pt]
  dsimp only
  rw [hd, ← Point64.addWith_affine, ← Point64.addWith_affine, hq', ha', hr, vladder_bit S K A ht]
  simp only [addWith_d]
  rfl

/-- The loop's invariant, after the bits above `n` of `S` and `k`, with `-A` the point `A`. -/
structure VInv (base : Addr) (S K : Nat) (A : Spec.Ed448.Point) (s₀ : State) (n : Nat) (s : State) : Prop where
  scr : Scr s base
  rbx : s.gpr .rbx = BitVec.ofNat 64 n
  gpr : ∀ r, r ∉ .rbx :: clob → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base 64 1584 s₀.mem s.mem
  q : pt (E s.mem base) 8 9 10 = Spec.Ed448.basePoint
  na : pt (E s.mem base) 6 7 10 = A
  d : E s.mem base 11 = Spec.Ed448.d
  rep : pt (E s.mem base) 0 1 2 = vladder S K A (456 - n)

include hP in
theorem vloop_ok {s₀ : State} {base : Addr} {S K : Nat} {A : Spec.Ed448.Point}
    (hbs : ∀ t < 456, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 ((S >>> t) &&& 1))
    (hbk : ∀ t < 456, s₀.mem (off base (KBITS + t)) = BitVec.ofNat 8 ((K >>> t) &&& 1)) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 456 → VInv base S K A s₀ n s →
      WP isa (.loop (vstep P) .ne) s fun s' => VInv base S K A s₀ 0 s' := by
  intro n s hn1 hn2 hi
  refine WP.loop (M := isa) (Q := fun s' => VInv base S K A s₀ 0 s')
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 456 ∧ VInv base S K A s₀ m s) ?_ n s ⟨hn1, hn2, hi⟩
  rintro m s ⟨hm1, hm2, hi⟩
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  have hb1 : (S >>> t) &&& 1 < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hb2 : (K >>> t) &&& 1 < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hout : ∀ o, 2048 ≤ o → o + t < 8192 → Proof.X448.X86_64.ofs base (off base (o + t)) < 64 ∨
      64 + 1584 ≤ Proof.X448.X86_64.ofs base (off base (o + t)) := fun o h1 h2 =>
    Or.inr (by rw [Proof.X448.X86_64.ofs_off' base (by omega)]; omega)
  have hbit1 : s.mem (off base (BITS + t)) = BitVec.ofNat 8 ((S >>> t) &&& 1) := by
    rw [hi.mem _ (hout BITS (by decide) (by simp only [BITS]; omega))]
    exact hbs t (by omega)
  have hbit2 : s.mem (off base (KBITS + t)) = BitVec.ofNat 8 ((K >>> t) &&& 1) := by
    rw [hi.mem _ (hout KBITS (by decide) (by simp only [KBITS]; omega))]
    exact hbk t (by omega)
  refine WP.mono (vstep_ok hP hi.scr (by omega) hi.rbx hb1 hb2 hbit1 hbit2)
    fun s' ⟨b', z', g', rd', wr', o', e'⟩ => ?_
  obtain ⟨k6, k7, k10, k11, k8, k9⟩ := vstepEnv_keep (decide ((S >>> t) &&& 1 = 1))
    (decide ((K >>> t) &&& 1 = 1)) (E s.mem base)
  rw [← e'] at k6 k7 k10 k11 k8 k9
  have inv : VInv base S K A s₀ t s' := by
    refine ⟨⟨(g' _ (by decide)).trans hi.scr.rdi, wr' ▸ hi.scr.wr, hi.scr.nowrap⟩, b',
      fun r hr => (g' r hr).trans (hi.gpr r hr), rd'.trans hi.rd, wr'.trans hi.wr,
      hi.mem.trans o', ?_, ?_, ?_, ?_⟩
    · show (⟨_, _, _⟩ : Spec.Ed448.Point) = _
      have h10 : E s.mem base 10 = 1 := (congrArg Spec.Ed448.Point.Z hi.q).trans rfl
      rw [k8, k9, k10, h10]
      rfl
    · rw [pt_congr k6 k7 k10]; exact hi.na
    · rw [k11]; exact hi.d
    · rw [e']; exact vladder_step (by omega) hi.rep hi.q hi.na hi.d
  simp only [eval, z', Option.map_some]
  rcases Nat.eq_zero_or_pos t with h | h
  · subst h
    exact .inl ⟨rfl, inv⟩
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬t = 0), Bool.not_false], t, by omega,
      h, by omega, inv⟩

end VG.Proof.Ed448.X86_64
