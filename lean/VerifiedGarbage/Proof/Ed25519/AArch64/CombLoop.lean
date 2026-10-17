module

public import VerifiedGarbage.Proof.Ed25519.AArch64.CombSelect
public import VerifiedGarbage.Proof.Ed25519.CombDigits64
import VerifiedGarbage.Proof.Ed25519.AArch64.CombStart
public import VerifiedGarbage.Proof.Ed25519.AArch64.Point64.Call
public import VerifiedGarbage.Proof.Ed25519.AArch64.PointSelect
public import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Impl.Mont.Mod
import VerifiedGarbage.Proof.Ed25519.AArch64.CounterKeep
import VerifiedGarbage.Proof.Ed25519.AArch64.Sub
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-!
# The comb's loop

`combNeg` negates the selected `2dT` under the sign's mask; a call of
`vg_ed25519_r64_add_affine_ext` adds it (`affCall_ok`), exactly as the
specification's `pointAdd`. After step `i` of the loop, the accumulator
(slots 0–3) represents `[v + Σ_{i' < i} d_{i'} 16^{i'}]B` (`digitSum64`), from
`[v]B`; the loop starts at `[17 G]B` (`combStart`) and ends at the scalar's
multiple (`comb64_total`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards
open Word64 Fin.CommRing

/-! ## Frames -/

/-- Only the registers the comb uses (`x1`, `x19` and the field operations') and the field
slots change. -/
structure CombKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ≠ .x19 → r ≠ .x1 → r ∉ clob → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base 64 704 s.mem t.mem

theorem CombKeep.refl (base : Addr) (s : State) : CombKeep base s s :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem CombKeep.trans {base : Addr} {s t u : State} (h : CombKeep base s t)
    (k : CombKeep base t u) : CombKeep base s u :=
  ⟨fun r a b c => (k.gpr r a b c).trans (h.gpr r a b c), k.rd.trans h.rd, k.wr.trans h.wr,
    k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem CombKeep.scr {base : Addr} {s t : State} (h : CombKeep base s t) (hs : Scr s base) :
    Scr t base := ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem CombKeep.of_keep {base : Addr} {s t : State} (h : Keep base s t) : CombKeep base s t :=
  ⟨fun r _ _ hc => h.gpr r hc, h.rd, h.wr, h.sp, h.mem⟩

theorem CombKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .x19 ∨ r = .x1 ∨ r ∈ clob) : CombKeep base s t := by
  refine ⟨fun r h19 h1 hc => h.gpr r (fun hm => ?_), h.rd, h.wr, h.sp, by rw [h.mem]; exact Outside.refl _ _ _ _⟩
  rcases hrs r hm with h | h | h
  · exact h19 h
  · exact h1 h
  · exact hc h

theorem CombKeep.bit {base : Addr} {s t : State} (h : CombKeep base s t) {q : Nat} (hq : q < 256) :
    t.mem (off base (768 + q)) = s.mem (off base (768 + q)) :=
  h.mem _ (by rw [ofs_off' base (by omega)]; omega)

theorem CombKeep.powers {base : Addr} {s t : State} (h : CombKeep base s t) :
    PowersKeep base 56 968 s t :=
  ⟨fun r a b c => h.gpr r a b c, h.rd, h.wr, h.sp, TableFrame.workspace h.mem⟩

/-- What a field program whose results are in slots 0–15 leaves: every slot from 16 on. -/
theorem outside_of_unwritten {ops : List FieldOp} {base : Addr} {m m' : Mem}
    (h : ∀ x, Point64.Unwritten ops base x → m' x = m x) (hd : ∀ op ∈ ops, (fieldDest op).val < 16) :
    Outside base 64 512 m m' := fun x hx => h x fun op hop => by
  have := hd op hop
  simp only [offset]
  omega

theorem env_high {base : Addr} {m m' : Mem} (h : Outside base 64 512 m m') (i : Slot) (hi : 16 ≤ i.val) :
    env m' base i = env m base i := by
  simp only [env, F]
  rw [h.fe (by simp only [offset]; omega) (by simp only [offset]; omega)]

/-! ## The negations -/

/-- `x4`–`x7` kept where the sign's mask in `x1` is set, else `x12`–`x15`. -/
theorem negSel_ok (s : State) {sg : Bool} (h1 : s.gpr .x1 = mask sg) :
    WP isa (.block negSel) s fun t =>
      t.gpr .x4 = (if sg then s.gpr .x4 else s.gpr .x12) ∧ t.gpr .x5 = (if sg then s.gpr .x5 else s.gpr .x13) ∧
      t.gpr .x6 = (if sg then s.gpr .x6 else s.gpr .x14) ∧ t.gpr .x7 = (if sg then s.gpr .x7 else s.gpr .x15) ∧
      Keeps [.x4, .x5, .x6, .x7] s t := by
  apply WP.of_runBlock
  cases sg <;>
  · simp only [negSel, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
      BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left', CondCode.holds,
      h1, mask, BitVec.and_self, Bool.false_eq_true, RegUpd.zf_write, decide_true, decide_false,
      show (BitVec.allOnes 64 = 0) = False by decide, Bool.not_false, Bool.not_true]
    refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ↓reduceIte]

/-- Slot `c` negated (`0 - [c]`, from slot 21) where the sign's mask in `x1` is set. -/
theorem combNeg_ok {s : State} {base : Addr} (hs : Scr s base) (c : Slot) {sg : Bool}
    (h1 : s.gpr .x1 = mask sg) :
    WP isa (.block (combNeg c)) s fun t => Op base (offset c) s t ∧
      F t.mem base (offset c) =
        if sg then F s.mem base (offset 21) - F s.mem base (offset c) else F s.mem base (offset c) := by
  rw [combNeg, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (subRegs_ok hs (slot_range 21) (slot_range c)) fun u ⟨eu, ku⟩ => ?_
  have hsu := hs.of_keeps ku (by decide)
  refine WP.mono (loads_ok hsu (slot_range c) (a := .x12) (b := .x13) (c := .x14) (d := .x15) (by decide))
    fun v ⟨v12, v13, v14, v15, kv⟩ => ?_
  have hsv := hsu.of_keeps kv (by decide)
  refine WP.mono (negSel_ok v (sg := sg) (by rw [kv.gpr _ (by decide), ku.gpr _ (by decide), h1]))
    fun w ⟨w4, w5, w6, w7, kw⟩ => ?_
  refine WP.mono (store4_ok (hsv.of_keeps kw (by decide)) (slot_range c)) fun t ht => ?_
  subst t
  have kuw : Keeps clob s w := (ku.mono (by decide)).trans ((kv.mono (by decide)).trans (kw.mono (by decide)))
  refine ⟨Op.of_store (slot_range c) kuw _ _ _ _, ?_⟩
  simp only [F]
  rw [fe_st4 _ _ (by simp only [offset]; omega), w4, w5, w6, w7]
  cases sg
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [v12, v13, v14, v15, ku.mem]
  · simp only [↓reduceIte]
    rw [kv.gpr _ (by decide), kv.gpr _ (by decide), kv.gpr _ (by decide), kv.gpr _ (by decide)]
    exact eu

/-! ## The loop over the digits -/

/-- The loop's invariant, after `j` steps from `[v]B`. -/
structure CombInv (s₀ : State) (base : Addr) (S : Nat) (v : ℤ) (j : Nat) (s : State) : Prop where
  bound : j ≤ 64
  scratch : Scr s base
  counter : s.gpr .x19 = BitVec.ofNat 64 j
  zero : env s.mem base 21 = 0
  bits : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)
  acc : Rep (point (env s.mem base) 0 1 2 3) ((v + digitSum64 S j) • baseAff)
  keep : CombKeep base s₀ s

private theorem next_fact : ∀ j < 64,
    BitVec.ofNat 64 j + BitVec.ofNat 64 1 = BitVec.ofNat 64 (j + 1) ∧
    (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 64 != 0) = decide (j + 1 ≠ 64) := by decide +kernel

theorem combNext_ok (s : State) {j : Nat} (hj : j < 64) (h : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block [.addImm .x .x19 .x19 1, .subImm .x .x8 .x19 64]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (j + 1) ∧ (t.gpr .x8 != 0) = decide (j + 1 ≠ 64) ∧
      Keeps [.x19, .x8] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addImm_x (show 1 < 4096 by decide),
    exec_subImm_x (show 64 < 4096 by decide), read_x, RegUpd.gpr_write, BitVec.setWidth_eq, h,
    (next_fact j hj).1, (next_fact j hj).2, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem combStep_ok {s₀ s : State} {base T : Addr} {S : Nat} {v : ℤ} {j : Nat}
    (h : CombInv s₀ base S v j s) (htb : TblAt s₀ base T) (hT : s.syms combSym = T)
    (hj : j < 64) :
    WP isa combStep s fun t => (t.gpr .x8 != 0) = decide (j + 1 ≠ 64) ∧
      CombInv s₀ base S v (j + 1) t := by
  rw [combStep]
  have hn := nib_lt S j
  -- The digit's masks.
  refine WP.seq (WP.mono_syms (combDigit_ok h.scratch (i := j) hj h.counter h.bits) fun a ha sya => ?_)
  have hsa : Scr a base := h.scratch.of_keeps ha.keeps (by decide)
  have a19 : a.gpr .x19 = BitVec.ofNat 64 j := (ha.keeps.gpr _ (by decide)).trans h.counter
  have hm : Masks (mag (nib S j)) a := ⟨ha.mask, ha.zero⟩
  have ksa : CombKeep base s a := CombKeep.of_keeps ha.keeps (by
    intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with hr | hr
    · exact Or.inr (Or.inr hr)
    · exact Or.inr (Or.inl hr))
  -- The entry.
  have hta : TblAt a base T := htb.of_far (by rw [ha.keeps.rd, ha.keeps.wr, h.keep.rd, h.keep.wr])
    (fun x hx => by rw [ha.keeps.mem]; exact h.keep.mem x (Or.inr (by omega)))
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (combSelect_ok hsa hta (by rw [sya]; exact hT) hj a19 (mag_lt hn) hm ha.sign)
    fun b ⟨b4, b5, b6, bf, kb⟩ => ?_
  have hsb : Scr b base := ⟨(kb.1 _ (by decide)).trans hsa.x0, kb.2.2.1 ▸ hsa.wr, hsa.nowrap⟩
  have b19 : b.gpr .x19 = BitVec.ofNat 64 j := (kb.1 _ (by decide)).trans a19
  have kab : CombKeep base a b := ⟨fun r _ _ hc => kb.1 r (fun hm => hc (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> decide)), kb.2.1, kb.2.2.1, kb.2.2.2,
    bf.mono (by simp only [offset]; omega) (by simp only [offset]; omega)⟩
  have ksb := ksa.trans kab
  have eb : ∀ i : Slot, (i.val < 4 ∨ 7 ≤ i.val) → env b.mem base i = env s.mem base i := fun i hi => by
    simp only [env, F]
    rw [bf.fe (by simp only [offset]; omega) (by simp only [offset]; omega), ha.keeps.mem]
  -- `2dT` negated for a negative digit.
  refine WP.mono (combNeg_ok hsb 6 (sg := decide (nib S j < 8))
    ((kb.1 _ (by decide)).trans ha.sign)) fun c ⟨oc, vc⟩ => ?_
  have kc : Keep base b c := op_keep oc
  obtain ⟨q, hq, hqz, hrq⟩ := combEntry64_ok j (nib S j) hj hn
  have b21 : env b.mem base 21 = 0 := (eb 21 (by decide)).trans h.zero
  have ec : ∀ i : Slot, i ≠ 6 → env c.mem base i = env b.mem base i := fun i hi => by
    rw [env_update 6 oc.mem, Function.update_of_ne hi]
  have cq : cachedAt (env c.mem base) 4 5 6 = cache q := by
    rw [← hq]
    have c6 : env c.mem base 6 = if decide (nib S j < 8) then
        env b.mem base 21 - env b.mem base 6 else env b.mem base 6 := vc
    rw [b21, b6] at c6
    have hT := combCached64_T j (mag (nib S j))
    by_cases hlt : nib S j < 8
    · simp only [hlt, decide_true, ↓reduceIte] at b4 b5 c6 ⊢
      simp only [cachedAt, negCached, ec 4 (by decide), ec 5 (by decide), b4, b5, c6, hT]
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte] at b4 b5 c6 ⊢
      rw [cachedAt_eq hT (by rw [ec 4 (by decide), b4]) (by rw [ec 5 (by decide), b5]) c6]
  have hsc := kc.scr hsb
  have c19 : c.gpr .x19 = BitVec.ofNat 64 j := (kc.gpr _ (by decide)).trans b19
  -- Added.
  refine WP.seq (WP.mono (Point64.affCall_ok hsc) fun d ⟨kd, vd, md⟩ => ?_)
  have hd := outside_of_unwritten md (by decide)
  have d19 : d.gpr .x19 = BitVec.ofNat 64 j := (kd.gpr _ (by decide)).trans c19
  refine WP.mono (combNext_ok d hj d19) fun t ⟨t19, t8, kt⟩ => ⟨t8, ?_⟩
  have kbt : CombKeep base b t :=
    (((CombKeep.of_keep kc).trans (CombKeep.of_keep kd))).trans (CombKeep.of_keeps kt (by decide))
  have kst := ksb.trans kbt
  have pc : point (env c.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
    simp only [point, ec 0 (by decide), ec 1 (by decide), ec 2 (by decide), ec 3 (by decide),
      eb 0 (by decide), eb 1 (by decide), eb 2 (by decide), eb 3 (by decide)]
  refine ⟨by omega, kbt.scr hsb, t19, ?_, fun q hq => ?_, ?_, h.keep.trans kst⟩
  · rw [kt.mem, env_high hd 21 (by decide), ec 21 (by decide)]
    exact b21
  · rw [kst.bit hq]; exact h.bits q hq
  · have h4 : env c.mem base 4 = q.Y - q.X := congrArg Spec.Ed25519.Point.X cq
    have h5 : env c.mem base 5 = q.Y + q.X := congrArg Spec.Ed25519.Point.Y cq
    have h6 : env c.mem base 6 = q.T * 2 * Spec.Ed25519.d := congrArg Spec.Ed25519.Point.Z cq
    rw [kt.mem, vd, Point64.addAffineOps_eval _ q hqz h4 h5 h6, pc, digitSum64, ← add_assoc, add_smul]
    exact pointAdd_rep h.acc hrq

/-- The loop's steps from digit `j₀ < 64` on, from the invariant at `j₀`. -/
theorem combSteps_ok {s₀ b : State} {base T : Addr} (htb : TblAt s₀ base T) {S : Nat} {v : ℤ}
    {j₀ : Nat} (hj₀ : j₀ < 64) (init : CombInv s₀ base S v j₀ b) (hT : b.syms combSym = T) :
    WP isa (.loop combStep (.nonzero .x .x8)) b fun t => CombInv s₀ base S v 64 t := by
  apply WP.loop (fun n (t : State) => (CombInv s₀ base S v (64 - n) t ∧ t.syms combSym = T) ∧
    0 < n ∧ n ≤ 64) (n := 64 - j₀)
  · intro n t ⟨⟨ht, hty⟩, hn0, hn⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    refine WP.mono_syms (combStep_ok ht htb hty (by omega)) fun u ⟨u8, hu⟩ suy => ?_
    by_cases hk : k = 0
    · subst hk
      exact Or.inl ⟨by simp only [eval, read_x, u8, show 64 - (0 + 1) + 1 = 64 from rfl, ne_eq,
        not_true_eq_false, decide_false], hu⟩
    · refine Or.inr ⟨by simp only [eval, read_x, u8, show 64 - (k + 1) + 1 ≠ 64 by omega, ne_eq,
        not_false_eq_true, decide_true], k, by omega, ⟨?_, by rw [suy]; exact hty⟩, by omega, by omega⟩
      rw [show 64 - k = 64 - (k + 1) + 1 by omega]; exact hu
  · exact ⟨⟨by rw [show 64 - (64 - j₀) = j₀ by omega]; exact init, hT⟩, by omega, by omega⟩

/-- The counter `x19` set to `j < 2^16`. -/
theorem counterInit_ok (s : State) (j : Nat) (hj : j < 2 ^ 16) :
    WP isa (.block [.movz .w .x19 j 0]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 j ∧ Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Size.bits]
    simp only [Nat.mul_zero, Nat.shiftLeft_zero, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
    omega
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

/-- The loop from digit `j₀ < 64`, from `[v + Σ_{i < j₀} d_i 16^i]B`. -/
theorem combLoopFrom_ok {s : State} {base T : Addr} (hs : Scr s base) (htb : TblAt s base T)
    (hT : s.syms combSym = T) {S : Nat} {v : ℤ} {j₀ : Nat} (hj₀ : j₀ < 64)
    (hz : env s.mem base 21 = 0)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2))
    (hv : Rep (point (env s.mem base) 0 1 2 3) ((v + digitSum64 S j₀) • baseAff)) :
    WP isa (combLoopFrom j₀) s fun t => CombInv s base S v 64 t := by
  rw [combLoopFrom]
  refine WP.seq (WP.mono_syms (counterInit_ok s j₀ (by omega)) fun b ⟨b19, kb⟩ syb => ?_)
  have ksb : CombKeep base s b := CombKeep.of_keeps kb (by decide)
  exact combSteps_ok htb hj₀
    ⟨by omega, hs.of_keeps kb (by decide), b19, by rw [kb.mem]; exact hz,
      fun q hq => by rw [kb.mem]; exact hb q hq, by rw [kb.mem]; exact hv, ksb⟩
    (by rw [syb]; exact hT)

/-- The loop over the 64 digits, from `[v]B`. -/
theorem combLoop_ok {s : State} {base T : Addr} (hs : Scr s base) (htb : TblAt s base T)
    (hT : s.syms combSym = T) {S : Nat} {v : ℤ}
    (hz : env s.mem base 21 = 0)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2))
    (hv : Rep (point (env s.mem base) 0 1 2 3) (v • baseAff)) :
    WP isa combLoop s fun t => CombInv s base S v 64 t :=
  combLoopFrom_ok hs htb hT (by decide) hz hb (by rw [digitSum64, add_zero]; exact hv)

/-! ## The comb -/

theorem combInit_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block combInit) s fun t => CombKeep base s t ∧ env t.mem base 21 = 0 ∧
      point (env t.mem base) 0 1 2 3 = combStart := by
  refine WP.mono (fieldCode_ok _ hs) fun t ⟨kt, vt⟩ => ⟨CombKeep.of_keep kt, ?_, ?_⟩
  · rw [vt]; rfl
  · rw [vt]; rfl

theorem combMultiply_ok {s : State} {base T : Addr} (hs : Scr s base) (htb : TblAt s base T)
    (hT : s.syms combSym = T) {S : Nat} (hS : S < 2 ^ 256)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa combMultiply s fun t =>
      Rep (point (env t.mem base) 0 1 2 3) (S • baseAff) ∧ CombKeep base s t := by
  rw [combMultiply]
  refine WP.seq (WP.mono_syms (combInit_ok hs) fun a ⟨ka, az, ap⟩ sya => ?_)
  have hsa := ka.scr hs
  have hta : TblAt a base T := htb.of_far (by rw [ka.rd, ka.wr])
    (fun x hx => ka.mem x (Or.inr (by omega)))
  have hv : Rep (point (env a.mem base) 0 1 2 3) (((17 * combGVal : Nat) : ℤ) • baseAff) := by
    rw [ap, natCast_zsmul]; exact combStart_ok
  refine WP.mono (combLoop_ok hsa hta (by rw [sya]; exact hT) az
    (fun q hq => by rw [ka.bit hq]; exact hb q hq) hv) fun t ht => ⟨?_, ka.trans ht.keep⟩
  have hu := ht.acc
  rw [comb64_total hS, natCast_zsmul] at hu
  exact hu

end VG.Proof.Ed25519.AArch64
