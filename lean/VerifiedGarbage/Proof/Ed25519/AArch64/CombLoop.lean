module

import VerifiedGarbage.Proof.Ed25519.AArch64.CombEntry
public import VerifiedGarbage.Proof.Ed25519.CombDigits64
import VerifiedGarbage.Proof.Ed25519.AArch64.CombStart
public import VerifiedGarbage.Proof.Ed25519.AArch64.CombAdd
public import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers
public import VerifiedGarbage.Proof.Ed25519.AArch64.CombSelect
public import VerifiedGarbage.Proof.Ed25519.Canonical64
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-!
# The comb's loop

`combNeg` negates the selected `2dT` under the sign's mask; `combAdd` adds it
(`combAdd_ok`), exactly as the specification's `pointAdd`, keeping the
accumulator's coordinates below `2·p` (`AccBel`). After step `i` of the loop, the accumulator
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

/-- The loop's invariant, after `j` steps from `[v]B`. -/
structure CombInv (s₀ : State) (base : Addr) (S : Nat) (v : ℤ) (j : Nat) (s : State) : Prop where
  bound : j ≤ 64
  scratch : Scr s base
  counter : s.gpr .x19 = BitVec.ofNat 64 j
  zero : env s.mem base 21 = 0
  bits : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)
  acc : Rep (point (env s.mem base) 0 1 2 3) ((v + digitSum64 S j) • baseAff)
  bel : AccBel s.mem base
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
  -- The digit's magnitude and sign.
  refine WP.seq (WP.mono_syms (combDigitS_ok h.scratch (i := j) hj h.counter h.bits)
    fun a ⟨a2, a1, ka⟩ sya => ?_)
  have hsa : Scr a base := h.scratch.of_keeps ka (by decide)
  have a19 : a.gpr .x19 = BitVec.ofNat 64 j := (ka.gpr _ (by decide)).trans h.counter
  have ksa : CombKeep base s a := CombKeep.of_keeps ka (by
    intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with hr | hr
    · exact Or.inr (Or.inr hr)
    · exact Or.inr (Or.inl hr))
  -- The entry, negated for a negative digit.
  have hta : TblAt a base T := htb.of_far (by rw [ka.rd, ka.wr, h.keep.rd, h.keep.wr])
    (fun x hx => by rw [ka.mem]; exact h.keep.mem x (Or.inr (by omega)))
  refine WP.seq (WP.mono (combEntry_ok hsa hta (by rw [sya]; exact hT) hj a19 (mag_lt hn) a2 a1)
    fun c ⟨c4, c5, c6, cf, kc⟩ => ?_)
  have fc : ∀ i : Slot, (i.val < 4 ∨ 7 ≤ i.val) → fe c.mem base (offset i) = fe s.mem base (offset i) :=
    fun i hi => by
      rw [cf.fe (by simp only [offset]; omega) (by simp only [offset]; omega), ka.mem]
  have ec : ∀ i : Slot, (i.val < 4 ∨ 7 ≤ i.val) → env c.mem base i = env s.mem base i := fun i hi => by
    simp only [env, F]
    rw [fc i hi]
  obtain ⟨q, hq, hqz, hrq⟩ := combEntry64_ok j (nib S j) hj hn
  have c21 : env c.mem base 21 = 0 := (ec 21 (by decide)).trans h.zero
  have cq : cachedAt (env c.mem base) 4 5 6 = cache q := by
    rw [← hq]
    have hT := combCached64_T j (mag (nib S j))
    by_cases hlt : nib S j < 8
    · simp only [hlt, decide_true, ↓reduceIte] at c4 c5 c6 ⊢
      simp only [cachedAt, negCached, c4, c5, c6, hT]
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte] at c4 c5 c6 ⊢
      rw [cachedAt_eq hT c4 c5 c6]
  have hsc := kc.scr hsa
  have c19 : c.gpr .x19 = BitVec.ofNat 64 j := (kc.gpr _ (by decide)).trans a19
  have belc : AccBel c.mem base := fun i hi => by
    rw [fc i (.inl hi)]
    exact h.bel i hi
  -- Added.
  rw [WP.seq_iff]
  refine WP.mono (combAdd_ok hsc belc) fun d ⟨kd, beld, vd, md⟩ => ?_
  have d19 : d.gpr .x19 = BitVec.ofNat 64 j := (kd.gpr _ (by decide)).trans c19
  refine WP.mono (combNext_ok d hj d19) fun t ⟨t19, t8, kt⟩ => ⟨t8, ?_⟩
  have kbt : CombKeep base a t :=
    (((CombKeep.of_keep kc).trans (CombKeep.of_keep kd))).trans (CombKeep.of_keeps kt (by decide))
  have kst := ksa.trans kbt
  have pc : point (env c.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
    simp only [point, ec 0 (by decide), ec 1 (by decide), ec 2 (by decide), ec 3 (by decide)]
  have d21 : env d.mem base 21 = env c.mem base 21 := by
    simp only [env, F]; rw [md 21 (.inr (by decide))]
  refine ⟨by omega, kbt.scr hsa, t19, ?_, fun q hq => ?_, ?_, fun i hi => by rw [kt.mem]; exact beld i hi,
    h.keep.trans kst⟩
  · rw [kt.mem, d21]
    exact c21
  · rw [kst.bit hq]; exact h.bits q hq
  · have h4 : env c.mem base 4 = q.Y - q.X := congrArg Spec.Ed25519.Point.X cq
    have h5 : env c.mem base 5 = q.Y + q.X := congrArg Spec.Ed25519.Point.Y cq
    have h6 : env c.mem base 6 = q.T * 2 * Spec.Ed25519.d := congrArg Spec.Ed25519.Point.Z cq
    rw [kt.mem, vd, h4, h5, h6]
    have e := Point64.mixedResult_eq (point (env c.mem base) 0 1 2 3) q hqz
    simp only [point] at e
    rw [e]
    simp only [point] at pc
    rw [pc, digitSum64, ← add_assoc, add_smul]
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
    (hv : Rep (point (env s.mem base) 0 1 2 3) ((v + digitSum64 S j₀) • baseAff))
    (hB : AccBel s.mem base) :
    WP isa (combLoopFrom j₀) s fun t => CombInv s base S v 64 t := by
  rw [combLoopFrom]
  refine WP.seq (WP.mono_syms (counterInit_ok s j₀ (by omega)) fun b ⟨b19, kb⟩ syb => ?_)
  have ksb : CombKeep base s b := CombKeep.of_keeps kb (by decide)
  exact combSteps_ok htb hj₀
    ⟨by omega, hs.of_keeps kb (by decide), b19, by rw [kb.mem]; exact hz,
      fun q hq => by rw [kb.mem]; exact hb q hq, by rw [kb.mem]; exact hv,
      fun i hi => by rw [kb.mem]; exact hB i hi, ksb⟩
    (by rw [syb]; exact hT)

/-- The loop over the 64 digits, from `[v]B`. -/
theorem combLoop_ok {s : State} {base T : Addr} (hs : Scr s base) (htb : TblAt s base T)
    (hT : s.syms combSym = T) {S : Nat} {v : ℤ}
    (hz : env s.mem base 21 = 0)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2))
    (hv : Rep (point (env s.mem base) 0 1 2 3) (v • baseAff)) (hB : AccBel s.mem base) :
    WP isa combLoop s fun t => CombInv s base S v 64 t :=
  combLoopFrom_ok hs htb hT (by decide) hz hb (by rw [digitSum64, add_zero]; exact hv) hB

/-! ## The comb -/

theorem combInit_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block combInit) s fun t => CombKeep base s t ∧ env t.mem base 21 = 0 ∧
      point (env t.mem base) 0 1 2 3 = combStart ∧ AccBel t.mem base := by
  refine WP.mono (fieldCode_okS _ hs (Small.none s.mem base)) fun t ⟨kt, vt, st⟩ =>
    ⟨CombKeep.of_keep kt, ?_, ?_, fun i hi => ?_⟩
  · rw [vt]; rfl
  · rw [vt]; rfl
  · have := st i ((by decide : ∀ i : Slot, i.val < 4 →
      smallAfterOps ([.const 21 0] ++ constPointOps combStart) (fun _ => false) i = true) i hi)
    simp only [VG.Proof.X25519.AArch64.AltLadder.P2]; omega

theorem combMultiply_ok {s : State} {base T : Addr} (hs : Scr s base) (htb : TblAt s base T)
    (hT : s.syms combSym = T) {S : Nat} (hS : S < 2 ^ 256)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa combMultiply s fun t =>
      Rep (point (env t.mem base) 0 1 2 3) (S • baseAff) ∧ CombKeep base s t := by
  rw [combMultiply]
  refine WP.seq (WP.mono_syms (combInit_ok hs) fun a ⟨ka, az, ap, ab⟩ sya => ?_)
  have hsa := ka.scr hs
  have hta : TblAt a base T := htb.of_far (by rw [ka.rd, ka.wr])
    (fun x hx => ka.mem x (Or.inr (by omega)))
  have hv : Rep (point (env a.mem base) 0 1 2 3) (((17 * combGVal : Nat) : ℤ) • baseAff) := by
    rw [ap, natCast_zsmul]; exact combStart_ok
  refine WP.mono (combLoop_ok hsa hta (by rw [sya]; exact hT) az
    (fun q hq => by rw [ka.bit hq]; exact hb q hq) hv ab) fun t ht => ⟨?_, ka.trans ht.keep⟩
  have hu := ht.acc
  rw [comb64_total hS, natCast_zsmul] at hu
  exact hu

end VG.Proof.Ed25519.AArch64
