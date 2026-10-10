import VerifiedGarbage.Proof.Ed25519.AArch64.CombSelect
import VerifiedGarbage.Proof.Ed25519.AArch64.CombStart
import VerifiedGarbage.Proof.Ed25519.AArch64.Point64.Call
import VerifiedGarbage.Proof.Ed25519.AArch64.PointSelect
import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers
import VerifiedGarbage.Proof.Ed25519.PointDouble

/-!
# The comb's loops and doublings

`combNeg` negates the selected cached point under the sign's mask; a call of
`vg_ed25519_r64_add_affine_ext` adds it (`affCall_ok`), exactly as the
specification's `pointAdd`; `double4` doubles four times, by calls of
`vg_ed25519_r64_double_ext` (`doubleCall_ok`, RFC 8032's doubling,
`pointDouble_rep`). After step `j` of the loop of the digits `2i + par`, the
accumulator (slots 0–3) represents `[v + Σ_{i < j} d_{2i+par} 256^i]B`
(`digitSum`), from `[v]B`; the odd digits' loop starts at `[G']B`
(`combStart`), the doublings make that `[16 (G + Σ_i d_{2i+1} 256^i) + G]B`
(`combStart_16`), and the even digits' loop ends at the scalar's multiple
(`comb_total`).
-/

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
    PowersKeep base 56 7368 s t :=
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

private theorem index3_fact : ∀ j < 32, BitVec.ofNat 64 j <<< 3 = BitVec.ofNat 64 (8 * j) := by
  decide +kernel

private theorem bit_mask : ∀ b < 2,
    ((BitVec.ofNat 8 b).setWidth 32).setWidth 64 - BitVec.ofNat 64 1 = mask (decide (b = 0)) := by
  decide

theorem nib_neg (S i : Nat) : decide (nib S i < 8) = decide ((S / 2 ^ (4 * i + 3)) % 2 = 0) := by
  rw [nib_bits]
  have h0 := Nat.mod_lt (S / 2 ^ (4 * i)) (show 2 > 0 by decide)
  have h1 := Nat.mod_lt (S / 2 ^ (4 * i + 1)) (show 2 > 0 by decide)
  have h2 := Nat.mod_lt (S / 2 ^ (4 * i + 2)) (show 2 > 0 by decide)
  have h3 := Nat.mod_lt (S / 2 ^ (4 * i + 3)) (show 2 > 0 by decide)
  apply decide_eq_decide.mpr
  omega

theorem signLoad_ok {s : State} {base : Addr} (hs : Scr s base) {S j i o : Nat} (hj : j < 32)
    (hi : i < 64) (hoi : 8 * j + o = 768 + 4 * i) (ho : o + 3 < 4096)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa (.block [.lsl .x .x3 .x19 3, .add .x .x3 .x0 .x3, .ldrb .x3 .x3 (o + 3),
      .subImm .x .x3 .x3 1]) s fun t =>
      t.gpr .x3 = mask (decide (nib S i < 8)) ∧ Keeps [.x3] s t := by
  have _hcap : workSize true = 8192 := rfl
  have hr : InRegions (s.rd ++ s.wr) (off base (768 + (4 * i + 3))) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by omega) (by omega)⟩
  have he : base + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 (o + 3) = off base (768 + (4 * i + 3)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (off base) (by omega)
  have hv := bit_mask _ (Nat.mod_lt (S / 2 ^ (4 * i + 3)) (show 2 > 0 by decide))
  rw [← hb _ (by omega), ← nib_neg] at hv
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, State.load, addr, Size.bits,
    show (3 : Nat) < 64 from by decide, show (1 : Nat) < 4096 from by decide,
    show o + 3 < 4096 * 1 by omega, Nat.mod_one, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq,
    hc, index3_fact j hj, hs.x0, he, hr, read_byte, hv,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- The negation, on the environment. -/
theorem neg_env (e : Env) (a b c : Slot) (sw : Bool) (hab : a ≠ b) (hc8 : c ≠ 8) (ha : a ≠ 8)
    (hb : b ≠ 8) (hac : a ≠ c) (hbc : b ≠ c) (hz : e 21 = 0) :
    cachedAt (swapEnvs [(a, b), (c, 8)] sw (evalOps [.sub 8 21 c] e)) a b c =
      if sw then negCached (cachedAt e a b c) else cachedAt e a b c := by
  cases sw <;> simp [cachedAt, negCached, swapEnvs, swapEnv, evalOps, evalOp,
    hab, hc8, ha, hb, ha.symm, hb.symm, hac, hac.symm, hbc, hbc.symm, hz]

theorem neg_other (e : Env) (a b c : Slot) (sw : Bool) (i : Slot) (ha : i ≠ a) (hb : i ≠ b)
    (hc : i ≠ c) (h8 : i ≠ 8) :
    swapEnvs [(a, b), (c, 8)] sw (evalOps [.sub 8 21 c] e) i = e i := by
  cases sw <;> simp [swapEnvs, swapEnv, evalOps, evalOp, Function.update_apply, ha, hb, hc, h8]

theorem combNeg_ok {s : State} {base : Addr} (hs : Scr s base) {S j i o : Nat} (a b c : Slot)
    (hj : j < 32) (hi : i < 64) (hoi : 8 * j + o = 768 + 4 * i) (ho : o + 3 < 4096)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2))
    (hdis : ∀ ab ∈ [(a, b), (c, (8 : Slot))], ab.1 ≠ ab.2) :
    WP isa (.block (combNeg a b c o)) s fun t => Keep base s t ∧
      env t.mem base = swapEnvs [(a, b), (c, 8)] (decide (nib S i < 8))
        (evalOps [.sub 8 21 c] (env s.mem base)) := by
  rw [combNeg, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCode_ok [.sub 8 21 c] hs) fun u ⟨ku, vu⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (signLoad_ok (S := S) (ku.scr hs) hj hi hoi ho ((ku.gpr _ (by decide)).trans hc)
    (fun q hq => by rw [ku.mem _ (by rw [ofs_off' base (by omega)]; omega)]; exact hb q hq))
    fun v ⟨v3, kv⟩ => ?_
  have kuv : Keep base u v := Keep.of_keeps kv (by decide)
  refine WP.mono (swapFields_ok ((ku.trans kuv).scr hs) [(a, b), (c, 8)] hdis v3)
    fun t ⟨kt, _, vt⟩ => ⟨(ku.trans kuv).trans kt, ?_⟩
  rw [vt, kv.mem, vu]

/-! ## Four doublings -/

theorem decX1_ok (s : State) (n : Nat) (hc : s.gpr .x1 = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block [.subImm .x .x1 .x1 1]) s fun t =>
      t.gpr .x1 = BitVec.ofNat 64 n ∧ Keeps [.x1] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (1 : Nat) < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, hc, BitVec.ofNat_add, BitVec.add_sub_cancel]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

theorem double4_counter : ∀ n < 16, (BitVec.ofNat 64 n != 0) = decide (n ≠ 0) := by decide

structure Double4Inv (s₀ : State) (base : Addr) (a : EPoint dZ) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 4
  scratch : Scr s base
  counter : s.gpr .x1 = BitVec.ofNat 64 n
  value : Rep (point (env s.mem base) 0 1 2 3) ((2 ^ (4 - n) : Nat) • a)
  high : Outside base 64 512 s₀.mem s.mem
  keep : CombKeep base s₀ s

theorem double4_ok {s : State} {base : Addr} (hs : Scr s base) {a : EPoint dZ}
    (hp : Rep (point (env s.mem base) 0 1 2 3) a) :
    WP isa double4 s fun t =>
      Rep (point (env t.mem base) 0 1 2 3) ((16 : Nat) • a) ∧ Outside base 64 512 s.mem t.mem ∧
        CombKeep base s t := by
  rw [double4]
  refine WP.seq (WP.mono (show WP isa (.block [.movz .w .x1 4 0]) s fun t =>
      t.gpr .x1 = BitVec.ofNat 64 4 ∧ Keeps [.x1] s t by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
      show 16 * 0 < Size.w.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
    · rw [RegUpd.gpr_write_self]; rfl
    · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)) fun b ⟨bc, kb⟩ => ?_)
  have hsb : Scr b base := hs.of_keeps kb (by decide)
  have ksb : CombKeep base s b := CombKeep.of_keeps kb (by decide)
  have eb : b.mem = s.mem := kb.mem
  have hl : WP isa (.loop (.seq Point64.doubleCall (.block [.subImm .x .x1 .x1 1])) (.nonzero .x .x1))
      b fun t => Rep (point (env t.mem base) 0 1 2 3) ((16 : Nat) • a) ∧
        Outside base 64 512 b.mem t.mem ∧ CombKeep base b t := by
    apply WP.loop (Double4Inv b base a) (n := 4)
    · intro n u hi
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega : n ≠ 0)
      have hk : k < 4 := by have := hi.bound; omega
      refine WP.seq (WP.mono (Point64.doubleCall_ok hi.scratch) fun c ⟨kc, vc, mc⟩ => ?_)
      have hc := outside_of_unwritten mc (by decide)
      refine WP.mono (decX1_ok c k ((kc.gpr _ (by decide)).trans hi.counter)) fun t ⟨htc, kt⟩ => ?_
      have hv : Rep (point (env t.mem base) 0 1 2 3) ((2 ^ (4 - k) : Nat) • a) := by
        rw [kt.mem, vc, Point64.doubleRfcOps_eval]
        have := pointDouble_rep hi.value.proj
        rw [← two_nsmul, smul_smul, ← pow_succ', show 4 - (k + 1) + 1 = 4 - k by omega] at this
        exact this
      have hh : Outside base 64 512 b.mem t.mem := by rw [kt.mem]; exact hi.high.trans hc
      have hkeep : CombKeep base b t :=
        (hi.keep.trans (CombKeep.of_keep kc)).trans (CombKeep.of_keeps kt (by decide))
      by_cases hk0 : k = 0
      · subst hk0
        exact Or.inl ⟨by simp only [eval, read_x, htc, double4_counter 0 (by decide),
          show decide ((0 : Nat) ≠ 0) = false from rfl], hv, hh, hkeep⟩
      · exact Or.inr ⟨by simp only [eval, read_x, htc, double4_counter k (by omega),
          decide_eq_true hk0], k, by omega, ⟨by omega, by omega, hkeep.scr hsb, htc, hv, hh, hkeep⟩⟩
    · exact ⟨by decide, le_refl _, hsb, bc, by rw [eb]; simpa using hp, Outside.refl _ _ _ _,
        CombKeep.refl _ _⟩
  exact WP.mono hl fun t ⟨tv, th, tk⟩ => ⟨tv, by rw [← eb]; exact th, ksb.trans tk⟩

/-! ## A loop over the digits -/

/-- `Σ_{i < c} d_{2i + par} 256^i`. -/
def digitSum (S par : Nat) : Nat → ℤ
  | 0 => 0
  | c + 1 => digitSum S par c + sdig S (2 * c + par) * 256 ^ c

theorem digitSum_odd (S : Nat) : ∀ c, digitSum S 1 c = oddSumZ S c
  | 0 => rfl
  | c + 1 => by rw [digitSum, oddSumZ, digitSum_odd S c]

theorem digitSum_even (S : Nat) : ∀ c, digitSum S 0 c = evenSumZ S c
  | 0 => rfl
  | c + 1 => by rw [digitSum, evenSumZ, digitSum_even S c, Nat.add_zero]

/-- The loop's invariant, after `j` steps from `[v]B`. -/
structure CombInv (s₀ : State) (base : Addr) (S par : Nat) (v : ℤ) (j : Nat) (s : State) : Prop where
  bound : j ≤ 32
  scratch : Scr s base
  counter : s.gpr .x19 = BitVec.ofNat 64 j
  zero : env s.mem base 21 = 0
  bits : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)
  acc : Rep (point (env s.mem base) 0 1 2 3) ((v + digitSum S par j) • baseAff)
  keep : CombKeep base s₀ s

private theorem next_fact : ∀ j < 32,
    BitVec.ofNat 64 j + BitVec.ofNat 64 1 = BitVec.ofNat 64 (j + 1) ∧
    (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 32 != 0) = decide (j + 1 ≠ 32) := by decide +kernel

theorem combNext_ok (s : State) {j : Nat} (hj : j < 32) (h : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block [.addImm .x .x19 .x19 1, .subImm .x .x8 .x19 32]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (j + 1) ∧ (t.gpr .x8 != 0) = decide (j + 1 ≠ 32) ∧
      Keeps [.x19, .x8] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addImm_x (show 1 < 4096 by decide),
    exec_subImm_x (show 32 < 4096 by decide), read_x, RegUpd.gpr_write, BitVec.setWidth_eq, h,
    (next_fact j hj).1, (next_fact j hj).2, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

private theorem dis_neg : ∀ ab ∈ [((4 : Slot), (5 : Slot)), (6, 8)], ab.1 ≠ ab.2 := by
  intro ab hab; simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
  rcases hab with rfl | rfl <;> decide

theorem combStep_ok {s₀ s : State} {base T : Addr} {S par : Nat} {v : ℤ} {j : Nat}
    (h : CombInv s₀ base S par v j s) (htb : TblAt s₀ base T) (hT : s.syms combSym = T)
    (hj : j < 32) (hpar : par < 2) :
    WP isa (combStep (768 + 4 * par)) s fun t => (t.gpr .x8 != 0) = decide (j + 1 ≠ 32) ∧
      CombInv s₀ base S par v (j + 1) t := by
  rw [combStep]
  have hn := nib_lt S (2 * j + par)
  -- The digit's masks.
  refine WP.seq (WP.mono_syms (combDigit_ok h.scratch (i := 2 * j + par) hj (by omega) (by omega)
    (by omega) h.counter h.bits) fun a ha sya => ?_)
  have hsa : Scr a base := h.scratch.of_keeps ha.keeps (by decide)
  have a19 : a.gpr .x19 = BitVec.ofNat 64 j := (ha.keeps.gpr _ (by decide)).trans h.counter
  have hm : Masks (mag (nib S (2 * j + par))) a := ⟨ha.mask, ha.zero⟩
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
  refine WP.mono (combSelect_ok hsa hta (by rw [sya]; exact hT) hj a19 (mag_lt hn) hm)
    fun b ⟨bq, bf, kb⟩ => ?_
  have hsb : Scr b base := ⟨(kb.1 _ (by decide)).trans hsa.x0, kb.2.2.1 ▸ hsa.wr, hsa.nowrap⟩
  have b19 : b.gpr .x19 = BitVec.ofNat 64 j := (kb.1 _ (by decide)).trans a19
  have kab : CombKeep base a b := ⟨fun r _ _ hc => kb.1 r (fun hm => hc (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> decide)), kb.2.1, kb.2.2.1, kb.2.2.2,
    bf.mono (by simp only [offset]; omega) (by simp only [offset]; omega)⟩
  have ksb := ksa.trans kab
  have bbits : ∀ q < 256, b.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2) :=
    fun q hq => by rw [ksb.bit hq]; exact h.bits q hq
  have eb : ∀ i : Slot, (i.val < 4 ∨ 7 ≤ i.val) → env b.mem base i = env s.mem base i := fun i hi => by
    simp only [env, F]
    rw [bf.fe (by simp only [offset]; omega) (by simp only [offset]; omega), ha.keeps.mem]
  -- Negated for a negative digit.
  refine WP.mono (combNeg_ok hsb (S := S) (i := 2 * j + par) 4 5 6 hj (by omega) (by omega)
    (by omega) b19 bbits dis_neg) fun c ⟨kc, vc⟩ => ?_
  obtain ⟨q, hq, hqz, hrq⟩ := combEntry_ok j (nib S (2 * j + par)) hj hn
  have b21 : env b.mem base 21 = 0 := (eb 21 (by decide)).trans h.zero
  have cq : cachedAt (env c.mem base) 4 5 6 = cache q := by
    rw [vc, neg_env _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      b21, bq, ← hq]
    by_cases hlt : nib S (2 * j + par) < 8 <;> simp only [hlt, decide_true, decide_false, ↓reduceIte,
      Bool.false_eq_true]
  have ec : ∀ i : Slot, (i.val < 4 ∨ 9 ≤ i.val) → env c.mem base i = env b.mem base i := fun i hi => by
    rw [vc, neg_other _ _ _ _ _ i (fun e => by subst e; revert hi; decide)
      (fun e => by subst e; revert hi; decide) (fun e => by subst e; revert hi; decide)
      (fun e => by subst e; revert hi; decide)]
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
    rw [kt.mem, vd, Point64.addAffineOps_eval _ q hqz h4 h5 h6, pc, digitSum, ← add_assoc, add_smul]
    exact pointAdd_rep h.acc hrq

/-- The loop of the digits `2i + par`, from `[v]B`. -/
theorem combLoop_ok {s : State} {base T : Addr} (hs : Scr s base) (htb : TblAt s base T)
    (hT : s.syms combSym = T) {S par : Nat} (hpar : par < 2) {v : ℤ}
    (hz : env s.mem base 21 = 0)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2))
    (hv : Rep (point (env s.mem base) 0 1 2 3) (v • baseAff)) :
    WP isa (combLoop (768 + 4 * par)) s fun t => CombInv s base S par v 32 t := by
  rw [combLoop]
  refine WP.seq (WP.mono_syms (show WP isa (.block [.movz .w .x19 0 0]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 0 ∧ Keeps [.x19] s t by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
      show 16 * 0 < Size.w.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
    · rw [RegUpd.gpr_write_self]; rfl
    · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr))
    fun b ⟨b19, kb⟩ syb => ?_)
  have ksb : CombKeep base s b := CombKeep.of_keeps kb (by decide)
  have init : CombInv s base S par v 0 b :=
    ⟨by decide, hs.of_keeps kb (by decide), b19, by rw [kb.mem]; exact hz,
      fun q hq => by rw [kb.mem]; exact hb q hq,
      by rw [kb.mem, digitSum, add_zero]; exact hv, ksb⟩
  apply WP.loop (fun n (t : State) => (CombInv s base S par v (32 - n) t ∧ t.syms combSym = T) ∧
    0 < n ∧ n ≤ 32) (n := 32)
  · intro n t ⟨⟨ht, hty⟩, hn0, hn⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    refine WP.mono_syms (combStep_ok ht htb hty (by omega) hpar) fun u ⟨u8, hu⟩ suy => ?_
    by_cases hk : k = 0
    · subst hk
      exact Or.inl ⟨by simp only [eval, read_x, u8, show 32 - (0 + 1) + 1 = 32 from rfl, ne_eq,
        not_true_eq_false, decide_false], hu⟩
    · refine Or.inr ⟨by simp only [eval, read_x, u8, show 32 - (k + 1) + 1 ≠ 32 by omega, ne_eq,
        not_false_eq_true, decide_true], k, by omega, ⟨?_, by rw [suy]; exact hty⟩, by omega, by omega⟩
      rw [show 32 - k = 32 - (k + 1) + 1 by omega]; exact hu
  · exact ⟨⟨init, by rw [syb]; exact hT⟩, by decide, by decide⟩

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
  have hv : Rep (point (env a.mem base) 0 1 2 3) ((combStartVal : ℤ) • baseAff) := by
    rw [ap, natCast_zsmul]; exact combStart_ok
  -- The odd digits.
  refine WP.seq (WP.mono_syms (combLoop_ok (par := 1) hsa hta (by rw [sya]; exact hT) (by decide) az
    (fun q hq => by rw [ka.bit hq]; exact hb q hq) hv) fun b hb' syb => ?_)
  -- Four doublings.
  refine WP.seq (WP.mono_syms (double4_ok hb'.scratch hb'.acc) fun c ⟨cv, ch, kc⟩ syc => ?_)
  have hsc := kc.scr hb'.scratch
  have htc : TblAt c base T := hta.of_far (by rw [kc.rd, kc.wr, hb'.keep.rd, hb'.keep.wr])
    (fun x hx => by rw [kc.mem x (Or.inr (by omega)), hb'.keep.mem x (Or.inr (by omega))])
  have h16 : (((16 * combStartVal : Nat) : ℤ)) • baseAff = (((17 * combGVal : Nat) : ℤ)) • baseAff := by
    rw [natCast_zsmul, natCast_zsmul]; exact combStart_16
  have v16 : ((16 : Nat) • (((combStartVal : ℤ) + digitSum S 1 32) • baseAff)) =
      ((16 * ((combGVal : ℤ) + oddSumZ S 32) + combGVal) • baseAff) := by
    calc ((16 : Nat) • (((combStartVal : ℤ) + digitSum S 1 32) • baseAff))
        = (((16 * combStartVal : Nat) : ℤ) + 16 * oddSumZ S 32) • baseAff := by
          rw [← natCast_zsmul, smul_smul, digitSum_odd]; congr 1; push_cast; ring
      _ = (((17 * combGVal : Nat) : ℤ) + 16 * oddSumZ S 32) • baseAff := by rw [add_smul, add_smul, h16]
      _ = ((16 * ((combGVal : ℤ) + oddSumZ S 32) + combGVal) • baseAff) := by
          congr 1; push_cast; ring
  rw [v16] at cv
  -- The even digits.
  refine WP.mono (combLoop_ok (par := 0) hsc htc (by rw [syc, syb, sya]; exact hT) (by decide)
    (by rw [env_high ch 21 (by decide)]; exact hb'.zero)
    (fun q hq => by rw [kc.bit hq]; exact hb'.bits q hq) cv) fun t ht => ⟨?_, ?_⟩
  · have hu := ht.acc
    rw [digitSum_even, add_assoc, comb_total hS, natCast_zsmul] at hu
    exact hu
  · exact ((ka.trans hb'.keep).trans kc).trans ht.keep

end VG.Proof.Ed25519.AArch64
