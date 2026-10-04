import VerifiedGarbage.Proof.Ed25519.X86.CombDigit

/-!
# The comb's constant-time selection, for two digits at once

With the word at `combOddMasks + 4k` (`combEvenMasks + 4k`) all ones exactly
for `k` the odd (even) digit's magnitude, `selectWord` loads every nonzero
candidate word once, ANDs it with both digits' masks and ORs it into `ebx`
and `ebp`, so only each digit's candidate survives, and stores them.
-/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519 VG.Impl.Ed25519.X86 VG.Proof.Ed25519
open VG.Impl.X25519.X86 (sc)

/-- The masks of both digits' magnitudes `ao` and `ae`, in memory. -/
def Masks (x : BitVec 32) (ao ae : Nat) (m : Mem) : Prop :=
  (∀ k < 9, wd m x (combOddMasks + 4 * k) = mask (decide (ao = k)).toNat) ∧
  (∀ k < 9, wd m x (combEvenMasks + 4 * k) = mask (decide (ae = k)).toNat)

theorem or0 (v : BitVec 32) : v ||| 0 = v := by ext i; simp
theorem zor (v : BitVec 32) : 0 ||| v = v := by ext i; simp

theorem mask_and (v : BitVec 32) (b : Bool) : v &&& mask b.toNat = if b then v else 0 := by
  cases b
  · show v &&& mask 0 = 0
    rw [show mask 0 = 0 by decide]; ext i; simp
  · show v &&& mask 1 = v
    rw [show mask 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]

/-- The masks survive stores below them. -/
theorem Masks.frame {x : BitVec 32} {ao ae : Nat} {m m' : Mem} (h : Masks x ao ae m)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ d, 1024 ≤ d → d + 4 ≤ 1160 → ∀ r ∈ rs, (sub x d 4).Disjoint r) :
    Masks x ao ae m' :=
  ⟨fun k hk => (wd_frame hf (hd _ (by simp only [combOddMasks]; omega)
      (by simp only [combOddMasks]; omega))).trans (h.1 k hk),
    fun k hk => (wd_frame hf (hd _ (by simp only [combEvenMasks]; omega)
      (by simp only [combEvenMasks]; omega))).trans (h.2 k hk)⟩

theorem selectCand_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {ao ae : Nat}
    (hm : Masks x ao ae s.mem) (v : Spec.X25519.Fe) {k : Nat} (hk : k < 9) (w : Nat) :
    WP isa (.block (selectCand v k w)) s fun t =>
      t.gpr .ebx = s.gpr .ebx ||| (if ao = k then feWord v w else 0) ∧
      t.gpr .ebp = s.gpr .ebp ||| (if ae = k then feWord v w else 0) ∧
      Keep s t ∧ t.mem = s.mem := by
  unfold selectCand
  split
  · rename_i h0
    refine WP.block_nil ⟨?_, ?_, Keep.refl _, rfl⟩ <;> (split <;> simp only [h0, or0])
  · refine Wp.wp_movi fun s₁ h₁ => Wp.wp_mov fun s₂ h₂ => ?_
    have k₂ : Keep s s₂ := (updKeep h₁).trans (updKeep h₂)
    have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
    refine wp_andm (k₂.ctx hc).edi ((k₂.ctx hc).inRW (by simp only [combOddMasks]; omega) (by decide))
      fun s₃ h₃ => ?_
    have k₃ := k₂.trans (updKeep h₃)
    refine wp_andm (k₃.ctx hc).edi ((k₃.ctx hc).inRW (by simp only [combEvenMasks]; omega) (by decide))
      fun s₄ h₄ => Wp.wp_or fun s₅ h₅ => Wp.wp_or fun s₆ h₆ => WP.block_nil ?_
    have m₃ : s₃.mem = s.mem := by rw [h₃.mem, m₂]
    refine ⟨?_, ?_, k₃.trans ((updKeep h₄).trans ((updKeep h₅).trans (updKeep h₆))),
      by rw [h₆.mem, h₅.mem, h₄.mem, m₃]⟩
    · rw [h₆.other .ebx (by decide), h₅.gpr, h₄.other .ebx (by decide), h₄.other .eax (by decide),
        h₃.gpr, h₃.other .ebx (by decide), h₂.other .ebx (by decide), h₂.other .eax (by decide),
        h₁.gpr, h₁.other .ebx (by decide), m₂]
      change _ ||| (feWord v w &&& wd s.mem x (combOddMasks + 4 * k)) = _
      rw [hm.1 k hk, mask_and]
      by_cases e : ao = k <;> simp [e]
    · rw [h₆.gpr, h₅.other .ebp (by decide), h₅.other .edx (by decide), h₄.gpr,
        h₄.other .ebp (by decide), h₃.other .ebp (by decide), h₃.other .edx (by decide), h₂.gpr,
        h₂.other .ebp (by decide), h₁.gpr, h₁.other .ebp (by decide), m₃]
      change _ ||| (feWord v w &&& wd s.mem x (combEvenMasks + 4 * k)) = _
      rw [hm.2 k hk, mask_and]
      by_cases e : ae = k <;> simp [e]

/-- Word `w` of `vs[a]` after the candidates `k < n`, zero if `a ≥ n`. -/
def selWord (vs : List Spec.X25519.Fe) (a n w : Nat) : BitVec 32 :=
  if a < n then feWord (vs.getD a 0) w else 0

theorem sel_step (vs : List Spec.X25519.Fe) (a n w : Nat) :
    selWord vs a n w ||| (if a = n then feWord (vs.getD n 0) w else 0) = selWord vs a (n + 1) w := by
  unfold selWord
  by_cases h : a < n
  · simp only [h, ↓reduceIte, show a < n + 1 by omega, show ¬ a = n by omega, or0]
  · by_cases he : a = n
    · subst he
      simp only [h, ↓reduceIte, Nat.lt_succ_self, zor]
    · simp only [h, he, ↓reduceIte, show ¬ a < n + 1 by omega, or0]

theorem selectCands_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {ao ae : Nat}
    (hm : Masks x ao ae s.mem) (vs : List Spec.X25519.Fe) (w : Nat) :
    ∀ n ≤ 9, WP isa (.block ((List.range n).flatMap fun k => selectCand (vs.getD k 0) k w)) s
      fun t => t.gpr .ebx = s.gpr .ebx ||| selWord vs ao n w ∧
        t.gpr .ebp = s.gpr .ebp ||| selWord vs ae n w ∧ Keep s t ∧ t.mem = s.mem
  | 0, _ => WP.block_nil ⟨by simp only [selWord, Nat.not_lt_zero, ↓reduceIte, or0],
      by simp only [selWord, Nat.not_lt_zero, ↓reduceIte, or0], Keep.refl _, rfl⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (selectCands_ok hc hm vs w n (by omega)) fun t ⟨tb, tp, kt, mt⟩ => ?_)
    refine WP.mono (selectCand_ok (ao := ao) (ae := ae) (kt.ctx hc) (by rw [mt]; exact hm) _
      (by omega : n < 9) w)
      fun u ⟨ub, up, ku, mu⟩ => ⟨?_, ?_, kt.trans ku, mu.trans mt⟩
    · rw [ub, tb, BitVec.or_assoc, sel_step]
    · rw [up, tp, BitVec.or_assoc, sel_step]

theorem selectWord_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {ao ae : Nat}
    (hm : Masks x ao ae s.mem) (vs : List Spec.X25519.Fe) {o e : Nat} (ho : o + 32 ≤ 1024)
    (he : e + 32 ≤ 1024) (w : Nat) (hw : w < 8) :
    WP isa (.block (selectWord vs o e w)) s fun t => Keep s t ∧
      t.mem = (s.mem.writeW (addr x (o + 4 * w)) (selWord vs ao 9 w)).writeW (addr x (e + 4 * w))
        (selWord vs ae 9 w) := by
  rw [show selectWord vs o e w = .mov .ebx (.imm 0) :: .mov .ebp (.imm 0) ::
    ((List.range 9).flatMap (fun k => selectCand (vs.getD k 0) k w) ++
      ([.store (sc (o + 4 * w)) .ebx, .store (sc (e + 4 * w)) .ebp] : List Instr)) from rfl]
  refine Wp.wp_movi fun s₁ h₁ => Wp.wp_movi fun s₂ h₂ => ?_
  have k₂ : Keep s s₂ := (updKeep h₁).trans (updKeep h₂)
  have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  rw [WP.block_append_iff]
  refine WP.mono (selectCands_ok (ao := ao) (ae := ae) (k₂.ctx hc) (by rw [m₂]; exact hm) vs w 9
    (le_refl _))
    fun t ⟨tb, tp, kt, mt⟩ => ?_
  have k₃ := k₂.trans kt
  refine Wp.wp_stm (k₃.ctx hc).edi ((k₃.ctx hc).inW (by omega) (by decide)) fun u hu => ?_
  have ku : Keep t u := ⟨by rw [hu.gpr], by rw [hu.gpr], by rw [hu.gpr], hu.rd, hu.wr⟩
  refine Wp.wp_stm ((k₃.trans ku).ctx hc).edi (((k₃.trans ku).ctx hc).inW (by omega) (by decide))
    fun v hv => WP.block_nil ⟨k₃.trans (ku.trans ⟨by rw [hv.gpr], by rw [hv.gpr], by rw [hv.gpr],
      hv.rd, hv.wr⟩), ?_⟩
  rw [hv.mem, hu.mem, hu.gpr, mt, m₂, tb, tp, h₂.other .ebx (by decide), h₂.gpr, h₁.gpr, zor, zor]

/-- Two regions of the workspace (`[o, o + n)` and `[e, e + n)`) may change. -/
abbrev Frame2 (x : BitVec 32) (o e n : Nat) (m m' : Mem) : Prop := Frame [sub x o n, sub x e n] m m'

theorem selectFieldPrefix_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {ao ae : Nat}
    (hm : Masks x ao ae s.mem) (vs : List Spec.X25519.Fe) {o e : Nat} (ho : o + 32 ≤ 1024)
    (he : e + 32 ≤ 1024) (hoe : o + 32 ≤ e ∨ e + 32 ≤ o) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap fun w => selectWord vs o e w)) s fun t =>
      Keep s t ∧ Frame2 x o e 32 s.mem t.mem ∧
      ∀ w < n, wd t.mem x (o + 4 * w) = selWord vs ao 9 w ∧ wd t.mem x (e + 4 * w) = selWord vs ae 9 w
  | 0, _ => WP.block_nil ⟨Keep.refl _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    have hfit := hc.fit
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (selectFieldPrefix_ok hc hm vs ho he hoe n (by omega))
      fun t ⟨kt, ft, wt⟩ => ?_)
    have hmt : Masks x ao ae t.mem := hm.frame ft fun d h1 h2 r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_disj (by omega) (by omega) (Or.inr (by omega))
      · exact sub_disj (by omega) (by omega) (Or.inr (by omega))
    refine WP.mono (selectWord_ok (kt.ctx hc) hmt vs ho he n (by omega)) fun u ⟨ku, mu⟩ =>
      ⟨kt.trans ku, ?_, fun w hw => ?_⟩
    · rw [mu]
      refine (ft.writeW List.mem_cons_self _ ?_).writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ ?_
      · exact sub_contains (by omega) (by omega) (by omega) (by decide)
      · exact sub_contains (by omega) (by omega) (by omega) (by decide)
    · rw [mu]
      by_cases hwn : w = n
      · subst hwn
        refine ⟨?_, wd_write_self _ _ _ _⟩
        rw [wd_write_ne _ _ (by omega) (by omega) (by omega), wd_write_self]
      · have hwl : w < n := by omega
        rw [wd_write_ne _ _ (by omega) (by omega) (by omega), wd_write_ne _ _ (by omega) (by omega)
          (by omega), wd_write_ne _ _ (by omega) (by omega) (by omega),
          wd_write_ne _ _ (by omega) (by omega) (by omega)]
        exact wt w hwl

theorem feWord_num (v : Spec.X25519.Fe) :
    num (fun w => (feWord v w).toNat) 8 = v.val := by
  rw [num_congr (g := fun k => v.val / (2 ^ 32) ^ k % 2 ^ 32) (fun k _ => by
    simp only [feWord, BitVec.toNat_ofNat]), num_digits]
  exact Nat.mod_eq_of_lt (by have h := v.isLt; simp only [Spec.X25519.P] at h; omega)

theorem selectField_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {ao ae : Nat} (hao : ao < 9)
    (hae : ae < 9) (hm : Masks x ao ae s.mem) (vs : List Spec.X25519.Fe) {o e : Nat}
    (ho : o + 32 ≤ 1024) (he : e + 32 ≤ 1024) (hoe : o + 32 ≤ e ∨ e + 32 ≤ o) :
    WP isa (.block (selectField vs o e)) s fun t =>
      Keep s t ∧ Frame2 x o e 32 s.mem t.mem ∧
      VG.Proof.X25519.X86.F t.mem x o = vs.getD ao 0 ∧ VG.Proof.X25519.X86.F t.mem x e = vs.getD ae 0 := by
  refine WP.mono (selectFieldPrefix_ok hc hm vs ho he hoe 8 (le_refl _)) fun t ⟨kt, ft, wt⟩ =>
    ⟨kt, ft, ?_, ?_⟩
  · have hf : fe t.mem x o = (vs.getD ao 0).val := by
      unfold fe
      rw [← feWord_num]
      refine num_congr fun w hw => ?_
      show (wd t.mem x (o + 4 * w)).toNat = _
      rw [(wt w hw).1, selWord]; simp only [hao, ↓reduceIte]
    rw [VG.Proof.X25519.X86.F, hf, VG.Proof.X25519.toFe_self]
  · have hf : fe t.mem x e = (vs.getD ae 0).val := by
      unfold fe
      rw [← feWord_num]
      refine num_congr fun w hw => ?_
      show (wd t.mem x (e + 4 * w)).toNat = _
      rw [(wt w hw).2, selWord]; simp only [hae, ↓reduceIte]
    rw [VG.Proof.X25519.X86.F, hf, VG.Proof.X25519.toFe_self]

theorem Frame2.F {x : BitVec 32} {o e q : Nat} {m m' : Mem} (h : Frame2 x o e 32 m m')
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (ho : o + 32 ≤ 8192) (he : e + 32 ≤ 8192) (hq : q + 32 ≤ 8192)
    (h1 : q + 32 ≤ o ∨ o + 32 ≤ q) (h2 : q + 32 ≤ e ∨ e + 32 ≤ q) :
    VG.Proof.X25519.X86.F m' x q = VG.Proof.X25519.X86.F m x q :=
  congrArg VG.Proof.X25519.toFe (fe_frame fun k hk => wd_frame h fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj (by omega) (by omega) (by omega)
    · exact sub_disj (by omega) (by omega) (by omega))

theorem Frame2.widen {x : BitVec 32} {o e o' e' : Nat} {m m' : Mem} (h : Frame2 x o e 32 m m')
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (h1 : o' ≤ o) (h2 : o + 32 ≤ o' + 96) (h3 : e' ≤ e)
    (h4 : e + 32 ≤ e' + 96) (ho : o < 8192) (he : e < 8192) :
    Frame [sub x o' 96, sub x e' 96] m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, sub_sub hx h1 h2 ho⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, sub_sub hx h3 h4 he⟩

/-- The cached point in slots `a`, `b`, `c`, with `2Z = 2`. -/
def cachedAt (e : Env) (a b c : Slot) : Spec.Ed25519.Point := ⟨e a, e b, e c, 2⟩

private theorem entries_getD (j a : Nat) (ha : a < 9) (f : Spec.Ed25519.Point → Spec.X25519.Fe) :
    (((List.range 9).map (combCached j)).map f).getD a 0 = f (combCached j a) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ha, Option.map_some,
    Option.getD_some]

theorem combCached_T (j a : Nat) : (combCached j a).T = 2 := by
  unfold combCached
  split
  · rfl
  · split; rfl

theorem cachedAt_eq {e : Env} {a b c : Slot} {q : Spec.Ed25519.Point} (hq : q.T = 2)
    (ha : e a = q.X) (hb : e b = q.Y) (hc : e c = q.Z) : cachedAt e a b c = q := by
  cases q
  simp only [cachedAt, ha, hb, hc] at hq ⊢
  rw [hq]

/-- The selection's frame: slots 4–6 and 13–15. -/
abbrev SelFrame (x : BitVec 32) (m m' : Mem) : Prop := Frame [sub x (offset 4) 96, sub x (offset 13) 96] m m'

theorem combSelect_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {ao ae : Nat} (hao : ao < 9)
    (hae : ae < 9) (hm : Masks x ao ae s.mem) (j : Nat) :
    WP isa (.block (combSelect j)) s fun t =>
      cachedAt (env t.mem x) 4 5 6 = combCached j ao ∧
      cachedAt (env t.mem x) 13 14 15 = combCached j ae ∧ Keep s t ∧ SelFrame x s.mem t.mem := by
  have hfit := hc.fit
  have mf : ∀ {m m' : Mem} {o e : Nat}, Masks x ao ae m → Frame2 x o e 32 m m' → o + 32 ≤ 1024 →
      e + 32 ≤ 1024 → Masks x ao ae m' := fun hm f ho he => hm.frame f fun d h1 h2 r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj (by omega) (by omega) (Or.inr (by omega))
    · exact sub_disj (by omega) (by omega) (Or.inr (by omega))
  rw [combSelect]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (selectField_ok hc hao hae hm _ (o := offset 4) (e := offset 13) (by decide) (by decide)
    (by decide)) fun b ⟨kb, fb, b4, b13⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (selectField_ok (kb.ctx hc) hao hae (mf hm fb (by decide) (by decide)) _ (o := offset 5)
    (e := offset 14) (by decide) (by decide) (by decide)) fun c ⟨kc, fc, c5, c14⟩ => ?_
  refine WP.mono (selectField_ok ((kb.trans kc).ctx hc) hao hae
    (mf (mf hm fb (by decide) (by decide)) fc (by decide) (by decide)) _ (o := offset 6) (e := offset 15)
    (by decide) (by decide) (by decide)) fun t ⟨kt, ft, t6, t15⟩ => ⟨?_, ?_, (kb.trans kc).trans kt, ?_⟩
  · rw [entries_getD j ao hao] at b4 c5 t6
    refine cachedAt_eq (combCached_T j ao) ?_ ?_ t6
    · change VG.Proof.X25519.X86.F t.mem x (offset 4) = _
      rw [ft.F hfit (by decide) (by decide) (by decide) (by decide) (by decide),
        fc.F hfit (by decide) (by decide) (by decide) (by decide) (by decide), b4]
    · change VG.Proof.X25519.X86.F t.mem x (offset 5) = _
      rw [ft.F hfit (by decide) (by decide) (by decide) (by decide) (by decide), c5]
  · rw [entries_getD j ae hae] at b13 c14 t15
    refine cachedAt_eq (combCached_T j ae) ?_ ?_ t15
    · change VG.Proof.X25519.X86.F t.mem x (offset 13) = _
      rw [ft.F hfit (by decide) (by decide) (by decide) (by decide) (by decide),
        fc.F hfit (by decide) (by decide) (by decide) (by decide) (by decide), b13]
    · change VG.Proof.X25519.X86.F t.mem x (offset 14) = _
      rw [ft.F hfit (by decide) (by decide) (by decide) (by decide) (by decide), c14]
  · exact ((fb.widen hfit (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (fc.widen hfit (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))).trans
      (ft.widen hfit (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))

theorem combSelectFrom_ok (ks : List Nat) (hks : ∀ k ∈ ks, k < 32) {x : BitVec 32} {s : State}
    (hc : Ctx x s) {ao ae : Nat} (hao : ao < 9) (hae : ae < 9) (hm : Masks x ao ae s.mem)
    {j : Nat} (hj : j ∈ ks) (hj32 : j < 32) (hesi : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (combSelectFrom ks) s fun t =>
      cachedAt (env t.mem x) 4 5 6 = combCached j ao ∧
      cachedAt (env t.mem x) 13 14 15 = combCached j ae ∧ Keep s t ∧ SelFrame x s.mem t.mem := by
  induction ks generalizing s with
  | nil => exact absurd hj List.not_mem_nil
  | cons k ks ih =>
    have hk : k < 32 := hks k List.mem_cons_self
    rw [combSelectFrom]
    have hcmp : WP isa (.block [.alu .cmp .esi (.imm (BitVec.ofNat 32 k))]) s fun t =>
        Keep s t ∧ t.mem = s.mem ∧ t.zf = some (decide (j = k)) :=
      Wp.wp_cmpi fun t ht _ zt => WP.block_nil ⟨⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd,
        ht.wr⟩, ht.mem, by rw [zt, hesi, Wp.sub_beq (by omega) (by omega)]⟩
    refine WP.seq (WP.mono hcmp fun t ⟨kt, mt, zt⟩ => ?_)
    have ct := kt.ctx hc
    have hmt : Masks x ao ae t.mem := by rw [mt]; exact hm
    refine WP.ite (decide (j = k)) zt (fun h => ?_) (fun h => ?_)
    · obtain rfl : j = k := of_decide_eq_true h
      refine WP.mono (combSelect_ok ct hao hae hmt j) fun u ⟨u1, u2, ku, fu⟩ =>
        ⟨u1, u2, kt.trans ku, by rw [← mt]; exact fu⟩
    · have hne : j ≠ k := of_decide_eq_false h
      have hj' : j ∈ ks := by
        rcases List.mem_cons.mp hj with h | h
        · exact absurd h hne
        · exact h
      refine WP.mono (ih (fun k hk => hks k (List.mem_cons_of_mem _ hk)) ct hmt hj'
        (by rw [kt.esi]; exact hesi)) fun u ⟨u1, u2, ku, fu⟩ =>
        ⟨u1, u2, kt.trans ku, by rw [← mt]; exact fu⟩

end VG.Proof.Ed25519.X86
