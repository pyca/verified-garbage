module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointTable
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.PointMul
public import VerifiedGarbage.Proof.Ed25519.ScalarMul
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Ed25519 on PPC64LE: doublings and tables of powers

`doubleCall_ok`: the point of slots 0–3 doubled (`p + p`). `double16_ok`:
doubled 16 times in a loop counted by `r15`, `powerPoint p 16`.
`pointPowers_ok`: the table at `start` filled with `powerPoint p (stride j)`
for `j < count`, the point doubled `stride` times between entries.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Proof.Ed25519 (powerPoint)

/-- Code that keeps the registers outside `R` and the memory outside the field area, maps the
point of slots 0–3 by `f` and keeps slot 16 and above. -/
def PtSpec (b : Addr) (R : List Reg) (c : Prog isa) (f : Spec.Ed25519.Point → Spec.Ed25519.Point) : Prop :=
  ∀ s, Ctx8 b s → env s.mem b 16 = Spec.Ed25519.d → WP isa c s fun t =>
    Rest R s t ∧ Frame [FA b] s.mem t.mem ∧ point (env t.mem b) 0 1 2 3 = f (point (env s.mem b) 0 1 2 3) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s.mem b i

theorem env_copyPointToQ (e : Env) : point (evalOps copyPointToQOps e) 4 5 6 7 = point e 0 1 2 3 ∧
    point (evalOps copyPointToQOps e) 0 1 2 3 = point e 0 1 2 3 ∧
    ∀ i : Slot, 8 ≤ i.val → evalOps copyPointToQOps e i = e i := by
  refine ⟨rfl, rfl, fun i hi => ?_⟩
  simp only [evalOps, copyPointToQOps, List.foldl, evalOp, Function.update_apply]
  have h4 : i ≠ 4 := fun h => by subst h; exact absurd hi (by decide)
  have h5 : i ≠ 5 := fun h => by subst h; exact absurd hi (by decide)
  have h6 : i ≠ 6 := fun h => by subst h; exact absurd hi (by decide)
  have h7 : i ≠ 7 := fun h => by subst h; exact absurd hi (by decide)
  simp only [h4, h5, h6, h7, ite_false]

theorem doubleCall_ok (b : Addr) : PtSpec b fclob doubleCall fun p => Spec.Ed25519.pointAdd p p := by
  intro s hc hd
  unfold doubleCall copyPointToQ
  refine WP.seq (WP.mono (fieldCode_ok copyPointToQOps hc.ctx) fun t ⟨kt, et⟩ => ?_)
  obtain ⟨q4, q0, qk⟩ := env_copyPointToQ (env s.mem b)
  rw [← et] at q4 q0 qk
  refine WP.mono (addCall_ok (hc.of_keep kt) (by rw [qk 16 (by decide), hd])) fun u ⟨ku, pu, keu⟩ =>
    ⟨kt.rest.trans ku.rest, kt.frame.trans ku.frame, by rw [pu, q4, q0], fun i hi => ?_⟩
  rw [keu i (.inr hi), qk i (by omega)]

theorem PtSpec.seq {b : Addr} {R : List Reg} {c₁ c₂ : Prog isa} {f g : Spec.Ed25519.Point → Spec.Ed25519.Point}
    (h₁ : PtSpec b R c₁ f) (h₂ : PtSpec b R c₂ g) (h6 : Reg.r6 ∉ R) : PtSpec b R (.seq c₁ c₂) (g ∘ f) :=
  fun s hc hd => WP.seq (WP.mono (h₁ s hc hd) fun t ⟨r1, f1, p1, k1⟩ =>
    WP.mono (h₂ t (hc.of_rest r1 h6) (by rw [k1 16 (by decide), hd])) fun u ⟨r2, f2, p2, k2⟩ =>
      ⟨r1.trans r2, f1.trans f2, by rw [p2, p1]; rfl, fun i hi => by rw [k2 i hi, k1 i hi]⟩)

theorem PtSpec.mono {b : Addr} {R R' : List Reg} {c : Prog isa} {f : Spec.Ed25519.Point → Spec.Ed25519.Point}
    (h : PtSpec b R c f) (hR : ∀ r ∈ R, r ∈ R') : PtSpec b R' c f :=
  fun s hc hd => WP.mono (h s hc hd) fun _ ⟨r, fr, p, k⟩ => ⟨r.mono hR, fr, p, k⟩

theorem powerPoint_succ' (p : Spec.Ed25519.Point) (n : Nat) :
    powerPoint p (n + 1) = Spec.Ed25519.pointAdd (powerPoint p n) (powerPoint p n) := rfl

/-- Sixteen doublings, counted by `r15`. -/
theorem double16_ok (b : Addr) : PtSpec b (.r15 :: fclob) double16 fun p => powerPoint p 16 := by
  intro s hc hd
  unfold double16
  refine WP.seq (wp_li (by decide) fun s1 u1 => WP.block_nil ?_)
  have hc1 : Ctx8 b s1 := hc.of_rest (u1.rest (ws := [.r15]) (by decide)) (by decide)
  refine WP.loop (M := isa) (fun n t => 1 ≤ n ∧ n ≤ 16 ∧ Rest (.r15 :: fclob) s t ∧ Frame [FA b] s.mem t.mem ∧
      t.gpr .r15 = BitVec.ofNat 64 n ∧ point (env t.mem b) 0 1 2 3 = powerPoint (point (env s.mem b) 0 1 2 3) (16 - n) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s.mem b i) ?_ 16 s1
    ⟨by decide, by decide, u1.rest (by decide), by rw [u1.mem]; exact Frame.refl _ _, u1.gpr,
      by rw [u1.mem]; rfl, fun i _ => by rw [u1.mem]⟩
  rintro n t ⟨h1, h2, hr, hf, h15, hp, hk⟩
  have hct : Ctx8 b t := hc.of_rest hr (by decide)
  unfold doubleBody
  refine WP.seq (WP.mono (doubleCall_ok b t hct (by rw [hk 16 (by decide), hd])) fun u ⟨ru, fu, pu, ku⟩ => ?_)
  refine wp_subi (by decide) (by decide) fun u1 v1 => WP.block_nil ?_
  have e15 : u1.gpr .r15 = BitVec.ofNat 64 (n - 1) := by
    rw [v1.gpr, ru.gpr _ (by decide), h15, ofNat_sub_one h1 (by omega)]
  have hz : (u1.gpr .r15 != 0) = decide (n - 1 ≠ 0) := by rw [e15, ofNat_ne_zero (by omega)]
  have hp' : point (env u1.mem b) 0 1 2 3 = powerPoint (point (env s.mem b) 0 1 2 3) (16 - (n - 1)) := by
    rw [v1.mem, pu, hp, show 16 - (n - 1) = 16 - n + 1 by omega]; rfl
  have hr' : Rest (.r15 :: fclob) s u1 := hr.trans ((ru.mono (by decide)).trans (v1.rest (by decide)))
  have hf' : Frame [FA b] s.mem u1.mem := by rw [v1.mem]; exact hf.trans fu
  have hk' : ∀ i : Slot, 16 ≤ i.val → env u1.mem b i = env s.mem b i := fun i hi => by
    rw [v1.mem, ku i hi, hk i hi]
  rw [eval_nonzero, hz]
  by_cases h0 : n - 1 = 0
  · refine .inl ⟨by simp [h0], hr', hf', ?_, hk'⟩
    rw [hp', h0]
  · exact .inr ⟨by simp [h0], n - 1, by omega, by omega, by omega, hr', hf', e15, hp', hk'⟩

/-- A table entry outside a frame's regions keeps its point. -/
theorem tableAt_keep {b : Addr} {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {o : Nat}
    (hd : ∀ r ∈ rs, (⟨b + BitVec.ofNat 64 o, 128⟩ : Region).Disjoint r) : tableAt m' b o = tableAt m b o := by
  have h : ∀ c < 4, V m' b (o + 32 * c) = V m b (o + 32 * c) := fun c hc => by
    unfold V
    exact val32_congr (limb_frame hf fun r hr k hk =>
      (hd r hr).sub_left (Offset.sub b (d := o + 32 * c + 4 * k) (n := 4) (e := o) (k := 128) (by omega) (by omega)))
  simp only [tableAt, FS]
  rw [← Nat.add_zero o, ← Nat.mul_zero 32, h 0 (by decide), Nat.mul_zero, Nat.add_zero,
    show o + 32 = o + 32 * 1 from rfl, h 1 (by decide), show o + 64 = o + 32 * 2 from rfl, h 2 (by decide),
    show o + 96 = o + 32 * 3 from rfl, h 3 (by decide)]

/-- A slot outside a frame's regions keeps its element. -/
theorem env_keep {b : Addr} {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (i : Slot)
    (hd : ∀ r ∈ rs, (⟨b + BitVec.ofNat 64 (offset i), 32⟩ : Region).Disjoint r) : env m' b i = env m b i := by
  have := slot_range i
  unfold env FS V
  exact congrArg _ (val32_congr (limb_frame hf fun r hr k hk =>
    (hd r hr).sub_left (Offset.sub b (d := offset i + 4 * k) (n := 4) (e := offset i) (k := 32) (by omega) (by omega))))

/-- `r14` at entry `n` of the table at `start`. -/
theorem tableAddr_ok {b : Addr} {s : State} (hc : Ctx8 b s) {start n : Nat} (hs : start < 2 ^ 15) (hn : n < 64)
    (h16 : s.gpr .r16 = BitVec.ofNat 64 n) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Rest [.r7, .r14] s t → t.mem = s.mem → t.gpr .r14 = b + BitVec.ofNat 64 (start + 128 * n) →
      WP isa (.block is) t Q) :
    WP isa (.block (tableAddr start ++ is)) s Q := by
  unfold tableAddr
  simp only [List.cons_append, List.nil_append]
  refine wp_addi (by decide) hs fun s1 u1 => wp_lsl (by decide) fun s2 u2 => wp_add fun s3 u3 => ?_
  refine k s3 ((u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide))))
    (by rw [u3.mem, u2.mem, u1.mem]) ?_
  rw [u3.gpr, u2.gpr, u2.other _ (by decide), u1.gpr, u1.other _ (by decide), hc.r6, h16, BitVec.add_assoc,
    show BitVec.ofNat 64 n <<< 7 = BitVec.ofNat 64 (128 * n) by
      apply BitVec.eq_of_toNat_eq
      rw [toNat_shl, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
      omega, BitVec.ofNat_add]

theorem ofNat_sub_ne_zero {a c : Nat} (ha : a < 2 ^ 64) (hc : c < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 c != 0) = decide (a ≠ c) := by
  by_cases h : a = c
  · subst h; simp
  · have : BitVec.ofNat 64 a - BitVec.ofNat 64 c ≠ 0 := fun e => h (by
      have e' : BitVec.ofNat 64 a = BitVec.ofNat 64 c := by
        rw [← BitVec.sub_add_cancel (BitVec.ofNat 64 a) (BitVec.ofNat 64 c), e]; simp
      have := congrArg BitVec.toNat e'
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc] at this)
    rw [bne_iff_ne.mpr this]
    simp [h]

/-- The point doubled `stride` times: `double16` or one `doubleCall`. -/
theorem powerBatch_ok (b : Addr) (batch : Bool) :
    PtSpec b (.r15 :: fclob) (powerBatch batch) fun p => powerPoint p (powerStride batch) := by
  cases batch
  · exact (doubleCall_ok b).mono (by decide)
  · exact double16_ok b

/-- While filling the table at `start` from `s0`, for the point `p`: `n` entries written. -/
structure PowInv (b : Addr) (start count stride : Nat) (s0 : State) (p : Spec.Ed25519.Point) (n : Nat)
    (s : State) : Prop where
  lt : n < count
  ctx : Ctx8 b s
  rest : Rest (.r7 :: .r14 :: .r15 :: .r16 :: fclob) s0 s
  frame : Frame [FA b, ⟨b + BitVec.ofNat 64 start, 128 * count⟩] s0.mem s.mem
  r16 : s.gpr .r16 = BitVec.ofNat 64 n
  point : point (env s.mem b) 0 1 2 3 = powerPoint p (stride * n)
  table : ∀ j < n, tableAt s.mem b (start + 128 * j) = powerPoint p (stride * j)
  keep : ∀ i : Slot, 16 ≤ i.val → env s.mem b i = env s0.mem b i

/-- **A table of powers**. -/
theorem pointPowers_ok {b : Addr} {s : State} (hc : Ctx8 b s) (hd : env s.mem b 16 = Spec.Ed25519.d)
    {start count : Nat} (batch : Bool) (hs : 1024 ≤ start) (hs' : start + 128 * count ≤ 8192)
    (hc1 : 1 ≤ count) :
    WP isa (pointPowers start count batch) s fun t =>
      Rest (.r7 :: .r14 :: .r15 :: .r16 :: fclob) s t ∧
      Frame [FA b, ⟨b + BitVec.ofNat 64 start, 128 * count⟩] s.mem t.mem ∧
      (∀ j < count, tableAt t.mem b (start + 128 * j) =
        powerPoint (point (env s.mem b) 0 1 2 3) (powerStride batch * j)) ∧
      point (env t.mem b) 0 1 2 3 = powerPoint (point (env s.mem b) 0 1 2 3) (powerStride batch * count) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s.mem b i := by
  have hS : start < 2 ^ 15 := by omega
  have hC : count < 64 := by omega
  unfold pointPowers
  refine WP.seq (wp_li (by decide) fun s1 u1 => WP.block_nil ?_)
  refine WP.loop (M := isa) (fun m t => ∃ n, m = count - n ∧
      PowInv b start count (powerStride batch) s (point (env s.mem b) 0 1 2 3) n t) ?_ count s1
    ⟨0, by omega, by omega, hc.of_rest (u1.rest (ws := [.r16]) (by decide)) (by decide), u1.rest (by decide),
      by rw [u1.mem]; exact Frame.refl _ _, u1.gpr, by rw [u1.mem]; rfl, fun j hj => by omega,
      fun i _ => by rw [u1.mem]⟩
  rintro m t ⟨n, rfl, h⟩
  have hn := h.lt
  unfold powersBody
  refine WP.seq (tableAddr_ok h.ctx hS (by omega) h.r16 fun t1 r1 m1 e14 => ?_)
  have hc1' : Ctx8 b t1 := h.ctx.of_rest r1 (by decide)
  refine WP.mono (pointToTable_ok hc1' e14 (by omega) (by omega)) fun t2 ⟨r2, f2, tb2⟩ => ?_
  rw [m1] at tb2 f2
  have hc2 : Ctx8 b t2 := hc1'.of_rest r2 (by decide)
  have hd2 : env t2.mem b 16 = Spec.Ed25519.d := by
    have := slot_range (16 : Slot)
    unfold env FS V
    rw [← hd, ← h.keep 16 (by decide)]
    refine congrArg _ (val32_congr (limb_frame f2 fun r hr k hk => ?_))
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by simp only [offset] at *; omega)) (by omega) (by omega)
  refine WP.seq (WP.mono (powerBatch_ok b batch t2 hc2 hd2) fun t3 ⟨r3, f3, p3, k3⟩ => ?_)
  have hc3 : Ctx8 b t3 := hc2.of_rest r3 (by decide)
  unfold powersNext
  refine wp_addi (by decide) (by decide) fun t4 u4 => wp_subi (by decide) (by omega) fun t5 u5 => WP.block_nil ?_
  have e16 : t5.gpr .r16 = BitVec.ofNat 64 (n + 1) := by
    rw [u5.other _ (by decide), u4.gpr, r3.gpr _ (by decide), r2.gpr _ (by decide), r1.gpr _ (by decide), h.r16,
      BitVec.ofNat_add]
  have e7 : (t5.gpr .r7 != 0) = decide (n + 1 ≠ count) := by
    rw [u5.gpr, u4.gpr, r3.gpr _ (by decide), r2.gpr _ (by decide), r1.gpr _ (by decide), h.r16,
      show BitVec.ofNat 64 n + BitVec.ofNat 64 1 = BitVec.ofNat 64 (n + 1) from (BitVec.ofNat_add _ _).symm,
      ofNat_sub_ne_zero (by omega) (by omega)]
  have hm5 : t5.mem = t3.mem := by rw [u5.mem, u4.mem]
  have hFA : ∀ o, start ≤ o → o + 128 ≤ start + 128 * count →
      (⟨b + BitVec.ofNat 64 o, 128⟩ : Region).Disjoint (FA b) := fun o h1 h2 =>
    Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  have hpt : point (env t2.mem b) 0 1 2 3 = point (env t.mem b) 0 1 2 3 := by
    have e : ∀ i : Slot, env t2.mem b i = env t.mem b i := fun i => by
      refine env_keep f2 i fun r hr => ?_
      rw [List.mem_singleton.mp hr]
      have := slot_range i
      exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
    simp only [point, e]
  have hR : Rest (.r7 :: .r14 :: .r15 :: .r16 :: fclob) s t5 :=
    h.rest.trans ((r1.mono (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest (by decide))))))
  have hF : Frame [FA b, ⟨b + BitVec.ofNat 64 start, 128 * count⟩] s.mem t5.mem := by
    rw [hm5]
    refine h.frame.trans ((f2.sub fun r hr => ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩).trans
      (f3.mono fun r hr => by simp [List.mem_singleton.mp hr]))
    rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)
  have hP : point (env t5.mem b) 0 1 2 3 = powerPoint (point (env s.mem b) 0 1 2 3) (powerStride batch * (n + 1)) := by
    rw [hm5, p3, hpt, h.point]
    dsimp only
    rw [← Proof.Ed25519.powerPoint_add, Nat.mul_succ]
  have hT : ∀ j < n + 1, tableAt t5.mem b (start + 128 * j) =
      powerPoint (point (env s.mem b) 0 1 2 3) (powerStride batch * j) := by
    intro j hj
    rw [hm5, tableAt_keep f3 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hFA _ (by omega) (by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [tableAt_keep f2 fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega) (by omega) (by omega)]
      exact h.table j hj
    · rw [tb2, h.point]
  have hK : ∀ i : Slot, 16 ≤ i.val → env t5.mem b i = env s.mem b i := fun i hi => by
    rw [hm5, k3 i hi, ← h.keep i hi]
    refine env_keep f2 i fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    have := slot_range i
    exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  rw [eval_nonzero, e7]
  by_cases hl : n + 1 = count
  · refine .inl ⟨by simp [hl], hR, hF, fun j hj => hT j (by omega), by rw [hP, hl], hK⟩
  · exact .inr ⟨by simp [hl], count - (n + 1), by omega, n + 1, rfl,
      ⟨by omega, hc3.of_rest ((u4.rest (ws := [.r7, .r16]) (by decide)).trans (u5.rest (by decide))) (by decide), hR, hF, e16, hP, hT,
        hK⟩⟩

end VG.Proof.Ed25519.PPC64LE
