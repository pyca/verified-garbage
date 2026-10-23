module

import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointPowers
import VerifiedGarbage.Proof.X25519.PPC64LE.Cswap
import VerifiedGarbage.Proof.Framework.Offset
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.PointMul
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointTable
public import VerifiedGarbage.Proof.Framework.Block

/-!
# Ed25519 on PPC64LE: adding a power if its bit is set

`pointAccumulate` with `r16 = i`: the accumulator of slots 0–3, plus entry
`i` of the table at 5728, kept if byte `BITSB + i` is 1 and discarded (the
accumulator saved in slots 17–20 selected back by a mask) if it is 0
(`pointAccumulate_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE

section
variable {b : Addr}

theorem env_savePoint (e : Env) : point (evalOps savePointOps e) 17 18 19 20 = point e 0 1 2 3 ∧
    point (evalOps savePointOps e) 0 1 2 3 = point e 0 1 2 3 ∧ evalOps savePointOps e 16 = e 16 := ⟨rfl, rfl, rfl⟩

theorem env_restorePoint (e : Env) : point (evalOps restorePointOps e) 0 1 2 3 = point e 17 18 19 20 ∧
    point (evalOps restorePointOps e) 17 18 19 20 = point e 17 18 19 20 ∧ evalOps restorePointOps e 16 = e 16 ∧
    point (evalOps restorePointOps e) 4 5 6 7 = point e 4 5 6 7 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem env_copyQ (e : Env) : point (evalOps copyPointToQOps e) 4 5 6 7 = point e 0 1 2 3 ∧
    point (evalOps copyPointToQOps e) 0 1 2 3 = point e 0 1 2 3 ∧
    point (evalOps copyPointToQOps e) 17 18 19 20 = point e 17 18 19 20 ∧ evalOps copyPointToQOps e 16 = e 16 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The mask of the bit at `BITSB + i`. -/
theorem scalarBitMask_ok {s : State} (hc : Ctx8 b s) {i : Nat} (hi : i < 16) (h16 : s.gpr .r16 = BitVec.ofNat 64 i)
    {w : Nat} (hw : w ≤ 1) (hb : (s.mem (b + BitVec.ofNat 64 (BITSB + i))).toNat = w)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Rest [.r7, .r11] s t → t.mem = s.mem → t.gpr .r11 = 0 - BitVec.ofNat 64 (1 - w) → WP isa (.block is) t Q) :
    WP isa (.block (scalarBitMask ++ is)) s Q := by
  unfold scalarBitMask
  simp only [List.cons_append, List.nil_append]
  refine wp_add fun s1 u1 => ?_
  refine wp_lbz (a := b + BitVec.ofNat 64 (BITSB + i)) (by decide) (by decide)
    (by rw [u1.gpr, hc.r6, h16, BitVec.add_assoc, BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 i)]) (by
      rw [u1.rd, u1.wr]; exact hc.inR (by simp only [BITSB]; omega)) fun s2 u2 => ?_
  refine wp_subi (by decide) (by decide) fun s3 u3 => k s3
    ((u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide))))
    (by rw [u3.mem, u2.mem, u1.mem]) ?_
  rw [u3.gpr, u2.gpr, u1.mem, hb]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hw with rfl | rfl <;> decide

theorem sel_V {m m' : Mem} {a c : Nat} {sw : Nat} (hsw : sw ≤ 1)
    (h : ∀ j < 8, limb m' b a j = sel sw (limb m b a j) (limb m b c j)) :
    V m' b a = sel sw (V m b a) (V m b c) := by
  unfold V
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
  · exact val32_congr fun j hj => by rw [h j hj]; rfl
  · exact val32_congr fun j hj => by rw [h j hj]; rfl

theorem sel_toFe {sw : Nat} {x y : Nat} : Proof.X25519.toFe (sel sw x y) = sel sw (Proof.X25519.toFe x) (Proof.X25519.toFe y) := by
  unfold sel; split <;> rfl

/-- A conditional swap of two slots, by the mask `0 - sw` in `r11`. -/
theorem cswapSlot_ok {s : State} (hc : Ctx8 b s) {sw : Nat} (hsw : sw ≤ 1) (h11 : s.gpr .r11 = 0 - BitVec.ofNat 64 sw)
    (a c : Slot) (hac : a ≠ c) :
    WP isa (.block (cswap (offset a) (offset c))) s fun t =>
      Rest [.r5, .r7, .r8] s t ∧ Frame [FA b] s.mem t.mem ∧
      env t.mem b a = sel sw (env s.mem b a) (env s.mem b c) ∧ env t.mem b c = sel sw (env s.mem b c) (env s.mem b a) ∧
      ∀ i : Slot, i ≠ a → i ≠ c → env t.mem b i = env s.mem b i := by
  have ha := slot_range a
  have hc' := slot_range c
  have hsep : offset a + 32 ≤ offset c ∨ offset c + 32 ≤ offset a := by
    have : a.val ≠ c.val := fun e => hac (Fin.ext e)
    simp only [offset]; omega
  refine WP.mono (cswap_ok (by omega) (by omega) hsep hc.ctx hsw h11) fun t ht => ⟨ht.rest, ?_, ?_, ?_, fun i hia hic => ?_⟩
  · refine ht.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.sub _ (by omega) (by omega)
    · exact Offset.sub _ (by omega) (by omega)
  · unfold env FS; rw [sel_V hsw ht.lx, sel_toFe]
  · unfold env FS; rw [sel_V hsw ht.ly, sel_toFe]
  · have hi := slot_range i
    have h1 : i.val ≠ a.val := fun e => hia (Fin.ext e)
    have h2 : i.val ≠ c.val := fun e => hic (Fin.ext e)
    refine env_keep ht.frame i fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (by simp only [offset] at *; omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by simp only [offset] at *; omega) (by omega) (by omega)

/-- **The selection**: slots 0–3 swapped with 17–20 if `sw` is 1. -/
theorem pointSelect_ok {s : State} (hc : Ctx8 b s) {sw : Nat} (hsw : sw ≤ 1)
    (h11 : s.gpr .r11 = 0 - BitVec.ofNat 64 sw) :
    WP isa (.block pointSelect) s fun t =>
      Rest [.r5, .r7, .r8] s t ∧ Frame [FA b] s.mem t.mem ∧
      point (env t.mem b) 0 1 2 3 = sel sw (point (env s.mem b) 0 1 2 3) (point (env s.mem b) 17 18 19 20) ∧
      env t.mem b 16 = env s.mem b 16 := by
  unfold pointSelect swapFields pointSelectPairs
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have k11 : ∀ t : State, Rest [.r5, .r7, .r8] s t → t.gpr .r11 = 0 - BitVec.ofNat 64 sw := fun t h => by
    rw [h.gpr _ (by decide), h11]
  refine WP.append (cswapSlot_ok hc hsw h11 0 17 (by decide)) fun t1 ⟨r1, f1, a1, c1, k1⟩ => ?_
  refine WP.append (cswapSlot_ok (hc.of_rest r1 (by decide)) hsw (k11 t1 r1) 1 18 (by decide))
    fun t2 ⟨r2, f2, a2, c2, k2⟩ => ?_
  have r12 := r1.trans r2
  refine WP.append (cswapSlot_ok (hc.of_rest r12 (by decide)) hsw (k11 t2 r12) 2 19 (by decide))
    fun t3 ⟨r3, f3, a3, c3, k3⟩ => ?_
  have r13 := r12.trans r3
  refine WP.mono (cswapSlot_ok (hc.of_rest r13 (by decide)) hsw (k11 t3 r13) 3 20 (by decide))
    fun t4 ⟨r4, f4, a4, c4, k4⟩ => ⟨r13.trans r4, f1.trans (f2.trans (f3.trans f4)), ?_, ?_⟩
  · have e0 : env t4.mem b 0 = sel sw (env s.mem b 0) (env s.mem b 17) := by
      rw [k4 0 (by decide) (by decide), k3 0 (by decide) (by decide), k2 0 (by decide) (by decide), a1]
    have e1 : env t4.mem b 1 = sel sw (env s.mem b 1) (env s.mem b 18) := by
      rw [k4 1 (by decide) (by decide), k3 1 (by decide) (by decide), a2, k1 1 (by decide) (by decide),
        k1 18 (by decide) (by decide)]
    have e2 : env t4.mem b 2 = sel sw (env s.mem b 2) (env s.mem b 19) := by
      rw [k4 2 (by decide) (by decide), a3, k2 2 (by decide) (by decide), k2 19 (by decide) (by decide),
        k1 2 (by decide) (by decide), k1 19 (by decide) (by decide)]
    have e3 : env t4.mem b 3 = sel sw (env s.mem b 3) (env s.mem b 20) := by
      rw [a4, k3 3 (by decide) (by decide), k3 20 (by decide) (by decide), k2 3 (by decide) (by decide),
        k2 20 (by decide) (by decide), k1 3 (by decide) (by decide), k1 20 (by decide) (by decide)]
    simp only [point, e0, e1, e2, e3]
    unfold sel; split <;> rfl
  · rw [k4 16 (by decide) (by decide), k3 16 (by decide) (by decide), k2 16 (by decide) (by decide),
      k1 16 (by decide) (by decide)]

/-- A byte below the field area keeps its value through writes in the field area. -/
theorem byte_FA {m m' : Mem} (hf : Frame [FA b] m m') {d : Nat} (hd : d < 64) :
    m' (b + BitVec.ofNat 64 d) = m (b + BitVec.ofNat 64 d) :=
  hf _ fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact fun hc => Offset.disjoint b (d := d) (n := 1) (e := 64) (k := 960) (.inl (by omega)) (by omega)
      (by omega) _ (Region.contains_self _ _) hc

/-- A table entry above the field area keeps its point through writes in the field area. -/
theorem table_FA {m m' : Mem} (hf : Frame [FA b] m m') {o : Nat} (ho : 1024 ≤ o) (ho' : o + 128 ≤ 8192) :
    tableAt m' b o = tableAt m b o :=
  tableAt_keep hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)

/-- **The power `T` added to the accumulator if the bit `w` is 1**. -/
theorem pointAccumulate_ok {s : State} (hc : Ctx8 b s) (hd : env s.mem b 16 = Spec.Ed25519.d) {i : Nat}
    (hi : i < 16) (h16 : s.gpr .r16 = BitVec.ofNat 64 i) {w : Nat} (hw : w ≤ 1)
    (hb : (s.mem (b + BitVec.ofNat 64 (BITSB + i))).toNat = w) :
    WP isa pointAccumulate s fun t =>
      Rest (.r14 :: fclob) s t ∧ Frame [FA b] s.mem t.mem ∧
      point (env t.mem b) 0 1 2 3 = (if w = 1 then Spec.Ed25519.pointAdd (point (env s.mem b) 0 1 2 3)
        (tableAt s.mem b (5728 + 128 * i)) else point (env s.mem b) 0 1 2 3) ∧
      env t.mem b 16 = Spec.Ed25519.d := by
  unfold pointAccumulate prepareAdd savePoint copyPointToQ restorePoint
  refine WP.seq (WP.seq (WP.mono (fieldCode_ok savePointOps hc.ctx) fun t1 ⟨k1, e1⟩ => ?_))
  obtain ⟨s17, s0, s16⟩ := env_savePoint (env s.mem b)
  rw [← e1] at s17 s0 s16
  have hc1 : Ctx8 b t1 := hc.of_keep k1
  refine WP.seq (tableAddr_ok hc1 (start := 5728) (n := i) (by decide) (by omega) (by rw [k1.rest.gpr _ (by decide), h16])
    fun t2 r2 m2 e14 => ?_)
  have hc2 : Ctx8 b t2 := hc1.of_rest r2 (by decide)
  refine WP.mono (pointFromTable_ok hc2 e14 (by omega) (by omega)) fun t3 ⟨r3, f3, p3, k3⟩ => ?_
  rw [m2] at p3 k3 f3
  have hT : tableAt t1.mem b (5728 + 128 * i) = tableAt s.mem b (5728 + 128 * i) :=
    table_FA k1.frame (by omega) (by omega)
  rw [hT] at p3
  have hc3 : Ctx8 b t3 := hc2.of_rest r3 (by decide)
  refine WP.seq (WP.mono (fieldCode_ok copyPointToQOps hc3.ctx) fun t4 ⟨k4, e4⟩ => ?_)
  obtain ⟨q4, q0, q17, q16⟩ := env_copyQ (env t3.mem b)
  rw [← e4] at q4 q0 q17 q16
  have hc4 : Ctx8 b t4 := hc3.of_keep k4
  refine WP.mono (fieldCode_ok restorePointOps hc4.ctx) fun t5 ⟨k5, e5⟩ => ?_
  obtain ⟨w0, w17, w16, w4⟩ := env_restorePoint (env t4.mem b)
  rw [← e5] at w0 w17 w16 w4
  have hc5 : Ctx8 b t5 := hc4.of_keep k5
  -- The saved point and `d`, kept through the table's read.
  have k3p : ∀ j : Slot, 4 ≤ j.val → env t3.mem b j = env t1.mem b j := k3
  have hA3 : point (env t3.mem b) 17 18 19 20 = point (env s.mem b) 0 1 2 3 := by
    rw [← s17]
    simp only [point, k3p 17 (by decide), k3p 18 (by decide), k3p 19 (by decide), k3p 20 (by decide)]
  have hA17 : point (env t5.mem b) 17 18 19 20 = point (env s.mem b) 0 1 2 3 := by rw [w17, q17, hA3]
  have hA0 : point (env t5.mem b) 0 1 2 3 = point (env s.mem b) 0 1 2 3 := by rw [w0, q17, hA3]
  have hQ : point (env t5.mem b) 4 5 6 7 = tableAt s.mem b (5728 + 128 * i) := by rw [w4, q4, p3]
  have hd5 : env t5.mem b 16 = Spec.Ed25519.d := by rw [w16, q16, k3p 16 (by decide), s16, hd]
  refine WP.seq (WP.mono (addCall_ok hc5 hd5) fun t6 ⟨k6, p6, kk6⟩ => ?_)
  have hc6 : Ctx8 b t6 := hc5.of_keep k6
  have hA6 : point (env t6.mem b) 17 18 19 20 = point (env s.mem b) 0 1 2 3 := by
    rw [← hA17]
    simp only [point, kk6 17 (by decide), kk6 18 (by decide), kk6 19 (by decide), kk6 20 (by decide)]
  -- The bit, kept below the field area.
  have hFt : Frame [FA b] s.mem t6.mem := by
    refine k1.frame.trans ((f3.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (k4.frame.trans (k5.frame.trans k6.frame)))
    rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)
  have hR6 : Rest (.r14 :: fclob) s t6 :=
    (k1.rest.mono (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
      ((k4.rest.mono (by decide)).trans ((k5.rest.mono (by decide)).trans (k6.rest.mono (by decide))))))
  have hb6 : (t6.mem (b + BitVec.ofNat 64 (BITSB + i))).toNat = w := by
    rw [byte_FA hFt (by simp only [BITSB]; omega), hb]
  refine scalarBitMask_ok hc6 hi (by rw [hR6.gpr _ (by decide), h16]) hw hb6 fun t7 r7 m7 e11 => ?_
  refine WP.mono (pointSelect_ok (hc6.of_rest r7 (by decide)) (sw := 1 - w) (by omega) e11)
    fun t8 ⟨r8, f8, p8, d8⟩ => ⟨hR6.trans ((r7.mono (by decide)).trans (r8.mono (by decide))),
      hFt.trans (by rw [← m7]; exact f8), ?_, ?_⟩
  · rw [p8, m7, p6, hA0, hQ, hA6]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hw with rfl | rfl
    · simp only [sel, show (1 : Nat) - 0 = 1 from rfl, ite_true, show (0 : Nat) ≠ 1 by decide, ite_false]
    · simp only [sel, show (1 : Nat) - 1 = 0 from rfl, show (0 : Nat) ≠ 1 by decide, ite_false, ite_true]
  · rw [d8, m7, kk6 16 (by decide), hd5]

/-- The accumulator after the bits `m - 1` down to 0: each adds `T i` if `w i` is 1. -/
def accum (T : Nat → Spec.Ed25519.Point) (w : Nat → Nat) : Nat → Spec.Ed25519.Point → Spec.Ed25519.Point
  | 0, A => A
  | m + 1, A => accum T w m (if w m = 1 then Spec.Ed25519.pointAdd A (T m) else A)

/-- **The 16 bits of a batch**, counted down by `r16`. -/
theorem accumulate16_ok {s : State} (hc : Ctx8 b s) (hd : env s.mem b 16 = Spec.Ed25519.d)
    (hw : ∀ i < 16, (s.mem (b + BitVec.ofNat 64 (BITSB + i))).toNat ≤ 1) :
    WP isa accumulate16 s fun t =>
      Rest (.r16 :: .r14 :: fclob) s t ∧ Frame [FA b] s.mem t.mem ∧
      point (env t.mem b) 0 1 2 3 = accum (fun i => tableAt s.mem b (5728 + 128 * i))
        (fun i => (s.mem (b + BitVec.ofNat 64 (BITSB + i))).toNat) 16 (point (env s.mem b) 0 1 2 3) ∧
      env t.mem b 16 = Spec.Ed25519.d := by
  unfold accumulate16
  refine WP.seq (wp_li (by decide) fun s1 u1 => WP.block_nil ?_)
  let T := fun i => tableAt s.mem b (5728 + 128 * i)
  let W := fun i => (s.mem (b + BitVec.ofNat 64 (BITSB + i))).toNat
  refine WP.loop (M := isa) (fun m t => 1 ≤ m ∧ m ≤ 16 ∧ Rest (.r16 :: .r14 :: fclob) s t ∧ Frame [FA b] s.mem t.mem ∧
      t.gpr .r16 = BitVec.ofNat 64 m ∧ accum T W m (point (env t.mem b) 0 1 2 3) =
        accum T W 16 (point (env s.mem b) 0 1 2 3) ∧ env t.mem b 16 = Spec.Ed25519.d) ?_ 16 s1
    ⟨by decide, by decide, u1.rest (by decide), by rw [u1.mem]; exact Frame.refl _ _, u1.gpr, by rw [u1.mem],
      by rw [u1.mem]; exact hd⟩
  rintro m t ⟨h1, h2, hr, hf, h16, ha, hdt⟩
  have hct : Ctx8 b t := hc.of_rest hr (by decide)
  unfold accumulateBody
  refine WP.seq (wp_subi (by decide) (by decide) fun t1 u1' => WP.block_nil ?_)
  have e16 : t1.gpr .r16 = BitVec.ofNat 64 (m - 1) := by rw [u1'.gpr, h16, ofNat_sub_one h1 (by omega)]
  have hb1 : (t1.mem (b + BitVec.ofNat 64 (BITSB + (m - 1)))).toNat = W (m - 1) := by
    rw [u1'.mem, byte_FA hf (by simp only [BITSB]; omega)]
  have hT1 : tableAt t1.mem b (5728 + 128 * (m - 1)) = T (m - 1) := by
    rw [u1'.mem]; exact table_FA hf (by omega) (by omega)
  refine WP.mono (pointAccumulate_ok (hct.of_rest (u1'.rest (ws := [.r16]) (by decide)) (by decide))
    (by rw [u1'.mem]; exact hdt) (by omega) e16 (hw (m - 1) (by omega)) hb1) fun t2 ⟨r2, f2, p2, d2⟩ => ?_
  rw [hT1] at p2
  have hR : Rest (.r16 :: .r14 :: fclob) s t2 := hr.trans ((u1'.rest (by decide)).trans (r2.mono (by decide)))
  have hF : Frame [FA b] s.mem t2.mem := by rw [u1'.mem] at f2; exact hf.trans f2
  have e16' : t2.gpr .r16 = BitVec.ofNat 64 (m - 1) := by rw [r2.gpr _ (by decide), e16]
  have hA : accum T W (m - 1) (point (env t2.mem b) 0 1 2 3) = accum T W 16 (point (env s.mem b) 0 1 2 3) := by
    rw [← ha, p2, u1'.mem]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rfl
  have hz : (t2.gpr .r16 != 0) = decide (m - 1 ≠ 0) := by rw [e16', ofNat_ne_zero (by omega)]
  rw [eval_nonzero, hz]
  by_cases h0 : m - 1 = 0
  · refine .inl ⟨by simp [h0], hR, hF, ?_, d2⟩
    rw [← hA, h0]; rfl
  · exact .inr ⟨by simp [h0], m - 1, by omega, by omega, by omega, hR, hF, e16', hA, d2⟩

end

end VG.Proof.Ed25519.PPC64LE
