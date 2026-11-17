module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointTable
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.PointMul
import VerifiedGarbage.Proof.X25519.PPC64LE.Bits
import VerifiedGarbage.Proof.X25519.PPC64LE.Field
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ed25519.ScalarBytes
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointPowers
public import VerifiedGarbage.Proof.Ed25519.ScalarMul
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Field
import VerifiedGarbage.Proof.X25519.PPC64LE.Cswap

/-! ### `Ed25519.PPC64LE.PointAccumulate`, which this module and modules that import it used -/

section

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
      rw [u1.rd, u1.wr]; exact hc.inR (by simp only [BITSB]; omega_arith)) fun s2 u2 => ?_
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
  obtain ha := slot_range a
  obtain hc' := slot_range c
  obtain hsep : offset a + 32 ≤ offset c ∨ offset c + 32 ≤ offset a := by
    have : a.val ≠ c.val := fun e => hac (Fin.ext e)
    simp only [offset]; omega_arith
  refine WP.mono (cswap_ok (by omega_arith) (by omega_arith) hsep hc.ctx hsw h11) fun t ht => ⟨ht.rest, ?_, ?_, ?_, fun i hia hic => ?_⟩
  · refine ht.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.sub _ (by omega_arith) (by omega_arith)
    · exact Offset.sub _ (by omega_arith) (by omega_arith)
  · unfold env FS; rw [sel_V hsw ht.lx, sel_toFe]
  · unfold env FS; rw [sel_V hsw ht.ly, sel_toFe]
  · have hi := slot_range i
    obtain h1 : i.val ≠ a.val := fun e => hia (Fin.ext e)
    obtain h2 : i.val ≠ c.val := fun e => hic (Fin.ext e)
    refine env_keep ht.frame i fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (by simp only [offset] at *; omega_arith) (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (by simp only [offset] at *; omega_arith) (by omega_arith) (by omega_arith)

/-- **The selection**: slots 0–3 swapped with 17–20 if `sw` is 1. -/
theorem pointSelect_ok {s : State} (hc : Ctx8 b s) {sw : Nat} (hsw : sw ≤ 1)
    (h11 : s.gpr .r11 = 0 - BitVec.ofNat 64 sw) :
    WP isa (.block pointSelect) s fun t =>
      Rest [.r5, .r7, .r8] s t ∧ Frame [FA b] s.mem t.mem ∧
      point (env t.mem b) 0 1 2 3 = sel sw (point (env s.mem b) 0 1 2 3) (point (env s.mem b) 17 18 19 20) ∧
      env t.mem b 16 = env s.mem b 16 := by
  unfold pointSelect swapFields pointSelectPairs
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  obtain k11 : ∀ t : State, Rest [.r5, .r7, .r8] s t → t.gpr .r11 = 0 - BitVec.ofNat 64 sw := fun t h => by
    rw [h.gpr _ (by decide), h11]
  refine WP.append (cswapSlot_ok hc hsw h11 0 17 (by decide)) fun t1 ⟨r1, f1, a1, c1, k1⟩ => ?_
  refine WP.append (cswapSlot_ok (hc.of_rest r1 (by decide)) hsw (k11 t1 r1) 1 18 (by decide))
    fun t2 ⟨r2, f2, a2, c2, k2⟩ => ?_
  obtain r12 := r1.trans r2
  refine WP.append (cswapSlot_ok (hc.of_rest r12 (by decide)) hsw (k11 t2 r12) 2 19 (by decide))
    fun t3 ⟨r3, f3, a3, c3, k3⟩ => ?_
  obtain r13 := r12.trans r3
  refine WP.mono (cswapSlot_ok (hc.of_rest r13 (by decide)) hsw (k11 t3 r13) 3 20 (by decide))
    fun t4 ⟨r4, f4, a4, c4, k4⟩ => ⟨r13.trans r4, f1.trans (f2.trans (f3.trans f4)), ?_, ?_⟩
  · have e0 : env t4.mem b 0 = sel sw (env s.mem b 0) (env s.mem b 17) := by
      rw [k4 0 (by decide) (by decide), k3 0 (by decide) (by decide), k2 0 (by decide) (by decide), a1]
    obtain e1 : env t4.mem b 1 = sel sw (env s.mem b 1) (env s.mem b 18) := by
      rw [k4 1 (by decide) (by decide), k3 1 (by decide) (by decide), a2, k1 1 (by decide) (by decide),
        k1 18 (by decide) (by decide)]
    obtain e2 : env t4.mem b 2 = sel sw (env s.mem b 2) (env s.mem b 19) := by
      rw [k4 2 (by decide) (by decide), a3, k2 2 (by decide) (by decide), k2 19 (by decide) (by decide),
        k1 2 (by decide) (by decide), k1 19 (by decide) (by decide)]
    obtain e3 : env t4.mem b 3 = sel sw (env s.mem b 3) (env s.mem b 20) := by
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
    exact fun hc => Offset.disjoint b (d := d) (n := 1) (e := 64) (k := 960) (.inl (by omega_arith)) (by omega_arith)
      (by omega_arith) _ (Region.contains_self _ _) hc

/-- A table entry above the field area keeps its point through writes in the field area. -/
theorem table_FA {m m' : Mem} (hf : Frame [FA b] m m') {o : Nat} (ho : 1024 ≤ o) (ho' : o + 128 ≤ 8192) :
    tableAt m' b o = tableAt m b o :=
  tableAt_keep hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)

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
  obtain hc1 : Ctx8 b t1 := hc.of_keep k1
  refine WP.seq (tableAddr_ok hc1 (start := 5728) (n := i) (by decide) (by omega_arith) (by rw [k1.rest.gpr _ (by decide), h16])
    fun t2 r2 m2 e14 => ?_)
  obtain hc2 : Ctx8 b t2 := hc1.of_rest r2 (by decide)
  refine WP.mono (pointFromTable_ok hc2 e14 (by omega_arith) (by omega_arith)) fun t3 ⟨r3, f3, p3, k3⟩ => ?_
  rw [m2] at p3 k3 f3
  obtain hT : tableAt t1.mem b (5728 + 128 * i) = tableAt s.mem b (5728 + 128 * i) :=
    table_FA k1.frame (by omega_arith) (by omega_arith)
  rw [hT] at p3
  obtain hc3 : Ctx8 b t3 := hc2.of_rest r3 (by decide)
  refine WP.seq (WP.mono (fieldCode_ok copyPointToQOps hc3.ctx) fun t4 ⟨k4, e4⟩ => ?_)
  obtain ⟨q4, q0, q17, q16⟩ := env_copyQ (env t3.mem b)
  rw [← e4] at q4 q0 q17 q16
  obtain hc4 : Ctx8 b t4 := hc3.of_keep k4
  refine WP.mono (fieldCode_ok restorePointOps hc4.ctx) fun t5 ⟨k5, e5⟩ => ?_
  obtain ⟨w0, w17, w16, w4⟩ := env_restorePoint (env t4.mem b)
  rw [← e5] at w0 w17 w16 w4
  obtain hc5 : Ctx8 b t5 := hc4.of_keep k5
  -- The saved point and `d`, kept through the table's read.
  have k3p : ∀ j : Slot, 4 ≤ j.val → env t3.mem b j = env t1.mem b j := k3
  obtain hA3 : point (env t3.mem b) 17 18 19 20 = point (env s.mem b) 0 1 2 3 := by
    rw [← s17]
    simp only [point, k3p 17 (by decide), k3p 18 (by decide), k3p 19 (by decide), k3p 20 (by decide)]
  obtain hA17 : point (env t5.mem b) 17 18 19 20 = point (env s.mem b) 0 1 2 3 := by rw [w17, q17, hA3]
  obtain hA0 : point (env t5.mem b) 0 1 2 3 = point (env s.mem b) 0 1 2 3 := by rw [w0, q17, hA3]
  obtain hQ : point (env t5.mem b) 4 5 6 7 = tableAt s.mem b (5728 + 128 * i) := by rw [w4, q4, p3]
  obtain hd5 : env t5.mem b 16 = Spec.Ed25519.d := by rw [w16, q16, k3p 16 (by decide), s16, hd]
  refine WP.seq (WP.mono (addCall_ok hc5 hd5) fun t6 ⟨k6, p6, kk6⟩ => ?_)
  obtain hc6 : Ctx8 b t6 := hc5.of_keep k6
  obtain hA6 : point (env t6.mem b) 17 18 19 20 = point (env s.mem b) 0 1 2 3 := by
    rw [← hA17]
    simp only [point, kk6 17 (by decide), kk6 18 (by decide), kk6 19 (by decide), kk6 20 (by decide)]
  -- The bit, kept below the field area.
  obtain hFt : Frame [FA b] s.mem t6.mem := by
    refine k1.frame.trans ((f3.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (k4.frame.trans (k5.frame.trans k6.frame)))
    rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
  obtain hR6 : Rest (.r14 :: fclob) s t6 :=
    (k1.rest.mono (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
      ((k4.rest.mono (by decide)).trans ((k5.rest.mono (by decide)).trans (k6.rest.mono (by decide))))))
  obtain hb6 : (t6.mem (b + BitVec.ofNat 64 (BITSB + i))).toNat = w := by
    rw [byte_FA hFt (by simp only [BITSB]; omega_arith), hb]
  refine scalarBitMask_ok hc6 hi (by rw [hR6.gpr _ (by decide), h16]) hw hb6 fun t7 r7 m7 e11 => ?_
  refine WP.mono (pointSelect_ok (hc6.of_rest r7 (by decide)) (sw := 1 - w) (by omega_arith) e11)
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
  obtain hct : Ctx8 b t := hc.of_rest hr (by decide)
  unfold accumulateBody
  refine WP.seq (wp_subi (by decide) (by decide) fun t1 u1' => WP.block_nil ?_)
  obtain e16 : t1.gpr .r16 = BitVec.ofNat 64 (m - 1) := by rw [u1'.gpr, h16, ofNat_sub_one h1 (by omega_arith)]
  obtain hb1 : (t1.mem (b + BitVec.ofNat 64 (BITSB + (m - 1)))).toNat = W (m - 1) := by
    rw [u1'.mem, byte_FA hf (by simp only [BITSB]; omega_arith)]
  obtain hT1 : tableAt t1.mem b (5728 + 128 * (m - 1)) = T (m - 1) := by
    rw [u1'.mem]; exact table_FA hf (by omega_arith) (by omega_arith)
  refine WP.mono (pointAccumulate_ok (hct.of_rest (u1'.rest (ws := [.r16]) (by decide)) (by decide))
    (by rw [u1'.mem]; exact hdt) (by omega_arith) e16 (hw (m - 1) (by omega_arith)) hb1) fun t2 ⟨r2, f2, p2, d2⟩ => ?_
  rw [hT1] at p2
  obtain hR : Rest (.r16 :: .r14 :: fclob) s t2 := hr.trans ((u1'.rest (by decide)).trans (r2.mono (by decide)))
  obtain hF : Frame [FA b] s.mem t2.mem := by rw [u1'.mem] at f2; exact hf.trans f2
  obtain e16' : t2.gpr .r16 = BitVec.ofNat 64 (m - 1) := by rw [r2.gpr _ (by decide), e16]
  obtain hA : accum T W (m - 1) (point (env t2.mem b) 0 1 2 3) = accum T W 16 (point (env s.mem b) 0 1 2 3) := by
    rw [← ha, p2, u1'.mem]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega_arith⟩
    rfl
  obtain hz : (t2.gpr .r16 != 0) = decide (m - 1 ≠ 0) := by rw [e16', ofNat_ne_zero (by omega_arith)]
  rw [eval_nonzero, hz]
  by_cases h0 : m - 1 = 0
  · refine .inl ⟨by simp [h0], hR, hF, ?_, d2⟩
    rw [← hA, h0]; rfl
  · exact .inr ⟨by simp [h0], m - 1, by omega_arith, by omega_arith, by omega_arith, hR, hF, e16', hA, d2⟩

end

end VG.Proof.Ed25519.PPC64LE

end

end

/-! ### `Ed25519.PPC64LE.BatchBits`, which only this module used -/

section

/-!
# Ed25519 on PPC64LE: a batch's 16 bits, one to a byte

`batchBits` with `r26 = c` and the scalar at `r19`: the scalar's bytes `2c`
and `2c + 1` as a 16-bit digit (`batchDigit_ok`), and bit `k` of it at byte
`BITSB + k` of the working space (`expandBits_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE

section
variable {b : Addr}

/-- After `k` bits of the digit `x` from `s1`. -/
structure KInv (b : Addr) (x : Nat) (s1 : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.r8] s1 s
  frame : Frame [⟨b + BitVec.ofNat 64 BITSB, k⟩] s1.mem s.mem
  bits : ∀ j < k, s.mem (b + BitVec.ofNat 64 (BITSB + j)) = BitVec.ofNat 8 ((x >>> j) &&& 1)

theorem expandBits_ok {s1 : State} (hc : Ctx8 b s1) {x : Nat} (h7 : (s1.gpr .r7).toNat = x) :
    WP isa (.block expandBits) s1 (KInv b x s1 16) := by
  have hB : BITSB = 32 := rfl
  refine wp_range_flatMap (M := isa) (KInv b x s1) (fun k s hk h => ?_) 16 (Nat.le_refl _) s1
    ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => by omega⟩
  have e7 : (s.gpr .r7).toNat = x := by rw [h.rest.gpr _ (by decide), h7]
  have hcs : Ctx8 b s := hc.of_rest h.rest (by decide)
  unfold expandBit
  refine wp_lsl (by omega_using []) fun s2 u2 => wp_lsr (by decide) fun s3 u3 => ?_
  have e8 : (s3.gpr .r8).toNat = (x >>> k) &&& 1 := by
    rw [u3.gpr, u2.gpr, bit_shift _ (by omega_using [hk]), e7]
  refine wp_stb (a := b + BitVec.ofNat 64 (BITSB + k)) (by decide) (by omega_using [hB, hk])
    (by rw [u3.other _ (by decide), u2.other _ (by decide), hcs.r6])
    (by rw [u3.wr, u2.wr]; exact hcs.inW (by omega_using [hB, hk])) fun s4 u4 => WP.block_nil ⟨?_, ?_, fun j hj => ?_⟩
  · exact h.rest.trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans (u4.rest _)))
  · rw [u4.mem, u3.mem, u2.mem]
    exact (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_using [])⟩).writeW
      (List.mem_singleton_self _) _ (by rw [hB]; exact Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [hk]))
  · rw [u4.mem, VG.WriteBytes.writeW8_apply, u3.mem, u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [ite_eq_right (Offset.add_ofNat_ne _ (by omega_arith) (by omega_using [hB, hk]) (by omega_using [hj]))]; exact h.bits j hj
    · rw [ite_eq_left rfl]; exact stb_byte e8

/-- The digit of batch `c`: bytes `2c` and `2c + 1` of the scalar at `r19`. -/
def digitAt (m : Mem) (p : Addr) (c : Nat) : Nat :=
  (m (p + BitVec.ofNat 64 (2 * c))).toNat + 256 * (m (p + BitVec.ofNat 64 (2 * c + 1))).toNat

theorem batchBits_ok {s : State} (hc : Ctx8 b s) {c : Nat} (hcl : c < 32) (h26 : s.gpr .r26 = BitVec.ofNat 64 c)
    {p : Addr} (h19 : s.gpr .r19 = p) (hin : ∀ i < 2, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (2 * c + i)) 1) :
    WP isa (.block batchBits) s fun t =>
      Rest [.r7, .r8, .r14] s t ∧ Frame [⟨b + BitVec.ofNat 64 BITSB, 16⟩] s.mem t.mem ∧
      ∀ k < 16, t.mem (b + BitVec.ofNat 64 (BITSB + k)) = BitVec.ofNat 8 ((digitAt s.mem p c >>> k) &&& 1) := by
  unfold batchBits batchDigit
  simp only [List.cons_append, List.nil_append]
  refine wp_lsl (by decide) fun s1 u1 => wp_add fun s2 u2 => ?_
  have e14 : s2.gpr .r14 = p + BitVec.ofNat 64 (2 * c) := by
    rw [u2.gpr, u1.other .r19 (by decide), h19, u1.gpr, h26]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [toNat_shl, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hcl]), Nat.mod_eq_of_lt (by omega_using [hcl]),
      Nat.mod_eq_of_lt (by omega_using [hcl])]
    omega_using []
  refine wp_lbz (a := p + BitVec.ofNat 64 (2 * c)) (by decide) (by decide) (by rw [e14, BitVec.add_zero])
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact Nat.add_zero (2 * c) ▸ hin 0 (by decide)) fun s3 u3 => ?_
  refine wp_lbz (a := p + BitVec.ofNat 64 (2 * c + 1)) (by decide) (by decide)
    (by rw [u3.other _ (by decide), e14, Offset.add_add])
    (by rw [u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact hin 1 (by decide)) fun s4 u4 => ?_
  refine wp_lsl (by decide) fun s5 u5 => wp_add fun s6 u6 => ?_
  have hm6 : s6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have hlo := (s.mem (p + BitVec.ofNat 64 (2 * c))).isLt
  have hhi := (s.mem (p + BitVec.ofNat 64 (2 * c + 1))).isLt
  have e7 : (s6.gpr .r7).toNat = digitAt s.mem p c := by
    have m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
    rw [u6.gpr, u5.other _ (by decide), u4.other _ (by decide), u3.gpr, u5.gpr, u4.gpr, u2.mem, u1.mem, m3]
    rw [toNat_add_lt, BitVec.toNat_ofNat, toNat_shl, BitVec.toNat_ofNat]
    · simp only [digitAt]
      rw [Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [])]
      omega_using []
    · rw [BitVec.toNat_ofNat, toNat_shl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using []),
        Nat.mod_eq_of_lt (by omega_using [])]
      omega_using []
  have hr6 : Rest [.r7, .r8, .r14] s s6 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  refine WP.mono (expandBits_ok (hc.of_rest hr6 (by decide)) e7) fun t ht =>
    ⟨hr6.trans (ht.rest.mono (by decide)), by rw [← hm6]; exact ht.frame, ht.bits⟩

end

end VG.Proof.Ed25519.PPC64LE

end

end


/-!
# Ed25519 on PPC64LE: scalar multiplication

`pointMulBody_ok`: from the accumulator `after S P (16 (c + 1))`, batch `c`
adds the powers `[2^(16c + i)] P` of its set bits from the top, leaving
`after S P (16 c)` (`accum_after`). `pointMultiply_ok`: from the identity
and the table of `[2^(16 j)] P`, all batches from the top, `[S] P`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Proof.Ed25519 (powerPoint after)

/-- Sixteen bits from the top, by `after_step`. -/
theorem accum_after (S : Nat) (P : Spec.Ed25519.Point) (c : Nat) :
    ∀ m ≤ 16, accum (fun i => powerPoint P (16 * c + i)) (fun i => S / 2 ^ (16 * c + i) % 2) m
      (after S P (16 * c + m)) = after S P (16 * c)
  | 0, _ => rfl
  | m + 1, hm => by
    rw [accum, ← accum_after S P c m (by omega_arith)]
    congr 1
    rw [Proof.Ed25519.after_step S P (16 * c + m)]
    by_cases h : S / 2 ^ (16 * c + m) % 2 = 0
    · rw [ite_eq_left h, ite_eq_right (by omega_arith)]; rfl
    · rw [ite_eq_right h, ite_eq_left (by omega_arith)]; rfl

theorem accum_congr {T T' : Nat → Spec.Ed25519.Point} {W W' : Nat → Nat} :
    ∀ m, (∀ i < m, T i = T' i) → (∀ i < m, W i = W' i) → ∀ A, accum T W m A = accum T' W' m A
  | 0, _, _, _ => rfl
  | m + 1, hT, hW, A => by
    rw [accum, accum, hT m (by omega_arith), hW m (by omega_arith)]
    exact accum_congr m (fun i hi => hT i (by omega_arith)) (fun i hi => hW i (by omega_arith)) _

/-- A batch's digit, as the scalar's bits. -/
theorem digit_bit {m : Mem} {p : Addr} {N c k : Nat} (hc : c < N) (hk : k < 16) :
    (digitAt m p c >>> k) &&& 1 = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p (2 * N)) / 2 ^ (16 * c + k) % 2 := by
  obtain ⟨S, hS⟩ : ∃ S, S = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p (2 * N)) := ⟨_, rfl⟩
  rw [← hS]
  have hb : ∀ i < 2 * N, S / 256 ^ i % 256 = (m (p + BitVec.ofNat 64 i)).toNat := fun i hi => by
    rw [hS, Proof.Ed25519.decodeLE_byte]
    exact congrArg BitVec.toNat (getD_bytesAt m p hi)
  have hd : digitAt m p c = S / 2 ^ (16 * c) % 2 ^ 16 := by
    have h1 := hb (2 * c) (by omega_arith)
    have h2 := hb (2 * c + 1) (by omega_arith)
    have hs := Proof.Ed25519.div_split S (2 * c)
    rw [show (2 : Nat) ^ (16 * c) = 256 ^ (2 * c) by rw [Nat.pow_mul, Nat.pow_mul], hs]
    unfold digitAt
    rw [← h1, ← h2]
    omega_arith
  have h2 : 2 ∣ 2 ^ (16 - k) := ⟨2 ^ (16 - k - 1), by rw [← Nat.pow_succ']; congr 1; omega_arith⟩
  rw [hd, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod,
    show (2 : Nat) ^ 16 = 2 ^ k * 2 ^ (16 - k) by rw [← Nat.pow_add]; congr 1; omega_arith,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ h2, Nat.div_div_eq_div_mul, ← Nat.pow_add]

section
variable {b : Addr}

/-- What a batch writes: the field area, the table of its powers and its bits. -/
abbrev batchW (b : Addr) : List Region := [FA b, ⟨b + BitVec.ofNat 64 5728, 2048⟩, ⟨b + BitVec.ofNat 64 BITSB, 16⟩]

/-- The registers a batch writes. -/
abbrev batchR : List Reg := .r8 :: .r14 :: .r15 :: .r16 :: .r26 :: fclob

theorem bytes_ws {m m' : Mem} {rs : List Region} (hf : Frame rs m m') (hs : ∀ r ∈ rs, Region.Sub r ⟨b, 8192⟩)
    {p : Addr} {nb : Nat} (hd : (⟨p, nb⟩ : Region).Disjoint ⟨b, 8192⟩) (hn : nb ≤ 64) {i : Nat} (hi : i < nb) :
    m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  hf _ fun r hr hc => hd _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) (hs r hr _ hc)

theorem batchW_sub : ∀ r ∈ batchW b, Region.Sub r ⟨b, 8192⟩ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.sub_base _ (by omega_arith)
  · exact Offset.sub_base _ (by omega_arith)
  · exact Offset.sub_base _ (by simp only [BITSB]; omega_arith)

theorem batch_table1 {m m' : Mem} (hf : Frame (batchW b) m m') {j : Nat} (hj : j < 32) :
    tableAt m' b (1632 + 128 * j) = tableAt m b (1632 + 128 * j) :=
  tableAt_keep hf fun r hr => by
    have hB : BITSB = 32 := rfl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (.inr (by simp only [BITSB]; omega_arith)) (by omega_arith) (by omega_arith)

/-- **Batch `c`**: from `after S P (16 (c + 1))` to `after S P (16 c)`. -/
theorem pointMulBody_ok {s : State} (hc : Ctx8 b s) (hd : env s.mem b 16 = Spec.Ed25519.d) {p : Addr} {N : Nat}
    (hN : N ≤ 32) (h19 : s.gpr .r19 = p) (hin : ∀ i < 2 * N, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1)
    (hpd : (⟨p, 2 * N⟩ : Region).Disjoint ⟨b, 8192⟩) {c : Nat} (hcl : c < N)
    (h26 : s.gpr .r26 = BitVec.ofNat 64 (c + 1)) {P : Spec.Ed25519.Point}
    (hacc : point (env s.mem b) 0 1 2 3 =
      after (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p (2 * N))) P (16 * (c + 1)))
    (htab : tableAt s.mem b (1632 + 128 * c) = powerPoint P (16 * c)) :
    WP isa pointMulBody s fun t =>
      Rest batchR s t ∧ Frame (batchW b) s.mem t.mem ∧ t.gpr .r26 = BitVec.ofNat 64 c ∧
      point (env t.mem b) 0 1 2 3 = after (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p (2 * N))) P (16 * c) ∧
      env t.mem b 16 = Spec.Ed25519.d := by
  obtain ⟨S, hS⟩ : ∃ S, S = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p (2 * N)) := ⟨_, rfl⟩
  rw [← hS] at hacc ⊢
  unfold pointMulBody batchStart
  refine WP.seq (wp_subi (by decide) (by decide) fun s1 u1 => wp_addi (by decide) (by decide) fun s2 u2 =>
    WP.block_nil ?_)
  have e26 : s2.gpr .r26 = BitVec.ofNat 64 c := by
    rw [u2.other _ (by decide), u1.gpr, h26, ofNat_sub_one (by omega_arith) (by omega_arith), Nat.add_sub_cancel]
  have e16 : s2.gpr .r16 = BitVec.ofNat 64 c := by
    rw [u2.gpr, BitVec.add_zero, u1.gpr, h26, ofNat_sub_one (by omega_arith) (by omega_arith), Nat.add_sub_cancel]
  have hr2 : Rest [.r16, .r26] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have hc2 : Ctx8 b s2 := hc.of_rest hr2 (by decide)
  -- The checkpoint, and the saved accumulator.
  unfold prepareBatch loadCheckpoint savePoint restorePoint
  refine WP.seq (WP.seq (WP.seq (WP.mono (fieldCode_ok savePointOps hc2.ctx) fun t1 ⟨k1, e1⟩ => ?_)))
  obtain ⟨s17, _, s16⟩ := env_savePoint (env s2.mem b)
  rw [← e1, hm2] at s17 s16
  have hc3 : Ctx8 b t1 := hc2.of_keep k1
  refine tableAddr_ok hc3 (start := 1632) (n := c) (by decide) (by omega_arith) (by rw [k1.rest.gpr _ (by decide), e16])
    fun t2 r2 m2 e14 => ?_
  refine WP.mono (pointFromTable_ok (hc3.of_rest r2 (by decide)) e14 (by omega_arith) (by omega_arith)) fun t3 ⟨r3, f3, p3, k3⟩ => ?_
  rw [m2] at p3 k3 f3
  rw [table_FA k1.frame (by omega_arith) (by omega_arith), hm2, htab] at p3
  have hc4 : Ctx8 b t3 := (hc3.of_rest r2 (by decide)).of_rest r3 (by decide)
  have hd3 : env t3.mem b 16 = Spec.Ed25519.d := by rw [k3 16 (by decide), s16, hd]
  -- The batch's powers, and the accumulator restored.
  refine WP.seq (WP.mono (pointPowers_ok hc4 hd3 false (start := 5728) (count := 16) (by omega_arith) (by omega_arith) (by omega_arith))
    fun t4 ⟨r4, f4, tab4, _, k4⟩ => ?_)
  have hc5 : Ctx8 b t4 := hc4.of_rest r4 (by decide)
  refine WP.mono (fieldCode_ok restorePointOps hc5.ctx) fun t5 ⟨k5, e5⟩ => ?_
  obtain ⟨w0, _, w16, _⟩ := env_restorePoint (env t4.mem b)
  rw [← e5] at w0 w16
  have hc6 : Ctx8 b t5 := hc5.of_keep k5
  have hA5 : point (env t5.mem b) 0 1 2 3 = after S P (16 * (c + 1)) := by
    rw [w0, ← hacc, ← s17]
    simp only [point, k4 17 (by decide), k4 18 (by decide), k4 19 (by decide), k4 20 (by decide),
      k3 17 (by decide), k3 18 (by decide), k3 19 (by decide), k3 20 (by decide)]
  have hd5 : env t5.mem b 16 = Spec.Ed25519.d := by rw [w16, k4 16 (by decide), hd3]
  -- Everything so far writes within the batch's regions.
  have hF5 : Frame (batchW b) s.mem t5.mem := by
    rw [← hm2]
    refine (k1.frame.mono (by simp)).trans ((f3.sub fun r hr => ⟨FA b, by simp, ?_⟩).trans
      ((f4.mono fun r hr => ?_).trans (k5.frame.mono (by simp))))
    · rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl (by simp))
  have hR5 : Rest batchR s t5 :=
    (hr2.mono (by decide)).trans ((k1.rest.mono (by decide)).trans ((r2.mono (by decide)).trans
      ((r3.mono (by decide)).trans ((r4.mono (by decide)).trans (k5.rest.mono (by decide))))))
  -- The bits.
  have hR25 : Rest (.r7 :: .r14 :: .r15 :: .r16 :: fclob) s2 t5 :=
    (k1.rest.mono (by decide)).trans ((r2.mono (by decide)).trans
      ((r3.mono (by decide)).trans ((r4.mono (by decide)).trans (k5.rest.mono (by decide)))))
  have e26' : t5.gpr .r26 = BitVec.ofNat 64 c := by rw [hR25.gpr _ (by decide), e26]
  refine WP.seq (WP.mono (batchBits_ok hc6 (by omega_arith) e26' (p := p)
    (by rw [hR5.gpr _ (by decide), h19]) (fun i hi => by rw [hR5.rd, hR5.wr]; exact hin _ (by omega_arith)))
    fun t6 ⟨r6, f6, bits6⟩ => ?_)
  have hB : BITSB = 32 := rfl
  have hc7 : Ctx8 b t6 := hc6.of_rest r6 (by decide)
  have hslot : ∀ j : Slot, env t6.mem b j = env t5.mem b j := fun j => env_keep f6 j fun r hr => by
    rw [List.mem_singleton.mp hr]
    have := slot_range j
    exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  have hd6 : env t6.mem b 16 = Spec.Ed25519.d := by rw [hslot, hd5]
  have hbit : ∀ k < 16, (t6.mem (b + BitVec.ofNat 64 (BITSB + k))).toNat = S / 2 ^ (16 * c + k) % 2 := fun k hk => by
    rw [bits6 k hk, BitVec.toNat_ofNat]
    have hdig : digitAt t5.mem p c = digitAt s.mem p c := by
      unfold digitAt
      rw [bytes_ws hF5 batchW_sub hpd (by omega_arith) (by omega_arith), bytes_ws hF5 batchW_sub hpd (by omega_arith) (by omega_arith)]
    rw [hdig, digit_bit hcl hk, ← hS]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))
  refine WP.mono (accumulate16_ok hc7 hd6 fun k hk => by rw [hbit k hk]; exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide)))
    fun t7 ⟨r7, f7, p7, d7⟩ => ⟨?_, ?_, ?_, ?_, d7⟩
  · exact hR5.trans ((r6.mono (by decide)).trans (r7.mono (by decide)))
  · exact hF5.trans ((f6.mono (by simp)).trans (f7.mono (by simp)))
  · rw [r7.gpr _ (by decide), r6.gpr _ (by decide), e26']
  · have hT : ∀ i < 16, tableAt t6.mem b (5728 + 128 * i) = powerPoint P (16 * c + i) := fun i hi => by
      rw [tableAt_keep f6 fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith),
        table_FA k5.frame (by omega_arith) (by omega_arith), tab4 i hi, p3, ← Proof.Ed25519.powerPoint_add,
        show powerStride false = 1 from rfl, Nat.one_mul]
    have hP6 : point (env t6.mem b) 0 1 2 3 = after S P (16 * c + 16) := by
      simp only [point, hslot]; rw [← Nat.mul_succ]; exact hA5
    rw [p7, hP6, accum_congr 16 hT hbit, accum_after S P c 16 (Nat.le_refl _)]

/-- What the multiplication writes: a batch's regions and the table of checkpoints. -/
abbrev mulW (b : Addr) : List Region := ⟨b + BitVec.ofNat 64 1632, 4096⟩ :: batchW b

theorem mulW_sub : ∀ r ∈ mulW b, Region.Sub r ⟨b, 8192⟩ := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact Offset.sub_base _ (by omega_arith)
  · exact batchW_sub r hr

theorem env_constPoint (e : Env) (p : Spec.Ed25519.Point) :
    point (evalOps (constPointOps p) e) 0 1 2 3 = p ∧ evalOps (constPointOps p) e 16 = e 16 := ⟨rfl, rfl⟩

/-- **`[S] P`**, for the point `P` of slots 0–3 and the scalar `S` of the `2 count` bytes at `r19`. -/
theorem pointMultiply_ok {s : State} (hc : Ctx8 b s) (hd : env s.mem b 16 = Spec.Ed25519.d) {p : Addr}
    {count : Nat} (hc1 : 1 ≤ count) (hc32 : count ≤ 32) (h19 : s.gpr .r19 = p)
    (hin : ∀ i < 2 * count, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1)
    (hpd : (⟨p, 2 * count⟩ : Region).Disjoint ⟨b, 8192⟩) :
    WP isa (pointMultiply count) s fun t =>
      Rest (.r7 :: batchR) s t ∧ Frame (mulW b) s.mem t.mem ∧
      point (env t.mem b) 0 1 2 3 =
        Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p (2 * count)))
          (point (env s.mem b) 0 1 2 3) ∧ env t.mem b 16 = Spec.Ed25519.d := by
  have hS := Proof.Ed25519.decodeLE_lt (Spec.Ed25519.bytesAt s.mem p (2 * count))
  rw [show (Spec.Ed25519.bytesAt s.mem p (2 * count)).length = 2 * count by simp [Spec.Ed25519.bytesAt],
    show (256 : Nat) ^ (2 * count) = 2 ^ (16 * count) by rw [Nat.pow_mul, Nat.pow_mul]] at hS
  obtain ⟨S, hSd⟩ : ∃ S, S = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p (2 * count)) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = point (env s.mem b) 0 1 2 3 := ⟨_, rfl⟩
  rw [← hSd, ← hP]
  rw [← hSd] at hS
  unfold pointMultiply
  refine WP.seq (WP.mono (pointPowers_ok hc hd true (start := 1632) (count := count) (by omega_arith) (by omega_arith) hc1)
    fun t1 ⟨r1, f1, tab1, _, k1⟩ => ?_)
  rw [← hP] at tab1
  have hc2 : Ctx8 b t1 := hc.of_rest r1 (by decide)
  unfold constPoint
  refine WP.seq (WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.identity) hc2.ctx) fun t2 ⟨k2, e2⟩ => ?_)
  obtain ⟨c0, c16⟩ := env_constPoint (env t1.mem b) Spec.Ed25519.identity
  rw [← e2] at c0 c16
  have hc3 : Ctx8 b t2 := hc2.of_keep k2
  refine WP.seq (wp_li (by omega_arith) fun t3 u3 => WP.block_nil ?_)
  have hc4 : Ctx8 b t3 := hc3.of_rest (u3.rest (ws := [.r26]) (by decide)) (by decide)
  -- The frames so far.
  have hF3 : Frame (mulW b) s.mem t3.mem := by
    rw [u3.mem]
    refine (f1.sub fun r hr => ?_).trans (k2.frame.mono (by simp))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨FA b, by simp, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by omega_arith)⟩
  have hbytes : ∀ {m : Mem}, Frame (mulW b) s.mem m →
      Spec.Ed25519.bytesAt m p (2 * count) = Spec.Ed25519.bytesAt s.mem p (2 * count) :=
    fun hf => by
      simp only [Spec.Ed25519.bytesAt, List.map_inj_left]
      intro i hi
      exact bytes_ws hf mulW_sub hpd (by omega_arith) (List.mem_range.mp hi)
  have hR3 : Rest (.r7 :: batchR) s t3 :=
    (r1.mono (by decide)).trans ((k2.rest.mono (by decide)).trans (u3.rest (by decide)))
  have hT3 : ∀ j < count, tableAt t3.mem b (1632 + 128 * j) = powerPoint P (16 * j) := fun j hj => by
    rw [u3.mem, table_FA k2.frame (by omega_arith) (by omega_arith), tab1 j hj]; rfl
  refine WP.loop (M := isa) (fun n t => 1 ≤ n ∧ n ≤ count ∧ Ctx8 b t ∧ Rest (.r7 :: batchR) s t ∧
      Frame (mulW b) s.mem t.mem ∧ t.gpr .r26 = BitVec.ofNat 64 n ∧
      point (env t.mem b) 0 1 2 3 = after S P (16 * n) ∧ env t.mem b 16 = Spec.Ed25519.d ∧
      ∀ j < count, tableAt t.mem b (1632 + 128 * j) = powerPoint P (16 * j)) ?_ count t3
    ⟨hc1, Nat.le_refl _, hc4, hR3, hF3, u3.gpr, by rw [u3.mem, c0, Proof.Ed25519.after_top S _ P hS],
      by rw [u3.mem, c16, k1 16 (by decide), hd], hT3⟩
  rintro n t ⟨h1, h2, hct, hr, hf, h26, ha, hdt, ht⟩
  obtain ⟨c, rfl⟩ : ∃ c, n = c + 1 := ⟨n - 1, by omega_arith⟩
  refine WP.mono (pointMulBody_ok hct hdt (p := p) hc32 (by rw [hr.gpr _ (by decide), h19])
    (fun i hi => by rw [hr.rd, hr.wr]; exact hin i hi) hpd (by omega_arith) h26 (P := P)
    (by rw [hbytes hf, ← hSd]; exact ha) (ht c (by omega_arith))) fun u ⟨ru, fu, e26, pu, du⟩ => ?_
  rw [hbytes hf, ← hSd] at pu
  have hfu : Frame (mulW b) s.mem u.mem := hf.trans (fu.mono (by simp))
  have hz : (u.gpr .r26 != 0) = decide (c ≠ 0) := by rw [e26, ofNat_ne_zero (by omega_arith)]
  rw [eval_nonzero, hz]
  by_cases hc0 : c = 0
  · subst hc0
    refine .inl ⟨by simp, hr.trans (ru.mono (by decide)), hfu, ?_, du⟩
    rw [pu, Nat.mul_zero, Proof.Ed25519.after_zero]
  · exact .inr ⟨by simp [hc0], c, by omega_arith, by omega_arith, by omega_arith, hct.of_rest ru (by decide),
      hr.trans (ru.mono (by decide)), hfu, e26, pu, du, fun j hj => by rw [batch_table1 fu (by omega_arith), ht j hj]⟩

end

end VG.Proof.Ed25519.PPC64LE
