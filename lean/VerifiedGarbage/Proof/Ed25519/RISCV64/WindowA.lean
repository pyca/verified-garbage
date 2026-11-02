module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.WindowOps
public import VerifiedGarbage.Proof.Ed25519.RISCV64.WindowTable
public import VerifiedGarbage.Proof.Ed25519.RISCV64.PointPowers
public import VerifiedGarbage.Proof.Ed25519.Group.Extended
import VerifiedGarbage.Proof.Ed25519.RISCV64.PointAccumulate
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The table of `A` on RISC-V

`storeCached` writes the cache of the point of slots 0–3 to entry `s2` of
the table at `TA`, keeping the point and the cached one in slots 4–7
(`storeCached_ok`). `aTable` fills the table's 15 entries with the caches
of `[1]A … [15]A` for `A` in slots 0–3 (`aTable_ok`): `aMult A j` by the
specification's addition, which represents `(j + 1) • A` (`aMult_rep`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Proof.Ed25519 (Rep cache)
open VG.Proof.X25519 (val32_congr)

/-- `[n + 1] p` by the specification's addition. -/
def aMult (p : Spec.Ed25519.Point) : Nat → Spec.Ed25519.Point
  | 0 => p
  | n + 1 => Spec.Ed25519.pointAdd (aMult p n) p

theorem aMult_rep {p : Spec.Ed25519.Point} {a : Edwards.EPoint Proof.Ed25519.dZ} (h : Rep p a) :
    ∀ n, Rep (aMult p n) ((n + 1) • a)
  | 0 => by simp only [aMult, zero_add, one_smul]; exact h
  | n + 1 => by
    rw [aMult, succ_nsmul]
    exact Proof.Ed25519.pointAdd_rep (aMult_rep h n) h

section
variable {b : Addr}

theorem TA_eq : TA = 1632 := rfl

/-- The table's entry `n`. -/
abbrev entryR (b : Addr) (n : Nat) : Region := ⟨b + BitVec.ofNat 64 (TA + 128 * n), 128⟩

theorem entry_FA {n : Nat} (hn : n < 15) : (entryR b n).Disjoint (FA b) :=
  Offset.disjoint _ (.inr (by simp only [TA]; omega)) (by simp only [TA]; omega) (by omega)

theorem slot_entry (i : Slot) {n : Nat} (hn : n < 15) :
    (⟨b + BitVec.ofNat 64 (offset i), 32⟩ : Region).Disjoint (entryR b n) := by
  have := slot_range i
  exact Offset.disjoint _ (.inl (by simp only [TA]; omega)) (by omega) (by simp only [TA]; omega)

theorem storeCached_ok {s : State} (hc : Ctx8 b s) (hd : env s.mem b 16 = Spec.Ed25519.d) {n : Nat}
    (hn : n < 15) (h16 : s.gpr .s2 = BitVec.ofNat 64 n) :
    WP isa storeCached s fun t => Rest (.a4 :: .s0 :: fclob) s t ∧ Frame [FA b, entryR b n] s.mem t.mem ∧
      tableAt t.mem b (TA + 128 * n) = cache (point (env s.mem b) 0 1 2 3) ∧
      point (env t.mem b) 0 1 2 3 = point (env s.mem b) 0 1 2 3 ∧
      point (env t.mem b) 4 5 6 7 = point (env s.mem b) 4 5 6 7 ∧ env t.mem b 16 = env s.mem b 16 := by
  unfold storeCached
  refine WP.seq (WP.mono (fieldCode_ok _ hc.ctx hc.ws) fun s1 ⟨k1, e1⟩ => ?_)
  obtain ⟨c1, p1⟩ := cacheOps_eval (env s.mem b) hd
  rw [← e1] at c1 p1
  have q1 : ∀ i : Slot, 4 ≤ i.val ∧ i.val < 8 ∨ i.val = 16 ∨ i.val = 21 → env s1.mem b i = env s.mem b i :=
    fun i hi => by rw [e1]; exact cacheOps_keep _ i hi
  have hc1 : Ctx8 b s1 := hc.of_keep k1
  refine WP.seq (tableAddr_ok hc1 (n := n) (by decide) (by omega) (by rw [k1.rest.gpr _ (by decide), h16]) fun t1 r1 m1 e14 => ?_)
  have hct1 : Ctx8 b t1 := hc1.of_rest r1 (by decide)
  refine WP.mono (pointToTable_ok hct1 e14 (by simp only [TA]; omega) (by simp only [TA]; omega))
    fun t2 ⟨r2, f2, tb2⟩ => ?_
  rw [m1] at f2 tb2
  have hct2 : Ctx8 b t2 := hct1.of_rest r2 (by decide)
  have k2 : ∀ i : Slot, env t2.mem b i = env s1.mem b i := fun i =>
    env_keep f2 i fun r hr => by rw [List.mem_singleton.mp hr]; exact slot_entry i hn
  refine WP.mono (fieldCode_ok restorePointOps hct2.ctx hct2.ws) fun t ⟨kt, et⟩ => ?_
  obtain ⟨rt0, -, rt16, rt4⟩ := env_restorePoint (env t2.mem b)
  rw [← et] at rt0 rt16 rt4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (k1.rest.mono (by decide)).trans ((r1.mono (by decide)).trans ((r2.mono (by decide)).trans
      (kt.rest.mono (by decide))))
  · exact (k1.frame.mono (by simp)).trans ((f2.mono (by simp)).trans (kt.frame.mono (by simp)))
  · rw [tableAt_keep kt.frame fun r hr => by rw [List.mem_singleton.mp hr]; exact entry_FA hn, tb2, c1]
  · rw [rt0]; simp only [point, k2]; exact p1
  · rw [rt4]; simp only [point, k2, q1 4 (by decide), q1 5 (by decide), q1 6 (by decide), q1 7 (by decide)]
  · rw [rt16, k2, q1 16 (by decide)]

/-- While filling the table of `A`: entries `j < n` written, the sum `aMult A (n - 1)` in slots 0–3
and the cached `A` in slots 4–7. -/
structure ATabInv (b : Addr) (s0 : State) (A : Spec.Ed25519.Point) (n : Nat) (s : State) : Prop where
  lo : 1 ≤ n
  lt : n < 15
  ctx : Ctx8 b s
  rest : Rest (.a4 :: .s0 :: .s2 :: fclob) s0 s
  frame : Frame [FA b, ⟨b + BitVec.ofNat 64 TA, 1920⟩] s0.mem s.mem
  s2 : s.gpr .s2 = BitVec.ofNat 64 n
  pt : point (env s.mem b) 0 1 2 3 = aMult A (n - 1)
  q : point (env s.mem b) 4 5 6 7 = cache A
  table : ∀ j < n, tableAt s.mem b (TA + 128 * j) = cache (aMult A j)
  d : env s.mem b 16 = Spec.Ed25519.d

theorem entry_sub {n : Nat} (hn : n < 15) :
    ∀ r ∈ [entryR b n], ∃ r' ∈ [FA b, (⟨b + BitVec.ofNat 64 TA, 1920⟩ : Region)], Region.Sub r r' :=
  fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨b + BitVec.ofNat 64 TA, 1920⟩, by simp,
      Offset.sub _ (by simp only [TA]; omega) (by simp only [TA]; omega)⟩

theorem entry_sub2 {n : Nat} (hn : n < 15) :
    ∀ r ∈ [FA b, entryR b n], ∃ r' ∈ [FA b, (⟨b + BitVec.ofNat 64 TA, 1920⟩ : Region)], Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨FA b, by simp, fun _ h => h⟩
    · exact entry_sub hn _ (List.mem_singleton_self _)

theorem entries_apart {j n : Nat} (hj : j < 15) (hn : n < 15) (h : j ≠ n) : (entryR b j).Disjoint (entryR b n) := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact Offset.disjoint _ (.inl (by omega)) (by simp only [TA]; omega) (by simp only [TA]; omega)
  · exact Offset.disjoint _ (.inr (by omega)) (by simp only [TA]; omega) (by simp only [TA]; omega)

/-- **The table of `A`**: entries `j < 15` at `TA` are the caches of `aMult A j`. -/
theorem aTable_ok {s : State} (hc : Ctx8 b s) (hd : env s.mem b 16 = Spec.Ed25519.d) :
    WP isa aTable s fun t => Rest (.a4 :: .s0 :: .s2 :: fclob) s t ∧
      Frame [FA b, ⟨b + BitVec.ofNat 64 TA, 1920⟩] s.mem t.mem ∧ Ctx8 b t ∧
      (∀ j < 15, tableAt t.mem b (TA + 128 * j) = cache (aMult (point (env s.mem b) 0 1 2 3) j)) ∧
      env t.mem b 16 = Spec.Ed25519.d := by
  set A := point (env s.mem b) 0 1 2 3 with hA
  unfold aTable aTableInit
  refine WP.seq (WP.seq (wp_li (by decide) fun s1 u1 => WP.block_nil ?_))
  have hc1 : Ctx8 b s1 := hc.of_rest (u1.rest (ws := [.s2]) (by decide)) (by decide)
  refine WP.seq (WP.mono (storeCached_ok hc1 (by rw [u1.mem]; exact hd) (n := 0) (by decide) u1.gpr)
    fun s2 ⟨r2, f2, tb2, p2, _, d2⟩ => ?_)
  rw [u1.mem] at f2 tb2 p2 d2
  have hc2 : Ctx8 b s2 := hc1.of_rest r2 (by decide)
  refine tableAddr_ok hc2 (n := 0) (by decide) (by decide)
    (by rw [r2.gpr _ (by decide), u1.gpr]) fun t1 r3 m3 e3 => ?_
  have hct1 : Ctx8 b t1 := hc2.of_rest r3 (by decide)
  refine WP.append (pointFromTableQ_ok hct1 e3 (fun k hk => by
      rw [Offset.add_add]; exact hct1.inR (by rw [TA_eq]; omega))
    (Offset.disjoint _ (.inr (by rw [TA_eq]; omega)) (by rw [TA_eq]; omega) (by omega)))
    fun t2 ⟨r4, f4, q4, k4⟩ => ?_
  refine wp_li (by decide) fun t3 u5 => WP.block_nil ?_
  rw [tableAt_shift, m3, tb2] at q4
  have hc3 : Ctx8 b t3 := (hct1.of_rest r4 (by decide)).of_rest (u5.rest (ws := [.s2]) (by decide)) (by decide)
  have m35 : t3.mem = t2.mem := u5.mem
  have hF3 : Frame [FA b, ⟨b + BitVec.ofNat 64 TA, 1920⟩] s.mem t3.mem := by
    rw [m35]
    refine ((f2.sub (entry_sub2 (n := 0) (by omega))).trans ?_)
    rw [← m3]
    exact f4.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨FA b, by simp, Offset.sub _ (by omega) (by omega)⟩
  have kq : ∀ i : Slot, (i.val < 4 ∨ 8 ≤ i.val) → env t3.mem b i = env s2.mem b i := fun i hi => by
    rw [m35, k4 i hi, m3]
  have I0 : ATabInv b s A 1 t3 := by
    refine ⟨le_rfl, by decide, hc3, ?_, hF3, u5.gpr, ?_, ?_, fun j hj => ?_, ?_⟩
    · exact (u1.rest (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
        ((r4.mono (by decide)).trans (u5.rest (by decide)))))
    · have e : point (env t3.mem b) 0 1 2 3 = point (env s2.mem b) 0 1 2 3 := by
        simp only [point, kq 0 (by decide), kq 1 (by decide), kq 2 (by decide), kq 3 (by decide)]
      rw [e, p2]; rfl
    · rw [m35]; simpa only [Nat.mul_zero, Nat.add_zero] using q4
    · obtain rfl : j = 0 := by omega
      rw [m35, tableAt_keep f4 fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inr (by rw [TA_eq]; omega)) (by rw [TA_eq]; omega) (by omega), m3, tb2]
      rfl
    · rw [kq 16 (by decide), d2, hd]
  refine WP.loop (M := isa) (fun m t => ∃ n, m = 15 - n ∧ ATabInv b s A n t) ?_ 14 t3 ⟨1, rfl, I0⟩
  rintro m t ⟨n, rfl, h⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := h.lo; omega⟩
  have hlt := h.lt
  unfold aTableBody
  refine WP.seq (WP.mono (fieldCode_ok pointAddCachedOps h.ctx.ctx h.ctx.ws) fun v1 ⟨kv1, ev1⟩ => ?_)
  have hcv1 : Ctx8 b v1 := h.ctx.of_keep kv1
  have pv1 : point (env v1.mem b) 0 1 2 3 = aMult A (n' + 1) := by
    rw [ev1, pointAddCached_eval _ A h.q, h.pt]; rfl
  have kv : ∀ i : Slot, 4 ≤ i.val ∧ i.val < 8 ∨ 16 ≤ i.val → env v1.mem b i = env t.mem b i := fun i hi => by
    rw [ev1]; exact pointAddCached_keep _ i hi
  have qv1 : point (env v1.mem b) 4 5 6 7 = cache A := by
    simp only [point, kv 4 (by decide), kv 5 (by decide), kv 6 (by decide), kv 7 (by decide)]
    exact h.q
  have dv1 : env v1.mem b 16 = Spec.Ed25519.d := by rw [kv 16 (by decide)]; exact h.d
  refine WP.seq (WP.mono (storeCached_ok hcv1 dv1 (n := n' + 1) h.lt (by rw [kv1.rest.gpr _ (by decide), h.s2]))
    fun v2 ⟨r6, f6, tb6, p6, q6, d6⟩ => ?_)
  have hcv2 : Ctx8 b v2 := hcv1.of_rest r6 (by decide)
  refine wp_addi (by decide) fun v3 u7 => wp_subi (imm := 15) (by decide) fun v4 u8 => WP.block_nil ?_
  have e16 : v4.gpr .s2 = BitVec.ofNat 64 (n' + 1 + 1) := by
    rw [u8.other _ (by decide), u7.gpr, r6.gpr _ (by decide), kv1.rest.gpr _ (by decide), h.s2]
    exact (BitVec.ofNat_add (n' + 1) 1).symm
  have e7 : (v4.gpr .a4 != 0) = decide (n' + 1 + 1 ≠ 15) := by
    rw [u8.gpr, u7.gpr, r6.gpr _ (by decide), kv1.rest.gpr _ (by decide), h.s2,
      show BitVec.ofNat 64 (n' + 1) + BitVec.ofNat 64 1 = BitVec.ofNat 64 (n' + 1 + 1) from (BitVec.ofNat_add _ _).symm,
      ofNat_sub_ne_zero (by omega) (by omega)]
  have m4 : v4.mem = v2.mem := by rw [u8.mem, u7.mem]
  have hc4 : Ctx8 b v4 :=
    hcv2.of_rest ((u7.rest (ws := [.s2, .a4]) (by decide)).trans (u8.rest (ws := [.s2, .a4]) (by decide))) (by decide)
  have hR : Rest (.a4 :: .s0 :: .s2 :: fclob) s v4 :=
    h.rest.trans ((kv1.rest.mono (by decide)).trans ((r6.mono (by decide)).trans
      ((u7.rest (by decide)).trans (u8.rest (by decide)))))
  have hF : Frame [FA b, ⟨b + BitVec.ofNat 64 TA, 1920⟩] s.mem v4.mem := by
    rw [m4]
    exact h.frame.trans ((kv1.frame.mono (by simp)).trans (f6.sub (entry_sub2 h.lt)))
  have hT : ∀ j < n' + 1 + 1, tableAt v4.mem b (TA + 128 * j) = cache (aMult A j) := by
    intro j hj
    rw [m4]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [tableAt_keep f6 fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact entry_FA (by have := h.lt; omega)
          · exact entries_apart (by have := h.lt; omega) h.lt (by omega),
        tableAt_keep kv1.frame fun r hr => by
          rw [List.mem_singleton.mp hr]; exact entry_FA (by have := h.lt; omega)]
      exact h.table j hj
    · rw [tb6, pv1]
  have hP : point (env v4.mem b) 0 1 2 3 = aMult A (n' + 1) := by rw [m4, p6, pv1]
  have hQ : point (env v4.mem b) 4 5 6 7 = cache A := by rw [m4, q6, qv1]
  have hD : env v4.mem b 16 = Spec.Ed25519.d := by rw [m4, d6, dv1]
  rw [eval_nonzero, e7]
  by_cases hl : n' + 1 + 1 = 15
  · exact .inl ⟨by simp [hl], hR, hF, hc4, fun j hj => hT j (by omega), hD⟩
  · exact .inr ⟨by simp [hl], 15 - (n' + 1 + 1), by omega, n' + 1 + 1, rfl,
      ⟨by omega, by have := h.lt; omega, hc4, hR, hF, e16, hP, hQ, hT, hD⟩⟩
end

end VG.Proof.Ed25519.RISCV64
