import VerifiedGarbage.Proof.Ed448.Arm.ScalarIO
import VerifiedGarbage.TCB.Arm.Target

/-!
# Ed448 scalar reduction on ARMv7: the whole function

`vg_ed448_scalar_reduce(out = r0, wide = r1, scratch = r2)` against a local
contract (`scalarReduceLocal`), the ABI included.
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X25519.Arm
open VG.Spec.Ed448 (L bytesAt decodeLE encodeLE)

def scalarReduceLocal : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 57⟩
    let wide : Region := ⟨State.addr (s.gpr .r1), 114⟩
    let ws : Region := ⟨State.addr (s.gpr .r2), 8192⟩
    s.rd = [wide] ∧ s.wr = [out, ws] ∧ out.Disjoint wide ∧ out.Disjoint ws ∧
      wide.Disjoint ws ∧ (s.gpr .r0).toNat + 57 ≤ 2 ^ 32 ∧
      (s.gpr .r1).toNat + 114 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32
  post s t := bytesAt t.mem (State.addr (s.gpr .r0)) 57 =
    Spec.Ed448.scalarReduce (bytesAt s.mem (State.addr (s.gpr .r1)) 114)
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2

structure ReducePre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r1), 114⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r0), 57⟩, ⟨State.addr (s.gpr .r2), 8192⟩]
  out_wide : (⟨State.addr (s.gpr .r0), 57⟩ : Region).Disjoint ⟨State.addr (s.gpr .r1), 114⟩
  out_ws : (⟨State.addr (s.gpr .r0), 57⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩
  wide_ws : (⟨State.addr (s.gpr .r1), 114⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩
  f0 : (s.gpr .r0).toNat + 57 ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + 114 ≤ 2 ^ 32
  f2 : (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32

theorem ReducePre.of {s : State} (h : scalarReduceLocal.pre s) : ReducePre s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem ctx8_of {b : BitVec 32} {s : State} (h0 : s.gpr .r0 = b) (hfit : b.toNat + 8192 ≤ 2 ^ 32)
    (hw : (⟨State.addr b, 8192⟩ : Region) ∈ s.wr) : Ctx8 b s := ⟨h0, hfit, hw⟩

theorem reduceSetup_ok {s : State} (h : ReducePre s) :
    WP isa (.block (saveAt .r2 ++ ([.str .r0 .r2 OUT, .mov .r0 (.reg .r2), .mov .r12 (.reg .r1),
      .movw .r6 0xffff] : List Instr))) s fun t =>
      Ctx8 (s.gpr .r2) t ∧ t.gpr .r6 = mask16 ∧ t.gpr .r12 = s.gpr .r1 ∧
      Saved (State.addr (s.gpr .r2)) s.gpr t.mem ∧
      t.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 OUT) 32 = s.gpr .r0 ∧
      Rest [.r0, .r6, .r12] s t ∧ Frame [⟨State.addr (s.gpr .r2), 36⟩] s.mem t.mem := by
  have hw : (⟨State.addr (s.gpr .r2), 8192⟩ : Region) ∈ s.wr := by rw [h.wr]; simp
  have hO := OUT_eq
  refine WP.append (saveAt_ok rfl h.f2 hw) fun u ⟨su, fu, gu, ku⟩ => ?_
  refine wp_str (a := State.addr (s.gpr .r2) + BitVec.ofNat 64 32) (by decide)
    (by rw [gu]; exact addr_add (by have := h.f2; omega))
    (by rw [ku.wr]; exact in_base hw (by decide) (by decide)) fun v hv => ?_
  refine wp_mov (op2_reg _ _) fun w hw' => wp_mov (op2_reg _ _) fun x hx =>
    wp_movw fun t ht => WP.block_nil ?_
  have kt : Rest [.r0, .r6, .r12] s t :=
    (ku.mono (by decide)).trans ((hv.rest _).trans ((hw'.rest (by decide)).trans
      ((hx.rest (by decide)).trans (ht.rest (by decide)))))
  have mt : t.mem = u.mem.writeW (State.addr (s.gpr .r2) + BitVec.ofNat 64 32) (s.gpr .r0) := by
    rw [ht.mem, hx.mem, hw'.mem, hv.mem, gu]
  refine ⟨ctx8_of ?_ h.f2 (by rw [kt.wr]; exact hw), ht.gpr, ?_, ?_, ?_, kt, ?_⟩
  · rw [ht.other _ (by decide), hx.other _ (by decide), hw'.gpr, hv.gpr, gu]
  · rw [ht.other _ (by decide), hx.gpr, hw'.other _ (by decide), hv.gpr, gu]
  · intro i hi
    rw [mt, Mem.readW_writeW_sep (Offset.sep _ (d := 4 * i) (e := 32) (n := 4) (k := 4) (by omega)
      (by omega) (by omega)) (by decide)]
    exact su i hi
  · rw [mt]; exact Mem.readW_writeW_self32 _ _ _
  · rw [mt]
    exact (fu.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))

theorem RA_buf : Buf RA := ⟨by decide, by decide⟩

theorem reduce_regions_sub {b : BitVec 32} {r : Region} (h : r ∈ [limbsR b TF, limbsR b RA]) :
    r.Sub ⟨State.addr b, 8192⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> exact Offset.sub_base _ (by decide)

theorem scalarReduce_correct {s : State} (h : ReducePre s) :
    WP isa scalarReduce s fun t => abiPreserved s t ∧ scalarReduceLocal.post s t := by
  have hT := TF_eq
  have hO := OUT_eq
  have hR : RA = 192 := rfl
  unfold scalarReduce
  refine WP.seq (WP.mono (reduceSetup_ok h) fun u ⟨hcu, h6u, pu, su, ou, ku, fu⟩ => ?_)
  have wide : (⟨State.addr (s.gpr .r1), 114⟩ : Region) ∈ s.rd ++ s.wr := by rw [h.rd]; simp
  refine WP.seq (WP.mono (reduce114_ok RA_buf hcu h6u pu h.f1
    (fun n hn => by rw [ku.rd, ku.wr]; exact in_base wide (by omega) (by omega))
    (fun r hr => h.wide_ws.sub_right (reduce_regions_sub hr))) fun v ⟨kv, lv, vv⟩ => ?_)
  have sv : Saved (State.addr (s.gpr .r2)) s.gpr v.mem :=
    su.frame kv.frame fun r hr i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
  have ov : v.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 OUT) 32 = s.gpr .r0 := by
    rw [kv.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), ou]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
  refine WP.mono (finish_ok (by decide) (hcu.of_rest kv.rest (by decide)) lv ov h.f0
    (by rw [kv.rest.wr, ku.wr, h.wr]; simp) h.out_ws sv) fun t ⟨gt, kt, _, bt⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [kt.sp, kv.rest.sp, ku.sp]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact gt 0 (by decide)
    · exact gt 1 (by decide)
    · exact gt 2 (by decide)
    · exact gt 3 (by decide)
    · exact gt 4 (by decide)
    · exact gt 5 (by decide)
    · exact gt 6 (by decide)
    · exact gt 7 (by decide)
    · rw [kt.gpr _ (by decide), kv.rest.gpr _ (by decide), ku.gpr _ (by decide)]
  · change bytesAt t.mem _ 57 = encodeLE 57 _
    rw [bt, vv]
    refine congrArg (fun bs => encodeLE 57 (decodeLE bs % L)) ?_
    exact bytesAt_frame fu (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact h.wide_ws.sub_right (Region.sub_prefix (by decide)))
      (by decide)

end VG.Proof.Ed448.Arm
