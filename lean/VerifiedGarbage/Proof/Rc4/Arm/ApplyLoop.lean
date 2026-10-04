import VerifiedGarbage.Proof.Rc4.Arm.ApplyStep
import VerifiedGarbage.Proof.Rc4.Update

/-! # RC4 on ARMv7: the stream loop -/

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc4.Arm VG.Spec.Rc4 VG.Proof.Rc4

/-- The context and output after the first `k` data bytes, from memory `m`. -/
def upd (m : Mem) (P D : BitVec 32) (k : Nat) : Context × List Byte :=
  update (contextAt m (State.addr P)) (bytesAt m (State.addr D) k)

theorem upd_succ (m : Mem) (P D : BitVec 32) (k : Nat) :
    upd m P D (k + 1) = ((step (upd m P D k).1).1, (upd m P D k).2 ++
      [m (State.addr D + BitVec.ofNat 64 k) ^^^ (step (upd m P D k).1).2]) := by
  unfold upd
  rw [bytes_snoc, update_snoc]

/-- What the stream loop writes: the table and the data. -/
def loopRegions (P D L : BitVec 32) : List Region :=
  [⟨State.addr P, 256⟩, ⟨State.addr D, L.toNat⟩]

/-- The stream loop after `k` bytes, from the state `b` it started in; `m₀`
is the memory on entry, which differs from `b`'s only outside the context
and the data. -/
structure LoopInv (m₀ : Mem) (P D L : BitVec 32) (b : State) (k : Nat) (t : State) : Prop where
  le : k ≤ L.toNat
  table : (contextAt t.mem (State.addr P)).table = (upd m₀ P D k).1.table
  i : t.gpr .r4 = (upd m₀ P D k).1.i.setWidth 32
  j : t.gpr .r5 = (upd m₀ P D k).1.j.setWidth 32
  data : bytesAt t.mem (State.addr D) k = (upd m₀ P D k).2
  tail : ∀ x, k ≤ x → x < L.toNat →
    t.mem (State.addr D + BitVec.ofNat 64 x) = m₀ (State.addr D + BitVec.ofNat 64 x)
  frame : Frame (loopRegions P D L) b.mem t.mem
  count : t.gpr .r0 = BitVec.ofNat 32 k
  keep : Keep stepRegs b t

/-- A byte outside the table and the data byte an iteration writes. -/
theorem step_other {m : Mem} {p d x : Addr} {ii jj : Byte} {w : Byte}
    (hT : ¬ (x - p).toNat < 256) (hD : x ≠ d) :
    (((m.write (p + BitVec.ofNat 64 jj.toNat) 1 (m (p + BitVec.ofNat 64 ii.toNat))).write
      (p + BitVec.ofNat 64 ii.toNat) 1 (m (p + BitVec.ofNat 64 jj.toNat))).write d 1 w) x =
      m x := by
  rw [write_byte, ite_eq_right hD]
  exact swap_frame m p ii jj x hT

/-- The concrete stream iteration realizes the abstract PRGA transition. -/
theorem apply_step_table (t : State) (i j : Byte) {P D L : BitVec 32} {k : Nat}
    (he : StepEnv t P D L) (h4 : t.gpr .r4 = i.setWidth 32) (h5 : t.gpr .r5 = j.setWidth 32)
    (h0 : t.gpr .r0 = BitVec.ofNat 32 k) (hk : k < L.toNat) :
    let next := step { table := (contextAt t.mem (State.addr P)).table, i, j }
    WP isa (.block applyStep) t fun u =>
      (contextAt u.mem (State.addr P)).table = next.1.table ∧
      u.gpr .r4 = next.1.i.setWidth 32 ∧ u.gpr .r5 = next.1.j.setWidth 32 ∧
      u.mem (State.addr D + BitVec.ofNat 64 k) =
        t.mem (State.addr D + BitVec.ofNat 64 k) ^^^ next.2 ∧
      (∀ x, ¬ (x - State.addr P).toNat < 256 → x ≠ State.addr D + BitVec.ofNat 64 k →
        u.mem x = t.mem x) ∧
      Frame (loopRegions P D L) t.mem u.mem ∧
      u.gpr .r0 = BitVec.ofNat 32 (k + 1) ∧
      u.z = (BitVec.ofNat 32 (k + 1) - L == 0#32) ∧ Keep stepRegs t u := by
  dsimp only
  rw [step_eq]
  dsimp only
  simp only [table_get]
  have hone : (1 : Byte) = 1#8 := rfl
  simp only [hone]
  refine WP.mono (apply_step t i j he h4 h5 h0 hk)
    fun u ⟨hum, hu4, hu5, hu0, huz, huk⟩ => ?_
  have hdk : ¬ (State.addr D + BitVec.ofNat 64 k - State.addr P).toNat < 256 := by
    have hin : (State.addr D + BitVec.ofNat 64 k - State.addr D).toNat < L.toNat := by
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hk
    exact fun h => he.sTD _ h hin
  have hTD : Mem.Sep (State.addr P) 256 (State.addr D + BitVec.ofNat 64 k) 1 :=
    sep_offset_right he.sTD (by omega) (by omega)
  refine ⟨?_, hu4, hu5, ?_, ?_, ?_, hu0, huz, huk⟩
  · rw [hum, table_write_sep _ _ _ _ hTD, table_swap]
  · rw [hum, write_byte, ite_eq_left rfl, swap_frame _ _ _ _ _ hdk]
    have ht := table_swap t.mem (State.addr P) (i + 1#8)
      (j + t.mem (State.addr P + BitVec.ofNat 64 (i + 1#8).toNat))
    rw [← ht, table_get]
  · intro x hT hD
    rw [hum]
    exact step_other hT hD
  · rw [hum]
    have hP : (⟨State.addr P, 256⟩ : Region) ∈ loopRegions P D L := List.mem_cons_self
    have hD : (⟨State.addr D, L.toNat⟩ : Region) ∈ loopRegions P D L :=
      List.mem_cons_of_mem _ List.mem_cons_self
    refine Frame.write ?_ hD _ (Offset.contains_base _ (by omega) (by omega))
    refine Frame.write ?_ hP _ (Offset.contains_base _ (by omega) (by omega))
    exact Frame.write (Frame.refl _ _) hP _ (Offset.contains_base _ (by omega) (by omega))

theorem loop_step (m₀ : Mem) {P D L : BitVec 32} (b : State) (hb : StepEnv b P D L) {k : Nat}
    (hk : k < L.toNat) (t : State) (ht : LoopInv m₀ P D L b k t) :
    WP isa (.block applyStep) t fun u => LoopInv m₀ P D L b (k + 1) u ∧
      u.z = (BitVec.ofNat 32 (k + 1) - L == 0#32) := by
  have he := hb.keep ht.keep (by decide)
  have hsD : ∀ x, x < L.toNat →
      ¬ (State.addr D + BitVec.ofNat 64 x - State.addr P).toNat < 256 := by
    intro x hx
    have hin : (State.addr D + BitVec.ofNat 64 x - State.addr D).toNat < L.toNat := by
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hx
    exact fun h => hb.sTD _ h hin
  have hctx : (⟨(contextAt t.mem (State.addr P)).table, (upd m₀ P D k).1.i,
      (upd m₀ P D k).1.j⟩ : Context) = (upd m₀ P D k).1 := context_ext ht.table rfl rfl
  have hst := apply_step_table t (upd m₀ P D k).1.i (upd m₀ P D k).1.j he ht.i ht.j ht.count hk
  rw [hctx] at hst
  refine WP.mono hst fun u ⟨htab, hui, huj, hbyte, hother, hfr, hu0, huz, huk⟩ => ⟨?_, huz⟩
  have hkeep : ∀ x, x < L.toNat → x ≠ k →
      u.mem (State.addr D + BitVec.ofNat 64 x) = t.mem (State.addr D + BitVec.ofNat 64 x) :=
    fun x hx hne => hother _ (hsD x hx) (data_ne hx hk hne)
  refine
    { le := hk
      table := by rw [upd_succ]; exact htab
      i := by rw [upd_succ]; exact hui
      j := by rw [upd_succ]; exact huj
      data := ?_
      tail := fun x hx hxL => by
        rw [hkeep x hxL (by omega)]
        exact ht.tail x (by omega) hxL
      frame := ht.frame.trans hfr
      count := hu0
      keep := (ht.keep.trans huk).mono (by decide) }
  rw [bytes_snoc, upd_succ, hbyte, ht.tail k (Nat.le_refl _) hk, ← ht.data]
  refine congrArg (· ++ _) ?_
  exact bytes_frame _ _ _ _ fun x hx => hkeep x (by omega) (by omega)

theorem apply_loop (m₀ : Mem) {P D L : BitVec 32} (b : State) (hb : StepEnv b P D L) {k : Nat}
    (hk : k < L.toNat) (t : State) (ht : LoopInv m₀ P D L b k t) :
    WP isa (.loop (.block applyStep) .ne) t (LoopInv m₀ P D L b L.toNat) := by
  refine WP.loop (M := isa)
    (fun rem u => ∃ j, j < L.toNat ∧ rem = L.toNat - j ∧ LoopInv m₀ P D L b j u)
    ?_ (L.toNat - k) t ⟨k, hk, rfl, ht⟩
  intro rem u ⟨j, hj, hrem, hu⟩
  refine WP.mono (loop_step m₀ b hb hj u hu) fun v ⟨hv, hz⟩ => ?_
  by_cases hend : j + 1 = L.toNat
  · left
    refine ⟨?_, hend ▸ hv⟩
    rw [hend, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.sub_self] at hz
    rw [eval_ne, hz]
    rfl
  · right
    have hL := L.isLt
    have hnz : BitVec.ofNat 32 (j + 1) - L ≠ 0#32 := by
      intro h
      have h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h'
      omega
    refine ⟨?_, L.toNat - (j + 1), by omega, j + 1, by omega, rfl, hv⟩
    rw [eval_ne, hz, beq_eq_false_iff_ne.mpr hnz]
    rfl

end VG.Proof.Rc4.Arm
