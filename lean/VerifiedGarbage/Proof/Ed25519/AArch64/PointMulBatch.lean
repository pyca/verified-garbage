import VerifiedGarbage.Impl.Ed25519.AArch64.Bits
import VerifiedGarbage.Impl.Ed25519.AArch64.PointPowers
import VerifiedGarbage.Impl.Ed25519.AArch64.PointTable
import VerifiedGarbage.Impl.Ed25519.AArch64.PointLoop
import VerifiedGarbage.Impl.Ed25519.AArch64.FieldMemory
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddVerified
import VerifiedGarbage.Proof.Ed25519.BaseTable
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Impl.Ed25519.AArch64.PointSelect
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddVerified
import VerifiedGarbage.Proof.Ed25519.Canonical64
import VerifiedGarbage.Impl.Ed25519.AArch64.PointMul

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.Points`. -/
section

/-! Exact extended-coordinate operations and the slots they preserve. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def fieldDest : FieldOp → Slot
  | .copy o _ | .const o _ | .mul o _ _ | .sqr o _ | .add o _ _ | .sub o _ _ => o

theorem evalOp_unchanged (op : FieldOp) (e : Env) (i : Slot) (hi : i ≠ VG.Proof.Ed25519.AArch64.fieldDest op) :
    evalOp op e i = e i := by
  cases op <;> exact Function.update_of_ne hi _ _

theorem evalOps_unchanged (ops : List FieldOp) (e : Env) (i : Slot)
    (hi : ∀ op ∈ ops, i ≠ VG.Proof.Ed25519.AArch64.fieldDest op) : evalOps ops e i = e i := by
  induction ops generalizing e with
  | nil => rfl
  | cons op ops ih =>
    change evalOps ops (evalOp op e) i = e i
    rw [ih (evalOp op e) (fun p hp => hi p (List.mem_cons_of_mem _ hp)), VG.Proof.Ed25519.AArch64.evalOp_unchanged op e i (hi op (by simp))]

theorem point_ops_high (ops : List FieldOp) (hops : ∀ op ∈ ops, (VG.Proof.Ed25519.AArch64.fieldDest op).val < 16)
    (e : Env) (i : Slot) (hi : 16 ≤ i.val) : evalOps ops e i = e i := by
  apply VG.Proof.Ed25519.AArch64.evalOps_unchanged
  intro op hop heq
  have h := hops op hop
  have := congrArg Fin.val heq
  omega

theorem pointAdd_high (e : Env) (i : Slot) (hi : 16 ≤ i.val) :
    evalOps pointAddOps e i = e i :=
  VG.Proof.Ed25519.AArch64.point_ops_high _ (by decide) e i hi

theorem pointDouble_high (e : Env) (i : Slot) (hi : 16 ≤ i.val) :
    evalOps pointDoubleOps e i = e i :=
  VG.Proof.Ed25519.AArch64.point_ops_high _ (by decide) e i hi

theorem constPoint_eval (p : Spec.Ed25519.Point) (e : Env) :
    VG.Proof.Ed25519.AArch64.point (evalOps (constPointOps p) e) 0 1 2 3 = p := by cases p; rfl

theorem restorePoint_eval (e : Env) :
    VG.Proof.Ed25519.AArch64.point (evalOps restorePointOps e) 0 1 2 3 = VG.Proof.Ed25519.AArch64.point e 17 18 19 20 := rfl

theorem pointDouble_ok {s : State} {base : Addr} (hs : Scr s base)
    (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block pointDouble) s fun t =>
      Keep base s t ∧ VG.Proof.Ed25519.AArch64.point (env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointAdd (VG.Proof.Ed25519.AArch64.point (env s.mem base) 0 1 2 3) (VG.Proof.Ed25519.AArch64.point (env s.mem base) 0 1 2 3) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i := by
  refine WP.mono (fieldCode_ok pointDoubleOps hs) fun t ⟨hk, hv⟩ => ?_
  rw [hv]
  exact ⟨hk, pointDouble_eval _ hd, VG.Proof.Ed25519.AArch64.pointDouble_high _⟩

theorem pointAdd_ok {s : State} {base : Addr} (hs : Scr s base)
    (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block pointAdd) s fun t =>
      Keep base s t ∧ VG.Proof.Ed25519.AArch64.point (env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointAdd (VG.Proof.Ed25519.AArch64.point (env s.mem base) 0 1 2 3) (VG.Proof.Ed25519.AArch64.point (env s.mem base) 4 5 6 7) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i := by
  refine WP.mono (fieldCode_ok pointAddOps hs) fun t ⟨hk, hv⟩ => ?_
  rw [hv]
  exact ⟨hk, pointAdd_eval _ hd, VG.Proof.Ed25519.AArch64.pointAdd_high _⟩

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.PointLoop`. -/
section

/-! Sixteen exact doublings, preserving the saved accumulator. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64


structure DoubleKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ≠ .x1 → r ∉ clob → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base 64 704 s.mem t.mem

theorem DoubleKeep.refl (base : Addr) (s : State) : VG.Proof.Ed25519.AArch64.DoubleKeep base s s :=
  ⟨fun _ _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem DoubleKeep.trans {base : Addr} {s t u : State} (h : VG.Proof.Ed25519.AArch64.DoubleKeep base s t)
    (k : VG.Proof.Ed25519.AArch64.DoubleKeep base t u) : VG.Proof.Ed25519.AArch64.DoubleKeep base s u :=
  ⟨fun r hr hc => (k.gpr r hr hc).trans (h.gpr r hr hc), k.rd.trans h.rd,
    k.wr.trans h.wr, k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem DoubleKeep.scratch {base : Addr} {s t : State} (h : VG.Proof.Ed25519.AArch64.DoubleKeep base s t) (hs : Scr s base) :
    Scr t base := ⟨(h.gpr _ (by decide) (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem point_counter_nonzero : ∀ n < 16,
    (BitVec.ofNat 64 n != 0) = decide (n ≠ 0) := by decide

theorem doubleDec_ok (s : State) (n : Nat)
    (hc : s.gpr .x1 = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block [.subImm .x .x1 .x1 1]) s fun t =>
      t.gpr .x1 = BitVec.ofNat 64 n ∧ Keeps [.x1] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (1 : Nat) < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, hc, BitVec.ofNat_add, BitVec.add_sub_cancel]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

theorem doubleBody_ok {s : State} {base : Addr} (hs : Scr s base) (n : Nat)
    (hc : s.gpr .x1 = BitVec.ofNat 64 (n + 1)) (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block doubleBody) s fun t =>
      t.gpr .x1 = BitVec.ofNat 64 n ∧
      VG.Proof.Ed25519.AArch64.point (env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointAdd (VG.Proof.Ed25519.AArch64.point (env s.mem base) 0 1 2 3) (VG.Proof.Ed25519.AArch64.point (env s.mem base) 0 1 2 3) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧ VG.Proof.Ed25519.AArch64.DoubleKeep base s t := by
  rw [doubleBody, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.pointDouble_ok hs hd) fun t ⟨hk, hv, hi⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.AArch64.doubleDec_ok t n ((hk.gpr _ (by decide)).trans hc)) fun u ⟨hcu, ku⟩ => ?_
  refine ⟨hcu, ?_, ?_, ?_⟩
  · rw [ku.mem]; exact hv
  · rw [ku.mem]; exact hi
  · exact ⟨fun r hr hc => (ku.gpr r (by simpa using hr)).trans (hk.gpr r hc),
      ku.rd.trans hk.rd, ku.wr.trans hk.wr, ku.sp.trans hk.sp, by rw [ku.mem]; exact hk.mem⟩

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.PointTableAddr`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.PointTable`. -/
section
/-! Point table accesses remain within the caller's scratch argument. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64

theorem tableWords_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (hp : s.gpr .x8 = off base o) (dst : Nat) (ha : dst % 8 = 0) (ho : o + dst + 32 ≤ 8192) :
    WP isa (.block (tableWords dst)) s fun t =>
      t.mem = st4 s.mem base (o + dst) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 :=
    fun d hd => ⟨_, hs.wr, Offset.contains_base _ hd (by omega)⟩
  apply WP.of_runBlock
  simp (disch := omega) only [tableWords, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
    Size.bytes, hp, off, Offset.add_add, State.store, read_x, BitVec.setWidth_eq,
    w (o + dst) (by omega), w (o + (dst + 8)) (by omega),
    w (o + (dst + 16)) (by omega), w (o + (dst + 24)) (by omega), ite_eq_left, ite_true,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, True.intro, True.intro, True.intro, True.intro⟩
  simp only [st4, write64_eq_writeW, Nat.add_assoc]

theorem fromTableWords_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (hp : s.gpr .x8 = off base o) (src : Nat) (ha : src % 8 = 0) (ho : o + src + 32 ≤ 8192) :
    WP isa (.block (fromTableWords src)) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) = fe s.mem base (o + src) ∧
      Keeps [.x4, .x5, .x6, .x7] s t := by
  have r : ∀ d, d + 8 ≤ 8192 → InRegions (s.rd ++ s.wr) (off base d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ hd (by omega)⟩
  apply WP.of_runBlock
  simp (disch := omega) only [fromTableWords, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
    Size.bytes, State.load, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hp, off, Offset.add_add, BitVec.setWidth_eq,
    r (o + src) (by omega), r (o + (src + 8)) (by omega),
    r (o + (src + 16)) (by omega), r (o + (src + 24)) (by omega),
    ite_eq_left, ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [fe, VG.Proof.Ed25519.AArch64.word, off, Nat.add_assoc]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

structure TableKeep (base : Addr) (o n : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.x4, .x5, .x6, .x7] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base o n s.mem t.mem

theorem TableKeep.scratch {s t : State} {base : Addr} {o n : Nat}
    (h : VG.Proof.Ed25519.AArch64.TableKeep base o n s t) (hs : Scr s base) : Scr t base :=
  ⟨(h.gpr _ (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem TableKeep.trans {s t u : State} {base : Addr} {o n : Nat}
    (h : VG.Proof.Ed25519.AArch64.TableKeep base o n s t) (k : VG.Proof.Ed25519.AArch64.TableKeep base o n t u) : VG.Proof.Ed25519.AArch64.TableKeep base o n s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem TableKeep.mono {s t : State} {base : Addr} {o n o' n' : Nat}
    (h : VG.Proof.Ed25519.AArch64.TableKeep base o n s t) (ho : o' ≤ o) (hn : o + n ≤ o' + n') : VG.Proof.Ed25519.AArch64.TableKeep base o' n' s t :=
  ⟨h.gpr, h.rd, h.wr, h.sp, h.mem.mono ho hn⟩

theorem table_env {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') (ho : 768 ≤ o) : env m' base = env m base := by
  funext i
  simp only [env, F]
  rw [h.fe (by simp only [offset]; omega) (by simp only [offset]; omega)]

theorem toTableQuarter_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (hp : s.gpr .x8 = off base o) (j : Nat) (hj : j < 4) (ho : o + 128 ≤ 8192) :
    WP isa (.block (loads (64 + 32 * j) .x4 .x5 .x6 .x7 ++ tableWords (32 * j))) s fun t =>
      F t.mem base (o + 32 * j) = env s.mem base ⟨j, by omega⟩ ∧ VG.Proof.Ed25519.AArch64.TableKeep base (o + 32 * j) 32 s t := by
  rw [WP.block_append_iff]
  refine WP.mono (loadsField_ok hs ⟨j, by omega⟩) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.AArch64.tableWords_ok (hs.of_keeps hk (by decide))
    ((hk.gpr _ (by decide)).trans hp) (32 * j) (by omega) (by omega)) fun u ⟨hm, hg, hrd, hwr, hsp⟩ => ?_
  refine ⟨?_, ⟨fun r hr => (congrFun hg r).trans (hk.gpr r hr), hrd.trans hk.rd,
    hwr.trans hk.wr, hsp.trans hk.sp, ?_⟩⟩
  · rw [F, hm, fe_st4 _ _ (by omega), hv]
    rfl
  · rw [hm, hk.mem]; exact st4_outside _ _ (by omega) _ _ _ _

theorem toTablePrefix_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (hp : s.gpr .x8 = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192)
    (n : Nat) (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap fun j =>
      loads (64 + 32 * j) .x4 .x5 .x6 .x7 ++ tableWords (32 * j))) s fun t =>
      (∀ j (hj : j < n), F t.mem base (o + 32 * j) = env s.mem base ⟨j, by omega⟩) ∧
      VG.Proof.Ed25519.AArch64.TableKeep base o (32 * n) s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨fun j hj => by omega,
      ⟨fun _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs hp (by omega)) fun t ⟨hv, hk⟩ => ?_
    refine WP.mono (VG.Proof.Ed25519.AArch64.toTableQuarter_ok (hk.scratch hs)
      ((hk.gpr _ (by decide)).trans hp) n (by omega) ho) fun u ⟨hu, ku⟩ => ?_
    refine ⟨fun j hj => ?_, (hk.mono (by omega) (by omega)).trans
      (ku.mono (by omega) (by omega))⟩
    by_cases h : j < n
    · rw [Outside_F ku.mem (by omega) (Or.inl (by omega)), hv j h]
    · have he : j = n := by omega
      subst j
      rw [hu, VG.Proof.Ed25519.AArch64.table_env hk.mem hlo]

def tablePoint (m : Mem) (base : Addr) (o : Nat) : Spec.Ed25519.Point :=
  ⟨F m base o, F m base (o + 32), F m base (o + 64), F m base (o + 96)⟩

theorem pointToTable_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (hp : s.gpr .x8 = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block pointToTable) s fun t =>
      VG.Proof.Ed25519.AArch64.tablePoint t.mem base o = VG.Proof.Ed25519.AArch64.point (env s.mem base) 0 1 2 3 ∧ VG.Proof.Ed25519.AArch64.TableKeep base o 128 s t := by
  refine WP.mono (VG.Proof.Ed25519.AArch64.toTablePrefix_ok hs hp hlo ho 4 (by decide)) fun t ⟨hv, hk⟩ => ?_
  refine ⟨?_, hk⟩
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  simp only [VG.Proof.Ed25519.AArch64.tablePoint, VG.Proof.Ed25519.AArch64.point, h0, h1, h2, h3]
  rfl

end VG.Proof.Ed25519.AArch64
end

/-! Merged from `Proof.Ed25519.AArch64.PointTableLoad`. -/
section
/-! Copying point tables back into the arithmetic workspace. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
theorem fromTableQuarter_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (hp : s.gpr .x8 = off base o) (j : Nat) (hj : j < 4) (ho : o + 128 ≤ 8192) :
    WP isa (.block (fromTableWords (32 * j) ++ stores (64 + 32 * j) .x4 .x5 .x6 .x7)) s fun t =>
      env t.mem base ⟨j, by omega⟩ = F s.mem base (o + 32 * j) ∧
      VG.Proof.Ed25519.AArch64.TableKeep base (64 + 32 * j) 32 s t := by
  have _hcap : workSize true = 8192 := rfl
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.fromTableWords_ok hs hp (32 * j) (by omega) (by omega)) fun t ⟨hv, hk⟩ => ?_
  have ht := hs.of_keeps hk (by decide)
  refine WP.mono (stores_ok ht (by constructor <;> omega) .x4 .x5 .x6 .x7) fun u hu => ?_
  subst u
  refine ⟨?_, ⟨hk.gpr, hk.rd, hk.wr, hk.sp, ?_⟩⟩
  · change F (st4 _ _ _ _ _ _ _) base (64 + 32 * j) = _
    rw [F, fe_st4 _ _ (by omega), hv]
  · rw [hk.mem]; exact st4_outside _ _ (by omega) _ _ _ _

theorem fromTablePrefix_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (hp : s.gpr .x8 = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192)
    (n : Nat) (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap fun j =>
      fromTableWords (32 * j) ++ stores (64 + 32 * j) .x4 .x5 .x6 .x7)) s fun t =>
      (∀ j (hj : j < n), env t.mem base ⟨j, by omega⟩ = F s.mem base (o + 32 * j)) ∧
      VG.Proof.Ed25519.AArch64.TableKeep base 64 (32 * n) s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨fun j hj => by omega,
      ⟨fun _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs hp (by omega)) fun t ⟨hv, hk⟩ => ?_
    refine WP.mono (VG.Proof.Ed25519.AArch64.fromTableQuarter_ok (hk.scratch hs)
      ((hk.gpr _ (by decide)).trans hp) n (by omega) ho) fun u ⟨hu, ku⟩ => ?_
    refine ⟨fun j hj => ?_, (hk.mono (by omega) (by omega)).trans
      (ku.mono (by omega) (by omega))⟩
    by_cases h : j < n
    · have he : env u.mem base ⟨j, by omega⟩ = env t.mem base ⟨j, by omega⟩ :=
        Outside_F ku.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega))
      rw [he, hv j h]
    · have he : j = n := by omega
      subst j
      rw [hu, Outside_F hk.mem (by omega) (Or.inr (by omega))]

theorem pointFromTable_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (hp : s.gpr .x8 = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block pointFromTable) s fun t =>
      VG.Proof.Ed25519.AArch64.point (env t.mem base) 0 1 2 3 = VG.Proof.Ed25519.AArch64.tablePoint s.mem base o ∧ VG.Proof.Ed25519.AArch64.TableKeep base 64 128 s t := by
  refine WP.mono (VG.Proof.Ed25519.AArch64.fromTablePrefix_ok hs hp hlo ho 4 (by decide)) fun t ⟨hv, hk⟩ => ?_
  refine ⟨?_, hk⟩
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  change env t.mem base 0 = _ at h0
  change env t.mem base 1 = _ at h1
  change env t.mem base 2 = _ at h2
  change env t.mem base 3 = _ at h3
  simp only [VG.Proof.Ed25519.AArch64.tablePoint, VG.Proof.Ed25519.AArch64.point, h0, h1, h2, h3]

end VG.Proof.Ed25519.AArch64
end

/-! Public point-table addresses are a base plus a bounded entry offset. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem tableAddr_ok {s : State} {base : Addr} (hp : s.gpr .x0 = base)
    (o j : Nat) (hj : j < 64) (hc : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block (tableAddr o)) s fun t =>
      t.gpr .x8 = off base (o + 128 * j) ∧ Keeps [.x8, .x3] s t := by
  have hshift : (BitVec.ofNat 64 j) <<< 7 = BitVec.ofNat 64 (128 * j) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    rw [show 2 ^ 7 = 128 from rfl, Nat.mul_comm]
    rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 128 * j < 2 ^ 64)]
  apply WP.of_runBlock
  simp only [tableAddr, const64, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (7 : Nat) < Size.x.bits from by decide,
    show 16 * 0 < Size.x.bits from by decide, show 16 * 1 < Size.x.bits from by decide,
    show 16 * 2 < Size.x.bits from by decide, show 16 * 3 < Size.x.bits from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, hc, hp, hshift,
    ite_true, ite_false, reduceCtorEq, movz_movk64', Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [BitVec.add_comm (BitVec.ofNat 64 (128 * j)), BitVec.add_assoc, ← BitVec.ofNat_add,
      Nat.add_comm (128 * j)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers`. -/
section

/-! Constructing bounded tables of exact point doublings. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

/-- Only the field workspace and the specified table can change. -/
def TableFrame (base : Addr) (o n : Nat) (m m' : Mem) : Prop :=
  ∀ p, (ofs base p < 64 ∨ 768 ≤ ofs base p) →
    (ofs base p < o ∨ o + n ≤ ofs base p) → m' p = m p

theorem TableFrame.refl (base : Addr) (o n : Nat) (m : Mem) : VG.Proof.Ed25519.AArch64.TableFrame base o n m m :=
  fun _ _ _ => rfl

theorem TableFrame.trans {base : Addr} {o n : Nat} {m m' m'' : Mem}
    (h : VG.Proof.Ed25519.AArch64.TableFrame base o n m m') (k : VG.Proof.Ed25519.AArch64.TableFrame base o n m' m'') : VG.Proof.Ed25519.AArch64.TableFrame base o n m m'' :=
  fun p hp hq => (k p hp hq).trans (h p hp hq)

theorem TableFrame.mono {base : Addr} {o n o' n' : Nat} {m m' : Mem}
    (h : VG.Proof.Ed25519.AArch64.TableFrame base o n m m') (ho : o' ≤ o) (hn : o + n ≤ o' + n') :
    VG.Proof.Ed25519.AArch64.TableFrame base o' n' m m' := fun p hp hq => h p hp (by omega)

theorem TableFrame.workspace {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base 64 704 m m') : VG.Proof.Ed25519.AArch64.TableFrame base o n m m' := fun p hp _ => h p hp

theorem TableFrame.table {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') : VG.Proof.Ed25519.AArch64.TableFrame base o n m m' := fun p _ hp => h p hp

theorem TableFrame.word {base : Addr} {o n : Nat} {m m' : Mem}
    (h : VG.Proof.Ed25519.AArch64.TableFrame base o n m m') {d : Nat} (hd : 768 ≤ d)
    (hsep : d + 8 ≤ o ∨ o + n ≤ d) (hb : d + 8 < 2 ^ 64) :
    VG.Proof.Ed25519.AArch64.word m' base d = VG.Proof.Ed25519.AArch64.word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off base (by omega)]; omega)
    (by rw [ofs_off base (by omega)]; omega)).symm).symm

theorem TableFrame.field {base : Addr} {o n : Nat} {m m' : Mem}
    (h : VG.Proof.Ed25519.AArch64.TableFrame base o n m m') {d : Nat} (hd : 768 ≤ d)
    (hsep : d + 32 ≤ o ∨ o + n ≤ d) (hb : d + 32 < 2 ^ 64) :
    F m' base d = F m base d := by
  simp only [F, fe]
  rw [h.word (by omega) (by omega) (by omega), h.word (by omega) (by omega) (by omega),
    h.word (by omega) (by omega) (by omega), h.word (by omega) (by omega) (by omega)]

theorem TableFrame.point {base : Addr} {o n : Nat} {m m' : Mem}
    (h : VG.Proof.Ed25519.AArch64.TableFrame base o n m m') {d : Nat} (hd : 768 ≤ d)
    (hsep : d + 128 ≤ o ∨ o + n ≤ d) (hb : d + 128 < 2 ^ 64) :
    VG.Proof.Ed25519.AArch64.tablePoint m' base d = VG.Proof.Ed25519.AArch64.tablePoint m base d := by
  simp only [VG.Proof.Ed25519.AArch64.tablePoint]
  rw [h.field (by omega) (by omega) (by omega), h.field (by omega) (by omega) (by omega),
    h.field (by omega) (by omega) (by omega), h.field (by omega) (by omega) (by omega)]

theorem workspace_tablePoint {base : Addr} {m m' : Mem}
    (h : Outside base 64 704 m m') {d : Nat} (hd : 768 ≤ d) (hb : d + 128 < 2 ^ 64) :
    VG.Proof.Ed25519.AArch64.tablePoint m' base d = VG.Proof.Ed25519.AArch64.tablePoint m base d := by
  simp only [VG.Proof.Ed25519.AArch64.tablePoint]
  rw [Outside_F h (by omega) (Or.inr (by omega)), Outside_F h (by omega) (Or.inr (by omega)),
    Outside_F h (by omega) (Or.inr (by omega)), Outside_F h (by omega) (Or.inr (by omega))]

structure PowersKeep (base : Addr) (o n : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ≠ .x19 → r ≠ .x1 → r ∉ clob → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : VG.Proof.Ed25519.AArch64.TableFrame base o n s.mem t.mem

theorem PowersKeep.refl (base : Addr) (o n : Nat) (s : State) : VG.Proof.Ed25519.AArch64.PowersKeep base o n s s :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, TableFrame.refl _ _ _ _⟩

theorem PowersKeep.scratch {s t : State} {base : Addr} {o n : Nat}
    (h : VG.Proof.Ed25519.AArch64.PowersKeep base o n s t) (hs : Scr s base) : Scr t base :=
  ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem PowersKeep.trans {s t u : State} {base : Addr} {o n : Nat}
    (h : VG.Proof.Ed25519.AArch64.PowersKeep base o n s t) (k : VG.Proof.Ed25519.AArch64.PowersKeep base o n t u) : VG.Proof.Ed25519.AArch64.PowersKeep base o n s u :=
  ⟨fun r hb hs hc => (k.gpr r hb hs hc).trans (h.gpr r hb hs hc), k.rd.trans h.rd,
    k.wr.trans h.wr, k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem PowersKeep.mono {s t : State} {base : Addr} {o n o' n' : Nat}
    (h : VG.Proof.Ed25519.AArch64.PowersKeep base o n s t) (ho : o' ≤ o) (hn : o + n ≤ o' + n') :
    VG.Proof.Ed25519.AArch64.PowersKeep base o' n' s t := ⟨h.gpr, h.rd, h.wr, h.sp, h.mem.mono ho hn⟩

theorem powersNext_ok (s : State) (j count : Nat) (hj : j < count) (hn : count ≤ 64)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block (powersNext count)) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (j + 1) ∧ (t.gpr .x8 != 0) = decide (j + 1 ≠ count) ∧
      Keeps [.x8, .x19] s t := by
  have ha : BitVec.ofNat 64 j + BitVec.ofNat 64 1 = BitVec.ofNat 64 (j + 1) := by rw [BitVec.ofNat_add]
  have hz : (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 count != 0) = decide (j + 1 ≠ count) := by
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne, decide_eq_true_eq]
    bv_omega_using [hj, hn]
  apply WP.of_runBlock
  simp only [powersNext, powersLeft, const64, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (1 : Nat) < 4096 from by decide,
    show 16 * 0 < Size.x.bits from by decide, show 16 * 1 < Size.x.bits from by decide,
    show 16 * 2 < Size.x.bits from by decide, show 16 * 3 < Size.x.bits from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, Size.bits, hc, ha,
    ite_true, ite_false, reduceCtorEq, movz_movk64', hz, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem powersLeft_ok (s : State) (n count : Nat) (hn : n ≤ count) (hc64 : count ≤ 64)
    (hc : s.gpr .x19 = BitVec.ofNat 64 n) :
    WP isa (.block (powersLeft count)) s fun t =>
      (t.gpr .x8 != 0) = decide (n ≠ count) ∧ Keeps [.x8] s t := by
  have hz : (BitVec.ofNat 64 n - BitVec.ofNat 64 count != 0) = decide (n ≠ count) := by
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne, decide_eq_true_eq]
    bv_omega_using [hn, hc64]
  apply WP.of_runBlock
  simp only [powersLeft, const64, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 16 * 0 < Size.x.bits from by decide, show 16 * 1 < Size.x.bits from by decide,
    show 16 * 2 < Size.x.bits from by decide, show 16 * 3 < Size.x.bits from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, Size.bits, hc,
    ite_true, ite_false, reduceCtorEq, movz_movk64', hz, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.BitByte`. -/
section

/-! Byte stores and expansion of one scalar byte into eight bits. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem sub_toNat_lt_one (x a : Addr) : (x - a).toNat < 1 ↔ x = a := by
  constructor
  · intro h
    have h0 : x - a = 0 := BitVec.eq_of_toNat_eq (by rw [show (0 : Addr).toNat = 0 from rfl]; omega)
    calc x = x - a + a := (BitVec.sub_add_cancel x a).symm
      _ = a := by rw [h0]; exact BitVec.zero_add a
  · rintro rfl; simp

theorem writeW8_apply (m : Mem) (a x : Addr) (v : BitVec 8) :
    (m.writeW a v) x = if x = a then v else m x := by
  by_cases h : x = a
  · subst h; simp [Mem.writeW, Mem.write]
  · simp only [Mem.writeW, Mem.write, Nat.reduceDiv, VG.Proof.Ed25519.AArch64.sub_toNat_lt_one, h, ite_false]

theorem off_eq_iff (base : Addr) {d e : Nat} (hd : d < 2 ^ 64) (he : e < 2 ^ 64) :
    off base d = off base e ↔ d = e := by
  constructor
  · intro h
    have := congrArg (fun x => ofs base x) h
    simp only [ofs_off' base hd, ofs_off' base he] at this
    exact this
  · intro h; rw [h]

theorem writeW8_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 8) (hd : d < 2 ^ 64) {x : Addr}
    (hx : ofs base x ≠ d) : (m.writeW (off base d) v) x = m x := by
  rw [VG.Proof.Ed25519.AArch64.writeW8_apply, ite_eq_right_iff.mpr]
  intro h; subst h; exact absurd (ofs_off' base hd) hx

theorem bit_byte : ∀ b : BitVec 8, ∀ j < 8,
    ((((b.setWidth 64 >>> j) &&& BitVec.ofNat 64 1).setWidth 32).setWidth 8 : BitVec 8) =
      BitVec.ofNat 8 ((b.toNat >>> j) &&& 1) := by decide

theorem expandScalarBit_ok {s : State} {base : Addr} (hs : Scr s base)
    (i j : Nat) (hi : i < 64) (hj : j < 8)
    (hp : s.gpr .x9 = off base (8 * i)) (hone : s.gpr .x11 = BitVec.ofNat 64 1)
    (b : BitVec 8) (hb : s.gpr .x8 = b.setWidth 64) :
    WP isa (.block (expandScalarBit j)) s fun t =>
      (∀ r, r ≠ .x2 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.mem = s.mem.writeW (off base (768 + (8 * i + j))) (BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) := by
  have _hcap : workSize true = 8192 := rfl
  have hw : InRegions s.wr (off base (768 + (8 * i + j))) 1 :=
    ⟨_, hs.wr, Offset.contains_base _ (by omega) (by omega)⟩
  have he : off base (8 * i) + BitVec.ofNat 64 (768 + j) = off base (768 + (8 * i + j)) := by
    rw [Offset.add_add]; exact congrArg (off base) (by omega)
  apply WP.of_runBlock
  simp only [expandScalarBit, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    show j < Size.x.bits from by change j < 64; omega,
    addr, State.store, RegUpd.gpr_write, RegUpd.wr_write, RegUpd.mem_write,
    BitVec.setWidth_eq, hp, hone, hb, he, hw, Nat.mod_one,
    show 768 + j < 4096 * 1 from by omega, and_self,
    ite_true, ite_false, reduceCtorEq, VG.Proof.Ed25519.AArch64.bit_byte b j hj,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => ?_, rfl, True.intro, rfl, ?_⟩
  · simp only [hr, ite_false]
  · rfl

structure BitKeep (base : Addr) (i n : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ≠ .x2 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base (768 + 8 * i) n s.mem t.mem

theorem BitKeep.scratch {base : Addr} {i n : Nat} {s t : State}
    (h : VG.Proof.Ed25519.AArch64.BitKeep base i n s t) (hs : Scr s base) : Scr t base :=
  ⟨(h.gpr _ (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem scalarBitPrefix_ok {s : State} {base : Addr} (hs : Scr s base)
    (i n : Nat) (hi : i < 64) (hn : n ≤ 8) (hp : s.gpr .x9 = off base (8 * i)) (hone : s.gpr .x11 = BitVec.ofNat 64 1)
    (b : BitVec 8) (hb : s.gpr .x8 = b.setWidth 64) :
    WP isa (.block ((List.range n).flatMap expandScalarBit)) s fun t => VG.Proof.Ed25519.AArch64.BitKeep base i n s t ∧
      ∀ j < n, t.mem (off base (768 + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1) := by
  induction n generalizing s with
  | zero => exact WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩, fun _ h => by omega⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs (by omega) hp hone hb) fun t ⟨hk, hv⟩ => ?_
    refine WP.mono (VG.Proof.Ed25519.AArch64.expandScalarBit_ok (hk.scratch hs) i n hi (by omega)
      ((hk.gpr _ (by decide)).trans hp) ((hk.gpr _ (by decide)).trans hone) b ((hk.gpr _ (by decide)).trans hb))
      fun u ⟨ug, ur, uw, usp, um⟩ => ?_
    refine ⟨⟨fun r hr => (ug r hr).trans (hk.gpr r hr), ur.trans hk.rd, uw.trans hk.wr, usp.trans hk.sp, ?_⟩, ?_⟩
    · intro p hp
      rw [um, VG.Proof.Ed25519.AArch64.writeW8_outside _ _ _ (by omega) (by omega), hk.mem p (by omega)]
    · intro j hj
      rw [um, VG.Proof.Ed25519.AArch64.writeW8_apply]
      by_cases h : j = n
      · subst j; rw [ite_eq_left rfl]
      · rw [ite_eq_right (fun he => h (by
          have hh := (VG.Proof.Ed25519.AArch64.off_eq_iff base (by omega) (by omega)).mp he
          omega))]
        exact hv j (by omega)

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.Bits`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.BitRead`. -/
section
/-! Load the next scalar byte and calculate its bit-output address. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64

theorem scalarByteRead_ok {s : State} {base k : Addr} (hs : Scr s base)
    (i : Nat) (hi : i < 64) (hc : s.gpr .x19 = BitVec.ofNat 64 i) (hp : s.gpr .x1 = k)
    (hr : InRegions (s.rd ++ s.wr) (off k i) 1) :
    WP isa (.block [.add .x .x8 .x1 .x19, .ldrb .x8 .x8 0,
      .lsl .x .x9 .x19 3, .add .x .x9 .x0 .x9]) s fun t =>
      t.gpr .x8 = (s.mem (off k i)).setWidth 64 ∧ t.gpr .x9 = off base (8 * i) ∧
      Keeps [.x8, .x9] s t := by
  have hshift : (BitVec.ofNat 64 i) <<< 3 = BitVec.ofNat 64 (8 * i) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    rw [show 2 ^ 3 = 8 from rfl, Nat.mul_comm]
    rw [Nat.mod_eq_of_lt (by omega : i < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 8 * i < 2 ^ 64)]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, addr, State.load,
    show (0 : Nat) < 4096 * 1 from by decide, show (0 : Nat) % 1 = 0 from rfl,
    show (3 : Nat) < Size.x.bits from by decide, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hp, hc, hs.x0, hshift, BitVec.add_zero, BitVec.setWidth_eq, hr, read_byte,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨BitVec.setWidth_setWidth (by decide), True.intro, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  intro r h
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp only [RegUpd.gpr_write, h.1, h.2, ite_false]

end VG.Proof.Ed25519.AArch64
end

/-! Expand all scalar bits, without X25519's clamping. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

structure BitsKeep (base : Addr) (o n : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.x8, .x9, .x2, .x19, .x11] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base o n s.mem t.mem

theorem BitsKeep.scratch {base : Addr} {o n : Nat} {s t : State}
    (h : VG.Proof.Ed25519.AArch64.BitsKeep base o n s t) (hs : Scr s base) : Scr t base :=
  ⟨(h.gpr _ (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem BitsKeep.trans {base : Addr} {o n : Nat} {s t u : State}
    (h : VG.Proof.Ed25519.AArch64.BitsKeep base o n s t) (k : VG.Proof.Ed25519.AArch64.BitsKeep base o n t u) : VG.Proof.Ed25519.AArch64.BitsKeep base o n s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem BitsKeep.mono {base : Addr} {o n o' n' : Nat} {s t : State}
    (h : VG.Proof.Ed25519.AArch64.BitsKeep base o n s t) (ho : o' ≤ o) (hn : o + n ≤ o' + n') : VG.Proof.Ed25519.AArch64.BitsKeep base o' n' s t :=
  ⟨h.gpr, h.rd, h.wr, h.sp, h.mem.mono ho hn⟩

theorem scalarByteBits_ok {s : State} {base k : Addr} (hs : Scr s base)
    (i count : Nat) (hi : i < count) (hn : count ≤ 64)
    (hc : s.gpr .x19 = BitVec.ofNat 64 i) (hp : s.gpr .x1 = k)
    (hr : InRegions (s.rd ++ s.wr) (off k i) 1) (hone : s.gpr .x11 = BitVec.ofNat 64 1) :
    WP isa (.block (scalarByteBits count)) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (i + 1) ∧ (t.gpr .x8 != 0) = decide (i + 1 ≠ count) ∧ t.gpr .x11 = BitVec.ofNat 64 1 ∧
      VG.Proof.Ed25519.AArch64.BitsKeep base (768 + 8 * i) 8 s t ∧
      ∀ j < 8, t.mem (off base (768 + (8 * i + j))) =
        BitVec.ofNat 8 (((s.mem (off k i)).toNat >>> j) &&& 1) := by
  rw [scalarByteBits, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.scalarByteRead_ok hs i (by omega) hc hp hr) fun a ⟨av, ap, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.scalarBitPrefix_ok (hs.of_keeps ka (by decide)) i 8 (by omega) (by decide)
    ap ((ka.gpr _ (by decide)).trans hone) _ av) fun b ⟨kb, bv⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.AArch64.powersNext_ok b i count hi hn
    ((kb.gpr _ (by decide)).trans ((ka.gpr _ (by decide)).trans hc))) fun t ⟨tc, tz, kt⟩ => ?_
  refine ⟨tc, tz, ?_, ⟨fun r hr => ?_, kt.rd.trans (kb.rd.trans ka.rd),
    kt.wr.trans (kb.wr.trans ka.wr), kt.sp.trans (kb.sp.trans ka.sp), ?_⟩, ?_⟩
  · rw [kt.gpr _ (by decide), kb.gpr _ (by decide), ka.gpr _ (by decide), hone]
  · have h8 : r ≠ .x8 := fun he => hr (by simp [he])
    have h9 : r ≠ .x9 := fun he => hr (by simp [he])
    have h2 : r ≠ .x2 := fun he => hr (by simp [he])
    have h19 : r ≠ .x19 := fun he => hr (by simp [he])
    exact (kt.gpr r (by simp [h8, h19])).trans
      ((kb.gpr r h2).trans (ka.gpr r (by simp [h8, h9])))
  · rw [kt.mem, ← ka.mem]; exact kb.mem
  · rw [kt.mem]; exact bv

structure BitsInv (s₀ : State) (base k : Addr) (count i : Nat) (s : State) : Prop where
  scratch : Scr s base
  ptr : s.gpr .x1 = k
  counter : s.gpr .x19 = BitVec.ofNat 64 i
  one : s.gpr .x11 = BitVec.ofNat 64 1
  keep : VG.Proof.Ed25519.AArch64.BitsKeep base 768 (8 * count) s₀ s
  bits : ∀ t < 8 * i, s.mem (off base (768 + t)) =
    BitVec.ofNat 8 (((s₀.mem (off k (t / 8))).toNat >>> (t % 8)) &&& 1)

theorem scalarBitsLoop_ok {s₀ : State} {base k : Addr} (count : Nat) (hn : count ≤ 64)
    (hr : ∀ q < count, InRegions (s₀.rd ++ s₀.wr) (off k q) 1)
    (hd : ∀ q < count, 8192 ≤ ofs base (off k q)) :
    ∀ i s, i < count → VG.Proof.Ed25519.AArch64.BitsInv s₀ base k count i s →
      WP isa (.loop (.block (scalarByteBits count)) (.nonzero .x .x8)) s fun t => VG.Proof.Ed25519.AArch64.BitsInv s₀ base k count count t := by
  intro i s hi h
  refine WP.loop (M := isa) (body := .block (scalarByteBits count)) (c := .nonzero .x .x8)
    (Q := fun t => VG.Proof.Ed25519.AArch64.BitsInv s₀ base k count count t)
    (fun n s => ∃ i, n = count - i ∧ i < count ∧ VG.Proof.Ed25519.AArch64.BitsInv s₀ base k count i s) ?_
    (count - i) s ⟨i, rfl, hi, h⟩
  rintro n s ⟨i, rfl, hi, h⟩
  refine WP.mono (VG.Proof.Ed25519.AArch64.scalarByteBits_ok h.scratch i count hi hn h.counter h.ptr
    (by rw [h.keep.rd, h.keep.wr]; exact hr i hi) h.one) fun t ⟨tc, tz, tone, tk, tb⟩ => ?_
  have hbyte : s.mem (off k i) = s₀.mem (off k i) := h.keep.mem _ (by have := hd i hi; omega)
  have inv : VG.Proof.Ed25519.AArch64.BitsInv s₀ base k count (i + 1) t := by
    refine ⟨tk.scratch h.scratch, (tk.gpr _ (by decide)).trans h.ptr, tc, tone,
      h.keep.trans (tk.mono (by omega) (by omega)), fun j hj => ?_⟩
    by_cases hp : j < 8 * i
    · rw [tk.mem _ (by rw [ofs_off' base (by omega)]; omega), h.bits j hp]
    · have e := tb (j - 8 * i) (by omega)
      rw [show 8 * i + (j - 8 * i) = j by omega, hbyte] at e
      rw [e, show j / 8 = i by omega, show j % 8 = j - 8 * i by omega]
  by_cases he : i + 1 = count
  · exact Or.inl ⟨by simp only [eval, read_x, tz, he, show decide (count ≠ count) = false from decide_eq_false (not_not_intro rfl)], he ▸ inv⟩
  · exact Or.inr ⟨by simp only [eval, read_x, tz, decide_eq_true he],
      count - (i + 1), by omega, i + 1, rfl, by omega, inv⟩

theorem input_byte (m : Mem) (k : Addr) (count j : Nat) (hj : j < count) :
    (Spec.Ed25519.bytesAt m k count).getD j 0 = m (off k j) := by
  simp only [Spec.Ed25519.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hj, Option.map_some, Option.getD_some]

theorem scalarBitsInit_ok (s : State) :
    WP isa (.block [.movz .w .x19 0 0, .movz .w .x11 1 0]) s fun t =>
      t.gpr .x19 = 0 ∧ t.gpr .x11 = BitVec.ofNat 64 1 ∧ Keeps [.x19, .x11] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, RegUpd.gpr_write,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem expandScalarBits_ok {s : State} {base k : Addr} (hs : Scr s base) (hp : s.gpr .x1 = k)
    (count : Nat) (hn0 : 0 < count) (hn : count ≤ 64)
    (hr : ∀ q < count, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < count, 8192 ≤ ofs base (off k q)) :
    WP isa (scalarBits count) s fun t => VG.Proof.Ed25519.AArch64.BitsKeep base 768 (8 * count) s t ∧
      ∀ j < 8 * count, t.mem (off base (768 + j)) =
        BitVec.ofNat 8 ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k count) / 2 ^ j) % 2) := by
  rw [scalarBits]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.scalarBitsInit_ok s) fun a ⟨ac, aone, ka⟩ => ?_)
  have init : VG.Proof.Ed25519.AArch64.BitsInv s base k count 0 a := by
    refine ⟨hs.of_keeps ka (by decide), (ka.gpr _ (by decide)).trans hp, ac, aone,
      ⟨fun r hr => ka.gpr r (fun hm => hr ((by decide : [Reg.x19, .x11] ⊆ [Reg.x8, .x9, .x2, .x19, .x11]) hm)), ka.rd, ka.wr, ka.sp, ?_⟩, fun j hj => by omega⟩
    rw [ka.mem]; exact Outside.refl _ _ _ _
  refine WP.mono (VG.Proof.Ed25519.AArch64.scalarBitsLoop_ok count hn hr hd 0 a hn0 init) fun t h => ?_
  refine ⟨h.keep, fun j hj => ?_⟩
  rw [h.bits j hj]
  have hb := Proof.X25519.leNum_bit (Spec.Ed25519.bytesAt s.mem k count) j
  rw [← decodeLE_eq, VG.Proof.Ed25519.AArch64.input_byte _ _ _ _ (by omega)] at hb
  simp only [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] at hb ⊢
  exact congrArg (BitVec.ofNat 8) hb.symm

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.Swap`. -/
section

/-! Swapping four limbs with a mask and writing the two field elements. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64

theorem swapWords_ok (s : State) (sw : Bool) (hm : s.gpr .x3 = mask sw) :
    WP isa (.block swapWords) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) =
        (if sw then val4 (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) (s.gpr .x24)
          else val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)) ∧
      val4 (t.gpr .x21) (t.gpr .x22) (t.gpr .x23) (t.gpr .x24) =
        (if sw then val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
          else val4 (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) (s.gpr .x24)) ∧
      Keeps [.x4, .x5, .x6, .x7, .x8, .x21, .x22, .x23, .x24] s t := by
  apply WP.of_runBlock
  simp only [swapWords, swapWord, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left', hm, (xor_sel sw _ _).1, (xor_sel sw _ _).2]
  refine ⟨?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · cases sw <;> rfl
  · cases sw <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

theorem cswap_ok {s : State} {base : Addr} (hs : Scr s base large) {x y : Nat}
    (hx : FieldRange x large) (hy : FieldRange y large) (hxy : x + 32 ≤ y ∨ y + 32 ≤ x)
    {sw : Bool} (hm : s.gpr .x3 = mask sw) :
    WP isa (.block (cswap x y)) s fun t =>
      (∀ r, r ∉ clob → t.gpr r = s.gpr r) ∧ t.gpr .x3 = s.gpr .x3 ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      (∃ m, Outside base x 32 s.mem m ∧ Outside base y 32 m t.mem ∧
        fe m base x = if sw then fe s.mem base y else fe s.mem base x) ∧
      fe t.mem base x = (if sw then fe s.mem base y else fe s.mem base x) ∧
      fe t.mem base y = (if sw then fe s.mem base x else fe s.mem base y) := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  rw [cswap, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loads_ok hs hx (by decide)) fun s₁ ⟨a0, a1, a2, a3, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok (hs.of_keeps k1 (by decide)) hy (by decide)) fun s₂ ⟨b0, b1, b2, b3, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.swapWords_ok s₂ sw (by rw [k2.gpr _ (by decide), k1.gpr _ (by decide), hm]))
    fun s₃ ⟨v3, w3, k3⟩ => ?_
  have va : val4 (s₂.gpr .x4) (s₂.gpr .x5) (s₂.gpr .x6) (s₂.gpr .x7) = fe s.mem base x := by
    rw [k2.gpr _ (by decide), k2.gpr _ (by decide), k2.gpr _ (by decide), k2.gpr _ (by decide),
      a0, a1, a2, a3]
  have vb : val4 (s₂.gpr .x21) (s₂.gpr .x22) (s₂.gpr .x23) (s₂.gpr .x24) = fe s.mem base y := by
    rw [b0, b1, b2, b3, k1.mem]
  rw [va, vb] at v3 w3
  have hs₃ := (hs.of_keeps k1 (by decide)).of_keeps k2 (by decide) |>.of_keeps k3 (by decide)
  have K : Keeps clob s s₃ := ((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide))
  have hc : s₃.gpr .x3 = s.gpr .x3 := by
    rw [k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide)]
  rw [WP.block_append_iff]
  refine WP.mono (store4_ok hs₃ hx) fun s₄ h4 => ?_
  subst s₄
  refine WP.mono (stores_ok (hs₃.setMem _) hy .x21 .x22 .x23 .x24) fun t ht => ?_
  subst t
  have o1 := st4_outside s₃.mem base (show x + 32 < 2 ^ 64 by have := hx.2; omega)
    (s₃.gpr .x4) (s₃.gpr .x5) (s₃.gpr .x6) (s₃.gpr .x7)
  have o2 := st4_outside (st4 s₃.mem base x (s₃.gpr .x4) (s₃.gpr .x5) (s₃.gpr .x6) (s₃.gpr .x7))
    base (show y + 32 < 2 ^ 64 by have := hy.2; omega)
    (s₃.gpr .x21) (s₃.gpr .x22) (s₃.gpr .x23) (s₃.gpr .x24)
  have vx : fe (st4 s₃.mem base x (s₃.gpr .x4) (s₃.gpr .x5) (s₃.gpr .x6) (s₃.gpr .x7)) base x =
      if sw then fe s.mem base y else fe s.mem base x := by
    rw [fe_st4 _ _ (by have := hx.2; omega)]; exact v3
  refine ⟨K.gpr, hc, K.rd, K.wr, K.sp, ⟨_, ?_, o2, vx⟩, ?_, ?_⟩
  · rw [← K.mem]; exact o1
  · rw [o2.fe hxy (by have := hx.2; omega)]; exact vx
  · rw [fe_st4 _ _ (by have := hy.2; omega)]; exact w3

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.PointSelect`. -/
section

/-! Point selection reuses the verified constant-time field swaps. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64

def swapEnv (a b : Slot) (sw : Bool) (e : Env) : Env :=
  Function.update (Function.update e a (if sw then e b else e a)) b (if sw then e a else e b)

def swapEnvs (ops : List (Slot × Slot)) (sw : Bool) (e : Env) : Env :=
  ops.foldl (fun e (a, b) => VG.Proof.Ed25519.AArch64.swapEnv a b sw e) e

theorem swapField_ok {s : State} {base : Addr} (hs : Scr s base) (a b : Slot)
    (hab : a ≠ b) {sw : Bool} (hm : s.gpr .x3 = mask sw) :
    WP isa (.block (cswap (offset a) (offset b))) s fun t =>
      Keep base s t ∧ t.gpr .x3 = s.gpr .x3 ∧ env t.mem base = VG.Proof.Ed25519.AArch64.swapEnv a b sw (env s.mem base) := by
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  refine WP.mono (VG.Proof.Ed25519.AArch64.cswap_ok hs (slot_range a) (slot_range b)
    (by simp only [offset]; omega) hm) fun t ⟨hg, hc, hr, hw, hsp, ⟨m, h₁, h₂, f₁⟩, _, f₂⟩ => ?_
  refine ⟨⟨hg, hr, hw, hsp, (h₁.mono (by simp only [offset]; omega) (by simp only [offset]; omega)).trans
    (h₂.mono (by simp only [offset]; omega) (by simp only [offset]; omega))⟩, hc, ?_⟩
  rw [env_update b h₂, env_update a h₁]
  simp only [F, f₁, f₂]
  cases sw <;> rfl

theorem swapFields_ok {s : State} {base : Addr} (hs : Scr s base) (ops : List (Slot × Slot))
    (hops : ∀ ab ∈ ops, ab.1 ≠ ab.2) {sw : Bool} (hm : s.gpr .x3 = mask sw) :
    WP isa (.block (swapFields ops)) s fun t =>
      Keep base s t ∧ t.gpr .x3 = s.gpr .x3 ∧ env t.mem base = VG.Proof.Ed25519.AArch64.swapEnvs ops sw (env s.mem base) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, rfl, rfl⟩
  | cons ab ops ih =>
    rw [swapFields, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed25519.AArch64.swapField_ok hs ab.1 ab.2 (hops ab (by simp)) hm) fun t ⟨hk, hc, hv⟩ => ?_
    refine WP.mono (ih (hk.scr hs) (fun p hp => hops p (List.mem_cons_of_mem _ hp)) (hc.trans hm))
      fun u ⟨ku, cu, vu⟩ => ?_
    refine ⟨hk.trans ku, cu.trans hc, ?_⟩
    rw [vu, hv]; rfl

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.PointAccumulate`. -/
section

/-! The scalar bit mask and the selection of the saved point. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64

theorem Keep.of_table {base : Addr} {s t : State}
    (h : VG.Proof.Ed25519.AArch64.TableKeep base 64 128 s t) : Keep base s t := by
  refine ⟨fun r hr => h.gpr r (fun hm => hr ?_), h.rd, h.wr, h.sp, h.mem.mono (by decide) (by decide)⟩
  exact (show ∀ r ∈ [Reg.x4, .x5, .x6, .x7], r ∈ clob by decide) r hm

theorem tableLoad_high {base : Addr} {s t : State} (hk : VG.Proof.Ed25519.AArch64.TableKeep base 64 128 s t)
    (i : Slot) (hi : 4 ≤ i.val) : env t.mem base i = env s.mem base i :=
  Outside_F hk.mem (by simp only [offset]; omega) (Or.inr (by simp only [offset]; omega))

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.PointMulCounter`. -/
section

/-! The public batch counter survives field and table operations. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem batchBegin_ok {s : State} {base : Addr} (hs : Scr s base)
    (j : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1)) :
    WP isa (.block batchBegin) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 j ∧ t.mem.readW (off base 56) 64 = BitVec.ofNat 64 j ∧
      (∀ r, r ≠ .x19 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Outside base 56 8 s.mem t.mem := by
  have hw : InRegions s.wr (off base 56) 8 :=
    ⟨_, hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  have hr : InRegions (s.rd ++ s.wr) (off base 56) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  have he : BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 j := by
    rw [BitVec.ofNat_add, BitVec.add_sub_cancel]
  change s.mem.read (off base 56) 8 = _ at hc
  apply WP.of_runBlock
  simp only [batchBegin, ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    addr, Size.bytes, Size.bits, State.load, State.store,
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write, BitVec.setWidth_eq,
    hs.x0, hr, hw, hc, he, Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, ?_, fun r hr => ?_, True.intro, True.intro, rfl, ?_⟩
  · rw [write64_eq_writeW]; exact Mem.readW_writeW_self64 _ _ _
  · simp only [hr, ite_false]
  · rw [write64_eq_writeW]; exact writeW_outside _ _ _ (by decide)

theorem batchTest_ok {s : State} {base : Addr} (hs : Scr s base)
    (j : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 j) :
    WP isa (.block batchTest) s fun t => t.gpr .x19 = BitVec.ofNat 64 j ∧ Keeps [.x19] s t :=
  WP.mono (ld_ok hs (by decide) (by decide) .x19) fun _ ⟨hv, hk⟩ => ⟨hv.trans hc, hk⟩

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.PointMulBatch`. -/
section

/-! Frames for the batches of the scalar multiplications. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem PowersKeep.of_keeps {base : Addr} {o n : Nat} {s t : State} {rs : List Reg}
    (h : Keeps rs s t) (hrs : ∀ r ∈ rs, r = .x19 ∨ r = .x1 ∨ r ∈ clob) : VG.Proof.Ed25519.AArch64.PowersKeep base o n s t := by
  refine ⟨fun r hb hs hr => h.gpr r (fun hm => ?_), h.rd, h.wr, h.sp, ?_⟩
  · rcases hrs r hm with h | h | h
    · exact hb h
    · exact hs h
    · exact hr h
  · rw [h.mem]; exact TableFrame.refl _ _ _ _

theorem PowersKeep.of_keep {base : Addr} {o n : Nat} {s t : State} (h : Keep base s t) :
    VG.Proof.Ed25519.AArch64.PowersKeep base o n s t := ⟨fun r _ _ hr => h.gpr r hr, h.rd, h.wr, h.sp, TableFrame.workspace h.mem⟩

theorem PowersKeep.of_counter {base : Addr} {o n : Nat} {s t : State} (h : CounterKeep base s t) :
    VG.Proof.Ed25519.AArch64.PowersKeep base o n s t := ⟨fun r hb _ hr => h.gpr r hr hb, h.rd, h.wr, h.sp, TableFrame.workspace h.mem⟩

theorem header_env {base : Addr} {m m' : Mem} (h : Outside base 56 8 m m') : env m' base = env m base := by
  funext i
  exact Outside_F h (by simp only [offset]; omega) (Or.inr (by simp only [offset]; omega))

end VG.Proof.Ed25519.AArch64

end
