import VerifiedGarbage.Proof.X448.Arm.Fn
import VerifiedGarbage.Proof.Framework.Arm.Call

/-!
# X448 on ARMv7: calls of the field functions

`mulFn_ok`, `addFn_ok`, `subFn_ok` and `mulA24Fn_ok` are what the field
functions do (`fn_ok` with their operations). A field operation of the
callers is a call (`Op.code`): the offsets are moved into `r1`–`r3` and
the function is called on the working space at `r0` (`callFn_ok`,
`mulA24Call_ok`); the call changes only the registers `clob` and the memory
`FieldMem` allows (`Op`), as the operations did when they were inlined.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16
open VG.Proof.X25519.Arm (Rest Upd wp_movw)

/-- What a function does, from its entry, for the relation `r` of the result
and the operands. -/
abbrev FnPost (s : State) (base : Addr) (o a b : Nat) (r : Nat → Nat → Nat → Prop) (t : State) : Prop :=
  (∀ q ∈ preserved, t.gpr q = s.gpr q) ∧ t.gpr .r0 = s.gpr .r0 ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    FieldMem base o s.mem t.mem ∧ Bounded t.mem base o ∧ r (fe t.mem base o) (fe s.mem base a) (fe s.mem base b)

abbrev mulRel (x y z : Nat) : Prop := x % Spec.X448.P = y * z % Spec.X448.P
abbrev addRel (x y z : Nat) : Prop := x % Spec.X448.P = (y + z) % Spec.X448.P
abbrev subRel (x y z : Nat) : Prop := (x + z) % Spec.X448.P = y % Spec.X448.P
abbrev a24Rel (x y _ : Nat) : Prop := x % Spec.X448.P = 39081 * y % Spec.X448.P

theorem mulFn_ok {s : State} {base : Addr} {o a b : Nat} (h : Entry true s base o a b)
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa mulFn s (FnPost s base o a b mulRel) :=
  fn_ok h ho ha hb ab bb fun _ hs po pa pb a₁ b₁ => mul_ok hs po pa (pb rfl) ho ha hb a₁ b₁

theorem addFn_ok {s : State} {base : Addr} {o a b : Nat} (h : Entry true s base o a b)
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa addFn s (FnPost s base o a b addRel) :=
  fn_ok h ho ha hb ab bb fun _ hs po pa pb a₁ b₁ => WP.mono (add_ok hs po pa (pb rfl) ho ha hb a₁ b₁)
    fun _ ⟨k, m, bo, v⟩ => ⟨k.mono fun _ h => List.mem_cons_of_mem _ h, m, bo, v⟩

theorem subFn_ok {s : State} {base : Addr} {o a b : Nat} (h : Entry true s base o a b)
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa subFn s (FnPost s base o a b subRel) :=
  fn_ok h ho ha hb ab bb fun _ hs po pa pb a₁ b₁ => WP.mono (sub_ok hs po pa (pb rfl) ho ha hb a₁ b₁)
    fun _ ⟨k, m, bo, v⟩ => ⟨k.mono fun _ h => List.mem_cons_of_mem _ h, m, bo, v⟩

theorem mulA24Fn_ok {s : State} {base : Addr} {o a : Nat} (h : Entry false s base o a a)
    (ho : Slot o) (ha : Slot a) (ab : Bounded s.mem base a) :
    WP isa mulA24Fn s (FnPost s base o a a a24Rel) :=
  fn_ok h ho ha ha ab ab fun _ hs po pa _ a₁ _ => WP.mono (mulSmall_ok hs po pa ho ha a₁)
    fun _ ⟨k, m, bo, v⟩ => ⟨k.mono fun _ h => List.mem_cons_of_mem _ h, m, bo, v⟩

/-- The working space a call narrows the regions to. -/
abbrev wsRegion (base : Addr) : Region := ⟨base, 8192⟩

theorem movw_toNat {x : Nat} (h : x < 65536) : ((BitVec.ofNat 16 x).setWidth 32).toNat = x := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

/-- A call of `body` after the arguments are set (`r1`–`r3` changed, `pre`
holding on the entry), as a field operation. -/
theorem call_ok {f : String} {body : Prog isa} (hn : body.noCalls = true) {s : State} {base : Addr}
    (hs : Scr s base) {o a b : Nat} {hasB : Bool} {r : Nat → Nat → Nat → Prop}
    (hbody : ∀ t, Entry hasB t base o a b → Bounded t.mem base a → Bounded t.mem base b →
      WP isa body t (FnPost t base o a b r))
    {s₃ : State} (k₃ : Rest [.r1, .r2, .r3] s s₃) (m₃ : s₃.mem = s.mem)
    (h1 : (s₃.gpr .r1).toNat = o) (h2 : (s₃.gpr .r2).toNat = a) (h3 : hasB = true → (s₃.gpr .r3).toNat = b)
    (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (.call f body) s₃ fun t => Op base o s t ∧ Bounded t.mem base o ∧
      r (fe t.mem base o) (fe s.mem base a) (fe s.mem base b) := by
  have hs₃ : Scr s₃ base := hs.of_keeps ⟨k₃.gpr, k₃.rd, k₃.wr⟩ (by decide)
  have g : ∀ q, q ∉ VG.Arm.linkRegs → (s₃.callEntry.withRegions [] [wsRegion base]).gpr q = s₃.gpr q :=
    fun q hq => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  refine WP.call (k := ⟨fun t => t.rd = [] ∧ t.wr = [wsRegion base] ∧ Entry hasB t base o a b ∧
      Bounded t.mem base a ∧ Bounded t.mem base b,
      fun t t' => t'.gpr .r0 = t.gpr .r0 ∧ FieldMem base o t.mem t'.mem ∧ Bounded t'.mem base o ∧
        r (fe t'.mem base o) (fe t.mem base a) (fe t.mem base b), fun _ _ => True⟩)
    (fun t ⟨_, _, he, ha', hb'⟩ => by
      obtain ⟨tr, t', hx, P, R0, _, _, M, B, V⟩ := hbody t he ha' hb'
      exact ⟨tr, t', hx, ⟨P, Exec.sp hx⟩, R0, M, B, V⟩)
    (rd := []) (wr := [wsRegion base])
    ⟨rfl, rfl, ⟨⟨by rw [g _ (by decide)]; exact hs₃.r0, List.mem_singleton_self _,
        by rw [g _ (by decide)]; exact hs₃.nowrap⟩,
      by rw [g _ (by decide)]; exact h1, by rw [g _ (by decide)]; exact h2,
      fun hb => by rw [g _ (by decide)]; exact h3 hb⟩,
      by rw [State.withRegions_mem, State.callEntry_mem, m₃]; exact ab,
      by rw [State.withRegions_mem, State.callEntry_mem, m₃]; exact bb⟩
    (Covers.right (Covers.of_mem fun _ hr => by rw [List.mem_singleton.mp hr]; exact hs₃.wr))
    (Covers.of_mem fun _ hr => by rw [List.mem_singleton.mp hr]; exact hs₃.wr)
    ?_ hn
  intro t rd wr _ _ P _ ⟨R0, M, B, V⟩
  simp only [State.withRegions_mem, State.callEntry_mem, m₃, State.withRegions_gpr] at R0 M B V
  rw [State.callEntry_gpr _ (by decide)] at R0
  refine ⟨⟨⟨fun q hq => ?_, by rw [rd, k₃.rd], by rw [wr, k₃.wr]⟩, M⟩, B, V⟩
  simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  obtain ⟨n1, n2, n3, n4, n5, n7, n12, nlr⟩ := hq
  by_cases h0 : q = .r0
  · subst h0; rw [R0, k₃.gpr _ (by decide)]
  · have hp : q ∈ preserved := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false]
      cases q <;> simp_all
    rw [P q hp nlr, k₃.gpr _ (by simp [n1, n2, n3])]

theorem callFn_ok {f : String} {body : Prog isa} (hn : body.noCalls = true) {s : State} {base : Addr}
    (hs : Scr s base) {o a b : Nat} {r : Nat → Nat → Nat → Prop}
    (hbody : ∀ t, Entry true t base o a b → Bounded t.mem base a → Bounded t.mem base b →
      WP isa body t (FnPost t base o a b r))
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (callFn f body o a b) s fun t => Op base o s t ∧ Bounded t.mem base o ∧
      r (fe t.mem base o) (fe s.mem base a) (fe s.mem base b) := by
  have ho' : o + 112 ≤ 3584 := ho
  have ha' : a + 112 ≤ 3584 := ha
  have hb' : b + 112 ≤ 3584 := hb
  rw [callFn, WP.seq_iff]
  refine wp_movw fun s₁ u₁ => wp_movw fun s₂ u₂ => wp_movw fun s₃ u₃ => WP.block_nil ?_
  exact call_ok hn hs hbody ((u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (u₃.rest (by decide))))
    (by rw [u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, movw_toNat (by omega)])
    (by rw [u₃.other _ (by decide), u₂.gpr, movw_toNat (by omega)])
    (fun _ => by rw [u₃.gpr, movw_toNat (by omega)]) ab bb

theorem mulA24Call_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : Slot o) (ha : Slot a) (ab : Bounded s.mem base a) :
    WP isa (mulA24Call o a) s fun t => Op base o s t ∧ Bounded t.mem base o ∧
      a24Rel (fe t.mem base o) (fe s.mem base a) (fe s.mem base a) := by
  have ho' : o + 112 ≤ 3584 := ho
  have ha' : a + 112 ≤ 3584 := ha
  rw [mulA24Call, WP.seq_iff]
  refine wp_movw fun s₁ u₁ => wp_movw fun s₂ u₂ => WP.block_nil ?_
  exact call_ok (by decide +kernel) hs (hasB := false) (b := a)
    (fun t he ha' _ => mulA24Fn_ok he ho ha ha')
    ((u₁.rest (by decide)).trans (u₂.rest (by decide))) (by rw [u₂.mem, u₁.mem])
    (by rw [u₂.other _ (by decide), u₁.gpr, movw_toNat (by omega)])
    (by rw [u₂.gpr, movw_toNat (by omega)]) (fun h => absurd h (by decide)) ab ab

/-- `[o] = [a] [b]`, by a call of `vg_gf448_r16_mul`. -/
theorem mulCall_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (Op.code (.mul o a b)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a * F s.mem base b :=
  WP.mono (callFn_ok (by decide +kernel) hs (fun _ he ha' hb' => mulFn_ok he ho ha hb ha' hb') ho ha hb ab bb)
    fun _ ⟨op, bo, v⟩ => ⟨op, bo, toFe_mul v⟩

/-- `[o] = [a] + [b]`, by a call of `vg_gf448_r16_add`. -/
theorem addCall_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (Op.code (.add o a b)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a + F s.mem base b :=
  WP.mono (callFn_ok (by decide +kernel) hs (fun _ he ha' hb' => addFn_ok he ho ha hb ha' hb') ho ha hb ab bb)
    fun _ ⟨op, bo, v⟩ => ⟨op, bo, toFe_add v⟩

/-- `[o] = [a] - [b]`, by a call of `vg_gf448_r16_sub`. -/
theorem subCall_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (Op.code (.sub o a b)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a - F s.mem base b :=
  WP.mono (callFn_ok (by decide +kernel) hs (fun _ he ha' hb' => subFn_ok he ho ha hb ha' hb') ho ha hb ab bb)
    fun _ ⟨op, bo, v⟩ => ⟨op, bo, toFe_sub v⟩

/-- `[o] = a24 [a]`, by a call of `vg_gf448_r16_mul_a24`. -/
theorem a24Call_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : Slot o) (ha : Slot a) (ab : Bounded s.mem base a) :
    WP isa (Op.code (.mulSmall o a)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = Spec.X448.a24 * F s.mem base a :=
  WP.mono (mulA24Call_ok hs ho ha ab) fun _ ⟨op, bo, v⟩ => ⟨op, bo, toFe_a24 v⟩

end VG.Proof.X448.Arm
