import VerifiedGarbage.Impl.Ed25519.AArch64.Power
import VerifiedGarbage.Proof.Ed25519.AArch64.Field
import VerifiedGarbage.Proof.X25519.Invert
import VerifiedGarbage.Proof.Ed25519.RootPower
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.Covers

/-! Merged from `Proof.Ed25519.AArch64.PowerEnv`. -/
section
/-! Compositional field exponentiation and fixed-count squaring loops. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open VG.Proof.X25519 (sqn)

def opMul (o a b : Slot) (e : Env) : Env := Function.update e o (e a * e b)

/-- What the inversion keeps: the registers but `clob` and `x19`, the regions,
and the memory outside `[512, 640)`. -/
structure IKeep (base : Addr) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .x19 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  mem : Outside base 512 128 s.mem s'.mem

theorem IKeep.trans {base : Addr} {s₁ s₂ s₃ : State} (h₁ : IKeep base s₁ s₂)
    (h₂ : IKeep base s₂ s₃) : IKeep base s₁ s₃ :=
  ⟨fun r hr hb => (h₂.gpr r hr hb).trans (h₁.gpr r hr hb), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp,
    h₁.mem.trans h₂.mem⟩

theorem IKeep.scr {base : Addr} {s s' : State} (h : IKeep base s s') (hs : Scr s base large) :
    Scr s' base large :=
  ⟨(h.gpr _ (by decide) (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

/-- `c` changes the slots by `f`, and keeps everything else (`IKeep`). -/
def ISpec (base : Addr) (c : Prog isa) (f : Env → Env) : Prop :=
  ∀ s, Scr s base large → WP isa c s fun s' => IKeep base s s' ∧ env s'.mem base = f (env s.mem base)

theorem ISpec.seq {base : Addr} {c₁ c₂ : Prog isa} {f g : Env → Env} (h₁ : ISpec (large := large) base c₁ f)
    (h₂ : ISpec (large := large) base c₂ g) : ISpec (large := large) base (.seq c₁ c₂) fun e => g (f e) := fun s hs =>
  WP.seq (WP.mono (h₁ s hs) fun _ ⟨k₁, e₁⟩ =>
    WP.mono (h₂ _ (k₁.scr hs)) fun _ ⟨k₂, e₂⟩ => ⟨k₁.trans k₂, by rw [e₂, e₁]⟩)

theorem ISpec.append {base : Addr} {l₁ l₂ : List Instr} {f g : Env → Env}
    (h₁ : ISpec (large := large) base (.block l₁) f) (h₂ : ISpec (large := large) base (.block l₂) g) :
    ISpec (large := large) base (.block (l₁ ++ l₂)) fun e => g (f e) := fun s hs => by
  rw [WP.block_append_iff]
  exact WP.mono (h₁ s hs) fun _ ⟨k₁, e₁⟩ =>
    WP.mono (h₂ _ (k₁.scr hs)) fun _ ⟨k₂, e₂⟩ => ⟨k₁.trans k₂, by rw [e₂, e₁]⟩

/-- A slot of the inversion's: 14 to 17. -/
abbrev ISlot (o : Slot) : Prop := 14 ≤ o.val ∧ o.val < 18

/-- A multiplication into a slot of the inversion's, which also keeps `x19`. -/
theorem mulI_ok {s : State} {base : Addr} (hs : Scr s base large) (o a b : Slot) (ho : ISlot o) :
    WP isa (.block (fieldMul (offset o) (offset a) (offset b))) s fun s' =>
      IKeep base s s' ∧ s'.gpr .x19 = s.gpr .x19 ∧ env s'.mem base = opMul o a b (env s.mem base) :=
  WP.mono (mul_ok hs (slot_rangeWith (large := large) o) (slot_rangeWith (large := large) a) (slot_rangeWith (large := large) b)) fun _ ⟨h, e⟩ =>
    ⟨⟨fun r hr _ => h.gpr r hr, h.rd, h.wr, h.sp, h.mem.mono (by simp only [offset]; omega) (by simp only [offset]; omega)⟩,
      h.gpr _ (by decide), by rw [env_update o h.mem, e]; rfl⟩

theorem mulI (base : Addr) (o a b : Slot) (ho : ISlot o) :
    ISpec (large := large) base (.block (fieldMul (offset o) (offset a) (offset b))) (opMul o a b) := fun _ hs =>
  WP.mono (mulI_ok hs o a b ho) fun _ ⟨k, _, e⟩ => ⟨k, e⟩

/-- A squaring into a slot of the inversion's, which also keeps `x19`. -/
theorem sqrI_ok {s : State} {base : Addr} (hs : Scr s base large) (o a : Slot) (ho : ISlot o) :
    WP isa (.block (fieldSqr (offset o) (offset a))) s fun s' =>
      IKeep base s s' ∧ s'.gpr .x19 = s.gpr .x19 ∧ env s'.mem base = opMul o a a (env s.mem base) :=
  WP.mono (sqr_ok hs (slot_rangeWith (large := large) o) (slot_rangeWith (large := large) a)) fun _ ⟨h, e⟩ =>
    ⟨⟨fun r hr _ => h.gpr r hr, h.rd, h.wr, h.sp, h.mem.mono (by simp only [offset]; omega) (by simp only [offset]; omega)⟩,
      h.gpr _ (by decide), by rw [env_update o h.mem, e]; rfl⟩

theorem sqrI (base : Addr) (o a : Slot) (ho : ISlot o) :
    ISpec (large := large) base (.block (fieldSqr (offset o) (offset a))) (opMul o a a) := fun _ hs =>
  WP.mono (sqrI_ok hs o a ho) fun _ ⟨k, _, e⟩ => ⟨k, e⟩

/-! ## Runs of squarings -/

theorem decX19_ok {s : State} {k : Nat} (hb : s.gpr .x19 = BitVec.ofNat 64 (k + 1)) :
    WP isa (.block [.subImm .x .x19 .x19 1]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 k ∧ Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (1 : Nat) < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, hb, BitVec.ofNat_add, BitVec.add_sub_cancel]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

theorem counter_nonzero {k : Nat} (hk : k < 2 ^ 64) :
    (BitVec.ofNat 64 k != 0) = decide (k ≠ 0) := by
  by_cases h : k = 0
  · subst k; rfl
  · rw [decide_eq_true h]
    apply bne_iff_ne.mpr
    intro he
    have he' := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, show (0 : BitVec 64).toNat = 0 from rfl] at he'
    exact h he'

/-- Slot `o` becomes slot `a` squared `n` times. -/
def opSqn (o a : Slot) (n : Nat) (e : Env) : Env := Function.update e o (sqn (e a) n)

theorem opMul_update (o : Slot) (e : Env) (v : Spec.X25519.Fe) :
    opMul o o o (Function.update e o v) = Function.update e o (v * v) := by
  simp only [opMul, Function.update_self, Function.update_idem]

/-- The loop of `sqn`, with the counter `x19 = m` and slot `o` squared
`n - m` times since `s₀`. -/
theorem sqLoop_ok {s₀ : State} {base : Addr} (hs₀ : Scr s₀ base large) (o : Slot) (ho : ISlot o)
    (x : Spec.X25519.Fe) (n : Nat) (hn : n < 2 ^ 32) :
    ∀ m s, 1 ≤ m → m < n → IKeep base s₀ s → s.gpr .x19 = BitVec.ofNat 64 m →
      env s.mem base = Function.update (env s₀.mem base) o (sqn x (n - m)) →
      WP isa (.loop (.block (fieldSqr (offset o) (offset o) ++
          ([.subImm .x .x19 .x19 1] : List Instr))) (.nonzero .x .x19)) s fun s' =>
        IKeep base s₀ s' ∧ env s'.mem base = Function.update (env s₀.mem base) o (sqn x n) := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  intro m s h1 h2 hk hb he
  refine WP.loop (M := isa) (Inv := fun m (s : State) => 1 ≤ m ∧ m < n ∧ IKeep base s₀ s ∧
    s.gpr .x19 = BitVec.ofNat 64 m ∧
    env s.mem base = Function.update (env s₀.mem base) o (sqn x (n - m))) ?_ m s ⟨h1, h2, hk, hb, he⟩
  intro m s ⟨h1, h2, hk, hb, he⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [WP.block_append_iff]
  refine WP.mono (sqrI_ok (hk.scr hs₀) o o ho) fun s1 ⟨k1, b1, e1⟩ => ?_
  refine WP.mono (decX19_ok (b1.trans hb)) fun s2 ⟨b2, kdec⟩ => ?_
  have k2 : IKeep base s₀ s2 := hk.trans (k1.trans ⟨fun r _ hr => kdec.gpr r (by simpa only [List.mem_singleton] using hr), kdec.rd, kdec.wr, kdec.sp,
    by rw [kdec.mem]; exact Outside.refl _ _ _ _⟩)
  have e2 : env s2.mem base = Function.update (env s₀.mem base) o (sqn x (n - m)) := by
    rw [kdec.mem, e1, he, opMul_update]
    congr 2
    rw [show n - m = (n - (m + 1)) + 1 by omega]
    rfl
  simp only [eval, read_x, b2, counter_nonzero (by omega : m < 2 ^ 64)]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, k2, by rw [e2, Nat.sub_zero]⟩
  · exact .inr ⟨by simp only [decide_eq_true (by omega : m ≠ 0)], m, by omega,
      by omega, by omega, k2, rfl, e2⟩

/-- `sqn o a n`: slot `o` becomes slot `a` squared `n` times (`o` may be `a`). -/
theorem sqnI (base : Addr) (o a : Slot) (ho : ISlot o) (n : Nat) (hn : 2 ≤ n)
    (hn' : n < 2 ^ 32) :
    ISpec (large := large) base (Impl.Ed25519.AArch64.sqn (offset o) (offset a) n) (opSqn o a n) := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  intro s hs
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (sqrI_ok hs o a ho) fun s1 ⟨k1, _, e1⟩ => ?_
  refine WP.mono (const64_ok s1 .x19 (BitVec.ofNat 64 (n - 1))) fun s2 ⟨b2, kdec⟩ => ?_
  have k2 : IKeep base s s2 := k1.trans ⟨fun r _ hr => kdec.gpr r (by simpa only [List.mem_singleton] using hr), kdec.rd, kdec.wr, kdec.sp,
    by rw [kdec.mem]; exact Outside.refl _ _ _ _⟩
  refine sqLoop_ok hs o ho (env s.mem base a) n hn' (n - 1) s2 (by omega) (by omega) k2 b2 ?_
  rw [kdec.mem, e1, show n - (n - 1) = 1 by omega]
  rfl


end VG.Proof.Ed25519.AArch64
end

/-! The shared addition chain computes inversion and square-root powers. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def power250Env (e : Env) : Env :=
  opMul 15 16 15 (opSqn 16 16 50 (opMul 16 17 16 (opSqn 17 16 100
    (opMul 16 16 15 (opSqn 16 15 50 (opMul 15 16 15 (opSqn 16 16 10 (opMul 16 17 16 (opSqn 17 16 20
    (opMul 16 16 15 (opSqn 16 15 10 (opMul 15 16 15 (opSqn 16 15 5 (opMul 15 15 16
    (opMul 16 14 14 (opMul 14 14 15 (opMul 15 2 15 (opMul 15 15 15 (opMul 15 14 14
    (opMul 14 2 2 e))))))))))))))))))))

theorem power250_spec (base : Addr) : ISpec (large := large) base power250 power250Env := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  have h : ISpec (large := large) base _ _ :=
    (sqrI base 14 2 ⟨by decide, by decide⟩).seq <|
    ((sqrI base 15 14 ⟨by decide, by decide⟩).append
      (sqrI base 15 15 ⟨by decide, by decide⟩)).seq <|
    ((((mulI base 15 2 15 ⟨by decide, by decide⟩).append
      (mulI base 14 14 15 ⟨by decide, by decide⟩)).append
      (sqrI base 16 14 ⟨by decide, by decide⟩)).append
      (mulI base 15 15 16 ⟨by decide, by decide⟩)).seq <|
    (sqnI base 16 15 ⟨by decide, by decide⟩ 5 (by decide) (by decide)).seq <|
    (mulI base 15 16 15 ⟨by decide, by decide⟩).seq <|
    (sqnI base 16 15 ⟨by decide, by decide⟩ 10 (by decide) (by decide)).seq <|
    (mulI base 16 16 15 ⟨by decide, by decide⟩).seq <|
    (sqnI base 17 16 ⟨by decide, by decide⟩ 20 (by decide) (by decide)).seq <|
    (mulI base 16 17 16 ⟨by decide, by decide⟩).seq <|
    (sqnI base 16 16 ⟨by decide, by decide⟩ 10 (by decide) (by decide)).seq <|
    (mulI base 15 16 15 ⟨by decide, by decide⟩).seq <|
    (sqnI base 16 15 ⟨by decide, by decide⟩ 50 (by decide) (by decide)).seq <|
    (mulI base 16 16 15 ⟨by decide, by decide⟩).seq <|
    (sqnI base 17 16 ⟨by decide, by decide⟩ 100 (by decide) (by decide)).seq <|
    (mulI base 16 17 16 ⟨by decide, by decide⟩).seq <|
    (sqnI base 16 16 ⟨by decide, by decide⟩ 50 (by decide) (by decide)).seq <|
    (mulI base 15 16 15 ⟨by decide, by decide⟩)
  exact h

/-! ## `vg_gf25519_r64_pow250` as a function, and its calls -/

theorem powKept_lanes : ∀ k ∈ powKept, k.2.2 < 2 := by decide
theorem powKept_nodup_lanes : (powKept.map fun k => (k.2.1, k.2.2)).Nodup := by decide
theorem powKept_nodup : (powKept.map Prod.fst).Nodup := by decide

/-- `power250` writes no vector register. -/
theorem power250_noV : power250.allInstrs (fun i => vdstOf i == none) = true := by decide +kernel

theorem power250_vdst (r : VReg) : ∀ i ∈ instrs power250, vdstOf i ≠ some r := fun i hi => by
  have h := List.all_eq_true.mp (by rw [← Code.allInstrs_eq]; exact power250_noV) i hi
  rw [beq_iff_eq.mp h]; exact fun h' => nomatch h'

/-- `powFn`: the slots as after `power250`, which writes only `[512, 640)` of the working
space, and every register outside `clob`, or kept in a lane, restored. -/
theorem powFn_ok {s : State} {base : Addr} (hs : Scr s base false) :
    WP isa powFn s fun u =>
      (∀ r, (r ∉ clob ∨ r ∈ powKept.map Prod.fst) → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧
        u.wr = s.wr ∧ u.sp = s.sp ∧ Outside base 512 128 s.mem u.mem ∧
        env u.mem base = power250Env (env s.mem base) := by
  unfold powFn
  rw [WP.seq_iff]
  refine WP.mono (insOf_ok powKept s powKept_lanes powKept_nodup_lanes)
    fun s₁ ⟨hg, hm, hr, hw, hsp, hls, _⟩ => ?_
  have hs₁ : Scr s₁ base false := ⟨by rw [hg]; exact hs.x0, by rw [hw]; exact hs.wr, hs.nowrap⟩
  rw [WP.seq_iff]
  obtain ⟨tb, t, he, hk, hev⟩ := power250_spec (large := false) base s₁ hs₁
  refine ⟨tb, t, he, ?_⟩
  have tl : ∀ k ∈ powKept, laneOf t k.2.1 k.2.2 = s.gpr k.1 := fun k hk' => by
    rw [laneOf, Exec.vec (power250_vdst _) he, ← laneOf, hls k hk']
  refine WP.mono (umovOf_ok powKept t powKept_lanes powKept_nodup)
    fun u ⟨um, ur, uw, usp, uls, uoth⟩ => ?_
  refine ⟨fun r hr' => ?_, by rw [ur, hk.rd, hr], by rw [uw, hk.wr, hw], by rw [usp, hk.sp, hsp],
    by rw [um, ← hm]; exact hk.mem, by rw [um, hev, hm]⟩
  by_cases hm' : r ∈ powKept.map Prod.fst
  · obtain ⟨k, hk', rfl⟩ := List.mem_map.mp hm'
    rw [uls k hk', tl k hk']
  · have h19 : r ≠ .x19 := fun h => hm' (by rw [h]; decide)
    rw [uoth r hm', hk.gpr r (hr'.resolve_right hm') h19, hg]

theorem powFn_keepsV : powFn.allInstrs keepsV = true := by decide +kernel

theorem powFn_v31 : ∀ i ∈ instrs powFn, vdstOf i ≠ some .v31 := fun i hi => by
  have h := List.all_eq_true.mp (by rw [← Code.allInstrs_eq]; exact (by decide +kernel :
    powFn.allInstrs (fun i => vdstOf i != some .v31) = true)) i hi
  simpa using h

/-- The callee-saved registers `powFn` restores. -/
theorem powFn_preserved : ∀ r ∈ preserved, r ∉ clob ∨ r ∈ powKept.map Prod.fst := by decide

/-- The contract of the call, from `powFn_ok`. -/
def powK (base : Addr) : Contract isa where
  pre t := t.rd = [] ∧ t.wr = [⟨base, 4096⟩] ∧ t.gpr .x0 = base ∧ base.toNat + 4096 ≤ 2 ^ 64
  post t t' := (∀ r, r ∉ clob → t'.gpr r = t.gpr r) ∧ Outside base 512 128 t.mem t'.mem ∧
    env t'.mem base = power250Env (env t.mem base) ∧ t'.v .v31 = t.v .v31
  pub _ _ := True

/-- **A call of `vg_gf25519_r64_pow250`**, with the return address kept in `v31`, as `power250`. -/
theorem powCall_spec (base : Addr) : ISpec (large := large) base powCall power250Env := by
  intro s hs
  unfold powCall
  rw [WP.seq_iff]
  refine WP.mono (insOf_ok [(.x30, .v31, 0)] s (by decide) (by decide))
    fun s₁ ⟨g₁, m₁, r₁, w₁, sp₁, l₁, _⟩ => ?_
  rw [WP.seq_iff]
  have hcov : Covers [⟨base, 4096⟩] s₁.wr := Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨⟨base, workSize large⟩, by rw [w₁]; exact hs.wr, 0, (BitVec.add_zero _).symm,
      workSize_ge large⟩
  have hx0 : s₁.gpr .x0 = base := by rw [g₁]; exact hs.x0
  refine WP.callV (k := powK base) (rd := []) (wr := [⟨base, 4096⟩]) ?hv
    ⟨rfl, rfl, by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), hx0],
      by have := workSize_ge large; have := hs.nowrap; omega⟩
    (Covers.right hcov) hcov ?_ (by decide +kernel)
  case hv =>
    intro t ⟨_, hwr, h0, hn⟩
    obtain ⟨tr, t', he, hg, hrd, hwr', hsp, hmem, hev⟩ :=
      powFn_ok (s := t) (base := base) ⟨h0, by rw [hwr]; exact List.mem_singleton_self _, hn⟩
    exact ⟨tr, t', he, ⟨fun r hr => hg r (powFn_preserved r hr), hsp, Exec.preservedV he powFn_keepsV⟩,
      fun r hr => hg r (.inl hr), hmem, hev, Exec.vec powFn_v31 he⟩
  intro t hrd hwr hsp _ _ _ _ ⟨hg, hmem, hev, hv31⟩
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, m₁] at hg hmem hev
  refine WP.mono (umovOf_ok [(.x30, .v31, 0)] t (by decide) (by decide))
    fun u ⟨um, ur, uw, usp, uls, uoth⟩ => ?_
  have l30 : u.gpr .x30 = s.gpr .x30 := by
    rw [uls _ List.mem_cons_self, ← l₁ _ List.mem_cons_self]
    exact congrArg (BitVec.extractLsb' (64 * 0) 64) hv31
  refine ⟨⟨fun r hr h19 => ?_, by rw [ur, hrd, r₁], by rw [uw, hwr, w₁], by rw [usp, hsp, sp₁],
    by rw [um]; exact hmem⟩, by rw [um, hev]⟩
  by_cases h30 : r = .x30
  · rw [h30]; exact l30
  · have hl : r ∉ linkRegs := by
      simp only [linkRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => hr (by rw [h]; decide), fun h => hr (by rw [h]; decide), h30⟩
    rw [uoth r (by simpa using h30), hg r hr, State.callEntry_gpr _ hl, g₁]

def invEnv (e : Env) : Env := opMul 15 15 14 (opSqn 15 15 5 (power250Env e))
def rootEnv (e : Env) : Env := opMul 15 15 2 (opSqn 15 15 2 (power250Env e))

theorem invert_spec (base : Addr) : ISpec (large := large) base invert invEnv := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  have h : ISpec (large := large) base _ _ := (powCall_spec base).seq ((sqnI base 15 15 ⟨by decide, by decide⟩ 5 (by decide) (by decide)).seq
    (mulI base 15 15 14 ⟨by decide, by decide⟩))
  exact h

theorem rootPower_spec (base : Addr) : ISpec (large := large) base Impl.Ed25519.AArch64.rootPower rootEnv := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  have h : ISpec (large := large) base _ _ := (powCall_spec base).seq ((sqnI base 15 15 ⟨by decide, by decide⟩ 2 (by decide) (by decide)).seq
    (mulI base 15 15 2 ⟨by decide, by decide⟩))
  exact h

theorem invEnv_eval (e : Env) : invEnv e 15 = VG.Proof.X25519.invert (e 2) := by
  simp only [↓reduceIte, invEnv, power250Env, opMul, opSqn, Function.update_apply]
  rfl

theorem rootEnv_eval (e : Env) : rootEnv e 15 = VG.Proof.Ed25519.rootPower (e 2) := by
  simp only [↓reduceIte, rootEnv, power250Env, opMul, opSqn, Function.update_apply]
  rfl

theorem invert_ok {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa invert s fun t => IKeep base s t ∧
      env t.mem base 15 = VG.Proof.X25519.invert (env s.mem base 2) :=
  WP.mono (invert_spec base s hs) fun _ ⟨hk, hv⟩ => ⟨hk, by rw [hv, invEnv_eval]⟩

theorem rootPower_ok {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa Impl.Ed25519.AArch64.rootPower s fun t => IKeep base s t ∧
      env t.mem base 15 = VG.Proof.Ed25519.rootPower (env s.mem base 2) :=
  WP.mono (rootPower_spec base s hs) fun _ ⟨hk, hv⟩ => ⟨hk, by rw [hv, rootEnv_eval]⟩

end VG.Proof.Ed25519.AArch64
