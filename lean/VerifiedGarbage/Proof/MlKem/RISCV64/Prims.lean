module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.MlKem.RISCV64.Mul
public import VerifiedGarbage.Proof.MlKem.RISCV64.Add
public import VerifiedGarbage.Proof.MlKem.RISCV64.Lay
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Mul
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Add
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Lay
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.Covers

/-!
# ML-KEM on RISC-V: calling the primitives

As on PPC64LE (`Proof/MlKem/PPC64LE/Prims.lean`). For each primitive, a
contract written with the precondition of its proof (`Add.Pre`, …) and what
its correctness proof shows (`kAdd`, …), from which a caller runs a call of
it (`add_call`, …, by `WP.call`), given its arguments in the registers and
its buffers where it may access them (`AccArgs`, …); and that two runs that
call it with the same pointers leak the same trace (`add_ct`, …, by
`RelCT.call`, with constant time from the taint analysis of its code).
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## Generic -/

/-- A contract from a precondition, what the code leaves and the public data. -/
def mkK (P : State → Prop) (Q : State → State → Prop) (pub : State → State → Prop) : Contract isa :=
  { pre := P, post := Q, pub := pub }

/-- The stack pointers and the registers `rs` are the same. -/
def regsEq (rs : List Reg) (s₁ s₂ : State) : Prop := s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem mkK_ok {c : Prog isa} {P : State → Prop} {Q : State → State → Prop} {pub : State → State → Prop}
    (h : ∀ s₀, P s₀ → WP isa c s₀ fun s =>
      (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.gpr .ra = s₀.gpr .ra ∧ Q s₀ s) :
    ∀ s, (mkK P Q pub).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (mkK P Q pub).post s s' :=
  fun s hs => let ⟨t, s', he, h1, h2, h3, h4⟩ := h s hs; ⟨t, s', he, ⟨h1, h2, h3⟩, h4⟩

/-- The state a callee runs from, with the permissions it is given. -/
abbrev view (s : State) (rd wr : List Region) : State := s.callEntry.withRegions rd wr

theorem view_gpr' (s : State) (rd wr : List Region) {r : Reg} (hr : r ∉ linkRegs) :
    (view s rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

/-- A call of a primitive without frames: what it keeps, and its postcondition. -/
theorem call_kept {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hn : c.noFrames = true) {s : State} {rd wr : List Region} (hpre : k.pre (view s rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept wr s s' → k.post (view s rd wr) (s'.withRegions rd wr) → Q s') :
    WP isa (.call n c) s Q :=
  WP.call hv hpre hc hw (fun s' hrd hwr hsp hf hcs _ hp => hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ hp) hn

/-- Two runs that call a primitive with the same arguments `x`, from the same
stack pointer. -/
theorem call_ct {α : Type} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (A : α → State → Prop) (rd wr : α → List Region)
    (hpre : ∀ x s, A x s → k.pre (view s (rd x) (wr x)))
    (hcov : ∀ x s, A x s → Covers (rd x ++ wr x) (s.rd ++ s.wr) ∧ Covers (wr x) s.wr)
    (hpub : ∀ x a b, A x a → A x b → a.sp = b.sp → k.pub (view a (rd x) (wr x)) (view b (rd x) (wr x)))
    {P : State → State → Prop} (hP : ∀ a b, P a b → a.sp = b.sp ∧ ∃ x, A x a ∧ A x b) :
    RelCT isa P (.call n c) fun _ _ => True := by
  refine RelCT.mono (P := fun (a b : State) => ∃ y : α × Addr, (A y.1 a ∧ a.sp = y.2) ∧ (A y.1 b ∧ b.sp = y.2))
    (RelCT.exists_ fun y => ?_) (fun (a b : State) h => let ⟨e, x, ha, hb⟩ := hP a b h; ⟨(x, a.sp), ⟨ha, rfl⟩, hb, e.symm⟩)
    (fun _ _ h => h)
  exact RelCT.call hv hct (rd y.1) (wr y.1) fun a b ⟨⟨ha, ea⟩, hb, eb⟩ =>
    ⟨hpre _ a ha, hpre _ b hb, hpub _ a b ha hb (ea.trans eb.symm), (hcov _ a ha).1, (hcov _ a ha).2,
      (hcov _ b hb).1, (hcov _ b hb).2⟩

theorem covers_append {rs ts ws : List Region} (h₁ : Covers rs ws) (h₂ : Covers ts ws) : Covers (rs ++ ts) ws :=
  fun x n ⟨q, hq, hc⟩ => (List.mem_append.mp hq).elim (fun h => h₁ x n ⟨q, h, hc⟩) (fun h => h₂ x n ⟨q, h, hc⟩)

theorem covers_cons' {r : Region} {rs ws : List Region} (h₁ : Covers [r] ws) (h₂ : Covers rs ws) :
    Covers (r :: rs) ws := covers_append (rs := [r]) h₁ h₂

theorem covers_nil' {ws : List Region} : Covers [] ws := fun _ _ ⟨_, h, _⟩ => absurd h List.not_mem_nil

theorem covers_rd {rs rd wr : List Region} (h : Covers rs rd) : Covers rs (rd ++ wr) := fun x n hi =>
  let ⟨r, hr, hc⟩ := h x n hi; ⟨r, List.mem_append_left _ hr, hc⟩

theorem covers_wr {rs rd wr : List Region} (h : Covers rs wr) : Covers rs (rd ++ wr) := fun x n hi =>
  let ⟨r, hr, hc⟩ := h x n hi; ⟨r, List.mem_append_right _ hr, hc⟩

theorem regsEq_view {rs : List Reg} (hl : ∀ r ∈ rs, r ∉ linkRegs) {a b : State} (hsp : a.sp = b.sp)
    (hab : ∀ r ∈ rs, a.gpr r = b.gpr r) (rd wr : List Region) : regsEq rs (view a rd wr) (view b rd wr) :=
  ⟨by simp only [State.withRegions_sp, State.callEntry_sp, hsp], fun r hr => by
    rw [view_gpr' _ _ _ (hl r hr), view_gpr' _ _ _ (hl r hr), hab r hr]⟩

/-! ## `vg_mlkem_add` and `vg_mlkem_sub` -/

def kAdd : Contract isa := mkK Add.Pre
  (fun s₀ s => PolyIs s.mem (Add.F s₀) (add (polyAt s₀.mem (Add.F s₀)) (polyAt s₀.mem (Add.G s₀))))
  (regsEq [.a0, .a1])

def kSub : Contract isa := mkK Add.Pre
  (fun s₀ s => PolyIs s.mem (Add.F s₀) (sub (polyAt s₀.mem (Add.F s₀)) (polyAt s₀.mem (Add.G s₀))))
  (regsEq [.a0, .a1])

theorem kAdd_ok : ∀ s, kAdd.pre s → ∃ t s', Exec isa Impl.MlKem.RISCV64.add s t s' ∧ abiPreserved s s' ∧
    kAdd.post s s' :=
  mkK_ok fun _ hp => WP.mono (Add.loop_ok hp (Add.add_hb hp)) fun _ h =>
    ⟨h.pres, h.sp, h.ra, Add.polyIs_of_inv h fun _ _ => rfl⟩

theorem kSub_ok : ∀ s, kSub.pre s → ∃ t s', Exec isa Impl.MlKem.RISCV64.sub s t s' ∧ abiPreserved s s' ∧
    kSub.post s s' :=
  mkK_ok fun _ hp => WP.mono (Add.loop_ok hp (Add.sub_hb hp)) fun _ h =>
    ⟨h.pres, h.sp, h.ra, Add.polyIs_of_inv h fun _ _ => rfl⟩

theorem kAdd_ct : ConstantTime isa kAdd.pre kAdd.pub Impl.MlKem.RISCV64.add :=
  Add.ctRegs (k := kAdd) [.a0, .a1] (fun _ _ h => h.2) (fun _ _ h => h.1) (by taint_decide)

theorem kSub_ct : ConstantTime isa kSub.pre kSub.pub Impl.MlKem.RISCV64.sub :=
  Add.ctRegs (k := kSub) [.a0, .a1] (fun _ _ h => h.2) (fun _ _ h => h.1) (by taint_decide)

/-- The arguments of `vg_mlkem_add` or `vg_mlkem_sub`: `f` and `g`. -/
structure AccArgs (s : State) (f g : Addr) : Prop where
  a0 : s.gpr .a0 = f
  a1 : s.gpr .a1 = g
  disj : (polyRegion f).Disjoint (polyRegion g)
  ff : f.toNat + 1024 ≤ 2 ^ 64
  fg : g.toNat + 1024 ≤ 2 ^ 64
  redF : Reduced s.mem f
  redG : Reduced s.mem g
  alF : f.toNat % 4 = 0
  alG : g.toNat % 4 = 0
  cw : Covers [polyRegion f] s.wr
  cr : Covers [polyRegion g] (s.rd ++ s.wr)

theorem acc_pre {s : State} {f g : Addr} (h : AccArgs s f g) :
    Add.Pre (view s [polyRegion g] [polyRegion f]) := by
  have e3 := view_gpr' s [polyRegion g] [polyRegion f] (r := .a0) (by decide)
  have e4 := view_gpr' s [polyRegion g] [polyRegion f] (r := .a1) (by decide)
  rw [h.a0] at e3; rw [h.a1] at e4
  exact ⟨by simp only [Add.G, e4]; rfl, by simp only [Add.F, e3]; rfl,
    by simp only [Add.F, Add.G, e3, e4]; exact h.disj,
    by simp only [Add.F, e3]; exact h.ff, by simp only [Add.G, e4]; exact h.fg,
    by simp only [Add.F, e3]; exact h.redF, by simp only [Add.G, e4]; exact h.redG,
    by simp only [Add.F, e3]; exact h.alF, by simp only [Add.G, e4]; exact h.alG⟩

theorem add_call {s : State} {f g : Addr} (h : AccArgs s f g) {Q : State → Prop}
    (hQ : ∀ s', Kept [polyRegion f] s s' → PolyIs s'.mem f (add (polyAt s.mem f) (polyAt s.mem g)) → Q s') :
    WP isa (.call "vg_mlkem_add" Impl.MlKem.RISCV64.add) s Q :=
  call_kept (k := kAdd) kAdd_ok (by decide +kernel) (acc_pre h) (covers_append h.cr (covers_wr h.cw)) h.cw
    fun s' hk hp => hQ s' hk (by
      have e3 := view_gpr' s [polyRegion g] [polyRegion f] (r := .a0) (by decide)
      have e4 := view_gpr' s [polyRegion g] [polyRegion f] (r := .a1) (by decide)
      rw [h.a0] at e3; rw [h.a1] at e4
      simpa only [kAdd, mkK, Add.F, Add.G, e3, e4, State.withRegions_mem, State.callEntry_mem] using hp)

theorem sub_call {s : State} {f g : Addr} (h : AccArgs s f g) {Q : State → Prop}
    (hQ : ∀ s', Kept [polyRegion f] s s' → PolyIs s'.mem f (sub (polyAt s.mem f) (polyAt s.mem g)) → Q s') :
    WP isa (.call "vg_mlkem_sub" Impl.MlKem.RISCV64.sub) s Q :=
  call_kept (k := kSub) kSub_ok (by decide +kernel) (acc_pre h) (covers_append h.cr (covers_wr h.cw)) h.cw
    fun s' hk hp => hQ s' hk (by
      have e3 := view_gpr' s [polyRegion g] [polyRegion f] (r := .a0) (by decide)
      have e4 := view_gpr' s [polyRegion g] [polyRegion f] (r := .a1) (by decide)
      rw [h.a0] at e3; rw [h.a1] at e4
      simpa only [kSub, mkK, Add.F, Add.G, e3, e4, State.withRegions_mem, State.callEntry_mem] using hp)

theorem acc_pub {f g : Addr} {a b : State} (ha : AccArgs a f g) (hb : AccArgs b f g) (hsp : a.sp = b.sp) :
    regsEq [.a0, .a1] (view a [polyRegion g] [polyRegion f]) (view b [polyRegion g] [polyRegion f]) :=
  regsEq_view (by decide) hsp (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [ha.a0, hb.a0]
    · rw [ha.a1, hb.a1]) _ _

theorem add_ct {P : State → State → Prop}
    (hP : ∀ a b, P a b → a.sp = b.sp ∧ ∃ f g, AccArgs a f g ∧ AccArgs b f g) :
    RelCT isa P (.call "vg_mlkem_add" Impl.MlKem.RISCV64.add) fun _ _ => True :=
  call_ct (k := kAdd) kAdd_ok kAdd_ct (fun (x : Addr × Addr) s => AccArgs s x.1 x.2)
    (fun x => [polyRegion x.2]) (fun x => [polyRegion x.1])
    (fun _ _ h => acc_pre h) (fun _ _ h => ⟨covers_append h.cr (covers_wr h.cw), h.cw⟩)
    (fun _ _ _ ha hb e => acc_pub ha hb e)
    fun a b hab => let ⟨e, f, g, h₁, h₂⟩ := hP a b hab; ⟨e, (f, g), h₁, h₂⟩

theorem sub_ct {P : State → State → Prop}
    (hP : ∀ a b, P a b → a.sp = b.sp ∧ ∃ f g, AccArgs a f g ∧ AccArgs b f g) :
    RelCT isa P (.call "vg_mlkem_sub" Impl.MlKem.RISCV64.sub) fun _ _ => True :=
  call_ct (k := kSub) kSub_ok kSub_ct (fun (x : Addr × Addr) s => AccArgs s x.1 x.2)
    (fun x => [polyRegion x.2]) (fun x => [polyRegion x.1])
    (fun _ _ h => acc_pre h) (fun _ _ h => ⟨covers_append h.cr (covers_wr h.cw), h.cw⟩)
    (fun _ _ _ ha hb e => acc_pub ha hb e)
    fun a b hab => let ⟨e, f, g, h₁, h₂⟩ := hP a b hab; ⟨e, (f, g), h₁, h₂⟩

/-! ## `vg_mlkem_multiply_ntts` -/

def kMul : Contract isa := mkK Mul.Pre
  (fun s₀ s => PolyIs s.mem (Mul.H s₀) (multiplyNTTs (Mul.fp s₀) (Mul.gp s₀))) (regsEq [.a0, .a1, .a2, .a3])

theorem kMul_ok : ∀ s, kMul.pre s → ∃ t s', Exec isa Impl.MlKem.RISCV64.multiplyNTTs s t s' ∧
    abiPreserved s s' ∧ kMul.post s s' :=
  mkK_ok fun _ hp => Mul.correct hp

theorem kMul_ct : ConstantTime isa kMul.pre kMul.pub Impl.MlKem.RISCV64.multiplyNTTs :=
  Add.ctRegs (k := kMul) [.a0, .a1, .a2, .a3] (fun _ _ h => h.2) (fun _ _ h => h.1) (by taint_decide)

/-- The arguments of `vg_mlkem_multiply_ntts`. -/
structure MulArgs (s : State) (h f g scr : Addr) : Prop where
  a0 : s.gpr .a0 = h
  a1 : s.gpr .a1 = f
  a2 : s.gpr .a2 = g
  a3 : s.gpr .a3 = scr
  hf : (polyRegion h).Disjoint (polyRegion f)
  hg : (polyRegion h).Disjoint (polyRegion g)
  hs : (polyRegion h).Disjoint (polyRegion scr)
  fs : (polyRegion f).Disjoint (polyRegion scr)
  gs : (polyRegion g).Disjoint (polyRegion scr)
  fh : h.toNat + 1024 ≤ 2 ^ 64
  ff : f.toNat + 1024 ≤ 2 ^ 64
  fg : g.toNat + 1024 ≤ 2 ^ 64
  fscr : scr.toNat + 1024 ≤ 2 ^ 64
  redF : Reduced s.mem f
  redG : Reduced s.mem g
  alH : h.toNat % 4 = 0
  alF : f.toNat % 4 = 0
  alG : g.toNat % 4 = 0
  alS : scr.toNat % 8 = 0
  cw : Covers [polyRegion h, polyRegion scr] s.wr
  cr : Covers [polyRegion f, polyRegion g] (s.rd ++ s.wr)

abbrev mulRd (f g : Addr) : List Region := [polyRegion f, polyRegion g]
abbrev mulWr (h scr : Addr) : List Region := [polyRegion h, polyRegion scr]

theorem mul_pre {s : State} {h f g scr : Addr} (a : MulArgs s h f g scr) :
    Mul.Pre (view s (mulRd f g) (mulWr h scr)) := by
  have e3 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .a0) (by decide)
  have e4 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .a1) (by decide)
  have e5 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .a2) (by decide)
  have e6 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .a3) (by decide)
  rw [a.a0] at e3; rw [a.a1] at e4; rw [a.a2] at e5; rw [a.a3] at e6
  exact ⟨by simp only [Mul.F, Mul.G, e4, e5]; rfl, by simp only [Mul.H, Mul.S, e3, e6]; rfl,
    by simp only [Mul.H, Mul.F, e3, e4]; exact a.hf,
    by simp only [Mul.H, Mul.G, e3, e5]; exact a.hg,
    by simp only [Mul.H, Mul.S, e3, e6]; exact a.hs,
    by simp only [Mul.F, Mul.S, e4, e6]; exact a.fs,
    by simp only [Mul.G, Mul.S, e5, e6]; exact a.gs,
    by simp only [Mul.H, e3]; exact a.fh, by simp only [Mul.F, e4]; exact a.ff,
    by simp only [Mul.G, e5]; exact a.fg, by simp only [Mul.S, e6]; exact a.fscr,
    by simp only [Mul.F, e4]; exact a.redF, by simp only [Mul.G, e5]; exact a.redG,
    by simp only [Mul.H, e3]; exact a.alH, by simp only [Mul.F, e4]; exact a.alF,
    by simp only [Mul.G, e5]; exact a.alG, by simp only [Mul.S, e6]; exact a.alS⟩

theorem mul_call {s : State} {h f g scr : Addr} (a : MulArgs s h f g scr) {Q : State → Prop}
    (hQ : ∀ s', Kept (mulWr h scr) s s' →
      PolyIs s'.mem h (multiplyNTTs (polyAt s.mem f) (polyAt s.mem g)) → Q s') :
    WP isa (.call "vg_mlkem_multiply_ntts" Impl.MlKem.RISCV64.multiplyNTTs) s Q :=
  call_kept (k := kMul) kMul_ok (by decide +kernel) (mul_pre a) (covers_append a.cr (covers_wr a.cw)) a.cw
    fun s' hk hp => hQ s' hk (by
      have e3 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .a0) (by decide)
      have e4 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .a1) (by decide)
      have e5 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .a2) (by decide)
      rw [a.a0] at e3; rw [a.a1] at e4; rw [a.a2] at e5
      simpa only [kMul, mkK, Mul.H, Mul.fp, Mul.gp, Mul.F, Mul.G, e3, e4, e5,
        State.withRegions_mem, State.callEntry_mem] using hp)

theorem mul_ct {P : State → State → Prop}
    (hP : ∀ a b, P a b → a.sp = b.sp ∧ ∃ h f g scr, MulArgs a h f g scr ∧ MulArgs b h f g scr) :
    RelCT isa P (.call "vg_mlkem_multiply_ntts" Impl.MlKem.RISCV64.multiplyNTTs) fun _ _ => True :=
  call_ct (k := kMul) kMul_ok kMul_ct (fun (x : Addr × Addr × Addr × Addr) s =>
      MulArgs s x.1 x.2.1 x.2.2.1 x.2.2.2)
    (fun x => mulRd x.2.1 x.2.2.1) (fun x => mulWr x.1 x.2.2.2)
    (fun _ _ h => mul_pre h) (fun _ _ h => ⟨covers_append h.cr (covers_wr h.cw), h.cw⟩)
    (fun _ _ _ ha hb e => regsEq_view (by decide) e (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [ha.a0, hb.a0]
      · rw [ha.a1, hb.a1]
      · rw [ha.a2, hb.a2]
      · rw [ha.a3, hb.a3]) _ _)
    fun a b hab => let ⟨e, h, f, g, scr, h₁, h₂⟩ := hP a b hab; ⟨e, (h, f, g, scr), h₁, h₂⟩

end VG.Proof.MlKem.RISCV64
