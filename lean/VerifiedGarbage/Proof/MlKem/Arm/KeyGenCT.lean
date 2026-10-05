import VerifiedGarbage.Proof.MlKem.Arm.SampleCT
import VerifiedGarbage.Proof.MlKem.Arm.NttInv
import VerifiedGarbage.Proof.MlKem.Arm.Mul
import VerifiedGarbage.Proof.MlKem.Arm.Cbd2
import VerifiedGarbage.Proof.MlKem.Arm.Encode12
import VerifiedGarbage.Proof.MlKem.Arm.Decode12
import VerifiedGarbage.Proof.MlKem.Arm.CompressEncode
import VerifiedGarbage.Proof.MlKem.Arm.Decompress
import VerifiedGarbage.Proof.MlKem.Arm.CallF
import VerifiedGarbage.Impl.MlKem.Arm.Top
import VerifiedGarbage.Proof.MlKem.KPke1024

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.Prims`. -/
section

/-!
# ML-KEM on 32-bit ARM: calling the primitives

For each primitive, a contract written with the precondition of its proof
(`Add.Pre`, …) and what its correctness proof shows (`kAdd`, …), from which a
caller runs a call of it (`add_call`, …, by `WP.call`, or `WP.callF` for
`vg_mlkem_sample_ntt`, which has frames), given its arguments in the registers
and its buffers where it may access them (`AccArgs`, …); and that two runs
that call it with the same pointers leak the same trace (`add_ct`, …, by
`RelCT.call`, with constant time from the taint analysis of its code, or from
`Sample.all_ct`).
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## Generic -/

/-- A contract from a precondition, what the code leaves and the public data. -/
def mkK (P : State → Prop) (Q : State → State → Prop) (pub : State → State → Prop) : Contract isa :=
  { pre := P, post := Q, pub := pub }

/-- The registers `rs` are the same. -/
def regsEq (rs : List Reg) (s₁ s₂ : State) : Prop := ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem mkK_ok {c : Prog isa} {P : State → Prop} {Q : State → State → Prop} {pub : State → State → Prop}
    (h : ∀ s₀, P s₀ → WP isa c s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ Q s₀ s) :
    ∀ s, (VG.Proof.MlKem.Arm.mkK P Q pub).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (VG.Proof.MlKem.Arm.mkK P Q pub).post s s' :=
  fun s hs => let ⟨t, s', he, h1, h2, h3⟩ := h s hs; ⟨t, s', he, ⟨h1, h2⟩, h3⟩

/-- The state a callee runs from, with the permissions it is given. -/
abbrev view (s : State) (rd wr : List Region) : State := s.callEntry.withRegions rd wr

theorem view_gpr' (s : State) (rd wr : List Region) {r : Reg} (hr : r ∉ linkRegs) :
    (VG.Proof.MlKem.Arm.view s rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

/-- A call of a primitive without calls: what it keeps, and its postcondition. -/
theorem call_kept {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hn : c.noCalls = true) {s : State} {rd wr : List Region} (hpre : k.pre (VG.Proof.MlKem.Arm.view s rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept wr s s' → k.post (VG.Proof.MlKem.Arm.view s rd wr) (s'.withRegions rd wr) → Q s') :
    WP isa (.call n c) s Q :=
  WP.call hv hpre hc hw (fun s' hrd hwr hsp hf hcs _ hp => hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ hp) hn

/-- Two runs that call a primitive with the same arguments `x`. -/
theorem call_ct {α : Type} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (A : α → State → Prop) (rd wr : α → List Region)
    (hpre : ∀ x s, A x s → k.pre (VG.Proof.MlKem.Arm.view s (rd x) (wr x)))
    (hcov : ∀ x s, A x s → Covers (rd x ++ wr x) (s.rd ++ s.wr) ∧ Covers (wr x) s.wr)
    (hpub : ∀ x a b, A x a → A x b → k.pub (VG.Proof.MlKem.Arm.view a (rd x) (wr x)) (VG.Proof.MlKem.Arm.view b (rd x) (wr x)))
    {P : State → State → Prop} (hP : ∀ a b, P a b → ∃ x, A x a ∧ A x b) :
    RelCT isa P (.call n c) fun _ _ => True := by
  refine RelCT.mono (P := fun a b => ∃ x, A x a ∧ A x b) (RelCT.exists_ fun x => ?_) hP (fun _ _ h => h)
  exact RelCT.call hv hct (rd x) (wr x) fun a b ⟨ha, hb⟩ =>
    ⟨hpre x a ha, hpre x b hb, hpub x a b ha hb, (hcov x a ha).1, (hcov x a ha).2, (hcov x b hb).1,
      (hcov x b hb).2⟩

/-- A region the state may access. -/
theorem covers_self {r : Region} {ws : List Region} (h : r ∈ ws) : Covers [r] ws := by
  intro x n ⟨q, hq, hc⟩
  rw [List.mem_singleton] at hq; subst hq
  exact ⟨_, h, hc⟩

/-- Part of a region the state may access. -/
theorem covers_off {base : Addr} {L o n : Nat} {ws : List Region} (h : (⟨base, L⟩ : Region) ∈ ws)
    (ho : o + n ≤ L) : Covers [⟨base + BitVec.ofNat 64 o, n⟩] ws := by
  intro x m ⟨q, hq, hc⟩
  rw [List.mem_singleton] at hq; subst hq
  refine ⟨_, h, ?_⟩
  simp only [Region.Contains] at hc ⊢
  bv_omega

theorem covers_append {rs ts ws : List Region} (h₁ : Covers rs ws) (h₂ : Covers ts ws) : Covers (rs ++ ts) ws :=
  fun x n ⟨q, hq, hc⟩ => (List.mem_append.mp hq).elim (fun h => h₁ x n ⟨q, h, hc⟩) (fun h => h₂ x n ⟨q, h, hc⟩)

theorem covers_cons' {r : Region} {rs ws : List Region} (h₁ : Covers [r] ws) (h₂ : Covers rs ws) :
    Covers (r :: rs) ws := VG.Proof.MlKem.Arm.covers_append (rs := [r]) h₁ h₂

theorem covers_nil' {ws : List Region} : Covers [] ws := fun _ _ ⟨_, h, _⟩ => absurd h List.not_mem_nil

theorem covers_rd {rs rd wr : List Region} (h : Covers rs rd) : Covers rs (rd ++ wr) := fun x n hi =>
  let ⟨r, hr, hc⟩ := h x n hi; ⟨r, List.mem_append_left _ hr, hc⟩

theorem covers_wr {rs rd wr : List Region} (h : Covers rs wr) : Covers rs (rd ++ wr) := fun x n hi =>
  let ⟨r, hr, hc⟩ := h x n hi; ⟨r, List.mem_append_right _ hr, hc⟩

/-! ## `vg_mlkem_add` and `vg_mlkem_sub` -/

def kAdd : Contract isa := VG.Proof.MlKem.Arm.mkK Add.Pre
  (fun s₀ s => PolyIs s.mem (Add.F s₀) (add (polyAt s₀.mem (Add.F s₀)) (polyAt s₀.mem (Add.G s₀))))
  (VG.Proof.MlKem.Arm.regsEq [.r0, .r1])

def kSub : Contract isa := VG.Proof.MlKem.Arm.mkK Add.Pre
  (fun s₀ s => PolyIs s.mem (Add.F s₀) (VG.Spec.MlKem.sub (polyAt s₀.mem (Add.F s₀)) (polyAt s₀.mem (Add.G s₀))))
  (VG.Proof.MlKem.Arm.regsEq [.r0, .r1])

theorem kAdd_ok : ∀ s, kAdd.pre s → ∃ t s', Exec isa Impl.MlKem.Arm.add s t s' ∧ abiPreserved s s' ∧
    kAdd.post s s' :=
  VG.Proof.MlKem.Arm.mkK_ok fun _ hp => WP.mono (Add.loop_ok hp (Add.add_hb hp)) fun _ h =>
    ⟨h.pres, h.sp, Add.polyIs_of_inv h fun _ _ => rfl⟩

theorem kSub_ok : ∀ s, kSub.pre s → ∃ t s', Exec isa Impl.MlKem.Arm.sub s t s' ∧ abiPreserved s s' ∧
    kSub.post s s' :=
  VG.Proof.MlKem.Arm.mkK_ok fun _ hp => WP.mono (Add.loop_ok hp (Add.sub_hb hp)) fun _ h =>
    ⟨h.pres, h.sp, Add.polyIs_of_inv h fun _ _ => rfl⟩

theorem kAdd_ct : ConstantTime isa kAdd.pre kAdd.pub Impl.MlKem.Arm.add :=
  Add.ctRegs [.r0, .r1] (fun _ _ h => h) (by taint_decide)

theorem kSub_ct : ConstantTime isa kSub.pre kSub.pub Impl.MlKem.Arm.sub :=
  Add.ctRegs [.r0, .r1] (fun _ _ h => h) (by taint_decide)

/-- The arguments of `vg_mlkem_add` or `vg_mlkem_sub`: `f` and `g`. -/
structure AccArgs (s : State) (f g : BitVec 32) : Prop where
  r0 : s.gpr .r0 = f
  r1 : s.gpr .r1 = g
  disj : (polyRegion (State.addr f)).Disjoint (polyRegion (State.addr g))
  ff : f.toNat + 1024 ≤ 2 ^ 32
  fg : g.toNat + 1024 ≤ 2 ^ 32
  redF : Reduced s.mem (State.addr f)
  redG : Reduced s.mem (State.addr g)
  cw : Covers [polyRegion (State.addr f)] s.wr
  cr : Covers [polyRegion (State.addr g)] (s.rd ++ s.wr)

theorem acc_pre {s : State} {f g : BitVec 32} (h : VG.Proof.MlKem.Arm.AccArgs s f g) :
    Add.Pre (VG.Proof.MlKem.Arm.view s [polyRegion (State.addr g)] [polyRegion (State.addr f)]) := by
  have e0 := VG.Proof.MlKem.Arm.view_gpr' s [polyRegion (State.addr g)] [polyRegion (State.addr f)] (r := .r0) (by decide)
  have e1 := VG.Proof.MlKem.Arm.view_gpr' s [polyRegion (State.addr g)] [polyRegion (State.addr f)] (r := .r1) (by decide)
  rw [h.r0] at e0; rw [h.r1] at e1
  exact ⟨by simp only [Add.G, Add.pg, e1]; rfl, by simp only [Add.F, Add.pf, e0]; rfl,
    by simp only [Add.F, Add.G, Add.pf, Add.pg, e0, e1]; exact h.disj,
    by simp only [Add.pf, e0]; exact h.ff, by simp only [Add.pg, e1]; exact h.fg,
    by simp only [Add.F, Add.pf, e0]; exact h.redF, by simp only [Add.G, Add.pg, e1]; exact h.redG⟩

theorem add_call {s : State} {f g : BitVec 32} (h : VG.Proof.MlKem.Arm.AccArgs s f g) {Q : State → Prop}
    (hQ : ∀ s', Kept [polyRegion (State.addr f)] s s' →
      PolyIs s'.mem (State.addr f) (add (polyAt s.mem (State.addr f)) (polyAt s.mem (State.addr g))) → Q s') :
    WP isa (.call "vg_mlkem_add" Impl.MlKem.Arm.add) s Q :=
  VG.Proof.MlKem.Arm.call_kept (k := VG.Proof.MlKem.Arm.kAdd) VG.Proof.MlKem.Arm.kAdd_ok (by decide +kernel) (VG.Proof.MlKem.Arm.acc_pre h) (VG.Proof.MlKem.Arm.covers_append h.cr (VG.Proof.MlKem.Arm.covers_wr h.cw)) h.cw
    fun s' hk hp => hQ s' hk (by
      have e0 := VG.Proof.MlKem.Arm.view_gpr' s [polyRegion (State.addr g)] [polyRegion (State.addr f)] (r := .r0) (by decide)
      have e1 := VG.Proof.MlKem.Arm.view_gpr' s [polyRegion (State.addr g)] [polyRegion (State.addr f)] (r := .r1) (by decide)
      rw [h.r0] at e0; rw [h.r1] at e1
      simpa only [VG.Proof.MlKem.Arm.kAdd, VG.Proof.MlKem.Arm.mkK, Add.F, Add.G, Add.pf, Add.pg, e0, e1, State.withRegions_mem,
        State.callEntry_mem] using hp)

theorem sub_call {s : State} {f g : BitVec 32} (h : VG.Proof.MlKem.Arm.AccArgs s f g) {Q : State → Prop}
    (hQ : ∀ s', Kept [polyRegion (State.addr f)] s s' →
      PolyIs s'.mem (State.addr f) (VG.Spec.MlKem.sub (polyAt s.mem (State.addr f)) (polyAt s.mem (State.addr g))) → Q s') :
    WP isa (.call "vg_mlkem_sub" Impl.MlKem.Arm.sub) s Q :=
  VG.Proof.MlKem.Arm.call_kept (k := VG.Proof.MlKem.Arm.kSub) VG.Proof.MlKem.Arm.kSub_ok (by decide +kernel) (VG.Proof.MlKem.Arm.acc_pre h) (VG.Proof.MlKem.Arm.covers_append h.cr (VG.Proof.MlKem.Arm.covers_wr h.cw)) h.cw
    fun s' hk hp => hQ s' hk (by
      have e0 := VG.Proof.MlKem.Arm.view_gpr' s [polyRegion (State.addr g)] [polyRegion (State.addr f)] (r := .r0) (by decide)
      have e1 := VG.Proof.MlKem.Arm.view_gpr' s [polyRegion (State.addr g)] [polyRegion (State.addr f)] (r := .r1) (by decide)
      rw [h.r0] at e0; rw [h.r1] at e1
      simpa only [VG.Proof.MlKem.Arm.kSub, VG.Proof.MlKem.Arm.mkK, Add.F, Add.G, Add.pf, Add.pg, e0, e1, State.withRegions_mem,
        State.callEntry_mem] using hp)

theorem acc_pub {f g : BitVec 32} {a b : State} (ha : VG.Proof.MlKem.Arm.AccArgs a f g) (hb : VG.Proof.MlKem.Arm.AccArgs b f g) :
    VG.Proof.MlKem.Arm.regsEq [.r0, .r1] (VG.Proof.MlKem.Arm.view a [polyRegion (State.addr g)] [polyRegion (State.addr f)])
      (VG.Proof.MlKem.Arm.view b [polyRegion (State.addr g)] [polyRegion (State.addr f)]) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [VG.Proof.MlKem.Arm.view_gpr' _ _ _ (by decide), VG.Proof.MlKem.Arm.view_gpr' _ _ _ (by decide), ha.r0, hb.r0]
  · rw [VG.Proof.MlKem.Arm.view_gpr' _ _ _ (by decide), VG.Proof.MlKem.Arm.view_gpr' _ _ _ (by decide), ha.r1, hb.r1]

theorem add_ct {P : State → State → Prop} (hP : ∀ a b, P a b → ∃ f g, VG.Proof.MlKem.Arm.AccArgs a f g ∧ VG.Proof.MlKem.Arm.AccArgs b f g) :
    RelCT isa P (.call "vg_mlkem_add" Impl.MlKem.Arm.add) fun _ _ => True :=
  VG.Proof.MlKem.Arm.call_ct (k := VG.Proof.MlKem.Arm.kAdd) VG.Proof.MlKem.Arm.kAdd_ok VG.Proof.MlKem.Arm.kAdd_ct (fun (x : BitVec 32 × BitVec 32) s => VG.Proof.MlKem.Arm.AccArgs s x.1 x.2)
    (fun x => [polyRegion (State.addr x.2)]) (fun x => [polyRegion (State.addr x.1)])
    (fun _ _ h => VG.Proof.MlKem.Arm.acc_pre h) (fun _ _ h => ⟨VG.Proof.MlKem.Arm.covers_append h.cr (VG.Proof.MlKem.Arm.covers_wr h.cw), h.cw⟩)
    (fun _ _ _ ha hb => VG.Proof.MlKem.Arm.acc_pub ha hb) fun a b hab => let ⟨f, g, h₁, h₂⟩ := hP a b hab; ⟨(f, g), h₁, h₂⟩

theorem sub_ct {P : State → State → Prop} (hP : ∀ a b, P a b → ∃ f g, VG.Proof.MlKem.Arm.AccArgs a f g ∧ VG.Proof.MlKem.Arm.AccArgs b f g) :
    RelCT isa P (.call "vg_mlkem_sub" Impl.MlKem.Arm.sub) fun _ _ => True :=
  VG.Proof.MlKem.Arm.call_ct (k := VG.Proof.MlKem.Arm.kSub) VG.Proof.MlKem.Arm.kSub_ok VG.Proof.MlKem.Arm.kSub_ct (fun (x : BitVec 32 × BitVec 32) s => VG.Proof.MlKem.Arm.AccArgs s x.1 x.2)
    (fun x => [polyRegion (State.addr x.2)]) (fun x => [polyRegion (State.addr x.1)])
    (fun _ _ h => VG.Proof.MlKem.Arm.acc_pre h) (fun _ _ h => ⟨VG.Proof.MlKem.Arm.covers_append h.cr (VG.Proof.MlKem.Arm.covers_wr h.cw), h.cw⟩)
    (fun _ _ _ ha hb => VG.Proof.MlKem.Arm.acc_pub ha hb) fun a b hab => let ⟨f, g, h₁, h₂⟩ := hP a b hab; ⟨(f, g), h₁, h₂⟩

/-! ## `vg_mlkem_multiply_ntts` -/

def kMul : Contract isa := VG.Proof.MlKem.Arm.mkK Mul.Pre
  (fun s₀ s => PolyIs s.mem (Mul.H s₀) (multiplyNTTs (Mul.fp s₀) (Mul.gp s₀))) (VG.Proof.MlKem.Arm.regsEq [.r0, .r1, .r2, .r3])

theorem kMul_ok : ∀ s, kMul.pre s → ∃ t s', Exec isa Impl.MlKem.Arm.multiplyNTTs s t s' ∧ abiPreserved s s' ∧
    kMul.post s s' :=
  VG.Proof.MlKem.Arm.mkK_ok fun _ hp => Mul.correct hp

theorem kMul_ct : ConstantTime isa kMul.pre kMul.pub Impl.MlKem.Arm.multiplyNTTs :=
  Add.ctRegs [.r0, .r1, .r2, .r3] (fun _ _ h => h) (by taint_decide)

/-- The arguments of `vg_mlkem_multiply_ntts`. -/
structure MulArgs (s : State) (h f g scr : BitVec 32) : Prop where
  r0 : s.gpr .r0 = h
  r1 : s.gpr .r1 = f
  r2 : s.gpr .r2 = g
  r3 : s.gpr .r3 = scr
  hf : (polyRegion (State.addr h)).Disjoint (polyRegion (State.addr f))
  hg : (polyRegion (State.addr h)).Disjoint (polyRegion (State.addr g))
  hs : (polyRegion (State.addr h)).Disjoint (polyRegion (State.addr scr))
  fs : (polyRegion (State.addr f)).Disjoint (polyRegion (State.addr scr))
  gs : (polyRegion (State.addr g)).Disjoint (polyRegion (State.addr scr))
  fh : h.toNat + 1024 ≤ 2 ^ 32
  ff : f.toNat + 1024 ≤ 2 ^ 32
  fg : g.toNat + 1024 ≤ 2 ^ 32
  fscr : scr.toNat + 1024 ≤ 2 ^ 32
  redF : Reduced s.mem (State.addr f)
  redG : Reduced s.mem (State.addr g)
  cw : Covers [polyRegion (State.addr h), polyRegion (State.addr scr)] s.wr
  cr : Covers [polyRegion (State.addr f), polyRegion (State.addr g)] (s.rd ++ s.wr)

abbrev mulRd (f g : BitVec 32) : List Region := [polyRegion (State.addr f), polyRegion (State.addr g)]
abbrev mulWr (h scr : BitVec 32) : List Region := [polyRegion (State.addr h), polyRegion (State.addr scr)]

theorem mul_pre {s : State} {h f g scr : BitVec 32} (a : VG.Proof.MlKem.Arm.MulArgs s h f g scr) :
    Mul.Pre (VG.Proof.MlKem.Arm.view s (VG.Proof.MlKem.Arm.mulRd f g) (VG.Proof.MlKem.Arm.mulWr h scr)) := by
  have e0 := VG.Proof.MlKem.Arm.view_gpr' s (VG.Proof.MlKem.Arm.mulRd f g) (VG.Proof.MlKem.Arm.mulWr h scr) (r := .r0) (by decide)
  have e1 := VG.Proof.MlKem.Arm.view_gpr' s (VG.Proof.MlKem.Arm.mulRd f g) (VG.Proof.MlKem.Arm.mulWr h scr) (r := .r1) (by decide)
  have e2 := VG.Proof.MlKem.Arm.view_gpr' s (VG.Proof.MlKem.Arm.mulRd f g) (VG.Proof.MlKem.Arm.mulWr h scr) (r := .r2) (by decide)
  have e3 := VG.Proof.MlKem.Arm.view_gpr' s (VG.Proof.MlKem.Arm.mulRd f g) (VG.Proof.MlKem.Arm.mulWr h scr) (r := .r3) (by decide)
  rw [a.r0] at e0; rw [a.r1] at e1; rw [a.r2] at e2; rw [a.r3] at e3
  exact ⟨by simp only [Mul.F, Mul.G, Mul.pf, Mul.pg, e1, e2]; rfl, by simp only [Mul.H, Mul.S, Mul.ph, Mul.ps, e0, e3]; rfl,
    by simp only [Mul.H, Mul.F, Mul.ph, Mul.pf, e0, e1]; exact a.hf,
    by simp only [Mul.H, Mul.G, Mul.ph, Mul.pg, e0, e2]; exact a.hg,
    by simp only [Mul.H, Mul.S, Mul.ph, Mul.ps, e0, e3]; exact a.hs,
    by simp only [Mul.F, Mul.S, Mul.pf, Mul.ps, e1, e3]; exact a.fs,
    by simp only [Mul.G, Mul.S, Mul.pg, Mul.ps, e2, e3]; exact a.gs,
    by simp only [Mul.ph, e0]; exact a.fh, by simp only [Mul.pf, e1]; exact a.ff,
    by simp only [Mul.pg, e2]; exact a.fg, by simp only [Mul.ps, e3]; exact a.fscr,
    by simp only [Mul.F, Mul.pf, e1]; exact a.redF, by simp only [Mul.G, Mul.pg, e2]; exact a.redG⟩

theorem mul_call {s : State} {h f g scr : BitVec 32} (a : VG.Proof.MlKem.Arm.MulArgs s h f g scr) {Q : State → Prop}
    (hQ : ∀ s', Kept (VG.Proof.MlKem.Arm.mulWr h scr) s s' →
      PolyIs s'.mem (State.addr h) (multiplyNTTs (polyAt s.mem (State.addr f)) (polyAt s.mem (State.addr g))) →
      Q s') :
    WP isa (.call "vg_mlkem_multiply_ntts" Impl.MlKem.Arm.multiplyNTTs) s Q :=
  VG.Proof.MlKem.Arm.call_kept (k := VG.Proof.MlKem.Arm.kMul) VG.Proof.MlKem.Arm.kMul_ok (by decide +kernel) (VG.Proof.MlKem.Arm.mul_pre a) (VG.Proof.MlKem.Arm.covers_append a.cr (VG.Proof.MlKem.Arm.covers_wr a.cw)) a.cw
    fun s' hk hp => hQ s' hk (by
      have e0 := VG.Proof.MlKem.Arm.view_gpr' s (VG.Proof.MlKem.Arm.mulRd f g) (VG.Proof.MlKem.Arm.mulWr h scr) (r := .r0) (by decide)
      have e1 := VG.Proof.MlKem.Arm.view_gpr' s (VG.Proof.MlKem.Arm.mulRd f g) (VG.Proof.MlKem.Arm.mulWr h scr) (r := .r1) (by decide)
      have e2 := VG.Proof.MlKem.Arm.view_gpr' s (VG.Proof.MlKem.Arm.mulRd f g) (VG.Proof.MlKem.Arm.mulWr h scr) (r := .r2) (by decide)
      rw [a.r0] at e0; rw [a.r1] at e1; rw [a.r2] at e2
      simpa only [VG.Proof.MlKem.Arm.kMul, VG.Proof.MlKem.Arm.mkK, Mul.H, Mul.fp, Mul.gp, Mul.F, Mul.G, Mul.ph, Mul.pf, Mul.pg, e0, e1, e2,
        State.withRegions_mem, State.callEntry_mem] using hp)

theorem regsEq_view {rs : List Reg} (hl : ∀ r ∈ rs, r ∉ linkRegs) {a b : State} (hab : ∀ r ∈ rs, a.gpr r = b.gpr r)
    (rd wr : List Region) : VG.Proof.MlKem.Arm.regsEq rs (VG.Proof.MlKem.Arm.view a rd wr) (VG.Proof.MlKem.Arm.view b rd wr) := fun r hr => by
  rw [VG.Proof.MlKem.Arm.view_gpr' _ _ _ (hl r hr), VG.Proof.MlKem.Arm.view_gpr' _ _ _ (hl r hr), hab r hr]

theorem mul_ct {P : State → State → Prop}
    (hP : ∀ a b, P a b → ∃ h f g scr, VG.Proof.MlKem.Arm.MulArgs a h f g scr ∧ VG.Proof.MlKem.Arm.MulArgs b h f g scr) :
    RelCT isa P (.call "vg_mlkem_multiply_ntts" Impl.MlKem.Arm.multiplyNTTs) fun _ _ => True :=
  VG.Proof.MlKem.Arm.call_ct (k := VG.Proof.MlKem.Arm.kMul) VG.Proof.MlKem.Arm.kMul_ok VG.Proof.MlKem.Arm.kMul_ct (fun (x : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32) s =>
      VG.Proof.MlKem.Arm.MulArgs s x.1 x.2.1 x.2.2.1 x.2.2.2)
    (fun x => VG.Proof.MlKem.Arm.mulRd x.2.1 x.2.2.1) (fun x => VG.Proof.MlKem.Arm.mulWr x.1 x.2.2.2)
    (fun _ _ h => VG.Proof.MlKem.Arm.mul_pre h) (fun _ _ h => ⟨VG.Proof.MlKem.Arm.covers_append h.cr (VG.Proof.MlKem.Arm.covers_wr h.cw), h.cw⟩)
    (fun _ _ _ ha hb => VG.Proof.MlKem.Arm.regsEq_view (by decide) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [ha.r0, hb.r0]
      · rw [ha.r1, hb.r1]
      · rw [ha.r2, hb.r2]
      · rw [ha.r3, hb.r3]) _ _)
    fun a b hab => let ⟨h, f, g, scr, h₁, h₂⟩ := hP a b hab; ⟨(h, f, g, scr), h₁, h₂⟩

end VG.Proof.MlKem.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.KemLay`. -/
section

/-!
# ML-KEM on 32-bit ARM: what the proofs need of a parameter set

The proofs of the top-level functions (`KeyGen.lean`, `Encaps.lean`,
`Decaps.lean`, …) hold for any parameter set `K : KemLay` that passes
`KemLay.wf`: a computation on the literals of `K`, which each parameter set
checks by `decide` (`kl768_wf` here, ML-KEM-1024's in `Proof/MlKem1024/Arm/`).
The proofs use it as facts (`KemLay.WF`): `1 ≤ k ≤ 4`, a `scratch` of at
least 32 KiB, `η₁ = η₂ = 2`, the
shifts of `atU`, that the buffers of decapsulation fit in `scratch`, and that
the immediates that depend on the parameters are encodable. Facts on the
offsets in `scratch` that follow from `k ≤ 4` alone, the proofs decide by
`omega` (`kdecide`, `Prf.lean`).
-/

namespace VG.Impl.MlKem.Arm

open VG VG.Arm

/-- What the proofs need of the parameters, as facts. -/
structure KemLay.WF (K : KemLay) : Prop where
  k1 : 1 ≤ K.k
  k4 : K.k ≤ 4
  scr : 32768 ≤ K.scratch
  η₁ : K.p.η₁ = 2
  η₂ : K.p.η₂ = 2
  du1 : 1 ≤ K.du
  du : K.du ≤ 11
  dv : K.dv ≤ 11
  sh : K.uShifts.all (fun t => 1 ≤ t && t ≤ 31) = true
  shSum : (K.uShifts.map (2 ^ ·)).sum = K.uLen
  ct : K.oCt + K.ctLen ≤ oCin
  cin : oCin + K.ctLen ≤ 32768
  encDu : encodable (BitVec.ofNat 32 K.du) = true
  encDv : encodable (BitVec.ofNat 32 K.dv) = true
  encU : encodable (BitVec.ofNat 32 K.uLen) = true
  encV : encodable (BitVec.ofNat 32 K.vLen) = true
  encVo : encodable (BitVec.ofNat 32 (K.uLen * K.k)) = true
  encCt : encodable (BitVec.ofNat 32 K.ctLen) = true
  encEk : encodable (BitVec.ofNat 32 K.ekLen) = true
  encT : encodable (BitVec.ofNat 32 (384 * K.k)) = true
  encH : encodable (BitVec.ofNat 32 (768 * K.k + 32)) = true
  encZ : encodable (BitVec.ofNat 32 (768 * K.k + 64)) = true

/-- `KemLay.WF` as a computation. -/
def KemLay.wf (K : KemLay) : Bool :=
  decide (1 ≤ K.k) && (decide (K.k ≤ 4) && (decide (32768 ≤ K.scratch) && (decide (K.p.η₁ = 2) && (decide (K.p.η₂ = 2) &&
  (decide (1 ≤ K.du) && (decide (K.du ≤ 11) && (decide (K.dv ≤ 11) && (K.uShifts.all (fun t => 1 ≤ t && t ≤ 31) &&
  (decide ((K.uShifts.map (2 ^ ·)).sum = K.uLen) && (decide (K.oCt + K.ctLen ≤ oCin) &&
  (decide (oCin + K.ctLen ≤ 32768) && (encodable (BitVec.ofNat 32 K.du) && (encodable (BitVec.ofNat 32 K.dv) &&
  (encodable (BitVec.ofNat 32 K.uLen) && (encodable (BitVec.ofNat 32 K.vLen) &&
  (encodable (BitVec.ofNat 32 (K.uLen * K.k)) && (encodable (BitVec.ofNat 32 K.ctLen) &&
  (encodable (BitVec.ofNat 32 K.ekLen) && (encodable (BitVec.ofNat 32 (384 * K.k)) &&
  (encodable (BitVec.ofNat 32 (768 * K.k + 32)) && encodable (BitVec.ofNat 32 (768 * K.k + 64))))))))))))))))))))))

theorem KemLay.WF.of {K : KemLay} (h : K.wf = true) : K.WF := by
  simp only [KemLay.wf, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22⟩

end VG.Impl.MlKem.Arm

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm

theorem kl768_wf : kl768.WF := .of (by decide)

/-- The parameter set of ML-KEM-768 with `k` changed: what a fact that depends
on a parameter set only through `k` says of any of them is what it says of
`kOf k`, which `decide` checks for every `k ≤ 4` at once (`KemLay.WF.k4`). -/
def kOf (k : Nat) : KemLay := { kl768 with p := { kl768.p with k := k } }

/-- The polynomials of `scratch` have encodable offsets. -/
theorem enc_poly : ∀ j < 21, encodable (BitVec.ofNat 32 (oPoly j)) = true := by decide

theorem _root_.VG.Impl.MlKem.Arm.KemLay.WF.enc {K : KemLay} (hK : K.WF) {j : Nat} (hj : j ≤ 3 * K.k + 8) :
    encodable (BitVec.ofNat 32 (oPoly j)) = true :=
  VG.Proof.MlKem.Arm.enc_poly j (by have := hK.k4; omega)

theorem _root_.VG.Impl.MlKem.Arm.KemLay.WF.ct_pos {K : KemLay} (hK : K.WF) : 0 < K.ctLen := by
  have h1 : 0 < K.uLen := by simp only [KemLay.uLen]; have := hK.du1; omega
  have h2 : K.uLen ≤ K.uLen * K.k := Nat.le_mul_of_pos_right _ hK.k1
  simp only [KemLay.ctLen]; omega

end VG.Proof.MlKem.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.Lay`. -/
section

/-!
# ML-KEM on 32-bit ARM: the buffers of the top-level functions

The top-level functions work on a few buffers (`Lay`): `scratch` (buffer 0),
the 8 bytes below the stack pointer (buffer 1), and their arguments; the
contracts make them pairwise disjoint (`Lay.Ok`). A region is `l` bytes at
offset `o` of buffer `i` (`Lay.R`), and two regions are disjoint when a
computation on the offsets says so (`sepB`, decided by the kernel), so what a
call writes and what the proofs keep track of are lists of triples `(i, o,
l)`.

A state `s` in which the functions run their parts is `Ctx`: `r7` points to
`scratch`, and the stack pointer is the one of buffer 1. `Kept rs s s'`
(`Keccak.lean`) says what a part changes.
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem

/-- Buffers: their pointers and sizes. -/
structure Lay where
  ptr : Nat → BitVec 32
  sizes : List Nat

/-- Whether the regions `a` and `b` (buffer, offset, length) are within
their buffers and apart. -/
def sepB (sz : List Nat) (a b : Nat × Nat × Nat) : Bool :=
  a.1 < sz.length && b.1 < sz.length && a.2.1 + a.2.2 ≤ sz.getD a.1 0 && b.2.1 + b.2.2 ≤ sz.getD b.1 0 &&
    (a.1 != b.1 || a.2.1 + a.2.2 ≤ b.2.1 || b.2.1 + b.2.2 ≤ a.2.1)

/-- `a` is apart from every region of `W`. -/
def sepAll (sz : List Nat) (a : Nat × Nat × Nat) (W : List (Nat × Nat × Nat)) : Bool := W.all (VG.Proof.MlKem.Arm.sepB sz a)

namespace Lay

variable (L : VG.Proof.MlKem.Arm.Lay)

abbrev size (i : Nat) : Nat := L.sizes.getD i 0

/-- `l` bytes at offset `o` of buffer `i`. -/
abbrev R (i o l : Nat) : Region := ⟨State.addr (L.ptr i) + BitVec.ofNat 64 o, l⟩

/-- The regions of the triples `W`. -/
abbrev RL (W : List (Nat × Nat × Nat)) : List Region := W.map fun w => L.R w.1 w.2.1 w.2.2

/-- The buffers fit in the address space and are pairwise disjoint. -/
structure Ok : Prop where
  fit : ∀ i < L.sizes.length, (L.ptr i).toNat + L.size i ≤ 2 ^ 32
  disj : ∀ i < L.sizes.length, ∀ j < L.sizes.length, i ≠ j →
    (⟨State.addr (L.ptr i), L.size i⟩ : Region).Disjoint ⟨State.addr (L.ptr j), L.size j⟩

variable {L}

theorem R_sub {i o l : Nat} (h : o + l ≤ L.size i) :
    Region.Sub (L.R i o l) ⟨State.addr (L.ptr i), L.size i⟩ := by
  intro a ha
  simp only [Region.Contains] at ha ⊢
  bv_omega

theorem disj (hL : L.Ok) {i o l j o' l' : Nat} (h : VG.Proof.MlKem.Arm.sepB L.sizes (i, o, l) (j, o', l') = true) :
    (L.R i o l).Disjoint (L.R j o' l') := by
  simp only [VG.Proof.MlKem.Arm.sepB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨ha, hb⟩, hla⟩, hlb⟩, hs⟩ := h
  by_cases e : i = j
  · subst e
    have hf : (L.ptr i).toNat + L.sizes.getD i 0 ≤ 2 ^ 32 := hL.fit i ha
    have hs' : o + l ≤ o' ∨ o' + l' ≤ o := by
      rcases hs with (hs | hs) | hs
      · exact absurd rfl hs
      · exact .inl hs
      · exact .inr hs
    exact region_disj_off hs' hla hlb (addr_fit _ (by omega))
  · exact ((hL.disj _ ha _ hb e).sub_left (VG.Proof.MlKem.Arm.Lay.R_sub hla)).sub_right (VG.Proof.MlKem.Arm.Lay.R_sub hlb)

theorem disjAll (hL : L.Ok) {i o l : Nat} {W : List (Nat × Nat × Nat)} (h : VG.Proof.MlKem.Arm.sepAll L.sizes (i, o, l) W = true) :
    ∀ r ∈ L.RL W, (L.R i o l).Disjoint r := by
  intro r hr
  obtain ⟨⟨j, o', l'⟩, hw, rfl⟩ := List.mem_map.mp hr
  exact VG.Proof.MlKem.Arm.Lay.disj hL (List.all_eq_true.mp h _ hw)

/-- The address of a pointer into a buffer. -/
theorem addr_off (hL : L.Ok) {i o : Nat} (hi : i < L.sizes.length) (ho : o < L.size i) :
    State.addr (L.ptr i + BitVec.ofNat 32 o) = State.addr (L.ptr i) + BitVec.ofNat 64 o :=
  addr_add (by have := hL.fit i hi; omega)

theorem regA_off (hL : L.Ok) {i o l : Nat} (hi : i < L.sizes.length) (ho : o < L.size i) :
    VG.Proof.MlKem.Arm.regA (L.ptr i + BitVec.ofNat 32 o) l = L.R i o l := by
  simp only [VG.Proof.MlKem.Arm.regA, VG.Proof.MlKem.Arm.Lay.addr_off hL hi ho]

theorem regA_zero (i l : Nat) : VG.Proof.MlKem.Arm.regA (L.ptr i) l = L.R i 0 l := by
  simp only [VG.Proof.MlKem.Arm.regA, Lay.R, add_ofNat_zero]

theorem fit_off (hL : L.Ok) {i o l : Nat} (hi : i < L.sizes.length) (h : o + l ≤ L.size i) (hl : 0 < l) :
    (L.ptr i + BitVec.ofNat 32 o).toNat + l ≤ 2 ^ 32 := by
  have := hL.fit i hi
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- A part of a buffer the state may access. -/
theorem covers {i o l : Nat} {ws : List Region} (hin : ⟨State.addr (L.ptr i), L.size i⟩ ∈ ws)
    (h : o + l ≤ L.size i) : Covers [L.R i o l] ws := by
  intro x n ⟨q, hq, hc⟩
  rw [List.mem_singleton] at hq; subst hq
  refine ⟨_, hin, ?_⟩
  simp only [Region.Contains] at hc ⊢
  bv_omega

theorem polyIs_keep (hL : L.Ok) {W : List (Nat × Nat × Nat)} {m m' : Mem} (hf : Frame (L.RL W) m m')
    {i o : Nat} (h : VG.Proof.MlKem.Arm.sepAll L.sizes (i, o, 1024) W = true) {f : VG.Spec.MlKem.Poly}
    (hp : PolyIs m (State.addr (L.ptr i) + BitVec.ofNat 64 o) f) :
    PolyIs m' (State.addr (L.ptr i) + BitVec.ofNat 64 o) f :=
  polyIs_frame hf (VG.Proof.MlKem.Arm.Lay.disjAll hL h) hp

theorem bytes_keep (hL : L.Ok) {W : List (Nat × Nat × Nat)} {m m' : Mem} (hf : Frame (L.RL W) m m')
    {i o l : Nat} (h : VG.Proof.MlKem.Arm.sepAll L.sizes (i, o, l) W = true) (hl : l ≤ 2 ^ 64) :
    Spec.Sha3.bytesAt m' (State.addr (L.ptr i) + BitVec.ofNat 64 o) l =
      Spec.Sha3.bytesAt m (State.addr (L.ptr i) + BitVec.ofNat 64 o) l :=
  bytesAt_frame hf (VG.Proof.MlKem.Arm.Lay.disjAll hL h) hl

theorem word_keep (hL : L.Ok) {W : List (Nat × Nat × Nat)} {m m' : Mem} (hf : Frame (L.RL W) m m')
    {i o : Nat} (h : VG.Proof.MlKem.Arm.sepAll L.sizes (i, o, 4) W = true) :
    m'.readW (State.addr (L.ptr i) + BitVec.ofNat 64 o) 32 = m.readW (State.addr (L.ptr i) + BitVec.ofNat 64 o) 32 :=
  hf.readW (Region.contains_self _ _) (VG.Proof.MlKem.Arm.Lay.disjAll hL h) (by decide)

/-- `Ok` from the disjointness of the buffers `i < j`. -/
theorem ok_of (hfit : ∀ i < L.sizes.length, (L.ptr i).toNat + L.size i ≤ 2 ^ 32)
    (hd : ∀ i < L.sizes.length, ∀ j < L.sizes.length, i < j →
      (⟨State.addr (L.ptr i), L.size i⟩ : Region).Disjoint ⟨State.addr (L.ptr j), L.size j⟩) : L.Ok := by
  refine ⟨hfit, fun i hi j hj hij => ?_⟩
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact hd i hi j hj h
  · exact (hd j hj i hi h).symm

end Lay

/-! ## What changes -/

theorem Kept.refl (rs : List Region) (s : State) : Kept rs s s :=
  ⟨fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem Kept.trans {rs : List Region} {s₁ s₂ s₃ : State} (h₁ : Kept rs s₁ s₂) (h₂ : Kept rs s₂ s₃) :
    Kept rs s₁ s₃ :=
  ⟨fun r hr h => by rw [h₂.cs r hr h, h₁.cs r hr h], by rw [h₂.sp, h₁.sp], by rw [h₂.rd, h₁.rd],
    by rw [h₂.wr, h₁.wr], h₁.frame.trans h₂.frame⟩

theorem Kept.mono {rs rs' : List Region} {s s' : State} (h : Kept rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    Kept rs' s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, h.frame.mono hs⟩

/-- The same, for regions given by triples. -/
theorem Kept.monoL {L : VG.Proof.MlKem.Arm.Lay} {W W' : List (Nat × Nat × Nat)} {s s' : State} (h : Kept (L.RL W) s s')
    (hs : ∀ w ∈ W, w ∈ W') : Kept (L.RL W') s s' :=
  h.mono fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact List.mem_map.mpr ⟨w, hs w hw, rfl⟩

/-- A state that differs only in registers other than the callee-saved ones. -/
structure Only (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Only.kept {s s' : State} (h : VG.Proof.MlKem.Arm.Only s s') (rs : List Region) : Kept rs s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, by rw [h.mem]; exact Frame.refl _ _⟩

theorem Only.trans {s₁ s₂ s₃ : State} (h₁ : VG.Proof.MlKem.Arm.Only s₁ s₂) (h₂ : VG.Proof.MlKem.Arm.Only s₂ s₃) : VG.Proof.MlKem.Arm.Only s₁ s₃ :=
  ⟨fun r hr h => by rw [h₂.cs r hr h, h₁.cs r hr h], by rw [h₂.mem, h₁.mem], by rw [h₂.rd, h₁.rd],
    by rw [h₂.wr, h₁.wr], by rw [h₂.sp, h₁.sp]⟩

theorem Kept.only {rs : List Region} {s₁ s₂ s₃ : State} (h₁ : Kept rs s₁ s₂) (h₂ : VG.Proof.MlKem.Arm.Only s₂ s₃) :
    Kept rs s₁ s₃ := h₁.trans (h₂.kept rs)

theorem Only.of_gpr {s : State} (g : Reg → BitVec 32) (h : ∀ r ∈ preserved, r ≠ .lr → g r = s.gpr r) :
    VG.Proof.MlKem.Arm.Only s { s with
                    gpr := g } :=
  ⟨h, rfl, rfl, rfl, rfl⟩

/-! ## The setting of the parts -/

/-- `s` runs a part of a top-level function: `scratch` (buffer 0, writable,
of which the parts use the first 32768 bytes) in `r7`, and the 8 bytes
below the stack pointer (buffer 1). -/
structure Ctx (L : VG.Proof.MlKem.Arm.Lay) (s : State) : Prop where
  ok : L.Ok
  sz0 : 32768 ≤ L.size 0
  sz1 : L.size 1 = 8
  len : 2 ≤ L.sizes.length
  r7 : s.gpr .r7 = L.ptr 0
  sp8 : 8 ≤ s.sp.toNat
  sp : L.ptr 1 = s.sp - BitVec.ofNat 32 8
  cw : (⟨State.addr (L.ptr 0), L.size 0⟩ : Region) ∈ s.wr

theorem Ctx.bel {L : VG.Proof.MlKem.Arm.Lay} {s : State} (h : VG.Proof.MlKem.Arm.Ctx L s) : below s 8 = L.R 1 0 8 := by
  simp only [Lay.R, h.sp, addr_sub h.sp8, add_ofNat_zero]

theorem Ctx.kept {L : VG.Proof.MlKem.Arm.Lay} {s s' : State} (h : VG.Proof.MlKem.Arm.Ctx L s) {rs : List Region} (hk : Kept rs s s') : VG.Proof.MlKem.Arm.Ctx L s' :=
  ⟨h.ok, h.sz0, h.sz1, h.len, by rw [hk.cs .r7 (by decide) (by decide), h.r7], by rw [hk.sp]; exact h.sp8,
    by rw [hk.sp]; exact h.sp, by rw [hk.wr]; exact h.cw⟩

theorem Ctx.only {L : VG.Proof.MlKem.Arm.Lay} {s s' : State} (h : VG.Proof.MlKem.Arm.Ctx L s) (hk : VG.Proof.MlKem.Arm.Only s s') : VG.Proof.MlKem.Arm.Ctx L s' := h.kept (hk.kept [])

/-- A part of `scratch` the state may write. -/
theorem Ctx.cs {L : VG.Proof.MlKem.Arm.Lay} {s : State} (h : VG.Proof.MlKem.Arm.Ctx L s) {o l : Nat} (hl : o + l ≤ 32768) :
    Covers [L.R 0 o l] s.wr := Lay.covers h.cw (Nat.le_trans hl h.sz0)

theorem Ctx.addr {L : VG.Proof.MlKem.Arm.Lay} {s : State} (h : VG.Proof.MlKem.Arm.Ctx L s) {o : Nat} (ho : o < 32768) :
    State.addr (L.ptr 0 + BitVec.ofNat 32 o) = State.addr (L.ptr 0) + BitVec.ofNat 64 o :=
  Lay.addr_off h.ok (by have := h.len; omega) (Nat.lt_of_lt_of_le ho h.sz0)

theorem Ctx.regAo {L : VG.Proof.MlKem.Arm.Lay} {s : State} (h : VG.Proof.MlKem.Arm.Ctx L s) {o : Nat} (ho : o < 32768) (l : Nat) :
    VG.Proof.MlKem.Arm.regA (L.ptr 0 + BitVec.ofNat 32 o) l = L.R 0 o l :=
  Lay.regA_off h.ok (by have := h.len; omega) (Nat.lt_of_lt_of_le ho h.sz0)

theorem Ctx.fit {L : VG.Proof.MlKem.Arm.Lay} {s : State} (h : VG.Proof.MlKem.Arm.Ctx L s) : (L.ptr 0).toNat + 32768 ≤ 2 ^ 32 := by
  have := h.ok.fit 0 (by have := h.len; omega); have := h.sz0; omega

theorem Ctx.fitO {L : VG.Proof.MlKem.Arm.Lay} {s : State} (h : VG.Proof.MlKem.Arm.Ctx L s) {o l : Nat} (hl : o + l ≤ 32768) (hl0 : 0 < l) :
    (L.ptr 0 + BitVec.ofNat 32 o).toNat + l ≤ 2 ^ 32 :=
  Lay.fit_off h.ok (by have := h.len; omega) (Nat.le_trans hl h.sz0) hl0

theorem Ctx.disj {L : VG.Proof.MlKem.Arm.Lay} {s : State} (h : VG.Proof.MlKem.Arm.Ctx L s) {a b : Nat × Nat × Nat} (hs : VG.Proof.MlKem.Arm.sepB L.sizes a b = true) :
    (L.R a.1 a.2.1 a.2.2).Disjoint (L.R b.1 b.2.1 b.2.2) := Lay.disj h.ok hs

end VG.Proof.MlKem.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.HashTop`. -/
section

/-!
# ML-KEM-768 on 32-bit ARM: the hash routine

`hash` (`Impl/MlKem/Arm/Top.lean`) computes the sponge of the concatenation of
its input pieces, and writes consecutive output to its output pieces
(`hash_ok`): from the all-zero state (`repr_nil`), each `absorb` continues the
message from the position the previous one returned, the padding, and each
`squeeze` continues the output. It changes only the Keccak state and working
space, the outputs, the 8 bytes below the stack pointer, and registers that
are not callee-saved (or `lr`).
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.Sha3 (Repr stateAt bytesAt absorb pad squeezeFrom rates)

theorem pres_ne {r : Reg} (h : r ∈ preserved) (hl : r ≠ .lr) :
    r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
  revert r; decide

theorem enc200 : encodable (BitVec.ofNat 32 200) = true := by decide
theorem enc0 : encodable (BitVec.ofNat 32 0) = true := by decide

/-- The arguments of an `absorb` or a `squeeze`. -/
theorem kargs_ok {s : State} {rate : Nat} (first : Bool) {p : Piece} (hb : p.base ∈ preserved ∧ p.base ≠ .lr)
    (hre : encodable (BitVec.ofNat 32 rate) = true) (hoe : encodable (BitVec.ofNat 32 p.off) = true)
    (hle : encodable (BitVec.ofNat 32 p.len) = true) :
    WP isa (.block (keccakArgs rate first ++ pieceArgs p)) s fun s' => VG.Proof.MlKem.Arm.Only s s' ∧
      s'.gpr .r0 = s.gpr .r7 ∧ s'.gpr .r1 = BitVec.ofNat 32 rate ∧
      s'.gpr .r2 = (if first then BitVec.ofNat 32 0 else s.gpr .r0) ∧
      s'.gpr .r3 = s.gpr p.base + BitVec.ofNat 32 p.off ∧ s'.gpr .r12 = BitVec.ofNat 32 p.len ∧
      s'.gpr .lr = s.gpr .r7 + BitVec.ofNat 32 200 := by
  obtain ⟨n0, n1, n2, n3, n12⟩ := VG.Proof.MlKem.Arm.pres_ne hb.1 hb.2
  have nl := hb.2
  cases first <;>
  · run_block [keccakArgs, pieceArgs, ptrTo, hre, hoe, hle, VG.Proof.MlKem.Arm.enc200, VG.Proof.MlKem.Arm.enc0, n0, n1, n2, n3, n12, nl]
    refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
    obtain ⟨m0, m1, m2, m3, m12⟩ := VG.Proof.MlKem.Arm.pres_ne hr hl
    simp only [m0, m1, m2, m3, m12, hl, ite_false]

/-- The arguments of a `pad`. -/
theorem pargs_ok {s : State} {rate sfx : Nat} (hre : encodable (BitVec.ofNat 32 rate) = true)
    (hse : encodable (BitVec.ofNat 32 sfx) = true) :
    WP isa (.block (keccakArgs rate false ++ ([.mov .r3 (.imm (BitVec.ofNat 32 sfx))] : List Instr))) s
      fun s' => VG.Proof.MlKem.Arm.Only s s' ∧ s'.gpr .r0 = s.gpr .r7 ∧ s'.gpr .r1 = BitVec.ofNat 32 rate ∧
        s'.gpr .r2 = s.gpr .r0 ∧ s'.gpr .r3 = BitVec.ofNat 32 sfx ∧ s'.gpr .lr = s.gpr .r7 + BitVec.ofNat 32 200 := by
  run_block [keccakArgs, ptrTo, hre, hse, VG.Proof.MlKem.Arm.enc200]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, m2, m3, m12⟩ := VG.Proof.MlKem.Arm.pres_ne hr hl
  simp only [m0, m1, m2, m3, hl, ite_false]

/-! ## Regions in `scratch` and below the stack pointer -/

theorem Ctx.sep00 {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hc : VG.Proof.MlKem.Arm.Ctx L s) {o l o' l' : Nat} (h₁ : o + l ≤ 32768)
    (h₂ : o' + l' ≤ 32768) (h : o + l ≤ o' ∨ o' + l' ≤ o) : VG.Proof.MlKem.Arm.sepB L.sizes (0, o, l) (0, o', l') = true := by
  have := hc.len; have := hc.sz0
  simp only [VG.Proof.MlKem.Arm.sepB, Lay.size] at this ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_true_eq_false,
    false_or]
  omega

theorem Ctx.sep01 {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hc : VG.Proof.MlKem.Arm.Ctx L s) {o l o' l' : Nat} (h₁ : o + l ≤ 32768)
    (h₂ : o' + l' ≤ 8) : VG.Proof.MlKem.Arm.sepB L.sizes (0, o, l) (1, o', l') = true := by
  have h0 := hc.len; have h1 := hc.sz0; have h2 := hc.sz1
  simp only [Lay.size] at h1 h2
  simp only [VG.Proof.MlKem.Arm.sepB, h2, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  omega

theorem sepB_symm {sz : List Nat} {a b : Nat × Nat × Nat} (h : VG.Proof.MlKem.Arm.sepB sz a b = true) : VG.Proof.MlKem.Arm.sepB sz b a = true := by
  simp only [VG.Proof.MlKem.Arm.sepB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h ⊢
  omega

/-- The regions of the sponge functions: the state, the working space and the stack arguments. -/
abbrev kRegs : List (Nat × Nat × Nat) := [(0, 0, 200), (0, 200, 640), (1, 0, 8)]

theorem Ctx.kregs {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hc : VG.Proof.MlKem.Arm.Ctx L s) :
    VG.Proof.MlKem.Arm.regA (L.ptr 0) 200 = L.R 0 0 200 ∧ VG.Proof.MlKem.Arm.regA (L.ptr 0 + BitVec.ofNat 32 200) 640 = L.R 0 200 640 ∧
      below s 8 = L.R 1 0 8 :=
  ⟨Lay.regA_zero _ _, hc.regAo (by decide) _, hc.bel⟩

/-! ## Pieces -/

/-- Piece `p` is the region `L.R (idx p.base) p.off p.len`, which the state
may read (or write, if `w`), apart from the sponge's regions. -/
structure PieceOk (L : VG.Proof.MlKem.Arm.Lay) (idx : Reg → Nat) (s : State) (w : Bool) (p : Piece) : Prop where
  base : p.base ∈ preserved ∧ p.base ≠ .lr
  ptr : s.gpr p.base = L.ptr (idx p.base)
  oenc : encodable (BitVec.ofNat 32 p.off) = true
  lenc : encodable (BitVec.ofNat 32 p.len) = true
  pos : 0 < p.len
  lt : p.off + p.len < 2 ^ 32
  sep : VG.Proof.MlKem.Arm.sepAll L.sizes (idx p.base, p.off, p.len) VG.Proof.MlKem.Arm.kRegs = true
  cov : (⟨State.addr (L.ptr (idx p.base)), L.size (idx p.base)⟩ : Region) ∈ (if w then s.wr else s.rd ++ s.wr)

/-- The region of a piece. -/
abbrev Lay.P (L : VG.Proof.MlKem.Arm.Lay) (idx : Reg → Nat) (p : Piece) : Region := L.R (idx p.base) p.off p.len

/-- The bytes of a piece. -/
abbrev Lay.pb (L : VG.Proof.MlKem.Arm.Lay) (idx : Reg → Nat) (m : Mem) (p : Piece) : List Byte :=
  bytesAt m (State.addr (L.ptr (idx p.base)) + BitVec.ofNat 64 p.off) p.len

theorem sepAll_head {sz : List Nat} {a w : Nat × Nat × Nat} {W : List (Nat × Nat × Nat)}
    (h : VG.Proof.MlKem.Arm.sepAll sz a (w :: W) = true) : VG.Proof.MlKem.Arm.sepB sz a w = true := by
  simp only [VG.Proof.MlKem.Arm.sepAll, List.all_cons, Bool.and_eq_true] at h; exact h.1

theorem sepB_bounds {sz : List Nat} {i o l : Nat} {w : Nat × Nat × Nat} (h : VG.Proof.MlKem.Arm.sepB sz (i, o, l) w = true) :
    i < sz.length ∧ o + l ≤ sz.getD i 0 := by
  simp only [VG.Proof.MlKem.Arm.sepB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.2⟩

theorem PieceOk.bounds {L : VG.Proof.MlKem.Arm.Lay} {idx : Reg → Nat} {s : State} {w : Bool} {p : Piece} (h : VG.Proof.MlKem.Arm.PieceOk L idx s w p) :
    idx p.base < L.sizes.length ∧ p.off + p.len ≤ L.size (idx p.base) :=
  VG.Proof.MlKem.Arm.sepB_bounds (VG.Proof.MlKem.Arm.sepAll_head h.sep)

theorem PieceOk.sepK {L : VG.Proof.MlKem.Arm.Lay} {idx : Reg → Nat} {s : State} {w : Bool} {p : Piece} (h : VG.Proof.MlKem.Arm.PieceOk L idx s w p) :
    VG.Proof.MlKem.Arm.sepB L.sizes (idx p.base, p.off, p.len) (0, 0, 200) = true ∧
      VG.Proof.MlKem.Arm.sepB L.sizes (idx p.base, p.off, p.len) (0, 200, 640) = true ∧
      VG.Proof.MlKem.Arm.sepB L.sizes (idx p.base, p.off, p.len) (1, 0, 8) = true := by
  have := h.sep
  simp only [VG.Proof.MlKem.Arm.sepAll, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true] at this
  exact ⟨this.1, this.2.1, this.2.2⟩

theorem PieceOk.regA {L : VG.Proof.MlKem.Arm.Lay} {idx : Reg → Nat} {s : State} {w : Bool} {p : Piece} (hL : L.Ok)
    (h : VG.Proof.MlKem.Arm.PieceOk L idx s w p) : VG.Proof.MlKem.Arm.regA (L.ptr (idx p.base) + BitVec.ofNat 32 p.off) p.len = L.P idx p :=
  Lay.regA_off hL h.bounds.1 (by have := h.bounds.2; have := h.pos; omega)

theorem RL_kRegs (L : VG.Proof.MlKem.Arm.Lay) : L.RL VG.Proof.MlKem.Arm.kRegs = [L.R 0 0 200, L.R 0 200 640, L.R 1 0 8] := rfl

/-- The position the next call starts from: 0 first, or the one the last
call returned. -/
def Pos (first : Bool) (s : State) : Nat := if first then 0 else (s.gpr .r0).toNat

theorem pos_r2 (first : Bool) (s : State) :
    (if first then BitVec.ofNat 32 0 else s.gpr .r0) = BitVec.ofNat 32 (VG.Proof.MlKem.Arm.Pos first s) := by
  cases first
  · simp only [VG.Proof.MlKem.Arm.Pos, Bool.false_eq_true, ite_false, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rfl

theorem rate_pos {rate : Nat} (h : rate ∈ rates) : 0 < rate := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega

/-- The registers and permissions of `s₀`. -/
structure Rg (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cs : ∀ r ∈ preserved, r ≠ .lr → s.gpr r = s₀.gpr r

theorem Kept.rg {rs : List Region} {s₀ s : State} (h : Kept rs s₀ s) : VG.Proof.MlKem.Arm.Rg s₀ s := ⟨h.rd, h.wr, h.sp, h.cs⟩

theorem Rg.kept {rs : List Region} {s₀ s s' : State} (h : VG.Proof.MlKem.Arm.Rg s₀ s) (hk : Kept rs s s') : VG.Proof.MlKem.Arm.Rg s₀ s' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp],
    fun r hr hl => by rw [hk.cs r hr hl, h.cs r hr hl]⟩

theorem Rg.ctx {L : VG.Proof.MlKem.Arm.Lay} {s₀ s : State} (hc : VG.Proof.MlKem.Arm.Ctx L s₀) (h : VG.Proof.MlKem.Arm.Rg s₀ s) : VG.Proof.MlKem.Arm.Ctx L s :=
  ⟨hc.ok, hc.sz0, hc.sz1, hc.len, by rw [h.cs .r7 (by decide) (by decide), hc.r7], by rw [h.sp]; exact hc.sp8,
    by rw [h.sp]; exact hc.sp, by rw [h.wr]; exact hc.cw⟩

theorem PieceOk.covR {L : VG.Proof.MlKem.Arm.Lay} {idx : Reg → Nat} {s₀ s : State} {p : Piece} (h : VG.Proof.MlKem.Arm.PieceOk L idx s₀ false p)
    (hg : VG.Proof.MlKem.Arm.Rg s₀ s) : Covers [L.P idx p] (s.rd ++ s.wr) := by
  have := h.cov
  simp only [Bool.false_eq_true, ite_false] at this
  rw [hg.rd, hg.wr]
  exact Lay.covers this h.bounds.2

theorem PieceOk.covW {L : VG.Proof.MlKem.Arm.Lay} {idx : Reg → Nat} {s₀ s : State} {p : Piece} (h : VG.Proof.MlKem.Arm.PieceOk L idx s₀ true p)
    (hg : VG.Proof.MlKem.Arm.Rg s₀ s) : Covers [L.P idx p] s.wr := by
  have := h.cov
  simp only [ite_true] at this
  rw [hg.wr]
  exact Lay.covers this h.bounds.2

theorem PieceOk.fit {L : VG.Proof.MlKem.Arm.Lay} {idx : Reg → Nat} {s : State} {w : Bool} {p : Piece} (hL : L.Ok)
    (h : VG.Proof.MlKem.Arm.PieceOk L idx s w p) : (L.ptr (idx p.base) + BitVec.ofNat 32 p.off).toNat + p.len ≤ 2 ^ 32 :=
  Lay.fit_off hL h.bounds.1 h.bounds.2 h.pos

theorem PieceOk.len32 {L : VG.Proof.MlKem.Arm.Lay} {idx : Reg → Nat} {s : State} {w : Bool} {p : Piece} (h : VG.Proof.MlKem.Arm.PieceOk L idx s w p)
    (_hL : L.Ok) : p.len < 2 ^ 32 := by
  have := h.lt; omega

theorem PieceOk.addr {L : VG.Proof.MlKem.Arm.Lay} {idx : Reg → Nat} {s : State} {w : Bool} {p : Piece} (hL : L.Ok)
    (h : VG.Proof.MlKem.Arm.PieceOk L idx s w p) :
    State.addr (L.ptr (idx p.base) + BitVec.ofNat 32 p.off) = State.addr (L.ptr (idx p.base)) + BitVec.ofNat 64 p.off :=
  Lay.addr_off hL h.bounds.1 (by have := h.bounds.2; have := h.pos; omega)

theorem covers_kregs {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hc : VG.Proof.MlKem.Arm.Ctx L s) :
    Covers [VG.Proof.MlKem.Arm.regA (L.ptr 0) 200, VG.Proof.MlKem.Arm.regA (L.ptr 0 + BitVec.ofNat 32 200) 640] s.wr := by
  rw [hc.kregs.1, hc.kregs.2.1]
  exact VG.Proof.MlKem.Arm.covers_cons' (hc.cs (by decide)) (VG.Proof.MlKem.Arm.covers_cons' (hc.cs (by decide)) VG.Proof.MlKem.Arm.covers_nil')

/-! ## The absorbs -/

theorem absorbs_ok {L : VG.Proof.MlKem.Arm.Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates)
    (hre : encodable (BitVec.ofNat 32 rate) = true) {s₀ : State} (hc : VG.Proof.MlKem.Arm.Ctx L s₀) :
    ∀ (ps : List Piece) (first : Bool) (s : State) (msg : List Byte),
      (∀ p ∈ ps, VG.Proof.MlKem.Arm.PieceOk L idx s₀ false p) →
      Kept (L.RL VG.Proof.MlKem.Arm.kRegs) s₀ s → Repr s.mem (State.addr (L.ptr 0)) rate msg →
      VG.Proof.MlKem.Arm.Pos first s = msg.length % rate →
      WP isa (absorbs rate first ps) s fun s' =>
        Kept (L.RL VG.Proof.MlKem.Arm.kRegs) s₀ s' ∧
        Repr s'.mem (State.addr (L.ptr 0)) rate (msg ++ (ps.map (L.pb idx s₀.mem)).flatten) ∧
        VG.Proof.MlKem.Arm.Pos (first && ps.isEmpty) s' = (msg ++ (ps.map (L.pb idx s₀.mem)).flatten).length % rate := by
  intro ps
  induction ps with
  | nil => exact fun first s msg _ hk hr hpos => WP.block_nil ⟨hk, by simpa using hr, by simpa using hpos⟩
  | cons p ps ih =>
    intro first s msg hps hk hr hpos
    have hp := hps p (List.mem_cons_self ..)
    have hL := hc.ok
    have rpos := VG.Proof.MlKem.Arm.rate_pos hrate
    have hcs := hk.rg.ctx hc
    refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.kargs_ok first hp.base hre hp.oenc hp.lenc) fun s₁ ⟨o₁, g0, g1, g2, g3, g12, glr⟩ => ?_)
    have hc₁ := hcs.only o₁
    have gb : s.gpr p.base = L.ptr (idx p.base) := by rw [hk.cs _ hp.base.1 hp.base.2, hp.ptr]
    rw [hcs.r7] at g0 glr
    rw [gb] at g3
    rw [VG.Proof.MlKem.Arm.pos_r2] at g2
    have hpos' : VG.Proof.MlKem.Arm.Pos first s < rate := by rw [hpos]; exact Nat.mod_lt _ rpos
    obtain ⟨e0, e1, e2⟩ := hc₁.kregs
    have er := hp.regA hL
    have hg₁ : VG.Proof.MlKem.Arm.Rg s₀ s₁ := hk.rg.kept (o₁.kept [])
    have hA : AbsorbArgs s₁ (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) (L.ptr (idx p.base) + BitVec.ofNat 32 p.off)
        rate (VG.Proof.MlKem.Arm.Pos first s) p.len := by
      refine ⟨g0, g1, g2, g3, g12, glr, hrate, hpos', hp.len32 hL, hc₁.sp8, fit_le (by decide) hc.fit,
        hp.fit hL, hc.fitO (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, VG.Proof.MlKem.Arm.covers_kregs hc₁, ?_⟩
      · rw [e0, e1]; exact Lay.disj hL (hc.sep00 (by decide) (by decide) (by decide))
      · rw [er, e0]; exact Lay.disj hL hp.sepK.1
      · rw [er, e1]; exact Lay.disj hL hp.sepK.2.1
      · rw [e2, e0]; exact Lay.disj hL (VG.Proof.MlKem.Arm.sepB_symm (hc.sep01 (by decide) (by decide)))
      · rw [e2, e1]; exact Lay.disj hL (VG.Proof.MlKem.Arm.sepB_symm (hc.sep01 (by decide) (by decide)))
      · rw [e2, er]; exact Lay.disj hL (VG.Proof.MlKem.Arm.sepB_symm hp.sepK.2.2)
      · rw [er]; exact hp.covR hg₁
    refine WP.seq (absorb_ok hA fun s₂ k₂ r₂ ret₂ => ?_)
    rw [e0, e1, e2, ← VG.Proof.MlKem.Arm.RL_kRegs] at k₂
    have hk₂ : Kept (L.RL VG.Proof.MlKem.Arm.kRegs) s₀ s₂ := hk.trans ((o₁.kept _).trans k₂)
    have eb : bytesAt s₁.mem (State.addr (L.ptr (idx p.base) + BitVec.ofNat 32 p.off)) p.len = L.pb idx s₀.mem p := by
      rw [o₁.mem, hp.addr hL]
      exact Lay.bytes_keep hL hk.frame hp.sep (by have := hp.len32 hL; omega)
    have rep := r₂ msg (by rw [o₁.mem]; exact hr) hpos
    rw [eb] at rep
    refine WP.mono (ih false s₂ (msg ++ L.pb idx s₀.mem p) (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hk₂ rep
      ?_) fun s' ⟨k', r', p'⟩ => ?_
    · show (s₂.gpr .r0).toNat = _
      rw [ret₂, hpos, List.length_append, bytesAt_length, Nat.mod_add_mod]
    · simp only [List.map_cons, List.flatten_cons, List.isEmpty_cons, Bool.and_false, ← List.append_assoc]
        at r' p' ⊢
      exact ⟨k', r', p'⟩

/-! ## The squeezes -/

/-- The triple of a piece. -/
abbrev trip (idx : Reg → Nat) (p : Piece) : Nat × Nat × Nat := (idx p.base, p.off, p.len)

/-- The output pieces hold consecutive output from the state `P`, from
position `c` on. -/
def Outs (L : VG.Proof.MlKem.Arm.Lay) (idx : Reg → Nat) (m : Mem) (rate : Nat) (P : Spec.Sha3.State) : Nat → List Piece → Prop
  | _, [] => True
  | c, p :: ps => L.pb idx m p = squeezeFrom rate P c p.len ∧ VG.Proof.MlKem.Arm.Outs L idx m rate P (c + p.len) ps

theorem sepAll_append {sz : List Nat} {a : Nat × Nat × Nat} {W W' : List (Nat × Nat × Nat)}
    (h : VG.Proof.MlKem.Arm.sepAll sz a W = true) (h' : VG.Proof.MlKem.Arm.sepAll sz a W' = true) : VG.Proof.MlKem.Arm.sepAll sz a (W ++ W') = true := by
  simp only [VG.Proof.MlKem.Arm.sepAll, List.all_append, Bool.and_eq_true] at h h' ⊢; exact ⟨h, h'⟩

theorem sepAll_map {α : Type} {sz : List Nat} {a : Nat × Nat × Nat} {ps : List α} {f : α → Nat × Nat × Nat}
    (h : ∀ q ∈ ps, VG.Proof.MlKem.Arm.sepB sz a (f q) = true) : VG.Proof.MlKem.Arm.sepAll sz a (ps.map f) = true := by
  simp only [VG.Proof.MlKem.Arm.sepAll, List.all_map, List.all_eq_true, Function.comp]; exact h

theorem squeezes_ok {L : VG.Proof.MlKem.Arm.Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates)
    (hre : encodable (BitVec.ofNat 32 rate) = true) {s₀ : State} (hc : VG.Proof.MlKem.Arm.Ctx L s₀) {P : Spec.Sha3.State} :
    ∀ (ps : List Piece) (first : Bool) (s : State) (c : Nat),
      (∀ p ∈ ps, VG.Proof.MlKem.Arm.PieceOk L idx s₀ true p) → ps.Pairwise (fun p q => VG.Proof.MlKem.Arm.sepB L.sizes (VG.Proof.MlKem.Arm.trip idx p) (VG.Proof.MlKem.Arm.trip idx q) = true) →
      VG.Proof.MlKem.Arm.Rg s₀ s → VG.Proof.MlKem.Arm.Pos first s ≤ rate →
      (∀ d, squeezeFrom rate (stateAt s.mem (State.addr (L.ptr 0))) (VG.Proof.MlKem.Arm.Pos first s) d = squeezeFrom rate P c d) →
      WP isa (squeezes rate first ps) s fun s' =>
        Kept (L.RL (VG.Proof.MlKem.Arm.kRegs ++ ps.map (VG.Proof.MlKem.Arm.trip idx))) s s' ∧ VG.Proof.MlKem.Arm.Outs L idx s'.mem rate P c ps := by
  intro ps
  induction ps with
  | nil => exact fun _ s _ _ _ _ _ _ => WP.block_nil ⟨Kept.refl _ _, trivial⟩
  | cons p ps ih =>
    intro first s c hps hpw hg hple hcont
    have hp := hps p (List.mem_cons_self ..)
    have hL := hc.ok
    have rpos := VG.Proof.MlKem.Arm.rate_pos hrate
    have rle := rates_lt hrate
    have hcs := hg.ctx hc
    refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.kargs_ok first hp.base hre hp.oenc hp.lenc) fun s₁ ⟨o₁, g0, g1, g2, g3, g12, glr⟩ => ?_)
    have hc₁ := hcs.only o₁
    have gb : s.gpr p.base = L.ptr (idx p.base) := by rw [hg.cs _ hp.base.1 hp.base.2, hp.ptr]
    rw [hcs.r7] at g0 glr
    rw [gb] at g3
    rw [VG.Proof.MlKem.Arm.pos_r2] at g2
    obtain ⟨e0, e1, e2⟩ := hc₁.kregs
    have er := hp.regA hL
    have hg₁ : VG.Proof.MlKem.Arm.Rg s₀ s₁ := hg.kept (o₁.kept [])
    have hS : SqueezeArgs s₁ (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) (L.ptr (idx p.base) + BitVec.ofNat 32 p.off)
        rate (VG.Proof.MlKem.Arm.Pos first s) p.len := by
      refine ⟨g0, g1, g2, g3, g12, glr, hrate, hple, hp.len32 hL, hc₁.sp8, fit_le (by decide) hc.fit,
        hp.fit hL, hc.fitO (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [e0, er]; exact Lay.disj hL (VG.Proof.MlKem.Arm.sepB_symm hp.sepK.1)
      · rw [e0, e1]; exact Lay.disj hL (hc.sep00 (by decide) (by decide) (by decide))
      · rw [er, e1]; exact Lay.disj hL hp.sepK.2.1
      · rw [e2, e0]; exact Lay.disj hL (VG.Proof.MlKem.Arm.sepB_symm (hc.sep01 (by decide) (by decide)))
      · rw [e2, er]; exact Lay.disj hL (VG.Proof.MlKem.Arm.sepB_symm hp.sepK.2.2)
      · rw [e2, e1]; exact Lay.disj hL (VG.Proof.MlKem.Arm.sepB_symm (hc.sep01 (by decide) (by decide)))
      · rw [e0, er, e1]
        exact VG.Proof.MlKem.Arm.covers_cons' (hc₁.cs (by decide)) (VG.Proof.MlKem.Arm.covers_cons' (hp.covW hg₁)
          (VG.Proof.MlKem.Arm.covers_cons' (hc₁.cs (by decide)) VG.Proof.MlKem.Arm.covers_nil'))
    refine WP.seq (squeeze_ok hS fun s₂ k₂ b₂ r₂ n₂ => ?_)
    rw [e0, er, e1, e2] at k₂
    have out₂ : L.pb idx s₂.mem p = squeezeFrom rate P c p.len := by
      show bytesAt s₂.mem (State.addr (L.ptr (idx p.base)) + BitVec.ofNat 64 p.off) p.len = _
      rw [← hp.addr hL, b₂, o₁.mem, hcont]
    have cont₂ : ∀ d, squeezeFrom rate (stateAt s₂.mem (State.addr (L.ptr 0))) (VG.Proof.MlKem.Arm.Pos false s₂) d =
        squeezeFrom rate P (c + p.len) d := fun d => by
      rw [show VG.Proof.MlKem.Arm.Pos false s₂ = (s₂.gpr .r0).toNat from rfl, n₂, o₁.mem]
      exact squeezeFrom_shift rpos (by omega) hcont p.len d
    have pw := List.pairwise_cons.mp hpw
    have hg₂ : VG.Proof.MlKem.Arm.Rg s₀ s₂ := hg₁.kept k₂
    refine WP.mono (ih false s₂ (c + p.len) (fun q hq => hps q (List.mem_cons_of_mem _ hq)) pw.2 hg₂ r₂ cont₂)
      fun s' ⟨k', o'⟩ => ⟨?_, ?_, o'⟩
    · refine (o₁.kept _).trans ((k₂.mono fun r hr => ?_).trans (k'.monoL fun w hw => ?_))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [Lay.RL, List.map_append, List.map_cons, List.mem_append, List.mem_cons, List.mem_map]
        rcases hr with rfl | rfl | rfl | rfl <;> simp
      · simp only [List.mem_append, List.mem_map, List.map_cons, List.mem_cons] at hw ⊢
        rcases hw with hw | ⟨q, hq, rfl⟩
        · exact .inl hw
        · exact .inr (.inr ⟨q, hq, rfl⟩)
    · rw [← out₂]
      exact Lay.bytes_keep hL k'.frame (VG.Proof.MlKem.Arm.sepAll_append hp.sep (VG.Proof.MlKem.Arm.sepAll_map pw.1)) (by have := hp.len32 hL; omega)

/-! ## The whole hash -/

theorem zeroState_ok {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hc : VG.Proof.MlKem.Arm.Ctx L s) :
    WP isa (.block (zeroState .r7)) s fun s' =>
      Kept (L.RL [(0, 0, 200)]) s s' ∧ stateAt s'.mem (State.addr (L.ptr 0)) = Spec.Sha3.zero := by
  rw [zeroState, ← List.singleton_append, WP.block_append_iff]
  have hmov : WP isa (.block [.mov .r12 (.imm 0)]) s fun s₁ => s₁.gpr = (s.setReg .r12 0).gpr ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.sp = s.sp := by
    run_block []
  refine WP.mono hmov fun s₁ ⟨g, m, rd, wr, sp⟩ => ?_
  have e7 : s₁.gpr .r7 = L.ptr 0 := by rw [g]; simp [State.setReg, hc.r7]
  refine WP.mono (Sample.zeroWords_ok .r7 (s₁ := s₁) (by rw [g]; simp [State.setReg])
    (by rw [e7]; exact fit_le (by decide) hc.fit) fun k hk => by
      rw [e7, wr]
      exact hc.cs (o := 4 * k) (l := 4) (by omega) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
    fun s₂ h₂ => ?_
  have hf := h₂.frame
  have hz := h₂.zero
  rw [e7] at hf hz
  refine ⟨⟨fun r hr hl => ?_, by rw [h₂.sp, sp], by rw [h₂.rd, rd], by rw [h₂.wr, wr], ?_⟩,
    Sample.stateAt_zero hz⟩
  · rw [h₂.gpr, g]
    obtain ⟨-, -, -, -, n12⟩ := VG.Proof.MlKem.Arm.pres_ne hr hl
    simp [State.setReg, n12]
  · rw [← m]
    refine hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    rw [List.mem_singleton] at hr; subst hr
    show Region.Sub _ (L.R 0 0 200)
    rw [← Lay.regA_zero]; exact fun _ h => h

theorem sfx8 {sfx : Nat} (h : sfx < 256) : (BitVec.ofNat 32 sfx).setWidth 8 = BitVec.ofNat 8 sfx := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : sfx < 2 ^ 32)]

/-- `hash`: the sponge of the pieces `ins`, output into the pieces `outs`. -/
theorem hash_ok {L : VG.Proof.MlKem.Arm.Lay} {idx : Reg → Nat} {rate sfx : Nat} (hrate : rate ∈ rates)
    (hre : encodable (BitVec.ofNat 32 rate) = true) (hse : encodable (BitVec.ofNat 32 sfx) = true)
    (hsfx : sfx < 256) {s₀ : State} (hc : VG.Proof.MlKem.Arm.Ctx L s₀) {ins outs : List Piece} (hne : ins ≠ [])
    (hin : ∀ p ∈ ins, VG.Proof.MlKem.Arm.PieceOk L idx s₀ false p) (hout : ∀ p ∈ outs, VG.Proof.MlKem.Arm.PieceOk L idx s₀ true p)
    (hpw : outs.Pairwise (fun p q => VG.Proof.MlKem.Arm.sepB L.sizes (VG.Proof.MlKem.Arm.trip idx p) (VG.Proof.MlKem.Arm.trip idx q) = true)) :
    WP isa (hash rate sfx ins outs) s₀ fun s' =>
      Kept (L.RL (VG.Proof.MlKem.Arm.kRegs ++ outs.map (VG.Proof.MlKem.Arm.trip idx))) s₀ s' ∧
      VG.Proof.MlKem.Arm.Outs L idx s'.mem rate (absorb rate (pad rate (BitVec.ofNat 8 sfx) (ins.map (L.pb idx s₀.mem)).flatten)) 0
        outs := by
  have hL := hc.ok
  have rpos := VG.Proof.MlKem.Arm.rate_pos hrate
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.zeroState_ok hc) fun s₁ ⟨k₁, z₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.absorbs_ok hrate hre hc ins true s₁ [] hin (k₁.monoL (by simp)) (repr_nil z₁)
    (by simp [VG.Proof.MlKem.Arm.Pos])) fun s₂ ⟨k₂, r₂, p₂⟩ => ?_)
  have hie : ins.isEmpty = false := by cases ins; exact absurd rfl hne; rfl
  rw [hie, Bool.and_false] at p₂
  rw [List.nil_append] at r₂ p₂
  have hc₂ := k₂.rg.ctx hc
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.pargs_ok hre hse) fun s₃ ⟨o₃, g0, g1, g2, g3, glr⟩ => ?_)
  have hc₃ := hc₂.only o₃
  rw [hc₂.r7] at g0 glr
  obtain ⟨e0, e1, e2⟩ := hc₃.kregs
  have hP : PadArgs s₃ (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) rate (s₂.gpr .r0).toNat (BitVec.ofNat 32 sfx) := by
    refine ⟨g0, g1, by rw [g2, BitVec.ofNat_toNat, BitVec.setWidth_eq], g3, glr, hrate,
      by rw [show (s₂.gpr .r0).toNat = VG.Proof.MlKem.Arm.Pos false s₂ from rfl, p₂]; exact Nat.mod_lt _ rpos, hc₃.sp8,
      fit_le (by decide) hc.fit, hc.fitO (by decide) (by decide), ?_, ?_, ?_, VG.Proof.MlKem.Arm.covers_kregs hc₃⟩
    · rw [e0, e1]; exact Lay.disj hL (hc.sep00 (by decide) (by decide) (by decide))
    · rw [e2, e0]; exact Lay.disj hL (VG.Proof.MlKem.Arm.sepB_symm (hc.sep01 (by decide) (by decide)))
    · rw [e2, e1]; exact Lay.disj hL (VG.Proof.MlKem.Arm.sepB_symm (hc.sep01 (by decide) (by decide)))
  refine WP.seq (pad_ok hP fun s₄ k₄ st₄ => ?_)
  rw [e0, e1, e2, ← VG.Proof.MlKem.Arm.RL_kRegs] at k₄
  have st := st₄ _ (by rw [o₃.mem]; exact r₂) p₂
  rw [VG.Proof.MlKem.Arm.sfx8 hsfx] at st
  have hg₄ : VG.Proof.MlKem.Arm.Rg s₀ s₄ := (k₂.trans ((o₃.kept _).trans k₄)).rg
  refine WP.mono (VG.Proof.MlKem.Arm.squeezes_ok hrate hre hc outs true s₄ 0 hout hpw hg₄ (Nat.zero_le _)
    (fun d => by rw [st]; rfl)) fun s' ⟨k', o'⟩ => ⟨?_, o'⟩
  refine ((k₂.trans ((o₃.kept _).trans k₄)).monoL fun w hw => List.mem_append_left _ hw).trans k'

/-! ## The arguments of the sponge functions, for the constant-time proofs -/

theorem absorbArgs_of {L : VG.Proof.MlKem.Arm.Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates) {s₀ s₁ : State}
    {p : Piece} (hc₁ : VG.Proof.MlKem.Arm.Ctx L s₁) (hg : VG.Proof.MlKem.Arm.Rg s₀ s₁) (hp : VG.Proof.MlKem.Arm.PieceOk L idx s₀ false p) {pos : Nat} (hpos : pos < rate)
    (g0 : s₁.gpr .r0 = L.ptr 0) (g1 : s₁.gpr .r1 = BitVec.ofNat 32 rate) (g2 : s₁.gpr .r2 = BitVec.ofNat 32 pos)
    (g3 : s₁.gpr .r3 = L.ptr (idx p.base) + BitVec.ofNat 32 p.off) (g12 : s₁.gpr .r12 = BitVec.ofNat 32 p.len)
    (glr : s₁.gpr .lr = L.ptr 0 + BitVec.ofNat 32 200) :
    AbsorbArgs s₁ (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) (L.ptr (idx p.base) + BitVec.ofNat 32 p.off)
      rate pos p.len := by
  have hL := hc₁.ok
  obtain ⟨e0, e1, e2⟩ := hc₁.kregs
  have er := hp.regA hL
  refine ⟨g0, g1, g2, g3, g12, glr, hrate, hpos, hp.len32 hL, hc₁.sp8, fit_le (by decide) hc₁.fit,
    hp.fit hL, hc₁.fitO (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, VG.Proof.MlKem.Arm.covers_kregs hc₁, ?_⟩
  · rw [e0, e1]; exact Lay.disj hL (hc₁.sep00 (by decide) (by decide) (by decide))
  · rw [er, e0]; exact Lay.disj hL hp.sepK.1
  · rw [er, e1]; exact Lay.disj hL hp.sepK.2.1
  · rw [e2, e0]; exact Lay.disj hL (VG.Proof.MlKem.Arm.sepB_symm (hc₁.sep01 (by decide) (by decide)))
  · rw [e2, e1]; exact Lay.disj hL (VG.Proof.MlKem.Arm.sepB_symm (hc₁.sep01 (by decide) (by decide)))
  · rw [e2, er]; exact Lay.disj hL (VG.Proof.MlKem.Arm.sepB_symm hp.sepK.2.2)
  · rw [er]; exact hp.covR hg

theorem squeezeArgs_of {L : VG.Proof.MlKem.Arm.Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates) {s₀ s₁ : State}
    {p : Piece} (hc₁ : VG.Proof.MlKem.Arm.Ctx L s₁) (hg : VG.Proof.MlKem.Arm.Rg s₀ s₁) (hp : VG.Proof.MlKem.Arm.PieceOk L idx s₀ true p) {pos : Nat} (hpos : pos ≤ rate)
    (g0 : s₁.gpr .r0 = L.ptr 0) (g1 : s₁.gpr .r1 = BitVec.ofNat 32 rate) (g2 : s₁.gpr .r2 = BitVec.ofNat 32 pos)
    (g3 : s₁.gpr .r3 = L.ptr (idx p.base) + BitVec.ofNat 32 p.off) (g12 : s₁.gpr .r12 = BitVec.ofNat 32 p.len)
    (glr : s₁.gpr .lr = L.ptr 0 + BitVec.ofNat 32 200) :
    SqueezeArgs s₁ (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) (L.ptr (idx p.base) + BitVec.ofNat 32 p.off)
      rate pos p.len := by
  have hL := hc₁.ok
  obtain ⟨e0, e1, e2⟩ := hc₁.kregs
  have er := hp.regA hL
  refine ⟨g0, g1, g2, g3, g12, glr, hrate, hpos, hp.len32 hL, hc₁.sp8, fit_le (by decide) hc₁.fit,
    hp.fit hL, hc₁.fitO (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e0, er]; exact Lay.disj hL (VG.Proof.MlKem.Arm.sepB_symm hp.sepK.1)
  · rw [e0, e1]; exact Lay.disj hL (hc₁.sep00 (by decide) (by decide) (by decide))
  · rw [er, e1]; exact Lay.disj hL hp.sepK.2.1
  · rw [e2, e0]; exact Lay.disj hL (VG.Proof.MlKem.Arm.sepB_symm (hc₁.sep01 (by decide) (by decide)))
  · rw [e2, er]; exact Lay.disj hL (VG.Proof.MlKem.Arm.sepB_symm hp.sepK.2.2)
  · rw [e2, e1]; exact Lay.disj hL (VG.Proof.MlKem.Arm.sepB_symm (hc₁.sep01 (by decide) (by decide)))
  · rw [e0, er, e1]
    exact VG.Proof.MlKem.Arm.covers_cons' (hc₁.cs (by decide)) (VG.Proof.MlKem.Arm.covers_cons' (hp.covW hg)
      (VG.Proof.MlKem.Arm.covers_cons' (hc₁.cs (by decide)) VG.Proof.MlKem.Arm.covers_nil'))

theorem padArgs_of {L : VG.Proof.MlKem.Arm.Lay} {rate : Nat} (hrate : rate ∈ rates) {s₁ : State} (hc₁ : VG.Proof.MlKem.Arm.Ctx L s₁) {pos : Nat}
    (hpos : pos < rate) {sfx : BitVec 32}
    (g0 : s₁.gpr .r0 = L.ptr 0) (g1 : s₁.gpr .r1 = BitVec.ofNat 32 rate) (g2 : s₁.gpr .r2 = BitVec.ofNat 32 pos)
    (g3 : s₁.gpr .r3 = sfx) (glr : s₁.gpr .lr = L.ptr 0 + BitVec.ofNat 32 200) :
    PadArgs s₁ (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) rate pos sfx := by
  have hL := hc₁.ok
  obtain ⟨e0, e1, e2⟩ := hc₁.kregs
  refine ⟨g0, g1, g2, g3, glr, hrate, hpos, hc₁.sp8, fit_le (by decide) hc₁.fit,
    hc₁.fitO (by decide) (by decide), ?_, ?_, ?_, VG.Proof.MlKem.Arm.covers_kregs hc₁⟩
  · rw [e0, e1]; exact Lay.disj hL (hc₁.sep00 (by decide) (by decide) (by decide))
  · rw [e2, e0]; exact Lay.disj hL (VG.Proof.MlKem.Arm.sepB_symm (hc₁.sep01 (by decide) (by decide)))
  · rw [e2, e1]; exact Lay.disj hL (VG.Proof.MlKem.Arm.sepB_symm (hc₁.sep01 (by decide) (by decide)))

/-- The 64 bytes of `G(c)` squeezed at once: both of its outputs. -/
theorem G_split (c : List Byte) :
    Spec.Sha3.squeezeFrom 72 (VG.Proof.MlKem.padded 72 Spec.Sha3.sha3Suffix c) 0 64 =
      (Spec.MlKem.G c).1 ++ (Spec.MlKem.G c).2 := by
  simp only [Spec.MlKem.G, VG.Proof.MlKem.sha3_512_eq, List.take_append_drop]

end VG.Proof.MlKem.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.Calls`. -/
section

/-!
# ML-KEM-768 on 32-bit ARM: calling the primitives on buffers

For each primitive, a contract written with the precondition of its proof and
what its correctness proof shows (`kNtt`, …, as `kAdd` in `Prims.lean`), and
the call of it with its arguments at offsets in the buffers of a layout
(`addL`, …): what it needs (the arguments in the registers, the regions apart
and permitted), what it changes (`Kept`, with the regions as triples) and what
it computes.
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The address at offset `o` of buffer `i`. -/
abbrev Lay.A (L : VG.Proof.MlKem.Arm.Lay) (i o : Nat) : Addr := State.addr (L.ptr i) + BitVec.ofNat 64 o

/-- A whole buffer, as a permitted region. -/
abbrev Lay.buf (L : VG.Proof.MlKem.Arm.Lay) (i : Nat) : Region := ⟨State.addr (L.ptr i), L.size i⟩

theorem Lay.ptr_ok {L : VG.Proof.MlKem.Arm.Lay} (hL : L.Ok) {i o l : Nat} (hb : i < L.sizes.length ∧ o + l ≤ L.sizes.getD i 0)
    (hl : 0 < l) :
    State.addr (L.ptr i + BitVec.ofNat 32 o) = L.A i o ∧ (L.ptr i + BitVec.ofNat 32 o).toNat + l ≤ 2 ^ 32 :=
  ⟨Lay.addr_off hL hb.1 (by have := hb.2; simp only [Lay.size]; omega), Lay.fit_off hL hb.1 hb.2 hl⟩

theorem view_r0 (s : State) (rd wr : List Region) : (VG.Proof.MlKem.Arm.view s rd wr).gpr .r0 = s.gpr .r0 := VG.Proof.MlKem.Arm.view_gpr' _ _ _ (by decide)
theorem view_r1 (s : State) (rd wr : List Region) : (VG.Proof.MlKem.Arm.view s rd wr).gpr .r1 = s.gpr .r1 := VG.Proof.MlKem.Arm.view_gpr' _ _ _ (by decide)
theorem view_r2 (s : State) (rd wr : List Region) : (VG.Proof.MlKem.Arm.view s rd wr).gpr .r2 = s.gpr .r2 := VG.Proof.MlKem.Arm.view_gpr' _ _ _ (by decide)
theorem view_r3 (s : State) (rd wr : List Region) : (VG.Proof.MlKem.Arm.view s rd wr).gpr .r3 = s.gpr .r3 := VG.Proof.MlKem.Arm.view_gpr' _ _ _ (by decide)

theorem Ctx.buf0 {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hc : VG.Proof.MlKem.Arm.Ctx L s) : L.buf 0 ∈ s.wr := by
  exact hc.cw

theorem mem_rd_wr {r : Region} {s : State} (h : r ∈ s.wr) : r ∈ s.rd ++ s.wr := List.mem_append_right _ h

/-! ## `vg_mlkem_add`, `vg_mlkem_sub` -/

theorem accL {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = L.ptr j + BitVec.ofNat 32 o')
    (hs : VG.Proof.MlKem.Arm.sepB L.sizes (i, o, 1024) (j, o', 1024) = true) (hw : L.buf i ∈ s.wr) (hr : L.buf j ∈ s.rd ++ s.wr)
    {f g : VG.Spec.MlKem.Poly} (hf : PolyIs s.mem (L.A i o) f) (hg : PolyIs s.mem (L.A j o') g) :
    VG.Proof.MlKem.Arm.AccArgs s (L.ptr i + BitVec.ofNat 32 o) (L.ptr j + BitVec.ofNat 32 o') ∧
      State.addr (L.ptr i + BitVec.ofNat 32 o) = L.A i o ∧ State.addr (L.ptr j + BitVec.ofNat 32 o') = L.A j o' := by
  obtain ⟨ea, fa⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds hs) (by decide)
  obtain ⟨eb, fb⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds (VG.Proof.MlKem.Arm.sepB_symm hs)) (by decide)
  refine ⟨⟨g0, g1, ?_, fa, fb, by rw [ea]; exact hf.1, by rw [eb]; exact hg.1, ?_, ?_⟩, ea, eb⟩
  · rw [ea, eb]; exact Lay.disj hL hs
  · rw [ea]; exact Lay.covers hw (VG.Proof.MlKem.Arm.sepB_bounds hs).2
  · rw [eb]; exact Lay.covers hr (VG.Proof.MlKem.Arm.sepB_bounds (VG.Proof.MlKem.Arm.sepB_symm hs)).2

theorem addL {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = L.ptr j + BitVec.ofNat 32 o')
    (hs : VG.Proof.MlKem.Arm.sepB L.sizes (i, o, 1024) (j, o', 1024) = true) (hw : L.buf i ∈ s.wr) (hr : L.buf j ∈ s.rd ++ s.wr)
    {f g : VG.Spec.MlKem.Poly} (hf : PolyIs s.mem (L.A i o) f) (hg : PolyIs s.mem (L.A j o') g) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(i, o, 1024)]) s s' → PolyIs s'.mem (L.A i o) (add f g) → Q s') :
    WP isa callAdd s Q := by
  obtain ⟨h, ea, eb⟩ := VG.Proof.MlKem.Arm.accL hL g0 g1 hs hw hr hf hg
  refine VG.Proof.MlKem.Arm.add_call h fun s' hk hp => hQ s' (by rw [ea] at hk; exact hk) ?_
  rw [ea, eb, hf.2, hg.2] at hp; exact hp

theorem subL {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = L.ptr j + BitVec.ofNat 32 o')
    (hs : VG.Proof.MlKem.Arm.sepB L.sizes (i, o, 1024) (j, o', 1024) = true) (hw : L.buf i ∈ s.wr) (hr : L.buf j ∈ s.rd ++ s.wr)
    {f g : VG.Spec.MlKem.Poly} (hf : PolyIs s.mem (L.A i o) f) (hg : PolyIs s.mem (L.A j o') g) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(i, o, 1024)]) s s' → PolyIs s'.mem (L.A i o) (VG.Spec.MlKem.sub f g) → Q s') :
    WP isa callSub s Q := by
  obtain ⟨h, ea, eb⟩ := VG.Proof.MlKem.Arm.accL hL g0 g1 hs hw hr hf hg
  refine VG.Proof.MlKem.Arm.sub_call h fun s' hk hp => hQ s' (by rw [ea] at hk; exact hk) ?_
  rw [ea, eb, hf.2, hg.2] at hp; exact hp

/-! ## `vg_mlkem_multiply_ntts` -/

theorem mulL {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hL : L.Ok) {ih oh jf of kg og ls os : Nat}
    (g0 : s.gpr .r0 = L.ptr ih + BitVec.ofNat 32 oh) (g1 : s.gpr .r1 = L.ptr jf + BitVec.ofNat 32 of)
    (g2 : s.gpr .r2 = L.ptr kg + BitVec.ofNat 32 og) (g3 : s.gpr .r3 = L.ptr ls + BitVec.ofNat 32 os)
    (s_hf : VG.Proof.MlKem.Arm.sepB L.sizes (ih, oh, 1024) (jf, of, 1024) = true) (s_hg : VG.Proof.MlKem.Arm.sepB L.sizes (ih, oh, 1024) (kg, og, 1024) = true)
    (s_hs : VG.Proof.MlKem.Arm.sepB L.sizes (ih, oh, 1024) (ls, os, 1024) = true) (s_fs : VG.Proof.MlKem.Arm.sepB L.sizes (jf, of, 1024) (ls, os, 1024) = true)
    (s_gs : VG.Proof.MlKem.Arm.sepB L.sizes (kg, og, 1024) (ls, os, 1024) = true)
    (wh : L.buf ih ∈ s.wr) (wf : L.buf jf ∈ s.rd ++ s.wr) (wg : L.buf kg ∈ s.rd ++ s.wr) (ws : L.buf ls ∈ s.wr)
    {f g : VG.Spec.MlKem.Poly} (hf : PolyIs s.mem (L.A jf of) f) (hg : PolyIs s.mem (L.A kg og) g) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(ih, oh, 1024), (ls, os, 1024)]) s s' → PolyIs s'.mem (L.A ih oh) (multiplyNTTs f g) →
      Q s') :
    WP isa callMul s Q := by
  obtain ⟨eh, fh⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds s_hf) (by decide)
  obtain ⟨ef, ff⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds s_fs) (by decide)
  obtain ⟨eg, fg⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds s_gs) (by decide)
  obtain ⟨es, fs⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds (VG.Proof.MlKem.Arm.sepB_symm s_hs)) (by decide)
  have a : VG.Proof.MlKem.Arm.MulArgs s (L.ptr ih + BitVec.ofNat 32 oh) (L.ptr jf + BitVec.ofNat 32 of) (L.ptr kg + BitVec.ofNat 32 og)
      (L.ptr ls + BitVec.ofNat 32 os) := by
    refine ⟨g0, g1, g2, g3, ?_, ?_, ?_, ?_, ?_, fh, ff, fg, fs, by rw [ef]; exact hf.1, by rw [eg]; exact hg.1, ?_, ?_⟩
    · rw [eh, ef]; exact Lay.disj hL s_hf
    · rw [eh, eg]; exact Lay.disj hL s_hg
    · rw [eh, es]; exact Lay.disj hL s_hs
    · rw [ef, es]; exact Lay.disj hL s_fs
    · rw [eg, es]; exact Lay.disj hL s_gs
    · rw [eh, es]
      exact VG.Proof.MlKem.Arm.covers_cons' (Lay.covers wh (VG.Proof.MlKem.Arm.sepB_bounds s_hf).2)
        (VG.Proof.MlKem.Arm.covers_cons' (Lay.covers ws (VG.Proof.MlKem.Arm.sepB_bounds (VG.Proof.MlKem.Arm.sepB_symm s_hs)).2) VG.Proof.MlKem.Arm.covers_nil')
    · rw [ef, eg]
      exact VG.Proof.MlKem.Arm.covers_cons' (Lay.covers wf (VG.Proof.MlKem.Arm.sepB_bounds s_fs).2)
        (VG.Proof.MlKem.Arm.covers_cons' (Lay.covers wg (VG.Proof.MlKem.Arm.sepB_bounds s_gs).2) VG.Proof.MlKem.Arm.covers_nil')
  refine VG.Proof.MlKem.Arm.mul_call a fun s' hk hp => hQ s' (by simp only [VG.Proof.MlKem.Arm.mulWr, eh, es] at hk; exact hk) ?_
  rw [eh, ef, eg, hf.2, hg.2] at hp; exact hp

/-! ## `vg_mlkem_ntt`, `vg_mlkem_inv_ntt` -/

def kNtt : Contract isa := VG.Proof.MlKem.Arm.mkK Ntt.Pre (fun s₀ s => PolyIs s.mem (Ntt.F s₀) (ntt (Ntt.P s₀))) (VG.Proof.MlKem.Arm.regsEq [.r0, .r1])

def kNttInv : Contract isa :=
  VG.Proof.MlKem.Arm.mkK Ntt.Pre (fun s₀ s => PolyIs s.mem (Ntt.F s₀) (nttInv (Ntt.P s₀))) (VG.Proof.MlKem.Arm.regsEq [.r0, .r1])

theorem kNtt_ok : ∀ s, kNtt.pre s → ∃ t s', Exec isa Impl.MlKem.Arm.ntt s t s' ∧ abiPreserved s s' ∧
    kNtt.post s s' := VG.Proof.MlKem.Arm.mkK_ok fun _ hp => Ntt.correct hp

theorem kNttInv_ok : ∀ s, kNttInv.pre s → ∃ t s', Exec isa Impl.MlKem.Arm.nttInv s t s' ∧ abiPreserved s s' ∧
    kNttInv.post s s' := VG.Proof.MlKem.Arm.mkK_ok fun _ hp => NttInv.correct hp

theorem ntt_pre {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = L.ptr j + BitVec.ofNat 32 o')
    (hs : VG.Proof.MlKem.Arm.sepB L.sizes (i, o, 1024) (j, o', 1024) = true) (wi : L.buf i ∈ s.wr) (wj : L.buf j ∈ s.wr)
    {f : VG.Spec.MlKem.Poly} (hf : PolyIs s.mem (L.A i o) f) :
    Ntt.Pre (VG.Proof.MlKem.Arm.view s [] [polyRegion (L.A i o), polyRegion (L.A j o')]) ∧
      Covers ([] ++ [polyRegion (L.A i o), polyRegion (L.A j o')]) (s.rd ++ s.wr) ∧
      Covers [polyRegion (L.A i o), polyRegion (L.A j o')] s.wr ∧
      Ntt.F (VG.Proof.MlKem.Arm.view s [] [polyRegion (L.A i o), polyRegion (L.A j o')]) = L.A i o ∧
      Ntt.P (VG.Proof.MlKem.Arm.view s [] [polyRegion (L.A i o), polyRegion (L.A j o')]) = f := by
  obtain ⟨ea, fa⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds hs) (by decide)
  obtain ⟨eb, fb⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds (VG.Proof.MlKem.Arm.sepB_symm hs)) (by decide)
  have cw : Covers [polyRegion (L.A i o), polyRegion (L.A j o')] s.wr :=
    VG.Proof.MlKem.Arm.covers_cons' (Lay.covers wi (VG.Proof.MlKem.Arm.sepB_bounds hs).2) (VG.Proof.MlKem.Arm.covers_cons' (Lay.covers wj (VG.Proof.MlKem.Arm.sepB_bounds (VG.Proof.MlKem.Arm.sepB_symm hs)).2)
      VG.Proof.MlKem.Arm.covers_nil')
  have eF : Ntt.F (VG.Proof.MlKem.Arm.view s [] [polyRegion (L.A i o), polyRegion (L.A j o')]) = L.A i o := by
    simp only [Ntt.F, Ntt.pf, VG.Proof.MlKem.Arm.view_r0, g0, ea]
  have eS : Ntt.S (VG.Proof.MlKem.Arm.view s [] [polyRegion (L.A i o), polyRegion (L.A j o')]) = L.A j o' := by
    simp only [Ntt.S, Ntt.ps, VG.Proof.MlKem.Arm.view_r1, g1, eb]
  refine ⟨⟨rfl, by rw [eF, eS]; rfl, by rw [eF, eS]; exact Lay.disj hL hs, by simp only [Ntt.pf, VG.Proof.MlKem.Arm.view_r0, g0]; exact fa,
    by simp only [Ntt.ps, VG.Proof.MlKem.Arm.view_r1, g1]; exact fb, by rw [eF]; exact hf.1⟩, VG.Proof.MlKem.Arm.covers_wr cw, cw, eF, ?_⟩
  simp only [Ntt.P, eF, State.withRegions_mem, State.callEntry_mem, hf.2]

theorem nttL {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = L.ptr j + BitVec.ofNat 32 o')
    (hs : VG.Proof.MlKem.Arm.sepB L.sizes (i, o, 1024) (j, o', 1024) = true) (wi : L.buf i ∈ s.wr) (wj : L.buf j ∈ s.wr)
    {f : VG.Spec.MlKem.Poly} (hf : PolyIs s.mem (L.A i o) f) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(i, o, 1024), (j, o', 1024)]) s s' → PolyIs s'.mem (L.A i o) (ntt f) → Q s') :
    WP isa callNtt s Q := by
  obtain ⟨hp, c1, c2, eF, eP⟩ := VG.Proof.MlKem.Arm.ntt_pre hL g0 g1 hs wi wj hf
  refine VG.Proof.MlKem.Arm.call_kept (k := VG.Proof.MlKem.Arm.kNtt) VG.Proof.MlKem.Arm.kNtt_ok (by decide +kernel) hp c1 c2 fun s' hk hq => hQ s' hk ?_
  simp only [VG.Proof.MlKem.Arm.kNtt, VG.Proof.MlKem.Arm.mkK, eF, eP, State.withRegions_mem] at hq; exact hq

theorem nttInvL {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = L.ptr j + BitVec.ofNat 32 o')
    (hs : VG.Proof.MlKem.Arm.sepB L.sizes (i, o, 1024) (j, o', 1024) = true) (wi : L.buf i ∈ s.wr) (wj : L.buf j ∈ s.wr)
    {f : VG.Spec.MlKem.Poly} (hf : PolyIs s.mem (L.A i o) f) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(i, o, 1024), (j, o', 1024)]) s s' → PolyIs s'.mem (L.A i o) (nttInv f) → Q s') :
    WP isa callNttInv s Q := by
  obtain ⟨hp, c1, c2, eF, eP⟩ := VG.Proof.MlKem.Arm.ntt_pre hL g0 g1 hs wi wj hf
  refine VG.Proof.MlKem.Arm.call_kept (k := VG.Proof.MlKem.Arm.kNttInv) VG.Proof.MlKem.Arm.kNttInv_ok (by decide +kernel) hp c1 c2 fun s' hk hq => hQ s' hk ?_
  simp only [VG.Proof.MlKem.Arm.kNttInv, VG.Proof.MlKem.Arm.mkK, eF, eP, State.withRegions_mem] at hq; exact hq

/-! ## `vg_mlkem_cbd2`, `vg_mlkem_decode12`, `vg_mlkem_encode12` -/

def kCbd : Contract isa := VG.Proof.MlKem.Arm.mkK Cbd2.Pre (fun s₀ s => PolyIs s.mem (Cbd2.F s₀) (Cbd2.D s₀)) (VG.Proof.MlKem.Arm.regsEq [.r0, .r1])

theorem kCbd_ok : ∀ s, kCbd.pre s → ∃ t s', Exec isa Impl.MlKem.Arm.cbd2 s t s' ∧ abiPreserved s s' ∧
    kCbd.post s s' :=
  VG.Proof.MlKem.Arm.mkK_ok fun s₀ hp => WP.mono (Cbd2.loop_ok hp) fun _ h => ⟨h.pres, h.sp,
    polyIs_of_coeffAt (p := Cbd2.F s₀) fun j hj => by
      rw [h.coeff j hj, ite_eq_left (by rw [VG.Proof.MlKem.n_eq] at hj; omega)]; rfl⟩

def kDec : Contract isa := VG.Proof.MlKem.Arm.mkK Decode12.Pre (fun s₀ s => PolyIs s.mem (Decode12.F s₀) (Decode12.D s₀))
  (VG.Proof.MlKem.Arm.regsEq [.r0, .r1])

theorem kDec_ok : ∀ s, kDec.pre s → ∃ t s', Exec isa Impl.MlKem.Arm.decode12 s t s' ∧ abiPreserved s s' ∧
    kDec.post s s' :=
  VG.Proof.MlKem.Arm.mkK_ok fun s₀ hp => WP.mono (Decode12.loop_ok hp) fun _ h => ⟨h.pres, h.sp,
    polyIs_of_coeffAt (p := Decode12.F s₀) fun j hj => by
      rw [h.coeff j hj, ite_eq_left (by rw [VG.Proof.MlKem.n_eq] at hj; omega)]; rfl⟩

def kEnc : Contract isa := VG.Proof.MlKem.Arm.mkK Encode12.Pre (fun s₀ s => bytesAt s.mem (Encode12.O s₀) 384 = Encode12.E s₀)
  (VG.Proof.MlKem.Arm.regsEq [.r0, .r1])

theorem kEnc_ok : ∀ s, kEnc.pre s → ∃ t s', Exec isa Impl.MlKem.Arm.encode12 s t s' ∧ abiPreserved s s' ∧
    kEnc.post s s' :=
  VG.Proof.MlKem.Arm.mkK_ok fun s₀ hp => WP.mono (Encode12.loop_ok hp) fun _ h => ⟨h.pres, h.sp,
    bytesAt_eq! (p := Encode12.O s₀) (encode12_length _) fun k hk => by
      rw [h.bytes k hk, ite_eq_left (by omega)]⟩

/-- `SamplePolyCBD₂` of the 128 bytes at `(i, o)` into the polynomial at `(j, o')`. -/
theorem cbd2L {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = L.ptr j + BitVec.ofNat 32 o')
    (hs : VG.Proof.MlKem.Arm.sepB L.sizes (i, o, 128) (j, o', 1024) = true) (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(j, o', 1024)]) s s' →
      PolyIs s'.mem (L.A j o') (samplePolyCBD 2 (bytesAt s.mem (L.A i o) 128)) → Q s') :
    WP isa callCbd2 s Q := by
  obtain ⟨ea, fa⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds hs) (by decide)
  obtain ⟨eb, fb⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds (VG.Proof.MlKem.Arm.sepB_symm hs)) (by decide)
  have eB : Cbd2.B (VG.Proof.MlKem.Arm.view s [⟨L.A i o, 128⟩] [polyRegion (L.A j o')]) = L.A i o := by
    simp only [Cbd2.B, Cbd2.pb, VG.Proof.MlKem.Arm.view_r0, g0, ea]
  have eF : Cbd2.F (VG.Proof.MlKem.Arm.view s [⟨L.A i o, 128⟩] [polyRegion (L.A j o')]) = L.A j o' := by
    simp only [Cbd2.F, Cbd2.pf, VG.Proof.MlKem.Arm.view_r1, g1, eb]
  have cw : Covers [polyRegion (L.A j o')] s.wr := Lay.covers wj (VG.Proof.MlKem.Arm.sepB_bounds (VG.Proof.MlKem.Arm.sepB_symm hs)).2
  refine VG.Proof.MlKem.Arm.call_kept (k := VG.Proof.MlKem.Arm.kCbd) VG.Proof.MlKem.Arm.kCbd_ok (by decide +kernel) (rd := [⟨L.A i o, 128⟩]) (wr := [polyRegion (L.A j o')])
    ⟨by simp only [Cbd2.inR, eB, State.withRegions_rd], by simp only [eF, State.withRegions_wr],
      by simp only [Cbd2.inR, eB, eF]; exact Lay.disj hL hs,
      by simp only [Cbd2.pb, VG.Proof.MlKem.Arm.view_r0, g0]; exact fa, by simp only [Cbd2.pf, VG.Proof.MlKem.Arm.view_r1, g1]; exact fb⟩
    (VG.Proof.MlKem.Arm.covers_append (Lay.covers wi (VG.Proof.MlKem.Arm.sepB_bounds hs).2) (VG.Proof.MlKem.Arm.covers_wr cw)) cw fun s' hk hq => hQ s' hk ?_
  simp only [VG.Proof.MlKem.Arm.kCbd, VG.Proof.MlKem.Arm.mkK, Cbd2.D, eB, eF, State.withRegions_mem, State.callEntry_mem] at hq; exact hq

/-- `ByteDecode₁₂` of the 384 bytes at `(i, o)` into the polynomial at `(j, o')`. -/
theorem decode12L {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = L.ptr j + BitVec.ofNat 32 o')
    (hs : VG.Proof.MlKem.Arm.sepB L.sizes (i, o, 384) (j, o', 1024) = true) (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(j, o', 1024)]) s s' →
      PolyIs s'.mem (L.A j o') (decode12 (bytesAt s.mem (L.A i o) 384)) → Q s') :
    WP isa callDecode12 s Q := by
  obtain ⟨ea, fa⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds hs) (by decide)
  obtain ⟨eb, fb⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds (VG.Proof.MlKem.Arm.sepB_symm hs)) (by decide)
  have eB : Decode12.B (VG.Proof.MlKem.Arm.view s [⟨L.A i o, 384⟩] [polyRegion (L.A j o')]) = L.A i o := by
    simp only [Decode12.B, Decode12.pb, VG.Proof.MlKem.Arm.view_r0, g0, ea]
  have eF : Decode12.F (VG.Proof.MlKem.Arm.view s [⟨L.A i o, 384⟩] [polyRegion (L.A j o')]) = L.A j o' := by
    simp only [Decode12.F, Decode12.pf, VG.Proof.MlKem.Arm.view_r1, g1, eb]
  have cw : Covers [polyRegion (L.A j o')] s.wr := Lay.covers wj (VG.Proof.MlKem.Arm.sepB_bounds (VG.Proof.MlKem.Arm.sepB_symm hs)).2
  refine VG.Proof.MlKem.Arm.call_kept (k := VG.Proof.MlKem.Arm.kDec) VG.Proof.MlKem.Arm.kDec_ok (by decide +kernel) (rd := [⟨L.A i o, 384⟩]) (wr := [polyRegion (L.A j o')])
    ⟨by simp only [Decode12.inR, eB, State.withRegions_rd], by simp only [eF, State.withRegions_wr],
      by simp only [Decode12.inR, eB, eF]; exact Lay.disj hL hs,
      by simp only [Decode12.pb, VG.Proof.MlKem.Arm.view_r0, g0]; exact fa, by simp only [Decode12.pf, VG.Proof.MlKem.Arm.view_r1, g1]; exact fb⟩
    (VG.Proof.MlKem.Arm.covers_append (Lay.covers wi (VG.Proof.MlKem.Arm.sepB_bounds hs).2) (VG.Proof.MlKem.Arm.covers_wr cw)) cw fun s' hk hq => hQ s' hk ?_
  simp only [VG.Proof.MlKem.Arm.kDec, VG.Proof.MlKem.Arm.mkK, Decode12.D, eB, eF, State.withRegions_mem, State.callEntry_mem] at hq; exact hq

/-- `ByteEncode₁₂` of the polynomial at `(i, o)` into the 384 bytes at `(j, o')`. -/
theorem encode12L {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = L.ptr j + BitVec.ofNat 32 o')
    (hs : VG.Proof.MlKem.Arm.sepB L.sizes (i, o, 1024) (j, o', 384) = true) (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr)
    {f : VG.Spec.MlKem.Poly} (hf : PolyIs s.mem (L.A i o) f) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(j, o', 384)]) s s' → bytesAt s'.mem (L.A j o') 384 = encode12 f → Q s') :
    WP isa callEncode12 s Q := by
  obtain ⟨ea, fa⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds hs) (by decide)
  obtain ⟨eb, fb⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds (VG.Proof.MlKem.Arm.sepB_symm hs)) (by decide)
  have eF : Encode12.F (VG.Proof.MlKem.Arm.view s [polyRegion (L.A i o)] [⟨L.A j o', 384⟩]) = L.A i o := by
    simp only [Encode12.F, Encode12.pf, VG.Proof.MlKem.Arm.view_r0, g0, ea]
  have eO : Encode12.O (VG.Proof.MlKem.Arm.view s [polyRegion (L.A i o)] [⟨L.A j o', 384⟩]) = L.A j o' := by
    simp only [Encode12.O, Encode12.po, VG.Proof.MlKem.Arm.view_r1, g1, eb]
  have cw : Covers [⟨L.A j o', 384⟩] s.wr := Lay.covers wj (VG.Proof.MlKem.Arm.sepB_bounds (VG.Proof.MlKem.Arm.sepB_symm hs)).2
  refine VG.Proof.MlKem.Arm.call_kept (k := VG.Proof.MlKem.Arm.kEnc) VG.Proof.MlKem.Arm.kEnc_ok (by decide +kernel) (rd := [polyRegion (L.A i o)]) (wr := [⟨L.A j o', 384⟩])
    ⟨by simp only [eF, State.withRegions_rd], by simp only [Encode12.outR, eO, State.withRegions_wr],
      by simp only [Encode12.outR, eF, eO]; exact Lay.disj hL hs,
      by simp only [Encode12.pf, VG.Proof.MlKem.Arm.view_r0, g0]; exact fa, by simp only [Encode12.po, VG.Proof.MlKem.Arm.view_r1, g1]; exact fb,
      by rw [eF]; exact hf.1⟩
    (VG.Proof.MlKem.Arm.covers_append (Lay.covers wi (VG.Proof.MlKem.Arm.sepB_bounds hs).2) (VG.Proof.MlKem.Arm.covers_wr cw)) cw fun s' hk hq => hQ s' hk ?_
  simp only [VG.Proof.MlKem.Arm.kEnc, VG.Proof.MlKem.Arm.mkK, Encode12.E, eF, eO, State.withRegions_mem, State.callEntry_mem, hf.2] at hq; exact hq

/-! ## `vg_mlkem_compress_encode`, `vg_mlkem_decode_decompress` -/

def kCmp : Contract isa := VG.Proof.MlKem.Arm.mkK CompressEncode.Pre
  (fun s₀ s => bytesAt s.mem (CompressEncode.O s₀) (CompressEncode.len s₀) = CompressEncode.CE s₀)
  (VG.Proof.MlKem.Arm.regsEq [.r0, .r1, .r2, .r3])

theorem kCmp_ok : ∀ s, kCmp.pre s → ∃ t s', Exec isa Impl.MlKem.Arm.compressEncode s t s' ∧
    abiPreserved s s' ∧ kCmp.post s s' := VG.Proof.MlKem.Arm.mkK_ok fun _ hp => CompressEncode.correct hp

def kDcm : Contract isa := VG.Proof.MlKem.Arm.mkK Decompress.Pre (fun s₀ s => PolyIs s.mem (Decompress.F s₀) (Decompress.D s₀))
  (VG.Proof.MlKem.Arm.regsEq [.r0, .r1, .r2, .r3])

theorem kDcm_ok : ∀ s, kDcm.pre s → ∃ t s', Exec isa Impl.MlKem.Arm.decodeDecompress s t s' ∧
    abiPreserved s s' ∧ kDcm.post s s' := VG.Proof.MlKem.Arm.mkK_ok fun _ hp => Decompress.correct hp

theorem width_lt {d : Nat} (hd : d ∈ compressWidths) : d < 2 ^ 32 ∧ 32 * d < 2 ^ 32 := by
  rcases VG.Proof.MlKem.mem_compressWidths hd with rfl | rfl | rfl <;> decide

/-- `ByteEncode_d(Compress_d(f))` of the polynomial at `(i, o)` into the `32 d` bytes at `(j, o')`. -/
theorem compressL {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hL : L.Ok) {i o j o' d : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = BitVec.ofNat 32 d)
    (g2 : s.gpr .r2 = L.ptr j + BitVec.ofNat 32 o') (g3 : s.gpr .r3 = BitVec.ofNat 32 (32 * d))
    (hd : d ∈ compressWidths) (hs : VG.Proof.MlKem.Arm.sepB L.sizes (i, o, 1024) (j, o', 32 * d) = true)
    (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr) {f : VG.Spec.MlKem.Poly} (hf : PolyIs s.mem (L.A i o) f)
    {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(j, o', 32 * d)]) s s' → bytesAt s'.mem (L.A j o') (32 * d) = compressEncode d f →
      Q s') :
    WP isa callCompress s Q := by
  have ⟨d1, d2⟩ := VG.Proof.MlKem.Arm.width_lt hd
  have hd0 : 0 < 32 * d := by rcases VG.Proof.MlKem.mem_compressWidths hd with rfl | rfl | rfl <;> decide
  obtain ⟨ea, fa⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds hs) (by decide)
  obtain ⟨eb, fb⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds (VG.Proof.MlKem.Arm.sepB_symm hs)) hd0
  have eF : CompressEncode.F (VG.Proof.MlKem.Arm.view s [polyRegion (L.A i o)] [⟨L.A j o', 32 * d⟩]) = L.A i o := by
    simp only [CompressEncode.F, CompressEncode.pf, VG.Proof.MlKem.Arm.view_r0, g0, ea]
  have eO : CompressEncode.O (VG.Proof.MlKem.Arm.view s [polyRegion (L.A i o)] [⟨L.A j o', 32 * d⟩]) = L.A j o' := by
    simp only [CompressEncode.O, CompressEncode.po, VG.Proof.MlKem.Arm.view_r2, g2, eb]
  have eD : CompressEncode.dd (VG.Proof.MlKem.Arm.view s [polyRegion (L.A i o)] [⟨L.A j o', 32 * d⟩]) = d := by
    simp only [CompressEncode.dd, VG.Proof.MlKem.Arm.view_r1, g1, toNat_ofNat32 d1]
  have eL : CompressEncode.len (VG.Proof.MlKem.Arm.view s [polyRegion (L.A i o)] [⟨L.A j o', 32 * d⟩]) = 32 * d := by
    simp only [CompressEncode.len, VG.Proof.MlKem.Arm.view_r3, g3, toNat_ofNat32 d2]
  have cw : Covers [⟨L.A j o', 32 * d⟩] s.wr := Lay.covers wj (VG.Proof.MlKem.Arm.sepB_bounds (VG.Proof.MlKem.Arm.sepB_symm hs)).2
  refine VG.Proof.MlKem.Arm.call_kept (k := VG.Proof.MlKem.Arm.kCmp) VG.Proof.MlKem.Arm.kCmp_ok (by decide +kernel) (rd := [polyRegion (L.A i o)])
    (wr := [⟨L.A j o', 32 * d⟩])
    ⟨by simp only [eF, State.withRegions_rd], by simp only [CompressEncode.outR, eO, eL, State.withRegions_wr],
      by simp only [CompressEncode.outR, eF, eO, eL]; exact Lay.disj hL hs,
      by simp only [CompressEncode.pf, VG.Proof.MlKem.Arm.view_r0, g0]; exact fa, by rw [eL]; simp only [CompressEncode.po, VG.Proof.MlKem.Arm.view_r2, g2]; exact fb,
      by rw [eD]; exact hd, by rw [eL, eD], by rw [eF]; exact hf.1⟩
    (VG.Proof.MlKem.Arm.covers_append (Lay.covers wi (VG.Proof.MlKem.Arm.sepB_bounds hs).2) (VG.Proof.MlKem.Arm.covers_wr cw)) cw fun s' hk hq => hQ s' hk ?_
  simp only [VG.Proof.MlKem.Arm.kCmp, VG.Proof.MlKem.Arm.mkK, CompressEncode.CE, CompressEncode.fp, eF, eO, eL, eD, State.withRegions_mem,
    State.callEntry_mem, hf.2] at hq
  exact hq

/-- `Decompress_d(ByteDecode_d(·))` of the `32 d` bytes at `(i, o)` into the polynomial at `(j, o')`. -/
theorem decompressL {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hL : L.Ok) {i o j o' d : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = BitVec.ofNat 32 (32 * d))
    (g2 : s.gpr .r2 = BitVec.ofNat 32 d) (g3 : s.gpr .r3 = L.ptr j + BitVec.ofNat 32 o')
    (hd : d ∈ compressWidths) (hs : VG.Proof.MlKem.Arm.sepB L.sizes (i, o, 32 * d) (j, o', 1024) = true)
    (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(j, o', 1024)]) s s' →
      PolyIs s'.mem (L.A j o') (decodeDecompress d (bytesAt s.mem (L.A i o) (32 * d))) → Q s') :
    WP isa callDecompress s Q := by
  have ⟨d1, d2⟩ := VG.Proof.MlKem.Arm.width_lt hd
  have hd0 : 0 < 32 * d := by rcases VG.Proof.MlKem.mem_compressWidths hd with rfl | rfl | rfl <;> decide
  obtain ⟨ea, fa⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds hs) hd0
  obtain ⟨eb, fb⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds (VG.Proof.MlKem.Arm.sepB_symm hs)) (by decide)
  have eB : Decompress.B (VG.Proof.MlKem.Arm.view s [⟨L.A i o, 32 * d⟩] [polyRegion (L.A j o')]) = L.A i o := by
    simp only [Decompress.B, Decompress.pb, VG.Proof.MlKem.Arm.view_r0, g0, ea]
  have eF : Decompress.F (VG.Proof.MlKem.Arm.view s [⟨L.A i o, 32 * d⟩] [polyRegion (L.A j o')]) = L.A j o' := by
    simp only [Decompress.F, Decompress.pf, VG.Proof.MlKem.Arm.view_r3, g3, eb]
  have eD : Decompress.dd (VG.Proof.MlKem.Arm.view s [⟨L.A i o, 32 * d⟩] [polyRegion (L.A j o')]) = d := by
    simp only [Decompress.dd, VG.Proof.MlKem.Arm.view_r2, g2, toNat_ofNat32 d1]
  have eL : Decompress.len (VG.Proof.MlKem.Arm.view s [⟨L.A i o, 32 * d⟩] [polyRegion (L.A j o')]) = 32 * d := by
    simp only [Decompress.len, VG.Proof.MlKem.Arm.view_r1, g1, toNat_ofNat32 d2]
  have cw : Covers [polyRegion (L.A j o')] s.wr := Lay.covers wj (VG.Proof.MlKem.Arm.sepB_bounds (VG.Proof.MlKem.Arm.sepB_symm hs)).2
  refine VG.Proof.MlKem.Arm.call_kept (k := VG.Proof.MlKem.Arm.kDcm) VG.Proof.MlKem.Arm.kDcm_ok (by decide +kernel) (rd := [⟨L.A i o, 32 * d⟩])
    (wr := [polyRegion (L.A j o')])
    ⟨by simp only [Decompress.inR, eB, eL, State.withRegions_rd], by simp only [eF, State.withRegions_wr],
      by simp only [Decompress.inR, eB, eF, eL]; exact Lay.disj hL hs,
      by rw [eL]; simp only [Decompress.pb, VG.Proof.MlKem.Arm.view_r0, g0]; exact fa, by simp only [Decompress.pf, VG.Proof.MlKem.Arm.view_r3, g3]; exact fb,
      by rw [eD]; exact hd, by rw [eL, eD]⟩
    (VG.Proof.MlKem.Arm.covers_append (Lay.covers wi (VG.Proof.MlKem.Arm.sepB_bounds hs).2) (VG.Proof.MlKem.Arm.covers_wr cw)) cw fun s' hk hq => hQ s' hk ?_
  simp only [VG.Proof.MlKem.Arm.kDcm, VG.Proof.MlKem.Arm.mkK, Decompress.D, Decompress.bs, eB, eF, eL, eD, State.withRegions_mem,
    State.callEntry_mem] at hq
  exact hq

/-! ## `vg_mlkem_sample_ntt` -/

/-- What `vg_mlkem_sample_ntt` computes, with its loop bounded by 280
iterations: the return value says whether `SampleNTT` finished, and if it
did, `a` holds its result. -/
def kSample : Contract isa := VG.Proof.MlKem.Arm.mkK Sample.Pre
  (fun s₀ s => s.gpr .r0 = (if (sampleNTT 280 (Sample.B s₀)).isSome then 1 else 0) ∧
    ∀ a, sampleNTT 280 (Sample.B s₀) = some a → PolyIs s.mem (Sample.A s₀) a)
  (fun a b => a.sp = b.sp ∧ VG.Proof.MlKem.Arm.regsEq [.r0, .r1, .r2] a b ∧ Sample.B a = Sample.B b)

theorem kSample_ok : ∀ s, kSample.pre s → ∃ t s', Exec isa Impl.MlKem.Arm.sampleNTT s t s' ∧
    abiPreserved s s' ∧ kSample.post s s' :=
  VG.Proof.MlKem.Arm.mkK_ok fun s₀ hp => WP.mono (Sample.correct hp) fun s ⟨h1, h2, h0, hc⟩ => ⟨h1, h2, by
    by_cases hl : (Sample.Ls s₀ 280).length = 256
    · have e : sampleNTT 280 (Sample.B s₀) = some (VG.Proof.MlKem.toPoly (Sample.Ls s₀ 280)) :=
        VG.Proof.MlKem.sampleNTT_of_full (Nat.le_refl _) (by rw [VG.Proof.MlKem.n_eq]; exact hl)
      refine ⟨by rw [h0, ite_eq_left hl, e]; rfl, fun a ha => ?_⟩
      rw [e, Option.some.injEq] at ha; subst ha
      exact Sample.polyAt_toPoly (by rw [VG.Proof.MlKem.n_eq]; exact hl) hc
    · have e : sampleNTT 280 (Sample.B s₀) = none :=
        VG.Proof.MlKem.sampleNTT_none (by rw [VG.Proof.MlKem.n_eq]; exact hl)
      refine ⟨by rw [h0, ite_eq_right hl, e]; rfl, fun a ha => ?_⟩
      rw [e] at ha; cases ha⟩

theorem stackUse_sample : stackUse Impl.MlKem.Arm.sampleNTT = 8 := by decide +kernel

/-- `SampleNTT` of the seed at `(i, o)` into the polynomial at `(j, o')`,
with the working space at `(k, o'')`. -/
theorem sampleL {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hc : VG.Proof.MlKem.Arm.Ctx L s) {i o j o' k o'' : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = L.ptr j + BitVec.ofNat 32 o')
    (g2 : s.gpr .r2 = L.ptr k + BitVec.ofNat 32 o'')
    (s_ij : VG.Proof.MlKem.Arm.sepB L.sizes (i, o, 34) (j, o', 1024) = true) (s_ik : VG.Proof.MlKem.Arm.sepB L.sizes (i, o, 34) (k, o'', 2048) = true)
    (s_jk : VG.Proof.MlKem.Arm.sepB L.sizes (j, o', 1024) (k, o'', 2048) = true) (s_i1 : VG.Proof.MlKem.Arm.sepB L.sizes (i, o, 34) (1, 0, 8) = true)
    (s_j1 : VG.Proof.MlKem.Arm.sepB L.sizes (j, o', 1024) (1, 0, 8) = true) (s_k1 : VG.Proof.MlKem.Arm.sepB L.sizes (k, o'', 2048) (1, 0, 8) = true)
    (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr) (wk : L.buf k ∈ s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(j, o', 1024), (k, o'', 2048), (1, 0, 8)]) s s' →
      s'.gpr .r0 = (if (sampleNTT 280 (bytesAt s.mem (L.A i o) 34)).isSome then 1 else 0) →
      (∀ a, sampleNTT 280 (bytesAt s.mem (L.A i o) 34) = some a → PolyIs s'.mem (L.A j o') a) → Q s') :
    WP isa callSample s Q := by
  have hL := hc.ok
  obtain ⟨ea, fa⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds s_ij) (by decide)
  obtain ⟨eb, fb⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds s_jk) (by decide)
  obtain ⟨ec, fc⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds (VG.Proof.MlKem.Arm.sepB_symm s_ik)) (by decide)
  let V := VG.Proof.MlKem.Arm.view s [⟨L.A i o, 34⟩] [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩]
  have eS : Sample.SEED V = L.A i o := by simp only [V, Sample.SEED, Sample.pseed, VG.Proof.MlKem.Arm.view_r0, g0, ea]
  have eA : Sample.A V = L.A j o' := by simp only [V, Sample.A, Sample.pa, VG.Proof.MlKem.Arm.view_r1, g1, eb]
  have eC : Sample.S V = L.A k o'' := by simp only [V, Sample.S, Sample.pscr, VG.Proof.MlKem.Arm.view_r2, g2, ec]
  have eb8 : below V 8 = L.R 1 0 8 := hc.bel
  have eBv : Sample.B V = bytesAt s.mem (L.A i o) 34 := by
    show bytesAt s.mem (Sample.SEED V) 34 = _
    rw [eS]
  have cw : Covers [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩] s.wr :=
    VG.Proof.MlKem.Arm.covers_cons' (Lay.covers wj (VG.Proof.MlKem.Arm.sepB_bounds s_jk).2) (VG.Proof.MlKem.Arm.covers_cons' (Lay.covers wk (VG.Proof.MlKem.Arm.sepB_bounds (VG.Proof.MlKem.Arm.sepB_symm s_ik)).2)
      VG.Proof.MlKem.Arm.covers_nil')
  have hpre : Sample.Pre V := by
    refine ⟨hc.sp8, by simp only [V, eS, State.withRegions_rd], by simp only [V, eA, eC, State.withRegions_wr],
      by rw [eS, eA]; exact Lay.disj hL s_ij, by rw [eS, eC]; exact Lay.disj hL s_ik,
      by rw [eA, eC]; exact Lay.disj hL s_jk, by rw [eb8, eS]; exact Lay.disj hL (VG.Proof.MlKem.Arm.sepB_symm s_i1),
      by rw [eb8, eA]; exact Lay.disj hL (VG.Proof.MlKem.Arm.sepB_symm s_j1), by rw [eb8, eC]; exact Lay.disj hL (VG.Proof.MlKem.Arm.sepB_symm s_k1),
      by simp only [V, Sample.pseed, VG.Proof.MlKem.Arm.view_r0, g0]; exact fa, by simp only [V, Sample.pa, VG.Proof.MlKem.Arm.view_r1, g1]; exact fb,
      by simp only [V, Sample.pscr, VG.Proof.MlKem.Arm.view_r2, g2]; exact fc⟩
  refine WP.callF (k := VG.Proof.MlKem.Arm.kSample) VG.Proof.MlKem.Arm.kSample_ok hpre (VG.Proof.MlKem.Arm.covers_append (Lay.covers wi (VG.Proof.MlKem.Arm.sepB_bounds s_ij).2) (VG.Proof.MlKem.Arm.covers_wr cw))
    cw (by rw [VG.Proof.MlKem.Arm.stackUse_sample]; exact hc.sp8) fun s' hrd hwr hsp hf hcs hq => hQ s' ⟨hcs, hsp, hrd, hwr, ?_⟩ ?_ ?_
  · rw [VG.Proof.MlKem.Arm.stackUse_sample] at hf
    have : belowA s.sp 8 = L.R 1 0 8 := hc.bel
    rw [this] at hf; exact hf
  · have h1 : s'.gpr .r0 = _ := hq.1
    rw [eBv] at h1; exact h1
  · intro a ha
    have h2 : PolyIs s'.mem (Sample.A V) a := hq.2 a (by rw [eBv]; exact ha)
    rw [eA] at h2; exact h2

end VG.Proof.MlKem.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.Loops`. -/
section

/-!
# ML-KEM-768 on 32-bit ARM: copying bytes and zeroing a polynomial

`copy` copies bytes one at a time (`copy_ok`: the destination holds the
source's bytes, and nothing else changes), and `zeroPoly` stores zero to every
coefficient (`zeroPoly_ok`).
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Add (ptr_succ)

theorem setWidth_byte (b : Byte) : (b.setWidth 32).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, setWidth32_toNat]
  exact Nat.mod_eq_of_lt b.isLt

/-! ## `copy` -/

section
variable {s : State} {x y c : BitVec 32}

theorem copyBody_ok (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y) (h2 : s.gpr .r2 = c)
    (ir : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 1)
    (ow : InRegions s.wr (State.addr (y + BitVec.ofNat 32 0)) 1) :
    WP isa (.block VG.Impl.MlKem.Arm.copyBody) s fun s' =>
      s'.gpr .r0 = x + 1 ∧ s'.gpr .r1 = y + 1 ∧ s'.gpr .r2 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = s.mem.writeW (State.addr (y + BitVec.ofNat 32 0))
        (((s.mem (State.addr (x + BitVec.ofNat 32 0))).setWidth 32).setWidth 8) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  run_block [VG.Impl.MlKem.Arm.copyBody, h0, h1, h2, ir, ow, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

end

/-- After copying `k` bytes of `len` from `S` to `D`. -/
structure CopyInv (S D : BitVec 32) (len : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = S + BitVec.ofNat 32 (1 * k)
  r1 : s.gpr .r1 = D + BitVec.ofNat 32 (1 * k)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (1 * (len - k))
  cs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨State.addr D, len⟩] s₀.mem s.mem
  bytes : ∀ t < k, s.mem (State.addr D + BitVec.ofNat 64 t) = s₀.mem (State.addr S + BitVec.ofNat 64 t)

theorem copy_step {S D : BitVec 32} {len : Nat} {s₀ : State} (fS : S.toNat + len ≤ 2 ^ 32)
    (fD : D.toNat + len ≤ 2 ^ 32) (hlen : len < 2 ^ 32)
    (hd : (⟨State.addr S, len⟩ : Region).Disjoint ⟨State.addr D, len⟩)
    (cr : Covers [⟨State.addr S, len⟩] (s₀.rd ++ s₀.wr)) (cw : Covers [⟨State.addr D, len⟩] s₀.wr)
    {k : Nat} (hk : k < len) {s : State} (h : VG.Proof.MlKem.Arm.CopyInv S D len s₀ k s) :
    WP isa (.block VG.Impl.MlKem.Arm.copyBody) s fun s' => VG.Proof.MlKem.Arm.CopyInv S D len s₀ (k + 1) s' ∧ s'.z = decide (k + 1 = len) := by
  have eS : State.addr (S + BitVec.ofNat 32 (1 * k) + BitVec.ofNat 32 0) = State.addr S + BitVec.ofNat 64 k := by
    rw [addr_ptr _ _ _ (by omega)]; simp
  have eD : State.addr (D + BitVec.ofNat 32 (1 * k) + BitVec.ofNat 32 0) = State.addr D + BitVec.ofNat 64 k := by
    rw [addr_ptr _ _ _ (by omega)]; simp
  have cS : (⟨State.addr S, len⟩ : Region).Contains (State.addr S + BitVec.ofNat 64 k) 1 :=
    contains_off (by omega) (by omega)
  have cD : (⟨State.addr D, len⟩ : Region).Contains (State.addr D + BitVec.ofNat 64 k) 1 :=
    contains_off (by omega) (by omega)
  refine WP.mono (VG.Proof.MlKem.Arm.copyBody_ok h.r0 h.r1 h.r2 (by rw [eS, h.rd, h.wr]; exact cr _ _ ⟨_, List.mem_singleton_self _, cS⟩)
    (by rw [eD, h.wr]; exact cw _ _ ⟨_, List.mem_singleton_self _, cD⟩))
    fun s' ⟨r0, r1, r2, z, m, rd, wr, sp, cs⟩ => ⟨⟨?_, ?_, ?_, fun r hr => (cs r hr).trans (h.cs r hr),
      rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, ?_, fun t ht => ?_⟩, ?_⟩
  · rw [r0]; exact ptr_succ _ 1 k
  · rw [r1]; exact ptr_succ _ 1 k
  · rw [r2]; exact count_sub (k := 1) hk
  · rw [m, eD]; exact h.frame.writeW (List.mem_singleton_self _) _ cD
  · rw [m, eD, eS, VG.Proof.MlKem.Arm.setWidth_byte, byte_writeW8 _ _ (by omega) (by omega)]
    have hsrc : s.mem (State.addr S + BitVec.ofNat 64 k) = s₀.mem (State.addr S + BitVec.ofNat 64 k) :=
      h.frame _ fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd _ cS
    by_cases e : t = k
    · subst e; rw [ite_eq_left rfl, hsrc]
    · rw [ite_eq_right e]; exact h.bytes t (by omega)
  · rw [z]; exact count_z (k := 1) hk (by decide) (by omega)

/-- `len` bytes copied from `S` to `D`, with the pointers and the count set
up in `r0`–`r2`. -/
theorem copy_loop {S D : BitVec 32} {len : Nat} {s₀ : State} (fS : S.toNat + len ≤ 2 ^ 32)
    (fD : D.toNat + len ≤ 2 ^ 32) (hlen : len < 2 ^ 32) (hl0 : 0 < len)
    (hd : (⟨State.addr S, len⟩ : Region).Disjoint ⟨State.addr D, len⟩)
    (cr : Covers [⟨State.addr S, len⟩] (s₀.rd ++ s₀.wr)) (cw : Covers [⟨State.addr D, len⟩] s₀.wr)
    (h0 : s₀.gpr .r0 = S) (h1 : s₀.gpr .r1 = D) (h2 : s₀.gpr .r2 = BitVec.ofNat 32 len) :
    WP isa (.loop (.block VG.Impl.MlKem.Arm.copyBody) .ne) s₀ fun s =>
      (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧
      Frame [⟨State.addr D, len⟩] s₀.mem s.mem ∧ bytesAt s.mem (State.addr D) len = bytesAt s₀.mem (State.addr S) len :=
  wp_loop_ne (VG.Proof.MlKem.Arm.CopyInv S D len s₀) hl0 (fun k hk s h => VG.Proof.MlKem.Arm.copy_step fS fD hlen hd cr cw hk h)
    (fun s h => ⟨h.cs, h.rd, h.wr, h.sp, h.frame, bytesAt_eq (bytesAt_length _ _ _) fun t ht => by
      rw [h.bytes t ht, bytesAt_getElem]⟩)
    ⟨by rw [h0]; simp, by rw [h1]; simp, by rw [h2]; simp, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _,
      fun t ht => absurd ht (Nat.not_lt_zero t)⟩

theorem copy_setup {s : State} {sb db : Reg} {so dO len : Nat} (hsb : sb ∈ preserved ∧ sb ≠ .lr)
    (hdb : db ∈ preserved ∧ db ≠ .lr) (hse : encodable (BitVec.ofNat 32 so) = true)
    (hde : encodable (BitVec.ofNat 32 dO) = true) (hle : encodable (BitVec.ofNat 32 len) = true) :
    WP isa (.block [ptrTo .r0 sb so, ptrTo .r1 db dO, .mov .r2 (.imm (BitVec.ofNat 32 len))]) s fun s' =>
      VG.Proof.MlKem.Arm.Only s s' ∧ s'.gpr .r0 = s.gpr sb + BitVec.ofNat 32 so ∧ s'.gpr .r1 = s.gpr db + BitVec.ofNat 32 dO ∧
      s'.gpr .r2 = BitVec.ofNat 32 len := by
  obtain ⟨-, -, -, -, -⟩ := VG.Proof.MlKem.Arm.pres_ne hsb.1 hsb.2
  obtain ⟨n0, -, -, -, -⟩ := VG.Proof.MlKem.Arm.pres_ne hdb.1 hdb.2
  run_block [ptrTo, hse, hde, hle, n0]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, m2, -, -⟩ := VG.Proof.MlKem.Arm.pres_ne hr hl
  simp only [m0, m1, m2, ite_false]

/-- `copy`: `len` bytes from offset `so` of buffer `i` (in `sb`) to offset
`dO` of buffer `j` (in `db`). -/
theorem copyL {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hL : L.Ok) {sb db : Reg} {so dO len i j : Nat}
    (hsb : sb ∈ preserved ∧ sb ≠ .lr) (hdb : db ∈ preserved ∧ db ≠ .lr)
    (gs : s.gpr sb = L.ptr i) (gd : s.gpr db = L.ptr j) (hse : encodable (BitVec.ofNat 32 so) = true)
    (hde : encodable (BitVec.ofNat 32 dO) = true) (hle : encodable (BitVec.ofNat 32 len) = true)
    (hlen : len < 2 ^ 32) (hl0 : 0 < len) (hs : VG.Proof.MlKem.Arm.sepB L.sizes (i, so, len) (j, dO, len) = true)
    (ri : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr) :
    WP isa (copy sb so db dO len) s fun s' =>
      Kept (L.RL [(j, dO, len)]) s s' ∧ bytesAt s'.mem (L.A j dO) len = bytesAt s.mem (L.A i so) len := by
  obtain ⟨ea, fa⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds hs) hl0
  obtain ⟨eb, fb⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds (VG.Proof.MlKem.Arm.sepB_symm hs)) hl0
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.copy_setup hsb hdb hse hde hle) fun s₁ ⟨o₁, g0, g1, g2⟩ => ?_)
  rw [gs] at g0; rw [gd] at g1
  refine WP.mono (VG.Proof.MlKem.Arm.copy_loop fa fb hlen hl0 (by rw [ea, eb]; exact Lay.disj hL hs)
    (by rw [ea, o₁.rd, o₁.wr]; exact Lay.covers ri (VG.Proof.MlKem.Arm.sepB_bounds hs).2)
    (by rw [eb, o₁.wr]; exact Lay.covers wj (VG.Proof.MlKem.Arm.sepB_bounds (VG.Proof.MlKem.Arm.sepB_symm hs)).2) g0 g1 g2)
    fun s' ⟨cs, rd, wr, sp, fr, hb⟩ => ⟨?_, ?_⟩
  · refine (o₁.kept _).trans ⟨fun r hr _ => cs r hr, sp, rd, wr, ?_⟩
    rw [eb] at fr; exact fr
  · rw [eb, ea, o₁.mem] at hb; exact hb

/-! ## `zeroPoly` -/

section
variable {s : State} {x c : BitVec 32}

theorem zeroBody_ok (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = 0) (h2 : s.gpr .r2 = c)
    (ow : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4) :
    WP isa (.block VG.Impl.MlKem.Arm.zeroBody) s fun s' =>
      s'.gpr .r0 = x + 4 ∧ s'.gpr .r1 = 0 ∧ s'.gpr .r2 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = s.mem.writeW (State.addr (x + BitVec.ofNat 32 0)) (0 : BitVec 32) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  run_block [VG.Impl.MlKem.Arm.zeroBody, h0, h1, h2, ow, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

end

/-- After zeroing `k` coefficients of the polynomial at `P`. -/
structure ZeroInv (P : BitVec 32) (s₀ : State) (k : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = P + BitVec.ofNat 32 (4 * k)
  r1 : s.gpr .r1 = 0
  r2 : s.gpr .r2 = BitVec.ofNat 32 (1 * (256 - k))
  cs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [polyRegion (State.addr P)] s₀.mem s.mem
  zero : ∀ t < 256, coeffAt s.mem (State.addr P) t = if t < k then 0 else coeffAt s₀.mem (State.addr P) t

theorem zero_step {P : BitVec 32} {s₀ : State} (fP : P.toNat + 1024 ≤ 2 ^ 32)
    (cw : Covers [polyRegion (State.addr P)] s₀.wr) {k : Nat} (hk : k < 256) {s : State} (h : VG.Proof.MlKem.Arm.ZeroInv P s₀ k s) :
    WP isa (.block VG.Impl.MlKem.Arm.zeroBody) s fun s' => VG.Proof.MlKem.Arm.ZeroInv P s₀ (k + 1) s' ∧ s'.z = decide (k + 1 = 256) := by
  have eP : State.addr (P + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0) = coeffAddr (State.addr P) k :=
    addr_coeff fP (by omega) hk
  have cP : (polyRegion (State.addr P)).Contains (coeffAddr (State.addr P) k) 4 :=
    coeff_contains _ (by rw [VG.Proof.MlKem.n_eq]; exact hk)
  refine WP.mono (VG.Proof.MlKem.Arm.zeroBody_ok h.r0 h.r1 h.r2 (by rw [eP, h.wr]; exact cw _ _ ⟨_, List.mem_singleton_self _, cP⟩))
    fun s' ⟨r0, r1, r2, z, m, rd, wr, sp, cs⟩ => ⟨⟨?_, r1, ?_, fun r hr => (cs r hr).trans (h.cs r hr),
      rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, ?_, ?_⟩, ?_⟩
  · rw [r0]; exact ptr_succ _ 4 k
  · rw [r2]; exact count_sub (k := 1) hk
  · rw [m, eP]; exact h.frame.writeW (List.mem_singleton_self _) _ cP
  · rw [m, eP]; exact coeff_one hk h.zero rfl
  · rw [z]; exact count_z (k := 1) hk (by decide) (by decide)

theorem zeroPoly_ok {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hc : VG.Proof.MlKem.Arm.Ctx L s) {off : Nat} (hoff : off + 1024 ≤ 32768)
    (he : encodable (BitVec.ofNat 32 off) = true) :
    WP isa (zeroPoly off) s fun s' => Kept (L.RL [(0, off, 1024)]) s s' ∧ PolyIs s'.mem (L.A 0 off) VG.Spec.MlKem.zero := by
  have ea := hc.addr (o := off) (by omega)
  have fa := hc.fitO (o := off) (l := 1024) hoff (by decide)
  have hfin : ∀ s', VG.Proof.MlKem.Arm.ZeroInv (L.ptr 0 + BitVec.ofNat 32 off) s 256 s' →
      Kept (L.RL [(0, off, 1024)]) s s' ∧ PolyIs s'.mem (L.A 0 off) VG.Spec.MlKem.zero := fun s' h => by
    refine ⟨⟨fun r hr _ => h.cs r hr, h.sp, h.rd, h.wr, ?_⟩, ?_⟩
    · have := h.frame; rw [ea] at this; exact this
    · refine polyIs_of_coeffAt fun t ht => ?_
      show coeffAt s'.mem (State.addr (L.ptr 0) + BitVec.ofNat 64 off) t = _
      rw [← ea, h.zero t (by rw [VG.Proof.MlKem.n_eq] at ht; exact ht),
        ite_eq_left (by rw [VG.Proof.MlKem.n_eq] at ht; exact ht), VG.Spec.MlKem.zero,
        getElem!_pos (Vector.replicate n (0 : Zq)) t ht, Vector.getElem_replicate]
      rfl
  refine WP.seq ?_
  have e7 := hc.r7
  run_block [ptrTo, he, e7]
  refine wp_loop_ne (VG.Proof.MlKem.Arm.ZeroInv (L.ptr 0 + BitVec.ofNat 32 off) s) (N := 256) (by decide)
    (fun k hk s h => VG.Proof.MlKem.Arm.zero_step fa (by rw [ea]; exact hc.cs hoff) hk h) hfin ?_
  refine ⟨by simp, rfl, rfl, fun r hr => ?_, rfl, rfl, rfl, Frame.refl _ _, fun t _ => by simp⟩
  have : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 := by revert r hr; decide
  simp [this.1, this.2.1, this.2.2]

end VG.Proof.MlKem.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.Prf`. -/
section

/-!
# ML-KEM on 32-bit ARM: sampling with `PRF` and `SamplePolyCBD`

`K.prfLoop withNtt N₀ N₁` writes `SamplePolyCBD₂(PRF₂(σ, N))` (its NTT if
`withNtt`) to polynomial `k + N` for `N₀ ≤ N < N₁` (`prfLoop_ok`), with `σ` at
offset 920 of `scratch`, and changes only the regions of `prfW`.
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt squeezeFrom rates)

/-! ## What changes, but for some callee-saved registers -/

/-- `s'` differs from `s` only in memory within `rs`, in registers that are
not callee-saved (or are `lr`), and in the callee-saved registers `xs`. -/
structure KeptX (xs : List Reg) (rs : List Region) (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, r ≠ .lr → r ∉ xs → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame rs s.mem s'.mem

theorem Kept.x {rs : List Region} {s s' : State} (h : Kept rs s s') (xs : List Reg) : VG.Proof.MlKem.Arm.KeptX xs rs s s' :=
  ⟨fun r hr hl _ => h.cs r hr hl, h.sp, h.rd, h.wr, h.frame⟩

theorem KeptX.trans {xs : List Reg} {rs : List Region} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.MlKem.Arm.KeptX xs rs s₁ s₂)
    (h₂ : VG.Proof.MlKem.Arm.KeptX xs rs s₂ s₃) : VG.Proof.MlKem.Arm.KeptX xs rs s₁ s₃ :=
  ⟨fun r hr h hx => by rw [h₂.cs r hr h hx, h₁.cs r hr h hx], by rw [h₂.sp, h₁.sp], by rw [h₂.rd, h₁.rd],
    by rw [h₂.wr, h₁.wr], h₁.frame.trans h₂.frame⟩

theorem KeptX.sub {xs : List Reg} {rs rs' : List Region} {s s' : State} (h : VG.Proof.MlKem.Arm.KeptX xs rs s s')
    (hs : ∀ r ∈ rs, ∃ r' ∈ rs', Region.Sub r r') : VG.Proof.MlKem.Arm.KeptX xs rs' s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, h.frame.sub hs⟩

theorem KeptX.mono {xs : List Reg} {rs rs' : List Region} {s s' : State} (h : VG.Proof.MlKem.Arm.KeptX xs rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs') : VG.Proof.MlKem.Arm.KeptX xs rs' s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, h.frame.mono hs⟩

theorem KeptX.weaken {xs ys : List Reg} {rs : List Region} {s s' : State} (h : VG.Proof.MlKem.Arm.KeptX xs rs s s')
    (hx : ∀ x ∈ xs, x ∈ ys) : VG.Proof.MlKem.Arm.KeptX ys rs s s' :=
  ⟨fun r hr hl hy => h.cs r hr hl fun hm => hy (hx r hm), h.sp, h.rd, h.wr, h.frame⟩

theorem KeptX.monoL {L : VG.Proof.MlKem.Arm.Lay} {xs : List Reg} {W W' : List (Nat × Nat × Nat)} {s s' : State}
    (h : VG.Proof.MlKem.Arm.KeptX xs (L.RL W) s s') (hs : ∀ w ∈ W, w ∈ W') : VG.Proof.MlKem.Arm.KeptX xs (L.RL W') s s' :=
  h.mono fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact List.mem_map.mpr ⟨w, hs w hw, rfl⟩

theorem Only.x {s s' : State} (h : VG.Proof.MlKem.Arm.Only s s') (xs : List Reg) (rs : List Region) : VG.Proof.MlKem.Arm.KeptX xs rs s s' :=
  (h.kept rs).x xs

theorem KeptX.ctx {L : VG.Proof.MlKem.Arm.Lay} {xs : List Reg} {rs : List Region} {s s' : State} (h : VG.Proof.MlKem.Arm.KeptX xs rs s s')
    (h7 : Reg.r7 ∉ xs) (hc : VG.Proof.MlKem.Arm.Ctx L s) : VG.Proof.MlKem.Arm.Ctx L s' :=
  ⟨hc.ok, hc.sz0, hc.sz1, hc.len, by rw [h.cs .r7 (by decide) (by decide) h7, hc.r7], by rw [h.sp]; exact hc.sp8,
    by rw [h.sp]; exact hc.sp, by rw [h.wr]; exact hc.cw⟩

/-- A region of `scratch` apart from the region `w` of `scratch` or of the stack. -/
def sep0 (o l : Nat) (w : Nat × Nat × Nat) : Bool :=
  (w.1 == 0 && decide (w.2.1 + w.2.2 ≤ 32768) && (decide (o + l ≤ w.2.1) || decide (w.2.1 + w.2.2 ≤ o))) ||
    (w.1 == 1 && decide (w.2.1 + w.2.2 ≤ 8))

theorem Ctx.sepAll0 {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hc : VG.Proof.MlKem.Arm.Ctx L s) {o l : Nat} (hl : o + l ≤ 32768)
    {W : List (Nat × Nat × Nat)} (h : W.all (VG.Proof.MlKem.Arm.sep0 o l) = true) : VG.Proof.MlKem.Arm.sepAll L.sizes (0, o, l) W = true := by
  refine List.all_eq_true.mpr fun w hw => ?_
  have h' := List.all_eq_true.mp h w hw
  obtain ⟨i, a, b⟩ := w
  simp only [VG.Proof.MlKem.Arm.sep0, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h'
  rcases h' with ⟨⟨h1, h2⟩, h3⟩ | ⟨h1, h2⟩
  · subst h1; exact hc.sep00 hl h2 h3
  · subst h1; exact hc.sep01 hl h2

/-- A part of `scratch` inside a bigger one. -/
theorem Ctx.sub0 {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hc : VG.Proof.MlKem.Arm.Ctx L s) {a l b l' : Nat} (h₁ : b ≤ a) (h₂ : a + l ≤ b + l')
    (h₃ : b + l' ≤ 32768) : Region.Sub (L.R 0 a l) (L.R 0 b l') := by
  have := hc.fit
  have := addr_toNat (L.ptr 0)
  intro x hx
  simp only [Region.Contains] at hx ⊢
  bv_omega

/-- A separation decided with a `scratch` of 32 KiB holds for a bigger one. -/
theorem sepB_scr {r : List Nat} {s : Nat} {a b : Nat × Nat × Nat} (h : VG.Proof.MlKem.Arm.sepB (32768 :: r) a b = true)
    (hs : 32768 ≤ s) : VG.Proof.MlKem.Arm.sepB (s :: r) a b = true := by
  obtain ⟨i, o, l⟩ := a
  obtain ⟨j, o', l'⟩ := b
  simp only [VG.Proof.MlKem.Arm.sepB, List.length_cons, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨⟨⟨⟨h1, h2⟩, ?_⟩, ?_⟩, h5⟩
  · cases i <;> simp only [List.getD_cons_zero, List.getD_cons_succ] at h3 ⊢ <;> omega
  · cases j <;> simp only [List.getD_cons_zero, List.getD_cons_succ] at h4 ⊢ <;> omega

theorem sepAll_scr {r : List Nat} {s : Nat} {a : Nat × Nat × Nat} {W : List (Nat × Nat × Nat)}
    (h : VG.Proof.MlKem.Arm.sepAll (32768 :: r) a W = true) (hs : 32768 ≤ s) : VG.Proof.MlKem.Arm.sepAll (s :: r) a W = true :=
  List.all_eq_true.mpr fun w hw => VG.Proof.MlKem.Arm.sepB_scr (List.all_eq_true.mp h w hw) hs

/-- `w` inside `w'`, a region of `scratch` or of the stack. -/
def subB0 (w w' : Nat × Nat × Nat) : Bool :=
  w.1 == w'.1 && decide (w'.2.1 ≤ w.2.1) && decide (w.2.1 + w.2.2 ≤ w'.2.1 + w'.2.2) &&
    ((w'.1 == 0 && decide (w'.2.1 + w'.2.2 ≤ 32768)) || (w'.1 == 1 && decide (w'.2.1 + w'.2.2 ≤ 8)))

theorem Lay.R_sub_R {L : VG.Proof.MlKem.Arm.Lay} (hL : L.Ok) {i a l b l' : Nat} (hi : i < L.sizes.length) (h₁ : b ≤ a)
    (h₂ : a + l ≤ b + l') (h₃ : b + l' ≤ L.size i) : Region.Sub (L.R i a l) (L.R i b l') := by
  have hf : (L.ptr i).toNat + L.size i ≤ 2 ^ 32 := hL.fit i hi
  have := addr_toNat (L.ptr i)
  have := h₃
  intro x hx
  simp only [Region.Contains] at hx ⊢
  bv_omega

theorem Ctx.subL {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hc : VG.Proof.MlKem.Arm.Ctx L s) {W W' : List (Nat × Nat × Nat)}
    (h : W.all (fun w => W'.any (VG.Proof.MlKem.Arm.subB0 w)) = true) : ∀ r ∈ L.RL W, ∃ r' ∈ L.RL W', Region.Sub r r' := by
  intro r hr
  obtain ⟨⟨i, a, l⟩, hw, rfl⟩ := List.mem_map.mp hr
  obtain ⟨⟨i', b, l'⟩, hw', hs⟩ := List.any_eq_true.mp (List.all_eq_true.mp h _ hw)
  simp only [VG.Proof.MlKem.Arm.subB0, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨e, h₁⟩, h₂⟩, h₃⟩ := hs
  subst e
  refine ⟨L.R i b l', List.mem_map.mpr ⟨_, hw', rfl⟩, Lay.R_sub_R hc.ok ?_ h₁ h₂ ?_⟩
  · have := hc.len; rcases h₃ with ⟨e, -⟩ | ⟨e, -⟩ <;> subst e <;> omega
  · rcases h₃ with ⟨e, h⟩ | ⟨e, h⟩ <;> subst e
    · exact Nat.le_trans h hc.sz0
    · rw [hc.sz1]; exact h

theorem KeptX.subL {L : VG.Proof.MlKem.Arm.Lay} {xs : List Reg} {W W' : List (Nat × Nat × Nat)} {s₀ s s' : State} (hc : VG.Proof.MlKem.Arm.Ctx L s₀)
    (h : VG.Proof.MlKem.Arm.KeptX xs (L.RL W) s s') (hb : W.all (fun w => W'.any (VG.Proof.MlKem.Arm.subB0 w)) = true) : VG.Proof.MlKem.Arm.KeptX xs (L.RL W') s s' :=
  h.sub (hc.subL hb)

/-! ## Addresses -/

/-- `w` inside `w'`. -/
def inB (w w' : Nat × Nat × Nat) : Bool :=
  w.1 == w'.1 && decide (w'.2.1 ≤ w.2.1) && decide (w.2.1 + w.2.2 ≤ w'.2.1 + w'.2.2)

/-- Arithmetic on the offsets in `scratch`, with the bounds on `k` of the
`KemLay.WF` in the context, if any. -/
macro "offs" : tactic => `(tactic| (
  (try have := (‹KemLay.WF _›).k1)
  (try have := (‹KemLay.WF _›).k4)
  (try have := (‹KemLay.WF _›).du)
  (try have := (‹KemLay.WF _›).dv)
  (try simp only [oPoly, oPrf, KemLay.oNtt, oSeed, oSigma, KemLay.oAcc, KemLay.oTmp, KemLay.oAhat, KemLay.oSample,
    oK, oKbar, oMsg, oHek, KemLay.oCt, oWork, oSave, oExtra, oG, oCin, KemLay.ekLen, KemLay.ctLen, KemLay.uLen,
    KemLay.vLen])
  omega))

theorem enc_le9 : ∀ n, n ≤ 9 → encodable (BitVec.ofNat 32 n) = true := by decide

/-- Decides that an immediate is encodable: by evaluation, or, for an offset
or a count that depends on the parameter set, from the bounds of its
`KemLay.WF`. -/
macro "kenc" : tactic => `(tactic| first
  | decide
  | exact enc_le9 _ (by have := (‹KemLay.WF _›).k4; omega)
  | exact (‹KemLay.WF _›).enc (by omega))

/-- Decides a fact about offsets and regions: by evaluation, or, for one that
depends on the parameter set (of the `KemLay.WF` in the context), by `omega`
on the offsets. -/
macro "kdecide" : tactic => `(tactic| first
  | decide
  | (
  (try have := (‹KemLay.WF _›).k1)
  (try have := (‹KemLay.WF _›).k4)
  (try have := (‹KemLay.WF _›).du)
  (try have := (‹KemLay.WF _›).dv)
  (try simp only [List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.all_append, List.any_append, sep0,
    subB0, inB, sepB, sepAll, List.length_cons, List.length_nil, List.getD_cons_zero, List.getD_cons_succ,
    oPoly, oPrf, KemLay.oNtt, oSeed, oSigma, KemLay.oAcc, KemLay.oTmp, KemLay.oAhat, KemLay.oSample, oK,
    oKbar, oMsg, oHek, KemLay.oCt, oWork, oSave, oExtra, oG, oCin, KemLay.ekLen, KemLay.ctLen, KemLay.uLen,
    KemLay.vLen, KemLay.dkLen, Bool.and_true, Bool.or_false,
    Bool.true_and, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq, true_and, and_true, not_true_eq_false, not_false_eq_true, false_or, or_false, true_or,
    or_true])
  omega))

theorem slot_eq (p : BitVec 32) {N off : Nat} (_h : off + 1024 * N < 2 ^ 32) :
    p + BitVec.ofNat 32 N <<< 10 + BitVec.ofNat 32 off = p + BitVec.ofNat 32 (off + 1024 * N) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem setWidth8_ofNat {N : Nat} (h : N < 2 ^ 32) : (BitVec.ofNat 32 N).setWidth 8 = BitVec.ofNat 8 N := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-! ## Counters -/

theorem count_ok {s : State} {c : Reg} {n k : Nat} (hk : k + 1 < 2 ^ 32)
    (hn : n < 2 ^ 32) (hen : encodable (BitVec.ofNat 32 n) = true) (h : s.gpr c = BitVec.ofNat 32 k) :
    WP isa (.block (count c n)) s fun s' =>
      VG.Proof.MlKem.Arm.KeptX [c] [] s s' ∧ s'.gpr c = BitVec.ofNat 32 (k + 1) ∧ s'.z = decide (k + 1 = n) := by
  have e1 : encodable (BitVec.ofNat 32 1) = true := by decide
  run_block [count, hen, e1, h]
  refine ⟨⟨fun r _ _ hx => ?_, rfl, rfl, rfl, Frame.refl _ _⟩, by rw [BitVec.ofNat_add]; rfl, ?_⟩
  · show (if r = c then _ else s.gpr r) = s.gpr r
    exact ite_eq_right (fun e : r = c => hx (by rw [e]; exact List.mem_singleton_self _))
  · rw [show BitVec.ofNat 32 k + 1 = BitVec.ofNat 32 (k + 1) by rw [BitVec.ofNat_add]; rfl, cmp_z _ _ hn,
      toNat_ofNat32 hk]

/-! ## One `PRF` -/

/-- Polynomial `k + N`: `SamplePolyCBD₂(PRF₂(σ, N))`, or its NTT. -/
def prfOut (withNtt : Bool) (σ : List Byte) (N : Nat) : VG.Spec.MlKem.Poly :=
  if withNtt then ntt (VG.Proof.MlKem.cbd σ N) else VG.Proof.MlKem.cbd σ N

/-- What one `PRF` changes. -/
abbrev prfW (K : KemLay) (N : Nat) : List (Nat × Nat × Nat) :=
  [(0, 0, 200), (0, 200, 640), (1, 0, 8), (0, 952, 1), (0, 1024, 128), (0, oPoly (K.k + N), 1024), (0, K.oNtt, 1024)]

theorem bytes_one (m : Mem) (p : Addr) : bytesAt m p 1 = [m p] := by
  simp [bytesAt]

theorem strb9_ok {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hc : VG.Proof.MlKem.Arm.Ctx L s) {N : Nat} (hN : N < 2 ^ 32)
    (h9 : s.gpr .r9 = BitVec.ofNat 32 N) :
    WP isa (.block [.strb .r9 .r7 (oSigma + 32)]) s fun s₁ =>
      VG.Proof.MlKem.Arm.KeptX [] (L.RL [(0, 952, 1)]) s s₁ ∧ s₁.mem = s.mem.writeW (L.A 0 952) (BitVec.ofNat 8 N) := by
  have e952 : State.addr (s.gpr .r7 + BitVec.ofNat 32 (oSigma + 32)) = L.A 0 952 := by
    rw [hc.r7]; exact hc.addr (by decide)
  have i952 : InRegions s.wr (State.addr (s.gpr .r7 + BitVec.ofNat 32 (oSigma + 32))) 1 := by
    rw [e952]; exact hc.cs (o := 952) (l := 1) (by decide) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  have ho : oSigma + 32 < 4096 := by decide
  run_block [i952, ho]
  refine ⟨⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, ?_⟩, ?_⟩
  · show Frame _ s.mem (s.mem.writeW _ _)
    rw [e952]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · show s.mem.writeW _ _ = _
    rw [e952, h9, VG.Proof.MlKem.Arm.setWidth8_ofNat hN]

theorem rate136 : 136 ∈ rates := by decide

section
variable {K : KemLay} (hK : K.WF)
include hK

theorem cbdArgs_ok {s : State} {P : BitVec 32} {N : Nat} (h7 : s.gpr .r7 = P) (h9 : s.gpr .r9 = BitVec.ofNat 32 N) :
    WP isa (.block (ptrTo .r0 .r7 oPrf :: slotAt .r1 .r9 (oPoly K.k))) s fun s' => VG.Proof.MlKem.Arm.Only s s' ∧
      s'.gpr .r0 = P + BitVec.ofNat 32 oPrf ∧ s'.gpr .r1 = P + BitVec.ofNat 32 N <<< 10 + BitVec.ofNat 32 (oPoly K.k) := by
  have e1 : encodable (BitVec.ofNat 32 oPrf) = true := by decide
  have e2 := VG.Proof.MlKem.Arm.enc_poly K.k (by have := hK.k4; omega)
  run_block [ptrTo, slotAt, e1, e2, h7, h9]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, -, -, -⟩ := VG.Proof.MlKem.Arm.pres_ne hr hl
  simp only [m0, m1, ite_false]

theorem nttArgs_ok {s : State} {P : BitVec 32} {N : Nat} (h7 : s.gpr .r7 = P) (h9 : s.gpr .r9 = BitVec.ofNat 32 N) :
    WP isa (.block (slotAt .r0 .r9 (oPoly K.k) ++ [ptrTo .r1 .r7 K.oNtt])) s fun s' => VG.Proof.MlKem.Arm.Only s s' ∧
      s'.gpr .r0 = P + BitVec.ofNat 32 N <<< 10 + BitVec.ofNat 32 (oPoly K.k) ∧
      s'.gpr .r1 = P + BitVec.ofNat 32 K.oNtt := by
  have e1 := VG.Proof.MlKem.Arm.enc_poly (3 * K.k + 7) (by have := hK.k4; omega)
  have e2 := VG.Proof.MlKem.Arm.enc_poly K.k (by have := hK.k4; omega)
  run_block [ptrTo, slotAt, e1, e2, h7, h9]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, -, -, -⟩ := VG.Proof.MlKem.Arm.pres_ne hr hl
  simp only [m0, m1, ite_false]

theorem prfBody_ok {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hc : VG.Proof.MlKem.Arm.Ctx L s) (withNtt : Bool) {N₁ N : Nat} (hN : N < N₁)
    (hN₁ : N₁ ≤ 2 * K.k + 1) (h9 : s.gpr .r9 = BitVec.ofNat 32 N) {σ : List Byte}
    (hσ : bytesAt s.mem (L.A 0 oSigma) 32 = σ) :
    WP isa (K.prfBody withNtt N₁) s fun s' => VG.Proof.MlKem.Arm.KeptX [.r9] (L.RL (VG.Proof.MlKem.Arm.prfW K N)) s s' ∧
      s'.gpr .r9 = BitVec.ofNat 32 (N + 1) ∧ s'.z = decide (N + 1 = N₁) ∧
      PolyIs s'.mem (L.A 0 (oPoly (K.k + N))) (VG.Proof.MlKem.Arm.prfOut withNtt σ N) := by
  have hL := hc.ok
  have k4 := hK.k4
  have eo : oPoly (K.k + N) = oPoly K.k + 1024 * N := by unfold oPoly; omega
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.strb9_ok hc (by omega) h9) fun s₁ ⟨k₁, m₁⟩ => ?_)
  have hc₁ := k₁.ctx (by decide) hc
  have g9₁ : s₁.gpr .r9 = BitVec.ofNat 32 N := by rw [k₁.cs .r9 (by decide) (by decide) (by decide), h9]
  have bσ : bytesAt s₁.mem (L.A 0 920) 33 = σ ++ [BitVec.ofNat 8 N] := by
    show bytesAt s₁.mem (State.addr (L.ptr 0) + BitVec.ofNat 64 920) (32 + 1) = _
    rw [bytesAt_add, VG.Proof.MlKem.Arm.bytes_one, add_ofNat_add]
    congr 1
    · rw [← hσ]
      exact Lay.bytes_keep hL k₁.frame (hc.sepAll0 (by decide) (by decide)) (by decide)
    · rw [m₁, VG.WriteBytes.writeW8_apply, ite_eq_left rfl]
  have hin : ∀ p ∈ [(⟨.r7, oSigma, 33⟩ : Piece)], VG.Proof.MlKem.Arm.PieceOk L (fun _ => 0) s₁ false p := by
    intro p hp; rw [List.mem_singleton] at hp; subst hp
    exact ⟨⟨by decide, by decide⟩, hc₁.r7, by decide, by decide, by decide, by decide,
      hc₁.sepAll0 (by decide) (by decide), VG.Proof.MlKem.Arm.mem_rd_wr hc₁.buf0⟩
  have hout : ∀ p ∈ [(⟨.r7, oPrf, 128⟩ : Piece)], VG.Proof.MlKem.Arm.PieceOk L (fun _ => 0) s₁ true p := by
    intro p hp; rw [List.mem_singleton] at hp; subst hp
    exact ⟨⟨by decide, by decide⟩, hc₁.r7, by decide, by decide, by decide, by decide,
      hc₁.sepAll0 (by decide) (by decide), hc₁.buf0⟩
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.hash_ok (idx := fun _ => 0) VG.Proof.MlKem.Arm.rate136 (by decide) (by decide) (by decide) hc₁
    (List.cons_ne_nil _ _) hin hout (List.pairwise_singleton _ _)) fun s₂ ⟨k₂, o₂⟩ => ?_)
  have hc₂ := hc₁.kept k₂
  have g9₂ : s₂.gpr .r9 = BitVec.ofNat 32 N := by rw [k₂.cs .r9 (by decide) (by decide), g9₁]
  have prfB : bytesAt s₂.mem (L.A 0 oPrf) 128 = prf 2 σ (BitVec.ofNat 8 N) := by
    have := o₂.1
    simp only [Lay.pb, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] at this
    rw [bσ] at this
    rw [this, VG.Proof.MlKem.prf_eq]; rfl
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.cbdArgs_ok hK hc₂.r7 g9₂) fun s₃ ⟨o₃, g0, g1⟩ => ?_)
  rw [VG.Proof.MlKem.Arm.slot_eq _ (by offs), ← eo] at g1
  have hc₃ := hc₂.only o₃
  refine WP.seq (VG.Proof.MlKem.Arm.cbd2L hL g0 g1 (hc.sep00 (by offs) (by offs) (by offs))
    (VG.Proof.MlKem.Arm.mem_rd_wr hc₃.buf0) hc₃.buf0 fun s₄ k₄ p₄ => ?_)
  rw [o₃.mem, prfB] at p₄
  have hc₄ := hc₃.kept k₄
  have g9₄ : s₄.gpr .r9 = BitVec.ofNat 32 N := by
    rw [k₄.cs .r9 (by decide) (by decide), o₃.cs .r9 (by decide) (by decide), g9₂]
  have fin : ∀ s₅, VG.Proof.MlKem.Arm.KeptX [.r9] (L.RL [(0, oPoly (K.k + N), 1024), (0, K.oNtt, 1024)]) s₄ s₅ →
      s₅.gpr .r9 = BitVec.ofNat 32 N → PolyIs s₅.mem (L.A 0 (oPoly (K.k + N))) (VG.Proof.MlKem.Arm.prfOut withNtt σ N) →
      WP isa (.block (count .r9 N₁)) s₅ fun s' => VG.Proof.MlKem.Arm.KeptX [.r9] (L.RL (VG.Proof.MlKem.Arm.prfW K N)) s s' ∧
        s'.gpr .r9 = BitVec.ofNat 32 (N + 1) ∧ s'.z = decide (N + 1 = N₁) ∧
        PolyIs s'.mem (L.A 0 (oPoly (K.k + N))) (VG.Proof.MlKem.Arm.prfOut withNtt σ N) := fun s₅ k₅ g9₅ p₅ =>
    WP.mono (VG.Proof.MlKem.Arm.count_ok (by omega) (by omega) (VG.Proof.MlKem.Arm.enc_le9 _ (by omega)) g9₅) fun s' ⟨k', g', z'⟩ => ⟨by
      exact ((k₁.weaken (by simp)).monoL (W' := VG.Proof.MlKem.Arm.prfW K N) (by simp)).trans (((k₂.x _).monoL (by simp)).trans
        ((o₃.x _ _).trans (((k₄.x _).monoL (by simp)).trans ((k₅.monoL (by simp)).trans (k'.mono (fun _ h => absurd h List.not_mem_nil)))))),
      g', z', polyIs_frame k'.frame (fun _ h => absurd h List.not_mem_nil) p₅⟩
  cases withNtt
  · refine WP.seq (WP.block_nil ?_)
    exact fin s₄ ((Kept.refl _ _).x _) g9₄ p₄
  · refine WP.seq (WP.seq (WP.mono (VG.Proof.MlKem.Arm.nttArgs_ok hK hc₄.r7 g9₄) fun s₅ ⟨o₅, g0', g1'⟩ => ?_))
    rw [VG.Proof.MlKem.Arm.slot_eq _ (by offs), ← eo] at g0'
    have hc₅ := hc₄.only o₅
    refine VG.Proof.MlKem.Arm.nttL hL g0' g1' (hc.sep00 (by offs) (by offs) (by offs)) hc₅.buf0 hc₅.buf0 (by rw [o₅.mem]; exact p₄)
      fun s₆ k₆ p₆ => fin s₆ (((o₅.kept _).trans k₆).x _) ?_ p₆
    rw [k₆.cs .r9 (by decide) (by decide), o₅.cs .r9 (by decide) (by decide), g9₄]

end

/-! ## The loop -/

/-- What the loop changes: the regions of `prfW`, with all its polynomials. -/
abbrev prfLW (K : KemLay) (N₀ N₁ : Nat) : List (Nat × Nat × Nat) :=
  [(0, 0, 200), (0, 200, 640), (1, 0, 8), (0, 952, 1), (0, 1024, 128), (0, oPoly (K.k + N₀), 1024 * (N₁ - N₀)),
    (0, K.oNtt, 1024)]

structure PrfInv (K : KemLay) (L : VG.Proof.MlKem.Arm.Lay) (withNtt : Bool) (σ : List Byte) (N₀ N₁ : Nat) (s₀ : State) (t : Nat)
    (s : State) : Prop where
  kx : VG.Proof.MlKem.Arm.KeptX [.r9] (L.RL (VG.Proof.MlKem.Arm.prfLW K N₀ N₁)) s₀ s
  r9 : s.gpr .r9 = BitVec.ofNat 32 (N₀ + t)
  sig : bytesAt s.mem (L.A 0 oSigma) 32 = σ
  slots : ∀ N, N₀ ≤ N → N < N₀ + t → PolyIs s.mem (L.A 0 (oPoly (K.k + N))) (VG.Proof.MlKem.Arm.prfOut withNtt σ N)

theorem prfW_sig {K : KemLay} (hK : K.WF) : ∀ N < 2 * K.k + 1, (VG.Proof.MlKem.Arm.prfW K N).all (VG.Proof.MlKem.Arm.sep0 oSigma 32) = true := by
  have := hK.k4
  intro N hN
  simp only [VG.Proof.MlKem.Arm.prfW, List.all_cons, List.all_nil, VG.Proof.MlKem.Arm.sep0, oPoly, KemLay.oNtt, oSigma, Bool.and_true, Bool.and_eq_true,
    Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, true_and]
  omega

theorem prfW_slot {K : KemLay} (hK : K.WF) {N N' : Nat} (hN : N < 2 * K.k + 1) (hN' : N' < 2 * K.k + 1)
    (h : N' ≠ N) : (VG.Proof.MlKem.Arm.prfW K N).all (VG.Proof.MlKem.Arm.sep0 (oPoly (K.k + N')) 1024) = true := by
  have := hK.k4
  simp only [VG.Proof.MlKem.Arm.prfW, List.all_cons, List.all_nil, VG.Proof.MlKem.Arm.sep0, oPoly, KemLay.oNtt, Bool.and_true, Bool.and_eq_true,
    Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, true_and]
  omega

theorem mov9_ok {s : State} {N : Nat} (he : encodable (BitVec.ofNat 32 N) = true) :
    WP isa (.block [.mov .r9 (.imm (BitVec.ofNat 32 N))]) s fun s' =>
      VG.Proof.MlKem.Arm.KeptX [.r9] [] s s' ∧ s'.gpr .r9 = BitVec.ofNat 32 N ∧ s'.mem = s.mem := by
  run_block [he]
  refine ⟨⟨fun r _ _ hx => ?_, rfl, rfl, rfl, Frame.refl _ _⟩, trivial⟩
  show (if r = .r9 then _ else s.gpr r) = s.gpr r
  exact ite_eq_right (fun e : r = .r9 => hx (by rw [e]; exact List.mem_singleton_self _))

section
variable {K : KemLay} (hK : K.WF)
include hK

theorem prfStep_ok {L : VG.Proof.MlKem.Arm.Lay} {s₀ : State} (hc : VG.Proof.MlKem.Arm.Ctx L s₀) (withNtt : Bool) {N₀ N₁ : Nat}
    (hN₁ : N₁ ≤ 2 * K.k + 1) {σ : List Byte} {t : Nat} (ht : t < N₁ - N₀) {s : State}
    (h : VG.Proof.MlKem.Arm.PrfInv K L withNtt σ N₀ N₁ s₀ t s) :
    WP isa (K.prfBody withNtt N₁) s fun s' =>
      VG.Proof.MlKem.Arm.PrfInv K L withNtt σ N₀ N₁ s₀ (t + 1) s' ∧ s'.z = decide (t + 1 = N₁ - N₀) := by
  have hL := hc.ok
  have k4 := hK.k4
  have hcs := h.kx.ctx (by decide) hc
  refine WP.mono (VG.Proof.MlKem.Arm.prfBody_ok hK hcs withNtt (N := N₀ + t) (by omega) hN₁ h.r9 h.sig) fun s' ⟨k', g', z', p'⟩ =>
    ⟨⟨h.kx.trans (k'.sub fun r hr => ?_), by rw [g', Nat.add_assoc], ?_, fun N h1 h2 => ?_⟩, ?_⟩
  · simp only [Lay.RL, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.R 0 0 200, by simp, fun _ h => h⟩
    · exact ⟨L.R 0 200 640, by simp, fun _ h => h⟩
    · exact ⟨L.R 1 0 8, by simp, fun _ h => h⟩
    · exact ⟨L.R 0 952 1, by simp, fun _ h => h⟩
    · exact ⟨L.R 0 1024 128, by simp, fun _ h => h⟩
    · exact ⟨L.R 0 (oPoly (K.k + N₀)) (1024 * (N₁ - N₀)), by simp, hc.sub0 (by offs) (by offs) (by offs)⟩
    · exact ⟨L.R 0 K.oNtt 1024, by simp, fun _ h => h⟩
  · rw [← h.sig]
    exact Lay.bytes_keep hL k'.frame (hc.sepAll0 (by decide) (VG.Proof.MlKem.Arm.prfW_sig hK _ (by omega))) (by decide)
  · by_cases e : N = N₀ + t
    · subst e; exact p'
    · exact Lay.polyIs_keep hL k'.frame (hc.sepAll0 (by offs) (VG.Proof.MlKem.Arm.prfW_slot hK (by omega) (by omega) e))
        (h.slots N h1 (by omega))
  · rw [z']; simp only [decide_eq_decide]; omega

theorem prfLoop_ok {L : VG.Proof.MlKem.Arm.Lay} {s₀ : State} (hc : VG.Proof.MlKem.Arm.Ctx L s₀) (withNtt : Bool) {N₀ N₁ : Nat} (h01 : N₀ < N₁)
    (hN₁ : N₁ ≤ 2 * K.k + 1) {σ : List Byte} (hσ : bytesAt s₀.mem (L.A 0 oSigma) 32 = σ) :
    WP isa (K.prfLoop withNtt N₀ N₁) s₀ fun s => VG.Proof.MlKem.Arm.KeptX [.r9] (L.RL (VG.Proof.MlKem.Arm.prfLW K N₀ N₁)) s₀ s ∧
      ∀ N, N₀ ≤ N → N < N₁ → PolyIs s.mem (L.A 0 (oPoly (K.k + N))) (VG.Proof.MlKem.Arm.prfOut withNtt σ N) := by
  have k4 := hK.k4
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.mov9_ok (VG.Proof.MlKem.Arm.enc_le9 _ (by omega))) fun s₁ ⟨k₁, g₁, m₁⟩ => ?_)
  exact wp_loop_ne (VG.Proof.MlKem.Arm.PrfInv K L withNtt σ N₀ N₁ s₀) (N := N₁ - N₀) (by omega)
    (fun t ht s h => VG.Proof.MlKem.Arm.prfStep_ok hK hc withNtt hN₁ ht h)
    (fun s h => ⟨h.kx, fun N h1 h2 => h.slots N h1 (by omega)⟩)
    ⟨k₁.mono (fun _ h => absurd h List.not_mem_nil), by rw [g₁, Nat.add_zero], by rw [m₁]; exact hσ,
      fun N h1 h2 => absurd h2 (by omega)⟩

end

end VG.Proof.MlKem.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.RowSum`. -/
section

/-!
# ML-KEM on 32-bit ARM: a row of `Â ∘ v̂`

`K.rowSum transpose` sums, in polynomial `3k + 2`, the products of the entries
`j < k` of row `i` (in `r9`) of `Â` (or of `Â^⊺`, `transpose`) with
polynomials `k + j`, sampling each entry into polynomial `3k + 4` from the
seed `ρ ‖ j ‖ i` (`ρ ‖ i ‖ j`) at 1216. If a `SampleNTT` does not finish, the
product uses polynomial `k + j` in its place (`effA`), and the flag in `r11`
becomes 0 (`rowSum_ok`). The sum is `KPke.dotK` (`rowAcc_eq`).
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## The algorithm -/

/-- The seed of entry `j` of row `i`: that of `Â[i, j]`, or of `Â[j, i]`. -/
def rowSeed (transpose : Bool) (ρ : List Byte) (i j : Nat) : List Byte :=
  if transpose then VG.Proof.MlKem.matSeed ρ j i else VG.Proof.MlKem.matSeed ρ i j

/-- The entry the product uses: the sampled one, or `v` if `SampleNTT` does not finish. -/
def effA (transpose : Bool) (ρ : List Byte) (i j : Nat) (v : VG.Spec.MlKem.Poly) : VG.Spec.MlKem.Poly :=
  (sampleNTT 280 (VG.Proof.MlKem.Arm.rowSeed transpose ρ i j)).getD v

/-- The sum of the first `j` products. -/
def rowAcc (a v : Nat → VG.Spec.MlKem.Poly) : Nat → VG.Spec.MlKem.Poly
  | 0 => VG.Spec.MlKem.zero
  | j + 1 => add (VG.Proof.MlKem.Arm.rowAcc a v j) (multiplyNTTs (a j) (v j))

/-- Whether the first `j` entries' `SampleNTT`s finished. -/
def okRow (transpose : Bool) (ρ : List Byte) (i j : Nat) : Bool :=
  (List.range j).all fun j' => (sampleNTT 280 (VG.Proof.MlKem.Arm.rowSeed transpose ρ i j')).isSome

theorem okRow_succ (transpose : Bool) (ρ : List Byte) (i j : Nat) :
    VG.Proof.MlKem.Arm.okRow transpose ρ i (j + 1) = (VG.Proof.MlKem.Arm.okRow transpose ρ i j && (sampleNTT 280 (VG.Proof.MlKem.Arm.rowSeed transpose ρ i j)).isSome) := by
  simp only [VG.Proof.MlKem.Arm.okRow, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]

theorem rowAcc_eq (a v : Nat → VG.Spec.MlKem.Poly) : ∀ k, VG.Proof.MlKem.Arm.rowAcc a v k = VG.Proof.MlKem.KPke.dotK a v k
  | 0 => rfl
  | k + 1 => by
    rw [VG.Proof.MlKem.Arm.rowAcc, VG.Proof.MlKem.Arm.rowAcc_eq a v k]
    exact (VG.Proof.MlKem.KPke.foldK_succ VG.Proof.MlKem.zero_add_poly _ k).symm

/-! ## The blocks -/

section
variable {K : KemLay} {s : State} {P : BitVec 32} {i j : Nat}

theorem seedArgs_ok (hK : K.WF) (transpose : Bool) (h7 : s.gpr .r7 = P) (h9 : s.gpr .r9 = BitVec.ofNat 32 i)
    (h10 : s.gpr .r10 = BitVec.ofNat 32 j)
    (w912 : InRegions s.wr (State.addr (P + BitVec.ofNat 32 (oSeed + 32))) 1)
    (w913 : InRegions s.wr (State.addr (P + BitVec.ofNat 32 (oSeed + 33))) 1) :
    WP isa (.block (seedBytes transpose ++ [ptrTo .r0 .r7 oSeed, ptrTo .r1 .r7 K.oAhat, ptrTo .r2 .r7 K.oSample])) s
      fun s' => (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        s'.mem = (s.mem.writeW (State.addr (P + BitVec.ofNat 32 (oSeed + 32)))
            ((BitVec.ofNat 32 (if transpose then i else j)).setWidth 8)).writeW
          (State.addr (P + BitVec.ofNat 32 (oSeed + 33))) ((BitVec.ofNat 32 (if transpose then j else i)).setWidth 8) ∧
        s'.gpr .r0 = P + BitVec.ofNat 32 oSeed ∧ s'.gpr .r1 = P + BitVec.ofNat 32 K.oAhat ∧
        s'.gpr .r2 = P + BitVec.ofNat 32 K.oSample := by
  have e1 : encodable (BitVec.ofNat 32 oSeed) = true := by decide
  have e2 : encodable (BitVec.ofNat 32 K.oAhat) = true := hK.enc (by omega)
  have e3 : encodable (BitVec.ofNat 32 K.oSample) = true := hK.enc (by omega)
  have o1 : oSeed + 32 < 4096 := by decide
  have o2 : oSeed + 33 < 4096 := by decide
  cases transpose <;>
  · run_block [seedBytes, ptrTo, e1, e2, e3, o1, o2, h7, h9, h10, w912, w913]
    refine ⟨fun r hr hl => ?_, trivial⟩
    obtain ⟨m0, m1, m2, -, -⟩ := VG.Proof.MlKem.Arm.pres_ne hr hl
    simp only [m0, m1, m2, ite_false]

theorem flag_ok {b c : Bool} (h0 : s.gpr .r0 = if c then 1 else 0) (h11 : s.gpr .r11 = if b then 1 else 0) :
    WP isa (.block [.dp .and .r11 .r11 (.reg .r0), .cmp .r0 (.imm 0)]) s fun s' =>
      VG.Proof.MlKem.Arm.KeptX [.r11] [] s s' ∧ s'.gpr .r11 = (if b && c then 1 else 0) ∧ s'.z = !c ∧ s'.mem = s.mem := by
  have e0 : encodable (0 : BitVec 32) = true := by decide
  run_block [e0, h0, h11]
  refine ⟨⟨fun r _ _ hx => ?_, rfl, rfl, rfl, Frame.refl _ _⟩, ?_, ?_⟩
  · show (if r = .r11 then _ else s.gpr r) = s.gpr r
    exact ite_eq_right (fun e : r = .r11 => hx (by rw [e]; exact List.mem_singleton_self _))
  · cases b <;> cases c <;> rfl
  · cases c <;> exact ⟨rfl, trivial⟩

theorem selT_ok (hK : K.WF) (h7 : s.gpr .r7 = P) (h10 : s.gpr .r10 = BitVec.ofNat 32 j) :
    WP isa (.block (slotAt .r1 .r10 (oPoly K.k))) s fun s' =>
      VG.Proof.MlKem.Arm.Only s s' ∧ s'.gpr .r1 = P + BitVec.ofNat 32 j <<< 10 + BitVec.ofNat 32 (oPoly K.k) := by
  have e1 : encodable (BitVec.ofNat 32 (oPoly K.k)) = true := hK.enc (by omega)
  run_block [slotAt, ptrTo, e1, h7, h10]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨-, m1, -, -, -⟩ := VG.Proof.MlKem.Arm.pres_ne hr hl
  simp only [m1, ite_false]

theorem selF_ok (hK : K.WF) (h7 : s.gpr .r7 = P) :
    WP isa (.block [ptrTo .r1 .r7 K.oAhat]) s fun s' => VG.Proof.MlKem.Arm.Only s s' ∧ s'.gpr .r1 = P + BitVec.ofNat 32 K.oAhat := by
  have e1 : encodable (BitVec.ofNat 32 K.oAhat) = true := hK.enc (by omega)
  run_block [ptrTo, e1, h7]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨-, m1, -, -, -⟩ := VG.Proof.MlKem.Arm.pres_ne hr hl
  simp only [m1, ite_false]

theorem mulArgs_ok (hK : K.WF) (h7 : s.gpr .r7 = P) (h10 : s.gpr .r10 = BitVec.ofNat 32 j) :
    WP isa (.block (ptrTo .r0 .r7 K.oTmp :: slotAt .r2 .r10 (oPoly K.k) ++ [ptrTo .r3 .r7 K.oNtt])) s fun s' =>
      VG.Proof.MlKem.Arm.Only s s' ∧ s'.gpr .r0 = P + BitVec.ofNat 32 K.oTmp ∧ s'.gpr .r1 = s.gpr .r1 ∧
      s'.gpr .r2 = P + BitVec.ofNat 32 j <<< 10 + BitVec.ofNat 32 (oPoly K.k) ∧
      s'.gpr .r3 = P + BitVec.ofNat 32 K.oNtt := by
  have e1 : encodable (BitVec.ofNat 32 K.oTmp) = true := hK.enc (by omega)
  have e2 : encodable (BitVec.ofNat 32 (oPoly K.k)) = true := hK.enc (by omega)
  have e3 : encodable (BitVec.ofNat 32 K.oNtt) = true := hK.enc (by omega)
  run_block [slotAt, ptrTo, e1, e2, e3, h7, h10]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, -, m2, m3, -⟩ := VG.Proof.MlKem.Arm.pres_ne hr hl
  simp only [m0, m2, m3, ite_false]

theorem accArgs_ok {o o' : Nat} (h7 : s.gpr .r7 = P) (he : encodable (BitVec.ofNat 32 o) = true)
    (he' : encodable (BitVec.ofNat 32 o') = true) :
    WP isa (.block [ptrTo .r0 .r7 o, ptrTo .r1 .r7 o']) s fun s' =>
      VG.Proof.MlKem.Arm.Only s s' ∧ s'.gpr .r0 = P + BitVec.ofNat 32 o ∧ s'.gpr .r1 = P + BitVec.ofNat 32 o' := by
  run_block [ptrTo, he, he', h7]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, -, -, -⟩ := VG.Proof.MlKem.Arm.pres_ne hr hl
  simp only [m0, m1, ite_false]

end

/-! ## The loop -/

/-- What a row needs of the state it starts from. -/
structure RowPre (K : KemLay) (L : VG.Proof.MlKem.Arm.Lay) (ρ : List Byte) (v : Nat → VG.Spec.MlKem.Poly) (i : Nat) (fl : Bool) (s : State) : Prop where
  wf : K.WF
  ctx : VG.Proof.MlKem.Arm.Ctx L s
  ik : i < K.k
  r9 : s.gpr .r9 = BitVec.ofNat 32 i
  r11 : s.gpr .r11 = if fl then 1 else 0
  rho : bytesAt s.mem (L.A 0 oSeed) 32 = ρ
  vec : ∀ j < K.k, PolyIs s.mem (L.A 0 (oPoly (K.k + j))) (v j)

/-- What a row changes: the indices of the seed, polynomials 11 to 13, the
working space of the callees and the stack. -/
abbrev rowW (K : KemLay) : List (Nat × Nat × Nat) := [(0, 1248, 2), (0, K.oAcc, 3072), (0, K.oSample, 3072), (1, 0, 8)]

/-- After the first `j` entries of the row. -/
structure RowInv (K : KemLay) (L : VG.Proof.MlKem.Arm.Lay) (transpose : Bool) (ρ : List Byte) (v : Nat → VG.Spec.MlKem.Poly) (i : Nat) (fl : Bool) (s₀ : State)
    (j : Nat) (s : State) : Prop where
  kx : VG.Proof.MlKem.Arm.KeptX [.r10, .r11] (L.RL (VG.Proof.MlKem.Arm.rowW K)) s₀ s
  r10 : s.gpr .r10 = BitVec.ofNat 32 j
  r11 : s.gpr .r11 = if fl && VG.Proof.MlKem.Arm.okRow transpose ρ i j then 1 else 0
  acc : PolyIs s.mem (L.A 0 K.oAcc) (VG.Proof.MlKem.Arm.rowAcc (fun j => VG.Proof.MlKem.Arm.effA transpose ρ i j (v j)) v j)

/-- The polynomials of `v̂` apart from what a row changes. -/
abbrev RowWVec (K : KemLay) : Prop := ∀ j < K.k, (VG.Proof.MlKem.Arm.rowW K).all (VG.Proof.MlKem.Arm.sep0 (oPoly (K.k + j)) 1024) = true

/-- The facts on the offsets of `scratch` that a row's steps use. -/
abbrev RowLF (K : KemLay) : Prop :=
  (VG.Proof.MlKem.Arm.rowW K).all (VG.Proof.MlKem.Arm.sep0 oSeed 32) = true ∧ [((0 : Nat), (1248 : Nat), (2 : Nat))].all (fun w => (VG.Proof.MlKem.Arm.rowW K).any (VG.Proof.MlKem.Arm.subB0 w)) = true ∧
  K.oAcc + 1024 ≤ 32768 ∧ [((0 : Nat), (1248 : Nat), (2 : Nat))].all (VG.Proof.MlKem.Arm.sep0 K.oAcc 1024) = true ∧
  K.oAhat + 1024 ≤ 32768 ∧ (oSeed + 34 ≤ K.oAhat ∨ K.oAhat + 1024 ≤ oSeed) ∧
  K.oSample + 2048 ≤ 32768 ∧ (oSeed + 34 ≤ K.oSample ∨ K.oSample + 2048 ≤ oSeed) ∧
  (K.oAhat + 1024 ≤ K.oSample ∨ K.oSample + 2048 ≤ K.oAhat) ∧
  [((0 : Nat), K.oAhat, (1024 : Nat)), (0, K.oSample, 2048), (1, 0, 8)].all (fun w => (VG.Proof.MlKem.Arm.rowW K).any (VG.Proof.MlKem.Arm.subB0 w)) = true ∧
  [((0 : Nat), K.oAhat, (1024 : Nat)), (0, K.oSample, 2048), (1, 0, 8)].all (VG.Proof.MlKem.Arm.sep0 K.oAcc 1024) = true ∧
  [((0 : Nat), K.oTmp, (1024 : Nat)), (0, K.oNtt, 1024)].all (fun w => (VG.Proof.MlKem.Arm.rowW K).any (VG.Proof.MlKem.Arm.subB0 w)) = true ∧
  [((0 : Nat), K.oTmp, (1024 : Nat)), (0, K.oNtt, 1024)].all (VG.Proof.MlKem.Arm.sep0 K.oAcc 1024) = true ∧
  K.oTmp + 1024 ≤ 32768 ∧ (K.oAcc + 1024 ≤ K.oTmp ∨ K.oTmp + 1024 ≤ K.oAcc) ∧
  [((0 : Nat), K.oAcc, (1024 : Nat))].all (fun w => (VG.Proof.MlKem.Arm.rowW K).any (VG.Proof.MlKem.Arm.subB0 w)) = true

theorem row_lf {K : KemLay} (hK : K.WF) : VG.Proof.MlKem.Arm.RowLF K :=
  (by decide : ∀ k < 5, RowLF (kOf k)) K.k (by have := hK.k4; omega)

theorem rowW_vec {K : KemLay} (hK : K.WF) : VG.Proof.MlKem.Arm.RowWVec K := (by decide : ∀ k < 5, RowWVec (kOf k)) K.k (by have := hK.k4; omega)

theorem bytes_two (m : Mem) (p : Addr) : bytesAt m p 2 = [m p, m (p + BitVec.ofNat 64 1)] := by
  simp only [bytesAt, show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_nil, add_ofNat_zero]

theorem rowSeed_eq (transpose : Bool) (ρ : List Byte) (i j : Nat) :
    VG.Proof.MlKem.Arm.rowSeed transpose ρ i j = ρ ++ [BitVec.ofNat 8 (if transpose then i else j), BitVec.ofNat 8 (if transpose then j else i)] := by
  cases transpose <;> rfl

/-! ### The steps of an iteration -/

/-- Whether entry `j`'s `SampleNTT` finishes. -/
abbrev cOk (transpose : Bool) (ρ : List Byte) (i j : Nat) : Bool := (sampleNTT 280 (VG.Proof.MlKem.Arm.rowSeed transpose ρ i j)).isSome

/-- Where the product takes the entry from. -/
abbrev oSel (K : KemLay) (c : Bool) (j : Nat) : Nat := if c then K.oAhat else oPoly (K.k + j)

section
variable (K : KemLay) (L : VG.Proof.MlKem.Arm.Lay) (transpose : Bool) (ρ : List Byte) (v : Nat → VG.Spec.MlKem.Poly) (i : Nat) (fl : Bool) (s₀ : State) (j : Nat)

/-- What holds through an iteration: what it changed, the counter, the sum so far. -/
structure RS (s : State) : Prop where
  kx : VG.Proof.MlKem.Arm.KeptX [.r10, .r11] (L.RL (VG.Proof.MlKem.Arm.rowW K)) s₀ s
  r10 : s.gpr .r10 = BitVec.ofNat 32 j
  acc : PolyIs s.mem (L.A 0 K.oAcc) (VG.Proof.MlKem.Arm.rowAcc (fun j => VG.Proof.MlKem.Arm.effA transpose ρ i j (v j)) v j)

/-- After the seed and the arguments of `SampleNTT`. -/
structure RA (s : State) : Prop where
  rs : VG.Proof.MlKem.Arm.RS K L transpose ρ v i s₀ j s
  r11 : s.gpr .r11 = if fl && VG.Proof.MlKem.Arm.okRow transpose ρ i j then 1 else 0
  r0 : s.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oSeed
  r1 : s.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 K.oAhat
  r2 : s.gpr .r2 = L.ptr 0 + BitVec.ofNat 32 K.oSample
  seed : bytesAt s.mem (L.A 0 oSeed) 34 = VG.Proof.MlKem.Arm.rowSeed transpose ρ i j

/-- After `SampleNTT`. -/
structure RB (s : State) : Prop where
  rs : VG.Proof.MlKem.Arm.RS K L transpose ρ v i s₀ j s
  r11 : s.gpr .r11 = if fl && VG.Proof.MlKem.Arm.okRow transpose ρ i j then 1 else 0
  r0 : s.gpr .r0 = if VG.Proof.MlKem.Arm.cOk transpose ρ i j then 1 else 0
  ahat : ∀ a, sampleNTT 280 (VG.Proof.MlKem.Arm.rowSeed transpose ρ i j) = some a → PolyIs s.mem (L.A 0 K.oAhat) a

/-- After the flag. -/
structure RC (s : State) : Prop where
  rs : VG.Proof.MlKem.Arm.RS K L transpose ρ v i s₀ j s
  r11 : s.gpr .r11 = if fl && VG.Proof.MlKem.Arm.okRow transpose ρ i (j + 1) then 1 else 0
  z : s.z = !VG.Proof.MlKem.Arm.cOk transpose ρ i j
  ahat : ∀ a, sampleNTT 280 (VG.Proof.MlKem.Arm.rowSeed transpose ρ i j) = some a → PolyIs s.mem (L.A 0 K.oAhat) a

/-- After the selection of the entry. -/
structure RD (s : State) : Prop where
  rs : VG.Proof.MlKem.Arm.RS K L transpose ρ v i s₀ j s
  r11 : s.gpr .r11 = if fl && VG.Proof.MlKem.Arm.okRow transpose ρ i (j + 1) then 1 else 0
  r1 : s.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (VG.Proof.MlKem.Arm.oSel K (VG.Proof.MlKem.Arm.cOk transpose ρ i j) j)
  sel : PolyIs s.mem (L.A 0 (VG.Proof.MlKem.Arm.oSel K (VG.Proof.MlKem.Arm.cOk transpose ρ i j) j)) (VG.Proof.MlKem.Arm.effA transpose ρ i j (v j))

/-- After the arguments of the product. -/
structure RE (s : State) : Prop where
  rd : VG.Proof.MlKem.Arm.RD K L transpose ρ v i fl s₀ j s
  r0 : s.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oTmp
  r2 : s.gpr .r2 = L.ptr 0 + BitVec.ofNat 32 (oPoly (K.k + j))
  r3 : s.gpr .r3 = L.ptr 0 + BitVec.ofNat 32 K.oNtt

/-- After the product. -/
structure RF (s : State) : Prop where
  rs : VG.Proof.MlKem.Arm.RS K L transpose ρ v i s₀ j s
  r11 : s.gpr .r11 = if fl && VG.Proof.MlKem.Arm.okRow transpose ρ i (j + 1) then 1 else 0
  tmp : PolyIs s.mem (L.A 0 K.oTmp) (multiplyNTTs (VG.Proof.MlKem.Arm.effA transpose ρ i j (v j)) (v j))

/-- After the arguments of the sum. -/
structure RG (s : State) : Prop where
  rf : VG.Proof.MlKem.Arm.RF K L transpose ρ v i fl s₀ j s
  r0 : s.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc
  r1 : s.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 K.oTmp

/-- After the sum. -/
structure RH (s : State) : Prop where
  kx : VG.Proof.MlKem.Arm.KeptX [.r10, .r11] (L.RL (VG.Proof.MlKem.Arm.rowW K)) s₀ s
  r10 : s.gpr .r10 = BitVec.ofNat 32 j
  r11 : s.gpr .r11 = if fl && VG.Proof.MlKem.Arm.okRow transpose ρ i (j + 1) then 1 else 0
  acc : PolyIs s.mem (L.A 0 K.oAcc) (VG.Proof.MlKem.Arm.rowAcc (fun j => VG.Proof.MlKem.Arm.effA transpose ρ i j (v j)) v (j + 1))

end

section
variable {K : KemLay} {L : VG.Proof.MlKem.Arm.Lay} {transpose : Bool} {ρ : List Byte} {v : Nat → VG.Spec.MlKem.Poly} {i : Nat} {fl : Bool}
  {s₀ : State} {j : Nat}

theorem RS.ctx (hp : VG.Proof.MlKem.Arm.RowPre K L ρ v i fl s₀) {s : State} (h : VG.Proof.MlKem.Arm.RS K L transpose ρ v i s₀ j s) : VG.Proof.MlKem.Arm.Ctx L s :=
  h.kx.ctx (by kdecide) hp.ctx

theorem RS.r9 (hp : VG.Proof.MlKem.Arm.RowPre K L ρ v i fl s₀) {s : State} (h : VG.Proof.MlKem.Arm.RS K L transpose ρ v i s₀ j s) :
    s.gpr .r9 = BitVec.ofNat 32 i := by
  have hK := hp.wf
  rw [h.kx.cs .r9 (by kdecide) (by kdecide) (by kdecide), hp.r9]

theorem RS.vec (hp : VG.Proof.MlKem.Arm.RowPre K L ρ v i fl s₀) (hj : j < K.k) {s : State} (h : VG.Proof.MlKem.Arm.RS K L transpose ρ v i s₀ j s) :
    PolyIs s.mem (L.A 0 (oPoly (K.k + j))) (v j) := by
  have hK := hp.wf
  exact Lay.polyIs_keep hp.ctx.ok h.kx.frame (hp.ctx.sepAll0 (by offs) (VG.Proof.MlKem.Arm.rowW_vec hp.wf j hj)) (hp.vec j hj)

/-- A step that keeps `RS`: it changes only the regions of `rowW K` and not `r10`, nor the sum. -/
theorem RS.step (hp : VG.Proof.MlKem.Arm.RowPre K L ρ v i fl s₀) {s s' : State} (h : VG.Proof.MlKem.Arm.RS K L transpose ρ v i s₀ j s) {xs : List Reg}
    {W : List (Nat × Nat × Nat)} (hk : VG.Proof.MlKem.Arm.KeptX xs (L.RL W) s s') (hx : ∀ x ∈ xs, x ∈ [Reg.r10, .r11])
    (h10 : Reg.r10 ∉ xs) (hW : W.all (fun w => (VG.Proof.MlKem.Arm.rowW K).any (VG.Proof.MlKem.Arm.subB0 w)) = true)
    (hA : VG.Proof.MlKem.Arm.sepAll L.sizes (0, K.oAcc, 1024) W = true) : VG.Proof.MlKem.Arm.RS K L transpose ρ v i s₀ j s' :=
  ⟨h.kx.trans ((hk.weaken hx).subL hp.ctx hW), by rw [hk.cs .r10 (by kdecide) (by kdecide) h10, h.r10],
    Lay.polyIs_keep hp.ctx.ok hk.frame hA h.acc⟩

theorem rowA_ok (hp : VG.Proof.MlKem.Arm.RowPre K L ρ v i fl s₀) (hj : j < K.k) {s : State} (h : VG.Proof.MlKem.Arm.RowInv K L transpose ρ v i fl s₀ j s) :
    WP isa (.block (seedBytes transpose ++ [ptrTo .r0 .r7 oSeed, ptrTo .r1 .r7 K.oAhat, ptrTo .r2 .r7 K.oSample])) s
      (VG.Proof.MlKem.Arm.RA K L transpose ρ v i fl s₀ j) := by
  have hK := hp.wf
  have k4 := hK.k4
  have hL := hp.ctx.ok
  have hi := hp.ik
  have hc := h.kx.ctx (by kdecide) hp.ctx
  have g9 : s.gpr .r9 = BitVec.ofNat 32 i := by rw [h.kx.cs .r9 (by kdecide) (by kdecide) (by kdecide), hp.r9]
  have ρs : bytesAt s.mem (L.A 0 oSeed) 32 = ρ := by
    rw [← hp.rho]; exact Lay.bytes_keep hL h.kx.frame (hp.ctx.sepAll0 (by kdecide) (VG.Proof.MlKem.Arm.row_lf hK).1) (by kdecide)
  have e912 := hc.addr (o := oSeed + 32) (by kdecide)
  have e913 := hc.addr (o := oSeed + 33) (by kdecide)
  have w912 : InRegions s.wr (State.addr (L.ptr 0 + BitVec.ofNat 32 (oSeed + 32))) 1 := by
    rw [e912]; exact hc.cs (o := 1248) (l := 1) (by kdecide) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  have w913 : InRegions s.wr (State.addr (L.ptr 0 + BitVec.ofNat 32 (oSeed + 33))) 1 := by
    rw [e913]; exact hc.cs (o := 1249) (l := 1) (by kdecide) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  refine WP.mono (VG.Proof.MlKem.Arm.seedArgs_ok hK transpose hc.r7 g9 h.r10 w912 w913)
    fun s₁ ⟨cs₁, rd₁, wr₁, sp₁, m₁, g0, g1, g2⟩ => ?_
  have m₁' : s₁.mem = (s.mem.writeW (L.A 0 1248) (BitVec.ofNat 8 (if transpose then i else j))).writeW (L.A 0 1249)
      (BitVec.ofNat 8 (if transpose then j else i)) := by
    rw [m₁, e912, e913, VG.Proof.MlKem.Arm.setWidth8_ofNat (by split <;> omega), VG.Proof.MlKem.Arm.setWidth8_ofNat (by split <;> omega)]
  have k₁ : VG.Proof.MlKem.Arm.KeptX [] (L.RL [(0, 1248, 2)]) s s₁ := by
    refine ⟨fun r hr hl _ => cs₁ r hr hl, sp₁, rd₁, wr₁, ?_⟩
    rw [m₁']
    have c1 : (L.R 0 1248 2).Contains (L.A 0 1248) 1 := by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
    have c2 : (L.R 0 1248 2).Contains (L.A 0 1249) 1 := by
      have := contains_off (base := State.addr (L.ptr 0) + BitVec.ofNat 64 1248) (len := 2) (off := 1) (n := 1)
        (by omega) (by omega)
      rwa [add_ofNat_add] at this
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c1).writeW (List.mem_singleton_self _) _ c2
  have ne : (L.A 0 1248 : Addr) ≠ L.A 0 1249 := by
    intro e; have := congrArg BitVec.toNat ((BitVec.add_right_inj _).mp e); simp at this
  have b912 : s₁.mem (L.A 0 1248) = BitVec.ofNat 8 (if transpose then i else j) := by
    rw [m₁', VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply, ite_eq_right ne, ite_eq_left rfl]
  have b913 : s₁.mem (L.A 0 1249) = BitVec.ofNat 8 (if transpose then j else i) := by
    rw [m₁', VG.WriteBytes.writeW8_apply, ite_eq_left rfl]
  refine ⟨⟨h.kx.trans ((k₁.weaken (by simp)).subL hp.ctx (VG.Proof.MlKem.Arm.row_lf hK).2.1),
    by rw [k₁.cs .r10 (by kdecide) (by kdecide) (by kdecide), h.r10],
    Lay.polyIs_keep hL k₁.frame (hc.sepAll0 (VG.Proof.MlKem.Arm.row_lf hK).2.2.1 (VG.Proof.MlKem.Arm.row_lf hK).2.2.2.1) h.acc⟩,
    by rw [k₁.cs .r11 (by kdecide) (by kdecide) (by kdecide), h.r11], g0, g1, g2, ?_⟩
  rw [VG.Proof.MlKem.Arm.rowSeed_eq]
  show bytesAt s₁.mem (State.addr (L.ptr 0) + BitVec.ofNat 64 1216) (32 + 2) = _
  rw [bytesAt_add, VG.Proof.MlKem.Arm.bytes_two, add_ofNat_add, add_ofNat_add]
  congr 1
  · rw [← ρs]
    exact Lay.bytes_keep hL k₁.frame (hc.sepAll0 (by kdecide) (by kdecide)) (by kdecide)
  · exact congrArg₂ (fun a b => [a, b]) b912 b913

theorem rowB_ok (hp : VG.Proof.MlKem.Arm.RowPre K L ρ v i fl s₀) {s : State} (h : VG.Proof.MlKem.Arm.RA K L transpose ρ v i fl s₀ j s) :
    WP isa callSample s (VG.Proof.MlKem.Arm.RB K L transpose ρ v i fl s₀ j) := by
  have hK := hp.wf
  have hc := h.rs.ctx hp
  refine VG.Proof.MlKem.Arm.sampleL hc h.r0 h.r1 h.r2 (hc.sep00 (by kdecide) (VG.Proof.MlKem.Arm.row_lf hK).2.2.2.2.1 (VG.Proof.MlKem.Arm.row_lf hK).2.2.2.2.2.1)
    (hc.sep00 (by kdecide) (VG.Proof.MlKem.Arm.row_lf hK).2.2.2.2.2.2.1 (VG.Proof.MlKem.Arm.row_lf hK).2.2.2.2.2.2.2.1) (hc.sep00 (VG.Proof.MlKem.Arm.row_lf hK).2.2.2.2.1 (VG.Proof.MlKem.Arm.row_lf hK).2.2.2.2.2.2.1 (VG.Proof.MlKem.Arm.row_lf hK).2.2.2.2.2.2.2.2.1)
    (hc.sep01 (by kdecide) (by kdecide)) (hc.sep01 (VG.Proof.MlKem.Arm.row_lf hK).2.2.2.2.1 (by kdecide)) (hc.sep01 (VG.Proof.MlKem.Arm.row_lf hK).2.2.2.2.2.2.1 (by kdecide))
    (VG.Proof.MlKem.Arm.mem_rd_wr hc.buf0) hc.buf0 hc.buf0 fun s' k' r0' a' => ?_
  rw [h.seed] at r0' a'
  exact ⟨h.rs.step hp (k'.x []) (by simp) (by simp) (VG.Proof.MlKem.Arm.row_lf hK).2.2.2.2.2.2.2.2.2.1 (hc.sepAll0 (VG.Proof.MlKem.Arm.row_lf hK).2.2.1 (VG.Proof.MlKem.Arm.row_lf hK).2.2.2.2.2.2.2.2.2.2.1),
    by rw [k'.cs .r11 (by kdecide) (by kdecide), h.r11], r0', a'⟩

theorem rowC_ok {s : State} (h : VG.Proof.MlKem.Arm.RB K L transpose ρ v i fl s₀ j s) :
    WP isa (.block [.dp .and .r11 .r11 (.reg .r0), .cmp .r0 (.imm 0)]) s (VG.Proof.MlKem.Arm.RC K L transpose ρ v i fl s₀ j) :=
  WP.mono (VG.Proof.MlKem.Arm.flag_ok h.r0 h.r11) fun s' ⟨k', f', z', m'⟩ =>
    ⟨⟨h.rs.kx.trans ((k'.weaken (by simp)).mono (fun _ h => absurd h List.not_mem_nil)),
      by rw [k'.cs .r10 (by kdecide) (by kdecide) (by kdecide), h.rs.r10], by rw [m']; exact h.rs.acc⟩,
      by rw [f', Bool.and_assoc, ← VG.Proof.MlKem.Arm.okRow_succ], z', by rw [m']; exact h.ahat⟩

theorem rowD_ok (hp : VG.Proof.MlKem.Arm.RowPre K L ρ v i fl s₀) (hj : j < K.k) {s : State} (h : VG.Proof.MlKem.Arm.RC K L transpose ρ v i fl s₀ j s) :
    WP isa (.ite .eq (.block (slotAt .r1 .r10 (oPoly K.k))) (.block [ptrTo .r1 .r7 K.oAhat])) s
      (VG.Proof.MlKem.Arm.RD K L transpose ρ v i fl s₀ j) := by
  have hK := hp.wf
  have hc := h.rs.ctx hp
  have eo : oPoly (K.k + j) = oPoly K.k + 1024 * j := by simp only [oPoly]; omega
  refine WP.ite s.z rfl (fun hz => WP.mono (VG.Proof.MlKem.Arm.selT_ok hK hc.r7 h.rs.r10) fun s₄ ⟨o₄, g1₄⟩ => ?_)
    (fun hz => WP.mono (VG.Proof.MlKem.Arm.selF_ok hK hc.r7) fun s₄ ⟨o₄, g1₄⟩ => ?_)
  · rw [h.z] at hz
    have hc' : VG.Proof.MlKem.Arm.cOk transpose ρ i j = false := by simpa using hz
    rw [VG.Proof.MlKem.Arm.slot_eq _ (by offs), ← eo] at g1₄
    have e : VG.Proof.MlKem.Arm.effA transpose ρ i j (v j) = v j := by
      simp only [VG.Proof.MlKem.Arm.effA]
      simp only [VG.Proof.MlKem.Arm.cOk] at hc'
      cases e' : sampleNTT 280 (VG.Proof.MlKem.Arm.rowSeed transpose ρ i j)
      · rfl
      · rw [e'] at hc'; cases hc'
    refine ⟨h.rs.step hp (o₄.x [] []) (W := []) (by simp) (by simp) rfl rfl,
      by rw [o₄.cs .r11 (by kdecide) (by kdecide), h.r11], by rw [g1₄, hc']; rfl, ?_⟩
    rw [hc', e, o₄.mem]; exact h.rs.vec hp hj
  · rw [h.z] at hz
    have hc' : VG.Proof.MlKem.Arm.cOk transpose ρ i j = true := by simpa using hz
    refine ⟨h.rs.step hp (o₄.x [] []) (W := []) (by simp) (by simp) rfl rfl,
      by rw [o₄.cs .r11 (by kdecide) (by kdecide), h.r11], by rw [g1₄, hc']; rfl, ?_⟩
    simp only [VG.Proof.MlKem.Arm.cOk] at hc'
    cases e' : sampleNTT 280 (VG.Proof.MlKem.Arm.rowSeed transpose ρ i j) with
    | none => rw [e'] at hc'; cases hc'
    | some a =>
      have e : VG.Proof.MlKem.Arm.effA transpose ρ i j (v j) = a := by simp only [VG.Proof.MlKem.Arm.effA, e', Option.getD_some]
      rw [e, o₄.mem, show VG.Proof.MlKem.Arm.oSel K (VG.Proof.MlKem.Arm.cOk transpose ρ i j) j = K.oAhat by simp [VG.Proof.MlKem.Arm.cOk, e']]
      exact h.ahat a e'

theorem rowE_ok (hp : VG.Proof.MlKem.Arm.RowPre K L ρ v i fl s₀) (hj : j < K.k) {s : State} (h : VG.Proof.MlKem.Arm.RD K L transpose ρ v i fl s₀ j s) :
    WP isa (.block (ptrTo .r0 .r7 K.oTmp :: slotAt .r2 .r10 (oPoly K.k) ++ [ptrTo .r3 .r7 K.oNtt])) s
      (VG.Proof.MlKem.Arm.RE K L transpose ρ v i fl s₀ j) := by
  have hK := hp.wf
  have hc := h.rs.ctx hp
  have eo : oPoly (K.k + j) = oPoly K.k + 1024 * j := by simp only [oPoly]; omega
  refine WP.mono (VG.Proof.MlKem.Arm.mulArgs_ok (j := j) hK hc.r7 h.rs.r10) fun s' ⟨o', m0, m1, m2, m3⟩ => ?_
  rw [VG.Proof.MlKem.Arm.slot_eq _ (by offs), ← eo] at m2
  exact ⟨⟨h.rs.step hp (o'.x [] []) (W := []) (by simp) (by simp) rfl rfl,
    by rw [o'.cs .r11 (by kdecide) (by kdecide), h.r11], by rw [m1, h.r1], by rw [o'.mem]; exact h.sel⟩, m0, m2, m3⟩

theorem sel_sep (hK : K.WF) (c : Bool) {j : Nat} (hj : j < K.k) :
    VG.Proof.MlKem.Arm.oSel K c j + 1024 ≤ 32768 ∧ (K.oTmp + 1024 ≤ VG.Proof.MlKem.Arm.oSel K c j ∨ VG.Proof.MlKem.Arm.oSel K c j + 1024 ≤ K.oTmp) ∧
      (VG.Proof.MlKem.Arm.oSel K c j + 1024 ≤ K.oNtt ∨ K.oNtt + 1024 ≤ VG.Proof.MlKem.Arm.oSel K c j) := by
  cases c <;> simp only [VG.Proof.MlKem.Arm.oSel, Bool.false_eq_true, ite_false, ite_true] <;> offs

theorem rowF_ok (hp : VG.Proof.MlKem.Arm.RowPre K L ρ v i fl s₀) (hj : j < K.k) {s : State} (h : VG.Proof.MlKem.Arm.RE K L transpose ρ v i fl s₀ j s) :
    WP isa callMul s (VG.Proof.MlKem.Arm.RF K L transpose ρ v i fl s₀ j) := by
  have hK := hp.wf
  have hc := h.rd.rs.ctx hp
  obtain ⟨s1, s2, s3⟩ := VG.Proof.MlKem.Arm.sel_sep hK (VG.Proof.MlKem.Arm.cOk transpose ρ i j) hj
  refine VG.Proof.MlKem.Arm.mulL hc.ok h.r0 h.rd.r1 h.r2 h.r3 (hc.sep00 (by offs) s1 s2) (hc.sep00 (by offs) (by offs) (by offs))
    (hc.sep00 (by offs) (by offs) (by offs)) (hc.sep00 s1 (by offs) s3) (hc.sep00 (by offs) (by offs) (by offs))
    hc.buf0 (VG.Proof.MlKem.Arm.mem_rd_wr hc.buf0) (VG.Proof.MlKem.Arm.mem_rd_wr hc.buf0) hc.buf0 h.rd.sel (h.rd.rs.vec hp hj) fun s' k' p' => ?_
  exact ⟨h.rd.rs.step hp (k'.x []) (by simp) (by simp) (VG.Proof.MlKem.Arm.row_lf hK).2.2.2.2.2.2.2.2.2.2.2.1 (hc.sepAll0 (VG.Proof.MlKem.Arm.row_lf hK).2.2.1 (VG.Proof.MlKem.Arm.row_lf hK).2.2.2.2.2.2.2.2.2.2.2.2.1),
    by rw [k'.cs .r11 (by kdecide) (by kdecide), h.rd.r11], p'⟩

theorem rowG_ok (hp : VG.Proof.MlKem.Arm.RowPre K L ρ v i fl s₀) {s : State} (h : VG.Proof.MlKem.Arm.RF K L transpose ρ v i fl s₀ j s) :
    WP isa (.block [ptrTo .r0 .r7 K.oAcc, ptrTo .r1 .r7 K.oTmp]) s (VG.Proof.MlKem.Arm.RG K L transpose ρ v i fl s₀ j) := by
  have hK := hp.wf
  have hc := h.rs.ctx hp
  exact WP.mono (VG.Proof.MlKem.Arm.accArgs_ok hc.r7 (by kenc) (by kenc)) fun s' ⟨o', a0, a1⟩ =>
    ⟨⟨h.rs.step hp (o'.x [] []) (W := []) (by simp) (by simp) rfl rfl,
      by rw [o'.cs .r11 (by kdecide) (by kdecide), h.r11], by rw [o'.mem]; exact h.tmp⟩, a0, a1⟩

theorem rowH_ok (hp : VG.Proof.MlKem.Arm.RowPre K L ρ v i fl s₀) {s : State} (h : VG.Proof.MlKem.Arm.RG K L transpose ρ v i fl s₀ j s) :
    WP isa callAdd s (VG.Proof.MlKem.Arm.RH K L transpose ρ v i fl s₀ j) := by
  have hK := hp.wf
  have hc := h.rf.rs.ctx hp
  refine VG.Proof.MlKem.Arm.addL hc.ok h.r0 h.r1 (hc.sep00 (VG.Proof.MlKem.Arm.row_lf hK).2.2.1 (VG.Proof.MlKem.Arm.row_lf hK).2.2.2.2.2.2.2.2.2.2.2.2.2.1 (VG.Proof.MlKem.Arm.row_lf hK).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) hc.buf0 (VG.Proof.MlKem.Arm.mem_rd_wr hc.buf0)
    h.rf.rs.acc h.rf.tmp fun s' k' p' => ?_
  exact ⟨h.rf.rs.kx.trans ((k'.x _).subL hp.ctx (VG.Proof.MlKem.Arm.row_lf hK).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2),
    by rw [k'.cs .r10 (by kdecide) (by kdecide), h.rf.rs.r10], by rw [k'.cs .r11 (by kdecide) (by kdecide), h.rf.r11],
    p'⟩

theorem rowI_ok (hK : K.WF) {s : State} (hj : j < K.k) (h : VG.Proof.MlKem.Arm.RH K L transpose ρ v i fl s₀ j s) :
    WP isa (.block (count .r10 K.k)) s fun s' =>
      VG.Proof.MlKem.Arm.RowInv K L transpose ρ v i fl s₀ (j + 1) s' ∧ s'.z = decide (j + 1 = K.k) := by
  have k4 := hK.k4
  exact WP.mono (VG.Proof.MlKem.Arm.count_ok (by omega) (by kdecide) (by kenc) h.r10) fun s' ⟨k', g', z'⟩ =>
    ⟨⟨h.kx.trans ((k'.weaken (by simp)).mono (fun _ h => absurd h List.not_mem_nil)), g',
      by rw [k'.cs .r11 (by kdecide) (by kdecide) (by kdecide), h.r11],
      polyIs_frame k'.frame (fun _ h => absurd h List.not_mem_nil) h.acc⟩, z'⟩

theorem rowBody_ok (hp : VG.Proof.MlKem.Arm.RowPre K L ρ v i fl s₀) (hj : j < K.k) {s : State} (h : VG.Proof.MlKem.Arm.RowInv K L transpose ρ v i fl s₀ j s) :
    WP isa (K.rowBody transpose) s fun s' => VG.Proof.MlKem.Arm.RowInv K L transpose ρ v i fl s₀ (j + 1) s' ∧ s'.z = decide (j + 1 = K.k) :=
  WP.seq (WP.mono (VG.Proof.MlKem.Arm.rowA_ok hp hj h) fun _ h₁ => WP.seq (WP.mono (VG.Proof.MlKem.Arm.rowB_ok hp h₁) fun _ h₂ =>
    WP.seq (WP.mono (VG.Proof.MlKem.Arm.rowC_ok h₂) fun _ h₃ => WP.seq (WP.mono (VG.Proof.MlKem.Arm.rowD_ok hp hj h₃) fun _ h₄ =>
    WP.seq (WP.mono (VG.Proof.MlKem.Arm.rowE_ok hp hj h₄) fun _ h₅ => WP.seq (WP.mono (VG.Proof.MlKem.Arm.rowF_ok hp hj h₅) fun _ h₆ =>
    WP.seq (WP.mono (VG.Proof.MlKem.Arm.rowG_ok hp h₆) fun _ h₇ => WP.seq (WP.mono (VG.Proof.MlKem.Arm.rowH_ok hp h₇) fun _ h₈ =>
      VG.Proof.MlKem.Arm.rowI_ok hp.wf hj h₈))))))))

end

theorem movc_ok {s : State} (c : Reg) {N : Nat} (he : encodable (BitVec.ofNat 32 N) = true) :
    WP isa (.block [.mov c (.imm (BitVec.ofNat 32 N))]) s fun s' =>
      VG.Proof.MlKem.Arm.KeptX [c] [] s s' ∧ s'.gpr c = BitVec.ofNat 32 N ∧ s'.mem = s.mem := by
  run_block [he]
  refine ⟨⟨fun r _ _ hx => ?_, rfl, rfl, rfl, Frame.refl _ _⟩, trivial⟩
  show (if r = c then _ else s.gpr r) = s.gpr r
  exact ite_eq_right (fun e : r = c => hx (by rw [e]; exact List.mem_singleton_self _))

theorem flagInit_ok {s : State} :
    WP isa (.block [.mov .r11 (.imm 1), .mov .r9 (.imm 0)]) s fun s' =>
      VG.Proof.MlKem.Arm.KeptX [.r9, .r11] [] s s' ∧ s'.gpr .r11 = 1 ∧ s'.gpr .r9 = 0 ∧ s'.mem = s.mem := by
  have e1 : encodable (1 : BitVec 32) = true := by decide
  have e0 : encodable (0 : BitVec 32) = true := by decide
  run_block [e1, e0]
  refine ⟨⟨fun r _ _ hx => ?_, rfl, rfl, rfl, Frame.refl _ _⟩, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  show (if r = .r9 then _ else if r = .r11 then _ else s.gpr r) = s.gpr r
  rw [ite_eq_right hx.1, ite_eq_right hx.2]

theorem rowSum_ok {K : KemLay} {L : VG.Proof.MlKem.Arm.Lay} {transpose : Bool} {ρ : List Byte} {v : Nat → VG.Spec.MlKem.Poly} {i : Nat}
    {fl : Bool} {s₀ : State} (hp : VG.Proof.MlKem.Arm.RowPre K L ρ v i fl s₀) :
    WP isa (K.rowSum transpose) s₀ (VG.Proof.MlKem.Arm.RowInv K L transpose ρ v i fl s₀ K.k) := by
  have hK := hp.wf
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.zeroPoly_ok hp.ctx (VG.Proof.MlKem.Arm.row_lf hK).2.2.1 (by kenc)) fun s₁ ⟨k₁, z₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.movc_ok .r10 (N := 0) (by decide)) fun s₂ ⟨k₂, g₂, m₂⟩ => ?_)
  refine wp_loop_ne (VG.Proof.MlKem.Arm.RowInv K L transpose ρ v i fl s₀) (N := K.k) (by kdecide) (fun j hj s h => VG.Proof.MlKem.Arm.rowBody_ok hp hj h)
    (fun _ h => h) ⟨?_, g₂, ?_, by rw [m₂]; exact z₁⟩
  · exact ((k₁.x _).subL hp.ctx (VG.Proof.MlKem.Arm.row_lf hK).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2).trans ((k₂.weaken (by simp)).mono (fun _ h => absurd h List.not_mem_nil))
  · rw [k₂.cs .r11 (by decide) (by decide) (by decide), k₁.cs .r11 (by decide) (by decide), hp.r11]
    simp [VG.Proof.MlKem.Arm.okRow]

/-! ## `dot` -/

theorem dotArgs_ok {K : KemLay} (hK : K.WF) {s : State} {P : BitVec 32} {j : Nat} (h7 : s.gpr .r7 = P)
    (h10 : s.gpr .r10 = BitVec.ofNat 32 j) :
    WP isa (.block (ptrTo .r0 .r7 K.oTmp :: slotAt .r1 .r10 (oPoly 0) ++ slotAt .r2 .r10 (oPoly K.k) ++
      [ptrTo .r3 .r7 K.oNtt])) s fun s' =>
      VG.Proof.MlKem.Arm.Only s s' ∧ s'.gpr .r0 = P + BitVec.ofNat 32 K.oTmp ∧
      s'.gpr .r1 = P + BitVec.ofNat 32 j <<< 10 + BitVec.ofNat 32 (oPoly 0) ∧
      s'.gpr .r2 = P + BitVec.ofNat 32 j <<< 10 + BitVec.ofNat 32 (oPoly K.k) ∧
      s'.gpr .r3 = P + BitVec.ofNat 32 K.oNtt := by
  have e1 : encodable (BitVec.ofNat 32 K.oTmp) = true := hK.enc (by omega)
  have e2 : encodable (BitVec.ofNat 32 (oPoly K.k)) = true := hK.enc (by omega)
  have e3 : encodable (BitVec.ofNat 32 K.oNtt) = true := hK.enc (by omega)
  have e4 : encodable (BitVec.ofNat 32 (oPoly 0)) = true := by decide
  run_block [slotAt, ptrTo, e1, e2, e3, e4, h7, h10]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, m2, m3, -⟩ := VG.Proof.MlKem.Arm.pres_ne hr hl
  simp only [m0, m1, m2, m3, ite_false]

/-- What `dot` changes: polynomials 11 and 12, and the working space of the callees. -/
abbrev dotW (K : KemLay) : List (Nat × Nat × Nat) := [(0, K.oAcc, 2048), (0, K.oNtt, 1024)]

/-- After the first `j` products. -/
structure DotInv (K : KemLay) (L : VG.Proof.MlKem.Arm.Lay) (a v : Nat → VG.Spec.MlKem.Poly) (s₀ : State) (j : Nat) (s : State) : Prop where
  kx : VG.Proof.MlKem.Arm.KeptX [.r10] (L.RL (VG.Proof.MlKem.Arm.dotW K)) s₀ s
  r10 : s.gpr .r10 = BitVec.ofNat 32 j
  acc : PolyIs s.mem (L.A 0 K.oAcc) (VG.Proof.MlKem.Arm.rowAcc a v j)

/-- The polynomials of the operands apart from what `dot` changes. -/
abbrev DotWVec (K : KemLay) : Prop := ∀ j < 2 * K.k, (VG.Proof.MlKem.Arm.dotW K).all (VG.Proof.MlKem.Arm.sep0 (oPoly j) 1024) = true

theorem dotW_vec {K : KemLay} (hK : K.WF) : VG.Proof.MlKem.Arm.DotWVec K := (by decide : ∀ k < 5, DotWVec (kOf k)) K.k (by have := hK.k4; omega)

/-- In `dotBody`, after the product. -/
structure DB (K : KemLay) (L : VG.Proof.MlKem.Arm.Lay) (a v : Nat → VG.Spec.MlKem.Poly) (s₀ : State) (j : Nat) (s : State) : Prop where
  kx : VG.Proof.MlKem.Arm.KeptX [.r10] (L.RL (VG.Proof.MlKem.Arm.dotW K)) s₀ s
  r10 : s.gpr .r10 = BitVec.ofNat 32 j
  acc : PolyIs s.mem (L.A 0 K.oAcc) (VG.Proof.MlKem.Arm.rowAcc a v j)
  tmp : PolyIs s.mem (L.A 0 K.oTmp) (multiplyNTTs (a j) (v j))

/-- In `dotBody`, after the sum. -/
structure DC (K : KemLay) (L : VG.Proof.MlKem.Arm.Lay) (a v : Nat → VG.Spec.MlKem.Poly) (s₀ : State) (j : Nat) (s : State) : Prop where
  kx : VG.Proof.MlKem.Arm.KeptX [.r10] (L.RL (VG.Proof.MlKem.Arm.dotW K)) s₀ s
  r10 : s.gpr .r10 = BitVec.ofNat 32 j
  acc : PolyIs s.mem (L.A 0 K.oAcc) (VG.Proof.MlKem.Arm.rowAcc a v (j + 1))

section
variable {K : KemLay} (hK : K.WF) {L : VG.Proof.MlKem.Arm.Lay} {a v : Nat → VG.Spec.MlKem.Poly} {s₀ : State} (hc₀ : VG.Proof.MlKem.Arm.Ctx L s₀)
    (ha : ∀ j < K.k, PolyIs s₀.mem (L.A 0 (oPoly j)) (a j)) (hv : ∀ j < K.k, PolyIs s₀.mem (L.A 0 (oPoly (K.k + j))) (v j))
    {j : Nat} (hj : j < K.k) {s : State} (h : VG.Proof.MlKem.Arm.DotInv K L a v s₀ j s)
include hK hc₀ ha hv hj h

omit ha hv in
theorem dot1_ok : WP isa (.block (ptrTo .r0 .r7 K.oTmp :: slotAt .r1 .r10 (oPoly 0) ++ slotAt .r2 .r10 (oPoly K.k) ++
      [ptrTo .r3 .r7 K.oNtt])) s fun s₁ => VG.Proof.MlKem.Arm.Only s s₁ ∧ s₁.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oTmp ∧
      s₁.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly j) ∧ s₁.gpr .r2 = L.ptr 0 + BitVec.ofNat 32 (oPoly (K.k + j)) ∧
      s₁.gpr .r3 = L.ptr 0 + BitVec.ofNat 32 K.oNtt := by
  have hc := h.kx.ctx (by kdecide) hc₀
  have eo : oPoly (K.k + j) = oPoly K.k + 1024 * j := by simp only [oPoly]; omega
  have eo' : oPoly j = oPoly 0 + 1024 * j := by simp only [oPoly]; try omega
  refine WP.mono (VG.Proof.MlKem.Arm.dotArgs_ok hK hc.r7 h.r10) fun s₁ ⟨o₁, m0, m1, m2, m3⟩ => ⟨o₁, m0, ?_, ?_, m3⟩
  · rw [m1, VG.Proof.MlKem.Arm.slot_eq _ (by offs), ← eo']
  · rw [m2, VG.Proof.MlKem.Arm.slot_eq _ (by offs), ← eo]

theorem dot2_ok {s₁ : State} (o₁ : VG.Proof.MlKem.Arm.Only s s₁) (m0 : s₁.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oTmp)
    (m1 : s₁.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly j)) (m2 : s₁.gpr .r2 = L.ptr 0 + BitVec.ofNat 32 (oPoly (K.k + j)))
    (m3 : s₁.gpr .r3 = L.ptr 0 + BitVec.ofNat 32 K.oNtt) : WP isa callMul s₁ (VG.Proof.MlKem.Arm.DB K L a v s₀ j) := by
  have hL := hc₀.ok
  have hc := h.kx.ctx (by kdecide) hc₀
  have as : PolyIs s.mem (L.A 0 (oPoly j)) (a j) :=
    Lay.polyIs_keep hL h.kx.frame (hc₀.sepAll0 (by offs) (VG.Proof.MlKem.Arm.dotW_vec hK j (by omega))) (ha j hj)
  have vs : PolyIs s.mem (L.A 0 (oPoly (K.k + j))) (v j) :=
    Lay.polyIs_keep hL h.kx.frame (hc₀.sepAll0 (by offs) (VG.Proof.MlKem.Arm.dotW_vec hK (K.k + j) (by omega))) (hv j hj)
  have hc₁ := hc.only o₁
  refine VG.Proof.MlKem.Arm.mulL hL m0 m1 m2 m3 (hc.sep00 (by offs) (by offs) (by offs)) (hc.sep00 (by offs) (by offs) (by offs))
    (hc.sep00 (by offs) (by offs) (by offs)) (hc.sep00 (by offs) (by offs) (by offs))
    (hc.sep00 (by offs) (by offs) (by offs)) hc₁.buf0 (VG.Proof.MlKem.Arm.mem_rd_wr hc₁.buf0) (VG.Proof.MlKem.Arm.mem_rd_wr hc₁.buf0) hc₁.buf0
    (by rw [o₁.mem]; exact as) (by rw [o₁.mem]; exact vs) fun s₂ k₂ p₂ => ⟨?_, ?_, ?_, p₂⟩
  · exact h.kx.trans ((o₁.x _ _).trans ((k₂.x _).subL hc₀ (by kdecide)))
  · rw [k₂.cs .r10 (by kdecide) (by kdecide), o₁.cs .r10 (by kdecide) (by kdecide), h.r10]
  · refine Lay.polyIs_keep hL k₂.frame (hc.sepAll0 (by kdecide) (by kdecide)) ?_
    rw [o₁.mem]; exact h.acc

omit ha hv hj h in
theorem dot3_ok {s₂ : State} (r : VG.Proof.MlKem.Arm.DB K L a v s₀ j s₂) :
    WP isa (.block [ptrTo .r0 .r7 K.oAcc, ptrTo .r1 .r7 K.oTmp]) s₂ fun s₃ => VG.Proof.MlKem.Arm.DB K L a v s₀ j s₃ ∧
      s₃.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧ s₃.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 K.oTmp := by
  have hc := r.kx.ctx (by kdecide) hc₀
  exact WP.mono (VG.Proof.MlKem.Arm.accArgs_ok hc.r7 (by kenc) (by kenc)) fun s₃ ⟨o₃, a0, a1⟩ =>
    ⟨⟨r.kx.trans (o₃.x _ _), by rw [o₃.cs .r10 (by kdecide) (by kdecide), r.r10], by rw [o₃.mem]; exact r.acc,
      by rw [o₃.mem]; exact r.tmp⟩, a0, a1⟩

omit ha hv hj h in
theorem dot4_ok {s₃ : State} (r : VG.Proof.MlKem.Arm.DB K L a v s₀ j s₃) (a0 : s₃.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc)
    (a1 : s₃.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 K.oTmp) : WP isa callAdd s₃ (VG.Proof.MlKem.Arm.DC K L a v s₀ j) := by
  have hc := r.kx.ctx (by kdecide) hc₀
  exact VG.Proof.MlKem.Arm.addL hc₀.ok a0 a1 (hc.sep00 (by kdecide) (by kdecide) (by kdecide)) hc.buf0 (VG.Proof.MlKem.Arm.mem_rd_wr hc.buf0)
    r.acc r.tmp fun s₄ k₄ p₄ => ⟨r.kx.trans ((k₄.x _).subL hc₀ (by kdecide)),
      by rw [k₄.cs .r10 (by kdecide) (by kdecide), r.r10], p₄⟩

omit hc₀ ha hv h in
theorem dot5_ok {s₄ : State} (r : VG.Proof.MlKem.Arm.DC K L a v s₀ j s₄) :
    WP isa (.block (count .r10 K.k)) s₄ fun s' => VG.Proof.MlKem.Arm.DotInv K L a v s₀ (j + 1) s' ∧ s'.z = decide (j + 1 = K.k) := by
  have k4 := hK.k4
  exact WP.mono (VG.Proof.MlKem.Arm.count_ok (by omega) (by kdecide) (by kenc) r.r10) fun s' ⟨k', g', z'⟩ =>
    ⟨⟨r.kx.trans (k'.mono (fun _ h => absurd h List.not_mem_nil)), g',
      polyIs_frame k'.frame (fun _ h => absurd h List.not_mem_nil) r.acc⟩, z'⟩

end

theorem dotBody_ok {K : KemLay} (hK : K.WF) {L : VG.Proof.MlKem.Arm.Lay} {a v : Nat → VG.Spec.MlKem.Poly} {s₀ : State} (hc₀ : VG.Proof.MlKem.Arm.Ctx L s₀)
    (ha : ∀ j < K.k, PolyIs s₀.mem (L.A 0 (oPoly j)) (a j)) (hv : ∀ j < K.k, PolyIs s₀.mem (L.A 0 (oPoly (K.k + j))) (v j))
    {j : Nat} (hj : j < K.k) {s : State} (h : VG.Proof.MlKem.Arm.DotInv K L a v s₀ j s) :
    WP isa K.dotBody s fun s' => VG.Proof.MlKem.Arm.DotInv K L a v s₀ (j + 1) s' ∧ s'.z = decide (j + 1 = K.k) :=
  WP.seq (WP.mono (VG.Proof.MlKem.Arm.dot1_ok hK hc₀ hj h) fun _ ⟨o₁, m0, m1, m2, m3⟩ =>
    WP.seq (WP.mono (VG.Proof.MlKem.Arm.dot2_ok hK hc₀ ha hv hj h o₁ m0 m1 m2 m3) fun _ r₂ =>
    WP.seq (WP.mono (VG.Proof.MlKem.Arm.dot3_ok hK hc₀ r₂) fun _ ⟨r₃, a0, a1⟩ =>
    WP.seq (WP.mono (VG.Proof.MlKem.Arm.dot4_ok hK hc₀ r₃ a0 a1) fun _ r₄ => VG.Proof.MlKem.Arm.dot5_ok hK hj r₄))))

theorem dot_ok {K : KemLay} (hK : K.WF) {L : VG.Proof.MlKem.Arm.Lay} {a v : Nat → VG.Spec.MlKem.Poly} {s₀ : State} (hc₀ : VG.Proof.MlKem.Arm.Ctx L s₀)
    (ha : ∀ j < K.k, PolyIs s₀.mem (L.A 0 (oPoly j)) (a j)) (hv : ∀ j < K.k, PolyIs s₀.mem (L.A 0 (oPoly (K.k + j))) (v j)) :
    WP isa K.dot s₀ fun s => VG.Proof.MlKem.Arm.KeptX [.r10] (L.RL (VG.Proof.MlKem.Arm.dotW K)) s₀ s ∧ PolyIs s.mem (L.A 0 K.oAcc) (VG.Proof.MlKem.KPke.dotK a v K.k) := by
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.zeroPoly_ok hc₀ (by kdecide) (by kenc)) fun s₁ ⟨k₁, z₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.movc_ok .r10 (N := 0) (by kdecide)) fun s₂ ⟨k₂, g₂, m₂⟩ => ?_)
  refine wp_loop_ne (VG.Proof.MlKem.Arm.DotInv K L a v s₀) (N := K.k) (by kdecide) (fun j hj s h => VG.Proof.MlKem.Arm.dotBody_ok hK hc₀ ha hv hj h)
    (fun _ h => ⟨h.kx, by rw [← VG.Proof.MlKem.Arm.rowAcc_eq]; exact h.acc⟩)
    ⟨((k₁.x _).subL hc₀ (by kdecide)).trans (k₂.mono (fun _ h => absurd h List.not_mem_nil)), g₂,
      by rw [m₂]; exact z₁⟩

/-! ## Blocks of the top-level functions -/

theorem at384_eq (p : BitVec 32) {i : Nat} (_h : 384 * i < 2 ^ 32) :
    p + BitVec.ofNat 32 i <<< 8 + BitVec.ofNat 32 i <<< 7 = p + BitVec.ofNat 32 (384 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem foldl_shl (v : BitVec 32) : ∀ (ts : List Nat) (x : BitVec 32),
    ts.foldl (fun y t => y + v <<< t) x = x + v * BitVec.ofNat 32 (ts.map (2 ^ ·)).sum
  | [], x => by simp
  | t :: ts, x => by
    rw [List.foldl_cons, VG.Proof.MlKem.Arm.foldl_shl v ts, List.map_cons, List.sum_cons, BitVec.ofNat_add, BitVec.mul_add,
      BitVec.shiftLeft_eq_mul_twoPow, ← BitVec.add_assoc]
    congr 3
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_twoPow]

/-- `d ← d + c <<< t` for each `t` of `ts`. -/
theorem addSh_ok {d c : Reg} (hdc : d ≠ c) :
    ∀ (ts : List Nat), ts.all (fun t => 1 ≤ t && t ≤ 31) = true → ∀ (s : State),
    WP isa (.block (ts.map fun t => .dp .add d d (.shifted c .lsl t))) s fun s' =>
      s'.gpr d = ts.foldl (fun y t => y + s.gpr c <<< t) (s.gpr d) ∧ (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp
  | [], _, s => WP.block_nil ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | t :: ts, h, s => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h⟩ := h
    rw [List.map_cons, ← List.singleton_append, WP.block_append_iff]
    have hs : WP isa (.block [.dp .add d d (.shifted c .lsl t)]) s fun s₁ =>
        s₁.gpr d = s.gpr d + s.gpr c <<< t ∧ (∀ r, r ≠ d → s₁.gpr r = s.gpr r) ∧
        s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.sp = s.sp := by
      run_block [h1, h2]
      exact ⟨trivial, fun r hr => ite_eq_right hr, trivial⟩
    refine WP.mono hs fun s₁ ⟨e, o, m, rd, wr, sp⟩ => WP.mono (VG.Proof.MlKem.Arm.addSh_ok hdc ts h s₁) fun s' ⟨e', o', m', rd', wr', sp'⟩ =>
      ⟨?_, fun r hr => (o' r hr).trans (o r hr), m'.trans m, rd'.trans rd, wr'.trans wr, sp'.trans sp⟩
    rw [e', e, o c (Ne.symm hdc), List.foldl_cons]

/-- `d ← b + 32 d_u · c` (`KemLay.atU`), changing no other register. -/
theorem atU_ok {K : KemLay} (hK : K.WF) {d b c : Reg} (hdc : d ≠ c) (s : State) :
    WP isa (.block (K.atU d b c)) s fun s' =>
      s'.gpr d = s.gpr b + s.gpr c * BitVec.ofNat 32 K.uLen ∧ (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hs := hK.sh
  rw [KemLay.atU, ← hK.shSum]
  have hu := hK.shSum
  have h1 := hK.du1
  match e : K.uShifts, hs with
  | [], _ =>
    rw [e] at hu
    simp only [List.map_nil, List.sum_nil, KemLay.uLen, KemLay.du] at hu h1
    omega
  | t :: ts, hs =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨⟨h1, h2⟩, hs⟩ := hs
    rw [atShifts, ← List.singleton_append, WP.block_append_iff]
    have hb : WP isa (.block [.dp .add d b (.shifted c .lsl t)]) s fun s₁ =>
        s₁.gpr d = s.gpr b + s.gpr c <<< t ∧ (∀ r, r ≠ d → s₁.gpr r = s.gpr r) ∧
        s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.sp = s.sp := by
      run_block [h1, h2]
      exact ⟨trivial, fun r hr => ite_eq_right hr, trivial⟩
    refine WP.mono hb fun s₁ ⟨e₁, o, m, rd, wr, sp⟩ => WP.mono (VG.Proof.MlKem.Arm.addSh_ok hdc ts hs s₁)
      fun s' ⟨e', o', m', rd', wr', sp'⟩ =>
      ⟨?_, fun r hr => (o' r hr).trans (o r hr), m'.trans m, rd'.trans rd, wr'.trans wr, sp'.trans sp⟩
    rw [e', e₁, o c (Ne.symm hdc), VG.Proof.MlKem.Arm.foldl_shl, List.map_cons, List.sum_cons, BitVec.ofNat_add, BitVec.mul_add,
      BitVec.shiftLeft_eq_mul_twoPow, ← BitVec.add_assoc]
    congr 3
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_twoPow]

theorem atU_eq (p : BitVec 32) (u i : Nat) : p + BitVec.ofNat 32 i * BitVec.ofNat 32 u = p + BitVec.ofNat 32 (u * i) := by
  rw [← BitVec.ofNat_mul, Nat.mul_comm]

section
variable {s : State} {P : BitVec 32} {i : Nat}

/-- `r0` at `o` in `scratch`, `r1` at polynomial `i` of the array at `o'`. -/
theorem ptrSlot_ok {o o' : Nat} (h7 : s.gpr .r7 = P) (h9 : s.gpr .r9 = BitVec.ofNat 32 i)
    (he : encodable (BitVec.ofNat 32 o) = true) (he' : encodable (BitVec.ofNat 32 o') = true) :
    WP isa (.block (ptrTo .r0 .r7 o :: slotAt .r1 .r9 o')) s fun s' =>
      VG.Proof.MlKem.Arm.Only s s' ∧ s'.gpr .r0 = P + BitVec.ofNat 32 o ∧ s'.gpr .r1 = P + BitVec.ofNat 32 i <<< 10 + BitVec.ofNat 32 o' := by
  run_block [slotAt, ptrTo, he, he', h7, h9]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, -, -, -⟩ := VG.Proof.MlKem.Arm.pres_ne hr hl
  simp only [m0, m1, ite_false]

/-- `r0` at `o` in `scratch`, `r1` at `b + 384 i`. -/
theorem ptr384_ok {o : Nat} {b : Reg} {B : BitVec 32} (hb : b = .r5 ∨ b = .r6) (h7 : s.gpr .r7 = P)
    (hB : s.gpr b = B) (h9 : s.gpr .r9 = BitVec.ofNat 32 i) (he : encodable (BitVec.ofNat 32 o) = true) :
    WP isa (.block (ptrTo .r0 .r7 o :: at384 .r1 b .r9)) s fun s' =>
      VG.Proof.MlKem.Arm.Only s s' ∧ s'.gpr .r0 = P + BitVec.ofNat 32 o ∧ s'.gpr .r1 = B + BitVec.ofNat 32 i <<< 8 + BitVec.ofNat 32 i <<< 7 := by
  rcases hb with rfl | rfl <;>
  · run_block [at384, ptrTo, he, h7, hB, h9]
    refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
    obtain ⟨m0, m1, -, -, -⟩ := VG.Proof.MlKem.Arm.pres_ne hr hl
    simp only [m0, m1, ite_false]

/-- `r0` at polynomial `i` of the array at `o'`, `r1` at `b + 384 i`. -/
theorem slot384_ok {o' : Nat} {b : Reg} {B : BitVec 32} (hb : b = .r5 ∨ b = .r6) (h7 : s.gpr .r7 = P)
    (hB : s.gpr b = B) (h9 : s.gpr .r9 = BitVec.ofNat 32 i) (he' : encodable (BitVec.ofNat 32 o') = true) :
    WP isa (.block (slotAt .r0 .r9 o' ++ at384 .r1 b .r9)) s fun s' =>
      VG.Proof.MlKem.Arm.Only s s' ∧ s'.gpr .r0 = P + BitVec.ofNat 32 i <<< 10 + BitVec.ofNat 32 o' ∧
      s'.gpr .r1 = B + BitVec.ofNat 32 i <<< 8 + BitVec.ofNat 32 i <<< 7 := by
  rcases hb with rfl | rfl <;>
  · run_block [at384, slotAt, ptrTo, he', h7, hB, h9]
    refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
    obtain ⟨m0, m1, -, -, -⟩ := VG.Proof.MlKem.Arm.pres_ne hr hl
    simp only [m0, m1, ite_false]

end

/-! ## The end of the top-level functions -/

theorem mem_rd_wr' {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

theorem topEnd_ok {L : VG.Proof.MlKem.Arm.Lay} {s₀ s : State} (hc : VG.Proof.MlKem.Arm.Ctx L s) (hsav : VG.Proof.MlKem.Arm.Saved s.mem (L.A 0 840) s₀.gpr)
    (hlr : s.mem.readW (L.A 0 872) 32 = s₀.gpr .lr) :
    WP isa (.block topEnd) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .r0 = s.gpr .r11 ∧
      s'.mem = s.mem ∧ s'.sp = s.sp := by
  have fs := hc.fit
  rw [topEnd, List.append_assoc, WP.block_append_iff]
  have e7 := hc.r7
  have hk : WP isa (.block [.mov .r0 (.reg .r11), .mov .r3 (.reg .r7)]) s fun s' =>
      s'.gpr .r0 = s.gpr .r11 ∧ s'.gpr .r3 = L.ptr 0 ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
    run_block [e7]
  refine WP.mono hk fun s₁ ⟨r0, r3, m₁, rd₁, wr₁, sp₁⟩ => ?_
  rw [WP.block_append_iff]
  have e3 : State.addr (s₁.gpr .r3) + BitVec.ofNat 64 840 = L.A 0 840 := by rw [r3]
  refine WP.mono (restoreRegs_ok .r3 (by decide) (off := 840) (by decide)
    (by rw [r3]; exact fit_le (by decide) fs) (g := s₀.gpr) (by rw [e3, m₁]; exact hsav)
    fun i hi => by
      rw [e3, rd₁, wr₁, add_ofNat_add]
      exact VG.Proof.MlKem.Arm.mem_rd_wr' (hc.cs (o := 840 + 4 * i) (l := 4) (by omega) _ _ ⟨_, List.mem_singleton_self _,
        Region.contains_self _ _⟩))
    fun s₂ h₂ => ?_
  have g3 : s₂.gpr .r3 = L.ptr 0 := by rw [h₂.other .r3 (by decide), r3]
  have e872 : State.addr (s₂.gpr .r3 + BitVec.ofNat 32 (oSave + 32)) = L.A 0 872 := by
    rw [g3]; exact hc.addr (by decide)
  have i12 : InRegions (s₂.rd ++ s₂.wr) (State.addr (s₂.gpr .r3 + BitVec.ofNat 32 (oSave + 32))) 4 := by
    rw [e872, h₂.rd, h₂.wr, rd₁, wr₁]
    exact VG.Proof.MlKem.Arm.mem_rd_wr' (hc.cs (o := 872) (l := 4) (by decide) _ _ ⟨_, List.mem_singleton_self _,
      Region.contains_self _ _⟩)
  have ho : oSave + 32 < 4096 := by decide
  have hl : WP isa (.block [.ldr .lr .r3 (oSave + 32)]) s₂ fun s' =>
      s'.gpr .lr = s₂.mem.readW (State.addr (s₂.gpr .r3 + BitVec.ofNat 32 (oSave + 32))) 32 ∧
      (∀ r, r ≠ .lr → s'.gpr r = s₂.gpr r) ∧ s'.mem = s₂.mem ∧ s'.sp = s₂.sp := by
    run_block [i12, ho, and_self, and_true]
    exact ⟨trivial, fun r hr => by simp [hr]⟩
  refine WP.mono hl fun s' ⟨lr, rr, m, sp⟩ => ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · by_cases e : r = .lr
    · subst e
      rw [lr, e872, h₂.mem, m₁]; exact hlr
    · have hs : ∀ r ∈ preserved, r ≠ .lr → ∃ i < 8, savedRegs.getD i .r4 = r := by decide
      obtain ⟨i, hi, rfl⟩ := hs r hr e
      rw [rr _ e]; exact h₂.loaded i hi
  · rw [rr .r0 (by decide), h₂.other .r0 (by decide), r0]
  · rw [m, h₂.mem, m₁]
  · rw [sp, h₂.sp, sp₁]

end VG.Proof.MlKem.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.HashCT`. -/
section

/-!
# ML-KEM-768 on 32-bit ARM: the hash routine in constant time

Two runs of `hash` from states whose buffers are the same (`HashOk` of the
same layout, and the same stack pointer) leak the same trace (`hash_ct`): the
blocks that set up the arguments access no memory (`relct_noMem`), the Keccak
state is zeroed through `r7` (the taint analysis), and the calls of the sponge
functions are on the same arguments in both runs (`absorb_ct`, …), the
positions being those of the same lengths.
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.Sha3 (rates)
open VG.Proof.MlKem.Arm.Sample (taint_block relct_wp)

/-! ## Blocks that access no memory -/

/-- An instruction that accesses no memory. -/
def noMem : Instr → Bool
  | .ldr .. | .str .. | .ldrb .. | .strb .. | .ldrSp .. | .push _ | .pop .. => false
  | _ => true

theorem addrs_noMem {i : Instr} (h : VG.Proof.MlKem.Arm.noMem i = true) (s : State) : addrs i s = [] := by
  cases i <;> first | rfl | simp [VG.Proof.MlKem.Arm.noMem] at h

theorem execBlock_noMem : ∀ {is : List Instr}, is.all VG.Proof.MlKem.Arm.noMem = true → ∀ {s s' : State} {t : List Leak},
    execBlock isa is s = some (s', t) → t = []
  | [], _, _, _, _, h => by simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
  | i :: is, hm, s, s', t, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hm
    simp only [execBlock] at h
    split at h
    · cases h
    · obtain ⟨⟨s'', t'⟩, h₁, h₂⟩ := Option.map_eq_some_iff.mp h
      cases h₂
      rw [VG.Proof.MlKem.Arm.addrs_noMem hm.1 s]
      simpa using VG.Proof.MlKem.Arm.execBlock_noMem hm.2 h₁

/-- A block that accesses no memory leaks nothing. -/
theorem relct_noMem {P : State → State → Prop} {is : List Instr} (h : is.all VG.Proof.MlKem.Arm.noMem = true) :
    RelCT isa P (.block is) fun _ _ => True := fun _ _ _ _ _ _ _ e₁ e₂ => by
  rw [Exec.block_iff] at e₁ e₂
  rw [VG.Proof.MlKem.Arm.execBlock_noMem h e₁, VG.Proof.MlKem.Arm.execBlock_noMem h e₂]; exact ⟨rfl, trivial⟩

/-- The empty block. -/
theorem relct_nil {P : State → State → Prop} : RelCT isa P (.block []) P := fun _ _ _ _ _ _ hp e₁ e₂ => by
  rw [Exec.block_iff] at e₁ e₂
  simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
  obtain ⟨rfl, rfl⟩ := e₁
  obtain ⟨rfl, rfl⟩ := e₂
  exact ⟨rfl, hp⟩

theorem kargs_noMem (rate : Nat) (first : Bool) (p : Piece) :
    (keccakArgs rate first ++ pieceArgs p).all VG.Proof.MlKem.Arm.noMem = true := by
  cases first <;> rfl

theorem pargs_noMem (rate sfx : Nat) :
    (keccakArgs rate false ++ ([.mov .r3 (.imm (BitVec.ofNat 32 sfx))] : List Instr)).all VG.Proof.MlKem.Arm.noMem = true := rfl

/-! ## The absorbs -/

/-- After the arguments of an `absorb` or a `squeeze` of piece `p` from position `X`. -/
structure KA (L : VG.Proof.MlKem.Arm.Lay) (idx : Reg → Nat) (rate : Nat) (p : Piece) (X : Nat) (s₀ s : State) : Prop where
  rg : VG.Proof.MlKem.Arm.Rg s₀ s
  r0 : s.gpr .r0 = L.ptr 0
  r1 : s.gpr .r1 = BitVec.ofNat 32 rate
  r2 : s.gpr .r2 = BitVec.ofNat 32 X
  r3 : s.gpr .r3 = L.ptr (idx p.base) + BitVec.ofNat 32 p.off
  r12 : s.gpr .r12 = BitVec.ofNat 32 p.len
  lr : s.gpr .lr = L.ptr 0 + BitVec.ofNat 32 200

theorem ka_ok {L : VG.Proof.MlKem.Arm.Lay} {idx : Reg → Nat} {rate : Nat} (hre : encodable (BitVec.ofNat 32 rate) = true)
    {s₀ s : State} (hc : VG.Proof.MlKem.Arm.Ctx L s₀) {first : Bool} {X : Nat} {p : Piece} {w : Bool} (hp : VG.Proof.MlKem.Arm.PieceOk L idx s₀ w p)
    (hg : VG.Proof.MlKem.Arm.Rg s₀ s) (hX : VG.Proof.MlKem.Arm.Pos first s = X) :
    WP isa (.block (keccakArgs rate first ++ pieceArgs p)) s (VG.Proof.MlKem.Arm.KA L idx rate p X s₀) :=
  WP.mono (VG.Proof.MlKem.Arm.kargs_ok first hp.base hre hp.oenc hp.lenc) fun s₁ ⟨o₁, g0, g1, g2, g3, g12, glr⟩ =>
    ⟨hg.kept (o₁.kept []), by rw [g0, (hg.ctx hc).r7], g1, by rw [g2, VG.Proof.MlKem.Arm.pos_r2, hX],
      by rw [g3, hg.cs _ hp.base.1 hp.base.2, hp.ptr], g12, by rw [glr, (hg.ctx hc).r7]⟩

theorem absorbs_ct {L : VG.Proof.MlKem.Arm.Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates)
    (hre : encodable (BitVec.ofNat 32 rate) = true) {s₀₁ s₀₂ : State} (hc₁ : VG.Proof.MlKem.Arm.Ctx L s₀₁) (hc₂ : VG.Proof.MlKem.Arm.Ctx L s₀₂)
    (hsp : s₀₁.sp = s₀₂.sp) :
    ∀ (ps : List Piece) (first : Bool) (X : Nat),
      (∀ p ∈ ps, VG.Proof.MlKem.Arm.PieceOk L idx s₀₁ false p ∧ VG.Proof.MlKem.Arm.PieceOk L idx s₀₂ false p) → X < rate →
      RelCT isa (fun a b => VG.Proof.MlKem.Arm.Rg s₀₁ a ∧ VG.Proof.MlKem.Arm.Rg s₀₂ b ∧ VG.Proof.MlKem.Arm.Pos first a = X ∧ VG.Proof.MlKem.Arm.Pos first b = X) (absorbs rate first ps)
        (fun a b => VG.Proof.MlKem.Arm.Rg s₀₁ a ∧ VG.Proof.MlKem.Arm.Rg s₀₂ b ∧ ∃ Y, Y < rate ∧ VG.Proof.MlKem.Arm.Pos (first && ps.isEmpty) a = Y ∧
          VG.Proof.MlKem.Arm.Pos (first && ps.isEmpty) b = Y)
  | [], first, X, _, hX =>
    RelCT.mono VG.Proof.MlKem.Arm.relct_nil (fun _ _ h => h) fun a b ⟨h1, h2, h3, h4⟩ =>
      ⟨h1, h2, X, hX, by simpa using h3, by simpa using h4⟩
  | p :: ps, first, X, hps, hX => by
    obtain ⟨hp₁, hp₂⟩ := hps p (List.mem_cons_self ..)
    have rpos := VG.Proof.MlKem.Arm.rate_pos hrate
    refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.KA L idx rate p X s₀₁ a ∧ VG.Proof.MlKem.Arm.KA L idx rate p X s₀₂ b)
      (relct_wp (VG.Proof.MlKem.Arm.relct_noMem (VG.Proof.MlKem.Arm.kargs_noMem _ _ _)) fun a b hab =>
        ⟨VG.Proof.MlKem.Arm.ka_ok hre hc₁ hp₁ hab.1 hab.2.2.1, VG.Proof.MlKem.Arm.ka_ok hre hc₂ hp₂ hab.2.1 hab.2.2.2⟩) ?_
    have hA : ∀ {s₀ s : State}, VG.Proof.MlKem.Arm.Ctx L s₀ → VG.Proof.MlKem.Arm.PieceOk L idx s₀ false p → VG.Proof.MlKem.Arm.KA L idx rate p X s₀ s →
        AbsorbArgs s (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) (L.ptr (idx p.base) + BitVec.ofNat 32 p.off)
          rate X p.len := fun hc hp h =>
      VG.Proof.MlKem.Arm.absorbArgs_of hrate (h.rg.ctx hc) h.rg hp hX h.r0 h.r1 h.r2 h.r3 h.r12 h.lr
    refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.Rg s₀₁ a ∧ VG.Proof.MlKem.Arm.Rg s₀₂ b ∧ VG.Proof.MlKem.Arm.Pos false a = (X + p.len) % rate ∧
      VG.Proof.MlKem.Arm.Pos false b = (X + p.len) % rate) ?_ ?_
    · refine RelCT.mono (relct_wp (F₁ := fun s' => VG.Proof.MlKem.Arm.Rg s₀₁ s' ∧ (s'.gpr .r0).toNat = (X + p.len) % rate)
        (F₂ := fun s' => VG.Proof.MlKem.Arm.Rg s₀₂ s' ∧ (s'.gpr .r0).toNat = (X + p.len) % rate) (absorb_ct fun a b hab => ⟨by rw [hab.1.rg.sp, hab.2.rg.sp, hsp], _, _, _, _, _, _,
        hA hc₁ hp₁ hab.1, hA hc₂ hp₂ hab.2⟩) fun a b hab =>
        ⟨absorb_ok (hA hc₁ hp₁ hab.1) fun s' k' _ r' => ⟨hab.1.rg.kept k', r'⟩,
         absorb_ok (hA hc₂ hp₂ hab.2) fun s' k' _ r' => ⟨hab.2.rg.kept k', r'⟩⟩) (fun _ _ h => h)
        fun a b ⟨⟨g₁, r₁⟩, ⟨g₂, r₂⟩⟩ => ⟨g₁, g₂, r₁, r₂⟩
    · refine RelCT.mono (VG.Proof.MlKem.Arm.absorbs_ct hrate hre hc₁ hc₂ hsp ps false ((X + p.len) % rate)
        (fun q hq => hps q (List.mem_cons_of_mem _ hq)) (Nat.mod_lt _ rpos)) (fun _ _ h => h)
        fun a b ⟨g₁, g₂, Y, hY, e₁, e₂⟩ => ⟨g₁, g₂, Y, hY, by simpa using e₁, by simpa using e₂⟩

/-! ## The whole hash -/

/-- A state `hash` may run from. -/
structure HashOk (L : VG.Proof.MlKem.Arm.Lay) (idx : Reg → Nat) (ins outs : List Piece) (s : State) : Prop where
  ctx : VG.Proof.MlKem.Arm.Ctx L s
  ins : ∀ p ∈ ins, VG.Proof.MlKem.Arm.PieceOk L idx s false p
  outs : ∀ p ∈ outs, VG.Proof.MlKem.Arm.PieceOk L idx s true p

/-- After the arguments of a `pad` from position `Y`. -/
structure PA (L : VG.Proof.MlKem.Arm.Lay) (rate sfx Y : Nat) (s₀ s : State) : Prop where
  rg : VG.Proof.MlKem.Arm.Rg s₀ s
  r0 : s.gpr .r0 = L.ptr 0
  r1 : s.gpr .r1 = BitVec.ofNat 32 rate
  r2 : s.gpr .r2 = BitVec.ofNat 32 Y
  r3 : s.gpr .r3 = BitVec.ofNat 32 sfx
  lr : s.gpr .lr = L.ptr 0 + BitVec.ofNat 32 200

theorem hash_ct {L : VG.Proof.MlKem.Arm.Lay} {idx : Reg → Nat} {rate sfx : Nat} (hrate : rate ∈ rates)
    (hre : encodable (BitVec.ofNat 32 rate) = true) (hse : encodable (BitVec.ofNat 32 sfx) = true)
    {ins : List Piece} {q : Piece} (hne : ins ≠ []) {P : State → State → Prop}
    (hP : ∀ a b, P a b → VG.Proof.MlKem.Arm.HashOk L idx ins [q] a ∧ VG.Proof.MlKem.Arm.HashOk L idx ins [q] b ∧ a.sp = b.sp) :
    RelCT isa P (hash rate sfx ins [q]) fun _ _ => True := by
  refine RelCT.mono (P := fun a b => ∃ x : State × State, a = x.1 ∧ b = x.2 ∧ VG.Proof.MlKem.Arm.HashOk L idx ins [q] x.1 ∧
    VG.Proof.MlKem.Arm.HashOk L idx ins [q] x.2 ∧ x.1.sp = x.2.sp) (RelCT.exists_ fun ⟨s₀₁, s₀₂⟩ => ?_)
    (fun a b h => ⟨(a, b), rfl, rfl, hP a b h⟩) (fun _ _ h => h)
  by_cases hH : VG.Proof.MlKem.Arm.HashOk L idx ins [q] s₀₁ ∧ VG.Proof.MlKem.Arm.HashOk L idx ins [q] s₀₂ ∧ s₀₁.sp = s₀₂.sp
  swap
  · exact RelCT.of_false fun a b h => hH ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  obtain ⟨h₁, h₂, hsp⟩ := hH
  have hc₁ := h₁.ctx
  have hc₂ := h₂.ctx
  have rpos := VG.Proof.MlKem.Arm.rate_pos hrate
  have g₀ : ∀ {s₀ : State}, VG.Proof.MlKem.Arm.Rg s₀ s₀ := ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩
  refine RelCT.mono (P := fun a b => a = s₀₁ ∧ b = s₀₂) ?_ (fun a b h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)
  -- the state set to zero
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.Rg s₀₁ a ∧ VG.Proof.MlKem.Arm.Rg s₀₂ b)
    (RelCT.mono (relct_wp (F₁ := VG.Proof.MlKem.Arm.Rg s₀₁) (F₂ := VG.Proof.MlKem.Arm.Rg s₀₂) (taint_block [.r7] (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hab.1, hab.2, hc₁.r7, hc₂.r7]) (by taint_decide))
      fun a b hab => ⟨by rw [hab.1]; exact WP.mono (VG.Proof.MlKem.Arm.zeroState_ok hc₁) fun s' h => (h.1.rg),
        by rw [hab.2]; exact WP.mono (VG.Proof.MlKem.Arm.zeroState_ok hc₂) fun s' h => (h.1.rg)⟩) (fun _ _ h => h) fun _ _ h => h) ?_
  -- the absorbs
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.Rg s₀₁ a ∧ VG.Proof.MlKem.Arm.Rg s₀₂ b ∧ ∃ Y, Y < rate ∧ VG.Proof.MlKem.Arm.Pos false a = Y ∧ VG.Proof.MlKem.Arm.Pos false b = Y)
    (RelCT.mono (VG.Proof.MlKem.Arm.absorbs_ct hrate hre hc₁ hc₂ hsp ins true 0 (fun p hp => ⟨h₁.ins p hp, h₂.ins p hp⟩) rpos)
      (fun a b h => ⟨h.1, h.2, rfl, rfl⟩) fun a b ⟨g₁, g₂, Y, hY, e₁, e₂⟩ => ⟨g₁, g₂, Y, hY, ?_, ?_⟩) ?_
  · cases ins with
    | nil => exact absurd rfl hne
    | cons _ _ => exact e₁
  · cases ins with
    | nil => exact absurd rfl hne
    | cons _ _ => exact e₂
  -- the padding
  refine RelCT.mono (P := fun a b => ∃ Y, Y < rate ∧ VG.Proof.MlKem.Arm.Rg s₀₁ a ∧ VG.Proof.MlKem.Arm.Rg s₀₂ b ∧ VG.Proof.MlKem.Arm.Pos false a = Y ∧ VG.Proof.MlKem.Arm.Pos false b = Y)
    (RelCT.exists_ fun Y => ?_) (fun a b ⟨g₁, g₂, Y, hY, e₁, e₂⟩ => ⟨Y, hY, g₁, g₂, e₁, e₂⟩) (fun _ _ h => h)
  by_cases hY : Y < rate
  swap
  · exact RelCT.of_false fun a b h => hY h.1
  have pa : ∀ (s₀ s : State), VG.Proof.MlKem.Arm.Ctx L s₀ → VG.Proof.MlKem.Arm.Rg s₀ s → VG.Proof.MlKem.Arm.Pos false s = Y →
      WP isa (.block (keccakArgs rate false ++ ([.mov .r3 (.imm (BitVec.ofNat 32 sfx))] : List Instr))) s
        (VG.Proof.MlKem.Arm.PA L rate sfx Y s₀) := fun s₀ s hc hg hX =>
    WP.mono (VG.Proof.MlKem.Arm.pargs_ok hre hse) fun s' ⟨o', g0, g1, g2, g3, glr⟩ =>
      ⟨hg.kept (o'.kept []), by rw [g0, (hg.ctx hc).r7], g1,
        by rw [g2, ← hX, show VG.Proof.MlKem.Arm.Pos false s = (s.gpr .r0).toNat from rfl, BitVec.ofNat_toNat, BitVec.setWidth_eq],
        g3, by rw [glr, (hg.ctx hc).r7]⟩
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.PA L rate sfx Y s₀₁ a ∧ VG.Proof.MlKem.Arm.PA L rate sfx Y s₀₂ b)
    (relct_wp (VG.Proof.MlKem.Arm.relct_noMem (VG.Proof.MlKem.Arm.pargs_noMem _ _)) fun a b hab =>
      ⟨pa _ _ hc₁ hab.2.1 hab.2.2.2.1, pa _ _ hc₂ hab.2.2.1 hab.2.2.2.2⟩) ?_
  have hPA : ∀ {s₀ s : State}, VG.Proof.MlKem.Arm.Ctx L s₀ → VG.Proof.MlKem.Arm.PA L rate sfx Y s₀ s →
      PadArgs s (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) rate Y (BitVec.ofNat 32 sfx) := fun hc h =>
    VG.Proof.MlKem.Arm.padArgs_of hrate (h.rg.ctx hc) hY h.r0 h.r1 h.r2 h.r3 h.lr
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.Rg s₀₁ a ∧ VG.Proof.MlKem.Arm.Rg s₀₂ b)
    (RelCT.mono (relct_wp (F₁ := VG.Proof.MlKem.Arm.Rg s₀₁) (F₂ := VG.Proof.MlKem.Arm.Rg s₀₂) (pad_ct fun a b hab =>
      ⟨by rw [hab.1.rg.sp, hab.2.rg.sp, hsp], _, _, _, _, _, hPA hc₁ hab.1, hPA hc₂ hab.2⟩) fun a b hab =>
      ⟨pad_ok (hPA hc₁ hab.1) fun s' k' _ => hab.1.rg.kept k', pad_ok (hPA hc₂ hab.2) fun s' k' _ => hab.2.rg.kept k'⟩)
      (fun _ _ h => h) fun _ _ h => h) ?_
  -- the squeeze
  have hq₁ := h₁.outs q (List.mem_singleton_self _)
  have hq₂ := h₂.outs q (List.mem_singleton_self _)
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.KA L idx rate q 0 s₀₁ a ∧ VG.Proof.MlKem.Arm.KA L idx rate q 0 s₀₂ b)
    (relct_wp (VG.Proof.MlKem.Arm.relct_noMem (VG.Proof.MlKem.Arm.kargs_noMem _ _ _)) fun a b hab =>
      ⟨VG.Proof.MlKem.Arm.ka_ok hre hc₁ hq₁ hab.1 rfl, VG.Proof.MlKem.Arm.ka_ok hre hc₂ hq₂ hab.2 rfl⟩) ?_
  have hS : ∀ {s₀ s : State}, VG.Proof.MlKem.Arm.Ctx L s₀ → VG.Proof.MlKem.Arm.PieceOk L idx s₀ true q → VG.Proof.MlKem.Arm.KA L idx rate q 0 s₀ s →
      SqueezeArgs s (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) (L.ptr (idx q.base) + BitVec.ofNat 32 q.off)
        rate 0 q.len := fun hc hq h =>
    VG.Proof.MlKem.Arm.squeezeArgs_of hrate (h.rg.ctx hc) h.rg hq (Nat.zero_le _) h.r0 h.r1 h.r2 h.r3 h.r12 h.lr
  refine RelCT.seq (R := fun _ _ => True) (squeeze_ct fun a b hab =>
    ⟨by rw [hab.1.rg.sp, hab.2.rg.sp, hsp], _, _, _, _, _, _, hS hc₁ hq₁ hab.1, hS hc₂ hq₂ hab.2⟩) VG.Proof.MlKem.Arm.relct_nil

end VG.Proof.MlKem.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.CallsCT`. -/
section

/-!
# ML-KEM on 32-bit ARM: calling the primitives in constant time

The taint analysis proves the primitives constant time from any state whose
argument registers are public (`addT`, …), so two runs that call one with the
same arguments leak the same trace (`RelCT.callT`), whatever else holds of
them. `vg_mlkem_sample_ntt` leaks its seed, so two runs that call it must also
have the same seed (`sample_ct`).
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Sample (taint_block relct_wp)

/-- A call of code that is constant time from any state with public `pub`. -/
theorem RelCT.callT {n : String} {c : Prog isa} {pub : State → State → Prop}
    (hct : ConstantTime isa (fun _ => True) pub c) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → pub s₁.callEntry s₂.callEntry) :
    RelCT isa P (.call n c) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | call h₁ b₁ r₁ =>
    cases e₂ with
    | call h₂ b₂ r₂ =>
      rw [call_callEntry, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      have ht := hct _ _ _ _ _ _ trivial trivial (hP _ _ hp) b₁ b₂
      exact ⟨by simp only [ht], trivial⟩

/-- Taint analysis of any code (not only a block). -/
theorem taint_prog {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hP : ∀ a b, P a b → ∀ r ∈ rs, a.gpr r = b.gpr r) {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs rs) (fun a b hab => Taint.agree_ofRegs (hP a b hab)) h

/-- `c` is constant time from any two states that agree on the registers `rs`,
by the taint analysis. -/
def RegsCT (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc : VG.Taint.Hint VG.Arm.taint.T, (VG.Arm.taint.check (Taint.ofRegs rs) c hc).isSome = true

theorem RegsCT.relct {rs : List Reg} {c : Prog isa} (h : VG.Proof.MlKem.Arm.RegsCT rs c) {P : State → State → Prop}
    (hP : ∀ a b, P a b → ∀ r ∈ rs, a.gpr r = b.gpr r) : RelCT isa P c fun _ _ => True :=
  h.elim fun _ h => VG.Proof.MlKem.Arm.taint_prog rs hP h

/-- A contract with no precondition, whose public data is the registers `rs`. -/
def kT (rs : List Reg) : Contract isa := VG.Proof.MlKem.Arm.mkK (fun _ => True) (fun _ _ => True) (VG.Proof.MlKem.Arm.regsEq rs)

theorem addT : ConstantTime isa (fun _ => True) (VG.Proof.MlKem.Arm.regsEq [.r0, .r1]) Impl.MlKem.Arm.add :=
  Add.ctRegs (k := VG.Proof.MlKem.Arm.kT [.r0, .r1]) [.r0, .r1] (fun _ _ h => h) (by taint_decide)

theorem subT : ConstantTime isa (fun _ => True) (VG.Proof.MlKem.Arm.regsEq [.r0, .r1]) Impl.MlKem.Arm.sub :=
  Add.ctRegs (k := VG.Proof.MlKem.Arm.kT [.r0, .r1]) [.r0, .r1] (fun _ _ h => h) (by taint_decide)

theorem mulT : ConstantTime isa (fun _ => True) (VG.Proof.MlKem.Arm.regsEq [.r0, .r1, .r2, .r3]) Impl.MlKem.Arm.multiplyNTTs :=
  Add.ctRegs (k := VG.Proof.MlKem.Arm.kT [.r0, .r1, .r2, .r3]) [.r0, .r1, .r2, .r3] (fun _ _ h => h) (by taint_decide)

theorem nttT : ConstantTime isa (fun _ => True) (VG.Proof.MlKem.Arm.regsEq [.r0, .r1]) Impl.MlKem.Arm.ntt :=
  Add.ctRegs (k := VG.Proof.MlKem.Arm.kT [.r0, .r1]) [.r0, .r1] (fun _ _ h => h) (by taint_decide)

theorem nttInvT : ConstantTime isa (fun _ => True) (VG.Proof.MlKem.Arm.regsEq [.r0, .r1]) Impl.MlKem.Arm.nttInv :=
  Add.ctRegs (k := VG.Proof.MlKem.Arm.kT [.r0, .r1]) [.r0, .r1] (fun _ _ h => h) (by taint_decide)

theorem cbd2T : ConstantTime isa (fun _ => True) (VG.Proof.MlKem.Arm.regsEq [.r0, .r1]) Impl.MlKem.Arm.cbd2 :=
  Add.ctRegs (k := VG.Proof.MlKem.Arm.kT [.r0, .r1]) [.r0, .r1] (fun _ _ h => h) (by taint_decide)

theorem encode12T : ConstantTime isa (fun _ => True) (VG.Proof.MlKem.Arm.regsEq [.r0, .r1]) Impl.MlKem.Arm.encode12 :=
  Add.ctRegs (k := VG.Proof.MlKem.Arm.kT [.r0, .r1]) [.r0, .r1] (fun _ _ h => h) (by taint_decide)

theorem decode12T : ConstantTime isa (fun _ => True) (VG.Proof.MlKem.Arm.regsEq [.r0, .r1]) Impl.MlKem.Arm.decode12 :=
  Add.ctRegs (k := VG.Proof.MlKem.Arm.kT [.r0, .r1]) [.r0, .r1] (fun _ _ h => h) (by taint_decide)

theorem compressT : ConstantTime isa (fun _ => True) (VG.Proof.MlKem.Arm.regsEq [.r0, .r1, .r2, .r3]) Impl.MlKem.Arm.compressEncode :=
  Add.ctRegs (k := VG.Proof.MlKem.Arm.kT [.r0, .r1, .r2, .r3]) [.r0, .r1, .r2, .r3] (fun _ _ h => h) (by taint_decide)

theorem decompressT :
    ConstantTime isa (fun _ => True) (VG.Proof.MlKem.Arm.regsEq [.r0, .r1, .r2, .r3]) Impl.MlKem.Arm.decodeDecompress :=
  Add.ctRegs (k := VG.Proof.MlKem.Arm.kT [.r0, .r1, .r2, .r3]) [.r0, .r1, .r2, .r3] (fun _ _ h => h) (by taint_decide)

/-- Two runs that call a primitive with the same registers `rs`. -/
theorem callEq {rs : List Reg} (hl : ∀ r ∈ rs, r ∉ linkRegs) {a b : State} (h : ∀ r ∈ rs, a.gpr r = b.gpr r) :
    VG.Proof.MlKem.Arm.regsEq rs a.callEntry b.callEntry := fun r hr => by
  rw [State.callEntry_gpr _ (hl r hr), State.callEntry_gpr _ (hl r hr), h r hr]

theorem regs2 {P : State → State → Prop} (hP : ∀ a b, P a b → a.gpr .r0 = b.gpr .r0 ∧ a.gpr .r1 = b.gpr .r1) :
    ∀ a b, P a b → VG.Proof.MlKem.Arm.regsEq [.r0, .r1] a.callEntry b.callEntry := fun a b h =>
  VG.Proof.MlKem.Arm.callEq (by decide) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hP a b h).1
    · exact (hP a b h).2

theorem regs4 {P : State → State → Prop}
    (hP : ∀ a b, P a b → a.gpr .r0 = b.gpr .r0 ∧ a.gpr .r1 = b.gpr .r1 ∧ a.gpr .r2 = b.gpr .r2 ∧
      a.gpr .r3 = b.gpr .r3) :
    ∀ a b, P a b → VG.Proof.MlKem.Arm.regsEq [.r0, .r1, .r2, .r3] a.callEntry b.callEntry := fun a b h =>
  VG.Proof.MlKem.Arm.callEq (by decide) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hP a b h).1
    · exact (hP a b h).2.1
    · exact (hP a b h).2.2.1
    · exact (hP a b h).2.2.2

/-! ## `vg_mlkem_sample_ntt` -/

theorem kSample_ct : ConstantTime isa kSample.pre kSample.pub Impl.MlKem.Arm.sampleNTT :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ ⟨hsp, hr, hb⟩ e₁ e₂ =>
    (Sample.all_ct ⟨h₁, h₂, hsp, hr .r0 (by simp), hr .r1 (by simp), hr .r2 (by simp), hb⟩
      s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1

theorem Ctx.sp_eq {L : VG.Proof.MlKem.Arm.Lay} {a b : State} (ha : VG.Proof.MlKem.Arm.Ctx L a) (hb : VG.Proof.MlKem.Arm.Ctx L b) : a.sp = b.sp := by
  have e := ha.sp.symm.trans hb.sp
  have := BitVec.sub_add_cancel a.sp (BitVec.ofNat 32 8)
  rw [e, BitVec.sub_add_cancel] at this
  exact this.symm

/-- What `vg_mlkem_sample_ntt` needs, as `sampleL` builds it. -/
theorem sample_view {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hc : VG.Proof.MlKem.Arm.Ctx L s) {i o j o' k o'' : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = L.ptr j + BitVec.ofNat 32 o')
    (g2 : s.gpr .r2 = L.ptr k + BitVec.ofNat 32 o'')
    (s_ij : VG.Proof.MlKem.Arm.sepB L.sizes (i, o, 34) (j, o', 1024) = true) (s_ik : VG.Proof.MlKem.Arm.sepB L.sizes (i, o, 34) (k, o'', 2048) = true)
    (s_jk : VG.Proof.MlKem.Arm.sepB L.sizes (j, o', 1024) (k, o'', 2048) = true) (s_i1 : VG.Proof.MlKem.Arm.sepB L.sizes (i, o, 34) (1, 0, 8) = true)
    (s_j1 : VG.Proof.MlKem.Arm.sepB L.sizes (j, o', 1024) (1, 0, 8) = true) (s_k1 : VG.Proof.MlKem.Arm.sepB L.sizes (k, o'', 2048) (1, 0, 8) = true)
    (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr) (wk : L.buf k ∈ s.wr) :
    Sample.Pre (VG.Proof.MlKem.Arm.view s [⟨L.A i o, 34⟩] [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩]) ∧
      Covers ([⟨L.A i o, 34⟩] ++ [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩]) (s.rd ++ s.wr) ∧
      Covers [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩] s.wr ∧
      Sample.B (VG.Proof.MlKem.Arm.view s [⟨L.A i o, 34⟩] [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩]) = bytesAt s.mem (L.A i o) 34 := by
  have hL := hc.ok
  obtain ⟨ea, fa⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds s_ij) (by decide)
  obtain ⟨eb, fb⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds s_jk) (by decide)
  obtain ⟨ec, fc⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds (VG.Proof.MlKem.Arm.sepB_symm s_ik)) (by decide)
  let V := VG.Proof.MlKem.Arm.view s [⟨L.A i o, 34⟩] [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩]
  have eS : Sample.SEED V = L.A i o := by simp only [V, Sample.SEED, Sample.pseed, VG.Proof.MlKem.Arm.view_r0, g0, ea]
  have eA : Sample.A V = L.A j o' := by simp only [V, Sample.A, Sample.pa, VG.Proof.MlKem.Arm.view_r1, g1, eb]
  have eC : Sample.S V = L.A k o'' := by simp only [V, Sample.S, Sample.pscr, VG.Proof.MlKem.Arm.view_r2, g2, ec]
  have eb8 : below V 8 = L.R 1 0 8 := hc.bel
  have cw : Covers [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩] s.wr :=
    VG.Proof.MlKem.Arm.covers_cons' (Lay.covers wj (VG.Proof.MlKem.Arm.sepB_bounds s_jk).2) (VG.Proof.MlKem.Arm.covers_cons' (Lay.covers wk (VG.Proof.MlKem.Arm.sepB_bounds (VG.Proof.MlKem.Arm.sepB_symm s_ik)).2)
      VG.Proof.MlKem.Arm.covers_nil')
  refine ⟨⟨hc.sp8, by simp only [V, eS, State.withRegions_rd], by simp only [V, eA, eC, State.withRegions_wr],
      by rw [eS, eA]; exact Lay.disj hL s_ij, by rw [eS, eC]; exact Lay.disj hL s_ik,
      by rw [eA, eC]; exact Lay.disj hL s_jk, by rw [eb8, eS]; exact Lay.disj hL (VG.Proof.MlKem.Arm.sepB_symm s_i1),
      by rw [eb8, eA]; exact Lay.disj hL (VG.Proof.MlKem.Arm.sepB_symm s_j1), by rw [eb8, eC]; exact Lay.disj hL (VG.Proof.MlKem.Arm.sepB_symm s_k1),
      by simp only [Sample.pseed, VG.Proof.MlKem.Arm.view_r0, g0]; exact fa, by simp only [Sample.pa, VG.Proof.MlKem.Arm.view_r1, g1]; exact fb,
      by simp only [Sample.pscr, VG.Proof.MlKem.Arm.view_r2, g2]; exact fc⟩,
    VG.Proof.MlKem.Arm.covers_append (Lay.covers wi (VG.Proof.MlKem.Arm.sepB_bounds s_ij).2) (VG.Proof.MlKem.Arm.covers_wr cw), cw, ?_⟩
  show bytesAt s.mem (Sample.SEED V) 34 = _
  rw [eS]

/-- Two runs that call `vg_mlkem_sample_ntt` on the same pointers and seed. -/
theorem sample_ct {L : VG.Proof.MlKem.Arm.Lay} {i o j o' k o'' : Nat} {P : State → State → Prop}
    (hP : ∀ a b, P a b → VG.Proof.MlKem.Arm.Ctx L a ∧ VG.Proof.MlKem.Arm.Ctx L b ∧
      a.gpr .r0 = L.ptr i + BitVec.ofNat 32 o ∧ a.gpr .r1 = L.ptr j + BitVec.ofNat 32 o' ∧
      a.gpr .r2 = L.ptr k + BitVec.ofNat 32 o'' ∧
      b.gpr .r0 = L.ptr i + BitVec.ofNat 32 o ∧ b.gpr .r1 = L.ptr j + BitVec.ofNat 32 o' ∧
      b.gpr .r2 = L.ptr k + BitVec.ofNat 32 o'' ∧
      bytesAt a.mem (L.A i o) 34 = bytesAt b.mem (L.A i o) 34 ∧
      L.buf i ∈ a.rd ++ a.wr ∧ L.buf j ∈ a.wr ∧ L.buf k ∈ a.wr ∧
      L.buf i ∈ b.rd ++ b.wr ∧ L.buf j ∈ b.wr ∧ L.buf k ∈ b.wr)
    (s_ij : VG.Proof.MlKem.Arm.sepB L.sizes (i, o, 34) (j, o', 1024) = true) (s_ik : VG.Proof.MlKem.Arm.sepB L.sizes (i, o, 34) (k, o'', 2048) = true)
    (s_jk : VG.Proof.MlKem.Arm.sepB L.sizes (j, o', 1024) (k, o'', 2048) = true) (s_i1 : VG.Proof.MlKem.Arm.sepB L.sizes (i, o, 34) (1, 0, 8) = true)
    (s_j1 : VG.Proof.MlKem.Arm.sepB L.sizes (j, o', 1024) (1, 0, 8) = true) (s_k1 : VG.Proof.MlKem.Arm.sepB L.sizes (k, o'', 2048) (1, 0, 8) = true) :
    RelCT isa P callSample fun _ _ => True :=
  RelCT.call VG.Proof.MlKem.Arm.kSample_ok VG.Proof.MlKem.Arm.kSample_ct [⟨L.A i o, 34⟩] [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩] fun a b hab => by
    obtain ⟨ca, cb, a0, a1, a2, b0, b1, b2, eb, wia, wja, wka, wib, wjb, wkb⟩ := hP a b hab
    obtain ⟨pa, c1a, c2a, ba⟩ := VG.Proof.MlKem.Arm.sample_view ca a0 a1 a2 s_ij s_ik s_jk s_i1 s_j1 s_k1 wia wja wka
    obtain ⟨pb, c1b, c2b, bb⟩ := VG.Proof.MlKem.Arm.sample_view cb b0 b1 b2 s_ij s_ik s_jk s_i1 s_j1 s_k1 wib wjb wkb
    refine ⟨pa, pb, ⟨by show a.sp = b.sp; exact Ctx.sp_eq ca cb, fun r hr => ?_, by rw [ba, bb, eb]⟩, c1a, c2a,
      c1b, c2b⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [VG.Proof.MlKem.Arm.view_r0, VG.Proof.MlKem.Arm.view_r0, a0, b0]
    · rw [VG.Proof.MlKem.Arm.view_r1, VG.Proof.MlKem.Arm.view_r1, a1, b1]
    · rw [VG.Proof.MlKem.Arm.view_r2, VG.Proof.MlKem.Arm.view_r2, a2, b2]

/-! ## Loops counted by a register -/

/-- A loop whose body runs `N` times, related in two runs by invariants at
the same iteration. -/
theorem relct_loop_ne {body : Prog isa} {I₁ I₂ : Nat → State → Prop} {N : Nat} (hN : 0 < N)
    (hstep : ∀ i < N, RelCT isa (fun a b => I₁ i a ∧ I₂ i b) body fun a b =>
      (I₁ (i + 1) a ∧ a.z = decide (i + 1 = N)) ∧ (I₂ (i + 1) b ∧ b.z = decide (i + 1 = N))) :
    RelCT isa (fun a b => I₁ 0 a ∧ I₂ 0 b) (.loop body .ne) fun a b => I₁ N a ∧ I₂ N b := by
  refine RelCT.mono (RelCT.loop (M := isa) (body := body) (c := .ne) (Q := fun a b => I₁ N a ∧ I₂ N b)
    (fun n a b => ∃ t, t < N ∧ n = N - t ∧ I₁ t a ∧ I₂ t b) (fun n => ?_) N) ?_ (fun _ _ h => h)
  · refine RelCT.mono (P := fun a b => ∃ t, t < N ∧ n = N - t ∧ I₁ t a ∧ I₂ t b)
      (RelCT.exists_ fun t => ?_) (fun _ _ hab => hab) (fun _ _ h => h)
    by_cases ht : t < N
    · by_cases hn : n = N - t
      · refine RelCT.mono (P := fun a b => I₁ t a ∧ I₂ t b) (hstep t ht) (fun _ _ hab => hab.2.2)
          fun a b ⟨⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ => ⟨?_, fun e => ?_, fun e => ?_⟩
        · show some (!a.z) = some (!b.z); rw [z₁, z₂]
        · have : t + 1 = N := by
            have e' : (!a.z) = false := Option.some.inj e
            rw [z₁] at e'; simpa using e'
          rw [this] at i₁ i₂; exact ⟨i₁, i₂⟩
        · have : t + 1 ≠ N := by
            have e' : (!a.z) = true := Option.some.inj e
            rw [z₁] at e'; simpa using e'
          exact ⟨N - (t + 1), by omega, t + 1, by omega, rfl, i₁, i₂⟩
      · exact RelCT.of_false fun _ _ hab => hn hab.2.1
    · exact RelCT.of_false fun _ _ hab => ht hab.1
  · exact fun a b hab => ⟨0, hN, rfl, hab⟩

/-! ## What each parameter set checks by evaluation -/

/-- What each parameter set proves of its code by evaluation: the contracts of
its primitives that compress to `d_u` and `d_v` bits (and decompress from
them), as calls on regions of a layout (as `compressL` and `decompressL`), and
their constant time; and the taint analyses of the code whose immediates
depend on the parameters (`taint_decide` evaluates closed code only). -/
structure _root_.VG.Impl.MlKem.Arm.KemLay.CallsOk (K : KemLay) : Prop where
  cu : ∀ {L : VG.Proof.MlKem.Arm.Lay} {s : State}, L.Ok → ∀ {i o j o' d : Nat}, s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o →
    s.gpr .r1 = BitVec.ofNat 32 d → s.gpr .r2 = L.ptr j + BitVec.ofNat 32 o' → s.gpr .r3 = BitVec.ofNat 32 (32 * d) →
    d = K.du ∨ d = K.dv → VG.Proof.MlKem.Arm.sepB L.sizes (i, o, 1024) (j, o', 32 * d) = true → L.buf i ∈ s.rd ++ s.wr →
    L.buf j ∈ s.wr → ∀ {f : VG.Spec.MlKem.Poly}, PolyIs s.mem (L.A i o) f → ∀ {Q : State → Prop},
    (∀ s', Kept (L.RL [(j, o', 32 * d)]) s s' → bytesAt s'.mem (L.A j o') (32 * d) = compressEncode d f → Q s') →
    WP isa K.callCU s Q
  du : ∀ {L : VG.Proof.MlKem.Arm.Lay} {s : State}, L.Ok → ∀ {i o j o' d : Nat}, s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o →
    s.gpr .r1 = BitVec.ofNat 32 (32 * d) → s.gpr .r2 = BitVec.ofNat 32 d → s.gpr .r3 = L.ptr j + BitVec.ofNat 32 o' →
    d = K.du ∨ d = K.dv → VG.Proof.MlKem.Arm.sepB L.sizes (i, o, 32 * d) (j, o', 1024) = true → L.buf i ∈ s.rd ++ s.wr →
    L.buf j ∈ s.wr → ∀ {Q : State → Prop},
    (∀ s', Kept (L.RL [(j, o', 1024)]) s s' →
      PolyIs s'.mem (L.A j o') (decodeDecompress d (bytesAt s.mem (L.A i o) (32 * d))) → Q s') →
    WP isa K.callDU s Q
  cuT : ConstantTime isa (fun _ => True) (VG.Proof.MlKem.Arm.regsEq [.r0, .r1, .r2, .r3]) K.compress
  duT : ConstantTime isa (fun _ => True) (VG.Proof.MlKem.Arm.regsEq [.r0, .r1, .r2, .r3]) K.decompress
  seedT : ∀ t, VG.Proof.MlKem.Arm.RegsCT [.r7] (.block (seedBytes t ++ [ptrTo .r0 .r7 oSeed, ptrTo .r1 .r7 K.oAhat, ptrTo .r2 .r7 K.oSample]))
  zeroT : VG.Proof.MlKem.Arm.RegsCT [.r7] (zeroPoly K.oAcc)
  kgSetupT : VG.Proof.MlKem.Arm.RegsCT [.r0, .r1, .r2, .r3] (.block K.kgSetup)
  rhoT : VG.Proof.MlKem.Arm.RegsCT [.r5, .r7] (copy .r7 oSeed .r5 (384 * K.k) 32)
  ekT : VG.Proof.MlKem.Arm.RegsCT [.r5, .r6] (copy .r5 0 .r6 (384 * K.k) K.ekLen)
  zT : VG.Proof.MlKem.Arm.RegsCT [.r4, .r6] (copy .r4 32 .r6 (768 * K.k + 64) 32)
  encSeedT : VG.Proof.MlKem.Arm.RegsCT [.r4, .r7] (copy .r4 (384 * K.k) .r7 oSeed 32)
  ctT : VG.Proof.MlKem.Arm.RegsCT [.r6, .r7] (copy .r6 0 .r7 oCin K.ctLen)
  cmpT : VG.Proof.MlKem.Arm.RegsCT [.r6, .r7] K.compare

theorem kl768_calls : kl768.CallsOk :=
  ⟨fun hL _ _ _ _ _ g0 g1 g2 g3 hd => VG.Proof.MlKem.Arm.compressL hL g0 g1 g2 g3 (by rcases hd with rfl | rfl <;> decide),
    fun hL _ _ _ _ _ g0 g1 g2 g3 hd => VG.Proof.MlKem.Arm.decompressL hL g0 g1 g2 g3 (by rcases hd with rfl | rfl <;> decide),
    VG.Proof.MlKem.Arm.compressT, VG.Proof.MlKem.Arm.decompressT, fun t => by cases t <;> exact ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

end VG.Proof.MlKem.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.CmpSel`. -/
section

/-!
# ML-KEM on 32-bit ARM: comparing `c` with `c'`, and selecting the key

`compare` ORs the XORs of the bytes of two buffers into `r12` (`compare_ok`: 0
exactly when they are equal); `selSetup` turns it into a mask, all ones
exactly when it is 0 (`selSetup_ok`); and the loop of `selBody` writes, byte
by byte, the first source under the mask and the second one otherwise
(`select_ok`).
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Add (ptr_succ)

/-! ## `compare` -/

section
variable {s : State} {x y c a : BitVec 32}

theorem cmpBody_ok (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y) (h9 : s.gpr .r9 = c) (h12 : s.gpr .r12 = a)
    (ir0 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 1)
    (ir1 : InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 1) :
    WP isa (.block cmpBody) s fun s' =>
      s'.gpr .r0 = x + 1 ∧ s'.gpr .r1 = y + 1 ∧ s'.gpr .r9 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.gpr .r12 = a ||| ((s.mem (State.addr (x + BitVec.ofNat 32 0))).setWidth 32 ^^^
        (s.mem (State.addr (y + BitVec.ofNat 32 0))).setWidth 32) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      ∀ r ∈ preserved, r ≠ .r9 → s'.gpr r = s.gpr r := by
  run_block [cmpBody, h0, h1, h9, h12, ir0, ir1, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

end

/-- After comparing `k` bytes of `S` and `D`. -/
structure CmpInv (S D : BitVec 32) (len : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = S + BitVec.ofNat 32 (1 * k)
  r1 : s.gpr .r1 = D + BitVec.ofNat 32 (1 * k)
  r9 : s.gpr .r9 = BitVec.ofNat 32 (1 * (len - k))
  cs : ∀ r ∈ preserved, r ≠ .r9 → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lt : (s.gpr .r12).toNat < 256
  eq : s.gpr .r12 = 0 ↔ ∀ t < k, s₀.mem (State.addr S + BitVec.ofNat 64 t) = s₀.mem (State.addr D + BitVec.ofNat 64 t)

theorem setWidth32_inj {a b : Byte} (h : a.setWidth 32 = b.setWidth 32) : a = b := by
  have := congrArg (BitVec.setWidth 8) h
  rwa [VG.Proof.MlKem.Arm.setWidth_byte, VG.Proof.MlKem.Arm.setWidth_byte] at this

theorem cmp_step {S D : BitVec 32} {len : Nat} {s₀ : State} (fS : S.toNat + len ≤ 2 ^ 32)
    (fD : D.toNat + len ≤ 2 ^ 32) (hlen : len < 2 ^ 32)
    (cr : Covers [⟨State.addr S, len⟩, ⟨State.addr D, len⟩] (s₀.rd ++ s₀.wr))
    {k : Nat} (hk : k < len) {s : State} (h : VG.Proof.MlKem.Arm.CmpInv S D len s₀ k s) :
    WP isa (.block cmpBody) s fun s' => VG.Proof.MlKem.Arm.CmpInv S D len s₀ (k + 1) s' ∧ s'.z = decide (k + 1 = len) := by
  have eS : State.addr (S + BitVec.ofNat 32 (1 * k) + BitVec.ofNat 32 0) = State.addr S + BitVec.ofNat 64 k := by
    rw [addr_ptr _ _ _ (by omega)]; simp
  have eD : State.addr (D + BitVec.ofNat 32 (1 * k) + BitVec.ofNat 32 0) = State.addr D + BitVec.ofNat 64 k := by
    rw [addr_ptr _ _ _ (by omega)]; simp
  have cS : (⟨State.addr S, len⟩ : Region).Contains (State.addr S + BitVec.ofNat 64 k) 1 :=
    contains_off (by omega) (by omega)
  have cD : (⟨State.addr D, len⟩ : Region).Contains (State.addr D + BitVec.ofNat 64 k) 1 :=
    contains_off (by omega) (by omega)
  refine WP.mono (VG.Proof.MlKem.Arm.cmpBody_ok h.r0 h.r1 h.r9 rfl
    (by rw [eS, h.rd, h.wr]; exact cr _ _ ⟨_, List.mem_cons_self .., cS⟩)
    (by rw [eD, h.rd, h.wr]; exact cr _ _ ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), cD⟩))
    fun s' ⟨r0, r1, r9, z, r12, m, rd, wr, sp, cs⟩ => ⟨⟨?_, ?_, ?_, fun r hr h9 => (cs r hr h9).trans (h.cs r hr h9),
      m.trans h.mem, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, ?_, ?_⟩, ?_⟩
  · rw [r0]; exact ptr_succ _ 1 k
  · rw [r1]; exact ptr_succ _ 1 k
  · rw [r9]; exact count_sub (k := 1) hk
  · rw [r12, BitVec.toNat_or, BitVec.toNat_xor]
    have ha := h.lt
    have hx := (s.mem (State.addr (S + BitVec.ofNat 32 (1 * k) + BitVec.ofNat 32 0))).isLt
    have hy := (s.mem (State.addr (D + BitVec.ofNat 32 (1 * k) + BitVec.ofNat 32 0))).isLt
    rw [setWidth32_toNat, setWidth32_toNat]
    exact Nat.or_lt_two_pow (n := 8) ha (Nat.xor_lt_two_pow (n := 8) hx hy)
  · rw [r12, eS, eD, h.mem]
    constructor
    · intro h₀ t ht
      obtain ⟨h₁, h₂⟩ := BitVec.or_eq_zero_iff.mp h₀
      by_cases e : t = k
      · subst e; exact VG.Proof.MlKem.Arm.setWidth32_inj (BitVec.xor_eq_zero_iff.mp h₂)
      · exact h.eq.mp h₁ t (by omega)
    · intro h₁
      exact BitVec.or_eq_zero_iff.mpr ⟨h.eq.mpr fun t ht => h₁ t (by omega),
        BitVec.xor_eq_zero_iff.mpr (congrArg _ (h₁ k (by omega)))⟩
  · rw [z]; exact count_z (k := 1) hk (by decide) (by omega)

theorem cmpArgs_ok {K : KemLay} (hK : K.WF) {s : State} {P C : BitVec 32} (h7 : s.gpr .r7 = P)
    (h6 : s.gpr .r6 = C) :
    WP isa (.block [.mov .r0 (.reg .r6), ptrTo .r1 .r7 K.oCt, .mov .r12 (.imm 0),
      .mov .r9 (.imm (BitVec.ofNat 32 K.ctLen))]) s
      fun s' => s'.gpr .r0 = C ∧ s'.gpr .r1 = P + BitVec.ofNat 32 K.oCt ∧ s'.gpr .r12 = 0 ∧
        s'.gpr .r9 = BitVec.ofNat 32 K.ctLen ∧ (∀ r ∈ preserved, r ≠ .r9 → s'.gpr r = s.gpr r) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have e1 : encodable (BitVec.ofNat 32 K.oCt) = true := hK.enc (by omega)
  have e2 : encodable (0 : BitVec 32) = true := by decide
  have e3 := hK.encCt
  run_block [ptrTo, e1, e2, e3, h7, h6, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

/-- `compare`: `r12` is 0 exactly when the `K.ctLen` bytes at `C` (in `r6`)
and at `P + K.oCt` (`r7 = P`) are equal. -/
theorem compare_ok {K : KemLay} (hK : K.WF) {s : State} {P C : BitVec 32} (h7 : s.gpr .r7 = P)
    (h6 : s.gpr .r6 = C) (fC : C.toNat + K.ctLen ≤ 2 ^ 32) (fD : (P + BitVec.ofNat 32 K.oCt).toNat + K.ctLen ≤ 2 ^ 32)
    (cr : Covers [⟨State.addr C, K.ctLen⟩, ⟨State.addr (P + BitVec.ofNat 32 K.oCt), K.ctLen⟩] (s.rd ++ s.wr)) :
    WP isa K.compare s fun s' => (∀ r ∈ preserved, r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (s'.gpr .r12).toNat < 256 ∧
      (s'.gpr .r12 = 0 ↔
        bytesAt s.mem (State.addr C) K.ctLen = bytesAt s.mem (State.addr (P + BitVec.ofNat 32 K.oCt)) K.ctLen) := by
  have c1 := hK.ct_pos
  have c2 : K.ctLen < 2 ^ 32 := by have := hK.cin; simp only [oCin] at this; omega
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.cmpArgs_ok hK h7 h6) fun s₁ ⟨g0, g1, g12, g9, cs, m, rd, wr, sp⟩ => ?_)
  refine wp_loop_ne (VG.Proof.MlKem.Arm.CmpInv C (P + BitVec.ofNat 32 K.oCt) K.ctLen s₁) (N := K.ctLen) c1
    (fun k hk s h => VG.Proof.MlKem.Arm.cmp_step fC fD c2 (by rw [rd, wr]; exact cr) hk h)
    (fun s' h => ⟨fun r hr h9 => (h.cs r hr h9).trans (cs r hr h9), h.mem.trans m, h.rd.trans rd, h.wr.trans wr,
      h.sp.trans sp, h.lt, ?_⟩)
    ⟨by rw [g0]; simp, by rw [g1]; simp, by rw [g9, Nat.sub_zero, Nat.one_mul], fun _ _ _ => rfl, rfl, rfl, rfl, rfl,
      by rw [g12]; decide, by rw [g12]; exact ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ => rfl⟩⟩
  rw [h.eq, ← m]
  constructor
  · intro he
    exact bytesAt_eq (bytesAt_length _ _ _) fun t ht => by rw [he t ht, bytesAt_getElem]
  · intro he t ht
    have := congrArg (fun L : List Byte => L[t]!) he
    simp only [bytesAt_getElem! _ _ ht] at this
    exact this

/-! ## The mask -/

theorem mask_eq : ∀ n < 256, (0 : BitVec 32) - (BitVec.ofNat 32 n - 1) >>> 31 =
    if n = 0 then BitVec.allOnes 32 else 0 := by
  decide +kernel

theorem mask_of {v : BitVec 32} (h : v.toNat < 256) :
    (0 : BitVec 32) - (v - 1) >>> 31 = if v = 0 then BitVec.allOnes 32 else 0 := by
  have := VG.Proof.MlKem.Arm.mask_eq v.toNat h
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  rw [this]
  by_cases e : v = 0
  · subst e; rfl
  · have e' : ¬ v.toNat = 0 := fun h' => e (BitVec.eq_of_toNat_eq (by rw [h']; rfl))
    simp only [e, e', ↓reduceIte]

theorem selSetup_ok {s : State} {P K : BitVec 32} (h7 : s.gpr .r7 = P) (hlt : (s.gpr .r12).toNat < 256)
    (hk : s.mem.readW (State.addr (P + BitVec.ofNat 32 oExtra)) 32 = K)
    (ik : InRegions (s.rd ++ s.wr) (State.addr (P + BitVec.ofNat 32 oExtra)) 4) :
    WP isa (.block selSetup) s fun s' =>
      s'.gpr .r12 = (if s.gpr .r12 = 0 then BitVec.allOnes 32 else 0) ∧ s'.gpr .r0 = P + BitVec.ofNat 32 oG ∧
      s'.gpr .r1 = P + BitVec.ofNat 32 oKbar ∧ s'.gpr .r2 = K ∧ s'.gpr .r9 = BitVec.ofNat 32 32 ∧
      (∀ r ∈ preserved, r ≠ .r9 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have e1 : encodable (1 : BitVec 32) = true := by decide
  have e0 : encodable (0 : BitVec 32) = true := by decide
  have e2 : encodable (BitVec.ofNat 32 oG) = true := by decide
  have e3 : encodable (BitVec.ofNat 32 oKbar) = true := by decide
  have e4 : encodable (32 : BitVec 32) = true := by decide
  have o1 : oExtra < 4096 := by decide
  run_block [selSetup, ptrTo, e1, e0, e2, e3, e4, o1, h7, ik, hk, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]
  exact VG.Proof.MlKem.Arm.mask_of hlt

/-! ## `select` -/

section
variable {s : State} {x y z c m : BitVec 32}

theorem selBody_ok (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y) (h2 : s.gpr .r2 = z) (h9 : s.gpr .r9 = c)
    (h12 : s.gpr .r12 = m)
    (ir0 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 1)
    (ir1 : InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 1)
    (iw : InRegions s.wr (State.addr (z + BitVec.ofNat 32 0)) 1) :
    WP isa (.block selBody) s fun s' =>
      s'.gpr .r0 = x + 1 ∧ s'.gpr .r1 = y + 1 ∧ s'.gpr .r2 = z + 1 ∧ s'.gpr .r9 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.gpr .r12 = m ∧
      s'.mem = s.mem.writeW (State.addr (z + BitVec.ofNat 32 0))
        (((((s.mem (State.addr (x + BitVec.ofNat 32 0))).setWidth 32 ^^^
            (s.mem (State.addr (y + BitVec.ofNat 32 0))).setWidth 32) &&& m) ^^^
          (s.mem (State.addr (y + BitVec.ofNat 32 0))).setWidth 32).setWidth 8) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      ∀ r ∈ preserved, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r := by
  run_block [selBody, h0, h1, h2, h9, h12, ir0, ir1, iw, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

end

theorem sel_byte (a b : Byte) (e : Bool) :
    ((((a.setWidth 32 ^^^ b.setWidth 32) &&& (if e then BitVec.allOnes 32 else 0)) ^^^ b.setWidth 32).setWidth 8) =
      if e then a else b := by
  cases e
  · simp
  · simp only [ite_true, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, VG.Proof.MlKem.Arm.setWidth_byte]

/-- After selecting `k` bytes of `X` or `Y` into `Z`. -/
structure SelInv (X Y Z : BitVec 32) (e : Bool) (s₀ : State) (k : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = X + BitVec.ofNat 32 (1 * k)
  r1 : s.gpr .r1 = Y + BitVec.ofNat 32 (1 * k)
  r2 : s.gpr .r2 = Z + BitVec.ofNat 32 (1 * k)
  r9 : s.gpr .r9 = BitVec.ofNat 32 (1 * (32 - k))
  r12 : s.gpr .r12 = if e then BitVec.allOnes 32 else 0
  cs : ∀ r ∈ preserved, r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨State.addr Z, 32⟩] s₀.mem s.mem
  bytes : ∀ t < k, s.mem (State.addr Z + BitVec.ofNat 64 t) =
    if e then s₀.mem (State.addr X + BitVec.ofNat 64 t) else s₀.mem (State.addr Y + BitVec.ofNat 64 t)

theorem sel_step {X Y Z : BitVec 32} {e : Bool} {s₀ : State} (fX : X.toNat + 32 ≤ 2 ^ 32)
    (fY : Y.toNat + 32 ≤ 2 ^ 32) (fZ : Z.toNat + 32 ≤ 2 ^ 32)
    (dX : (⟨State.addr X, 32⟩ : Region).Disjoint ⟨State.addr Z, 32⟩)
    (dY : (⟨State.addr Y, 32⟩ : Region).Disjoint ⟨State.addr Z, 32⟩)
    (cr : Covers [⟨State.addr X, 32⟩, ⟨State.addr Y, 32⟩] (s₀.rd ++ s₀.wr)) (cw : Covers [⟨State.addr Z, 32⟩] s₀.wr)
    {k : Nat} (hk : k < 32) {s : State} (h : VG.Proof.MlKem.Arm.SelInv X Y Z e s₀ k s) :
    WP isa (.block selBody) s fun s' => VG.Proof.MlKem.Arm.SelInv X Y Z e s₀ (k + 1) s' ∧ s'.z = decide (k + 1 = 32) := by
  have eX : State.addr (X + BitVec.ofNat 32 (1 * k) + BitVec.ofNat 32 0) = State.addr X + BitVec.ofNat 64 k := by
    rw [addr_ptr _ _ _ (by omega)]; simp
  have eY : State.addr (Y + BitVec.ofNat 32 (1 * k) + BitVec.ofNat 32 0) = State.addr Y + BitVec.ofNat 64 k := by
    rw [addr_ptr _ _ _ (by omega)]; simp
  have eZ : State.addr (Z + BitVec.ofNat 32 (1 * k) + BitVec.ofNat 32 0) = State.addr Z + BitVec.ofNat 64 k := by
    rw [addr_ptr _ _ _ (by omega)]; simp
  have cX : (⟨State.addr X, 32⟩ : Region).Contains (State.addr X + BitVec.ofNat 64 k) 1 :=
    contains_off (by omega) (by omega)
  have cY : (⟨State.addr Y, 32⟩ : Region).Contains (State.addr Y + BitVec.ofNat 64 k) 1 :=
    contains_off (by omega) (by omega)
  have cZ : (⟨State.addr Z, 32⟩ : Region).Contains (State.addr Z + BitVec.ofNat 64 k) 1 :=
    contains_off (by omega) (by omega)
  refine WP.mono (VG.Proof.MlKem.Arm.selBody_ok h.r0 h.r1 h.r2 h.r9 h.r12
    (by rw [eX, h.rd, h.wr]; exact cr _ _ ⟨_, List.mem_cons_self .., cX⟩)
    (by rw [eY, h.rd, h.wr]; exact cr _ _ ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), cY⟩)
    (by rw [eZ, h.wr]; exact cw _ _ ⟨_, List.mem_singleton_self _, cZ⟩))
    fun s' ⟨r0, r1, r2, r9, z, r12, m, rd, wr, sp, cs⟩ => ⟨⟨?_, ?_, ?_, ?_, r12,
      fun r hr h9 h10 => (cs r hr h9 h10).trans (h.cs r hr h9 h10), rd.trans h.rd, wr.trans h.wr, sp.trans h.sp,
      ?_, fun t ht => ?_⟩, ?_⟩
  · rw [r0]; exact ptr_succ _ 1 k
  · rw [r1]; exact ptr_succ _ 1 k
  · rw [r2]; exact ptr_succ _ 1 k
  · rw [r9]; exact count_sub (k := 1) hk
  · rw [m, eZ]; exact h.frame.writeW (List.mem_singleton_self _) _ cZ
  · have hX : s.mem (State.addr X + BitVec.ofNat 64 k) = s₀.mem (State.addr X + BitVec.ofNat 64 k) :=
      h.frame _ fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact dX _ cX
    have hY : s.mem (State.addr Y + BitVec.ofNat 64 k) = s₀.mem (State.addr Y + BitVec.ofNat 64 k) :=
      h.frame _ fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact dY _ cY
    rw [m, eZ, eX, eY, byte_writeW8 _ _ (by omega) (by omega), VG.Proof.MlKem.Arm.sel_byte, hX, hY]
    by_cases et : t = k
    · subst et; rw [ite_eq_left rfl]
    · rw [ite_eq_right et]; exact h.bytes t (by omega)
  · rw [z]; exact count_z (k := 1) hk (by decide) (by omega)

/-- The loop of `selBody`: the 32 bytes at `X` if `e`, and at `Y` otherwise, into `Z`. -/
theorem select_ok {X Y Z : BitVec 32} {e : Bool} {s₀ : State} (fX : X.toNat + 32 ≤ 2 ^ 32)
    (fY : Y.toNat + 32 ≤ 2 ^ 32) (fZ : Z.toNat + 32 ≤ 2 ^ 32)
    (dX : (⟨State.addr X, 32⟩ : Region).Disjoint ⟨State.addr Z, 32⟩)
    (dY : (⟨State.addr Y, 32⟩ : Region).Disjoint ⟨State.addr Z, 32⟩)
    (cr : Covers [⟨State.addr X, 32⟩, ⟨State.addr Y, 32⟩] (s₀.rd ++ s₀.wr)) (cw : Covers [⟨State.addr Z, 32⟩] s₀.wr)
    (h0 : s₀.gpr .r0 = X) (h1 : s₀.gpr .r1 = Y) (h2 : s₀.gpr .r2 = Z) (h9 : s₀.gpr .r9 = BitVec.ofNat 32 32)
    (h12 : s₀.gpr .r12 = if e then BitVec.allOnes 32 else 0) :
    WP isa (.loop (.block selBody) .ne) s₀ fun s =>
      (∀ r ∈ preserved, r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧
      Frame [⟨State.addr Z, 32⟩] s₀.mem s.mem ∧
      bytesAt s.mem (State.addr Z) 32 = if e then bytesAt s₀.mem (State.addr X) 32 else bytesAt s₀.mem (State.addr Y) 32 :=
  wp_loop_ne (VG.Proof.MlKem.Arm.SelInv X Y Z e s₀) (N := 32) (by decide) (fun k hk s h => VG.Proof.MlKem.Arm.sel_step fX fY fZ dX dY cr cw hk h)
    (fun s h => ⟨h.cs, h.rd, h.wr, h.sp, h.frame, by
      cases e
      · show bytesAt s.mem (State.addr Z) 32 = bytesAt s₀.mem (State.addr Y) 32
        exact bytesAt_eq (bytesAt_length _ _ _) fun t ht => by rw [h.bytes t ht, bytesAt_getElem]; rfl
      · show bytesAt s.mem (State.addr Z) 32 = bytesAt s₀.mem (State.addr X) 32
        exact bytesAt_eq (bytesAt_length _ _ _) fun t ht => by rw [h.bytes t ht, bytesAt_getElem]; rfl⟩)
    ⟨by rw [h0]; simp, by rw [h1]; simp, by rw [h2]; simp, by rw [h9], h12, fun _ _ _ _ => rfl, rfl, rfl, rfl,
      Frame.refl _ _, fun t ht => absurd ht (Nat.not_lt_zero t)⟩

end VG.Proof.MlKem.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.Encrypt`. -/
section

/-!
# ML-KEM on 32-bit ARM: K-PKE.Encrypt, correctness

`K.encrypt` runs within encapsulation and decapsulation, on buffers the callers
choose (`EB`): the encapsulation key (in `r4`), the message (in `r5`) and the
ciphertext (in `r8`), each at an offset of one of the callers' buffers; `r` is
at 920 in `scratch`. It writes the ciphertext, and changes nothing but the
regions of `encW` (`encrypt_ok`). Its phases: `ρ` copied to the seed of
`SampleNTT`, `t̂` decoded (`decT_loop`), the `PRF`s into `ŷ`, `e₁` and `e₂`,
`μ`, the rows of `u` compressed into the ciphertext (`encRow_step`), and `v`.
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## Regions inside regions -/

theorem sepB_mono {sz : List Nat} {a a' b b' : Nat × Nat × Nat} (h : VG.Proof.MlKem.Arm.sepB sz a b = true) (ha : VG.Proof.MlKem.Arm.inB a' a = true)
    (hb : VG.Proof.MlKem.Arm.inB b' b = true) : VG.Proof.MlKem.Arm.sepB sz a' b' = true := by
  obtain ⟨i, o, l⟩ := a
  obtain ⟨i', o', l'⟩ := a'
  obtain ⟨j, p, n⟩ := b
  obtain ⟨j', p', n'⟩ := b'
  simp only [VG.Proof.MlKem.Arm.inB, VG.Proof.MlKem.Arm.sepB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne,
    ne_eq] at h ha hb ⊢
  obtain ⟨⟨e1, a1⟩, a2⟩ := ha
  obtain ⟨⟨e2, b1⟩, b2⟩ := hb
  subst e1; subst e2
  omega

theorem sepAll_mono {sz : List Nat} {a a' : Nat × Nat × Nat} {W W' : List (Nat × Nat × Nat)}
    (h : VG.Proof.MlKem.Arm.sepAll sz a W' = true) (ha : VG.Proof.MlKem.Arm.inB a' a = true) (hW : W.all (fun w => W'.any (VG.Proof.MlKem.Arm.inB w)) = true) :
    VG.Proof.MlKem.Arm.sepAll sz a' W = true :=
  List.all_eq_true.mpr fun w hw => by
    obtain ⟨w', hw', hi⟩ := List.any_eq_true.mp (List.all_eq_true.mp hW w hw)
    exact VG.Proof.MlKem.Arm.sepB_mono (List.all_eq_true.mp h w' hw') ha hi

theorem inB_off {i o l k n : Nat} (h : k + n ≤ l) : VG.Proof.MlKem.Arm.inB (i, o + k, n) (i, o, l) = true := by
  simp only [VG.Proof.MlKem.Arm.inB, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]; omega

theorem inB_refl (w : Nat × Nat × Nat) : VG.Proof.MlKem.Arm.inB w w = true := by
  simp only [VG.Proof.MlKem.Arm.inB, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]; omega

/-- The bounds of a region apart from another. -/
theorem sepAll_bounds {sz : List Nat} {i o l : Nat} {w : Nat × Nat × Nat} {W : List (Nat × Nat × Nat)}
    (h : VG.Proof.MlKem.Arm.sepAll sz (i, o, l) (w :: W) = true) : i < sz.length ∧ o + l ≤ sz.getD i 0 :=
  VG.Proof.MlKem.Arm.sepB_bounds (List.all_eq_true.mp h w (List.mem_cons_self ..))

/-- A part of a buffer inside a bigger one. -/
theorem KeptX.subOff {L : VG.Proof.MlKem.Arm.Lay} {xs : List Reg} {s s' : State} (hL : L.Ok) {i o l k n : Nat}
    (hb : i < L.sizes.length ∧ o + l ≤ L.size i) (hk : k + n ≤ l) (h : VG.Proof.MlKem.Arm.KeptX xs (L.RL [(i, o + k, n)]) s s') :
    VG.Proof.MlKem.Arm.KeptX xs (L.RL [(i, o, l)]) s s' :=
  h.sub fun r hr => by
    simp only [Lay.RL, List.map_cons, List.map_nil, List.mem_singleton] at hr; subst hr
    exact ⟨L.R i o l, List.mem_singleton_self _, Lay.R_sub_R hL hb.1 (by omega) (by omega) hb.2⟩

/-! ## Copying from an offset -/

theorem copyLo {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hL : L.Ok) {sb db : Reg} {bo so dO len i j : Nat}
    (hsb : sb ∈ preserved ∧ sb ≠ .lr) (hdb : db ∈ preserved ∧ db ≠ .lr)
    (gs : s.gpr sb = L.ptr i + BitVec.ofNat 32 bo) (gd : s.gpr db = L.ptr j)
    (hse : encodable (BitVec.ofNat 32 so) = true)
    (hde : encodable (BitVec.ofNat 32 dO) = true) (hle : encodable (BitVec.ofNat 32 len) = true)
    (hlen : len < 2 ^ 32) (hl0 : 0 < len) (hs : VG.Proof.MlKem.Arm.sepB L.sizes (i, bo + so, len) (j, dO, len) = true)
    (ri : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr) :
    WP isa (copy sb so db dO len) s fun s' =>
      Kept (L.RL [(j, dO, len)]) s s' ∧ bytesAt s'.mem (L.A j dO) len = bytesAt s.mem (L.A i (bo + so)) len := by
  obtain ⟨ea, fa⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds hs) hl0
  obtain ⟨eb, fb⟩ := Lay.ptr_ok hL (VG.Proof.MlKem.Arm.sepB_bounds (VG.Proof.MlKem.Arm.sepB_symm hs)) hl0
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.copy_setup hsb hdb hse hde hle) fun s₁ ⟨o₁, g0, g1, g2⟩ => ?_)
  rw [gs, ptr_add_add32] at g0; rw [gd] at g1
  refine WP.mono (VG.Proof.MlKem.Arm.copy_loop fa fb hlen hl0 (by rw [ea, eb]; exact Lay.disj hL hs)
    (by rw [ea, o₁.rd, o₁.wr]; exact Lay.covers ri (VG.Proof.MlKem.Arm.sepB_bounds hs).2)
    (by rw [eb, o₁.wr]; exact Lay.covers wj (VG.Proof.MlKem.Arm.sepB_bounds (VG.Proof.MlKem.Arm.sepB_symm hs)).2) g0 g1 g2)
    fun s' ⟨cs, rd, wr, sp, fr, hb⟩ => ⟨?_, ?_⟩
  · refine (o₁.kept _).trans ⟨fun r hr _ => cs r hr, sp, rd, wr, ?_⟩
    rw [eb] at fr; exact fr
  · rw [eb, ea, o₁.mem] at hb; exact hb

/-! ## Decoding `t̂` -/

theorem decTArgs_ok {s : State} {P B : BitVec 32} {i : Nat} (h7 : s.gpr .r7 = P) (h4 : s.gpr .r4 = B)
    (h9 : s.gpr .r9 = BitVec.ofNat 32 i) :
    WP isa (.block (at384 .r0 .r4 .r9 ++ slotAt .r1 .r9 (oPoly 0))) s fun s' =>
      VG.Proof.MlKem.Arm.Only s s' ∧ s'.gpr .r0 = B + BitVec.ofNat 32 i <<< 8 + BitVec.ofNat 32 i <<< 7 ∧
      s'.gpr .r1 = P + BitVec.ofNat 32 i <<< 10 + BitVec.ofNat 32 (oPoly 0) := by
  have e1 : encodable (BitVec.ofNat 32 (oPoly 0)) = true := by decide
  run_block [at384, slotAt, ptrTo, e1, h7, h4, h9]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, -, -, -⟩ := VG.Proof.MlKem.Arm.pres_ne hr hl
  simp only [m0, m1, ite_false]

/-- The polynomials `0` to `k - 1` decoded from the `384 k` bytes at offset `o` of buffer `i` (in `r4`). -/
structure DecInv (K : KemLay) (L : VG.Proof.MlKem.Arm.Lay) (i o : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  kx : VG.Proof.MlKem.Arm.KeptX [.r9] (L.RL [(0, 2048, 1024 * K.k)]) s₀ s
  r9 : s.gpr .r9 = BitVec.ofNat 32 j
  t : ∀ k < j, PolyIs s.mem (L.A 0 (oPoly k)) (decode12 (bytesAt s₀.mem (L.A i (o + 384 * k)) 384))

/-- Polynomial `k < K.k` of `t̂` is in what the decoding writes, apart from the others. -/
abbrev DecTSlots (K : KemLay) : Prop :=
  ∀ k < K.k, [((0 : Nat), oPoly k, (1024 : Nat))].all (fun w => [(0, 2048, 1024 * K.k)].any (VG.Proof.MlKem.Arm.subB0 w)) = true ∧
    (∀ k' < K.k, k' ≠ k → [((0 : Nat), oPoly k, (1024 : Nat))].all (VG.Proof.MlKem.Arm.sep0 (oPoly k') 1024) = true)

section
variable {K : KemLay} (hK : K.WF)
include hK

theorem decT_slots : VG.Proof.MlKem.Arm.DecTSlots K := (by decide : ∀ k < 5, DecTSlots (kOf k)) K.k (by have := hK.k4; omega)

theorem decT_step {L : VG.Proof.MlKem.Arm.Lay} {i o : Nat} {s₀ : State} (hc : VG.Proof.MlKem.Arm.Ctx L s₀) (h4 : s₀.gpr .r4 = L.ptr i + BitVec.ofNat 32 o)
    (hs : VG.Proof.MlKem.Arm.sepAll L.sizes (i, o, 384 * K.k) [(0, 2048, 1024 * K.k)] = true) (hr : L.buf i ∈ s₀.rd ++ s₀.wr)
    {j : Nat} (hj : j < K.k) {s : State} (h : VG.Proof.MlKem.Arm.DecInv K L i o s₀ j s) :
    WP isa K.decTBody s fun s' => VG.Proof.MlKem.Arm.DecInv K L i o s₀ (j + 1) s' ∧ s'.z = decide (j + 1 = K.k) := by
  have hL := hc.ok
  have k4 := hK.k4
  have hc' := h.kx.ctx (by decide) hc
  obtain ⟨c_sub, c_sep⟩ := VG.Proof.MlKem.Arm.decT_slots hK j hj
  have g4 : s.gpr .r4 = L.ptr i + BitVec.ofNat 32 o := by rw [h.kx.cs .r4 (by decide) (by decide) (by decide), h4]
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.decTArgs_ok hc'.r7 g4 h.r9) fun s₁ ⟨o₁, a0, a1⟩ => ?_)
  rw [VG.Proof.MlKem.Arm.at384_eq _ (by omega), ptr_add_add32] at a0
  rw [VG.Proof.MlKem.Arm.slot_eq _ (by offs), show 2048 + 1024 * 0 + 1024 * j = 2048 + 1024 * j by omega] at a1
  have hc₁ := hc'.only o₁
  have hsj : VG.Proof.MlKem.Arm.sepAll L.sizes (i, o + 384 * j, 384) [(0, 2048, 1024 * K.k)] = true :=
    VG.Proof.MlKem.Arm.sepAll_mono hs (VG.Proof.MlKem.Arm.inB_off (by omega)) (by kdecide)
  have hsep : VG.Proof.MlKem.Arm.sepB L.sizes (i, o + 384 * j, 384) (0, oPoly j, 1024) = true :=
    VG.Proof.MlKem.Arm.sepB_mono (List.all_eq_true.mp hsj _ (List.mem_singleton_self _)) (VG.Proof.MlKem.Arm.inB_refl _) (by
      simp only [VG.Proof.MlKem.Arm.inB, oPoly, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]; omega)
  refine WP.seq (VG.Proof.MlKem.Arm.decode12L hL a0 a1 hsep (by rw [o₁.rd, o₁.wr, h.kx.rd, h.kx.wr]; exact hr) hc₁.buf0
    fun s₂ k₂ p₂ => ?_)
  have g9 : s₂.gpr .r9 = BitVec.ofNat 32 j := by
    rw [k₂.cs .r9 (by decide) (by decide), o₁.cs .r9 (by decide) (by decide), h.r9]
  refine WP.mono (VG.Proof.MlKem.Arm.count_ok (by omega) (by omega) (by kenc) g9) fun s' ⟨k', g', z'⟩ => ⟨⟨?_, g', ?_⟩, z'⟩
  all_goals have K : VG.Proof.MlKem.Arm.KeptX [.r9] (L.RL [(0, oPoly j, 1024)]) s s' :=
    (o₁.x _ _).trans ((k₂.x _).trans (k'.mono (fun _ h => absurd h List.not_mem_nil)))
  · exact h.kx.trans (K.subL hc c_sub)
  · intro k hk
    have hb : bytesAt s.mem (L.A i (o + 384 * j)) 384 = bytesAt s₀.mem (L.A i (o + 384 * j)) 384 :=
      Lay.bytes_keep hL h.kx.frame hsj (by decide)
    by_cases e : k = j
    · subst e
      rw [o₁.mem, hb] at p₂
      exact polyIs_frame k'.frame (fun _ h => absurd h List.not_mem_nil) p₂
    · exact Lay.polyIs_keep hL K.frame (hc.sepAll0 (by offs) (c_sep k (by omega) e)) (h.t k (by omega))

omit hK in
theorem decT_init {L : VG.Proof.MlKem.Arm.Lay} {i o : Nat} {s₀ : State} :
    WP isa (.block [.mov .r9 (.imm 0)]) s₀ (VG.Proof.MlKem.Arm.DecInv K L i o s₀ 0) :=
  WP.mono (VG.Proof.MlKem.Arm.movc_ok .r9 (N := 0) (by decide)) fun _ ⟨k, g, _⟩ =>
    ⟨k.mono (fun _ h => absurd h List.not_mem_nil), g, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩

theorem decT_loop {L : VG.Proof.MlKem.Arm.Lay} {i o : Nat} {s₀ : State} (hc : VG.Proof.MlKem.Arm.Ctx L s₀) (h4 : s₀.gpr .r4 = L.ptr i + BitVec.ofNat 32 o)
    (hs : VG.Proof.MlKem.Arm.sepAll L.sizes (i, o, 384 * K.k) [(0, 2048, 1024 * K.k)] = true) (hr : L.buf i ∈ s₀.rd ++ s₀.wr) {s : State}
    (h : VG.Proof.MlKem.Arm.DecInv K L i o s₀ 0 s) : WP isa (.loop K.decTBody .ne) s (VG.Proof.MlKem.Arm.DecInv K L i o s₀ K.k) :=
  wp_loop_ne (VG.Proof.MlKem.Arm.DecInv K L i o s₀) (N := K.k) hK.k1 (fun _ hj _ h => VG.Proof.MlKem.Arm.decT_step hK hc h4 hs hr hj h) (fun _ h => h) h

end

namespace Enc

/-! ## The buffers of K-PKE.Encrypt -/

/-- Where `encrypt` finds `ek` and `m`, and writes `c`: offsets in buffers. -/
structure EB where
  iE : Nat
  oE : Nat
  iM : Nat
  oM : Nat
  iC : Nat
  oC : Nat

/-- What `encrypt` changes in `scratch` and the stack: the polynomials and the
working spaces of the callees. -/
abbrev encW0 (K : KemLay) : List (Nat × Nat × Nat) :=
  [(0, 0, 840), (0, 952, 1), (0, 1024, 128), (0, 1216, 34), (0, 2048, 1024 * (3 * K.k + 5)), (0, K.oSample, 3072),
    (1, 0, 8)]

/-- What `encrypt` changes. -/
abbrev encW (K : KemLay) (b : VG.Proof.MlKem.Arm.Enc.EB) : List (Nat × Nat × Nat) := VG.Proof.MlKem.Arm.Enc.encW0 K ++ [(b.iC, b.oC, K.ctLen)]

/-- A state `encrypt` runs from. -/
structure EncPre (K : KemLay) (L : VG.Proof.MlKem.Arm.Lay) (b : VG.Proof.MlKem.Arm.Enc.EB) (s : State) : Prop where
  wf : K.WF
  calls : K.CallsOk
  ctx : VG.Proof.MlKem.Arm.Ctx L s
  r4 : s.gpr .r4 = L.ptr b.iE + BitVec.ofNat 32 b.oE
  r5 : s.gpr .r5 = L.ptr b.iM + BitVec.ofNat 32 b.oM
  r8 : s.gpr .r8 = L.ptr b.iC + BitVec.ofNat 32 b.oC
  sE : VG.Proof.MlKem.Arm.sepAll L.sizes (b.iE, b.oE, K.ekLen) (VG.Proof.MlKem.Arm.Enc.encW0 K) = true
  sM : VG.Proof.MlKem.Arm.sepAll L.sizes (b.iM, b.oM, 32) (VG.Proof.MlKem.Arm.Enc.encW0 K) = true
  sC : VG.Proof.MlKem.Arm.sepAll L.sizes (b.iC, b.oC, K.ctLen) (VG.Proof.MlKem.Arm.Enc.encW0 K) = true
  wE : L.buf b.iE ∈ s.rd ++ s.wr
  wM : L.buf b.iM ∈ s.rd ++ s.wr
  wC : L.buf b.iC ∈ s.wr

/-- The entries of `Â` the products use, from `ρ` and `r`: `Â[i, j]`, or
`ŷ[i]` if its `SampleNTT` does not finish. -/
def aEnc (ρ r : List Byte) (i j : Nat) : VG.Spec.MlKem.Poly := VG.Proof.MlKem.Arm.effA true ρ j i (VG.Proof.MlKem.encY r i)

/-- Whether the `SampleNTT`s of the first `i` rows of `Â^⊺` (of `k` entries) finished. -/
def okEnc (k : Nat) (ρ : List Byte) (i : Nat) : Bool := (List.range i).all fun i' => VG.Proof.MlKem.Arm.okRow true ρ i' k

section
variable (K : KemLay) (L : VG.Proof.MlKem.Arm.Lay) (b : VG.Proof.MlKem.Arm.Enc.EB) (s₀ : State)

/-- `ek`. -/
abbrev ekB : List Byte := bytesAt s₀.mem (L.A b.iE b.oE) K.ekLen
/-- `m`. -/
abbrev mB : List Byte := bytesAt s₀.mem (L.A b.iM b.oM) 32
/-- `r`. -/
abbrev rB : List Byte := bytesAt s₀.mem (L.A 0 oSigma) 32

/-- `ρ`. -/
abbrev ρE : List Byte := ekRho K.p (VG.Proof.MlKem.Arm.Enc.ekB K L b s₀)
/-- The entries of `Â` the products use. -/
abbrev aE : Nat → Nat → VG.Spec.MlKem.Poly := VG.Proof.MlKem.Arm.Enc.aEnc (VG.Proof.MlKem.Arm.Enc.ρE K L b s₀) (VG.Proof.MlKem.Arm.Enc.rB L s₀)
/-- Whether the `SampleNTT`s of the first `i` rows finished. -/
abbrev okE (i : Nat) : Bool := VG.Proof.MlKem.Arm.Enc.okEnc K.k (VG.Proof.MlKem.Arm.Enc.ρE K L b s₀) i

end

theorem okE_succ (K : KemLay) (L : VG.Proof.MlKem.Arm.Lay) (b : VG.Proof.MlKem.Arm.Enc.EB) (s₀ : State) (i : Nat) :
    VG.Proof.MlKem.Arm.Enc.okE K L b s₀ (i + 1) = (VG.Proof.MlKem.Arm.Enc.okE K L b s₀ i && VG.Proof.MlKem.Arm.okRow true (VG.Proof.MlKem.Arm.Enc.ρE K L b s₀) i K.k) := by
  simp only [VG.Proof.MlKem.Arm.Enc.okE, VG.Proof.MlKem.Arm.Enc.okEnc, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]

/-- Before the rows: what changes is within `encW0`. -/
abbrev EA (K : KemLay) (L : VG.Proof.MlKem.Arm.Lay) (s₀ s : State) : Prop := VG.Proof.MlKem.Arm.KeptX [.r9, .r10, .r11] (L.RL (VG.Proof.MlKem.Arm.Enc.encW0 K)) s₀ s

section
variable {K : KemLay} {L : VG.Proof.MlKem.Arm.Lay} {b : VG.Proof.MlKem.Arm.Enc.EB} {s₀ : State} (hp : VG.Proof.MlKem.Arm.Enc.EncPre K L b s₀)
include hp

theorem EA.ctx {s : State} (h : VG.Proof.MlKem.Arm.Enc.EA K L s₀ s) : VG.Proof.MlKem.Arm.Ctx L s := KeptX.ctx h (by decide) hp.ctx

/-- The bytes of a part of a buffer apart from `encW0`. -/
theorem EA.bytes {s : State} (h : VG.Proof.MlKem.Arm.Enc.EA K L s₀ s) {i o l : Nat} (hs : VG.Proof.MlKem.Arm.sepAll L.sizes (i, o, l) (VG.Proof.MlKem.Arm.Enc.encW0 K) = true) :
    bytesAt s.mem (L.A i o) l = bytesAt s₀.mem (L.A i o) l := by
  have := VG.Proof.MlKem.Arm.sepAll_bounds hs
  have := hp.ctx.ok.fit i this.1
  exact Lay.bytes_keep hp.ctx.ok h.frame hs (by simp only [Lay.size] at this; omega)

theorem EA.ek {s : State} (h : VG.Proof.MlKem.Arm.Enc.EA K L s₀ s) {k n : Nat} (hk : k + n ≤ K.ekLen) :
    bytesAt s.mem (L.A b.iE (b.oE + k)) n = bytesAt s₀.mem (L.A b.iE (b.oE + k)) n :=
  EA.bytes hp h (VG.Proof.MlKem.Arm.sepAll_mono hp.sE (VG.Proof.MlKem.Arm.inB_off hk) (List.all_eq_true.mpr fun _ h => List.any_eq_true.mpr ⟨_, h, VG.Proof.MlKem.Arm.inB_refl _⟩))

omit hp in
theorem EA.reg {s : State} (h : VG.Proof.MlKem.Arm.Enc.EA K L s₀ s) {r : Reg} (hr : r ∈ [Reg.r4, .r5, .r7, .r8]) : s.gpr r = s₀.gpr r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact h.cs _ (by decide) (by decide) (by decide)

/-! ## `ρ` -/

theorem enc1_ok : WP isa (copy .r4 (384 * K.k) .r7 oSeed 32) s₀ fun s =>
    VG.Proof.MlKem.Arm.Enc.EA K L s₀ s ∧ Frame (L.RL [(0, oSeed, 32)]) s₀.mem s.mem ∧ bytesAt s.mem (L.A 0 oSeed) 32 = VG.Proof.MlKem.Arm.Enc.ρE K L b s₀ := by
  have hL := hp.ctx.ok
  have hK := hp.wf
  have k4 := hK.k4
  have hs : VG.Proof.MlKem.Arm.sepB L.sizes (b.iE, b.oE + 384 * K.k, 32) (0, oSeed, 32) = true :=
    VG.Proof.MlKem.Arm.sepB_mono (List.all_eq_true.mp hp.sE (0, 1216, 34) (by simp)) (VG.Proof.MlKem.Arm.inB_off (by offs)) (by decide)
  refine WP.mono (VG.Proof.MlKem.Arm.copyLo hL (bo := b.oE) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ hp.r4 hp.ctx.r7 hK.encT
    (by decide) (by decide) (by decide) (by decide) hs hp.wE hp.ctx.buf0) fun s ⟨k, e⟩ =>
    ⟨(k.x _).subL hp.ctx (by kdecide), k.frame, e.trans ?_⟩
  show _ = ((bytesAt s₀.mem (L.A b.iE b.oE) K.ekLen).drop (384 * K.k)).take 32
  rw [bytesAt_slice _ _ (by offs), add_ofNat_add]

/-! ## `t̂` -/

theorem enc2_ok {s₁ : State} (h₁ : VG.Proof.MlKem.Arm.Enc.EA K L s₀ s₁) (hρ : bytesAt s₁.mem (L.A 0 oSeed) 32 = VG.Proof.MlKem.Arm.Enc.ρE K L b s₀) {s : State}
    (h : VG.Proof.MlKem.Arm.DecInv K L b.iE b.oE s₁ K.k s) :
    VG.Proof.MlKem.Arm.Enc.EA K L s₀ s ∧ bytesAt s.mem (L.A 0 oSeed) 32 = VG.Proof.MlKem.Arm.Enc.ρE K L b s₀ ∧
      ∀ k < K.k, PolyIs s.mem (L.A 0 (oPoly k)) (VG.Proof.MlKem.ekT (VG.Proof.MlKem.Arm.Enc.ekB K L b s₀) k) := by
  have hK := hp.wf
  refine ⟨h₁.trans ((h.kx.weaken (by simp)).subL hp.ctx (by kdecide)),
    (Lay.bytes_keep hp.ctx.ok h.kx.frame (hp.ctx.sepAll0 (by decide) (by kdecide)) (by decide)).trans hρ,
    fun k hk => ?_⟩
  have := h.t k hk
  rw [EA.ek hp h₁ (by offs)] at this
  show PolyIs _ _ (decode12 (((bytesAt s₀.mem (L.A b.iE b.oE) K.ekLen).drop (384 * k)).take 384))
  rw [bytesAt_slice _ _ (by offs), add_ofNat_add]; exact this

/-! ## The `PRF`s -/

/-- How the regions of the `PRF`s lie among those of `encrypt`. -/
abbrev PrfEk (K : KemLay) : Prop := (VG.Proof.MlKem.Arm.prfLW K 0 K.k).all (fun w => (VG.Proof.MlKem.Arm.Enc.encW0 K).any (VG.Proof.MlKem.Arm.subB0 w)) = true ∧
    (VG.Proof.MlKem.Arm.prfLW K K.k (2 * K.k + 1)).all (fun w => (VG.Proof.MlKem.Arm.Enc.encW0 K).any (VG.Proof.MlKem.Arm.subB0 w)) = true ∧
    (VG.Proof.MlKem.Arm.prfLW K 0 K.k).all (VG.Proof.MlKem.Arm.sep0 oSeed 32) = true ∧ (VG.Proof.MlKem.Arm.prfLW K K.k (2 * K.k + 1)).all (VG.Proof.MlKem.Arm.sep0 oSeed 32) = true ∧
    (∀ k < K.k, (VG.Proof.MlKem.Arm.prfLW K 0 K.k).all (VG.Proof.MlKem.Arm.sep0 (oPoly k) 1024) = true) ∧
    (∀ k < 2 * K.k, (VG.Proof.MlKem.Arm.prfLW K K.k (2 * K.k + 1)).all (VG.Proof.MlKem.Arm.sep0 (oPoly k) 1024) = true) ∧
    (VG.Proof.MlKem.Arm.Enc.encW0 K).all (VG.Proof.MlKem.Arm.sep0 oSigma 32) = true

omit hp in
theorem prf_ek (hK : K.WF) : VG.Proof.MlKem.Arm.Enc.PrfEk K :=
  (by decide : ∀ k < 5, PrfEk (kOf k)) K.k (by have := hK.k4; omega)

theorem enc3_ok {s₂ : State} (h₂ : VG.Proof.MlKem.Arm.Enc.EA K L s₀ s₂) (hρ : bytesAt s₂.mem (L.A 0 oSeed) 32 = VG.Proof.MlKem.Arm.Enc.ρE K L b s₀)
    (ht : ∀ k < K.k, PolyIs s₂.mem (L.A 0 (oPoly k)) (VG.Proof.MlKem.ekT (VG.Proof.MlKem.Arm.Enc.ekB K L b s₀) k)) :
    WP isa (K.prfLoop true 0 K.k) s₂ fun s => VG.Proof.MlKem.Arm.Enc.EA K L s₀ s ∧ bytesAt s.mem (L.A 0 oSeed) 32 = VG.Proof.MlKem.Arm.Enc.ρE K L b s₀ ∧
      (∀ k < K.k, PolyIs s.mem (L.A 0 (oPoly k)) (VG.Proof.MlKem.ekT (VG.Proof.MlKem.Arm.Enc.ekB K L b s₀) k)) ∧
      ∀ j < K.k, PolyIs s.mem (L.A 0 (oPoly (K.k + j))) (VG.Proof.MlKem.encY (VG.Proof.MlKem.Arm.Enc.rB L s₀) j) := by
  have hK := hp.wf
  have hc := EA.ctx hp h₂
  obtain ⟨c1, -, c3, -, c5, -, c7⟩ := VG.Proof.MlKem.Arm.Enc.prf_ek hK
  refine WP.mono (VG.Proof.MlKem.Arm.prfLoop_ok hK hc true (N₀ := 0) (N₁ := K.k) hK.k1 (by omega)
    (EA.bytes hp h₂ (hp.ctx.sepAll0 (by decide) c7))) fun s ⟨k, p⟩ => ⟨?_, ?_, fun k' hk' => ?_, fun j hj => ?_⟩
  · exact h₂.trans ((k.weaken (by simp)).subL hp.ctx c1)
  · rw [← hρ]; exact Lay.bytes_keep hp.ctx.ok k.frame (hc.sepAll0 (by decide) c3) (by decide)
  · exact Lay.polyIs_keep hp.ctx.ok k.frame (hc.sepAll0 (by offs) (c5 k' hk')) (ht k' hk')
  · exact p j (Nat.zero_le _) hj

theorem enc4_ok {s₃ : State} (h₃ : VG.Proof.MlKem.Arm.Enc.EA K L s₀ s₃) (hρ : bytesAt s₃.mem (L.A 0 oSeed) 32 = VG.Proof.MlKem.Arm.Enc.ρE K L b s₀)
    (hv : ∀ k < 2 * K.k, PolyIs s₃.mem (L.A 0 (oPoly k)) (if k < K.k then VG.Proof.MlKem.ekT (VG.Proof.MlKem.Arm.Enc.ekB K L b s₀) k
      else VG.Proof.MlKem.encY (VG.Proof.MlKem.Arm.Enc.rB L s₀) (k - K.k))) :
    WP isa (K.prfLoop false K.k (2 * K.k + 1)) s₃ fun s => VG.Proof.MlKem.Arm.Enc.EA K L s₀ s ∧ bytesAt s.mem (L.A 0 oSeed) 32 = VG.Proof.MlKem.Arm.Enc.ρE K L b s₀ ∧
      (∀ k < 2 * K.k, PolyIs s.mem (L.A 0 (oPoly k)) (if k < K.k then VG.Proof.MlKem.ekT (VG.Proof.MlKem.Arm.Enc.ekB K L b s₀) k
        else VG.Proof.MlKem.encY (VG.Proof.MlKem.Arm.Enc.rB L s₀) (k - K.k))) ∧
      ∀ N, K.k ≤ N → N < 2 * K.k + 1 → PolyIs s.mem (L.A 0 (oPoly (K.k + N))) (VG.Proof.MlKem.cbd (VG.Proof.MlKem.Arm.Enc.rB L s₀) N) := by
  have hK := hp.wf
  have hc := EA.ctx hp h₃
  obtain ⟨-, c2, -, c4, -, c6, c7⟩ := VG.Proof.MlKem.Arm.Enc.prf_ek hK
  refine WP.mono (VG.Proof.MlKem.Arm.prfLoop_ok hK hc false (N₀ := K.k) (N₁ := 2 * K.k + 1) (by omega) (by omega)
    (EA.bytes hp h₃ (hp.ctx.sepAll0 (by decide) c7))) fun s ⟨k, p⟩ => ⟨?_, ?_, fun k' hk' => ?_, p⟩
  · exact h₃.trans ((k.weaken (by simp)).subL hp.ctx c2)
  · rw [← hρ]; exact Lay.bytes_keep hp.ctx.ok k.frame (hc.sepAll0 (by decide) c4) (by decide)
  · exact Lay.polyIs_keep hp.ctx.ok k.frame (hc.sepAll0 (by offs) (c6 k' hk')) (hv k' hk')

/-! ## `μ` -/

omit hp in
theorem muArgs_ok (hK : K.WF) {s : State} {P M : BitVec 32} (h7 : s.gpr .r7 = P) (h5 : s.gpr .r5 = M) :
    WP isa (.block [.mov .r0 (.reg .r5), .mov .r1 (.imm 32), .mov .r2 (.imm 1), ptrTo .r3 .r7 (oPoly (3 * K.k + 1))]) s
      fun s' => VG.Proof.MlKem.Arm.Only s s' ∧ s'.gpr .r0 = M ∧ s'.gpr .r1 = BitVec.ofNat 32 (32 * 1) ∧
        s'.gpr .r2 = BitVec.ofNat 32 1 ∧ s'.gpr .r3 = P + BitVec.ofNat 32 (oPoly (3 * K.k + 1)) := by
  have e1 : encodable (32 : BitVec 32) = true := by decide
  have e2 : encodable (1 : BitVec 32) = true := by decide
  have e3 : encodable (BitVec.ofNat 32 (oPoly (3 * K.k + 1))) = true := hK.enc (by omega)
  run_block [ptrTo, e1, e2, e3, h7, h5]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, m2, m3, -⟩ := VG.Proof.MlKem.Arm.pres_ne hr hl
  simp only [m0, m1, m2, m3, ite_false]

theorem enc5a_ok {s₄ : State} (h₄ : VG.Proof.MlKem.Arm.Enc.EA K L s₀ s₄) :
    WP isa (.block [.mov .r0 (.reg .r5), .mov .r1 (.imm 32), .mov .r2 (.imm 1), ptrTo .r3 .r7 (oPoly (3 * K.k + 1))]) s₄
      fun s => (VG.Proof.MlKem.Arm.Enc.EA K L s₀ s ∧ s.mem = s₄.mem) ∧ s.gpr .r0 = L.ptr b.iM + BitVec.ofNat 32 b.oM ∧
        s.gpr .r1 = BitVec.ofNat 32 (32 * 1) ∧ s.gpr .r2 = BitVec.ofNat 32 1 ∧
        s.gpr .r3 = L.ptr 0 + BitVec.ofNat 32 (oPoly (3 * K.k + 1)) := by
  have hc := EA.ctx hp h₄
  have g5 : s₄.gpr .r5 = L.ptr b.iM + BitVec.ofNat 32 b.oM := by rw [EA.reg h₄ (by simp), hp.r5]
  exact WP.mono (VG.Proof.MlKem.Arm.Enc.muArgs_ok hp.wf hc.r7 g5) fun s₁ ⟨o₁, a0, a1, a2, a3⟩ =>
    ⟨⟨h₄.trans (o₁.x _ _), o₁.mem⟩, a0, a1, a2, a3⟩

theorem enc5b_ok {s₄ s : State} (h₄ : VG.Proof.MlKem.Arm.Enc.EA K L s₀ s₄) (h : VG.Proof.MlKem.Arm.Enc.EA K L s₀ s ∧ s.mem = s₄.mem)
    (a0 : s.gpr .r0 = L.ptr b.iM + BitVec.ofNat 32 b.oM) (a1 : s.gpr .r1 = BitVec.ofNat 32 (32 * 1))
    (a2 : s.gpr .r2 = BitVec.ofNat 32 1) (a3 : s.gpr .r3 = L.ptr 0 + BitVec.ofNat 32 (oPoly (3 * K.k + 1))) :
    WP isa callDecompress s fun s' => VG.Proof.MlKem.Arm.Enc.EA K L s₀ s' ∧ Frame (L.RL [(0, oPoly (3 * K.k + 1), 1024)]) s₄.mem s'.mem ∧
      PolyIs s'.mem (L.A 0 (oPoly (3 * K.k + 1))) (decodeDecompress 1 (VG.Proof.MlKem.Arm.Enc.mB L b s₀)) := by
  have hK := hp.wf
  have hc := EA.ctx hp h.1
  have hs : VG.Proof.MlKem.Arm.sepB L.sizes (b.iM, b.oM, 32 * 1) (0, oPoly (3 * K.k + 1), 1024) = true :=
    VG.Proof.MlKem.Arm.sepB_mono (List.all_eq_true.mp hp.sM (0, 2048, 1024 * (3 * K.k + 5)) (by simp)) (VG.Proof.MlKem.Arm.inB_refl _) (by kdecide)
  refine VG.Proof.MlKem.Arm.decompressL hp.ctx.ok a0 a1 a2 a3 (by decide) hs (by rw [h.1.rd, h.1.wr]; exact hp.wM)
    hc.buf0 fun s' k p => ⟨?_, ?_, ?_⟩
  · exact h.1.trans ((k.x _).subL hp.ctx (by kdecide))
  · rw [← h.2]; exact k.frame
  · rw [h.2, show 32 * 1 = 32 from rfl, EA.bytes hp h₄ hp.sM] at p; exact p

end

/-! ## What the rows and `v` use -/

theorem sepAll_left {sz : List Nat} {a a' : Nat × Nat × Nat} {W : List (Nat × Nat × Nat)} (h : VG.Proof.MlKem.Arm.sepAll sz a W = true)
    (ha : VG.Proof.MlKem.Arm.inB a' a = true) : VG.Proof.MlKem.Arm.sepAll sz a' W = true :=
  VG.Proof.MlKem.Arm.sepAll_mono h ha (List.all_eq_true.mpr fun w hw => List.any_eq_true.mpr ⟨w, hw, VG.Proof.MlKem.Arm.inB_refl w⟩)

theorem sepB_same {sz : List Nat} {i o l o' l' : Nat} (hb : i < sz.length) (h1 : o + l ≤ sz.getD i 0)
    (h2 : o' + l' ≤ sz.getD i 0) (hd : o + l ≤ o' ∨ o' + l' ≤ o) : VG.Proof.MlKem.Arm.sepB sz (i, o, l) (i, o', l') = true := by
  simp only [VG.Proof.MlKem.Arm.sepB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_true_eq_false,
    false_or]
  omega

/-- The polynomials the rows and `v` use: `ρ`, `t̂`, `ŷ`, `e₁`, `e₂` and `μ`. -/
structure EData (K : KemLay) (L : VG.Proof.MlKem.Arm.Lay) (b : VG.Proof.MlKem.Arm.Enc.EB) (s₀ s : State) : Prop where
  rho : bytesAt s.mem (L.A 0 oSeed) 32 = VG.Proof.MlKem.Arm.Enc.ρE K L b s₀
  v : ∀ k < 2 * K.k, PolyIs s.mem (L.A 0 (oPoly k)) (if k < K.k then VG.Proof.MlKem.ekT (VG.Proof.MlKem.Arm.Enc.ekB K L b s₀) k
    else VG.Proof.MlKem.encY (VG.Proof.MlKem.Arm.Enc.rB L s₀) (k - K.k))
  e : ∀ N, K.k ≤ N → N < 2 * K.k + 1 → PolyIs s.mem (L.A 0 (oPoly (K.k + N))) (VG.Proof.MlKem.cbd (VG.Proof.MlKem.Arm.Enc.rB L s₀) N)
  mu : PolyIs s.mem (L.A 0 (oPoly (3 * K.k + 1))) (decodeDecompress 1 (VG.Proof.MlKem.Arm.Enc.mB L b s₀))

theorem EData.keep {K : KemLay} {L : VG.Proof.MlKem.Arm.Lay} {b : VG.Proof.MlKem.Arm.Enc.EB} {s₀ s s' : State} (hL : L.Ok) (h : VG.Proof.MlKem.Arm.Enc.EData K L b s₀ s)
    {W : List (Nat × Nat × Nat)} (hf : Frame (L.RL W) s.mem s'.mem) (h1 : VG.Proof.MlKem.Arm.sepAll L.sizes (0, 1216, 32) W = true)
    (h2 : VG.Proof.MlKem.Arm.sepAll L.sizes (0, 2048, 1024 * (3 * K.k + 2)) W = true) : VG.Proof.MlKem.Arm.Enc.EData K L b s₀ s' := by
  have hp : ∀ k < 3 * K.k + 2, VG.Proof.MlKem.Arm.sepAll L.sizes (0, oPoly k, 1024) W = true := fun k hk =>
    VG.Proof.MlKem.Arm.Enc.sepAll_left h2 (by simp only [VG.Proof.MlKem.Arm.inB, oPoly, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]; omega)
  exact ⟨(Lay.bytes_keep hL hf h1 (by decide)).trans h.rho, fun k hk => Lay.polyIs_keep hL hf (hp k (by omega)) (h.v k hk),
    fun N h3 h7 => Lay.polyIs_keep hL hf (hp (K.k + N) (by omega)) (h.e N h3 h7),
    Lay.polyIs_keep hL hf (hp (3 * K.k + 1) (by omega)) h.mu⟩

/-- After the rows `i' < i`. -/
structure ERow (K : KemLay) (L : VG.Proof.MlKem.Arm.Lay) (b : VG.Proof.MlKem.Arm.Enc.EB) (s₀ : State) (i : Nat) (s : State) : Prop where
  kx : VG.Proof.MlKem.Arm.KeptX [.r9, .r10, .r11] (L.RL (VG.Proof.MlKem.Arm.Enc.encW K b)) s₀ s
  r9 : s.gpr .r9 = BitVec.ofNat 32 i
  r11 : s.gpr .r11 = if VG.Proof.MlKem.Arm.Enc.okE K L b s₀ i then 1 else 0
  d : VG.Proof.MlKem.Arm.Enc.EData K L b s₀ s
  c : ∀ i' < i, bytesAt s.mem (L.A b.iC (b.oC + K.uLen * i')) K.uLen =
    compressEncode K.du (VG.Proof.MlKem.KPke.encU K.p (VG.Proof.MlKem.Arm.Enc.aE K L b s₀) (VG.Proof.MlKem.Arm.Enc.rB L s₀) i')

/-- In row `i` (from `s`), with the sum `f`. -/
structure RB (K : KemLay) (L : VG.Proof.MlKem.Arm.Lay) (b : VG.Proof.MlKem.Arm.Enc.EB) (s₀ : State) (i : Nat) (s : State) (f : VG.Spec.MlKem.Poly) (s' : State) : Prop where
  kx : VG.Proof.MlKem.Arm.KeptX [.r9, .r10, .r11] (L.RL (VG.Proof.MlKem.Arm.rowW K)) s s'
  r9 : s'.gpr .r9 = BitVec.ofNat 32 i
  r11 : s'.gpr .r11 = if VG.Proof.MlKem.Arm.Enc.okE K L b s₀ (i + 1) then 1 else 0
  acc : PolyIs s'.mem (L.A 0 K.oAcc) f

/-- In row `i`, after its encoding. -/
structure RC (K : KemLay) (L : VG.Proof.MlKem.Arm.Lay) (b : VG.Proof.MlKem.Arm.Enc.EB) (s₀ : State) (i : Nat) (s : State) (s' : State) : Prop where
  kx : VG.Proof.MlKem.Arm.KeptX [.r9, .r10, .r11] (L.RL (VG.Proof.MlKem.Arm.rowW K ++ [(b.iC, b.oC + K.uLen * i, K.uLen)])) s s'
  r9 : s'.gpr .r9 = BitVec.ofNat 32 i
  r11 : s'.gpr .r11 = if VG.Proof.MlKem.Arm.Enc.okE K L b s₀ (i + 1) then 1 else 0
  cb : bytesAt s'.mem (L.A b.iC (b.oC + K.uLen * i)) K.uLen =
    compressEncode K.du (VG.Proof.MlKem.KPke.encU K.p (VG.Proof.MlKem.Arm.Enc.aE K L b s₀) (VG.Proof.MlKem.Arm.Enc.rB L s₀) i)

/-- How the regions of a row lie among those of `encrypt`. -/
abbrev RowFacts (K : KemLay) : Prop := (VG.Proof.MlKem.Arm.rowW K).all (fun w => (VG.Proof.MlKem.Arm.Enc.encW0 K).any (VG.Proof.MlKem.Arm.subB0 w)) = true ∧
    (VG.Proof.MlKem.Arm.rowW K).all (fun w => (VG.Proof.MlKem.Arm.Enc.encW0 K).any (VG.Proof.MlKem.Arm.inB w)) = true ∧
    (VG.Proof.MlKem.Arm.rowW K).all (VG.Proof.MlKem.Arm.sep0 1216 32) = true ∧ (VG.Proof.MlKem.Arm.rowW K).all (VG.Proof.MlKem.Arm.sep0 2048 (1024 * (3 * K.k + 2))) = true ∧
    [((0 : Nat), K.oAcc, (1024 : Nat)), (0, K.oNtt, 1024)].all (fun w => (VG.Proof.MlKem.Arm.rowW K).any (VG.Proof.MlKem.Arm.subB0 w)) = true ∧
    [((0 : Nat), K.oAcc, (1024 : Nat))].all (fun w => (VG.Proof.MlKem.Arm.rowW K).any (VG.Proof.MlKem.Arm.subB0 w)) = true ∧
    (∀ i < K.k, (VG.Proof.MlKem.Arm.rowW K).all (VG.Proof.MlKem.Arm.sep0 (oPoly (K.k + (K.k + i))) 1024) = true)

theorem row_facts {K : KemLay} (hK : K.WF) : VG.Proof.MlKem.Arm.Enc.RowFacts K := (by decide : ∀ k < 5, RowFacts (kOf k)) K.k (by have := hK.k4; omega)

/-- A `u[i]` within `c`. -/
theorem uSlot {K : KemLay} {i : Nat} (hi : i < K.k) : K.uLen * i + K.uLen ≤ K.ctLen := by
  have : K.uLen * i + K.uLen ≤ K.uLen * K.k := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  simp only [KemLay.ctLen]; omega

/-- Two `u[i]` within `c` are apart. -/
theorem uApart {K : KemLay} {i i' : Nat} (h : i' ≠ i) :
    K.uLen * i' + K.uLen ≤ K.uLen * i ∨ K.uLen * i + K.uLen ≤ K.uLen * i' := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact .inl (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h)
  · exact .inr (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h)

section
variable {K : KemLay} {L : VG.Proof.MlKem.Arm.Lay} {b : VG.Proof.MlKem.Arm.Enc.EB} {s₀ : State} (hp : VG.Proof.MlKem.Arm.Enc.EncPre K L b s₀)
include hp

/-- The part `[k, k + n)` of `c` apart from regions inside `encW0`. -/
theorem cSep {k n : Nat} (hk : k + n ≤ K.ctLen) {W : List (Nat × Nat × Nat)}
    (hW : W.all (fun w => (VG.Proof.MlKem.Arm.Enc.encW0 K).any (VG.Proof.MlKem.Arm.inB w)) = true) : VG.Proof.MlKem.Arm.sepAll L.sizes (b.iC, b.oC + k, n) W = true :=
  VG.Proof.MlKem.Arm.sepAll_mono hp.sC (VG.Proof.MlKem.Arm.inB_off hk) hW

theorem cData {k n : Nat} (hk : k + n ≤ K.ctLen) :
    VG.Proof.MlKem.Arm.sepAll L.sizes (0, 1216, 32) [(b.iC, b.oC + k, n)] = true ∧
      VG.Proof.MlKem.Arm.sepAll L.sizes (0, 2048, 1024 * (3 * K.k + 2)) [(b.iC, b.oC + k, n)] = true := by
  have hK := hp.wf
  have c1 := VG.Proof.MlKem.Arm.Enc.cSep hp hk (W := [(0, 1216, 32)]) (by kdecide)
  have c2 := VG.Proof.MlKem.Arm.Enc.cSep hp hk (W := [(0, 2048, 1024 * (3 * K.k + 2))]) (by kdecide)
  simp only [VG.Proof.MlKem.Arm.sepAll, List.all_cons, List.all_nil, Bool.and_true] at c1 c2 ⊢
  exact ⟨VG.Proof.MlKem.Arm.sepB_symm c1, VG.Proof.MlKem.Arm.sepB_symm c2⟩

theorem cBound : b.iC < L.sizes.length ∧ b.oC + K.ctLen ≤ L.size b.iC := VG.Proof.MlKem.Arm.sepAll_bounds hp.sC

theorem ERow.rowPre {i : Nat} (hi : i < K.k) {s : State} (h : VG.Proof.MlKem.Arm.Enc.ERow K L b s₀ i s) :
    VG.Proof.MlKem.Arm.RowPre K L (VG.Proof.MlKem.Arm.Enc.ρE K L b s₀) (VG.Proof.MlKem.encY (VG.Proof.MlKem.Arm.Enc.rB L s₀)) i (VG.Proof.MlKem.Arm.Enc.okE K L b s₀ i) s :=
  ⟨hp.wf, h.kx.ctx (by decide) hp.ctx, hi, h.r9, h.r11, h.d.rho, fun j hj => by
    have := h.d.v (K.k + j) (by omega)
    have e : ¬ (K.k + j < K.k) := by omega
    simp only [e, ↓reduceIte, show K.k + j - K.k = j by omega] at this
    exact this⟩

section
variable {i : Nat} (hi : i < K.k) {s : State} (h : VG.Proof.MlKem.Arm.Enc.ERow K L b s₀ i s)
include hi h

omit hi in
theorem RB.ctx {f : VG.Spec.MlKem.Poly} {s' : State} (r : VG.Proof.MlKem.Arm.Enc.RB K L b s₀ i s f s') : VG.Proof.MlKem.Arm.Ctx L s' :=
  r.kx.ctx (by decide) (h.kx.ctx (by decide) hp.ctx)

omit hi in
theorem er2_ok {s₁ : State}
    (r : VG.Proof.MlKem.Arm.RowInv K L true (VG.Proof.MlKem.Arm.Enc.ρE K L b s₀) (VG.Proof.MlKem.encY (VG.Proof.MlKem.Arm.Enc.rB L s₀)) i (VG.Proof.MlKem.Arm.Enc.okE K L b s₀ i) s K.k s₁) :
    WP isa (.block [ptrTo .r0 .r7 K.oAcc, ptrTo .r1 .r7 K.oNtt]) s₁ fun s₂ =>
      VG.Proof.MlKem.Arm.Enc.RB K L b s₀ i s (VG.Proof.MlKem.KPke.dotK (fun j => VG.Proof.MlKem.Arm.Enc.aE K L b s₀ j i) (VG.Proof.MlKem.encY (VG.Proof.MlKem.Arm.Enc.rB L s₀)) K.k) s₂ ∧
      s₂.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧ s₂.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 K.oNtt := by
  have hK := hp.wf
  have hc₁ := r.kx.ctx (by decide) (h.kx.ctx (by decide) hp.ctx)
  refine WP.mono (VG.Proof.MlKem.Arm.accArgs_ok hc₁.r7 (by kenc) (by kenc)) fun s₂ ⟨o₂, a0, a1⟩ => ⟨⟨?_, ?_, ?_, ?_⟩, a0, a1⟩
  · exact (r.kx.weaken (by simp)).trans (o₂.x _ _)
  · rw [o₂.cs .r9 (by decide) (by decide), r.kx.cs .r9 (by decide) (by decide) (by decide), h.r9]
  · rw [o₂.cs .r11 (by decide) (by decide), r.r11, VG.Proof.MlKem.Arm.Enc.okE_succ]
  · rw [o₂.mem, ← VG.Proof.MlKem.Arm.rowAcc_eq]; exact r.acc

omit hi in
theorem er3_ok {f : VG.Spec.MlKem.Poly} {s₂ : State} (r : VG.Proof.MlKem.Arm.Enc.RB K L b s₀ i s f s₂) (g0 : s₂.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc)
    (g1 : s₂.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 K.oNtt) : WP isa callNttInv s₂ (VG.Proof.MlKem.Arm.Enc.RB K L b s₀ i s (nttInv f)) := by
  have hK := hp.wf
  have hc := r.ctx hp h
  obtain ⟨-, -, -, -, c5, -, -⟩ := VG.Proof.MlKem.Arm.Enc.row_facts hK
  exact VG.Proof.MlKem.Arm.nttInvL hp.ctx.ok g0 g1 (hc.sep00 (by offs) (by offs) (by offs)) hc.buf0 hc.buf0 r.acc
    fun s₃ k₃ p₃ => ⟨r.kx.trans ((k₃.x _).subL hp.ctx c5), by rw [k₃.cs .r9 (by decide) (by decide), r.r9],
      by rw [k₃.cs .r11 (by decide) (by decide), r.r11], p₃⟩

theorem er4_ok {f : VG.Spec.MlKem.Poly} {s₃ : State} (r : VG.Proof.MlKem.Arm.Enc.RB K L b s₀ i s f s₃) :
    WP isa (.block (ptrTo .r0 .r7 K.oAcc :: slotAt .r1 .r9 (oPoly (2 * K.k)))) s₃ fun s₄ => VG.Proof.MlKem.Arm.Enc.RB K L b s₀ i s f s₄ ∧
      s₄.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧
      s₄.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly (K.k + (K.k + i))) := by
  have hK := hp.wf
  have hc := r.ctx hp h
  refine WP.mono (VG.Proof.MlKem.Arm.ptrSlot_ok (i := i) hc.r7 r.r9 (by kenc) (by kenc)) fun s₄ ⟨o₄, a0, a1⟩ => ?_
  rw [VG.Proof.MlKem.Arm.slot_eq _ (by offs), show oPoly (2 * K.k) + 1024 * i = oPoly (K.k + (K.k + i)) by offs] at a1
  exact ⟨⟨r.kx.trans (o₄.x _ _), by rw [o₄.cs .r9 (by decide) (by decide), r.r9],
    by rw [o₄.cs .r11 (by decide) (by decide), r.r11], by rw [o₄.mem]; exact r.acc⟩, a0, a1⟩

theorem er5_ok {f : VG.Spec.MlKem.Poly} {s₄ : State} (r : VG.Proof.MlKem.Arm.Enc.RB K L b s₀ i s f s₄) (g0 : s₄.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc)
    (g1 : s₄.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly (K.k + (K.k + i)))) :
    WP isa callAdd s₄ (VG.Proof.MlKem.Arm.Enc.RB K L b s₀ i s (add f (VG.Proof.MlKem.cbd (VG.Proof.MlKem.Arm.Enc.rB L s₀) (K.k + i)))) := by
  have hK := hp.wf
  have hc := r.ctx hp h
  obtain ⟨-, -, -, -, -, c6, c7⟩ := VG.Proof.MlKem.Arm.Enc.row_facts hK
  have he : PolyIs s₄.mem (L.A 0 (oPoly (K.k + (K.k + i)))) (VG.Proof.MlKem.cbd (VG.Proof.MlKem.Arm.Enc.rB L s₀) (K.k + i)) :=
    Lay.polyIs_keep hp.ctx.ok r.kx.frame (hc.sepAll0 (by offs) (c7 i hi)) (h.d.e (K.k + i) (by omega) (by omega))
  exact VG.Proof.MlKem.Arm.addL hp.ctx.ok g0 g1 (hc.sep00 (by offs) (by offs) (by offs)) hc.buf0 (VG.Proof.MlKem.Arm.mem_rd_wr hc.buf0) r.acc he
    fun s₅ k₅ p₅ => ⟨r.kx.trans ((k₅.x _).subL hp.ctx c6), by rw [k₅.cs .r9 (by decide) (by decide), r.r9],
      by rw [k₅.cs .r11 (by decide) (by decide), r.r11], p₅⟩

omit hp hi h in
theorem cArgs_ok (hK : K.WF) {s : State} {P C : BitVec 32} {i : Nat} (h7 : s.gpr .r7 = P) (h8 : s.gpr .r8 = C)
    (h9 : s.gpr .r9 = BitVec.ofNat 32 i) :
    WP isa (.block (([ptrTo .r0 .r7 K.oAcc, .mov .r1 (.imm (BitVec.ofNat 32 K.du))] : List Instr) ++
      K.atU .r2 .r8 .r9 ++ ([.mov .r3 (.imm (BitVec.ofNat 32 K.uLen))] : List Instr))) s
      fun s' => VG.Proof.MlKem.Arm.Only s s' ∧ s'.gpr .r0 = P + BitVec.ofNat 32 K.oAcc ∧ s'.gpr .r1 = BitVec.ofNat 32 K.du ∧
        s'.gpr .r2 = C + BitVec.ofNat 32 i * BitVec.ofNat 32 K.uLen ∧ s'.gpr .r3 = BitVec.ofNat 32 (32 * K.du) := by
  have e1 : encodable (BitVec.ofNat 32 K.oAcc) = true := hK.enc (by omega)
  have e2 := hK.encDu
  have e3 := hK.encU
  rw [WP.block_append_iff, WP.block_append_iff]
  have hb : WP isa (.block [ptrTo .r0 .r7 K.oAcc, .mov .r1 (.imm (BitVec.ofNat 32 K.du))]) s fun s₁ =>
      s₁.gpr .r0 = P + BitVec.ofNat 32 K.oAcc ∧ s₁.gpr .r1 = BitVec.ofNat 32 K.du ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
      s₁.sp = s.sp := by
    run_block [ptrTo, e1, e2, h7]
    exact ⟨trivial, trivial, fun r h0 h1 => by rw [ite_eq_right h1, ite_eq_right h0], trivial⟩
  refine WP.mono hb fun s₁ ⟨a0, a1, o₁, m₁, rd₁, wr₁, sp₁⟩ => WP.mono (VG.Proof.MlKem.Arm.atU_ok hK (d := .r2) (by decide) s₁)
    fun s₂ ⟨a2, o₂, m₂, rd₂, wr₂, sp₂⟩ => ?_
  run_block [e3]
  refine ⟨⟨fun r hr hl => ?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁]⟩,
    by rw [o₂ .r0 (by decide), a0], by rw [o₂ .r1 (by decide), a1], ?_, trivial⟩
  · obtain ⟨m0, m1, m2, m3, -⟩ := VG.Proof.MlKem.Arm.pres_ne hr hl
    show (if r = .r3 then _ else s₂.gpr r) = s.gpr r
    rw [ite_eq_right m3, o₂ r m2, o₁ r m0 m1]
  · rw [a2, o₁ .r8 (by decide) (by decide), h8, o₁ .r9 (by decide) (by decide), h9]

omit hi in
theorem er6_ok {f : VG.Spec.MlKem.Poly} {s₅ : State} (r : VG.Proof.MlKem.Arm.Enc.RB K L b s₀ i s f s₅) :
    WP isa (.block (([ptrTo .r0 .r7 K.oAcc, .mov .r1 (.imm (BitVec.ofNat 32 K.du))] : List Instr) ++
      K.atU .r2 .r8 .r9 ++ ([.mov .r3 (.imm (BitVec.ofNat 32 K.uLen))] : List Instr))) s₅
      fun s₆ => VG.Proof.MlKem.Arm.Enc.RB K L b s₀ i s f s₆ ∧ s₆.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧
        s₆.gpr .r1 = BitVec.ofNat 32 K.du ∧ s₆.gpr .r2 = L.ptr b.iC + BitVec.ofNat 32 (b.oC + K.uLen * i) ∧
        s₆.gpr .r3 = BitVec.ofNat 32 (32 * K.du) := by
  have hc := r.ctx hp h
  have g8 : s₅.gpr .r8 = L.ptr b.iC + BitVec.ofNat 32 b.oC := by
    rw [r.kx.cs .r8 (by decide) (by decide) (by decide), h.kx.cs .r8 (by decide) (by decide) (by decide), hp.r8]
  refine WP.mono (VG.Proof.MlKem.Arm.Enc.cArgs_ok hp.wf hc.r7 g8 r.r9) fun s₆ ⟨o₆, a0, a1, a2, a3⟩ => ?_
  rw [VG.Proof.MlKem.Arm.atU_eq, ptr_add_add32] at a2
  exact ⟨⟨r.kx.trans (o₆.x _ _), by rw [o₆.cs .r9 (by decide) (by decide), r.r9],
    by rw [o₆.cs .r11 (by decide) (by decide), r.r11], by rw [o₆.mem]; exact r.acc⟩, a0, a1, a2, a3⟩

theorem er7_ok {s₆ : State} (r : VG.Proof.MlKem.Arm.Enc.RB K L b s₀ i s (VG.Proof.MlKem.KPke.encU K.p (VG.Proof.MlKem.Arm.Enc.aE K L b s₀) (VG.Proof.MlKem.Arm.Enc.rB L s₀) i) s₆)
    (g0 : s₆.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc) (g1 : s₆.gpr .r1 = BitVec.ofNat 32 K.du)
    (g2 : s₆.gpr .r2 = L.ptr b.iC + BitVec.ofNat 32 (b.oC + K.uLen * i)) (g3 : s₆.gpr .r3 = BitVec.ofNat 32 (32 * K.du)) :
    WP isa K.callCU s₆ (VG.Proof.MlKem.Arm.Enc.RC K L b s₀ i s) := by
  have hK := hp.wf
  have hc := r.ctx hp h
  have hs : VG.Proof.MlKem.Arm.sepB L.sizes (0, K.oAcc, 1024) (b.iC, b.oC + K.uLen * i, 32 * K.du) = true := by
    have := VG.Proof.MlKem.Arm.Enc.cSep hp (k := K.uLen * i) (n := K.uLen) (VG.Proof.MlKem.Arm.Enc.uSlot hi) (W := [(0, K.oAcc, 1024)]) (by kdecide)
    simp only [VG.Proof.MlKem.Arm.sepAll, List.all_cons, List.all_nil, Bool.and_true] at this
    exact VG.Proof.MlKem.Arm.sepB_symm this
  exact hp.calls.cu hp.ctx.ok g0 g1 g2 g3 (.inl rfl) hs (VG.Proof.MlKem.Arm.mem_rd_wr hc.buf0)
    (by rw [r.kx.wr, h.kx.wr]; exact hp.wC) r.acc fun s₇ k₇ p₇ =>
    ⟨(r.kx.monoL (by simp)).trans ((k₇.x _).monoL (by simp)), by rw [k₇.cs .r9 (by decide) (by decide), r.r9],
      by rw [k₇.cs .r11 (by decide) (by decide), r.r11], p₇⟩

theorem er8_ok {s₇ : State} (r : VG.Proof.MlKem.Arm.Enc.RC K L b s₀ i s s₇) :
    WP isa (.block (count .r9 K.k)) s₇ fun s' => VG.Proof.MlKem.Arm.Enc.ERow K L b s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = K.k) := by
  have hL := hp.ctx.ok
  have hK := hp.wf
  have k4 := hK.k4
  obtain ⟨r1, r2, r3, r4, -, -, -⟩ := VG.Proof.MlKem.Arm.Enc.row_facts hK
  obtain ⟨cb1, cb2⟩ := VG.Proof.MlKem.Arm.Enc.cBound hp
  refine WP.mono (VG.Proof.MlKem.Arm.count_ok (by omega) (by omega) (by kenc) r.r9) fun s' ⟨k', g', z'⟩ => ⟨⟨?_, g', ?_, ?_, ?_⟩, z'⟩
  all_goals have K' : VG.Proof.MlKem.Arm.KeptX [.r9, .r10, .r11] (L.RL (VG.Proof.MlKem.Arm.rowW K ++ [(b.iC, b.oC + K.uLen * i, K.uLen)])) s s' :=
    r.kx.trans ((k'.weaken (by simp)).mono (fun _ h => absurd h List.not_mem_nil))
  · refine h.kx.trans ?_
    have e : ∀ w ∈ L.RL (VG.Proof.MlKem.Arm.rowW K ++ [(b.iC, b.oC + K.uLen * i, K.uLen)]), ∃ w' ∈ L.RL (VG.Proof.MlKem.Arm.Enc.encW K b), Region.Sub w w' := by
      intro w hw
      simp only [Lay.RL, List.map_append, List.mem_append] at hw
      rcases hw with hw | hw
      · obtain ⟨w', hw', hs⟩ := hp.ctx.subL r1 w hw
        exact ⟨w', by simp only [Lay.RL, List.map_append, List.mem_append]; exact .inl hw', hs⟩
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hw; subst hw
        have := VG.Proof.MlKem.Arm.Enc.uSlot (K := K) hi
        exact ⟨L.R b.iC b.oC K.ctLen, by simp, Lay.R_sub_R hL cb1 (by omega) (by omega) cb2⟩
    exact K'.sub e
  · rw [k'.cs .r11 (by decide) (by decide) (by decide), r.r11]
  · obtain ⟨d1, d2⟩ := VG.Proof.MlKem.Arm.Enc.cData hp (k := K.uLen * i) (n := K.uLen) (VG.Proof.MlKem.Arm.Enc.uSlot hi)
    exact h.d.keep hL K'.frame (VG.Proof.MlKem.Arm.sepAll_append (hp.ctx.sepAll0 (by decide) r3) d1)
      (VG.Proof.MlKem.Arm.sepAll_append (hp.ctx.sepAll0 (by offs) r4) d2)
  · intro i' hi'
    by_cases e : i' = i
    · subst e
      exact (bytesAt_frame k'.frame (fun _ h => absurd h List.not_mem_nil) (by offs)).trans r.cb
    · have u1 := VG.Proof.MlKem.Arm.Enc.uSlot (K := K) (i := i') (by omega)
      have u2 := VG.Proof.MlKem.Arm.Enc.uSlot (K := K) hi
      have s1 : VG.Proof.MlKem.Arm.sepAll L.sizes (b.iC, b.oC + K.uLen * i', K.uLen) (VG.Proof.MlKem.Arm.rowW K) = true := VG.Proof.MlKem.Arm.Enc.cSep hp (by omega) r2
      have s2 : VG.Proof.MlKem.Arm.sepAll L.sizes (b.iC, b.oC + K.uLen * i', K.uLen) [(b.iC, b.oC + K.uLen * i, K.uLen)] = true := by
        simp only [VG.Proof.MlKem.Arm.sepAll, List.all_cons, List.all_nil, Bool.and_true]
        exact VG.Proof.MlKem.Arm.Enc.sepB_same cb1 (by simp only [Lay.size] at cb2; omega) (by simp only [Lay.size] at cb2; omega)
          (by have := VG.Proof.MlKem.Arm.Enc.uApart (K := K) e; omega)
      rw [← h.c i' (by omega)]
      exact Lay.bytes_keep hL K'.frame (VG.Proof.MlKem.Arm.sepAll_append s1 s2) (by offs)

end

theorem encRow_step {i : Nat} (hi : i < K.k) {s : State} (h : VG.Proof.MlKem.Arm.Enc.ERow K L b s₀ i s) :
    WP isa K.encRowBody s fun s' => VG.Proof.MlKem.Arm.Enc.ERow K L b s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = K.k) :=
  WP.seq (WP.mono (VG.Proof.MlKem.Arm.rowSum_ok (transpose := true) (h.rowPre hp hi)) fun _ r₁ =>
    WP.seq (WP.mono (VG.Proof.MlKem.Arm.Enc.er2_ok hp h r₁) fun _ ⟨r₂, a0, a1⟩ =>
    WP.seq (WP.mono (VG.Proof.MlKem.Arm.Enc.er3_ok hp h r₂ a0 a1) fun _ r₃ =>
    WP.seq (WP.mono (VG.Proof.MlKem.Arm.Enc.er4_ok hp hi h r₃) fun _ ⟨r₄, b0, b1⟩ =>
    WP.seq (WP.mono (VG.Proof.MlKem.Arm.Enc.er5_ok hp hi h r₄ b0 b1) fun _ r₅ =>
    WP.seq (WP.mono (VG.Proof.MlKem.Arm.Enc.er6_ok hp h r₅) fun _ ⟨r₆, c0, c1, c2, c3⟩ =>
    WP.seq (WP.mono (VG.Proof.MlKem.Arm.Enc.er7_ok hp hi h r₆ c0 c1 c2 c3) fun _ r₇ => VG.Proof.MlKem.Arm.Enc.er8_ok hp hi h r₇)))))))

end

/-! ## `v` -/

/-- What the steps of `v` keep: what the rows left. -/
structure VEnv (K : KemLay) (L : VG.Proof.MlKem.Arm.Lay) (b : VG.Proof.MlKem.Arm.Enc.EB) (s₀ s : State) : Prop where
  kx : VG.Proof.MlKem.Arm.KeptX [.r9, .r10, .r11] (L.RL (VG.Proof.MlKem.Arm.Enc.encW K b)) s₀ s
  r11 : s.gpr .r11 = if VG.Proof.MlKem.Arm.Enc.okE K L b s₀ K.k then 1 else 0
  d : VG.Proof.MlKem.Arm.Enc.EData K L b s₀ s
  c : ∀ i' < K.k, bytesAt s.mem (L.A b.iC (b.oC + K.uLen * i')) K.uLen =
    compressEncode K.du (VG.Proof.MlKem.KPke.encU K.p (VG.Proof.MlKem.Arm.Enc.aE K L b s₀) (VG.Proof.MlKem.Arm.Enc.rB L s₀) i')

/-- A region of `scratch` the steps of `v` may change. -/
def vOK (K : KemLay) (w : Nat × Nat × Nat) : Bool :=
  (VG.Proof.MlKem.Arm.Enc.encW0 K).any (VG.Proof.MlKem.Arm.subB0 w) && (VG.Proof.MlKem.Arm.Enc.encW0 K).any (VG.Proof.MlKem.Arm.inB w) && VG.Proof.MlKem.Arm.sep0 1216 32 w && VG.Proof.MlKem.Arm.sep0 2048 (1024 * (3 * K.k + 2)) w

/-- What `v` writes keeps `VEnv`. -/
abbrev VOKFacts (K : KemLay) : Prop := (VG.Proof.MlKem.Arm.dotW K).all (VG.Proof.MlKem.Arm.Enc.vOK K) = true ∧
    [((0 : Nat), K.oAcc, (1024 : Nat)), (0, K.oNtt, 1024)].all (VG.Proof.MlKem.Arm.Enc.vOK K) = true ∧
    [((0 : Nat), K.oAcc, (1024 : Nat))].all (VG.Proof.MlKem.Arm.Enc.vOK K) = true

theorem vOK_facts {K : KemLay} (hK : K.WF) : VG.Proof.MlKem.Arm.Enc.VOKFacts K := (by decide : ∀ k < 5, VOKFacts (kOf k)) K.k (by have := hK.k4; omega)

section
variable {K : KemLay} {L : VG.Proof.MlKem.Arm.Lay} {b : VG.Proof.MlKem.Arm.Enc.EB} {s₀ : State} (hp : VG.Proof.MlKem.Arm.Enc.EncPre K L b s₀)
include hp

theorem VEnv.keep {s s' : State} (h : VG.Proof.MlKem.Arm.Enc.VEnv K L b s₀ s) {xs : List Reg} {W : List (Nat × Nat × Nat)}
    (k : VG.Proof.MlKem.Arm.KeptX xs (L.RL W) s s') (hx : ∀ x ∈ xs, x ∈ [Reg.r9, .r10]) (hW : W.all (VG.Proof.MlKem.Arm.Enc.vOK K) = true) : VG.Proof.MlKem.Arm.Enc.VEnv K L b s₀ s' := by
  have hL := hp.ctx.ok
  have hK := hp.wf
  have hc := h.kx.ctx (by decide) hp.ctx
  have w1 : W.all (fun w => (VG.Proof.MlKem.Arm.Enc.encW0 K).any (VG.Proof.MlKem.Arm.subB0 w)) = true := List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp hW w hw; simp only [VG.Proof.MlKem.Arm.Enc.vOK, Bool.and_eq_true] at this; exact this.1.1.1
  have w2 : W.all (fun w => (VG.Proof.MlKem.Arm.Enc.encW0 K).any (VG.Proof.MlKem.Arm.inB w)) = true := List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp hW w hw; simp only [VG.Proof.MlKem.Arm.Enc.vOK, Bool.and_eq_true] at this; exact this.1.1.2
  have w3 : W.all (VG.Proof.MlKem.Arm.sep0 1216 32) = true := List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp hW w hw; simp only [VG.Proof.MlKem.Arm.Enc.vOK, Bool.and_eq_true] at this; exact this.1.2
  have w4 : W.all (VG.Proof.MlKem.Arm.sep0 2048 (1024 * (3 * K.k + 2))) = true := List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp hW w hw; simp only [VG.Proof.MlKem.Arm.Enc.vOK, Bool.and_eq_true] at this; exact this.2
  refine ⟨h.kx.trans ?_, ?_, h.d.keep hL k.frame (hc.sepAll0 (by decide) w3) (hc.sepAll0 (by offs) w4),
    fun i' hi' => (Lay.bytes_keep hL k.frame (VG.Proof.MlKem.Arm.Enc.cSep hp (VG.Proof.MlKem.Arm.Enc.uSlot hi') w2) (by simp only [KemLay.uLen]; have := hK.du; omega)).trans
      (h.c i' hi')⟩
  · refine ((k.weaken fun x hx' => ?_).subL hp.ctx w1).monoL fun w hw => List.mem_append_left _ hw
    have := hx x hx'; simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
    rcases this with rfl | rfl <;> simp
  · rw [k.cs .r11 (by decide) (by decide) (fun hm => by have := hx _ hm; simp at this), h.r11]

omit hp in
theorem ERow.venv {s : State} (h : VG.Proof.MlKem.Arm.Enc.ERow K L b s₀ K.k s) : VG.Proof.MlKem.Arm.Enc.VEnv K L b s₀ s := ⟨h.kx, h.r11, h.d, h.c⟩

theorem ev1_ok {s : State} (h : VG.Proof.MlKem.Arm.Enc.VEnv K L b s₀ s) :
    WP isa K.dot s fun s' => VG.Proof.MlKem.Arm.Enc.VEnv K L b s₀ s' ∧ PolyIs s'.mem (L.A 0 K.oAcc)
      (VG.Proof.MlKem.KPke.dotK (VG.Proof.MlKem.ekT (VG.Proof.MlKem.Arm.Enc.ekB K L b s₀)) (VG.Proof.MlKem.encY (VG.Proof.MlKem.Arm.Enc.rB L s₀)) K.k) := by
  have hK := hp.wf
  have hc := h.kx.ctx (by decide) hp.ctx
  refine WP.mono (VG.Proof.MlKem.Arm.dot_ok hK hc (fun j hj => ?_) (fun j hj => ?_)) fun s' ⟨k, p⟩ =>
    ⟨h.keep hp k (by simp) (VG.Proof.MlKem.Arm.Enc.vOK_facts hK).1, p⟩
  · have := h.d.v j (by omega); simp only [hj, ↓reduceIte] at this; exact this
  · have := h.d.v (K.k + j) (by omega)
    have e : ¬ (K.k + j < K.k) := by omega
    simp only [e, ↓reduceIte, show K.k + j - K.k = j by omega] at this
    exact this

theorem evArgs_ok {s : State} {f : VG.Spec.MlKem.Poly} (h : VG.Proof.MlKem.Arm.Enc.VEnv K L b s₀ s) (hf : PolyIs s.mem (L.A 0 K.oAcc) f) {o : Nat}
    (he : encodable (BitVec.ofNat 32 o) = true) :
    WP isa (.block [ptrTo .r0 .r7 K.oAcc, ptrTo .r1 .r7 o]) s fun s' => (VG.Proof.MlKem.Arm.Enc.VEnv K L b s₀ s' ∧ PolyIs s'.mem (L.A 0 K.oAcc) f) ∧
      s'.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧ s'.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 o := by
  have hK := hp.wf
  have hc := h.kx.ctx (by decide) hp.ctx
  exact WP.mono (VG.Proof.MlKem.Arm.accArgs_ok hc.r7 (by kenc) he) fun s' ⟨o', a0, a1⟩ =>
    ⟨⟨h.keep hp (xs := []) (W := []) (o'.x _ _) (fun _ h => absurd h List.not_mem_nil) rfl, by rw [o'.mem]; exact hf⟩, a0, a1⟩

theorem ev3_ok {s : State} {f : VG.Spec.MlKem.Poly} (h : VG.Proof.MlKem.Arm.Enc.VEnv K L b s₀ s ∧ PolyIs s.mem (L.A 0 K.oAcc) f)
    (g0 : s.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc) (g1 : s.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 K.oNtt) :
    WP isa callNttInv s fun s' => VG.Proof.MlKem.Arm.Enc.VEnv K L b s₀ s' ∧ PolyIs s'.mem (L.A 0 K.oAcc) (nttInv f) := by
  have hK := hp.wf
  have hc := h.1.kx.ctx (by decide) hp.ctx
  exact VG.Proof.MlKem.Arm.nttInvL hp.ctx.ok g0 g1 (hc.sep00 (by offs) (by offs) (by offs)) hc.buf0 hc.buf0 h.2
    fun s' k p => ⟨h.1.keep hp (k.x []) (by simp) (VG.Proof.MlKem.Arm.Enc.vOK_facts hK).2.1, p⟩

theorem evAdd_ok {s : State} {f g : VG.Spec.MlKem.Poly} {k : Nat} (hk : k = 3 * K.k ∨ k = 3 * K.k + 1)
    (h : VG.Proof.MlKem.Arm.Enc.VEnv K L b s₀ s ∧ PolyIs s.mem (L.A 0 K.oAcc) f) (hg : PolyIs s.mem (L.A 0 (oPoly k)) g)
    (g0 : s.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc) (g1 : s.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly k)) :
    WP isa callAdd s fun s' => VG.Proof.MlKem.Arm.Enc.VEnv K L b s₀ s' ∧ PolyIs s'.mem (L.A 0 K.oAcc) (add f g) := by
  have hK := hp.wf
  have hc := h.1.kx.ctx (by decide) hp.ctx
  exact VG.Proof.MlKem.Arm.addL hp.ctx.ok g0 g1 (hc.sep00 (by offs) (by rcases hk with rfl | rfl <;> offs)
    (by rcases hk with rfl | rfl <;> offs)) hc.buf0 (VG.Proof.MlKem.Arm.mem_rd_wr hc.buf0) h.2 hg
    fun s' k p => ⟨h.1.keep hp (k.x []) (by simp) (VG.Proof.MlKem.Arm.Enc.vOK_facts hK).2.2, p⟩

omit hp in
theorem vArgs_ok (hK : K.WF) {s : State} {P C : BitVec 32} (h7 : s.gpr .r7 = P) (h8 : s.gpr .r8 = C) :
    WP isa (.block [ptrTo .r0 .r7 K.oAcc, .mov .r1 (.imm (BitVec.ofNat 32 K.dv)), ptrTo .r2 .r8 (K.uLen * K.k),
      .mov .r3 (.imm (BitVec.ofNat 32 K.vLen))]) s
      fun s' => VG.Proof.MlKem.Arm.Only s s' ∧ s'.gpr .r0 = P + BitVec.ofNat 32 K.oAcc ∧ s'.gpr .r1 = BitVec.ofNat 32 K.dv ∧
        s'.gpr .r2 = C + BitVec.ofNat 32 (K.uLen * K.k) ∧ s'.gpr .r3 = BitVec.ofNat 32 (32 * K.dv) := by
  have e1 : encodable (BitVec.ofNat 32 K.oAcc) = true := hK.enc (by omega)
  have e2 := hK.encDv
  have e3 := hK.encVo
  have e4 := hK.encV
  run_block [ptrTo, e1, e2, e3, e4, h7, h8]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, m2, m3, -⟩ := VG.Proof.MlKem.Arm.pres_ne hr hl
  simp only [m0, m1, m2, m3, ite_false]

theorem ev8_ok {s : State} {f : VG.Spec.MlKem.Poly} (h : VG.Proof.MlKem.Arm.Enc.VEnv K L b s₀ s ∧ PolyIs s.mem (L.A 0 K.oAcc) f) :
    WP isa (.block [ptrTo .r0 .r7 K.oAcc, .mov .r1 (.imm (BitVec.ofNat 32 K.dv)), ptrTo .r2 .r8 (K.uLen * K.k),
      .mov .r3 (.imm (BitVec.ofNat 32 K.vLen))]) s
      fun s' => (VG.Proof.MlKem.Arm.Enc.VEnv K L b s₀ s' ∧ PolyIs s'.mem (L.A 0 K.oAcc) f) ∧ s'.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧
        s'.gpr .r1 = BitVec.ofNat 32 K.dv ∧ s'.gpr .r2 = L.ptr b.iC + BitVec.ofNat 32 (b.oC + K.uLen * K.k) ∧
        s'.gpr .r3 = BitVec.ofNat 32 (32 * K.dv) := by
  have hc := h.1.kx.ctx (by decide) hp.ctx
  have g8 : s.gpr .r8 = L.ptr b.iC + BitVec.ofNat 32 b.oC := by
    rw [h.1.kx.cs .r8 (by decide) (by decide) (by decide), hp.r8]
  exact WP.mono (VG.Proof.MlKem.Arm.Enc.vArgs_ok hp.wf hc.r7 g8) fun s' ⟨o', a0, a1, a2, a3⟩ =>
    ⟨⟨h.1.keep hp (xs := []) (W := []) (o'.x _ _) (fun _ h => absurd h List.not_mem_nil) rfl, by rw [o'.mem]; exact h.2⟩, a0, a1,
      by rw [a2, ptr_add_add32], a3⟩

omit hp in
/-- `c * k` bytes as `k` pieces of `c`. -/
theorem bytes_catK (m : Mem) (p : Addr) (c : Nat) :
    ∀ k, bytesAt m p (c * k) = VG.Proof.MlKem.KPke.catK (fun i => bytesAt m (p + BitVec.ofNat 64 (c * i)) c) k
  | 0 => rfl
  | k + 1 => by
    rw [Nat.mul_succ, bytesAt_add, VG.Proof.MlKem.Arm.Enc.bytes_catK m p c k]
    exact (VG.Proof.MlKem.KPke.foldK_succ List.nil_append _ k).symm

omit hp in
theorem catK_congr {f g : Nat → List Byte} : ∀ {k}, (∀ i < k, f i = g i) →
    VG.Proof.MlKem.KPke.catK f k = VG.Proof.MlKem.KPke.catK g k
  | 0, _ => rfl
  | k + 1, h => by
    show VG.Proof.MlKem.KPke.foldK (· ++ ·) [] f (k + 1) = VG.Proof.MlKem.KPke.foldK (· ++ ·) [] g (k + 1)
    rw [VG.Proof.MlKem.KPke.foldK_succ List.nil_append, VG.Proof.MlKem.KPke.foldK_succ List.nil_append]
    exact congrArg₂ (· ++ ·) (VG.Proof.MlKem.Arm.Enc.catK_congr fun i hi => h i (by omega)) (h k (by omega))

theorem ev9_ok {s : State} (h : VG.Proof.MlKem.Arm.Enc.VEnv K L b s₀ s ∧ PolyIs s.mem (L.A 0 K.oAcc)
      (VG.Proof.MlKem.KPke.encV K.p (VG.Proof.MlKem.Arm.Enc.ekB K L b s₀) (VG.Proof.MlKem.Arm.Enc.mB L b s₀) (VG.Proof.MlKem.Arm.Enc.rB L s₀)))
    (g0 : s.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc) (g1 : s.gpr .r1 = BitVec.ofNat 32 K.dv)
    (g2 : s.gpr .r2 = L.ptr b.iC + BitVec.ofNat 32 (b.oC + K.uLen * K.k)) (g3 : s.gpr .r3 = BitVec.ofNat 32 (32 * K.dv)) :
    WP isa K.callCU s fun s' => VG.Proof.MlKem.Arm.KeptX [.r9, .r10, .r11] (L.RL (VG.Proof.MlKem.Arm.Enc.encW K b)) s₀ s' ∧
      s'.gpr .r11 = (if VG.Proof.MlKem.Arm.Enc.okE K L b s₀ K.k then 1 else 0) ∧
      bytesAt s'.mem (L.A b.iC b.oC) K.ctLen =
        VG.Proof.MlKem.KPke.ct K.p (VG.Proof.MlKem.Arm.Enc.aE K L b s₀) (VG.Proof.MlKem.Arm.Enc.ekB K L b s₀) (VG.Proof.MlKem.Arm.Enc.mB L b s₀) (VG.Proof.MlKem.Arm.Enc.rB L s₀) := by
  have hL := hp.ctx.ok
  have hK := hp.wf
  have hc := h.1.kx.ctx (by decide) hp.ctx
  obtain ⟨cb1, cb2⟩ := VG.Proof.MlKem.Arm.Enc.cBound hp
  have hs : VG.Proof.MlKem.Arm.sepB L.sizes (0, K.oAcc, 1024) (b.iC, b.oC + K.uLen * K.k, 32 * K.dv) = true := by
    have := VG.Proof.MlKem.Arm.Enc.cSep hp (k := K.uLen * K.k) (n := K.vLen) (by simp only [KemLay.ctLen]; omega) (W := [(0, K.oAcc, 1024)])
      (by kdecide)
    simp only [VG.Proof.MlKem.Arm.sepAll, List.all_cons, List.all_nil, Bool.and_true] at this
    exact VG.Proof.MlKem.Arm.sepB_symm this
  have ect : K.ctLen = K.uLen * K.k + 32 * K.dv := rfl
  have eu : K.uLen = 32 * K.du := rfl
  have du := hK.du
  simp only [Lay.size] at cb2
  refine hp.calls.cu hL g0 g1 g2 g3 (.inr rfl) hs (VG.Proof.MlKem.Arm.mem_rd_wr hc.buf0)
    (by rw [h.1.kx.wr]; exact hp.wC) h.2 fun s' k p => ⟨?_, ?_, ?_⟩
  · refine h.1.kx.trans ((k.x _).sub fun r hr => ?_)
    simp only [Lay.RL, List.map_cons, List.map_nil, List.mem_singleton] at hr; subst hr
    exact ⟨L.R b.iC b.oC K.ctLen, by simp, Lay.R_sub_R hL cb1 (by omega) (by omega) cb2⟩
  · rw [k.cs .r11 (by decide) (by decide), h.1.r11]
  · have keep : ∀ i' < K.k, bytesAt s'.mem (L.A b.iC (b.oC + K.uLen * i')) K.uLen =
        compressEncode K.du (VG.Proof.MlKem.KPke.encU K.p (VG.Proof.MlKem.Arm.Enc.aE K L b s₀) (VG.Proof.MlKem.Arm.Enc.rB L s₀) i') := fun i' hi' => by
      have u1 := VG.Proof.MlKem.Arm.Enc.uSlot (K := K) hi'
      have u2 : K.uLen * i' + K.uLen ≤ K.uLen * K.k := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi'
      rw [← h.1.c i' hi']
      refine Lay.bytes_keep hL k.frame ?_ (by omega)
      simp only [VG.Proof.MlKem.Arm.sepAll, List.all_cons, List.all_nil, Bool.and_true]
      exact VG.Proof.MlKem.Arm.Enc.sepB_same cb1 (by omega) (by omega) (by omega)
    simp only [Lay.A] at keep p ⊢
    rw [KemLay.ctLen, bytesAt_add, VG.Proof.MlKem.Arm.Enc.bytes_catK, add_ofNat_add, VG.Proof.MlKem.KPke.ct]
    refine congrArg₂ (· ++ ·) (VG.Proof.MlKem.Arm.Enc.catK_congr fun i hi => ?_) p
    rw [add_ofNat_add]; exact keep i hi

end

/-! ## The whole of K-PKE.Encrypt -/

/-- `μ` apart from the polynomials of the `PRF`s. -/
abbrev MuSep (K : KemLay) : Prop :=
  (∀ k < 2 * K.k, [((0 : Nat), oPoly (3 * K.k + 1), (1024 : Nat))].all (VG.Proof.MlKem.Arm.sep0 (oPoly k) 1024) = true) ∧
    (∀ N < 2 * K.k + 1, [((0 : Nat), oPoly (3 * K.k + 1), (1024 : Nat))].all (VG.Proof.MlKem.Arm.sep0 (oPoly (K.k + N)) 1024) = true)

theorem mu_sep {K : KemLay} (hK : K.WF) : VG.Proof.MlKem.Arm.Enc.MuSep K := (by decide : ∀ k < 5, MuSep (kOf k)) K.k (by have := hK.k4; omega)

section
variable {K : KemLay} {L : VG.Proof.MlKem.Arm.Lay} {b : VG.Proof.MlKem.Arm.Enc.EB} {s₀ : State} (hp : VG.Proof.MlKem.Arm.Enc.EncPre K L b s₀)
include hp

theorem dec_pre {s₁ : State} (e₁ : VG.Proof.MlKem.Arm.Enc.EA K L s₀ s₁) :
    VG.Proof.MlKem.Arm.Ctx L s₁ ∧ s₁.gpr .r4 = L.ptr b.iE + BitVec.ofNat 32 b.oE ∧
      VG.Proof.MlKem.Arm.sepAll L.sizes (b.iE, b.oE, 384 * K.k) [(0, 2048, 1024 * K.k)] = true ∧ L.buf b.iE ∈ s₁.rd ++ s₁.wr := by
  have hK := hp.wf
  exact ⟨EA.ctx hp e₁, by rw [EA.reg e₁ (by simp), hp.r4], VG.Proof.MlKem.Arm.sepAll_mono hp.sE (by simp [VG.Proof.MlKem.Arm.inB]) (by kdecide),
    by rw [e₁.rd, e₁.wr]; exact hp.wE⟩

omit hp in
theorem v_of {s₃ : State} (t₃ : ∀ k < K.k, PolyIs s₃.mem (L.A 0 (oPoly k)) (VG.Proof.MlKem.ekT (VG.Proof.MlKem.Arm.Enc.ekB K L b s₀) k))
    (y₃ : ∀ j < K.k, PolyIs s₃.mem (L.A 0 (oPoly (K.k + j))) (VG.Proof.MlKem.encY (VG.Proof.MlKem.Arm.Enc.rB L s₀) j)) :
    ∀ k < 2 * K.k, PolyIs s₃.mem (L.A 0 (oPoly k)) (if k < K.k then VG.Proof.MlKem.ekT (VG.Proof.MlKem.Arm.Enc.ekB K L b s₀) k
      else VG.Proof.MlKem.encY (VG.Proof.MlKem.Arm.Enc.rB L s₀) (k - K.k)) := fun k hk => by
  by_cases e : k < K.k
  · simp only [e, ↓reduceIte]; exact t₃ k e
  · simp only [e, ↓reduceIte]
    have := y₃ (k - K.k) (by omega)
    rwa [show K.k + (k - K.k) = k by omega] at this

theorem rows_init {s₅ : State} (e₅ : VG.Proof.MlKem.Arm.Enc.EA K L s₀ s₅) (d₅ : VG.Proof.MlKem.Arm.Enc.EData K L b s₀ s₅) :
    WP isa (.block [.mov .r11 (.imm 1), .mov .r9 (.imm 0)]) s₅ (VG.Proof.MlKem.Arm.Enc.ERow K L b s₀ 0) :=
  WP.mono VG.Proof.MlKem.Arm.flagInit_ok fun _ ⟨k, g11, g9, m⟩ =>
    ⟨(e₅.monoL fun w hw => List.mem_append_left _ hw).trans ((k.weaken (by simp)).mono
      (fun _ h => absurd h List.not_mem_nil)), g9, by rw [g11]; rfl,
      d₅.keep hp.ctx.ok (W := []) (by rw [m]; exact Frame.refl _ _) rfl rfl,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem data5 {s₄ s₅ : State} (ρ₄ : bytesAt s₄.mem (L.A 0 oSeed) 32 = VG.Proof.MlKem.Arm.Enc.ρE K L b s₀)
    (v₄ : ∀ k < 2 * K.k, PolyIs s₄.mem (L.A 0 (oPoly k)) (if k < K.k then VG.Proof.MlKem.ekT (VG.Proof.MlKem.Arm.Enc.ekB K L b s₀) k
      else VG.Proof.MlKem.encY (VG.Proof.MlKem.Arm.Enc.rB L s₀) (k - K.k)))
    (E₄ : ∀ N, K.k ≤ N → N < 2 * K.k + 1 → PolyIs s₄.mem (L.A 0 (oPoly (K.k + N))) (VG.Proof.MlKem.cbd (VG.Proof.MlKem.Arm.Enc.rB L s₀) N))
    (f₅ : Frame (L.RL [(0, oPoly (3 * K.k + 1), 1024)]) s₄.mem s₅.mem)
    (μ₅ : PolyIs s₅.mem (L.A 0 (oPoly (3 * K.k + 1))) (decodeDecompress 1 (VG.Proof.MlKem.Arm.Enc.mB L b s₀))) : VG.Proof.MlKem.Arm.Enc.EData K L b s₀ s₅ := by
  have hL := hp.ctx.ok
  have hK := hp.wf
  exact ⟨(Lay.bytes_keep hL f₅ (hp.ctx.sepAll0 (by decide) (by kdecide)) (by decide)).trans ρ₄,
    fun k hk => Lay.polyIs_keep hL f₅ (hp.ctx.sepAll0 (by offs) ((VG.Proof.MlKem.Arm.Enc.mu_sep hK).1 k hk)) (v₄ k hk),
    fun N h3 h7 => Lay.polyIs_keep hL f₅ (hp.ctx.sepAll0 (by offs) ((VG.Proof.MlKem.Arm.Enc.mu_sep hK).2 N h7)) (E₄ N h3 h7), μ₅⟩

theorem encrypt_ok : WP isa K.encrypt s₀ fun s => VG.Proof.MlKem.Arm.KeptX [.r9, .r10, .r11] (L.RL (VG.Proof.MlKem.Arm.Enc.encW K b)) s₀ s ∧
    s.gpr .r11 = (if VG.Proof.MlKem.Arm.Enc.okE K L b s₀ K.k then 1 else 0) ∧
    bytesAt s.mem (L.A b.iC b.oC) K.ctLen =
      VG.Proof.MlKem.KPke.ct K.p (VG.Proof.MlKem.Arm.Enc.aE K L b s₀) (VG.Proof.MlKem.Arm.Enc.ekB K L b s₀) (VG.Proof.MlKem.Arm.Enc.mB L b s₀) (VG.Proof.MlKem.Arm.Enc.rB L s₀) := by
  have hL := hp.ctx.ok
  have hK := hp.wf
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Enc.enc1_ok hp) fun s₁ ⟨e₁, _, ρ₁⟩ => ?_)
  obtain ⟨hc₁, g4, hsE, hr₁⟩ := VG.Proof.MlKem.Arm.Enc.dec_pre hp e₁
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.decT_init (K := K) (L := L) (i := b.iE) (o := b.oE)) fun s₁' h₁' => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.decT_loop hK hc₁ g4 hsE hr₁ h₁') fun s₂ h₂ => ?_)
  obtain ⟨e₂, ρ₂, t₂⟩ := VG.Proof.MlKem.Arm.Enc.enc2_ok hp e₁ ρ₁ h₂
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Enc.enc3_ok hp e₂ ρ₂ t₂) fun s₃ ⟨e₃, ρ₃, t₃, y₃⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Enc.enc4_ok hp e₃ ρ₃ (VG.Proof.MlKem.Arm.Enc.v_of t₃ y₃)) fun s₄ ⟨e₄, ρ₄, v₄, E₄⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Enc.enc5a_ok hp e₄) fun s₄' ⟨h₄', a0, a1, a2, a3⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Enc.enc5b_ok hp e₄ h₄' a0 a1 a2 a3) fun s₅ ⟨e₅, f₅, μ₅⟩ => ?_)
  have d₅ := VG.Proof.MlKem.Arm.Enc.data5 hp ρ₄ v₄ E₄ f₅ μ₅
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Enc.rows_init hp e₅ d₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (wp_loop_ne (VG.Proof.MlKem.Arm.Enc.ERow K L b s₀) (N := K.k) hK.k1 (fun i hi s h => VG.Proof.MlKem.Arm.Enc.encRow_step hp hi h)
    (fun _ h => h) h₆) fun s₇ h₇ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Enc.ev1_ok hp h₇.venv) fun s₈ h₈ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Enc.evArgs_ok hp h₈.1 h₈.2 (o := K.oNtt) (by kenc)) fun s₉ ⟨h₉, a0, a1⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Enc.ev3_ok hp h₉ a0 a1) fun s₁₀ h₁₀ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Enc.evArgs_ok hp h₁₀.1 h₁₀.2 (o := oPoly (3 * K.k)) (by kenc)) fun s₁₁ ⟨h₁₁, b0, b1⟩ => ?_)
  have e₁₁ := h₁₁.1.d.e (2 * K.k) (by omega) (by omega)
  rw [show K.k + 2 * K.k = 3 * K.k by omega] at e₁₁
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Enc.evAdd_ok hp (.inl rfl) h₁₁ e₁₁ b0 b1) fun s₁₂ h₁₂ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Enc.evArgs_ok hp h₁₂.1 h₁₂.2 (o := oPoly (3 * K.k + 1)) (by kenc)) fun s₁₃ ⟨h₁₃, c0, c1⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Enc.evAdd_ok hp (.inr rfl) h₁₃ h₁₃.1.d.mu c0 c1) fun s₁₄ h₁₄ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Enc.ev8_ok hp h₁₄) fun s₁₅ ⟨h₁₅, d0, d1, d2, d3⟩ => ?_)
  exact VG.Proof.MlKem.Arm.Enc.ev9_ok hp h₁₅ d0 d1 d2 d3

end

/-! ## The matrix, for the contracts -/

/-- The `SampleNTT`s of `Â` all finished, with the entries the rows used. -/
theorem enc_some {k : Nat} {ρ r : List Byte} (hk : VG.Proof.MlKem.Arm.Enc.okEnc k ρ k = true) :
    ∀ i < k, ∀ j < k, sampleNTT 280 (VG.Proof.MlKem.matSeed ρ i j) = some (VG.Proof.MlKem.Arm.Enc.aEnc ρ r i j) := by
  intro i hi j hj
  have h₁ := List.all_eq_true.mp hk j (List.mem_range.mpr hj)
  have h₂ := List.all_eq_true.mp h₁ i (List.mem_range.mpr hi)
  simp only [VG.Proof.MlKem.Arm.rowSeed, ↓reduceIte] at h₂
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h₂
  rw [hv]
  simp only [VG.Proof.MlKem.Arm.Enc.aEnc, VG.Proof.MlKem.Arm.effA, VG.Proof.MlKem.Arm.rowSeed, ↓reduceIte, hv, Option.getD_some]

/-- A `SampleNTT` of `Â` did not finish. -/
theorem enc_none {k : Nat} {ρ : List Byte} (hk : VG.Proof.MlKem.Arm.Enc.okEnc k ρ k = false) :
    ∃ i < k, ∃ j < k, sampleNTT 280 (VG.Proof.MlKem.matSeed ρ i j) = none := by
  rw [VG.Proof.MlKem.Arm.Enc.okEnc, List.all_eq_false] at hk
  obtain ⟨j, hj, h₁⟩ := hk
  rw [Bool.not_eq_true, VG.Proof.MlKem.Arm.okRow, List.all_eq_false] at h₁
  obtain ⟨i, hi, h₂⟩ := h₁
  simp only [VG.Proof.MlKem.Arm.rowSeed, ↓reduceIte] at h₂
  exact ⟨i, List.mem_range.mp hi, j, List.mem_range.mp hj, Option.not_isSome_iff_eq_none.mp h₂⟩

end Enc

end VG.Proof.MlKem.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.Decaps`. -/
section

/-!
# ML-KEM on 32-bit ARM: decapsulation, correctness

`K.decaps` for any parameter set `K` (`KemLay.WF`).

The buffers of the function (`lay`): `scratch`, the stack below the stack
pointer, `dk` and `key`; `c`, which may overlap `dk`, is only read by its copy
into `scratch`, with a layout of its own (`layC`). What every phase keeps
(`DEnv`), and the phases: the setup, `c` copied, K-PKE.Decrypt into `m'`,
`G(m' ‖ h)` into `K' ‖ r'`, `J(z ‖ c)` into `K̄`, the re-encryption `c'`
(`Enc.encrypt_ok`), the comparison of `c` and `c'`, and the selection of `K'`
or `K̄` into `key`.
-/

namespace VG.Proof.MlKem.Arm.Decaps

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Enc

section
variable (s₀ : State)

def pDk : BitVec 32 := s₀.gpr .r0
def pC : BitVec 32 := s₀.gpr .r1
def pKey : BitVec 32 := s₀.gpr .r2
def pScr : BitVec 32 := s₀.gpr .r3

/-- The buffers: `scratch`, the 8 bytes below the stack pointer, `dk` and `key`. -/
def lay (K : KemLay) : VG.Proof.MlKem.Arm.Lay :=
  ⟨fun i => [VG.Proof.MlKem.Arm.Decaps.pScr s₀, s₀.sp - BitVec.ofNat 32 8, VG.Proof.MlKem.Arm.Decaps.pDk s₀, VG.Proof.MlKem.Arm.Decaps.pKey s₀].getD i 0, [K.scratch, 8, K.dkLen, 32]⟩

/-- The buffers of the copy of `c`: `scratch`, the stack and `c`. -/
def layC (K : KemLay) : VG.Proof.MlKem.Arm.Lay := ⟨fun i => [VG.Proof.MlKem.Arm.Decaps.pScr s₀, s₀.sp - BitVec.ofNat 32 8, VG.Proof.MlKem.Arm.Decaps.pC s₀].getD i 0, [K.scratch, 8, K.ctLen]⟩

end

/-- The sizes of the buffers. -/
abbrev dSz (K : KemLay) : List Nat := [K.scratch, 8, K.dkLen, 32]

theorem lay_sizes (K : KemLay) (s₀ : State) : (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).sizes = VG.Proof.MlKem.Arm.Decaps.dSz K := rfl
theorem layC_sizes (K : KemLay) (s₀ : State) : (VG.Proof.MlKem.Arm.Decaps.layC s₀ K).sizes = [K.scratch, 8, K.ctLen] := rfl
theorem lay_ptr0 (K : KemLay) (s₀ : State) : (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 = VG.Proof.MlKem.Arm.Decaps.pScr s₀ := rfl
theorem layC_ptr0 (K : KemLay) (s₀ : State) : (VG.Proof.MlKem.Arm.Decaps.layC s₀ K).ptr 0 = VG.Proof.MlKem.Arm.Decaps.pScr s₀ := rfl

/-- The precondition of the contract. -/
structure Pre (K : KemLay) (s : State) : Prop where
  wf : K.WF
  calls : K.CallsOk
  sp8 : 8 ≤ s.sp.toNat
  spf : s.sp.toNat ≤ 2 ^ 32
  rd : s.rd = [⟨State.addr (VG.Proof.MlKem.Arm.Decaps.pDk s), K.dkLen⟩, ⟨State.addr (VG.Proof.MlKem.Arm.Decaps.pC s), K.ctLen⟩]
  wr : s.wr = [⟨State.addr (VG.Proof.MlKem.Arm.Decaps.pKey s), 32⟩, ⟨State.addr (VG.Proof.MlKem.Arm.Decaps.pScr s), K.scratch⟩]
  d_dk_key : (⟨State.addr (VG.Proof.MlKem.Arm.Decaps.pDk s), K.dkLen⟩ : Region).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.Decaps.pKey s), 32⟩
  d_dk_scr : (⟨State.addr (VG.Proof.MlKem.Arm.Decaps.pDk s), K.dkLen⟩ : Region).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.Decaps.pScr s), K.scratch⟩
  d_c_key : (⟨State.addr (VG.Proof.MlKem.Arm.Decaps.pC s), K.ctLen⟩ : Region).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.Decaps.pKey s), 32⟩
  d_c_scr : (⟨State.addr (VG.Proof.MlKem.Arm.Decaps.pC s), K.ctLen⟩ : Region).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.Decaps.pScr s), K.scratch⟩
  d_key_scr : (⟨State.addr (VG.Proof.MlKem.Arm.Decaps.pKey s), 32⟩ : Region).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.Decaps.pScr s), K.scratch⟩
  b_dk : (below s 8).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.Decaps.pDk s), K.dkLen⟩
  b_c : (below s 8).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.Decaps.pC s), K.ctLen⟩
  b_key : (below s 8).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.Decaps.pKey s), 32⟩
  b_scr : (below s 8).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.Decaps.pScr s), K.scratch⟩
  f_dk : (VG.Proof.MlKem.Arm.Decaps.pDk s).toNat + K.dkLen ≤ 2 ^ 32
  f_c : (VG.Proof.MlKem.Arm.Decaps.pC s).toNat + K.ctLen ≤ 2 ^ 32
  f_key : (VG.Proof.MlKem.Arm.Decaps.pKey s).toNat + 32 ≤ 2 ^ 32
  f_scr : (VG.Proof.MlKem.Arm.Decaps.pScr s).toNat + K.scratch ≤ 2 ^ 32

section
variable {K : KemLay} {s₀ : State} (hp : VG.Proof.MlKem.Arm.Decaps.Pre K s₀)
include hp

theorem stack_eq : (⟨State.addr (s₀.sp - BitVec.ofNat 32 8), 8⟩ : Region) = below s₀ 8 := by
  rw [addr_sub hp.sp8]

theorem stack_fit : (s₀.sp - BitVec.ofNat 32 8).toNat + 8 ≤ 2 ^ 32 := by
  have := hp.sp8; have := s₀.sp.isLt; bv_omega

theorem lay_ok : (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).Ok := by
  have es := VG.Proof.MlKem.Arm.Decaps.stack_eq hp
  refine Lay.ok_of (fun i hi => ?_) (fun i hi j hj hij => ?_)
  · simp only [VG.Proof.MlKem.Arm.Decaps.lay, List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    · exact hp.f_scr
    · exact VG.Proof.MlKem.Arm.Decaps.stack_fit hp
    · exact hp.f_dk
    · exact hp.f_key
  · simp only [VG.Proof.MlKem.Arm.Decaps.lay, List.length_cons, List.length_nil] at hi hj
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
    rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl <;>
    simp only [VG.Proof.MlKem.Arm.Decaps.lay, Lay.size, List.getD_cons_zero, List.getD_cons_succ] <;>
    first | omega | skip
    · rw [es]; exact hp.b_scr.symm
    · exact hp.d_dk_scr.symm
    · exact hp.d_key_scr.symm
    · rw [es]; exact hp.b_dk
    · rw [es]; exact hp.b_key
    · exact hp.d_dk_key

theorem layC_ok : (VG.Proof.MlKem.Arm.Decaps.layC s₀ K).Ok := by
  have es := VG.Proof.MlKem.Arm.Decaps.stack_eq hp
  refine Lay.ok_of (fun i hi => ?_) (fun i hi j hj hij => ?_)
  · simp only [VG.Proof.MlKem.Arm.Decaps.layC, List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact hp.f_scr
    · exact VG.Proof.MlKem.Arm.Decaps.stack_fit hp
    · exact hp.f_c
  · simp only [VG.Proof.MlKem.Arm.Decaps.layC, List.length_cons, List.length_nil] at hi hj
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
    rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl <;>
    simp only [VG.Proof.MlKem.Arm.Decaps.layC, Lay.size, List.getD_cons_zero, List.getD_cons_succ] <;>
    first | omega | skip
    · rw [es]; exact hp.b_scr.symm
    · exact hp.d_c_scr.symm
    · rw [es]; exact hp.b_c

end

/-- What every phase keeps: `scratch`, our caller's registers and `key` in
`scratch`, and `dk`. -/
structure DEnv (K : KemLay) (s₀ s : State) : Prop where
  ctx : VG.Proof.MlKem.Arm.Ctx (VG.Proof.MlKem.Arm.Decaps.lay s₀ K) s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  sav : VG.Proof.MlKem.Arm.Saved s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 840) s₀.gpr
  savlr : s.mem.readW ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 872) 32 = s₀.gpr .lr
  key : s.mem.readW ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 876) 32 = VG.Proof.MlKem.Arm.Decaps.pKey s₀
  dk : bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 2 0) K.dkLen = bytesAt s₀.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 2 0) K.dkLen

/-- A region the phases may change: apart from the saved registers, `key`'s pointer and `dk`. -/
def okW (K : KemLay) (w : Nat × Nat × Nat) : Bool := VG.Proof.MlKem.Arm.sepB (VG.Proof.MlKem.Arm.Decaps.dSz K) (0, 840, 40) w && VG.Proof.MlKem.Arm.sepB (VG.Proof.MlKem.Arm.Decaps.dSz K) (2, 0, K.dkLen) w

/-- A region decryption may change. -/
def okD (K : KemLay) (w : Nat × Nat × Nat) : Bool := VG.Proof.MlKem.Arm.Decaps.okW K w && VG.Proof.MlKem.Arm.sepB (VG.Proof.MlKem.Arm.Decaps.dSz K) (0, oCin, K.ctLen) w

/-! ### The facts on the offsets, once for any parameter set

They depend on the parameter set only through `k`, the size of `scratch`, and
the length of `c`: each is decided for every `k ≤ 4` with a `scratch` of 32 KiB
(`kOf`) and the longest `c` that fits (8192 bytes from `oCin`, `oCin - oCt`
from `oCt`), and holds for a bigger `scratch` (`sepB_scr`) and a shorter `c`
(`sepB_mono`). -/

/-- `okW`, with the sizes `sz` of the buffers. -/
abbrev okWm (K : KemLay) (sz : List Nat) (w : Nat × Nat × Nat) : Bool :=
  VG.Proof.MlKem.Arm.sepB sz (0, 840, 40) w && VG.Proof.MlKem.Arm.sepB sz (2, 0, K.dkLen) w

/-- `okD`, with the sizes `sz` of the buffers and the longest `c`. -/
abbrev okDm (K : KemLay) (sz : List Nat) (w : Nat × Nat × Nat) : Bool := VG.Proof.MlKem.Arm.Decaps.okWm K sz w && VG.Proof.MlKem.Arm.sepB sz (0, oCin, 8192) w

theorem inB_len {i o n l : Nat} (h : n ≤ l) : VG.Proof.MlKem.Arm.inB (i, o, n) (i, o, l) = true := by
  simp only [VG.Proof.MlKem.Arm.inB, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]; omega

theorem ct_le {K : KemLay} (hK : K.WF) : K.ctLen ≤ 8192 := by
  have := hK.cin; simp only [oCin] at this; omega

theorem okW_of {K : KemLay} (hK : K.WF) {w : Nat × Nat × Nat} (h : VG.Proof.MlKem.Arm.Decaps.okWm K (VG.Proof.MlKem.Arm.Decaps.dSz (VG.Proof.MlKem.Arm.kOf K.k)) w = true) :
    VG.Proof.MlKem.Arm.Decaps.okW K w = true := by
  simp only [VG.Proof.MlKem.Arm.Decaps.okWm, VG.Proof.MlKem.Arm.Decaps.okW, Bool.and_eq_true] at h ⊢
  exact ⟨VG.Proof.MlKem.Arm.sepB_scr h.1 hK.scr, VG.Proof.MlKem.Arm.sepB_scr h.2 hK.scr⟩

theorem allOkW_of {K : KemLay} (hK : K.WF) {W : List (Nat × Nat × Nat)}
    (h : W.all (VG.Proof.MlKem.Arm.Decaps.okWm K (VG.Proof.MlKem.Arm.Decaps.dSz (VG.Proof.MlKem.Arm.kOf K.k))) = true) : W.all (VG.Proof.MlKem.Arm.Decaps.okW K) = true :=
  List.all_eq_true.mpr fun w hw => VG.Proof.MlKem.Arm.Decaps.okW_of hK (List.all_eq_true.mp h w hw)

theorem allOkD_of {K : KemLay} (hK : K.WF) {W : List (Nat × Nat × Nat)}
    (h : W.all (VG.Proof.MlKem.Arm.Decaps.okDm K (VG.Proof.MlKem.Arm.Decaps.dSz (VG.Proof.MlKem.Arm.kOf K.k))) = true) : W.all (VG.Proof.MlKem.Arm.Decaps.okD K) = true :=
  List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp h w hw
    rw [VG.Proof.MlKem.Arm.Decaps.okDm, Bool.and_eq_true] at this
    rw [VG.Proof.MlKem.Arm.Decaps.okD, Bool.and_eq_true]
    exact ⟨VG.Proof.MlKem.Arm.Decaps.okW_of hK this.1, VG.Proof.MlKem.Arm.sepB_mono (VG.Proof.MlKem.Arm.sepB_scr this.2 hK.scr) (VG.Proof.MlKem.Arm.Decaps.inB_len (VG.Proof.MlKem.Arm.Decaps.ct_le hK)) (VG.Proof.MlKem.Arm.inB_refl w)⟩

/-- The regions decryption and the hashes change, apart from what `DD` keeps. -/
abbrev DecF (K : KemLay) (sz : List Nat) : Prop :=
  [((0 : Nat), oPoly K.k, 1024 * K.k), (0, K.oNtt, 1024)].all (VG.Proof.MlKem.Arm.Decaps.okDm K sz) = true ∧
  [((0 : Nat), (2048 : Nat), 1024 * K.k)].all (VG.Proof.MlKem.Arm.Decaps.okDm K sz) = true ∧ (VG.Proof.MlKem.Arm.dotW K).all (VG.Proof.MlKem.Arm.Decaps.okDm K sz) = true ∧
  [((0 : Nat), K.oAcc, (1024 : Nat)), (0, K.oNtt, 1024)].all (VG.Proof.MlKem.Arm.Decaps.okDm K sz) = true ∧
  [((0 : Nat), oPoly (3 * K.k), (1024 : Nat))].all (VG.Proof.MlKem.Arm.Decaps.okDm K sz) = true ∧
  [((0 : Nat), oMsg, 32 * 1)].all (VG.Proof.MlKem.Arm.Decaps.okDm K sz) = true ∧ (VG.Proof.MlKem.Arm.kRegs ++ [(0, oG, 64)]).all (VG.Proof.MlKem.Arm.Decaps.okDm K sz) = true ∧
  (VG.Proof.MlKem.Arm.kRegs ++ [(0, oKbar, 32)]).all (VG.Proof.MlKem.Arm.Decaps.okDm K sz) = true ∧ VG.Proof.MlKem.Arm.Decaps.okWm K sz (0, oCin, 8192) = true ∧
  [((3 : Nat), (0 : Nat), (32 : Nat))].all (VG.Proof.MlKem.Arm.Decaps.okWm K sz) = true

theorem dec_f {K : KemLay} (hK : K.WF) :
    [((0 : Nat), oPoly K.k, 1024 * K.k), (0, K.oNtt, 1024)].all (VG.Proof.MlKem.Arm.Decaps.okD K) = true ∧
    [((0 : Nat), (2048 : Nat), 1024 * K.k)].all (VG.Proof.MlKem.Arm.Decaps.okD K) = true ∧ (VG.Proof.MlKem.Arm.dotW K).all (VG.Proof.MlKem.Arm.Decaps.okD K) = true ∧
    [((0 : Nat), K.oAcc, (1024 : Nat)), (0, K.oNtt, 1024)].all (VG.Proof.MlKem.Arm.Decaps.okD K) = true ∧
    [((0 : Nat), oPoly (3 * K.k), (1024 : Nat))].all (VG.Proof.MlKem.Arm.Decaps.okD K) = true ∧
    [((0 : Nat), oMsg, 32 * 1)].all (VG.Proof.MlKem.Arm.Decaps.okD K) = true ∧ (VG.Proof.MlKem.Arm.kRegs ++ [(0, oG, 64)]).all (VG.Proof.MlKem.Arm.Decaps.okD K) = true ∧
    (VG.Proof.MlKem.Arm.kRegs ++ [(0, oKbar, 32)]).all (VG.Proof.MlKem.Arm.Decaps.okD K) = true ∧ [((0 : Nat), oCin, K.ctLen)].all (VG.Proof.MlKem.Arm.Decaps.okW K) = true ∧
    [((3 : Nat), (0 : Nat), (32 : Nat))].all (VG.Proof.MlKem.Arm.Decaps.okW K) = true := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ :=
    (by decide : ∀ k < 5, DecF (kOf k) (dSz (kOf k))) K.k (by have := hK.k4; omega)
  refine ⟨VG.Proof.MlKem.Arm.Decaps.allOkD_of hK f1, VG.Proof.MlKem.Arm.Decaps.allOkD_of hK f2, VG.Proof.MlKem.Arm.Decaps.allOkD_of hK f3, VG.Proof.MlKem.Arm.Decaps.allOkD_of hK f4, VG.Proof.MlKem.Arm.Decaps.allOkD_of hK f5, VG.Proof.MlKem.Arm.Decaps.allOkD_of hK f6,
    VG.Proof.MlKem.Arm.Decaps.allOkD_of hK f7, VG.Proof.MlKem.Arm.Decaps.allOkD_of hK f8, ?_, VG.Proof.MlKem.Arm.Decaps.allOkW_of hK f10⟩
  simp only [List.all_cons, List.all_nil, Bool.and_true, VG.Proof.MlKem.Arm.Decaps.okWm, VG.Proof.MlKem.Arm.Decaps.okW, Bool.and_eq_true] at f9 ⊢
  exact ⟨VG.Proof.MlKem.Arm.sepB_mono (VG.Proof.MlKem.Arm.sepB_scr f9.1 hK.scr) (VG.Proof.MlKem.Arm.inB_refl _) (VG.Proof.MlKem.Arm.Decaps.inB_len (VG.Proof.MlKem.Arm.Decaps.ct_le hK)),
    VG.Proof.MlKem.Arm.sepB_mono (VG.Proof.MlKem.Arm.sepB_scr f9.2 hK.scr) (VG.Proof.MlKem.Arm.inB_refl _) (VG.Proof.MlKem.Arm.Decaps.inB_len (VG.Proof.MlKem.Arm.Decaps.ct_le hK))⟩

/-- The pieces of the hashes, and what the end keeps. -/
abbrev DecP (K : KemLay) (sz : List Nat) : Prop :=
  VG.Proof.MlKem.Arm.sepAll sz (0, oMsg, 32) VG.Proof.MlKem.Arm.kRegs = true ∧ VG.Proof.MlKem.Arm.sepAll sz (2, 768 * K.k + 32, 32) VG.Proof.MlKem.Arm.kRegs = true ∧
  VG.Proof.MlKem.Arm.sepAll sz (0, oG, 64) VG.Proof.MlKem.Arm.kRegs = true ∧ VG.Proof.MlKem.Arm.sepAll sz (2, 768 * K.k + 64, 32) VG.Proof.MlKem.Arm.kRegs = true ∧
  VG.Proof.MlKem.Arm.sepAll sz (0, oCin, 8192) VG.Proof.MlKem.Arm.kRegs = true ∧ VG.Proof.MlKem.Arm.sepAll sz (0, oKbar, 32) VG.Proof.MlKem.Arm.kRegs = true ∧
  VG.Proof.MlKem.Arm.sepAll sz (0, oMsg, 32) (VG.Proof.MlKem.Arm.kRegs ++ [(0, oKbar, 32)]) = true ∧ VG.Proof.MlKem.Arm.sepAll sz (0, oMsg, 32) (VG.Proof.MlKem.Arm.kRegs ++ [(0, oG, 64)]) = true ∧
  VG.Proof.MlKem.Arm.sepAll sz (0, oG, 32) (VG.Proof.MlKem.Arm.kRegs ++ [(0, oKbar, 32)]) = true ∧
  VG.Proof.MlKem.Arm.sepAll sz (0, oSigma, 32) (VG.Proof.MlKem.Arm.kRegs ++ [(0, oKbar, 32)]) = true ∧
  VG.Proof.MlKem.Arm.sepB sz (0, oG, 32) (3, 0, 32) = true ∧ VG.Proof.MlKem.Arm.sepB sz (0, oKbar, 32) (3, 0, 32) = true ∧
  VG.Proof.MlKem.Arm.sepAll sz (2, 0, K.dkLen) [(0, 840, 40)] = true

theorem dec_p {K : KemLay} (hK : K.WF) :
    VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.Decaps.dSz K) (0, oMsg, 32) VG.Proof.MlKem.Arm.kRegs = true ∧ VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.Decaps.dSz K) (2, 768 * K.k + 32, 32) VG.Proof.MlKem.Arm.kRegs = true ∧
    VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.Decaps.dSz K) (0, oG, 64) VG.Proof.MlKem.Arm.kRegs = true ∧ VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.Decaps.dSz K) (2, 768 * K.k + 64, 32) VG.Proof.MlKem.Arm.kRegs = true ∧
    VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.Decaps.dSz K) (0, oCin, K.ctLen) VG.Proof.MlKem.Arm.kRegs = true ∧ VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.Decaps.dSz K) (0, oKbar, 32) VG.Proof.MlKem.Arm.kRegs = true ∧
    VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.Decaps.dSz K) (0, oMsg, 32) (VG.Proof.MlKem.Arm.kRegs ++ [(0, oKbar, 32)]) = true ∧
    VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.Decaps.dSz K) (0, oMsg, 32) (VG.Proof.MlKem.Arm.kRegs ++ [(0, oG, 64)]) = true ∧
    VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.Decaps.dSz K) (0, oG, 32) (VG.Proof.MlKem.Arm.kRegs ++ [(0, oKbar, 32)]) = true ∧
    VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.Decaps.dSz K) (0, oSigma, 32) (VG.Proof.MlKem.Arm.kRegs ++ [(0, oKbar, 32)]) = true ∧
    VG.Proof.MlKem.Arm.sepB (VG.Proof.MlKem.Arm.Decaps.dSz K) (0, oG, 32) (3, 0, 32) = true ∧ VG.Proof.MlKem.Arm.sepB (VG.Proof.MlKem.Arm.Decaps.dSz K) (0, oKbar, 32) (3, 0, 32) = true ∧
    VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.Decaps.dSz K) (2, 0, K.dkLen) [(0, 840, 40)] = true := by
  have s := hK.scr
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13⟩ :=
    (by decide : ∀ k < 5, DecP (kOf k) (dSz (kOf k))) K.k (by have := hK.k4; omega)
  exact ⟨VG.Proof.MlKem.Arm.sepAll_scr f1 s, VG.Proof.MlKem.Arm.sepAll_scr f2 s, VG.Proof.MlKem.Arm.sepAll_scr f3 s, VG.Proof.MlKem.Arm.sepAll_scr f4 s,
    VG.Proof.MlKem.Arm.Enc.sepAll_left (VG.Proof.MlKem.Arm.sepAll_scr f5 s) (VG.Proof.MlKem.Arm.Decaps.inB_len (VG.Proof.MlKem.Arm.Decaps.ct_le hK)), VG.Proof.MlKem.Arm.sepAll_scr f6 s, VG.Proof.MlKem.Arm.sepAll_scr f7 s, VG.Proof.MlKem.Arm.sepAll_scr f8 s,
    VG.Proof.MlKem.Arm.sepAll_scr f9 s, VG.Proof.MlKem.Arm.sepAll_scr f10 s, VG.Proof.MlKem.Arm.sepB_scr f11 s, VG.Proof.MlKem.Arm.sepB_scr f12 s, VG.Proof.MlKem.Arm.sepAll_scr f13 s⟩

/-- The buffer of each pointer register. -/
def didx : Reg → Nat
  | .r4 => 2 | _ => 0

/-- Decides a fact about the offsets in the buffers. -/
macro "ddecide" : tactic => `(tactic| first
  | decide
  | ((try have := (‹Pre _ _›).wf)
     (try simp only [lay_sizes, layC_sizes, dSz, okW, okD, didx, kRegs, List.all_cons, List.all_nil,
        List.all_append, List.map_cons, List.map_nil, trip, Bool.and_true])
     (try have := (‹KemLay.WF _›).scr)
     (try (have h := (‹KemLay.WF _›).cin; simp only [oCin, KemLay.ctLen, KemLay.uLen, KemLay.vLen] at h))
     kdecide))

theorem DEnv.keep {K : KemLay} {s₀ s s' : State} (hp : VG.Proof.MlKem.Arm.Decaps.Pre K s₀) (h : VG.Proof.MlKem.Arm.Decaps.DEnv K s₀ s) {xs : List Reg} {W : List (Nat × Nat × Nat)}
    (hk : VG.Proof.MlKem.Arm.KeptX xs ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).RL W) s s') (h7 : Reg.r7 ∉ xs) (hW : W.all (VG.Proof.MlKem.Arm.Decaps.okW K) = true) : VG.Proof.MlKem.Arm.Decaps.DEnv K s₀ s' := by
  have hL := VG.Proof.MlKem.Arm.Decaps.lay_ok hp
  have h1 : VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).sizes (0, 840, 40) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw; simp only [VG.Proof.MlKem.Arm.Decaps.okW, Bool.and_eq_true] at this; exact this.1
  have h2 : VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).sizes (2, 0, K.dkLen) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw; simp only [VG.Proof.MlKem.Arm.Decaps.okW, Bool.and_eq_true] at this; exact this.2
  have hd := Lay.disjAll hL h1
  have c872 : (Lay.R (VG.Proof.MlKem.Arm.Decaps.lay s₀ K) 0 840 40).Contains ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 872) 4 := by
    simp only [Region.Contains]; bv_omega
  have c876 : (Lay.R (VG.Proof.MlKem.Arm.Decaps.lay s₀ K) 0 840 40).Contains ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 876) 4 := by
    simp only [Region.Contains]; bv_omega
  refine ⟨hk.ctx h7 h.ctx, hk.rd.trans h.rd, hk.wr.trans h.wr, hk.sp.trans h.sp, fun i hi => ?_, ?_, ?_, ?_⟩
  · rw [hk.frame.readW (r := Lay.R (VG.Proof.MlKem.Arm.Decaps.lay s₀ K) 0 840 40) (by simp only [Region.Contains]; bv_omega) hd (by ddecide)]
    exact h.sav i hi
  · rw [hk.frame.readW c872 hd (by ddecide)]; exact h.savlr
  · rw [hk.frame.readW c876 hd (by ddecide)]; exact h.key
  · rw [Lay.bytes_keep hL hk.frame h2 (by ddecide)]; exact h.dk

theorem buf_wr {K : KemLay} {s₀ : State} (hp : VG.Proof.MlKem.Arm.Decaps.Pre K s₀) :
    (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).buf 0 ∈ s₀.wr ∧ (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).buf 3 ∈ s₀.wr ∧ (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).buf 2 ∈ s₀.rd ++ s₀.wr ∧
      (VG.Proof.MlKem.Arm.Decaps.layC s₀ K).buf 2 ∈ s₀.rd ++ s₀.wr ∧ (VG.Proof.MlKem.Arm.Decaps.layC s₀ K).buf 0 ∈ s₀.wr := by
  rw [hp.wr, hp.rd]; simp [Lay.buf, VG.Proof.MlKem.Arm.Decaps.lay, VG.Proof.MlKem.Arm.Decaps.layC]

/-! ## The setup -/

theorem setup_ok {K : KemLay} {s₀ : State} (hp : VG.Proof.MlKem.Arm.Decaps.Pre K s₀) :
    WP isa (.block decapsSetup) s₀ fun s => VG.Proof.MlKem.Arm.Decaps.DEnv K s₀ s ∧ s.gpr .r4 = VG.Proof.MlKem.Arm.Decaps.pDk s₀ ∧ s.gpr .r6 = VG.Proof.MlKem.Arm.Decaps.pC s₀ ∧
      bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.layC s₀ K).A 2 0) K.ctLen = bytesAt s₀.mem ((VG.Proof.MlKem.Arm.Decaps.layC s₀ K).A 2 0) K.ctLen := by
  have hL := VG.Proof.MlKem.Arm.Decaps.lay_ok hp
  have scr := hp.wf.scr
  have fc := hp.f_scr
  obtain ⟨w0, -, -, -, -⟩ := VG.Proof.MlKem.Arm.Decaps.buf_wr hp
  have wS : ∀ {o n : Nat}, o + n ≤ K.scratch → InRegions s₀.wr ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 o) n := fun h =>
    Lay.covers w0 h _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [decapsSetup, WP.block_append_iff]
  refine WP.mono (saveRegs_ok .r3 (off := 840) (by ddecide) (fit_le (by ddecide) fc) fun i hi => by
    rw [add_ofNat_add]; exact wS (by omega)) fun s₁ h₁ => ?_
  have g3 : s₁.gpr .r3 = VG.Proof.MlKem.Arm.Decaps.pScr s₀ := by rw [h₁.gpr]; rfl
  have e872 : State.addr (s₁.gpr .r3 + BitVec.ofNat 32 (oSave + 32)) = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 872 := by
    rw [g3, ← VG.Proof.MlKem.Arm.Decaps.lay_ptr0]; exact addr_add (by rw [VG.Proof.MlKem.Arm.Decaps.lay_ptr0]; offs)
  have e876 : State.addr (s₁.gpr .r3 + BitVec.ofNat 32 oExtra) = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 876 := by
    rw [g3, ← VG.Proof.MlKem.Arm.Decaps.lay_ptr0]; exact addr_add (by rw [VG.Proof.MlKem.Arm.Decaps.lay_ptr0]; offs)
  have i872 : InRegions s₁.wr (State.addr (s₁.gpr .r3 + BitVec.ofNat 32 (oSave + 32))) 4 := by
    rw [e872, h₁.wr]; exact wS (by ddecide)
  have i876 : InRegions s₁.wr (State.addr (s₁.gpr .r3 + BitVec.ofNat 32 oExtra)) 4 := by
    rw [e876, h₁.wr]; exact wS (by ddecide)
  have o1 : oSave + 32 < 4096 := by decide
  have o2 : oExtra < 4096 := by decide
  run_block [i872, i876, o1, o2]
  have ne1 : ∀ i < 8, ∀ (m : Mem) (v : BitVec 32), (m.writeW ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 872) v).readW
      ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 = m.readW ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 :=
    fun i hi m v => Mem.readW_writeW_sep (fun x h1 h2 => by bv_omega) (by ddecide)
  have ne2 : ∀ i < 9, ∀ (m : Mem) (v : BitVec 32), (m.writeW ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 876) v).readW
      ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 = m.readW ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 :=
    fun i hi m v => Mem.readW_writeW_sep (fun x h1 h2 => by bv_omega) (by ddecide)
  have fr₀ : Frame ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).RL [(0, 840, 40)]) s₀.mem s₁.mem := by
    refine h₁.frame.sub fun r hr' => ⟨Lay.R (VG.Proof.MlKem.Arm.Decaps.lay s₀ K) 0 840 40, by simp, ?_⟩
    rw [List.mem_singleton] at hr'; subst hr'
    show Region.Sub ⟨State.addr (s₀.gpr .r3) + BitVec.ofNat 64 840, 32⟩ _
    exact Lay.R_sub_R hL (i := 0) (a := 840) (l := 32) (by simp [VG.Proof.MlKem.Arm.Decaps.lay]) (by ddecide) (by ddecide) (by simp [VG.Proof.MlKem.Arm.Decaps.lay]; omega)
  have c872 : ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).R 0 840 40).Contains ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 872) 4 := by
    simp only [Region.Contains]; bv_omega
  have c876 : ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).R 0 840 40).Contains ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 876) 4 := by
    simp only [Region.Contains]; bv_omega
  have fr : Frame ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).RL [(0, 840, 40)]) s₀.mem
      ((s₁.mem.writeW ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 872) (s₁.gpr .lr)).writeW ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 876) (s₁.gpr .r2)) :=
    (fr₀.writeW (List.mem_singleton_self _) _ c872).writeW (List.mem_singleton_self _) _ c876
  refine ⟨⟨⟨hL, scr, rfl, by simp [VG.Proof.MlKem.Arm.Decaps.lay], ?_, by show 8 ≤ s₁.sp.toNat; rw [h₁.sp]; exact hp.sp8, ?_, ?_⟩,
    h₁.rd, h₁.wr, h₁.sp, fun i hi => ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [h₁.gpr]; rfl
  · show s₀.sp - BitVec.ofNat 32 8 = s₁.sp - BitVec.ofNat 32 8
    rw [h₁.sp]
  · show (⟨State.addr (VG.Proof.MlKem.Arm.Decaps.pScr s₀), K.scratch⟩ : Region) ∈ s₁.wr
    rw [h₁.wr, hp.wr]; simp
  · show ((s₁.mem.writeW _ _).writeW _ _).readW _ _ = _
    rw [e872, e876, ne2 i (by omega), ne1 i hi]
    exact h₁.saved i hi
  · show ((s₁.mem.writeW _ _).writeW _ _).readW _ _ = _
    rw [e872, e876, show (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 872 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 840 + BitVec.ofNat 64 (4 * 8) by
      rw [add_ofNat_add], ne2 8 (by ddecide), add_ofNat_add, Mem.readW_writeW_self32, h₁.gpr]
  · show ((s₁.mem.writeW _ _).writeW _ _).readW _ _ = _
    rw [e872, e876, Mem.readW_writeW_self32, h₁.gpr]; rfl
  · show bytesAt ((s₁.mem.writeW _ _).writeW _ _) _ _ = _
    rw [e872, e876]
    exact Lay.bytes_keep hL fr (VG.Proof.MlKem.Arm.Decaps.dec_p hp.wf).2.2.2.2.2.2.2.2.2.2.2.2 (by ddecide)
  · simp [h₁.gpr]; rfl
  · simp [h₁.gpr]; rfl
  · show bytesAt ((s₁.mem.writeW _ _).writeW _ _) _ _ = _
    rw [e872, e876]
    have fC : Frame ((VG.Proof.MlKem.Arm.Decaps.layC s₀ K).RL [(0, 840, 40)]) s₀.mem
        ((s₁.mem.writeW ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 872) (s₁.gpr .lr)).writeW ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 876) (s₁.gpr .r2)) := by
      simpa only [Lay.RL, List.map_cons, List.map_nil, Lay.R, VG.Proof.MlKem.Arm.Decaps.lay_ptr0, VG.Proof.MlKem.Arm.Decaps.layC_ptr0] using fr
    exact Lay.bytes_keep (VG.Proof.MlKem.Arm.Decaps.layC_ok hp) fC (by rw [VG.Proof.MlKem.Arm.Decaps.layC_sizes]; ddecide) (by ddecide)


/-! ## `c` copied -/

/-- `dk`. -/
abbrev DK (K : KemLay) (s₀ : State) : List Byte := bytesAt s₀.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 2 0) K.dkLen

/-- `c`. -/
abbrev CT (K : KemLay) (s₀ : State) : List Byte := bytesAt s₀.mem ((VG.Proof.MlKem.Arm.Decaps.layC s₀ K).A 2 0) K.ctLen

theorem layA0 (K : KemLay) (s₀ : State) (o : Nat) : (VG.Proof.MlKem.Arm.Decaps.layC s₀ K).A 0 o = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 o := by
  simp only [Lay.A, VG.Proof.MlKem.Arm.Decaps.lay_ptr0, VG.Proof.MlKem.Arm.Decaps.layC_ptr0]

theorem copyC_ok {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.Decaps.Pre K s₀) (h : VG.Proof.MlKem.Arm.Decaps.DEnv K s₀ s) (h6 : s.gpr .r6 = VG.Proof.MlKem.Arm.Decaps.pC s₀)
    (hc : bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.layC s₀ K).A 2 0) K.ctLen = VG.Proof.MlKem.Arm.Decaps.CT K s₀) :
    WP isa (copy .r6 0 .r7 oCin K.ctLen) s fun s' =>
      VG.Proof.MlKem.Arm.Decaps.DEnv K s₀ s' ∧ s'.gpr .r4 = s.gpr .r4 ∧ bytesAt s'.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 oCin) K.ctLen = VG.Proof.MlKem.Arm.Decaps.CT K s₀ := by
  obtain ⟨-, -, -, wC, wC0⟩ := VG.Proof.MlKem.Arm.Decaps.buf_wr hp
  refine WP.mono (VG.Proof.MlKem.Arm.copyL (VG.Proof.MlKem.Arm.Decaps.layC_ok hp) (i := 2) (j := 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ h6
    (by rw [h.ctx.r7, VG.Proof.MlKem.Arm.Decaps.lay_ptr0, VG.Proof.MlKem.Arm.Decaps.layC_ptr0]) (by ddecide) (by ddecide) hp.wf.encCt (by ddecide) hp.wf.ct_pos
    (by rw [VG.Proof.MlKem.Arm.Decaps.layC_sizes]; ddecide) (by rw [h.rd, h.wr]; exact wC) (by rw [h.wr]; exact wC0)) fun s' ⟨k, e⟩ =>
    ⟨?_, k.cs .r4 (by ddecide) (by ddecide), ?_⟩
  · have k' : Kept ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).RL [(0, oCin, K.ctLen)]) s s' := by
      simpa only [Lay.RL, List.map_cons, List.map_nil, Lay.R, VG.Proof.MlKem.Arm.Decaps.lay_ptr0, VG.Proof.MlKem.Arm.Decaps.layC_ptr0] using k
    exact h.keep hp (k'.x []) (by simp) (VG.Proof.MlKem.Arm.Decaps.dec_f hp.wf).2.2.2.2.2.2.2.2.1
  · rw [← VG.Proof.MlKem.Arm.Decaps.layA0, e, hc]

theorem ptr6_ok {s : State} :
    WP isa (.block [ptrTo .r6 .r7 oCin]) s fun s' =>
      VG.Proof.MlKem.Arm.KeptX [.r6] [] s s' ∧ s'.gpr .r6 = s.gpr .r7 + BitVec.ofNat 32 oCin ∧ s'.mem = s.mem := by
  have e1 : encodable (BitVec.ofNat 32 oCin) = true := by decide
  run_block [ptrTo, e1]
  refine ⟨⟨fun r _ _ hx => ?_, rfl, rfl, rfl, Frame.refl _ _⟩, trivial⟩
  show (if r = .r6 then _ else s.gpr r) = s.gpr r
  exact ite_eq_right (fun e : r = .r6 => hx (by rw [e]; exact List.mem_singleton_self _))

/-- What decryption keeps: `DEnv`, `dk` in `r4`, and the copy of `c` in `r6`. -/
structure DD (K : KemLay) (s₀ s : State) : Prop where
  env : VG.Proof.MlKem.Arm.Decaps.DEnv K s₀ s
  r4 : s.gpr .r4 = VG.Proof.MlKem.Arm.Decaps.pDk s₀
  r6 : s.gpr .r6 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 oCin
  c : bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 oCin) K.ctLen = VG.Proof.MlKem.Arm.Decaps.CT K s₀


theorem DD.keep {K : KemLay} {s₀ s s' : State} (hp : VG.Proof.MlKem.Arm.Decaps.Pre K s₀) (h : VG.Proof.MlKem.Arm.Decaps.DD K s₀ s) {xs : List Reg} {W : List (Nat × Nat × Nat)}
    (hk : VG.Proof.MlKem.Arm.KeptX xs ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).RL W) s s') (hx : ∀ r ∈ [Reg.r4, .r6, .r7], r ∉ xs) (hW : W.all (VG.Proof.MlKem.Arm.Decaps.okD K) = true) :
    VG.Proof.MlKem.Arm.Decaps.DD K s₀ s' := by
  have w1 : W.all (VG.Proof.MlKem.Arm.Decaps.okW K) = true := List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp hW w hw; simp only [VG.Proof.MlKem.Arm.Decaps.okD, Bool.and_eq_true] at this; exact this.1
  have w2 : VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).sizes (0, oCin, K.ctLen) W = true := List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp hW w hw; simp only [VG.Proof.MlKem.Arm.Decaps.okD, Bool.and_eq_true] at this; exact this.2
  refine ⟨h.env.keep hp hk (hx .r7 (by simp)) w1, ?_, ?_, ?_⟩
  · rw [hk.cs .r4 (by ddecide) (by ddecide) (hx .r4 (by simp)), h.r4]
  · rw [hk.cs .r6 (by ddecide) (by ddecide) (hx .r6 (by simp)), h.r6]
  · rw [Lay.bytes_keep (VG.Proof.MlKem.Arm.Decaps.lay_ok hp) hk.frame w2 (by ddecide)]; exact h.c

/-! ## `û` -/

theorem uArgs_ok {K : KemLay} (hK : K.WF) {s : State} {P C : BitVec 32} {j : Nat} (h7 : s.gpr .r7 = P)
    (h6 : s.gpr .r6 = C) (h9 : s.gpr .r9 = BitVec.ofNat 32 j) :
    WP isa (.block (K.atU .r0 .r6 .r9 ++ ([.mov .r1 (.imm (BitVec.ofNat 32 K.uLen)),
      .mov .r2 (.imm (BitVec.ofNat 32 K.du))] : List Instr) ++ slotAt .r3 .r9 (oPoly K.k))) s fun s' =>
      VG.Proof.MlKem.Arm.Only s s' ∧ s'.gpr .r0 = C + BitVec.ofNat 32 j * BitVec.ofNat 32 K.uLen ∧
        s'.gpr .r1 = BitVec.ofNat 32 (32 * K.du) ∧ s'.gpr .r2 = BitVec.ofNat 32 K.du ∧
        s'.gpr .r3 = P + BitVec.ofNat 32 j <<< 10 + BitVec.ofNat 32 (oPoly K.k) := by
  have e1 := hK.encU
  have e2 := hK.encDu
  have e3 : encodable (BitVec.ofNat 32 (oPoly K.k)) = true := hK.enc (by omega)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.Arm.atU_ok hK (d := .r0) (by ddecide) s) fun s₁ ⟨a0, o₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  have g7 : s₁.gpr .r7 = P := by rw [o₁ .r7 (by ddecide), h7]
  have g9 : s₁.gpr .r9 = BitVec.ofNat 32 j := by rw [o₁ .r9 (by ddecide), h9]
  have hb : WP isa (.block ([.mov .r1 (.imm (BitVec.ofNat 32 K.uLen)), .mov .r2 (.imm (BitVec.ofNat 32 K.du))] :
      List Instr)) s₁ fun s₂ => s₂.gpr .r1 = BitVec.ofNat 32 K.uLen ∧ s₂.gpr .r2 = BitVec.ofNat 32 K.du ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧
      s₂.sp = s₁.sp := by
    run_block [e1, e2]
    exact ⟨trivial, trivial, fun r h1 h2 => by rw [ite_eq_right h2, ite_eq_right h1], trivial⟩
  refine WP.mono hb fun s₂ ⟨a1, a2, o₂, m₂, rd₂, wr₂, sp₂⟩ => ?_
  have g7' : s₂.gpr .r7 = P := by rw [o₂ .r7 (by ddecide) (by ddecide), g7]
  have g9' : s₂.gpr .r9 = BitVec.ofNat 32 j := by rw [o₂ .r9 (by ddecide) (by ddecide), g9]
  run_block [slotAt, ptrTo, e3, g7', g9']
  refine ⟨⟨fun r hr hl => ?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁]⟩,
    by rw [o₂ .r0 (by ddecide) (by ddecide), a0, h6, h9], by rw [a1], by rw [a2], trivial⟩
  obtain ⟨m0, m1, m2, m3, -⟩ := VG.Proof.MlKem.Arm.pres_ne hr hl
  show (if r = .r3 then _ else if r = .r3 then _ else s₂.gpr r) = s.gpr r
  rw [ite_eq_right m3, ite_eq_right m3, o₂ r m1 m2, o₁ r m0]

/-- `û` for the first `j` rows, from `s₁`. -/
structure UInv (K : KemLay) (s₀ s₁ : State) (j : Nat) (s : State) : Prop where
  kx : VG.Proof.MlKem.Arm.KeptX [.r9] ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).RL [(0, oPoly K.k, 1024 * K.k), (0, K.oNtt, 1024)]) s₁ s
  r9 : s.gpr .r9 = BitVec.ofNat 32 j
  u : ∀ i < j, PolyIs s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 (oPoly (K.k + i))) (ntt (VG.Proof.MlKem.KPke.dcU K.p (VG.Proof.MlKem.Arm.Decaps.CT K s₀) i))

/-- In row `j` of `û`, from `s`, after the decompression. -/
structure UB (K : KemLay) (s₀ : State) (j : Nat) (s : State) (s' : State) : Prop where
  kx : VG.Proof.MlKem.Arm.KeptX [] ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).RL [(0, oPoly (K.k + j), 1024)]) s s'
  p : PolyIs s'.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 (oPoly (K.k + j))) (VG.Proof.MlKem.KPke.dcU K.p (VG.Proof.MlKem.Arm.Decaps.CT K s₀) j)

/-- Polynomial `k + j` of `û` is in what the decoding of `û` writes, apart from the others. -/
abbrev USlots (K : KemLay) : Prop := ∀ j < K.k,
    [((0 : Nat), oPoly (K.k + j), (1024 : Nat)), (0, K.oNtt, 1024)].all
      (fun w => [(0, oPoly K.k, 1024 * K.k), (0, K.oNtt, 1024)].any (VG.Proof.MlKem.Arm.subB0 w)) = true ∧
    (∀ i < K.k, i ≠ j → [((0 : Nat), oPoly (K.k + j), (1024 : Nat)), (0, K.oNtt, 1024)].all
      (VG.Proof.MlKem.Arm.sep0 (oPoly (K.k + i)) 1024) = true)

theorem u_facts {K : KemLay} (hK : K.WF) {j : Nat} (hj : j < K.k) :
    [((0 : Nat), oPoly (K.k + j), (1024 : Nat)), (0, K.oNtt, 1024)].all
      (fun w => [(0, oPoly K.k, 1024 * K.k), (0, K.oNtt, 1024)].any (VG.Proof.MlKem.Arm.subB0 w)) = true ∧
    (∀ i < K.k, i ≠ j → [((0 : Nat), oPoly (K.k + j), (1024 : Nat)), (0, K.oNtt, 1024)].all
      (VG.Proof.MlKem.Arm.sep0 (oPoly (K.k + i)) 1024) = true) ∧
    [((0 : Nat), oPoly K.k, 1024 * K.k), (0, K.oNtt, 1024)].all (VG.Proof.MlKem.Arm.sep0 oCin K.ctLen) = true := by
  have := hK.ct
  have u : VG.Proof.MlKem.Arm.Decaps.USlots K := (by decide : ∀ k < 5, USlots (kOf k)) K.k (by have := hK.k4; omega)
  exact ⟨(u j hj).1, (u j hj).2, by kdecide⟩

section
variable {K : KemLay} {s₀ : State} (hp : VG.Proof.MlKem.Arm.Decaps.Pre K s₀) {s₁ : State} (h₁ : VG.Proof.MlKem.Arm.Decaps.DD K s₀ s₁) {j : Nat} (hj : j < K.k)
  {s : State} (h : VG.Proof.MlKem.Arm.Decaps.UInv K s₀ s₁ j s)
include hp h₁ hj h

theorem u1_ok : WP isa (.block (K.atU .r0 .r6 .r9 ++ ([.mov .r1 (.imm (BitVec.ofNat 32 K.uLen)),
      .mov .r2 (.imm (BitVec.ofNat 32 K.du))] : List Instr) ++ slotAt .r3 .r9 (oPoly K.k))) s fun s' =>
      VG.Proof.MlKem.Arm.Only s s' ∧ s'.gpr .r0 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 (oCin + K.uLen * j) ∧
        s'.gpr .r1 = BitVec.ofNat 32 (32 * K.du) ∧ s'.gpr .r2 = BitVec.ofNat 32 K.du ∧
        s'.gpr .r3 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 (oPoly (K.k + j)) := by
  have hK := hp.wf
  have hc := h.kx.ctx (by ddecide) h₁.env.ctx
  have g6 : s.gpr .r6 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 oCin := by
    rw [h.kx.cs .r6 (by ddecide) (by ddecide) (by ddecide), h₁.r6]
  refine WP.mono (VG.Proof.MlKem.Arm.Decaps.uArgs_ok hK hc.r7 g6 h.r9) fun s' ⟨o, a0, a1, a2, a3⟩ => ⟨o, ?_, a1, a2, ?_⟩
  · rw [a0, VG.Proof.MlKem.Arm.atU_eq, ptr_add_add32]
  · rw [a3, VG.Proof.MlKem.Arm.slot_eq _ (by offs), show oPoly K.k + 1024 * j = oPoly (K.k + j) by offs]

theorem u2_ok {s' : State} (o : VG.Proof.MlKem.Arm.Only s s')
    (a0 : s'.gpr .r0 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 (oCin + K.uLen * j))
    (a1 : s'.gpr .r1 = BitVec.ofNat 32 (32 * K.du)) (a2 : s'.gpr .r2 = BitVec.ofNat 32 K.du)
    (a3 : s'.gpr .r3 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 (oPoly (K.k + j))) :
    WP isa K.callDU s' (VG.Proof.MlKem.Arm.Decaps.UB K s₀ j s) := by
  have hL := VG.Proof.MlKem.Arm.Decaps.lay_ok hp
  have hK := hp.wf
  have hc := (h.kx.ctx (by ddecide) h₁.env.ctx).only o
  obtain ⟨-, -, c3⟩ := VG.Proof.MlKem.Arm.Decaps.u_facts hK hj
  have u1 := Enc.uSlot (K := K) hj
  have cin := hK.cin
  have hcb : bytesAt s'.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 (oCin + K.uLen * j)) (32 * K.du) =
      (((VG.Proof.MlKem.Arm.Decaps.CT K s₀).drop (K.uLen * j)).take K.uLen) := by
    rw [o.mem, ← h₁.c, ← Lay.bytes_keep hL h.kx.frame (h₁.env.ctx.sepAll0 (by simp only [oCin] at cin ⊢; omega) c3)
      (by simp only [oCin] at cin; omega), bytesAt_slice _ _ u1, add_ofNat_add]
  refine hp.calls.du hL a0 a1 a2 a3 (.inl rfl) (hc.sep00 (by simp only [oCin, KemLay.uLen] at cin u1 ⊢; omega)
    (by offs) (by have := hK.ct; simp only [oCin, KemLay.uLen, KemLay.oCt, oPoly] at cin u1 this ⊢; omega))
    (VG.Proof.MlKem.Arm.mem_rd_wr hc.buf0) hc.buf0 fun s'' k p => ⟨(o.x _ _).trans (k.x _), ?_⟩
  rw [hcb] at p; exact p

/-- In row `j` of `û`, from `s`, after the NTT. -/
structure UD (K : KemLay) (s₀ : State) (j : Nat) (s : State) (s' : State) : Prop where
  kx : VG.Proof.MlKem.Arm.KeptX [] ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).RL [(0, oPoly (K.k + j), 1024), (0, K.oNtt, 1024)]) s s'
  p : PolyIs s'.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 (oPoly (K.k + j))) (ntt (VG.Proof.MlKem.KPke.dcU K.p (VG.Proof.MlKem.Arm.Decaps.CT K s₀) j))

theorem u3_ok {s₂ : State} (r : VG.Proof.MlKem.Arm.Decaps.UB K s₀ j s s₂) :
    WP isa (.block (slotAt .r0 .r9 (oPoly K.k) ++ ([ptrTo .r1 .r7 K.oNtt] : List Instr))) s₂ fun s₃ =>
      VG.Proof.MlKem.Arm.Decaps.UB K s₀ j s s₃ ∧ s₃.gpr .r0 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 (oPoly (K.k + j)) ∧
        s₃.gpr .r1 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 K.oNtt := by
  have hK := hp.wf
  have hc₂ := r.kx.ctx (by ddecide) (h.kx.ctx (by ddecide) h₁.env.ctx)
  have g9 : s₂.gpr .r9 = BitVec.ofNat 32 j := by
    rw [r.kx.cs .r9 (by ddecide) (by ddecide) (by simp), h.r9]
  refine WP.mono (VG.Proof.MlKem.Arm.nttArgs_ok hK hc₂.r7 g9) fun s₃ ⟨o, a0, a1⟩ =>
    ⟨⟨r.kx.trans (o.x _ _), by rw [o.mem]; exact r.p⟩, ?_, a1⟩
  rw [a0, VG.Proof.MlKem.Arm.slot_eq _ (by offs), show oPoly K.k + 1024 * j = oPoly (K.k + j) by offs]

theorem u4_ok {s₃ : State} (r : VG.Proof.MlKem.Arm.Decaps.UB K s₀ j s s₃)
    (a0 : s₃.gpr .r0 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 (oPoly (K.k + j)))
    (a1 : s₃.gpr .r1 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 K.oNtt) : WP isa callNtt s₃ (VG.Proof.MlKem.Arm.Decaps.UD K s₀ j s) := by
  have hK := hp.wf
  have hc₃ := r.kx.ctx (by ddecide) (h.kx.ctx (by ddecide) h₁.env.ctx)
  exact VG.Proof.MlKem.Arm.nttL (VG.Proof.MlKem.Arm.Decaps.lay_ok hp) a0 a1 (hc₃.sep00 (by offs) (by offs) (by offs)) hc₃.buf0 hc₃.buf0 r.p fun s₄ k p =>
    ⟨(r.kx.monoL (by simp)).trans (k.x _), p⟩

theorem u5_ok {s₄ : State} (r : VG.Proof.MlKem.Arm.Decaps.UD K s₀ j s s₄) :
    WP isa (.block (count .r9 K.k)) s₄ fun s' => VG.Proof.MlKem.Arm.Decaps.UInv K s₀ s₁ (j + 1) s' ∧ s'.z = decide (j + 1 = K.k) := by
  have hK := hp.wf
  have k4 := hK.k4
  obtain ⟨c1, c2, -⟩ := VG.Proof.MlKem.Arm.Decaps.u_facts hK hj
  have g9 : s₄.gpr .r9 = BitVec.ofNat 32 j := by
    rw [r.kx.cs .r9 (by ddecide) (by ddecide) (by simp), h.r9]
  refine WP.mono (VG.Proof.MlKem.Arm.count_ok (by omega) (by omega) (by kenc) g9) fun s' ⟨k', g', z'⟩ => ⟨⟨?_, g', fun i hi => ?_⟩, z'⟩
  · exact h.kx.trans (((r.kx.weaken (by simp)).trans (k'.mono (fun _ h => absurd h List.not_mem_nil))).subL
      h₁.env.ctx c1)
  · by_cases e : i = j
    · subst e
      exact polyIs_frame k'.frame (fun _ h => absurd h List.not_mem_nil) r.p
    · exact polyIs_frame k'.frame (fun _ h => absurd h List.not_mem_nil)
        (Lay.polyIs_keep (VG.Proof.MlKem.Arm.Decaps.lay_ok hp) r.kx.frame (h₁.env.ctx.sepAll0 (by offs) (c2 i (by omega) e)) (h.u i (by omega)))

theorem decU_step : WP isa K.decUBody s fun s' => VG.Proof.MlKem.Arm.Decaps.UInv K s₀ s₁ (j + 1) s' ∧ s'.z = decide (j + 1 = K.k) :=
  WP.seq (WP.mono (VG.Proof.MlKem.Arm.Decaps.u1_ok hp h₁ hj h) fun _ ⟨o, a0, a1, a2, a3⟩ =>
    WP.seq (WP.mono (VG.Proof.MlKem.Arm.Decaps.u2_ok hp h₁ hj h o a0 a1 a2 a3) fun _ r₂ =>
    WP.seq (WP.mono (VG.Proof.MlKem.Arm.Decaps.u3_ok hp h₁ hj h r₂) fun _ ⟨r₃, b0, b1⟩ =>
    WP.seq (WP.mono (VG.Proof.MlKem.Arm.Decaps.u4_ok hp h₁ hj h r₃ b0 b1) fun _ r₄ => VG.Proof.MlKem.Arm.Decaps.u5_ok hp h₁ hj h r₄))))

end


/-! ## The rest of K-PKE.Decrypt -/

section
variable {K : KemLay} {s₀ : State} (hp : VG.Proof.MlKem.Arm.Decaps.Pre K s₀)
include hp

omit hp in
theorem dU_init {s₁ : State} : WP isa (.block [.mov .r9 (.imm 0)]) s₁ (VG.Proof.MlKem.Arm.Decaps.UInv K s₀ s₁ 0) :=
  WP.mono (VG.Proof.MlKem.Arm.movc_ok .r9 (N := 0) (by ddecide)) fun _ ⟨k, g, _⟩ =>
    ⟨k.mono (fun _ h => absurd h List.not_mem_nil), g, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩

theorem dU_done {s₁ s : State} (h₁ : VG.Proof.MlKem.Arm.Decaps.DD K s₀ s₁) (h : VG.Proof.MlKem.Arm.Decaps.UInv K s₀ s₁ K.k s) : VG.Proof.MlKem.Arm.Decaps.DD K s₀ s := by
  have hK := hp.wf
  exact h₁.keep hp h.kx (by simp) (VG.Proof.MlKem.Arm.Decaps.dec_f hp.wf).1

theorem dT_pre {s : State} (h : VG.Proof.MlKem.Arm.Decaps.DD K s₀ s) :
    VG.Proof.MlKem.Arm.Ctx (VG.Proof.MlKem.Arm.Decaps.lay s₀ K) s ∧ s.gpr .r4 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 2 + BitVec.ofNat 32 0 ∧
      VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).sizes (2, 0, 384 * K.k) [(0, 2048, 1024 * K.k)] = true ∧ (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).buf 2 ∈ s.rd ++ s.wr := by
  have hK := hp.wf
  obtain ⟨-, -, w2, -, -⟩ := VG.Proof.MlKem.Arm.Decaps.buf_wr hp
  exact ⟨h.env.ctx, by rw [h.r4, show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero]; rfl, by ddecide,
    by rw [h.env.rd, h.env.wr]; exact w2⟩

/-- `ŝ` of `dk`. -/
abbrev sHat (K : KemLay) (s₀ : State) : Nat → VG.Spec.MlKem.Poly := VG.Proof.MlKem.dcS (VG.Proof.MlKem.KPke.dkPke K.p (VG.Proof.MlKem.Arm.Decaps.DK K s₀))

/-- `NTT(u')` of `c`. -/
abbrev uHat (K : KemLay) (s₀ : State) (i : Nat) : VG.Spec.MlKem.Poly := ntt (VG.Proof.MlKem.KPke.dcU K.p (VG.Proof.MlKem.Arm.Decaps.CT K s₀) i)

theorem dT_done {s₂ s : State} (h₂ : VG.Proof.MlKem.Arm.Decaps.DD K s₀ s₂)
    (hu : ∀ i < K.k, PolyIs s₂.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 (oPoly (K.k + i))) (VG.Proof.MlKem.Arm.Decaps.uHat K s₀ i))
    (h : VG.Proof.MlKem.Arm.DecInv K (VG.Proof.MlKem.Arm.Decaps.lay s₀ K) 2 0 s₂ K.k s) :
    VG.Proof.MlKem.Arm.Decaps.DD K s₀ s ∧ (∀ k < K.k, PolyIs s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 (oPoly k)) (VG.Proof.MlKem.Arm.Decaps.sHat K s₀ k)) ∧
      ∀ i < K.k, PolyIs s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 (oPoly (K.k + i))) (VG.Proof.MlKem.Arm.Decaps.uHat K s₀ i) := by
  have hL := VG.Proof.MlKem.Arm.Decaps.lay_ok hp
  have hK := hp.wf
  refine ⟨h₂.keep hp h.kx (by simp) (VG.Proof.MlKem.Arm.Decaps.dec_f hp.wf).2.1, fun k hk => ?_, fun i hi => ?_⟩
  · have := h.t k hk
    have e : bytesAt s₂.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 2 (0 + 384 * k)) 384 = ((VG.Proof.MlKem.Arm.Decaps.DK K s₀).drop (384 * k)).take 384 := by
      have dk : bytesAt s₂.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 2 0) K.dkLen = VG.Proof.MlKem.Arm.Decaps.DK K s₀ := h₂.env.dk
      rw [← dk, bytesAt_slice _ _ (by simp only [KemLay.dkLen]; omega), add_ofNat_add]
    rw [e] at this
    show PolyIs _ _ (decode12 ((((VG.Proof.MlKem.Arm.Decaps.DK K s₀).take (384 * K.k)).drop (384 * k)).take 384))
    rw [VG.Proof.MlKem.slice_take _ (by omega)]; exact this
  · exact Lay.polyIs_keep hL h.kx.frame (h₂.env.ctx.sepAll0 (by offs) (by kdecide)) (hu i hi)

/-- After `dot`, with the sum `f`. -/
abbrev DV (K : KemLay) (s₀ : State) (f : VG.Spec.MlKem.Poly) (s : State) : Prop :=
  VG.Proof.MlKem.Arm.Decaps.DD K s₀ s ∧ PolyIs s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 K.oAcc) f

theorem dDot_ok {s : State} (h : VG.Proof.MlKem.Arm.Decaps.DD K s₀ s) (hs : ∀ k < K.k, PolyIs s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 (oPoly k)) (VG.Proof.MlKem.Arm.Decaps.sHat K s₀ k))
    (hu : ∀ i < K.k, PolyIs s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 (oPoly (K.k + i))) (VG.Proof.MlKem.Arm.Decaps.uHat K s₀ i)) :
    WP isa K.dot s (VG.Proof.MlKem.Arm.Decaps.DV K s₀ (VG.Proof.MlKem.KPke.dotK (VG.Proof.MlKem.Arm.Decaps.sHat K s₀) (VG.Proof.MlKem.Arm.Decaps.uHat K s₀) K.k)) := by
  have hK := hp.wf
  exact WP.mono (VG.Proof.MlKem.Arm.dot_ok hK h.env.ctx hs hu) fun _ ⟨k, p⟩ => ⟨h.keep hp k (by simp) (VG.Proof.MlKem.Arm.Decaps.dec_f hp.wf).2.2.1, p⟩

theorem dArgs_ok {s : State} {f : VG.Spec.MlKem.Poly} (h : VG.Proof.MlKem.Arm.Decaps.DV K s₀ f s) {o o' : Nat} (he : encodable (BitVec.ofNat 32 o) = true)
    (he' : encodable (BitVec.ofNat 32 o') = true) :
    WP isa (.block [ptrTo .r0 .r7 o, ptrTo .r1 .r7 o']) s fun s' => (VG.Proof.MlKem.Arm.Decaps.DV K s₀ f s' ∧ s'.mem = s.mem) ∧
      s'.gpr .r0 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 o ∧ s'.gpr .r1 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 o' :=
  WP.mono (VG.Proof.MlKem.Arm.accArgs_ok h.1.env.ctx.r7 he he') fun _ ⟨o₁, a0, a1⟩ =>
    ⟨⟨⟨h.1.keep hp (xs := []) (W := []) (o₁.x _ _) (by simp) rfl, by rw [o₁.mem]; exact h.2⟩, o₁.mem⟩, a0, a1⟩

theorem dInv_ok {s : State} {f : VG.Spec.MlKem.Poly} (h : VG.Proof.MlKem.Arm.Decaps.DV K s₀ f s) (a0 : s.gpr .r0 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 K.oAcc)
    (a1 : s.gpr .r1 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 K.oNtt) : WP isa callNttInv s (VG.Proof.MlKem.Arm.Decaps.DV K s₀ (nttInv f)) := by
  have hK := hp.wf
  have hc := h.1.env.ctx
  exact VG.Proof.MlKem.Arm.nttInvL (VG.Proof.MlKem.Arm.Decaps.lay_ok hp) a0 a1 (hc.sep00 (by offs) (by offs) (by offs)) hc.buf0 hc.buf0 h.2
    fun s' k p => ⟨h.1.keep hp (k.x []) (by simp) (VG.Proof.MlKem.Arm.Decaps.dec_f hp.wf).2.2.2.1, p⟩

omit hp in
theorem vDArgs_ok (hK : K.WF) {s : State} {P C : BitVec 32} (h7 : s.gpr .r7 = P) (h6 : s.gpr .r6 = C) :
    WP isa (.block [ptrTo .r0 .r6 (K.uLen * K.k), .mov .r1 (.imm (BitVec.ofNat 32 K.vLen)),
      .mov .r2 (.imm (BitVec.ofNat 32 K.dv)), ptrTo .r3 .r7 (oPoly (3 * K.k))]) s
      fun s' => VG.Proof.MlKem.Arm.Only s s' ∧ s'.gpr .r0 = C + BitVec.ofNat 32 (K.uLen * K.k) ∧
        s'.gpr .r1 = BitVec.ofNat 32 (32 * K.dv) ∧
        s'.gpr .r2 = BitVec.ofNat 32 K.dv ∧ s'.gpr .r3 = P + BitVec.ofNat 32 (oPoly (3 * K.k)) := by
  have e1 := hK.encVo
  have e2 := hK.encV
  have e3 := hK.encDv
  have e4 : encodable (BitVec.ofNat 32 (oPoly (3 * K.k))) = true := hK.enc (by omega)
  run_block [ptrTo, e1, e2, e3, e4, h7, h6]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, m2, m3, -⟩ := VG.Proof.MlKem.Arm.pres_ne hr hl
  simp only [m0, m1, m2, m3, ite_false]

theorem dV1_ok {s : State} {f : VG.Spec.MlKem.Poly} (h : VG.Proof.MlKem.Arm.Decaps.DV K s₀ f s) :
    WP isa (.block [ptrTo .r0 .r6 (K.uLen * K.k), .mov .r1 (.imm (BitVec.ofNat 32 K.vLen)),
      .mov .r2 (.imm (BitVec.ofNat 32 K.dv)), ptrTo .r3 .r7 (oPoly (3 * K.k))]) s
      fun s' => VG.Proof.MlKem.Arm.Decaps.DV K s₀ f s' ∧ s'.gpr .r0 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 (oCin + K.uLen * K.k) ∧
        s'.gpr .r1 = BitVec.ofNat 32 (32 * K.dv) ∧ s'.gpr .r2 = BitVec.ofNat 32 K.dv ∧
        s'.gpr .r3 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 (oPoly (3 * K.k)) :=
  WP.mono (VG.Proof.MlKem.Arm.Decaps.vDArgs_ok hp.wf h.1.env.ctx.r7 h.1.r6) fun _ ⟨o, a0, a1, a2, a3⟩ =>
    ⟨⟨h.1.keep hp (xs := []) (W := []) (o.x _ _) (by simp) rfl, by rw [o.mem]; exact h.2⟩,
      by rw [a0, ptr_add_add32], a1, a2, a3⟩

theorem dV2_ok {s : State} {f : VG.Spec.MlKem.Poly} (h : VG.Proof.MlKem.Arm.Decaps.DV K s₀ f s)
    (a0 : s.gpr .r0 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 (oCin + K.uLen * K.k))
    (a1 : s.gpr .r1 = BitVec.ofNat 32 (32 * K.dv))
    (a2 : s.gpr .r2 = BitVec.ofNat 32 K.dv) (a3 : s.gpr .r3 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 (oPoly (3 * K.k))) :
    WP isa K.callDU s fun s' => VG.Proof.MlKem.Arm.Decaps.DV K s₀ f s' ∧
      PolyIs s'.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 (oPoly (3 * K.k))) (VG.Proof.MlKem.KPke.dcV K.p (VG.Proof.MlKem.Arm.Decaps.CT K s₀)) := by
  have hK := hp.wf
  have hc := h.1.env.ctx
  have cin := hK.cin
  have ect : K.ctLen = K.uLen * K.k + 32 * K.dv := rfl
  have hcb : bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 (oCin + K.uLen * K.k)) (32 * K.dv) =
      ((VG.Proof.MlKem.Arm.Decaps.CT K s₀).drop (K.uLen * K.k)).take (32 * K.dv) := by
    rw [← h.1.c, bytesAt_slice _ _ (by omega), add_ofNat_add]
  refine hp.calls.du (VG.Proof.MlKem.Arm.Decaps.lay_ok hp) a0 a1 a2 a3 (.inr rfl) (hc.sep00 (by simp only [oCin] at cin ⊢; omega) (by offs)
    (by have := hK.k4; simp only [oCin, oPoly] at cin ⊢; omega))
    (VG.Proof.MlKem.Arm.mem_rd_wr hc.buf0) hc.buf0 fun s' k p => ⟨⟨h.1.keep hp (k.x []) (by simp) (VG.Proof.MlKem.Arm.Decaps.dec_f hp.wf).2.2.2.2.1, ?_⟩, ?_⟩
  · have := hK.k4
    refine Lay.polyIs_keep (VG.Proof.MlKem.Arm.Decaps.lay_ok hp) k.frame (hc.sepAll0 (o := K.oAcc) (l := 1024) ?_ ?_) h.2
    · simp only [KemLay.oAcc, oPoly]; omega_using [this]
    · simp only [List.all_cons, List.all_nil, Bool.and_true, VG.Proof.MlKem.Arm.sep0, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq, KemLay.oAcc, oPoly, true_and]
      omega_using [this]
  · rw [hcb] at p; exact p

theorem dV4_ok {s : State} {f : VG.Spec.MlKem.Poly} (h : VG.Proof.MlKem.Arm.Decaps.DV K s₀ f s)
    (hv : PolyIs s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 (oPoly (3 * K.k))) (VG.Proof.MlKem.KPke.dcV K.p (VG.Proof.MlKem.Arm.Decaps.CT K s₀)))
    (a0 : s.gpr .r0 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 (oPoly (3 * K.k)))
    (a1 : s.gpr .r1 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 K.oAcc) :
    WP isa callSub s fun s' => VG.Proof.MlKem.Arm.Decaps.DD K s₀ s' ∧
      PolyIs s'.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 (oPoly (3 * K.k))) (VG.Spec.MlKem.sub (VG.Proof.MlKem.KPke.dcV K.p (VG.Proof.MlKem.Arm.Decaps.CT K s₀)) f) := by
  have hK := hp.wf
  have hc := h.1.env.ctx
  exact VG.Proof.MlKem.Arm.subL (VG.Proof.MlKem.Arm.Decaps.lay_ok hp) a0 a1 (hc.sep00 (by offs) (by offs) (by offs)) hc.buf0 (VG.Proof.MlKem.Arm.mem_rd_wr hc.buf0) hv h.2
    fun s' k p => ⟨h.1.keep hp (k.x []) (by simp) (VG.Proof.MlKem.Arm.Decaps.dec_f hp.wf).2.2.2.2.1, p⟩

omit hp in
theorem mArgs_ok (hK : K.WF) {s : State} {P : BitVec 32} (h7 : s.gpr .r7 = P) :
    WP isa (.block [ptrTo .r0 .r7 (oPoly (3 * K.k)), .mov .r1 (.imm 1), ptrTo .r2 .r7 oMsg, .mov .r3 (.imm 32)]) s
      fun s' => VG.Proof.MlKem.Arm.Only s s' ∧ s'.gpr .r0 = P + BitVec.ofNat 32 (oPoly (3 * K.k)) ∧ s'.gpr .r1 = BitVec.ofNat 32 1 ∧
        s'.gpr .r2 = P + BitVec.ofNat 32 oMsg ∧ s'.gpr .r3 = BitVec.ofNat 32 (32 * 1) := by
  have e1 : encodable (BitVec.ofNat 32 (oPoly (3 * K.k))) = true := hK.enc (by omega)
  have e2 : encodable (1 : BitVec 32) = true := by decide
  have e3 : encodable (BitVec.ofNat 32 oMsg) = true := by decide
  have e4 : encodable (32 : BitVec 32) = true := by decide
  run_block [ptrTo, e1, e2, e3, e4, h7]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, m2, m3, -⟩ := VG.Proof.MlKem.Arm.pres_ne hr hl
  simp only [m0, m1, m2, m3, ite_false]

theorem dM1_ok {s : State} {g : VG.Spec.MlKem.Poly} (h : VG.Proof.MlKem.Arm.Decaps.DD K s₀ s) (hg : PolyIs s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 (oPoly (3 * K.k))) g) :
    WP isa (.block [ptrTo .r0 .r7 (oPoly (3 * K.k)), .mov .r1 (.imm 1), ptrTo .r2 .r7 oMsg, .mov .r3 (.imm 32)]) s
      fun s' => (VG.Proof.MlKem.Arm.Decaps.DD K s₀ s' ∧ PolyIs s'.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 (oPoly (3 * K.k))) g) ∧
        s'.gpr .r0 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 (oPoly (3 * K.k)) ∧ s'.gpr .r1 = BitVec.ofNat 32 1 ∧
        s'.gpr .r2 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 oMsg ∧ s'.gpr .r3 = BitVec.ofNat 32 (32 * 1) :=
  WP.mono (VG.Proof.MlKem.Arm.Decaps.mArgs_ok hp.wf h.env.ctx.r7) fun _ ⟨o, a0, a1, a2, a3⟩ =>
    ⟨⟨h.keep hp (xs := []) (W := []) (o.x _ _) (by simp) rfl, by rw [o.mem]; exact hg⟩, a0, a1, a2, a3⟩

theorem dM2_ok {s : State} {g : VG.Spec.MlKem.Poly} (h : VG.Proof.MlKem.Arm.Decaps.DD K s₀ s ∧ PolyIs s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 (oPoly (3 * K.k))) g)
    (a0 : s.gpr .r0 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 (oPoly (3 * K.k))) (a1 : s.gpr .r1 = BitVec.ofNat 32 1)
    (a2 : s.gpr .r2 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 oMsg) (a3 : s.gpr .r3 = BitVec.ofNat 32 (32 * 1)) :
    WP isa callCompress s fun s' => VG.Proof.MlKem.Arm.Decaps.DD K s₀ s' ∧ bytesAt s'.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 oMsg) 32 = compressEncode 1 g := by
  have hK := hp.wf
  have hc := h.1.env.ctx
  exact VG.Proof.MlKem.Arm.compressL (VG.Proof.MlKem.Arm.Decaps.lay_ok hp) a0 a1 a2 a3 (by ddecide) (hc.sep00 (by offs) (by offs) (by offs)) (VG.Proof.MlKem.Arm.mem_rd_wr hc.buf0)
    hc.buf0 h.2 fun s' k p => ⟨h.1.keep hp (k.x []) (by simp) (VG.Proof.MlKem.Arm.Decaps.dec_f hp.wf).2.2.2.2.2.1, p⟩

end

/-- `m'`. -/
abbrev MM (K : KemLay) (s₀ : State) : List Byte := VG.Proof.MlKem.KPke.decM K.p (VG.Proof.MlKem.Arm.Decaps.DK K s₀) (VG.Proof.MlKem.Arm.Decaps.CT K s₀)

theorem decrypt_ok {K : KemLay} {s₀ s₁ : State} (hp : VG.Proof.MlKem.Arm.Decaps.Pre K s₀) (h₁ : VG.Proof.MlKem.Arm.Decaps.DD K s₀ s₁) :
    WP isa K.decrypt s₁ fun s => VG.Proof.MlKem.Arm.Decaps.DD K s₀ s ∧ bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 oMsg) 32 = VG.Proof.MlKem.Arm.Decaps.MM K s₀ := by
  have hK := hp.wf
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Decaps.dU_init (K := K) (s₀ := s₀)) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (wp_loop_ne (VG.Proof.MlKem.Arm.Decaps.UInv K s₀ s₁) (N := K.k) hK.k1 (fun j hj s h => VG.Proof.MlKem.Arm.Decaps.decU_step hp h₁ hj h)
    (fun _ h => h) h₂) fun s₃ h₃ => ?_)
  have d₃ := VG.Proof.MlKem.Arm.Decaps.dU_done hp h₁ h₃
  obtain ⟨hc₃, g4, hs₃, hr₃⟩ := VG.Proof.MlKem.Arm.Decaps.dT_pre hp d₃
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.decT_init (K := K) (L := VG.Proof.MlKem.Arm.Decaps.lay s₀ K) (i := 2) (o := 0)) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.decT_loop hK hc₃ g4 hs₃ hr₃ h₄) fun s₅ h₅ => ?_)
  obtain ⟨d₅, ŝ₅, û₅⟩ := VG.Proof.MlKem.Arm.Decaps.dT_done hp d₃ h₃.u h₅
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Decaps.dDot_ok hp d₅ ŝ₅ û₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Decaps.dArgs_ok hp h₆ (o := K.oAcc) (o' := K.oNtt) (by kenc) (by kenc)) fun s₇ ⟨h₇, a0, a1⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Decaps.dInv_ok hp h₇.1 a0 a1) fun s₈ h₈ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Decaps.dV1_ok hp h₈) fun s₉ ⟨h₉, b0, b1, b2, b3⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Decaps.dV2_ok hp h₉ b0 b1 b2 b3) fun s₁₀ ⟨h₁₀, v₁₀⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Decaps.dArgs_ok hp h₁₀ (o := oPoly (3 * K.k)) (o' := K.oAcc) (by kenc) (by kenc))
    fun s₁₁ ⟨h₁₁, c0, c1⟩ => ?_)
  have v₁₁ : PolyIs s₁₁.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 (oPoly (3 * K.k))) (VG.Proof.MlKem.KPke.dcV K.p (VG.Proof.MlKem.Arm.Decaps.CT K s₀)) := by
    rw [h₁₁.2]; exact v₁₀
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Decaps.dV4_ok hp h₁₁.1 v₁₁ c0 c1) fun s₁₂ ⟨h₁₂, w₁₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Decaps.dM1_ok hp h₁₂ w₁₂) fun s₁₃ ⟨h₁₃, e0, e1, e2, e3⟩ => ?_)
  refine WP.mono (VG.Proof.MlKem.Arm.Decaps.dM2_ok hp h₁₃ e0 e1 e2 e3) fun s ⟨h, m⟩ => ⟨h, m.trans ?_⟩
  show _ = kpkeDecrypt K.p (VG.Proof.MlKem.KPke.dkPke K.p (VG.Proof.MlKem.Arm.Decaps.DK K s₀)) (VG.Proof.MlKem.Arm.Decaps.CT K s₀)
  rw [VG.Proof.MlKem.KPke.kpkeDecrypt_eq]


/-! ## The hashes -/

theorem pieceD {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.Decaps.Pre K s₀) (h : VG.Proof.MlKem.Arm.Decaps.DD K s₀ s) {p : Piece} {w : Bool}
    (hb : p.base = .r4 ∨ p.base = .r7) (hw : w = true → p.base = .r7)
    (hoe : encodable (BitVec.ofNat 32 p.off) = true) (hle : encodable (BitVec.ofNat 32 p.len) = true)
    (hpos : 0 < p.len) (hlt : p.off + p.len < 2 ^ 32)
    (hsep : VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.Decaps.dSz K) (VG.Proof.MlKem.Arm.Decaps.didx p.base, p.off, p.len) VG.Proof.MlKem.Arm.kRegs = true) :
    VG.Proof.MlKem.Arm.PieceOk (VG.Proof.MlKem.Arm.Decaps.lay s₀ K) VG.Proof.MlKem.Arm.Decaps.didx s w p := by
  obtain ⟨w0, -, w2, -, -⟩ := VG.Proof.MlKem.Arm.Decaps.buf_wr hp
  rw [← h.env.wr] at w0
  rw [← h.env.wr, ← h.env.rd] at w2
  refine ⟨?_, ?_, hoe, hle, hpos, hlt, hsep, ?_⟩
  · rcases hb with e | e <;> rw [e] <;> decide
  · rcases hb with e | e <;> rw [e]
    · exact h.r4
    · exact h.env.ctx.r7
  · cases w
    · simp only [Bool.false_eq_true, ite_false]
      rcases hb with e | e <;> rw [e]
      · exact w2
      · exact VG.Proof.MlKem.Arm.mem_rd_wr w0
    · simp only [ite_true]
      rw [hw rfl]; exact w0

section
variable (K : KemLay) (s₀ : State)

/-- `h`, `z` and `ek` of `dk`. -/
abbrev hH : List Byte := VG.Proof.MlKem.KPke.dkH K.p (VG.Proof.MlKem.Arm.Decaps.DK K s₀)
abbrev zZ : List Byte := VG.Proof.MlKem.KPke.dkZ K.p (VG.Proof.MlKem.Arm.Decaps.DK K s₀)
abbrev eK : List Byte := VG.Proof.MlKem.KPke.dkEk K.p (VG.Proof.MlKem.Arm.Decaps.DK K s₀)

/-- `K'` and `r'`, the outputs of `G(m' ‖ h)`, and `K̄ = J(z ‖ c)`. -/
abbrev K1 : List Byte := (G (VG.Proof.MlKem.Arm.Decaps.MM K s₀ ++ VG.Proof.MlKem.Arm.Decaps.hH K s₀)).1
abbrev R1 : List Byte := (G (VG.Proof.MlKem.Arm.Decaps.MM K s₀ ++ VG.Proof.MlKem.Arm.Decaps.hH K s₀)).2
abbrev KB : List Byte := J (VG.Proof.MlKem.Arm.Decaps.zZ K s₀ ++ VG.Proof.MlKem.Arm.Decaps.CT K s₀)

end

theorem dk_slice {K : KemLay} {s₀ s : State} (h : VG.Proof.MlKem.Arm.Decaps.DD K s₀ s) {k : Nat} (hk : k + 32 ≤ K.dkLen) :
    bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 2 k) 32 = ((VG.Proof.MlKem.Arm.Decaps.DK K s₀).drop k).take 32 := by
  have dk : bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 2 0) K.dkLen = VG.Proof.MlKem.Arm.Decaps.DK K s₀ := h.env.dk
  rw [← dk, bytesAt_slice _ _ hk, add_ofNat_add, Nat.zero_add]

theorem hashG_ok {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.Decaps.Pre K s₀) (h : VG.Proof.MlKem.Arm.Decaps.DD K s₀ s) (hm : bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 oMsg) 32 = VG.Proof.MlKem.Arm.Decaps.MM K s₀) :
    WP isa (hash 72 0x06 [⟨.r7, oMsg, 32⟩, ⟨.r4, 768 * K.k + 32, 32⟩] [⟨.r7, oG, 64⟩]) s fun s' =>
      VG.Proof.MlKem.Arm.Decaps.DD K s₀ s' ∧ Frame ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).RL (VG.Proof.MlKem.Arm.kRegs ++ [(0, oG, 64)])) s.mem s'.mem ∧
      bytesAt s'.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 oG) 32 = VG.Proof.MlKem.Arm.Decaps.K1 K s₀ ∧ bytesAt s'.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 oSigma) 32 = VG.Proof.MlKem.Arm.Decaps.R1 K s₀ := by
  have hin : ∀ p ∈ [(⟨.r7, oMsg, 32⟩ : Piece), ⟨.r4, 768 * K.k + 32, 32⟩], VG.Proof.MlKem.Arm.PieceOk (VG.Proof.MlKem.Arm.Decaps.lay s₀ K) VG.Proof.MlKem.Arm.Decaps.didx s false p := by
    intro p hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · exact VG.Proof.MlKem.Arm.Decaps.pieceD hp h (.inr rfl) (by simp) (by ddecide) (by ddecide) (by ddecide) (by ddecide) (VG.Proof.MlKem.Arm.Decaps.dec_p hp.wf).1
    · exact VG.Proof.MlKem.Arm.Decaps.pieceD hp h (.inl rfl) (by simp) hp.wf.encH (by ddecide) (by ddecide) (by ddecide) (VG.Proof.MlKem.Arm.Decaps.dec_p hp.wf).2.1
  have hout : ∀ p ∈ [(⟨.r7, oG, 64⟩ : Piece)], VG.Proof.MlKem.Arm.PieceOk (VG.Proof.MlKem.Arm.Decaps.lay s₀ K) VG.Proof.MlKem.Arm.Decaps.didx s true p := by
    intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
    exact VG.Proof.MlKem.Arm.Decaps.pieceD hp h (.inr rfl) (fun _ => rfl) (by ddecide) (by ddecide) (by ddecide) (by ddecide) (VG.Proof.MlKem.Arm.Decaps.dec_p hp.wf).2.2.1
  have hin' : (List.map ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).pb VG.Proof.MlKem.Arm.Decaps.didx s.mem) [⟨.r7, oMsg, 32⟩, ⟨.r4, 768 * K.k + 32, 32⟩]).flatten = VG.Proof.MlKem.Arm.Decaps.MM K s₀ ++ VG.Proof.MlKem.Arm.Decaps.hH K s₀ := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    show bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 oMsg) 32 ++ bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 2 (768 * K.k + 32)) 32 = _
    rw [hm, VG.Proof.MlKem.Arm.Decaps.dk_slice h (by ddecide)]; rfl
  refine WP.mono (VG.Proof.MlKem.Arm.hash_ok VG.Proof.MlKem.rate72 (by ddecide) (by ddecide) (by ddecide) h.env.ctx (List.cons_ne_nil _ _)
    hin hout (List.pairwise_singleton _ _)) fun s' ⟨k', o'⟩ => ⟨?_, k'.frame, ?_⟩
  · exact h.keep hp (k'.x []) (by simp) (VG.Proof.MlKem.Arm.Decaps.dec_f hp.wf).2.2.2.2.2.2.1
  · have e1 := o'.1
    rw [hin'] at e1
    have e2 : bytesAt s'.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 oG) 64 = (G (VG.Proof.MlKem.Arm.Decaps.MM K s₀ ++ VG.Proof.MlKem.Arm.Decaps.hH K s₀)).1 ++ (G (VG.Proof.MlKem.Arm.Decaps.MM K s₀ ++ VG.Proof.MlKem.Arm.Decaps.hH K s₀)).2 :=
      e1.trans (VG.Proof.MlKem.Arm.G_split _)
    rw [show (64 : Nat) = 32 + 32 from rfl, bytesAt_add] at e2
    have l1 : (bytesAt s'.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 oG) 32).length = (G (VG.Proof.MlKem.Arm.Decaps.MM K s₀ ++ VG.Proof.MlKem.Arm.Decaps.hH K s₀)).1.length := by
      rw [bytesAt_length, VG.Proof.MlKem.G_fst_length]
    obtain ⟨r1, r2⟩ := List.append_inj e2 l1
    refine ⟨r1, ?_⟩
    show bytesAt s'.mem (State.addr ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0) + BitVec.ofNat 64 (888 + 32)) 32 = _
    rw [← add_ofNat_add]; exact r2

theorem hashJ_ok {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.Decaps.Pre K s₀) (h : VG.Proof.MlKem.Arm.Decaps.DD K s₀ s) :
    WP isa (hash 136 0x1f [⟨.r4, 768 * K.k + 64, 32⟩, ⟨.r7, oCin, K.ctLen⟩] [⟨.r7, oKbar, 32⟩]) s fun s' =>
      VG.Proof.MlKem.Arm.Decaps.DD K s₀ s' ∧ Frame ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).RL (VG.Proof.MlKem.Arm.kRegs ++ [(0, oKbar, 32)])) s.mem s'.mem ∧
      bytesAt s'.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 oKbar) 32 = VG.Proof.MlKem.Arm.Decaps.KB K s₀ := by
  have hin : ∀ p ∈ [(⟨.r4, 768 * K.k + 64, 32⟩ : Piece), ⟨.r7, oCin, K.ctLen⟩], VG.Proof.MlKem.Arm.PieceOk (VG.Proof.MlKem.Arm.Decaps.lay s₀ K) VG.Proof.MlKem.Arm.Decaps.didx s false p := by
    intro p hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · exact VG.Proof.MlKem.Arm.Decaps.pieceD hp h (.inl rfl) (by simp) hp.wf.encZ (by ddecide) (by ddecide) (by ddecide) (VG.Proof.MlKem.Arm.Decaps.dec_p hp.wf).2.2.2.1
    · exact VG.Proof.MlKem.Arm.Decaps.pieceD hp h (.inr rfl) (by simp) (by ddecide) hp.wf.encCt hp.wf.ct_pos (by ddecide) (VG.Proof.MlKem.Arm.Decaps.dec_p hp.wf).2.2.2.2.1
  have hout : ∀ p ∈ [(⟨.r7, oKbar, 32⟩ : Piece)], VG.Proof.MlKem.Arm.PieceOk (VG.Proof.MlKem.Arm.Decaps.lay s₀ K) VG.Proof.MlKem.Arm.Decaps.didx s true p := by
    intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
    exact VG.Proof.MlKem.Arm.Decaps.pieceD hp h (.inr rfl) (fun _ => rfl) (by ddecide) (by ddecide) (by ddecide) (by ddecide) (VG.Proof.MlKem.Arm.Decaps.dec_p hp.wf).2.2.2.2.2.1
  have hin' : (List.map ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).pb VG.Proof.MlKem.Arm.Decaps.didx s.mem) [⟨.r4, 768 * K.k + 64, 32⟩, ⟨.r7, oCin, K.ctLen⟩]).flatten =
      VG.Proof.MlKem.Arm.Decaps.zZ K s₀ ++ VG.Proof.MlKem.Arm.Decaps.CT K s₀ := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    show bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 2 (768 * K.k + 64)) 32 ++ bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 oCin) K.ctLen = _
    rw [VG.Proof.MlKem.Arm.Decaps.dk_slice h (by ddecide), h.c]; rfl
  refine WP.mono (VG.Proof.MlKem.Arm.hash_ok VG.Proof.MlKem.rate136 (by ddecide) (by ddecide) (by ddecide) h.env.ctx (List.cons_ne_nil _ _)
    hin hout (List.pairwise_singleton _ _)) fun s' ⟨k', o'⟩ => ⟨h.keep hp (k'.x []) (by simp) (VG.Proof.MlKem.Arm.Decaps.dec_f hp.wf).2.2.2.2.2.2.2.1, k'.frame, ?_⟩
  have e1 := o'.1
  rw [hin'] at e1
  refine e1.trans ?_
  show _ = J (VG.Proof.MlKem.Arm.Decaps.zZ K s₀ ++ VG.Proof.MlKem.Arm.Decaps.CT K s₀)
  rw [VG.Proof.MlKem.J_eq]; rfl


/-! ## The re-encryption -/

theorem ptrs_ok {K : KemLay} (hK : K.WF) {s : State} :
    WP isa (.block [ptrTo .r4 .r4 (384 * K.k), ptrTo .r5 .r7 oMsg, ptrTo .r8 .r7 K.oCt]) s fun s' =>
      VG.Proof.MlKem.Arm.KeptX [.r4, .r5, .r8] [] s s' ∧ s'.gpr .r4 = s.gpr .r4 + BitVec.ofNat 32 (384 * K.k) ∧
      s'.gpr .r5 = s.gpr .r7 + BitVec.ofNat 32 oMsg ∧ s'.gpr .r8 = s.gpr .r7 + BitVec.ofNat 32 K.oCt ∧
      s'.mem = s.mem := by
  have e1 := hK.encT
  have e2 : encodable (BitVec.ofNat 32 oMsg) = true := by decide
  have e3 : encodable (BitVec.ofNat 32 K.oCt) = true := hK.enc (by omega)
  run_block [ptrTo, e1, e2, e3]
  refine ⟨⟨fun r _ _ hx => ?_, rfl, rfl, rfl, Frame.refl _ _⟩, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  show (if r = .r8 then _ else if r = .r5 then _ else if r = .r4 then _ else s.gpr r) = s.gpr r
  rw [ite_eq_right hx.2.2, ite_eq_right hx.2.1, ite_eq_right hx.1]

/-- Before the re-encryption. -/
structure DP (K : KemLay) (s₀ s : State) : Prop where
  env : VG.Proof.MlKem.Arm.Decaps.DEnv K s₀ s
  r4 : s.gpr .r4 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 2 + BitVec.ofNat 32 (384 * K.k)
  r5 : s.gpr .r5 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 oMsg
  r6 : s.gpr .r6 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 oCin
  r8 : s.gpr .r8 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 K.oCt
  c : bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 oCin) K.ctLen = VG.Proof.MlKem.Arm.Decaps.CT K s₀
  m : bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 oMsg) 32 = VG.Proof.MlKem.Arm.Decaps.MM K s₀
  k1 : bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 oG) 32 = VG.Proof.MlKem.Arm.Decaps.K1 K s₀
  r1 : bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 oSigma) 32 = VG.Proof.MlKem.Arm.Decaps.R1 K s₀
  kb : bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 oKbar) 32 = VG.Proof.MlKem.Arm.Decaps.KB K s₀

theorem ptrs_dp {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.Decaps.Pre K s₀) (h : VG.Proof.MlKem.Arm.Decaps.DD K s₀ s) (hm : bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 oMsg) 32 = VG.Proof.MlKem.Arm.Decaps.MM K s₀)
    (hk : bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 oG) 32 = VG.Proof.MlKem.Arm.Decaps.K1 K s₀) (hr : bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 oSigma) 32 = VG.Proof.MlKem.Arm.Decaps.R1 K s₀)
    (hb : bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 oKbar) 32 = VG.Proof.MlKem.Arm.Decaps.KB K s₀) :
    WP isa (.block [ptrTo .r4 .r4 (384 * K.k), ptrTo .r5 .r7 oMsg, ptrTo .r8 .r7 K.oCt]) s (VG.Proof.MlKem.Arm.Decaps.DP K s₀) :=
  WP.mono (VG.Proof.MlKem.Arm.Decaps.ptrs_ok hp.wf) fun _ ⟨k, g4, g5, g8, m⟩ =>
    ⟨h.env.keep hp (W := []) k (by simp) rfl, by rw [g4, h.r4]; rfl, by rw [g5, h.env.ctx.r7],
      by rw [k.cs .r6 (by ddecide) (by ddecide) (by simp), h.r6], by rw [g8, h.env.ctx.r7],
      by rw [m]; exact h.c, by rw [m]; exact hm, by rw [m]; exact hk, by rw [m]; exact hr, by rw [m]; exact hb⟩

/-- The buffers of `encrypt`: `ek` in `dk`, `m'` and `c'` in `scratch`. -/
abbrev db (K : KemLay) : VG.Proof.MlKem.Arm.Enc.EB := ⟨2, 384 * K.k, 0, oMsg, 0, K.oCt⟩

/-- The facts on the buffers of the re-encryption, with the sizes `sz` and the longest `c`. -/
abbrev EncF (K : KemLay) (sz : List Nat) : Prop :=
  (VG.Proof.MlKem.Arm.Enc.encW0 K ++ [(0, K.oCt, oCin - K.oCt)]).all (VG.Proof.MlKem.Arm.Decaps.okWm K sz) = true ∧
  [((0 : Nat), oCin, (8192 : Nat)), (0, oG, 32), (0, oKbar, 32)].all
    (fun w => VG.Proof.MlKem.Arm.sepAll sz w (VG.Proof.MlKem.Arm.Enc.encW0 K ++ [(0, K.oCt, oCin - K.oCt)])) = true ∧
  VG.Proof.MlKem.Arm.sepAll sz (2, 384 * K.k, K.ekLen) (VG.Proof.MlKem.Arm.Enc.encW0 K) = true ∧ VG.Proof.MlKem.Arm.sepAll sz (0, oMsg, 32) (VG.Proof.MlKem.Arm.Enc.encW0 K) = true ∧
  VG.Proof.MlKem.Arm.sepAll sz (0, K.oCt, oCin - K.oCt) (VG.Proof.MlKem.Arm.Enc.encW0 K) = true

theorem enc_f {K : KemLay} (hK : K.WF) : (VG.Proof.MlKem.Arm.Enc.encW K (VG.Proof.MlKem.Arm.Decaps.db K)).all (VG.Proof.MlKem.Arm.Decaps.okW K) = true ∧
    [((0 : Nat), oCin, (K.ctLen : Nat)), (0, oG, 32), (0, oKbar, 32)].all
      (fun w => VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.Decaps.dSz K) w (VG.Proof.MlKem.Arm.Enc.encW K (VG.Proof.MlKem.Arm.Decaps.db K))) = true ∧
    VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.Decaps.dSz K) (2, 384 * K.k, K.ekLen) (VG.Proof.MlKem.Arm.Enc.encW0 K) = true ∧ VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.Decaps.dSz K) (0, oMsg, 32) (VG.Proof.MlKem.Arm.Enc.encW0 K) = true ∧
    VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.Decaps.dSz K) (0, K.oCt, K.ctLen) (VG.Proof.MlKem.Arm.Enc.encW0 K) = true := by
  have s := hK.scr
  have hct : K.ctLen ≤ oCin - K.oCt := Nat.le_sub_of_add_le' hK.ct
  obtain ⟨e1, e2, e3, e4, e5⟩ := (by decide : ∀ k < 5, EncF (kOf k) (dSz (kOf k))) K.k (by have := hK.k4; omega)
  have hW : (VG.Proof.MlKem.Arm.Enc.encW0 K ++ [((0 : Nat), K.oCt, K.ctLen)]).all
      (fun x => (VG.Proof.MlKem.Arm.Enc.encW0 K ++ [((0 : Nat), K.oCt, oCin - K.oCt)]).any (VG.Proof.MlKem.Arm.inB x)) = true := by
    rw [List.all_append, Bool.and_eq_true]
    refine ⟨List.all_eq_true.mpr fun x hx => List.any_eq_true.mpr ⟨x, List.mem_append_left _ hx, VG.Proof.MlKem.Arm.inB_refl x⟩, ?_⟩
    rw [List.all_cons, List.all_nil, Bool.and_true]
    exact List.any_eq_true.mpr ⟨_, List.mem_append_right _ (List.mem_singleton_self _), VG.Proof.MlKem.Arm.Decaps.inB_len hct⟩
  refine ⟨?_, ?_, VG.Proof.MlKem.Arm.sepAll_scr e3 s, VG.Proof.MlKem.Arm.sepAll_scr e4 s, VG.Proof.MlKem.Arm.Enc.sepAll_left (VG.Proof.MlKem.Arm.sepAll_scr e5 s) (VG.Proof.MlKem.Arm.Decaps.inB_len hct)⟩
  · show (VG.Proof.MlKem.Arm.Enc.encW0 K ++ [((0 : Nat), K.oCt, K.ctLen)]).all (VG.Proof.MlKem.Arm.Decaps.okW K) = true
    rw [List.all_append, Bool.and_eq_true] at e1 ⊢
    refine ⟨VG.Proof.MlKem.Arm.Decaps.allOkW_of hK e1.1, ?_⟩
    have e := e1.2
    rw [List.all_cons, List.all_nil, Bool.and_true] at e ⊢
    simp only [VG.Proof.MlKem.Arm.Decaps.okWm, VG.Proof.MlKem.Arm.Decaps.okW, Bool.and_eq_true] at e ⊢
    exact ⟨VG.Proof.MlKem.Arm.sepB_mono (VG.Proof.MlKem.Arm.sepB_scr e.1 s) (VG.Proof.MlKem.Arm.inB_refl _) (VG.Proof.MlKem.Arm.Decaps.inB_len hct), VG.Proof.MlKem.Arm.sepB_mono (VG.Proof.MlKem.Arm.sepB_scr e.2 s) (VG.Proof.MlKem.Arm.inB_refl _) (VG.Proof.MlKem.Arm.Decaps.inB_len hct)⟩
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at e2 ⊢
    exact ⟨VG.Proof.MlKem.Arm.sepAll_mono (VG.Proof.MlKem.Arm.sepAll_scr e2.1 s) (VG.Proof.MlKem.Arm.Decaps.inB_len (VG.Proof.MlKem.Arm.Decaps.ct_le hK)) hW, VG.Proof.MlKem.Arm.sepAll_mono (VG.Proof.MlKem.Arm.sepAll_scr e2.2.1 s) (VG.Proof.MlKem.Arm.inB_refl _) hW,
      VG.Proof.MlKem.Arm.sepAll_mono (VG.Proof.MlKem.Arm.sepAll_scr e2.2.2 s) (VG.Proof.MlKem.Arm.inB_refl _) hW⟩

theorem encPre {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.Decaps.Pre K s₀) (h : VG.Proof.MlKem.Arm.Decaps.DP K s₀ s) : VG.Proof.MlKem.Arm.Enc.EncPre K (VG.Proof.MlKem.Arm.Decaps.lay s₀ K) (VG.Proof.MlKem.Arm.Decaps.db K) s := by
  have hK := hp.wf
  obtain ⟨w0, -, w2, -, -⟩ := VG.Proof.MlKem.Arm.Decaps.buf_wr hp
  obtain ⟨-, -, f3, f4, f5⟩ := VG.Proof.MlKem.Arm.Decaps.enc_f hK
  exact ⟨hK, hp.calls, h.env.ctx, h.r4, h.r5, h.r8, f3, f4, f5, by rw [h.env.rd, h.env.wr]; exact w2,
    by rw [h.env.rd, h.env.wr]; exact VG.Proof.MlKem.Arm.mem_rd_wr w0, by rw [h.env.wr]; exact w0⟩

theorem encW_ok {K : KemLay} (hK : K.WF) : (VG.Proof.MlKem.Arm.Enc.encW K (VG.Proof.MlKem.Arm.Decaps.db K)).all (VG.Proof.MlKem.Arm.Decaps.okW K) = true ∧
    [((0 : Nat), oCin, (K.ctLen : Nat)), (0, oG, 32), (0, oKbar, 32)].all
      (fun w => VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.Decaps.dSz K) w (VG.Proof.MlKem.Arm.Enc.encW K (VG.Proof.MlKem.Arm.Decaps.db K))) = true :=
  ⟨(VG.Proof.MlKem.Arm.Decaps.enc_f hK).1, (VG.Proof.MlKem.Arm.Decaps.enc_f hK).2.1⟩

/-- `ρ` of `dk`. -/
abbrev ρD (K : KemLay) (s₀ : State) : List Byte := ekRho K.p (VG.Proof.MlKem.Arm.Decaps.eK K s₀)

/-- `c'`. -/
abbrev C2 (K : KemLay) (s₀ : State) : List Byte := VG.Proof.MlKem.KPke.ct K.p (VG.Proof.MlKem.Arm.Enc.aEnc (VG.Proof.MlKem.Arm.Decaps.ρD K s₀) (VG.Proof.MlKem.Arm.Decaps.R1 K s₀)) (VG.Proof.MlKem.Arm.Decaps.eK K s₀) (VG.Proof.MlKem.Arm.Decaps.MM K s₀) (VG.Proof.MlKem.Arm.Decaps.R1 K s₀)

/-- After the re-encryption. -/
structure DQ (K : KemLay) (s₀ s : State) : Prop where
  env : VG.Proof.MlKem.Arm.Decaps.DEnv K s₀ s
  r6 : s.gpr .r6 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 oCin
  r11 : s.gpr .r11 = if VG.Proof.MlKem.Arm.Enc.okEnc K.k (VG.Proof.MlKem.Arm.Decaps.ρD K s₀) K.k then 1 else 0
  c : bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 oCin) K.ctLen = VG.Proof.MlKem.Arm.Decaps.CT K s₀
  c2 : bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 K.oCt) K.ctLen = VG.Proof.MlKem.Arm.Decaps.C2 K s₀
  k1 : bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 oG) 32 = VG.Proof.MlKem.Arm.Decaps.K1 K s₀
  kb : bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 oKbar) 32 = VG.Proof.MlKem.Arm.Decaps.KB K s₀

theorem rhoE_eq {K : KemLay} {s₀ s : State} (h : VG.Proof.MlKem.Arm.Decaps.DP K s₀ s) : VG.Proof.MlKem.Arm.Enc.ρE K (VG.Proof.MlKem.Arm.Decaps.lay s₀ K) (VG.Proof.MlKem.Arm.Decaps.db K) s = VG.Proof.MlKem.Arm.Decaps.ρD K s₀ := by
  show ekRho K.p (bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 2 (384 * K.k)) K.ekLen) = _
  have dk : bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 2 0) K.dkLen = VG.Proof.MlKem.Arm.Decaps.DK K s₀ := h.env.dk
  rw [show (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 2 (384 * K.k) = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 2 0 + BitVec.ofNat 64 (384 * K.k) by rw [add_ofNat_add, Nat.zero_add],
    ← bytesAt_slice _ _ (by simp only [KemLay.ekLen, KemLay.dkLen]; omega : 384 * K.k + K.ekLen ≤ K.dkLen), dk]
  rfl

theorem reenc_ok {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.Decaps.Pre K s₀) (h : VG.Proof.MlKem.Arm.Decaps.DP K s₀ s) : WP isa K.encrypt s (VG.Proof.MlKem.Arm.Decaps.DQ K s₀) := by
  have hL := VG.Proof.MlKem.Arm.Decaps.lay_ok hp
  have eρ : VG.Proof.MlKem.Arm.Enc.ρE K (VG.Proof.MlKem.Arm.Decaps.lay s₀ K) (VG.Proof.MlKem.Arm.Decaps.db K) s = VG.Proof.MlKem.Arm.Decaps.ρD K s₀ := VG.Proof.MlKem.Arm.Decaps.rhoE_eq h
  have e1 : VG.Proof.MlKem.Arm.Enc.ekB K (VG.Proof.MlKem.Arm.Decaps.lay s₀ K) (VG.Proof.MlKem.Arm.Decaps.db K) s = VG.Proof.MlKem.Arm.Decaps.eK K s₀ := by
    show bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 2 (384 * K.k)) K.ekLen = _
    have dk : bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 2 0) K.dkLen = VG.Proof.MlKem.Arm.Decaps.DK K s₀ := h.env.dk
    rw [show (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 2 (384 * K.k) = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 2 0 + BitVec.ofNat 64 (384 * K.k) by rw [add_ofNat_add, Nat.zero_add],
      ← bytesAt_slice _ _ (by simp only [KemLay.ekLen, KemLay.dkLen]; omega : 384 * K.k + K.ekLen ≤ K.dkLen), dk]
    rfl
  have e2 : VG.Proof.MlKem.Arm.Enc.mB (VG.Proof.MlKem.Arm.Decaps.lay s₀ K) (VG.Proof.MlKem.Arm.Decaps.db K) s = VG.Proof.MlKem.Arm.Decaps.MM K s₀ := h.m
  have er : VG.Proof.MlKem.Arm.Enc.rB (VG.Proof.MlKem.Arm.Decaps.lay s₀ K) s = VG.Proof.MlKem.Arm.Decaps.R1 K s₀ := h.r1
  obtain ⟨c1, c2⟩ := VG.Proof.MlKem.Arm.Decaps.encW_ok hp.wf
  have sep : ∀ {o l : Nat}, ((0 : Nat), o, l) ∈ [((0 : Nat), oCin, (K.ctLen : Nat)), (0, oG, 32), (0, oKbar, 32)] →
      VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).sizes (0, o, l) (VG.Proof.MlKem.Arm.Enc.encW K (VG.Proof.MlKem.Arm.Decaps.db K)) = true := fun hm => List.all_eq_true.mp c2 _ hm
  refine WP.mono (VG.Proof.MlKem.Arm.Enc.encrypt_ok (VG.Proof.MlKem.Arm.Decaps.encPre hp h)) fun s' ⟨kp, r11, ct⟩ =>
    ⟨h.env.keep hp kp (by simp) c1, by rw [kp.cs .r6 (by ddecide) (by ddecide) (by simp), h.r6], ?_,
      (Lay.bytes_keep hL kp.frame (sep (by simp)) (by ddecide)).trans h.c, ?_,
      (Lay.bytes_keep hL kp.frame (sep (by simp)) (by ddecide)).trans h.k1,
      (Lay.bytes_keep hL kp.frame (sep (by simp)) (by ddecide)).trans h.kb⟩
  · rw [r11]; show (if VG.Proof.MlKem.Arm.Enc.okEnc K.k (VG.Proof.MlKem.Arm.Enc.ρE K (VG.Proof.MlKem.Arm.Decaps.lay s₀ K) (VG.Proof.MlKem.Arm.Decaps.db K) s) K.k = true then _ else _) = _; rw [eρ]
  · rw [e1, e2] at ct
    show _ = VG.Proof.MlKem.KPke.ct K.p (VG.Proof.MlKem.Arm.Enc.aEnc (VG.Proof.MlKem.Arm.Decaps.ρD K s₀) (VG.Proof.MlKem.Arm.Decaps.R1 K s₀)) (VG.Proof.MlKem.Arm.Decaps.eK K s₀) (VG.Proof.MlKem.Arm.Decaps.MM K s₀) (VG.Proof.MlKem.Arm.Decaps.R1 K s₀)
    rw [← eρ, ← er]; exact ct


/-! ## The comparison and the selection -/

theorem covers2 {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hc : VG.Proof.MlKem.Arm.Ctx L s) {o o' l l' : Nat} (h : o + l ≤ 32768) (h' : o' + l' ≤ 32768) :
    Covers [L.R 0 o l, L.R 0 o' l'] (s.rd ++ s.wr) := fun a n ⟨r, hr, hcn⟩ => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact VG.Proof.MlKem.Arm.mem_rd_wr' (hc.cs h _ _ ⟨_, List.mem_singleton_self _, hcn⟩)
  · exact VG.Proof.MlKem.Arm.mem_rd_wr' (hc.cs h' _ _ ⟨_, List.mem_singleton_self _, hcn⟩)

/-- After the comparison. -/
structure DR (K : KemLay) (s₀ s : State) : Prop where
  q : VG.Proof.MlKem.Arm.Decaps.DQ K s₀ s
  lt : (s.gpr .r12).toNat < 256
  eq : s.gpr .r12 = 0 ↔ VG.Proof.MlKem.Arm.Decaps.CT K s₀ = VG.Proof.MlKem.Arm.Decaps.C2 K s₀

theorem kept_of {s s' : State} {x : Reg} {W : List Region} (cs : ∀ r ∈ preserved, r ≠ x → s'.gpr r = s.gpr r)
    (sp : s'.sp = s.sp) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (fr : Frame W s.mem s'.mem) : VG.Proof.MlKem.Arm.KeptX [x] W s s' :=
  ⟨fun r hr _ hx => cs r hr fun e => hx (by rw [e]; exact List.mem_singleton_self _), sp, rd, wr, fr⟩

theorem cmp_ok {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.Decaps.Pre K s₀) (h : VG.Proof.MlKem.Arm.Decaps.DQ K s₀ s) : WP isa K.compare s (VG.Proof.MlKem.Arm.Decaps.DR K s₀) := by
  have hc := h.env.ctx
  have hK := hp.wf
  have hct : K.oCt + K.ctLen ≤ 32768 := by
    have h1 := hK.ct; simp only [KemLay.oCt, oPoly, oCin] at h1 ⊢; omega
  have hct' : K.oCt < 32768 := by have := hK.ct_pos; omega
  refine WP.mono (VG.Proof.MlKem.Arm.compare_ok hK (P := (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0) hc.r7 h.r6 (hc.fitO (by ddecide) hK.ct_pos)
    (hc.fitO hct hK.ct_pos)
    (by rw [hc.addr (by ddecide), hc.addr hct']; exact VG.Proof.MlKem.Arm.Decaps.covers2 hc (by ddecide) hct))
    fun s' ⟨cs, m, rd, wr, sp, lt, eq⟩ => ?_
  have k : VG.Proof.MlKem.Arm.KeptX [.r9] ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).RL []) s s' := VG.Proof.MlKem.Arm.Decaps.kept_of cs sp rd wr (by rw [m]; exact Frame.refl _ _)
  refine ⟨⟨h.env.keep hp k (by ddecide) rfl, by rw [cs .r6 (by ddecide) (by ddecide), h.r6],
    by rw [cs .r11 (by ddecide) (by ddecide), h.r11], by rw [m]; exact h.c, by rw [m]; exact h.c2,
    by rw [m]; exact h.k1, by rw [m]; exact h.kb⟩, lt, ?_⟩
  rw [eq, hc.addr (by ddecide), hc.addr (by ddecide)]
  show bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 oCin) K.ctLen = bytesAt s.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 K.oCt) K.ctLen ↔ _
  rw [h.c, h.c2]

/-- After the mask. -/
structure DS (K : KemLay) (s₀ s : State) : Prop where
  q : VG.Proof.MlKem.Arm.Decaps.DQ K s₀ s
  r0 : s.gpr .r0 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 oG
  r1 : s.gpr .r1 = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 oKbar
  r2 : s.gpr .r2 = VG.Proof.MlKem.Arm.Decaps.pKey s₀
  r9 : s.gpr .r9 = BitVec.ofNat 32 32
  r12 : s.gpr .r12 = if decide (VG.Proof.MlKem.Arm.Decaps.CT K s₀ = VG.Proof.MlKem.Arm.Decaps.C2 K s₀) then BitVec.allOnes 32 else 0

theorem mask_ok {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.Decaps.Pre K s₀) (h : VG.Proof.MlKem.Arm.Decaps.DR K s₀ s) : WP isa (.block selSetup) s (VG.Proof.MlKem.Arm.Decaps.DS K s₀) := by
  have hc := h.q.env.ctx
  refine WP.mono (VG.Proof.MlKem.Arm.selSetup_ok (P := (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0) (K := VG.Proof.MlKem.Arm.Decaps.pKey s₀) hc.r7 h.lt
    (by rw [hc.addr (by ddecide)]; exact h.q.env.key)
    (by rw [hc.addr (by ddecide)]; exact VG.Proof.MlKem.Arm.mem_rd_wr' (hc.cs (o := 876) (l := 4) (by ddecide) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)))
    fun s' ⟨g12, g0, g1, g2, g9, cs, m, rd, wr, sp⟩ => ?_
  have k : VG.Proof.MlKem.Arm.KeptX [.r9] ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).RL []) s s' := VG.Proof.MlKem.Arm.Decaps.kept_of cs sp rd wr (by rw [m]; exact Frame.refl _ _)
  refine ⟨⟨h.q.env.keep hp k (by ddecide) rfl, by rw [cs .r6 (by ddecide) (by ddecide), h.q.r6],
    by rw [cs .r11 (by ddecide) (by ddecide), h.q.r11], by rw [m]; exact h.q.c, by rw [m]; exact h.q.c2,
    by rw [m]; exact h.q.k1, by rw [m]; exact h.q.kb⟩, g0, g1, g2, g9, ?_⟩
  rw [g12]
  simp only [h.eq, decide_eq_true_eq]

theorem sel_ok {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.Decaps.Pre K s₀) (h : VG.Proof.MlKem.Arm.Decaps.DS K s₀ s) :
    WP isa (.loop (.block selBody) .ne) s fun s' => VG.Proof.MlKem.Arm.Decaps.DEnv K s₀ s' ∧
      s'.gpr .r11 = (if VG.Proof.MlKem.Arm.Enc.okEnc K.k (VG.Proof.MlKem.Arm.Decaps.ρD K s₀) K.k then 1 else 0) ∧
      bytesAt s'.mem (State.addr (VG.Proof.MlKem.Arm.Decaps.pKey s₀)) 32 = if VG.Proof.MlKem.Arm.Decaps.CT K s₀ = VG.Proof.MlKem.Arm.Decaps.C2 K s₀ then VG.Proof.MlKem.Arm.Decaps.K1 K s₀ else VG.Proof.MlKem.Arm.Decaps.KB K s₀ := by
  have hL := VG.Proof.MlKem.Arm.Decaps.lay_ok hp
  have hc := h.q.env.ctx
  obtain ⟨-, w3, -, -, -⟩ := VG.Proof.MlKem.Arm.Decaps.buf_wr hp
  have eZ : (⟨State.addr (VG.Proof.MlKem.Arm.Decaps.pKey s₀), 32⟩ : Region) = (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).R 3 0 32 := by simp only [Lay.R, add_ofNat_zero]; rfl
  have dZ : ∀ o, VG.Proof.MlKem.Arm.sepB (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).sizes (0, o, 32) (3, 0, 32) = true → o + 32 ≤ 32768 →
      (⟨State.addr ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 o), 32⟩ : Region).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.Decaps.pKey s₀), 32⟩ :=
    fun o hs ho => by rw [hc.addr (by omega), eZ]; exact Lay.disj hL hs
  refine WP.mono (VG.Proof.MlKem.Arm.select_ok (e := decide (VG.Proof.MlKem.Arm.Decaps.CT K s₀ = VG.Proof.MlKem.Arm.Decaps.C2 K s₀)) (hc.fitO (by ddecide) (by ddecide))
    (hc.fitO (by ddecide) (by ddecide)) hp.f_key (dZ _ (VG.Proof.MlKem.Arm.Decaps.dec_p hp.wf).2.2.2.2.2.2.2.2.2.2.1 (by ddecide)) (dZ _ (VG.Proof.MlKem.Arm.Decaps.dec_p hp.wf).2.2.2.2.2.2.2.2.2.2.2.1 (by ddecide))
    (by rw [hc.addr (by ddecide), hc.addr (by ddecide)]; exact VG.Proof.MlKem.Arm.Decaps.covers2 hc (by ddecide) (by ddecide))
    (by rw [eZ, h.q.env.wr]; exact Lay.covers w3 (by simp only [Lay.size, VG.Proof.MlKem.Arm.Decaps.lay_sizes]; exact Nat.le_refl _)) h.r0 h.r1 h.r2 h.r9 h.r12)
    fun s' ⟨cs, rd, wr, sp, fr, b⟩ => ⟨?_, ?_, ?_⟩
  · have k : VG.Proof.MlKem.Arm.KeptX [.r9, .r10] ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).RL [(3, 0, 32)]) s s' :=
      ⟨fun r hr _ hx => cs r hr (fun e => hx (by rw [e]; simp)) (fun e => hx (by rw [e]; simp)), sp, rd, wr,
        by rw [show (VG.Proof.MlKem.Arm.Decaps.lay s₀ K).RL [(3, 0, 32)] = [⟨State.addr (VG.Proof.MlKem.Arm.Decaps.pKey s₀), 32⟩] by rw [eZ]; rfl]; exact fr⟩
    exact h.q.env.keep hp k (by ddecide) (VG.Proof.MlKem.Arm.Decaps.dec_f hp.wf).2.2.2.2.2.2.2.2.2
  · rw [cs .r11 (by ddecide) (by ddecide) (by ddecide), h.q.r11]
  · rw [b, hc.addr (by ddecide), hc.addr (by ddecide), h.q.k1, h.q.kb]
    by_cases e : VG.Proof.MlKem.Arm.Decaps.CT K s₀ = VG.Proof.MlKem.Arm.Decaps.C2 K s₀ <;> simp [e]


/-! ## The whole function -/

theorem dd_of {K : KemLay} {s₀ s₂ s₃ : State} (hp : VG.Proof.MlKem.Arm.Decaps.Pre K s₀) (h₂ : VG.Proof.MlKem.Arm.Decaps.DEnv K s₀ s₂) (g4 : s₂.gpr .r4 = VG.Proof.MlKem.Arm.Decaps.pDk s₀)
    (c₂ : bytesAt s₂.mem ((VG.Proof.MlKem.Arm.Decaps.lay s₀ K).A 0 oCin) K.ctLen = VG.Proof.MlKem.Arm.Decaps.CT K s₀)
    (h₃ : VG.Proof.MlKem.Arm.KeptX [.r6] [] s₂ s₃ ∧ s₃.gpr .r6 = s₂.gpr .r7 + BitVec.ofNat 32 oCin ∧ s₃.mem = s₂.mem) : VG.Proof.MlKem.Arm.Decaps.DD K s₀ s₃ :=
  ⟨h₂.keep hp (W := []) h₃.1 (by ddecide) rfl, by rw [h₃.1.cs .r4 (by ddecide) (by ddecide) (by ddecide), g4],
    by rw [h₃.2.1, h₂.ctx.r7], by rw [h₃.2.2]; exact c₂⟩

theorem correct {K : KemLay} {s₀ : State} (hp : VG.Proof.MlKem.Arm.Decaps.Pre K s₀) :
    WP isa K.decaps s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      s.gpr .r0 = (if VG.Proof.MlKem.Arm.Enc.okEnc K.k (VG.Proof.MlKem.Arm.Decaps.ρD K s₀) K.k then 1 else 0) ∧
      bytesAt s.mem (State.addr (VG.Proof.MlKem.Arm.Decaps.pKey s₀)) 32 = if VG.Proof.MlKem.Arm.Decaps.CT K s₀ = VG.Proof.MlKem.Arm.Decaps.C2 K s₀ then VG.Proof.MlKem.Arm.Decaps.K1 K s₀ else VG.Proof.MlKem.Arm.Decaps.KB K s₀ := by
  have hL := VG.Proof.MlKem.Arm.Decaps.lay_ok hp
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Decaps.setup_ok hp) fun s₁ ⟨h₁, g4, g6, c₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Decaps.copyC_ok hp h₁ g6 c₁) fun s₂ ⟨h₂, g4₂, c₂⟩ => ?_)
  refine WP.seq (WP.mono VG.Proof.MlKem.Arm.Decaps.ptr6_ok fun s₃ h₃ => ?_)
  have d₃ := VG.Proof.MlKem.Arm.Decaps.dd_of hp h₂ (by rw [g4₂, g4]) c₂ h₃
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Decaps.decrypt_ok hp d₃) fun s₄ ⟨d₄, m₄⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Decaps.hashG_ok hp d₄ m₄) fun s₅ ⟨d₅, f₅, k₅, r₅⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Decaps.hashJ_ok hp d₅) fun s₆ ⟨d₆, f₆, kb₆⟩ => ?_)
  have m₆ := (Lay.bytes_keep hL f₆ (VG.Proof.MlKem.Arm.Decaps.dec_p hp.wf).2.2.2.2.2.2.1 (by ddecide)).trans
    ((Lay.bytes_keep hL f₅ (VG.Proof.MlKem.Arm.Decaps.dec_p hp.wf).2.2.2.2.2.2.2.1 (by ddecide)).trans m₄)
  have k₆ := (Lay.bytes_keep hL f₆ (VG.Proof.MlKem.Arm.Decaps.dec_p hp.wf).2.2.2.2.2.2.2.2.1 (by ddecide)).trans k₅
  have r₆ := (Lay.bytes_keep hL f₆ (VG.Proof.MlKem.Arm.Decaps.dec_p hp.wf).2.2.2.2.2.2.2.2.2.1 (by ddecide)).trans r₅
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Decaps.ptrs_dp hp d₆ m₆ k₆ r₆ kb₆) fun s₇ h₇ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Decaps.reenc_ok hp h₇) fun s₈ h₈ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Decaps.cmp_ok hp h₈) fun s₉ h₉ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Decaps.mask_ok hp h₉) fun s₁₀ h₁₀ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Decaps.sel_ok hp h₁₀) fun s₁₁ ⟨h₁₁, r11, key⟩ => ?_)
  exact WP.mono (VG.Proof.MlKem.Arm.topEnd_ok h₁₁.ctx h₁₁.sav h₁₁.savlr) fun s ⟨pr, r0, m', sp'⟩ =>
    ⟨pr, sp'.trans h₁₁.sp, by rw [r0, r11], by rw [m']; exact key⟩

end VG.Proof.MlKem.Arm.Decaps

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.Encaps`. -/
section

/-!
# ML-KEM on 32-bit ARM: encapsulation, correctness

`K.encaps` for any parameter set `K` (`KemLay.WF`).

The buffers of the function (`lay`): `scratch` (the argument on the stack),
the stack below the stack pointer, `ek`, `key` and `ct`; `m`, which may
overlap `ek`, is only read by its copy into `scratch`, with a layout of its
own (`layM`). What every phase keeps (`EnEnv`), and the phases: the setup, `m`
copied, `H(ek)`, `G(m ‖ H(ek))` into `K ‖ r`, `K` copied into `key`, and
K-PKE.Encrypt (`Enc.encrypt_ok`) into `ct`.
-/

namespace VG.Proof.MlKem.Arm.Encaps

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Enc

section
variable (s₀ : State)

def pEk : BitVec 32 := s₀.gpr .r0
def pM : BitVec 32 := s₀.gpr .r1
def pKey : BitVec 32 := s₀.gpr .r2
def pCt : BitVec 32 := s₀.gpr .r3
def pScr : BitVec 32 := stackArg s₀ 0

/-- The buffers: `scratch`, the 8 bytes below the stack pointer, `ek`, `key` and `ct`. -/
def lay (K : KemLay) : VG.Proof.MlKem.Arm.Lay :=
  ⟨fun i => [VG.Proof.MlKem.Arm.Encaps.pScr s₀, s₀.sp - BitVec.ofNat 32 8, VG.Proof.MlKem.Arm.Encaps.pEk s₀, VG.Proof.MlKem.Arm.Encaps.pKey s₀, VG.Proof.MlKem.Arm.Encaps.pCt s₀].getD i 0, [K.scratch, 8, K.ekLen, 32, K.ctLen]⟩

/-- The buffers of the copy of `m`: `scratch`, the stack and `m`. -/
def layM (K : KemLay) : VG.Proof.MlKem.Arm.Lay := ⟨fun i => [VG.Proof.MlKem.Arm.Encaps.pScr s₀, s₀.sp - BitVec.ofNat 32 8, VG.Proof.MlKem.Arm.Encaps.pM s₀].getD i 0, [K.scratch, 8, 32]⟩

end

/-- The sizes of the buffers. -/
abbrev eSz (K : KemLay) : List Nat := [K.scratch, 8, K.ekLen, 32, K.ctLen]

theorem lay_sizes (K : KemLay) (s₀ : State) : (VG.Proof.MlKem.Arm.Encaps.lay s₀ K).sizes = VG.Proof.MlKem.Arm.Encaps.eSz K := rfl

theorem layM_sizes (K : KemLay) (s₀ : State) : (VG.Proof.MlKem.Arm.Encaps.layM s₀ K).sizes = [K.scratch, 8, 32] := rfl

theorem lay_ptr0 (K : KemLay) (s₀ : State) : (VG.Proof.MlKem.Arm.Encaps.lay s₀ K).ptr 0 = VG.Proof.MlKem.Arm.Encaps.pScr s₀ := rfl
theorem layM_ptr0 (K : KemLay) (s₀ : State) : (VG.Proof.MlKem.Arm.Encaps.layM s₀ K).ptr 0 = VG.Proof.MlKem.Arm.Encaps.pScr s₀ := rfl

/-- The precondition of the contract. -/
structure Pre (K : KemLay) (s : State) : Prop where
  wf : K.WF
  calls : K.CallsOk
  sp8 : 8 ≤ s.sp.toNat
  spf : s.sp.toNat + 4 ≤ 2 ^ 32
  rd : s.rd = [⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pEk s), K.ekLen⟩, ⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pM s), 32⟩, ⟨stackArgAddr s 0, 4⟩]
  wr : s.wr = [⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pKey s), 32⟩, ⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pCt s), K.ctLen⟩, ⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pScr s), K.scratch⟩]
  d_ek_key : (⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pEk s), K.ekLen⟩ : Region).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pKey s), 32⟩
  d_ek_ct : (⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pEk s), K.ekLen⟩ : Region).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pCt s), K.ctLen⟩
  d_ek_scr : (⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pEk s), K.ekLen⟩ : Region).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pScr s), K.scratch⟩
  d_m_key : (⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pM s), 32⟩ : Region).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pKey s), 32⟩
  d_m_ct : (⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pM s), 32⟩ : Region).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pCt s), K.ctLen⟩
  d_m_scr : (⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pM s), 32⟩ : Region).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pScr s), K.scratch⟩
  d_key_ct : (⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pKey s), 32⟩ : Region).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pCt s), K.ctLen⟩
  d_key_scr : (⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pKey s), 32⟩ : Region).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pScr s), K.scratch⟩
  d_key_arg : (⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pKey s), 32⟩ : Region).Disjoint ⟨stackArgAddr s 0, 4⟩
  d_ct_scr : (⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pCt s), K.ctLen⟩ : Region).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pScr s), K.scratch⟩
  d_ct_arg : (⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pCt s), K.ctLen⟩ : Region).Disjoint ⟨stackArgAddr s 0, 4⟩
  d_scr_arg : (⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pScr s), K.scratch⟩ : Region).Disjoint ⟨stackArgAddr s 0, 4⟩
  b_ek : (below s 8).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pEk s), K.ekLen⟩
  b_m : (below s 8).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pM s), 32⟩
  b_key : (below s 8).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pKey s), 32⟩
  b_ct : (below s 8).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pCt s), K.ctLen⟩
  b_scr : (below s 8).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pScr s), K.scratch⟩
  b_arg : (below s 8).Disjoint ⟨stackArgAddr s 0, 4⟩
  f_ek : (VG.Proof.MlKem.Arm.Encaps.pEk s).toNat + K.ekLen ≤ 2 ^ 32
  f_m : (VG.Proof.MlKem.Arm.Encaps.pM s).toNat + 32 ≤ 2 ^ 32
  f_key : (VG.Proof.MlKem.Arm.Encaps.pKey s).toNat + 32 ≤ 2 ^ 32
  f_ct : (VG.Proof.MlKem.Arm.Encaps.pCt s).toNat + K.ctLen ≤ 2 ^ 32
  f_scr : (VG.Proof.MlKem.Arm.Encaps.pScr s).toNat + K.scratch ≤ 2 ^ 32

section
variable {K : KemLay} {s₀ : State} (hp : VG.Proof.MlKem.Arm.Encaps.Pre K s₀)
include hp

theorem stack_eq : (⟨State.addr (s₀.sp - BitVec.ofNat 32 8), 8⟩ : Region) = below s₀ 8 := by
  rw [addr_sub hp.sp8]

theorem stack_fit : (s₀.sp - BitVec.ofNat 32 8).toNat + 8 ≤ 2 ^ 32 := by
  have := hp.sp8; have := s₀.sp.isLt; bv_omega

theorem lay_ok : (VG.Proof.MlKem.Arm.Encaps.lay s₀ K).Ok := by
  have es := VG.Proof.MlKem.Arm.Encaps.stack_eq hp
  refine Lay.ok_of (fun i hi => ?_) (fun i hi j hj hij => ?_)
  · simp only [VG.Proof.MlKem.Arm.Encaps.lay, List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · exact hp.f_scr
    · exact VG.Proof.MlKem.Arm.Encaps.stack_fit hp
    · exact hp.f_ek
    · exact hp.f_key
    · exact hp.f_ct
  · simp only [VG.Proof.MlKem.Arm.Encaps.lay, List.length_cons, List.length_nil] at hi hj
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
    simp only [VG.Proof.MlKem.Arm.Encaps.lay, Lay.size, List.getD_cons_zero, List.getD_cons_succ] <;>
    first | omega | skip
    · rw [es]; exact hp.b_scr.symm
    · exact hp.d_ek_scr.symm
    · exact hp.d_key_scr.symm
    · exact hp.d_ct_scr.symm
    · rw [es]; exact hp.b_ek
    · rw [es]; exact hp.b_key
    · rw [es]; exact hp.b_ct
    · exact hp.d_ek_key
    · exact hp.d_ek_ct
    · exact hp.d_key_ct

theorem layM_ok : (VG.Proof.MlKem.Arm.Encaps.layM s₀ K).Ok := by
  have es := VG.Proof.MlKem.Arm.Encaps.stack_eq hp
  refine Lay.ok_of (fun i hi => ?_) (fun i hi j hj hij => ?_)
  · simp only [VG.Proof.MlKem.Arm.Encaps.layM, List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact hp.f_scr
    · exact VG.Proof.MlKem.Arm.Encaps.stack_fit hp
    · exact hp.f_m
  · simp only [VG.Proof.MlKem.Arm.Encaps.layM, List.length_cons, List.length_nil] at hi hj
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
    rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl <;>
    simp only [VG.Proof.MlKem.Arm.Encaps.layM, Lay.size, List.getD_cons_zero, List.getD_cons_succ] <;>
    first | omega | skip
    · rw [es]; exact hp.b_scr.symm
    · exact hp.d_m_scr.symm
    · rw [es]; exact hp.b_m

end

/-- What every phase keeps: the pointers, our caller's registers in
`scratch`, and `ek`. -/
structure EnEnv (K : KemLay) (s₀ s : State) : Prop where
  ctx : VG.Proof.MlKem.Arm.Ctx (VG.Proof.MlKem.Arm.Encaps.lay s₀ K) s
  r4 : s.gpr .r4 = VG.Proof.MlKem.Arm.Encaps.pEk s₀
  r6 : s.gpr .r6 = VG.Proof.MlKem.Arm.Encaps.pKey s₀
  r8 : s.gpr .r8 = VG.Proof.MlKem.Arm.Encaps.pCt s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  sav : VG.Proof.MlKem.Arm.Saved s.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 840) s₀.gpr
  savlr : s.mem.readW ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 872) 32 = s₀.gpr .lr
  ek : bytesAt s.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 2 0) K.ekLen = bytesAt s₀.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 2 0) K.ekLen

/-- A region the phases may change: apart from the saved registers and `ek`. -/
def okW (K : KemLay) (w : Nat × Nat × Nat) : Bool := VG.Proof.MlKem.Arm.sepB (VG.Proof.MlKem.Arm.Encaps.eSz K) (0, 840, 36) w && VG.Proof.MlKem.Arm.sepB (VG.Proof.MlKem.Arm.Encaps.eSz K) (2, 0, K.ekLen) w

/-- The buffer of each pointer register. -/
def eidx : Reg → Nat
  | .r4 => 2 | .r6 => 3 | .r8 => 4 | _ => 0

/-- Decides a fact about the offsets in the buffers. -/
macro "edecide" : tactic => `(tactic| first
  | decide
  | ((try simp only [lay_sizes, layM_sizes, eSz, okW, eidx, kRegs, List.all_cons, List.all_nil, List.all_append,
        List.map_cons, List.map_nil, trip, Bool.and_true])
     (try have := (‹KemLay.WF _›).scr)
     kdecide))

theorem EnEnv.keep {K : KemLay} {s₀ s s' : State} (hp : VG.Proof.MlKem.Arm.Encaps.Pre K s₀) (h : VG.Proof.MlKem.Arm.Encaps.EnEnv K s₀ s) {xs : List Reg} {W : List (Nat × Nat × Nat)}
    (hk : VG.Proof.MlKem.Arm.KeptX xs ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).RL W) s s') (hx : ∀ r ∈ [Reg.r4, .r6, .r7, .r8], r ∉ xs) (hW : W.all (VG.Proof.MlKem.Arm.Encaps.okW K) = true) :
    VG.Proof.MlKem.Arm.Encaps.EnEnv K s₀ s' := by
  have hL := VG.Proof.MlKem.Arm.Encaps.lay_ok hp
  have h1 : VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.Encaps.lay s₀ K).sizes (0, 840, 36) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw; simp only [VG.Proof.MlKem.Arm.Encaps.okW, Bool.and_eq_true] at this; exact this.1
  have h2 : VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.Encaps.lay s₀ K).sizes (2, 0, K.ekLen) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw; simp only [VG.Proof.MlKem.Arm.Encaps.okW, Bool.and_eq_true] at this; exact this.2
  have hd := Lay.disjAll hL h1
  have hc : (Lay.R (VG.Proof.MlKem.Arm.Encaps.lay s₀ K) 0 840 36).Contains ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 872) 4 := by
    simp only [Region.Contains]; bv_omega
  refine ⟨hk.ctx (by simp at hx; exact hx.2.2.1) h.ctx, ?_, ?_, ?_, hk.rd.trans h.rd, hk.wr.trans h.wr,
    hk.sp.trans h.sp, fun i hi => ?_, ?_, ?_⟩
  · rw [hk.cs .r4 (by decide) (by decide) (hx .r4 (by simp)), h.r4]
  · rw [hk.cs .r6 (by decide) (by decide) (hx .r6 (by simp)), h.r6]
  · rw [hk.cs .r8 (by decide) (by decide) (hx .r8 (by simp)), h.r8]
  · rw [hk.frame.readW (r := Lay.R (VG.Proof.MlKem.Arm.Encaps.lay s₀ K) 0 840 36) (by simp only [Region.Contains]; bv_omega) hd (by decide)]
    exact h.sav i hi
  · rw [hk.frame.readW hc hd (by decide)]; exact h.savlr
  · rw [Lay.bytes_keep hL hk.frame h2 (by have := hp.wf; offs)]; exact h.ek

theorem buf_wr {K : KemLay} {s₀ : State} (hp : VG.Proof.MlKem.Arm.Encaps.Pre K s₀) :
    (VG.Proof.MlKem.Arm.Encaps.lay s₀ K).buf 0 ∈ s₀.wr ∧ (VG.Proof.MlKem.Arm.Encaps.lay s₀ K).buf 3 ∈ s₀.wr ∧ (VG.Proof.MlKem.Arm.Encaps.lay s₀ K).buf 4 ∈ s₀.wr ∧
      (VG.Proof.MlKem.Arm.Encaps.lay s₀ K).buf 2 ∈ s₀.rd ++ s₀.wr ∧ (VG.Proof.MlKem.Arm.Encaps.layM s₀ K).buf 2 ∈ s₀.rd ++ s₀.wr ∧ (VG.Proof.MlKem.Arm.Encaps.layM s₀ K).buf 0 ∈ s₀.wr := by
  rw [hp.wr, hp.rd]; simp [Lay.buf, VG.Proof.MlKem.Arm.Encaps.lay, VG.Proof.MlKem.Arm.Encaps.layM]

/-! ## The setup -/

theorem ldrSp_ok {K : KemLay} {s₀ : State} (hp : VG.Proof.MlKem.Arm.Encaps.Pre K s₀) :
    WP isa (.block [.ldrSp .r12 0]) s₀ fun s => s.gpr .r12 = VG.Proof.MlKem.Arm.Encaps.pScr s₀ ∧
      (∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r) ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp := by
  have hin : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 0)) 4 := by
    refine ⟨⟨stackArgAddr s₀ 0, 4⟩, by rw [hp.rd]; simp, ?_⟩
    exact Region.contains_self _ _
  have o0 : (0 : Nat) < 4096 := by decide
  run_block [hin, o0]
  refine ⟨rfl, fun r hr => ?_, trivial⟩
  show (if r = .r12 then _ else s₀.gpr r) = s₀.gpr r
  exact ite_eq_right hr

theorem setup_ok {K : KemLay} {s₀ s₁ : State} (hp : VG.Proof.MlKem.Arm.Encaps.Pre K s₀) (h12 : s₁.gpr .r12 = VG.Proof.MlKem.Arm.Encaps.pScr s₀)
    (hr : ∀ r, r ≠ .r12 → s₁.gpr r = s₀.gpr r) (hm : s₁.mem = s₀.mem) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr)
    (hsp : s₁.sp = s₀.sp) :
    WP isa (.block encapsSetup) s₁ fun s => VG.Proof.MlKem.Arm.Encaps.EnEnv K s₀ s ∧ s.gpr .r5 = VG.Proof.MlKem.Arm.Encaps.pM s₀ ∧
      bytesAt s.mem ((VG.Proof.MlKem.Arm.Encaps.layM s₀ K).A 2 0) 32 = bytesAt s₀.mem ((VG.Proof.MlKem.Arm.Encaps.layM s₀ K).A 2 0) 32 := by
  have hL := VG.Proof.MlKem.Arm.Encaps.lay_ok hp
  have hK := hp.wf
  have scr := hK.scr
  have fc := hp.f_scr
  obtain ⟨w0, -, -, -, -, -⟩ := VG.Proof.MlKem.Arm.Encaps.buf_wr hp
  have wS : ∀ {o n : Nat}, o + n ≤ K.scratch → InRegions s₁.wr ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 o) n := fun h => by
    rw [hwr]; exact Lay.covers w0 h _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [encapsSetup, WP.block_append_iff]
  refine WP.mono (saveRegs_ok .r12 (off := 840) (by decide) (by rw [h12]; exact fit_le (by omega) fc) fun i hi => by
    rw [h12, add_ofNat_add]; exact wS (by omega)) fun s₂ h₂ => ?_
  have g12 : s₂.gpr .r12 = VG.Proof.MlKem.Arm.Encaps.pScr s₀ := by rw [h₂.gpr, h12]
  have e872 : State.addr (s₂.gpr .r12 + BitVec.ofNat 32 (oSave + 32)) = (VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 872 := by
    rw [g12]; exact addr_add (by offs)
  have i872 : InRegions s₂.wr (State.addr (s₂.gpr .r12 + BitVec.ofNat 32 (oSave + 32))) 4 := by
    rw [e872, h₂.wr]; exact wS (by omega)
  have o1 : oSave + 32 < 4096 := by decide
  run_block [i872, o1]
  have ne1 : ∀ i < 8, ∀ (m : Mem) (v : BitVec 32), (m.writeW ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 872) v).readW
      ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 = m.readW ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 :=
    fun i hi m v => Mem.readW_writeW_sep (fun x h1 h2 => by bv_omega) (by decide)
  have g : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r hr' => by rw [h₂.gpr, hr r hr']
  have hne : ∀ i < 8, savedRegs.getD i Reg.r4 ≠ Reg.r12 := by decide
  have fr₀ : Frame ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).RL [(0, 840, 36)]) s₀.mem s₂.mem := by
    rw [← hm]
    refine h₂.frame.sub fun r hr' => ⟨Lay.R (VG.Proof.MlKem.Arm.Encaps.lay s₀ K) 0 840 36, by simp, ?_⟩
    rw [List.mem_singleton] at hr'; subst hr'
    show Region.Sub ⟨State.addr (s₁.gpr .r12) + BitVec.ofNat 64 840, 32⟩ _
    rw [h12, ← VG.Proof.MlKem.Arm.Encaps.lay_ptr0]
    exact Lay.R_sub_R hL (by simp [VG.Proof.MlKem.Arm.Encaps.lay]) (by decide) (by decide) (by simp [VG.Proof.MlKem.Arm.Encaps.lay]; omega)
  have c872 : ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).R 0 840 36).Contains ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 872) 4 := by
    simp only [Region.Contains]; bv_omega
  refine ⟨⟨⟨hL, scr, rfl, by simp [VG.Proof.MlKem.Arm.Encaps.lay], ?_, by show 8 ≤ s₂.sp.toNat; rw [h₂.sp, hsp]; exact hp.sp8, ?_, ?_⟩,
    ?_, ?_, ?_, h₂.rd.trans hrd, h₂.wr.trans hwr, h₂.sp.trans hsp, fun i hi => ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [h₂.gpr, h12]; rfl
  · show s₀.sp - BitVec.ofNat 32 8 = s₂.sp - BitVec.ofNat 32 8
    rw [h₂.sp, hsp]
  · show (⟨State.addr (VG.Proof.MlKem.Arm.Encaps.pScr s₀), K.scratch⟩ : Region) ∈ s₂.wr
    rw [h₂.wr, hwr, hp.wr]; simp
  · simp [g .r0 (by decide)]; rfl
  · simp [g .r2 (by decide)]; rfl
  · simp [g .r3 (by decide)]; rfl
  · show (s₂.mem.writeW _ _).readW _ _ = _
    rw [e872, ne1 i hi]
    have := h₂.saved i hi
    rw [h12] at this
    exact this.trans (hr _ (hne i hi))
  · show (s₂.mem.writeW _ _).readW _ _ = _
    rw [e872, Mem.readW_writeW_self32, h₂.gpr, hr .lr (by decide)]
  · show bytesAt (s₂.mem.writeW _ _) _ _ = _
    rw [e872]
    exact Lay.bytes_keep hL (fr₀.writeW (List.mem_singleton_self _) _ c872) (by edecide) (by offs)
  · simp [g .r1 (by decide)]; rfl
  · show bytesAt (s₂.mem.writeW _ _) _ _ = _
    rw [e872]
    have fM : Frame ((VG.Proof.MlKem.Arm.Encaps.layM s₀ K).RL [(0, 840, 36)]) s₀.mem (s₂.mem.writeW ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 872) (s₂.gpr .lr)) := by
      have := fr₀.writeW (List.mem_singleton_self _) (s₂.gpr .lr) c872
      simpa only [Lay.RL, List.map_cons, List.map_nil, Lay.R, VG.Proof.MlKem.Arm.Encaps.lay_ptr0, VG.Proof.MlKem.Arm.Encaps.layM_ptr0] using this
    exact Lay.bytes_keep (VG.Proof.MlKem.Arm.Encaps.layM_ok hp) fM (by edecide) (by decide)


/-! ## `m` copied -/

/-- `m`. -/
abbrev M (K : KemLay) (s₀ : State) : List Byte := bytesAt s₀.mem ((VG.Proof.MlKem.Arm.Encaps.layM s₀ K).A 2 0) 32

/-- `ek`. -/
abbrev EK (K : KemLay) (s₀ : State) : List Byte := bytesAt s₀.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 2 0) K.ekLen

theorem layA0 (K : KemLay) (s₀ : State) (o : Nat) : (VG.Proof.MlKem.Arm.Encaps.layM s₀ K).A 0 o = (VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 o := by
  simp only [Lay.A, VG.Proof.MlKem.Arm.Encaps.lay_ptr0, VG.Proof.MlKem.Arm.Encaps.layM_ptr0]

theorem copyM_ok {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.Encaps.Pre K s₀) (h : VG.Proof.MlKem.Arm.Encaps.EnEnv K s₀ s) (h5 : s.gpr .r5 = VG.Proof.MlKem.Arm.Encaps.pM s₀)
    (hm : bytesAt s.mem ((VG.Proof.MlKem.Arm.Encaps.layM s₀ K).A 2 0) 32 = VG.Proof.MlKem.Arm.Encaps.M K s₀) :
    WP isa (copy .r5 0 .r7 oMsg 32) s fun s' =>
      VG.Proof.MlKem.Arm.Encaps.EnEnv K s₀ s' ∧ bytesAt s'.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 oMsg) 32 = VG.Proof.MlKem.Arm.Encaps.M K s₀ := by
  have hK := hp.wf
  obtain ⟨-, -, -, -, wM, wM0⟩ := VG.Proof.MlKem.Arm.Encaps.buf_wr hp
  refine WP.mono (VG.Proof.MlKem.Arm.copyL (VG.Proof.MlKem.Arm.Encaps.layM_ok hp) (i := 2) (j := 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ h5
    (by rw [h.ctx.r7, VG.Proof.MlKem.Arm.Encaps.lay_ptr0, VG.Proof.MlKem.Arm.Encaps.layM_ptr0]) (by edecide) (by edecide) (by edecide) (by edecide) (by edecide)
    (by edecide) (by rw [h.rd, h.wr]; exact wM) (by rw [h.wr]; exact wM0)) fun s' ⟨k, e⟩ => ⟨?_, ?_⟩
  · have k' : Kept ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).RL [(0, oMsg, 32)]) s s' := by
      simpa only [Lay.RL, List.map_cons, List.map_nil, Lay.R, VG.Proof.MlKem.Arm.Encaps.lay_ptr0, VG.Proof.MlKem.Arm.Encaps.layM_ptr0] using k
    exact h.keep hp (k'.x []) (by simp) (by edecide)
  · rw [← VG.Proof.MlKem.Arm.Encaps.layA0, e, hm]

theorem ptr5_ok {s : State} :
    WP isa (.block [ptrTo .r5 .r7 oMsg]) s fun s' =>
      VG.Proof.MlKem.Arm.KeptX [.r5] [] s s' ∧ s'.gpr .r5 = s.gpr .r7 + BitVec.ofNat 32 oMsg ∧ s'.mem = s.mem := by
  have e1 : encodable (BitVec.ofNat 32 oMsg) = true := by decide
  run_block [ptrTo, e1]
  refine ⟨⟨fun r _ _ hx => ?_, rfl, rfl, rfl, Frame.refl _ _⟩, trivial⟩
  show (if r = .r5 then _ else s.gpr r) = s.gpr r
  exact ite_eq_right (fun e : r = .r5 => hx (by rw [e]; exact List.mem_singleton_self _))

/-! ## The hashes -/

theorem pieceE {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.Encaps.Pre K s₀) (h : VG.Proof.MlKem.Arm.Encaps.EnEnv K s₀ s) {p : Piece} {w : Bool}
    (hb : p.base = .r4 ∨ p.base = .r7) (hw : w = true → p.base = .r7)
    (hoe : encodable (BitVec.ofNat 32 p.off) = true) (hle : encodable (BitVec.ofNat 32 p.len) = true)
    (hpos : 0 < p.len) (hlt : p.off + p.len < 2 ^ 32)
    (hsep : VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.Encaps.eSz K) (VG.Proof.MlKem.Arm.Encaps.eidx p.base, p.off, p.len) VG.Proof.MlKem.Arm.kRegs = true) :
    VG.Proof.MlKem.Arm.PieceOk (VG.Proof.MlKem.Arm.Encaps.lay s₀ K) VG.Proof.MlKem.Arm.Encaps.eidx s w p := by
  have hK := hp.wf
  obtain ⟨w0, -, -, w2, -, -⟩ := VG.Proof.MlKem.Arm.Encaps.buf_wr hp
  rw [← h.wr] at w0
  rw [← h.wr, ← h.rd] at w2
  refine ⟨?_, ?_, hoe, hle, hpos, hlt, hsep, ?_⟩
  · rcases hb with e | e <;> rw [e] <;> decide
  · rcases hb with e | e <;> rw [e]
    · exact h.r4
    · exact h.ctx.r7
  · cases w
    · simp only [Bool.false_eq_true, ite_false]
      rcases hb with e | e <;> rw [e]
      · exact w2
      · exact VG.Proof.MlKem.Arm.mem_rd_wr w0
    · simp only [ite_true]
      rw [hw rfl]; exact w0

theorem hashH_ok {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.Encaps.Pre K s₀) (h : VG.Proof.MlKem.Arm.Encaps.EnEnv K s₀ s) :
    WP isa (hash 136 0x06 [⟨.r4, 0, K.ekLen⟩] [⟨.r7, oHek, 32⟩]) s fun s' =>
      VG.Proof.MlKem.Arm.Encaps.EnEnv K s₀ s' ∧ Frame ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).RL (VG.Proof.MlKem.Arm.kRegs ++ [(0, oHek, 32)])) s.mem s'.mem ∧ s'.gpr .r5 = s.gpr .r5 ∧
      bytesAt s'.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 oHek) 32 = H (VG.Proof.MlKem.Arm.Encaps.EK K s₀) := by
  have hK := hp.wf
  have hin : ∀ p ∈ [(⟨.r4, 0, K.ekLen⟩ : Piece)], VG.Proof.MlKem.Arm.PieceOk (VG.Proof.MlKem.Arm.Encaps.lay s₀ K) VG.Proof.MlKem.Arm.Encaps.eidx s false p := by
    intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
    exact VG.Proof.MlKem.Arm.Encaps.pieceE hp h (.inl rfl) (by simp) VG.Proof.MlKem.Arm.enc0 hK.encEk (by dsimp only; offs) (by dsimp only; offs) (by edecide)
  have hout : ∀ p ∈ [(⟨.r7, oHek, 32⟩ : Piece)], VG.Proof.MlKem.Arm.PieceOk (VG.Proof.MlKem.Arm.Encaps.lay s₀ K) VG.Proof.MlKem.Arm.Encaps.eidx s true p := by
    intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
    exact VG.Proof.MlKem.Arm.Encaps.pieceE hp h (.inr rfl) (fun _ => rfl) (by edecide) (by edecide) (by edecide) (by edecide) (by edecide)
  refine WP.mono (VG.Proof.MlKem.Arm.hash_ok (idx := VG.Proof.MlKem.Arm.Encaps.eidx) VG.Proof.MlKem.rate136 (by edecide) (by edecide) (by edecide) h.ctx
    (List.cons_ne_nil _ _) hin hout (List.pairwise_singleton _ _)) fun s' ⟨k, o⟩ =>
    ⟨h.keep hp (k.x []) (by simp) (by edecide), k.frame, k.cs .r5 (by edecide) (by edecide), ?_⟩
  have e := o.1
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] at e
  refine e.trans ?_
  show _ = H (VG.Proof.MlKem.Arm.Encaps.EK K s₀)
  have ek : bytesAt s.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 2 0) K.ekLen = VG.Proof.MlKem.Arm.Encaps.EK K s₀ := h.ek
  rw [VG.Proof.MlKem.H_eq, ← ek]; rfl

theorem hashG_ok {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.Encaps.Pre K s₀) (h : VG.Proof.MlKem.Arm.Encaps.EnEnv K s₀ s)
    (hm : bytesAt s.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 oMsg) 32 = VG.Proof.MlKem.Arm.Encaps.M K s₀) (hh : bytesAt s.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 oHek) 32 = H (VG.Proof.MlKem.Arm.Encaps.EK K s₀)) :
    WP isa (hash 72 0x06 [⟨.r7, oMsg, 32⟩, ⟨.r7, oHek, 32⟩] [⟨.r7, oG, 64⟩]) s fun s' =>
      VG.Proof.MlKem.Arm.Encaps.EnEnv K s₀ s' ∧ Frame ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).RL (VG.Proof.MlKem.Arm.kRegs ++ [(0, oG, 64)])) s.mem s'.mem ∧ s'.gpr .r5 = s.gpr .r5 ∧
      bytesAt s'.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 oG) 32 = (G (VG.Proof.MlKem.Arm.Encaps.M K s₀ ++ H (VG.Proof.MlKem.Arm.Encaps.EK K s₀))).1 ∧
      bytesAt s'.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 oSigma) 32 = (G (VG.Proof.MlKem.Arm.Encaps.M K s₀ ++ H (VG.Proof.MlKem.Arm.Encaps.EK K s₀))).2 := by
  have hK := hp.wf
  have hin : ∀ p ∈ [(⟨.r7, oMsg, 32⟩ : Piece), ⟨.r7, oHek, 32⟩], VG.Proof.MlKem.Arm.PieceOk (VG.Proof.MlKem.Arm.Encaps.lay s₀ K) VG.Proof.MlKem.Arm.Encaps.eidx s false p := by
    intro p hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · exact VG.Proof.MlKem.Arm.Encaps.pieceE hp h (.inr rfl) (by simp) (by edecide) (by edecide) (by edecide) (by edecide) (by edecide)
    · exact VG.Proof.MlKem.Arm.Encaps.pieceE hp h (.inr rfl) (by simp) (by edecide) (by edecide) (by edecide) (by edecide) (by edecide)
  have hout : ∀ p ∈ [(⟨.r7, oG, 64⟩ : Piece)], VG.Proof.MlKem.Arm.PieceOk (VG.Proof.MlKem.Arm.Encaps.lay s₀ K) VG.Proof.MlKem.Arm.Encaps.eidx s true p := by
    intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
    exact VG.Proof.MlKem.Arm.Encaps.pieceE hp h (.inr rfl) (fun _ => rfl) (by edecide) (by edecide) (by edecide) (by edecide) (by edecide)
  have hin' : (List.map ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).pb VG.Proof.MlKem.Arm.Encaps.eidx s.mem) [⟨.r7, oMsg, 32⟩, ⟨.r7, oHek, 32⟩]).flatten =
      VG.Proof.MlKem.Arm.Encaps.M K s₀ ++ H (VG.Proof.MlKem.Arm.Encaps.EK K s₀) := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    show bytesAt s.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 oMsg) 32 ++ bytesAt s.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 oHek) 32 = _
    rw [hm, hh]
  refine WP.mono (VG.Proof.MlKem.Arm.hash_ok VG.Proof.MlKem.rate72 (by edecide) (by edecide) (by edecide) h.ctx (List.cons_ne_nil _ _)
    hin hout (List.pairwise_singleton _ _)) fun s' ⟨k', o'⟩ => ⟨?_, k'.frame, k'.cs .r5 (by edecide) (by edecide), ?_⟩
  · exact h.keep hp (k'.x []) (by simp) (by edecide)
  · have e1 := o'.1
    rw [hin'] at e1
    have e2 : bytesAt s'.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 oG) 64 = (G (VG.Proof.MlKem.Arm.Encaps.M K s₀ ++ H (VG.Proof.MlKem.Arm.Encaps.EK K s₀))).1 ++ (G (VG.Proof.MlKem.Arm.Encaps.M K s₀ ++ H (VG.Proof.MlKem.Arm.Encaps.EK K s₀))).2 :=
      e1.trans (VG.Proof.MlKem.Arm.G_split _)
    rw [show (64 : Nat) = 32 + 32 from rfl, bytesAt_add] at e2
    have l1 : (bytesAt s'.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 oG) 32).length = (G (VG.Proof.MlKem.Arm.Encaps.M K s₀ ++ H (VG.Proof.MlKem.Arm.Encaps.EK K s₀))).1.length := by
      rw [bytesAt_length, VG.Proof.MlKem.G_fst_length]
    obtain ⟨r1, r2⟩ := List.append_inj e2 l1
    refine ⟨r1, ?_⟩
    show bytesAt s'.mem (State.addr ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).ptr 0) + BitVec.ofNat 64 (888 + 32)) 32 = _
    rw [← add_ofNat_add]; exact r2

theorem copyK_ok {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.Encaps.Pre K s₀) (h : VG.Proof.MlKem.Arm.Encaps.EnEnv K s₀ s) :
    WP isa (copy .r7 oG .r6 0 32) s fun s' => VG.Proof.MlKem.Arm.Encaps.EnEnv K s₀ s' ∧ Kept ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).RL [(3, 0, 32)]) s s' ∧
      bytesAt s'.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 3 0) 32 = bytesAt s.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 oG) 32 := by
  have hK := hp.wf
  obtain ⟨w0, w3, -, -, -, -⟩ := VG.Proof.MlKem.Arm.Encaps.buf_wr hp
  exact WP.mono (VG.Proof.MlKem.Arm.copyL (VG.Proof.MlKem.Arm.Encaps.lay_ok hp) (i := 0) (j := 3) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ h.ctx.r7 h.r6
    (by edecide) (by edecide) (by edecide) (by edecide) (by edecide) (by edecide)
    (by rw [h.rd, h.wr]; exact VG.Proof.MlKem.Arm.mem_rd_wr w0) (by rw [h.wr]; exact w3)) fun s' ⟨k, e⟩ =>
    ⟨h.keep hp (k.x []) (by simp) (by edecide), k, e⟩

/-! ## K-PKE.Encrypt -/

/-- The buffers of `encrypt`: `ek`, the copy of `m`, and `ct`. -/
abbrev eb : VG.Proof.MlKem.Arm.Enc.EB := ⟨2, 0, 0, oMsg, 4, 0⟩

theorem encPre {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.Encaps.Pre K s₀) (h : VG.Proof.MlKem.Arm.Encaps.EnEnv K s₀ s) (h5 : s.gpr .r5 = (VG.Proof.MlKem.Arm.Encaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 oMsg) :
    VG.Proof.MlKem.Arm.Enc.EncPre K (VG.Proof.MlKem.Arm.Encaps.lay s₀ K) VG.Proof.MlKem.Arm.Encaps.eb s := by
  have hK := hp.wf
  obtain ⟨w0, -, w4, w2, -, -⟩ := VG.Proof.MlKem.Arm.Encaps.buf_wr hp
  exact ⟨hK, hp.calls, h.ctx, by rw [h.r4, show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero]; rfl, h5,
    by rw [h.r8, show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero]; rfl, by edecide, by edecide, by edecide,
    by rw [h.rd, h.wr]; exact w2, by rw [h.rd, h.wr]; exact VG.Proof.MlKem.Arm.mem_rd_wr w0, by rw [h.wr]; exact w4⟩

theorem encW_ok {K : KemLay} (hK : K.WF) :
    (VG.Proof.MlKem.Arm.Enc.encW K VG.Proof.MlKem.Arm.Encaps.eb).all (VG.Proof.MlKem.Arm.Encaps.okW K) = true ∧ VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.Encaps.eSz K) (3, 0, 32) (VG.Proof.MlKem.Arm.Enc.encW K VG.Proof.MlKem.Arm.Encaps.eb) = true := by
  have := hK.scr
  constructor <;> edecide


/-! ## The phases, from the copy of `m` on -/

section
variable (K : KemLay) (s₀ : State)

/-- `K`, the first output of `G(m ‖ H(ek))`. -/
abbrev KK : List Byte := (G (VG.Proof.MlKem.Arm.Encaps.M K s₀ ++ H (VG.Proof.MlKem.Arm.Encaps.EK K s₀))).1

/-- `r`, the second output of `G(m ‖ H(ek))`. -/
abbrev RR : List Byte := (G (VG.Proof.MlKem.Arm.Encaps.M K s₀ ++ H (VG.Proof.MlKem.Arm.Encaps.EK K s₀))).2

/-- After the copy of `m`, with its pointer in `r5`. -/
abbrev F4 (s : State) : Prop := VG.Proof.MlKem.Arm.Encaps.EnEnv K s₀ s ∧ s.gpr .r5 = (VG.Proof.MlKem.Arm.Encaps.lay s₀ K).ptr 0 + BitVec.ofNat 32 oMsg ∧
  bytesAt s.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 oMsg) 32 = VG.Proof.MlKem.Arm.Encaps.M K s₀

end

section
variable {K : KemLay} {s₀ : State} (hp : VG.Proof.MlKem.Arm.Encaps.Pre K s₀)
include hp

theorem s4_ok {s : State} (h : VG.Proof.MlKem.Arm.Encaps.EnEnv K s₀ s) (hm : bytesAt s.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 oMsg) 32 = VG.Proof.MlKem.Arm.Encaps.M K s₀) :
    WP isa (.block [ptrTo .r5 .r7 oMsg]) s (VG.Proof.MlKem.Arm.Encaps.F4 K s₀) :=
  WP.mono VG.Proof.MlKem.Arm.Encaps.ptr5_ok fun _ ⟨k, g5, m⟩ =>
    ⟨h.keep hp (W := []) k (by simp) rfl, by rw [g5, h.ctx.r7], by rw [m]; exact hm⟩

theorem s5_ok {s : State} (h : VG.Proof.MlKem.Arm.Encaps.F4 K s₀ s) :
    WP isa (hash 136 0x06 [⟨.r4, 0, K.ekLen⟩] [⟨.r7, oHek, 32⟩]) s fun s' =>
      VG.Proof.MlKem.Arm.Encaps.F4 K s₀ s' ∧ bytesAt s'.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 oHek) 32 = H (VG.Proof.MlKem.Arm.Encaps.EK K s₀) := by
  have hK := hp.wf
  exact WP.mono (VG.Proof.MlKem.Arm.Encaps.hashH_ok hp h.1) fun _ ⟨e, f, g5, hh⟩ =>
    ⟨⟨e, by rw [g5, h.2.1], (Lay.bytes_keep (VG.Proof.MlKem.Arm.Encaps.lay_ok hp) f (by edecide) (by edecide)).trans h.2.2⟩, hh⟩

theorem s6_ok {s : State} (h : VG.Proof.MlKem.Arm.Encaps.F4 K s₀ s ∧ bytesAt s.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 oHek) 32 = H (VG.Proof.MlKem.Arm.Encaps.EK K s₀)) :
    WP isa (hash 72 0x06 [⟨.r7, oMsg, 32⟩, ⟨.r7, oHek, 32⟩] [⟨.r7, oG, 64⟩]) s fun s' =>
      VG.Proof.MlKem.Arm.Encaps.F4 K s₀ s' ∧ bytesAt s'.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 oG) 32 = VG.Proof.MlKem.Arm.Encaps.KK K s₀ ∧ bytesAt s'.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 oSigma) 32 = VG.Proof.MlKem.Arm.Encaps.RR K s₀ := by
  have hK := hp.wf
  exact WP.mono (VG.Proof.MlKem.Arm.Encaps.hashG_ok hp h.1.1 h.1.2.2 h.2) fun _ ⟨e, f, g5, k, r⟩ =>
    ⟨⟨e, by rw [g5, h.1.2.1], (Lay.bytes_keep (VG.Proof.MlKem.Arm.Encaps.lay_ok hp) f (by edecide) (by edecide)).trans h.1.2.2⟩, k, r⟩

theorem s7_ok {s : State}
    (h : VG.Proof.MlKem.Arm.Encaps.F4 K s₀ s ∧ bytesAt s.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 oG) 32 = VG.Proof.MlKem.Arm.Encaps.KK K s₀ ∧ bytesAt s.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 oSigma) 32 = VG.Proof.MlKem.Arm.Encaps.RR K s₀) :
    WP isa (copy .r7 oG .r6 0 32) s fun s' =>
      VG.Proof.MlKem.Arm.Encaps.F4 K s₀ s' ∧ bytesAt s'.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 3 0) 32 = VG.Proof.MlKem.Arm.Encaps.KK K s₀ ∧ bytesAt s'.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 oSigma) 32 = VG.Proof.MlKem.Arm.Encaps.RR K s₀ := by
  have hK := hp.wf
  exact WP.mono (VG.Proof.MlKem.Arm.Encaps.copyK_ok hp h.1.1) fun _ ⟨e, k, key⟩ =>
    ⟨⟨e, by rw [k.cs .r5 (by edecide) (by edecide), h.1.2.1],
      (Lay.bytes_keep (VG.Proof.MlKem.Arm.Encaps.lay_ok hp) k.frame (by edecide) (by edecide)).trans h.1.2.2⟩, key.trans h.2.1,
      (Lay.bytes_keep (VG.Proof.MlKem.Arm.Encaps.lay_ok hp) k.frame (by edecide) (by edecide)).trans h.2.2⟩

theorem s8_ok {s : State}
    (h : VG.Proof.MlKem.Arm.Encaps.F4 K s₀ s ∧ bytesAt s.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 3 0) 32 = VG.Proof.MlKem.Arm.Encaps.KK K s₀ ∧ bytesAt s.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 0 oSigma) 32 = VG.Proof.MlKem.Arm.Encaps.RR K s₀) :
    WP isa K.encrypt s fun s' => VG.Proof.MlKem.Arm.Encaps.EnEnv K s₀ s' ∧ bytesAt s'.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 3 0) 32 = VG.Proof.MlKem.Arm.Encaps.KK K s₀ ∧
      s'.gpr .r11 = (if VG.Proof.MlKem.Arm.Enc.okEnc K.k (ekRho K.p (VG.Proof.MlKem.Arm.Encaps.EK K s₀)) K.k then 1 else 0) ∧
      bytesAt s'.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 4 0) K.ctLen =
        VG.Proof.MlKem.KPke.ct K.p (VG.Proof.MlKem.Arm.Enc.aEnc (ekRho K.p (VG.Proof.MlKem.Arm.Encaps.EK K s₀)) (VG.Proof.MlKem.Arm.Encaps.RR K s₀)) (VG.Proof.MlKem.Arm.Encaps.EK K s₀) (VG.Proof.MlKem.Arm.Encaps.M K s₀) (VG.Proof.MlKem.Arm.Encaps.RR K s₀) := by
  have hK := hp.wf
  have eρ : VG.Proof.MlKem.Arm.Enc.ρE K (VG.Proof.MlKem.Arm.Encaps.lay s₀ K) VG.Proof.MlKem.Arm.Encaps.eb s = ekRho K.p (VG.Proof.MlKem.Arm.Encaps.EK K s₀) := by
    show ekRho K.p (bytesAt s.mem ((VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 2 0) K.ekLen) = _
    rw [h.1.1.ek]
  have er : VG.Proof.MlKem.Arm.Enc.rB (VG.Proof.MlKem.Arm.Encaps.lay s₀ K) s = VG.Proof.MlKem.Arm.Encaps.RR K s₀ := h.2.2
  have e1 : VG.Proof.MlKem.Arm.Enc.ekB K (VG.Proof.MlKem.Arm.Encaps.lay s₀ K) VG.Proof.MlKem.Arm.Encaps.eb s = VG.Proof.MlKem.Arm.Encaps.EK K s₀ := h.1.1.ek
  have e2 : VG.Proof.MlKem.Arm.Enc.mB (VG.Proof.MlKem.Arm.Encaps.lay s₀ K) VG.Proof.MlKem.Arm.Encaps.eb s = VG.Proof.MlKem.Arm.Encaps.M K s₀ := h.1.2.2
  refine WP.mono (VG.Proof.MlKem.Arm.Enc.encrypt_ok (VG.Proof.MlKem.Arm.Encaps.encPre hp h.1.1 h.1.2.1)) fun s' ⟨K', r11, ct⟩ =>
    ⟨h.1.1.keep hp K' (by simp) (VG.Proof.MlKem.Arm.Encaps.encW_ok hK).1, (Lay.bytes_keep (VG.Proof.MlKem.Arm.Encaps.lay_ok hp) K'.frame (VG.Proof.MlKem.Arm.Encaps.encW_ok hK).2 (by decide)).trans h.2.1,
      ?_, ?_⟩
  · rw [r11]; show (if VG.Proof.MlKem.Arm.Enc.okEnc K.k (VG.Proof.MlKem.Arm.Enc.ρE K (VG.Proof.MlKem.Arm.Encaps.lay s₀ K) VG.Proof.MlKem.Arm.Encaps.eb s) K.k = true then _ else _) = _; rw [eρ]
  · rw [e1, e2] at ct
    show _ = VG.Proof.MlKem.KPke.ct K.p (VG.Proof.MlKem.Arm.Enc.aEnc (ekRho K.p (VG.Proof.MlKem.Arm.Encaps.EK K s₀)) (VG.Proof.MlKem.Arm.Encaps.RR K s₀)) (VG.Proof.MlKem.Arm.Encaps.EK K s₀) (VG.Proof.MlKem.Arm.Encaps.M K s₀) (VG.Proof.MlKem.Arm.Encaps.RR K s₀)
    rw [← eρ, ← er]; exact ct

end

/-! ## The whole function -/

theorem correct {K : KemLay} {s₀ : State} (hp : VG.Proof.MlKem.Arm.Encaps.Pre K s₀) :
    WP isa K.encaps s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      s.gpr .r0 = (if VG.Proof.MlKem.Arm.Enc.okEnc K.k (ekRho K.p (VG.Proof.MlKem.Arm.Encaps.EK K s₀)) K.k then 1 else 0) ∧
      bytesAt s.mem (State.addr (VG.Proof.MlKem.Arm.Encaps.pKey s₀)) 32 = VG.Proof.MlKem.Arm.Encaps.KK K s₀ ∧
      bytesAt s.mem (State.addr (VG.Proof.MlKem.Arm.Encaps.pCt s₀)) K.ctLen =
        VG.Proof.MlKem.KPke.ct K.p (VG.Proof.MlKem.Arm.Enc.aEnc (ekRho K.p (VG.Proof.MlKem.Arm.Encaps.EK K s₀)) (VG.Proof.MlKem.Arm.Encaps.RR K s₀)) (VG.Proof.MlKem.Arm.Encaps.EK K s₀) (VG.Proof.MlKem.Arm.Encaps.M K s₀) (VG.Proof.MlKem.Arm.Encaps.RR K s₀) := by
  have hK := hp.wf
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Encaps.ldrSp_ok hp) fun s₁ ⟨a, b, c, d, e, f⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Encaps.setup_ok hp a b c d e f) fun s₂ ⟨h₂, g5, m₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Encaps.copyM_ok hp h₂ g5 m₂) fun s₃ ⟨h₃, m₃⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Encaps.s4_ok hp h₃ m₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Encaps.s5_ok hp h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Encaps.s6_ok hp h₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Encaps.s7_ok hp h₆) fun s₇ h₇ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Encaps.s8_ok hp h₇) fun s₈ ⟨h₈, key₈, r11₈, ct₈⟩ => ?_)
  refine WP.mono (VG.Proof.MlKem.Arm.topEnd_ok h₈.ctx h₈.sav h₈.savlr) fun s ⟨pr, r0, m', sp'⟩ =>
    ⟨pr, sp'.trans h₈.sp, by rw [r0, r11₈], ?_, ?_⟩
  · rw [m', show State.addr (VG.Proof.MlKem.Arm.Encaps.pKey s₀) = (VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 3 0 by simp only [Lay.A, add_ofNat_zero]; rfl]
    exact key₈
  · rw [m', show State.addr (VG.Proof.MlKem.Arm.Encaps.pCt s₀) = (VG.Proof.MlKem.Arm.Encaps.lay s₀ K).A 4 0 by simp only [Lay.A, add_ofNat_zero]; rfl]
    exact ct₈

end VG.Proof.MlKem.Arm.Encaps

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.KeyGen`. -/
section

/-!
# ML-KEM on 32-bit ARM: key generation, correctness

`K.keygen` for any parameter set `K` (`KemLay.WF`). The buffers of the
function (`lay`): `scratch`, the stack, `seed`, `ek` and `dk`; what every
phase keeps (`KEnv`: the pointers, our caller's registers in `scratch`, the
seed); and the phases: the setup, `G(d ‖ k)` into `ρ` and `σ`, the `PRF`s
into `ŝ` and `ê`, the rows of `t̂ = Â ∘ ŝ + ê` encoded into `ek`, `ŝ` encoded
into `dk`, the copies of `ρ`, `ek` and `z`, and `H(ek)`.
-/

namespace VG.Proof.MlKem.Arm.KeyGen

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Enc (bytes_catK catK_congr)

section
variable (s₀ : State)

abbrev pSeed : BitVec 32 := s₀.gpr .r0
abbrev pEk : BitVec 32 := s₀.gpr .r1
abbrev pDk : BitVec 32 := s₀.gpr .r2
abbrev pScr : BitVec 32 := s₀.gpr .r3

/-- The buffers: `scratch`, the 8 bytes below the stack pointer, `seed`,
`ek` and `dk`. -/
def lay (K : KemLay) : VG.Proof.MlKem.Arm.Lay :=
  ⟨fun i => [VG.Proof.MlKem.Arm.KeyGen.pScr s₀, s₀.sp - BitVec.ofNat 32 8, VG.Proof.MlKem.Arm.KeyGen.pSeed s₀, VG.Proof.MlKem.Arm.KeyGen.pEk s₀, VG.Proof.MlKem.Arm.KeyGen.pDk s₀].getD i 0,
    [K.scratch, 8, 64, K.ekLen, K.dkLen]⟩

end

/-- The sizes of the buffers. -/
abbrev kSz (K : KemLay) : List Nat := [K.scratch, 8, 64, K.ekLen, K.dkLen]

theorem lay_sizes (K : KemLay) (s₀ : State) : (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).sizes = VG.Proof.MlKem.Arm.KeyGen.kSz K := rfl

/-- The precondition of the contract. -/
structure Pre (K : KemLay) (s₀ : State) : Prop where
  wf : K.WF
  calls : K.CallsOk
  sp8 : 8 ≤ s₀.sp.toNat
  rd : s₀.rd = [⟨State.addr (VG.Proof.MlKem.Arm.KeyGen.pSeed s₀), 64⟩]
  wr : s₀.wr = [⟨State.addr (VG.Proof.MlKem.Arm.KeyGen.pEk s₀), K.ekLen⟩, ⟨State.addr (VG.Proof.MlKem.Arm.KeyGen.pDk s₀), K.dkLen⟩, ⟨State.addr (VG.Proof.MlKem.Arm.KeyGen.pScr s₀), K.scratch⟩]
  d_se : (⟨State.addr (VG.Proof.MlKem.Arm.KeyGen.pSeed s₀), 64⟩ : Region).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.KeyGen.pEk s₀), K.ekLen⟩
  d_sd : (⟨State.addr (VG.Proof.MlKem.Arm.KeyGen.pSeed s₀), 64⟩ : Region).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.KeyGen.pDk s₀), K.dkLen⟩
  d_ss : (⟨State.addr (VG.Proof.MlKem.Arm.KeyGen.pSeed s₀), 64⟩ : Region).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.KeyGen.pScr s₀), K.scratch⟩
  d_ed : (⟨State.addr (VG.Proof.MlKem.Arm.KeyGen.pEk s₀), K.ekLen⟩ : Region).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.KeyGen.pDk s₀), K.dkLen⟩
  d_es : (⟨State.addr (VG.Proof.MlKem.Arm.KeyGen.pEk s₀), K.ekLen⟩ : Region).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.KeyGen.pScr s₀), K.scratch⟩
  d_ds : (⟨State.addr (VG.Proof.MlKem.Arm.KeyGen.pDk s₀), K.dkLen⟩ : Region).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.KeyGen.pScr s₀), K.scratch⟩
  b_s : (below s₀ 8).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.KeyGen.pSeed s₀), 64⟩
  b_e : (below s₀ 8).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.KeyGen.pEk s₀), K.ekLen⟩
  b_d : (below s₀ 8).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.KeyGen.pDk s₀), K.dkLen⟩
  b_c : (below s₀ 8).Disjoint ⟨State.addr (VG.Proof.MlKem.Arm.KeyGen.pScr s₀), K.scratch⟩
  f_s : (VG.Proof.MlKem.Arm.KeyGen.pSeed s₀).toNat + 64 ≤ 2 ^ 32
  f_e : (VG.Proof.MlKem.Arm.KeyGen.pEk s₀).toNat + K.ekLen ≤ 2 ^ 32
  f_d : (VG.Proof.MlKem.Arm.KeyGen.pDk s₀).toNat + K.dkLen ≤ 2 ^ 32
  f_c : (VG.Proof.MlKem.Arm.KeyGen.pScr s₀).toNat + K.scratch ≤ 2 ^ 32

section
variable {K : KemLay} {s₀ : State} (hp : VG.Proof.MlKem.Arm.KeyGen.Pre K s₀)
include hp

theorem stack_eq : (⟨State.addr (s₀.sp - BitVec.ofNat 32 8), 8⟩ : Region) = below s₀ 8 := by
  rw [addr_sub hp.sp8]

theorem lay_ok : (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).Ok := by
  have es := VG.Proof.MlKem.Arm.KeyGen.stack_eq hp
  refine Lay.ok_of (fun i hi => ?_) (fun i hi j hj hij => ?_)
  · simp only [VG.Proof.MlKem.Arm.KeyGen.lay, List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · exact hp.f_c
    · show (s₀.sp - BitVec.ofNat 32 8).toNat + 8 ≤ 2 ^ 32
      have := hp.sp8; have := s₀.sp.isLt; bv_omega
    · exact hp.f_s
    · exact hp.f_e
    · exact hp.f_d
  · simp only [VG.Proof.MlKem.Arm.KeyGen.lay, List.length_cons, List.length_nil] at hi hj
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
    simp only [VG.Proof.MlKem.Arm.KeyGen.lay, Lay.size, List.getD_cons_zero, List.getD_cons_succ] <;>
    first | omega | skip
    · rw [es]; exact hp.b_c.symm
    · exact hp.d_ss.symm
    · exact hp.d_es.symm
    · exact hp.d_ds.symm
    · rw [es]; exact hp.b_s
    · rw [es]; exact hp.b_e
    · rw [es]; exact hp.b_d
    · exact hp.d_se
    · exact hp.d_sd
    · exact hp.d_ed

end

/-- What every phase keeps: the pointers, our caller's registers in
`scratch`, and the seed. -/
structure KEnv (K : KemLay) (s₀ s : State) : Prop where
  ctx : VG.Proof.MlKem.Arm.Ctx (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K) s
  r4 : s.gpr .r4 = VG.Proof.MlKem.Arm.KeyGen.pSeed s₀
  r5 : s.gpr .r5 = VG.Proof.MlKem.Arm.KeyGen.pEk s₀
  r6 : s.gpr .r6 = VG.Proof.MlKem.Arm.KeyGen.pDk s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  sav : VG.Proof.MlKem.Arm.Saved s.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 840) s₀.gpr
  savlr : s.mem.readW ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 872) 32 = s₀.gpr .lr
  seed : bytesAt s.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 2 0) 64 = bytesAt s₀.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 2 0) 64

/-- A region the phases may change: apart from the saved registers and the seed. -/
def okW (K : KemLay) (w : Nat × Nat × Nat) : Bool := VG.Proof.MlKem.Arm.sepB (VG.Proof.MlKem.Arm.KeyGen.kSz K) (0, 840, 36) w && VG.Proof.MlKem.Arm.sepB (VG.Proof.MlKem.Arm.KeyGen.kSz K) (2, 0, 64) w

/-- The buffer of each pointer register. -/
def kidx : Reg → Nat
  | .r4 => 2 | .r5 => 3 | .r6 => 4 | _ => 0

/-- Decides a fact about the offsets in the buffers. -/
macro "ldecide" : tactic => `(tactic| first
  | decide
  | ((try simp only [lay_sizes, kSz, kidx, okW, kRegs, List.all_cons, List.all_nil, List.all_append, List.map_cons,
        List.map_nil, trip, Bool.and_true])
     (try have := (‹KemLay.WF _›).scr)
     kdecide))

theorem KEnv.keep {K : KemLay} {s₀ s s' : State} (hp : VG.Proof.MlKem.Arm.KeyGen.Pre K s₀) (h : VG.Proof.MlKem.Arm.KeyGen.KEnv K s₀ s) {xs : List Reg}
    {W : List (Nat × Nat × Nat)} (hk : VG.Proof.MlKem.Arm.KeptX xs ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).RL W) s s') (hx : ∀ r ∈ [Reg.r4, .r5, .r6, .r7], r ∉ xs)
    (hW : W.all (VG.Proof.MlKem.Arm.KeyGen.okW K) = true) : VG.Proof.MlKem.Arm.KeyGen.KEnv K s₀ s' := by
  have hL := VG.Proof.MlKem.Arm.KeyGen.lay_ok hp
  have h1 : VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).sizes (0, 840, 36) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw; simp only [VG.Proof.MlKem.Arm.KeyGen.okW, Bool.and_eq_true] at this; exact this.1
  have h2 : VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).sizes (2, 0, 64) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw; simp only [VG.Proof.MlKem.Arm.KeyGen.okW, Bool.and_eq_true] at this; exact this.2
  have hd := Lay.disjAll hL h1
  have hc : (Lay.R (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K) 0 840 36).Contains ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 872) 4 := by
    simp only [Region.Contains]; bv_omega
  refine ⟨hk.ctx (by simp at hx; exact hx.2.2.2) h.ctx, ?_, ?_, ?_, hk.rd.trans h.rd, hk.wr.trans h.wr,
    hk.sp.trans h.sp, fun i hi => ?_, ?_, ?_⟩
  · rw [hk.cs .r4 (by decide) (by decide) (hx .r4 (by simp)), h.r4]
  · rw [hk.cs .r5 (by decide) (by decide) (hx .r5 (by simp)), h.r5]
  · rw [hk.cs .r6 (by decide) (by decide) (hx .r6 (by simp)), h.r6]
  · rw [hk.frame.readW (r := Lay.R (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K) 0 840 36) (by simp only [Region.Contains]; bv_omega) hd (by decide)]
    exact h.sav i hi
  · rw [hk.frame.readW hc hd (by decide)]; exact h.savlr
  · rw [Lay.bytes_keep hL hk.frame h2 (by decide)]; exact h.seed

theorem buf_wr {K : KemLay} {s₀ : State} (hp : VG.Proof.MlKem.Arm.KeyGen.Pre K s₀) :
    (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).buf 0 ∈ s₀.wr ∧ (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).buf 3 ∈ s₀.wr ∧ (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).buf 4 ∈ s₀.wr ∧
      (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).buf 2 ∈ s₀.rd ++ s₀.wr := by
  rw [hp.wr, hp.rd]; simp [Lay.buf, VG.Proof.MlKem.Arm.KeyGen.lay]

theorem setup_ok {K : KemLay} {s₀ : State} (hp : VG.Proof.MlKem.Arm.KeyGen.Pre K s₀) :
    WP isa (.block K.kgSetup) s₀ fun s => VG.Proof.MlKem.Arm.KeyGen.KEnv K s₀ s ∧ s.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 oK) = BitVec.ofNat 8 K.k := by
  have hL := VG.Proof.MlKem.Arm.KeyGen.lay_ok hp
  have hK := hp.wf
  have fc := hp.f_c
  have := hK.scr
  obtain ⟨w0, -, -, -⟩ := VG.Proof.MlKem.Arm.KeyGen.buf_wr hp
  have wS : ∀ {o n : Nat}, o + n ≤ 32768 → InRegions s₀.wr ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 o) n := fun h =>
    Lay.covers w0 (by simp only [VG.Proof.MlKem.Arm.KeyGen.lay, Lay.size, List.getD_cons_zero]; omega) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [KemLay.kgSetup, WP.block_append_iff]
  refine WP.mono (saveRegs_ok .r3 (off := 840) (by decide) (fit_le (by omega) fc) fun i hi => by
    rw [add_ofNat_add]; exact wS (by omega)) fun s₁ h₁ => ?_
  have g3 : s₁.gpr .r3 = VG.Proof.MlKem.Arm.KeyGen.pScr s₀ := by rw [h₁.gpr]
  have e872 : State.addr (s₁.gpr .r3 + BitVec.ofNat 32 (oSave + 32)) = (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 872 := by
    rw [g3]; exact addr_add (by offs)
  have e1152 : State.addr (s₁.gpr .r3 + BitVec.ofNat 32 oK) = (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 1152 := by
    rw [g3]; exact addr_add (by offs)
  have i872 : InRegions s₁.wr (State.addr (s₁.gpr .r3 + BitVec.ofNat 32 (oSave + 32))) 4 := by
    rw [e872, h₁.wr]; exact wS (by decide)
  have i1152 : InRegions s₁.wr (State.addr (s₁.gpr .r3 + BitVec.ofNat 32 oK)) 1 := by
    rw [e1152, h₁.wr]; exact wS (by decide)
  have o1 : oSave + 32 < 4096 := by decide
  have o2 : oK < 4096 := by decide
  have e3 : encodable (BitVec.ofNat 32 K.k) = true := by kenc
  run_block [i872, i1152, o1, o2, e3]
  have eS : (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 840 = State.addr (s₀.gpr .r3) + BitVec.ofNat 64 840 := rfl
  have ne1 : ∀ i < 8, ∀ (m : Mem) (v : BitVec 32), (m.writeW ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 872) v).readW
      ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 = m.readW ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 :=
    fun i hi m v => Mem.readW_writeW_sep (fun x h1 h2 => by bv_omega) (by decide)
  have ne2 : ∀ i < 9, ∀ (m : Mem) (v : Byte), (m.writeW ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 1152) v).readW
      ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 = m.readW ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 :=
    fun i hi m v => Mem.readW_writeW_sep (fun x h1 h2 => by bv_omega) (by decide)
  refine ⟨⟨⟨hL, hK.scr, rfl, by simp [VG.Proof.MlKem.Arm.KeyGen.lay], ?_, by show 8 ≤ s₁.sp.toNat; rw [h₁.sp]; exact hp.sp8, ?_, ?_⟩, ?_, ?_, ?_,
    h₁.rd, h₁.wr, h₁.sp, fun i hi => ?_, ?_, ?_⟩, ?_⟩
  · simp [h₁.gpr]; rfl
  · show s₀.sp - BitVec.ofNat 32 8 = s₁.sp - BitVec.ofNat 32 8
    rw [h₁.sp]
  · show (⟨State.addr (VG.Proof.MlKem.Arm.KeyGen.pScr s₀), K.scratch⟩ : Region) ∈ s₁.wr
    rw [h₁.wr, hp.wr]; simp
  · simp [h₁.gpr]
  · simp [h₁.gpr]
  · simp [h₁.gpr]
  · show ((s₁.mem.writeW _ _).writeW _ _).readW _ _ = _
    rw [e872, e1152, ne2 i (by omega), ne1 i hi]
    exact h₁.saved i hi
  · show ((s₁.mem.writeW _ _).writeW _ _).readW _ _ = _
    rw [e872, e1152, show (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 872 = (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 840 + BitVec.ofNat 64 (4 * 8) by
      rw [add_ofNat_add], ne2 8 (by decide), add_ofNat_add, Mem.readW_writeW_self32, h₁.gpr]
  · show bytesAt ((s₁.mem.writeW _ _).writeW _ _) _ _ = _
    rw [e872, e1152]
    have fr : Frame ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).RL [(0, 840, 36), (0, 1152, 1)]) s₀.mem
        ((s₁.mem.writeW ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 872) (s₁.gpr .lr)).writeW ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 1152)
          (BitVec.setWidth 8 (BitVec.ofNat 32 K.k))) := by
      refine ((h₁.frame.sub fun r hr => ⟨Lay.R (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K) 0 840 36, by simp, ?_⟩).writeW
        (r := Lay.R (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K) 0 840 36) (by simp) _ ?_).writeW (r := Lay.R (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K) 0 1152 1) (by simp) _ ?_
      · rw [List.mem_singleton] at hr; subst hr
        show Region.Sub (Lay.R (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K) 0 840 32) _
        exact Lay.R_sub_R hL (by simp [VG.Proof.MlKem.Arm.KeyGen.lay]) (by decide) (by decide) (by simp [VG.Proof.MlKem.Arm.KeyGen.lay]; omega)
      · simp only [Region.Contains]; bv_omega
      · simp only [Region.Contains]; bv_omega
    exact Lay.bytes_keep hL fr (by ldecide) (by decide)
  · show ((s₁.mem.writeW _ _).writeW _ _) _ = _
    rw [e1152, VG.WriteBytes.writeW8_apply, ite_eq_left rfl, VG.Proof.MlKem.Arm.setWidth8_ofNat (by have := hK.k4; omega)]

/-! ## Pieces of the hashes -/

theorem pieceK {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.KeyGen.Pre K s₀) (h : VG.Proof.MlKem.Arm.KeyGen.KEnv K s₀ s) {p : Piece} {w : Bool}
    (hb : p.base = .r4 ∨ p.base = .r5 ∨ p.base = .r6 ∨ p.base = .r7) (hw : w = true → p.base ≠ .r4)
    (hoe : encodable (BitVec.ofNat 32 p.off) = true) (hle : encodable (BitVec.ofNat 32 p.len) = true)
    (hpos : 0 < p.len) (hlt : p.off + p.len < 2 ^ 32)
    (hsep : VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.KeyGen.kSz K) (VG.Proof.MlKem.Arm.KeyGen.kidx p.base, p.off, p.len) VG.Proof.MlKem.Arm.kRegs = true) :
    VG.Proof.MlKem.Arm.PieceOk (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K) VG.Proof.MlKem.Arm.KeyGen.kidx s w p := by
  obtain ⟨w0, w3, w4, w2⟩ := VG.Proof.MlKem.Arm.KeyGen.buf_wr hp
  rw [← h.wr] at w0 w3 w4
  rw [← h.wr, ← h.rd] at w2
  have hsep' : VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).sizes (VG.Proof.MlKem.Arm.KeyGen.kidx p.base, p.off, p.len) VG.Proof.MlKem.Arm.kRegs = true := hsep
  refine ⟨?_, ?_, hoe, hle, hpos, hlt, hsep', ?_⟩
  · rcases hb with e | e | e | e <;> rw [e] <;> decide
  · rcases hb with e | e | e | e <;> rw [e]
    · exact h.r4
    · exact h.r5
    · exact h.r6
    · exact h.ctx.r7
  · cases w
    · simp only [Bool.false_eq_true, ite_false]
      rcases hb with e | e | e | e <;> rw [e]
      · exact w2
      · exact VG.Proof.MlKem.Arm.mem_rd_wr w3
      · exact VG.Proof.MlKem.Arm.mem_rd_wr w4
      · exact VG.Proof.MlKem.Arm.mem_rd_wr w0
    · simp only [ite_true]
      rcases hb with e | e | e | e
      · exact absurd e (hw rfl)
      all_goals rw [e]
      · exact w3
      · exact w4
      · exact w0

/-! ## `G(d ‖ k)` -/

/-- `d`, the first half of the seed. -/
abbrev D (s₀ : State) : List Byte := bytesAt s₀.mem (State.addr (VG.Proof.MlKem.Arm.KeyGen.pSeed s₀)) 32

/-- `z`, the second half of the seed. -/
abbrev Z (s₀ : State) : List Byte := bytesAt s₀.mem (State.addr (VG.Proof.MlKem.Arm.KeyGen.pSeed s₀) + BitVec.ofNat 64 32) 32

theorem rate72 : 72 ∈ Spec.Sha3.rates := by decide

theorem g_ins {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.KeyGen.Pre K s₀) (h : VG.Proof.MlKem.Arm.KeyGen.KEnv K s₀ s) :
    ∀ p ∈ [(⟨.r4, 0, 32⟩ : Piece), ⟨.r7, oK, 1⟩], VG.Proof.MlKem.Arm.PieceOk (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K) VG.Proof.MlKem.Arm.KeyGen.kidx s false p := by
  have hK := hp.wf
  intro p hp'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl
  · exact VG.Proof.MlKem.Arm.KeyGen.pieceK hp h (.inl rfl) (by simp) (by decide) (by decide) (by decide) (by decide) (by ldecide)
  · exact VG.Proof.MlKem.Arm.KeyGen.pieceK hp h (.inr (.inr (.inr rfl))) (by simp) (by decide) (by decide) (by decide) (by decide)
      (by ldecide)

theorem g_outs {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.KeyGen.Pre K s₀) (h : VG.Proof.MlKem.Arm.KeyGen.KEnv K s₀ s) :
    ∀ p ∈ [(⟨.r7, oG, 64⟩ : Piece)], VG.Proof.MlKem.Arm.PieceOk (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K) VG.Proof.MlKem.Arm.KeyGen.kidx s true p := by
  have hK := hp.wf
  intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
  exact VG.Proof.MlKem.Arm.KeyGen.pieceK hp h (.inr (.inr (.inr rfl))) (by simp) (by decide) (by decide) (by decide) (by decide)
    (by ldecide)

theorem g_ok {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.KeyGen.Pre K s₀) (h : VG.Proof.MlKem.Arm.KeyGen.KEnv K s₀ s)
    (h3 : s.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 oK) = BitVec.ofNat 8 K.k) :
    WP isa (hash 72 0x06 [⟨.r4, 0, 32⟩, ⟨.r7, oK, 1⟩] [⟨.r7, oG, 64⟩]) s fun s' =>
      VG.Proof.MlKem.Arm.KeyGen.KEnv K s₀ s' ∧ bytesAt s'.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 oG) 32 = VG.Proof.MlKem.KPke.kgRho K.p (VG.Proof.MlKem.Arm.KeyGen.D s₀) ∧
      bytesAt s'.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (VG.Proof.MlKem.Arm.KeyGen.D s₀) := by
  have hK := hp.wf
  have hin := VG.Proof.MlKem.Arm.KeyGen.g_ins hp h
  have hout := VG.Proof.MlKem.Arm.KeyGen.g_outs hp h
  have hD : bytesAt s.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 2 0) 32 = VG.Proof.MlKem.Arm.KeyGen.D s₀ := by
    have := congrArg (List.take 32) h.seed
    rw [bytesAt_take _ _ (by decide), bytesAt_take _ _ (by decide)] at this
    rw [this]; show bytesAt s₀.mem (State.addr (VG.Proof.MlKem.Arm.KeyGen.pSeed s₀) + BitVec.ofNat 64 0) 32 = _; rw [add_ofNat_zero]
  have hin' : (List.map ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).pb VG.Proof.MlKem.Arm.KeyGen.kidx s.mem) [⟨.r4, 0, 32⟩, ⟨.r7, oK, 1⟩]).flatten =
      VG.Proof.MlKem.Arm.KeyGen.D s₀ ++ [BitVec.ofNat 8 K.k] := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    show bytesAt s.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 2 0) 32 ++ bytesAt s.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 oK) 1 = _
    rw [hD, VG.Proof.MlKem.Arm.bytes_one, h3]
  refine WP.mono (VG.Proof.MlKem.Arm.hash_ok VG.Proof.MlKem.Arm.KeyGen.rate72 (by decide) (by decide) (by decide) h.ctx (List.cons_ne_nil _ _) hin hout
    (List.pairwise_singleton _ _)) fun s' ⟨k', o'⟩ => ⟨?_, ?_⟩
  · exact h.keep hp (k'.x []) (by simp) (by ldecide)
  · have e1 := o'.1
    rw [hin'] at e1
    have e2 : bytesAt s'.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 oG) 64 = (G (VG.Proof.MlKem.Arm.KeyGen.D s₀ ++ [BitVec.ofNat 8 K.k])).1 ++
        (G (VG.Proof.MlKem.Arm.KeyGen.D s₀ ++ [BitVec.ofNat 8 K.k])).2 := e1.trans (VG.Proof.MlKem.Arm.G_split _)
    rw [show (64 : Nat) = 32 + 32 from rfl, bytesAt_add] at e2
    have l1 : (bytesAt s'.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 oG) 32).length = (G (VG.Proof.MlKem.Arm.KeyGen.D s₀ ++ [BitVec.ofNat 8 K.k])).1.length := by
      rw [bytesAt_length, VG.Proof.MlKem.G_fst_length]
    obtain ⟨r1, r2⟩ := List.append_inj e2 l1
    refine ⟨r1, ?_⟩
    show bytesAt s'.mem (State.addr ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).ptr 0) + BitVec.ofNat 64 (888 + 32)) 32 = _
    rw [← add_ofNat_add]; exact r2

theorem rho_ok {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.KeyGen.Pre K s₀) (h : VG.Proof.MlKem.Arm.KeyGen.KEnv K s₀ s)
    (hr : bytesAt s.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 oG) 32 = VG.Proof.MlKem.KPke.kgRho K.p (VG.Proof.MlKem.Arm.KeyGen.D s₀))
    (hs : bytesAt s.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (VG.Proof.MlKem.Arm.KeyGen.D s₀)) :
    WP isa (copy .r7 oG .r7 oSeed 32) s fun s' => VG.Proof.MlKem.Arm.KeyGen.KEnv K s₀ s' ∧
      bytesAt s'.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 oSeed) 32 = VG.Proof.MlKem.KPke.kgRho K.p (VG.Proof.MlKem.Arm.KeyGen.D s₀) ∧
      bytesAt s'.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (VG.Proof.MlKem.Arm.KeyGen.D s₀) := by
  have hL := VG.Proof.MlKem.Arm.KeyGen.lay_ok hp
  have hK := hp.wf
  obtain ⟨w0, -, -, -⟩ := VG.Proof.MlKem.Arm.KeyGen.buf_wr hp
  refine WP.mono (VG.Proof.MlKem.Arm.copyL hL (i := 0) (j := 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ h.ctx.r7 h.ctx.r7
    (by decide) (by decide) (by decide) (by decide) (by decide) (by ldecide)
    (by rw [h.rd, h.wr]; exact VG.Proof.MlKem.Arm.mem_rd_wr w0) (by rw [h.wr]; exact w0)) fun s' ⟨k', b'⟩ =>
    ⟨h.keep hp (k'.x []) (by simp) (by ldecide), b'.trans hr,
      (Lay.bytes_keep hL k'.frame (by ldecide) (by decide)).trans hs⟩

/-! ## The `PRF`s -/

theorem prf_phase {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.KeyGen.Pre K s₀) (h : VG.Proof.MlKem.Arm.KeyGen.KEnv K s₀ s)
    (hr : bytesAt s.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 oSeed) 32 = VG.Proof.MlKem.KPke.kgRho K.p (VG.Proof.MlKem.Arm.KeyGen.D s₀))
    (hs : bytesAt s.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (VG.Proof.MlKem.Arm.KeyGen.D s₀)) :
    WP isa (K.prfLoop true 0 (2 * K.k)) s fun s' => VG.Proof.MlKem.Arm.KeyGen.KEnv K s₀ s' ∧
      bytesAt s'.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 oSeed) 32 = VG.Proof.MlKem.KPke.kgRho K.p (VG.Proof.MlKem.Arm.KeyGen.D s₀) ∧
      ∀ N < 2 * K.k, PolyIs s'.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 (oPoly (K.k + N)))
        (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.KPke.kgSigma K.p (VG.Proof.MlKem.Arm.KeyGen.D s₀)) N)) := by
  have hK := hp.wf
  exact WP.mono (VG.Proof.MlKem.Arm.prfLoop_ok hK h.ctx true (by have := hK.k1; omega) (by omega) hs) fun s' ⟨k', p'⟩ =>
    ⟨h.keep hp k' (by simp) (by ldecide), by rw [← hr]; exact Lay.bytes_keep (VG.Proof.MlKem.Arm.KeyGen.lay_ok hp) k'.frame (by ldecide) (by decide),
      fun N hN => p' N (Nat.zero_le _) hN⟩

/-! ## The rows of `t̂` -/

section
variable (K : KemLay) (s₀ : State)

/-- `ρ`. -/
abbrev ρ₀ : List Byte := VG.Proof.MlKem.KPke.kgRho K.p (VG.Proof.MlKem.Arm.KeyGen.D s₀)

/-- `ŝ`. -/
abbrev sK : Nat → VG.Spec.MlKem.Poly := VG.Proof.MlKem.KPke.kgS K.p (VG.Proof.MlKem.Arm.KeyGen.D s₀)

/-- The entries of `Â` the products use. -/
abbrev aK (i j : Nat) : VG.Spec.MlKem.Poly := VG.Proof.MlKem.Arm.effA false (VG.Proof.MlKem.Arm.KeyGen.ρ₀ K s₀) i j (VG.Proof.MlKem.Arm.KeyGen.sK K s₀ j)

/-- Whether the `SampleNTT`s of the first `i` rows finished. -/
def okK (i : Nat) : Bool := (List.range i).all fun i' => VG.Proof.MlKem.Arm.okRow false (VG.Proof.MlKem.Arm.KeyGen.ρ₀ K s₀) i' K.k

/-- `t̂`. -/
abbrev tK : Nat → VG.Spec.MlKem.Poly := VG.Proof.MlKem.KPke.kgT K.p (VG.Proof.MlKem.Arm.KeyGen.aK K s₀) (VG.Proof.MlKem.Arm.KeyGen.D s₀)

end

theorem okK_succ (K : KemLay) (s₀ : State) (i : Nat) :
    VG.Proof.MlKem.Arm.KeyGen.okK K s₀ (i + 1) = (VG.Proof.MlKem.Arm.KeyGen.okK K s₀ i && VG.Proof.MlKem.Arm.okRow false (VG.Proof.MlKem.Arm.KeyGen.ρ₀ K s₀) i K.k) := by
  simp only [VG.Proof.MlKem.Arm.KeyGen.okK, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]

/-- After the first `i` rows. -/
structure KRow (K : KemLay) (s₀ : State) (i : Nat) (s : State) : Prop where
  env : VG.Proof.MlKem.Arm.KeyGen.KEnv K s₀ s
  r9 : s.gpr .r9 = BitVec.ofNat 32 i
  r11 : s.gpr .r11 = if VG.Proof.MlKem.Arm.KeyGen.okK K s₀ i then 1 else 0
  rho : bytesAt s.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 oSeed) 32 = VG.Proof.MlKem.Arm.KeyGen.ρ₀ K s₀
  slots : ∀ N < 2 * K.k, PolyIs s.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 (oPoly (K.k + N)))
    (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.KPke.kgSigma K.p (VG.Proof.MlKem.Arm.KeyGen.D s₀)) N))
  ek : ∀ i' < i, bytesAt s.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 3 (384 * i')) 384 = encode12 (VG.Proof.MlKem.Arm.KeyGen.tK K s₀ i')

/-- What a row changes. -/
abbrev rowK (K : KemLay) (i : Nat) : List (Nat × Nat × Nat) :=
  [(0, 1248, 2), (0, K.oAcc, 3072), (0, K.oSample, 3072), (1, 0, 8), (0, K.oAcc, 1024), (3, 384 * i, 384)]

/-- `rowK_ok` with the sizes `sz` of the buffers. -/
abbrev RowKF (K : KemLay) (sz : List Nat) : Prop := ∀ i < K.k,
    (VG.Proof.MlKem.Arm.KeyGen.rowK K i).all (fun w => VG.Proof.MlKem.Arm.sepB sz (0, 840, 36) w && VG.Proof.MlKem.Arm.sepB sz (2, 0, 64) w) = true ∧
    VG.Proof.MlKem.Arm.sepAll sz (0, oSeed, 32) (VG.Proof.MlKem.Arm.KeyGen.rowK K i) = true ∧
    (∀ N < 2 * K.k, VG.Proof.MlKem.Arm.sepAll sz (0, oPoly (K.k + N), 1024) (VG.Proof.MlKem.Arm.KeyGen.rowK K i) = true) ∧
    (∀ i' < K.k, i' ≠ i → VG.Proof.MlKem.Arm.sepAll sz (3, 384 * i', 384) (VG.Proof.MlKem.Arm.KeyGen.rowK K i) = true) ∧
    VG.Proof.MlKem.Arm.sepB sz (0, K.oAcc, 1024) (3, 384 * i, 384) = true ∧
    VG.Proof.MlKem.Arm.sepB sz (0, K.oAcc, 1024) (0, oPoly (K.k + (K.k + i)), 1024) = true

theorem rowK_ok {K : KemLay} (hK : K.WF) {i : Nat} (hi : i < K.k) : (VG.Proof.MlKem.Arm.KeyGen.rowK K i).all (VG.Proof.MlKem.Arm.KeyGen.okW K) = true ∧
    VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.KeyGen.kSz K) (0, oSeed, 32) (VG.Proof.MlKem.Arm.KeyGen.rowK K i) = true ∧
    (∀ N < 2 * K.k, VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.KeyGen.kSz K) (0, oPoly (K.k + N), 1024) (VG.Proof.MlKem.Arm.KeyGen.rowK K i) = true) ∧
    (∀ i' < K.k, i' ≠ i → VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.KeyGen.kSz K) (3, 384 * i', 384) (VG.Proof.MlKem.Arm.KeyGen.rowK K i) = true) ∧
    VG.Proof.MlKem.Arm.sepB (VG.Proof.MlKem.Arm.KeyGen.kSz K) (0, K.oAcc, 1024) (3, 384 * i, 384) = true ∧
    VG.Proof.MlKem.Arm.sepB (VG.Proof.MlKem.Arm.KeyGen.kSz K) (0, K.oAcc, 1024) (0, oPoly (K.k + (K.k + i)), 1024) = true := by
  have scr := hK.scr
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ :=
    (by decide : ∀ k < 5, RowKF (kOf k) (kSz (kOf k))) K.k (by have := hK.k4; omega) i hi
  refine ⟨List.all_eq_true.mpr fun w hw => ?_, VG.Proof.MlKem.Arm.sepAll_scr c2 scr, fun N hN => VG.Proof.MlKem.Arm.sepAll_scr (c3 N hN) scr,
    fun i' hi' hne => VG.Proof.MlKem.Arm.sepAll_scr (c4 i' hi' hne) scr, VG.Proof.MlKem.Arm.sepB_scr c5 scr, VG.Proof.MlKem.Arm.sepB_scr c6 scr⟩
  have := List.all_eq_true.mp c1 w hw
  simp only [VG.Proof.MlKem.Arm.KeyGen.okW, Bool.and_eq_true] at this ⊢
  exact ⟨VG.Proof.MlKem.Arm.sepB_scr this.1 scr, VG.Proof.MlKem.Arm.sepB_scr this.2 scr⟩

/-- The row's facts at its start `s`, for its `RowSum`. -/
theorem KRow.rowPre {K : KemLay} {s₀ : State} (hp : VG.Proof.MlKem.Arm.KeyGen.Pre K s₀) {i : Nat} (hi : i < K.k) {s : State}
    (h : VG.Proof.MlKem.Arm.KeyGen.KRow K s₀ i s) : VG.Proof.MlKem.Arm.RowPre K (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K) (VG.Proof.MlKem.Arm.KeyGen.ρ₀ K s₀) (VG.Proof.MlKem.Arm.KeyGen.sK K s₀) i (VG.Proof.MlKem.Arm.KeyGen.okK K s₀ i) s :=
  ⟨hp.wf, h.env.ctx, hi, h.r9, h.r11, h.rho, fun j hj => h.slots j (by omega)⟩

section
variable (K : KemLay) (s₀ : State) (i : Nat) (s : State)

/-- After the arguments of `t̂[i] += ê[i]`. -/
structure KR2 (s₂ : State) : Prop where
  kx : VG.Proof.MlKem.Arm.KeptX [.r9, .r10, .r11] ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).RL (VG.Proof.MlKem.Arm.KeyGen.rowK K i)) s s₂
  r9 : s₂.gpr .r9 = BitVec.ofNat 32 i
  r0 : s₂.gpr .r0 = (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).ptr 0 + BitVec.ofNat 32 K.oAcc
  r1 : s₂.gpr .r1 = (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).ptr 0 + BitVec.ofNat 32 (oPoly (K.k + (K.k + i)))
  r11 : s₂.gpr .r11 = if VG.Proof.MlKem.Arm.KeyGen.okK K s₀ (i + 1) then 1 else 0
  acc : PolyIs s₂.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 K.oAcc) (VG.Proof.MlKem.KPke.dotK (VG.Proof.MlKem.Arm.KeyGen.aK K s₀ i) (VG.Proof.MlKem.Arm.KeyGen.sK K s₀) K.k)

/-- After `t̂[i]`. -/
structure KR3 (s₃ : State) : Prop where
  kx : VG.Proof.MlKem.Arm.KeptX [.r9, .r10, .r11] ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).RL (VG.Proof.MlKem.Arm.KeyGen.rowK K i)) s s₃
  r9 : s₃.gpr .r9 = BitVec.ofNat 32 i
  r11 : s₃.gpr .r11 = if VG.Proof.MlKem.Arm.KeyGen.okK K s₀ (i + 1) then 1 else 0
  acc : PolyIs s₃.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 K.oAcc) (VG.Proof.MlKem.Arm.KeyGen.tK K s₀ i)

/-- After the arguments of its encoding. -/
structure KR4 (s₄ : State) : Prop where
  r3 : VG.Proof.MlKem.Arm.KeyGen.KR3 K s₀ i s s₄
  r0 : s₄.gpr .r0 = (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).ptr 0 + BitVec.ofNat 32 K.oAcc
  r1 : s₄.gpr .r1 = (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).ptr 3 + BitVec.ofNat 32 (384 * i)

/-- After its encoding. -/
structure KR5 (s₅ : State) : Prop where
  kx : VG.Proof.MlKem.Arm.KeptX [.r9, .r10, .r11] ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).RL (VG.Proof.MlKem.Arm.KeyGen.rowK K i)) s s₅
  r9 : s₅.gpr .r9 = BitVec.ofNat 32 i
  r11 : s₅.gpr .r11 = if VG.Proof.MlKem.Arm.KeyGen.okK K s₀ (i + 1) then 1 else 0
  enc : bytesAt s₅.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 3 (384 * i)) 384 = encode12 (VG.Proof.MlKem.Arm.KeyGen.tK K s₀ i)

end

theorem KRow.ctxOf {K : KemLay} {s₀ : State} {i : Nat} {s : State} (h : VG.Proof.MlKem.Arm.KeyGen.KRow K s₀ i s) {x : State} {xs : List Reg}
    {W : List (Nat × Nat × Nat)} (k : VG.Proof.MlKem.Arm.KeptX xs ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).RL W) s x) (h7 : Reg.r7 ∉ xs) : VG.Proof.MlKem.Arm.Ctx (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K) x :=
  k.ctx h7 h.env.ctx

section
variable {K : KemLay} {s₀ : State} (hp : VG.Proof.MlKem.Arm.KeyGen.Pre K s₀) {i : Nat} (hi : i < K.k) {s : State} (h : VG.Proof.MlKem.Arm.KeyGen.KRow K s₀ i s)
include hp hi h

theorem kr2_ok {s₁ : State}
    (r : VG.Proof.MlKem.Arm.RowInv K (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K) false (VG.Proof.MlKem.Arm.KeyGen.ρ₀ K s₀) (VG.Proof.MlKem.Arm.KeyGen.sK K s₀) i (VG.Proof.MlKem.Arm.KeyGen.okK K s₀ i) s K.k s₁) :
    WP isa (.block (ptrTo .r0 .r7 K.oAcc :: slotAt .r1 .r9 (oPoly (2 * K.k)))) s₁ (VG.Proof.MlKem.Arm.KeyGen.KR2 K s₀ i s) := by
  have hK := hp.wf
  have hc₁ := h.ctxOf r.kx (by decide)
  have g9₁ : s₁.gpr .r9 = BitVec.ofNat 32 i := by rw [r.kx.cs .r9 (by decide) (by decide) (by decide), h.r9]
  refine WP.mono (VG.Proof.MlKem.Arm.ptrSlot_ok (i := i) hc₁.r7 g9₁ (by kenc) (by kenc)) fun s₂ ⟨o₂, a0, a1⟩ => ?_
  rw [VG.Proof.MlKem.Arm.slot_eq _ (by offs), show oPoly (2 * K.k) + 1024 * i = oPoly (K.k + (K.k + i)) by offs] at a1
  exact ⟨((r.kx.weaken (by simp)).monoL (by simp)).trans (o₂.x _ _),
    by rw [o₂.cs .r9 (by decide) (by decide), g9₁], a0, a1,
    by rw [o₂.cs .r11 (by decide) (by decide), r.r11, ← VG.Proof.MlKem.Arm.KeyGen.okK_succ],
    by rw [o₂.mem, ← VG.Proof.MlKem.Arm.rowAcc_eq]; exact r.acc⟩

theorem kr3_ok {s₂ : State} (r : VG.Proof.MlKem.Arm.KeyGen.KR2 K s₀ i s s₂) : WP isa callAdd s₂ (VG.Proof.MlKem.Arm.KeyGen.KR3 K s₀ i s) := by
  have hL := VG.Proof.MlKem.Arm.KeyGen.lay_ok hp
  have hc₂ := h.ctxOf r.kx (by decide)
  obtain ⟨-, -, c_slots, -, -, c_add⟩ := VG.Proof.MlKem.Arm.KeyGen.rowK_ok hp.wf hi
  have sl₂ : PolyIs s₂.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 (oPoly (K.k + (K.k + i))))
      (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.KPke.kgSigma K.p (VG.Proof.MlKem.Arm.KeyGen.D s₀)) (K.k + i))) :=
    Lay.polyIs_keep hL r.kx.frame (c_slots (K.k + i) (by omega)) (h.slots (K.k + i) (by omega))
  exact VG.Proof.MlKem.Arm.addL hL r.r0 r.r1 c_add hc₂.buf0 (VG.Proof.MlKem.Arm.mem_rd_wr hc₂.buf0) r.acc sl₂ fun s₃ k₃ p₃ =>
    ⟨r.kx.trans ((k₃.x _).monoL (by simp)), by rw [k₃.cs .r9 (by decide) (by decide), r.r9],
      by rw [k₃.cs .r11 (by decide) (by decide), r.r11], p₃⟩

theorem kr4_ok {s₃ : State} (r : VG.Proof.MlKem.Arm.KeyGen.KR3 K s₀ i s s₃) :
    WP isa (.block (ptrTo .r0 .r7 K.oAcc :: at384 .r1 .r5 .r9)) s₃ (VG.Proof.MlKem.Arm.KeyGen.KR4 K s₀ i s) := by
  have hK := hp.wf
  have hc₃ := h.ctxOf r.kx (by decide)
  have g5₃ : s₃.gpr .r5 = VG.Proof.MlKem.Arm.KeyGen.pEk s₀ := by rw [r.kx.cs .r5 (by decide) (by decide) (by decide), h.env.r5]
  refine WP.mono (VG.Proof.MlKem.Arm.ptr384_ok (b := .r5) (.inl rfl) hc₃.r7 g5₃ r.r9 (by kenc)) fun s₄ ⟨o₄, b0, b1⟩ => ?_
  rw [VG.Proof.MlKem.Arm.at384_eq _ (by offs)] at b1
  exact ⟨⟨r.kx.trans (o₄.x _ _), by rw [o₄.cs .r9 (by decide) (by decide), r.r9],
    by rw [o₄.cs .r11 (by decide) (by decide), r.r11], by rw [o₄.mem]; exact r.acc⟩, b0, b1⟩

theorem kr5_ok {s₄ : State} (r : VG.Proof.MlKem.Arm.KeyGen.KR4 K s₀ i s s₄) : WP isa callEncode12 s₄ (VG.Proof.MlKem.Arm.KeyGen.KR5 K s₀ i s) := by
  have hL := VG.Proof.MlKem.Arm.KeyGen.lay_ok hp
  have hc₄ := h.ctxOf r.r3.kx (by decide)
  obtain ⟨-, -, -, -, c_enc, -⟩ := VG.Proof.MlKem.Arm.KeyGen.rowK_ok hp.wf hi
  obtain ⟨-, w3, -, -⟩ := VG.Proof.MlKem.Arm.KeyGen.buf_wr hp
  exact VG.Proof.MlKem.Arm.encode12L hL (i := 0) (j := 3) (o' := 384 * i) r.r0 r.r1 c_enc (VG.Proof.MlKem.Arm.mem_rd_wr hc₄.buf0)
    (by rw [r.r3.kx.wr, h.env.wr]; exact w3) r.r3.acc fun s₅ k₅ e₅ =>
    ⟨r.r3.kx.trans ((k₅.x _).monoL (by simp)), by rw [k₅.cs .r9 (by decide) (by decide), r.r3.r9],
      by rw [k₅.cs .r11 (by decide) (by decide), r.r3.r11], e₅⟩

theorem kr6_ok {s₅ : State} (r : VG.Proof.MlKem.Arm.KeyGen.KR5 K s₀ i s s₅) :
    WP isa (.block (count .r9 K.k)) s₅ fun s' => VG.Proof.MlKem.Arm.KeyGen.KRow K s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = K.k) := by
  have hL := VG.Proof.MlKem.Arm.KeyGen.lay_ok hp
  have hK := hp.wf
  have k4 := hK.k4
  obtain ⟨c_ok, c_rho, c_slots, c_ek, -, -⟩ := VG.Proof.MlKem.Arm.KeyGen.rowK_ok hK hi
  refine WP.mono (VG.Proof.MlKem.Arm.count_ok (by omega) (by omega) (by kenc) r.r9) fun s' ⟨k', g', z'⟩ => ⟨⟨?_, g', ?_, ?_, ?_, ?_⟩, z'⟩
  all_goals have K' : VG.Proof.MlKem.Arm.KeptX [.r9, .r10, .r11] ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).RL (VG.Proof.MlKem.Arm.KeyGen.rowK K i)) s s' :=
    r.kx.trans ((k'.weaken (by simp)).mono (fun _ h => absurd h List.not_mem_nil))
  · exact h.env.keep hp K' (by simp) c_ok
  · rw [k'.cs .r11 (by decide) (by decide) (by decide), r.r11]
  · rw [← h.rho]; exact Lay.bytes_keep hL K'.frame c_rho (by decide)
  · exact fun N hN => Lay.polyIs_keep hL K'.frame (c_slots N hN) (h.slots N hN)
  · intro i' hi'
    by_cases e : i' = i
    · subst e
      exact (bytesAt_frame k'.frame (fun _ h => absurd h List.not_mem_nil) (by decide)).trans r.enc
    · rw [← h.ek i' (by omega)]; exact Lay.bytes_keep hL K'.frame (c_ek i' (by omega) e) (by decide)

end

theorem kgRow_step {K : KemLay} {s₀ : State} (hp : VG.Proof.MlKem.Arm.KeyGen.Pre K s₀) {i : Nat} (hi : i < K.k) {s : State}
    (h : VG.Proof.MlKem.Arm.KeyGen.KRow K s₀ i s) :
    WP isa K.kgRowBody s fun s' => VG.Proof.MlKem.Arm.KeyGen.KRow K s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = K.k) :=
  WP.seq (WP.mono (VG.Proof.MlKem.Arm.rowSum_ok (transpose := false) (h.rowPre hp hi)) fun _ r₁ =>
    WP.seq (WP.mono (VG.Proof.MlKem.Arm.KeyGen.kr2_ok hp hi h r₁) fun _ r₂ => WP.seq (WP.mono (VG.Proof.MlKem.Arm.KeyGen.kr3_ok hp hi h r₂) fun _ r₃ =>
    WP.seq (WP.mono (VG.Proof.MlKem.Arm.KeyGen.kr4_ok hp hi h r₃) fun _ r₄ => WP.seq (WP.mono (VG.Proof.MlKem.Arm.KeyGen.kr5_ok hp hi h r₄) fun _ r₅ =>
      VG.Proof.MlKem.Arm.KeyGen.kr6_ok hp hi h r₅)))))

theorem rows_init {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.KeyGen.Pre K s₀) (h : VG.Proof.MlKem.Arm.KeyGen.KEnv K s₀ s)
    (hr : bytesAt s.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 oSeed) 32 = VG.Proof.MlKem.Arm.KeyGen.ρ₀ K s₀)
    (hs : ∀ N < 2 * K.k, PolyIs s.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 (oPoly (K.k + N)))
      (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.KPke.kgSigma K.p (VG.Proof.MlKem.Arm.KeyGen.D s₀)) N))) :
    WP isa (.block [.mov .r11 (.imm 1), .mov .r9 (.imm 0)]) s (VG.Proof.MlKem.Arm.KeyGen.KRow K s₀ 0) :=
  WP.mono VG.Proof.MlKem.Arm.flagInit_ok fun _ ⟨k₁, g11, g9, m₁⟩ =>
    ⟨h.keep hp (xs := [.r9, .r11]) (W := []) k₁ (by simp) rfl, g9, by rw [g11]; rfl, by rw [m₁]; exact hr,
      by rw [m₁]; exact hs, fun i' hi' => absurd hi' (Nat.not_lt_zero _)⟩

/-! ## `ŝ` into `dk` -/

/-- After encoding the first `j` polynomials of `ŝ`. -/
structure KS (K : KemLay) (s₀ : State) (j : Nat) (s : State) : Prop where
  env : VG.Proof.MlKem.Arm.KeyGen.KEnv K s₀ s
  r9 : s.gpr .r9 = BitVec.ofNat 32 j
  r11 : s.gpr .r11 = if VG.Proof.MlKem.Arm.KeyGen.okK K s₀ K.k then 1 else 0
  rho : bytesAt s.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 oSeed) 32 = VG.Proof.MlKem.Arm.KeyGen.ρ₀ K s₀
  ek : ∀ i' < K.k, bytesAt s.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 3 (384 * i')) 384 = encode12 (VG.Proof.MlKem.Arm.KeyGen.tK K s₀ i')
  slots : ∀ j' < K.k, PolyIs s.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 0 (oPoly (K.k + j'))) (VG.Proof.MlKem.Arm.KeyGen.sK K s₀ j')
  dk : ∀ j' < j, bytesAt s.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 4 (384 * j')) 384 = encode12 (VG.Proof.MlKem.Arm.KeyGen.sK K s₀ j')

/-- `sK_ok` with the sizes `sz` of the buffers. -/
abbrev SKF (K : KemLay) (sz : List Nat) : Prop := ∀ j < K.k,
    [((4 : Nat), 384 * j, (384 : Nat))].all (fun w => VG.Proof.MlKem.Arm.sepB sz (0, 840, 36) w && VG.Proof.MlKem.Arm.sepB sz (2, 0, 64) w) = true ∧
    VG.Proof.MlKem.Arm.sepAll sz (0, oSeed, 32) [(4, 384 * j, 384)] = true ∧
    (∀ i' < K.k, VG.Proof.MlKem.Arm.sepAll sz (3, 384 * i', 384) [(4, 384 * j, 384)] = true) ∧
    (∀ j' < K.k, VG.Proof.MlKem.Arm.sepAll sz (0, oPoly (K.k + j'), 1024) [(4, 384 * j, 384)] = true) ∧
    (∀ j' < K.k, j' ≠ j → VG.Proof.MlKem.Arm.sepAll sz (4, 384 * j', 384) [(4, 384 * j, 384)] = true) ∧
    VG.Proof.MlKem.Arm.sepB sz (0, oPoly (K.k + j), 1024) (4, 384 * j, 384) = true

theorem sK_ok {K : KemLay} (hK : K.WF) {j : Nat} (hj : j < K.k) : [((4 : Nat), 384 * j, (384 : Nat))].all (VG.Proof.MlKem.Arm.KeyGen.okW K) = true ∧
    VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.KeyGen.kSz K) (0, oSeed, 32) [(4, 384 * j, 384)] = true ∧
    (∀ i' < K.k, VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.KeyGen.kSz K) (3, 384 * i', 384) [(4, 384 * j, 384)] = true) ∧
    (∀ j' < K.k, VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.KeyGen.kSz K) (0, oPoly (K.k + j'), 1024) [(4, 384 * j, 384)] = true) ∧
    (∀ j' < K.k, j' ≠ j → VG.Proof.MlKem.Arm.sepAll (VG.Proof.MlKem.Arm.KeyGen.kSz K) (4, 384 * j', 384) [(4, 384 * j, 384)] = true) ∧
    VG.Proof.MlKem.Arm.sepB (VG.Proof.MlKem.Arm.KeyGen.kSz K) (0, oPoly (K.k + j), 1024) (4, 384 * j, 384) = true := by
  have scr := hK.scr
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ :=
    (by decide : ∀ k < 5, SKF (kOf k) (kSz (kOf k))) K.k (by have := hK.k4; omega) j hj
  refine ⟨List.all_eq_true.mpr fun w hw => ?_, VG.Proof.MlKem.Arm.sepAll_scr c2 scr, fun i' hi' => VG.Proof.MlKem.Arm.sepAll_scr (c3 i' hi') scr,
    fun j' hj' => VG.Proof.MlKem.Arm.sepAll_scr (c4 j' hj') scr, fun j' hj' hne => VG.Proof.MlKem.Arm.sepAll_scr (c5 j' hj' hne) scr, VG.Proof.MlKem.Arm.sepB_scr c6 scr⟩
  have := List.all_eq_true.mp c1 w hw
  simp only [VG.Proof.MlKem.Arm.KeyGen.okW, Bool.and_eq_true] at this ⊢
  exact ⟨VG.Proof.MlKem.Arm.sepB_scr this.1 scr, VG.Proof.MlKem.Arm.sepB_scr this.2 scr⟩

theorem s_init {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.KeyGen.Pre K s₀) (h : VG.Proof.MlKem.Arm.KeyGen.KRow K s₀ K.k s) :
    WP isa (.block [.mov .r9 (.imm 0)]) s (VG.Proof.MlKem.Arm.KeyGen.KS K s₀ 0) :=
  WP.mono (VG.Proof.MlKem.Arm.movc_ok .r9 (N := 0) (by decide)) fun _ ⟨k₆, g9', m₆⟩ =>
    ⟨h.env.keep hp (xs := [.r9]) (W := []) k₆ (by simp) rfl, g9',
      by rw [k₆.cs .r11 (by decide) (by decide) (by decide), h.r11], by rw [m₆]; exact h.rho,
      by rw [m₆]; exact h.ek, fun j' hj' => by rw [m₆]; exact h.slots j' (by omega),
      fun j' hj' => absurd hj' (Nat.not_lt_zero _)⟩

section
variable (K : KemLay) (s₀ : State) (j : Nat) (s : State)

/-- After the arguments of the encoding of `ŝ[j]`. -/
structure KS1 (s₁ : State) : Prop where
  o : VG.Proof.MlKem.Arm.Only s s₁
  r0 : s₁.gpr .r0 = (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).ptr 0 + BitVec.ofNat 32 (oPoly (K.k + j))
  r1 : s₁.gpr .r1 = (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).ptr 4 + BitVec.ofNat 32 (384 * j)

/-- After the encoding of `ŝ[j]`. -/
structure KS2 (s₂ : State) : Prop where
  kx : VG.Proof.MlKem.Arm.KeptX [.r9] ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).RL [(4, 384 * j, 384)]) s s₂
  r9 : s₂.gpr .r9 = BitVec.ofNat 32 j
  enc : bytesAt s₂.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 4 (384 * j)) 384 = encode12 (VG.Proof.MlKem.Arm.KeyGen.sK K s₀ j)

end

section
variable {K : KemLay} {s₀ : State} (hp : VG.Proof.MlKem.Arm.KeyGen.Pre K s₀) {j : Nat} (hj : j < K.k) {s : State} (h : VG.Proof.MlKem.Arm.KeyGen.KS K s₀ j s)
include hp hj h

theorem ks1_ok : WP isa (.block (slotAt .r0 .r9 (oPoly K.k) ++ at384 .r1 .r6 .r9)) s (VG.Proof.MlKem.Arm.KeyGen.KS1 K s₀ j s) := by
  have hK := hp.wf
  refine WP.mono (VG.Proof.MlKem.Arm.slot384_ok (b := .r6) (.inr rfl) h.env.ctx.r7 h.env.r6 h.r9 (o' := oPoly K.k) (by kenc))
    fun s₁ ⟨o₁, a0, a1⟩ => ⟨o₁, ?_, ?_⟩
  · rw [a0, VG.Proof.MlKem.Arm.slot_eq _ (by offs), show oPoly K.k + 1024 * j = oPoly (K.k + j) by offs]
  · rw [a1, VG.Proof.MlKem.Arm.at384_eq _ (by offs)]; rfl

theorem ks2_ok {s₁ : State} (r : VG.Proof.MlKem.Arm.KeyGen.KS1 K s₀ j s s₁) : WP isa callEncode12 s₁ (VG.Proof.MlKem.Arm.KeyGen.KS2 K s₀ j s) := by
  have hL := VG.Proof.MlKem.Arm.KeyGen.lay_ok hp
  have hc₁ := h.env.ctx.only r.o
  obtain ⟨-, -, -, -, -, c_enc⟩ := VG.Proof.MlKem.Arm.KeyGen.sK_ok hp.wf hj
  obtain ⟨-, -, w4, -⟩ := VG.Proof.MlKem.Arm.KeyGen.buf_wr hp
  exact VG.Proof.MlKem.Arm.encode12L hL (i := 0) (j := 4) (o' := 384 * j) r.r0 r.r1 c_enc (VG.Proof.MlKem.Arm.mem_rd_wr hc₁.buf0)
    (by rw [r.o.wr, h.env.wr]; exact w4) (by rw [r.o.mem]; exact h.slots j hj) fun s₂ k₂ e₂ =>
    ⟨(r.o.x _ _).trans ((k₂.x _).monoL (by simp)),
      by rw [k₂.cs .r9 (by decide) (by decide), r.o.cs .r9 (by decide) (by decide), h.r9], e₂⟩

theorem ks3_ok {s₂ : State} (r : VG.Proof.MlKem.Arm.KeyGen.KS2 K s₀ j s s₂) :
    WP isa (.block (count .r9 K.k)) s₂ fun s' => VG.Proof.MlKem.Arm.KeyGen.KS K s₀ (j + 1) s' ∧ s'.z = decide (j + 1 = K.k) := by
  have hL := VG.Proof.MlKem.Arm.KeyGen.lay_ok hp
  have hK := hp.wf
  have k4 := hK.k4
  obtain ⟨c_ok, c_rho, c_ek, c_slots, c_dk, -⟩ := VG.Proof.MlKem.Arm.KeyGen.sK_ok hK hj
  refine WP.mono (VG.Proof.MlKem.Arm.count_ok (by omega) (by omega) (by kenc) r.r9) fun s' ⟨k', g', z'⟩ =>
    ⟨⟨?_, g', ?_, ?_, ?_, ?_, ?_⟩, z'⟩
  all_goals have K' : VG.Proof.MlKem.Arm.KeptX [.r9] ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).RL [(4, 384 * j, 384)]) s s' :=
    r.kx.trans (k'.mono (fun _ h => absurd h List.not_mem_nil))
  · exact h.env.keep hp K' (by simp) c_ok
  · rw [K'.cs .r11 (by decide) (by decide) (by decide), h.r11]
  · rw [← h.rho]; exact Lay.bytes_keep hL K'.frame c_rho (by decide)
  · exact fun i' hi' => (Lay.bytes_keep hL K'.frame (c_ek i' hi') (by decide)).trans (h.ek i' hi')
  · exact fun j' hj' => Lay.polyIs_keep hL K'.frame (c_slots j' hj') (h.slots j' hj')
  · intro j' hj'
    by_cases e : j' = j
    · subst e
      exact (bytesAt_frame k'.frame (fun _ h => absurd h List.not_mem_nil) (by decide)).trans r.enc
    · exact (Lay.bytes_keep hL K'.frame (c_dk j' (by omega) e) (by decide)).trans (h.dk j' (by omega))

end

theorem kgS_step {K : KemLay} {s₀ : State} (hp : VG.Proof.MlKem.Arm.KeyGen.Pre K s₀) {j : Nat} (hj : j < K.k) {s : State} (h : VG.Proof.MlKem.Arm.KeyGen.KS K s₀ j s) :
    WP isa K.kgSBody s fun s' => VG.Proof.MlKem.Arm.KeyGen.KS K s₀ (j + 1) s' ∧ s'.z = decide (j + 1 = K.k) :=
  WP.seq (WP.mono (VG.Proof.MlKem.Arm.KeyGen.ks1_ok hp hj h) fun _ r₁ => WP.seq (WP.mono (VG.Proof.MlKem.Arm.KeyGen.ks2_ok hp hj h r₁) fun _ r₂ => VG.Proof.MlKem.Arm.KeyGen.ks3_ok hp hj h r₂))

/-! ## The encapsulation key, `H(ek)` and `z` -/

section
variable (K : KemLay) (s₀ : State)

/-- `ek`. -/
abbrev EK : List Byte := VG.Proof.MlKem.KPke.ekPKE K.p (VG.Proof.MlKem.Arm.KeyGen.aK K s₀) (VG.Proof.MlKem.Arm.KeyGen.D s₀)

/-- `dk`. -/
abbrev DK : List Byte := VG.Proof.MlKem.KPke.dkPKE K.p (VG.Proof.MlKem.Arm.KeyGen.D s₀) ++ VG.Proof.MlKem.Arm.KeyGen.EK K s₀ ++ H (VG.Proof.MlKem.Arm.KeyGen.EK K s₀) ++ VG.Proof.MlKem.Arm.KeyGen.Z s₀

end

theorem h_ins {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.KeyGen.Pre K s₀) (h : VG.Proof.MlKem.Arm.KeyGen.KEnv K s₀ s) :
    ∀ p ∈ [(⟨.r5, 0, K.ekLen⟩ : Piece)], VG.Proof.MlKem.Arm.PieceOk (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K) VG.Proof.MlKem.Arm.KeyGen.kidx s false p := by
  have hK := hp.wf
  intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
  exact VG.Proof.MlKem.Arm.KeyGen.pieceK hp h (.inr (.inl rfl)) (by simp) VG.Proof.MlKem.Arm.enc0 hK.encEk (by offs) (by offs) (by ldecide)

theorem h_outs {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.KeyGen.Pre K s₀) (h : VG.Proof.MlKem.Arm.KeyGen.KEnv K s₀ s) :
    ∀ p ∈ [(⟨.r6, 768 * K.k + 32, 32⟩ : Piece)], VG.Proof.MlKem.Arm.PieceOk (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K) VG.Proof.MlKem.Arm.KeyGen.kidx s true p := by
  have hK := hp.wf
  intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
  exact VG.Proof.MlKem.Arm.KeyGen.pieceK hp h (.inr (.inr (.inl rfl))) (by simp) hK.encH (by dsimp only; decide) (by dsimp only; decide) (by offs) (by ldecide)

/-! What each step of the end keeps, for the proof of constant time. -/

section
variable {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.KeyGen.Pre K s₀) (h : VG.Proof.MlKem.Arm.KeyGen.KEnv K s₀ s)
include hp h

theorem cpRho_env : WP isa (copy .r7 oSeed .r5 (384 * K.k) 32) s (VG.Proof.MlKem.Arm.KeyGen.KEnv K s₀) := by
  have hK := hp.wf
  obtain ⟨w0, w3, -, -⟩ := VG.Proof.MlKem.Arm.KeyGen.buf_wr hp
  exact WP.mono (VG.Proof.MlKem.Arm.copyL (VG.Proof.MlKem.Arm.KeyGen.lay_ok hp) (i := 0) (j := 3) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ h.ctx.r7 h.r5
    (by decide) hK.encT (by decide) (by decide) (by decide) (by ldecide) (by rw [h.rd, h.wr]; exact VG.Proof.MlKem.Arm.mem_rd_wr w0)
    (by rw [h.wr]; exact w3)) fun _ ⟨k, _⟩ => h.keep hp (k.x []) (by simp) (by ldecide)

theorem cpEk_env : WP isa (copy .r5 0 .r6 (384 * K.k) K.ekLen) s (VG.Proof.MlKem.Arm.KeyGen.KEnv K s₀) := by
  have hK := hp.wf
  obtain ⟨-, w3, w4, -⟩ := VG.Proof.MlKem.Arm.KeyGen.buf_wr hp
  exact WP.mono (VG.Proof.MlKem.Arm.copyL (VG.Proof.MlKem.Arm.KeyGen.lay_ok hp) (i := 3) (j := 4) (so := 0) (dO := 384 * K.k) (len := K.ekLen) ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ h.r5 h.r6 (by decide) hK.encT hK.encEk (by offs) (by offs) (by ldecide)
    (by rw [h.rd, h.wr]; exact VG.Proof.MlKem.Arm.mem_rd_wr w3) (by rw [h.wr]; exact w4)) fun _ ⟨k, _⟩ =>
    h.keep hp (k.x []) (by simp) (by ldecide)

theorem hashH_env : WP isa (hash 136 0x06 [⟨.r5, 0, K.ekLen⟩] [⟨.r6, 768 * K.k + 32, 32⟩]) s (VG.Proof.MlKem.Arm.KeyGen.KEnv K s₀) := by
  have hK := hp.wf
  exact WP.mono (VG.Proof.MlKem.Arm.hash_ok (idx := VG.Proof.MlKem.Arm.KeyGen.kidx) VG.Proof.MlKem.Arm.rate136 (by decide) (by decide) (by decide) h.ctx (List.cons_ne_nil _ _)
    (VG.Proof.MlKem.Arm.KeyGen.h_ins hp h) (VG.Proof.MlKem.Arm.KeyGen.h_outs hp h) (List.pairwise_singleton _ _)) fun _ ⟨k, _⟩ => h.keep hp (k.x []) (by simp) (by ldecide)

theorem cpZ_env : WP isa (copy .r4 32 .r6 (768 * K.k + 64) 32) s (VG.Proof.MlKem.Arm.KeyGen.KEnv K s₀) := by
  have hK := hp.wf
  obtain ⟨-, -, w4, w2⟩ := VG.Proof.MlKem.Arm.KeyGen.buf_wr hp
  exact WP.mono (VG.Proof.MlKem.Arm.copyL (VG.Proof.MlKem.Arm.KeyGen.lay_ok hp) (i := 2) (j := 4) (so := 32) (dO := 768 * K.k + 64) (len := 32)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ h.r4 h.r6 (by decide) hK.encZ (by decide) (by decide) (by decide)
    (by ldecide) (by rw [h.rd, h.wr]; exact w2) (by rw [h.wr]; exact w4)) fun _ ⟨k, _⟩ =>
    h.keep hp (k.x []) (by simp) (by ldecide)

end

theorem ek_split (K : KemLay) (m : Mem) (q : Addr) :
    bytesAt m q K.ekLen = bytesAt m q (384 * K.k) ++ bytesAt m (q + BitVec.ofNat 64 (384 * K.k)) 32 :=
  bytesAt_add _ _ (384 * K.k) 32

theorem dk_split (K : KemLay) (m : Mem) (q : Addr) :
    bytesAt m q K.dkLen = bytesAt m q (384 * K.k) ++ bytesAt m (q + BitVec.ofNat 64 (384 * K.k)) K.ekLen ++
      bytesAt m (q + BitVec.ofNat 64 (768 * K.k + 32)) 32 ++ bytesAt m (q + BitVec.ofNat 64 (768 * K.k + 64)) 32 := by
  rw [show K.dkLen = 384 * K.k + (K.ekLen + (32 + 32)) by simp only [KemLay.dkLen, KemLay.ekLen]; omega,
    bytesAt_add _ _ (384 * K.k), bytesAt_add _ _ K.ekLen, bytesAt_add _ _ 32 32, add_ofNat_add, add_ofNat_add,
    show 384 * K.k + K.ekLen = 768 * K.k + 32 by simp only [KemLay.ekLen]; omega,
    show 768 * K.k + 32 + 32 = 768 * K.k + 64 by omega]
  simp only [List.append_assoc]

/-- What a region of `KEnv` must be apart from, with the sizes `sz` of the buffers. -/
abbrev okWz (sz : List Nat) (w : Nat × Nat × Nat) : Bool := VG.Proof.MlKem.Arm.sepB sz (0, 840, 36) w && VG.Proof.MlKem.Arm.sepB sz (2, 0, 64) w

theorem okWz_scr {r : List Nat} {s : Nat} {W : List (Nat × Nat × Nat)} (h : W.all (VG.Proof.MlKem.Arm.KeyGen.okWz (32768 :: r)) = true)
    (hs : 32768 ≤ s) : W.all (VG.Proof.MlKem.Arm.KeyGen.okWz (s :: r)) = true :=
  List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp h w hw
    simp only [VG.Proof.MlKem.Arm.KeyGen.okWz, Bool.and_eq_true] at this ⊢
    exact ⟨VG.Proof.MlKem.Arm.sepB_scr this.1 hs, VG.Proof.MlKem.Arm.sepB_scr this.2 hs⟩

/-- The separations of the copies and the hash of `tail_ok`, with the sizes `sz` of the buffers. -/
abbrev TailF (K : KemLay) (sz : List Nat) : Prop :=
  VG.Proof.MlKem.Arm.sepB sz (0, oSeed, 32) (3, 384 * K.k, 32) = true ∧ [(3, 384 * K.k, 32)].all (VG.Proof.MlKem.Arm.KeyGen.okWz sz) = true ∧
  (∀ i < K.k, VG.Proof.MlKem.Arm.sepAll sz (3, 384 * i, 384) [(3, 384 * K.k, 32)] = true) ∧
  VG.Proof.MlKem.Arm.sepB sz (3, 0, K.ekLen) (4, 384 * K.k, K.ekLen) = true ∧ [(4, 384 * K.k, K.ekLen)].all (VG.Proof.MlKem.Arm.KeyGen.okWz sz) = true ∧
  VG.Proof.MlKem.Arm.sepAll sz (3, 0, K.ekLen) [(4, 384 * K.k, K.ekLen)] = true ∧
  (VG.Proof.MlKem.Arm.kRegs ++ [(4, 768 * K.k + 32, 32)]).all (VG.Proof.MlKem.Arm.KeyGen.okWz sz) = true ∧
  VG.Proof.MlKem.Arm.sepB sz (2, 32, 32) (4, 768 * K.k + 64, 32) = true ∧ [(4, 768 * K.k + 64, 32)].all (VG.Proof.MlKem.Arm.KeyGen.okWz sz) = true ∧
  VG.Proof.MlKem.Arm.sepAll sz (3, 0, K.ekLen) [(4, 768 * K.k + 64, 32)] = true ∧
  VG.Proof.MlKem.Arm.sepAll sz (3, 0, K.ekLen) (VG.Proof.MlKem.Arm.kRegs ++ [(4, 768 * K.k + 32, 32)]) = true ∧
  (∀ i < K.k, VG.Proof.MlKem.Arm.sepAll sz (4, 384 * i, 384) [(4, 768 * K.k + 64, 32)] = true ∧
    VG.Proof.MlKem.Arm.sepAll sz (4, 384 * i, 384) (VG.Proof.MlKem.Arm.kRegs ++ [(4, 768 * K.k + 32, 32)]) = true ∧
    VG.Proof.MlKem.Arm.sepAll sz (4, 384 * i, 384) [(4, 384 * K.k, K.ekLen)] = true ∧
    VG.Proof.MlKem.Arm.sepAll sz (4, 384 * i, 384) [(3, 384 * K.k, 32)] = true) ∧
  VG.Proof.MlKem.Arm.sepAll sz (4, 384 * K.k, K.ekLen) [(4, 768 * K.k + 64, 32)] = true ∧
  VG.Proof.MlKem.Arm.sepAll sz (4, 384 * K.k, K.ekLen) (VG.Proof.MlKem.Arm.kRegs ++ [(4, 768 * K.k + 32, 32)]) = true ∧
  VG.Proof.MlKem.Arm.sepAll sz (4, 768 * K.k + 32, 32) [(4, 768 * K.k + 64, 32)] = true

theorem tail_facts {K : KemLay} (hK : K.WF) : VG.Proof.MlKem.Arm.KeyGen.TailF K (VG.Proof.MlKem.Arm.KeyGen.kSz K) := by
  have s := hK.scr
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15⟩ :=
    (by decide : ∀ k < 5, TailF (kOf k) (kSz (kOf k))) K.k (by have := hK.k4; omega)
  exact ⟨VG.Proof.MlKem.Arm.sepB_scr f1 s, VG.Proof.MlKem.Arm.KeyGen.okWz_scr f2 s, fun i hi => VG.Proof.MlKem.Arm.sepAll_scr (f3 i hi) s, VG.Proof.MlKem.Arm.sepB_scr f4 s, VG.Proof.MlKem.Arm.KeyGen.okWz_scr f5 s,
    VG.Proof.MlKem.Arm.sepAll_scr f6 s, VG.Proof.MlKem.Arm.KeyGen.okWz_scr f7 s, VG.Proof.MlKem.Arm.sepB_scr f8 s, VG.Proof.MlKem.Arm.KeyGen.okWz_scr f9 s, VG.Proof.MlKem.Arm.sepAll_scr f10 s, VG.Proof.MlKem.Arm.sepAll_scr f11 s,
    fun i hi => ⟨VG.Proof.MlKem.Arm.sepAll_scr (f12 i hi).1 s, VG.Proof.MlKem.Arm.sepAll_scr (f12 i hi).2.1 s, VG.Proof.MlKem.Arm.sepAll_scr (f12 i hi).2.2.1 s,
      VG.Proof.MlKem.Arm.sepAll_scr (f12 i hi).2.2.2 s⟩, VG.Proof.MlKem.Arm.sepAll_scr f13 s, VG.Proof.MlKem.Arm.sepAll_scr f14 s, VG.Proof.MlKem.Arm.sepAll_scr f15 s⟩

theorem tail_ok {K : KemLay} {s₀ s : State} (hp : VG.Proof.MlKem.Arm.KeyGen.Pre K s₀) (h : VG.Proof.MlKem.Arm.KeyGen.KS K s₀ K.k s) :
    WP isa (.seq (copy .r7 oSeed .r5 (384 * K.k) 32) <| .seq (copy .r5 0 .r6 (384 * K.k) K.ekLen) <|
      .seq (hash 136 0x06 [⟨.r5, 0, K.ekLen⟩] [⟨.r6, 768 * K.k + 32, 32⟩]) <|
      .seq (copy .r4 32 .r6 (768 * K.k + 64) 32) (.block topEnd)) s
      fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧
        s'.gpr .r0 = (if VG.Proof.MlKem.Arm.KeyGen.okK K s₀ K.k then 1 else 0) ∧ bytesAt s'.mem (State.addr (VG.Proof.MlKem.Arm.KeyGen.pEk s₀)) K.ekLen = VG.Proof.MlKem.Arm.KeyGen.EK K s₀ ∧
        bytesAt s'.mem (State.addr (VG.Proof.MlKem.Arm.KeyGen.pDk s₀)) K.dkLen = VG.Proof.MlKem.Arm.KeyGen.DK K s₀ := by
  have hL := VG.Proof.MlKem.Arm.KeyGen.lay_ok hp
  have hK := hp.wf
  have k4 := hK.k4
  have scr := hK.scr
  obtain ⟨w0, w3, w4, w2⟩ := VG.Proof.MlKem.Arm.KeyGen.buf_wr hp
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15⟩ := VG.Proof.MlKem.Arm.KeyGen.tail_facts hK
  -- `ρ` into `ek`
  have h₀ := h.env
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.copyL hL (i := 0) (j := 3) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ h₀.ctx.r7 h₀.r5
    (by decide) hK.encT (by decide) (by decide) (by decide) f1 (by rw [h₀.rd, h₀.wr]; exact VG.Proof.MlKem.Arm.mem_rd_wr w0)
    (by rw [h₀.wr]; exact w3)) fun s₁ ⟨k₁, b₁⟩ => ?_)
  have h₁ := h₀.keep hp (k₁.x []) (by simp) f2
  have ek₁ : bytesAt s₁.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 3 0) K.ekLen = VG.Proof.MlKem.Arm.KeyGen.EK K s₀ := by
    rw [VG.Proof.MlKem.Arm.KeyGen.ek_split, VG.Proof.MlKem.Arm.Enc.bytes_catK, add_ofNat_add, Nat.zero_add, b₁, h.rho]
    refine congrArg (· ++ _) (VG.Proof.MlKem.Arm.Enc.catK_congr fun i hi => ?_)
    rw [add_ofNat_add, Nat.zero_add]
    exact (Lay.bytes_keep hL k₁.frame (f3 i hi) (by decide)).trans (h.ek i hi)
  -- `ek` into `dk`
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.copyL hL (i := 3) (j := 4) (so := 0) (dO := 384 * K.k) (len := K.ekLen) ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ h₁.r5 h₁.r6 (by decide) hK.encT hK.encEk (by offs) (by offs) f4
    (by rw [h₁.rd, h₁.wr]; exact VG.Proof.MlKem.Arm.mem_rd_wr w3) (by rw [h₁.wr]; exact w4)) fun s₂ ⟨k₂, b₂⟩ => ?_)
  rw [ek₁] at b₂
  have h₂ := h₁.keep hp (k₂.x []) (by simp) f5
  have ek₂ : bytesAt s₂.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 3 0) K.ekLen = VG.Proof.MlKem.Arm.KeyGen.EK K s₀ :=
    (Lay.bytes_keep hL k₂.frame f6 (by offs)).trans ek₁
  -- `H(ek)`
  have hin := VG.Proof.MlKem.Arm.KeyGen.h_ins hp h₂
  have hout := VG.Proof.MlKem.Arm.KeyGen.h_outs hp h₂
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.hash_ok (idx := VG.Proof.MlKem.Arm.KeyGen.kidx) VG.Proof.MlKem.Arm.rate136 (by decide) (by decide) (by decide) h₂.ctx
    (List.cons_ne_nil _ _) hin hout (List.pairwise_singleton _ _)) fun s₃ ⟨k₃, o₃⟩ => ?_)
  have h₃ := h₂.keep hp (k₃.x []) (by simp) f7
  have hek₃ : bytesAt s₃.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 4 (768 * K.k + 32)) 32 = H (VG.Proof.MlKem.Arm.KeyGen.EK K s₀) := by
    have e := o₃.1
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] at e
    refine e.trans ?_
    show _ = H (VG.Proof.MlKem.Arm.KeyGen.EK K s₀)
    rw [VG.Proof.MlKem.H_eq, ← ek₂]; rfl
  -- `z`
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.copyL hL (i := 2) (j := 4) (so := 32) (dO := 768 * K.k + 64) (len := 32)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ h₃.r4 h₃.r6 (by decide) hK.encZ (by decide) (by decide) (by decide)
    f8 (by rw [h₃.rd, h₃.wr]; exact w2) (by rw [h₃.wr]; exact w4)) fun s₄ ⟨k₄, b₄⟩ => ?_)
  have h₄ := h₃.keep hp (k₄.x []) (by simp) f9
  have z₄ : bytesAt s₄.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 4 (768 * K.k + 64)) 32 = VG.Proof.MlKem.Arm.KeyGen.Z s₀ := by
    rw [b₄]
    have := congrArg (List.drop 32) h₃.seed
    rw [bytesAt_drop _ _ (by decide), bytesAt_drop _ _ (by decide)] at this
    rw [show (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 2 32 = (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 2 0 + BitVec.ofNat 64 32 by simp only [Lay.A, add_ofNat_add], this]
    simp only [Lay.A, add_ofNat_zero]; rfl
  refine WP.mono (VG.Proof.MlKem.Arm.topEnd_ok h₄.ctx h₄.sav h₄.savlr) fun s' ⟨pr, r0, m', sp'⟩ => ⟨pr, sp'.trans h₄.sp, ?_, ?_, ?_⟩
  · rw [r0, k₄.cs .r11 (by decide) (by decide), k₃.cs .r11 (by decide) (by decide), k₂.cs .r11 (by decide) (by decide),
      k₁.cs .r11 (by decide) (by decide), h.r11]
  · rw [m', show State.addr (VG.Proof.MlKem.Arm.KeyGen.pEk s₀) = (VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 3 0 by simp only [Lay.A, add_ofNat_zero]; rfl,
      Lay.bytes_keep hL k₄.frame f10 (by offs), Lay.bytes_keep hL k₃.frame f11 (by offs), ek₂]
  · have kd : ∀ i < K.k, bytesAt s₄.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 4 (384 * i)) 384 = bytesAt s.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).A 4 (384 * i)) 384 :=
      fun i hi => (Lay.bytes_keep hL k₄.frame (f12 i hi).1 (by decide)).trans
        ((Lay.bytes_keep hL k₃.frame (f12 i hi).2.1 (by decide)).trans
        ((Lay.bytes_keep hL k₂.frame (f12 i hi).2.2.1 (by decide)).trans
          (Lay.bytes_keep hL k₁.frame (f12 i hi).2.2.2 (by decide))))
    have e4 := (Lay.bytes_keep hL k₄.frame (i := 4) (o := 384 * K.k) (l := K.ekLen) f13 (by offs)).trans
      ((Lay.bytes_keep hL k₃.frame f14 (by offs)).trans b₂)
    have hh := (Lay.bytes_keep hL k₄.frame (i := 4) (o := 768 * K.k + 32) (l := 32) f15 (by decide)).trans hek₃
    simp only [Lay.A] at e4 hh z₄ kd
    rw [m', show State.addr (VG.Proof.MlKem.Arm.KeyGen.pDk s₀) = State.addr ((VG.Proof.MlKem.Arm.KeyGen.lay s₀ K).ptr 4) from rfl, VG.Proof.MlKem.Arm.KeyGen.dk_split, VG.Proof.MlKem.Arm.Enc.bytes_catK, e4, hh, z₄]
    refine congrArg (· ++ _ ++ _ ++ _) (VG.Proof.MlKem.Arm.Enc.catK_congr fun i hi => ?_)
    exact (kd i hi).trans (h.dk i hi)

/-! ## The whole function -/

theorem correct {K : KemLay} {s₀ : State} (hp : VG.Proof.MlKem.Arm.KeyGen.Pre K s₀) :
    WP isa K.keygen s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      s.gpr .r0 = (if VG.Proof.MlKem.Arm.KeyGen.okK K s₀ K.k then 1 else 0) ∧ bytesAt s.mem (State.addr (VG.Proof.MlKem.Arm.KeyGen.pEk s₀)) K.ekLen = VG.Proof.MlKem.Arm.KeyGen.EK K s₀ ∧
      bytesAt s.mem (State.addr (VG.Proof.MlKem.Arm.KeyGen.pDk s₀)) K.dkLen = VG.Proof.MlKem.Arm.KeyGen.DK K s₀ := by
  have hK := hp.wf
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.KeyGen.setup_ok hp) fun s₁ ⟨h₁, b₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.KeyGen.g_ok hp h₁ b₁) fun s₂ ⟨h₂, r₂, σ₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.KeyGen.rho_ok hp h₂ r₂ σ₂) fun s₂' ⟨h₂', r₂', σ₂'⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.KeyGen.prf_phase hp h₂' r₂' σ₂') fun s₃ ⟨h₃, r₃, p₃⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.KeyGen.rows_init hp h₃ r₃ p₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (wp_loop_ne (VG.Proof.MlKem.Arm.KeyGen.KRow K s₀) (N := K.k) hK.k1 (fun i hi s h => VG.Proof.MlKem.Arm.KeyGen.kgRow_step hp hi h)
    (fun _ h => h) h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.KeyGen.s_init hp h₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (wp_loop_ne (VG.Proof.MlKem.Arm.KeyGen.KS K s₀) (N := K.k) hK.k1 (fun j hj s h => VG.Proof.MlKem.Arm.KeyGen.kgS_step hp hj h)
    (fun _ h => h) h₆) fun s₇ h₇ => ?_)
  exact WP.mono (VG.Proof.MlKem.Arm.KeyGen.tail_ok hp h₇) fun s ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩

end VG.Proof.MlKem.Arm.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.PrfCT`. -/
section

/-!
# ML-KEM on 32-bit ARM: the `PRF`s in constant time

Two runs of `prfLoop` with the same `scratch` leak the same trace
(`prfLoop_ct`): every address is `scratch` plus an offset that depends only on
the counter `N`, and the calls take the same pointers in both runs. What each
run is at each point comes from its correctness (`relct_wp`).
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Sample (taint_block relct_wp)

theorem prf_hashOk {L : VG.Proof.MlKem.Arm.Lay} {s : State} (hc : VG.Proof.MlKem.Arm.Ctx L s) :
    VG.Proof.MlKem.Arm.HashOk L (fun _ => 0) [⟨.r7, oSigma, 33⟩] [⟨.r7, oPrf, 128⟩] s := by
  refine ⟨hc, fun p hp => ?_, fun p hp => ?_⟩ <;> rw [List.mem_singleton] at hp <;> subst hp
  · exact ⟨⟨by decide, by decide⟩, hc.r7, by decide, by decide, by decide, by decide,
      hc.sepAll0 (by decide) (by decide), VG.Proof.MlKem.Arm.mem_rd_wr hc.buf0⟩
  · exact ⟨⟨by decide, by decide⟩, hc.r7, by decide, by decide, by decide, by decide,
      hc.sepAll0 (by decide) (by decide), hc.buf0⟩

/-- A state `prfBody` runs from, as far as its timing is concerned. -/
abbrev PS (L : VG.Proof.MlKem.Arm.Lay) (N : Nat) (s : State) : Prop := VG.Proof.MlKem.Arm.Ctx L s ∧ s.gpr .r9 = BitVec.ofNat 32 N

theorem prfBody_ct {K : KemLay} (hK : K.WF) {L : VG.Proof.MlKem.Arm.Lay} (withNtt : Bool) {N₁ N : Nat} (hN : N < N₁)
    (hN₁ : N₁ ≤ 2 * K.k + 1) :
    RelCT isa (fun a b => VG.Proof.MlKem.Arm.PS L N a ∧ VG.Proof.MlKem.Arm.PS L N b) (K.prfBody withNtt N₁) fun _ _ => True := by
  have k4 := hK.k4
  -- the counter
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.PS L N a ∧ VG.Proof.MlKem.Arm.PS L N b)
    (relct_wp (taint_block [.r7] (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hab.1.1.r7, hab.2.1.r7]) (by taint_decide))
      fun a b hab => ⟨WP.mono (VG.Proof.MlKem.Arm.strb9_ok hab.1.1 (by omega) hab.1.2) fun s' ⟨k', _⟩ =>
          ⟨k'.ctx (by decide) hab.1.1, by rw [k'.cs .r9 (by decide) (by decide) (by decide), hab.1.2]⟩,
        WP.mono (VG.Proof.MlKem.Arm.strb9_ok hab.2.1 (by omega) hab.2.2) fun s' ⟨k', _⟩ =>
          ⟨k'.ctx (by decide) hab.2.1, by rw [k'.cs .r9 (by decide) (by decide) (by decide), hab.2.2]⟩⟩) ?_
  -- `PRF`
  have hh : ∀ s, VG.Proof.MlKem.Arm.PS L N s → WP isa (hash 136 0x1f [⟨.r7, oSigma, 33⟩] [⟨.r7, oPrf, 128⟩]) s (VG.Proof.MlKem.Arm.PS L N) :=
    fun s h => WP.mono (VG.Proof.MlKem.Arm.hash_ok VG.Proof.MlKem.Arm.rate136 (by decide) (by decide) (by decide) h.1 (List.cons_ne_nil _ _)
      (VG.Proof.MlKem.Arm.prf_hashOk h.1).ins (VG.Proof.MlKem.Arm.prf_hashOk h.1).outs (List.pairwise_singleton _ _)) fun s' ⟨k', _⟩ =>
      ⟨h.1.kept k', by rw [k'.cs .r9 (by decide) (by decide), h.2]⟩
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.PS L N a ∧ VG.Proof.MlKem.Arm.PS L N b)
    (relct_wp (VG.Proof.MlKem.Arm.hash_ct VG.Proof.MlKem.Arm.rate136 (by decide) (by decide) (List.cons_ne_nil _ _) fun a b hab =>
      ⟨VG.Proof.MlKem.Arm.prf_hashOk hab.1.1, VG.Proof.MlKem.Arm.prf_hashOk hab.2.1, hab.1.1.sp_eq hab.2.1⟩) fun a b hab => ⟨hh a hab.1, hh b hab.2⟩) ?_
  -- `SamplePolyCBD₂`
  let F : State → Prop := fun s => VG.Proof.MlKem.Arm.PS L N s ∧ s.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oPrf ∧
    s.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly (K.k + N))
  have eo : oPoly (K.k + N) = oPoly K.k + 1024 * N := by simp only [oPoly]; omega
  have ha : ∀ s, VG.Proof.MlKem.Arm.PS L N s → WP isa (.block (ptrTo .r0 .r7 oPrf :: slotAt .r1 .r9 (oPoly K.k))) s F :=
    fun s h => WP.mono (VG.Proof.MlKem.Arm.cbdArgs_ok hK h.1.r7 h.2) fun s' ⟨o', g0, g1⟩ =>
      ⟨⟨h.1.only o', by rw [o'.cs .r9 (by decide) (by decide), h.2]⟩, g0,
        by rw [g1, VG.Proof.MlKem.Arm.slot_eq _ (by offs), ← eo]⟩
  refine RelCT.seq (R := fun a b => F a ∧ F b) (relct_wp (VG.Proof.MlKem.Arm.relct_noMem rfl) fun a b hab => ⟨ha a hab.1, ha b hab.2⟩) ?_
  have hcb : ∀ s, F s → WP isa callCbd2 s (VG.Proof.MlKem.Arm.PS L N) := fun s h =>
    VG.Proof.MlKem.Arm.cbd2L h.1.1.ok h.2.1 h.2.2 (h.1.1.sep00 (by offs) (by offs) (by offs)) (VG.Proof.MlKem.Arm.mem_rd_wr h.1.1.buf0) h.1.1.buf0
      fun s' k' _ => ⟨h.1.1.kept k', by rw [k'.cs .r9 (by decide) (by decide), h.1.2]⟩
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.PS L N a ∧ VG.Proof.MlKem.Arm.PS L N b)
    (relct_wp (RelCT.callT VG.Proof.MlKem.Arm.cbd2T (VG.Proof.MlKem.Arm.regs2 fun a b hab => ⟨by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2, hab.2.2.2]⟩))
      fun a b hab => ⟨hcb a hab.1, hcb b hab.2⟩) ?_
  -- the NTT, and the counter
  cases withNtt
  · exact RelCT.seq (R := fun _ _ => True) (VG.Proof.MlKem.Arm.relct_noMem rfl) (VG.Proof.MlKem.Arm.relct_noMem rfl)
  · refine RelCT.seq (R := fun _ _ => True) ?_ (VG.Proof.MlKem.Arm.relct_noMem rfl)
    let G : State → Prop := fun s => s.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 (oPoly (K.k + N)) ∧
      s.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 K.oNtt
    have hn : ∀ s, VG.Proof.MlKem.Arm.PS L N s → WP isa (.block (slotAt .r0 .r9 (oPoly K.k) ++ [ptrTo .r1 .r7 K.oNtt])) s G :=
      fun s h => WP.mono (VG.Proof.MlKem.Arm.nttArgs_ok hK h.1.r7 h.2) fun s' ⟨_, g0, g1⟩ => ⟨by rw [g0, VG.Proof.MlKem.Arm.slot_eq _ (by offs), ← eo], g1⟩
    exact RelCT.seq (R := fun a b => G a ∧ G b) (relct_wp (VG.Proof.MlKem.Arm.relct_noMem rfl) fun a b hab => ⟨hn a hab.1, hn b hab.2⟩)
      (RelCT.callT VG.Proof.MlKem.Arm.nttT (VG.Proof.MlKem.Arm.regs2 fun a b hab => ⟨by rw [hab.1.1, hab.2.1], by rw [hab.1.2, hab.2.2]⟩))

theorem prfLoop_ct {K : KemLay} (hK : K.WF) {L : VG.Proof.MlKem.Arm.Lay} (withNtt : Bool) {N₀ N₁ : Nat} (h01 : N₀ < N₁)
    (hN₁ : N₁ ≤ 2 * K.k + 1)
    {s₀₁ s₀₂ : State} (hc₁ : VG.Proof.MlKem.Arm.Ctx L s₀₁) (hc₂ : VG.Proof.MlKem.Arm.Ctx L s₀₂) {σ₁ σ₂ : List Byte}
    (hσ₁ : bytesAt s₀₁.mem (L.A 0 oSigma) 32 = σ₁) (hσ₂ : bytesAt s₀₂.mem (L.A 0 oSigma) 32 = σ₂) :
    RelCT isa (fun a b => a = s₀₁ ∧ b = s₀₂) (K.prfLoop withNtt N₀ N₁) fun _ _ => True := by
  have k4 := hK.k4
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.PrfInv K L withNtt σ₁ N₀ N₁ s₀₁ 0 a ∧ VG.Proof.MlKem.Arm.PrfInv K L withNtt σ₂ N₀ N₁ s₀₂ 0 b)
    (relct_wp (VG.Proof.MlKem.Arm.relct_noMem rfl) fun a b hab => ⟨?_, ?_⟩) (RelCT.mono (VG.Proof.MlKem.Arm.relct_loop_ne (I₁ := VG.Proof.MlKem.Arm.PrfInv K L withNtt σ₁ N₀ N₁ s₀₁) (I₂ := VG.Proof.MlKem.Arm.PrfInv K L withNtt σ₂ N₀ N₁ s₀₂)
      (N := N₁ - N₀) (by omega) fun t ht => ?_)
      (fun _ _ h => h) fun _ _ _ => trivial)
  · rw [hab.1]
    exact WP.mono (VG.Proof.MlKem.Arm.mov9_ok (VG.Proof.MlKem.Arm.enc_le9 N₀ (by omega))) fun s₁ ⟨k₁, g₁, m₁⟩ =>
      ⟨k₁.mono (fun _ h => absurd h List.not_mem_nil), by rw [g₁, Nat.add_zero], by rw [m₁]; exact hσ₁,
        fun N h1 h2 => absurd h2 (by omega)⟩
  · rw [hab.2]
    exact WP.mono (VG.Proof.MlKem.Arm.mov9_ok (VG.Proof.MlKem.Arm.enc_le9 N₀ (by omega))) fun s₁ ⟨k₁, g₁, m₁⟩ =>
      ⟨k₁.mono (fun _ h => absurd h List.not_mem_nil), by rw [g₁, Nat.add_zero], by rw [m₁]; exact hσ₂,
        fun N h1 h2 => absurd h2 (by omega)⟩
  -- one iteration: the body's timing from where it runs, and each run by correctness
  exact relct_wp (RelCT.mono (VG.Proof.MlKem.Arm.prfBody_ct hK (N := N₀ + t) withNtt (by omega) hN₁) (fun a b hab =>
      ⟨⟨hab.1.kx.ctx (by decide) hc₁, hab.1.r9⟩, ⟨hab.2.kx.ctx (by decide) hc₂, hab.2.r9⟩⟩) fun _ _ h => h)
    fun a b hab => ⟨VG.Proof.MlKem.Arm.prfStep_ok hK hc₁ withNtt hN₁ ht hab.1, VG.Proof.MlKem.Arm.prfStep_ok hK hc₂ withNtt hN₁ ht hab.2⟩

end VG.Proof.MlKem.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.RowCT`. -/
section

/-!
# ML-KEM on 32-bit ARM: a row of `Â ∘ v̂` in constant time

Two runs of `rowSum` with the same `scratch`, the same `ρ` and the same row
leak the same trace (`rowSum_ct`): the seeds of the `SampleNTT`s are the same
(`ρ ‖ j ‖ i`), so their calls leak the same trace and return the same value,
on which the selection of the entry branches; every other address is `scratch`
plus an offset of the indices. What each run is at each step comes from its
correctness (`rowA_ok`, …).
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Sample (taint_block relct_wp)

/-- Constant time from any two states related by `P`, proved for each pair. -/
theorem RelCT.pointwise {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ s₁ s₂, P s₁ s₂ → RelCT isa (fun a b => a = s₁ ∧ b = s₂) c Q) : RelCT isa P c Q :=
  fun s₁ s₂ _ _ _ _ hp e₁ e₂ => h s₁ s₂ hp s₁ s₂ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

section
variable {K : KemLay} (hT : K.CallsOk) {L : VG.Proof.MlKem.Arm.Lay} {ρ : List Byte} {v₁ v₂ : Nat → VG.Spec.MlKem.Poly} {i : Nat} {fl₁ fl₂ : Bool}
  {s₀₁ s₀₂ : State}

include hT in
theorem rowBody_ct {transpose : Bool} (hp₁ : VG.Proof.MlKem.Arm.RowPre K L ρ v₁ i fl₁ s₀₁) (hp₂ : VG.Proof.MlKem.Arm.RowPre K L ρ v₂ i fl₂ s₀₂) {j : Nat}
    (hj : j < K.k) :
    RelCT isa (fun a b => VG.Proof.MlKem.Arm.RowInv K L transpose ρ v₁ i fl₁ s₀₁ j a ∧ VG.Proof.MlKem.Arm.RowInv K L transpose ρ v₂ i fl₂ s₀₂ j b)
      (K.rowBody transpose) fun _ _ => True := by
  -- the seed
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.RA K L transpose ρ v₁ i fl₁ s₀₁ j a ∧ VG.Proof.MlKem.Arm.RA K L transpose ρ v₂ i fl₂ s₀₂ j b)
    (relct_wp ?_ fun a b hab => ⟨VG.Proof.MlKem.Arm.rowA_ok hp₁ hj hab.1, VG.Proof.MlKem.Arm.rowA_ok hp₂ hj hab.2⟩) ?_
  · have h7 : ∀ a b, VG.Proof.MlKem.Arm.RowInv K L transpose ρ v₁ i fl₁ s₀₁ j a ∧ VG.Proof.MlKem.Arm.RowInv K L transpose ρ v₂ i fl₂ s₀₂ j b →
        ∀ r ∈ [Reg.r7], a.gpr r = b.gpr r := fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr
      rw [(hab.1.kx.ctx (by decide) hp₁.ctx).r7, (hab.2.kx.ctx (by decide) hp₂.ctx).r7]
    exact (hT.seedT transpose).relct h7
  -- `SampleNTT`
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.RB K L transpose ρ v₁ i fl₁ s₀₁ j a ∧ VG.Proof.MlKem.Arm.RB K L transpose ρ v₂ i fl₂ s₀₂ j b)
    (relct_wp (VG.Proof.MlKem.Arm.sample_ct (L := L) (i := 0) (o := oSeed) (j := 0) (o' := K.oAhat) (k := 0) (o'' := K.oSample)
      (fun a b hab => ?_) (by exact (hab_sep hp₁).1) (by exact (hab_sep hp₁).2.1) (by exact (hab_sep hp₁).2.2.1)
      (by exact (hab_sep hp₁).2.2.2.1) (by exact (hab_sep hp₁).2.2.2.2.1) (by exact (hab_sep hp₁).2.2.2.2.2))
      fun a b hab => ⟨VG.Proof.MlKem.Arm.rowB_ok hp₁ hab.1, VG.Proof.MlKem.Arm.rowB_ok hp₂ hab.2⟩) ?_
  · have ca := hab.1.rs.ctx hp₁
    have cb := hab.2.rs.ctx hp₂
    exact ⟨ca, cb, hab.1.r0, hab.1.r1, hab.1.r2, hab.2.r0, hab.2.r1, hab.2.r2, by rw [hab.1.seed, hab.2.seed],
      VG.Proof.MlKem.Arm.mem_rd_wr ca.buf0, ca.buf0, ca.buf0, VG.Proof.MlKem.Arm.mem_rd_wr cb.buf0, cb.buf0, cb.buf0⟩
  -- the flag
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.RC K L transpose ρ v₁ i fl₁ s₀₁ j a ∧ VG.Proof.MlKem.Arm.RC K L transpose ρ v₂ i fl₂ s₀₂ j b)
    (relct_wp (VG.Proof.MlKem.Arm.relct_noMem rfl) fun a b hab => ⟨VG.Proof.MlKem.Arm.rowC_ok hab.1, VG.Proof.MlKem.Arm.rowC_ok hab.2⟩) ?_
  -- the entry
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.RD K L transpose ρ v₁ i fl₁ s₀₁ j a ∧ VG.Proof.MlKem.Arm.RD K L transpose ρ v₂ i fl₂ s₀₂ j b)
    (relct_wp (RelCT.ite (fun a b hab => by show some a.z = some b.z; rw [hab.1.z, hab.2.z])
      (VG.Proof.MlKem.Arm.relct_noMem rfl) (VG.Proof.MlKem.Arm.relct_noMem rfl)) fun a b hab => ⟨VG.Proof.MlKem.Arm.rowD_ok hp₁ hj hab.1, VG.Proof.MlKem.Arm.rowD_ok hp₂ hj hab.2⟩) ?_
  -- the product
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.RE K L transpose ρ v₁ i fl₁ s₀₁ j a ∧ VG.Proof.MlKem.Arm.RE K L transpose ρ v₂ i fl₂ s₀₂ j b)
    (relct_wp (VG.Proof.MlKem.Arm.relct_noMem rfl) fun a b hab => ⟨VG.Proof.MlKem.Arm.rowE_ok hp₁ hj hab.1, VG.Proof.MlKem.Arm.rowE_ok hp₂ hj hab.2⟩) ?_
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.RF K L transpose ρ v₁ i fl₁ s₀₁ j a ∧ VG.Proof.MlKem.Arm.RF K L transpose ρ v₂ i fl₂ s₀₂ j b)
    (relct_wp (RelCT.callT VG.Proof.MlKem.Arm.mulT (VG.Proof.MlKem.Arm.regs4 fun a b hab => ⟨by rw [hab.1.r0, hab.2.r0], by rw [hab.1.rd.r1, hab.2.rd.r1],
      by rw [hab.1.r2, hab.2.r2], by rw [hab.1.r3, hab.2.r3]⟩))
      fun a b hab => ⟨VG.Proof.MlKem.Arm.rowF_ok hp₁ hj hab.1, VG.Proof.MlKem.Arm.rowF_ok hp₂ hj hab.2⟩) ?_
  -- the sum, and the counter
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.RG K L transpose ρ v₁ i fl₁ s₀₁ j a ∧ VG.Proof.MlKem.Arm.RG K L transpose ρ v₂ i fl₂ s₀₂ j b)
    (relct_wp (VG.Proof.MlKem.Arm.relct_noMem rfl) fun a b hab => ⟨VG.Proof.MlKem.Arm.rowG_ok hp₁ hab.1, VG.Proof.MlKem.Arm.rowG_ok hp₂ hab.2⟩) ?_
  exact RelCT.seq (R := fun _ _ => True)
    (RelCT.callT VG.Proof.MlKem.Arm.addT (VG.Proof.MlKem.Arm.regs2 fun a b hab => ⟨by rw [hab.1.r0, hab.2.r0], by rw [hab.1.r1, hab.2.r1]⟩))
    (VG.Proof.MlKem.Arm.relct_noMem rfl)
where
  hab_sep (hp : VG.Proof.MlKem.Arm.RowPre K L ρ v₁ i fl₁ s₀₁) :
      VG.Proof.MlKem.Arm.sepB L.sizes (0, oSeed, 34) (0, K.oAhat, 1024) = true ∧ VG.Proof.MlKem.Arm.sepB L.sizes (0, oSeed, 34) (0, K.oSample, 2048) = true ∧
      VG.Proof.MlKem.Arm.sepB L.sizes (0, K.oAhat, 1024) (0, K.oSample, 2048) = true ∧ VG.Proof.MlKem.Arm.sepB L.sizes (0, oSeed, 34) (1, 0, 8) = true ∧
      VG.Proof.MlKem.Arm.sepB L.sizes (0, K.oAhat, 1024) (1, 0, 8) = true ∧ VG.Proof.MlKem.Arm.sepB L.sizes (0, K.oSample, 2048) (1, 0, 8) = true := by
    have hK := hp.wf
    exact ⟨hp.ctx.sep00 (by offs) (by offs) (by offs), hp.ctx.sep00 (by offs) (by offs) (by offs),
      hp.ctx.sep00 (by offs) (by offs) (by offs), hp.ctx.sep01 (by offs) (by offs),
      hp.ctx.sep01 (by offs) (by offs), hp.ctx.sep01 (by offs) (by offs)⟩

include hT in
theorem rowSum_ct {transpose : Bool} (hp₁ : VG.Proof.MlKem.Arm.RowPre K L ρ v₁ i fl₁ s₀₁) (hp₂ : VG.Proof.MlKem.Arm.RowPre K L ρ v₂ i fl₂ s₀₂) :
    RelCT isa (fun a b => a = s₀₁ ∧ b = s₀₂) (K.rowSum transpose) fun _ _ => True := by
  have hK := hp₁.wf
  let Z : State → State → Prop := fun s₀ s₁ => Kept (L.RL [(0, K.oAcc, 1024)]) s₀ s₁ ∧ PolyIs s₁.mem (L.A 0 K.oAcc) VG.Spec.MlKem.zero
  refine RelCT.seq (R := fun a b => Z s₀₁ a ∧ Z s₀₂ b) (relct_wp (hT.zeroT.relct (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hab.1, hab.2, hp₁.ctx.r7, hp₂.ctx.r7]))
    fun a b hab => ⟨by rw [hab.1]; exact VG.Proof.MlKem.Arm.zeroPoly_ok hp₁.ctx (by kdecide) (by kenc),
      by rw [hab.2]; exact VG.Proof.MlKem.Arm.zeroPoly_ok hp₂.ctx (by kdecide) (by kenc)⟩) ?_
  have init : ∀ {v : Nat → VG.Spec.MlKem.Poly} {fl : Bool} {s₀ : State}, VG.Proof.MlKem.Arm.RowPre K L ρ v i fl s₀ → ∀ s₁, Z s₀ s₁ →
      WP isa (.block [.mov .r10 (.imm 0)]) s₁ (VG.Proof.MlKem.Arm.RowInv K L transpose ρ v i fl s₀ 0) :=
    fun {v fl s₀} hp s₁ ⟨k₁, z₁⟩ => WP.mono (VG.Proof.MlKem.Arm.movc_ok .r10 (N := 0) (by decide)) fun s₂ ⟨k₂, g₂, m₂⟩ =>
      ⟨((k₁.x _).subL hp.ctx (by kdecide)).trans ((k₂.weaken (by simp)).mono (fun _ h => absurd h List.not_mem_nil)),
        g₂, by rw [k₂.cs .r11 (by decide) (by decide) (by decide), k₁.cs .r11 (by decide) (by decide), hp.r11]
               simp [VG.Proof.MlKem.Arm.okRow],
        by rw [m₂]; exact z₁⟩
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.RowInv K L transpose ρ v₁ i fl₁ s₀₁ 0 a ∧ VG.Proof.MlKem.Arm.RowInv K L transpose ρ v₂ i fl₂ s₀₂ 0 b)
    (relct_wp (VG.Proof.MlKem.Arm.relct_noMem rfl) fun a b hab => ⟨init hp₁ a hab.1, init hp₂ b hab.2⟩) ?_
  exact RelCT.mono (VG.Proof.MlKem.Arm.relct_loop_ne (N := K.k) (by kdecide) fun j hj =>
    relct_wp (VG.Proof.MlKem.Arm.rowBody_ct hT hp₁ hp₂ hj) fun a b hab => ⟨VG.Proof.MlKem.Arm.rowBody_ok hp₁ hj hab.1, VG.Proof.MlKem.Arm.rowBody_ok hp₂ hj hab.2⟩)
    (fun _ _ h => h) fun _ _ _ => trivial

end

/-! ## `dot` -/

section
variable {K : KemLay} (hK : K.WF) {L : VG.Proof.MlKem.Arm.Lay} {a₁ v₁ a₂ v₂ : Nat → VG.Spec.MlKem.Poly} {x y : State} (hc₁ : VG.Proof.MlKem.Arm.Ctx L x) (hc₂ : VG.Proof.MlKem.Arm.Ctx L y)
    (ha₁ : ∀ j < K.k, PolyIs x.mem (L.A 0 (oPoly j)) (a₁ j))
    (hv₁ : ∀ j < K.k, PolyIs x.mem (L.A 0 (oPoly (K.k + j))) (v₁ j))
    (ha₂ : ∀ j < K.k, PolyIs y.mem (L.A 0 (oPoly j)) (a₂ j))
    (hv₂ : ∀ j < K.k, PolyIs y.mem (L.A 0 (oPoly (K.k + j))) (v₂ j))
include hK hc₁ hc₂ ha₁ hv₁ ha₂ hv₂

theorem dotBody_ct {j : Nat} (hj : j < K.k) :
    RelCT isa (fun a b => VG.Proof.MlKem.Arm.DotInv K L a₁ v₁ x j a ∧ VG.Proof.MlKem.Arm.DotInv K L a₂ v₂ y j b) K.dotBody fun a b =>
      (VG.Proof.MlKem.Arm.DotInv K L a₁ v₁ x (j + 1) a ∧ a.z = decide (j + 1 = K.k)) ∧
      (VG.Proof.MlKem.Arm.DotInv K L a₂ v₂ y (j + 1) b ∧ b.z = decide (j + 1 = K.k)) := by
  refine relct_wp (RelCT.pointwise fun u w ⟨hu, hw⟩ => ?_) fun a b hab =>
    ⟨VG.Proof.MlKem.Arm.dotBody_ok hK hc₁ ha₁ hv₁ hj hab.1, VG.Proof.MlKem.Arm.dotBody_ok hK hc₂ ha₂ hv₂ hj hab.2⟩
  refine RelCT.seq (R := fun (a b : State) =>
      (VG.Proof.MlKem.Arm.Only u a ∧ a.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oTmp ∧ a.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly j) ∧
        a.gpr .r2 = L.ptr 0 + BitVec.ofNat 32 (oPoly (K.k + j)) ∧ a.gpr .r3 = L.ptr 0 + BitVec.ofNat 32 K.oNtt) ∧
      (VG.Proof.MlKem.Arm.Only w b ∧ b.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oTmp ∧ b.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly j) ∧
        b.gpr .r2 = L.ptr 0 + BitVec.ofNat 32 (oPoly (K.k + j)) ∧ b.gpr .r3 = L.ptr 0 + BitVec.ofNat 32 K.oNtt))
    (relct_wp (VG.Proof.MlKem.Arm.relct_noMem rfl) fun a b hab => ⟨by rw [hab.1]; exact VG.Proof.MlKem.Arm.dot1_ok hK hc₁ hj hu,
      by rw [hab.2]; exact VG.Proof.MlKem.Arm.dot1_ok hK hc₂ hj hw⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => VG.Proof.MlKem.Arm.DB K L a₁ v₁ x j a ∧ VG.Proof.MlKem.Arm.DB K L a₂ v₂ y j b)
    (relct_wp (RelCT.callT VG.Proof.MlKem.Arm.mulT (VG.Proof.MlKem.Arm.regs4 fun a b hab => ⟨by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2.1, hab.2.2.2.1],
      by rw [hab.1.2.2.2.1, hab.2.2.2.2.1], by rw [hab.1.2.2.2.2, hab.2.2.2.2.2]⟩))
      fun a b ⟨⟨o₁, m0, m1, m2, m3⟩, ⟨o₂, n0, n1, n2, n3⟩⟩ =>
        ⟨VG.Proof.MlKem.Arm.dot2_ok hK hc₁ ha₁ hv₁ hj hu o₁ m0 m1 m2 m3, VG.Proof.MlKem.Arm.dot2_ok hK hc₂ ha₂ hv₂ hj hw o₂ n0 n1 n2 n3⟩) ?_
  refine RelCT.seq (R := fun (a b : State) =>
      (VG.Proof.MlKem.Arm.DB K L a₁ v₁ x j a ∧ a.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧
        a.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 K.oTmp) ∧
      (VG.Proof.MlKem.Arm.DB K L a₂ v₂ y j b ∧ b.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧
        b.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 K.oTmp))
    (relct_wp (VG.Proof.MlKem.Arm.relct_noMem rfl) fun a b hab => ⟨VG.Proof.MlKem.Arm.dot3_ok hK hc₁ hab.1, VG.Proof.MlKem.Arm.dot3_ok hK hc₂ hab.2⟩) ?_
  exact RelCT.seq (R := fun _ _ => True)
    (RelCT.callT VG.Proof.MlKem.Arm.addT (VG.Proof.MlKem.Arm.regs2 fun a b hab => ⟨by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2, hab.2.2.2]⟩))
    (VG.Proof.MlKem.Arm.relct_noMem rfl)

theorem dot_ct (hT : K.CallsOk) : RelCT isa (fun a b => a = x ∧ b = y) K.dot fun _ _ => True := by
  let Z : State → State → Prop := fun s₀ s₁ => Kept (L.RL [(0, K.oAcc, 1024)]) s₀ s₁ ∧ PolyIs s₁.mem (L.A 0 K.oAcc) VG.Spec.MlKem.zero
  refine RelCT.seq (R := fun a b => Z x a ∧ Z y b) (relct_wp (hT.zeroT.relct (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hab.1, hab.2, hc₁.r7, hc₂.r7]))
    fun a b hab => ⟨by rw [hab.1]; exact VG.Proof.MlKem.Arm.zeroPoly_ok hc₁ (by kdecide) (by kenc),
      by rw [hab.2]; exact VG.Proof.MlKem.Arm.zeroPoly_ok hc₂ (by kdecide) (by kenc)⟩) ?_
  have init : ∀ {a v : Nat → VG.Spec.MlKem.Poly} {s₀ : State}, VG.Proof.MlKem.Arm.Ctx L s₀ → ∀ s₁, Z s₀ s₁ →
      WP isa (.block [.mov .r10 (.imm 0)]) s₁ (VG.Proof.MlKem.Arm.DotInv K L a v s₀ 0) :=
    fun {a v s₀} hc s₁ ⟨k₁, z₁⟩ => WP.mono (VG.Proof.MlKem.Arm.movc_ok .r10 (N := 0) (by decide)) fun s₂ ⟨k₂, g₂, m₂⟩ =>
      ⟨((k₁.x _).subL hc (by kdecide)).trans (k₂.mono (fun _ h => absurd h List.not_mem_nil)), g₂,
        by rw [m₂]; exact z₁⟩
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.DotInv K L a₁ v₁ x 0 a ∧ VG.Proof.MlKem.Arm.DotInv K L a₂ v₂ y 0 b)
    (relct_wp (VG.Proof.MlKem.Arm.relct_noMem rfl) fun a b hab => ⟨init hc₁ a hab.1, init hc₂ b hab.2⟩) ?_
  exact RelCT.mono (VG.Proof.MlKem.Arm.relct_loop_ne (N := K.k) (by kdecide) fun j hj =>
      VG.Proof.MlKem.Arm.dotBody_ct hK hc₁ hc₂ ha₁ hv₁ ha₂ hv₂ hj)
    (fun _ _ h => h) fun _ _ _ => trivial

end

end VG.Proof.MlKem.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.KeyGenCT`. -/
section

/-!
# ML-KEM on 32-bit ARM: key generation, constant time and `Verified`

Two runs from states that agree on the public data (the pointers, the stack
pointer and `ρ`, which the contract lets the function leak) leak the same
trace (`all_ct`), phase by phase: the blocks by the taint analysis, from the
pointers, or because they access no memory (`relct_noMem`); the hashes by
`hash_ct`; the `PRF`s by `prfLoop_ct`; the rows of `t̂` by `rowSum_ct`, whose
`SampleNTT`s take the same seeds `ρ ‖ j ‖ i` in both runs; and the calls of
the primitives on the same pointers (`RelCT.callT`). What each run is at each
point comes from its correctness (`KeyGen.lean`).

All of it holds for any parameter set: the taint analyses of the blocks whose
immediates depend on it are facts of `KemLay.CallsOk`, which the parameter set
checks by evaluation. Its `outcome` is the contract's, which ML-KEM-768's
`verified` (below) and ML-KEM-1024's (`Proof/MlKem1024/Arm/`) use.
-/

namespace VG.Proof.MlKem.Arm.KeyGen

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Sample (taint_block relct_wp)

/-- Two runs, from states that agree on the public data. -/
structure Two (K : KemLay) (s₁ s₂ : State) : Prop where
  hp₁ : VG.Proof.MlKem.Arm.KeyGen.Pre K s₁
  hp₂ : VG.Proof.MlKem.Arm.KeyGen.Pre K s₂
  sp : s₁.sp = s₂.sp
  r0 : s₁.gpr .r0 = s₂.gpr .r0
  r1 : s₁.gpr .r1 = s₂.gpr .r1
  r2 : s₁.gpr .r2 = s₂.gpr .r2
  r3 : s₁.gpr .r3 = s₂.gpr .r3
  rho : VG.Proof.MlKem.Arm.KeyGen.ρ₀ K s₁ = VG.Proof.MlKem.Arm.KeyGen.ρ₀ K s₂

section
variable {K : KemLay} {s₁ s₂ : State} (two : VG.Proof.MlKem.Arm.KeyGen.Two K s₁ s₂)
include two

theorem Two.lay : VG.Proof.MlKem.Arm.KeyGen.lay s₂ K = VG.Proof.MlKem.Arm.KeyGen.lay s₁ K := by
  simp only [KeyGen.lay, VG.Proof.MlKem.Arm.KeyGen.pSeed, VG.Proof.MlKem.Arm.KeyGen.pEk, VG.Proof.MlKem.Arm.KeyGen.pDk, VG.Proof.MlKem.Arm.KeyGen.pScr, two.r0, two.r1, two.r2, two.r3, two.sp]

/-- The registers that hold pointers are the same in both runs. -/
theorem Two.regs {a b : State} (ha : VG.Proof.MlKem.Arm.KeyGen.KEnv K s₁ a) (hb : VG.Proof.MlKem.Arm.KeyGen.KEnv K s₂ b) :
    ∀ r ∈ [Reg.r4, .r5, .r6, .r7], a.gpr r = b.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [ha.r4, hb.r4]; exact two.r0
  · rw [ha.r5, hb.r5]; exact two.r1
  · rw [ha.r6, hb.r6]; exact two.r2
  · rw [ha.ctx.r7, hb.ctx.r7, two.lay]

theorem Two.sub {rs : List Reg} (hs : ∀ r ∈ rs, r ∈ [Reg.r4, .r5, .r6, .r7]) {a b : State} (ha : VG.Proof.MlKem.Arm.KeyGen.KEnv K s₁ a)
    (hb : VG.Proof.MlKem.Arm.KeyGen.KEnv K s₂ b) : ∀ r ∈ rs, a.gpr r = b.gpr r := fun r hr => two.regs ha hb r (hs r hr)

theorem Two.spE {a b : State} (ha : VG.Proof.MlKem.Arm.KeyGen.KEnv K s₁ a) (hb : VG.Proof.MlKem.Arm.KeyGen.KEnv K s₂ b) : a.sp = b.sp := by
  rw [ha.sp, hb.sp, two.sp]

/-! ## The rows of `t̂` -/

theorem kgRow_ct {i : Nat} (hi : i < K.k) :
    RelCT isa (fun a b => VG.Proof.MlKem.Arm.KeyGen.KRow K s₁ i a ∧ VG.Proof.MlKem.Arm.KeyGen.KRow K s₂ i b) K.kgRowBody fun a b =>
      (VG.Proof.MlKem.Arm.KeyGen.KRow K s₁ (i + 1) a ∧ a.z = decide (i + 1 = K.k)) ∧ (VG.Proof.MlKem.Arm.KeyGen.KRow K s₂ (i + 1) b ∧ b.z = decide (i + 1 = K.k)) := by
  refine RelCT.pointwise fun x y ⟨hx, hy⟩ => ?_
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  have py : VG.Proof.MlKem.Arm.RowPre K (VG.Proof.MlKem.Arm.KeyGen.lay s₁ K) (VG.Proof.MlKem.Arm.KeyGen.ρ₀ K s₁) (VG.Proof.MlKem.Arm.KeyGen.sK K s₂) i (VG.Proof.MlKem.Arm.KeyGen.okK K s₂ i) y := by
    have := hy.rowPre hp₂ hi; rwa [two.lay, ← two.rho] at this
  -- `RowSum`
  refine RelCT.seq (R := fun (a b : State) =>
      VG.Proof.MlKem.Arm.RowInv K (VG.Proof.MlKem.Arm.KeyGen.lay s₁ K) false (VG.Proof.MlKem.Arm.KeyGen.ρ₀ K s₁) (VG.Proof.MlKem.Arm.KeyGen.sK K s₁) i (VG.Proof.MlKem.Arm.KeyGen.okK K s₁ i) x K.k a ∧
      VG.Proof.MlKem.Arm.RowInv K (VG.Proof.MlKem.Arm.KeyGen.lay s₂ K) false (VG.Proof.MlKem.Arm.KeyGen.ρ₀ K s₂) (VG.Proof.MlKem.Arm.KeyGen.sK K s₂) i (VG.Proof.MlKem.Arm.KeyGen.okK K s₂ i) y K.k b)
    (relct_wp (VG.Proof.MlKem.Arm.rowSum_ct hp₁.calls (hx.rowPre hp₁ hi) py) fun a b hab =>
      ⟨by rw [hab.1]; exact VG.Proof.MlKem.Arm.rowSum_ok (hx.rowPre hp₁ hi), by rw [hab.2]; exact VG.Proof.MlKem.Arm.rowSum_ok (hy.rowPre hp₂ hi)⟩) ?_
  -- `t̂[i] += ê[i]`
  refine RelCT.seq (R := fun (a b : State) => VG.Proof.MlKem.Arm.KeyGen.KR2 K s₁ i x a ∧ VG.Proof.MlKem.Arm.KeyGen.KR2 K s₂ i y b)
    (relct_wp (VG.Proof.MlKem.Arm.relct_noMem rfl) fun a b hab => ⟨VG.Proof.MlKem.Arm.KeyGen.kr2_ok hp₁ hi hx hab.1, VG.Proof.MlKem.Arm.KeyGen.kr2_ok hp₂ hi hy hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => VG.Proof.MlKem.Arm.KeyGen.KR3 K s₁ i x a ∧ VG.Proof.MlKem.Arm.KeyGen.KR3 K s₂ i y b)
    (relct_wp (RelCT.callT VG.Proof.MlKem.Arm.addT (VG.Proof.MlKem.Arm.regs2 fun a b hab =>
      ⟨by rw [hab.1.r0, hab.2.r0, two.lay], by rw [hab.1.r1, hab.2.r1, two.lay]⟩))
      fun a b hab => ⟨VG.Proof.MlKem.Arm.KeyGen.kr3_ok hp₁ hi hx hab.1, VG.Proof.MlKem.Arm.KeyGen.kr3_ok hp₂ hi hy hab.2⟩) ?_
  -- its encoding
  refine RelCT.seq (R := fun (a b : State) => VG.Proof.MlKem.Arm.KeyGen.KR4 K s₁ i x a ∧ VG.Proof.MlKem.Arm.KeyGen.KR4 K s₂ i y b)
    (relct_wp (VG.Proof.MlKem.Arm.relct_noMem rfl) fun a b hab => ⟨VG.Proof.MlKem.Arm.KeyGen.kr4_ok hp₁ hi hx hab.1, VG.Proof.MlKem.Arm.KeyGen.kr4_ok hp₂ hi hy hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => VG.Proof.MlKem.Arm.KeyGen.KR5 K s₁ i x a ∧ VG.Proof.MlKem.Arm.KeyGen.KR5 K s₂ i y b)
    (relct_wp (RelCT.callT VG.Proof.MlKem.Arm.encode12T (VG.Proof.MlKem.Arm.regs2 fun a b hab =>
      ⟨by rw [hab.1.r0, hab.2.r0, two.lay], by rw [hab.1.r1, hab.2.r1, two.lay]⟩))
      fun a b hab => ⟨VG.Proof.MlKem.Arm.KeyGen.kr5_ok hp₁ hi hx hab.1, VG.Proof.MlKem.Arm.KeyGen.kr5_ok hp₂ hi hy hab.2⟩) ?_
  exact relct_wp (VG.Proof.MlKem.Arm.relct_noMem rfl) fun a b hab => ⟨VG.Proof.MlKem.Arm.KeyGen.kr6_ok hp₁ hi hx hab.1, VG.Proof.MlKem.Arm.KeyGen.kr6_ok hp₂ hi hy hab.2⟩

/-! ## `ŝ` into `dk` -/

theorem kgS_ct {j : Nat} (hj : j < K.k) :
    RelCT isa (fun a b => VG.Proof.MlKem.Arm.KeyGen.KS K s₁ j a ∧ VG.Proof.MlKem.Arm.KeyGen.KS K s₂ j b) K.kgSBody fun a b =>
      (VG.Proof.MlKem.Arm.KeyGen.KS K s₁ (j + 1) a ∧ a.z = decide (j + 1 = K.k)) ∧ (VG.Proof.MlKem.Arm.KeyGen.KS K s₂ (j + 1) b ∧ b.z = decide (j + 1 = K.k)) := by
  refine RelCT.pointwise fun x y ⟨hx, hy⟩ => ?_
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  refine RelCT.seq (R := fun (a b : State) => VG.Proof.MlKem.Arm.KeyGen.KS1 K s₁ j x a ∧ VG.Proof.MlKem.Arm.KeyGen.KS1 K s₂ j y b)
    (relct_wp (VG.Proof.MlKem.Arm.relct_noMem rfl) fun a b hab => ⟨by rw [hab.1]; exact VG.Proof.MlKem.Arm.KeyGen.ks1_ok hp₁ hj hx,
      by rw [hab.2]; exact VG.Proof.MlKem.Arm.KeyGen.ks1_ok hp₂ hj hy⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => VG.Proof.MlKem.Arm.KeyGen.KS2 K s₁ j x a ∧ VG.Proof.MlKem.Arm.KeyGen.KS2 K s₂ j y b)
    (relct_wp (RelCT.callT VG.Proof.MlKem.Arm.encode12T (VG.Proof.MlKem.Arm.regs2 fun a b hab =>
      ⟨by rw [hab.1.r0, hab.2.r0, two.lay], by rw [hab.1.r1, hab.2.r1, two.lay]⟩))
      fun a b hab => ⟨VG.Proof.MlKem.Arm.KeyGen.ks2_ok hp₁ hj hx hab.1, VG.Proof.MlKem.Arm.KeyGen.ks2_ok hp₂ hj hy hab.2⟩) ?_
  exact relct_wp (VG.Proof.MlKem.Arm.relct_noMem rfl) fun a b hab => ⟨VG.Proof.MlKem.Arm.KeyGen.ks3_ok hp₁ hj hx hab.1, VG.Proof.MlKem.Arm.KeyGen.ks3_ok hp₂ hj hy hab.2⟩

/-! ## The whole function -/

theorem all_ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) K.keygen fun _ _ => True := by
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  have hK := hp₁.wf
  -- the setup
  refine RelCT.seq (R := fun (a b : State) => (VG.Proof.MlKem.Arm.KeyGen.KEnv K s₁ a ∧ a.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₁ K).A 0 oK) = BitVec.ofNat 8 K.k) ∧
      (VG.Proof.MlKem.Arm.KeyGen.KEnv K s₂ b ∧ b.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₂ K).A 0 oK) = BitVec.ofNat 8 K.k))
    (relct_wp (hp₁.calls.kgSetupT.relct (fun a b hab r hr => by
      rw [hab.1, hab.2]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact two.r0
      · exact two.r1
      · exact two.r2
      · exact two.r3))
      fun a b hab => ⟨by rw [hab.1]; exact VG.Proof.MlKem.Arm.KeyGen.setup_ok hp₁, by rw [hab.2]; exact VG.Proof.MlKem.Arm.KeyGen.setup_ok hp₂⟩) ?_
  -- `G(d ‖ 3)`
  refine RelCT.seq (R := fun (a b : State) =>
      (VG.Proof.MlKem.Arm.KeyGen.KEnv K s₁ a ∧ bytesAt a.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₁ K).A 0 oG) 32 = VG.Proof.MlKem.KPke.kgRho K.p (VG.Proof.MlKem.Arm.KeyGen.D s₁) ∧
        bytesAt a.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₁ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (VG.Proof.MlKem.Arm.KeyGen.D s₁)) ∧
      (VG.Proof.MlKem.Arm.KeyGen.KEnv K s₂ b ∧ bytesAt b.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₂ K).A 0 oG) 32 = VG.Proof.MlKem.KPke.kgRho K.p (VG.Proof.MlKem.Arm.KeyGen.D s₂) ∧
        bytesAt b.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₂ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (VG.Proof.MlKem.Arm.KeyGen.D s₂)))
    (relct_wp (VG.Proof.MlKem.Arm.hash_ct (L := VG.Proof.MlKem.Arm.KeyGen.lay s₁ K) (idx := VG.Proof.MlKem.Arm.KeyGen.kidx) VG.Proof.MlKem.Arm.KeyGen.rate72 (by decide) (by decide) (List.cons_ne_nil _ _)
      fun a b hab => ⟨⟨hab.1.1.ctx, VG.Proof.MlKem.Arm.KeyGen.g_ins hp₁ hab.1.1, VG.Proof.MlKem.Arm.KeyGen.g_outs hp₁ hab.1.1⟩,
        by rw [← two.lay]; exact ⟨hab.2.1.ctx, VG.Proof.MlKem.Arm.KeyGen.g_ins hp₂ hab.2.1, VG.Proof.MlKem.Arm.KeyGen.g_outs hp₂ hab.2.1⟩,
        two.spE hab.1.1 hab.2.1⟩)
      fun a b hab => ⟨VG.Proof.MlKem.Arm.KeyGen.g_ok hp₁ hab.1.1 hab.1.2, VG.Proof.MlKem.Arm.KeyGen.g_ok hp₂ hab.2.1 hab.2.2⟩) ?_
  -- `ρ`
  refine RelCT.seq (R := fun (a b : State) =>
      (VG.Proof.MlKem.Arm.KeyGen.KEnv K s₁ a ∧ bytesAt a.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₁ K).A 0 oSeed) 32 = VG.Proof.MlKem.KPke.kgRho K.p (VG.Proof.MlKem.Arm.KeyGen.D s₁) ∧
        bytesAt a.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₁ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (VG.Proof.MlKem.Arm.KeyGen.D s₁)) ∧
      (VG.Proof.MlKem.Arm.KeyGen.KEnv K s₂ b ∧ bytesAt b.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₂ K).A 0 oSeed) 32 = VG.Proof.MlKem.KPke.kgRho K.p (VG.Proof.MlKem.Arm.KeyGen.D s₂) ∧
        bytesAt b.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₂ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (VG.Proof.MlKem.Arm.KeyGen.D s₂)))
    (relct_wp (VG.Proof.MlKem.Arm.taint_prog [.r7] (fun a b hab => two.sub (by simp) hab.1.1 hab.2.1) (by taint_decide))
      fun a b hab => ⟨VG.Proof.MlKem.Arm.KeyGen.rho_ok hp₁ hab.1.1 hab.1.2.1 hab.1.2.2, VG.Proof.MlKem.Arm.KeyGen.rho_ok hp₂ hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  -- the `PRF`s
  refine RelCT.seq (R := fun (a b : State) =>
      (VG.Proof.MlKem.Arm.KeyGen.KEnv K s₁ a ∧ bytesAt a.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₁ K).A 0 oSeed) 32 = VG.Proof.MlKem.KPke.kgRho K.p (VG.Proof.MlKem.Arm.KeyGen.D s₁) ∧
        ∀ N < 2 * K.k, PolyIs a.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₁ K).A 0 (oPoly (K.k + N)))
          (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.KPke.kgSigma K.p (VG.Proof.MlKem.Arm.KeyGen.D s₁)) N))) ∧
      (VG.Proof.MlKem.Arm.KeyGen.KEnv K s₂ b ∧ bytesAt b.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₂ K).A 0 oSeed) 32 = VG.Proof.MlKem.KPke.kgRho K.p (VG.Proof.MlKem.Arm.KeyGen.D s₂) ∧
        ∀ N < 2 * K.k, PolyIs b.mem ((VG.Proof.MlKem.Arm.KeyGen.lay s₂ K).A 0 (oPoly (K.k + N)))
          (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.KPke.kgSigma K.p (VG.Proof.MlKem.Arm.KeyGen.D s₂)) N))))
    (relct_wp (RelCT.pointwise fun x y hxy =>
      VG.Proof.MlKem.Arm.prfLoop_ct hK (L := VG.Proof.MlKem.Arm.KeyGen.lay s₁ K) true (by have := hK.k1; omega) (by omega) hxy.1.1.ctx
        (by rw [← two.lay]; exact hxy.2.1.ctx) rfl rfl)
      fun a b hab => ⟨VG.Proof.MlKem.Arm.KeyGen.prf_phase hp₁ hab.1.1 hab.1.2.1 hab.1.2.2, VG.Proof.MlKem.Arm.KeyGen.prf_phase hp₂ hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  -- the rows of `t̂`
  refine RelCT.seq (R := fun (a b : State) => VG.Proof.MlKem.Arm.KeyGen.KRow K s₁ 0 a ∧ VG.Proof.MlKem.Arm.KeyGen.KRow K s₂ 0 b)
    (relct_wp (VG.Proof.MlKem.Arm.relct_noMem rfl) fun a b hab =>
      ⟨VG.Proof.MlKem.Arm.KeyGen.rows_init hp₁ hab.1.1 hab.1.2.1 hab.1.2.2, VG.Proof.MlKem.Arm.KeyGen.rows_init hp₂ hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => VG.Proof.MlKem.Arm.KeyGen.KRow K s₁ K.k a ∧ VG.Proof.MlKem.Arm.KeyGen.KRow K s₂ K.k b)
    (VG.Proof.MlKem.Arm.relct_loop_ne (N := K.k) hK.k1 fun i hi => VG.Proof.MlKem.Arm.KeyGen.kgRow_ct two hi) ?_
  -- `ŝ` into `dk`
  refine RelCT.seq (R := fun (a b : State) => VG.Proof.MlKem.Arm.KeyGen.KS K s₁ 0 a ∧ VG.Proof.MlKem.Arm.KeyGen.KS K s₂ 0 b)
    (relct_wp (VG.Proof.MlKem.Arm.relct_noMem rfl) fun a b hab => ⟨VG.Proof.MlKem.Arm.KeyGen.s_init hp₁ hab.1, VG.Proof.MlKem.Arm.KeyGen.s_init hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => VG.Proof.MlKem.Arm.KeyGen.KEnv K s₁ a ∧ VG.Proof.MlKem.Arm.KeyGen.KEnv K s₂ b)
    (RelCT.mono (VG.Proof.MlKem.Arm.relct_loop_ne (N := K.k) hK.k1 fun j hj => VG.Proof.MlKem.Arm.KeyGen.kgS_ct two hj) (fun _ _ h => h)
      fun _ _ h => ⟨h.1.env, h.2.env⟩) ?_
  -- the end
  refine RelCT.seq (R := fun (a b : State) => VG.Proof.MlKem.Arm.KeyGen.KEnv K s₁ a ∧ VG.Proof.MlKem.Arm.KeyGen.KEnv K s₂ b)
    (relct_wp (hp₁.calls.rhoT.relct (fun a b hab => two.sub (by simp) hab.1 hab.2))
      fun a b hab => ⟨VG.Proof.MlKem.Arm.KeyGen.cpRho_env hp₁ hab.1, VG.Proof.MlKem.Arm.KeyGen.cpRho_env hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => VG.Proof.MlKem.Arm.KeyGen.KEnv K s₁ a ∧ VG.Proof.MlKem.Arm.KeyGen.KEnv K s₂ b)
    (relct_wp (hp₁.calls.ekT.relct (fun a b hab => two.sub (by simp) hab.1 hab.2))
      fun a b hab => ⟨VG.Proof.MlKem.Arm.KeyGen.cpEk_env hp₁ hab.1, VG.Proof.MlKem.Arm.KeyGen.cpEk_env hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => VG.Proof.MlKem.Arm.KeyGen.KEnv K s₁ a ∧ VG.Proof.MlKem.Arm.KeyGen.KEnv K s₂ b)
    (relct_wp (VG.Proof.MlKem.Arm.hash_ct (L := VG.Proof.MlKem.Arm.KeyGen.lay s₁ K) (idx := VG.Proof.MlKem.Arm.KeyGen.kidx) VG.Proof.MlKem.Arm.rate136 (by decide) (by decide) (List.cons_ne_nil _ _)
      fun a b hab => ⟨⟨hab.1.ctx, VG.Proof.MlKem.Arm.KeyGen.h_ins hp₁ hab.1, VG.Proof.MlKem.Arm.KeyGen.h_outs hp₁ hab.1⟩,
        by rw [← two.lay]; exact ⟨hab.2.ctx, VG.Proof.MlKem.Arm.KeyGen.h_ins hp₂ hab.2, VG.Proof.MlKem.Arm.KeyGen.h_outs hp₂ hab.2⟩, two.spE hab.1 hab.2⟩)
      fun a b hab => ⟨VG.Proof.MlKem.Arm.KeyGen.hashH_env hp₁ hab.1, VG.Proof.MlKem.Arm.KeyGen.hashH_env hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => VG.Proof.MlKem.Arm.KeyGen.KEnv K s₁ a ∧ VG.Proof.MlKem.Arm.KeyGen.KEnv K s₂ b)
    (relct_wp (hp₁.calls.zT.relct (fun a b hab => two.sub (by simp) hab.1 hab.2))
      fun a b hab => ⟨VG.Proof.MlKem.Arm.KeyGen.cpZ_env hp₁ hab.1, VG.Proof.MlKem.Arm.KeyGen.cpZ_env hp₂ hab.2⟩) ?_
  exact taint_block [.r7] (fun a b hab => two.sub (by simp) hab.1 hab.2) (by taint_decide)

end

/-! ## The outcome -/

/-- The `SampleNTT`s of `Â` all finished, with the entries the rows used. -/
theorem sample_some {K : KemLay} {s₀ : State} (hk : VG.Proof.MlKem.Arm.KeyGen.okK K s₀ K.k = true) :
    ∀ i < K.k, ∀ j < K.k, sampleNTT 280 (VG.Proof.MlKem.matSeed (VG.Proof.MlKem.KPke.kgRho K.p (VG.Proof.MlKem.Arm.KeyGen.D s₀)) i j) =
      some (VG.Proof.MlKem.Arm.KeyGen.aK K s₀ i j) := by
  intro i hi j hj
  have h₁ := List.all_eq_true.mp hk i (List.mem_range.mpr hi)
  have h₂ := List.all_eq_true.mp h₁ j (List.mem_range.mpr hj)
  simp only [VG.Proof.MlKem.Arm.rowSeed, Bool.false_eq_true, ite_false] at h₂
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h₂
  rw [hv]
  simp only [VG.Proof.MlKem.Arm.KeyGen.aK, VG.Proof.MlKem.Arm.effA, VG.Proof.MlKem.Arm.rowSeed, Bool.false_eq_true, ite_false, hv, Option.getD_some]

/-- A `SampleNTT` of `Â` did not finish. -/
theorem sample_none {K : KemLay} {s₀ : State} (hk : VG.Proof.MlKem.Arm.KeyGen.okK K s₀ K.k = false) :
    ∃ i < K.k, ∃ j < K.k, sampleNTT 280 (VG.Proof.MlKem.matSeed (VG.Proof.MlKem.KPke.kgRho K.p (VG.Proof.MlKem.Arm.KeyGen.D s₀)) i j) = none := by
  rw [VG.Proof.MlKem.Arm.KeyGen.okK, List.all_eq_false] at hk
  obtain ⟨i, hi, h₁⟩ := hk
  rw [Bool.not_eq_true, VG.Proof.MlKem.Arm.okRow, List.all_eq_false] at h₁
  obtain ⟨j, hj, h₂⟩ := h₁
  simp only [VG.Proof.MlKem.Arm.rowSeed, Bool.false_eq_true, ite_false] at h₂
  exact ⟨i, List.mem_range.mp hi, j, List.mem_range.mp hj, Option.not_isSome_iff_eq_none.mp h₂⟩

/-- What key generation returns and writes is the outcome of
`ML-KEM.KeyGen_internal(d, z)`. -/
theorem outcome {K : KemLay} (hK : K.WF) (s₀ : State) :
    Outcome (fun iters => keyGenInternal K.p iters (VG.Proof.MlKem.Arm.KeyGen.D s₀) (VG.Proof.MlKem.Arm.KeyGen.Z s₀)) (if VG.Proof.MlKem.Arm.KeyGen.okK K s₀ K.k then 1 else 0)
      (VG.Proof.MlKem.Arm.KeyGen.EK K s₀, VG.Proof.MlKem.Arm.KeyGen.DK K s₀) := by
  refine VG.Proof.MlKem.outcome_of_min ?_
  rw [show minIterations = 280 from rfl]
  cases hk : VG.Proof.MlKem.Arm.KeyGen.okK K s₀ K.k
  · obtain ⟨i, hi, j, hj, hn⟩ := VG.Proof.MlKem.Arm.KeyGen.sample_none hk
    refine .inr ⟨rfl, ?_⟩
    rw [VG.Proof.MlKem.KPke.keyGenInternal_eq, VG.Proof.MlKem.KPke.kpkeKeyGen_none hi hj hn]; rfl
  · refine .inl ⟨rfl, ?_⟩
    rw [VG.Proof.MlKem.KPke.keyGenInternal_eq, VG.Proof.MlKem.KPke.kpkeKeyGen_some hK.η₁ (VG.Proof.MlKem.Arm.KeyGen.sample_some hk)]; rfl

/-! ## ML-KEM-768 -/

theorem pre_of {s : State} (h : (Spec.MlKem.keyGenContract Arm.abi 8).pre s) : VG.Proof.MlKem.Arm.KeyGen.Pre kl768 s := by
  sig_pre [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h0, -, h1, h2, d1, d2, d3, d4, d5, d6, b1, b2, b3, b4, f1, f2, f3, f4⟩ := h
  exact ⟨VG.Proof.MlKem.Arm.kl768_wf, VG.Proof.MlKem.Arm.kl768_calls, h0, h1, h2, d1, d2, d3, d4, d5, d6, b1, b2, b3, b4, f1, f2, f3, f4⟩

theorem post_of {s₀ s : State} (h0 : s.gpr .r0 = if VG.Proof.MlKem.Arm.KeyGen.okK kl768 s₀ kl768.k then 1 else 0)
    (hek : bytesAt s.mem (State.addr (VG.Proof.MlKem.Arm.KeyGen.pEk s₀)) 1184 = VG.Proof.MlKem.Arm.KeyGen.EK kl768 s₀)
    (hdk : bytesAt s.mem (State.addr (VG.Proof.MlKem.Arm.KeyGen.pDk s₀)) 2400 = VG.Proof.MlKem.Arm.KeyGen.DK kl768 s₀) :
    (Spec.MlKem.keyGenContract Arm.abi 8).post s₀ s := by
  sig_post [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  rw [setWidth_append32, h0]
  have e1 : bytesAt s.mem (BitVec.setWidth 64 (s₀.gpr .r1)) 1184 = VG.Proof.MlKem.Arm.KeyGen.EK kl768 s₀ := hek
  have e2 : bytesAt s.mem (BitVec.setWidth 64 (s₀.gpr .r2)) 2400 = VG.Proof.MlKem.Arm.KeyGen.DK kl768 s₀ := hdk
  have eD : bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r0)) 32 = VG.Proof.MlKem.Arm.KeyGen.D s₀ := rfl
  have eZ : bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r0) + 32) 32 = VG.Proof.MlKem.Arm.KeyGen.Z s₀ := rfl
  rw [e1, e2, eD, eZ]
  exact VG.Proof.MlKem.Arm.KeyGen.outcome VG.Proof.MlKem.Arm.kl768_wf s₀

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x10000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 1184⟩, ⟨0x3000, 2400⟩, ⟨0x10000, 32768⟩]

theorem verified : Verified Arm.target Impl.MlKem.Arm.keygen (Spec.MlKem.keyGenContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h0, hek, hdk⟩ := VG.Proof.MlKem.Arm.KeyGen.correct (VG.Proof.MlKem.Arm.KeyGen.pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp⟩, VG.Proof.MlKem.Arm.KeyGen.post_of h0 hek hdk⟩
  · sig_pub [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at hpub
    obtain ⟨hsp, hl, h0, h1, h2, h3⟩ := hpub
    have hr : VG.Proof.MlKem.Arm.KeyGen.ρ₀ kl768 s₁ = VG.Proof.MlKem.Arm.KeyGen.ρ₀ kl768 s₂ :=
      (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (VG.Proof.MlKem.Arm.KeyGen.all_ct ⟨VG.Proof.MlKem.Arm.KeyGen.pre_of h₁, VG.Proof.MlKem.Arm.KeyGen.pre_of h₂, hsp, h0, h1, h2, h3, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨VG.Proof.MlKem.Arm.KeyGen.satState, ?_⟩
    sig_sat_check [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]

end VG.Proof.MlKem.Arm.KeyGen

end
