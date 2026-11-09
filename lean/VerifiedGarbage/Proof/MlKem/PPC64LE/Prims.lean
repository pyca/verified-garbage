module

public import VerifiedGarbage.Proof.MlKem.PPC64LE.Mul
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Lay
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Mul
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Lay
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.Covers

/-!
# ML-KEM on PPC64LE: calling the primitives

As on 32-bit ARM (`Proof/MlKem/Arm/Prims.lean`). For each primitive, a
contract written with the precondition of its proof (`Add.Pre`, …) and what
its correctness proof shows (`kAdd`, …), from which a caller runs a call of
it (`add_call`, …, by `WP.call`), given its arguments in the registers and
its buffers where it may access them (`AccArgs`, …); and that two runs that
call it with the same pointers leak the same trace (`add_ct`, …, by
`RelCT.call`, with constant time from the taint analysis of its code).
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
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
      (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.lr = s₀.lr ∧ Q s₀ s) :
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

theorem covers_append {rs ts ws : List Region} (h₁ : Covers rs ws) (h₂ : Covers ts ws) : Covers (rs ++ ts) ws :=
  fun x n ⟨q, hq, hc⟩ => (List.mem_append.mp hq).elim (fun h => h₁ x n ⟨q, h, hc⟩) (fun h => h₂ x n ⟨q, h, hc⟩)

theorem covers_cons' {r : Region} {rs ws : List Region} (h₁ : Covers [r] ws) (h₂ : Covers rs ws) :
    Covers (r :: rs) ws := covers_append (rs := [r]) h₁ h₂

theorem covers_nil' {ws : List Region} : Covers [] ws := fun _ _ ⟨_, h, _⟩ => absurd h List.not_mem_nil

theorem covers_wr {rs rd wr : List Region} (h : Covers rs wr) : Covers rs (rd ++ wr) := fun x n hi =>
  let ⟨r, hr, hc⟩ := h x n hi; ⟨r, List.mem_append_right _ hr, hc⟩

/-! ## `vg_mlkem_add` and `vg_mlkem_sub` -/

def kAdd : Contract isa := mkK Add.Pre
  (fun s₀ s => PolyIs s.mem (Add.F s₀) (add (polyAt s₀.mem (Add.F s₀)) (polyAt s₀.mem (Add.G s₀))))
  (regsEq [.r3, .r4])

def kSub : Contract isa := mkK Add.Pre
  (fun s₀ s => PolyIs s.mem (Add.F s₀) (sub (polyAt s₀.mem (Add.F s₀)) (polyAt s₀.mem (Add.G s₀))))
  (regsEq [.r3, .r4])

theorem kAdd_ok : ∀ s, kAdd.pre s → ∃ t s', Exec isa Impl.MlKem.PPC64LE.add s t s' ∧ abiPreserved s s' ∧
    kAdd.post s s' :=
  mkK_ok fun _ hp => WP.mono (Add.loop_ok hp (Add.add_hb hp)) fun _ h =>
    ⟨h.pres, h.sp, h.lr, Add.polyIs_of_inv h fun _ _ => rfl⟩

theorem kSub_ok : ∀ s, kSub.pre s → ∃ t s', Exec isa Impl.MlKem.PPC64LE.sub s t s' ∧ abiPreserved s s' ∧
    kSub.post s s' :=
  mkK_ok fun _ hp => WP.mono (Add.loop_ok hp (Add.sub_hb hp)) fun _ h =>
    ⟨h.pres, h.sp, h.lr, Add.polyIs_of_inv h fun _ _ => rfl⟩

/-- The arguments of `vg_mlkem_add` or `vg_mlkem_sub`: `f` and `g`. -/
structure AccArgs (s : State) (f g : Addr) : Prop where
  r3 : s.gpr .r3 = f
  r4 : s.gpr .r4 = g
  disj : (polyRegion f).Disjoint (polyRegion g)
  ff : f.toNat + 1024 ≤ 2 ^ 64
  fg : g.toNat + 1024 ≤ 2 ^ 64
  redF : Reduced s.mem f
  redG : Reduced s.mem g
  cw : Covers [polyRegion f] s.wr
  cr : Covers [polyRegion g] (s.rd ++ s.wr)

theorem acc_pre {s : State} {f g : Addr} (h : AccArgs s f g) :
    Add.Pre (view s [polyRegion g] [polyRegion f]) := by
  have e3 := view_gpr' s [polyRegion g] [polyRegion f] (r := .r3) (by decide)
  have e4 := view_gpr' s [polyRegion g] [polyRegion f] (r := .r4) (by decide)
  rw [h.r3] at e3; rw [h.r4] at e4
  exact ⟨by simp only [Add.G, e4]; rfl, by simp only [Add.F, e3]; rfl,
    by simp only [Add.F, Add.G, e3, e4]; exact h.disj,
    by simp only [Add.F, e3]; exact h.ff, by simp only [Add.G, e4]; exact h.fg,
    by simp only [Add.F, e3]; exact h.redF, by simp only [Add.G, e4]; exact h.redG⟩

theorem add_call {s : State} {f g : Addr} (h : AccArgs s f g) {Q : State → Prop}
    (hQ : ∀ s', Kept [polyRegion f] s s' → PolyIs s'.mem f (add (polyAt s.mem f) (polyAt s.mem g)) → Q s') :
    WP isa (.call "vg_mlkem_add" Impl.MlKem.PPC64LE.add) s Q :=
  call_kept (k := kAdd) kAdd_ok (by decide +kernel) (acc_pre h) (covers_append h.cr (covers_wr h.cw)) h.cw
    fun s' hk hp => hQ s' hk (by
      have e3 := view_gpr' s [polyRegion g] [polyRegion f] (r := .r3) (by decide)
      have e4 := view_gpr' s [polyRegion g] [polyRegion f] (r := .r4) (by decide)
      rw [h.r3] at e3; rw [h.r4] at e4
      simpa only [kAdd, mkK, Add.F, Add.G, e3, e4, State.withRegions_mem, State.callEntry_mem] using hp)

theorem sub_call {s : State} {f g : Addr} (h : AccArgs s f g) {Q : State → Prop}
    (hQ : ∀ s', Kept [polyRegion f] s s' → PolyIs s'.mem f (sub (polyAt s.mem f) (polyAt s.mem g)) → Q s') :
    WP isa (.call "vg_mlkem_sub" Impl.MlKem.PPC64LE.sub) s Q :=
  call_kept (k := kSub) kSub_ok (by decide +kernel) (acc_pre h) (covers_append h.cr (covers_wr h.cw)) h.cw
    fun s' hk hp => hQ s' hk (by
      have e3 := view_gpr' s [polyRegion g] [polyRegion f] (r := .r3) (by decide)
      have e4 := view_gpr' s [polyRegion g] [polyRegion f] (r := .r4) (by decide)
      rw [h.r3] at e3; rw [h.r4] at e4
      simpa only [kSub, mkK, Add.F, Add.G, e3, e4, State.withRegions_mem, State.callEntry_mem] using hp)

/-! ## `vg_mlkem_multiply_ntts` -/

def kMul : Contract isa := mkK Mul.Pre
  (fun s₀ s => PolyIs s.mem (Mul.H s₀) (multiplyNTTs (Mul.fp s₀) (Mul.gp s₀))) (regsEq [.r3, .r4, .r5, .r6])

theorem kMul_ok : ∀ s, kMul.pre s → ∃ t s', Exec isa Impl.MlKem.PPC64LE.multiplyNTTs s t s' ∧
    abiPreserved s s' ∧ kMul.post s s' :=
  mkK_ok fun _ hp => Mul.correct hp

/-- The arguments of `vg_mlkem_multiply_ntts`. -/
structure MulArgs (s : State) (h f g scr : Addr) : Prop where
  r3 : s.gpr .r3 = h
  r4 : s.gpr .r4 = f
  r5 : s.gpr .r5 = g
  r6 : s.gpr .r6 = scr
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
  cw : Covers [polyRegion h, polyRegion scr] s.wr
  cr : Covers [polyRegion f, polyRegion g] (s.rd ++ s.wr)

abbrev mulRd (f g : Addr) : List Region := [polyRegion f, polyRegion g]
abbrev mulWr (h scr : Addr) : List Region := [polyRegion h, polyRegion scr]

theorem mul_pre {s : State} {h f g scr : Addr} (a : MulArgs s h f g scr) :
    Mul.Pre (view s (mulRd f g) (mulWr h scr)) := by
  have e3 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .r3) (by decide)
  have e4 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .r4) (by decide)
  have e5 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .r5) (by decide)
  have e6 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .r6) (by decide)
  rw [a.r3] at e3; rw [a.r4] at e4; rw [a.r5] at e5; rw [a.r6] at e6
  exact ⟨by simp only [Mul.F, Mul.G, e4, e5]; rfl, by simp only [Mul.H, Mul.S, e3, e6]; rfl,
    by simp only [Mul.H, Mul.F, e3, e4]; exact a.hf,
    by simp only [Mul.H, Mul.G, e3, e5]; exact a.hg,
    by simp only [Mul.H, Mul.S, e3, e6]; exact a.hs,
    by simp only [Mul.F, Mul.S, e4, e6]; exact a.fs,
    by simp only [Mul.G, Mul.S, e5, e6]; exact a.gs,
    by simp only [Mul.H, e3]; exact a.fh, by simp only [Mul.F, e4]; exact a.ff,
    by simp only [Mul.G, e5]; exact a.fg, by simp only [Mul.S, e6]; exact a.fscr,
    by simp only [Mul.F, e4]; exact a.redF, by simp only [Mul.G, e5]; exact a.redG⟩

theorem mul_call {s : State} {h f g scr : Addr} (a : MulArgs s h f g scr) {Q : State → Prop}
    (hQ : ∀ s', Kept (mulWr h scr) s s' →
      PolyIs s'.mem h (multiplyNTTs (polyAt s.mem f) (polyAt s.mem g)) → Q s') :
    WP isa (.call "vg_mlkem_multiply_ntts" Impl.MlKem.PPC64LE.multiplyNTTs) s Q :=
  call_kept (k := kMul) kMul_ok (by decide +kernel) (mul_pre a) (covers_append a.cr (covers_wr a.cw)) a.cw
    fun s' hk hp => hQ s' hk (by
      have e3 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .r3) (by decide)
      have e4 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .r4) (by decide)
      have e5 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .r5) (by decide)
      rw [a.r3] at e3; rw [a.r4] at e4; rw [a.r5] at e5
      simpa only [kMul, mkK, Mul.H, Mul.fp, Mul.gp, Mul.F, Mul.G, e3, e4, e5,
        State.withRegions_mem, State.callEntry_mem] using hp)

end VG.Proof.MlKem.PPC64LE
