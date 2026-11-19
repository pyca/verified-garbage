module

public import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseMain
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMemory
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseEngine
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X25519.AArch64.Ladder
meta import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseMain
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMemory
meta import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseEngine
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X25519.AArch64.Ladder
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Proof.Ed25519.AArch64.CTSupport
public import VerifiedGarbage.Impl.Ed25519.AArch64.ScalarBase
public import VerifiedGarbage.Proof.Ed25519.AArch64.CombEntry
meta import VerifiedGarbage.Proof.Ed25519.AArch64.CTSupport
meta import VerifiedGarbage.Impl.Ed25519.AArch64.ScalarBase
meta import VerifiedGarbage.Proof.Ed25519.AArch64.CombEntry

/-! ### `Ed25519.AArch64.ScalarBaseCTEngine`, which this module and modules that import it used -/

section

/-! Expanding the secret scalar's bits, the comb and the encoding have a public
trace. The loops' counters (`x19`, and `x1` for the doublings) and the table index are
public, every address is the workspace pointer `x0` plus a constant or a counter, or the
static's address plus a constant and the counter, and the digits only reach masks. Each part
has its own taint check, so that X25519's fixed-base engine shares the comb's
(`combMultiply_ct`). -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def BaseEnginePre (base k T : Addr) (s : State) : Prop :=
  Scr s base ∧ s.gpr .x1 = k ∧
    (∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1) ∧
    (∀ q < 32, 8192 ≤ ofs base (off k q)) ∧ TblAt s base T ∧ s.syms combSym = T

/-- The comb, from the workspace pointer `x0` and the static's address: `x0` is the same in both
runs after it. -/
theorem combMultiply_ct (base T : Addr) :
    CT (fun x y => (Scr x base ∧ x.syms combSym = T) ∧ (Scr y base ∧ y.syms combSym = T))
      combMultiply (fun x y => ∀ r ∈ [Reg.x0], x.gpr r = y.gpr r) := by
  apply CT.taintSRegs (L := [combSym]) (τ := Taint.ofRegs [.x0]) _ [.x0] (by taint_decide)
  intro x y h
  refine ⟨agree_ofRegs fun r hr => ?_, fun n hn => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h.1.1.x0.trans h.2.1.x0.symm
  · simp only [List.mem_singleton] at hn
    subst hn
    exact h.1.2.trans h.2.2.symm

/-- The comb of a scalar whose bits 0–2 are clear (`combMultiplyClamped`), as `combMultiply_ct`. -/
theorem combMultiplyClamped_ct (base T : Addr) :
    CT (fun x y => (Scr x base ∧ x.syms combSym = T) ∧ (Scr y base ∧ y.syms combSym = T))
      combMultiplyClamped (fun x y => ∀ r ∈ [Reg.x0], x.gpr r = y.gpr r) := by
  apply CT.taintSRegs (L := [combSym]) (τ := Taint.ofRegs [.x0]) _ [.x0] (by taint_decide)
  intro x y h
  refine ⟨agree_ofRegs fun r hr => ?_, fun n hn => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h.1.1.x0.trans h.2.1.x0.symm
  · simp only [List.mem_singleton] at hn
    subst hn
    exact h.1.2.trans h.2.2.symm

/-- The preparation: a public trace, and the comb's start in each run. -/
theorem scalarBasePrepare_ct (base k T : Addr) :
    CT (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y) scalarBasePrepare
      (fun x y => (Scr x base ∧ x.syms combSym = T) ∧ (Scr y base ∧ y.syms combSym = T)) := by
  have hc : CT (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y) scalarBasePrepare
      (fun _ _ => True) := by
    apply CT.taintS (L := [combSym]) (Taint.ofRegs [.x0, .x1]) _ (by taint_decide)
    intro x y h
    refine ⟨agree_ofRegs fun r hr => ?_, fun n hn => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1.1.x0.trans h.2.1.x0.symm
      · exact h.1.2.1.trans h.2.2.1.symm
    · simp only [List.mem_singleton] at hn
      subst hn
      exact h.1.2.2.2.2.2.trans h.2.2.2.2.2.2.symm
  have hw : ∀ s, BaseEnginePre base k T s →
      WP isa scalarBasePrepare s (fun t => Scr t base ∧ t.syms combSym = T) := fun s h =>
    WP.mono_syms (scalarBasePrepare_ok h.1 h.2.1 h.2.2.1 h.2.2.2.1) fun _ ⟨kt, _, _⟩ syt =>
      ⟨kt.scratch h.1, by rw [syt]; exact h.2.2.2.2.2⟩
  exact (hc.wp fun x y h => ⟨hw x h.1, hw y h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- The engine: the preparation, the comb (`combMultiply_ct`) and the encoding, each with a
public trace. -/
theorem scalarBaseEngine_ct (base k T : Addr) :
    CT (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y)
      scalarBaseEngine (fun _ _ => True) := by
  rw [scalarBaseEngine]
  refine CT.seq (scalarBasePrepare_ct base k T) (CT.seq (combMultiply_ct base T) ?_)
  exact CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_ofRegs h) (by taint_decide)

end VG.Proof.Ed25519.AArch64

end

end

/-! Merged from `Proof.Ed25519.AArch64.ScalarBaseCT`. -/

@[expose] public section

section
/-! Public argument pointers survive the secret point arithmetic. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

private def BaseStart (base k out T : Addr) (s : State) : Prop :=
  scalarBaseLocal.pre s ∧ s.gpr .x0 = out ∧ s.gpr .x1 = k ∧ s.gpr .x2 = base ∧ s.syms combSym = T

private def BasePrepared (base k out T : Addr) (s : State) : Prop :=
  BaseEnginePre base k T s ∧ s.mem.readW (off base 48) 64 = out

private def BaseReady (base out : Addr) (s : State) : Prop :=
  Scr s base ∧ s.mem.readW (off base 48) 64 = out

private theorem start_ok {base k out T : Addr} {s : State} (hs : BaseStart base k out T s) :
    WP isa (.block (scalarSave ++ scalarBaseSetup)) s (BasePrepared base k out T) := by
  obtain ⟨⟨hr, hw, hd, hn, hct⟩, ho, hk, hb, hT⟩ := hs
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw, hb]; simp
  have htb : TblAt s base T := by
    rw [← hb, ← hT]; exact hct.tblAt (by rw [hr]; simp) (by simp)
  rw [WP.block_append_iff]
  refine WP.mono_syms (scalarSave_ok hb hws) fun a ⟨ga, ra, wa, _, ma, _⟩ sya => ?_
  have hwa : (⟨a.gpr .x2, 8192⟩ : Region) ∈ a.wr := by rw [ga, hb, wa]; exact hws
  refine WP.mono_syms (scalarBaseSetup_ok a hwa) fun b ⟨pb, gb, rb, wb, _, ob, mb⟩ syb => ?_
  rw [ga, hb] at pb ob mb
  refine ⟨⟨⟨pb, by rw [wb, wa]; exact hws, by rw [← hb]; exact hn⟩,
    (gb _ (by decide)).trans ((congrFun ga _).trans hk), ?_, ?_, ?_, by rw [syb, sya]; exact hT⟩,
    ob.trans ho⟩
  · intro q hq
    exact ⟨⟨k, 32⟩, by rw [rb, ra, hr, hk]; simp, Offset.contains_base _ (by omega_using [hq]) (by omega_using [hq])⟩
  · intro q hq
    rw [hk, hb] at hd
    exact farScr hd hq (by decide)
  · exact htb.of_far (by rw [rb, ra, wb, wa]) fun x hx => by
      rw [mb x (Or.inr (by omega_using [hx])), ma x (Or.inr (by omega_using [hx]))]

private theorem start_ct (base k out T : Addr) :
    CT (fun x y => BaseStart base k out T x ∧ BaseStart base k out T y)
      (.block (scalarSave ++ scalarBaseSetup))
      (fun x y => BasePrepared base k out T x ∧ BasePrepared base k out T y) := by
  have hc : CT (fun x y => BaseStart base k out T x ∧ BaseStart base k out T y)
      (.block (scalarSave ++ scalarBaseSetup)) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0, .x1, .x2]) _ (by taint_decide)
    intro x y h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.2.1.trans h.2.2.1.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
    · exact h.1.2.2.2.1.trans h.2.2.2.2.1.symm
  exact (hc.wp (fun _ _ h => ⟨start_ok h.1, start_ok h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

private theorem engine_ready [VG.Proof.Ed25519.AArch64.Divstep.Sound] {base k out T : Addr} {s : State} (hs : BasePrepared base k out T s) :
    WP isa scalarBaseEngine s (BaseReady base out) := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, ho⟩ := hs
  refine WP.mono (scalarBaseEngine_ok h1 h2 h3 h4 h5 h6) fun t ⟨kt, _⟩ => ?_
  exact ⟨kt.scratch h1, ((powersKeep_outside kt).word
    (d := 48) (Or.inl (by decide)) (by decide)).trans ho⟩

private theorem engine_ct [VG.Proof.Ed25519.AArch64.Divstep.Sound] (base k out T : Addr) :
    CT (fun x y => BasePrepared base k out T x ∧ BasePrepared base k out T y)
      scalarBaseEngine (fun x y => BaseReady base out x ∧ BaseReady base out y) := by
  have hc := (scalarBaseEngine_ct base k T).mono
    (fun _ _ (h : BasePrepared base k out T _ ∧ BasePrepared base k out T _) => ⟨h.1.1, h.2.1⟩)
    (fun _ _ h => h)
  exact (hc.wp (fun _ _ h => ⟨engine_ready h.1, engine_ready h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

private theorem finish_ct (base out : Addr) :
    CT (fun x y => BaseReady base out x ∧ BaseReady base out y)
      scalarBaseFinish (fun _ _ => True) := by
  have hc : CT (fun x y => BaseReady base out x ∧ BaseReady base out y)
      (.block scalarBaseFinishArgs) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    intro x y h
    exact agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.1.x0.trans h.2.1.x0.symm)
  have hw : ∀ s, BaseReady base out s → WP isa (.block scalarBaseFinishArgs) s
      (fun t => t.gpr .x2 = base ∧ t.gpr .x0 = out) := by
    intro s h
    exact WP.mono (scalarBaseFinishArgs_ok h.1) fun _ ht => ⟨ht.1, ht.2.1.trans h.2⟩
  have hc' := (hc.wp (fun _ _ h => ⟨hw _ h.1, hw _ h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)
  rw [scalarBaseFinish]
  refine CT.seq hc' ?_
  apply CT.taint (Taint.ofRegs [.x2, .x0]) _ (by taint_decide)
  intro x y h
  apply agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.trans h.2.1.symm
  · exact h.1.2.trans h.2.2.symm

theorem scalarBase_ct [VG.Proof.Ed25519.AArch64.Divstep.Sound] : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase := by
  intro x y tx ty x' y' hx hy ⟨hsp, ho, hk, hb, hsy⟩ ex ey
  have hc := CT.seq (start_ct (x.gpr .x2) (x.gpr .x1) (x.gpr .x0) (x.syms combSym))
    (CT.seq (engine_ct (x.gpr .x2) (x.gpr .x1) (x.gpr .x0) (x.syms combSym))
      (finish_ct (x.gpr .x2) (x.gpr .x0)))
  exact (hc _ _ _ _ _ _ ⟨hsp, ⟨hx, rfl, rfl, rfl, rfl⟩, ⟨hy, ho.symm, hk.symm, hb.symm, hsy.symm⟩⟩
    ex ey).1

end VG.Proof.Ed25519.AArch64
end

/-! Base-point multiplication satisfies the merged specification. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem scalarBase_ok [VG.Proof.Ed25519.AArch64.Divstep.Sound] (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa scalarBase s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s' := scalarBase_correct hs

def baseSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x8000
  mem := satMem
  rd := [⟨0x2000, 32⟩, ⟨0x100000, 49152⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 8192⟩]
  syms _ := 0x100000

end VG.Proof.Ed25519.AArch64
