module

public import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBasePrecomputed
import VerifiedGarbage.Proof.Ed25519.X86_64.CombLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.CombLit
import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport
import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverCTBlocks
public import VerifiedGarbage.Proof.Framework.X86_64.TaintSym
public import VerifiedGarbage.Proof.Ed25519.Group.Extended
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.X25519.X86_64.Divstep.FRow
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit
import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverParity
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCTLit
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBasePrecomputed
meta import VerifiedGarbage.Proof.Ed25519.X86_64.CombLoop
meta import VerifiedGarbage.Proof.Ed25519.X86_64.CombLit
meta import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport
meta import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverCTBlocks
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintSym
meta import VerifiedGarbage.Proof.Ed25519.Group.Extended
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.X25519.X86_64.Divstep.FRow
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverParity
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit
meta import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCTLit
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul
public import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseMain
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMemory
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul
meta import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseMain
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMemory
import VerifiedGarbage.Impl.Ed25519.X86_64.PointMul
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldWide
public import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowers
meta import VerifiedGarbage.Impl.Ed25519.X86_64.PointMul
meta import VerifiedGarbage.Proof.Ed25519.X86_64.FieldWide
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowers

/-! ### `Ed25519.X86_64.ScalarBaseCT`, which only this module used -/

section

/-! Merged from `Proof.Ed25519.X86_64.PointMulCT`. -/

@[expose] public section

/-! Merged from `Proof.Ed25519.X86_64.ScalarBaseCTEngine`. -/
section
/-! Expand secret scalar bits, multiply, and encode with a public trace. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs)

variable {fld : Arith} [EdArith fld]

def BaseEnginePre (base k T : Addr) (s : State) : Prop :=
  Scratch s base ∧ s.gpr .rsi = k ∧
    (∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1) ∧
    (∀ q < 32, 8192 ≤ ofs base (off k q)) ∧ CombTbl s T ∧ TblFar base T

end VG.Proof.Ed25519.X86_64
end

/-! Public argument pointers survive the secret point arithmetic. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

variable {fld : Arith} [EdArith fld]

private def BaseStart (base k T out : Addr) (s : State) : Prop :=
  scalarBaseLocal.pre s ∧ s.gpr .rdi = out ∧ s.gpr .rsi = k ∧ s.gpr .rdx = base ∧ s.syms combSym = T

private def BasePrepared (base k T out : Addr) (s : State) : Prop :=
  BaseEnginePre base k T s ∧ s.mem.readW (off base 48) 64 = out

private def BaseReady (base out : Addr) (s : State) : Prop :=
  Scratch s base ∧ s.mem.readW (off base 48) 64 = out

private theorem start_ok {base k T out : Addr} {s : State} (hs : BaseStart base k T out s) :
    WP isa (.block (scalarSave ++ scalarBaseSetup)) s (BasePrepared base k T out) := by
  have ⟨tbl, far⟩ := scalarBaseLocal_tbl hs.1
  obtain ⟨⟨hr, hw, hd, _, _, hn, hh⟩, ho, hk, hb, hT⟩ := hs
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw, hb]; simp
  rw [WP.block_append_iff]
  refine WP.mono_syms (scalarSave_ok hb hws) fun a ⟨ga, ra, wa, ma, _⟩ asy => ?_
  have hwa : (⟨a.gpr .rdx, 8192⟩ : Region) ∈ a.wr := by rw [ga, hb, wa]; exact hws
  refine WP.mono_syms (scalarBaseSetup_ok a hwa) fun b ⟨pb, gb, rb, wb, ob, mb⟩ bsy => ?_
  rw [ga, hb] at pb ob mb
  rw [hb] at far
  have hh2 := hh.2.2 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  rw [hT] at tbl far hh2
  have fm : Frame [⟨base, 8192⟩] s.mem b.mem :=
    (scratchFrame ma (by decide)).trans (scratchFrame mb (by decide))
  refine ⟨⟨⟨pb, by rw [wb, wa]; exact hws, by rw [← hb]; exact hn⟩,
    (gb _ (by decide)).trans ((congrFun ga _).trans hk), ?_, ?_,
    tbl.frame fm (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [← hb]; exact hh2)
      (by rw [rb, wb, ra, wa]) (by rw [bsy, asy]), far⟩, ob.trans ho⟩
  · intro q hq
    exact ⟨⟨k, 32⟩, by rw [rb, ra, hr, hk]; simp, Offset.contains_base _ (by omega_using [hq]) (by omega_using [hq])⟩
  · intro q hq
    rw [hk, hb] at hd
    exact farScratch hd hq (by decide)

private theorem start_ct (base k T out : Addr) :
    RelCT isa (fun x y => BaseStart base k T out x ∧ BaseStart base k T out y)
      (.block (scalarSave ++ scalarBaseSetup))
      (fun x y => BasePrepared base k T out x ∧ BasePrepared base k T out y) := by
  have hc : RelCT isa (fun x y => BaseStart base k T out x ∧ BaseStart base k T out y)
      (.block (scalarSave ++ scalarBaseSetup)) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi, .rsi, .rdx]) _ (by fld_taint_decide)
    intro x y h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.2.1.trans h.2.2.1.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
    · exact h.1.2.2.2.1.trans h.2.2.2.2.1.symm
  exact (hc.wp (fun _ _ h => ⟨start_ok h.1, start_ok h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

private theorem engine_ready {engine : Prog isa} (engine_ok : BaseEngineCorrect engine) {base k T out : Addr}
    {s : State} (hs : BasePrepared base k T out s) :
    WP isa engine s (BaseReady base out) := by
  refine WP.mono (engine_ok hs.1.1 hs.1.2.1 hs.1.2.2.1 hs.1.2.2.2.1 hs.1.2.2.2.2.1 hs.1.2.2.2.2.2)
    fun t ⟨kt, _⟩ => ?_
  exact ⟨kt.scratch hs.1.1, ((powersKeep_outside kt).word
    (d := 48) (Or.inl (by decide)) (by decide)).trans hs.2⟩

private theorem engine_ct {engine : Prog isa} (engine_ok : BaseEngineCorrect engine)
    (engine_ct : ∀ base k T, RelCT isa (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y)
      engine (fun _ _ => True)) (base k T out : Addr) :
    RelCT isa (fun x y => BasePrepared base k T out x ∧ BasePrepared base k T out y)
      engine (fun x y => BaseReady base out x ∧ BaseReady base out y) := by
  have hc := (engine_ct base k T).mono
    (fun _ _ (h : BasePrepared base k T out _ ∧ BasePrepared base k T out _) => ⟨h.1.1, h.2.1⟩)
    (fun _ _ h => h)
  exact (hc.wp (fun _ _ h => ⟨engine_ready engine_ok h.1, engine_ready engine_ok h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

private theorem finish_ct (base out : Addr) :
    RelCT isa (fun x y => BaseReady base out x ∧ BaseReady base out y)
      scalarBaseFinish (fun _ _ => True) := by
  have hc : RelCT isa (fun x y => BaseReady base out x ∧ BaseReady base out y)
      (.block scalarBaseFinishArgs) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    intro x y h
    exact Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.1.rdi.trans h.2.1.rdi.symm)
  have hw : ∀ s, BaseReady base out s → WP isa (.block scalarBaseFinishArgs) s
      (fun t => t.gpr .rdx = base ∧ t.gpr .rdi = out) := by
    intro s h
    exact WP.mono (scalarBaseFinishArgs_ok h.1) fun _ ht => ⟨ht.1, ht.2.1.trans h.2⟩
  have hc' := (hc.wp (fun _ _ h => ⟨hw _ h.1, hw _ h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)
  rw [scalarBaseFinish]
  refine VG.RelCT.seq hc' ?_
  apply taintFld (Taint.ofRegs [.rdx, .rdi]) _ (by fld_taint_decide)
  intro x y h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.trans h.2.1.symm
  · exact h.1.2.trans h.2.2.symm

theorem scalarBase_ct_of_engine (engine : Prog isa) (engine_ok : BaseEngineCorrect engine)
    (engineCT : ∀ base k T, RelCT isa (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y)
      engine (fun _ _ => True)) :
    ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub (scalarBaseWith engine) := by
  apply VG.RelCT.constantTime (Q := fun _ _ => True)
  intro x y tx ty x' y' ⟨hx, hy, _, ho, hk, hb, hT⟩ ex ey
  have hc := VG.RelCT.seq (start_ct (x.gpr .rdx) (x.gpr .rsi) (x.syms combSym) (x.gpr .rdi))
    (VG.RelCT.seq (engine_ct engine_ok engineCT (x.gpr .rdx) (x.gpr .rsi) (x.syms combSym) (x.gpr .rdi))
      (finish_ct (x.gpr .rdx) (x.gpr .rdi)))
  exact hc _ _ _ _ _ _ ⟨⟨hx, rfl, rfl, rfl, rfl⟩, ⟨hy, ho.symm, hk.symm, hb.symm, hT.symm⟩⟩ ex ey

end VG.Proof.Ed25519.X86_64

end

end

/-! Merged from `Proof.Ed25519.X86_64.ScalarBasePrecomputedEngine`. -/

@[expose] public section

section
namespace VG.Proof.Ed25519.X86_64
open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off ofs val4)

variable {fld : Arith} [EdArith fld]

/-- The encoding's value depends only on the point represented. -/
theorem encodedValue_rep {p : Spec.Ed25519.Point} {a : EPoint dZ} (h : Rep p a) :
    encodedValue p = (a.y : Spec.X25519.Fe).val + ((a.x : Spec.X25519.Fe).val % 2) * 2 ^ 255 := by
  have hx : p.X * Spec.X25519.pow p.Z (Spec.X25519.P - 2) = (a.x : Spec.X25519.Fe) := by
    show toZ (p.X * Spec.X25519.pow p.Z (Spec.X25519.P - 2)) = a.x
    rw [toZ_mul, toZ_pow, h.x, mul_pow_inv h.z]
  have hy : p.Y * Spec.X25519.pow p.Z (Spec.X25519.P - 2) = (a.y : Spec.X25519.Fe) := by
    show toZ (p.Y * Spec.X25519.pow p.Z (Spec.X25519.P - 2)) = a.y
    rw [toZ_mul, toZ_pow, h.y, mul_pow_inv h.z]
  simp only [encodedValue, hx, hy]
  rfl

/-- A comb: `[S]B` into slots 0–3 from the scalar's bits at byte 768, keeping what the engine
needs, in constant time where the scratch and the static are public. -/
structure CombOk (comb : Prog isa) : Prop where
  ok : ∀ {s : State} {base T : Addr} {S : Nat}, Scratch s base → S < 2 ^ (16 * 16) →
    env s.mem base 16 = Spec.Ed25519.d →
    (∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) → CombTbl s T →
    TblFar base T →
    WP isa comb s fun t => Rep (point (env t.mem base) 0 1 2 3) (S • baseAff) ∧ PowersKeep base 56 7368 s t
  ct : ∀ P : State → State → Prop,
    (∀ s₁ s₂, P s₁ s₂ → VG.X86_64.Taint.AgreeS [combSym] (Taint.ofRegs [.rdi]) s₁ s₂) →
    RelCT isa P comb fun _ _ => True

omit [EdArith fld] in
/-- The scalar's bits and the start, without calls. -/
theorem scalarBasePrepare_inline : (scalarBasePrepare fld).inline = scalarBasePrepare fld :=
  Code.inline_of_noCalls rfl

omit [EdArith fld] in
/-- An engine with its calls inlined, for a comb that inlines to `comb'`. -/
theorem scalarBaseEngineOf_inline {comb comb' : Prog isa} (hci : comb.inline = comb') :
    (scalarBaseEngineOf fld comb).inline = .seq (scalarBasePrepare fld) (.seq comb' (pointEncode fld).inline) := by
  rw [scalarBaseEngineOf]; simp only [Code.inline]; rw [scalarBasePrepare_inline, hci]

/-- `scalarBaseWith`'s frame has no calls but the engine's. -/
theorem scalarBaseWith_inline (engine : Prog isa) :
    (scalarBaseWith engine).inline = scalarBaseWith engine.inline := by
  simp only [scalarBaseWith, scalarBaseFinish, Code.inline]

theorem scalarBaseEngineOf_ok [X25519.X86_64.DivstepInv] {comb comb' : Prog isa} (hc : CombOk comb')
    (hci : comb.inline = comb') {s : State} {base k T : Addr}
    (hs : Scratch s base) (hp : s.gpr .rsi = k)
    (hr : ∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < 32, 8192 ≤ ofs base (off k q)) (ht : CombTbl s T) (hfar : TblFar base T) :
    WP isa (scalarBaseEngineOf fld comb).inline s fun t => PowersKeep base 56 7368 s t ∧
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) =
        encodedValue (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32))
          Spec.Ed25519.basePoint) := by
  rw [scalarBaseEngineOf_inline hci]
  refine WP.seq (WP.mono_syms (scalarBasePrepare_ok hs hp hr hd)
    fun b ⟨kab, _, bd, bbits, hscalar⟩ bsy => ?_)
  refine WP.seq (WP.mono (hc.ok (kab.scratch hs) hscalar bd bbits (ht.keep hfar kab bsy) hfar)
    fun c ⟨cp, kc⟩ => ?_)
  refine WP.mono (pointEncode_ok (kc.scratch (kab.scratch hs))) fun t ⟨kt, tv⟩ => ?_
  refine ⟨(kab.trans kc).trans (PowersKeep.of_rbx kt), ?_⟩
  change val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) = encodedValue (point (env c.mem base) 0 1 2 3) at tv
  rw [tv, encodedValue_rep cp, encodedValue_rep (pointMul_rep _ basePoint_rep)]

end VG.Proof.Ed25519.X86_64
end

namespace VG.Proof.Ed25519.X86_64
open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs)

variable {fld : Arith} [EdArith fld]

/-- `scalarBasePrepare_ok`, and the comb's tables kept. -/
theorem scalarBasePrepareT_ok {s : State} {base k T : Addr} (hs : Scratch s base) (hp : s.gpr .rsi = k)
    (hr : ∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < 32, 8192 ≤ ofs base (off k q)) (ht : CombTbl s T) (hfar : TblFar base T) :
    WP isa (scalarBasePrepare fld) s fun t => (PowersKeep base 56 7368 s t ∧
      point (env t.mem base) 0 1 2 3 = Spec.Ed25519.basePoint ∧
      env t.mem base 16 = Spec.Ed25519.d ∧
      (∀ i < 16 * 16, t.mem (off base (768 + i)) =
        BitVec.ofNat 8 ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32) / 2 ^ i) % 2)) ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32) < 2 ^ (16 * 16)) ∧ CombTbl t T :=
  WP.mono_syms (scalarBasePrepare_ok hs hp hr hd) fun _ h hsy => ⟨h, ht.keep hfar h.1 hsy⟩

/-- `RelCT.taint` for the analysis with the comb's static public, with the hint found by
`fld_taint_decide` for each field arithmetic. -/
theorem taintSymFld {P : State → State → Prop} {c : Prog isa} (τ : VG.X86_64.Taint.T)
    (hp : ∀ s₁ s₂, P s₁ s₂ → VG.X86_64.Taint.AgreeS [combSym] τ s₁ s₂)
    (h : ∃ hc : VG.Taint.Hint VG.X86_64.Taint.T, ((taintSym [combSym]).check τ c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  let ⟨_, h⟩ := h; VG.RelCT.taint (A := taintSym [combSym]) τ hp h

theorem scalarBaseEngineOf_ct {comb comb' : Prog isa} (hcomb : CombOk comb') (hci : comb.inline = comb')
    (base k T : Addr) :
    RelCT isa (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y)
      (scalarBaseEngineOf fld comb).inline (fun _ _ => True) := by
  have hc : RelCT isa (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y)
      (scalarBasePrepare fld) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi, .rsi]) _ (by fld_taint_decide)
    intro x y h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.rdi.trans h.2.1.rdi.symm
    · exact h.1.2.1.trans h.2.2.1.symm
  have hp := withRuns hc (fun x y h =>
    ⟨scalarBasePrepareT_ok (fld := fld) h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2,
     scalarBasePrepareT_ok (fld := fld) h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2⟩)
  rw [scalarBaseEngineOf_inline hci]
  refine VG.RelCT.seq hp ?_
  intro x y tx ty x' y' ⟨_, a, b, hab, hx, hy⟩ ex ey
  have hct : RelCT isa (fun u v =>
      (Scratch u base ∧ env u.mem base 16 = Spec.Ed25519.d ∧
        (∀ q < 256, u.mem (off base (768 + q)) =
          BitVec.ofNat 8 ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt a.mem k 32) / 2 ^ q) % 2)) ∧
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt a.mem k 32) < 2 ^ (16 * 16) ∧ CombTbl u T ∧
        TblFar base T) ∧
      (Scratch v base ∧ env v.mem base 16 = Spec.Ed25519.d ∧
        (∀ q < 256, v.mem (off base (768 + q)) =
          BitVec.ofNat 8 ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt b.mem k 32) / 2 ^ q) % 2)) ∧
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt b.mem k 32) < 2 ^ (16 * 16) ∧ CombTbl v T ∧
        TblFar base T))
      comb' (fun _ _ => True) :=
    hcomb.ct _ (fun _ _ h => ⟨rdi_agree h.1.1.rdi h.2.1.rdi, fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn
      exact h.1.2.2.2.2.1.sym.trans h.2.2.2.2.2.1.sym.symm⟩)
  have hm' := withRuns hct (fun u v h =>
    ⟨hcomb.ok h.1.1 h.1.2.2.2.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2,
     hcomb.ok h.2.1 h.2.2.2.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2⟩)
  have he : RelCT isa (fun u v => u.gpr .rdi = base ∧ v.gpr .rdi = base)
      (pointEncode fld).inline (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    intro u v h
    exact Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.trans h.2.symm)
  have hm'' := hm'.mono (fun _ _ h => h) (fun u v ⟨_, c, d, hcd, hu, hv⟩ =>
      And.intro (hu.2.scratch hcd.1.1).rdi (hv.2.scratch hcd.2.1).rdi)
  exact (VG.RelCT.seq hm'' he) _ _ _ _ _ _
    ⟨⟨hx.1.1.scratch hab.1.1, hx.1.2.2.1, hx.1.2.2.2.1, hx.1.2.2.2.2, hx.2, hab.1.2.2.2.2.2⟩,
     ⟨hy.1.1.scratch hab.2.1, hy.1.2.2.1, hy.1.2.2.2.1, hy.1.2.2.2.2, hy.2, hab.2.2.2.2.2.2⟩⟩ ex ey

/-- The comb of `combMultiply`, its doublings' calls inlined. -/
theorem combOk : CombOk (combMultiply fld combSelect (Point64.bodies fld)) :=
  ⟨fun hs hS hd hb ht hfar => combMultiply_ok hs hS hd hb ht hfar,
    fun _ hp => taintSymFld (Taint.ofRegs [.rdi]) hp (by fld_taint_decide)⟩

omit [EdArith fld] in
theorem combMultiply_inline : (combMultiply fld).inline = combMultiply fld combSelect (Point64.bodies fld) := rfl

theorem scalarBasePrecomputedEngine_ok [X25519.X86_64.DivstepInv] :
    BaseEngineCorrect (scalarBasePrecomputedEngine fld).inline :=
  fun hs hp hr hd ht hfar => scalarBaseEngineOf_ok combOk combMultiply_inline hs hp hr hd ht hfar

theorem scalarBasePrecomputedEngine_ct (base k T : Addr) :
    RelCT isa (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y)
      (scalarBasePrecomputedEngine fld).inline (fun _ _ => True) :=
  scalarBaseEngineOf_ct combOk combMultiply_inline base k T

/-- Constant time of the code with `vg_gf25519_r64_invert`'s inlined. -/
theorem scalarBase_precomputed_ct [X25519.X86_64.DivstepInv] : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub
    (scalarBase_precomputed fld).inline := by
  rw [scalarBase_precomputed, scalarBaseWith_inline]
  exact scalarBase_ct_of_engine _ scalarBasePrecomputedEngine_ok scalarBasePrecomputedEngine_ct

end VG.Proof.Ed25519.X86_64
