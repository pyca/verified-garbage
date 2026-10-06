import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBasePrecomputed
import VerifiedGarbage.Proof.Ed25519.X86_64.CombLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseEngine
import VerifiedGarbage.Proof.Ed25519.X86_64.CombLit
import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport
import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseCT
import VerifiedGarbage.Proof.Framework.X86_64.TaintSym

/-! Merged from `Proof.Ed25519.X86_64.ScalarBasePrecomputedEngine`. -/
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

theorem scalarBaseEngineOf_ok [X25519.X86_64.DivstepInv] {comb : Prog isa} (hc : CombOk comb) {s : State} {base k T : Addr}
    (hs : Scratch s base) (hp : s.gpr .rsi = k)
    (hr : ∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < 32, 8192 ≤ ofs base (off k q)) (ht : CombTbl s T) (hfar : TblFar base T) :
    WP isa (scalarBaseEngineOf fld comb) s fun t => PowersKeep base 56 7368 s t ∧
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) =
        encodedValue (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32))
          Spec.Ed25519.basePoint) := by
  rw [scalarBaseEngineOf]
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

theorem scalarBaseEngineOf_ct {comb : Prog isa} (hcomb : CombOk comb) (base k T : Addr) :
    RelCT isa (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y)
      (scalarBaseEngineOf fld comb) (fun _ _ => True) := by
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
  rw [scalarBaseEngineOf]
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
      comb (fun _ _ => True) :=
    hcomb.ct _ (fun _ _ h => ⟨rdi_agree h.1.1.rdi h.2.1.rdi, fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn
      exact h.1.2.2.2.2.1.sym.trans h.2.2.2.2.2.1.sym.symm⟩)
  have hm' := withRuns hct (fun u v h =>
    ⟨hcomb.ok h.1.1 h.1.2.2.2.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2,
     hcomb.ok h.2.1 h.2.2.2.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2⟩)
  have he : RelCT isa (fun u v => u.gpr .rdi = base ∧ v.gpr .rdi = base)
      (pointEncode fld) (fun _ _ => True) := by
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

/-- The comb of `combMultiply`. -/
theorem combOk : CombOk (combMultiply fld) :=
  ⟨fun hs hS hd hb ht hfar => combMultiply_ok hs hS hd hb ht hfar,
    fun _ hp => taintSymFld (Taint.ofRegs [.rdi]) hp (by fld_taint_decide)⟩

theorem scalarBasePrecomputedEngine_ok [X25519.X86_64.DivstepInv] : BaseEngineCorrect (scalarBasePrecomputedEngine fld) :=
  fun hs hp hr hd ht hfar => scalarBaseEngineOf_ok combOk hs hp hr hd ht hfar

theorem scalarBasePrecomputedEngine_ct (base k T : Addr) :
    RelCT isa (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y)
      (scalarBasePrecomputedEngine fld) (fun _ _ => True) :=
  scalarBaseEngineOf_ct combOk base k T

theorem scalarBase_precomputed_ct [X25519.X86_64.DivstepInv] : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub
    (scalarBase_precomputed fld) :=
  scalarBase_ct_of_engine (scalarBasePrecomputedEngine fld) scalarBasePrecomputedEngine_ok
    scalarBasePrecomputedEngine_ct

end VG.Proof.Ed25519.X86_64
