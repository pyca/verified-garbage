module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.PointOpsFn
public import VerifiedGarbage.Impl.Secp256k1.X86_64.Joint
public import VerifiedGarbage.Proof.Weierstrass.X86_64.PointOpsMixed
public import VerifiedGarbage.Proof.Weierstrass.X86_64.PointOpsVal
public import VerifiedGarbage.Proof.Secp256k1.X86_64.PointOpsLit
import VerifiedGarbage.Proof.Secp256k1.X86_64.JointTiming
import VerifiedGarbage.Proof.Secp256k1.X86_64.JacTiming
public import VerifiedGarbage.Proof.Weierstrass.JacDbl0
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Weierstrass.PointFacts
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.PointOpsCT
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract
public import VerifiedGarbage.Proof.Weierstrass.MulContract

/-!
# secp256k1's point functions on x86-64: their slots, `Verified` and contracts

Where the functions' bodies' slots are (`fnSlots`), laid out for the field
arithmetic, and the facts of `FnCfg`, `DoubleLay`, `CachedPts` and
`MixedLay` about them, checked by the kernel, with the doubling for `a = 0`
(`dblJ0`); the facts of `Impl.Weierstrass.PointOps.secp256k1`'s contracts
on x86-64 (`ws` in `rdi`, `fnPre`), which the functions meet (`fn_ok` and the
bodies' values, their doubling `dblJ0` the specification's `jacDouble0`,
`jdblSpec_dblJ0`), the spec's coordinates being the slots' field elements
(`pt_eq`, given Fermat's little theorem in `Fin p`, from the curve's group
law), the additions constant time by relating two runs from states whose
points agree (`FieldPair`); and these x86-64 contracts imply the shared ones
(`sig_pre`, `sig_post` and `sig_pub` evaluate them), which a working space
holding `p` at slot 0 and zeros elsewhere satisfies (`fnSat`).
-/

@[expose] public section

namespace VG.Proof.Secp256k1.X86_64.PointOps

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Secp256k1.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Weierstrass.X86_64.PointOps

/-- The joint verifier's slots. -/
def K : WinCfg := publicJoint.K

/-- `E`'s cached `Z²`, then `Z³`. -/
def sel : Nat := publicJoint.selected

/-- The slots the functions' bodies use. -/
def fnSlots : List Nat := rcbW K.S K.D ++ rcbR K.S K.R K.E ++ [sel, sel + 32]

abbrev Sl : Nat → Prop := (· ∈ fnSlots)

theorem K_n : K.M.n = 4 := rfl

theorem lay : Lay K.M 8192 Sl := by
  have h : ∀ x ∈ fnSlots, ∀ y ∈ fnSlots, x ≠ y → x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := by
    decide +kernel
  exact ⟨by decide +kernel, fun x y hx hy => h x hx y hy, by decide +kernel, by decide +kernel⟩

theorem p_odd : Impl.Weierstrass.PointOps.secp256k1.p % 2 = 1 := by decide +kernel

theorem fnCfg : FnCfg K Impl.Weierstrass.PointOps.secp256k1 Sl where
  n := rfl
  rx := rfl
  ry := rfl
  rz := rfl
  ex := rfl
  ey := rfl
  ez := rfl
  mo := rfl
  lay := lay
  modOk mem base h := by
    refine ⟨by decide, by decide, by decide, by decide, h, by decide +kernel, by decide +kernel⟩
  keep := by
    intro i hi hown hp
    simp only [Impl.Weierstrass.PointOps.Curve.Own, Impl.Weierstrass.PointOps.Curve.slot,
      Impl.Weierstrass.PointOps.Curve.tmpAt, Impl.Weierstrass.PointOps.Curve.pAt,
      Impl.Weierstrass.PointOps.Curve.ptBytes, Impl.Weierstrass.PointOps.secp256k1] at hown hp
    refine ⟨fun w hw => ?_, ?_⟩
    · have hw' : w ∈ [800, 832, 864, 896, 928, 960, 608, 640, 672, 512, 544, 576] := by
        revert w; decide +kernel
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      rw [K_n]
      omega
    · have : K.M.tmp = 128 := rfl
      rw [K_n, this]
      omega
  small := by decide
  wsl w hw := by
    simp only [Sl, fnSlots]
    exact List.mem_append_left _ (by
      rcases List.mem_append.mp hw with h | h
      · exact List.mem_append_left _ h
      · revert w; decide +kernel)
  clob := by decide
  odd := p_odd

theorem doubleLay : DoubleLay K 8192 Sl dblJ0 where
  lay := lay
  apart := ⟨by decide +kernel, by decide +kernel⟩
  sl x hx := by
    simp only [Sl, fnSlots]
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_append_left _ (List.mem_append_left _ h)
    · revert x; decide +kernel
  reads := by decide +kernel
  accum := by decide +kernel
  copy := by decide +kernel

theorem one_lt : K.one < Impl.Weierstrass.PointOps.secp256k1.p := by decide +kernel

theorem one_val : toM Impl.Weierstrass.PointOps.secp256k1.p (2 ^ (64 * K.M.n)) K.one = 1 := by
  have h : K.one = 1 * 2 ^ (64 * K.M.n) % Impl.Weierstrass.PointOps.secp256k1.p := by decide +kernel
  rw [h, toM_mont (unitMod_pow_two p_odd _)]
  decide +kernel

theorem cachedPts : CachedPts (m := Impl.Weierstrass.PointOps.secp256k1.p) K sel 8192 Sl dblJ0 where
  lay := {
    lay := lay
    apart := ⟨by decide +kernel, by decide +kernel⟩
    c2 := by decide +kernel
    c3 := by decide +kernel
    sl := fun x hx => by
      simp only [Sl, fnSlots]
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_append_left _ h
      · revert x; decide +kernel
    head := by decide +kernel
    tail := by decide +kernel
    dbl := doubleLay.reads
    accum := doubleLay.accum
    copy := doubleLay.copy }
  dN := by decide +kernel
  eD := by decide +kernel
  rD := by decide +kernel
  one := one_lt
  oneVal := one_val

theorem mixedLay : MixedLay K 8192 Sl dblJ0 where
  lay := lay
  apart := cachedPts.lay.apart
  sl x hx := cachedPts.lay.sl x (List.mem_append_left _ hx)
  head := by decide +kernel
  tail := by decide +kernel
  dbl := doubleLay.reads
  accum := doubleLay.accum
  copy := doubleLay.copy
  dN := cachedPts.dN
  eD := cachedPts.eD

end VG.Proof.Secp256k1.X86_64.PointOps

namespace VG.Proof.Secp256k1.X86_64.PointOps

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Secp256k1.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Weierstrass.X86_64.PointOps
open VG.Impl.Secp256k1.X86_64.PointOps (doubleFn addCachedFn addAffineFn)

/-- secp256k1's curve of `Proof/Weierstrass/PointOpsContract.lean`. -/
abbrev C : Impl.Weierstrass.PointOps.Curve := Impl.Weierstrass.PointOps.secp256k1

/-- `dblJ0` computes the specification's doubling for `a = 0`. -/
theorem dblJ0N_spec {m : Nat} [NeZero m] (e : Nat → Fin m) :
    (runOps dblJ0N e 6, runOps dblJ0N e 7, runOps dblJ0N e 8) =
      Impl.Weierstrass.PointOps.jacDouble0 (e 11) (e 12) (e 13) := by
  dsimp only [dblJ0N, dblJ0, runOps, List.foldl, FOp.run, Function.update]
  rfl

theorem jdblSpec_dblJ0 {m : Nat} [NeZero m] :
    JDblSpec (m := m) dblJ0 Impl.Weierstrass.PointOps.jacDouble0 :=
  ⟨dblJ0N, dblJ0N_ok, dblJ0_eq, dblJ0N_spec⟩

/-- The spec's point at `o` is the slots' field elements. -/
theorem pt_eq (hFe : Point.Fermat C.p) (m : Mem) (ws : Addr) {o : Nat} (ho : o + 16 * 4 < 2 ^ 32) :
    C.pt ws m o = (env C.p 4 m ws o, env C.p 4 m ws (o + 8 * 4), env C.p 4 m ws (o + 16 * 4)) := by
  have dq := Point.dec_eq C.toCurve (by decide +kernel) hFe (unitMod_pow_two p_odd _)
  have hk : C.k = 4 := rfl
  simp only [Impl.Weierstrass.PointOps.Curve.pt, Impl.Weierstrass.Point.Curve.decPt,
    Impl.Weierstrass.Point.Curve.pointAt, Impl.Weierstrass.Point.elemBytes, dq, env, Impl.Weierstrass.Point.Curve.R, hk]
  rw [coordAt_eq _ _ _ (by omega), coordAt_eq _ _ _ (by omega), coordAt_eq _ _ _ (by omega), hk,
    show 2 * (8 * 4) = 16 * 4 from rfl]

/-- What every function's analysis may consider public, but for the additions'
points. -/
def fnPub (s₁ s₂ : State) : Prop := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi

theorem below_lt {m : Mem} {ws : Addr} {o : Nat} (ho : o + 16 * 4 < 2 ^ 32)
    (h : C.Below (C.pointAt m ws o)) :
    wordsVal m ws o 4 < C.p ∧ wordsVal m ws (o + 8 * 4) 4 < C.p ∧ wordsVal m ws (o + 16 * 4) 4 < C.p := by
  obtain ⟨h0, h1, h2⟩ := h
  have hk : C.k = 4 := rfl
  simp only [Impl.Weierstrass.Point.Curve.pointAt, Impl.Weierstrass.Point.elemBytes, hk] at h0 h1 h2
  rw [coordAt_eq _ _ _ (by omega), hk] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

theorem el_eq (hFe : Point.Fermat C.p) (m : Mem) (ws : Addr) {o : Nat} (ho : o < 2 ^ 32) :
    C.el ws m o = env C.p 4 m ws o := by
  have dq := Point.dec_eq C.toCurve (by decide +kernel) hFe (unitMod_pow_two p_odd _)
  have hk : C.k = 4 := rfl
  simp only [Impl.Weierstrass.PointOps.Curve.el, dq, env, Impl.Weierstrass.Point.Curve.R, hk]
  rw [coordAt_eq _ _ _ ho, hk]

/-- The cached addition's contract on x86-64. -/
def addCachedK : Contract isa where
  pre s := fnPre s ∧ C.ModOk (s.gpr .rdi) s.mem ∧ C.Below (C.pointAt s.mem (s.gpr .rdi) C.pAt) ∧
    C.Below (C.pointAt s.mem (s.gpr .rdi) C.qAt) ∧ C.CoordBelow (s.gpr .rdi) s.mem C.zzAt ∧
    C.CoordBelow (s.gpr .rdi) s.mem C.zzzAt
  post s s' := let P := C.pt (s.gpr .rdi) s.mem C.pAt
    let Q := C.pt (s.gpr .rdi) s.mem C.qAt
    C.Result C.pAt (Impl.Weierstrass.PointOps.jacAddCached P.1 P.2.1 P.2.2 Q.1 Q.2.1 Q.2.2
      (C.el (s.gpr .rdi) s.mem C.zzAt) (C.el (s.gpr .rdi) s.mem C.zzzAt) C.dbl) (s.gpr .rdi) s.mem s'.mem
  pub s₁ s₂ := fnPub s₁ s₂ ∧ C.reads true (s₁.gpr .rdi) s₁.mem = C.reads true (s₂.gpr .rdi) s₂.mem

/-- The doubling's contract on x86-64. -/
def doubleK : Contract isa where
  pre s := fnPre s ∧ C.ModOk (s.gpr .rdi) s.mem ∧ C.Below (C.pointAt s.mem (s.gpr .rdi) C.pAt)
  post s s' := let P := C.pt (s.gpr .rdi) s.mem C.pAt
    C.Result C.pAt (C.dbl P.1 P.2.1 P.2.2) (s.gpr .rdi) s.mem s'.mem
  pub s₁ s₂ := fnPub s₁ s₂

/-- The mixed addition's contract on x86-64. -/
def addAffineK : Contract isa where
  pre s := fnPre s ∧ C.ModOk (s.gpr .rdi) s.mem ∧ C.Below (C.pointAt s.mem (s.gpr .rdi) C.pAt) ∧
    C.Below (C.pointAt s.mem (s.gpr .rdi) C.qAt)
  post s s' := let P := C.pt (s.gpr .rdi) s.mem C.pAt
    let Q := C.pt (s.gpr .rdi) s.mem C.qAt
    C.Result C.pAt (Impl.Weierstrass.PointOps.jacAddAffine P.1 P.2.1 P.2.2 Q.1 Q.2.1 Q.2.2 C.dbl)
      (s.gpr .rdi) s.mem s'.mem
  pub s₁ s₂ := fnPub s₁ s₂ ∧ C.reads false (s₁.gpr .rdi) s₁.mem = C.reads false (s₂.gpr .rdi) s₂.mem

theorem rV : ∀ x ∈ jacCoords K.R, Sl x := fun x hx =>
  doubleLay.sl x (List.mem_append_right _ (by
    simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [rcbR]))

theorem eV : ∀ x ∈ jacCoords K.E, Sl x := fun x hx =>
  cachedPts.lay.sl x (List.mem_append_left _ (List.mem_append_right _ (by
    simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [rcbR])))

theorem addCached_correct (hFe : Point.Fermat C.p)
    (hok : wrapOk addCachedFn = true) (s : State) (hs : addCachedK.pre s) :
    ∃ t s', Exec isa addCachedFn s t s' ∧ abiPreserved s s' ∧ addCachedK.post s s' := by
  obtain ⟨hp, hmod, hbp, hbq, h2, h3⟩ := hs
  have lp := below_lt (by decide) hbp
  have lq := below_lt (by decide) hbq
  have hsel : sel + 8 * K.M.n = C.zzzAt := by rw [K_n]; rfl
  obtain ⟨t, s', he, ha, hB, hv, hK⟩ := fn_ok fnCfg
    (body := Impl.Weierstrass.X86_64.PointOps.addCachedBody K sel dblJ0)
    (V := cV K sel)
    (r := fun E => Impl.Weierstrass.PointOps.jacAddCached (E K.R.x) (E K.R.y) (E K.R.z)
      (E K.E.x) (E K.E.y) (E K.E.z) (E sel) (E (sel + 8 * K.M.n)) Impl.Weierstrass.PointOps.jacDouble0)
    hok (by decide +kernel) (fun x hx => by
      simp only [cV, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (hx | hx) | rfl | rfl
      · exact rV x hx
      · exact eV x hx
      · exact cachedPts.lay.sl _ (by simp)
      · exact cachedPts.lay.sl _ (by simp))
    (fun s E hI => WP.mono (addCachedBody_val cachedPts (unitMod_pow_two p_odd _) hI jdblSpec_dblJ0)
      fun t ⟨kt, E', it, et⟩ => ⟨kt, E', it, et⟩) s hp hmod (by
      intro x hx
      rw [K_n]
      simp only [cV, jacCoords, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      have c2 := h2
      have c3 := h3
      simp only [Impl.Weierstrass.PointOps.Curve.CoordBelow] at c2 c3
      rw [coordAt_eq _ _ _ (by decide)] at c2 c3
      rcases hx with ((rfl | rfl | rfl) | (rfl | rfl | rfl)) | rfl | rfl
      · exact fnCfg.rx ▸ lp.1
      · exact fnCfg.ry ▸ lp.2.1
      · exact fnCfg.rz ▸ lp.2.2
      · exact fnCfg.ex ▸ lq.1
      · exact fnCfg.ey ▸ lq.2.1
      · exact fnCfg.ez ▸ lq.2.2
      · exact c2
      · rw [hsel]; exact c3)
  refine ⟨t, s', he, ha, hB, ?_, hK⟩
  rw [pt_eq hFe _ _ (by decide), pt_eq hFe _ _ (by decide), pt_eq hFe _ _ (by decide),
    el_eq hFe _ _ (by decide), el_eq hFe _ _ (by decide)]
  rw [show C.k = 4 from rfl] at hv
  rw [hv, fnCfg.rx, fnCfg.ry, fnCfg.rz, fnCfg.ex, fnCfg.ey,
    fnCfg.ez, hsel, K_n]
  rfl

theorem double_correct (hFe : Point.Fermat C.p)
    (hok : wrapOk doubleFn = true) (s : State) (hs : doubleK.pre s) :
    ∃ t s', Exec isa doubleFn s t s' ∧ abiPreserved s s' ∧ doubleK.post s s' := by
  obtain ⟨hp, hmod, hbp⟩ := hs
  have lp := below_lt (by decide) hbp
  obtain ⟨t, s', he, ha, hB, hv, hK⟩ := fn_ok fnCfg
    (body := Impl.Weierstrass.X86_64.PointOps.doubleBody K dblJ0)
    (V := jacCoords K.R)
    (r := fun E => Impl.Weierstrass.PointOps.jacDouble0 (E K.R.x) (E K.R.y) (E K.R.z))
    hok (by decide +kernel) rV
    (fun s E hI => WP.mono (doubleBody_val doubleLay (unitMod_pow_two p_odd _) hI jdblSpec_dblJ0)
      fun t ⟨kt, E', it, et⟩ => ⟨kt, E', it, et⟩) s hp hmod (by
      intro x hx
      rw [K_n]
      simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact fnCfg.rx ▸ lp.1
      · exact fnCfg.ry ▸ lp.2.1
      · exact fnCfg.rz ▸ lp.2.2)
  refine ⟨t, s', he, ha, hB, ?_, hK⟩
  rw [pt_eq hFe _ _ (by decide), pt_eq hFe _ _ (by decide)]
  rw [show C.k = 4 from rfl] at hv
  rw [hv, fnCfg.rx, fnCfg.ry, fnCfg.rz, K_n]
  rfl

theorem addAffine_correct (hFe : Point.Fermat C.p)
    (hok : wrapOk addAffineFn = true) (s : State) (hs : addAffineK.pre s) :
    ∃ t s', Exec isa addAffineFn s t s' ∧ abiPreserved s s' ∧ addAffineK.post s s' := by
  obtain ⟨hp, hmod, hbp, hbq⟩ := hs
  have lp := below_lt (by decide) hbp
  have lq := below_lt (by decide) hbq
  obtain ⟨t, s', he, ha, hB, hv, hK⟩ := fn_ok fnCfg
    (body := Impl.Weierstrass.X86_64.PointOps.addAffineBody K dblJ0)
    (V := mV K)
    (r := fun E => Impl.Weierstrass.PointOps.jacAddAffine (E K.R.x) (E K.R.y) (E K.R.z)
      (E K.E.x) (E K.E.y) (E K.E.z) Impl.Weierstrass.PointOps.jacDouble0)
    hok (by decide +kernel) (fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact rV x hx
      · exact eV x hx)
    (fun s E hI => WP.mono (addAffineBody_val mixedLay (unitMod_pow_two p_odd _) one_lt
      one_val hI jdblSpec_dblJ0) fun t ⟨kt, E', it, et⟩ => ⟨kt, E', it, et⟩) s hp hmod (by
      intro x hx
      rw [K_n]
      simp only [mV, jacCoords, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (rfl | rfl | rfl) | (rfl | rfl | rfl)
      · exact fnCfg.rx ▸ lp.1
      · exact fnCfg.ry ▸ lp.2.1
      · exact fnCfg.rz ▸ lp.2.2
      · exact fnCfg.ex ▸ lq.1
      · exact fnCfg.ey ▸ lq.2.1
      · exact fnCfg.ez ▸ lq.2.2)
  refine ⟨t, s', he, ha, hB, ?_, hK⟩
  rw [pt_eq hFe _ _ (by decide), pt_eq hFe _ _ (by decide), pt_eq hFe _ _ (by decide)]
  rw [show C.k = 4 from rfl] at hv
  rw [hv, fnCfg.rx, fnCfg.ry, fnCfg.rz, fnCfg.ex, fnCfg.ey,
    fnCfg.ez, K_n]
  rfl

/-! ## Constant time -/

/-- The doubling's timing depends only on `rdi`: its code branches on nothing
and addresses only `rdi` plus constants (checked on the literal). -/
theorem double_ct : ConstantTime isa doubleK.pre doubleK.pub doubleFn := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ hp e₁ e₂
  exact doubleFn_ct s₁ s₂ t₁ t₂ s₁' s₂' trivial trivial (Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact hp.2) e₁ e₂

theorem cachedChecks : CachedJacChecks K K.R K.E K.D sel dblJ0 := nafCachedJac_checks

theorem mixedChecks : JacMixedChecks K K.R K.E K.D dblJ0 := nafMixedJac_checks

theorem copyCt : ScratchCT (.block (copyPt K.M.n K.R K.D)) := joint_cached_checks.copy

theorem bytes_length (ws : Addr) (m : Mem) (o n : Nat) :
    (Impl.Weierstrass.PointOps.Curve.bytes ws m o n).length = n := by
  simp [Impl.Weierstrass.PointOps.Curve.bytes]

/-- The offsets of the numbers the additions read. -/
def readSlots (cached : Bool) : List Nat :=
  [512, 544, 576, 704, 736, 768] ++ if cached then [5408, 5440] else []

/-- Runs from states whose points' (and cached powers') bytes agree read the
same numbers. -/
theorem reads_wordsVal {cached : Bool} {ws : Addr} {m₁ m₂ : Mem}
    (h : C.reads cached ws m₁ = C.reads cached ws m₂) {x : Nat} (hx : x ∈ readSlots cached) :
    wordsVal m₁ ws x 4 = wordsVal m₂ ws x 4 := by
  simp only [Impl.Weierstrass.PointOps.Curve.reads, List.append_assoc] at h
  obtain ⟨hp, h'⟩ := append_bytes h (by rw [bytes_length, bytes_length])
  obtain ⟨hq, hc⟩ := append_bytes h' (by rw [bytes_length, bytes_length])
  simp only [readSlots, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl) | hx
  · exact wordsVal_of_bytes hp (by decide) (by decide)
  · exact wordsVal_of_bytes hp (by decide) (by decide)
  · exact wordsVal_of_bytes hp (by decide) (by decide)
  · exact wordsVal_of_bytes hq (by decide) (by decide)
  · exact wordsVal_of_bytes hq (by decide) (by decide)
  · exact wordsVal_of_bytes hq (by decide) (by decide)
  · cases cached
    · simp at hx
    · simp only [↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact wordsVal_of_bytes hc (by decide) (by decide)
      · exact wordsVal_of_bytes hc (by decide) (by decide)

theorem cV_readSlots : ∀ x ∈ cV K sel, x ∈ readSlots true := by
  decide +kernel

theorem mV_readSlots : ∀ x ∈ mV K, x ∈ readSlots false := by
  decide +kernel

theorem addCached_ct : ConstantTime isa addCachedK.pre addCachedK.pub addCachedFn := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' p₁ p₂ hp e₁ e₂
  obtain ⟨⟨_, hrdi⟩, hr⟩ := hp
  rw [← hrdi] at hr
  have lt (s : State) (hs : addCachedK.pre s) : ∀ x ∈ cV K sel, wordsVal s.mem (s.gpr .rdi) x K.M.n < C.p := by
    obtain ⟨_, _, hbp, hbq, h2, h3⟩ := hs
    have lp := below_lt (by decide) hbp
    have lq := below_lt (by decide) hbq
    simp only [Impl.Weierstrass.PointOps.Curve.CoordBelow] at h2 h3
    rw [coordAt_eq _ _ _ (by decide)] at h2 h3
    intro x hx
    rw [K_n]
    simp only [cV, jacCoords, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with ((rfl | rfl | rfl) | (rfl | rfl | rfl)) | rfl | rfl
    · exact fnCfg.rx ▸ lp.1
    · exact fnCfg.ry ▸ lp.2.1
    · exact fnCfg.rz ▸ lp.2.2
    · exact fnCfg.ex ▸ lq.1
    · exact fnCfg.ey ▸ lq.2.1
    · exact fnCfg.ez ▸ lq.2.2
    · exact h2
    · rw [K_n]; exact h3
  have hV : ∀ x ∈ cV K sel, Sl x := fun x hx => by
    simp only [cV, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (hx | hx) | rfl | rfl
    · exact rV x hx
    · exact eV x hx
    · exact cachedPts.lay.sl _ (by simp)
    · exact cachedPts.lay.sl _ (by simp)
  have I₁ := inv_of fnCfg hV p₁.1 p₁.2.1 (lt s₁ p₁)
  have I₂ := inv_of fnCfg hV p₂.1 p₂.2.1 (lt s₂ p₂)
  rw [← hrdi] at I₂
  have ag : ∀ x ∈ cV K sel, env C.p K.M.n s₂.mem (s₁.gpr .rdi) x =
      env C.p K.M.n s₁.mem (s₁.gpr .rdi) x := by
    intro x hx
    simp only [env, K_n]
    rw [reads_wordsVal hr.symm (cV_readSlots x hx)]
  have hb := addCachedBody_relCT (base := s₁.gpr .rdi) cachedPts.lay (unitMod_pow_two p_odd _) cachedPts.one
    cachedChecks copyCt (E := env C.p K.M.n s₁.mem (s₁.gpr .rdi)) (fun _ h => h) ⟨dblJ0N, dblJ0N_ok, dblJ0_eq⟩
  rw [Code.inline_of_noCalls (by decide +kernel)] at hb
  exact (wrap_relCT hb s₁ s₂ t₁ t₂ s₁' s₂' ⟨I₁, I₂.congr_env ag⟩ e₁ e₂).1

theorem addAffine_ct : ConstantTime isa addAffineK.pre addAffineK.pub addAffineFn := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' p₁ p₂ hp e₁ e₂
  obtain ⟨⟨_, hrdi⟩, hr⟩ := hp
  rw [← hrdi] at hr
  have lt (s : State) (hs : addAffineK.pre s) : ∀ x ∈ mV K, wordsVal s.mem (s.gpr .rdi) x K.M.n < C.p := by
    obtain ⟨_, _, hbp, hbq⟩ := hs
    have lp := below_lt (by decide) hbp
    have lq := below_lt (by decide) hbq
    intro x hx
    rw [K_n]
    simp only [mV, jacCoords, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl) | (rfl | rfl | rfl)
    · exact fnCfg.rx ▸ lp.1
    · exact fnCfg.ry ▸ lp.2.1
    · exact fnCfg.rz ▸ lp.2.2
    · exact fnCfg.ex ▸ lq.1
    · exact fnCfg.ey ▸ lq.2.1
    · exact fnCfg.ez ▸ lq.2.2
  have hV : ∀ x ∈ mV K, Sl x := fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact rV x hx
    · exact eV x hx
  have I₁ := inv_of fnCfg hV p₁.1 p₁.2.1 (lt s₁ p₁)
  have I₂ := inv_of fnCfg hV p₂.1 p₂.2.1 (lt s₂ p₂)
  rw [← hrdi] at I₂
  have ag : ∀ x ∈ mV K, env C.p K.M.n s₂.mem (s₁.gpr .rdi) x =
      env C.p K.M.n s₁.mem (s₁.gpr .rdi) x := by
    intro x hx
    simp only [env, K_n]
    rw [reads_wordsVal (cached := false) hr.symm (mV_readSlots x hx)]
  have hb := addAffineBody_relCT (base := s₁.gpr .rdi) mixedLay (unitMod_pow_two p_odd _)
    one_lt mixedChecks copyCt (E := env C.p K.M.n s₁.mem (s₁.gpr .rdi)) ⟨dblJ0N, dblJ0N_ok, dblJ0_eq⟩
  rw [Code.inline_of_noCalls (by decide +kernel)] at hb
  exact (wrap_relCT hb s₁ s₂ t₁ t₂ s₁' s₂' ⟨I₁, I₂.congr_env ag⟩ e₁ e₂).1

end VG.Proof.Secp256k1.X86_64.PointOps

namespace VG.Proof.Secp256k1.X86_64.PointOps

open VG VG.X86_64 VG.Proof.Weierstrass.X86_64.PointOps
open VG.Impl.Secp256k1.X86_64.PointOps

/-! ## The shared contracts -/

/-- `p` at slot 0 of a working space at `0x1000`, the rest zeros. -/
def satMem : Mem := fun a =>
  let i := (a - 0x1000).toNat
  if 64 ≤ i ∧ i < 96 then BitVec.ofNat 8 (C.p >>> (8 * (i - 64))) else 0

/-- A state satisfying the preconditions. -/
def fnSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem sat_mod : C.ModOk 0x1000 satMem := by
  unfold Impl.Weierstrass.PointOps.Curve.ModOk; decide +kernel

theorem sat_p : C.toCurve.Below (C.toCurve.pointAt satMem 0x1000 C.pAt) := by
  unfold Impl.Weierstrass.Point.Curve.Below; decide +kernel

theorem sat_q : C.toCurve.Below (C.toCurve.pointAt satMem 0x1000 C.qAt) := by
  unfold Impl.Weierstrass.Point.Curve.Below; decide +kernel

theorem sat_c2 : C.CoordBelow 0x1000 satMem C.zzAt := by
  unfold Impl.Weierstrass.PointOps.Curve.CoordBelow; decide +kernel

theorem sat_c3 : C.CoordBelow 0x1000 satMem C.zzzAt := by
  unfold Impl.Weierstrass.PointOps.Curve.CoordBelow; decide +kernel

theorem sat_ret : (⟨0x8000, 8⟩ : Region).Disjoint ⟨0x1000, 8192⟩ :=
  Region.disjoint_of_le (by decide) (by decide) (by decide)

theorem addCachedK_implies : addCachedK.Implies (C.addCachedContract X86_64.abi) where
  pre s h := by
    sig_pre [Impl.Weierstrass.PointOps.Curve.addCachedContract, Impl.Weierstrass.PointOps.sig,
      X86_64.abi, X86_64.argRegs] at h
    exact ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩
  post _ _ _ h := h
  pub s₁ s₂ _ _ h := by
    sig_pub [Impl.Weierstrass.PointOps.Curve.addCachedContract, Impl.Weierstrass.PointOps.sig,
      X86_64.abi, X86_64.argRegs] at h
    exact ⟨⟨h.1, h.2.2⟩, h.2.1⟩
  sat := ⟨fnSat, by
    sig_pre [Impl.Weierstrass.PointOps.Curve.addCachedContract, Impl.Weierstrass.PointOps.sig,
      X86_64.abi, X86_64.argRegs]
    exact ⟨sat_ret, by decide, sat_mod, sat_p, sat_q, sat_c2, sat_c3⟩⟩

theorem doubleK_implies : doubleK.Implies (C.doubleContract X86_64.abi) where
  pre s h := by
    sig_pre [Impl.Weierstrass.PointOps.Curve.doubleContract, Impl.Weierstrass.PointOps.sig,
      X86_64.abi, X86_64.argRegs] at h
    exact ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩, h.2.2.2.2.1, h.2.2.2.2.2⟩
  post _ _ _ h := h
  pub s₁ s₂ _ _ h := by
    sig_pub [Impl.Weierstrass.PointOps.Curve.doubleContract, Impl.Weierstrass.PointOps.sig,
      X86_64.abi, X86_64.argRegs] at h
    exact ⟨h.1, h.2⟩
  sat := ⟨fnSat, by
    sig_pre [Impl.Weierstrass.PointOps.Curve.doubleContract, Impl.Weierstrass.PointOps.sig,
      X86_64.abi, X86_64.argRegs]
    exact ⟨sat_ret, by decide, sat_mod, sat_p⟩⟩

theorem addAffineK_implies : addAffineK.Implies (C.addAffineContract X86_64.abi) where
  pre s h := by
    sig_pre [Impl.Weierstrass.PointOps.Curve.addAffineContract, Impl.Weierstrass.PointOps.sig,
      X86_64.abi, X86_64.argRegs] at h
    exact ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  post _ _ _ h := h
  pub s₁ s₂ _ _ h := by
    sig_pub [Impl.Weierstrass.PointOps.Curve.addAffineContract, Impl.Weierstrass.PointOps.sig,
      X86_64.abi, X86_64.argRegs] at h
    exact ⟨⟨h.1, h.2.2⟩, h.2.1⟩
  sat := ⟨fnSat, by
    sig_pre [Impl.Weierstrass.PointOps.Curve.addAffineContract, Impl.Weierstrass.PointOps.sig,
      X86_64.abi, X86_64.argRegs]
    exact ⟨sat_ret, by decide, sat_mod, sat_p, sat_q⟩⟩

/-! ## `Verified` -/

/-- The functions' code passes `wrapOk` (checked on the literals). -/
theorem double_ok : wrapOk doubleFn = true := by
  rw [doubleLit.lit_eq]; decide +kernel

theorem addCached_ok : wrapOk addCachedFn = true := by
  rw [addCachedLit.lit_eq]; decide +kernel

theorem addAffine_ok : wrapOk addAffineFn = true := by
  rw [addAffineLit.lit_eq]; decide +kernel

theorem double_verified (hFe : Proof.Weierstrass.Point.Fermat C.p) :
    Verified X86_64.target doubleFn (C.doubleContract X86_64.abi) :=
  Verified.of_correct (double_correct hFe double_ok) double_ct doubleK_implies

theorem addCached_verified (hFe : Proof.Weierstrass.Point.Fermat C.p) :
    Verified X86_64.target addCachedFn (C.addCachedContract X86_64.abi) :=
  Verified.of_correct (addCached_correct hFe addCached_ok) addCached_ct addCachedK_implies

theorem addAffine_verified (hFe : Proof.Weierstrass.Point.Fermat C.p) :
    Verified X86_64.target addAffineFn (C.addAffineContract X86_64.abi) :=
  Verified.of_correct (addAffine_correct hFe addAffine_ok) addAffine_ct addAffineK_implies

end VG.Proof.Secp256k1.X86_64.PointOps
