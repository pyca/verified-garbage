module

import VerifiedGarbage.Proof.Ed25519.X86.Power
public import VerifiedGarbage.Proof.Ed25519.Recover
public import VerifiedGarbage.Proof.Ed25519.X86.RecoverSign
public import VerifiedGarbage.Proof.Ed25519.X86.PowerEnv
import VerifiedGarbage.Proof.Ed25519.X86.AccumulateStep
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! Merged from `Proof.Ed25519.X86.RecoverCandidate`. -/

@[expose] public section

section
/-! Candidate root and its squared check agree with the decoding specification. -/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

private theorem recoverInit_eval (e : Env) :
    evalOps recoverInitOps e 1 = e 1 ∧
    evalOps recoverInitOps e 6 = rootU (e 1) ∧
    evalOps recoverInitOps e 7 = rootV (e 1) ∧
    evalOps recoverInitOps e 9 = Spec.X25519.pow (rootV (e 1)) 3 ∧
    evalOps recoverInitOps e 2 = rootU (e 1) * Spec.X25519.pow (rootV (e 1)) 7 := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · exact pow_three _
  · exact congrArg (rootU (e 1) * ·) (pow_seven _)

private theorem recoverFinish_eval (e : Env) :
    evalOps recoverFinishOps e 0 = e 6 * e 9 * e 15 ∧
    evalOps recoverFinishOps e 1 = e 1 ∧
    evalOps recoverFinishOps e 5 = 0 ∧
    evalOps recoverFinishOps e 6 = e 6 ∧
    evalOps recoverFinishOps e 7 = e 7 ∧
    evalOps recoverFinishOps e 11 = e 7 * (e 6 * e 9 * e 15) * (e 6 * e 9 * e 15) ∧
    evalOps recoverFinishOps e 12 = 0 - e 6 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem recoverCandidate_ok {s : State} {base : BitVec 32} (hs : Ctx base s) :
    WP isa recoverCandidate s fun t => IKeep base s t ∧
      env t.mem base 0 = rootX (env s.mem base 1) ∧
      env t.mem base 1 = env s.mem base 1 ∧
      env t.mem base 5 = 0 ∧ env t.mem base 6 = rootU (env s.mem base 1) ∧
      env t.mem base 7 = rootV (env s.mem base 1) ∧
      env t.mem base 11 = rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) ∧
      env t.mem base 12 = 0 - rootU (env s.mem base 1) := by
  rw [recoverCandidate]
  refine WP.seq (WP.mono (fieldCode_ok recoverInitOps hs) fun a ⟨ka, va⟩ => ?_)
  refine WP.seq (WP.mono (rootPower_ok (ka.ctx hs)) fun b ⟨kb, vb, be⟩ => ?_)
  have kbr := kb
  refine WP.mono (fieldCode_ok recoverFinishOps (kbr.ctx (ka.ctx hs))) fun t ⟨kt, vt⟩ => ?_
  have ay := (recoverInit_eval (env s.mem base)).1
  have au := (recoverInit_eval (env s.mem base)).2.1
  have av := (recoverInit_eval (env s.mem base)).2.2.1
  have av3 := (recoverInit_eval (env s.mem base)).2.2.2.1
  have az := (recoverInit_eval (env s.mem base)).2.2.2.2
  have bx : env b.mem base 6 * env b.mem base 9 * env b.mem base 15 = rootX (env s.mem base 1) := by
    rw [be 6 (by decide), be 9 (by decide), vb, rootPower_eq, va, au, av3, az]
    rfl
  have kar : IKeep base s a := IKeep.of_field ka
  have ktr : IKeep base b t := IKeep.of_field kt
  refine ⟨kar.trans (kbr.trans ktr), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vt, (recoverFinish_eval _).1, bx]
  · rw [vt, (recoverFinish_eval _).2.1, be 1 (by decide), va, ay]
  · rw [vt, (recoverFinish_eval _).2.2.1]
  · rw [vt, (recoverFinish_eval _).2.2.2.1, be 6 (by decide), va, au]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.1, be 7 (by decide), va, av]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.2.1, bx, be 7 (by decide), va, av]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.2.2, be 6 (by decide), va, au]

end VG.Proof.Ed25519.X86
end

/-! Candidate validation implements RFC 8032's recoverX exactly. -/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

def recoverResult (y : Spec.X25519.Fe) (b : Bool) : Option Spec.Ed25519.Point :=
  if rootV y * rootX y * rootX y = rootU y then signResult (rootX y) y b
  else if rootV y * rootX y * rootX y = 0 - rootU y then signResult (rootX y * Spec.Ed25519.sqrtM1) y b
  else none

private theorem signResult_map (x y : Spec.X25519.Fe) (b : Bool) :
    signResult x y b = (do
      let z ← some x
      if z = 0 && b then none else some (signedX z b)).map (fun z => recoveredPoint z y) := by
  unfold signResult
  change (if x = 0 && b then none else some (recoveredPoint (signedX x b) y)) =
    (if x = 0 && b then none else some (signedX x b)).map (fun z => recoveredPoint z y)
  split <;> rfl

theorem recoverResult_spec (y : Spec.X25519.Fe) (b : Bool) :
    recoverResult y b = (Spec.Ed25519.recoverX y b).map (fun x => recoveredPoint x y) := by
  unfold recoverResult Spec.Ed25519.recoverX
  change (if rootV y * rootX y * rootX y = rootU y then signResult (rootX y) y b
    else if rootV y * rootX y * rootX y = 0 - rootU y then signResult (rootX y * Spec.Ed25519.sqrtM1) y b else none) =
    (if rootV y * rootX y * rootX y = rootU y then (do
        let z ← some (rootX y)
        if z = 0 && b then none else some (signedX z b))
      else if rootV y * rootX y * rootX y = 0 - rootU y then (do
        let z ← some (rootX y * Spec.Ed25519.sqrtM1)
        if z = 0 && b then none else some (signedX z b))
      else none).map (fun x => recoveredPoint x y)
  by_cases h : rootV y * rootX y * rootX y = rootU y
  · rw [ite_eq_left h, ite_eq_left h]
    exact signResult_map _ _ _
  · rw [ite_eq_right h, ite_eq_right h]
    by_cases h' : rootV y * rootX y * rootX y = 0 - rootU y
    · rw [ite_eq_left h', ite_eq_left h']
      exact signResult_map _ _ _
    · rw [ite_eq_right h', ite_eq_right h']
      rfl


private theorem sign_known {s : State} {base : BitVec 32} (hs : Ctx base s)
    (b : Bool) (hb : s.gpr .esi = signWord b) (x y : Spec.X25519.Fe)
    (hx : env s.mem base 0 = x) (hy : env s.mem base 1 = y) :
    WP isa recoverSign s fun t => FieldKeep base s t ∧ DecodeResult base (signResult x y b) t := by
  refine WP.mono (recoverSign_ok hs b hb) fun t ⟨kt, tr⟩ => ?_
  exact ⟨kt, by rw [hx, hy] at tr; exact tr⟩

/-- The root `recoverRoot` leaves in slot 0, if there is one. -/
def rootSel (y : Spec.X25519.Fe) : Option Spec.X25519.Fe :=
  if rootV y * rootX y * rootX y = rootU y then some (rootX y)
  else if rootV y * rootX y * rootX y = 0 - rootU y then some (rootX y * Spec.Ed25519.sqrtM1) else none

theorem recoverResult_sel (y : Spec.X25519.Fe) (b : Bool) :
    recoverResult y b = (rootSel y).bind fun x => signResult x y b := by
  unfold recoverResult rootSel
  by_cases h : rootV y * rootX y * rootX y = rootU y
  · rw [ite_eq_left h, ite_eq_left h, Option.bind_some]
  · rw [ite_eq_right h, ite_eq_right h]
    by_cases h' : rootV y * rootX y * rootX y = 0 - rootU y
    · rw [ite_eq_left h', ite_eq_left h', Option.bind_some]
    · rw [ite_eq_right h', ite_eq_right h', Option.bind_none]

theorem recoverRoot_ok {s : State} {base : BitVec 32} (hs : Ctx base s) (y : Spec.X25519.Fe)
    (hx : env s.mem base 0 = rootX y)
    (hu : env s.mem base 6 = rootU y)
    (hvx : env s.mem base 11 = rootV y * rootX y * rootX y)
    (hnu : env s.mem base 12 = 0 - rootU y) :
    WP isa recoverRoot s fun t => FieldKeep base s t ∧ env t.mem base 1 = env s.mem base 1 ∧
      t.gpr .eax = signWord (rootSel y).isSome ∧ ∀ x, rootSel y = some x → env t.mem base 0 = x := by
  refine WP.seq (WP.mono (fieldEqual_ok hs 11 6) fun c ⟨kc, ce, cz⟩ => ?_)
  have cx : env c.mem base 0 = rootX y := (ce 0 (by decide)).trans hx
  have cy : env c.mem base 1 = env s.mem base 1 := ce 1 (by decide)
  apply WP.ite (decide (rootV y * rootX y * rootX y = rootU y)) (by rw [← hvx, ← hu]; exact cz)
  · intro ht
    have hsel : rootSel y = some (rootX y) := by rw [rootSel, ite_eq_left (of_decide_eq_true ht)]
    refine WP.mono (returnFlag_ok c base true) fun t ⟨kt, mt, rt⟩ =>
      ⟨kc.trans kt, by rw [mt]; exact cy, by rw [rt, hsel, Option.isSome_some], fun x hx' => ?_⟩
    rw [hsel] at hx'
    rw [← Option.some.inj hx', mt]; exact cx
  · intro hf
    have hf' := of_decide_eq_false hf
    refine WP.seq (WP.mono (fieldEqual_ok (kc.ctx hs) 11 12) fun d ⟨kd, de, dz⟩ => ?_)
    have kcd := kc.trans kd
    have dx : env d.mem base 0 = rootX y := (de 0 (by decide)).trans cx
    have dy : env d.mem base 1 = env s.mem base 1 := (de 1 (by decide)).trans cy
    apply WP.ite (decide (rootV y * rootX y * rootX y = 0 - rootU y))
      (by rw [ce 11 (by decide), ce 12 (by decide), hvx, hnu] at dz; exact dz)
    · intro ht
      have hsel : rootSel y = some (rootX y * Spec.Ed25519.sqrtM1) := by
        rw [rootSel, ite_eq_right hf', ite_eq_left (of_decide_eq_true ht)]
      rw [WP.block_append_iff]
      refine WP.mono (fieldCode_ok [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18] (kcd.ctx hs))
        fun e ⟨ke, ve⟩ => ?_
      have ex : env e.mem base 0 = rootX y * Spec.Ed25519.sqrtM1 := by
        rw [ve]; change env d.mem base 0 * Spec.Ed25519.sqrtM1 = _; rw [dx]
      have ey : env e.mem base 1 = env s.mem base 1 := by rw [ve]; exact dy
      refine WP.mono (returnFlag_ok e base true) fun t ⟨kt, mt, rt⟩ =>
        ⟨(kcd.trans ke).trans kt, by rw [mt]; exact ey, by rw [rt, hsel, Option.isSome_some], fun x hx' => ?_⟩
      rw [hsel] at hx'
      rw [← Option.some.inj hx', mt]; exact ex
    · intro hf2
      have hsel : rootSel y = none := by
        rw [rootSel, ite_eq_right hf', ite_eq_right (of_decide_eq_false hf2)]
      refine WP.mono (returnFlag_ok d base false) fun t ⟨kt, mt, rt⟩ =>
        ⟨kcd.trans kt, by rw [mt]; exact dy, by rw [rt, hsel, Option.isSome_none], fun x hx' => ?_⟩
      rw [hsel] at hx'; cases hx'

theorem recoverChecks_ok {s : State} {base : BitVec 32} (hs : Ctx base s)
    (b : Bool) (hb : s.gpr .esi = signWord b) (y : Spec.X25519.Fe)
    (hx : env s.mem base 0 = rootX y) (hy : env s.mem base 1 = y)
    (hu : env s.mem base 6 = rootU y)
    (hvx : env s.mem base 11 = rootV y * rootX y * rootX y)
    (hnu : env s.mem base 12 = 0 - rootU y) :
    WP isa recoverChecks s fun t => FieldKeep base s t ∧ DecodeResult base (recoverResult y b) t := by
  refine WP.seq (WP.mono (recoverRoot_ok hs y hx hu hvx hnu) fun a ⟨ka, ay, ra, xa⟩ => ?_)
  refine WP.seq (WP.mono (flagTest_ok base _ ra) fun c ⟨kc, mc, zc⟩ => ?_)
  have kac := ka.trans kc
  rw [recoverResult_sel]
  apply WP.ite _ zc
  · intro ht
    obtain ⟨x, hxs⟩ := Option.isSome_iff_exists.mp ht
    refine WP.mono (sign_known (kac.ctx hs) b (kac.keep.esi.trans hb) x y (by rw [mc]; exact xa x hxs)
      (by rw [mc, ay]; exact hy)) fun t ⟨kt, tr⟩ => ⟨kac.trans kt, ?_⟩
    rw [hxs, Option.bind_some]; exact tr
  · intro hf
    have hn : rootSel y = none := by
      cases h : rootSel y with
      | none => rfl
      | some _ => rw [h] at hf; cases hf
    refine WP.mono (recoverInvalid_ok c base) fun t ⟨kt, tr⟩ => ⟨kac.trans kt, ?_⟩
    rw [hn, Option.bind_none]; exact tr

theorem recoverPoint_ok {s : State} {base : BitVec 32} (hs : Ctx base s)
    (b : Bool) (hb : wd s.mem base 32 = signWord b) :
    WP isa recoverPoint s fun t => IKeep base s t ∧
      DecodeResult base ((Spec.Ed25519.recoverX (env s.mem base 1) b).map
        (fun x => recoveredPoint x (env s.mem base 1))) t := by
  rw [← recoverResult_spec]
  refine WP.seq (WP.mono (recoverCandidate_ok hs) fun a ⟨ka, ax, ay, _, au, _, avx, anu⟩ => ?_)
  have ca := ka.ctx hs
  refine WP.seq (Wp.wp_ldm ca.edi (ca.inRW (by decide) (by decide)) fun c hc => WP.block_nil ?_)
  have kc : IKeep base a c := IKeep.of_counter hc
  have cb : c.gpr .esi = signWord b := by
    rw [hc.gpr]
    change wd a.mem base 32 = _
    rw [IKeep.word ka hs 32 (by decide), hb]
  refine WP.mono (recoverChecks_ok (kc.ctx ca) b cb (env s.mem base 1)
    (by rw [hc.mem]; exact ax) (by rw [hc.mem]; exact ay) (by rw [hc.mem]; exact au)
    (by rw [hc.mem]; exact avx) (by rw [hc.mem]; exact anu)) fun t ⟨kt, tr⟩ => ?_
  exact ⟨(ka.trans kc).trans (IKeep.of_field kt), tr⟩

end VG.Proof.Ed25519.X86
