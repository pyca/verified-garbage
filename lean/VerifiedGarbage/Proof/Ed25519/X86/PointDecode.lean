module

public import VerifiedGarbage.Impl.Ed25519.X86.PointDecode
import VerifiedGarbage.Proof.Ed25519.X86.FreezeField
public import VerifiedGarbage.Proof.Ed25519.X86.PointMultiplyFrame
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBody
import VerifiedGarbage.Proof.X25519.X86.Freeze
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Ed25519.Recover
public import VerifiedGarbage.Proof.Ed25519.X86.PowerEnv
public import VerifiedGarbage.Proof.Ed25519.X86.RecoverParity
import VerifiedGarbage.Proof.Ed25519.X86.PrepareAdd

/-! ### `Ed25519.X86.RecoverPoint`, which this module and modules that import it used -/

section

/-! ### `Ed25519.X86.RecoverSign`, which this module and modules that import it used -/

section

/-! Merged from `Proof.Ed25519.X86.RecoverAdjust`. -/

@[expose] public section

section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def recoveredPoint (x y : Spec.X25519.Fe) : Spec.Ed25519.Point := ⟨x, y, 1, x * y⟩
def signedX (x : Spec.X25519.Fe) (b : Bool) : Spec.X25519.Fe :=
  if (x.val % 2 == 1) == b then x else 0 - x

theorem recoverSuccess_ok {s : State} {x : BitVec 32} (hc : Ctx x s) :
    WP isa (.block recoverSuccess) s fun t => FieldKeep x s t ∧ t.gpr .eax = 1 ∧
      point (env t.mem x) 0 1 2 3 = recoveredPoint (env s.mem x 0) (env s.mem x 1) := by
  rw [recoverSuccess, WP.block_append_iff]
  refine WP.mono (fieldCode_ok recoverSuccessOps hc) fun a ⟨ka, ea⟩ => ?_
  refine WP.mono (returnFlag_ok a x true) fun t ⟨kt, mt, rt⟩ => ?_
  exact ⟨ka.trans kt, rt, by rw [mt, ea]; rfl⟩

private theorem adjustBranch_ok {s : State} {x : BitVec 32} (hc : Ctx x s) (b : Bool)
    (hz : s.zf = some (((env s.mem x 0).val % 2 == 1) == b)) :
    WP isa (.ite .e (.block []) (.block (fieldCode [.const 5 0, .sub 0 5 0]))) s fun t =>
      FieldKeep x s t ∧ env t.mem x 0 = signedX (env s.mem x 0) b ∧ env t.mem x 1 = env s.mem x 1 := by
  apply WP.ite (((env s.mem x 0).val % 2 == 1) == b) hz
  · intro h
    exact WP.block_nil ⟨FieldKeep.refl _ _, by simp only [signedX, h, ite_true], rfl⟩
  · intro h
    refine WP.mono (fieldCode_ok [.const 5 0, .sub 0 5 0] hc) fun t ⟨kt, et⟩ => ?_
    refine ⟨kt, ?_, ?_⟩
    · rw [et]
      change 0 - env s.mem x 0 = signedX (env s.mem x 0) b
      simp only [signedX, h, Bool.false_eq_true, ite_false]
    · rw [et]; rfl

theorem recoverAdjustSign_ok {s : State} {x : BitVec 32} (hc : Ctx x s)
    (b : Bool) (hb : s.gpr .esi = signWord b) :
    WP isa recoverAdjustSign s fun t => FieldKeep x s t ∧ t.gpr .eax = 1 ∧
      point (env t.mem x) 0 1 2 3 = recoveredPoint (signedX (env s.mem x 0) b) (env s.mem x 1) := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (freezeField_ok hc 0) fun a ⟨ka, ea, va⟩ => ?_
  refine WP.mono (recoverParity_ok (ka.ctx hc) b (ka.keep.esi.trans hb)) fun c ⟨kc, mc, zc⟩ => ?_
  have ec : env c.mem x = env s.mem x := by rw [mc, ea]
  have zc' : c.zf = some (((env c.mem x 0).val % 2 == 1) == b) := by
    change fe a.mem x 64 = _ at va
    rw [zc, va, ec]
  refine WP.seq (WP.mono (adjustBranch_ok ((ka.trans kc).ctx hc) b zc') fun d ⟨kd, dx, dy⟩ => ?_)
  refine WP.mono (recoverSuccess_ok (((ka.trans kc).trans kd).ctx hc)) fun t ⟨kt, rt, pt⟩ => ?_
  exact ⟨((ka.trans kc).trans kd).trans kt, rt, by rw [pt, dx, dy, ec]⟩

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def DecodeResult (x : BitVec 32) (p : Option Spec.Ed25519.Point) (s : State) : Prop :=
  match p with
  | none => s.gpr .eax = 0
  | some p => s.gpr .eax = 1 ∧ point (env s.mem x) 0 1 2 3 = p

def signResult (x y : Spec.X25519.Fe) (b : Bool) : Option Spec.Ed25519.Point :=
  if x = 0 && b then none else some (recoveredPoint (signedX x b) y)

theorem recoverInvalid_ok (s : State) (x : BitVec 32) :
    WP isa recoverInvalid s fun t => FieldKeep x s t ∧ DecodeResult x none t :=
  WP.mono (returnFlag_ok s x false) fun _ ⟨kt, _, rt⟩ => ⟨kt, rt⟩

/-- `test eax, eax` of a flag `c`. -/
theorem flagTest_ok {s : State} (x : BitVec 32) (c : Bool) (hc : s.gpr .eax = signWord c) :
    WP isa (.block [.alu .test .eax (.reg .eax)]) s fun t => FieldKeep x s t ∧ t.mem = s.mem ∧
      isa.eval .ne t = some c := by
  refine Wp.wp_test fun t ht zt => WP.block_nil ?_
  refine ⟨FieldKeep.of_mem ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩ ht.mem, ht.mem, ?_⟩
  show t.zf.map (!·) = _
  rw [zt, BitVec.and_self, hc]
  cases c <;> rfl

theorem recoverZero_ok {s : State} {x : BitVec 32} (hc : Ctx x s)
    (b : Bool) (hb : s.gpr .esi = signWord b) :
    WP isa recoverZero s fun t => FieldKeep x s t ∧ env t.mem x = env s.mem x ∧
      t.gpr .eax = signWord (decide (env s.mem x 0 = 0) && b) := by
  refine WP.seq (WP.mono (fieldZero_ok hc 0) fun a ⟨ka, ea, za⟩ => ?_)
  apply WP.ite (decide (env s.mem x 0 = 0)) za
  · intro hz
    refine Wp.wp_mov fun t ht => WP.block_nil ⟨ka.trans (FieldKeep.of_mem (updKeep ht) ht.mem),
      by rw [ht.mem, ea], ?_⟩
    rw [ht.gpr, ka.keep.esi, hb, hz, Bool.true_and]
  · intro hn
    refine WP.mono (returnFlag_ok a x false) fun t ⟨kt, mt, rt⟩ => ⟨ka.trans kt, by rw [mt, ea], ?_⟩
    rw [rt, hn, Bool.false_and]

theorem recoverSign_ok {s : State} {x : BitVec 32} (hc : Ctx x s)
    (b : Bool) (hb : s.gpr .esi = signWord b) :
    WP isa recoverSign s fun t => FieldKeep x s t ∧
      DecodeResult x (signResult (env s.mem x 0) (env s.mem x 1) b) t := by
  refine WP.seq (WP.mono (recoverZero_ok hc b hb) fun a ⟨ka, ea, ra⟩ => ?_)
  refine WP.seq (WP.mono (flagTest_ok x _ ra) fun c ⟨kc, mc, zc⟩ => ?_)
  have kac := ka.trans kc
  have ec : env c.mem x = env s.mem x := by rw [mc, ea]
  apply WP.ite _ zc
  · intro ht
    refine WP.mono (recoverInvalid_ok c x) fun t ⟨kt, tr⟩ => ⟨kac.trans kt, ?_⟩
    simpa only [signResult, ht, ite_true] using tr
  · intro hf
    refine WP.mono (recoverAdjustSign_ok (kac.ctx hc) b (kac.keep.esi.trans hb)) fun t ⟨kt, rt, pt⟩ => ?_
    refine ⟨kac.trans kt, ?_⟩
    simp only [signResult, hf, Bool.false_eq_true, ite_false, DecodeResult]
    exact ⟨rt, by rw [ec] at pt; exact pt⟩

end VG.Proof.Ed25519.X86

end

end

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

end

end

/-! Merged from `Proof.Ed25519.X86.DecodeY`. -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.X86.CanonicalY`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem canonicalY_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (hy : fe s.mem x 96 < 2 ^ 255) :
    WP isa (.block canonicalY) s fun t => FieldKeep x s t ∧
      env t.mem x = env s.mem x ∧ wd t.mem x 32 = wd s.mem x 32 ∧
      t.zf = some (decide (fe s.mem x 96 < Spec.X25519.P)) := by
  rw [canonicalY, List.append_assoc, WP.block_append_iff]
  refine WP.mono (setAcc_ok (s := s) 19) fun a ⟨ka, ma, aa⟩ => ?_
  rw [WP.block_append_iff]
  have ca := ka.ctx hc
  refine WP.mono (cols_ok ca (fun k => [.addM (96 + 4 * k)]) 8 (by decide)
    (fun k hk t ht d hd => ?_) (fun k _ => ?_) (by rw [aa]; decide)) fun b ⟨kb, fb, vb, _⟩ => ?_
  · simp only [List.mem_singleton] at ht; subst ht
    simp only [treads, List.mem_singleton] at hd; subst hd
    exact ⟨by omega_using [hk], .inl (by simp only [T]; omega_using [hk])⟩
  · rw [colv_addM]; have := wv_lt a.mem x (96 + 4 * k); omega_using [this]
  have nn : num (fun k => colv a.mem x [.addM (96 + 4 * k)]) 8 = fe s.mem x 96 := by
    rw [ma]; exact num_congr fun k _ => colv_addM _ _ _
  rw [nn, aa, show (19 : BitVec 32).toNat = 19 from rfl] at vb
  have vsum : fe b.mem x T = fe s.mem x 96 + 19 := by
    change fe b.mem x T + (2 ^ 32) ^ 8 * acc b = _ at vb
    have hb : acc b = 0 := by
      rcases Nat.eq_zero_or_pos (acc b) with h | h
      · exact h
      · have hh := Nat.mul_le_mul_left ((2 ^ 32) ^ 8) h
        omega_using [hy, vb, hh]
    rw [hb, Nat.mul_zero, Nat.add_zero] at vb
    omega_using [vb]
  have cb := kb.ctx ca
  refine Wp.wp_ldm cb.edi (cb.inRW (by decide) (by decide)) fun c hcl => ?_
  refine Wp.wp_shr (by decide) fun d hd _ => Wp.wp_test fun t ht zt => WP.block_nil ?_
  have kt : Keep b t := (updKeep hcl).trans ((updKeep hd).trans
    ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩)
  have mt : t.mem = b.mem := by rw [ht.mem, hd.mem, hcl.mem]
  have ff : Frame [sub x T 32] s.mem t.mem := by rw [mt]; rw [ma] at fb; exact fb
  have envt : env t.mem x = env s.mem x := by
    funext i
    apply congrArg VG.Proof.X25519.toFe
    have ii := i.isLt
    exact fe_frame1 ff hc.fit (by decide) (by simp only [offset]; omega_using [ii])
      (Or.inl (by simp only [offset, T]; omega_using [ii]))
  refine ⟨⟨ka.trans (kb.trans kt), frameWiden ff hc.fit (by decide) (by decide) (by decide)⟩,
    envt, wd_frame1 ff hc.fit (by decide) (by decide) (Or.inl (by decide)), ?_⟩
  have top := (fold_top (f := fun k => wv b.mem x (T + 4 * k)) fun _ _ => wv_lt _ _ _).2
  change fe b.mem x T / 2 ^ 255 = wv b.mem x (T + 28) / 2 ^ 31 at top
  rw [vsum] at top
  have flag : (d.gpr .eax).toNat = (fe s.mem x 96 + 19) / 2 ^ 255 := by
    rw [hd.gpr, shr31_toNat, hcl.gpr]
    exact top.symm
  rw [zt, BitVec.and_self]
  apply congrArg some
  apply Bool.eq_iff_iff.mpr
  change (d.gpr .eax == 0) = true ↔ decide (fe s.mem x 96 < Spec.X25519.P) = true
  rw [beq_iff_eq, decide_eq_true_eq]
  have hz : d.gpr .eax = 0 ↔ (d.gpr .eax).toNat = 0 :=
    ⟨fun h => congrArg BitVec.toNat h, fun h => BitVec.eq_of_toNat_eq h⟩
  rw [hz, flag]
  simp only [Spec.X25519.P]
  omega_using [hy]

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem decodeY_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa (.block decodeY) s fun t => MulKeep x s t ∧
      fe t.mem x 96 = fe s.mem x 96 % 2 ^ 255 ∧
      wd t.mem x 32 = BitVec.ofNat 32 (fe s.mem x 96 / 2 ^ 255) := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun a ha => ?_
  refine Wp.wp_shr (by decide) fun b hb _ => ?_
  have kb : IKeep x s b := (IKeep.of_counter ha).trans (IKeep.of_counter hb)
  have cb := kb.ctx hc
  refine Wp.wp_stm cb.edi (cb.inW (by decide) (by decide)) fun c hcw => ?_
  have kc : ScalarKeep s c := ⟨by rw [hcw.gpr, kb.edi], by rw [hcw.gpr, kb.esp], hcw.rd.trans kb.rd, hcw.wr.trans kb.wr⟩
  have cc := kc.ctx hc
  have mc : c.mem = s.mem.writeW (addr x 32) (b.gpr .esi) := by rw [hcw.mem, hb.mem, ha.mem]
  have fc : Frame [sub x 32 4] s.mem c.mem := by
    rw [mc]; exact frame_write1 (Frame.refl _ _) hc.fit (by decide) (by decide) (by decide) _
  refine Wp.wp_ldm cc.edi (cc.inRW (by decide) (by decide)) fun d hd => ?_
  refine Wp.wp_andi fun e he => ?_
  have ce := ((updKeep hd).trans (updKeep he)).ctx cc
  refine Wp.wp_stm ce.edi (ce.inW (by decide) (by decide)) fun t ht => WP.block_nil ?_
  have kt : Keep c t := ((updKeep hd).trans (updKeep he)).trans
    ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩
  have mt : t.mem = c.mem.writeW (addr x 124) (e.gpr .eax) := by rw [ht.mem, he.mem, hd.mem]
  have ft : Frame [sub x 124 4] c.mem t.mem := by
    rw [mt]; exact frame_write1 (Frame.refl _ _) hc.fit (by decide) (by decide) (by decide) _
  have top : wd c.mem x 124 = wd s.mem x 124 := wd_frame1 fc hc.fit (by decide) (by decide) (Or.inr (by decide))
  have ev : (e.gpr .eax).toNat = wv s.mem x 124 % 2 ^ 31 := by
    rw [he.gpr, hd.gpr, low31_toNat]
    change wv c.mem x 124 % 2 ^ 31 = _
    rw [wv, top]
  have sv : b.gpr .esi = BitVec.ofNat 32 (fe s.mem x 96 / 2 ^ 255) := by
    apply BitVec.eq_of_toNat_eq
    rw [hb.gpr, shr31_toNat, ha.gpr, BitVec.toNat_ofNat]
    have hh := (fold_top (f := fun k => wv s.mem x (96 + 4 * k)) fun _ _ => wv_lt _ _ _).2
    change fe s.mem x 96 / 2 ^ 255 = wv s.mem x 124 / 2 ^ 31 at hh
    rw [hh]
    exact (Nat.mod_eq_of_lt (by have hw := wv_lt s.mem x 124; omega_using [hw])).symm
  refine ⟨⟨kt.edi.trans kc.edi, kt.esp.trans kc.esp, kt.rd.trans kc.rd, kt.wr.trans kc.wr,
    Frame.withStk (s := s) ((frameWiden (n' := 7144) fc hc.fit (by decide) (by decide) (by decide)).trans
      (frameWiden (n' := 7144) ft hc.fit (by decide) (by decide) (by decide)))⟩, ?_, ?_⟩
  · rw [mt, fe_last_write _ _ hc.fit, ev]
    have nl : num (fun j => wv c.mem x (96 + 4 * j)) 7 = num (fun j => wv s.mem x (96 + 4 * j)) 7 :=
      num_congr fun j hj => congrArg BitVec.toNat
        (wd_frame1 fc hc.fit (by decide) (by omega_using [hj]) (Or.inr (by omega_using [hj])))
    rw [nl]
    exact (fold_top (f := fun k => wv s.mem x (96 + 4 * k)) fun _ _ => wv_lt _ _ _).1.symm
  · rw [wd_frame1 ft hc.fit (by decide) (by decide) (Or.inl (by decide)), mc, wd_write_self, sv]

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def decodeNumber (n : Nat) : Option Spec.Ed25519.Point :=
  if h : n % 2 ^ 255 < Spec.X25519.P then
    (Spec.Ed25519.recoverX ⟨n % 2 ^ 255, h⟩ (n / 2 ^ 255 == 1)).map
      (fun x => recoveredPoint x ⟨n % 2 ^ 255, h⟩)
  else none

theorem pointDecode_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa pointDecode s fun t => MulKeep x s t ∧ DecodeResult x (decodeNumber (fe s.mem x 96)) t := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (decodeY_ok hc) fun a ⟨ka, ya, ba⟩ => ?_
  have ca := ka.ctx hc
  refine WP.mono (canonicalY_ok ca (by rw [ya]; exact Nat.mod_lt _ (by decide))) fun b ⟨kb, eb, bb, zb⟩ => ?_
  have km := ka.trans (MulKeep.of_ikeep ca (IKeep.of_field kb))
  apply WP.ite (decide (fe s.mem x 96 % 2 ^ 255 < Spec.X25519.P)) (by rw [ya] at zb; exact zb)
  · intro hh
    have hh' := of_decide_eq_true hh
    have ey : env b.mem x 1 = (⟨fe s.mem x 96 % 2 ^ 255, hh'⟩ : Spec.X25519.Fe) := by
      rw [eb]
      change VG.Proof.X25519.toFe (fe a.mem x 96) = _
      rw [ya]
      apply Fin.ext
      exact Nat.mod_eq_of_lt hh'
    have ebits : wd b.mem x 32 = signWord (fe s.mem x 96 / 2 ^ 255 == 1) := by
      rw [bb, ba]
      have hn : fe s.mem x 96 / 2 ^ 255 ≤ 1 := by have := fe_lt s.mem x 96; omega_using [this]
      rcases (by omega_using [hn] : fe s.mem x 96 / 2 ^ 255 = 0 ∨ fe s.mem x 96 / 2 ^ 255 = 1) with h | h <;>
        rw [h] <;> rfl
    refine WP.mono (recoverPoint_ok (km.ctx hc) _ ebits) fun t ⟨kt, tr⟩ => ?_
    refine ⟨km.trans (MulKeep.of_ikeep (km.ctx hc) kt), ?_⟩
    rw [ey] at tr
    simpa only [decodeNumber, dite_eq_left hh'] using tr
  · intro hh
    have hh' := of_decide_eq_false hh
    refine WP.mono (recoverInvalid_ok b x) fun t ⟨kt, tr⟩ => ?_
    exact ⟨km.trans (MulKeep.of_ikeep (km.ctx hc) (IKeep.of_field kt)), by
      simpa only [decodeNumber, dite_eq_right hh'] using tr⟩

end VG.Proof.Ed25519.X86
