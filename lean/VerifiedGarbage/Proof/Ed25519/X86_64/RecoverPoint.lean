import VerifiedGarbage.Proof.Ed25519.X86_64.PointAffine
import VerifiedGarbage.Impl.Ed25519.X86_64.Recover
import VerifiedGarbage.Proof.Ed25519.Recover
import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverSign

/-! Candidate root and its squared check agree with the decoding specification. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

/-- The square root's power of `y`'s decoding: `(u v⁷)^((p - 5) / 8)`. -/
def rootPow (y : Spec.X25519.Fe) : Spec.X25519.Fe :=
  Spec.X25519.pow (rootU y * Spec.X25519.pow (rootV y) 7) ((Spec.X25519.P - 5) / 8)

private theorem recoverPrep_eval (e : Env) :
    evalOps recoverPrepOps e 1 = e 1 ∧
    evalOps recoverPrepOps e 6 = rootU (e 1) ∧
    evalOps recoverPrepOps e 7 = rootV (e 1) ∧
    evalOps recoverPrepOps e 9 = Spec.X25519.pow (rootV (e 1)) 3 ∧
    evalOps recoverPrepOps e 15 = e 15 := by
  refine ⟨rfl, rfl, rfl, ?_, rfl⟩
  exact pow_three _

private theorem recoverFinish_eval (e : Env) :
    evalOps recoverFinishOps e 0 = e 6 * e 9 * e 15 ∧
    evalOps recoverFinishOps e 1 = e 1 ∧
    evalOps recoverFinishOps e 5 = 0 ∧
    evalOps recoverFinishOps e 6 = e 6 ∧
    evalOps recoverFinishOps e 7 = e 7 ∧
    evalOps recoverFinishOps e 11 = e 7 * (e 6 * e 9 * e 15) * (e 6 * e 9 * e 15) ∧
    evalOps recoverFinishOps e 12 = 0 - e 6 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The candidate, from the power in slot 15 (`hp`). -/
theorem recoverCandidate_ok {s : State} {base : Addr} (hs : Scratch s base)
    (hp : env s.mem base 15 = rootPow (env s.mem base 1)) :
    WP isa (recoverCandidate fld) s fun t => RbxKeep base s t ∧
      env t.mem base 0 = rootX (env s.mem base 1) ∧
      env t.mem base 1 = env s.mem base 1 ∧
      env t.mem base 5 = 0 ∧ env t.mem base 6 = rootU (env s.mem base 1) ∧
      env t.mem base 7 = rootV (env s.mem base 1) ∧
      env t.mem base 11 = rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) ∧
      env t.mem base 12 = 0 - rootU (env s.mem base 1) := by
  rw [recoverCandidate]
  refine WP.mono (fieldCodeWide_ok hs (recoverPrepOps ++ recoverFinishOps)) fun t ⟨kt, vt⟩ => ?_
  have ve : env t.mem base = evalOps recoverFinishOps (evalOps recoverPrepOps (env s.mem base)) := by
    rw [vt, evalOps, List.foldl_append]; rfl
  obtain ⟨ay, au, av, av3, ap⟩ := recoverPrep_eval (env s.mem base)
  have bx : evalOps recoverPrepOps (env s.mem base) 6 * evalOps recoverPrepOps (env s.mem base) 9 *
      evalOps recoverPrepOps (env s.mem base) 15 = rootX (env s.mem base 1) := by
    rw [au, av3, ap, hp]
    rfl
  refine ⟨RbxKeep.of_keep kt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ve, (recoverFinish_eval _).1, bx]
  · rw [ve, (recoverFinish_eval _).2.1, ay]
  · rw [ve, (recoverFinish_eval _).2.2.1]
  · rw [ve, (recoverFinish_eval _).2.2.2.1, au]
  · rw [ve, (recoverFinish_eval _).2.2.2.2.1, av]
  · rw [ve, (recoverFinish_eval _).2.2.2.2.2.1, bx, av]
  · rw [ve, (recoverFinish_eval _).2.2.2.2.2.2, au]

end VG.Proof.Ed25519.X86_64

/-! Candidate validation implements RFC 8032's recoverX exactly. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

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


private theorem sign_known {s : State} {base : Addr} (hs : Scratch s base)
    (b : Bool) (hb : s.gpr .rsi = signWord b) (x y : Spec.X25519.Fe)
    (hx : env s.mem base 0 = x) (hy : env s.mem base 1 = y) :
    WP isa (recoverSign fld) s fun t => RbxKeep base s t ∧ DecodeResult base (signResult x y b) t := by
  refine WP.mono (recoverSign_ok hs b hb) fun t ⟨kt, tr⟩ => ?_
  exact ⟨RbxKeep.of_keep kt, by rw [hx, hy] at tr; exact tr⟩

theorem recoverPoint_ok {s : State} {base : Addr} (hs : Scratch s base)
    (b : Bool) (hb : s.gpr .rsi = signWord b) (hp : env s.mem base 15 = rootPow (env s.mem base 1)) :
    WP isa (recoverPoint fld) s fun t => RbxKeep base s t ∧
      DecodeResult base ((Spec.Ed25519.recoverX (env s.mem base 1) b).map
        (fun x => recoveredPoint x (env s.mem base 1))) t := by
  rw [← recoverResult_spec, recoverPoint]
  refine WP.seq (WP.mono (recoverCandidate_ok hs hp) fun a ⟨ka, ax, ay, _, au, _, avx, anu⟩ => ?_)
  refine WP.seq (WP.mono (fieldEqual_ok (ka.scratch hs) 11 6) fun c ⟨cz, kc, ce⟩ => ?_)
  have kac := ka.trans (RbxKeep.of_keep kc)
  have cx : env c.mem base 0 = rootX (env s.mem base 1) := (ce 0 (by decide)).trans ax
  have cy : env c.mem base 1 = env s.mem base 1 := (ce 1 (by decide)).trans ay
  apply WP.ite (decide (rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) =
    rootU (env s.mem base 1))) (by change c.zf = _; rw [cz, avx, au])
  · intro ht
    have ht' := of_decide_eq_true ht
    refine WP.mono (sign_known (kac.scratch hs) b ((kac.gpr _ (by decide) (by decide)).trans hb)
      _ _ cx cy) fun t ⟨kt, tr⟩ => ?_
    exact ⟨kac.trans kt, by simpa only [recoverResult, ht', ite_true] using tr⟩
  · intro hf
    have hf' := of_decide_eq_false hf
    refine WP.seq (WP.mono (fieldEqual_ok (kac.scratch hs) 11 12) fun d ⟨dz, kd, de⟩ => ?_)
    have kacd := kac.trans (RbxKeep.of_keep kd)
    have dx : env d.mem base 0 = rootX (env s.mem base 1) := (de 0 (by decide)).trans cx
    have dy : env d.mem base 1 = env s.mem base 1 := (de 1 (by decide)).trans cy
    apply WP.ite (decide (rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) =
      0 - rootU (env s.mem base 1))) (by change d.zf = _; rw [dz, ce 11 (by decide), ce 12 (by decide), avx, anu])
    · intro ht
      have ht' := of_decide_eq_true ht
      refine WP.seq (WP.mono (fieldCodeWide_ok (kacd.scratch hs) [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])
        fun e ⟨ke, ve⟩ => ?_)
      have ex : env e.mem base 0 = rootX (env s.mem base 1) * Spec.Ed25519.sqrtM1 := by
        rw [ve]; change env d.mem base 0 * Spec.Ed25519.sqrtM1 = _; rw [dx]
      have ey : env e.mem base 1 = env s.mem base 1 := by rw [ve]; exact dy
      have kacde := kacd.trans (RbxKeep.of_keep ke)
      refine WP.mono (sign_known (kacde.scratch hs) b ((kacde.gpr _ (by decide) (by decide)).trans hb)
        _ _ ex ey) fun t ⟨kt, tr⟩ => ?_
      exact ⟨kacde.trans kt, by rw [recoverResult, ite_eq_right hf', ite_eq_left ht']; exact tr⟩
    · intro hf2
      have hf2' := of_decide_eq_false hf2
      refine WP.mono (recoverInvalid_ok d base) fun t ⟨kt, tr⟩ => ?_
      exact ⟨kacd.trans (RbxKeep.of_keep kt), by simpa only [recoverResult, hf', hf2', ite_false] using tr⟩

end VG.Proof.Ed25519.X86_64
