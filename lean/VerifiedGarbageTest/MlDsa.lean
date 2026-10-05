import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import Lean.Data.Json
import VerifiedGarbageTest.Sha256
import VerifiedGarbage.Spec.MlDsa.Contract

/-!
# Known-answer tests for the ML-DSA specification: the checks

NIST ACVP vectors for FIPS 204, read from the vendored `internalProjection.json`
files under `vectors/nist-acvp/` (see `vectors/sources/`) when the files
`MlDsa44.lean`, `MlDsa65.lean` and `MlDsa87.lean` are built, and checked
against `VG.Spec.MlDsa`, so that a transcription error in the spec fails the
build. (Evaluating the spec is slow, so each parameter set is checked in a
file of its own, which Lake builds in parallel.) The loops are bounded by
`minBounds`, which none of the vectors reaches.

For each parameter set: the first vector of `ML-DSA.KeyGen_internal`; of
signature generation, the first vector of each test group of the internal
interface (`ML-DSA.Sign_internal`, with `μ` given or computed from the
message) and of the external interface of pure ML-DSA (`ML-DSA.Sign`, which
formats the message with its context string), deterministic and hedged; and
of signature verification, in each such test group, the first vector of
each reason a signature is valid or not. The contracts' leakage functions
are checked on the same vectors: signing's (`signLeak`) starts with `ρ` and
ends with the hint of the signature, each iteration's `c̃` tagged with
whether it was rejected. HashML-DSA has no spec, so its
test groups are skipped. (Only these are checked here; the Rust tests run
the implementation on every vector.)
-/

namespace VG.Test.MlDsa

open Lean Elab Command Spec.MlDsa

/-- A successful iteration returns the commitment it computed. -/
private theorem iteration_commit (p : Params) (b : Bounds) (a : List (List Poly))
    (s1 s2 t0 : List Poly) (mu rho : List Byte) (k : Nat)
    (r : List Byte × Option (List Poly × List (Vector Bool n)))
    (h : signIteration p b a s1 s2 t0 mu rho k = some r) :
    r.1 = (signCommit p a mu rho k).2.2 := by
  unfold signIteration at h
  generalize hc : signCommit p a mu rho k = sc at h ⊢
  rcases sc with ⟨y, w, ct⟩
  dsimp only at h ⊢
  generalize he : sampleInBall p.τ b.ball ct = sampled at h
  cases sampled with
  | none => cases h
  | some c =>
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · cases h; rfl
    · split at h <;> (cases h; rfl)

/-- Test evaluator that reuses the iteration's commitment. -/
private def leakLoopCached (p : Params) (b : Bounds) (a : List (List Poly))
    (s1 s2 t0 : List Poly) (mu rho : List Byte) : Nat → Nat → List Nat
  | 0, _ => []
  | iters + 1, k =>
    match signIteration p b a s1 s2 t0 mu rho k with
    | some (ct, none) => leakBytes ct ++ 0 :: leakLoopCached p b a s1 s2 t0 mu rho iters (k + p.ℓ)
    | some (ct, some (_, h)) => leakBytes ct ++ 1 :: h.flatMap (fun hi => hi.toList.map Bool.toNat)
    | none => leakBytes (signCommit p a mu rho k).2.2

private theorem leakLoopCached_eq (p : Params) (b : Bounds) (a : List (List Poly))
    (s1 s2 t0 : List Poly) (mu rho : List Byte) (iters k : Nat) :
    leakLoopCached p b a s1 s2 t0 mu rho iters k = signLeakLoop p b a s1 s2 t0 mu rho iters k := by
  induction iters generalizing k with
  | zero => rfl
  | succ iters ih =>
    simp only [leakLoopCached, signLeakLoop]
    cases e : signIteration p b a s1 s2 t0 mu rho k with
    | none => simp only [List.append_nil]
    | some r =>
      have h := iteration_commit p b a s1 s2 t0 mu rho k r e
      rcases r with ⟨ct, r⟩
      dsimp only at h
      cases r with
      | none => simp only [h, ih]
      | some r => rcases r with ⟨z, hh⟩; simp only [h]

private def leakCached (p : Params) (sk mu rnd : List Byte) : List Nat :=
  let (rho, key, _tr, s1, s2, t0) := skDecode p sk
  leakBytes rho ++
    match expandA p maxBounds rho with
    | none => []
    | some a =>
      leakLoopCached p maxBounds a (s1.map fun s => ntt (toRq s)) (s2.map fun s => ntt (toRq s))
        (t0.map fun t => ntt (toRq t)) mu (H (key ++ rnd ++ mu) 64) maxBounds.sign 0

private theorem leakCached_eq (p : Params) (sk mu rnd : List Byte) :
    leakCached p sk mu rnd = signLeak p sk mu rnd := by
  simp only [leakCached, signLeak, leakLoopCached_eq]
  rfl

private theorem iteration_mono (p : Params) (a : List (List Poly))
    (s1 s2 t0 : List Poly) (mu rho : List Byte) (k : Nat)
    (r : List Byte × Option (List Poly × List (Vector Bool n)))
    (h : signIteration p minBounds a s1 s2 t0 mu rho k = some r) :
    signIteration p maxBounds a s1 s2 t0 mu rho k = some r := by
  unfold signIteration at h ⊢
  generalize hc : signCommit p a mu rho k = sc at h ⊢
  rcases sc with ⟨y, w, ct⟩
  dsimp only at h ⊢
  cases he : sampleInBall p.τ minBounds.ball ct with
  | none => simp only [he, Option.bind_eq_bind, Option.bind_none] at h; cases h
  | some c =>
    have he' := VG.Proof.MlDsa.Sign.sampleInBall_mono
      VG.Proof.MlDsa.Sign.minBounds_le_max.2.1 he
    simpa only [he, he', Option.bind_eq_bind, Option.bind_some] using h

private abbrev SignedParts := List Byte × List Poly × List (Vector Bool n)

/-- Record the exact leakage while finding the first accepted signature. -/
private def traceLoop (p : Params) (b : Bounds) (a : List (List Poly))
    (s1 s2 t0 : List Poly) (mu rho : List Byte) : Nat → Nat → Option (SignedParts × List Nat)
  | 0, _ => none
  | iters + 1, k => do
    match ← signIteration p b a s1 s2 t0 mu rho k with
    | (ct, some (z, h)) =>
      return ((ct, z, h), leakBytes ct ++ 1 :: h.flatMap (fun hi => hi.toList.map Bool.toNat))
    | (ct, none) =>
      let (sig, leak) ← traceLoop p b a s1 s2 t0 mu rho iters (k + p.ℓ)
      return (sig, leakBytes ct ++ 0 :: leak)

private theorem traceLoop_sig (p : Params) (b : Bounds) (a : List (List Poly))
    (s1 s2 t0 : List Poly) (mu rho : List Byte) (iters k : Nat) :
    (traceLoop p b a s1 s2 t0 mu rho iters k).map Prod.fst =
      signLoop p b a s1 s2 t0 mu rho iters k := by
  induction iters generalizing k with
  | zero => rfl
  | succ iters ih =>
    simp only [traceLoop, signLoop]
    cases he : signIteration p b a s1 s2 t0 mu rho k with
    | none => rfl
    | some r =>
      rcases r with ⟨ct, z⟩
      cases z with
      | some zh => rcases zh with ⟨z, h⟩; rfl
      | none =>
        simp only [Option.bind_eq_bind, Option.bind_some]
        rw [← ih]
        cases traceLoop p b a s1 s2 t0 mu rho iters (k + p.ℓ) <;> rfl

private theorem traceLoop_leak (p : Params) (a : List (List Poly))
    (s1 s2 t0 : List Poly) (mu rho : List Byte) (iters more k : Nat)
    (hbound : iters ≤ more) (sig : SignedParts) (leak : List Nat)
    (h : traceLoop p minBounds a s1 s2 t0 mu rho iters k = some (sig, leak)) :
    leak = leakLoopCached p maxBounds a s1 s2 t0 mu rho more k := by
  induction iters generalizing more k sig leak with
  | zero => cases h
  | succ iters ih =>
    cases more with
    | zero => omega
    | succ more =>
      have hb : iters ≤ more := Nat.le_of_succ_le_succ hbound
      simp only [traceLoop] at h
      cases he : signIteration p minBounds a s1 s2 t0 mu rho k with
      | none => simp only [he, Option.bind_eq_bind, Option.bind_none] at h; cases h
      | some r =>
        have he' := iteration_mono p a s1 s2 t0 mu rho k r he
        rcases r with ⟨ct, z⟩
        rw [leakLoopCached, he']
        cases z with
        | some zh =>
          rcases zh with ⟨z, hh⟩
          simp only [he, Option.bind_eq_bind, Option.bind_some] at h
          change Option.some _ = Option.some (sig, leak) at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact h.2.symm
        | none =>
          simp only [he, Option.bind_eq_bind, Option.bind_some] at h
          cases ht : traceLoop p minBounds a s1 s2 t0 mu rho iters (k + p.ℓ) with
          | none => simp only [ht, Option.bind_none] at h; cases h
          | some pair =>
            rcases pair with ⟨sig', leak'⟩
            simp only [ht, Option.bind_some] at h
            change Option.some _ = Option.some (sig, leak) at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.2, ih more (k + p.ℓ) hb sig' leak' ht]

private def traceMu (p : Params) (sk mu rnd : List Byte) : Option (List Byte × List Nat) := do
  let (rho, key, _tr, s1, s2, t0) := skDecode p sk
  let s1Hat := s1.map fun s => ntt (toRq s)
  let s2Hat := s2.map fun s => ntt (toRq s)
  let t0Hat := t0.map fun s => ntt (toRq s)
  let a ← expandA p minBounds rho
  let rho' := H (key ++ rnd ++ mu) 64
  let ((ct, z, h), leak) ← traceLoop p minBounds a s1Hat s2Hat t0Hat mu rho' minBounds.sign 0
  return (sigEncode p ct (z.map fun zi => zi.map fun c => modPm c.val q) h, leakBytes rho ++ leak)

private theorem traceMu_sig (p : Params) (sk mu rnd : List Byte) :
    (traceMu p sk mu rnd).map Prod.fst = signMu p minBounds sk mu rnd := by
  rcases hd : skDecode p sk with ⟨rho, key, tr, s1, s2, t0⟩
  simp only [traceMu, signMu, hd]
  cases ha : expandA p minBounds rho with
  | none => rfl
  | some a =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [← traceLoop_sig]
    cases traceLoop p minBounds a (s1.map fun s => ntt (toRq s))
      (s2.map fun s => ntt (toRq s)) (t0.map fun s => ntt (toRq s)) mu
      (H (key ++ rnd ++ mu) 64) minBounds.sign 0 with
    | none => rfl
    | some r => rcases r with ⟨⟨ct, z, h⟩, leak⟩; rfl

private theorem traceMu_leak (p : Params) (sk mu rnd sig : List Byte) (leak : List Nat)
    (h : traceMu p sk mu rnd = some (sig, leak)) : leak = signLeak p sk mu rnd := by
  rcases hd : skDecode p sk with ⟨rho, key, tr, s1, s2, t0⟩
  simp only [traceMu, hd] at h
  cases ha : expandA p minBounds rho with
  | none => simp only [ha, Option.bind_eq_bind, Option.bind_none] at h; cases h
  | some a =>
    have ha' := VG.Proof.MlDsa.Sign.expandA_mono VG.Proof.MlDsa.Sign.minBounds_le_max.1 ha
    simp only [ha, Option.bind_eq_bind, Option.bind_some] at h
    cases ht : traceLoop p minBounds a (s1.map fun s => ntt (toRq s))
      (s2.map fun s => ntt (toRq s)) (t0.map fun s => ntt (toRq s)) mu
      (H (key ++ rnd ++ mu) 64) minBounds.sign 0 with
    | none => simp only [ht, Option.bind_none] at h; cases h
    | some r =>
      rcases r with ⟨⟨ct, z, hh⟩, trace⟩
      simp only [ht, Option.bind_some] at h
      change Option.some _ = Option.some (sig, leak) at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      have he := traceLoop_leak p a (s1.map fun s => ntt (toRq s))
        (s2.map fun s => ntt (toRq s)) (t0.map fun s => ntt (toRq s)) mu
        (H (key ++ rnd ++ mu) 64) minBounds.sign maxBounds.sign 0
        VG.Proof.MlDsa.Sign.minBounds_le_max.2.2 (ct, z, hh) trace ht
      rw [← h.2, ← leakCached_eq]
      simp only [leakCached, hd, ha', he]

/-- The vendored `vectors/nist-acvp/<dir>/internalProjection.json`. -/
def readVectors (dir : String) : CommandElabM Json := do
  -- This file is `lean/VerifiedGarbageTest/MlDsa.lean`.
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "nist-acvp" / dir / "internalProjection.json")
  match Json.parse text with
  | .ok j => pure j
  | .error e => throwError "{dir}: {e}"

/-- The parameter set named `name`. -/
def params (name : String) : Option Params :=
  match name with
  | "ML-DSA-44" => some mlDsa44
  | "ML-DSA-65" => some mlDsa65
  | "ML-DSA-87" => some mlDsa87
  | _ => none

/-- A test group: its parameter set, its interface (`internal` or
`external`), its pre-hash mode (`none`, `pure` or `preHash`), whether `μ`
is given, whether signing is deterministic, and its test cases. -/
structure Group where
  params : Params
  name : String
  interface : String
  preHash : String
  externalMu : Bool
  deterministic : Bool
  tests : Array Json

/-- The test groups of an ACVP file. -/
def groups (j : Json) : Except String (List Group) := do
  let gs ← j.getObjValAs? (Array Json) "testGroups"
  gs.toList.mapM fun g => do
    let name ← g.getObjValAs? String "parameterSet"
    let some p := params name | throw s!"unknown parameter set {name}"
    return { params := p, name,
             interface := (g.getObjValAs? String "signatureInterface").toOption.getD ""
             preHash := (g.getObjValAs? String "preHash").toOption.getD ""
             externalMu := (g.getObjValAs? Bool "externalMu").toOption.getD false
             deterministic := (g.getObjValAs? Bool "deterministic").toOption.getD false
             tests := ← g.getObjValAs? (Array Json) "tests" }

/-- The bytes written in hex in the field `key` of a test case. -/
def bytes (t : Json) (key : String) : Except String (List Byte) := do
  let s ← t.getObjValAs? String key
  let some bs := Test.Sha256.unhex s.toLower | throw s!"bad hex in {key}"
  return bs

/-- Runs `check` on each test group of the parameter set `name`, failing
with its error. -/
def checkGroups (name dir : String) (check : Group → Except String Unit) :
    CommandElabM Unit := do
  let gs ← match groups (← readVectors dir) with
    | .ok gs => pure gs
    | .error e => throwError "{dir}: {e}"
  let gs := gs.filter (·.name == name)
  if gs.isEmpty then throwError "{dir}: no {name} test group"
  for g in gs do
    match check g with
    | .ok () => pure ()
    | .error e => throwError "{dir}, {g.name} {g.interface} {g.preHash}: {e}"

/-- The formatted message `M′` of a test case: its message, formatted with
its context string by the external interface, or as it is by the internal
one. -/
def formatted (g : Group) (t : Json) : Except String (List Byte) := do
  let M ← bytes t "message"
  if g.interface == "external" then
    let some M' := formatMessage (← bytes t "context") M | throw "context string too long"
    return M'
  return M

/-- The message representative `μ` of a test case: given (`externalMu`), or
computed from the public key hash `tr` and its formatted message. -/
def mu (g : Group) (t : Json) (tr : List Byte) : Except String (List Byte) := do
  if g.externalMu then bytes t "mu" else return messageRep tr (← formatted g t)

/-- Checks the spec against the vectors of the parameter set `name` (see
above). -/
def check (name : String) : CommandElabM Unit := do
  checkGroups name "ML-DSA-keyGen-FIPS204" fun g => do
    let some t := g.tests[0]? | throw "no test case"
    unless keyGenInternal g.params minBounds (← bytes t "seed") ==
        some (← bytes t "pk", ← bytes t "sk") do
      throw "KeyGen_internal is wrong"
    unless (keyGenLeak g.params (← bytes t "seed")).length ==
        32 + (g.params.ℓ + g.params.k) * 2 * maxBounds.rejBounded do
      throw "keyGenLeak is wrong"
  checkGroups name "ML-DSA-sigGen-FIPS204" fun g => do
    if g.preHash == "preHash" then return
    let some t := g.tests[0]? | throw "no test case"
    let sk ← bytes t "sk"
    let rnd ← if g.deterministic then pure (List.replicate 32 0) else bytes t "rnd"
    let μ ← mu g t (skTr sk)
    let σ ← bytes t "signature"
    let both := (⟨traceMu g.params sk μ rnd,
      traceMu_sig g.params sk μ rnd, fun sig leak h => traceMu_leak g.params sk μ rnd sig leak h⟩ :
      {r : Option (List Byte × List Nat) // r.map Prod.fst = signMu g.params minBounds sk μ rnd ∧
        ∀ sig leak, r = some (sig, leak) → leak = signLeak g.params sk μ rnd}).val
    let some (signed, leak) := both | throw "Sign_internal is wrong"
    unless signed == σ do
      throw "Sign_internal is wrong"
    -- What the contract lets signing leak ends with the hint of the signature.
    let some h := (sigDecode g.params σ).2.2 | throw "the signature's hint is malformed"

    -- `ρ`, then each iteration's `c̃` and 0 (rejected), then the last one's
    -- `c̃`, 1 and hint.
    let hint := h.flatMap (·.toList.map Bool.toNat)
    let iters := (leak.length - 32 - hint.length) / (g.params.ctildeLen + 1)
    unless leak.take 32 == leakBytes (sk.take 32) && leak.drop (leak.length - hint.length) == hint &&
        32 + iters * (g.params.ctildeLen + 1) + hint.length == leak.length &&
        (List.range iters).all (fun i =>
          leak.getD (32 + (i + 1) * (g.params.ctildeLen + 1) - 1) 2 == if i + 1 = iters then 1 else 0) do
      throw "signLeak is wrong"
  checkGroups name "ML-DSA-sigVer-FIPS204" fun g => do
    if g.preHash == "preHash" then return
    let mut seen : List String := []
    for t in g.tests do
      let reason ← t.getObjValAs? String "reason"
      if reason ∈ seen then continue
      seen := reason :: seen
      let pk ← bytes t "pk"
      unless verifyMu g.params minBounds pk (← mu g t (pkTr pk)) (← bytes t "signature") ==
          some (← t.getObjValAs? Bool "testPassed") do
        throw s!"Verify_internal is wrong on {reason}"
    if seen.length < 4 then throw s!"only the reasons {seen}"

end VG.Test.MlDsa
