module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.CT
public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.AnyHash
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Frame
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.X25519.X86.Column

/-!
# Deterministic ECDSA on x86 (32-bit): `Verified`

The code for a curve `R` and a tier `t` of hash functions does not depend on
the hash function: a run with `hash = i + 1` is one of the run of
`mkP R I₀ t i` (`RfcHash`), whose instance is `instOf I₀ (i + 1)`: the
contract's with the hash function `i + 1` names. So for every `i`, `sign_ok`
gives the postcondition of `rfcX86` at that instance, and `sign_ct` constant
time between runs with the same `hash` (public): together `anyK`, which
`Verified.narrowTo` moves to `I₀.signAnyContract`, whose arguments' slots
are writable (`AnyFacts`: what its precondition says, evaluated). No
instruction of the function or of those it calls writes `esp` but the
frames' (`sign_spSafe`, from `body_nosp`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.Pbkdf2.Whole.X86 (Tier)

/-- No instruction writes `esp` but the frames'. -/
theorem sign_spSafe (P : RfcHash) : (cfgOf P).sign.all (fun i => !isa.writesSp i) = true := by
  have h : (cfgOf P).body.all (fun i => !isa.writesSp i) = true := by
    rw [Proof.Pbkdf2.Whole.X86.all_eq, List.all_eq_true]
    intro i hi
    rw [← Proof.Pbkdf2.Whole.X86.clobbers_esp]
    simpa using body_nosp P i hi
  show (!isa.writesSp _ && (cfgOf P).body.all _ && !isa.writesSp _) = true
  rw [h]
  rfl

/-! ## The hash function `hash` names -/

/-- The instance `I₀` with the hash function `k` names (`HashId`). -/
def instOf (I₀ : Spec.Ecdsa.Rfc6979.Instance) (k : Nat) : Spec.Ecdsa.Rfc6979.Instance :=
  { I₀ with hash := (Spec.HashId.hmac k).getD I₀.hash, hashLen := ((Spec.HashId.mgf1 k).map (·.len)).getD 0 }

/-- The proof's contract for any of the hash functions: `rfcX86` at the
instance of `hash`. -/
def anyK (I₀ : Spec.Ecdsa.Rfc6979.Instance) (N : Nat) (cs : List (String × List (BitVec 64))) : Contract isa where
  pre s := ∃ i < 7, (arg s 5).toNat = i + 1 ∧ (rfcX86 (instOf I₀ (i + 1)) (i + 1) N cs).pre s
  post s s' := ∀ i < 7, (arg s 5).toNat = i + 1 → (rfcX86 (instOf I₀ (i + 1)) (i + 1) N cs).post s s'
  pub s₁ s₂ := ∃ i < 7, (arg s₁ 5).toNat = i + 1 ∧ (rfcX86 (instOf I₀ (i + 1)) (i + 1) N cs).pub s₁ s₂

/-- The run with the `i`th hash function of the tier `t`. -/
def mkP (R : RfcCurve) (I₀ : Spec.Ecdsa.Rfc6979.Instance) (hE : I₀.ecdsa = R.inst) (htp : 0 < I₀.tries)
    (htl : I₀.tries < 2 ^ 32) (t : Tier) (i : Nat) (hi : i < 7) : RfcHash where
  R := R
  I₀ := I₀
  ecdsa := hE
  tries_pos := htp
  tries_lt := htl
  fns := t.fns
  nodup := by rw [t.keys]; decide
  keys_lt p hp := by
    have : p.1 ∈ t.fns.map (·.1) := List.mem_map_of_mem hp
    rw [t.keys] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    omega
  fnsSp p hp := by
    obtain ⟨h, -, e⟩ := t.fns_mem hp
    rw [e]
    exact ⟨h.ok.hiSp, h.ok.hH.updSp, h.ok.hfSp⟩
  k := i + 1
  T := t.get i hi
  mem := t.mem_fns i hi
  hmac := t.hmac_get i hi

theorem mkP_I {R : RfcCurve} {I₀ : Spec.Ecdsa.Rfc6979.Instance} {hE : I₀.ecdsa = R.inst} {htp : 0 < I₀.tries}
    {htl : I₀.tries < 2 ^ 32} {t : Tier} {i : Nat} (hi : i < 7) :
    (mkP R I₀ hE htp htl t i hi).I = instOf I₀ (i + 1) := by
  show { I₀ with hash := _, hashLen := _ } = { I₀ with hash := _, hashLen := _ }
  rw [t.hmac_get i hi, t.len_get i hi]
  rfl

theorem mkP_cfg {R : RfcCurve} {I₀ : Spec.Ecdsa.Rfc6979.Instance} {hE : I₀.ecdsa = R.inst} {htp : 0 < I₀.tries}
    {htl : I₀.tries < 2 ^ 32} {t : Tier} {i : Nat} (hi : i < 7) :
    cfgOf (mkP R I₀ hE htp htl t i hi) = cfgAny R t.fns I₀ := rfl

/-- The code meets `anyK`: each run is one of the `mkP` of its `hash`. -/
theorem any_verified (R : RfcCurve) (I₀ : Spec.Ecdsa.Rfc6979.Instance) (hE : I₀.ecdsa = R.inst)
    (htp : 0 < I₀.tries) (htl : I₀.tries < 2 ^ 32) (t : Tier) (hsat : ∃ s, (anyK I₀ 536 R.E.combConsts).pre s) :
    Verified X86.target (cfgAny R t.fns I₀).sign (anyK I₀ 536 R.E.combConsts) := by
  refine ⟨fun s ⟨i, hi, hk, hp⟩ => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨i, hi, hk, hp₁⟩ ⟨j, hj, hk', hp₂⟩ ⟨l, hl, hk'', hpub⟩ e₁ e₂ => ?_,
    hsat⟩
  · rw [← mkP_I (hE := hE) (htp := htp) (htl := htl) (t := t) hi] at hp
    obtain ⟨tr, s', ex, ha, hq⟩ := sign_ok hp
    refine ⟨tr, s', ex, ha, fun j _ hj => ?_⟩
    have e : i = j := by omega
    subst e
    rw [← mkP_I (hE := hE) (htp := htp) (htl := htl) (t := t) hi]
    exact hq
  · have e : i = l := by omega
    subst e
    have e : i = j := by
      have := hpub.2.2.2.2.2.2.1
      have h5 : (arg s₁ 5).toNat = (arg s₂ 5).toNat := by rw [this]
      omega
    subst e
    rw [← mkP_I (hE := hE) (htp := htp) (htl := htl) (t := t) hi] at hp₁ hp₂ hpub
    exact sign_ct (P := mkP R I₀ hE htp htl t i hi) s₁ s₂ t₁ t₂ s₁' s₂' hp₁ hp₂ hpub e₁ e₂

/-! ## The shared contract -/

/-- The regions `rfcX86` reads: the arguments' slots, among them. -/
def anyRd (I₀ : Spec.Ecdsa.Rfc6979.Instance) (s : State) (cs : List (String × List (BitVec 64))) : List Region :=
  [⟨(arg s 1).setWidth 64, I₀.ecdsa.curve.len⟩, ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩, ⟨argAddr s 0, 24⟩] ++
    Abi.constRegions (fun n => (s.syms n).setWidth 64) cs
def anyWr (I₀ : Spec.Ecdsa.Rfc6979.Instance) (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 2 * I₀.ecdsa.curve.len⟩, ⟨(arg s 4).setWidth 64, 8192⟩]

/-- What the shared contract's precondition says, evaluated. -/
structure AnyFacts (I₀ : Spec.Ecdsa.Rfc6979.Instance) (cs : List (String × List (BitVec 64))) (s : State) : Prop where
  hash : (arg s 5).toNat ∈ Spec.Ecdsa.Rfc6979.hashIds
  len : ∀ H, Spec.HashId.mgf1 (arg s 5).toNat = some H → (arg s 3).toNat = H.len
  rd : s.rd = [⟨(arg s 1).setWidth 64, I₀.ecdsa.curve.len⟩, ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩] ++
    Abi.constRegions (fun n => (s.syms n).setWidth 64) cs
  wr : s.wr = [⟨(arg s 0).setWidth 64, 2 * I₀.ecdsa.curve.len⟩, ⟨(arg s 4).setWidth 64, 8192⟩, ⟨argAddr s 0, 24⟩]
  pre : (rfcX86 { I₀ with hashLen := (arg s 3).toNat } (arg s 5).toNat 536 cs).pre
    (s.withRegions (anyRd I₀ s cs) (anyWr I₀ s))

theorem facts_nil (I₀ : Spec.Ecdsa.Rfc6979.Instance) (hS : I₀.scratchWords = 1024) (s : State)
    (h : (I₀.signAnyContract (X86.abi.withConsts []) 536).pre s) : AnyFacts I₀ [] s := by
  sig_pre [Spec.Ecdsa.Rfc6979.Instance.signAnyContract, Spec.Ecdsa.Rfc6979.Instance.signAnySig,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
  simp only [hS, Nat.reduceMul] at h
  obtain ⟨sp, top, rd, wr, od, og, oc, oa, dc, da, gc, ga, ca, ro, rd', rg, rc, ra, ko, kd, kg, kc, ka,
    bo, bd, bg, bc, hh, hl⟩ := h
  refine ⟨hh, hl, by rw [rd]; rfl, wr, ?_⟩
  simp only [rfcX86, anyRd, anyWr, arg_withRegions, argAddr_withRegions, State.withRegions_gpr,
    State.withRegions_rd, State.withRegions_wr, State.withRegions_syms]
  refine ⟨sp, top, trivial, trivial, od, og, oc, dc, gc, oa.symm, ca.symm, ro, rc, ko, kd, kg, kc, bo, bd, bg, bc,
    trivial, trivial, ?_, ?_⟩
  · simp [Abi.constsHeld]
  · simp [Abi.constRegions]

theorem facts_cons (I₀ : Spec.Ecdsa.Rfc6979.Instance) (hS : I₀.scratchWords = 1024) (c : String × List (BitVec 64))
    (cs : List (String × List (BitVec 64))) (s : State)
    (h : (I₀.signAnyContract (X86.abi.withConsts (c :: cs)) 536).pre s) : AnyFacts I₀ (c :: cs) s := by
  sig_pre [Spec.Ecdsa.Rfc6979.Instance.signAnyContract, Spec.Ecdsa.Rfc6979.Instance.signAnySig,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Abi.withConsts, stackBelow] at h
  simp only [hS, Nat.reduceMul] at h
  obtain ⟨sp, top, hdrop, held, tbl, htake, wr, od, og, oc, oa, dc, da, gc, ga, ca, ro, rd', rg, rc, ra,
    ko, kd, kg, kc, ka, bo, bd, bg, bc, hh, hl⟩ := h
  have rd : s.rd = [⟨(arg s 1).setWidth 64, I₀.ecdsa.curve.len⟩, ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩] ++
      Abi.constRegions (fun n => (s.syms n).setWidth 64) (c :: cs) := by
    rw [← List.take_append_drop (s.rd.length - (cs.length + 1)) s.rd, htake, hdrop]
  refine ⟨hh, hl, rd, wr, ?_⟩
  simp only [rfcX86, anyRd, anyWr, arg_withRegions, argAddr_withRegions, State.withRegions_gpr,
    State.withRegions_rd, State.withRegions_wr, State.withRegions_syms]
  refine ⟨sp, top, trivial, trivial, od, og, oc, dc, gc, oa.symm, ca.symm, ro, rc, ko, kd, kg, kc, bo, bd, bg, bc,
    trivial, trivial, held, fun t ht => ⟨(tbl t ht).1, ?_⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (tbl t ht).2.1 _ (by rw [wr]; simp)
  · exact (tbl t ht).2.1 _ (by rw [wr]; simp)
  · exact (tbl t ht).2.2.1
  · exact (tbl t ht).2.2.2

theorem facts (I₀ : Spec.Ecdsa.Rfc6979.Instance) (hS : I₀.scratchWords = 1024) (cs : List (String × List (BitVec 64)))
    (s : State) (h : (I₀.signAnyContract (X86.abi.withConsts cs) 536).pre s) : AnyFacts I₀ cs s := by
  cases cs with
  | nil => exact facts_nil I₀ hS s h
  | cons c cs => exact facts_cons I₀ hS c cs s h

/-- The hash function's number, `i + 1`, and its values' length. -/
theorem AnyFacts.idx {I₀ : Spec.Ecdsa.Rfc6979.Instance} {cs : List (String × List (BitVec 64))} {s : State}
    (h : AnyFacts I₀ cs s) : ∃ i < 7, (arg s 5).toNat = i + 1 ∧ (instOf I₀ (i + 1)).hashLen = (arg s 3).toNat := by
  have hh := h.hash
  simp only [Spec.Ecdsa.Rfc6979.hashIds, List.mem_cons, List.not_mem_nil, or_false] at hh
  refine ⟨(arg s 5).toNat - 1, by omega, by omega, ?_⟩
  have hl := h.len
  rcases hh with e | e | e | e | e | e | e <;> rw [e] at hl ⊢ <;> exact (hl _ rfl).symm

/-- `rfcX86` at the instance of `hash`. -/
theorem AnyFacts.anyPre {I₀ : Spec.Ecdsa.Rfc6979.Instance} {cs : List (String × List (BitVec 64))} {s : State}
    (h : AnyFacts I₀ cs s) : (anyK I₀ 536 cs).pre (s.withRegions (anyRd I₀ s cs) (anyWr I₀ s)) := by
  obtain ⟨i, hi, hk, hl⟩ := h.idx
  refine ⟨i, hi, by rw [arg_withRegions, hk], ?_⟩
  have e : instOf I₀ (i + 1) = { instOf I₀ (i + 1) with hashLen := (arg s 3).toNat } := by
    rw [← hl]
  have hp := h.pre
  rw [hk] at hp
  rw [e]
  exact hp

/-- RFC 6979's signature with the hash function `hash` names. -/
theorem anyResult_eq (I₀ : Spec.Ecdsa.Rfc6979.Instance) {i : Nat} (hi : i < 7) (m : Mem) (d dg : Addr) {n : Nat}
    (hn : (instOf I₀ (i + 1)).hashLen = n) :
    I₀.anyResult m d dg n (i + 1) = some (result (instOf I₀ (i + 1)) m d dg) := by
  obtain ⟨H, hH⟩ : ∃ H, Spec.HashId.hmac (i + 1) = some H := by
    match i, hi with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => exact ⟨_, rfl⟩
  subst hn
  simp only [Spec.Ecdsa.Rfc6979.Instance.anyResult, hH, Option.map_some, result,
    Spec.Ecdsa.Rfc6979.Instance.result, instOf, Option.getD_some]

/-- The tables change only what the shared contract reads and its public data. -/
theorem post_eq (I₀ : Spec.Ecdsa.Rfc6979.Instance) (cs : List (String × List (BitVec 64))) :
    (I₀.signAnyContract (X86.abi.withConsts cs) 536).post = (I₀.signAnyContract (X86.abi.withConsts []) 536).post := by
  cases cs <;> rfl

/-- The shared contract's public data, evaluated. -/
theorem pub_facts (I₀ : Spec.Ecdsa.Rfc6979.Instance) (cs : List (String × List (BitVec 64))) {s₁ s₂ : State}
    (h : (I₀.signAnyContract (X86.abi.withConsts cs) 536).pub s₁ s₂) :
    s₁.gpr .esp = s₂.gpr .esp ∧ (∀ c ∈ cs, s₁.syms c.1 = s₂.syms c.1) ∧
      ((I₀.anyResult s₁.mem ((arg s₁ 1).setWidth 64) ((arg s₁ 2).setWidth 64) (arg s₁ 3).toNat (arg s₁ 5).toNat).map
        (·.2)).getD 0 =
      ((I₀.anyResult s₂.mem ((arg s₂ 1).setWidth 64) ((arg s₂ 2).setWidth 64) (arg s₂ 3).toNat (arg s₂ 5).toNat).map
        (·.2)).getD 0 ∧
      arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3 ∧ arg s₁ 4 = arg s₂ 4 ∧
      arg s₁ 5 = arg s₂ 5 := by
  cases cs with
  | nil =>
    sig_pub [Spec.Ecdsa.Rfc6979.Instance.signAnyContract, Spec.Ecdsa.Rfc6979.Instance.signAnySig,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Abi.withConsts, stackBelow] at h
    obtain ⟨he, hl, a0, a1, a2, a3, a4, a5⟩ := h
    exact ⟨he, by simp, (List.cons.inj hl).1, a0, a1, a2, a3, a4, a5⟩
  | cons c cs =>
    sig_pub [Spec.Ecdsa.Rfc6979.Instance.signAnyContract, Spec.Ecdsa.Rfc6979.Instance.signAnySig,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Abi.withConsts, stackBelow] at h
    obtain ⟨he, hc, hcs, hl, a0, a1, a2, a3, a4, a5⟩ := h
    refine ⟨he, ?_, (List.cons.inj hl).1, a0, a1, a2, a3, a4, a5⟩
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hc
    · exact hcs x hx

/-- The code meets the shared contract. -/
theorem sign_verified (R : RfcCurve) (I₀ : Spec.Ecdsa.Rfc6979.Instance) (hE : I₀.ecdsa = R.inst)
    (htp : 0 < I₀.tries) (htl : I₀.tries < 2 ^ 32) (hS : I₀.scratchWords = 1024) (t : Tier)
    (hsat : ∃ s, (I₀.signAnyContract (X86.abi.withConsts R.E.combConsts) 536).pre s) :
    Verified X86.target (cfgAny R t.fns I₀).sign (I₀.signAnyContract (X86.abi.withConsts R.E.combConsts) 536) := by
  have hf := facts I₀ hS R.E.combConsts
  refine Verified.narrowTo (any_verified R I₀ hE htp htl t
      (hsat.elim fun s h => ⟨_, (hf s h).anyPre⟩))
    (fun s => anyRd I₀ s R.E.combConsts) (anyWr I₀) (fun s h => (hf s h).anyPre) ?_ ?_ ?_ ?_ hsat
  · intro s h a n ⟨r, hr, hc⟩
    rw [(hf s h).rd, (hf s h).wr]
    refine ⟨r, ?_, hc⟩
    simp only [anyRd, anyWr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with ((rfl | rfl | rfl) | hr) | (rfl | rfl) <;> simp_all
  · intro s h a n ⟨r, hr, hc⟩
    rw [(hf s h).wr]
    refine ⟨r, ?_, hc⟩
    simp only [anyWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp
  · intro s s' h hq
    obtain ⟨i, hi, hk, hl⟩ := (hf s h).idx
    have hq := hq i hi (by rw [arg_withRegions, hk])
    simp only [rfcX86, arg_withRegions, State.withRegions_gpr, State.withRegions_mem] at hq
    rw [post_eq]
    sig_post [Spec.Ecdsa.Rfc6979.Instance.signAnyContract, Spec.Ecdsa.Rfc6979.Instance.signAnySig,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Abi.withConsts, stackBelow]
    rw [hk, anyResult_eq I₀ hi _ _ _ hl]
    revert hq
    generalize result (instOf I₀ (i + 1)) s.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64) = r
    obtain ⟨o, n⟩ := r
    cases o <;> exact id
  · intro s₁ s₂ h₁ h₂ hp
    obtain ⟨i, hi, hk, hl⟩ := (hf s₁ h₁).idx
    obtain ⟨he, hsy, hl', a0, a1, a2, a3, a4, a5⟩ := pub_facts I₀ R.E.combConsts hp
    refine ⟨i, hi, by rw [arg_withRegions, hk], ?_⟩
    simp only [rfcX86, arg_withRegions, State.withRegions_gpr, State.withRegions_mem, State.withRegions_syms]
    refine ⟨he, a0, a1, a2, a3, a4, a5, ?_, hsy⟩
    have hk₂ : (arg s₂ 5).toNat = i + 1 := by rw [← a5, hk]
    have hl₂ : (instOf I₀ (i + 1)).hashLen = (arg s₂ 3).toNat := by rw [← a3, hl]
    rw [hk, hk₂, anyResult_eq I₀ hi _ _ _ hl, anyResult_eq I₀ hi _ _ _ hl₂] at hl'
    exact hl'

end VG.Proof.Ecdsa.Rfc6979.X86
