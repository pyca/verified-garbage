import VerifiedGarbage.Proof.Ed25519.AArch64.Point64.Fn
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.TCB.AArch64.Target

/-!
# Ed25519's point functions on AArch64: their `Verified`

The facts of `Spec.Ed25519.Point64`'s contracts on AArch64 (`fnPre`: `ws` in
`x0`), which the functions meet (`fn_correct`, from `fn_ok`): the callee-saved
registers are restored, no instruction writes `v8`–`v15`, and every byte they
write is in slots 0–3 or 8–15; the spec's coordinates are the slots' field
elements (`elemAt_eq`). Constant time by taint tracking (only the pointer, in
`x0`, is public, and every address is `ws` plus a constant), and a state
satisfying the precondition.
-/

namespace VG.Proof.Ed25519.AArch64.Point64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.Ed25519.AArch64.Point64 VG.Proof.Ed25519.AArch64
open VG.Spec.Ed25519.Point64 (elemAt pointAt PointIs pAt qAt elemBytes)

/-- The spec's coordinate at `o` is the field element there. -/
theorem elemAt_eq (m : Mem) (base : Addr) (o : Nat) : elemAt m base o = F m base o := by
  show Fin.ofNat _ (m.read (Mont.off base o) (8 * 4)).toNat = Proof.X25519.toFe (fe m base o)
  rw [Mont.read_eq_wordsVal]
  simp only [Mont.wordsVal, fe, Word64.val4, word, off, Mont.word, Mont.off, Nat.mul_zero,
    Nat.add_zero]
  congr 1
  grind

/-- The spec's point at slot `i` is the slots' point. -/
theorem pointAt_eq (m : Mem) (base : Addr) (i : Nat) (hi : i + 3 < 22) :
    pointAt m base (64 + 32 * i) =
      point (env m base) ⟨i, by omega⟩ ⟨i + 1, by omega⟩ ⟨i + 2, by omega⟩ ⟨i + 3, by omega⟩ := by
  simp only [pointAt, point, env, offset, elemAt_eq, elemBytes]
  congr 2 <;> omega

/-- The facts of the shared contracts about the state: `ws` in `x0`, writable for its 8192
bytes, and not wrapping around. -/
def fnPre (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨s.gpr .x0, 8192⟩] ∧ (s.gpr .x0).toNat + 8192 ≤ 2 ^ 64

/-- What every function's analysis may consider public. -/
def fnPub (s₁ s₂ : State) : Prop := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.sp = s₂.sp

/-- The doubling's contract on AArch64. -/
def doubleK : Contract isa where
  pre := fnPre
  post s s' := PointIs true s'.mem (s.gpr .x0) pAt
      (Spec.Ed25519.Point64.pointDouble (pointAt s.mem (s.gpr .x0) pAt)) ∧
    Spec.Ed25519.Point64.Keeps (s.gpr .x0) s.mem s'.mem
  pub := fnPub

/-- The affine addition's contract on AArch64. -/
def affK : Contract isa where
  pre := fnPre
  post s s' := (∀ q : Spec.Ed25519.Point, q.Z = 1 → elemAt s.mem (s.gpr .x0) qAt = q.Y - q.X →
      elemAt s.mem (s.gpr .x0) (qAt + elemBytes) = q.Y + q.X →
      elemAt s.mem (s.gpr .x0) (qAt + 2 * elemBytes) = q.T * 2 * Spec.Ed25519.d →
      PointIs true s'.mem (s.gpr .x0) pAt (Spec.Ed25519.pointAdd (pointAt s.mem (s.gpr .x0) pAt) q)) ∧
    Spec.Ed25519.Point64.Keeps (s.gpr .x0) s.mem s'.mem
  pub := fnPub

/-- The program's results are in slots 0–3 or 8–15. -/
abbrev OutsOk (ops : List FieldOp) : Prop :=
  ∀ op ∈ ops, (fieldDest op).val < 4 ∨ (8 ≤ (fieldDest op).val ∧ (fieldDest op).val < 16)

/-- The callee-saved registers the functions restore. -/
theorem fn_preserved : ∀ r ∈ preserved, r ∉ clob ∨ r ∈ kept.map Prod.fst := by decide

/-- A function running the field program `ops`: the calling convention kept, the slots' values
`evalOps ops` of theirs, and `Keeps`. -/
theorem fn_correct (ops : List FieldOp) (hv : ∀ r, ∀ i ∈ fieldCode ops, vdstOf i ≠ some r)
    (hkv : (fn ops).allInstrs keepsV = true) (hout : OutsOk ops) (s : State) (hs : fnPre s) :
    ∃ t s', Exec isa (fn ops) s t s' ∧ abiPreserved s s' ∧
      env s'.mem (s.gpr .x0) = evalOps ops (env s.mem (s.gpr .x0)) ∧
      Spec.Ed25519.Point64.Keeps (s.gpr .x0) s.mem s'.mem := by
  obtain ⟨_, hwr, hnw⟩ := hs
  obtain ⟨t, s', he, ⟨hg, _, _, hsp, hm, hev⟩, hpv⟩ :=
    WP.preservedV (fn_ok (s := s) (base := s.gpr .x0) ⟨rfl, by rw [hwr]; simp, hnw⟩ ops hv) hkv
  refine ⟨t, s', he, ⟨fun r hr => hg r (fn_preserved r hr), hsp, hpv⟩, hev, ?_⟩
  intro i hi hp hown
  simp only [Spec.Ed25519.Point64.wsBytes, Spec.Ed25519.Point64.pAt, Spec.Ed25519.Point64.elemBytes,
    Spec.Ed25519.Point64.ownAt, Spec.Ed25519.Point64.ownEnd] at hi hp hown
  refine hm _ fun op hop => ?_
  rw [ofs_off' _ (by omega)]
  have := hout op hop
  simp only [offset]
  omega

theorem doubleRfcOps_vdst : ∀ r, ∀ i ∈ fieldCode doubleRfcOps, vdstOf i ≠ some r := by
  intro r i hi
  have h := List.all_eq_true.mp (by decide +kernel :
    (fieldCode doubleRfcOps).all (fun i => vdstOf i == none) = true) i hi
  rw [beq_iff_eq.mp h]; exact fun h' => nomatch h'

theorem addAffineOps_vdst : ∀ r, ∀ i ∈ fieldCode addAffineOps, vdstOf i ≠ some r := by
  intro r i hi
  have h := List.all_eq_true.mp (by decide +kernel :
    (fieldCode addAffineOps).all (fun i => vdstOf i == none) = true) i hi
  rw [beq_iff_eq.mp h]; exact fun h' => nomatch h'

theorem doubleFn_keepsV : doubleFn.allInstrs keepsV = true := by decide +kernel

theorem affFn_keepsV : affFn.allInstrs keepsV = true := by decide +kernel

/-- `PointIs` of slots 0–3. -/
theorem pointIs_of (m : Mem) (base : Addr) (r : Spec.Ed25519.Point)
    (h : point (env m base) 0 1 2 3 = r) : PointIs true m base pAt r := by
  have e := pointAt_eq m base 0 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at e
  show pointAt m base 64 = r
  rw [e]; exact h

/-- The doubling meets `doubleK`. -/
theorem double_correct (s : State) (hs : doubleK.pre s) :
    ∃ tr s', Exec isa doubleFn s tr s' ∧ abiPreserved s s' ∧ doubleK.post s s' := by
  obtain ⟨tr, s', he, ha, hv, hk⟩ :=
    fn_correct doubleRfcOps doubleRfcOps_vdst doubleFn_keepsV (by decide) s hs
  have hp := pointAt_eq s.mem (s.gpr .x0) 0 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at hp
  refine ⟨tr, s', he, ha, pointIs_of _ _ _ ?_, hk⟩
  rw [hv, doubleRfcOps_eval, show pAt = 64 from rfl, hp]; rfl

/-- The affine addition meets `affK`. -/
theorem aff_correct (s : State) (hs : affK.pre s) :
    ∃ tr s', Exec isa affFn s tr s' ∧ abiPreserved s s' ∧ affK.post s s' := by
  obtain ⟨tr, s', he, ha, hv, hk⟩ :=
    fn_correct addAffineOps addAffineOps_vdst affFn_keepsV (by decide) s hs
  have hp := pointAt_eq s.mem (s.gpr .x0) 0 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at hp
  refine ⟨tr, s', he, ha, fun q hz h4 h5 h6 => pointIs_of _ _ _ ?_, hk⟩
  rw [elemAt_eq] at h4 h5 h6
  rw [hv, addAffineOps_eval _ q hz h4 h5 h6, show pAt = 64 from rfl, hp]; rfl

/-! ## Constant time -/

theorem fnPub_agree (s₁ s₂ : State) (_ : fnPre s₁) (_ : fnPre s₂) (hp : fnPub s₁ s₂) :
    taint.Agree (Taint.ofRegs [.x0]) s₁ s₂ :=
  ⟨hp.2, fun r hr => by
    simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr; exact hp.1⟩

theorem doubleFn_ct : ConstantTime isa fnPre fnPub doubleFn :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0]) fnPub_agree (by taint_decide)

theorem affFn_ct : ConstantTime isa fnPre fnPub affFn :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0]) fnPub_agree (by taint_decide)

/-! ## The shared contracts -/

/-- A state satisfying the precondition: `ws` at `0x1000`, and the stack at `0x10000`. -/
def fnSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem doubleFn_verified :
    Verified AArch64.target doubleFn (Spec.Ed25519.Point64.doubleContract AArch64.abi true) :=
  Verified.of_correct double_correct doubleFn_ct (by
    sig_implies [Spec.Ed25519.Point64.doubleContract, Spec.Ed25519.Point64.sig, AArch64.abi,
      AArch64.argRegs, doubleK, fnPre, fnPub] [fnSat] using fnSat)

theorem affFn_verified :
    Verified AArch64.target affFn (Spec.Ed25519.Point64.addAffineContract AArch64.abi true) :=
  Verified.of_correct aff_correct affFn_ct (by
    sig_implies [Spec.Ed25519.Point64.addAffineContract, Spec.Ed25519.Point64.sig, AArch64.abi,
      AArch64.argRegs, affK, fnPre, fnPub] [fnSat] using fnSat)

end VG.Proof.Ed25519.AArch64.Point64
