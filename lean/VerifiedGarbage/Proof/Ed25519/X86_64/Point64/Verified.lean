import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Fn
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Ed25519's point functions on x86-64: their `Verified`

The facts of `Spec.Ed25519.Point64`'s contracts on x86-64 (`fnPre`: `ws` in
`rdi`), which the functions meet (`fn_correct`, from `fn_ok`): the callee-saved
registers are restored, and every byte they write is in slots 0–3 or 8–15,
which the return address is apart from; the spec's coordinates are the
slots' field elements (`elemAt_eq`). Constant time by taint tracking (only
`rsp` and `ws` are public, and every address is `ws` plus a constant), and a
state satisfying the precondition.
-/

namespace VG.Proof.Ed25519.X86_64.Point64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Point64 VG.Proof.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (clob ofs F fe)
open VG.Spec.Ed25519.Point64 (elemAt pointAt PointIs Keeps pAt qAt pointDouble)

variable {fld : Arith} [EdArith fld]

/-- The spec's coordinate at `o` is the field element there. -/
theorem elemAt_eq (m : Mem) (base : Addr) (o : Nat) : elemAt m base o = F m base o := by
  show Fin.ofNat _ (m.read (Mont.off base o) (8 * 4)).toNat = Proof.X25519.toFe (fe m base o)
  rw [Mont.read_eq_wordsVal]
  simp only [Mont.wordsVal, Proof.X25519.X86_64.fe, Proof.X25519.X86_64.val4, Proof.X25519.X86_64.word,
    Mont.word, Proof.X25519.X86_64.off, Mont.off, Nat.mul_zero, Nat.add_zero]
  congr 1
  grind

/-- The spec's point at slot `i` is the slots' point. -/
theorem pointAt_eq (m : Mem) (base : Addr) (i : Nat) (hi : i + 3 < 22) :
    pointAt m base (64 + 32 * i) =
      point (env m base) ⟨i, by omega⟩ ⟨i + 1, by omega⟩ ⟨i + 2, by omega⟩ ⟨i + 3, by omega⟩ := by
  simp only [pointAt, point, env, offset, elemAt_eq, Spec.Ed25519.Point64.elemBytes]
  congr 2 <;> omega

/-- `PointIs` from the slots' values. -/
theorem pointIs_of (ext : Bool) (m : Mem) (base : Addr) (r : Spec.Ed25519.Point)
    (h0 : env m base 0 = r.X) (h1 : env m base 1 = r.Y) (h2 : env m base 2 = r.Z)
    (h3 : ext = true → env m base 3 = r.T) : PointIs ext m base pAt r := by
  have e := pointAt_eq m base 0 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at e
  cases ext
  · refine ⟨?_, ?_, ?_⟩
    · exact (congrArg Spec.Ed25519.Point.X e).trans h0
    · exact (congrArg Spec.Ed25519.Point.Y e).trans h1
    · exact (congrArg Spec.Ed25519.Point.Z e).trans h2
  · show pointAt m base 64 = r
    rw [e]
    show (⟨env m base 0, env m base 1, env m base 2, env m base 3⟩ : Spec.Ed25519.Point) = r
    rw [h0, h1, h2, h3 rfl]

/-- The facts of the shared contracts about the state: `ws` in `rdi`, writable for its 8192
bytes, apart from the return address, and not wrapping around. -/
def fnPre (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨s.gpr .rdi, 8192⟩] ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 8192⟩ ∧
    (s.gpr .rdi).toNat + 8192 ≤ 2 ^ 64

/-- What every function's analysis may consider public. -/
def fnPub (s₁ s₂ : State) : Prop := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi

/-- The doubling's contract on x86-64. -/
def doubleK (ext : Bool) : Contract isa where
  pre := fnPre
  post s s' := PointIs ext s'.mem (s.gpr .rdi) pAt (pointDouble (pointAt s.mem (s.gpr .rdi) pAt)) ∧
    Keeps (s.gpr .rdi) s.mem s'.mem
  pub := fnPub

/-- The cached addition's contract on x86-64. -/
def addK (ext : Bool) : Contract isa where
  pre := fnPre
  post s s' := (∀ q, pointAt s.mem (s.gpr .rdi) qAt = Spec.Ed25519.Point64.cache q →
      PointIs ext s'.mem (s.gpr .rdi) pAt (Spec.Ed25519.pointAdd (pointAt s.mem (s.gpr .rdi) pAt) q)) ∧
    Keeps (s.gpr .rdi) s.mem s'.mem
  pub := fnPub

/-- The affine addition's contract on x86-64. -/
def addAffK : Contract isa where
  pre := fnPre
  post s s' := (∀ q : Spec.Ed25519.Point, q.Z = 1 →
      elemAt s.mem (s.gpr .rdi) qAt = q.Y - q.X →
      elemAt s.mem (s.gpr .rdi) (qAt + Spec.Ed25519.Point64.elemBytes) = q.Y + q.X →
      elemAt s.mem (s.gpr .rdi) (qAt + 2 * Spec.Ed25519.Point64.elemBytes) = q.T * 2 * Spec.Ed25519.d →
      PointIs true s'.mem (s.gpr .rdi) pAt (Spec.Ed25519.pointAdd (pointAt s.mem (s.gpr .rdi) pAt) q)) ∧
    Keeps (s.gpr .rdi) s.mem s'.mem
  pub := fnPub

/-- The program's results are in slots 0–3 or 8–15. -/
abbrev OutsOk (ops : List FieldOp) : Prop :=
  ∀ op ∈ ops, (64 ≤ offset op.out ∧ offset op.out + 32 ≤ 192) ∨
    (320 ≤ offset op.out ∧ offset op.out + 32 ≤ 576)

/-- A function running the field program `ops`: the calling convention kept, the slots' values
`evalOps ops` of theirs, and `Keeps`. -/
theorem fn_correct (ops : List FieldOp) (hk : ∀ r ∈ keptRegs, KeepReg.keeps r (fn fld ops) = true)
    (hmx : (fn fld ops).allInstrs (fun i => !loadsMxcsr i) = true) (hout : OutsOk ops)
    (s : State) (hs : fnPre s) :
    ∃ t s', Exec isa (fn fld ops) s t s' ∧ abiPreserved s s' ∧
      env s'.mem (s.gpr .rdi) = evalOps ops (env s.mem (s.gpr .rdi)) ∧ Keeps (s.gpr .rdi) s.mem s'.mem := by
  obtain ⟨hrd, hwr, hret, hnw⟩ := hs
  have hscr : Scratch s (s.gpr .rdi) := ⟨rfl, by rw [hwr]; simp, hnw⟩
  obtain ⟨t, s', he, hg, _, _, hv, hm⟩ := fn_ok hscr ops hk
  have outs : ∀ i, i < 8192 → (i < 64 ∨ 192 ≤ i) → (i < 320 ∨ 576 ≤ i) →
      Outs ops (s.gpr .rdi) (s.gpr .rdi + BitVec.ofNat 64 i) := by
    intro i hi h1 h2 op hop
    rw [VG.Proof.X25519.X86_64.ofs_off' _ (by omega)]
    have := hout op hop
    omega
  refine ⟨t, s', he, abiPreserved_of_exec hmx he ⟨fun r hr => hg r ?_, ?_⟩, hv, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · refine Mem.readW_congr fun i hi => hm _ fun op hop => ?_
    have hx := hret (s.gpr .rsp + BitVec.ofNat 64 i) (by
      simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)
    simp only [Region.Contains, Nat.not_le] at hx
    have := hout op hop
    simp only [ofs]; omega
  · intro i hi hp hown
    simp only [Spec.Ed25519.Point64.wsBytes, Spec.Ed25519.Point64.pAt, Spec.Ed25519.Point64.elemBytes,
      Spec.Ed25519.Point64.ownAt, Spec.Ed25519.Point64.ownEnd] at hi hp hown
    exact hm _ (outs i hi hp hown)

theorem dblOps_outs (t : Bool) : OutsOk (dblOps t) := by cases t <;> decide

theorem addCachedOps_outs (t : Bool) : OutsOk (addCachedOps t) := by cases t <;> decide

/-- The doubling meets `doubleK`. -/
theorem double_correct (t : Bool) (hk : ∀ r ∈ keptRegs, KeepReg.keeps r (doubleFn fld t) = true)
    (hmx : (doubleFn fld t).allInstrs (fun i => !loadsMxcsr i) = true) (s : State) (hs : (doubleK t).pre s) :
    ∃ tr s', Exec isa (doubleFn fld t) s tr s' ∧ abiPreserved s s' ∧ (doubleK t).post s s' := by
  obtain ⟨tr, s', he, ha, hv, hk'⟩ := fn_correct (dblOps t) hk hmx (dblOps_outs t) s hs
  obtain ⟨e0, e1, e2, e3⟩ := dblOps_eval (env s.mem (s.gpr .rdi)) t
  have hp := pointAt_eq s.mem (s.gpr .rdi) 0 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at hp
  refine ⟨tr, s', he, ha, pointIs_of t _ _ _ ?_ ?_ ?_ ?_, hk'⟩
  · rw [hv, e0, show pAt = 64 from rfl, hp]; rfl
  · rw [hv, e1, show pAt = 64 from rfl, hp]; rfl
  · rw [hv, e2, show pAt = 64 from rfl, hp]; rfl
  · intro ht; rw [hv, e3 ht, show pAt = 64 from rfl, hp]; rfl

/-- The cached addition meets `addK`. -/
theorem add_correct (t : Bool) (hk : ∀ r ∈ keptRegs, KeepReg.keeps r (addFn fld t) = true)
    (hmx : (addFn fld t).allInstrs (fun i => !loadsMxcsr i) = true) (s : State) (hs : (addK t).pre s) :
    ∃ tr s', Exec isa (addFn fld t) s tr s' ∧ abiPreserved s s' ∧ (addK t).post s s' := by
  obtain ⟨tr, s', he, ha, hv, hk'⟩ := fn_correct (addCachedOps t) hk hmx (addCachedOps_outs t) s hs
  have hp := pointAt_eq s.mem (s.gpr .rdi) 0 (by decide)
  have hq := pointAt_eq s.mem (s.gpr .rdi) 4 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at hp
  refine ⟨tr, s', he, ha, fun q hcq => ?_, hk'⟩
  rw [show qAt = 64 + 32 * 4 from rfl, hq] at hcq
  obtain ⟨e0, e1, e2, e3⟩ := addCachedOps_eval (env s.mem (s.gpr .rdi)) t q hcq
  refine pointIs_of t _ _ _ ?_ ?_ ?_ ?_
  · rw [hv, e0, show pAt = 64 from rfl, hp]; rfl
  · rw [hv, e1, show pAt = 64 from rfl, hp]; rfl
  · rw [hv, e2, show pAt = 64 from rfl, hp]; rfl
  · intro ht; rw [hv, e3 ht, show pAt = 64 from rfl, hp]; rfl

theorem pointAddAffineOps_outs : OutsOk pointAddAffineOps := by decide

/-- The affine addition meets `addAffK`. -/
theorem addAffine_correct (hk : ∀ r ∈ keptRegs, KeepReg.keeps r (addAffineFn fld) = true)
    (hmx : (addAffineFn fld).allInstrs (fun i => !loadsMxcsr i) = true) (s : State) (hs : addAffK.pre s) :
    ∃ tr s', Exec isa (addAffineFn fld) s tr s' ∧ abiPreserved s s' ∧ addAffK.post s s' := by
  obtain ⟨tr, s', he, ha, hv, hk'⟩ := fn_correct pointAddAffineOps hk hmx pointAddAffineOps_outs s hs
  have hp := pointAt_eq s.mem (s.gpr .rdi) 0 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at hp
  refine ⟨tr, s', he, ha, fun q hz h4 h5 h6 => ?_, hk'⟩
  rw [elemAt_eq] at h4 h5 h6
  have h4' : env s.mem (s.gpr .rdi) 4 = q.Y - q.X := h4
  have h5' : env s.mem (s.gpr .rdi) 5 = q.Y + q.X := h5
  have h6' : env s.mem (s.gpr .rdi) 6 = q.T * 2 * Spec.Ed25519.d := h6
  have h7 : q.Z * 2 = 2 := by rw [hz]; grind
  have hq : (⟨env s.mem (s.gpr .rdi) 4, env s.mem (s.gpr .rdi) 5, env s.mem (s.gpr .rdi) 6, 2⟩ :
      Spec.Ed25519.Point) = cache q := by
    simp only [cache]; rw [h4', h5', h6', h7]
  have e := pointAddAffine_eval (env s.mem (s.gpr .rdi)) q hq
  refine pointIs_of true _ _ _ ?_ ?_ ?_ ?_
  · rw [hv, show pAt = 64 from rfl, hp]; exact congrArg Spec.Ed25519.Point.X e
  · rw [hv, show pAt = 64 from rfl, hp]; exact congrArg Spec.Ed25519.Point.Y e
  · rw [hv, show pAt = 64 from rfl, hp]; exact congrArg Spec.Ed25519.Point.Z e
  · intro _; rw [hv, show pAt = 64 from rfl, hp]; exact congrArg Spec.Ed25519.Point.T e

/-! ## Constant time -/

theorem fnPub_agree {s₁ s₂ : State} (hp : fnPub s₁ s₂) :
    VG.X86_64.Taint.Agree (Taint.ofRegs [.rdi, .rsp]) s₁ s₂ := by
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.2
  · exact hp.1

/-! ## The shared contracts -/

/-- A state satisfying the precondition. -/
def fnSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem doubleK_implies (ext : Bool) :
    (doubleK ext).Implies (Spec.Ed25519.Point64.doubleContract X86_64.abi ext) := by
  cases ext <;>
  sig_implies [Spec.Ed25519.Point64.doubleContract, Spec.Ed25519.Point64.sig, X86_64.abi, X86_64.argRegs,
    doubleK, fnPre, fnPub] [fnSat] using fnSat

theorem addK_implies (ext : Bool) :
    (addK ext).Implies (Spec.Ed25519.Point64.addCachedContract X86_64.abi ext) := by
  cases ext <;>
  sig_implies [Spec.Ed25519.Point64.addCachedContract, Spec.Ed25519.Point64.sig, X86_64.abi, X86_64.argRegs,
    addK, fnPre, fnPub] [fnSat] using fnSat

theorem addAffK_implies : addAffK.Implies (Spec.Ed25519.Point64.addAffineContract X86_64.abi true) := by
  sig_implies [Spec.Ed25519.Point64.addAffineContract, Spec.Ed25519.Point64.sig, X86_64.abi, X86_64.argRegs,
    addAffK, fnPre, fnPub] [fnSat] using fnSat

end VG.Proof.Ed25519.X86_64.Point64
