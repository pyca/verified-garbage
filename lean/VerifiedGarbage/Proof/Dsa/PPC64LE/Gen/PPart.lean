module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.PAttempt
public import VerifiedGarbage.Proof.Dsa.Generation.Search
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on PPC64LE: the search for p

`pAdvance_vp`: the next counter; `pCont_vp` and `pExit_vp`: the code after a
candidate (`pTail`), which goes on to the next counter, or ends the search;
the definitions of the search's stages, as `Spec.Dsa.primeFromSeed` searches
the counters (`pSpec`, `pCount`, `pU`, `pFin`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-- A stage's pure facts, as hypotheses. -/
theorem VP.intro {P : Prop} {F Q : State → State → Prop} {c : Prog isa} (h : P → VP F c Q) :
    VP (fun σ s => P ∧ F σ s) c Q := by
  by_cases hp : P
  · exact (h hp).mono (fun σ s h => h.2) fun _ _ h => h
  · exact VP.of_false fun σ s h => hp h.1

section
variable {G : GP} {X : State → Prop}

/-- `r := r + i`, for a register both runs know. -/
theorem addi_vp {P : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → St G (c σ) X σ s) {r : Reg}
    (hr : r ≠ .r0) (h28 : r ≠ .r28) {v i : Nat} (hi : i < 2 ^ 15) :
    VP (fun σ s => P σ s ∧ s.gpr r = BitVec.ofNat 64 v) (.block [.addi r r i])
      (fun σ s => St G (c σ) X σ s ∧ s.gpr r = BitVec.ofNat 64 (v + i)) := by
  refine VP.pub (SS.pub (c := c) fun σ s h => (hF σ s h.1).1) [r] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
      (Taint.ofRegs [.r28, r]) (.block [.addi r r i]), rfl⟩ (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2])
    fun σ s ⟨h, e⟩ => ?_
  have h' := hF σ s h
  refine WP.wr (exec_addi hr hi) fun t u sp _ => WP.block_nil ⟨⟨h'.1.of_upd u sp h28, h'.2⟩, ?_⟩
  rw [u.gpr, e, BitVec.ofNat_add]

/-- The next counter: `fCounter` + 1, `fOffset` + `C`, and `r0 = 0` when the
counter reaches `32 pLen` (`4 L`). -/
theorem pAdvance_vp {d : Cfg} {j off C : Nat} (hC : C < 2 ^ 15) (hCt : fCounter ∈ d.LS)
    (hCv : d.V fCounter = BitVec.ofNat 64 j) (hOf : fOffset ∈ d.LS) (hOv : d.V fOffset = BitVec.ofNat 64 off)
    (hj : j + 1 < 2 ^ 32) :
    VP (St G d X) (.block [ld .r3 fCounter, .addi .r3 .r3 1, st .r3 fCounter, ld .r4 fOffset,
        .addi .r4 .r4 C, st .r4 fOffset, .subi .r0 .r3 (32 * G.pLen)])
      (fun σ s => St G ((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset (BitVec.ofNat 64 (off + C))) X σ s ∧
        isa.eval (.zero .d .r0) s = some (decide (j + 1 = 32 * G.pLen))) := by
  show VP _ (.block ([ld .r3 fCounter] ++ ([.addi .r3 .r3 1] ++ ([st .r3 fCounter] ++ ([ld .r4 fOffset] ++
    ([.addi .r4 .r4 C] ++ ([st .r4 fOffset] ++ [.subi .r0 .r3 (32 * G.pLen)]))))))) _
  -- The counter.
  refine VP.block_append (G := fun σ s => St G d X σ s ∧ s.gpr .r3 = BitVec.ofNat 64 j)
    (ld_vp (c := fun _ => d) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV hCt).trans hCv) fun σ s t ⟨_, x⟩ h' u => ⟨⟨h', x⟩, u.gpr⟩) ?_
  refine VP.block_append (G := fun σ s => St G d X σ s ∧ s.gpr .r3 = BitVec.ofNat 64 (j + 1))
    (addi_vp (c := fun _ => d) (fun σ s h => h) (by decide) (by decide) (by decide)) ?_
  have d1O : fOffset ∈ (d.setV fCounter (BitVec.ofNat 64 (j + 1))).LS := List.mem_cons_of_mem _ hOf
  refine VP.block_append (G := fun σ s => St G (d.setV fCounter (BitVec.ofNat 64 (j + 1))) X σ s ∧
      s.gpr .r3 = BitVec.ofNat 64 (j + 1))
    (st_vp (c := fun _ => d) (fun σ s h => h.1.1) (varOk_of (by decide))
      fun σ s t ⟨⟨_, x⟩, r3⟩ h' K => ⟨⟨r3 ▸ h', x⟩, by rw [K.gpr (by decide), r3]⟩) ?_
  -- The offset.
  refine VP.block_append (G := fun σ s => (St G (d.setV fCounter (BitVec.ofNat 64 (j + 1))) X σ s ∧
      s.gpr .r3 = BitVec.ofNat 64 (j + 1)) ∧ s.gpr .r4 = BitVec.ofNat 64 off)
    (ld_vp (c := fun _ => d.setV fCounter (BitVec.ofNat 64 (j + 1))) (fun σ s h => h.1.1) (by decide) (by decide)
      (by decide) (fun σ s h => (h.1.1.gi.slotV d1O).trans (by
        show upd d.V fCounter (BitVec.ofNat 64 (j + 1)) fOffset = _; rw [upd_ne _ _ (by decide)]; exact hOv))
      fun σ s t ⟨⟨_, x⟩, r3⟩ h' u => ⟨⟨⟨h', x⟩, by rw [u.other _ (by decide), r3]⟩, u.gpr⟩) ?_
  refine VP.block_append (G := fun σ s => (St G (d.setV fCounter (BitVec.ofNat 64 (j + 1))) X σ s ∧
      s.gpr .r3 = BitVec.ofNat 64 (j + 1)) ∧ s.gpr .r4 = BitVec.ofNat 64 (off + C))
    (VP.pub (SS.pub (c := fun _ => d.setV fCounter (BitVec.ofNat 64 (j + 1))) fun σ s h => h.1.1.1) [.r4]
      ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r4]) (.block [.addi .r4 .r4 C]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]) fun σ s ⟨⟨⟨h, x⟩, r3⟩, r4⟩ =>
        WP.wr (exec_addi (by decide) hC) fun t u sp _ => WP.block_nil
          ⟨⟨⟨h.of_upd u sp (by decide), x⟩, by rw [u.other _ (by decide), r3]⟩, by
            rw [u.gpr, r4, BitVec.ofNat_add]⟩) ?_
  refine VP.block_append (G := fun σ s => St G ((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
      (BitVec.ofNat 64 (off + C))) X σ s ∧ s.gpr .r3 = BitVec.ofNat 64 (j + 1))
    (st_vp (c := fun _ => d.setV fCounter (BitVec.ofNat 64 (j + 1))) (fun σ s h => h.1.1.1)
      (varOk_of (by decide))
      fun σ s t ⟨⟨⟨_, x⟩, r3⟩, r4⟩ h' K => ⟨⟨r4 ▸ h', x⟩, by rw [K.gpr (by decide), r3]⟩) ?_
  -- The end of the counters.
  refine VP.pub (SS.pub (c := fun _ => (d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
      (BitVec.ofNat 64 (off + C))) fun σ s h => h.1.1) [.r3] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
      (Taint.ofRegs [.r28, .r3]) (.block [.subi .r0 .r3 (32 * G.pLen)]), rfl⟩
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]) fun σ s ⟨⟨h, x⟩, r3⟩ => ?_
  have l := h.lens
  have h15 : 32 * G.pLen ≤ 2 ^ 15 := by rcases l with e | e | e <;> rw [e] <;> decide
  refine WP.wr (exec_subi (by decide) h15) fun t u sp _ => WP.block_nil ⟨⟨h.of_upd u sp (by decide), x⟩, ?_⟩
  rw [eval_zero, u.gpr, r3, sub_beq_zero]
  congr 1
  by_cases e : j + 1 = 32 * G.pLen
  · simp [e]
  · simp only [e, decide_false]
    refine beq_false_of_ne fun h' => e ?_
    have := congrArg BitVec.toNat h'; simp only [BitVec.toNat_ofNat] at this; omega

/-- The code after a candidate. -/
abbrev pTail (C : Nat) (L : Nat) : Prog isa :=
  .seq (.block (cmpF fP 4)) (.seq (.ite (.zero .d .r0) (.seq (.block [ld .r3 fCounter, .addi .r3 .r3 1,
      st .r3 fCounter, ld .r4 fOffset, .addi .r4 .r4 C, st .r4 fOffset, .subi .r0 .r3 (32 * L)])
    (.ite (.zero .d .r0) (.block (stImm fP 2)) (.block []))) (.block [])) (.block (cmpF fP 4)))

theorem ofNat64_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a = b) := by
  by_cases e : a = b
  · subst e; simp
  · simp only [e, decide_false]
    refine beq_false_of_ne fun h' => e ?_
    have := congrArg BitVec.toNat h'; simp only [BitVec.toNat_ofNat] at this; omega

/-- After a candidate that is not p: the next counter, or `fP` := 2 after the last. -/
theorem pCont_vp {d : Cfg} {j off C : Nat} (hC : C < 2 ^ 15) (hP : fP ∈ d.LS)
    (hPv : d.V fP = BitVec.ofNat 64 4) (hCt : fCounter ∈ d.LS) (hCv : d.V fCounter = BitVec.ofNat 64 j)
    (hOf : fOffset ∈ d.LS) (hOv : d.V fOffset = BitVec.ofNat 64 off) (hj : j + 1 < 2 ^ 32) :
    VP (St G d X) (pTail C G.pLen)
      (fun σ s => if j + 1 = 32 * G.pLen then
          St G (((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset (BitVec.ofNat 64 (off + C))).setV fP
            (BitVec.ofNat 64 2)) X σ s ∧ isa.eval (.zero .d .r0) s = some false
        else St G ((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset (BitVec.ofNat 64 (off + C))) X σ s ∧
          isa.eval (.zero .d .r0) s = some true) := by
  refine VP.seq (G := fun σ s => St G d X σ s ∧ isa.eval (.zero .d .r0) s = some true)
    (cmpF_vp (c := fun _ => d) (x := BitVec.ofNat 64 4) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV hP).trans hPv) fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩) ?_
  by_cases e : j + 1 = 32 * G.pLen
  · refine VP.mono (G := fun σ s => St G (((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
        (BitVec.ofNat 64 (off + C))).setV fP (BitVec.ofNat 64 2)) X σ s ∧ isa.eval (.zero .d .r0) s = some false) ?_
      (fun _ _ h => h) fun σ s h => by rw [ite_eq_left_of_eq_true _ _ (eq_true e)]; exact h
    refine VP.seq (G := St G (((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
        (BitVec.ofNat 64 (off + C))).setV fP (BitVec.ofNat 64 2)) X) (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
        rw [h₁.2, h₂.2]) (VP.seq ((pAdvance_vp hC hCt hCv hOf hOv hj).mono (fun σ s h => h.1.1) fun _ _ h => h)
          (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
            (stImm_vp (c := fun _ => (d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
              (BitVec.ofNat 64 (off + C))) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
              fun σ s t h h' _ => ⟨h', h.1.1.2⟩)
            (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp [e] at z)))
        (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp at z)) ?_
    exact cmpF_vp (x := BitVec.ofNat 64 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp))
      fun σ s t ⟨_, x⟩ h' _ e' => ⟨⟨h', x⟩, by rw [e']; rfl⟩
  · refine VP.mono (G := fun σ s => St G ((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
        (BitVec.ofNat 64 (off + C))) X σ s ∧ isa.eval (.zero .d .r0) s = some true) ?_
      (fun _ _ h => h) fun σ s h => by rw [ite_eq_right_of_eq_false _ _ (eq_false e)]; exact h
    refine VP.seq (G := St G ((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
        (BitVec.ofNat 64 (off + C))) X) (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
        rw [h₁.2, h₂.2]) (VP.seq ((pAdvance_vp hC hCt hCv hOf hOv hj).mono (fun σ s h => h.1.1) fun _ _ h => h)
          (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
            (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp [e] at z)
            (VP.block_nil fun σ s h => h.1.1)))
        (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp at z)) ?_
    exact cmpF_vp (x := BitVec.ofNat 64 4) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV (by simp [hP])).trans (by
        show upd (upd d.V fCounter (BitVec.ofNat 64 (j + 1))) fOffset (BitVec.ofNat 64 (off + C)) fP = _
        rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact hPv))
      fun σ s t ⟨_, x⟩ h' _ e' => ⟨⟨h', x⟩, by rw [e']; rfl⟩

/-- After a candidate that ends the search (`fP` := 0 or 1). -/
theorem pExit_vp {d : Cfg} {v C : Nat} (hP : fP ∈ d.LS) (hPv : d.V fP = BitVec.ofNat 64 v) (hv : v < 4) :
    VP (St G d X) (pTail C G.pLen) (fun σ s => St G d X σ s ∧ isa.eval (.zero .d .r0) s = some false) := by
  have ne : (BitVec.ofNat 64 v == BitVec.ofNat 64 4) = false := by
    rw [ofNat64_beq (by omega) (by decide)]; simp; omega
  refine VP.seq (G := fun σ s => St G d X σ s ∧ isa.eval (.zero .d .r0) s = some false)
    (cmpF_vp (c := fun _ => d) (x := BitVec.ofNat 64 v) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV hP).trans hPv) fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e, ne]⟩) ?_
  refine VP.seq (G := St G d X) (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
    (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp at z) (VP.block_nil fun σ s h => h.1.1)) ?_
  exact cmpF_vp (c := fun _ => d) (x := BitVec.ofNat 64 v) (fun σ s h => h.1) (by decide) (by decide) (by decide)
    (fun σ s h => (h.1.gi.slotV hP).trans hPv) fun σ s t h h' _ e => ⟨⟨h', h.2⟩, by rw [e, ne]⟩

end

section
variable {Gh : Hash}

/-- Counter `j`'s candidate. -/
abbrev pCand (HO : HashOk Gh) (G : GP) (k j : Nat) : Nat :=
  pVal (Spec.Dsa.decodeBE (xBytes HO G k (1 + j * (cnt G + 1)))) (Spec.Dsa.decodeBE (qBytes G k))

/-- Whether counter `j`'s candidate is too short to test. -/
abbrev pShort (HO : HashOk Gh) (G : GP) (k j : Nat) : Prop := pCand HO G k j < 2 ^ (8 * G.pLen - 1)

/-- The witnesses read before counter `j`. -/
def pU (HO : HashOk Gh) (G : GP) (k u0 : Nat) : Nat → Nat
  | 0 => u0
  | j + 1 => if pShort HO G k j then pU HO G k u0 j else
      match Spec.Dsa.probablePrime (pCand HO G k j) (G.witB.drop (pU HO G k u0 j)) with
      | some (_, r) => G.witLen - r.length
      | none => pU HO G k u0 j

/-- The search's iterations from counter `j`, with `m` counters after it. -/
def pCount (HO : HashOk Gh) (G : GP) (k u0 : Nat) : Nat → Nat → Nat
  | 0, j => j + 1
  | m + 1, j => if pShort HO G k j then pCount HO G k u0 m (j + 1) else
      match Spec.Dsa.probablePrime (pCand HO G k j) (G.witB.drop (pU HO G k u0 j)) with
      | some (false, _) => pCount HO G k u0 m (j + 1)
      | _ => j + 1

theorem pCount_gt (HO : HashOk Gh) (G : GP) (k u0 : Nat) : ∀ m j, j < pCount HO G k u0 m j
  | 0, j => by simp [pCount]
  | m + 1, j => by
    have := pCount_gt HO G k u0 m (j + 1)
    simp only [pCount]; split
    · omega
    · split <;> omega

/-- The search's header words at counter `j`, with `u` witnesses read. -/
abbrev pBase (c : Cfg) (HO : HashOk Gh) (G : GP) (k : Nat) : Cfg :=
  { c with
    cl := [(sMsg + G.qLen, padTail HO.md G.qLen), (pStart G 0, []), (sQ, qBytes G k)]
    live := []
    kls := [] }

abbrev pCfgJ (c : Cfg) (HO : HashOk Gh) (G : GP) (k j u : Nat) : Cfg :=
  ((((pBase c HO G k).setV fUsed (BitVec.ofNat 64 u)).setV fCounter (BitVec.ofNat 64 j)).setV fOffset
    (BitVec.ofNat 64 (1 + j * (cnt G + 1)))).setV fP (BitVec.ofNat 64 4)

/-- The spec's search from counter `j`. -/
abbrev pSpec (HO : HashOk Gh) (G : GP) (k u0 j : Nat) : Option (Option Nat × Spec.RsaKeyGen.Rand) :=
  VG.Proof.Dsa.Generation.primeSearch (8 * G.pLen) (8 * G.qLen) (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k) j
    (G.witB.drop (pU HO G k u0 j))

/-- The arrays of p. -/
abbrev pAp (p q : Nat) : Nat → Nat := KU (KU (KU (KU (fun _ => 0) aOne 1) aPm1 (p - 1)) aE ((p - 1) / q)) aP p

/-- The stage after the search. -/
abbrev pFound (c : Cfg) (HO : HashOk Gh) (G : GP) (k p : Nat) : Cfg :=
  { c with
    cl := (sE, Spec.Rsa.i2osp ((p - 1) / Spec.Dsa.decodeBE (qBytes G k)) (eBytes G.pLen G.qLen)) ::
      (sPBE, Spec.Rsa.i2osp p G.pLen) :: pRest HO.md G k
    A := pAp p (Spec.Dsa.decodeBE (qBytes G k))
    live := [aE, aP, aPm1, aOne, aZero]
    kls := [] }

abbrev pNone (c : Cfg) (HO : HashOk Gh) (G : GP) : Cfg :=
  { c with
    cl := [(sMsg + G.qLen, padTail HO.md G.qLen)]
    live := []
    kls := [] }

def pFin (c : Cfg) (HO : HashOk Gh) (G : GP) (k : Nat) : Option (Option Nat × Spec.RsaKeyGen.Rand) → Cfg
  | some (some p, rest) =>
    ((pFound c HO G k p).setV fUsed (BitVec.ofNat 64 (G.witLen - rest.length))).setV fP (BitVec.ofNat 64 1)
  | some (none, r) => ((pNone c HO G).setV fUsed (BitVec.ofNat 64 (G.witLen - r.length))).setV fP (BitVec.ofNat 64 2)
  | none => (pNone c HO G).setV fP (BitVec.ofNat 64 0)

/-- The search with `r` iterations left of `N`. -/
abbrev pInv (c : Cfg) (HO : HashOk Gh) (G : GP) (k u0 N : Nat) (X : State → Prop) (r : Nat) (σ s : State) : Prop :=
  (r ≤ N ∧ N - r < 32 * G.pLen ∧ pCount HO G k u0 (32 * G.pLen - 1 - (N - r)) (N - r) = N ∧
    pSpec HO G k u0 (N - r) = pSpec HO G k u0 0 ∧ pU HO G k u0 (N - r) ≤ G.witLen) ∧
    St G (pCfgJ c HO G k (N - r) (pU HO G k u0 (N - r))) X σ s

/-- The words the search keeps apart from `c`'s. -/
abbrev PNot (c : Cfg) : Prop :=
  fUsed ∉ c.LS ∧ fCounter ∉ c.LS ∧ fOffset ∉ c.LS ∧ fP ∉ c.LS ∧ fRes ∉ c.LS ∧ fUsedOut ∉ c.LS ∧
    ∀ o ∈ c.LS, fUsedOut + 8 ≤ o ∨ o + 8 ≤ fUsedOut

theorem PNot.ne {c : Cfg} (h : PNot c) {o : Nat} (ho : o ∈ c.LS) :
    o ≠ fUsed ∧ o ≠ fCounter ∧ o ≠ fOffset ∧ o ≠ fP ∧ o ≠ fRes :=
  ⟨fun e => h.1 (e ▸ ho), fun e => h.2.1 (e ▸ ho), fun e => h.2.2.1 (e ▸ ho), fun e => h.2.2.2.1 (e ▸ ho),
    fun e => h.2.2.2.2.1 (e ▸ ho)⟩

/-- A stage's words agree with the search's at counter `j`. -/
theorem pCfgJ_V {c : Cfg} (hn : PNot c) {HO : HashOk Gh} {G : GP} {k j u : Nat} {LS : List Nat}
    {V : Nat → BitVec 64} (hLS : ∀ o ∈ c.LS, o ∈ LS) (h1 : fP ∈ LS) (h2 : fOffset ∈ LS) (h3 : fCounter ∈ LS)
    (h4 : fUsed ∈ LS) (vP : V fP = BitVec.ofNat 64 4) (vO : V fOffset = BitVec.ofNat 64 (1 + j * (cnt G + 1)))
    (vC : V fCounter = BitVec.ofNat 64 j) (vU : V fUsed = BitVec.ofNat 64 u) (vc : ∀ o ∈ c.LS, V o = c.V o) :
    ∀ o ∈ (pCfgJ c HO G k j u).LS, o ∈ LS ∧ V o = (pCfgJ c HO G k j u).V o := by
  intro o ho
  change o ∈ fP :: fOffset :: fCounter :: fUsed :: c.LS at ho
  simp only [List.mem_cons] at ho
  rcases ho with rfl | rfl | rfl | rfl | ho
  · exact ⟨h1, by rw [vP]; simp [upd]⟩
  · exact ⟨h2, by rw [vO]; simp [upd, fOffset, fP]⟩
  · exact ⟨h3, by rw [vC]; simp [upd, fCounter, fOffset, fP]⟩
  · exact ⟨h4, by rw [vU]; simp [upd, fUsed, fCounter, fOffset, fP]⟩
  · obtain ⟨n1, n2, n3, n4, -⟩ := hn.ne ho
    exact ⟨hLS o ho, by rw [vc o ho]; simp [upd, n1, n2, n3, n4]⟩

end

end VG.Proof.Dsa.PPC64LE.Gen
