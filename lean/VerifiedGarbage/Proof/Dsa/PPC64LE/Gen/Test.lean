module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.PrimeCall
public import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on PPC64LE: a probable-prime test (`test_vp`)

`test pLen c src n name code` copies the candidate to byte `c` of the
working space of the functions we call and tests it with the witnesses from
`fUsed` on: `fRes` := its status, and `fUsed` := the witnesses it read when
the tape sufficed (`testCfg`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-- A stage: a state of the search with the contents `c`, and `X` of the run. -/
abbrev St (G : GP) (c : Cfg) (X : State → Prop) (σ s : State) : Prop := SS G 176 σ c s ∧ X σ

/-- The stage after a test, from its result `res`. -/
def testCfg (c : Cfg) (cl : Claims) (witLen : Nat) : Option (Bool × Spec.RsaKeyGen.Rand) → Cfg
  | none => { c with cl := cl }.setV fRes 0
  | some (b, rest) => ({ c with cl := cl }.setV fRes (BitVec.ofNat 64 (if b then 1 else 2))).setV fUsed
      (BitVec.ofNat 64 (witLen - rest.length))

section
variable {G : GP} {c : Cfg} {X : State → Prop}

theorem varOk_of {o : Nat} (h : o + 8 ≤ fSave ∧ o % 8 = 0 ∧ o ≠ fLR ∧ o ∉ [fOut, fWit, fWitLen, fHs, fHsLen]) :
    VarOk G o := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun p hp e => h.2.2.2 ?_⟩
  simp only [fixedWords, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp [e]

theorem varOk_fRes : VarOk G fRes := varOk_of (by decide)
theorem varOk_fUsed : VarOk G fUsed := varOk_of (by decide)
theorem varOk_fUsedOut : VarOk G fUsedOut := varOk_of (by decide)

/-! ## The arguments -/

/-- `r3`–`r7`, the test's arguments, from the header. -/
theorem targs_vp {u : Nat} (hu : u ≤ G.witLen) (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 64 u) :
    VP (St G c X) (.seq (.block [scr .r3 (wB G.pLen), .li .r4 (wWords G.pLen), ld .r9 fUsed, ld .r5 fWit,
        ld .r6 fWitLen, .add .r5 .r5 .r9, .sub .r6 .r6 .r9, scr .r7 fUsedOut])
        (.ite (.zero .d .r6) (.block [ld .r5 fWit]) (.block [])))
      (fun σ s => St G c X σ s ∧ TArgs G u s) := by
  let M : State → State → Prop := fun σ s => St G c X σ s ∧ s.gpr .r3 = G.sa (wB G.pLen) ∧
    s.gpr .r4 = BitVec.ofNat 64 (wWords G.pLen) ∧ s.gpr .r5 = G.wit + BitVec.ofNat 64 u ∧
    s.gpr .r6 = BitVec.ofNat 64 (G.witLen - u) ∧ s.gpr .r7 = G.sa fUsedOut
  refine VP.seq (G := M) (VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1) []
    ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block [scr .r3 (wB 128), .li .r4 (wWords 128),
      ld .r9 fUsed, ld .r5 fWit, ld .r6 fWitLen, .add .r5 .r5 .r9, .sub .r6 .r6 .r9, scr .r7 fUsedOut]), rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_) ?_
  · have gi := h.gi
    have lens := gi.lens3
    have wl := gi.witLt
    have wBl : wB G.pLen < 2 ^ 15 := by rcases lens with e | e | e <;> rw [e] <;> decide
    refine WP.sp_eq ?_
    refine WP.wr (exec_addi (by decide) wBl) fun s₁ u₁ sp₁ _ => ?_
    have h₁ := h.of_upd u₁ sp₁ (by decide)
    refine WP.wr (exec_li (wWords_lt lens)) fun s₂ u₂ sp₂ _ => ?_
    have h₂ := h₁.of_upd u₂ sp₂ (by decide)
    refine h₂.ldK (o := fUsed) (by decide) (by decide) ((h₂.gi.slotV hU).trans hUv) (by decide) fun s₃ h₃ u₃ => ?_
    refine h₃.ldK (o := fWit) (by decide) (by decide) (h₃.gi.fixedV (v := G.wit) (by simp [fixedWords])) (by decide)
      fun s₄ h₄ u₄ => ?_
    refine h₄.ldK (o := fWitLen) (by decide) (by decide)
      (h₄.gi.fixedV (v := BitVec.ofNat 64 G.witLen) (by simp [fixedWords])) (by decide)
      fun s₅ h₅ u₅ => ?_
    refine WP.wr exec_add fun s₆ u₆ sp₆ _ => ?_
    have h₆ := h₅.of_upd u₆ sp₆ (by decide)
    refine WP.wr exec_sub fun s₇ u₇ sp₇ _ => ?_
    have h₇ := h₆.of_upd u₇ sp₇ (by decide)
    refine WP.wr (exec_addi (by decide) (by decide)) fun s₈ u₈ sp₈ _ => WP.block_nil fun _ => ?_
    have h₈ := h₇.of_upd u₈ sp₈ (by decide)
    refine ⟨⟨h₈, x⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, gi.r28]
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
    · rw [u₈.other .r5 (by decide), u₇.other .r5 (by decide), u₆.gpr, u₅.other .r5 (by decide),
        u₅.other .r9 (by decide), u₄.gpr, u₄.other .r9 (by decide), u₃.gpr]
    · rw [u₈.other .r6 (by decide), u₇.gpr, u₆.other .r6 (by decide), u₆.other .r9 (by decide), u₅.gpr,
        u₅.other .r9 (by decide), u₄.other .r9 (by decide), u₃.gpr, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega)
        (by omega)]
    · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), gi.r28]
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2.2.2.2.1, h₂.2.2.2.2.1]) ?_ ?_
  · refine VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1.1.1) []
      ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block [ld .r5 fWit]), rfl⟩
      (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨⟨⟨h, x⟩, r3, r4, r5, r6, r7⟩, e⟩ => ?_
    have wl := h.gi.witLt
    rw [eval_zero, r6, ofNat_beq_zero (by omega)] at e
    have hu' : u = G.witLen := by simp at e; omega
    refine WP.sp_eq (h.ldK (o := fWit) (by decide) (by decide) (h.gi.fixedV (v := G.wit) (by simp [fixedWords]))
      (by decide) fun t ht ut => WP.block_nil fun sp => ⟨⟨ht, x⟩, ?_, ?_, ?_, ?_, ?_⟩)
    · rw [ut.other _ (by decide), r3]
    · rw [ut.other _ (by decide), r4]
    · rw [ut.gpr, GP.randP, ite_eq_left hu']
    · rw [ut.other _ (by decide), r6]
    · rw [ut.other _ (by decide), r7]
  · refine VP.block_nil fun σ s ⟨⟨hx, r3, r4, r5, r6, r7⟩, e⟩ => ⟨hx, r3, r4, ?_, r6, r7⟩
    have wl := hx.1.gi.witLt
    rw [eval_zero, r6, ofNat_beq_zero (by omega)] at e
    have hu' : u ≠ G.witLen := by simp at e; omega
    rw [r5, GP.randP, ite_eq_right hu']

end

end VG.Proof.Dsa.PPC64LE.Gen
