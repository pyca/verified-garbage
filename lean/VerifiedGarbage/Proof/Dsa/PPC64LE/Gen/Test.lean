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

/-! ## The call -/

/-- After the call: the count's word known when the tape sufficed. -/
def callCfg (c : Cfg) (cl : Claims) (witLen u : Nat) : Option (Bool × Spec.RsaKeyGen.Rand) → Cfg
  | none => { c with cl := cl }
  | some (_, rest) => { c with cl := cl }.setV fUsedOut (BitVec.ofNat 64 (witLen - u - rest.length))

/-- One more known header word. -/
theorem GI.addSlot {STK : Nat} {σ t : State} {V : Nat → BitVec 64} {LS : List Nat} (h : GI G STK σ V LS t) {o : Nat}
    (ho : VarOk G o) {v : BitVec 64} (hv : fw t.mem G o = v) : GI G STK σ (upd V o v) (o :: LS) t := by
  refine ⟨h.pre, h.hG, h.sp, h.rd, h.wr, h.r28, h.saved, h.lr, h.fixed, fun o' ho' => ?_, fun o' ho' => ?_, h.frame⟩
  · by_cases e : o' = o
    · subst e; rw [upd_self]; exact hv
    · rw [upd_ne _ _ e]; exact h.slots o' (List.mem_of_ne_of_mem e ho')
  · rcases List.mem_cons.mp ho' with rfl | ho'
    · exact ho
    · exact h.ls o' ho'

/-- The call of the test on the candidate `cb` at byte `L.candidate` of the
working space, with the witnesses from `u` on. -/
theorem primeCall_vp {L : Spec.Dsa.ProbablePrime.Layout} {code : Prog isa} {name : String} {u : Nat}
    {cb : List Byte} {cl' : Claims} (ok : PrimeOk L code) (hu : u ≤ G.witLen)
    (hsize : L.size ≤ 8 * wWords G.pLen) (hL : ∀ r ∈ L.scratch, r.1 + r.2 ≤ 8 * wWords G.pLen)
    (hcb : (wB G.pLen + L.candidate, cb) ∈ c.cl) (hcbl : cb.length = L.bits / 8)
    (hodd : Spec.Dsa.decodeBE cb % 2 = 1) (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = L.bits)
    (hU : ∀ o ∈ c.LS, fUsedOut + 8 ≤ o ∨ o + 8 ≤ fUsedOut)
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ ∀ r ∈ L.scratch, Apart (wB G.pLen + r.1) r.2 x) :
    VP (fun σ s => St G c X σ s ∧ TArgs G u s) (.call name code)
      (fun σ t => St G (callCfg c cl' G.witLen u (tRes G cb u)) X σ t ∧
        ((t.gpr .r3).setWidth 32).toNat = Spec.Dsa.ProbablePrime.status (tRes G cb u)) := by
  have bytes : ∀ σ s, SS G 176 σ c s →
      Spec.Rsa.bytesAt s.mem (G.sa (wB G.pLen) + BitVec.ofNat 64 L.candidate) (L.bits / 8) = cb := fun σ s h => by
    have := h.sb _ hcb; rw [hcbl, ← GP.sa_add] at this; exact this
  refine VP.of_ct (fun σ₁ σ₂ => ?_) fun σ s ⟨⟨h, x⟩, regs⟩ => ?_
  · refine (RelCT.call ok.verified.1 ok.verified.2.1 (tRd G u) (tWr G) fun s₁ s₂ ⟨⟨⟨h₁, _⟩, g₁⟩, ⟨⟨h₂, _⟩, g₂⟩⟩ =>
      ?_).mono (fun _ _ h => h) fun _ _ _ => trivial
    have p₁ := pre_of_pin (h₁.tEntry_pin g₁ hu hsize (bytes _ _ h₁) hodd hbl)
    have p₂ := pre_of_pin (h₂.tEntry_pin g₂ hu hsize (bytes _ _ h₂) hodd hbl)
    obtain ⟨cr₁, cw₁⟩ := h₁.tCovers hu
    obtain ⟨cr₂, cw₂⟩ := h₂.tCovers hu
    have eg : ∀ {s : State}, ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7], (tEntry G u s).gpr r = s.gpr r := fun r hr => by
      rw [State.withRegions_gpr, State.callEntry_gpr _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
    obtain ⟨a3, a4, a5, a6, a7⟩ := g₁
    obtain ⟨b3, b4, b5, b6, b7⟩ := g₂
    refine ⟨p₁, p₂, pub_of ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, Covers.append cr₁ cw₁, cw₁, Covers.append cr₂ cw₂, cw₂⟩
    · have e₁ : s₁.sp = G.sp := by rw [h₁.gi.sp, ← h₁.gi.hG]; rfl
      have e₂ : s₂.sp = G.sp := by rw [h₂.gi.sp, ← h₂.gi.hG]; rfl
      show s₁.sp = s₂.sp
      rw [e₁, e₂]
    · rw [eg _ (by simp), eg _ (by simp), a3, b3]
    · rw [eg _ (by simp), eg _ (by simp), a4, b4]
    · rw [eg _ (by simp), eg _ (by simp), a5, b5]
    · rw [eg _ (by simp), eg _ (by simp), a6, b6]
    · rw [eg _ (by simp), eg _ (by simp), a7, b7]
    · simp only [candOf, Spec.Dsa.ProbablePrime.candidateAt, State.withRegions_mem, State.callEntry_mem]
      rw [eg _ (by simp), eg _ (by simp), a3, b3, bytes _ _ h₁, bytes _ _ h₂]
    · have wl := h₁.gi.witLt
      have e6 : (BitVec.ofNat 64 (G.witLen - u)).toNat = G.witLen - u := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [State.withRegions_mem, State.callEntry_mem]
      rw [eg _ (by simp), eg _ (by simp), eg _ (by simp), eg _ (by simp), a5, a6, b5, b6, e6, h₁.gi.randBytes hu,
        h₂.gi.randBytes hu]
  have hU' : ∀ o ∈ c.LS, fUsedOut + 8 ≤ o ∨ o + 8 ≤ fUsedOut := hU
  refine h.primeCall_ok (name := name) ok regs hu hsize hL (bytes _ _ h) hodd hbl
    fun t g rd wr sp f st used => ⟨⟨?_, x⟩, st⟩
  have big := h.gi.wBig
  have kb := h.gi.kBig
  have hE := h.gi.hEnd_le
  have h' : SS G 176 σ { c with cl := cl' } t := by
    refine h.of_hdrScrs (keep_of_preserved g rd wr) sp (os := L.scratch.map fun r => (wB G.pLen + r.1, r.2))
      (fun p hp => ?_) (hw := [fUsedOut]) (fun o ho => ?_) (by
        refine f.sub fun x hx => ?_
        rcases List.mem_append.mp hx with h1 | h2
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h1
          exact ⟨G.rs (wB G.pLen + q.1) q.2, List.mem_append_left _ (List.mem_append_left _
            (List.mem_map.mpr ⟨(wB G.pLen + q.1, q.2), List.mem_map.mpr ⟨q, hq, rfl⟩, rfl⟩)), fun _ h => h⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
          rcases h2 with rfl | rfl
          · exact ⟨G.rs fUsedOut 8, List.mem_append_left _ (List.mem_append_right _ (by simp)), fun _ h => h⟩
          · exact ⟨rBelow σ 176, List.mem_append_right _ (by simp), fun _ h => h⟩) fun y hy => ⟨(hcl y hy).1, fun p hp => ?_⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have := hL q hq
      refine ⟨by simp only [hEnd, wB, kB, pB, fSave] at hE ⊢; omega, .inr (by omega), by simp; omega⟩
    · simp only [List.mem_singleton] at ho; subst ho; exact ⟨varOk_fUsedOut, hU'⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact (hcl y hy).2 q hq
  unfold callCfg
  split
  · exact h'
  · rename_i b rest e
    refine ⟨h'.gi.addSlot varOk_fUsedOut ?_, h'.sb, h'.clOk, h'.arrs, h'.liveOk, h'.ksl, h'.kslOk⟩
    have := used b rest e
    simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
      List.cons.injEq, and_true] at this
    exact this

end

end VG.Proof.Dsa.PPC64LE.Gen
