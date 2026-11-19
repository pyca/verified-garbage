module

public import VerifiedGarbage.Impl.Cast5.AArch64.TblKey
public import VerifiedGarbage.Proof.Cast5.AArch64.TblBatch
public import VerifiedGarbage.Proof.Cast5.KeyMem
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
import VerifiedGarbage.Proof.Blowfish.AArch64.Batch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Cast5.AArch64.Block
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AArch64.StraightV
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Blowfish.AArch64.EcbMain
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Cast5.Contract
public import VerifiedGarbage.Proof.Blowfish.AArch64.ConstantTime
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Cast5.AArch64.TblLit
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Impl.Cast5.AArch64.TblKey
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Cast5.Contract
meta import VerifiedGarbage.Proof.Cast5.AArch64.TblLit
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym

/-!
# CAST5 key expansion on AArch64, S-boxes by `tbl`

The proofs of `Impl/Cast5/AArch64/TblKey.lean`.
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64.Tbl

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Cast5 VG.Impl.Cast5.AArch64.Tbl
open VG.Impl.Blowfish.AArch64 (idxReg outReg qReg tReg c64 c128 veor vperm words wordReg)
open VG.AArch64.Tbl (VOnly)
open VG.Proof.Blowfish.AArch64 (Consts lookupRegs wordsRegs words_run word_ext vbyte_word vword_xor exec_vmov)
open VG.Proof.Cast5 (XZ HoldsXZ off_lt lineOk KMem GroupOk)
open VG.Proof.Cast5.AArch64 (wp_countdown)
open VG.Proof.Blowfish.AArch64 (constants_run cat_run)
open VG.Impl.Blowfish.AArch64 (constants)
open VG.Proof.Cast5.AArch64 (rev32_eq)

/-! ## Lanes -/

theorem vword_setLane (x : BitVec 128) (y : BitVec 32) {i j : Nat} (_ : i < 4) (hj : j < 4) :
    vword (setLane x 32 i y) j = if i = j then y else vword x j := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [vword, setLane, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    hk, decide_true, Bool.true_and]
  obtain h1 : 32 * j + k < 128 := by omega
  by_cases hij : i = j
  · subst hij
    simp [h1, hk, show ¬ 32 * i + k < 32 * i by omega, show k < 128 by omega]
  · rw [ite_eq_right hij]
    simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and, h1]
    by_cases hlt : 32 * j + k < 32 * i
    · simp [hlt]
    · have : ¬ 32 * j + k - 32 * i < 32 := by omega
      obtain hy : y.getLsbD (32 * j + k - 32 * i) = false := BitVec.getLsbD_of_ge _ _ (by omega)
      simp [hlt, this, hy]

theorem vbyte_setLane (x : BitVec 128) (y : BitVec 8) {i j : Nat} (_ : i < 16) (hj : j < 16) :
    vbyte (setLane x 8 i y) j = if i = j then y else vbyte x j := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [vbyte, setLane, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    hk, decide_true, Bool.true_and]
  obtain h1 : 8 * j + k < 128 := by omega
  by_cases hij : i = j
  · subst hij
    simp [h1, hk, show ¬ 8 * i + k < 8 * i by omega, show k < 128 by omega]
  · rw [ite_eq_right hij]
    simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and, h1]
    by_cases hlt : 8 * j + k < 8 * i
    · simp [hlt]
    · have : ¬ 8 * j + k - 8 * i < 8 := by omega
      obtain hy : y.getLsbD (8 * j + k - 8 * i) = false := BitVec.getLsbD_of_ge _ _ (by omega)
      simp [hlt, this, hy]

theorem exec_insE4 (s : State) (d n : VReg) {i j : Nat} (hi : i < 4) (hj : j < 4) :
    exec (.vop (.insE .s4 d i n j)) s = some (s.setV d (setLane (s.v d) 32 i (vword (s.v n) j))) := by
  obtain h : i < 128 / VArr.s4.esize ∧ j < 128 / VArr.s4.esize := ⟨hi, hj⟩
  show (Option.map _ (if _ then _ else _)) = _
  rw [ite_eq_left h]
  rfl

/-! ## The lookups -/

/-- `S_{5+j}` at byte lane `e` of its index. -/
def kbox (v : VReg → BitVec 128) (j e : Nat) : Spec.Cast5.Word := sbox (4 + j) (vbyte (v (idxReg j)) e)

/-- The registers `sboxes5678` writes. -/
def keyVRegs : List VReg := lookupRegs ++ wordsRegs ++ [.v4, .v5, .v6, .v7]

/-- The XOR of the first `j + 1` S-boxes at lane `e`. -/
def kacc (v : VReg → BitVec 128) (e : Nat) : Nat → Spec.Cast5.Word
  | 0 => kbox v 0 e
  | j + 1 => kacc v e j ^^^ kbox v (j + 1) e

theorem gatherOut_run (s : State) {j : Nat} (hj : j < 4) :
    ∃ s', runBlock isa (gatherOut j) s = some s' ∧
      s'.v .v4 = (if j = 0 then s.v (wordReg 0) else s.v .v4 ^^^ s.v (wordReg 0)) ∧
      s'.v .v5 = (if j = 0 then s.v (wordReg 1) else s.v .v5 ^^^ s.v (wordReg 1)) ∧
      s'.v .v7 = setLane (s.v .v7) 32 j (vword (s.v (wordReg 1)) 1) ∧
      s'.v .v6 = setLane (s.v .v6) 32 j (vword (s.v (wordReg 2)) 0) ∧
      VOnly [.v4, .v5, .v6, .v7] s s' := by
  let a := if j = 0 then s.v (wordReg 0) else s.v .v4 ^^^ s.v (wordReg 0)
  let b := if j = 0 then s.v (wordReg 1) else s.v .v5 ^^^ s.v (wordReg 1)
  let s₁ := s.setV .v4 a
  let s₂ := s₁.setV .v5 b
  let s₃ := s₂.setV .v7 (setLane (s₂.v .v7) 32 j (vword (s₂.v (wordReg 1)) 1))
  let s₄ := s₃.setV .v6 (setLane (s₃.v .v6) 32 j (vword (s₃.v (wordReg 2)) 0))
  obtain e₃ : exec (.vop (.insE .s4 .v7 j (wordReg 1) 1)) s₂ = some s₃ := exec_insE4 s₂ _ _ hj (by decide)
  obtain e₄ : exec (.vop (.insE .s4 .v6 j (wordReg 2) 0)) s₃ = some s₄ := exec_insE4 s₃ _ _ hj (by decide)
  obtain r : runBlock isa (gatherOut j) s = some s₄ := by
    by_cases h0 : j = 0
    · have e₁ : exec (.vop (.mov .v4 (wordReg 0))) s = some s₁ := by
        rw [exec_vmov]; simp only [s₁, a, h0, ite_true]
      obtain e₂ : exec (.vop (.mov .v5 (wordReg 1))) s₁ = some s₂ := by
        rw [exec_vmov]; simp only [s₂, b, h0, ite_true]; rfl
      simp only [gatherOut, h0, ite_true, List.cons_append, List.nil_append]
      rw [h0] at e₃ e₄
      rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃, runStep_some,
        runBlock_cons, e₄, runStep_some, runBlock_nil]
    · have e₁ : exec (veor .v4 .v4 (wordReg 0)) s = some s₁ := by
        show some (s.setV .v4 (s.v .v4 ^^^ s.v (wordReg 0))) = _
        simp only [s₁, a, h0, ite_false]
      obtain e₂ : exec (veor .v5 .v5 (wordReg 1)) s₁ = some s₂ := by
        show some (s₁.setV .v5 (s₁.v .v5 ^^^ s₁.v (wordReg 1))) = _
        simp only [s₂, b, h0, ite_false]; rfl
      simp only [gatherOut, h0, ite_false, List.cons_append, List.nil_append]
      rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃, runStep_some,
        runBlock_cons, e₄, runStep_some, runBlock_nil]
  refine ⟨s₄, r, rfl, rfl, rfl, rfl, ?_⟩
  exact (((VOnly.setV s (by simp) _).trans (VOnly.setV _ (by simp) _)).trans (VOnly.setV _ (by simp) _)).trans
    (VOnly.setV _ (by simp) _)

theorem key_notin : ∀ r ∈ [VReg.v4, .v5, .v6, .v7], r ∉ lookupRegs ∧ r ∉ wordsRegs := by decide
theorem word_notin : ∀ k < 4, wordReg k ∉ [VReg.v4, .v5, .v6, .v7] := by decide
theorem idx_notin_key : ∀ j < 4, idxReg j ∉ keyVRegs := by decide
theorem const_notin_key : c64 ∉ keyVRegs ∧ c128 ∉ keyVRegs := by decide

/-- One S-box of `sboxes5678`. -/
theorem step_run {s : State} (h9 : s.gpr .x9 = s.syms planesSym) (hc : Consts s) {j : Nat} (hj : j < 4) :
    ∃ s', runBlock isa (lookup (4 + j) j ++ words ++ gatherOut j) s = some s' ∧
      (∀ l < 4, vword (s'.v .v4) l =
        if j = 0 then kbox s.v j l else vword (s.v .v4) l ^^^ kbox s.v j l) ∧
      (vword (s'.v .v5) 0 = if j = 0 then kbox s.v j 4 else vword (s.v .v5) 0 ^^^ kbox s.v j 4) ∧
      (∀ i < 4, vword (s'.v .v7) i = if j = i then kbox s.v j 5 else vword (s.v .v7) i) ∧
      (∀ i < 4, vword (s'.v .v6) i = if j = i then kbox s.v j 8 else vword (s.v .v6) i) ∧
      VOnly keyVRegs s s' := by
  obtain ⟨s₁, r₁, v₁, o₁⟩ := lookup_run h9 hc (t := 4 + j) (by omega_using [hj]) hj
  obtain ⟨s₂, r₂, v₂, o₂⟩ := words_run s₁
  obtain ⟨s₃, r₃, a₃, b₃, e₃, k₃, o₃⟩ := gatherOut_run s₂ hj
  obtain w : ∀ n < 16, vword (s₂.v (wordReg (n / 4))) (n % 4) = kbox s.v j n := by
    intro n hn
    obtain hk : n / 4 < 4 := by omega_using [hn]
    obtain hl : n % 4 < 4 := by omega_using []
    refine word_ext fun b hb => ?_
    rw [← vbyte_word _ hb, v₂ _ hk _ hl _ hb, show 4 * (n / 4) + n % 4 = n by omega_using [], v₁ _ hb _ hn]
    rfl
  obtain kp : ∀ r ∈ [VReg.v4, .v5, .v6, .v7], s₂.v r = s.v r := fun r hr => by
    rw [o₂.2 _ (key_notin r hr).2, o₁.2 _ (key_notin r hr).1]
  refine ⟨s₃, VG.AArch64.Tbl.runBlock_cat_some (VG.AArch64.Tbl.runBlock_cat_some r₁ r₂) r₃, fun l hl => ?_,
    ?_, fun i hi => ?_, fun i hi => ?_, ?_⟩
  · have := w l (by omega_using [hl])
    rw [show l / 4 = 0 by omega_using [hl], show l % 4 = l by omega_using [hl]] at this
    rw [a₃]
    split
    · exact this
    · rw [vword_xor, this, kp .v4 (by simp)]
  · have := w 4 (by decide)
    rw [b₃]
    split
    · exact this
    · rw [vword_xor, kp .v5 (by simp)]; exact congrArg _ this
  · rw [e₃, vword_setLane _ _ hj hi, kp .v7 (by simp),
      show vword (s₂.v (wordReg 1)) 1 = kbox s.v j 5 from w 5 (by decide)]
  · rw [k₃, vword_setLane _ _ hj hi, kp .v6 (by simp),
      show vword (s₂.v (wordReg 2)) 0 = kbox s.v j 8 from w 8 (by decide)]
  · exact ((Proof.Blowfish.AArch64.VOnly.mono o₁ (by decide)).trans
      (Proof.Blowfish.AArch64.VOnly.mono o₂ (by decide))).trans (Proof.Blowfish.AArch64.VOnly.mono o₃ (by decide))

theorem sboxes_eq : sboxes5678 = .block (([.adrSym .x9 planesSym] : List Instr) ++
    ((lookup (4 + 0) 0 ++ words ++ gatherOut 0) ++
    ((lookup (4 + 1) 1 ++ words ++ gatherOut 1) ++ ((lookup (4 + 2) 2 ++ words ++ gatherOut 2) ++
      ((lookup (4 + 3) 3 ++ words ++ gatherOut 3) ++ []))))) := rfl

/-- What the registers hold after `sboxes5678`. -/
structure Looked (s s' : State) : Prop where
  keys : ∀ l < 4, vword (s'.v .v4) l = kacc s.v l 3
  line : vword (s'.v .v5) 0 = kacc s.v 4 3
  extras : ∀ i < 4, vword (s'.v .v7) i = kbox s.v i 5
  kextras : ∀ i < 4, vword (s'.v .v6) i = kbox s.v i 8
  only : VOnly keyVRegs (s.write .x .x9 (s.syms planesSym)) s'

theorem sboxes_run' {s : State} (h9 : s.gpr .x9 = s.syms planesSym) (hc : Consts s) :
    ∃ s', runBlock isa ((lookup (4 + 0) 0 ++ words ++ gatherOut 0) ++
      ((lookup (4 + 1) 1 ++ words ++ gatherOut 1) ++ ((lookup (4 + 2) 2 ++ words ++ gatherOut 2) ++
        ((lookup (4 + 3) 3 ++ words ++ gatherOut 3) ++ [])))) s = some s' ∧
      (∀ l < 4, vword (s'.v .v4) l = kacc s.v l 3) ∧ vword (s'.v .v5) 0 = kacc s.v 4 3 ∧
      (∀ i < 4, vword (s'.v .v7) i = kbox s.v i 5) ∧ (∀ i < 4, vword (s'.v .v6) i = kbox s.v i 8) ∧
      VOnly keyVRegs s s' := by
  obtain keep : ∀ {u : State}, VOnly keyVRegs s u →
      u.gpr .x9 = u.syms planesSym ∧ Consts u ∧ ∀ j < 4, ∀ e, kbox u.v j e = kbox s.v j e := by
    intro u hu
    refine ⟨by rw [hu.gpr, hu.1]; exact h9, ⟨fun e he => ?_, fun e he => ?_⟩, fun j hj e => ?_⟩
    · rw [hu.2 _ const_notin_key.1]; exact hc.1 e he
    · rw [hu.2 _ const_notin_key.2]; exact hc.2 e he
    · simp only [kbox]; rw [hu.2 _ (idx_notin_key j hj)]
  obtain ⟨s₀, r₀, a₀, b₀, e₀, k₀, o₀⟩ := step_run h9 hc (by decide : 0 < 4)
  obtain q₀ := keep o₀
  obtain ⟨s₁, r₁, a₁, b₁, e₁, k₁, o₁⟩ := step_run q₀.1 q₀.2.1 (by decide : 1 < 4)
  obtain p₁ := o₀.trans o₁
  obtain q₁ := keep p₁
  obtain ⟨s₂, r₂, a₂, b₂, e₂, k₂, o₂⟩ := step_run q₁.1 q₁.2.1 (by decide : 2 < 4)
  obtain p₂ := p₁.trans o₂
  obtain q₂ := keep p₂
  obtain ⟨s₃, r₃, a₃, b₃, e₃, k₃, o₃⟩ := step_run q₂.1 q₂.2.1 (by decide : 3 < 4)
  simp only [↓reduceIte] at a₀ b₀
  simp only [(by decide : ¬ (1 : Nat) = 0), (by decide : ¬ (2 : Nat) = 0), (by decide : ¬ (3 : Nat) = 0),
    ↓reduceIte, q₀.2.2 _ (by decide : 1 < 4), q₁.2.2 _ (by decide : 2 < 4),
    q₂.2.2 _ (by decide : 3 < 4)] at a₁ a₂ a₃ b₁ b₂ b₃ e₁ e₂ e₃ k₁ k₂ k₃
  refine ⟨s₃, VG.AArch64.Tbl.runBlock_cat_some r₀ (VG.AArch64.Tbl.runBlock_cat_some r₁
    (VG.AArch64.Tbl.runBlock_cat_some r₂ (VG.AArch64.Tbl.runBlock_cat_some r₃ runBlock_nil))),
    fun l hl => ?_, ?_, fun i hi => ?_, fun i hi => ?_, p₂.trans o₃⟩
  · rw [a₃ l hl, a₂ l hl, a₁ l hl, a₀ l hl]; rfl
  · rw [b₃, b₂, b₁, b₀]; rfl
  · rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    · rw [e₃ 0 hi, e₂ 0 hi, e₁ 0 hi, e₀ 0 hi]; simp
    · rw [e₃ 1 hi, e₂ 1 hi, e₁ 1 hi]; simp
    · rw [e₃ 2 hi, e₂ 2 hi]; simp
    · rw [e₃ 3 hi]; simp
  · rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    · rw [k₃ 0 hi, k₂ 0 hi, k₁ 0 hi, k₀ 0 hi]; simp
    · rw [k₃ 1 hi, k₂ 1 hi, k₁ 1 hi]; simp
    · rw [k₃ 2 hi, k₂ 2 hi]; simp
    · rw [k₃ 3 hi]; simp

theorem sboxes_run {s : State} (hc : Consts s) :
    ∃ s', runBlock isa (([.adrSym .x9 planesSym] : List Instr) ++
      ((lookup (4 + 0) 0 ++ words ++ gatherOut 0) ++
      ((lookup (4 + 1) 1 ++ words ++ gatherOut 1) ++ ((lookup (4 + 2) 2 ++ words ++ gatherOut 2) ++
        ((lookup (4 + 3) 3 ++ words ++ gatherOut 3) ++ []))))) s = some s' ∧ Looked s s' := by
  let s₀ := s.write .x .x9 (s.syms planesSym)
  obtain e₀ : runBlock isa ([.adrSym .x9 planesSym] : List Instr) s = some s₀ := by
    rw [runBlock_cons, exec_adrSym, runStep_some, runBlock_nil]
  obtain h9 : s₀.gpr .x9 = s₀.syms planesSym := by
    show (s.write .x .x9 _).gpr .x9 = s.syms planesSym
    rw [gpr_write_self]; exact BitVec.setWidth_eq _
  obtain ⟨s', r, a, b, e, k, o⟩ := sboxes_run' (s := s₀) h9 hc
  exact ⟨s', VG.AArch64.Tbl.runBlock_cat_some e₀ r, ⟨a, b, e, k, o⟩⟩

/-! ## A pass -/

/-- The contract of `sboxes5678` for its callers. -/
def sboxesK : Contract isa where
  pre s := Consts s
  post s s' := Looked s s'
  pub _ _ := True

theorem vonly_sp {ds : List VReg} {s s' : State} (h : VOnly ds s s') : s'.sp = s.sp := by rw [h.1]
theorem vonly_syms {ds : List VReg} {s s' : State} (h : VOnly ds s s') : s'.syms = s.syms := by rw [h.1]

theorem keyV_not_saved : ∀ r ∈ preservedV, r ∉ keyVRegs := by decide

theorem sboxes_correct (s : State) (h : sboxesK.pre s) :
    ∃ t s', Exec isa sboxes5678 s t s' ∧ abiPreserved s s' ∧ sboxesK.post s s' := by
  obtain ⟨s', r, L⟩ := sboxes_run h
  obtain ⟨t, s'', he, e⟩ := (WP.of_runBlock ⟨s', r, rfl⟩ : WP isa (.block _) s (· = s'))
  subst e
  rw [sboxes_eq]
  refine ⟨t, _, he, ⟨fun r hr => ?_, (vonly_sp L.only).trans rfl, fun r hr => by
    rw [L.only.2 r (keyV_not_saved r hr)]; rfl⟩, L⟩
  rw [congrFun L.only.gpr r]
  exact gpr_write_of_ne _ _ _ (by rintro rfl; revert hr; decide)

/-- The state after a pass. -/
structure Passed (s s' : State) : Prop where
  keys : ∀ l < 4, vword (s'.v .v4) l = kacc s.v l 3
  line : vword (s'.v .v5) 0 = kacc s.v 4 3
  extras : ∀ i < 4, vword (s'.v .v7) i = kbox s.v i 5
  kextras : ∀ i < 4, vword (s'.v .v6) i = kbox s.v i 8
  v : ∀ r, r ∉ keyVRegs → s'.v r = s.v r
  gpr : ∀ r, r ∉ linkRegs → r ≠ .x9 → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  syms : s'.syms = s.syms

theorem pass_ok {s : State} (hc : Consts s) : WP isa pass s (Passed s) := by
  refine WP.callV (k := sboxesK) sboxes_correct (rd := s.rd) (wr := s.wr) hc (Covers.refl _) (Covers.refl _) ?_
    (by rfl)
  intro s' hrd hwr hsp _ _ _ _ L
  obtain hg := congrFun L.only.gpr
  exact ⟨L.keys, L.line, L.extras, L.kextras, L.only.2, fun r hr h9 => by
    refine (hg r).trans ((gpr_write_of_ne _ _ _ h9).trans ?_)
    exact State.callEntry_gpr _ hr, L.only.mem, hrd, hwr, hsp, (vonly_syms L.only).trans rfl⟩

/-! ## Gathering the indices -/

/-- Bytes to gather: the lane, the S-box's index register, and the byte. -/
abbrev Gs := List (Nat × Nat × Pos)

def gatherL (gs : Gs) : List Instr := gs.flatMap fun g => gatherByte g.1 g.2.1 g.2.2

/-- The bytes of the index registers after a gather, from those before. -/
def gfold (st : XZ) : Gs → (Nat → Nat → Byte) → Nat → Nat → Byte
  | [], f => f
  | g :: gs, f => gfold st gs fun j e => if j = g.2.1 ∧ e = g.1 then st.get g.2.2 else f j e

theorem idx_inj : ∀ j < 4, ∀ j' < 4, idxReg j = idxReg j' → j = j' := by decide

theorem byte_back (b : Byte) : ((b.setWidth 32).setWidth 64).setWidth 8 = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and, show i < 32 by omega, show i < 64 by omega]

theorem gatherByte_run (s : State) {lane j : Nat} {p : Pos} (hl : lane < 16) (ho : srcOff p < 4096)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (srcOff p)) 1) :
    ∃ u, runBlock isa (gatherByte lane j p) s = some u ∧
      u.v (idxReg j) = setLane (s.v (idxReg j)) 8 lane (s.mem (s.gpr .x3 + BitVec.ofNat 64 (srcOff p))) ∧
      (∀ r, r ≠ idxReg j → u.v r = s.v r) ∧ (∀ r, r ≠ .x10 → u.gpr r = s.gpr r) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧ u.syms = s.syms := by
  let s₁ := s.write .w .x10 ((s.mem (s.gpr .x3 + BitVec.ofNat 64 (srcOff p))).setWidth 32)
  let s₂ := s₁.setV (idxReg j) (setLane (s₁.v (idxReg j)) 8 lane ((s₁.gpr .x10).setWidth 8))
  obtain e₁ : exec (.ldrb .x10 .x3 (srcOff p)) s = some s₁ := Proof.Cast5.AArch64.exec_ldrb' ho hr
  obtain e₂ : exec (.vop (.ins .b16 (idxReg j) lane .x10)) s₁ = some s₂ := by
    show Option.map _ (if lane < 16 then _ else _) = _
    rw [ite_eq_left hl]; rfl
  refine ⟨s₂, by rw [gatherByte, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_nil],
    ?_, fun r hr => v_setV_of_ne _ _ hr, fun r hr => gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl, rfl, rfl⟩
  show (s₁.setV _ _).v _ = _
  rw [v_setV_self]
  show setLane (s.v (idxReg j)) 8 lane ((s₁.gpr .x10).setWidth 8) = _
  obtain e : s₁.gpr .x10 = ((s.mem (s.gpr .x3 + BitVec.ofNat 64 (srcOff p))).setWidth 32).setWidth 64 := by
    show (s.write .w .x10 _).gpr .x10 = _
    rw [gpr_write_self]
  rw [e, byte_back]

/-- What a gather needs: lanes, registers and bytes in range. -/
def GsOk (gs : Gs) : Prop := ∀ g ∈ gs, g.1 < 16 ∧ g.2.1 < 4 ∧ g.2.2.2 < 16

theorem gatherL_run (st : XZ) : ∀ (gs : Gs) (s : State) (f : Nat → Nat → Byte), GsOk gs →
    InRegions (s.rd ++ s.wr) (s.gpr .x3) 64 → HoldsXZ s.mem (s.gpr .x3) st →
    (∀ j < 4, ∀ e < 16, vbyte (s.v (idxReg j)) e = f j e) →
    ∃ u, runBlock isa (gatherL gs) s = some u ∧
      (∀ j < 4, ∀ e < 16, vbyte (u.v (idxReg j)) e = gfold st gs f j e) ∧
      (∀ r, (∀ j < 4, r ≠ idxReg j) → u.v r = s.v r) ∧ (∀ r, r ≠ .x10 → u.gpr r = s.gpr r) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧ u.syms = s.syms
  | [], s, f, _, _, _, hf => ⟨s, rfl, hf, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  | g :: gs, s, f, hg, hw, hm, hf => by
    obtain ⟨hl, hj, hp⟩ := hg g List.mem_cons_self
    obtain ho : srcOff g.2.2 < 4096 := by
      have := off_lt g.2.2.1; simp only [srcOff]; omega_using [hp, this]
    obtain hr : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (srcOff g.2.2)) 1 :=
      CallLay.inRegions_sub hw (by have := off_lt g.2.2.1; simp only [srcOff]; omega_using [hp, this]) (by decide)
    obtain ⟨u, ru, vu, ou, gu, mu, rdu, wru, spu, syu⟩ := gatherByte_run s (j := g.2.1) hl ho hr
    obtain ⟨w, rw', vw, ow, gw, mw, rdw, wrw, spw, syw⟩ := gatherL_run st gs u
      (fun j e => if j = g.2.1 ∧ e = g.1 then st.get g.2.2 else f j e)
      (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
      (by rw [rdu, wru, gu _ (by decide)]; exact hw) (by rw [mu, gu _ (by decide)]; exact hm)
      (fun j hj' e he => by
        by_cases hjj : j = g.2.1
        · subst hjj
          rw [vu, vbyte_setLane _ _ hl he, hm.pos hp]
          by_cases hee : e = g.1
          · rw [ite_eq_left hee.symm, ite_eq_left ⟨rfl, hee⟩]
          · rw [ite_eq_right (fun h => hee h.symm), ite_eq_right (fun h => hee h.2)]; exact hf _ hj' e he
        · rw [ou _ (fun h => hjj (idx_inj j hj' _ hj h)), ite_eq_right (fun h => hjj h.1)]; exact hf j hj' e he)
    refine ⟨w, ?_, vw, fun r hr => (ow r hr).trans (ou r (hr _ hj)), fun r hr => (gw r hr).trans (gu r hr),
      mw.trans mu, rdw.trans rdu, wrw.trans wru, spw.trans spu, syw.trans syu⟩
    show runBlock isa (gatherByte g.1 g.2.1 g.2.2 ++ gatherL gs) s = some w
    exact VG.AArch64.Tbl.runBlock_cat_some ru rw'

/-! ## Storing a line -/

/-- A line's value from its lookups `v` and the memory `m` holding its quadruple. -/
def withWord (m : Mem) (p : Addr) (v : Spec.Cast5.Word) : Option (Arr × Nat) → Spec.Cast5.Word
  | some (a, q) => v ^^^ byteRev32 (m.readW (p + BitVec.ofNat 64 (off a + 4 * q)) 32)
  | none => v

theorem storeLine_ok (u : State) (l : Impl.Cast5.Line) {k : Nat} (tgt : Arr) (hk : k < 4)
    (hl : lineOk l = true) {V X : Spec.Cast5.Word} (hV : vword (u.v .v5) 0 = V)
    (hX : u.mem.readW (u.gpr .x3 + BitVec.ofNat 64 (extraOff + 4 * (l.extra.1 - 5))) 32 = X)
    (hr : InRegions (u.rd ++ u.wr) (u.gpr .x3) 64) (hw : InRegions u.wr (u.gpr .x3) 64) :
    WP isa (.block (storeLine l k tgt)) u fun w =>
      w.mem = u.mem.writeW (u.gpr .x3 + BitVec.ofNat 64 (off tgt + 4 * k))
        (byteRev32 (withWord u.mem (u.gpr .x3) (V ^^^ X) l.word)) ∧
      (∀ r, r ≠ .x0 → r ≠ .x10 → w.gpr r = u.gpr r) ∧ w.rd = u.rd ∧ w.wr = u.wr ∧ w.v = u.v ∧
      w.sp = u.sp ∧ w.syms = u.syms := by
  simp only [lineOk, Bool.and_eq_true, decide_eq_true_eq] at hl
  obtain ⟨⟨⟨_, he5⟩, he8⟩, hwd⟩ := hl
  obtain hto := off_lt tgt
  obtain hE : (extraOff + 4 * (l.extra.1 - 5)) % 4 = 0 ∧ extraOff + 4 * (l.extra.1 - 5) < 16384 := by
    simp only [extraOff]; omega_using [he8]
  obtain rE : InRegions (u.rd ++ u.wr) (u.gpr .x3 + BitVec.ofNat 64 (extraOff + 4 * (l.extra.1 - 5))) 4 :=
    CallLay.inRegions_sub hr (by simp only [extraOff]; omega_using [he5, he8]) (by decide)
  obtain hT : (off tgt + 4 * k) % 4 = 0 ∧ off tgt + 4 * k < 16384 := by
    cases tgt <;> simp only [off, xOff, zOff] <;> omega_using [hk]
  obtain wT : InRegions u.wr (u.gpr .x3 + BitVec.ofNat 64 (off tgt + 4 * k)) 4 :=
    CallLay.inRegions_sub hw (by omega_using [hk, hto]) (by decide)
  unfold storeLine
  rcases hwd' : l.word with _ | ⟨a, q⟩
  · crun [hV, hX, hE, rE, hT, wT, rev32_eq, withWord]
    exact fun r h0 h10 => by simp only [h0, h10, ite_false]
  · have hq4 : q < 4 := by rw [hwd'] at hwd; simpa using hwd
    obtain hao := off_lt a
    obtain hQ : (off a + 4 * q) % 4 = 0 ∧ off a + 4 * q < 16384 := by
      cases a <;> simp only [off, xOff, zOff] <;> omega_using [hq4]
    obtain rQ : InRegions (u.rd ++ u.wr) (u.gpr .x3 + BitVec.ofNat 64 (off a + 4 * q)) 4 :=
      CallLay.inRegions_sub hr (by omega_using [hq4, hao]) (by decide)
    crun [hV, hX, hE, rE, hT, wT, hQ, rQ, rev32_eq, withWord]
    exact fun r h0 h10 => by simp only [h0, h10, ite_false]

/-! ## A store of four words -/

theorem w32_apply (m : Mem) (a x : Addr) (w : BitVec 32) :
    (m.writeW a w) x = if (x - a).toNat < 4 then w.extractLsb' (8 * (x - a).toNat) 8 else m x := by
  simp [Mem.writeW, Mem.write]

theorem w128_apply (m : Mem) (a x : Addr) (w : BitVec 128) :
    (m.writeW a w) x = if (x - a).toNat < 16 then w.extractLsb' (8 * (x - a).toNat) 8 else m x := by
  simp [Mem.writeW, Mem.write]

theorem sub_add_toNat (x a : Addr) {n : Nat} (hn : n < 2 ^ 64) :
    (x - (a + BitVec.ofNat 64 n)).toNat = ((x - a).toNat + 2 ^ 64 - n) % 2 ^ 64 := by
  have := x.isLt; have := a.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem byte_of_word (v : BitVec 128) (t : Nat) {b : Nat} (hb : b < 4) :
    (vword v t).extractLsb' (8 * b) 8 = v.extractLsb' (8 * (4 * t + b)) 8 :=
  (vbyte_word v hb).symm

/-- Sixteen bytes stored are four words stored. -/
theorem writeW_split (m : Mem) (a : Addr) (v : BitVec 128) :
    m.writeW a v = (((m.writeW a (vword v 0)).writeW (a + BitVec.ofNat 64 4) (vword v 1)).writeW
      (a + BitVec.ofNat 64 8) (vword v 2)).writeW (a + BitVec.ofNat 64 12) (vword v 3) := by
  funext x
  rw [w128_apply, w32_apply, w32_apply, w32_apply, w32_apply, sub_add_toNat x a (by decide : 4 < 2 ^ 64),
    sub_add_toNat x a (by decide : 8 < 2 ^ 64), sub_add_toNat x a (by decide : 12 < 2 ^ 64)]
  obtain hd := (x - a).isLt
  generalize (x - a).toNat = d at hd ⊢
  rcases (by omega : d < 4 ∨ (4 ≤ d ∧ d < 8) ∨ (8 ≤ d ∧ d < 12) ∨ (12 ≤ d ∧ d < 16) ∨ 16 ≤ d) with h | h | h | h | h
  · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left h, byte_of_word v 0 h]
    exact congrArg (fun i => v.extractLsb' (8 * i) 8) (by omega)
  · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      show (d + 2 ^ 64 - 4) % 2 ^ 64 = d - 4 by omega, byte_of_word v 1 (by omega)]
    exact congrArg (fun i => v.extractLsb' (8 * i) 8) (by omega)
  · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      show (d + 2 ^ 64 - 8) % 2 ^ 64 = d - 8 by omega, byte_of_word v 2 (by omega)]
    exact congrArg (fun i => v.extractLsb' (8 * i) 8) (by omega)
  · rw [ite_eq_left (by omega), ite_eq_left (by omega),
      show (d + 2 ^ 64 - 12) % 2 ^ 64 = d - 12 by omega, byte_of_word v 3 (by omega)]
    exact congrArg (fun i => v.extractLsb' (8 * i) 8) (by omega)
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega)]

/-! ## What a gather leaves -/

theorem gfold_other (st : XZ) : ∀ (gs : Gs) (f : Nat → Nat → Byte) (j e : Nat),
    (∀ g ∈ gs, ¬(j = g.2.1 ∧ e = g.1)) → gfold st gs f j e = f j e
  | [], _, _, _, _ => rfl
  | g :: gs, f, j, e, h => by
    rw [gfold, gfold_other st gs _ j e (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')),
      ite_eq_right (h g List.mem_cons_self)]

/-- No two bytes of a gather go to the same lane of the same register. -/
def GsDistinct (gs : Gs) : Prop := gs.Pairwise fun a b => ¬(a.2.1 = b.2.1 ∧ a.1 = b.1)

theorem gfold_mem (st : XZ) : ∀ (gs : Gs) (f : Nat → Nat → Byte), GsDistinct gs →
    ∀ g ∈ gs, gfold st gs f g.2.1 g.1 = st.get g.2.2
  | [], _, _, _, hg => absurd hg List.not_mem_nil
  | g' :: gs, f, hp, g, hg => by
    obtain hp' := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp hg with rfl | hin
    · rw [gfold, gfold_other st gs _ _ _ (fun g'' hg'' => hp'.1 g'' hg''), ite_eq_left ⟨rfl, rfl⟩]
    · exact gfold_mem st gs _ hp'.2 g hin

/-- A gather: every byte is in its lane. -/
theorem gather_ok (st : XZ) (gs : Gs) (s : State) (hok : GsOk gs) (hd : GsDistinct gs)
    (hw : InRegions (s.rd ++ s.wr) (s.gpr .x3) 64) (hm : HoldsXZ s.mem (s.gpr .x3) st) :
    ∃ u, runBlock isa (gatherL gs) s = some u ∧
      (∀ g ∈ gs, vbyte (u.v (idxReg g.2.1)) g.1 = st.get g.2.2) ∧
      (∀ r, (∀ j < 4, r ≠ idxReg j) → u.v r = s.v r) ∧ (∀ r, r ≠ .x10 → u.gpr r = s.gpr r) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧ u.syms = s.syms := by
  obtain ⟨u, ru, vu, rest⟩ := gatherL_run st gs s (fun j e => vbyte (s.v (idxReg j)) e) hok hw hm
    (fun _ _ _ _ => rfl)
  exact ⟨u, ru, fun g hg => by rw [vu _ (hok g hg).2.1 _ (hok g hg).1, gfold_mem st gs _ hd g hg], rest⟩

/-- A line's main bytes, to lane `lane`. -/
def gsMain (lane : Nat) (l : Impl.Cast5.Line) : Gs :=
  [(lane, 0, l.main.1), (lane, 1, l.main.2.1), (lane, 2, l.main.2.2.1), (lane, 3, l.main.2.2.2)]

/-- A group's extra bytes, to lane `lane`. -/
def gsExtras (lane : Nat) (ls : List Impl.Cast5.Line) : Gs :=
  [(lane, 0, extraOf ls 5), (lane, 1, extraOf ls 6), (lane, 2, extraOf ls 7), (lane, 3, extraOf ls 8)]

/-- The bytes of a group of subkeys. -/
def gsKeys (ls : List Impl.Cast5.Line) : Gs :=
  gsMain 0 (ls.getD 0 default) ++ gsMain 1 (ls.getD 1 default) ++ gsMain 2 (ls.getD 2 default) ++
    gsMain 3 (ls.getD 3 default) ++ gsExtras 8 ls

theorem gatherMain_eq (lane : Nat) (l : Impl.Cast5.Line) : gatherMain lane l = gatherL (gsMain lane l) := rfl
theorem gatherExtras_eq (lane : Nat) (ls : List Impl.Cast5.Line) :
    gatherExtras lane ls = gatherL (gsExtras lane ls) := rfl
theorem gatherKeys_eq (ls : List Impl.Cast5.Line) : gatherKeys ls = gatherL (gsKeys ls) := rfl

theorem gatherL_append (a b : Gs) : gatherL (a ++ b) = gatherL a ++ gatherL b := List.flatMap_append

theorem GsOk.append {a b : Gs} (ha : GsOk a) (hb : GsOk b) : GsOk (a ++ b) := fun g hg => by
  rcases List.mem_append.mp hg with h | h
  · exact ha g h
  · exact hb g h

theorem gsMain_ok {lane : Nat} (hl : lane < 16) {l : Impl.Cast5.Line} (h : lineOk l = true) :
    GsOk (gsMain lane l) := by
  simp only [lineOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, _⟩, _⟩, _⟩ := h
  intro g hg
  simp only [gsMain, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  exacts [⟨hl, (by decide : 0 < 4), ha⟩, ⟨hl, (by decide : 1 < 4), hb⟩, ⟨hl, (by decide : 2 < 4), hc⟩,
    ⟨hl, (by decide : 3 < 4), hd⟩]

theorem gsExtras_ok {lane : Nat} (hl : lane < 16) {ls : List Impl.Cast5.Line}
    (h : ∀ e < 4, (extraOf ls (5 + e)).2 < 16) : GsOk (gsExtras lane ls) := by
  intro g hg
  simp only [gsExtras, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  exacts [⟨hl, (by decide : 0 < 4), h 0 (by decide)⟩, ⟨hl, (by decide : 1 < 4), h 1 (by decide)⟩,
    ⟨hl, (by decide : 2 < 4), h 2 (by decide)⟩, ⟨hl, (by decide : 3 < 4), h 3 (by decide)⟩]

theorem gsKeys_ok {ls : List Impl.Cast5.Line} (h : GroupOk none ls) : GsOk (gsKeys ls) :=
  ((((gsMain_ok (by decide) (h.1 0 (by decide)).1).append (gsMain_ok (by decide) (h.1 1 (by decide)).1)).append
    (gsMain_ok (by decide) (h.1 2 (by decide)).1)).append (gsMain_ok (by decide) (h.1 3 (by decide)).1)).append
    (gsExtras_ok (by decide) h.2)

/-! ## The S-boxes of a line -/

theorem sbox_k {j : Nat} (hj : j < 4) (b : Byte) : sbox (4 + j) b = Proof.Cast5.sbox (5 + j) b := by
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem kacc_three (v : VReg → BitVec 128) (e : Nat) :
    kacc v e 3 = Spec.Cast5.S5 (vbyte (v (idxReg 0)) e) ^^^ Spec.Cast5.S6 (vbyte (v (idxReg 1)) e) ^^^
      Spec.Cast5.S7 (vbyte (v (idxReg 2)) e) ^^^ Spec.Cast5.S8 (vbyte (v (idxReg 3)) e) := rfl

/-- The lookups of a line whose main bytes are in lane `e`, with its extra lookup `X`. -/
theorem line_lookups (st : XZ) (l : Impl.Cast5.Line) (v : VReg → BitVec 128) {e : Nat}
    (hg : ∀ g ∈ gsMain e l, vbyte (v (idxReg g.2.1)) g.1 = st.get g.2.2) {X : Spec.Cast5.Word}
    (hX : X = Proof.Cast5.sbox l.extra.1 (st.get l.extra.2)) :
    kacc v e 3 ^^^ X = Spec.Cast5.S8 (st.get l.main.2.2.2) ^^^ Spec.Cast5.S7 (st.get l.main.2.2.1) ^^^
      Spec.Cast5.S6 (st.get l.main.2.1) ^^^ Spec.Cast5.S5 (st.get l.main.1) ^^^
      Proof.Cast5.sbox l.extra.1 (st.get l.extra.2) := by
  obtain h0 := hg (e, 0, l.main.1) (by simp [gsMain])
  obtain h1 := hg (e, 1, l.main.2.1) (by simp [gsMain])
  obtain h2 := hg (e, 2, l.main.2.2.1) (by simp [gsMain])
  obtain h3 := hg (e, 3, l.main.2.2.2) (by simp [gsMain])
  simp only at h0 h1 h2 h3
  rw [kacc_three, h0, h1, h2, h3, hX]
  exact Proof.Cast5.xor5 _ _ _ _ _

/-! ## The state of key expansion -/

/-- The state of key expansion from the memory `m0`: the working space `c` in
`x3`, writable, as is the schedule `K`; the table's address and the
constants; and the memory (`KMem`). -/
structure TS (m0 : Mem) (c K : Addr) (s : State) (st : XZ) (ws : List Spec.Cast5.Word) : Prop where
  rc : s.gpr .x3 = c
  mem : KMem m0 s.mem c K st ws
  len : ws.length ≤ 32
  wS : InRegions s.wr c 64
  wK : InRegions s.wr K 128
  dKS : Region.Disjoint ⟨K, 128⟩ ⟨c, 64⟩
  consts : Consts s

/-- The general-purpose registers a pass and its stores write. -/
def passGprs : List Reg := [.x0, .x9, .x10, .x16, .x17, .x30]

/-- The vector registers a pass and its gather write. -/
def passVRegs : List VReg := keyVRegs ++ [.v16, .v17, .v18, .v19]

/-- What a pass and its stores keep. -/
structure Kept (s s' : State) : Prop where
  gpr : ∀ r, r ∉ passGprs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  syms : s'.syms = s.syms
  v : ∀ r, r ∉ passVRegs → s'.v r = s.v r

theorem Kept.refl (s : State) : Kept s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Kept.trans {a b c : State} (h₁ : Kept a b) (h₂ : Kept b c) : Kept a c :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp,
    h₂.syms.trans h₁.syms, fun r hr => (h₂.v r hr).trans (h₁.v r hr)⟩

theorem const_notin_pass : c64 ∉ passVRegs ∧ c128 ∉ passVRegs := by decide

/-- The same state, later. -/
theorem TS.next {m0 : Mem} {c K : Addr} {s u : State} {st st' : XZ} {ws ws' : List Spec.Cast5.Word}
    (h : TS m0 c K s st ws) (k : Kept s u) (hm : KMem m0 u.mem c K st' ws') (hl : ws'.length ≤ 32) :
    TS m0 c K u st' ws' where
  rc := (k.gpr _ (by decide)).trans h.rc
  mem := hm
  len := hl
  wS := by rw [k.wr]; exact h.wS
  wK := by rw [k.wr]; exact h.wK
  dKS := h.dKS
  consts := ⟨fun e he => by rw [k.v _ const_notin_pass.1]; exact h.consts.1 e he,
    fun e he => by rw [k.v _ const_notin_pass.2]; exact h.consts.2 e he⟩

theorem TS.ws {m0 : Mem} {c K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : TS m0 c K s st ws) : InRegions (s.rd ++ s.wr) (s.gpr .x3) 64 := by
  rw [h.rc]; obtain ⟨g, hg, hc⟩ := h.wS; exact ⟨g, List.mem_append_right _ hg, hc⟩

/-! ## Four subkeys stored -/

theorem kmem_keys4 {m0 m : Mem} {c K : Addr} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KMem m0 m c K st ws) (dKS : Region.Disjoint ⟨K, 128⟩ ⟨c, 64⟩) (hws : ws.length + 4 ≤ 32)
    (v : BitVec 128) :
    KMem m0 (m.writeW (K + BitVec.ofNat 64 (4 * ws.length)) v) c K st
      (ws ++ [vword v 0, vword v 1, vword v 2, vword v 3]) := by
  obtain l1 : (ws ++ [vword v 0]).length = ws.length + 1 := by simp
  obtain l2 : (ws ++ [vword v 0] ++ [vword v 1]).length = ws.length + 2 := by simp
  obtain l3 : (ws ++ [vword v 0] ++ [vword v 1] ++ [vword v 2]).length = ws.length + 3 := by simp
  obtain k1 := h.key dKS (by omega_using [hws]) (vword v 0)
  obtain k2 := k1.key dKS (by rw [l1]; omega_using [hws]) (vword v 1)
  rw [l1] at k2
  obtain k3 := k2.key dKS (by rw [l2]; omega_using [hws]) (vword v 2)
  rw [l2] at k3
  obtain k4 := k3.key dKS (by rw [l3]; omega_using [hws]) (vword v 3)
  rw [l3] at k4
  rw [writeW_split, Proof.Cast5.add_ofNat_add, Proof.Cast5.add_ofNat_add, Proof.Cast5.add_ofNat_add]
  obtain e : ws ++ [vword v 0, vword v 1, vword v 2, vword v 3] =
      ws ++ [vword v 0] ++ [vword v 1] ++ [vword v 2] ++ [vword v 3] := by simp
  rw [e, show 4 * ws.length + 4 = 4 * (ws.length + 1) by omega_using [],
    show 4 * ws.length + 8 = 4 * (ws.length + 2) by omega_using [],
    show 4 * ws.length + 12 = 4 * (ws.length + 3) by omega_using []]
  exact k4

theorem exec_strq_w {s : State} {t : VReg} {n : Reg} {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.strq t n off) s =
      some (Proof.Cast5.AArch64.putMem s (s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) (s.v t))) := by
  rw [Proof.Blowfish.AArch64.exec_strq ho h, VG.AArch64.StraightV.write16_writeW]
  rfl

/-- The subkeys of a group stored. -/
theorem storeKeys_ok (u : State) {o : Nat} (ho : o % 16 = 0 ∧ o < 65536)
    (hw : InRegions u.wr (u.gpr .x2 + BitVec.ofNat 64 o) 16) :
    WP isa (.block (storeKeys o)) u fun w =>
      w.mem = u.mem.writeW (u.gpr .x2 + BitVec.ofNat 64 o) (u.v .v4 ^^^ u.v .v6) ∧ w.gpr = u.gpr ∧
      w.rd = u.rd ∧ w.wr = u.wr ∧ w.sp = u.sp ∧ w.syms = u.syms ∧ (∀ r, r ≠ .v4 → w.v r = u.v r) := by
  let u₁ := u.setV .v4 (u.v .v4 ^^^ u.v .v6)
  have e₁ : exec (veor .v4 .v4 .v6) u = some u₁ := rfl
  obtain e₂ : exec (.strq .v4 .x2 o) u₁ = some (Proof.Cast5.AArch64.putMem u₁
      (u₁.mem.writeW (u₁.gpr .x2 + BitVec.ofNat 64 o) (u₁.v .v4))) := exec_strq_w ho hw
  refine WP.of_runBlock ⟨Proof.Cast5.AArch64.putMem u₁ (u₁.mem.writeW (u₁.gpr .x2 + BitVec.ofNat 64 o) (u₁.v .v4)),
    by rw [storeKeys, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_nil], ?_, rfl,
    rfl, rfl, rfl, rfl, fun r hr => v_setV_of_ne _ _ hr⟩
  show u.mem.writeW _ ((u.setV .v4 _).v .v4) = _
  rw [v_setV_self]
  rfl

/-- The extra lookups of a group kept in the working space. -/
theorem storeExtras_ok (u : State) (hw : InRegions u.wr (u.gpr .x3) 64) :
    WP isa (.block [.strq .v7 .x3 extraOff]) u fun w =>
      w.mem = u.mem.writeW (u.gpr .x3 + BitVec.ofNat 64 48) (u.v .v7) ∧ w.gpr = u.gpr ∧
      w.rd = u.rd ∧ w.wr = u.wr ∧ w.sp = u.sp ∧ w.syms = u.syms ∧ w.v = u.v := by
  obtain e : exec (.strq .v7 .x3 extraOff) u = some (Proof.Cast5.AArch64.putMem u
      (u.mem.writeW (u.gpr .x3 + BitVec.ofNat 64 extraOff) (u.v .v7))) :=
    exec_strq_w (by decide) (CallLay.inRegions_sub hw (by decide) (by decide))
  exact WP.of_runBlock ⟨Proof.Cast5.AArch64.putMem u (u.mem.writeW (u.gpr .x3 + BitVec.ofNat 64 extraOff) (u.v .v7)),
    by rw [runBlock_cons, e, runStep_some, runBlock_nil], rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A word of the extra lookups, read back. -/
theorem extras_read (m : Mem) (c : Addr) (v : BitVec 128) {j : Nat} (hj : j < 4) :
    (m.writeW (c + BitVec.ofNat 64 48) v).readW (c + BitVec.ofNat 64 (48 + 4 * j)) 32 = vword v j := by
  rw [writeW_split, Proof.Cast5.add_ofNat_add, Proof.Cast5.add_ofNat_add, Proof.Cast5.add_ofNat_add]
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · rw [Mem.readW_writeW_sep (Offset.sep c (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep c (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep c (by decide) (by decide) (by decide)) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · rw [Mem.readW_writeW_sep (Offset.sep c (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep c (by decide) (by decide) (by decide)) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · rw [Mem.readW_writeW_sep (Offset.sep c (by decide) (by decide) (by decide)) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · exact Mem.readW_writeW_self32 _ _ _

/-! ## The extra lookups in the working space -/

/-- The extra lookups of a group, kept at `c + 48`. -/
def ExAt (m : Mem) (c : Addr) (f : Nat → Spec.Cast5.Word) : Prop :=
  ∀ j < 4, m.readW (c + BitVec.ofNat 64 (48 + 4 * j)) 32 = f j

theorem ExAt.quad {m : Mem} {c : Addr} {f : Nat → Spec.Cast5.Word} (h : ExAt m c f) (tgt : Arr) {k : Nat}
    (hk : k < 4) (w : Spec.Cast5.Word) : ExAt (m.writeW (c + BitVec.ofNat 64 (off tgt + 4 * k)) w) c f := by
  intro j hj
  have := off_lt tgt
  rw [Mem.readW_writeW_sep (Offset.sep c (Or.inr (by omega_using [hk, this])) (by omega_using [hj])
    (by omega_using [hk, this])) (by decide)]
  exact h j hj

theorem ExAt.keys {m : Mem} {c K : Addr} {f : Nat → Spec.Cast5.Word} (h : ExAt m c f)
    (dKS : Region.Disjoint ⟨K, 128⟩ ⟨c, 64⟩) {n : Nat} (hn : n + 4 ≤ 32) (v : BitVec 128) :
    ExAt (m.writeW (K + BitVec.ofNat 64 (4 * n)) v) c f := by
  intro j hj
  rw [Mem.readW_writeW_sep (dKS.symm.sep (Offset.contains_base c (by omega_using [hj]) (by omega_using [hj]))
    (Offset.contains_base K (by omega_using [hn]) (by omega_using [hn]))) (by decide)]
  exact h j hj

theorem idx_in_pass : ∀ j < 4, idxReg j ∈ passVRegs := by decide
theorem link_in_pass : ∀ r ∈ linkRegs, r ∈ passGprs := by decide
theorem keyV_in_pass : ∀ r ∈ keyVRegs, r ∈ passVRegs := fun _ h => List.mem_append_left _ h

/-- What a gather keeps. -/
theorem kept_gather {s u : State} (ou : ∀ r, (∀ j < 4, r ≠ idxReg j) → u.v r = s.v r)
    (gu : ∀ r, r ≠ .x10 → u.gpr r = s.gpr r) (rdu : u.rd = s.rd) (wru : u.wr = s.wr) (spu : u.sp = s.sp)
    (syu : u.syms = s.syms) : Kept s u :=
  ⟨fun r hr => gu r (by rintro rfl; exact hr (by decide)), rdu, wru, spu, syu,
    fun r hr => ou r (fun j hj => by rintro rfl; exact hr (idx_in_pass j hj))⟩

/-- What a pass keeps. -/
theorem kept_pass {u p : State} (P : Passed u p) : Kept u p :=
  ⟨fun r hr => P.gpr r (fun h => hr (link_in_pass r h)) (by rintro rfl; exact hr (by decide)), P.rd, P.wr, P.sp,
    P.syms,
    fun r hr => P.v r (fun h => hr (keyV_in_pass r h))⟩

/-! ## A line's pass -/

theorem lineOk_extra {l : Impl.Cast5.Line} (hl : lineOk l = true) : 5 ≤ l.extra.1 ∧ l.extra.1 ≤ 8 := by
  simp only [lineOk, Bool.and_eq_true, decide_eq_true_eq] at hl
  exact ⟨hl.1.1.2, hl.1.2⟩

theorem lineOk_word {l : Impl.Cast5.Line} (hl : lineOk l = true) : ∀ a q, l.word = some (a, q) → q < 4 := by
  simp only [lineOk, Bool.and_eq_true, decide_eq_true_eq] at hl
  intro a q h
  have := hl.2
  rw [h] at this
  simpa using this

/-- A line's value from its lookups. -/
theorem line_value (st : XZ) (l : Impl.Cast5.Line) (hl : lineOk l = true) (v : VReg → BitVec 128)
    (hg : ∀ g ∈ gsMain 4 l, vbyte (v (idxReg g.2.1)) g.1 = st.get g.2.2) {X : Spec.Cast5.Word}
    (hX : X = Proof.Cast5.sbox l.extra.1 (st.get l.extra.2)) {m : Mem} {c : Addr} (hm : HoldsXZ m c st) :
    withWord m c (kacc v 4 3 ^^^ X) l.word = Proof.Cast5.lineVal st l := by
  rw [line_lookups st l v hg hX]
  rcases hwd : l.word with _ | ⟨a, q⟩
  · simp only [withWord, Proof.Cast5.lineVal, hwd]
  · simp only [withWord, Proof.Cast5.lineVal, hwd, hm.quad a (lineOk_word hl a q hwd)]

/-- After a pass that looked up a line's main bytes: the line stored. -/
theorem lineStore_ok {m0 : Mem} {c K : Addr} {u p : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (hp : TS m0 c K p st ws) {l : Impl.Cast5.Line} (hl : lineOk l = true)
    (vu : ∀ g ∈ gsMain 4 l, vbyte (u.v (idxReg g.2.1)) g.1 = st.get g.2.2)
    (h5 : vword (p.v .v5) 0 = kacc u.v 4 3) {f : Nat → Spec.Cast5.Word} (hE : ExAt p.mem c f)
    (hx : f (l.extra.1 - 5) = Proof.Cast5.sbox l.extra.1 (st.get l.extra.2)) (tgt : Arr) {k : Nat} (hk : k < 4) :
    WP isa (.block (storeLine l k tgt)) p fun w =>
      TS m0 c K w (st.put tgt k (Proof.Cast5.lineVal st l)) ws ∧ ExAt w.mem c f ∧ Kept p w := by
  obtain he := lineOk_extra hl
  obtain hX : p.mem.readW (p.gpr .x3 + BitVec.ofNat 64 (extraOff + 4 * (l.extra.1 - 5))) 32 = f (l.extra.1 - 5) := by
    rw [hp.rc]; exact hE _ (by omega_using [he])
  refine WP.mono (storeLine_ok p l tgt hk hl h5 hX hp.ws (by rw [hp.rc]; exact hp.wS))
    fun w ⟨wm, wg, wrd, wwr, wv, wsp, wsy⟩ => ?_
  obtain k₃ : Kept p w := ⟨fun r hr => wg r (by rintro rfl; exact hr (by decide)) (by rintro rfl; exact hr (by decide)),
    wrd, wwr, wsp, wsy, fun r _ => by rw [wv]⟩
  rw [line_value st l hl u.v vu hx (by rw [hp.rc]; exact hp.mem.xz), hp.rc] at wm
  exact ⟨hp.next k₃ (by rw [wm]; exact hp.mem.quad hp.dKS hp.len tgt hk _) hp.len,
    by rw [wm]; exact hE.quad tgt hk _, k₃⟩

/-- A line after the first of its group: its bytes gathered, a pass, and the line stored. -/
theorem linePass_ok {m0 : Mem} {c K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : TS m0 c K s st ws) {f : Nat → Spec.Cast5.Word} (hE : ExAt s.mem c f) {l : Impl.Cast5.Line}
    (hl : lineOk l = true) (hx : f (l.extra.1 - 5) = Proof.Cast5.sbox l.extra.1 (st.get l.extra.2))
    (tgt : Arr) {k : Nat} (hk : k < 4) :
    WP isa (.seq (.block (gatherMain 4 l)) (.seq pass (.block (storeLine l k tgt)))) s fun s' =>
      TS m0 c K s' (st.put tgt k (Proof.Cast5.lineVal st l)) ws ∧ ExAt s'.mem c f ∧ Kept s s' := by
  obtain ⟨u, ru, vu, ou, gu, mu, rdu, wru, spu, syu⟩ := gather_ok st (gsMain 4 l) s (gsMain_ok (by decide) hl)
    (by simp [GsDistinct, gsMain]) h.ws (by rw [h.rc]; exact h.mem.xz)
  rw [gatherMain_eq]
  refine WP.seq (WP.of_runBlock ⟨u, ru, ?_⟩)
  obtain k₁ := kept_gather ou gu rdu wru spu syu
  obtain hu := h.next k₁ (by rw [mu]; exact h.mem) h.len
  refine WP.seq (WP.mono (pass_ok hu.consts) fun p P => ?_)
  obtain k₂ := kept_pass P
  obtain hp := hu.next k₂ (by rw [P.mem]; exact hu.mem) hu.len
  refine WP.mono (lineStore_ok hp hl vu P.line (by rw [P.mem, mu]; exact hE) hx tgt hk)
    fun w ⟨hw, wE, k₃⟩ => ⟨hw, wE, (k₁.trans k₂).trans k₃⟩

/-! ## A group's subkeys -/

/-- What a group of subkeys needs of its lines: line `k`'s extra S-box is
`S_{5+k}`, and it has no quadruple. -/
def KeysOk (kl : List Impl.Cast5.Line) : Prop :=
  GroupOk none kl ∧ ∀ k < 4, (kl.getD k default).extra.1 = 5 + k ∧ (kl.getD k default).word = none

theorem gsMain_sub_keys (kl : List Impl.Cast5.Line) {k : Nat} (hk : k < 4) :
    ∀ g ∈ gsMain k (kl.getD k default), g ∈ gsKeys kl := by
  intro g hg
  rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hg)))
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hg)))
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hg))
  · exact List.mem_append_left _ (List.mem_append_right _ hg)

/-- Subkey `k` of a group from its lookups. -/
theorem key_value (st : XZ) {kl : List Impl.Cast5.Line} (hk : KeysOk kl) (v : VReg → BitVec 128)
    (hg : ∀ g ∈ gsKeys kl, vbyte (v (idxReg g.2.1)) g.1 = st.get g.2.2) {k : Nat} (h4 : k < 4) :
    kacc v k 3 ^^^ kbox v k 8 = Proof.Cast5.lineVal st (kl.getD k default) := by
  obtain ⟨he, hw⟩ := hk.2 k h4
  obtain hex := (hk.1.1 k h4).2.1
  rw [he] at hex
  obtain hX : kbox v k 8 = Proof.Cast5.sbox (kl.getD k default).extra.1 (st.get (kl.getD k default).extra.2) := by
    have := hg (8, k, extraOf kl (5 + k)) (by
      rcases (by omega_using [h4] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
        simp [gsKeys, gsExtras])
    simp only at this
    rw [kbox, this, sbox_k h4, hex, he]
  rw [line_lookups st _ v (fun g hg' => hg g (gsMain_sub_keys kl h4 g hg')) hX]
  simp only [Proof.Cast5.lineVal, hw]

/-- After a pass that looked up a group of subkeys: the subkeys stored. -/
theorem keysStore_ok {m0 : Mem} {c K : Addr} {u p : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (hp : TS m0 c K p st ws) {kl : List Impl.Cast5.Line} (hk : KeysOk kl)
    (vu : ∀ g ∈ gsKeys kl, vbyte (u.v (idxReg g.2.1)) g.1 = st.get g.2.2)
    (h4 : ∀ l < 4, vword (p.v .v4) l = kacc u.v l 3) (h6 : ∀ i < 4, vword (p.v .v6) i = kbox u.v i 8)
    {ko : Nat} (ho : ko % 16 = 0 ∧ ko < 65536)
    (hx2 : p.gpr .x2 + BitVec.ofNat 64 ko = K + BitVec.ofNat 64 (4 * ws.length)) (hlen : ws.length + 4 ≤ 32) :
    WP isa (.block (storeKeys ko)) p fun w =>
      TS m0 c K w st (ws ++ Proof.Cast5.keys4 kl st) ∧
      w.mem = p.mem.writeW (K + BitVec.ofNat 64 (4 * ws.length)) (p.v .v4 ^^^ p.v .v6) ∧ Kept p w ∧
      w.v .v5 = p.v .v5 := by
  obtain hw : InRegions p.wr (p.gpr .x2 + BitVec.ofNat 64 ko) 16 := by
    rw [hx2]; exact CallLay.inRegions_sub hp.wK (by omega_using [hlen]) (by decide)
  refine WP.mono (storeKeys_ok p ho hw) fun w ⟨wm, wg, wrd, wwr, wsp, wsy, wv⟩ => ?_
  obtain k₃ : Kept p w := ⟨fun r _ => by rw [wg], wrd, wwr, wsp, wsy,
    fun r hr => wv r (by rintro rfl; exact hr (by decide))⟩
  rw [hx2] at wm
  obtain val : ∀ k < 4, vword (p.v .v4 ^^^ p.v .v6) k = Proof.Cast5.lineVal st (kl.getD k default) := fun k hk4 => by
    rw [vword_xor, h4 k hk4, h6 k hk4, key_value st hk u.v vu hk4]
  obtain e : [vword (p.v .v4 ^^^ p.v .v6) 0, vword (p.v .v4 ^^^ p.v .v6) 1, vword (p.v .v4 ^^^ p.v .v6) 2,
      vword (p.v .v4 ^^^ p.v .v6) 3] = Proof.Cast5.keys4 kl st := by
    rw [val 0 (by decide), val 1 (by decide), val 2 (by decide), val 3 (by decide)]; rfl
  obtain km := kmem_keys4 hp.mem hp.dKS hlen (p.v .v4 ^^^ p.v .v6)
  rw [e] at km
  exact ⟨hp.next k₃ (by rw [wm]; exact km) (by
      rw [List.length_append, show (Proof.Cast5.keys4 kl st).length = 4 from rfl]; exact hlen),
    wm, k₃, wv _ (by decide)⟩

/-! ## A group of four lines -/

/-- The extra lookups of a group from `st`. -/
def exF (st : XZ) (ls : List Impl.Cast5.Line) : Nat → Spec.Cast5.Word :=
  fun j => Proof.Cast5.sbox (5 + j) (st.get (extraOf ls (5 + j)))

/-- A line's extra lookup among its group's, while the group runs. -/
theorem exF_line (st : XZ) {tgt : Arr} {ls : List Impl.Cast5.Line} (hg : GroupOk (some tgt) ls) {k : Nat}
    (hk : k < 4) (n : Nat) :
    exF st ls ((ls.getD k default).extra.1 - 5) =
      Proof.Cast5.sbox (ls.getD k default).extra.1 ((Proof.Cast5.runQ tgt ls n st).get (ls.getD k default).extra.2) := by
  obtain ⟨hok, hex, hna⟩ := hg.1 k hk
  obtain he := lineOk_extra hok
  rw [exF, show 5 + ((ls.getD k default).extra.1 - 5) = (ls.getD k default).extra.1 by omega_using [he], hex,
    Proof.Cast5.get_runQ _ _ _ _ fun e => hna (by rw [e])]

/-- The bytes of a group's first pass. -/
def gsFirst (ls : List Impl.Cast5.Line) (kl : List Impl.Cast5.Line) (keys : Bool) : Gs :=
  gsMain 4 (ls.getD 0 default) ++ gsExtras 5 ls ++ (if keys then gsKeys kl else [])

/-- A gather is distinct when its registers and lanes, which are literals, are. -/
private theorem gsDistinct_of_keys {gs : Gs} (ks : List (Nat × Nat)) (e : gs.map (fun g => (g.2.1, g.1)) = ks)
    (h : ks.Pairwise fun a b => ¬(a.1 = b.1 ∧ a.2 = b.2)) : GsDistinct gs := by
  subst e; exact List.pairwise_map.mp h

theorem gsFirst_distinct (ls kl : List Impl.Cast5.Line) (keys : Bool) : GsDistinct (gsFirst ls kl keys) := by
  cases keys
  · exact gsDistinct_of_keys [(0, 4), (1, 4), (2, 4), (3, 4), (0, 5), (1, 5), (2, 5), (3, 5)] rfl (by decide)
  · exact gsDistinct_of_keys [(0, 4), (1, 4), (2, 4), (3, 4), (0, 5), (1, 5), (2, 5), (3, 5),
      (0, 0), (1, 0), (2, 0), (3, 0), (0, 1), (1, 1), (2, 1), (3, 1), (0, 2), (1, 2), (2, 2), (3, 2),
      (0, 3), (1, 3), (2, 3), (3, 3), (0, 8), (1, 8), (2, 8), (3, 8)] rfl (by decide)

theorem gsFirst_ok {tgt : Arr} {ls kl : List Impl.Cast5.Line} (hg : GroupOk (some tgt) ls) {keys : Bool}
    (hk : keys = true → KeysOk kl) : GsOk (gsFirst ls kl keys) := by
  refine ((gsMain_ok (by decide) (hg.1 0 (by decide)).1).append (gsExtras_ok (by decide) hg.2)).append ?_
  cases keys
  · exact fun g hg' => absurd hg' List.not_mem_nil
  · exact gsKeys_ok (hk rfl).1

theorem gatherFirst_eq (ls kl : List Impl.Cast5.Line) (keys : Bool) :
    gatherMain 4 (ls.getD 0 default) ++ gatherExtras 5 ls ++ (if keys then gatherKeys kl else []) =
      gatherL (gsFirst ls kl keys) := by
  cases keys <;> rfl

theorem group4_ok {m0 : Mem} {c K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : TS m0 c K s st ws) (tgt : Arr) {ls : List Impl.Cast5.Line} (hg : GroupOk (some tgt) ls)
    {kl : List Impl.Cast5.Line} {ko : Nat} (keys : Bool)
    (hkeys : keys = true → KeysOk kl ∧ (ko % 16 = 0 ∧ ko < 65536) ∧
      s.gpr .x2 + BitVec.ofNat 64 ko = K + BitVec.ofNat 64 (4 * ws.length) ∧ ws.length + 4 ≤ 32) :
    WP isa (group4 ls tgt kl ko keys) s fun u =>
      TS m0 c K u (Proof.Cast5.runQ tgt ls 4 st) (if keys then ws ++ Proof.Cast5.keys4 kl st else ws) ∧
        Kept s u := by
  obtain hl0 := (hg.1 0 (by decide)).1
  obtain ⟨u, ru, vu, ou, gu, mu, rdu, wru, spu, syu⟩ := gather_ok st (gsFirst ls kl keys) s
    (gsFirst_ok hg fun hk => (hkeys hk).1) (gsFirst_distinct ls kl keys) h.ws (by rw [h.rc]; exact h.mem.xz)
  obtain vu₀ : ∀ g ∈ gsMain 4 (ls.getD 0 default), vbyte (u.v (idxReg g.2.1)) g.1 = st.get g.2.2 :=
    fun g hg' => vu g (List.mem_append_left _ (List.mem_append_left _ hg'))
  obtain vuE : ∀ j < 4, vbyte (u.v (idxReg j)) 5 = st.get (extraOf ls (5 + j)) := fun j hj => by
    obtain hmem : (5, j, extraOf ls (5 + j)) ∈ gsExtras 5 ls := by
      rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
        simp [gsExtras]
    exact vu _ (List.mem_append_left _ (List.mem_append_right _ hmem))
  unfold group4
  rw [gatherFirst_eq]
  refine WP.seq (WP.of_runBlock ⟨u, ru, ?_⟩)
  obtain k₁ := kept_gather ou gu rdu wru spu syu
  obtain hu := h.next k₁ (by rw [mu]; exact h.mem) h.len
  refine WP.seq (WP.mono (pass_ok hu.consts) fun p P => ?_)
  obtain k₂ := kept_pass P
  obtain hp := hu.next k₂ (by rw [P.mem]; exact hu.mem) hu.len
  -- the group's extra lookups to the working space
  refine WP.seq ?_
  rw [List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono (storeExtras_ok p (by rw [hp.rc]; exact hp.wS))
    fun q ⟨qm, qg, qrd, qwr, qsp, qsy, qv⟩ => ?_)
  obtain k₃ : Kept p q := ⟨fun r _ => by rw [qg], qrd, qwr, qsp, qsy, fun r _ => by rw [qv]⟩
  rw [hp.rc] at qm
  obtain qk : KMem m0 (p.mem.writeW (c + BitVec.ofNat 64 48) (p.v .v7)) c K st ws :=
    KMem.write (d := 48) hp.mem hp.dKS hp.len (p.v .v7) (by decide) (Or.inr (by decide))
  obtain hq := hp.next k₃ (by rw [qm]; exact qk) hp.len
  obtain qE : ExAt q.mem c (exF st ls) := fun j hj => by
    rw [qm, extras_read _ _ _ hj, P.extras j hj, kbox, vuE j hj, sbox_k hj]; rfl
  -- the subkeys, if any
  obtain mid : WP isa (.block (if keys then storeKeys ko else [])) q fun r =>
      TS m0 c K r st (if keys then ws ++ Proof.Cast5.keys4 kl st else ws) ∧ ExAt r.mem c (exF st ls) ∧
        Kept q r ∧ r.v .v5 = q.v .v5 := by
    cases keys
    · exact WP.block_nil ⟨hq, qE, Kept.refl q, rfl⟩
    · obtain ⟨hk, ho, hx2, hlen⟩ := hkeys rfl
      refine WP.mono (keysStore_ok hq hk (fun g hg' => vu g (List.mem_append_right _ hg'))
        (fun l hl => by rw [qv]; exact P.keys l hl) (fun i hi => by rw [qv]; exact P.kextras i hi) ho
        (by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide)]; exact hx2) hlen)
        fun r ⟨hr, rm, k₄, r5⟩ => ⟨hr, by rw [rm]; exact qE.keys hq.dKS hlen _, k₄, r5⟩
  refine WP.block_append_iff.mpr (WP.mono mid fun r ⟨hr, rE, k₄, r5⟩ => ?_)
  -- the first line
  refine WP.mono (lineStore_ok hr hl0 vu₀ (by rw [r5, qv]; exact P.line) rE (exF_line st hg (by decide) 0) tgt
    (by decide : 0 < 4)) fun w₀ ⟨hw₀, wE₀, k₅⟩ => ?_
  obtain k₀ := (((k₁.trans k₂).trans k₃).trans k₄).trans k₅
  -- the other lines
  obtain e₁ : st.put tgt 0 (Proof.Cast5.lineVal st (ls.getD 0 default)) = Proof.Cast5.runQ tgt ls 1 st :=
    (Proof.Cast5.runQ_succ tgt ls 0 st).symm
  rw [e₁] at hw₀
  refine WP.seq (WP.mono (linePass_ok hw₀ wE₀ (hg.1 1 (by decide)).1 (exF_line st hg (by decide) 1) tgt
    (by decide : 1 < 4)) fun w₁ ⟨hw₁, wE₁, j₁⟩ => ?_)
  rw [← Proof.Cast5.runQ_succ] at hw₁
  refine WP.seq (WP.mono (linePass_ok hw₁ wE₁ (hg.1 2 (by decide)).1 (exF_line st hg (by decide) 2) tgt
    (by decide : 2 < 4)) fun w₂ ⟨hw₂, wE₂, j₂⟩ => ?_)
  rw [← Proof.Cast5.runQ_succ] at hw₂
  refine WP.mono (linePass_ok hw₂ wE₂ (hg.1 3 (by decide)).1 (exF_line st hg (by decide) 3) tgt
    (by decide : 3 < 4)) fun w₃ ⟨hw₃, _, j₃⟩ => ?_
  rw [← Proof.Cast5.runQ_succ] at hw₃
  exact ⟨hw₃, ((k₀.trans j₁).trans j₂).trans j₃⟩

/-! ## A half -/

/-- The general-purpose registers a half writes. -/
def halfGprs : List Reg := passGprs ++ [.x1, .x2]

/-- What a half keeps. -/
structure KeptH (s s' : State) : Prop where
  gpr : ∀ r, r ∉ halfGprs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  syms : s'.syms = s.syms
  v : ∀ r, r ∉ passVRegs → s'.v r = s.v r

theorem KeptH.refl (s : State) : KeptH s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem KeptH.trans {a b c : State} (h₁ : KeptH a b) (h₂ : KeptH b c) : KeptH a c :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp,
    h₂.syms.trans h₁.syms, fun r hr => (h₂.v r hr).trans (h₁.v r hr)⟩

theorem Kept.toH {s u : State} (k : Kept s u) : KeptH s u :=
  ⟨fun r hr => k.gpr r (fun h => hr (List.mem_append_left _ h)), k.rd, k.wr, k.sp, k.syms, k.v⟩

theorem gsKeys_distinct (kl : List Impl.Cast5.Line) : GsDistinct (gsKeys kl) :=
  gsDistinct_of_keys [(0, 0), (1, 0), (2, 0), (3, 0), (0, 1), (1, 1), (2, 1), (3, 1), (0, 2), (1, 2), (2, 2), (3, 2),
    (0, 3), (1, 3), (2, 3), (3, 3), (0, 8), (1, 8), (2, 8), (3, 8)] rfl (by decide)

/-- The last subkeys of a half: their pass, then `x2` and the count of halves. -/
theorem keysPass_ok {m0 : Mem} {c K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : TS m0 c K s st ws) {kl : List Impl.Cast5.Line} (hk : KeysOk kl) {ko : Nat}
    (ho : ko % 16 = 0 ∧ ko < 65536)
    (hx2 : s.gpr .x2 + BitVec.ofNat 64 ko = K + BitVec.ofNat 64 (4 * ws.length)) (hlen : ws.length + 4 ≤ 32) :
    WP isa (.seq (.block (gatherKeys kl)) (.seq pass
      (.block (storeKeys ko ++ ([.addImm .x .x2 .x2 64, .subImm .x .x1 .x1 1] : List Instr))))) s fun u =>
      TS m0 c K u st (ws ++ Proof.Cast5.keys4 kl st) ∧ u.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 64 ∧
        u.gpr .x1 = s.gpr .x1 - BitVec.ofNat 64 1 ∧ KeptH s u := by
  obtain ⟨u, ru, vu, ou, gu, mu, rdu, wru, spu, syu⟩ := gather_ok st (gsKeys kl) s (gsKeys_ok hk.1)
    (gsKeys_distinct kl) h.ws (by rw [h.rc]; exact h.mem.xz)
  rw [gatherKeys_eq]
  refine WP.seq (WP.of_runBlock ⟨u, ru, ?_⟩)
  obtain k₁ := kept_gather ou gu rdu wru spu syu
  obtain hu := h.next k₁ (by rw [mu]; exact h.mem) h.len
  refine WP.seq (WP.mono (pass_ok hu.consts) fun p P => ?_)
  obtain k₂ := kept_pass P
  obtain hp := hu.next k₂ (by rw [P.mem]; exact hu.mem) hu.len
  refine WP.block_append_iff.mpr (WP.mono (keysStore_ok hp hk vu P.keys P.kextras ho
    (by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide)]; exact hx2) hlen) fun r ⟨hr, _, k₃, _⟩ => ?_)
  obtain k := (k₁.trans k₂).trans k₃
  let r₁ := r.write .x .x2 (r.gpr .x2 + BitVec.ofNat 64 64)
  let r₂ := r₁.write .x .x1 (r₁.gpr .x1 - BitVec.ofNat 64 1)
  obtain e₁ : exec (.addImm .x .x2 .x2 64) r = some r₁ := Proof.Cast5.AArch64.exec_addImm_x' (by decide)
  obtain e₂ : exec (.subImm .x .x1 .x1 1) r₁ = some r₂ := Proof.Cast5.AArch64.exec_subImm_x' (by decide)
  obtain g₂ : ∀ x, x ≠ .x1 → x ≠ .x2 → r₂.gpr x = r.gpr x := fun x h1 h2 => by
    show ((r.write .x .x2 _).write .x .x1 _).gpr x = _
    rw [gpr_write_of_ne _ _ _ h1, gpr_write_of_ne _ _ _ h2]
  refine WP.of_runBlock ⟨r₂, by rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_nil],
    ⟨(g₂ _ (by decide) (by decide)).trans hr.rc, hr.mem, hr.len, hr.wS, hr.wK, hr.dKS, hr.consts⟩, ?_, ?_,
    ⟨fun x hx => (g₂ x (fun e => hx (by rw [e]; decide)) (fun e => hx (by rw [e]; decide))).trans
      (k.gpr x (fun h' => hx (List.mem_append_left _ h'))), k.rd, k.wr, k.sp, k.syms, k.v⟩⟩
  · show ((r.write .x .x2 _).write .x .x1 _).gpr .x2 = _
    rw [gpr_write_of_ne _ _ _ (by decide), gpr_write_self, k.gpr _ (by decide)]
    exact BitVec.setWidth_eq _
  · show ((r.write .x .x2 _).write .x .x1 _).gpr .x1 = _
    rw [gpr_write_self]
    show BitVec.setWidth 64 ((r.write .x .x2 _).gpr .x1 - _) = _
    rw [gpr_write_of_ne _ _ _ (by decide), k.gpr _ (by decide)]
    exact BitVec.setWidth_eq _

theorem gZ : GroupOk (some .z) zLines := by unfold GroupOk; decide
theorem gX : GroupOk (some .x) xLines := by unfold GroupOk; decide
theorem kA : KeysOk aLines := ⟨by unfold GroupOk; decide, by decide⟩
theorem kB : KeysOk bLines := ⟨by unfold GroupOk; decide, by decide⟩
theorem kC : KeysOk cLines := ⟨by unfold GroupOk; decide, by decide⟩
theorem kD : KeysOk dLines := ⟨by unfold GroupOk; decide, by decide⟩

theorem halfTbl_ok {m0 : Mem} {c K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : TS m0 c K s st ws) {hh : Nat} (hdx : s.gpr .x2 = K + BitVec.ofNat 64 (64 * hh))
    (hlen : ws.length = 16 * hh) (hle : hh < 2) :
    WP isa halfTbl s fun u =>
      TS m0 c K u (Proof.Cast5.halfImpl st).2 (ws ++ (Proof.Cast5.halfImpl st).1) ∧
      u.gpr .x2 = K + BitVec.ofNat 64 (64 * (hh + 1)) ∧ u.gpr .x1 = s.gpr .x1 - BitVec.ofNat 64 1 ∧
      KeptH s u := by
  have l4 (ls : List Impl.Cast5.Line) (t : XZ) : (Proof.Cast5.keys4 ls t).length = 4 := rfl
  unfold halfTbl
  refine WP.seq (WP.mono (group4_ok h .z gZ (kl := []) (ko := 0) false (fun e => absurd e (by decide)))
    fun u1 ⟨h1, k1⟩ => ?_)
  rw [Proof.Cast5.runQ_z] at h1
  simp only [Bool.false_eq_true, ite_false] at h1
  obtain x1 : u1.gpr .x2 = K + BitVec.ofNat 64 (64 * hh) := (k1.gpr _ (by decide)).trans hdx
  refine WP.seq (WP.mono (group4_ok h1 .x gX (kl := aLines) (ko := 0) true fun _ => ⟨kA, by decide,
    by rw [x1, Proof.Cast5.add_ofNat_add, hlen]; exact congrArg (fun n => K + BitVec.ofNat 64 n) (by omega_using []),
    by omega_using [hlen, hle]⟩) fun u2 ⟨h2, k2⟩ => ?_)
  rw [Proof.Cast5.runQ_x] at h2
  simp only [ite_true] at h2
  obtain x2 : u2.gpr .x2 = K + BitVec.ofNat 64 (64 * hh) := (k2.gpr _ (by decide)).trans x1
  refine WP.seq (WP.mono (group4_ok h2 .z gZ (kl := bLines) (ko := 16) true fun _ => ⟨kB, by decide,
    by rw [x2, Proof.Cast5.add_ofNat_add, List.length_append, hlen, l4]
       exact congrArg (fun n => K + BitVec.ofNat 64 n) (by omega_using []),
    by rw [List.length_append, hlen, l4]; omega_using [hle]⟩) fun u3 ⟨h3, k3⟩ => ?_)
  rw [Proof.Cast5.runQ_z] at h3
  simp only [ite_true] at h3
  obtain x3 : u3.gpr .x2 = K + BitVec.ofNat 64 (64 * hh) := (k3.gpr _ (by decide)).trans x2
  refine WP.seq (WP.mono (group4_ok h3 .x gX (kl := cLines) (ko := 32) true fun _ => ⟨kC, by decide,
    by rw [x3, Proof.Cast5.add_ofNat_add, List.length_append, List.length_append, hlen, l4, l4]
       exact congrArg (fun n => K + BitVec.ofNat 64 n) (by omega_using []),
    by rw [List.length_append, List.length_append, hlen, l4, l4]; omega_using [hle]⟩) fun u4 ⟨h4, k4⟩ => ?_)
  rw [Proof.Cast5.runQ_x] at h4
  simp only [ite_true] at h4
  obtain x4 : u4.gpr .x2 = K + BitVec.ofNat 64 (64 * hh) := (k4.gpr _ (by decide)).trans x3
  refine WP.mono (keysPass_ok h4 kD (ko := 48) (by decide)
    (by rw [x4, Proof.Cast5.add_ofNat_add, List.length_append, List.length_append, List.length_append, hlen, l4,
          l4, l4]
        exact congrArg (fun n => K + BitVec.ofNat 64 n) (by omega_using []))
    (by rw [List.length_append, List.length_append, List.length_append, hlen, l4, l4, l4]; omega_using [hle]))
    fun u5 ⟨h5, x5, c5, k5⟩ => ?_
  obtain k14 := ((k1.trans k2).trans k3).trans k4
  obtain hks : ws ++ (Proof.Cast5.halfImpl st).1 = ws ++ Proof.Cast5.keys4 aLines (Proof.Cast5.runZ zLines st) ++
      Proof.Cast5.keys4 bLines (Proof.Cast5.runX xLines (Proof.Cast5.runZ zLines st)) ++
      Proof.Cast5.keys4 cLines (Proof.Cast5.runZ zLines (Proof.Cast5.runX xLines (Proof.Cast5.runZ zLines st))) ++
      Proof.Cast5.keys4 dLines (Proof.Cast5.runX xLines (Proof.Cast5.runZ zLines (Proof.Cast5.runX xLines
        (Proof.Cast5.runZ zLines st)))) := by
    simp only [Proof.Cast5.halfImpl, List.append_assoc]
  rw [hks]
  refine ⟨h5, ?_, by rw [c5, k14.gpr _ (by decide)], k14.toH.trans k5⟩
  rw [x5, x4, Proof.Cast5.add_ofNat_add, Nat.mul_succ]

/-! ## The key into `x` -/

/-- `x` while the key is copied: the first `j` key bytes, then zeros; `z`
as it was; and only the working space written. -/
structure CInv (m0 : Mem) (key c : Addr) (j : Nat) (m : Mem) : Prop where
  x : ∀ i < 16, m (c + BitVec.ofNat 64 (16 + i)) = if i < j then m0 (key + BitVec.ofNat 64 i) else 0
  z : ∀ i < 16, m (c + BitVec.ofNat 64 (32 + i)) = m0 (c + BitVec.ofNat 64 (32 + i))
  fr : Frame [⟨c, 64⟩] m0 m

theorem zero_byte (m : Mem) (c : Addr) {d e : Nat} (hd : d + 8 ≤ 2 ^ 63) (he : e < 2 ^ 63) :
    (m.writeW (c + BitVec.ofNat 64 d) (BitVec.setWidth 64 (0 : BitVec 16))) (c + BitVec.ofNat 64 e) =
      if d ≤ e ∧ e < d + 8 then 0 else m (c + BitVec.ofNat 64 e) := by
  simp only [Mem.writeW]
  rw [byte_write m c _ hd he]
  split
  · simp
  · rfl

theorem zero_ok (s : State) (key : Addr) (hw : InRegions s.wr (s.gpr .x3) 64) :
    WP isa (.block [.movz .x .x9 0 0, .str .x .x9 .x3 xOff, .str .x .x9 .x3 (xOff + 8),
      .addImm .x .x4 .x3 xOff]) s fun u =>
      CInv s.mem key (s.gpr .x3) 0 u.mem ∧ u.gpr .x4 = s.gpr .x3 + BitVec.ofNat 64 16 ∧
      (∀ r, r ≠ .x4 → r ≠ .x9 → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.syms = s.syms := by
  obtain h16 : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 16) 8 := CallLay.inRegions_sub hw (by decide) (by decide)
  obtain h24 : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 24) 8 := CallLay.inRegions_sub hw (by decide) (by decide)
  unfold xOff
  crun [h16, h24, Nat.reduceAdd]
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_⟩, fun r h4 h9 => ?_⟩
  · rw [zero_byte _ _ (by decide) (by omega_using [hi]), zero_byte _ _ (by decide) (by omega_using [hi])]
    split <;> split <;> first | rfl | omega
  · rw [zero_byte _ _ (by decide) (by omega_using [hi]), zero_byte _ _ (by decide) (by omega_using [hi]), ite_eq_right (by omega_using []),
      ite_eq_right (by omega_using [])]
  · exact ((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))
  · simp only [h4, h9, ite_false]

theorem add_one' (p : Addr) (a : Nat) : p + BitVec.ofNat 64 a + 1#64 = p + BitVec.ofNat 64 (a + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem copyStep_ok (u : State) {m0 : Mem} {key c : Addr} {j : Nat} (hj : j < 16) (hI : CInv m0 key c j u.mem)
    (hdi : u.gpr .x0 = key + BitVec.ofNat 64 j) (hax : u.gpr .x4 = c + BitVec.ofNat 64 (16 + j))
    (hr : InRegions (u.rd ++ u.wr) (key + BitVec.ofNat 64 j) 1)
    (hw : InRegions u.wr (c + BitVec.ofNat 64 (16 + j)) 1)
    (hk : u.mem (key + BitVec.ofNat 64 j) = m0 (key + BitVec.ofNat 64 j)) :
    WP isa (.block copyStep) u fun v =>
      CInv m0 key c (j + 1) v.mem ∧ v.gpr .x0 = key + BitVec.ofNat 64 (j + 1) ∧
      v.gpr .x4 = c + BitVec.ofNat 64 (16 + (j + 1)) ∧ v.gpr .x1 = u.gpr .x1 - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .x4 → r ≠ .x0 → r ≠ .x1 → r ≠ .x9 → v.gpr r = u.gpr r) ∧
      v.rd = u.rd ∧ v.wr = u.wr ∧ v.syms = u.syms := by
  obtain hr' : InRegions (u.rd ++ u.wr) (u.gpr .x0 + BitVec.ofNat 64 0) 1 := by rw [BitVec.add_zero, hdi]; exact hr
  obtain hw' : InRegions u.wr (u.gpr .x4 + BitVec.ofNat 64 0) 1 := by rw [BitVec.add_zero, hax]; exact hw
  obtain hk' : u.mem (u.gpr .x0 + BitVec.ofNat 64 0) = m0 (key + BitVec.ofNat 64 j) := by
    rw [BitVec.add_zero, hdi]; exact hk
  unfold copyStep
  crun [hr', hw', hk']
  simp only [BitVec.add_zero, hdi, hax, add_one']
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_⟩, trivial, by rw [Nat.add_assoc], fun r h1 h2 h3 h4 => ?_⟩
  · simp only [Mem.writeW]
    rw [byte_write _ _ _ (by omega_using [hj]) (by omega_using [hi])]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left ⟨Nat.le_refl _, by omega_using []⟩, ite_eq_left (by omega_using []), Nat.sub_self]
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      simp [hk]
    · rw [ite_eq_right (by omega_using [hij]), hI.x i hi]
      by_cases hl : i < j
      · rw [ite_eq_left hl, ite_eq_left (by omega_using [hl])]
      · rw [ite_eq_right hl, ite_eq_right (by omega_using [hij, hl])]
  · simp only [Mem.writeW]
    rw [byte_write _ _ _ (by omega_using [hj]) (by omega_using [hi]), ite_eq_right (by omega_using [hj])]
    exact hI.z i hi
  · exact hI.fr.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
  · simp only [h1, h2, h3, h4, ite_false]


/-! ## Key expansion -/

/-- The facts of key expansion's precondition (the shared contract's,
`Spec.Cast5.expandKeyContract`). -/
structure TPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩]
  wr : s.wr = [⟨s.gpr .x2, 128⟩, ⟨s.gpr .x3, 256⟩]
  dkK : Region.Disjoint ⟨s.gpr .x0, (s.gpr .x1).toNat⟩ ⟨s.gpr .x2, 128⟩
  dkS : Region.Disjoint ⟨s.gpr .x0, (s.gpr .x1).toNat⟩ ⟨s.gpr .x3, 256⟩
  dKS : Region.Disjoint ⟨s.gpr .x2, 128⟩ ⟨s.gpr .x3, 256⟩
  fk : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  fK : (s.gpr .x2).toNat + 128 ≤ 2 ^ 64
  fS : (s.gpr .x3).toNat + 256 ≤ 2 ^ 64
  len : 5 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 16

/-- The count of halves, the return address to `x15`, and the constants. -/
theorem setupKey_run (u : State) :
    ∃ w, runBlock isa (([.movz .x .x1 2 0, .addImm .x .x15 .x30 0] : List Instr) ++ constants) u = some w ∧
      w.gpr .x1 = BitVec.ofNat 64 2 ∧ w.gpr .x15 = u.gpr .x30 ∧
      (∀ r, r ≠ .x1 → r ≠ .x15 → r ≠ .x6 → w.gpr r = u.gpr r) ∧ Consts w ∧ w.mem = u.mem ∧
      w.rd = u.rd ∧ w.wr = u.wr ∧ w.sp = u.sp ∧ w.syms = u.syms ∧
      (∀ r, r ≠ c64 → r ≠ c128 → w.v r = u.v r) := by
  let u₁ := u.write .x .x1 ((2 : BitVec 16).setWidth 64)
  let u₂ := u₁.write .x .x15 (u₁.gpr .x30 + BitVec.ofNat 64 0)
  have e₁ : exec (.movz .x .x1 2 0) u = some u₁ := Proof.Cast5.AArch64.exec_movz_x'
  obtain e₂ : exec (.addImm .x .x15 .x30 0) u₁ = some u₂ := Proof.Cast5.AArch64.exec_addImm_x' (by decide)
  obtain r₂ : runBlock isa ([.movz .x .x1 2 0, .addImm .x .x15 .x30 0] : List Instr) u = some u₂ := by
    rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_nil]
  obtain ⟨u₃, r₃, c₃, g₃, m₃, rd₃, wr₃, sp₃, o₃⟩ := constants_run u₂
  obtain sy₃ : u₃.syms = u.syms := (vonly_syms o₃).trans rfl
  obtain g₂ : ∀ r, r ≠ .x1 → r ≠ .x15 → u₂.gpr r = u.gpr r := fun r h1 h15 => by
    show ((u.write .x .x1 _).write .x .x15 _).gpr r = _
    rw [gpr_write_of_ne _ _ _ h15, gpr_write_of_ne _ _ _ h1]
  refine ⟨u₃, cat_run r₂ r₃, ?_, ?_, fun r h1 h15 h6 => ?_, c₃, m₃, rd₃, wr₃, sp₃, sy₃,
    fun r h64 h128 => ?_⟩
  · rw [g₃ _ (by decide)]
    show ((u.write .x .x1 _).write .x .x15 _).gpr .x1 = _
    rw [gpr_write_of_ne _ _ _ (by decide), gpr_write_self]
    rfl
  · rw [g₃ _ (by decide)]
    show ((u.write .x .x1 _).write .x .x15 _).gpr .x15 = _
    rw [gpr_write_self]
    show BitVec.setWidth 64 ((u.write .x .x1 _).gpr .x30 + BitVec.ofNat 64 0) = _
    rw [gpr_write_of_ne _ _ _ (by decide), BitVec.add_zero]
    exact BitVec.setWidth_eq _
  · rw [g₃ r h6, g₂ r h1 h15]
  · rw [o₃.2 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h64, h128⟩)]
    rfl

theorem saved_not_half : ∀ r ∈ preserved, r ≠ .x30 →
    r ∉ halfGprs ∧ r ≠ .x1 ∧ r ≠ .x15 ∧ r ≠ .x6 ∧ r ≠ .x9 ∧ r ∉ [Reg.x4, .x0, .x1, .x9] ∧ r ∉ [Reg.x4, .x9] := by
  decide

theorem savedV_not_pass : ∀ r ∈ preservedV, r ∉ passVRegs ∧ r ≠ c64 ∧ r ≠ c128 := by decide

theorem expandKey_ok (s : State) (h : TPre s) :
    WP isa expandKey s fun u =>
      Spec.Cast5.scheduleAt u.mem (s.gpr .x2) =
        Spec.Cast5.expandKey (Spec.Cast5.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) ∧ abiPreserved s u := by
  obtain ⟨n, hn⟩ : ∃ n, (s.gpr .x1).toNat = n := ⟨_, rfl⟩
  obtain ⟨key, hkey⟩ : ∃ key, s.gpr .x0 = key := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, s.gpr .x3 = c := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, s.gpr .x2 = K := ⟨_, rfl⟩
  have hl := h.len
  rw [hn] at hl
  obtain hwS : InRegions s.wr c 256 := by
    rw [h.wr, hc]; exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.contains_self _ _⟩
  obtain hwK : InRegions s.wr K 128 := by
    rw [h.wr, hK]; exact ⟨_, List.mem_cons_self, Region.contains_self _ _⟩
  obtain hw64 : InRegions s.wr c 64 := by
    have := CallLay.inRegions_sub hwS (off := 0) (l := 64) (by decide) (by decide)
    rwa [BitVec.add_zero] at this
  obtain hrK : InRegions (s.rd ++ s.wr) key n := by
    rw [h.rd, hkey, hn]; exact ⟨_, List.mem_cons_self, Region.contains_self _ _⟩
  obtain dkc : Region.Disjoint ⟨key, n⟩ ⟨c, 64⟩ := by
    have := h.dkS; rw [hkey, hn, hc] at this; exact this.sub_right (Region.sub_prefix (by decide))
  unfold expandKey
  refine WP.seq (WP.mono (Proof.Cast5.AArch64.WP.keep [.x4, .x9] (zero_ok s key (by rw [hc]; exact hw64))
    (by decide)) fun u0 ⟨⟨c0, ax0, g0, rd0, wr0, sy0⟩, kp0⟩ => ?_)
  rw [hc] at c0 ax0
  have hkb (j : Nat) (hj : j < n) (m : Mem) (hf : Frame [⟨c, 64⟩] s.mem m) :
      m (key + BitVec.ofNat 64 j) = s.mem (key + BitVec.ofNat 64 j) := by
    refine hf.bytes (R := ⟨key, n⟩) (fun r hr => ?_) (by show n ≤ 2 ^ 64; omega_using [hn]) hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hr]; exact dkc
  obtain hsi0 : u0.gpr .x1 = BitVec.ofNat 64 n := by
    rw [g0 _ (by decide) (by decide), ← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (Proof.Cast5.AArch64.WP.keep [.x4, .x0, .x1, .x9]
    (wp_countdown (cnt := .x1) (N := n) (by omega_using [hn]) (by omega_using [hl])
    (fun j u => CInv s.mem key c j u.mem ∧ u.gpr .x0 = key + BitVec.ofNat 64 j ∧
      u.gpr .x4 = c + BitVec.ofNat 64 (16 + j) ∧ (∀ r, r ∉ [Reg.x4, .x0, .x1, .x9] → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.syms = s.syms)
    (fun j hj u ⟨cu, du, au, gu, rdu, wru, syu⟩ _ => WP.mono (copyStep_ok u (by omega_using [hl, hj]) cu du au
      (by rw [rdu, wru]; exact CallLay.inRegions_sub hrK (by omega_using [hj]) (by omega_using [hn]))
      (by rw [wru]; exact CallLay.inRegions_sub hw64 (by omega_using [hl, hj]) (by decide))
      (hkb j hj u.mem cu.fr))
      fun v ⟨cv, dv, av, sv, gv, rdv, wrv, syv⟩ => ⟨⟨cv, dv, av, fun r hr => ?keepStep, rdv.trans rdu,
        wrv.trans wru, syv.trans syu⟩, sv⟩)
    ⟨c0, by rw [g0 _ (by decide) (by decide), hkey, BitVec.add_zero], by rw [ax0], fun r hr => ?keep0, rd0,
      wr0, sy0⟩ hsi0) (by decide)) fun u ⟨hu, kpu⟩ => ?rest)
  case keepStep =>
    have hr' := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [gv r hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2, gu r hr]
  case keep0 =>
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact g0 r hr.1 hr.2.2.2
  case rest =>
    obtain ⟨cu, -, -, gu, rdu, wru, syu⟩ := hu
    obtain ⟨w, rw', w1, w15, gw, cw, mw, rdw, wrw, spw, syw, vw⟩ := setupKey_run u
    refine WP.seq (WP.of_runBlock ⟨w, rw', ?_⟩)
    have gws (r : Reg) (hr : r ∉ [Reg.x4, .x0, .x1, .x9]) (h15 : r ≠ .x15) (h6 : r ≠ .x6) :
        w.gpr r = s.gpr r := by
      have hr' := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      rw [gw r hr'.2.2.1 h15 h6, gu r hr]
    let st0 : XZ := ⟨fun j => (Spec.Cast5.bytesAt s.mem key n).getD j 0,
      fun j => s.mem (c + BitVec.ofNat 64 (32 + j))⟩
    obtain xz0 : HoldsXZ w.mem c st0 := by
      intro a i hi
      rw [mw]
      cases a with
      | x => rw [show off .x + i = 16 + i from rfl, cu.x i hi]; exact (bytesAt_getD _ _ _ _).symm
      | z => exact cu.z i hi
    obtain fr0 : Frame [⟨c, 64⟩, ⟨K, 128⟩] s.mem w.mem := by
      rw [mw]
      refine cu.fr.mono fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [hr]; exact List.mem_cons_self
    obtain dKS0 : Region.Disjoint ⟨K, 128⟩ ⟨c, 64⟩ := by
      have := h.dKS; rw [hK, hc] at this; exact this.sub_right (Region.sub_prefix (by decide))
    obtain ts0 : TS s.mem c K w st0 [] :=
      ⟨by rw [gws _ (by decide) (by decide) (by decide), hc],
        ⟨xz0, fun i hi => absurd hi (Nat.not_lt_zero _), fr0⟩, Nat.zero_le _,
        by rw [wrw, wru]; exact hw64, by rw [wrw, wru]; exact hwK, dKS0, cw⟩
    refine WP.seq (WP.mono (wp_countdown (cnt := .x1) (N := 2) (by decide) (by decide)
      (fun hh v => TS s.mem c K v (halves st0 hh).1 (halves st0 hh).2 ∧
        v.gpr .x2 = K + BitVec.ofNat 64 (64 * hh) ∧ KeptH w v)
      (fun hh hh2 v ⟨kv, dv, pv⟩ _ => WP.mono (halfTbl_ok kv dv (halves_length st0 hh) hh2)
        fun x ⟨kx, dx, sx, px⟩ => ⟨⟨kx, dx, pv.trans px⟩, sx⟩)
      ⟨ts0, by rw [gws _ (by decide) (by decide) (by decide), hK, Nat.mul_zero, BitVec.add_zero], KeptH.refl w⟩
      w1) fun v ⟨kv, _, pv⟩ => ?_)
    let z := v.write .x .x30 (v.gpr .x15 + BitVec.ofNat 64 0)
    obtain ez : exec (.addImm .x .x30 .x15 0) v = some z := Proof.Cast5.AArch64.exec_addImm_x' (by decide)
    refine WP.of_runBlock ⟨z, by rw [runBlock_cons, ez, runStep_some, runBlock_nil], ?_, ?_, ?_, ?_⟩
    · show Spec.Cast5.scheduleAt v.mem _ = _
      rw [hK, hkey, hn, scheduleAt_keys kv.mem.keys (halves_length st0 2), Proof.Cast5.expandKey_eq _ st0.z,
        halves_two]
    · intro r hr
      by_cases h30 : r = .x30
      · subst h30
        show (v.write .x .x30 _).gpr .x30 = _
        rw [gpr_write_self, BitVec.add_zero, pv.gpr _ (by decide), w15, gu _ (by decide)]
        exact BitVec.setWidth_eq _
      · obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := saved_not_half r hr h30
        show (v.write .x .x30 _).gpr r = _
        rw [gpr_write_of_ne _ _ _ h30, pv.gpr r n1, gws r n6 n3 n4]
    · show v.sp = s.sp
      rw [pv.sp, spw, kpu.sp, kp0.sp]
    · intro r hr
      obtain ⟨n1, n2, n3⟩ := savedV_not_pass r hr
      show (v.v r).extractLsb' 0 64 = _
      rw [pv.v r n1, vw r n2 n3, kpu.vcs r hr, kp0.vcs r hr]

/-! ## Verified against the shared contract

The pointers and `key_len` are public, and so is everything the code
computes from them: every address and branch. The key's bytes, `x` and `z`
are only ever loaded into lanes, looked up by `tbl` and `tbx`, XORed and
stored. -/

/-- The contract the proof of key expansion is written against. -/
def keyT : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let sched : Region := ⟨s.gpr .x2, 128⟩
    let buf : Region := ⟨s.gpr .x3, 256⟩
    s.rd = [key] ∧ s.wr = [sched, buf] ∧ key.Disjoint sched ∧ key.Disjoint buf ∧ sched.Disjoint buf ∧
      (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 128 ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat + 256 ≤ 2 ^ 64 ∧ (5 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 16)
  post s s' :=
    Spec.Cast5.scheduleAt s'.mem (s.gpr .x2) =
      Spec.Cast5.expandKey (Spec.Cast5.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
  pub := Proof.Blowfish.AArch64.PublicRegs [.x0, .x1, .x2, .x3]

theorem key_correct (s : State) (h : keyT.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ keyT.post s s' := by
  obtain ⟨hrd, hwr, dkK, dkS, dKS, fk, fK, fS, len⟩ := h
  obtain ⟨t, s', he, hp, ha⟩ := expandKey_ok s ⟨hrd, hwr, dkK, dkS, dKS, fk, fK, fS, len⟩
  exact ⟨t, s', he, ha, hp⟩

theorem expandKey_constantTime (pre : State → Prop) :
    ConstantTime isa pre (Proof.Blowfish.AArch64.PublicRegs [.x0, .x1, .x2, .x3]) expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

/-- A state satisfying key expansion's precondition: a 16-byte key. -/
def keySat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 256⟩]

theorem publicRegs_four (s₁ s₂ : State) :
    Proof.Blowfish.AArch64.PublicRegs [.x0, .x1, .x2, .x3] s₁ s₂ ↔
      s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
        s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 := by
  simp [Proof.Blowfish.AArch64.PublicRegs]

theorem expandKey_verified :
    Verified AArch64.target expandKey (Spec.Cast5.expandKeyContract AArch64.abi) := by
  refine Verified.of_correct (k := keyT) key_correct (expandKey_constantTime _) ?_
  sig_implies [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, Spec.Cast5.expandKeyPre,
    Spec.Cast5.expandKeyPost, Spec.Cast5.validKey, abi, argRegs, keyT, publicRegs_four]
    [keySat] using keySat

end VG.Proof.Cast5.AArch64.Tbl
