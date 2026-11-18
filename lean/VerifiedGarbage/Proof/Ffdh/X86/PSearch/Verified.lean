module

public import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Steps
public import VerifiedGarbage.Impl.Ffdh.X86.ParamSearch
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ToAdditive
public import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Loop
meta import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Loop
meta import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Ffdh.X86.Cand.Verified
import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Exits
public import VerifiedGarbage.Proof.Ffdh.Contract
meta import VerifiedGarbage.Proof.Ffdh.X86.Cand.Verified
meta import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Exits
meta import VerifiedGarbage.Proof.Ffdh.Contract
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.X86.Target
meta import VerifiedGarbage.Proof.Mont.X86.Instr
meta import VerifiedGarbage.Proof.Mont.X86.Words
meta import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Steps
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Ffdh.SievedBounds
public import VerifiedGarbage.Proof.EntropyRequest
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Ffdh.SievedBounds
meta import VerifiedGarbage.Proof.EntropyRequest
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Rc2.PairMem
meta import VerifiedGarbage.Proof.Framework.X86.Spill
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Ffdh.X86.PSearch.CT`, which only this module used -/

section

/-! ### `Ffdh.X86.PSearch.Correct`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86.PSearch.Finish`, which this module and modules that import it used -/

section

/-! # The parameter search's finish (x86)

From a finished search, `finish` writes the octets consumed to `used` (64
bits), returns the status and restores the caller's `esi` (`finish_ok`):
the state's four public words, `used`, the output, the callee-saved
registers and the return address are as the contract asks (`Fin`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.PSearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.ParamSearch
open VG.Proof.Ffdh.X86.KeySearch (Ctl Aligned upd Scratch saved_ne bytes_frame)
open VG.Proof.Dsa.X86 (argumentPointer)

/-- What the contract asks after a search with the result `r`. -/
structure Fin (o : State) (r : ParameterSearchResult) (t : State) : Prop where
  eax : t.gpr .eax = BitVec.ofNat 32 r.status
  saved : ∀ q ∈ calleeSaved, t.gpr q = o.gpr q
  ret : t.mem.readW ((o.gpr .esp).setWidth 64) 32 = o.mem.readW ((o.gpr .esp).setWidth 64) 32
  output : Output (ofState o) r t.mem
  policy : Spec.Rsa.wordsAt t.mem (argumentPointer o 9) 4 =
    [BitVec.ofNat 64 r.remaining, BitVec.ofNat 64 (arg o 1).toNat,
      BitVec.ofNat 64 (parameterEntropy (arg o 3).toNat), BitVec.ofNat 64 (Proof.Ffdh.requested (arg o 3).toNat r)]
  used : Spec.Rsa.wordsAt t.mem (argumentPointer o 2) 1 = [BitVec.ofNat 64 r.used]

theorem Done.st {o s : State} {r : ParameterSearchResult} (h : Done (ofState o) o r s) :
    St o doneDs (doneF (ofState o) (o.gpr .esi) r) s :=
  ⟨h.input.1, h.rd, h.wr, h.syms, h.esp, h.esi, h.saved, h.frame, h.words⟩

/-- A 64-bit word of two 32-bit halves. -/
theorem word64 {m : Mem} {a : Addr} {k : Nat} (hk : k < 2 ^ 64) (lo : m.readW a 32 = BitVec.ofNat 32 k)
    (hi : m.readW (a + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 (k / 2 ^ 32)) : m.readW a 64 = BitVec.ofNat 64 k := by
  rw [Proof.Rc2.Word32.read64_pair, lo, hi]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show k / 2 ^ 32 < 2 ^ 32 by omega_using [hk]), Nat.mod_eq_of_lt hk,
    ← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by decide)), Nat.shiftLeft_eq]
  omega_using []

/-- The return address, apart from every region the run writes. -/
theorem ret_apart {o : State} (A : PSearchABI o) : ∀ r ∈ frameR o, (retR o).Disjoint r := by
  have h1 : 212 ≤ (o.gpr .esp).toNat := A.stackLow
  have hl : (retR o).Disjoint (lowR o) := by
    show Region.Disjoint ⟨(o.gpr .esp).setWidth 64, 4⟩ ⟨(o.gpr .esp).setWidth 64 - BitVec.ofNat 64 212, 212⟩
    exact Offset.base_disjoint_below _ (by omega_using [])
  exact apart A A.retO A.retU A.retB A.retS A.retA hl

/-- A 64-bit word below `2³²`. -/
theorem word64z {m : Mem} {a : Addr} {k : Nat} (hk : k < 2 ^ 32) (lo : m.readW a 32 = BitVec.ofNat 32 k)
    (hi : m.readW (a + BitVec.ofNat 64 4) 32 = 0) : m.readW a 64 = BitVec.ofNat 64 k :=
  word64 (by omega_using [hk]) lo (by rw [hi, Nat.div_eq_of_lt hk]; rfl)

/-- A word of the state at offset `d`, as `wordsAt` addresses it. -/
theorem st_addr {o : State} (A : PSearchABI o) {d : Nat} (hd : d + 4 ≤ 128) :
    addr (arg o 9) d = argumentPointer o 9 + BitVec.ofNat 64 d := Spill.addr_eq_of A.sBound hd

theorem finish_ok {o s : State} {r : ParameterSearchResult} (h : Done (ofState o) o r s) :
    WP isa (.block finish) s (Fin o r) := by
  have S := h.st
  have A := h.input.1
  have hA : Aligned doneDs := by decide
  have hS := A.sBound
  have hub := A.uBound
  obtain ⟨hk, hc, hu⟩ := h.small
  have hat := attempts_le A
  have hcap := cap_lt A
  have hR : (ofState o).randLen < 2 ^ 32 := (arg o 6).isLt
  unfold finish
  refine S.ld (Or.inr (Or.inl rfl)) (d := upOff) (by decide) (by decide) fun t₁ S₁ g₁ _ _ m₁ => ?_
  refine S₁.ld (Or.inl rfl) (d := usedOff) (by decide) (by decide) fun t₂ S₂ g₂ o₂ _ m₂ => ?_
  have ec : t₂.gpr .ecx = arg o 2 := by rw [o₂ .ecx (by decide), g₁]; rfl
  have uIn : ∀ t : State, t.wr = o.wr → ∀ d, d + 4 ≤ 8 →
      InRegions t.wr (argumentPointer o 2 + BitVec.ofNat 64 d) 4 := fun t ht d hd =>
    ⟨uR o, by rw [ht]; exact uR_mem A, Offset.contains_base _ hd (by omega_using [hd])⟩
  refine wp_storeS (show t₂.ea (at_ .ecx 0) = argumentPointer o 2 + BitVec.ofNat 64 0 by
      show (t₂.gpr .ecx + BitVec.ofNat 32 0).setWidth 64 = _; rw [ec]; exact addr_eq (by omega_using []))
    (uIn t₂ S₂.wr 0 (by decide)) fun t₃ M₃ => ?_
  refine wp_movi fun t₄ U₄ => ?_
  refine wp_storeS (show t₄.ea (at_ .ecx 4) = argumentPointer o 2 + BitVec.ofNat 64 4 by
      show (t₄.gpr .ecx + BitVec.ofNat 32 4).setWidth 64 = _
      rw [U₄.other _ (by decide), M₃.gpr, ec]; exact addr_eq (by omega_using [hub]))
    (by rw [U₄.wr, M₃.wr]; exact uIn t₂ S₂.wr 4 (by decide)) fun t₅ M₅ => ?_
  -- The stores at `used`.
  have mem₅ : t₅.mem = (t₂.mem.writeW (argumentPointer o 2 + BitVec.ofNat 64 0) (BitVec.ofNat 32 r.used)).writeW
      (argumentPointer o 2 + BitVec.ofNat 64 4) (0 : BitVec 32) := by
    rw [M₅.mem, U₄.gpr, U₄.mem, M₃.mem, g₂]; rfl
  have fu : Frame [uR o] t₂.mem t₅.mem := by
    rw [mem₅]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by omega_using []))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by omega_using []))
  have S₅ : St o doneDs (doneF (ofState o) (o.gpr .esi) r) t₅ := by
    refine ⟨A, M₅.rd.trans (U₄.rd.trans (M₃.rd.trans S₂.rd)), M₅.wr.trans (U₄.wr.trans (M₃.wr.trans S₂.wr)),
      M₅.syms.trans (U₄.syms.trans (M₃.syms.trans S₂.syms)), ?_, ?_, fun q hq hne => ?_,
      S₂.frame.trans (fu.mono fun r hr => ?_), S₂.words.frame hS hA fu fun r hr => ?_⟩
    · rw [M₅.gpr, U₄.other _ (by decide), M₃.gpr, S₂.esp]
    · rw [M₅.gpr, U₄.other _ (by decide), M₃.gpr, S₂.esi]
    · rw [M₅.gpr, U₄.other _ (saved_ne (Or.inl rfl) hq), M₃.gpr, S₂.saved q hq hne]
    · simp only [List.mem_singleton] at hr; subst hr; exact List.mem_append_left _ (uR_mem A)
    · simp only [List.mem_singleton] at hr; subst hr; exact A.us.symm
  refine S₅.ld (Or.inl rfl) (d := statusOff) (by decide) (by decide) fun t₆ S₆ g₆ o₆ _ m₆ => ?_
  refine wp_ldm S₆.esi (S₆.rIn (d := savedOff) (by decide)) fun t₇ U₇ => WP.block_nil ?_
  have m₇ : t₇.mem = t₅.mem := by rw [U₇.mem, m₆]
  have m₂ : t₂.mem = s.mem := by rw [m₂, m₁]
  refine ⟨?_, fun q hq => ?_, ?_, ?_, ?_, ?_⟩
  · rw [U₇.other _ (by decide), g₆]; simp [doneF, statusOff]
  · by_cases hq' : q = .esi
    · subst hq'; rw [U₇.gpr, S₆.words.get (d := savedOff) (by decide)]; simp [doneF, savedOff]
    · rw [U₇.other _ hq', S₆.saved q hq hq']
  · rw [m₇]; exact S₅.frame.readW (Region.contains_self _ _) (ret_apart A) (by decide)
  · have out := h.output
    have kx : Spec.Rsa.bytesAt t₇.mem (argumentPointer o 0) (arg o 1).toNat =
        Spec.Rsa.bytesAt s.mem (argumentPointer o 0) (arg o 1).toNat := by
      rw [m₇, ← m₂]
      exact bytes_frame fu (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact A.ou) (by have := A.oBound; omega_using [])
    unfold Output at out ⊢
    split at out <;> exact kx.trans out
  · have W : ∀ d ∈ doneDs, t₇.mem.readW (addr (arg o 9) d) 32 = doneF (ofState o) (o.gpr .esi) r d := by
      intro d hd; rw [m₇]; exact S₅.words.get hd
    have hl : (arg o 1).toNat < 2 ^ 32 := (arg o 1).isLt
    have hcap' : parameterEntropy (arg o 3).toNat < 2 ^ 32 := by
      have : (ofState o).cap = parameterEntropy (arg o 3).toNat := rfl; omega
    have hc' : (Proof.Ffdh.requested (arg o 3).toNat r) < 2 ^ 32 := by
      have : (ofState o).bits = (arg o 3).toNat := rfl
      rw [← this]; omega_using [hc, hcap]
    unfold Spec.Rsa.wordsAt
    rw [show List.range 4 = [0, 1, 2, 3] from rfl]
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    refine ⟨word64 (by omega_using [hk, hat]) ?_ ?_, word64z hl ?_ ?_, word64z hcap' ?_ ?_, word64z hc' ?_ ?_⟩
    · rw [← st_addr A (d := 0) (by decide), W 0 (by decide)]; simp [doneF]
    · rw [Offset.add_add, ← st_addr A (d := 4) (by decide), W 4 (by decide)]; simp [doneF]
    · rw [← st_addr A (d := 8) (by decide), W 8 (by decide)]; simp [doneF, ofState]
    · rw [Offset.add_add, ← st_addr A (d := 12) (by decide), W 12 (by decide)]; simp [doneF]
    · rw [← st_addr A (d := 16) (by decide), W 16 (by decide)]; simp [doneF, ofState]
    · rw [Offset.add_add, ← st_addr A (d := 20) (by decide), W 20 (by decide)]; simp [doneF]
    · rw [← st_addr A (d := 24) (by decide), W 24 (by decide)]; simp [doneF, ofState]
    · rw [Offset.add_add, ← st_addr A (d := 28) (by decide), W 28 (by decide)]; simp [doneF]
  · unfold Spec.Rsa.wordsAt
    rw [show List.range 1 = [0] from rfl]
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    rw [m₇, mem₅]
    refine word64z (by omega_using [hu, hR]) ?_ ?_
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
        show (8 * 0 : Nat) = 0 from rfl, Mem.readW_writeW_self32]
    · rw [show (8 * 0 : Nat) = 0 from rfl, Offset.add_add, Mem.readW_writeW_self32]

end VG.Proof.Ffdh.X86.PSearch

end

end

/-! # The parameter search against its contract (x86)

The entry, the loop from its first state and the finish run the search from
the tape's start (`operation_ok`), which is `sievedParameterSearch`; so the
code meets `vg_ffdh_generate_parameters`'s contract (`correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.PSearch

open VG VG.X86 VG.X86.Wp VG.Spec.Ffdh
open VG.Proof.Dsa.X86 (argumentPointer)

/-- The search the contract specifies. -/
abbrev searchOf (o : State) : ParameterSearchResult :=
  sievedParameterSearch (ofState o).bits (ofState o).gen (ofState o).attempts (ofState o).rand

theorem tail_zero (o : State) : (ofState o).tail 0 (ofState o).attempts = searchOf o := by
  simp only [PPub.tail, ptail, List.drop_zero, Generation.consume_zero]

theorem operation_ok {o : State} (A : PSearchABI o) :
    WP isa Impl.Ffdh.X86.ParamSearch.code o (Fin o (searchOf o)) := by
  unfold Impl.Ffdh.X86.ParamSearch.code
  refine WP.seq (WP.mono (entry_ok A) fun s hs => ?_)
  refine WP.seq (WP.mono (loop_ok hs) fun t ht => ?_)
  rw [tail_zero] at ht
  exact finish_ok ht

theorem correct (s : State) (h : contract.pre s) :
    ∃ trace t, Exec isa Impl.Ffdh.X86.ParamSearch.code s trace t ∧ abiPreserved s t ∧ contract.post s t := by
  obtain ⟨trace, t, E, F⟩ := operation_ok (pSearchABI_of h)
  refine ⟨trace, t, E, ⟨F.saved, F.ret⟩, ?_⟩
  have out := F.output
  unfold Output at out
  sig_post [contract, Spec.Ffdh.sievedParameterSearchContract, Spec.Ffdh.parameterSearchSig, abi, argSlots, argVal,
    argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts]
  refine ⟨?_, ?_, F.used, _, F.policy, SievedGeneration.search_requests _ _ _ _⟩
  · rw [BitVec.setWidth_append_eq_right, F.eax, toNat_ofNat_lt (by have := status_le (searchOf s); omega_using [this])]
    rfl
  · show Spec.Rsa.bytesAt t.mem ((arg s 0).setWidth 64) (arg s 1).toNat = (match searchOf s with
      | .accepted p _ => Spec.Rsa.i2osp p (arg s 1).toNat
      | _ => List.replicate (arg s 1).toNat 0)
    revert out
    cases searchOf s <;> exact id

end VG.Proof.Ffdh.X86.PSearch

end

end

/-! ### `Ffdh.X86.PSearch.CTAttempt`, which only this module used -/

section

/-! ### `Ffdh.X86.PSearch.CTExits`, which this module and modules that import it used -/

section

/-! # Two runs of the parameter search's exits (x86)

Two runs relate by a public descriptor (`Any`), which fixes `esi` and `esp`;
the taint analysis checks a piece of code from them. `zeroOut` addresses the
output through words loaded from the state, which the descriptor fixes
(`zeroOut_ct`). From loop states at the same point, `exhausted` and
`request` leak nothing more (`exhausted_ct`, `request_ct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.PSearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.ParamSearch
open VG.Proof.Ffdh.X86.KeySearch (Ctl Aligned upd Scratch)
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite)

/-- A run's state with the public descriptor `p`. -/
def Any (p : PPub) (s : State) : Prop := ∃ o ds f, ofState o = p ∧ St o ds f s

theorem any_pins {α : Type} {Φ : α → State → Prop} (g : α → PPub) (h : ∀ a s, Φ a s → Any (g a) s) :
    Pins Φ [.esi, .esp] := by
  intro a s₁ s₂ h₁ h₂ r hr
  obtain ⟨o₁, _, _, e₁, S₁⟩ := h a s₁ h₁
  obtain ⟨o₂, _, _, e₂, S₂⟩ := h a s₂ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [S₁.esi, S₂.esi]; show (ofState o₁).S = (ofState o₂).S; rw [e₁, e₂]
  · rw [S₁.esp, S₂.esp]; show (ofState o₁).sp = (ofState o₂).sp; rw [e₁, e₂]

/-- A run's state from which the output is zeroed. -/
def ZAt (p : PPub) (s : State) : Prop :=
  ∃ o ds f, ofState o = p ∧ St o ds f s ∧ Aligned ds ∧ outOff ∈ ds ∧ widthOff ∈ ds ∧ f outOff = arg o 0 ∧
    f widthOff = BitVec.ofNat 32 (arg o 1).toNat

theorem ZAt.any {p : PPub} {s : State} (h : ZAt p s) : Any p s :=
  let ⟨o, ds, f, e, S, _⟩ := h; ⟨o, ds, f, e, S⟩

theorem zeroHead_ok (p : PPub) (s : State) (h : ZAt p s) :
    WP isa (.block [.mov .edx (.mem (st outOff)), .mov .ecx (.mem (st widthOff)), .mov .eax (.imm 0)]) s
      fun t => Any p t ∧ t.gpr .edx = p.op ∧ t.gpr .ecx = BitVec.ofNat 32 p.len := by
  obtain ⟨o, ds, f, rfl, S, _, ho, hw, eo, ew⟩ := h
  refine S.ld (Or.inr (Or.inr rfl)) ho (by decide) fun t₁ S₁ g₁ _ _ _ => ?_
  refine S₁.ld (Or.inr (Or.inl rfl)) hw (by decide) fun t₂ S₂ g₂ o₂ _ _ => ?_
  refine wp_movi fun t₃ U₃ => WP.block_nil ⟨⟨o, ds, f, rfl, S₂.reg U₃ (Or.inl rfl)⟩, ?_, ?_⟩
  · rw [U₃.other _ (by decide), o₂ _ (by decide), g₁, eo]; rfl
  · rw [U₃.other _ (by decide), g₂, ew]; rfl

theorem zeroOut_ct : RelCT isa (Two ZAt) zeroOut fun _ _ => True := by
  unfold zeroOut
  refine RelCT.seq (two_piece (Ψ := fun p t => Any p t ∧ t.gpr .edx = p.op ∧ t.gpr .ecx = BitVec.ofNat 32 p.len)
    [.esi, .esp] (any_pins id fun _ _ h => h.any) (by taint_decide) zeroHead_ok) ?_
  refine two_taint [.edx, .ecx, .esi, .esp] (fun a s₁ s₂ h₁ h₂ r hr => ?_) (by taint_decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | hr
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2, h₂.2.2]
  · exact any_pins (Φ := fun p t => Any p t ∧ t.gpr .edx = p.op ∧ t.gpr .ecx = BitVec.ofNat 32 p.len) id
      (fun _ _ h => h.1) a _ _ h₁ h₂ r (by simpa using hr)

/-- The loop's public data: the descriptor, the octets consumed and the attempts left. -/
abbrev Lp := PPub × Nat × Nat

/-- A loop state at the point `q`. -/
def LiveAt (q : Lp) (s : State) : Prop := ∃ o, Live q.1 o q.2.1 q.2.2 s

theorem LiveAt.any {q : Lp} {s : State} (h : LiveAt q s) : Any q.1 s := by
  obtain ⟨o, L⟩ := h
  exact ⟨o, _, _, L.input.2, L.st⟩

theorem liveAt_pins : Pins LiveAt [.esi, .esp] := any_pins (fun q => q.1) fun _ _ h => h.any

theorem exhausted_ct : RelCT isa (Two LiveAt) exhausted fun _ _ => True := by
  unfold exhausted
  refine RelCT.seq (two_piece (Ψ := fun q t => ZAt q.1 t) [.esi, .esp] liveAt_pins (by taint_decide)
    fun q s ⟨o, L⟩ => ?_) (two_map (fun q => q.1) (fun _ _ h => h) zeroOut_ct)
  obtain ⟨p, used, n⟩ := q
  have S := L.st
  obtain ⟨A, e⟩ := L.input
  subst e
  refine WP.mono (S.terminal liveDs_aligned 3) fun t ⟨Sx, _⟩ => ⟨o, _, _, rfl, Sx, by decide, by decide, by decide,
    ?_, ?_⟩
  all_goals simp [upd, liveF, ofState, outOff, widthOff, statusOff, requestOff, attemptsOff]

theorem request_ct : RelCT isa (Two LiveAt) request fun _ _ => True := by
  unfold request
  refine RelCT.seq (two_piece (Ψ := fun q t => ZAt q.1 t) [.esi, .esp] liveAt_pins (by taint_decide)
    fun q s ⟨o, L⟩ => ?_) (two_map (fun q => q.1) (fun _ _ h => h) zeroOut_ct)
  obtain ⟨p, used, n⟩ := q
  have S := L.st
  obtain ⟨A, e⟩ := L.input
  subst e
  have hc := cap_lt A
  have hr := A.randLen
  have hL := len_pos A
  have ec : (ofState o).cap = parameterEntropy (arg o 3).toNat := rfl
  have el : (ofState o).len = (arg o 1).toNat := rfl
  refine WP.mono (S.requestWords liveDs_aligned (by decide) (by decide) (by decide) (a := (ofState o).randLen - used)
    (L := (ofState o).len) (c := (ofState o).cap) (by simp [liveF, leftOff]) (by simp [liveF, widthOff])
    (by simp [liveF, capOff]) (by rw [ec] at hc; have : (ofState o).randLen = (arg o 6).toNat := rfl; omega_using [hc, hr, this])
    (by omega_using [hL, el]) (by omega_using [hc])) fun t Sx => ⟨o, _, _, rfl, Sx, by decide, by decide, by decide, ?_, ?_⟩
  all_goals simp [upd, liveF, ofState, outOff, widthOff, statusOff, requestOff]

end VG.Proof.Ffdh.X86.PSearch

end

end

/-! # Two runs of an attempt (x86)

Two runs with the same public descriptor and loop point pass
`vg_ffdh_parameter_candidate_sieved` the same arguments and the same public
data (`callee_pub`), so their attempts leak the same (`attempt_ct`); after
it, `classify` branches on the candidate's status, a function of the public
tape (`classify_ct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.PSearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.ParamSearch
open VG.Proof.Ffdh.X86.KeySearch (Ctl Aligned upd Scratch)
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite argumentPointer)

/-- Two entry states with the same public descriptor have the same arguments. -/
theorem args_eq {o₁ o₂ : State} (e : ofState o₁ = ofState o₂) {i : Nat} (hi : i < 10) : arg o₁ i = arg o₂ i := by
  have ofn : ∀ {x y : BitVec 32}, x.toNat = y.toNat → x = y := BitVec.eq_of_toNat_eq
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 by omega_using [hi])
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact congrArg PPub.op e
  · exact ofn (congrArg PPub.len e)
  · exact congrArg PPub.up e
  · exact ofn (congrArg PPub.bits e)
  · exact ofn (congrArg PPub.gen e)
  · exact congrArg PPub.rp e
  · exact ofn (congrArg PPub.randLen e)
  · exact congrArg PPub.B e
  · exact ofn (congrArg PPub.slen e)
  · exact congrArg PPub.S e

theorem callArg_eq {o₁ o₂ : State} (e : ofState o₁ = ofState o₂) (used j : Nat) :
    callArg o₁ used j = callArg o₂ used j := by
  unfold callArg
  simp only [args_eq e (i := 0) (by omega_using []), args_eq e (i := 1) (by omega_using []), args_eq e (i := 3) (by omega_using []),
    args_eq e (i := 4) (by omega_using []), args_eq e (i := 5) (by omega_using []), args_eq e (i := 6) (by omega_using []),
    args_eq e (i := 7) (by omega_using []), args_eq e (i := 8) (by omega_using []), args_eq e (i := 9) (by omega_using [])]

theorem callee_pub {o₁ o₂ t₁ t₂ : State} {ds₁ ds₂ : List Nat} {f₁ f₂ : Nat → BitVec 32} {used : Nat}
    (e : ofState o₁ = ofState o₂) (h₁ : Fr o₁ ds₁ f₁ t₁) (h₂ : Fr o₂ ds₂ f₂ t₂)
    (hu : used < (arg o₁ 6).toNat) (a₁ : ArgsAt o₁ used 9 t₁.mem) (a₂ : ArgsAt o₂ used 9 t₂.mem)
    (rd wr : List Region) :
    Cand.contract.pub (t₁.callEntry.withRegions rd wr) (t₂.callEntry.withRegions rd wr) := by
  have A₁ := h₁.abi
  have A₂ := h₂.abi
  have hu₂ : used < (arg o₂ 6).toNat := by rw [← args_eq e (i := 6) (by omega_using [])]; exact hu
  have sp : o₁.gpr .esp = o₂.gpr .esp := congrArg PPub.sp e
  sig_pub [Cand.contract, Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi,
    argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts]
  have c₁ := fun j (hj : j < 9) => ce_arg A₁ h₁.esp a₁ rd wr hj
  have c₂ := fun j (hj : j < 9) => ce_arg A₂ h₂.esp a₂ rd wr hj
  simp only [c₁ 0 (by decide), c₁ 1 (by decide), c₁ 2 (by decide), c₁ 3 (by decide), c₁ 4 (by decide),
    c₁ 5 (by decide), c₁ 6 (by decide), c₁ 7 (by decide), c₁ 8 (by decide),
    c₂ 0 (by decide), c₂ 1 (by decide), c₂ 2 (by decide), c₂ 3 (by decide), c₂ 4 (by decide),
    c₂ 5 (by decide), c₂ 6 (by decide), c₂ 7 (by decide), c₂ 8 (by decide)]
  have ca := callArg_eq e used
  refine ⟨by rw [h₁.esp, h₂.esp, sp], by rw [h₁.syms, h₂.syms]; exact congrArg PPub.T e, ?_, ca 0, ca 1, ca 2,
    ca 3, ca 4, ca 5, ca 6, ca 7, ca 8⟩
  have l₁ : (BitVec.ofNat 32 ((arg o₁ 6).toNat - used)).toNat = (arg o₁ 6).toNat - used := by
    have := (arg o₁ 6).isLt; rw [BitVec.toNat_ofNat]; omega_using []
  have l₂ : (BitVec.ofNat 32 ((arg o₂ 6).toNat - used)).toNat = (arg o₂ 6).toNat - used := by
    have := (arg o₂ 6).isLt; rw [BitVec.toNat_ofNat]; omega_using []
  simp only [callArg, Nat.reduceEqDiff, ↓reduceIte, l₁, l₂]
  rw [ret_eq A₁ h₁.esp, ret_eq A₂ h₂.esp, entry_bytes h₁ hu, entry_bytes h₂ hu₂, e]

/-- Relating two runs for each public datum. -/
theorem two_of {α : Type} {Φ : α → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : ∀ a, RelCT isa (fun s₁ s₂ => Φ a s₁ ∧ Φ a s₂) c Q) : RelCT isa (Two Φ) c Q :=
  fun _ _ _ _ _ _ ⟨a, h₁, h₂⟩ e₁ e₂ => h a _ _ _ _ _ _ ⟨h₁, h₂⟩ e₁ e₂

/-- In the attempt's frame. -/
def FrAt (q : Lp) (f : State) : Prop := ∃ s, LiveAt q s ∧ q.2.1 < q.1.randLen ∧ f = allocFrame argsBytes s

/-- With the arguments in the frame. -/
def CallAt (q : Lp) (t : State) : Prop :=
  ∃ o, ofState o = q.1 ∧ Fr o liveDs (liveF q.1 (o.gpr .esi) q.2.1 q.2.2) t ∧ ArgsAt o q.2.1 9 t.mem ∧
    q.2.1 < q.1.randLen

theorem frAt_pins : Pins FrAt [.esi, .esp] := by
  intro k f₁ f₂ ⟨s₁, ⟨o₁, L₁⟩, _, e₁⟩ ⟨s₂, ⟨o₂, L₂⟩, _, e₂⟩ r hr
  subst e₁ e₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [allocFrame_gpr _ _ (by decide), allocFrame_gpr _ _ (by decide), L₁.esi, L₂.esi]
  · rw [allocFrame_esp, allocFrame_esp, L₁.esp, L₂.esp]

/-- What the callee reads and writes, from the public descriptor. -/
abbrev callRdK (p : PPub) (used : Nat) : List Region :=
  [⟨(p.rp + BitVec.ofNat 32 used).setWidth 64, p.randLen - used⟩,
    ⟨p.T.setWidth 64, 8192⟩]
abbrev callWrK (p : PPub) : List Region :=
  [⟨p.op.setWidth 64, p.len⟩, ⟨(p.S + BitVec.ofNat 32 candOff).setWidth 64, 8⟩, ⟨p.B.setWidth 64, p.slen * 8⟩,
    ⟨p.sp.setWidth 64 - 212#64 + BitVec.ofNat 64 176, 36⟩]

theorem call_ct (q : Lp) :
    RelCT isa (fun t₁ t₂ => CallAt q t₁ ∧ CallAt q t₂)
      (.call "vg_ffdh_parameter_candidate_sieved" Impl.Ffdh.X86.Candidate.code) fun _ _ => True := by
  refine RelCT.call Cand.verified.1 Cand.verified.2.1 (callRdK q.1 q.2.1) (callWrK q.1)
    fun t₁ t₂ ⟨⟨o₁, e₁, F₁, a₁, hu₁⟩, ⟨o₂, e₂, F₂, a₂, hu₂⟩⟩ => ?_
  obtain ⟨p, used, n⟩ := q
  dsimp only at e₁ e₂ F₁ F₂ a₁ a₂ hu₁ hu₂ ⊢
  subst e₁
  have r₁ : callRdK (ofState o₁) used = callRd o₁ used := by rw [callRd, tableRs_eq]; rfl
  have w₁ : callWrK (ofState o₁) = callWr o₁ := rfl
  have r₂ : callRdK (ofState o₂) used = callRd o₂ used := by rw [callRd, tableRs_eq]; rfl
  have w₂ : callWrK (ofState o₂) = callWr o₂ := rfl
  have c₁ := call_covers (t := t₁) F₁.abi hu₁ F₁.rd F₁.wr
  have hu₂' : used < (arg o₂ 6).toNat := by have := hu₂; rw [← e₂] at this; exact this
  have c₂ := call_covers (t := t₂) F₂.abi hu₂' F₂.rd F₂.wr
  have eqR : callRd o₂ used = callRd o₁ used := by rw [← r₁, ← r₂, e₂]
  have eqW : callWr o₂ = callWr o₁ := by rw [← w₁, ← w₂, e₂]
  rw [r₁, w₁]
  rw [eqR, eqW] at c₂
  refine ⟨call_pre F₁.abi hu₁ F₁.esp a₁ F₁.syms F₁.frame, ?_, callee_pub e₂.symm F₁ F₂ hu₁ a₁ a₂ _ _,
    c₁.1, c₁.2, c₂.1, c₂.2, ?_⟩
  · rw [← eqR, ← eqW]
    exact call_pre F₂.abi hu₂' F₂.esp a₂ F₂.syms F₂.frame
  · rw [F₁.esp, F₂.esp, show o₁.gpr .esp = o₂.gpr .esp from (congrArg PPub.sp e₂).symm]

theorem attempt_ct : RelCT isa (Two fun (q : Lp) s => LiveAt q s ∧ q.2.1 < q.1.randLen) attempt fun _ _ => True := by
  unfold attempt
  refine RelCT.frameAlloc ((RelCT.seq (two_piece (Ψ := CallAt) [.esi, .esp] frAt_pins (by taint_decide)
    fun q f ⟨s, ⟨o, L⟩, hu, e⟩ => ?_) (two_of call_ct)).mono
      (fun a b ⟨s₁, s₂, ⟨q, h₁, h₂⟩, e₁, e₂⟩ => ⟨q, ⟨s₁, h₁.1, h₁.2, e₁⟩, ⟨s₂, h₂.1, h₂.2, e₂⟩⟩) fun _ _ h => h)
  subst e
  have S := L.st
  obtain ⟨A, e⟩ := L.input
  obtain ⟨p, used, n⟩ := q
  dsimp only at e S hu ⊢
  subst e
  exact WP.mono (arguments_ok S.alloc) fun t ⟨F, a⟩ => ⟨o, rfl, F, a, hu⟩

/-! ## After the attempt -/

/-- The status of the candidate at the loop point `q`. -/
abbrev Lp.status (q : Lp) : Nat := candidateStatus (candAt q.1.bits q.1.gen q.1.rand q.2.1)

/-- The loop point after the candidate's octets. -/
abbrev Lp.adv (q : Lp) : Lp := (q.1, q.2.1 + q.1.cu q.2.1, q.2.2)

/-- After an attempt from the loop point `q`. -/
def ClsAt (q : Lp) (u : State) : Prop :=
  ∃ o s₀, ofState o = q.1 ∧ Live q.1 o q.2.1 q.2.2 s₀ ∧ St o liveDs (liveF q.1 (o.gpr .esi) q.2.1 q.2.2) u ∧
    u.gpr .eax = BitVec.ofNat 32 q.status ∧
    u.mem.readW (addr (arg o 9) candOff) 32 = BitVec.ofNat 32 (q.1.cu q.2.1)

/-- The status in `edx` compared with `j`, the candidate's octets consumed. -/
def CmpAt (j : Nat) (q : Lp) (t : State) : Prop :=
  LiveAt q.adv t ∧ t.gpr .edx = BitVec.ofNat 32 q.status ∧ isa.eval .e t = some (decide (q.status = j))

theorem cmp_ok {q : Lp} {t : State} {i : Nat} (h : CmpAt i q t) (j : Nat) (hj : j ≤ 2) :
    WP isa (.block [.alu .cmp .edx (.imm (BitVec.ofNat 32 j))]) t (CmpAt j q) := by
  obtain ⟨⟨o, L⟩, he, _⟩ := h
  refine wp_cmpi fun t' F _ z => WP.block_nil ⟨⟨o, L.fupd F⟩, by rw [F.gpr]; exact he, ?_⟩
  exact cmp_status (candidateStatus_le _) hj he z

/-- `mov eax, [esi + 56]; mov ecx, [esi + 16]; cmp eax, ecx`: the borrow when the tape holds less than the
entropy cap. -/
theorem capCmp_ok {p : PPub} {o s : State} {used n : Nat} (h : Live p o used n s) :
    WP isa (.block [.mov .eax (.mem (st leftOff)), .mov .ecx (.mem (st capOff)), .alu .cmp .eax (.reg .ecx)]) s
      fun t => Live p o used n t ∧ isa.eval .b t = some (decide (p.randLen - used < p.cap)) := by
  have S := h.st
  have hnl := h.n_le
  have hul := h.used_le
  obtain ⟨A, rfl⟩ := h.input
  have hR : (ofState o).randLen < 2 ^ 32 := (arg o 6).isLt
  have hc := cap_lt A
  refine S.ld (Or.inl rfl) (d := leftOff) (by decide) (by decide) fun t₁ S₁ g₁ _ _ _ => ?_
  refine S₁.ld (Or.inr (Or.inl rfl)) (d := capOff) (by decide) (by decide) fun t₂ S₂ g₂ o₂ _ _ => ?_
  refine wp_cmp fun t₃ F₃ c₃ _ => WP.block_nil ⟨(S₂.fupd F₃).live hul hnl, ?_⟩
  show t₃.cf = _
  rw [c₃, o₂ .eax (by decide), g₁, g₂]
  simp only [liveF, leftOff, capOff, ↓reduceIte, Nat.reduceEqDiff]
  rw [toNat_ofNat_lt (by omega_using [hR]), toNat_ofNat_lt (by omega_using [hc])]

theorem shortage_ct : RelCT isa (Two LiveAt) shortage fun _ _ => True := by
  unfold shortage
  refine RelCT.seq (two_piece (Ψ := fun q t => LiveAt q t ∧
      isa.eval .b t = some (decide (q.1.randLen - q.2.1 < q.1.cap)))
    [.esi, .esp] liveAt_pins (by taint_decide) fun q s ⟨o, L⟩ =>
      WP.mono (capCmp_ok L) fun t ⟨L', e⟩ => ⟨⟨o, L'⟩, e⟩) ?_
  exact two_ite (fun q _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) (two_map id (fun _ _ h => h.1.1) request_ct)
    (two_map id (fun _ _ h => h.1.1) exhausted_ct)

theorem classify_ct : RelCT isa (Two ClsAt) classify fun _ _ => True := by
  unfold classify
  refine RelCT.seq (two_piece (Ψ := CmpAt 1) [.esi, .esp]
    (any_pins (fun q => q.1) fun q s ⟨o, _, e, _, S, _⟩ => ⟨o, _, _, e, S⟩) (by taint_decide)
    fun q u ⟨o, s₀, e, L₀, S, he, hcu⟩ => ?_) ?_
  · obtain ⟨p, used, n⟩ := q
    dsimp only at e L₀ S he hcu ⊢
    subst e
    have hlen := rand_length (o := o)
    have hul := L₀.used_le
    have hcl : used + (ofState o).cu used ≤ (ofState o).randLen := by
      have h2 := candUsed_le (ofState o).bits (ofState o).gen (ofState o).rand used
      rw [hlen] at h2
      show used + candUsed _ _ _ _ ≤ _
      have : (ofState o).randLen = (arg o 6).toNat := rfl
      omega_using [hul, h2, this]
    exact advance_ok (S.withWord hcu) hcl fun t S' hed _ => wp_cmpi fun t' F _ z => WP.block_nil
      ⟨⟨o, (S'.fupd F).live hcl L₀.n_le⟩, by rw [F.gpr, hed, he], cmp_status (candidateStatus_le _) (by decide)
        (hed.trans he) z⟩
  refine two_ite (fun q _ _ h₁ h₂ => h₁.2.2.trans h₂.2.2.symm)
    (two_taint [.esi, .esp] (any_pins (fun q => q.1) fun _ _ h => h.1.1.any) (by taint_decide)) ?_
  refine RelCT.seq (two_piece (Ψ := CmpAt 2) [.esi, .esp]
    (any_pins (fun q => q.1) fun _ _ h => h.1.1.any) (by taint_decide)
    fun q t h => cmp_ok h.1 2 (by decide)) ?_
  refine two_ite (fun q _ _ h₁ h₂ => h₁.2.2.trans h₂.2.2.symm)
    (two_taint [.esi, .esp] (any_pins (fun q => q.1) fun _ _ h => h.1.1.any) (by taint_decide)) ?_
  exact two_map Lp.adv (fun _ _ h => h.1.1) shortage_ct

end VG.Proof.Ffdh.X86.PSearch

end

end

/-! # The parameter search in constant time (x86)

The tape, the arguments, the attempts and the table's address are public,
so two runs whose public data agree start at the same loop point
(`pub_point`), and the search from there, all its branches included, is a
function of that point. The entry is checked by the taint analysis from
`esp`, then from `esp` and the state's pointer (`entry_ct`); an iteration
branches alike in both runs and leaves them at the same next point
(`ct_step`), so the loop leaks the points alone (`loop_ct`); `finish` stores
through `used`, which the descriptor fixes (`finish_ct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.PSearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.ParamSearch
open VG.Proof.Ffdh.X86.KeySearch (Ctl Aligned upd Scratch)
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite argumentPointer)
open VG.Impl.Bignum.X86.PublicRt (argAt)

theorem Done.any {p : PPub} {o s : State} {r : ParameterSearchResult} (h : Done p o r s) : Any p s := by
  obtain ⟨A, rfl⟩ := h.input
  exact ⟨o, _, _, rfl, h.st⟩

theorem Rej.any {p : PPub} {o s : State} {used n : Nat} (h : Rej p o used n s) : Any p s :=
  LiveAt.any (q := (p, used, n)) ⟨o, h.1⟩

theorem branch_ct : RelCT isa (Two LiveAt) branch fun _ _ => True := by
  unfold branch
  refine RelCT.seq (two_piece (Ψ := fun q t => LiveAt q t ∧ isa.eval .e t = some (decide (q.2.2 = 0)))
    [.esi, .esp] liveAt_pins (by taint_decide)
    fun q s ⟨o, L⟩ => WP.mono (attempts_ok L) fun t ⟨L', e⟩ => ⟨⟨o, L'⟩, e⟩) ?_
  refine two_ite (fun q _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) (two_map id (fun _ _ h => h.1.1) exhausted_ct) ?_
  unfold attemptOrRequest
  refine RelCT.seq (two_piece (Ψ := fun q t => LiveAt q t ∧
      isa.eval .b t = some (decide (q.1.randLen - q.2.1 < q.1.len)))
    [.esi, .esp] (any_pins (fun q => q.1) fun _ _ h => h.1.1.any) (by taint_decide)
    fun q s ⟨⟨⟨o, L⟩, _⟩, _⟩ => WP.mono (room_ok L) fun t ⟨L', e⟩ => ⟨⟨o, L'⟩, e⟩) ?_
  refine two_ite (fun q _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) (two_map id (fun _ _ h => h.1.1) request_ct) ?_
  -- The attempt, from a tape that holds a candidate's octets.
  have hatt : ∀ (q : Lp) s, (LiveAt q s ∧ isa.eval .b s = some (decide (q.1.randLen - q.2.1 < q.1.len))) ∧
      isa.eval .b s = some false → LiveAt q s ∧ q.2.1 < q.1.randLen := by
    intro q s ⟨⟨⟨o, L⟩, e⟩, hf⟩
    rw [e] at hf
    simp only [Option.some.injEq, decide_eq_false_iff_not, Nat.not_lt] at hf
    have A := L.input.1
    have hp := L.input.2
    have hl : 64 ≤ q.1.len := by rw [← hp]; exact (len_pos A).1
    exact ⟨⟨o, L⟩, by omega_using [hf, hl]⟩
  refine RelCT.seq (two_post (Ψ := ClsAt) (two_map id hatt attempt_ct) fun q s h => ?_) classify_ct
  obtain ⟨⟨o, L⟩, hu⟩ := hatt q s h
  obtain ⟨p, used, n⟩ := q
  have hp := L.input.2
  dsimp only at hp L hu
  subst hp
  exact WP.mono (attempt_ok L hu) fun u ⟨Su, eu, _, cu⟩ => ⟨o, s, rfl, L, Su, eu, cu⟩

theorem iteration_ct : RelCT isa (Two LiveAt) iteration fun _ _ => True := by
  unfold iteration
  refine RelCT.seq (two_post (Ψ := fun q t => Any q.1 t) branch_ct fun q s ⟨o, L⟩ => WP.mono (branch_ok L)
    fun v hv => ?_) (two_taint [.esi, .esp] (any_pins (fun q => q.1) fun _ _ h => h) (by taint_decide))
  rcases hv with ⟨D, _⟩ | ⟨_, R⟩
  · exact D.any
  · exact R.any

/-- The loop point after a rejection. -/
abbrev Lp.next (q : Lp) : Lp := (q.1, q.2.1 + q.1.cu q.2.1, q.2.2 - 1)

def CTStep (q : Lp) (s : State) : Prop :=
  (q.1.cont q.2.1 q.2.2 ∧ isa.eval .e s = some true ∧ LiveAt q.next s) ∨
    (¬ q.1.cont q.2.1 q.2.2 ∧ isa.eval .e s = some false)

theorem ct_step (q : Lp) (s : State) (h : LiveAt q s) : WP isa iteration s (CTStep q) := by
  obtain ⟨p, used, n⟩ := q
  obtain ⟨o, L⟩ := h
  unfold iteration
  refine WP.seq (WP.mono (branch_ok L) fun v hv => ?_)
  rcases hv with ⟨D, stop⟩ | ⟨co, R⟩
  · exact WP.mono (guard_done D) fun t ⟨he, _⟩ => Or.inr ⟨stop, he⟩
  · exact WP.mono (guard_rej R) fun t ⟨he, Lt⟩ => Or.inl ⟨co, he, o, Lt⟩

private def LoopPair (n : Nat) (s t : State) : Prop := ∃ q : Lp, n = q.2.2 ∧ LiveAt q s ∧ LiveAt q t

private theorem iteration_pair (n : Nat) :
    RelCT isa (LoopPair n) iteration fun s t =>
      isa.eval .e s = isa.eval .e t ∧ (isa.eval .e s = some false → True) ∧
      (isa.eval .e s = some true → ∃ m < n, LoopPair m s t) := by
  have hc := two_post (Φ := fun (q : Lp) s => n = q.2.2 ∧ LiveAt q s)
    (Ψ := fun q t => n = q.2.2 ∧ CTStep q t) (iteration_ct.mono
    (fun _ _ ⟨q, h₁, h₂⟩ => ⟨q, h₁.2, h₂.2⟩) fun _ _ h => h) fun q s h =>
      WP.mono (ct_step q s h.2) fun _ ht => ⟨h.1, ht⟩
  refine hc.mono (fun _ _ ⟨q, hn, h₁, h₂⟩ => ⟨q, ⟨hn, h₁⟩, hn, h₂⟩) ?_
  rintro s t ⟨q, ⟨hn, h₁⟩, _, h₂⟩
  rcases h₁ with ⟨co, e₁, L₁⟩ | ⟨nc, e₁⟩
  · rcases h₂ with ⟨_, e₂, L₂⟩ | ⟨nc, _⟩
    · refine ⟨e₁.trans e₂.symm, fun _ => trivial, fun _ => ⟨q.next.2.2, ?_, q.next, rfl, L₁, L₂⟩⟩
      have := co.1
      show q.2.2 - 1 < n
      omega_using [hn, this]
    · exact absurd co nc
  · rcases h₂ with ⟨co, _, _⟩ | ⟨_, e₂⟩
    · exact absurd co nc
    · refine ⟨e₁.trans e₂.symm, fun _ => trivial, fun ht => ?_⟩
      rw [e₁] at ht
      cases ht

theorem loop_ct : RelCT isa (Two LiveAt) (.loop iteration .e) fun _ _ => True := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration) (c := .e) (Q := fun _ _ => True) LoopPair iteration_pair
    q.2.2 _ _ _ _ _ _ ⟨q, rfl, hs, ht⟩ he₁ he₂

/-- The loop point an entry state starts at. -/
def entryPt (s : State) : Lp := (ofState s, 0, (ofState s).attempts)

/-- An entry state at the point `q`. -/
def EntAt (q : Lp) (s : State) : Prop := PSearchABI s ∧ entryPt s = q

theorem entry_ct : RelCT isa (Two EntAt) (.block entry) (Two LiveAt) := by
  refine two_post ?_ fun q s ⟨A, e⟩ => WP.mono (entry_ok A) fun t L => ⟨s, by rw [← e]; exact L⟩
  rw [show entry = [.mov .eax (.mem (argAt 0 9))] ++ entry.drop 1 from rfl]
  refine RelCT.block_append (RelCT.seq (two_piece
    (Ψ := fun (q : Lp) t => t.gpr .eax = q.1.S ∧ t.gpr .esp = q.1.sp) [.esp]
    (fun q s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact congrArg (fun q : Lp => q.1.sp) (h₁.2.trans h₂.2.symm)) (by taint_decide) fun q s ⟨A, e⟩ => ?_)
    (two_taint [.eax, .esp] (fun q s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2, h₂.2]) (by taint_decide)))
  subst e
  have e9 : argAt 0 9 = ⟨.esp, 4 + 4 * 9⟩ := by simp [argAt, at_]
  have r9 : readSrc s (.mem (argAt 0 9)) = some (arg s 9) := by
    rw [e9, readSrc_mem rfl ⟨_, List.mem_append_right _ (aR_mem A), arg_in A (i := 9) (by decide)⟩]; rfl
  exact wp_movS r9 fun t U _ => WP.block_nil ⟨U.gpr, by rw [U.other _ (by decide)]; rfl⟩

/-- A finished search with the public descriptor `p`. -/
def DoneAt (p : PPub) (s : State) : Prop := ∃ o r, Done p o r s

theorem finish_ct : RelCT isa (Two DoneAt) (.block finish) fun _ _ => True := by
  have pin : Pins (fun (p : PPub) t => Any p t ∧ t.gpr .ecx = p.up) [.esi, .esp] :=
    any_pins id fun _ _ h => h.1
  rw [show finish = [.mov .ecx (.mem (st upOff))] ++ finish.drop 1 from rfl]
  refine RelCT.block_append (RelCT.seq (two_piece
    (Ψ := fun (p : PPub) t => Any p t ∧ t.gpr .ecx = p.up) [.esi, .esp]
    (any_pins id fun p s ⟨_, _, D⟩ => D.any) (by taint_decide) fun p s ⟨o, r, D⟩ => ?_)
    (two_taint [.ecx, .esi, .esp] (fun q s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.2, h₂.2]
      · exact pin q s₁ s₂ h₁ h₂ .esi (by decide)
      · exact pin q s₁ s₂ h₁ h₂ .esp (by decide))
      (by taint_decide)))
  obtain ⟨A, rfl⟩ := D.input
  exact D.st.ld (Or.inr (Or.inl rfl)) (d := upOff) (by decide) (by decide) fun t St g _ _ _ =>
    WP.block_nil ⟨⟨o, _, _, rfl, St⟩, by rw [g]; rfl⟩

theorem wordsAt4 (m : Mem) (p : Addr) : Spec.Rsa.wordsAt m p 4 =
    [m.readW (p + BitVec.ofNat 64 0) 64, m.readW (p + BitVec.ofNat 64 8) 64, m.readW (p + BitVec.ofNat 64 16) 64,
      m.readW (p + BitVec.ofNat 64 24) 64] := rfl

/-- Two entry states whose public data agree start at the same loop point. -/
theorem pub_point {s t : State} (H : contract.pub s t) : entryPt s = entryPt t := by
  sig_pub [contract, Spec.Ffdh.sievedParameterSearchContract, Spec.Ffdh.parameterSearchSig, abi, argSlots, argVal,
    argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts] at H
  obtain ⟨SP, sy, L, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := H
  have inj : ∀ {l l' : List Byte}, l.map (fun x => x.toNat) = l'.map (fun x => x.toNat) → l = l' :=
    fun h => (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp h
  obtain ⟨L₁, L₂⟩ := List.append_inj L (by simp [Spec.Rsa.bytesAt, a6])
  have D := inj L₁
  rw [wordsAt4, wordsAt4] at L₂
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at L₂
  obtain ⟨k, _, _, _⟩ := L₂
  rw [BitVec.add_zero, BitVec.add_zero] at k
  have e : ofState s = ofState t := by
    simp only [ofState, PPub.mk.injEq]
    exact ⟨SP, a9, a0, a2, a5, a7, congrArg BitVec.toNat a1, congrArg BitVec.toNat a3, congrArg BitVec.toNat a4,
      congrArg BitVec.toNat a6, congrArg BitVec.toNat a8, k, D, sy⟩
  simp only [entryPt, e]

theorem code_ct : RelCT isa (Two EntAt) Impl.Ffdh.X86.ParamSearch.code fun _ _ => True := by
  unfold Impl.Ffdh.X86.ParamSearch.code
  exact RelCT.seq entry_ct (RelCT.seq (two_post (Ψ := fun (q : Lp) s => DoneAt q.1 s) loop_ct
    fun q s ⟨o, L⟩ => WP.mono (loop_ok L) fun t D => ⟨o, _, D⟩) (two_map (fun q : Lp => q.1) (fun _ _ h => h)
      finish_ct))

theorem constantTime : ConstantTime isa contract.pre contract.pub Impl.Ffdh.X86.ParamSearch.code := by
  intro s t tr ur sf tf S T H E F
  exact (code_ct _ _ _ _ _ _ ⟨entryPt s, ⟨pSearchABI_of S, rfl⟩, ⟨pSearchABI_of T, (pub_point H).symm⟩⟩
    E F).1

end VG.Proof.Ffdh.X86.PSearch

end

end

/-! # `vg_ffdh_generate_parameters` on i686, verified -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.PSearch

open VG VG.X86

def satArgument : Nat → BitVec 32
  | 0 => 0x1000
  | 1 => 64
  | 2 => 0x2000
  | 3 => 512
  | 4 => 2
  | 5 => 0x3000
  | 6 => 0
  | 7 => 0x10000
  | 8 => 1056
  | _ => 0x6000

/-- The arguments; a state with no attempts, the width 64 and the cap `32769 · 64 = 0x200040`; RSA's
table at `0x30000`. -/
def satMemory : Mem := fun a =>
  if (a - 0x20004).toNat < 40 then
    (satArgument ((a - 0x20004).toNat / 4)).extractLsb' (8 * ((a - 0x20004).toNat % 4)) 8
  else if a = 0x6008 then 0x40
  else if a = 0x6010 then 0x40
  else if a = 0x6012 then 0x20
  else constMem 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed a

def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemory
  rd := [⟨0x3000, 0⟩, ⟨0x30000, 8192⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 8⟩, ⟨0x10000, 8448⟩, ⟨0x6000, 128⟩, ⟨0x20004, 40⟩]
  syms _ := 0x30000

theorem sat_arguments (i : Nat) (index : i < 10) : arg satState i = satArgument i := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega_using [index]
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem single_held {m : Mem} {f : String → Addr} {name : String} {words : List (BitVec 64)}
    (H : ∀ i < words.length, m.readW (f name + BitVec.ofNat 64 (8 * i)) 64 = words.getD i 0) :
    Abi.constsHeld m f [(name, words)] := by
  intro c mem
  obtain rfl := List.mem_singleton.mp mem
  exact H

private theorem packed_regions (f : String → Addr) :
    Abi.constRegions f [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] =
      [⟨f VG.Impl.RsaKeyGen.TrialTable32.symbol, 8192⟩] := by
  rw [Abi.constRegions_cons, Abi.constRegions_nil, VG.Proof.RsaKeyGen.X86.Candidate.packed_length]

theorem sat_table : Abi.constsHeld satState.mem (fun name => (satState.syms name).setWidth 64)
    VG.Impl.RsaKeyGen.TrialTable32.consts := by
  apply single_held
  intro i index
  have fit : 8 * VG.Impl.RsaKeyGen.TrialTable32.packed.length ≤ 2 ^ 64 := by
    rw [VG.Proof.RsaKeyGen.X86.Candidate.packed_length]; decide
  have small : i < 1024 := by simpa only [VG.Proof.RsaKeyGen.X86.Candidate.packed_length] using index
  have ix : i < VG.Impl.RsaKeyGen.TrialTable32.packed.length := by
    rw [VG.Proof.RsaKeyGen.X86.Candidate.packed_length]; exact small
  change satMemory.readW (0x30000#64 + BitVec.ofNat 64 (8 * i)) 64 = VG.Impl.RsaKeyGen.TrialTable32.packed.getD i 0
  have held := constMem_held 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed fit i ix
  refine Eq.trans (Mem.readW_congr (m := satMemory) (m' := constMem 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed) ?_) held
  intro j bound
  have address : ((0x30000#64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j) - 0x20004#64).toNat =
      65532 + 8 * i + j := by
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_using [small, bound]
  have far : ∀ c : Addr, c.toNat < 0x10000 →
      0x30000#64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j ≠ c := by
    intro c hc e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
    omega_using [small, bound, hc, this]
  change (if _ then _ else _) = _
  rw [ite_eq_right_of_eq_false _ _ (eq_false fun inside => by
      change ((0x30000#64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j) - 0x20004#64).toNat < 40 at inside
      rw [address] at inside; omega_using [inside]),
    ite_eq_right_of_eq_false _ _ (eq_false (far 0x6008 (by decide))), ite_eq_right_of_eq_false _ _ (eq_false (far 0x6010 (by decide))),
    ite_eq_right_of_eq_false _ _ (eq_false (far 0x6012 (by decide)))]

theorem satisfiable : ∃ s, contract.pre s := by
  refine ⟨satState, ?_⟩
  sig_pre [contract, Spec.Ffdh.sievedParameterSearchContract, Spec.Ffdh.parameterSearchSig, abi,
    argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts, stackBelow]
  simp only [sat_arguments 0 (by decide), sat_arguments 1 (by decide), sat_arguments 2 (by decide),
    sat_arguments 3 (by decide), sat_arguments 4 (by decide), sat_arguments 5 (by decide),
    sat_arguments 6 (by decide), sat_arguments 7 (by decide), sat_arguments 8 (by decide),
    sat_arguments 9 (by decide)]
  simp only [packed_regions, List.forall_mem_singleton]
  sig_and_intros
  all_goals first
    | exact sat_table
    | exact Region.disjoint_of_sep (by decide +kernel)
    | (unfold Spec.Rsa.scratchWords; decide +kernel)
    | decide +kernel
    | rfl

theorem verified : Verified target Impl.Ffdh.X86.ParamSearch.code contract :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Ffdh.X86.PSearch
