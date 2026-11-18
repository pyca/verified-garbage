module

import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Bignum.Layout
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.Loop
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.Correct
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.Loop
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.Correct
meta import VerifiedGarbage.Proof.Rsa.BytesFrame
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchGuards
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchGuards
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.CT
import VerifiedGarbage.Proof.EntropyRequest
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.CT
meta import VerifiedGarbage.Proof.EntropyRequest
import VerifiedGarbage.Spec.RsaKeyGen.GenerationAgrees
meta import VerifiedGarbage.Spec.RsaKeyGen.GenerationAgrees
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.Classify
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.Classify
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `RsaKeyGen.X86_64.Generate.CTClassify`, which only this module used -/

section

/-! ### `RsaKeyGen.X86_64.Generate.CTCalls`, which only this module used -/

section

/-! ### `RsaKeyGen.X86_64.Generate.CTFrame`, which only this module used -/

section

/-! # The frame's public words, for the taint analysis

Two runs with the same public descriptor have the same writable regions, the
frame first, and the same frame words 0 to 7 and 11 (the pointers and
lengths the controller loads): the taint analysis starts from `r12` and
`rsp` public, `r12` the frame's base and those words public (`genT`), and so
from any frame state of each (`AnyFrame`) — or, inside a call's frame of its
stack arguments, from `genT'` with `rsp` that frame's base.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.Generation (allocated allocated_rsp allocated_reg)
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (limitOf)

/-- The writable regions in the frame: the frame, the key's buffer, `used`,
the working space and the state. -/
def genWr (p : GenPublic) : List Region := [p.frame, cK p, rU p, rS p, cS p]

/-- A frame state of some run with the public descriptor `p`. -/
def AnyFrame (p : GenPublic) (s : State) : Prop := ∃ original used st, GenFrame p original used st s

/-- The taint: `rs`, `r12` and `rsp` public, `r12` the frame's base, the
frame's words 0 to 7 and 11 public. -/
def genT (rs : List Reg) : X86_64.Taint.T :=
  { regs := .ofList (rs ++ [.r12, .rsp]), flags := false, lens := [160, 0, 0, 0, 0], bases := [(.r12, 0, 0)],
    slots := [(0, 0, 64), (0, 88, 8)] }

/-- The taint inside a call's frame of `k` octets: that frame first, `rsp`
its base. -/
def genT' (k : Nat) (rs : List Reg) : X86_64.Taint.T :=
  { regs := .ofList (rs ++ [.r12, .rsp]), flags := false, lens := [k, 160, 0, 0, 0, 0],
    bases := [(.rsp, 0, 0), (.r12, 1, 0)], slots := [(1, 0, 64), (1, 88, 8)] }

section

variable {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}

theorem GenFrame.wr_eq (h : GenFrame p original used st s) : s.wr = genWr p := by
  have hs : inScr original = rS p := by rw [← h.input.2]; rfl
  rw [h.wr, h.input.1.2.2.2.1]
  simp only [inWrites]
  rw [h.key_region, h.used_region, h.state_region, hs]; rfl

theorem genWr_wf (hf : CFacts p) (hfk : p.frame.Disjoint (cK p))
    (hfu : p.frame.Disjoint (rU p)) (hfs : p.frame.Disjoint (rS p)) (hft : p.frame.Disjoint (cS p)) :
    (genWr p).Pairwise Region.Disjoint ∧ ∀ r ∈ genWr p, r.len ≤ 2 ^ 64 := by
  refine ⟨?_, ?_⟩
  · simp only [genWr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hfk, hfu, hfs, hft⟩, ⟨hf.kU, hf.kS, hf.kT⟩, ⟨hf.uS, hf.uT⟩, hf.sT, fun _ h => h.elim⟩
  · simp only [genWr, List.mem_cons, List.not_mem_nil, or_false]
    have := hf.nK; have := hf.nS
    rintro r (rfl | rfl | rfl | rfl | rfl) <;> simp only <;> omega_arith

theorem GenFrame.frame_facts (h : GenFrame p original used st s) :
    p.frame.Disjoint (cK p) ∧ p.frame.Disjoint (rU p) ∧ p.frame.Disjoint (rS p) ∧ p.frame.Disjoint (cS p) := by
  have hs : inScr original = rS p := by rw [← h.input.2]; rfl
  refine ⟨h.frame_key, ?_, ?_, h.state_frame⟩
  · have := h.input.frame_disjoint_writes (r := inUsed original) (by simp [inWrites])
    rwa [h.used_region] at this
  · have := h.input.frame_disjoint_writes (r := inScr original) (by simp [inWrites])
    rwa [hs] at this

end

/-- A word's bytes agree where the words do. -/
theorem word_bytes {m₁ m₂ : Mem} {a : Addr} (h : m₁.readW a 64 = m₂.readW a 64) {k : Nat} (hk : k < 8) :
    m₁ (a + BitVec.ofNat 64 k) = m₂ (a + BitVec.ofNat 64 k) := by
  rw [← byte_readW m₁ a (w := 64) (by omega_using [hk]), ← byte_readW m₂ a (w := 64) (by omega_using [hk]), h]

/-- Two frame states with the same descriptor agree on the frame's public
bytes. -/
theorem frame_slots {p : GenPublic} {s₁ s₂ : State} (h₁ : AnyFrame p s₁) (h₂ : AnyFrame p s₂) {k : Nat}
    (hk : k < 64 ∨ (88 ≤ k ∧ k < 96)) :
    s₁.mem (p.F + BitVec.ofNat 64 k) = s₂.mem (p.F + BitVec.ofNat 64 k) := by
  obtain ⟨o₁, u₁, t₁, g₁⟩ := h₁
  obtain ⟨o₂, u₂, t₂, g₂⟩ := h₂
  have hF : p.F.toNat + 160 ≤ 2 ^ 64 := g₁.scr.nowrap
  have hw (j : Nat) (v : BitVec 64) (hj : ∀ u, (j, v) ∈ p.headers u) :
      s₁.mem.readW (p.F + BitVec.ofNat 64 (8 * j)) 64 = s₂.mem.readW (p.F + BitVec.ofNat 64 (8 * j)) 64 :=
    (g₁.header (hj u₁)).trans (g₂.header (hj u₂)).symm
  have key (j : Nat) (v : BitVec 64) (hj : ∀ u, (j, v) ∈ p.headers u) (hk' : 8 * j ≤ k ∧ k < 8 * j + 8) :
      s₁.mem (p.F + BitVec.ofNat 64 k) = s₂.mem (p.F + BitVec.ofNat 64 k) := by
    rw [show p.F + BitVec.ofNat 64 k = p.F + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 (k - 8 * j) by
      rw [Offset.add_add]; congr 2; omega_using [hk']]
    exact word_bytes (hw j v hj) (by omega_using [hk'])
  have hq : k / 8 < 8 ∨ k / 8 = 11 := by omega_using [hk]
  rcases hq with hq | hq
  · have : k / 8 = 0 ∨ k / 8 = 1 ∨ k / 8 = 2 ∨ k / 8 = 3 ∨ k / 8 = 4 ∨ k / 8 = 5 ∨ k / 8 = 6 ∨ k / 8 = 7 := by omega_using [hq]
    rcases this with h | h | h | h | h | h | h | h
    · exact key 0 p.kp (fun _ => by simp [GenPublic.headers]) (by omega_using [h])
    · exact key 1 (BitVec.ofNat 64 p.L) (fun _ => by simp [GenPublic.headers]) (by omega_using [h])
    · exact key 2 p.up (fun _ => by simp [GenPublic.headers]) (by omega_using [h])
    · exact key 3 p.rp (fun _ => by simp [GenPublic.headers]) (by omega_using [h])
    · exact key 4 (BitVec.ofNat 64 p.randLen) (fun _ => by simp [GenPublic.headers]) (by omega_using [h])
    · exact key 5 p.B (fun _ => by simp [GenPublic.headers]) (by omega_using [h])
    · exact key 6 (BitVec.ofNat 64 (p.Z / 8)) (fun _ => by simp [GenPublic.headers]) (by omega_using [h])
    · exact key 7 p.stp (fun _ => by simp [GenPublic.headers]) (by omega_using [h])
  · exact key 11 (BitVec.ofNat 64 (limitOf p.L p.eB)) (fun _ => by simp [GenPublic.headers]) (by omega_using [hq])

theorem any_agree {p : GenPublic} {rs : List Reg} {s₁ s₂ : State} (h₁ : AnyFrame p s₁) (h₂ : AnyFrame p s₂)
    (hrs : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : X86_64.Taint.Agree (genT rs) s₁ s₂ := by
  obtain ⟨o₁, u₁, t₁, g₁⟩ := id h₁
  obtain ⟨o₂, u₂, t₂, g₂⟩ := id h₂
  have hf := g₁.input.cfacts
  obtain ⟨hfk, hfu, hfs, hft⟩ := g₁.frame_facts
  obtain ⟨hpw, hlen⟩ := genWr_wf hf hfk hfu hfs hft
  have wf : ∀ {s : State}, s.wr = genWr p → s.gpr .r12 = p.F → X86_64.Taint.Wf (genT rs) s := fun hw hr => by
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun q hq => ?_⟩
    · rw [hw]; exact .cons (Nat.le_refl _) (.cons (Nat.zero_le _) (.cons (Nat.zero_le _) (.cons (Nat.zero_le _)
        (.cons (Nat.zero_le _) .nil))))
    · rw [hw]; exact hpw
    · rw [hw]; exact hlen
    · simp only [genT, List.mem_singleton] at hq; subst hq
      simp only [X86_64.Taint.region, hw, genWr, List.getD_cons_zero]
      rw [hr, BitVec.add_zero]
  have hb : ∀ {s : State}, s.wr = genWr p → ∀ k, X86_64.Taint.byteAddr s 0 k = p.F + BitVec.ofNat 64 k := fun hw k => by
    simp only [X86_64.Taint.byteAddr, X86_64.Taint.region, hw, genWr, List.getD_cons_zero]
  refine ⟨⟨fun r hr => ?_, fun hf => by cases hf⟩, fun _ => by rw [g₁.wr_eq, g₂.wr_eq],
    wf g₁.wr_eq g₁.r12, wf g₂.wr_eq g₂.r12, fun sl hsl => ?_, fun sl hsl k hk₁ hk₂ => ?_, X86_64.Taint.noLo,
    X86_64.Taint.noXr⟩
  · rcases List.mem_append.mp (RegSet.mem_ofList.mp hr) with hr | hr
    · exact hrs r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [g₁.r12, g₂.r12]
      · rw [g₁.rsp, g₂.rsp]
  · simp only [genT, List.mem_cons, List.not_mem_nil, or_false] at hsl
    rcases hsl with rfl | rfl <;> simp [genT]
  · simp only [genT, List.mem_cons, List.not_mem_nil, or_false] at hsl
    rcases hsl with rfl | rfl <;> simp only at hk₁ hk₂ ⊢ <;> rw [hb g₁.wr_eq, hb g₂.wr_eq]
    · exact frame_slots h₁ h₂ (.inl hk₂)
    · exact frame_slots h₁ h₂ (.inr ⟨hk₁, hk₂⟩)

/-- Code the taint analysis checks from `genT rs`. -/
theorem frame_taint {α : Type} {Φ : α → State → Prop} {c : Prog isa} (g : α → GenPublic) (rs : List Reg)
    (hΦ : ∀ a s, Φ a s → AnyFrame (g a) s) (hrs : Pins Φ rs) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (genT rs) c hc).isSome = true) : RelCT isa (Two Φ) c fun _ _ => True :=
  RelCT.taint (A := taint) (genT rs) (fun _ _ ⟨a, h₁, h₂⟩ => any_agree (hΦ a _ h₁) (hΦ a _ h₂) (hrs a _ _ h₁ h₂)) h

/-- Inside a call's frame of `k` octets below the controller's. -/
theorem alloc_agree {p : GenPublic} {rs : List Reg} {k : Nat} (hk : k ≤ 392) {s₁ s₂ : State}
    (h₁ : AnyFrame p s₁) (h₂ : AnyFrame p s₂)
    (hrs : ∀ r ∈ rs, (allocated k s₁).gpr r = (allocated k s₂).gpr r) :
    X86_64.Taint.Agree (genT' k rs) (allocated k s₁) (allocated k s₂) := by
  obtain ⟨o₁, u₁, t₁, g₁⟩ := id h₁
  obtain ⟨o₂, u₂, t₂, g₂⟩ := id h₂
  have hf := g₁.input.cfacts
  obtain ⟨hfk, hfu, hfs, hft⟩ := g₁.frame_facts
  obtain ⟨hpw, hlen⟩ := genWr_wf hf hfk hfu hfs hft
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, sU, sS, sT, -⟩ := hst
  have hFk : p.F - BitVec.ofNat 64 k = p.sp - BitVec.ofNat 64 (160 + k) := by
    rw [GenPublic.F, BitVec.sub_sub, BitVec.ofNat_add]
  have hA : Region.Sub ⟨p.F - BitVec.ofNat 64 k, k⟩ (cStack p) := by
    rw [hFk]; exact Offset.sub_below p.sp (by omega_using [hk]) (by omega_using [hk])
  have hAF : (⟨p.F - BitVec.ofNat 64 k, k⟩ : Region).Disjoint p.frame := by
    have := Offset.sep_below p.sp 552 (a := 160 + k) (n := k) (b := 160) (k := 160) (by omega_using [hk]) (by decide)
      (Or.inl (by omega_using [hk])) (by omega_using [hk]) (by decide)
    rw [← hFk] at this
    exact disj_of_sep this
  have hwr : ∀ {s : State} {o : State} {u : Nat} {t : KeyProgress}, GenFrame p o u t s →
      (allocated k s).wr = ⟨p.F - BitVec.ofNat 64 k, k⟩ :: genWr p := fun {s} _ _ _ g => by
    show (⟨s.gpr .rsp - BitVec.ofNat 64 k, k⟩ : Region) :: s.wr = _
    rw [g.rsp, g.wr_eq]
  have wf : ∀ {s : State} {o : State} {u : Nat} {t : KeyProgress}, GenFrame p o u t s →
      X86_64.Taint.Wf (genT' k rs) (allocated k s) := fun g => by
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun q hq => ?_⟩
    · rw [hwr g]; exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) (.cons (Nat.zero_le _) (.cons (Nat.zero_le _)
        (.cons (Nat.zero_le _) (.cons (Nat.zero_le _) .nil)))))
    · rw [hwr g]
      refine List.Pairwise.cons (fun r hr => ?_) hpw
      simp only [genWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact hAF
      · exact (sK.sub_right hA).symm
      · exact (sU.sub_right hA).symm
      · exact (sS.sub_right hA).symm
      · exact (sT.sub_right hA).symm
    · rw [hwr g]
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · show k ≤ 2 ^ 64; omega_using [hk]
      · exact hlen r hr
    · simp only [genT', List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · simp only [X86_64.Taint.region, hwr g, List.getD_cons_zero]
        rw [allocated_rsp, g.rsp, BitVec.add_zero]
      · simp only [X86_64.Taint.region, hwr g, genWr, List.getD_cons_succ, List.getD_cons_zero]
        rw [allocated_reg _ _ _ (by decide), g.r12, BitVec.add_zero]
  have hb : ∀ {s : State} {o : State} {u : Nat} {t : KeyProgress}, GenFrame p o u t s → ∀ j,
      X86_64.Taint.byteAddr (allocated k s) 1 j = p.F + BitVec.ofNat 64 j := fun g j => by
    simp only [X86_64.Taint.byteAddr, X86_64.Taint.region, hwr g, genWr, List.getD_cons_succ, List.getD_cons_zero]
  refine ⟨⟨fun r hr => ?_, fun hf => by cases hf⟩, fun _ => by rw [hwr g₁, hwr g₂], wf g₁, wf g₂,
    fun sl hsl => ?_, fun sl hsl j hj₁ hj₂ => ?_, X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · rcases List.mem_append.mp (RegSet.mem_ofList.mp hr) with hr | hr
    · exact hrs r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [allocated_reg _ _ _ (by decide), allocated_reg _ _ _ (by decide), g₁.r12, g₂.r12]
      · rw [allocated_rsp, allocated_rsp, g₁.rsp, g₂.rsp]
  · simp only [genT', List.mem_cons, List.not_mem_nil, or_false] at hsl
    rcases hsl with rfl | rfl <;> simp [genT']
  · simp only [genT', List.mem_cons, List.not_mem_nil, or_false] at hsl
    rcases hsl with rfl | rfl <;> simp only at hj₁ hj₂ ⊢ <;> rw [hb g₁, hb g₂] <;>
      simp only [VG.Proof.Ffdh.X86_64.Generation.allocated_mem]
    · exact frame_slots h₁ h₂ (.inl hj₂)
    · exact frame_slots h₁ h₂ (.inr ⟨hj₁, hj₂⟩)

end VG.Proof.RsaKeyGen.X86_64.Generate

end

end

/-! ### `RsaKeyGen.X86_64.Generate.CTPoint`, which only this module used -/

section

/-! # Where two runs of the loop are

Two runs at the same point (`GenPoint`) agree on the public descriptor, the
octets consumed, the progress' public words (the generations left, the
phase's word and the counted candidates left), the state's request word and
the trace still to come, which each run's own key search from there gives.
The trace's first entry is the prime search's status, consumption, octets
left and trace, and, after `q`'s, the key's status: what each step does
follows from it (`gen_ct_step`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 (RoundImpl)
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

structure GenPoint where
  inputs : GenPublic
  used : Nat
  left : Nat
  ph : Nat
  remaining : Nat
  req : BitVec 64
  trace : List Nat

/-- A run's progress `st` from `original`, at the point. -/
def AtPoint (q : GenPoint) (original : State) (st : KeyProgress) : Prop :=
  st.left = q.left ∧ phaseWord st.phase = q.ph ∧ st.remaining = q.remaining ∧
    (tailOf q.inputs original q.used st).trace = q.trace

/-- A loop state at the point. -/
def GenCTL (q : GenPoint) (s : State) : Prop :=
  ∃ original st, AtPoint q original st ∧ GenLive q.inputs original q.used st s ∧
    word s.mem q.inputs.stp 24 = q.req

/-! ## The first step, from the trace -/

abbrev GenPoint.status (q : GenPoint) : Nat := traceStatus q.trace
abbrev GenPoint.cand (q : GenPoint) : Nat := traceUsed q.trace
abbrev GenPoint.key (q : GenPoint) : Nat := traceKey q.trace

/-- Whether the key search goes on past the point's step. -/
def GenPoint.continues (q : GenPoint) : Prop :=
  (q.status = 3 ∧ ¬q.left < 2) ∨ (q.status = 1 ∧ q.cand ≠ 0 ∧ (q.ph = 0 ∨ q.key = 2))

/-- The point past the step, when the key search goes on. -/
def GenPoint.next (q : GenPoint) : GenPoint :=
  ⟨q.inputs, q.used + q.cand, if q.status = 3 then q.left - 1 else q.left,
    if q.status = 1 ∧ q.ph = 0 then 1 else 0, limitOf q.inputs.L q.inputs.eB, BitVec.ofNat 64 0,
    q.trace.drop (traceEntry q.trace + if q.status = 1 ∧ q.ph ≠ 0 then 2 else 0)⟩

section

variable {q : GenPoint} {original s : State} {st : KeyProgress}

theorem AtPoint.entry (h : AtPoint q original st) :
    ∃ rest, q.trace = primeEntry (rOf q.inputs original q.used st) ++ rest := by
  obtain ⟨rest, hr⟩ := keySearch_trace (L := q.inputs.L) (eB := q.inputs.eB) st ((genRand original).drop q.used)
  exact ⟨rest, h.2.2.2.symm.trans hr⟩

theorem AtPoint.status (h : AtPoint q original st) : (rOf q.inputs original q.used st).status = q.status := by
  obtain ⟨rest, hr⟩ := h.entry
  rw [GenPoint.status, hr, (primeEntry_facts _ rest).1]

theorem AtPoint.cand (h : AtPoint q original st) : (rOf q.inputs original q.used st).used = q.cand := by
  obtain ⟨rest, hr⟩ := h.entry
  rw [GenPoint.cand, hr, (primeEntry_facts _ rest).2.1]

theorem AtPoint.available (h : AtPoint q original st) :
    (rOf q.inputs original q.used st).available = traceAvailable q.trace := by
  obtain ⟨rest, hr⟩ := h.entry
  rw [hr, (primeEntry_facts _ rest).2.2.1]

theorem AtPoint.prime (h : AtPoint q original st) : (rOf q.inputs original q.used st).trace = tracePrime q.trace := by
  obtain ⟨rest, hr⟩ := h.entry
  rw [hr, (primeEntry_facts _ rest).2.2.2.1]

theorem AtPoint.entryLen (h : AtPoint q original st) :
    (primeEntry (rOf q.inputs original q.used st)).length = traceEntry q.trace := by
  obtain ⟨rest, hr⟩ := h.entry
  rw [hr, (primeEntry_facts _ rest).2.2.2.2]

/-- After `q`'s search accepted a prime, the key's status. -/
theorem AtPoint.keyStatus (h : AtPoint q original st)
    (hle : q.used + (rOf q.inputs original q.used st).used ≤ q.inputs.randLen)
    (hrl : (genRand original).length = q.inputs.randLen) {c : Nat}
    {pB : List Byte} (ho : (rOf q.inputs original q.used st).outcome = .accepted c)
    (hpos : 0 < (rOf q.inputs original q.used st).used) (hph : st.phase = .q pB) :
    keyResultStatus (keyFromPrimes (16 * q.inputs.L) (Spec.Rsa.os2ip q.inputs.eB) (Spec.Rsa.os2ip pB)
      (Spec.Rsa.os2ip (Spec.Rsa.i2osp c q.inputs.L))) = q.key := by
  have hrest : (rOf q.inputs original q.used st).used ≤ ((genRand original).drop q.used).length := by
    rw [List.length_drop, hrl]; omega_using [hle]
  obtain ⟨rest, hr⟩ := keySearch_trace_key (L := q.inputs.L) (eB := q.inputs.eB) ho (drop_lt hpos hrest) hph
  rw [GenPoint.key, ← h.2.2.2, tailOf, hr, primeEntry_key]

theorem keyResultStatus_two (k : Except Failure Key ⊕ Unit) : keyResultStatus k = 2 ↔ k = .inr () := by
  rcases k with (k | k) | ⟨⟩ <;> simp [keyResultStatus]

theorem continues_iff (h : AtPoint q original st) (hl : GenFrame q.inputs original q.used st s) :
    ContSpec q.inputs original q.used st ↔ q.continues := by
  have hs := h.status
  have hc := h.cand
  have hleft := h.1
  have hph := h.2.1
  unfold ContSpec GenPoint.continues
  rw [← hs, ← hc, ← hleft, ← hph]
  cases ho : (rOf q.inputs original q.used st).outcome with
  | entropy k a => simp [rOf_status, ho, Spec.Entropy.Outcome.status]
  | exhausted => simp [rOf_status, ho, Spec.Entropy.Outcome.status]
  | accepted c =>
    have hs1 : (rOf q.inputs original q.used st).status = 1 := by rw [rOf_status, ho]; rfl
    rw [hs1]
    by_cases h0 : (rOf q.inputs original q.used st).used = 0
    · simp [h0]
    · cases hp : st.phase with
      | p => simp [h0, phaseWord]
      | q pB =>
        have hk := h.keyStatus (rOf_used_le hl) (genRand_length hl) ho (by omega_using [h0]) hp
        rw [← hk]
        simp [h0, phaseWord, keyResultStatus_two]

end

/-! ## A step -/

/-- After an iteration: the next point and the loop's condition, or its end. -/
def GenCTStep (q : GenPoint) (t : State) : Prop :=
  (q.continues ∧ eval .e t = some true ∧ GenCTL q.next t) ∨ (¬q.continues ∧ eval .e t = some false)

theorem next_point {q : GenPoint} {original t : State} {st : KeyProgress} {final : KeySearchResult}
    (h : AtPoint q original st) (hc : Cont q.inputs original final q.used st t) : GenCTL q.next t := by
  obtain ⟨-, hreq, ⟨st', e, hlive, -, htail, hrem, hnext⟩, -⟩ := hc
  have hs := h.status
  have hcd := h.cand
  obtain ⟨hleft, hph, -, htr⟩ := h
  refine ⟨original, st', ⟨?_, ?_, ?_, ?_⟩, by rw [GenPoint.next, ← hcd]; exact hlive, hreq⟩
  all_goals simp only [GenPoint.next]
  · rcases hnext with ⟨ho, hl, -, -⟩ | ⟨c, ho, -, hl, -, -⟩ | ⟨c, pB, ho, -, hl, -, -⟩ <;>
      rw [← hs, rOf_status, ho] <;> simp [hl, hleft, Spec.Entropy.Outcome.status]
  · rcases hnext with ⟨ho, -, hp, -⟩ | ⟨c, ho, hp, -, hp', -⟩ | ⟨c, pB, ho, hp, -, hp', -⟩
    · rw [← hs, rOf_status, ho, hp]; simp [Spec.Entropy.Outcome.status, phaseWord]
    · rw [← hs, rOf_status, ho, hp', ← hph, hp]; simp [Spec.Entropy.Outcome.status, phaseWord]
    · rw [← hs, rOf_status, ho, hp', ← hph, hp]; simp [Spec.Entropy.Outcome.status, phaseWord]
  · exact hrem
  · rw [← hcd, ← htr, htail]
    simp only [Spec.Entropy.Result.consume, List.drop_append]
    rcases hnext with ⟨ho, -, -, rfl⟩ | ⟨c, ho, hp, -, -, rfl⟩ | ⟨c, pB, ho, hp, -, -, rfl⟩
    · rw [← hs, rOf_status, ho]; simp [Spec.Entropy.Outcome.status]
    · rw [← hs, rOf_status, ho, ← hph, hp]; simp [Spec.Entropy.Outcome.status, phaseWord]
    · rw [← hs, rOf_status, ho, ← hph, hp]; simp [Spec.Entropy.Outcome.status, phaseWord, List.length_append]

theorem gen_ct_step [Key.KeyProof] (v : RoundImpl) (q : GenPoint) (s : State) (h : GenCTL q s) :
    WP isa (iteration (searchCall v) keyCall) s (GenCTStep q) := by
  obtain ⟨o, st, ha, hl, -⟩ := h
  have hi : GenIter q.inputs o ((tailOf q.inputs o q.used st).consume q.used []) q.used st s := ⟨hl, [], rfl⟩
  unfold iteration
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq (WP.mono (search_run v hl) fun t hs => ?_)
  refine WP.seq (WP.mono (classify_ok hi hs) fun u hc => ?_)
  rcases hc with ⟨hcs, hct⟩ | ⟨hcs, hd⟩
  · obtain ⟨o', st', ha', hl', hr'⟩ := next_point ha hct
    refine WP.mono (status_guard hl'.toGenFrame hct.status (by decide)) fun x ⟨⟨hx, hmem⟩, k⟩ =>
      .inl ⟨(continues_iff ha hl.toGenFrame).mp hcs, hx, o', st', ha', ⟨hl'.toGenFrame.keep hmem k.2.1 k.2.2
        (fun r hr => k.gpr (by revert r; decide)), by rw [hmem]; exact hl'.key⟩, by rw [hmem]; exact hr'⟩
  · have hlt := keyStatus_lt ((tailOf q.inputs o q.used st).consume q.used [])
    refine WP.mono (status_guard hd.1 hd.2.1 (by omega_using [hlt])) fun x ⟨⟨hx, _⟩, _⟩ =>
      .inr ⟨fun h => hcs ((continues_iff ha hl.toGenFrame).mpr h), ?_⟩
    rw [hx]; congr 1; simp only [decide_eq_false_iff_not]; omega_using [hlt]

end VG.Proof.RsaKeyGen.X86_64.Generate

end

end

/-! # The calls' timing

The prime search's and the key's: their arguments are the same in two runs
at a point, and so is what their contracts let their timing depend on — the
search's status, consumption, request and trace, and the key's status, all
from the point's trace.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 (RoundImpl)
open VG.Proof.Ffdh.X86_64.Generation (allocated allocated_rsp allocated_reg allocated_mem frame_alloc_ct)
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

theorem GenCTL.any {q : GenPoint} {s : State} (h : GenCTL q s) : AnyFrame q.inputs s :=
  let ⟨o, st, _, hl, _⟩ := h; ⟨o, _, st, hl.toGenFrame⟩

theorem outOf_ph {p : GenPublic} {st₁ st₂ : KeyProgress} (h : phaseWord st₁.phase = phaseWord st₂.phase) :
    outOf p st₁ = outOf p st₂ := by
  unfold outOf; rw [h]

theorem plenOf_ph {p : GenPublic} {st₁ st₂ : KeyProgress} (h : phaseWord st₁.phase = phaseWord st₂.phase) :
    plenOf p st₁ = plenOf p st₂ := by
  unfold plenOf; rw [h]

/-! ## The prime search -/

/-- The search's entry, before the call. -/
def CallSCT (q : GenPoint) (u : State) : Prop :=
  ∃ original st s, AtPoint q original st ∧ GenLive q.inputs original q.used st s ∧
    word s.mem q.inputs.stp 24 = q.req ∧ SearchRegs q.inputs st u ∧
    u.mem = writeFrame s.mem (q.inputs.F - BitVec.ofNat 64 48) (callValues q.inputs q.used st) ∧
    Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11] (allocated 48 s) u

/-- The search's exponent and state words at its entry. -/
theorem callS_state {p : GenPublic} {original s u : State} {used : Nat} {st : KeyProgress}
    (h : GenLive p original used st s) (hu : u.gpr .rsp = p.sp - BitVec.ofNat 64 208) (ha : SearchRegs p st u)
    (hm : u.mem = writeFrame s.mem (p.F - BitVec.ofNat 64 48) (callValues p used st)) :
    Search.searchE (callS p used st u) = p.eB ∧
      Spec.Rsa.wordsAt (callS p used st u).mem (stackArg (callS p used st u) 5) 4 =
        [BitVec.ofNat 64 st.remaining, BitVec.ofNat 64 p.L, BitVec.ofNat 64 (primeEntropy p.L),
          word s.mem p.stp 24] := by
  have hf := h.input.cfacts
  have hfr := callS_frame hu hm
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨-, -, -, sT, -⟩ := hst
  obtain ⟨-, -, -, -, -, a5⟩ := callS_args (used := used) (st := st) hu hm
  obtain ⟨-, -, -, hcx, h8, -⟩ := ha
  have hword (d : Nat) (hd : d + 8 ≤ 56) : word (callS p used st u).mem p.stp d = word s.mem p.stp d :=
    hfr.readW (r := cS p) (Offset.contains_base _ hd (by have := hf.nT; omega_using [hd]))
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact sT) (by decide)
  refine ⟨?_, ?_⟩
  · simp only [Search.searchE, callS_gpr (show Reg.rcx ≠ .rsp by decide), callS_gpr (show Reg.r8 ≠ .rsp by decide),
      hcx, h8, toNat_ofNat_lt (show 8 < 2 ^ 64 by decide)]
    rw [← h.state.e]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact hfr.bytes (R := ⟨p.stp + BitVec.ofNat 64 48, 8⟩) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact sT.sub_left rE_sub) (by show 8 ≤ 2 ^ 64; decide)
      (List.mem_range.mp hi)
  · rw [a5]
    show [word _ p.stp (8 * 0), word _ p.stp (8 * 1), word _ p.stp (8 * 2), word _ p.stp (8 * 3)] = _
    rw [hword _ (by decide), hword _ (by decide), hword _ (by decide), hword _ (by decide)]
    have h0 := h.state.remaining
    have h1 := h.state.len
    have h2 := h.state.cap
    simp only [Nat.reduceMul] at h0 h1 h2 ⊢
    rw [h0, h1, h2]

theorem search_call_ct (v : RoundImpl) : RelCT isa (Two CallSCT) (searchCall v) (fun _ _ => True) := by
  refine RelCT.callEx (k := Search.searchContract) (Search.search_correct v) (Search.search_constantTime v)
    fun u₁ u₂ ⟨q, h₁, h₂⟩ => ?_
  obtain ⟨o₁, st₁, s₁, a₁, l₁, w₁, r₁, m₁, k₁⟩ := h₁
  obtain ⟨o₂, st₂, s₂, a₂, l₂, w₂, r₂, m₂, k₂⟩ := h₂
  have hu₁ : u₁.gpr .rsp = q.inputs.sp - BitVec.ofNat 64 208 := by
    rw [k₁.gpr (by decide), allocated_rsp, l₁.rsp, F_48]
  have hu₂ : u₂.gpr .rsp = q.inputs.sp - BitVec.ofNat 64 208 := by
    rw [k₂.gpr (by decide), allocated_rsp, l₂.rsp, F_48]
  have hph : phaseWord st₁.phase = phaseWord st₂.phase := a₁.2.1.trans a₂.2.1.symm
  have hres₁ := callS_result l₁ hu₁ r₁ m₁
  have hres₂ := callS_result l₂ hu₂ r₂ m₂
  obtain ⟨e₁, ws₁⟩ := callS_state l₁ hu₁ r₁ m₁
  obtain ⟨e₂, ws₂⟩ := callS_state l₂ hu₂ r₂ m₂
  have hlen₁ : Search.searchLen (callS q.inputs q.used st₁ u₁) = q.inputs.L := by
    simp only [Search.searchLen, callS_gpr (show Reg.rsi ≠ .rsp by decide), r₁.2.1]
    exact toNat_ofNat_lt (by have := l₁.input.cfacts.len.2.1; omega_using [this])
  have hlen₂ : Search.searchLen (callS q.inputs q.used st₂ u₂) = q.inputs.L := by
    simp only [Search.searchLen, callS_gpr (show Reg.rsi ≠ .rsp by decide), r₂.2.1]
    exact toNat_ofNat_lt (by have := l₂.input.cfacts.len.2.1; omega_using [this])
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := callS_args (used := q.used) (st := st₁) hu₁ m₁
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := callS_args (used := q.used) (st := st₂) hu₂ m₂
  obtain ⟨di₁, si₁, dx₁, cx₁, r8₁, r9₁⟩ := r₁
  obtain ⟨di₂, si₂, dx₂, cx₂, r8₂, r9₂⟩ := r₂
  refine ⟨sReads q.inputs q.used st₁, sWrites q.inputs st₁, sReads q.inputs q.used st₂, sWrites q.inputs st₂,
    callS_pre l₁ hu₁ ⟨di₁, si₁, dx₁, cx₁, r8₁, r9₁⟩ m₁, callS_pre l₂ hu₂ ⟨di₂, si₂, dx₂, cx₂, r8₂, r9₂⟩ m₂, ?_,
    search_covers_reads l₁ k₁.2.1 k₁.2.2, search_covers_writes l₁ k₁.2.2,
    search_covers_reads l₂ k₂.2.1 k₂.2.2, search_covers_writes l₂ k₂.2.2, hu₁.trans hu₂.symm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, e₁.trans e₂.symm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [callS_rsp hu₁, callS_rsp hu₂]
  · rw [callS_gpr (by decide), callS_gpr (by decide), di₁, di₂, outOf_ph hph]
  · rw [callS_gpr (by decide), callS_gpr (by decide), si₁, si₂]
  · rw [callS_gpr (by decide), callS_gpr (by decide), dx₁, dx₂]
  · rw [callS_gpr (by decide), callS_gpr (by decide), cx₁, cx₂]
  · rw [callS_gpr (by decide), callS_gpr (by decide), r8₁, r8₂]
  · rw [callS_gpr (by decide), callS_gpr (by decide), r9₁, r9₂]
  · match j, hj with
    | 0, _ => rw [b0, c0, plenOf_ph hph]
    | 1, _ => rw [b1, c1]
    | 2, _ => rw [b2, c2]
    | 3, _ => rw [b3, c3]
    | 4, _ => rw [b4, c4]
    | 5, _ => rw [b5, c5]
  · rw [ws₁, ws₂, a₁.2.2.1, a₂.2.2.1, w₁, w₂]
  · rw [hres₁, hres₂, a₁.status, a₂.status]
  · rw [hres₁, hres₂, a₁.cand, a₂.cand]
  · rw [hlen₁, hlen₂, hres₁, hres₂]
    exact Entropy.requested_congr (a₁.status.trans a₂.status.symm) (a₁.available.trans a₂.available.symm)
  · rw [hres₁, hres₂, a₁.prime, a₂.prime]

/-- A loop state at the point, past the allocation of the search's frame. -/
def AllocSCT (q : GenPoint) (u : State) : Prop := ∃ s, GenCTL q s ∧ u = allocated 48 s

theorem search_run_ct (v : RoundImpl) :
    RelCT isa (Two GenCTL) (searchRun (searchCall v)) (fun _ _ => True) := by
  unfold searchRun
  apply frame_alloc_ct
  have ha : RelCT isa (Two AllocSCT) (.block searchArgs) (Two CallSCT) :=
    two_post (RelCT.taint (A := taint) (genT' 48 []) (fun _ _ ⟨q, ⟨s, hs, e₁⟩, ⟨t, ht, e₂⟩⟩ => by
      subst e₁ e₂; exact alloc_agree (by decide) hs.any ht.any (fun _ h => absurd h List.not_mem_nil))
      (by taint_decide))
      (fun q u ⟨s, ⟨o, st, ha, hl, hw⟩, e⟩ => by
        subst e
        exact WP.mono (search_args_ok hl) fun _ ⟨hr, hm, k⟩ => ⟨o, st, s, ha, hl, hw, hr, hm, k⟩)
  refine (RelCT.seq ha (search_call_ct v)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩⟩

/-! ## The key -/

theorem keyStatus_keyOp (L : Nat) (eB pB qB : List Byte) :
    keyStatus (keyOp L eB pB qB) = keyResultStatus (keyFromPrimes (16 * L) (Spec.Rsa.os2ip eB)
      (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip qB)) := by
  unfold keyOp
  split <;> rename_i h <;> rw [h] <;> rfl

/-- After `q`'s search accepted a prime, at the point: the key's state. -/
def KeyCT (q : GenPoint) (u : State) : Prop :=
  ∃ original st final c pB, AtPoint q original st ∧ Mid q.inputs original final q.used st u ∧
    (rOf q.inputs original q.used st).outcome = .accepted c ∧ 0 < (rOf q.inputs original q.used st).used ∧
    st.phase = .q pB

theorem KeyCT.frame {q : GenPoint} {u : State} (h : KeyCT q u) : AnyFrame q.inputs u :=
  let ⟨o, _, _, _, _, _, hm, _⟩ := h; ⟨o, _, _, hm.frame⟩

/-- The key's status, from the point. -/
theorem KeyCT.status {q : GenPoint} {u : State} (h : KeyCT q u) : keyStatus (keyOf q.inputs u.mem) = q.key := by
  obtain ⟨o, st, final, c, pB, ha, hm, ho, hpos, hph⟩ := h
  have hs4 := hm.slot4
  have hs5 := hm.slot5
  rw [hph] at hs4 hs5
  simp only [outBytes, ho] at hs5
  simp only [keyOf, hs4, hs5, keyStatus_keyOp]
  exact ha.keyStatus hm.frame.used_le (genRand_length hm.frame) ho hpos hph

/-- The key's entry, before the call. -/
def CallKCT (q : GenPoint) (u : State) : Prop :=
  ∃ s, KeyCT q s ∧ KeyRegs q.inputs u ∧
    u.mem = writeFrame s.mem (q.inputs.F - BitVec.ofNat 64 96) (keyValues q.inputs) ∧
    Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (allocated 96 s) u

theorem key_call_ct [Key.KeyProof] : RelCT isa (Two CallKCT) keyCall (fun _ _ => True) := by
  refine RelCT.callEx (k := Key.keyCtr) (Key.KeyProof.correct keyCode_mx) Key.KeyProof.ct
    fun u₁ u₂ ⟨q, h₁, h₂⟩ => ?_
  obtain ⟨s₁, c₁, r₁, m₁, k₁⟩ := h₁
  obtain ⟨s₂, c₂, r₂, m₂, k₂⟩ := h₂
  obtain ⟨o₁, _, _, _, _, _, hm₁, _⟩ := id c₁
  obtain ⟨o₂, _, _, _, _, _, hm₂, _⟩ := id c₂
  have g₁ := hm₁.frame
  have g₂ := hm₂.frame
  have hu₁ : u₁.gpr .rsp = q.inputs.sp - BitVec.ofNat 64 256 := by
    rw [k₁.gpr (by decide), allocated_rsp, g₁.rsp, F_96]
  have hu₂ : u₂.gpr .rsp = q.inputs.sp - BitVec.ofNat 64 256 := by
    rw [k₂.gpr (by decide), allocated_rsp, g₂.rsp, F_96]
  obtain ⟨res₁, e₁⟩ := callK_res g₁ hu₁ r₁ m₁
  obtain ⟨res₂, e₂⟩ := callK_res g₂ hu₂ r₂ m₂
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := callK_args (s := s₁) hu₁ m₁
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩ := callK_args (s := s₂) hu₂ m₂
  obtain ⟨di₁, si₁, dx₁, cx₁, r8₁, r9₁⟩ := r₁
  obtain ⟨di₂, si₂, dx₂, cx₂, r8₂, r9₂⟩ := r₂
  refine ⟨kReads q.inputs, kWrites q.inputs, kReads q.inputs, kWrites q.inputs,
    callK_pre g₁ hu₁ ⟨di₁, si₁, dx₁, cx₁, r8₁, r9₁⟩ m₁, callK_pre g₂ hu₂ ⟨di₂, si₂, dx₂, cx₂, r8₂, r9₂⟩ m₂, ?_,
    key_covers_reads g₁ k₁.2.1 k₁.2.2, key_covers_writes g₁ k₁.2.2,
    key_covers_reads g₂ k₂.2.1 k₂.2.2, key_covers_writes g₂ k₂.2.2, hu₁.trans hu₂.symm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by rw [callK_rsp hu₁, callK_rsp hu₂], fun i hi => ?_, ?_⟩
  · rw [callK_gpr (by decide), callK_gpr (by decide), di₁, di₂]
  · rw [callK_gpr (by decide), callK_gpr (by decide), si₁, si₂]
  · rw [callK_gpr (by decide), callK_gpr (by decide), dx₁, dx₂]
  · rw [callK_gpr (by decide), callK_gpr (by decide), cx₁, cx₂]
  · rw [callK_gpr (by decide), callK_gpr (by decide), r8₁, r8₂]
  · rw [callK_gpr (by decide), callK_gpr (by decide), r9₁, r9₂]
  · match i, hi with
    | 0, _ => rw [b0, d0]
    | 1, _ => rw [b1, d1]
    | 2, _ => rw [b2, d2]
    | 3, _ => rw [b3, d3]
    | 4, _ => rw [b4, d4]
    | 5, _ => rw [b5, d5]
    | 6, _ => rw [b6, d6]
    | 7, _ => rw [b7, d7]
    | 8, _ => rw [b8, d8]
    | 9, _ => rw [b9, d9]
    | 10, _ => rw [b10, d10]
    | 11, _ => rw [b11, d11]
  · unfold Key.keyLeak
    rw [e₁, e₂, res₁, res₂, c₁.status, c₂.status]

/-- At the point, past the allocation of the key's frame. -/
def AllocKCT (q : GenPoint) (u : State) : Prop := ∃ s, KeyCT q s ∧ u = allocated 96 s

theorem key_run_ct [Key.KeyProof] : RelCT isa (Two KeyCT) (keyRun keyCall) (fun _ _ => True) := by
  unfold keyRun
  apply frame_alloc_ct
  have ha : RelCT isa (Two AllocKCT) (.block keyArgs) (Two CallKCT) :=
    two_post (RelCT.taint (A := taint) (genT' 96 []) (fun _ _ ⟨q, ⟨s, hs, e₁⟩, ⟨t, ht, e₂⟩⟩ => by
      subst e₁ e₂; exact alloc_agree (by decide) hs.frame ht.frame (fun _ h => absurd h List.not_mem_nil))
      (by taint_decide))
      (fun q u ⟨s, hs, e⟩ => by
        subst e
        obtain ⟨o, _, _, _, _, _, hm, _⟩ := id hs
        exact WP.mono (key_args_ok hm.frame) fun _ ⟨hr, hmem, k⟩ => ⟨s, hs, hr, hmem, k⟩)
  refine (RelCT.seq ha key_call_ct).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩⟩

end VG.Proof.RsaKeyGen.X86_64.Generate

end

end

/-! # The classification's timing

After the search, each test the controller branches on is of the point:
the search's status and consumption, the generations left, the phase and
the key's status. Every block between them the taint analysis checks from
the frame's public words.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 (RoundImpl)
open VG.Proof.Ffdh.X86_64.Generation (candidate_status_guard second_status_guard)
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

theorem ev_false {c : Cond} {s : State} {b : Prop} [Decidable b] (he : eval c s = some (decide b))
    (hf : isa.eval c s = some false) : ¬b := fun h => by
  have hx : some (decide b) = some false := he.symm.trans hf
  simp [h] at hx

theorem no_pins {α : Type} (Φ : α → State → Prop) : Pins Φ [] := fun _ _ _ _ _ _ h => absurd h List.not_mem_nil

/-- After the search, at the point. -/
def AfterCT (q : GenPoint) (t : State) : Prop :=
  ∃ original st s, AtPoint q original st ∧ GenLive q.inputs original q.used st s ∧
    word s.mem q.inputs.stp 24 = q.req ∧ AfterSearch q.inputs original q.used st s t

/-- After the search and the count of its octets, at the point. -/
def MidCT (q : GenPoint) (u : State) : Prop :=
  ∃ original st, AtPoint q original st ∧
    Mid q.inputs original ((tailOf q.inputs original q.used st).consume q.used []) q.used st u

theorem MidCT.any {q : GenPoint} {u : State} (h : MidCT q u) : AnyFrame q.inputs u :=
  let ⟨o, _, _, hm⟩ := h; ⟨o, _, _, hm.frame⟩

theorem status_cases (r : PrimeSearchResult) : r.status = 0 ∨ r.status = 1 ∨ r.status = 3 := by
  rw [rOf_status]; cases r.outcome <;> simp [Spec.Entropy.Outcome.status]

theorem MidCT.status {q : GenPoint} {u : State} (h : MidCT q u) : q.status = 0 ∨ q.status = 1 ∨ q.status = 3 := by
  obtain ⟨o, st, ha, -⟩ := h
  rw [← ha.status]; exact status_cases _

/-! ## The blocks between the tests -/

theorem frame_ct {Φ : GenPoint → State → Prop} {c : Prog isa} (hΦ : ∀ q s, Φ q s → AnyFrame q.inputs s)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (h : (taint.check (genT []) c hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  frame_taint (fun q => q.inputs) [] hΦ (no_pins Φ) h

/-! ## The head -/

/-- The head's test, at the point. -/
def HeadCT (q : GenPoint) (u : State) : Prop :=
  MidCT q u ∧ u.gpr .rax = BitVec.ofNat 64 q.status ∧ u.gpr .rcx = BitVec.ofNat 64 q.cand ∧
    eval .e u = some (decide (q.status = 0))

theorem head_ct : RelCT isa (Two AfterCT) (.block [.mov32 .rax (.reg .rax), .mov .rcx (.mem (field 2)),
    .mov .rcx (.mem { base := .rcx }), .mov .rdx (.mem (field 8)), .alu .add .rdx (.reg .rcx),
    .store (field 8) .rdx, .alu .test .rax (.reg .rax)]) (Two HeadCT) :=
  two_post (frame_ct (fun _ _ ⟨o, _, _, _, _, _, ha⟩ => ⟨o, _, _, ha.frame⟩) (by taint_decide))
    fun q t ⟨o, st, s, ha, hl, _, haf⟩ => WP.mono (after_head ⟨hl, [], rfl⟩ haf) fun u ⟨he, hax, hcx, hm⟩ =>
      ⟨⟨o, st, ha, hm⟩, by rw [hax, ha.status], by rw [hcx, ha.cand], by rw [he, ha.status]⟩

/-! ## A generation exhausted -/

/-- The generations' test, at the point. -/
def LeftCT (q : GenPoint) (u : State) : Prop :=
  AnyFrame q.inputs u ∧ u.gpr .rax = q.inputs.stp ∧ u.gpr .rcx = BitVec.ofNat 64 q.left ∧
    eval .b u = some (decide (q.left < 2))

theorem exhausted_ct : RelCT isa (Two MidCT) exhaustedGen (fun _ _ => True) := by
  unfold exhaustedGen
  refine RelCT.seq (two_post (Ψ := LeftCT) (frame_ct (fun _ _ h => h.any) (by taint_decide))
    fun q u ⟨o, st, ha, hm⟩ => WP.mono (left_ok hm.frame) fun v ⟨⟨hb, hax, hcx, hmem⟩, k⟩ =>
      ⟨⟨o, _, _, hm.frame.keep hmem k.2.1 k.2.2 (fun r hr => k.gpr (by revert r; decide))⟩, hax,
        by rw [hcx]; exact congrArg _ ha.1,
        by rw [hb]; congr 2; exact propext ⟨fun h => ha.1 ▸ h, fun h => ha.1.symm ▸ h⟩⟩) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm) ?_ ?_
  · exact frame_ct (fun _ _ h => h.1.1) (by taint_decide)
  · exact frame_taint (fun q => q.inputs) [.rax, .rcx] (fun _ _ h => h.1.1)
      (fun _ _ _ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        exacts [h₁.1.2.1.trans h₂.1.2.1.symm, h₁.1.2.2.1.trans h₂.1.2.2.1.symm]) (by taint_decide)

/-! ## After the key -/

/-- After the key, at the point. -/
def AfterKCT (q : GenPoint) (v : State) : Prop :=
  AnyFrame q.inputs v ∧ ((v.gpr .rax).setWidth 32).toNat = q.key ∧ q.key < 3

theorem keyStatus_lt3 (k : Except Failure (List (List Byte)) ⊕ Unit) : keyStatus k < 3 := by
  unfold keyStatus; split <;> decide

/-- The key's first test, at the point. -/
def Key1CT (q : GenPoint) (v : State) : Prop :=
  AnyFrame q.inputs v ∧ v.gpr .rax = BitVec.ofNat 64 q.key ∧ q.key < 3 ∧ eval .e v = some (decide (q.key = 1))

/-- The key's second test, at the point. -/
def Key2CT (q : GenPoint) (v : State) : Prop := AnyFrame q.inputs v ∧ eval .e v = some (decide (q.key = 2))

theorem after_key_ct : RelCT isa (Two AfterKCT) afterKey (fun _ _ => True) := by
  unfold afterKey
  refine RelCT.seq (two_post (Ψ := Key1CT) (frame_ct (fun _ _ h => h.1) (by taint_decide))
    fun q v ⟨⟨o, u, st, g⟩, hs, h3⟩ => WP.mono (candidate_status_guard v) fun w ⟨⟨he, hax, hmem⟩, k⟩ =>
      ⟨⟨o, u, st, g.keep hmem k.2.1 k.2.2 (fun r hr => k.gpr (by revert r; decide))⟩,
        status_of hs hax, h3, by rw [he, hs]⟩) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm) ?_ ?_
  · exact frame_ct (fun _ _ h => h.1.1) (by taint_decide)
  · refine RelCT.seq (two_post (Ψ := Key2CT) (frame_ct (fun _ _ h => h.1.1) (by taint_decide))
      fun q v ⟨⟨⟨o, u, st, g⟩, hax, h3, _⟩, _⟩ => WP.mono (second_status_guard hax (by omega_using [h3]))
        fun w ⟨⟨he, hmem⟩, k⟩ =>
        ⟨⟨o, u, st, g.keep hmem k.2.1 k.2.2 (fun r hr => k.gpr (by revert r; decide))⟩, he⟩) ?_
    refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
    · exact frame_ct (fun _ _ h => h.1.1) (by taint_decide)
    · exact frame_ct (fun _ _ h => h.1.1) (by taint_decide)

/-! ## A prime accepted -/

/-- The phase's test, at the point, after an accepted prime. -/
def PhCT (q : GenPoint) (u : State) : Prop :=
  MidCT q u ∧ q.status = 1 ∧ q.cand ≠ 0 ∧ eval .e u = some (decide (q.ph = 0))

theorem accepted_ct [Key.KeyProof] : RelCT isa (Two fun q u => MidCT q u ∧ q.status = 1 ∧ q.cand ≠ 0) (accepted keyCall)
    (fun _ _ => True) := by
  unfold accepted
  refine RelCT.seq (two_post (Ψ := PhCT) (frame_ct (fun _ _ h => h.1.any) (by taint_decide))
    fun q u ⟨⟨o, st, ha, hm⟩, h1, h0⟩ => WP.mono (phase_ok hm.frame) fun v ⟨⟨he, hmem⟩, k⟩ =>
      ⟨⟨o, st, ha, hm.keep hmem k.2.1 k.2.2 (fun r hr => k.gpr (by revert r; decide))⟩, h1, h0,
        by rw [he]; show some (decide (phaseWord st.phase = 0)) = _; rw [ha.2.1]⟩) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm) ?_ ?_
  · exact frame_ct (fun _ _ h => h.1.1.any) (by taint_decide)
  · -- `q`: the key.
    have hk : ∀ q u, (PhCT q u ∧ eval .e u = some false) → KeyCT q u := by
      rintro q u ⟨⟨⟨o, st, ha, hm⟩, h1, h0, he⟩, hf⟩
      have hph : q.ph ≠ 0 := ev_false he hf
      obtain ⟨left, phase, remaining⟩ := st
      cases phase with
      | p => exact absurd (ha.2.1.symm.trans rfl) hph
      | q pB =>
        cases ho : (rOf q.inputs o q.used ⟨left, .q pB, remaining⟩).outcome with
        | entropy k a => rw [← ha.status, rOf_status, ho] at h1; cases h1
        | exhausted => rw [← ha.status, rOf_status, ho] at h1; cases h1
        | accepted c => exact ⟨o, _, _, c, pB, ha, hm, ho, by rw [ha.cand]; omega_using [h0], rfl⟩
    refine RelCT.seq (two_post (Ψ := AfterKCT) ((key_run_ct).mono (fun _ _ ⟨q, h₁, h₂⟩ =>
      ⟨q, hk q _ h₁, hk q _ h₂⟩) fun _ _ h => h) fun q u h => ?_) after_key_ct
    have hkc := hk q u h
    obtain ⟨o, st, final, c, pB, ha, hm, ho, hpos, hph⟩ := hkc
    refine WP.mono (key_run hm.frame) fun v hak => ⟨⟨o, _, _, hak.frame⟩, ?_, ?_⟩
    · rw [hak.status, (show KeyCT q u from ⟨o, st, final, c, pB, ha, hm, ho, hpos, hph⟩).status]
    · rw [← (show KeyCT q u from ⟨o, st, final, c, pB, ha, hm, ho, hpos, hph⟩).status]
      exact keyStatus_lt3 _

/-! ## The classification -/

/-- The test of the search's status 3, at the point. -/
def Mid3CT (q : GenPoint) (u : State) : Prop :=
  MidCT q u ∧ u.gpr .rcx = BitVec.ofNat 64 q.cand ∧ q.status ≠ 0 ∧ eval .e u = some (decide (q.status = 3))

/-- The test of the octets the search consumed, at the point. -/
def Mid4CT (q : GenPoint) (u : State) : Prop :=
  MidCT q u ∧ q.status = 1 ∧ eval .e u = some (decide (q.cand = 0))

theorem classify_ct [Key.KeyProof] : RelCT isa (Two AfterCT) (classify keyCall) (fun _ _ => True) := by
  unfold classify
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine RelCT.seq head_ct ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm) ?_ ?_
  · exact frame_ct (fun _ _ h => h.1.1.any) (by taint_decide)
  · refine RelCT.seq (two_post (Ψ := Mid3CT) (frame_ct (fun _ _ h => h.1.1.any) (by taint_decide))
      fun q u ⟨⟨⟨o, st, ha, hm⟩, hax, hcx, he⟩, hf⟩ => ?_) ?_
    · have hs := MidCT.status ⟨o, st, ha, hm⟩
      have h0 : q.status ≠ 0 := ev_false he hf
      refine WP.mono (cmp3_guard hax (by omega_using [hs])) fun v ⟨⟨he3, hmem⟩, k⟩ =>
        ⟨⟨o, st, ha, hm.keep hmem k.2.1 k.2.2 (fun r hr => k.gpr (by revert r; decide))⟩,
          by rw [k.gpr (by decide)]; exact hcx, h0, he3⟩
    refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm) ?_ ?_
    · exact (exhausted_ct.mono (fun _ _ ⟨q, h₁, h₂⟩ => ⟨q, h₁.1.1, h₂.1.1⟩) fun _ _ h => h)
    · refine RelCT.seq (two_post (Ψ := Mid4CT) (frame_ct (fun _ _ h => h.1.1.any) (by taint_decide))
        fun q u ⟨⟨hm, hcx, h0, he⟩, hf⟩ => ?_) ?_
      · have hs := MidCT.status hm
        have h3 : q.status ≠ 3 := ev_false he hf
        obtain ⟨o, st, ha, hm'⟩ := hm
        have hu64 : q.cand < 2 ^ 64 := by
          have := hm'.frame.used_le; have := hm'.frame.input.cfacts.rand64; rw [← ha.cand]; omega_arith
        refine WP.mono (test_guard hcx hu64) fun v ⟨⟨he4, hmem⟩, k⟩ =>
          ⟨⟨o, st, ha, hm'.keep hmem k.2.1 k.2.2 (fun r hr => k.gpr (by revert r; decide))⟩, by omega_using [h0, hs, h3], he4⟩
      refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.trans h₂.2.2.symm) ?_ ?_
      · exact frame_ct (fun _ _ h => h.1.1.any) (by taint_decide)
      · refine (accepted_ct.mono (fun _ _ ⟨q, h₁, h₂⟩ => ⟨q, ?_, ?_⟩) fun _ _ h => h)
        · obtain ⟨⟨hm, h1, he⟩, hf⟩ := h₁
          exact ⟨hm, h1, ev_false he hf⟩
        · obtain ⟨⟨hm, h1, he⟩, hf⟩ := h₂
          exact ⟨hm, h1, ev_false he hf⟩

end VG.Proof.RsaKeyGen.X86_64.Generate

end

end

/-! ### `RsaKeyGen.X86_64.Generate.Correct`, which this module and modules that import it used -/

section

/-! # RSA key generation's controller on x86-64: correctness

The entry, the key's buffer cleared but `p`, the loop and the return: the
contract's postcondition, the callee-saved registers and the regions kept;
and with the stack the code uses and its return address, `genContract`'s
correctness.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 (RoundImpl)
open VG.Proof.Ffdh.X86_64.Generation (allocated allocated_rsp allocated_reg allocated_mem freed freed_rsp
  freed_reg freed_mem frame_alloc)
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

/-- The controller, with the prime search and the key it calls. -/
abbrev genCode (v : RoundImpl) : Prog isa := code (searchCall v) keyCall

/-- The return: the octets consumed to `used`, the status, and r12. -/
theorem finish_ok {p : GenPublic} {original s : State} {final : KeySearchResult}
    (h : GenDone p original final s) :
    WP isa (.block finish) s fun t =>
      (t.gpr .rax = BitVec.ofNat 64 final.keyStatus ∧ t.gpr .r12 = original.gpr .r12 ∧
        t.mem = s.mem.writeW p.up (BitVec.ofNat 64 final.used)) ∧ Keep [.rax, .rcx, .r12] s t := by
  obtain ⟨g, hst, -, -⟩ := h
  have scr := g.scr
  have hu := g.usedScr
  have hl2 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 16) 8 := scr.ld (d := 16) (by decide)
  have hl8 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 64) 8 := scr.ld (d := 64) (by decide)
  have hl9 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 72) 8 := scr.ld (d := 72) (by decide)
  have hl10 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 80) 8 := scr.ld (d := 80) (by decide)
  have hsu : InRegions s.wr p.up 8 := by simpa only [off, BitVec.add_zero] using hu.st (d := 0) (by decide)
  have h2 := g.header (j := 2) (v := p.up) (by simp [GenPublic.headers])
  have h8 := g.header (j := 8) (v := BitVec.ofNat 64 final.used) (by simp [GenPublic.headers])
  simp only [Nat.reduceMul] at h2 h8
  have hnF : p.F.toNat + 160 ≤ 2 ^ 64 := scr.nowrap
  have hkeep (v : BitVec 64) (d : Nat) (hd : d + 8 ≤ 160) :
      (s.mem.writeW p.up v).readW (p.F + BitVec.ofNat 64 d) 64 = s.mem.readW (p.F + BitVec.ofNat 64 d) 64 :=
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self (rU p)) v (Region.contains_self _ _)).readW
      (r := p.frame) (Offset.contains_base _ hd (by omega_using [hd])) (fun q hq => by
        obtain rfl := List.mem_singleton.mp hq
        exact g.input.frame_disjoint_writes (r := inUsed original) (by simp [inWrites]) |>.sub_right
          (by rw [g.used_region]; exact fun _ h => h)) (by decide)
  have hk9 : ∀ v : BitVec 64, (s.mem.writeW p.up v).readW (p.F + BitVec.ofNat 64 72) 64 = original.gpr .r12 :=
    fun v => (hkeep v 72 (by decide)).trans g.savedR12
  have hk10 : ∀ v : BitVec 64, (s.mem.writeW p.up v).readW (p.F + BitVec.ofNat 64 80) 64 =
      BitVec.ofNat 64 final.keyStatus := fun v => (hkeep v 80 (by decide)).trans hst
  refine WP.keep [.rax, .rcx, .r12] ?_ rfl
  unfold finish
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    g.r12, hl2, hl8, hl9, hl10, hsu, h2, h8, hk9, hk10]

theorem phase_word_if (ph : KeyPhase) :
    BitVec.ofNat 64 (phaseWord ph) = BitVec.ofNat 64 (if ph = .p then 0 else 1) := by
  cases ph <;> rfl

/-- What the controller returns, from what the loop leaves. -/
theorem done_post {p : GenPublic} {s d t : State} (hp : GenInput p s)
    (h : GenDone p s (genResult s) d)
    (hax : t.gpr .rax = BitVec.ofNat 64 (genResult s).keyStatus)
    (hm : t.mem = d.mem.writeW p.up (BitVec.ofNat 64 (genResult s).used)) : genPost s t := by
  obtain ⟨g, -, hkey, req, hreq, hr⟩ := h
  have hf := hp.cfacts
  have hst := g.state
  have hkp : s.gpr .rdi = p.kp := by rw [← hp.2]; rfl
  have hup : s.gpr .rdx = p.up := by rw [← hp.2]; rfl
  have hstp : stackArg s 1 = p.stp := by rw [← hp.2]; rfl
  have hL : genLen s = p.L := by rw [← hp.2]; rfl
  have heB : genE s = p.eB := by rw [← hp.2]; rfl
  -- The store to `used` is apart from the key's buffer and the state.
  have hfr : Frame [rU p] d.mem t.mem := by
    rw [hm]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hword (j : Nat) (hj : j < 7) : word t.mem p.stp (8 * j) = word d.mem p.stp (8 * j) :=
    hfr.readW (r := cS p) (Offset.contains_base _ (by omega_using [hj]) (by have := hf.nT; omega_using [hj]))
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hf.uT.symm) (by decide)
  have hbytes {R : Region} (hR : Region.Sub R (cK p) ∨ Region.Sub R (cS p)) (hn : R.len ≤ 2 ^ 64) :
      Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt d.mem R.base R.len := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    refine hfr.bytes (fun q hq => ?_) hn (List.mem_range.mp hi)
    obtain rfl := List.mem_singleton.mp hq
    rcases hR with hR | hR
    exacts [(hf.kU.sub_left hR), (hf.uT.symm.sub_left hR)]
  refine ⟨?_, ?_, ?_, req, ?_, ?_, ?_⟩
  · have := keyStatus_lt (genResult s)
    rw [hax, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [this]), Nat.mod_eq_of_lt (by omega_using [this])]
  · rw [hkp, hL, ← hkey]
    exact hbytes (R := ⟨p.kp, 9 * p.L⟩) (.inl fun _ h => h) (by show 9 * p.L ≤ 2 ^ 64; have := hf.nK; omega_using [this])
  · rw [hup]
    show [t.mem.readW (p.up + BitVec.ofNat 64 (8 * 0)) 64] = _
    rw [Nat.mul_zero, BitVec.add_zero, hm, Mem.readW_writeW_self64]
  · rw [hstp, hL]
    show [word t.mem p.stp (8 * 0), word t.mem p.stp (8 * 1), word t.mem p.stp (8 * 2), word t.mem p.stp (8 * 3),
      word t.mem p.stp (8 * 4), word t.mem p.stp (8 * 5)] = _
    rw [hword 0 (by decide), hword 1 (by decide), hword 2 (by decide), hword 3 (by decide), hword 4 (by decide),
      hword 5 (by decide)]
    simp only [Nat.reduceMul]
    rw [show word d.mem p.stp 0 = _ from hst.remaining, show word d.mem p.stp 8 = _ from hst.len,
      show word d.mem p.stp 16 = _ from hst.cap, show word d.mem p.stp 24 = _ from hreq,
      show word d.mem p.stp 32 = _ from hst.phase, show word d.mem p.stp 40 = _ from hst.left, phase_word_if]
  · rw [hstp, heB]
    have := hbytes (R := ⟨p.stp + BitVec.ofNat 64 48, 8⟩) (.inr rE_sub) (by show 8 ≤ 2 ^ 64; decide)
    exact this.trans hst.e
  · rw [hL]; exact hr

/-- `genPost` holds whatever the bytes of a frame on the controller's stack
hold once released: the key, the used count and the state lie apart from it. -/
theorem genPost_lost {p : GenPublic} {s t t' : State} (hp : GenInput p s) (h : genPost s t)
    (hr : t'.gpr .rax = t.gpr .rax) {R : Region} (fm : Frame [R] t.mem t'.mem) (hR : R.Sub (cStack p)) :
    genPost s t' := by
  have hf := hp.cfacts
  have hstk := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hstk
  obtain ⟨sK, sU, -, sT, -⟩ := hstk
  have hd : ∀ {B : Region}, B.Disjoint (cStack p) → B.Disjoint R := fun hB x h₁ h₂ => hB x h₁ (hR x h₂)
  have hb : ∀ {B : Region}, B.Disjoint (cStack p) →
      Spec.Rsa.bytesAt t'.mem B.base B.len = Spec.Rsa.bytesAt t.mem B.base B.len := fun hB =>
    List.map_congr_left fun i hi => lost_byte fm (hd hB) (List.mem_range.mp hi)
  have hkp : s.gpr .rdi = p.kp := by rw [← hp.2]; rfl
  have hup : s.gpr .rdx = p.up := by rw [← hp.2]; rfl
  have hstp : stackArg s 1 = p.stp := by rw [← hp.2]; rfl
  have hL : genLen s = p.L := by rw [← hp.2]; rfl
  obtain ⟨a, b, c, req, d, e, f⟩ := h
  refine ⟨by rw [hr]; exact a, ?_, ?_, req, ?_, ?_, f⟩
  · rw [hkp, hL] at b ⊢
    exact (hb (B := cK p) sK).trans b
  · rw [hup] at c ⊢
    rw [Proof.Rsa.wordsAt_frame (p := p.up) (n := 1) fm (by decide) fun q hq => by
      obtain rfl := List.mem_singleton.mp hq; exact hd sU]
    exact c
  · rw [hstp] at d ⊢
    rw [Proof.Rsa.wordsAt_frame (p := p.stp) (n := 6) fm (by decide) fun q hq => by
      obtain rfl := List.mem_singleton.mp hq; exact hd (sT.sub_left (Region.sub_prefix (by decide)))]
    exact d
  · rw [hstp] at e ⊢
    exact (hb (B := rE p) (sT.sub_left rE_sub)).trans e

theorem gen_correct_ok [Key.KeyProof] (v : RoundImpl) {s : State} (h : genPre s) :
    WP isa (genCode v) s fun t => genPost s t ∧
      (∀ reg ∈ calleeSaved, t.gpr reg = s.gpr reg) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hp : GenInput (genOfState s) s := ⟨h, rfl⟩
  have hroom := hp.room
  have hf := hp.cfacts
  unfold genCode code
  apply frame_alloc (by decide) (by decide) (by decide) (by
    rw [← hp.sp_eq]; have : 552 ≤ (genOfState s).sp.toNat := hroom; show 160 ≤ _; omega_using [this])
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq (WP.mono (gen_start hp) fun u ⟨hu, hfu⟩ => ?_)
  refine WP.seq (WP.mono (clearAround_ok hu ?_) fun w ⟨hw, _⟩ => ?_)
  · intro pB hpB
    simp only [genProgress, keyProgressAt] at hpB
    split at hpB
    · cases hpB
    · cases hpB
      obtain ⟨hL1, -, -⟩ := hf.len
      exact bytes_kept hfu (hu.frame_key.sub_right (slot_sub _ (by omega_using []))) (by
        show (genOfState s).L ≤ 2 ^ 64; have := hf.nK; omega_using [this])
  have hinv : GenInv (genOfState s) s (genResult s) (genMeasure (genOfState s) 0 (genProgress s)) w :=
    ⟨0, genProgress s, rfl, hw, [], by rw [consume_zero]; rfl⟩
  refine WP.seq (WP.mono (gen_loop v hinv) fun d hd => ?_)
  refine WP.mono (finish_ok hd) fun x ⟨⟨hax, hr12, hmx⟩, k⟩ => ?_
  have g := hd.1
  have hxs : x.gpr .rsp = (genOfState s).F := by rw [k.gpr (by decide)]; exact g.rsp
  have hR : Region.Sub ⟨s.gpr .rsp - BitVec.ofNat 64 160, 160⟩ (cStack (genOfState s)) := by
    rw [← hp.sp_eq]; exact Offset.sub_below _ (by decide) (by decide)
  refine ⟨by rw [hxs]; exact (alloc_rsp hp).symm, by rw [k.2.2, g.wr]; exact (alloc_wr hp).symm,
    fun m uu fm => ⟨genPost_lost hp (t := freed 160 x)
      (done_post hp hd (by rw [freed_reg _ _ _ (by decide)]; exact hax) (by rw [freed_mem]; exact hmx))
      (freed_reg 160 x .rax (by decide)) fm hR,
    fun r hr => ?_, ?_, ?_⟩⟩
  · show (freed 160 x).gpr r = s.gpr r
    have hnot : r ≠ .r12 → r ∉ [Reg.rax, .rcx, .r12] := by revert r; decide
    by_cases hsp : r = .rsp
    · subst hsp
      rw [freed_rsp, hxs, ← hp.sp_eq]
      exact BitVec.sub_add_cancel _ _
    · rw [freed_reg _ _ _ hsp]
      by_cases h12 : r = .r12
      · subst h12; exact hr12
      · rw [k.gpr (hnot h12)]
        exact g.saved r hr h12 hsp
  · show x.rd = s.rd
    rw [k.2.1, g.rd]
  · show x.wr.tail = s.wr
    rw [k.2.2, g.wr]; rfl

/-! ## The code -/

private theorem code_all (q : Instr → Bool) (a b : Prog isa)
    (hp : (code (.block []) (.block [])).all q = true) (ha : a.all q = true) (hb : b.all q = true) :
    (code a b).all q = true := by
  unfold code iteration searchRun classify accepted keyRun at hp ⊢
  simp only [VG.Impl.Bignum.X86_64.seqs, Code.all, List.all_nil, ha, hb, Bool.and_true] at hp ⊢
  exact hp

private theorem code_instrs (q : Instr → Bool) (a b : Prog isa)
    (hp : (code (.block []) (.block [])).allInstrs q = true) (ha : a.allInstrs q = true)
    (hb : b.allInstrs q = true) : (code a b).allInstrs q = true := by
  unfold code iteration searchRun classify accepted keyRun at hp ⊢
  simp only [VG.Impl.Bignum.X86_64.seqs, Code.allInstrs, ha, hb, Bool.and_true] at hp ⊢
  exact hp

private theorem code_ctlC (a b : Prog isa) (hp : ctlC (code (.block []) (.block [])) = true)
    (ha : ctlC a = true) (hb : ctlC b = true) : ctlC (code a b) = true := by
  unfold code iteration searchRun classify accepted keyRun at hp ⊢
  simp only [VG.Impl.Bignum.X86_64.seqs, ctlC, ha, hb, Bool.and_true] at hp ⊢
  exact hp

theorem keyCode_sp : VG.Impl.RsaKeyGen.X86_64.Key.code.all (fun i => !isa.writesSp i) = true := by
  decide +kernel

theorem genCode_sp (v : RoundImpl) : (genCode v).all (fun i => !isa.writesSp i) = true :=
  code_all _ _ _ (by decide +kernel) (Search.searchCode_sp v) keyCode_sp

/-- Key generation loads MXCSR only where the round restores it. -/
theorem genCode_ctlC (v : RoundImpl) : ctlC (genCode v) = true :=
  code_ctlC _ _ (by decide +kernel) (ctlOk_of_ctlC (Search.searchCode_ctlC v)) (ctlOk_of_noLoad keyCode_mx)

theorem keyCode_x86_64Depth : VG.Impl.RsaKeyGen.X86_64.Key.code.x86_64Depth = 0 :=
  x86_64Depth_zero keyCode_noSp keyCode_depth

theorem genCode_depth (v : RoundImpl) : (genCode v).x86_64Depth ≤ stackUse := by
  have hs := Search.searchCode_depth v
  have hk := keyCode_x86_64Depth
  have hc : clearAround.x86_64Depth = 0 := rfl
  have he : exhaustedGen.x86_64Depth = 0 := rfl
  have hf : (fail 3).x86_64Depth = 0 := rfl
  have ha : afterKey.x86_64Depth = 0 := rfl
  unfold genCode code iteration searchRun classify accepted keyRun searchCall keyCall
  simp only [VG.Impl.Bignum.X86_64.seqs, Code.x86_64Depth, Instr.frameBytes, frameBytes, hk, hc, he, hf, ha,
    Nat.zero_max, Nat.max_zero, Nat.zero_add]
  have hs' : (Search.searchCode v).x86_64Depth ≤ 336 := hs
  exact Nat.add_le_of_le_sub (by decide) (Nat.max_le.mpr ⟨by show _ ≤ 392; omega_using [hs'], by decide⟩)

theorem gen_return_address (v : RoundImpl) {s t : State} {tr : List Leak}
    (h : genPre s) (he : Exec isa (genCode v) s tr t) :
    t.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  obtain ⟨-, -, -, hwr, -, -, -, hstk, -⟩ := h
  have hd : (genCode v).x86_64Depth ≤ 552 := genCode_depth v
  have hf := Exec.stackFrame (SpSafe.of_all (genCode_sp v)) he (by omega_using [hd])
  refine hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · rw [hwr] at hr
    exact (hstk r (List.mem_append_left _ hr)).1
  · obtain rfl := List.mem_singleton.mp hr
    exact Offset.base_disjoint_below _ (by omega_using [hd])

theorem gen_correct [Key.KeyProof] (v : RoundImpl) (s : State) (h : genContract.pre s) :
    ∃ tr t, Exec isa (genCode v) s tr t ∧ abiPreserved s t ∧ genContract.post s t := by
  obtain ⟨tr, t, he, hp, hg, _, _⟩ := gen_correct_ok v h
  exact ⟨tr, t, he, abiPreserved_of_ctl (ctlOk_of_ctlC (genCode_ctlC v)) he ⟨hg, gen_return_address v h he⟩, hp⟩

end VG.Proof.RsaKeyGen.X86_64.Generate

end

end

-- separate module: its proofs build in parallel with the correctness ones, `Correct`

/-! # The controller's timing depends on its public data and its trace

Two runs that `genContract.pub` relates start at the same point
(`initialPoint`): an iteration takes both to the next point or ends both
(`gen_ct_step`), and every block, call and test between is of the point.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 (RoundImpl)
open VG.Proof.Ffdh.X86_64.Generation (allocated allocated_rsp allocated_reg allocated_mem frame_alloc_ct)
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

/-! ## An iteration -/

theorem search_run_post (v : RoundImpl) :
    RelCT isa (Two GenCTL) (searchRun (searchCall v)) (Two AfterCT) :=
  two_post (search_run_ct v) fun _ s ⟨o, st, ha, hl, hw⟩ =>
    WP.mono (search_run v hl) fun _ h => ⟨o, st, s, ha, hl, hw, h⟩

theorem classify_any [Key.KeyProof] (q : GenPoint) (t : State) (h : AfterCT q t) :
    WP isa (classify keyCall) t (AnyFrame q.inputs) := by
  obtain ⟨o, st, s, -, hl, -, ha⟩ := h
  refine WP.mono (classify_ok ⟨hl, [], rfl⟩ ha) fun u hc => ?_
  rcases hc with ⟨-, -, -, ⟨st', -, hl', -⟩, -⟩ | ⟨-, hd⟩
  · exact ⟨o, _, st', hl'.toGenFrame⟩
  · exact ⟨o, _, _, hd.1⟩

theorem iteration_ct [Key.KeyProof] (v : RoundImpl) :
    RelCT isa (Two GenCTL) (iteration (searchCall v) keyCall) (fun _ _ => True) := by
  unfold iteration
  simp only [VG.Impl.Bignum.X86_64.seqs]
  exact RelCT.seq (search_run_post v) (RelCT.seq (two_post classify_ct classify_any)
    (frame_ct (fun _ _ h => h) (by taint_decide)))

/-! ## The loop -/

/-- What each step that goes on lowers. -/
def GenPoint.measure (q : GenPoint) : Nat := (q.inputs.randLen - q.used) * 2 ^ 64 + q.left

theorem next_measure {q : GenPoint} {t : State} (hc : q.continues) (h : GenCTL q.next t) :
    q.next.measure < q.measure := by
  obtain ⟨o, st, ha, hl, -⟩ := h
  have hle := hl.used_le
  have hlt := hl.state.left_lt
  rw [ha.1] at hlt
  unfold GenPoint.measure
  simp only [GenPoint.next] at hle hlt ⊢
  rcases hc with ⟨h3, hl2⟩ | ⟨h1, hc0, -⟩
  · simp only [h3, ↓reduceIte] at hlt ⊢
    have hmul : (q.inputs.randLen - (q.used + q.cand)) * 2 ^ 64 ≤ (q.inputs.randLen - q.used) * 2 ^ 64 :=
      Nat.mul_le_mul_right _ (by omega_using [])
    omega_using [hl2]
  · have h3 : ¬q.status = 3 := by omega_using [h1]
    simp only [h3, ↓reduceIte] at hlt ⊢
    have hmul : (q.inputs.randLen - (q.used + q.cand) + 1) * 2 ^ 64 ≤ (q.inputs.randLen - q.used) * 2 ^ 64 :=
      Nat.mul_le_mul_right _ (by omega_using [hle, hc0])
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega_using [hle, hc0]

private def LoopPair (n : Nat) (s t : State) : Prop := ∃ q : GenPoint, n = q.measure ∧ GenCTL q s ∧ GenCTL q t

private theorem iteration_pair [Key.KeyProof] (v : RoundImpl) (n : Nat) :
    RelCT isa (LoopPair n) (iteration (searchCall v) keyCall) fun s t =>
      eval .e s = eval .e t ∧ (eval .e s = some false → True) ∧
      (eval .e s = some true → ∃ m < n, LoopPair m s t) := by
  have hw (q : GenPoint) (s : State) (h : n = q.measure ∧ GenCTL q s) :
      WP isa (iteration (searchCall v) keyCall) s fun t => n = q.measure ∧ GenCTStep q t :=
    WP.mono (gen_ct_step v q s h.2) fun _ ht => ⟨h.1, ht⟩
  have hc := two_post ((iteration_ct v).mono (fun _ _ ⟨q, h₁, h₂⟩ => ⟨q, h₁.2, h₂.2⟩) (fun _ _ h => h)) hw
  refine hc.mono (fun _ _ ⟨q, hn, h₁, h₂⟩ => ⟨q, ⟨hn, h₁⟩, hn, h₂⟩) ?_
  rintro s t ⟨q, ⟨hn, h₁⟩, _, h₂⟩
  rcases h₁ with ⟨hb, e₁, c₁⟩ | ⟨hb, e₁⟩ <;> rcases h₂ with ⟨hb', e₂, c₂⟩ | ⟨hb', e₂⟩
  · exact ⟨e₁.trans e₂.symm, fun _ => trivial, fun _ => ⟨_, by rw [hn]; exact next_measure hb c₁, q.next, rfl,
      c₁, c₂⟩⟩
  · exact absurd hb hb'
  · exact absurd hb' hb
  · exact ⟨e₁.trans e₂.symm, fun _ => trivial, fun h => by rw [e₁] at h; cases h⟩

theorem loop_ct [Key.KeyProof] (v : RoundImpl) :
    RelCT isa (Two GenCTL) (.loop (iteration (searchCall v) keyCall) .e) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration (searchCall v) keyCall) (c := .e)
    (Q := fun _ _ => True) LoopPair (iteration_pair v) q.measure _ _ _ _ _ _ ⟨q, rfl, hs, ht⟩ he₁ he₂

/-! ## Entry and return -/

/-- The point a run starts at. -/
def initialPoint (s : State) : GenPoint :=
  ⟨genOfState s, 0, (genProgress s).left, phaseWord (genProgress s).phase, (genProgress s).remaining,
    word s.mem (stackArg s 1) 24, (genResult s).trace⟩

/-- A run's entry at a point. -/
def GenStart (q : GenPoint) (s : State) : Prop := genPre s ∧ initialPoint s = q

/-- A run's entry, past the frame's allocation. -/
def AllocStart (q : GenPoint) (u : State) : Prop := ∃ s, GenStart q s ∧ u = allocated 160 s

/-- The registers past the frame's first words. -/
def EntryPins (q : GenPoint) (t : State) : Prop :=
  t.gpr .rax = q.inputs.stp ∧ t.gpr .r12 = q.inputs.F ∧ t.gpr .rsp = q.inputs.F

theorem alloc_start_pins : Pins AllocStart [.rsp] := by
  rintro q _ _ ⟨s, ⟨h₁, e₁⟩, rfl⟩ ⟨t, ⟨h₂, e₂⟩, rfl⟩ r hr
  simp only [List.mem_singleton] at hr
  subst r
  rw [alloc_rsp (p := q.inputs) ⟨h₁, by rw [← e₁]; rfl⟩, alloc_rsp (p := q.inputs) ⟨h₂, by rw [← e₂]; rfl⟩]

theorem entry_pins (q : GenPoint) (u : State) (h : AllocStart q u) : WP isa (.block entryHead) u (EntryPins q) := by
  obtain ⟨s, ⟨hp, e⟩, rfl⟩ := h
  have hi : GenInput q.inputs s := ⟨hp, by rw [← e]; rfl⟩
  refine WP.mono (entry_head_ok hi) fun t ⟨hr, ha, _, k⟩ => ⟨?_, hr, ?_⟩
  · rw [ha, ← hi.2]; rfl
  · rw [k.gpr (by decide), alloc_rsp hi]

theorem entry_ct : RelCT isa (Two AllocStart) (.block (entryHead ++ entryWords)) (fun _ _ => True) :=
  RelCT.block_append (RelCT.seq (two_piece (Ψ := EntryPins) [.rsp] alloc_start_pins (by taint_decide) entry_pins)
    (two_taint [.rax, .r12, .rsp] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [h₁.1.trans h₂.1.symm, h₁.2.1.trans h₂.2.1.symm, h₁.2.2.trans h₂.2.2.symm]) (by taint_decide)))

/-- Past the entry, at the point. -/
def StartCT (q : GenPoint) (t : State) : Prop :=
  ∃ s, GenStart q s ∧ GenFrame q.inputs s 0 (genProgress s) t ∧ Frame [q.inputs.frame] s.mem t.mem

theorem entry_post (q : GenPoint) (u : State) (h : AllocStart q u) :
    WP isa (.block (entryHead ++ entryWords)) u (StartCT q) := by
  obtain ⟨s, ⟨hp, e⟩, rfl⟩ := h
  have hi : GenInput q.inputs s := ⟨hp, by rw [← e]; rfl⟩
  exact WP.mono (gen_start hi) fun t ⟨hg, hf⟩ => ⟨s, ⟨hp, e⟩, hg, hf⟩

theorem start_point (q : GenPoint) (t : State) (h : StartCT q t) : WP isa clearAround t (GenCTL q) := by
  obtain ⟨s, ⟨hp, e⟩, hg, hfr⟩ := h
  subst e
  have hf := hg.input.cfacts
  obtain ⟨hL1, -, -⟩ := hf.len
  refine WP.mono (clearAround_ok hg ?_) fun w ⟨hw, hfw⟩ => ⟨s, genProgress s, ⟨rfl, rfl, rfl, rfl⟩, hw, ?_⟩
  · intro pB hpB
    simp only [genProgress, keyProgressAt] at hpB
    split at hpB
    · cases hpB
    · cases hpB
      exact bytes_kept hfr (hg.frame_key.sub_right (slot_sub _ (by omega_using []))) (by
        show (initialPoint s).inputs.L ≤ 2 ^ 64; have := hf.nK; omega_using [this])
  · -- The state's request word, kept through the entry and the clearing.
    have hd : ∀ r ∈ [(⟨(initialPoint s).inputs.kp, 9 * (initialPoint s).inputs.L⟩ : Region),
        (initialPoint s).inputs.frame], (cS (initialPoint s).inputs).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hf.kT.symm
      · exact hg.state_frame.symm
    have h1 := hfw.readW (r := cS (initialPoint s).inputs) (a := (initialPoint s).inputs.stp + BitVec.ofNat 64 24)
      (w := 64) (Offset.contains_base _ (d := 24) (n := 8) (k := 56) (by decide) (by have := hf.nT; omega_using [])) hd
      (by decide)
    have h2 := hfr.readW (r := cS (initialPoint s).inputs) (a := (initialPoint s).inputs.stp + BitVec.ofNat 64 24)
      (w := 64) (Offset.contains_base _ (d := 24) (n := 8) (k := 56) (by decide) (by have := hf.nT; omega_using []))
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hg.state_frame.symm) (by decide)
    exact h1.trans h2

theorem clear_around_ct : RelCT isa (Two StartCT) clearAround (fun _ _ => True) :=
  frame_ct (fun _ _ ⟨s, _, hg, _⟩ => ⟨s, _, _, hg⟩) (by taint_decide)

/-- A loop's end. -/
def DoneCT (q : GenPoint) (t : State) : Prop := ∃ original final, GenDone q.inputs original final t

theorem loop_done [Key.KeyProof] (v : RoundImpl) (q : GenPoint) (s : State) (h : GenCTL q s) :
    WP isa (.loop (iteration (searchCall v) keyCall) .e) s (DoneCT q) := by
  obtain ⟨o, st, -, hl, -⟩ := h
  exact WP.mono (gen_loop v (n := genMeasure q.inputs q.used st)
    (final := (tailOf q.inputs o q.used st).consume q.used []) ⟨q.used, st, rfl, hl, [], rfl⟩)
    fun _ ht => ⟨o, _, ht⟩

theorem finish_ct : RelCT isa (Two DoneCT) (.block finish) (fun _ _ => True) :=
  frame_ct (fun _ _ ⟨o, _, hd⟩ => ⟨o, _, _, hd.1⟩) (by taint_decide)

/-! ## The whole controller -/

theorem gen_code_ct [Key.KeyProof] (v : RoundImpl) : RelCT isa (Two GenStart) (genCode v) (fun _ _ => True) := by
  unfold genCode code
  apply frame_alloc_ct
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine (RelCT.seq (two_post entry_ct entry_post)
    (RelCT.seq (two_post clear_around_ct start_point)
      (RelCT.seq (two_post (loop_ct v) (loop_done v)) finish_ct))).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩⟩

theorem initial_point_eq {s t : State} (hp : genPub s t) : initialPoint s = initialPoint t := by
  obtain ⟨hsp, hdi, hsi, hdx, hcx, h8, h9, ha, hw, -, -, -, htr⟩ := hp
  have hj : ∀ j < 7, s.mem.readW (stackArg s 1 + BitVec.ofNat 64 (8 * j)) 64 =
      t.mem.readW (stackArg t 1 + BitVec.ofNat 64 (8 * j)) 64 := fun j hj' => by
    have := congrArg (fun l => l[j]?) hw
    simpa [Spec.Rsa.wordsAt, List.getElem?_map, hj'] using this
  have w0 := hj 0 (by decide)
  have w1 := hj 1 (by decide)
  have w3 := hj 3 (by decide)
  have w4 := hj 4 (by decide)
  have w5 := hj 5 (by decide)
  have w6 := hj 6 (by decide)
  simp only [Nat.reduceMul, BitVec.add_zero] at w0 w1 w3 w4 w5 w6
  have a0 := ha 0 (by decide)
  have a1 := ha 1 (by decide)
  rw [a1] at w0 w1 w3 w4 w5 w6
  have he : genE s = genE t := by
    simp only [genE, Spec.Rsa.bytesAt, a1]
    refine List.map_congr_left fun i hi => ?_
    exact word_bytes (m₁ := s.mem) (m₂ := t.mem) (a := stackArg t 1 + BitVec.ofNat 64 48) w6 (List.mem_range.mp hi)
  have hL : genLen s = genLen t := by
    simp only [genLen, a1]
    exact congrArg BitVec.toNat w1
  have hG : genOfState s = genOfState t := by
    simp only [genOfState, hdi, hdx, hcx, h9, a1, hsp, hL, h8, a0, he]
  have hpw : phaseWord (genProgress s).phase = phaseWord (genProgress t).phase := by
    have e4 : (s.mem.readW (stackArg t 1 + 32) 64).toNat = (t.mem.readW (stackArg t 1 + 32) 64).toNat :=
      congrArg BitVec.toNat w4
    simp only [genProgress, keyProgressAt, a1, e4]
    split <;> rfl
  have hl : (genProgress s).left = (genProgress t).left := by
    have e5 : (s.mem.readW (stackArg t 1 + 40) 64).toNat = (t.mem.readW (stackArg t 1 + 40) 64).toNat :=
      congrArg BitVec.toNat w5
    simp only [genProgress, keyProgressAt, a1, e5]
  have hr : (genProgress s).remaining = (genProgress t).remaining := by
    have e0 : (s.mem.readW (stackArg t 1) 64).toNat = (t.mem.readW (stackArg t 1) 64).toNat :=
      congrArg BitVec.toNat w0
    simp only [genProgress, keyProgressAt, a1, e0]
  simp only [initialPoint, hG, hpw, hl, hr, htr, Bignum.word, off, a1]
  rw [w3]

theorem gen_constantTime [Key.KeyProof] (v : RoundImpl) :
    ConstantTime isa genContract.pre genContract.pub (genCode v) := by
  refine RelCT.constantTime ((gen_code_ct v).mono ?_ (fun _ _ h => h))
  intro s t ⟨hs, ht, hp⟩
  exact ⟨initialPoint s, ⟨hs, rfl⟩, ⟨ht, (initial_point_eq hp).symm⟩⟩

end VG.Proof.RsaKeyGen.X86_64.Generate
