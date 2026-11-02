module

public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Body
public import VerifiedGarbage.Proof.Framework.RISCV64.FrameTaint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Argon2 on RISC-V: two runs of the derivation

`Two s₀₁ s₀₂`: two runs with the same public data (`Pub2`: the stack pointer
and the arguments). The body's pieces are analysed by `frameTaint` from
`τF ws rs`: `s3`, `s4`, `s0` and the registers `rs` public, and the frame's
doublewords at the offsets `ws` and the arguments' public bytes (`leaf`,
from `agreeF`). `RelCT.seqW` composes pieces, carrying what each run
satisfies by correctness.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Impl.Argon2.RISCV64.Derive (argOff)

/-- What two runs share: the stack pointer and the arguments' public bits. -/
def Pub2 (s₀₁ s₀₂ : State) : Prop := s₀₁.sp = s₀₂.sp ∧ ∀ i < 18, argPub s₀₁ i = argPub s₀₂ i

namespace Pub2
variable {s₀₁ s₀₂ : State} (h : Pub2 s₀₁ s₀₂)
include h

theorem E_eq : E s₀₁ = E s₀₂ := by simp only [E, h.1]

theorem arg_eq {i : Nat} (hi : i < 18) (hn : i ∉ intArgs := by decide) : arg s₀₁ i = arg s₀₂ i := by
  have e := h.2 i hi
  simp only [argPub, hn, ite_false] at e
  exact e

theorem arg32_eq {i : Nat} (hi : i < 18) : arg32 s₀₁ i = arg32 s₀₂ i := by
  have e := h.2 i hi
  by_cases hn : i ∈ intArgs
  · simp only [argPub, hn, ite_true] at e
    have e' := congrArg (BitVec.setWidth 32) e
    rwa [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq,
      BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq] at e'
  · rw [arg32, arg32, h.arg_eq hi hn]

theorem memP_eq : memP s₀₁ = memP s₀₂ := h.arg_eq (i := 13) (by decide)
theorem scrP_eq : scrP s₀₁ = scrP s₀₂ := h.arg_eq (i := 15) (by decide)
theorem outP_eq : outP s₀₁ = outP s₀₂ := h.arg_eq (i := 16) (by decide)
theorem outL_eq : outL s₀₁ = outL s₀₂ := by simp only [outL, h.arg_eq (i := 17) (by decide)]
theorem blocksN_eq : blocksN s₀₁ = blocksN s₀₂ := by simp only [blocksN, h.arg_eq (i := 14) (by decide)]
theorem lanesN_eq : lanesN s₀₁ = lanesN s₀₂ := by simp only [lanesN, h.arg32_eq (i := 7) (by decide)]
theorem itersN_eq : itersN s₀₁ = itersN s₀₂ := by simp only [itersN, h.arg32_eq (i := 5) (by decide)]

theorem prm_eq : prm s₀₁ = prm s₀₂ := by
  simp only [prm, kindV, itersN, mcostN, lanesN, outL, h.arg32_eq (i := 0) (by decide),
    h.arg32_eq (i := 5) (by decide), h.arg32_eq (i := 6) (by decide), h.arg32_eq (i := 7) (by decide),
    h.arg_eq (i := 17) (by decide)]

end Pub2

/-- Two runs of the derivation, with the same public data. -/
structure Two (s₀₁ s₀₂ : State) : Prop where
  hp₁ : DPre s₀₁
  hp₂ : DPre s₀₂
  pb : Pub2 s₀₁ s₀₂

/-! ## The taint of the body -/

/-- The bytes of the doublewords at the offsets `ws`. -/
def slotsOf (ws : List Nat) : Nat := ws.foldr (fun d S => Nat.lor (Slots.bits d 8) S) 0

/-- The public bytes of argument `i`'s copy in the frame: its low word if it
is a 32-bit one. -/
def argWidth (i : Nat) : Nat := if i ∈ intArgs then 4 else 8

/-- The public bytes of the arguments' copies in the frame. -/
def argSlots : Nat := (List.range 18).foldr (fun i S => Nat.lor (Slots.bits (argOff i) (argWidth i)) S) 0

/-- `s3`, `s4`, `s0` and `rs` public, and the doublewords at `ws` and the
arguments' public bytes. -/
def τF (ws : List Nat) (rs : List Reg := []) : FrameTaint.T :=
  ⟨RegSet.ofList (.s3 :: .s4 :: .s0 :: rs), Nat.lor (slotsOf ws) argSlots⟩

theorem slotsOf_testBit {ws : List Nat} {k : Nat} (h : (slotsOf ws).testBit k = true) :
    ∃ d ∈ ws, d ≤ k ∧ k < d + 8 := by
  induction ws with
  | nil => simp [slotsOf] at h
  | cons d ws ih =>
    simp only [slotsOf, List.foldr_cons] at h ih
    rw [show Nat.lor _ _ = _ ||| _ from rfl, Nat.testBit_or, Bool.or_eq_true, Slots.testBit_bits] at h
    rcases h with h | h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨d, by simp, h⟩
    · obtain ⟨e, he, h⟩ := ih h
      exact ⟨e, by simp [he], h⟩

theorem argSlots_testBit {k : Nat} (h : argSlots.testBit k = true) :
    ∃ i < 18, argOff i ≤ k ∧ k < argOff i + argWidth i := by
  suffices ∀ l : List Nat, (∀ i ∈ l, i < 18) →
      (l.foldr (fun i S => Nat.lor (Slots.bits (argOff i) (argWidth i)) S) 0).testBit k = true →
      ∃ i < 18, argOff i ≤ k ∧ k < argOff i + argWidth i from
    this _ (fun i hi => List.mem_range.mp hi) h
  intro l hl h
  induction l with
  | nil => simp at h
  | cons i l ih =>
    simp only [List.foldr_cons] at h
    rw [show Nat.lor _ _ = _ ||| _ from rfl, Nat.testBit_or, Bool.or_eq_true, Slots.testBit_bits] at h
    rcases h with h | h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨i, hl i (by simp), h⟩
    · exact ih (fun j hj => hl j (by simp [hj])) h

/-- Byte `j` of equal words. -/
theorem byte_of_lw32 {m₁ m₂ : Mem} {a₁ a₂ : Addr} (h : m₁.readW a₁ 32 = m₂.readW a₂ 32) {j : Nat}
    (hj : j < 4) : m₁ (a₁ + BitVec.ofNat 64 j) = m₂ (a₂ + BitVec.ofNat 64 j) := by
  rw [← Mem.extractLsb'_read m₁ a₁ (n := 4) hj, ← Mem.extractLsb'_read m₂ a₂ (n := 4) hj]
  have e : m₁.read a₁ 4 = m₂.read a₂ 4 := by simpa [Mem.readW] using h
  rw [e]

/-- Byte `j` of equal doublewords. -/
theorem byte_of_lw {m₁ m₂ : Mem} {a₁ a₂ : Addr} (h : m₁.readW a₁ 64 = m₂.readW a₂ 64) {j : Nat}
    (hj : j < 8) : m₁ (a₁ + BitVec.ofNat 64 j) = m₂ (a₂ + BitVec.ofNat 64 j) := by
  rw [← Mem.extractLsb'_read m₁ a₁ (n := 8) hj, ← Mem.extractLsb'_read m₂ a₂ (n := 8) hj]
  have e : m₁.read a₁ 8 = m₂.read a₂ 8 := by simpa [Mem.readW] using h
  rw [e]

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- What the taint analysis knows, from what two runs of the body share. -/
theorem agreeF {s₁ s₂ : State} (h₁ : Inv s₀₁ s₁) (h₂ : Inv s₀₂ s₂) (ws : List Nat) (rs : List Reg)
    (hw : ∀ d ∈ ws, lw s₀₁ s₁ d = lw s₀₂ s₂ d)
    (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : FrameTaint.Agree (τF ws rs) s₁ s₂ := by
  refine ⟨⟨by rw [h₁.sp, h₂.sp, T.pb.E_eq], fun r hr' => ?_⟩, fun k hk hbit => ?_⟩
  · simp only [τF, RegSet.mem_ofList, List.mem_cons] at hr'
    rcases hr' with rfl | rfl | rfl | hr'
    · rw [h₁.s3, h₂.s3, T.pb.E_eq]
    · rw [h₁.s4, h₂.s4, T.pb.scrP_eq]
    · rw [h₁.s0, h₂.s0, hiP, hiP, T.pb.scrP_eq]
    · exact hr _ hr'
  · have e : ∀ {s₀ s : State} {d : Nat}, d ≤ k → Inv s₀ s →
        s.mem (s.gpr .s3 + BitVec.ofNat 64 k) = s.mem (E s₀ + BitVec.ofNat 64 d + BitVec.ofNat 64 (k - d)) :=
      fun {s₀ s d} hd h => by rw [h.s3, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' hd]
    simp only [τF] at hbit
    rw [show Nat.lor _ _ = _ ||| _ from rfl, Nat.testBit_or, Bool.or_eq_true] at hbit
    rcases hbit with hbit | hbit
    · obtain ⟨d, hd, h₁d, h₂d⟩ := slotsOf_testBit hbit
      rw [e h₁d h₁, e h₁d h₂]
      exact byte_of_lw (hw d hd) (by omega)
    · obtain ⟨i, hi, h₁d, h₂d⟩ := argSlots_testBit hbit
      rw [e h₁d h₁, e h₁d h₂]
      by_cases hn : i ∈ intArgs
      · simp only [argWidth, hn, ite_true] at h₂d
        refine byte_of_lw32 ?_ (by omega)
        rw [h₁.arg32 T.hp₁ hi, h₂.arg32 T.hp₂ hi, T.pb.arg32_eq hi]
      · simp only [argWidth, hn, ite_false] at h₂d
        refine byte_of_lw ?_ (by omega)
        rw [h₁.arg T.hp₁ hi, h₂.arg T.hp₂ hi, T.pb.arg_eq hi hn]

/-- A piece the taint analysis proves, from the doublewords at `ws`, which
both runs agree on, and the registers `rs`. -/
theorem leaf {P : State → State → Prop} {c : Prog isa} (ws : List Nat) (rs : List Reg)
    (hag : ∀ s₁ s₂, P s₁ s₂ → Inv s₀₁ s₁ ∧ Inv s₀₂ s₂ ∧ (∀ d ∈ ws, lw s₀₁ s₁ d = lw s₀₂ s₂ d) ∧
      ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (VG.Taint.check frameTaint (τF ws rs) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  refine RelCT.taint (A := frameTaint) (τF ws rs) (fun s₁ s₂ h => ?_) hc
  obtain ⟨i₁, i₂, hw, hr⟩ := hag s₁ s₂ h
  exact T.agreeF i₁ i₂ ws rs hw hr

end Two

/-! ## Composition -/

/-- What each run satisfies after a piece, in the relation of its final states. -/
theorem rel_wp {F₁ F₂ G₁ G₂ : State → Prop} {c : Prog isa}
    (h : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c fun _ _ => True)
    (w₁ : ∀ s, F₁ s → WP isa c s G₁) (w₂ : ∀ s, F₂ s → WP isa c s G₂) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c fun s₁ s₂ => G₁ s₁ ∧ G₂ s₂ :=
  (h.wp fun s₁ s₂ hp => ⟨w₁ s₁ hp.1, w₂ s₂ hp.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- Composition, with what each run satisfies after the first part. -/
theorem RelCT.seqW {F₁ F₂ G₁ G₂ : State → Prop} {c₁ c₂ : Prog isa} {Q : State → State → Prop}
    (h₁ : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c₁ fun _ _ => True)
    (w₁ : ∀ s, F₁ s → WP isa c₁ s G₁) (w₂ : ∀ s, F₂ s → WP isa c₁ s G₂)
    (h₂ : RelCT isa (fun s₁ s₂ => G₁ s₁ ∧ G₂ s₂) c₂ Q) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) (.seq c₁ c₂) Q :=
  RelCT.seq (rel_wp h₁ w₁ w₂) h₂

/-- A branch on a condition that agrees in both runs. -/
theorem RelCT.iteF {F₁ F₂ : State → Prop} {c : Cond} {th el : Prog isa} {Q : State → State → Prop}
    (hc : ∀ s₁ s₂, F₁ s₁ → F₂ s₂ → isa.eval c s₁ = isa.eval c s₂)
    (ht : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) th Q) (he : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) el Q) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) (.ite c th el) Q :=
  RelCT.ite (fun s₁ s₂ h => hc s₁ s₂ h.1 h.2) (ht.mono (fun _ _ h => h.1) fun _ _ h => h)
    (he.mono (fun _ _ h => h.1) fun _ _ h => h)

end VG.Proof.Argon2.RISCV64.Derive
