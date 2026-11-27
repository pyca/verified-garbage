module

public import VerifiedGarbage.Proof.Argon2.Arm.Derive.Initial
public import VerifiedGarbage.Proof.Argon2.Arm.HPrime.Finish
import VerifiedGarbage.Proof.Argon2.Arm.HPrime.Verified
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Argon2.Arm.CompressVerified
meta import VerifiedGarbage.Proof.Argon2.Arm.Derive.Initial
meta import VerifiedGarbage.Proof.Argon2.Arm.HPrime.Finish
meta import VerifiedGarbage.Proof.Argon2.Arm.HPrime.Verified
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Argon2.Arm.CompressVerified
public import VerifiedGarbage.Proof.Argon2.Arm.Derive.FillCall
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Argon2.Arm.CompressLit
import VerifiedGarbage.Proof.Blake2.Arm.CompressB
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Argon2.Arm.Derive.FillCall
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Argon2.Arm.CompressLit
meta import VerifiedGarbage.Proof.Blake2.Arm.CompressB
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT

/-! ### `Argon2.Arm.Derive.CTCall`, which this module and modules that import it used -/

section

/-! ### `Argon2.Arm.Derive.CTBase`, which only this module used -/

section

/-!
# Argon2 on ARMv7: the derivation's taint analysis

The body reads its arguments, which the caller's frame and the first frame
hold above the locals, through `r11`. So its pieces are analysed from states
with more permissions (`RelCT.taintW`, by `Exec.widen`): the locals, the
saved registers and the arguments as one writable region of 256 bytes at `r11`,
the memory matrix, `scratch` and the output (`wide`). `τB sl rs` makes `r11`,
the registers `rs`, the arguments and the locals' slots `sl` public;
`agreeB` gives it from what two runs of the body are known to share.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Spec.Blake2 (bytesAt)

/-- Two runs leak the same trace if, from states with more permissions, the
taint analysis proves it. -/
theorem RelCT.taintW {P : State → State → Prop} {c : Prog isa} (τ : VG.Arm.Taint.T)
    (hp : ∀ s₁ s₂, P s₁ s₂ → ∃ w₁ w₂, Covers s₁.wr w₁ ∧ Covers s₂.wr w₂ ∧
      VG.Arm.Taint.Agree τ (s₁.withRegions s₁.rd w₁) (s₂.withRegions s₂.rd w₂))
    {hc : VG.Taint.Hint VG.Arm.Taint.T} (h : (VG.Taint.check taint τ c hc).isSome = true) :
    RelCT isa P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  obtain ⟨w₁, w₂, c₁, c₂, ag⟩ := hp _ _ hP
  have e₁' := Exec.widen e₁ (Covers.append (Covers.refl _) c₁) c₁
  have e₂' := Exec.widen e₂ (Covers.append (Covers.refl _) c₂) c₂
  exact ⟨((VG.RelCT.taint (A := taint) (P := fun a b => a = s₁.withRegions s₁.rd w₁ ∧
    b = s₂.withRegions s₂.rd w₂) τ (fun _ _ ⟨h₁, h₂⟩ => by subst h₁ h₂; exact ag) h) _ _ _ _ _ _
    ⟨rfl, rfl⟩ e₁' e₂').1, trivial⟩

/-- A block of one instruction that touches no memory leaks nothing. -/
theorem RelCT.quiet {P : State → State → Prop} {i : Instr} (hi : ∀ s, addrs i s = []) :
    RelCT isa P (.block [i]) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  simp only [execBlock] at e₁ e₂
  split at e₁ <;> split at e₂ <;> simp_all [isa]

/-! ## The regions -/

/-- The regions the taint analysis of the body knows: the locals, saved
registers and arguments, the memory matrix, `scratch` and the output. -/
def wide (s₀ : State) : List Region :=
  [⟨State.addr (E s₀), 256⟩, memR s₀, scrR s₀, outR s₀]

/-- The taint state of the body, with the locals' slots `sl` and the registers
`rs` public. -/
def τB (sl : List (Nat × Nat × Nat)) (rs : List Reg := []) : VG.Arm.Taint.T :=
  { regs := .ofList (.r11 :: rs), flags := false, lens := [256, 1024, 16384, 0], bases := [(.r11, 0)],
    slots := sl ++ [(0, 184, 72)] }

/-- A region of two parts, each apart from `R`. -/
theorem disj_union {x : Addr} {n m : Nat} {R : Region} (hfit : n + m ≤ 2 ^ 64)
    (h₁ : Region.Disjoint ⟨x, n⟩ R) (h₂ : Region.Disjoint ⟨x + BitVec.ofNat 64 n, m⟩ R) :
    Region.Disjoint ⟨x, n + m⟩ R := by
  intro a ha hb
  simp only [Region.Contains] at ha
  by_cases hk : (a - x).toNat < n
  · exact h₁ a (by simp only [Region.Contains]; omega_using [hk]) hb
  · refine h₂ a ?_ hb
    simp only [Region.Contains]
    have := (Offset.lt_iff a x (d := n) (n := m) hfit).mpr ⟨by omega_using [hk], by omega_using [ha]⟩
    omega_using [this]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The 256 bytes at `E`: the locals, the saved registers and the arguments. -/
theorem big_disj {R : Region} (hR : R ∈ [memR s₀, scrR s₀, outR s₀]) :
    Region.Disjoint ⟨State.addr (E s₀), 256⟩ R := by
  have := hp.sp_lo; have := hp.sp_hi
  have hE := E_nat hp
  have e0 : (E0 s₀).toNat = s₀.sp.toNat := rfl
  have hS : R ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀, memR s₀, scrR s₀, outR s₀] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl <;> simp
  have st : Region.Sub ⟨State.addr (E s₀), 200⟩ (stkR0 s₀) := by
    simpa using frame_stk hp (d := 0) (n := 200) (by decide)
  have sa : Region.Sub ⟨State.addr (E s₀) + BitVec.ofNat 64 200, 56⟩ (argR s₀) := by
    rw [← addr_add (by have := E_hi hp; omega_using [hE])]
    show Region.Sub _ ⟨State.addr (s₀.sp + BitVec.ofNat 32 (4 * 0)), 56⟩
    have eE : (E s₀ + BitVec.ofNat 32 200).toNat = (E s₀).toNat + 200 := add_nat (by omega_using [hE])
    have eS : (s₀.sp + BitVec.ofNat 32 (4 * 0)).toNat = s₀.sp.toNat + 4 * 0 := add_nat (by omega_using [])
    exact sub32 (by rw [eE, eS]; omega_using [hE, e0]) (by rw [eE, eS]; omega_arith)
  exact disj_union (n := 200) (m := 56) (by decide) ((hp.stk_all R hS).sub_left st)
    ((hp.ro_w _ (by simp) R (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢; exact hR)).sub_left sa)

/-- A range of the 256 bytes at `E`, as an offset. -/
theorem in_big {x : BitVec 32} {n : Nat} (h₁ : (E s₀).toNat ≤ x.toNat) (h₂ : x.toNat + n ≤ (E s₀).toNat + 256) :
    ∃ off, State.addr x = State.addr (E s₀) + BitVec.ofNat 64 off ∧ off + n ≤ 256 := by
  have hE := E_hi hp
  refine ⟨x.toNat - (E s₀).toNat, ?_, by omega_using [h₁, h₂]⟩
  rw [← addr_add (by omega_using [])]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [add_nat (by omega_using [])]; omega_using [h₁]

theorem covers_wide : Covers (entry s₀).wr (wide s₀) := by
  have := hp.sp_lo; have := hp.sp_hi
  have hE := E_nat hp
  have e0 : (E0 s₀).toNat = s₀.sp.toNat := rfl
  have s1 := S1_nat hp
  have s2 := sp2 (s₀ := s₀) (by omega_arith)
  refine Covers.of_sub fun r hr => ?_
  simp only [entry, allocated, pushed_wr, List.mem_cons] at hr
  have big : ∀ x : BitVec 32, ∀ n, (E s₀).toNat ≤ x.toNat → x.toNat + n ≤ (E s₀).toNat + 256 →
      ∃ r' ∈ wide s₀, ∃ off, (⟨State.addr x, n⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧
        off + (⟨State.addr x, n⟩ : Region).len ≤ r'.len := fun x n h₁ h₂ => by
    obtain ⟨off, e, l⟩ := in_big hp h₁ h₂
    exact ⟨⟨State.addr (E s₀), 256⟩, by simp [wide], off, e, l⟩
  have f0 : ((pushed savedRegs (pushed argRegs s₀)).sp - BitVec.ofNat 32 144).toNat = (E0 s₀).toNat - 200 := by
    rw [VG.Arm.FrameStack.sub_toNat' (sp := (pushed savedRegs (pushed argRegs s₀)).sp) (k := 144) (by omega_arith), s2]
    omega_using []
  have f1 : ((pushed argRegs s₀).sp - BitVec.ofNat 32 (4 * savedRegs.length)).toNat = (E0 s₀).toNat - 56 := by
    rw [VG.Arm.FrameStack.sub_toNat' (sp := (pushed argRegs s₀).sp) (k := 4 * savedRegs.length)
      (by simp only [List.length_cons, List.length_nil]; omega_arith), s1]
    simp only [List.length_cons, List.length_nil]; omega_using []
  have f2 : (s₀.sp - BitVec.ofNat 32 (4 * argRegs.length)).toNat = (E0 s₀).toNat - 16 := by
    rw [VG.Arm.FrameStack.sub_toNat' (sp := s₀.sp) (k := 4 * argRegs.length)
      (by simp only [List.length_cons, List.length_nil]; omega_arith)]
    simp only [List.length_cons, List.length_nil]
  rcases hr with rfl | rfl | rfl | hr
  · exact big _ _ (by rw [f0]; omega_using [hE]) (by rw [f0]; omega_using [hE])
  · exact big _ _ (by rw [f1]; omega_using [hE]) (by rw [f1]; simp only [List.length_cons, List.length_nil]; omega_using [hE])
  · exact big _ _ (by rw [f2]; omega_using [hE]) (by rw [f2]; simp only [List.length_cons, List.length_nil]; omega_using [hE])
  · rw [hp.wr] at hr
    exact ⟨r, by simp only [wide, List.mem_cons] at hr ⊢; simp at hr; rcases hr with h | h | h <;> simp [h],
      0, by simp, by simp⟩

end

/-- What two runs share: the stack pointer and the arguments. -/
def Pub2 (s₀₁ s₀₂ : State) : Prop := E0 s₀₁ = E0 s₀₂ ∧ ∀ i < 18, arg s₀₁ i = arg s₀₂ i

theorem Pub2.E {s₀₁ s₀₂ : State} (h : Pub2 s₀₁ s₀₂) : E s₀₁ = E s₀₂ := by
  show E0 s₀₁ - BitVec.ofNat 32 200 = E0 s₀₂ - BitVec.ofNat 32 200
  rw [h.1]

theorem Pub2.wide_eq {s₀₁ s₀₂ : State} (h : Pub2 s₀₁ s₀₂) : wide s₀₁ = wide s₀₂ := by
  unfold wide
  rw [h.E, show memR s₀₁ = memR s₀₂ by simp only [memR, memP, blocksN, h.2 13 (by decide), h.2 14 (by decide)],
    show scrR s₀₁ = scrR s₀₂ by simp only [scrR, scrP, h.2 15 (by decide)],
    show outR s₀₁ = outR s₀₂ by simp only [outR, outP, outL, h.2 16 (by decide), h.2 17 (by decide)]]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem wf_wide (sl : List (Nat × Nat × Nat)) (rs : List Reg) {s : State} (h : Inv s₀ s) :
    VG.Arm.Taint.Wf (τB sl rs) (s.withRegions s.rd (wide s₀)) := by
  have hE := E_hi hp
  have b1 := blocks_pos hp
  have hm := hp.mem_fits
  have hs := hp.scr_fits
  have ho := hp.out_fits
  refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hp' => ?_, fun h0 => absurd h0 (Nat.lt_irrefl 0),
    fun _ h' => (List.not_mem_nil h').elim⟩
  · simp only [State.withRegions_wr, wide, τB]
    refine .cons (by simp) (.cons ?_ (.cons (by simp) (.cons (by simp) .nil)))
    show 1024 ≤ blocksN s₀ * 1024; omega_using [b1]
  · simp only [State.withRegions_wr, wide]
    refine .cons ?_ (.cons ?_ (.cons ?_ (.cons (fun _ h => (List.not_mem_nil h).elim) .nil)))
    · intro r hr; exact big_disj hp hr
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [hp.mem_scr, hp.mem_out]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact hp.scr_out
  · simp only [State.withRegions_wr, wide, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl) <;> simp only [MdStream.Arm.addr_toNat]
    · omega_using [hE]
    · exact hm
    · exact hs
    · exact ho
  · simp only [τB, List.mem_singleton] at hp'
    subst hp'
    show State.addr (s.gpr .r11) = State.addr (E s₀)
    rw [h.r11]

/-- A byte of the 256 bytes at `E`, from its word. -/
theorem loc_byte (m : Mem) {k : Nat} (hk : k < 256) :
    m (State.addr (E s₀) + BitVec.ofNat 64 k) =
      (m.readW (State.addr (E s₀ + BitVec.ofNat 32 (4 * (k / 4)))) 32).extractLsb' (8 * (k % 4)) 8 := by
  have := E_hi hp
  rw [addr_add (by omega_using [hk, this]), ← Mem.readW_byte m _ (Nat.mod_lt _ (by decide)), BitVec.add_assoc,
    BitVec.ofNat_add_ofNat, Nat.div_add_mod]

end

/-- The taint analysis's knowledge of the body, from what two runs share and
the values of the locals' slots `sl` in both. -/
theorem agreeB {s₀₁ s₀₂ s₁ s₂ : State} (hp₁ : DPre s₀₁) (hp₂ : DPre s₀₂) (pb : Pub2 s₀₁ s₀₂)
    (h₁ : Inv s₀₁ s₁) (h₂ : Inv s₀₂ s₂) (sl : List (Nat × Nat × Nat)) (rs : List Reg)
    (hrs : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hok : VG.Arm.Taint.SlotsOk (τB sl rs))
    (hsl : ∀ x ∈ sl, x.1 = 0 ∧ ∀ k, x.2.1 ≤ k → k < x.2.1 + x.2.2 →
      lw s₀₁ s₁ (4 * (k / 4)) = lw s₀₂ s₂ (4 * (k / 4))) :
    ∃ w₁ w₂, Covers s₁.wr w₁ ∧ Covers s₂.wr w₂ ∧
      VG.Arm.Taint.Agree (τB sl rs) (s₁.withRegions s₁.rd w₁) (s₂.withRegions s₂.rd w₂) := by
  refine ⟨wide s₀₁, wide s₀₂, by rw [h₁.wr]; exact covers_wide hp₁, by rw [h₂.wr]; exact covers_wide hp₂,
    ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => pb.wide_eq, wf_wide hp₁ sl rs h₁, wf_wide hp₂ sl rs h₂, hok,
      fun x hx k hk₁ hk₂ => ?_, fun h0 => absurd h0 (Nat.lt_irrefl 0),
      fun _ h0 => absurd h0 (Nat.not_lt_zero _)⟩⟩
  · simp only [τB, RegSet.mem_ofList, List.mem_cons] at hr
    rcases hr with rfl | hr
    · rw [State.withRegions_gpr, State.withRegions_gpr, h₁.r11, h₂.r11, pb.E]
    · rw [State.withRegions_gpr, State.withRegions_gpr]; exact hrs r hr
  · have hlen := hok x hx
    simp only [τB, List.mem_append, List.mem_singleton] at hx
    have hw : ∀ k < 256, lw s₀₁ s₁ (4 * (k / 4)) = lw s₀₂ s₂ (4 * (k / 4)) →
        (s₁.withRegions s₁.rd (wide s₀₁)).mem (VG.Arm.Taint.byteAddr (s₁.withRegions s₁.rd (wide s₀₁)) 0 k) =
        (s₂.withRegions s₂.rd (wide s₀₂)).mem (VG.Arm.Taint.byteAddr (s₂.withRegions s₂.rd (wide s₀₂)) 0 k) :=
      fun k hk e => by
        simp only [VG.Arm.Taint.byteAddr, VG.Arm.Taint.region, State.withRegions_wr, State.withRegions_mem,
          wide, List.getD_cons_zero]
        rw [loc_byte hp₁ s₁.mem hk, loc_byte hp₂ s₂.mem hk]
        exact congrArg _ e
    rcases hx with hx | rfl
    · obtain ⟨x0, hk⟩ := hsl x hx
      rw [x0] at hlen ⊢
      simp only [τB, List.getD_cons_zero] at hlen
      exact hw k (by omega_using [hk₂, hlen]) (hk k hk₁ hk₂)
    · simp only at hk₁ hk₂ ⊢
      refine hw k (by omega_using [hk₂]) ?_
      have e : 4 * (k / 4) = Impl.Argon2.Arm.Derive.argOff ((k - 184) / 4) := by
        simp only [Impl.Argon2.Arm.Derive.argOff, Impl.Argon2.Arm.Derive.locals]; omega_using [hk₁]
      rw [e, h₁.arg hp₁ (by omega_using [hk₂]), h₂.arg hp₂ (by omega_using [hk₂]), pb.2 _ (by omega_using [hk₂])]

end VG.Proof.Argon2.Arm.Derive

end

end


/-!
# Argon2 on ARMv7: two runs of the body

`Two s₀₁ s₀₂`: two runs of the derivation with the same public data.
`Two.leaf` relates a piece of the body the taint analysis proves, from the
public words of the locals (`slots_of_words`), and adds what each run
satisfies by correctness; `ccall_rel` and `hcall_rel` relate the calls of G
and H′, from their preconditions in both runs and their public arguments.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.Argon2.Arm (compressArm)

/-- Two runs of the derivation, with the same public data. -/
structure Two (s₀₁ s₀₂ : State) : Prop where
  hp₁ : DPre s₀₁
  hp₂ : DPre s₀₂
  pb : Pub2 s₀₁ s₀₂

namespace Pub2
variable {s₀₁ s₀₂ : State} (h : Pub2 s₀₁ s₀₂)
include h

theorem arg_eq {i : Nat} (hi : i < 18) : arg s₀₁ i = arg s₀₂ i := h.2 i hi
theorem memP_eq : memP s₀₁ = memP s₀₂ := h.2 13 (by decide)
theorem scrP_eq : scrP s₀₁ = scrP s₀₂ := h.2 15 (by decide)
theorem outP_eq : outP s₀₁ = outP s₀₂ := h.2 16 (by decide)
theorem blocksN_eq : blocksN s₀₁ = blocksN s₀₂ := by simp only [blocksN, h.2 14 (by decide)]
theorem lanesN_eq : lanesN s₀₁ = lanesN s₀₂ := by simp only [lanesN, h.2 7 (by decide)]
theorem itersN_eq : itersN s₀₁ = itersN s₀₂ := by simp only [itersN, h.2 5 (by decide)]

theorem prm_eq : prm s₀₁ = prm s₀₂ := by
  simp only [prm, kindV, itersN, mcostN, lanesN, outL, h.2 0 (by decide), h.2 5 (by decide),
    h.2 6 (by decide), h.2 7 (by decide), h.2 17 (by decide)]

end Pub2

/-- The slots `sl` of the locals hold the words `ws`. -/
theorem slots_of_words {s₀₁ s₀₂ s₁ s₂ : State} {ws : List Nat} {sl : List (Nat × Nat × Nat)}
    (hw : ∀ d ∈ ws, lw s₀₁ s₁ d = lw s₀₂ s₂ d)
    (hc : ∀ x ∈ sl, x.1 = 0 ∧ ∀ j < x.2.2, 4 * ((x.2.1 + j) / 4) ∈ ws) :
    ∀ x ∈ sl, x.1 = 0 ∧ ∀ k, x.2.1 ≤ k → k < x.2.1 + x.2.2 →
      lw s₀₁ s₁ (4 * (k / 4)) = lw s₀₂ s₂ (4 * (k / 4)) := by
  intro x hx
  obtain ⟨h0, hj⟩ := hc x hx
  refine ⟨h0, fun k h₁ h₂ => hw _ ?_⟩
  have := hj (k - x.2.1) (by omega_using [h₁, h₂])
  rwa [Nat.add_sub_cancel' h₁] at this

/-- A relation proved for each pair of related states. -/
theorem RelCT.of_eq {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ s₁ s₂, P s₁ s₂ → RelCT isa (fun a b => a = s₁ ∧ b = s₂) c Q) : RelCT isa P c Q :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => h s₁ s₂ hp s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

theorem execBlock_append (l₁ l₂ : List Instr) (s : State) :
    execBlock isa (l₁ ++ l₂) s = (execBlock isa l₁ s).bind fun p =>
      (execBlock isa l₂ p.1).map fun q => (q.1, p.2 ++ q.2) := by
  induction l₁ generalizing s with
  | nil => simp [execBlock]
  | cons i is ih =>
    simp only [List.cons_append, execBlock]
    split
    · rfl
    · rw [ih]
      cases execBlock isa is _ with
      | none => rfl
      | some p => simp [Function.comp_def, List.append_assoc]

/-- A block in two parts leaks as their sequence. -/
theorem RelCT.block_split {P Q : State → State → Prop} {l₁ l₂ : List Instr}
    (h : RelCT isa P (.seq (.block l₁) (.block l₂)) Q) : RelCT isa P (.block (l₁ ++ l₂)) Q := by
  have split : ∀ {s t s'}, Exec isa (.block (l₁ ++ l₂)) s t s' →
      Exec isa (.seq (.block l₁) (.block l₂)) s t s' := by
    intro s t s' e
    rw [Exec.block_iff, execBlock_append, Option.bind_eq_some_iff] at e
    obtain ⟨⟨s₁, t₁⟩, h₁, h₂⟩ := e
    rw [Option.map_eq_some_iff] at h₂
    obtain ⟨⟨s₂, t₂⟩, h₂, he⟩ := h₂
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact .seq (.block h₁) (.block h₂)
  exact fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (split e₁) (split e₂)

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- A piece of the body the taint analysis proves, from the slots `sl` of the
locals, which hold the words `ws`, public, and the registers `rs`. -/
theorem leaf {P : State → State → Prop} {c : Prog isa} (ws : List Nat) (sl : List (Nat × Nat × Nat))
    (rs : List Reg) (hok : VG.Arm.Taint.SlotsOk (τB sl rs))
    (hsl : ∀ x ∈ sl, x.1 = 0 ∧ ∀ j < x.2.2, 4 * ((x.2.1 + j) / 4) ∈ ws)
    (hag : ∀ s₁ s₂, P s₁ s₂ → Inv s₀₁ s₁ ∧ Inv s₀₂ s₂ ∧ (∀ d ∈ ws, lw s₀₁ s₁ d = lw s₀₂ s₂ d) ∧
      ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (VG.Taint.check taint (τB sl rs) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  refine RelCT.taintW (τB sl rs) (fun s₁ s₂ h => ?_) hc
  obtain ⟨i₁, i₂, hw, hr⟩ := hag s₁ s₂ h
  exact agreeB T.hp₁ T.hp₂ T.pb i₁ i₂ sl rs hr hok (slots_of_words hw hsl)

/-- A call of G: `compress(r0, r1, r2, r3)` to `scratch + o`, with the same
blocks in both runs. -/
theorem ccall_rel {o : Nat} (ho : 4096 ≤ o) (ho' : o + 1024 ≤ 16384) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ →
      (Inv s₀₁ s₁ ∧ s₁.gpr .r3 = scrP s₀₁ ∧ s₁.gpr .r2 = scrP s₀₁ + BitVec.ofNat 32 o ∧
        GArg s₀₁ o (s₁.gpr .r0) ∧ GArg s₀₁ o (s₁.gpr .r1)) ∧
      (Inv s₀₂ s₂ ∧ s₂.gpr .r3 = scrP s₀₂ ∧ s₂.gpr .r2 = scrP s₀₂ + BitVec.ofNat 32 o ∧
        GArg s₀₂ o (s₂.gpr .r0) ∧ GArg s₀₂ o (s₂.gpr .r1)) ∧
      s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1) :
    RelCT isa P Impl.Argon2.Arm.Derive.compressCall fun _ _ => True := by
  refine RelCT.of_eq fun s₁ s₂ hP => ?_
  obtain ⟨⟨i₁, d₁, c₁, x₁, y₁⟩, ⟨i₂, d₂, c₂, x₂, y₂⟩, ea, es⟩ := h s₁ s₂ hP
  obtain ⟨p₁, v₁, w₁⟩ := ccall_pre T.hp₁ i₁ d₁ ho ho' c₁ x₁ y₁
  obtain ⟨p₂, v₂, w₂⟩ := ccall_pre T.hp₂ i₂ d₂ ho ho' c₂ x₂ y₂
  have eR : cRd s₂ = cRd s₁ := by simp only [cRd, ea, es]
  have eW : cWr s₀₂ o = cWr s₀₁ o := by simp only [cWr, scrB, T.pb.scrP_eq]
  rw [eR, eW] at p₂ v₂
  rw [eW] at w₂
  unfold Impl.Argon2.Arm.Derive.compressCall
  refine RelCT.call (k := compressArm) Proof.Argon2.Arm.compress_verified'.1 Proof.Argon2.Arm.compress_ct
    (cRd s₁) (cWr s₀₁ o) fun a b ⟨ha, hb⟩ => ?_
  subst a b
  refine ⟨p₁, p₂, ?_, v₁, w₁, v₂, w₂⟩
  simp only [compressArm, State.withRegions_gpr,
    State.callEntry_gpr _ (show Reg.r0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.r2 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide)]
  exact ⟨ea, es, by rw [c₁, c₂, T.pb.scrP_eq], by rw [d₁, d₂, T.pb.scrP_eq]⟩

/-- A call of H′: `hprime(r0, r1, r2, r3, r12)`, with the same arguments in
both runs. -/
theorem hcall_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ →
      (Inv s₀₁ s₁ ∧ s₁.gpr .r12 = scrP s₀₁ ∧
        (∃ R ∈ [memR s₀₁, locR s₀₁], ∃ off, State.addr (s₁.gpr .r0) = R.base + BitVec.ofNat 64 off ∧
          off + (s₁.gpr .r1).toNat ≤ R.len) ∧ (s₁.gpr .r0).toNat + (s₁.gpr .r1).toNat ≤ 2 ^ 32 ∧
        (∃ R ∈ [memR s₀₁, outR s₀₁], ∃ off, State.addr (s₁.gpr .r2) = R.base + BitVec.ofNat 64 off ∧
          off + (s₁.gpr .r3).toNat ≤ R.len) ∧ (s₁.gpr .r2).toNat + (s₁.gpr .r3).toNat ≤ 2 ^ 32 ∧
        1 ≤ (s₁.gpr .r3).toNat) ∧
      (Inv s₀₂ s₂ ∧ s₂.gpr .r12 = scrP s₀₂ ∧
        (∃ R ∈ [memR s₀₂, locR s₀₂], ∃ off, State.addr (s₂.gpr .r0) = R.base + BitVec.ofNat 64 off ∧
          off + (s₂.gpr .r1).toNat ≤ R.len) ∧ (s₂.gpr .r0).toNat + (s₂.gpr .r1).toNat ≤ 2 ^ 32 ∧
        (∃ R ∈ [memR s₀₂, outR s₀₂], ∃ off, State.addr (s₂.gpr .r2) = R.base + BitVec.ofNat 64 off ∧
          off + (s₂.gpr .r3).toNat ≤ R.len) ∧ (s₂.gpr .r2).toNat + (s₂.gpr .r3).toNat ≤ 2 ^ 32 ∧
        1 ≤ (s₂.gpr .r3).toNat) ∧
      s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
        s₁.gpr .r3 = s₂.gpr .r3) :
    RelCT isa P Impl.Argon2.Arm.Derive.hPrimeCall fun _ _ => True := by
  unfold Impl.Argon2.Arm.Derive.hPrimeCall
  refine RelCT.of_eq fun s₁ s₂ hP => ?_
  obtain ⟨⟨i₁, d₁, n₁, nf₁, o₁, of₁, l₁⟩, ⟨i₂, d₂, n₂, nf₂, o₂, of₂, l₂⟩, e0, e1, e2, e3⟩ := h s₁ s₂ hP
  have hsp : s₁.sp = s₂.sp := by rw [i₁.sp, i₂.sp, T.pb.E]
  obtain ⟨p₁, v₁, w₁⟩ := hcall_pre T.hp₁ i₁ d₁ n₁ nf₁ o₁ of₁ l₁
  obtain ⟨p₂, v₂, w₂⟩ := hcall_pre T.hp₂ i₂ d₂ n₂ nf₂ o₂ of₂ l₂
  have eR : hRd s₂ = hRd s₁ := by simp only [hRd, e0, e1, hsp]
  have eW : hWr s₀₂ s₂ = hWr s₀₁ s₁ := by simp only [hWr, e2, e3, scrR, scrP, T.pb.scrP_eq]
  rw [eR, eW] at p₂ v₂
  rw [eW] at w₂
  have hn₁ : 4 * hregs.length ≤ s₁.sp.toNat := by
    have := T.hp₁.sp_lo
    simp only [List.length_cons, List.length_nil]; rw [i₁.sp, E_nat T.hp₁]; omega_using [this]
  have hn₂ : 4 * hregs.length ≤ s₂.sp.toNat := by rw [← hsp]; exact hn₁
  refine frameCall_rel (rs := hregs) (t := .r12) (by decide) (k := HPrime.hPrimeArm) HPrime.hPrime_verified.1
    HPrime.hPrime_verified.2.1 (hRd s₁) (hWr s₀₁ s₁) fun a b ⟨ha, hb⟩ => ?_
  subst a b
  refine ⟨hsp, p₁, p₂, ⟨by simp [hsp], ?_, ?_, ?_, ?_, ?_⟩, v₁, w₁, v₂, w₂⟩
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r0 ∉ linkRegs by decide), pushed_gpr, e0]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r1 ∉ linkRegs by decide), pushed_gpr, e1]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r2 ∉ linkRegs by decide), pushed_gpr, e2]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), pushed_gpr, e3]
  · exact VG.Proof.Argon2.Arm.pushed_arg_eq hn₁ hn₂ (i := 0) (by decide)
      (by show s₁.gpr .r12 = s₂.gpr .r12; rw [d₁, d₂, T.pb.scrP_eq])

end Two

end VG.Proof.Argon2.Arm.Derive

end

end

/-!
# Argon2 on ARMv7: H₀, in two runs

`code_rel`: H₀'s hash leaks the same trace in two runs with the same public
data. The BLAKE2b calls are related by H′'s macros' relations
(`HPrime.init_rel`, `update_rel`, `finalize_rel`, `absorbFixed_rel`), from
the same arguments: `scratch`, the inputs' places and lengths, and the byte
count, which only the inputs' lengths fix.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Spec.Blake2 (Repr b bytesAt)
open VG.Proof.Argon2.Arm.HPrime (Ctx InitIn UpdateIn FinalizeIn FixedIn)
open VG.Impl.Argon2.Arm.Derive (countLoOff countHiOff argOff ld st)

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp only [bytesAt, List.length_map, List.length_range]

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

theorem slotsOkE (rs : List Reg) : VG.Arm.Taint.SlotsOk (τB [] rs) := by
  intro x hx
  simp only [τB, List.nil_append, List.mem_singleton] at hx
  subst hx; simp [τB]

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- A piece the taint analysis proves from the arguments and the registers
`rs`, which both runs agree on. -/
theorem leafI {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s₁ s₂, P s₁ s₂ → Inv s₀₁ s₁ ∧ Inv s₀₂ s₂ ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (VG.Taint.check taint (τB [] rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  T.leaf [] [] rs (slotsOkE rs) (fun _ h => (List.not_mem_nil h).elim)
    (fun s₁ s₂ h => let ⟨i₁, i₂, hr⟩ := hag s₁ s₂ h; ⟨i₁, i₂, fun _ h => (List.not_mem_nil h).elim, hr⟩) hc

/-- `scratch`'s context in the second run, in the first run's terms. -/
theorem ctx₂ {s : State} (h : Inv s₀₂ s) (hb : s.gpr .r4 = scrP s₀₂) : Ctx (scrP s₀₁) (E s₀₁) s := by
  rw [T.pb.scrP_eq, T.pb.E]; exact ctx T.hp₂ h hb

/-- `start` leaks the same trace in two runs. -/
theorem start_rel :
    RelCT isa (fun s₁ s₂ => (Inv s₀₁ s₁ ∧ Prm s₀₁ s₁) ∧ (Inv s₀₂ s₂ ∧ Prm s₀₂ s₂))
      Impl.Argon2.Arm.Derive.start fun _ _ => True := by
  have hs := T.hp₁.scr_fits
  unfold Impl.Argon2.Arm.Derive.start
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => stA_ok T.hp₁ h.1 h.2) (fun s h => stA_ok T.hp₂ h.1 h.2) ?_
  refine RelCT.seqW ((HPrime.init_rel (B := scrP s₀₁) (SP := E s₀₁) (n := 64) (by decide) (by decide)).mono
      (fun s₁ s₂ h => ⟨⟨ctx T.hp₁ h.1.1 h.1.2.2.1, h.1.2.2.2⟩, ⟨T.ctx₂ h.2.1 h.2.2.2.1, h.2.2.2.2⟩⟩)
      fun _ _ h => h)
    (fun s h => stInit_ok T.hp₁ h) (fun s h => stInit_ok T.hp₂ h) ?_
  refine RelCT.seqW (T.leafI [.r4] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.2.2.1, h.2.2.2.1, T.pb.scrP_eq]⟩) ⟨_, by taint_decide⟩)
    (G₁ := fun t => Inv s₀₁ t ∧ Prm s₀₁ t ∧ t.gpr .r4 = scrP s₀₁ ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem (State.addr (scrP s₀₁)) [] ∧
      bytesAt t.mem (State.addr (scrP s₀₁) + BitVec.ofNat 64 768) 24 = Proof.Argon2.initialHeader (prm s₀₁))
    (G₂ := fun t => Inv s₀₂ t ∧ Prm s₀₂ t ∧ t.gpr .r4 = scrP s₀₂ ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem (State.addr (scrP s₀₂)) [] ∧
      bytesAt t.mem (State.addr (scrP s₀₂) + BitVec.ofNat 64 768) 24 = Proof.Argon2.initialHeader (prm s₀₂))
    (fun s h => (header_ok T.hp₁ h.1 h.2.1 h.2.2.1 h.2.2.2).mono fun t ⟨i, p, e, r, d, _⟩ => ⟨i, p, e, r, d⟩)
    (fun s h => (header_ok T.hp₂ h.1 h.2.1 h.2.2.1 h.2.2.2).mono fun t ⟨i, p, e, r, d, _⟩ => ⟨i, p, e, r, d⟩) ?_
  refine RelCT.seqW ((HPrime.absorbFixed_rel (B := scrP s₀₁) (SP := E s₀₁) (offset := 768) (size := 24)
      (by decide) (by decide) (by omega_arith) (by decide) (by decide) (stk_scr T.hp₁ (by decide) (by decide))
      ⟨_, by taint_decide⟩).mono
      (fun s₁ s₂ h => ⟨⟨ctx T.hp₁ h.1.1 h.1.2.2.1, scr_cov T.hp₁ h.1.1 (by decide)⟩,
        ⟨T.ctx₂ h.2.1 h.2.2.2.1, by rw [T.pb.scrP_eq]; exact scr_cov T.hp₂ h.2.1 (by decide)⟩⟩) fun _ _ h => h)
    (fun s h => stFix_ok T.hp₁ h) (fun s h => stFix_ok T.hp₂ h) ?_
  exact T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩

/-- `absorb ptr len` leaks the same trace in two runs whose absorbed data have
the same length. -/
theorem absorb_rel {ptr len : Nat} (hptr : ptr < 18) (hlen : len < 18)
    (hR₁ : (⟨State.addr (arg s₀₁ ptr), (arg s₀₁ len).toNat⟩ : Region) ∈ [pwR s₀₁, saltR s₀₁, secR s₀₁, adR s₀₁])
    (hR₂ : (⟨State.addr (arg s₀₂ ptr), (arg s₀₂ len).toNat⟩ : Region) ∈ [pwR s₀₂, saltR s₀₂, secR s₀₂, adR s₀₂])
    (hfit₁ : (arg s₀₁ ptr).toNat + (arg s₀₁ len).toNat ≤ 2 ^ 32)
    (hfit₂ : (arg s₀₂ ptr).toNat + (arg s₀₂ len).toNat ≤ 2 ^ 32) {data₁ data₂ : List Byte}
    (hd : data₁.length + 4 + 2 ^ 32 < 2 ^ 36) (heq : data₁.length = data₂.length)
    (hcA : ∃ hc, (VG.Taint.check taint (τB [] [.r4]) (.block [ld .r0 (argOff len), .str .r0 .r4 792,
      ld .r2 countLoOff, ld .r3 countHiOff, .dp .add .r9 .r4 (.imm 792), .mov .r10 (.imm 4)]) hc).isSome = true)
    (hcB : ∃ hc, (VG.Taint.check taint (τB [] []) (.block (Impl.Argon2.Arm.Derive.addCount (.imm 4) ++
      ([ld .r9 (argOff ptr), ld .r10 (argOff len)] : List Instr))) hc).isSome = true)
    (hcC : ∃ hc, (VG.Taint.check taint (τB [] [])
      (.block (ld .r0 (argOff len) :: Impl.Argon2.Arm.Derive.addCount (.reg .r0))) hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => HI s₀₁ data₁ s₁ ∧ HI s₀₂ data₂ s₂) (Impl.Argon2.Arm.Derive.absorb ptr len)
      fun _ _ => True := by
  have hs := T.hp₁.scr_fits
  have ep := T.pb.arg_eq hptr
  have el := T.pb.arg_eq hlen
  have e792 : State.addr (scrP s₀₁ + 792) = State.addr (scrP s₀₁) + BitVec.ofNat 64 792 :=
    scr_addr T.hp₁ (o := 792) (by decide)
  have cov792 : ∀ {s₀ s : State}, DPre s₀ → Inv s₀ s →
      Covers [⟨State.addr (scrP s₀ + 792), 4⟩] (s.rd ++ s.wr) := fun {s₀ s} hp h => by
    rw [show State.addr (scrP s₀ + 792) = State.addr (scrP s₀) + BitVec.ofNat 64 792 from
      scr_addr hp (o := 792) (by decide)]
    exact Covers.right (scr_cov hp h (by decide))
  have covIn : ∀ {s₀ s : State}, DPre s₀ → Inv s₀ s →
      (⟨State.addr (arg s₀ ptr), (arg s₀ len).toNat⟩ : Region) ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀] →
      Covers [⟨State.addr (arg s₀ ptr), (arg s₀ len).toNat⟩] (s.rd ++ s.wr) := fun {s₀ s} hp h hR => by
    have hR' : (⟨State.addr (arg s₀ ptr), (arg s₀ len).toNat⟩ : Region) ∈
        [pwR s₀, saltR s₀, secR s₀, adR s₀, argR s₀] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
      rcases hR with h | h | h | h <;> simp [h]
    rw [h.rd, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_left _ hR', 0, by simp, by simp⟩
  have hS : (⟨State.addr (arg s₀₁ ptr), (arg s₀₁ len).toNat⟩ : Region) ∈
      [pwR s₀₁, saltR s₀₁, secR s₀₁, adR s₀₁, memR s₀₁, scrR s₀₁, outR s₀₁] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR₁ ⊢
    rcases hR₁ with h | h | h | h <;> simp [h]
  have hR' : (⟨State.addr (arg s₀₁ ptr), (arg s₀₁ len).toNat⟩ : Region) ∈
      [pwR s₀₁, saltR s₀₁, secR s₀₁, adR s₀₁, argR s₀₁] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR₁ ⊢
    rcases hR₁ with h | h | h | h <;> simp [h]
  unfold Impl.Argon2.Arm.Derive.absorb
  refine RelCT.seqW (T.leafI [.r4] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.r4, h.2.r4, T.pb.scrP_eq]⟩) hcA)
    (fun s h => absA_ok T.hp₁ hlen h.hc) (fun s h => absA_ok T.hp₂ hlen h.hc) ?_
  refine RelCT.seqW ((HPrime.update_rel (B := scrP s₀₁) (SP := E s₀₁) (D := scrP s₀₁ + 792) (L := 4)
      (lo := BitVec.ofNat 32 data₁.length) (hi := BitVec.ofNat 32 (data₁.length / 2 ^ 32))
      (by have : (scrP s₀₁ + 792).toNat = (scrP s₀₁).toNat + 792 := add_nat (k := 792) (by omega_arith)
          omega_arith)
      (by rw [e792]; exact Offset.disjoint_base _ (by decide) (by decide))
      (by rw [e792]; exact stk_scr T.hp₁ (by decide) (by decide))).mono
      (fun s₁ s₂ ⟨⟨g₁, e₁, d₁, c₁, x₁, _⟩, ⟨g₂, e₂, d₂, c₂, x₂, _⟩⟩ =>
        ⟨⟨ctx T.hp₁ g₁.inv g₁.r4, e₁, d₁, c₁, x₁, cov792 T.hp₁ g₁.inv⟩,
         ⟨T.ctx₂ g₂.inv g₂.r4, by rw [e₂, T.pb.scrP_eq], d₂, by rw [c₂, heq], by rw [x₂, heq],
           by rw [T.pb.scrP_eq]; exact cov792 T.hp₂ g₂.inv⟩⟩) fun _ _ h => h)
    (fun s h => absU1_ok T.hp₁ h.1 rfl (by omega_arith) h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
    (fun s h => absU1_ok T.hp₂ h.1 rfl (by omega_arith) h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2) ?_
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩) hcB)
    (fun s h => absB_ok T.hp₁ hptr hlen (by omega_arith) h) (fun s h => absB_ok T.hp₂ hptr hlen (by omega_arith) h) ?_
  refine RelCT.seqW ((HPrime.update_rel (B := scrP s₀₁) (SP := E s₀₁) (D := arg s₀₁ ptr)
      (L := (arg s₀₁ len).toNat) (lo := BitVec.ofNat 32 (data₁.length + 4))
      (hi := BitVec.ofNat 32 ((data₁.length + 4) / 2 ^ 32))
      hfit₁ ((T.hp₁.ro_w _ hR' (scrR s₀₁) (by simp)).sub_right (Region.sub_prefix (by decide)))
      ((T.hp₁.stk_all _ hS).sub_left fun a ha => call_stk T.hp₁ a (stk32_call T.hp₁ a ha))).mono
      (fun s₁ s₂ ⟨⟨g₁, e₁, d₁, c₁, x₁⟩, ⟨g₂, e₂, d₂, c₂, x₂⟩⟩ =>
        ⟨⟨ctx T.hp₁ g₁.inv g₁.r4, e₁, d₁, c₁, x₁, covIn T.hp₁ g₁.inv hR₁⟩,
         ⟨T.ctx₂ g₂.inv g₂.r4, by rw [e₂, ep], by rw [d₂, el], by rw [c₂, heq], by rw [x₂, heq],
           by rw [ep, el]; exact covIn T.hp₂ g₂.inv hR₂⟩⟩) fun _ _ h => h)
    (fun s h => absU2_ok T.hp₁ hR₁ hfit₁ h.1 (by simp [Proof.Argon2.le32_length]) (by omega_arith)
      h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
    (fun s h => absU2_ok T.hp₂ hR₂ hfit₂ h.1 (by simp [Proof.Argon2.le32_length]) (by omega_arith)
      h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2) ?_
  exact T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩) hcC

/-- `finish` leaks the same trace in two runs whose absorbed data have the same
length. -/
theorem finish_rel {data₁ data₂ : List Byte} (heq : data₁.length = data₂.length) :
    RelCT isa (fun s₁ s₂ => HI s₀₁ data₁ s₁ ∧ HI s₀₂ data₂ s₂) Impl.Argon2.Arm.Derive.finish
      fun _ _ => True := by
  unfold Impl.Argon2.Arm.Derive.finish
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => fiA_ok T.hp₁ h) (fun s h => fiA_ok T.hp₂ h) ?_
  refine RelCT.seqW ((HPrime.finalize_rel (B := scrP s₀₁) (SP := E s₀₁) (lo := BitVec.ofNat 32 data₁.length)
      (hi := BitVec.ofNat 32 (data₁.length / 2 ^ 32))).mono
      (fun s₁ s₂ ⟨⟨g₁, c₁, x₁⟩, ⟨g₂, c₂, x₂⟩⟩ =>
        ⟨⟨ctx T.hp₁ g₁.inv g₁.r4, c₁, x₁⟩, ⟨T.ctx₂ g₂.inv g₂.r4, by rw [c₂, heq], by rw [x₂, heq]⟩⟩)
      fun _ _ h => h)
    (fun s h => fiFin_ok T.hp₁ h.1 h.2.1 h.2.2) (fun s h => fiFin_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  exact T.leafI [.r4] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by
    simp only [List.mem_singleton, forall_eq]; rw [h.1.2.2.1, h.2.2.2.1, T.pb.scrP_eq]⟩) ⟨_, by taint_decide⟩

/-- H₀'s code leaks the same trace in two runs. -/
theorem code_rel :
    RelCT isa (fun s₁ s₂ => (Inv s₀₁ s₁ ∧ Prm s₀₁ s₁) ∧ (Inv s₀₂ s₂ ∧ Prm s₀₂ s₂))
      Impl.Argon2.Arm.Derive.code fun _ _ => True := by
  have l1 := (arg s₀₁ 2).isLt
  have l2 := (arg s₀₁ 4).isLt
  have l3 := (arg s₀₁ 10).isLt
  have hpp := T.pb
  have a2 : (arg s₀₂ 2).toNat = (arg s₀₁ 2).toNat := by rw [hpp.arg_eq (by decide)]
  have a4 : (arg s₀₂ 4).toNat = (arg s₀₁ 4).toNat := by rw [hpp.arg_eq (by decide)]
  have a10 : (arg s₀₂ 10).toNat = (arg s₀₁ 10).toNat := by rw [hpp.arg_eq (by decide)]
  have a12 : (arg s₀₂ 12).toNat = (arg s₀₁ 12).toNat := by rw [hpp.arg_eq (by decide)]
  unfold Impl.Argon2.Arm.Derive.code
  refine RelCT.seqW T.start_rel (fun s h => start_ok T.hp₁ h.1 h.2) (fun s h => start_ok T.hp₂ h.1 h.2) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 1) (len := 2) (by decide) (by decide) (by simp) (by simp)
      T.hp₁.pw_fits T.hp₂.pw_fits (by rw [Proof.Argon2.initialHeader_length]; omega_arith)
      (by rw [Proof.Argon2.initialHeader_length, Proof.Argon2.initialHeader_length])
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => absorb_ok T.hp₁ (ptr := 1) (len := 2) (by decide) (by decide) (by simp) T.hp₁.pw_fits
      (by rw [Proof.Argon2.initialHeader_length]; omega_arith) h)
    (fun s h => absorb_ok T.hp₂ (ptr := 1) (len := 2) (by decide) (by decide) (by simp) T.hp₂.pw_fits
      (by rw [Proof.Argon2.initialHeader_length]; omega_arith) h) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 3) (len := 4) (by decide) (by decide) (by simp) (by simp)
      T.hp₁.salt_fits T.hp₂.salt_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]; omega_arith)
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length, a2])
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => absorb_ok T.hp₁ (ptr := 3) (len := 4) (by decide) (by decide) (by simp) T.hp₁.salt_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]; omega_arith) h)
    (fun s h => absorb_ok T.hp₂ (ptr := 3) (len := 4) (by decide) (by decide) (by simp) T.hp₂.salt_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]
          have := (arg s₀₂ 2).isLt; omega_arith) h) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 9) (len := 10) (by decide) (by decide) (by simp) (by simp)
      T.hp₁.sec_fits T.hp₂.sec_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]; omega_arith)
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length, a2, a4])
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => absorb_ok T.hp₁ (ptr := 9) (len := 10) (by decide) (by decide) (by simp) T.hp₁.sec_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]; omega_arith) h)
    (fun s h => absorb_ok T.hp₂ (ptr := 9) (len := 10) (by decide) (by decide) (by simp) T.hp₂.sec_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]
          have := (arg s₀₂ 2).isLt; have := (arg s₀₂ 4).isLt; omega_arith) h) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 11) (len := 12) (by decide) (by decide) (by simp) (by simp)
      T.hp₁.ad_fits T.hp₂.ad_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]; omega_arith)
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length, a2, a4,
        a10])
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => absorb_ok T.hp₁ (ptr := 11) (len := 12) (by decide) (by decide) (by simp) T.hp₁.ad_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]; omega_arith) h)
    (fun s h => absorb_ok T.hp₂ (ptr := 11) (len := 12) (by decide) (by decide) (by simp) T.hp₂.ad_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]
          have := (arg s₀₂ 2).isLt; have := (arg s₀₂ 4).isLt; have := (arg s₀₂ 10).isLt; omega_arith) h) ?_
  exact T.finish_rel (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length,
    bytesAt_length, a2, a4, a10, a12])

end Two

end VG.Proof.Argon2.Arm.Derive
