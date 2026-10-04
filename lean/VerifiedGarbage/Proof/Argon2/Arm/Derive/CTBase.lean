import VerifiedGarbage.Proof.Argon2.Arm.Derive.Correct
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

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
  · exact h₁ a (by simp only [Region.Contains]; omega) hb
  · refine h₂ a ?_ hb
    simp only [Region.Contains]
    have := (Offset.lt_iff a x (d := n) (n := m) hfit).mpr ⟨by omega, by omega⟩
    omega

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
    rw [← addr_add (by have := E_hi hp; omega)]
    show Region.Sub _ ⟨State.addr (s₀.sp + BitVec.ofNat 32 (4 * 0)), 56⟩
    have eE : (E s₀ + BitVec.ofNat 32 200).toNat = (E s₀).toNat + 200 := add_nat (by omega)
    have eS : (s₀.sp + BitVec.ofNat 32 (4 * 0)).toNat = s₀.sp.toNat + 4 * 0 := add_nat (by omega)
    exact sub32 (by rw [eE, eS]; omega) (by rw [eE, eS]; omega)
  exact disj_union (n := 200) (m := 56) (by decide) ((hp.stk_all R hS).sub_left st)
    ((hp.ro_w _ (by simp) R (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢; exact hR)).sub_left sa)

/-- A range of the 256 bytes at `E`, as an offset. -/
theorem in_big {x : BitVec 32} {n : Nat} (h₁ : (E s₀).toNat ≤ x.toNat) (h₂ : x.toNat + n ≤ (E s₀).toNat + 256) :
    ∃ off, State.addr x = State.addr (E s₀) + BitVec.ofNat 64 off ∧ off + n ≤ 256 := by
  have hE := E_hi hp
  refine ⟨x.toNat - (E s₀).toNat, ?_, by omega⟩
  rw [← addr_add (by omega)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [add_nat (by omega)]; omega

theorem covers_wide : Covers (entry s₀).wr (wide s₀) := by
  have := hp.sp_lo; have := hp.sp_hi
  have hE := E_nat hp
  have e0 : (E0 s₀).toNat = s₀.sp.toNat := rfl
  have s1 := S1_nat hp
  have s2 := sp2 (s₀ := s₀) (by omega)
  refine Covers.of_sub fun r hr => ?_
  simp only [entry, allocated, pushed_wr, List.mem_cons] at hr
  have big : ∀ x : BitVec 32, ∀ n, (E s₀).toNat ≤ x.toNat → x.toNat + n ≤ (E s₀).toNat + 256 →
      ∃ r' ∈ wide s₀, ∃ off, (⟨State.addr x, n⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧
        off + (⟨State.addr x, n⟩ : Region).len ≤ r'.len := fun x n h₁ h₂ => by
    obtain ⟨off, e, l⟩ := in_big hp h₁ h₂
    exact ⟨⟨State.addr (E s₀), 256⟩, by simp [wide], off, e, l⟩
  have f0 : ((pushed savedRegs (pushed argRegs s₀)).sp - BitVec.ofNat 32 144).toNat = (E0 s₀).toNat - 200 := by
    rw [VG.Arm.FrameStack.sub_toNat' (sp := (pushed savedRegs (pushed argRegs s₀)).sp) (k := 144) (by omega), s2]
    omega
  have f1 : ((pushed argRegs s₀).sp - BitVec.ofNat 32 (4 * savedRegs.length)).toNat = (E0 s₀).toNat - 56 := by
    rw [VG.Arm.FrameStack.sub_toNat' (sp := (pushed argRegs s₀).sp) (k := 4 * savedRegs.length)
      (by simp only [List.length_cons, List.length_nil]; omega), s1]
    simp only [List.length_cons, List.length_nil]; omega
  have f2 : (s₀.sp - BitVec.ofNat 32 (4 * argRegs.length)).toNat = (E0 s₀).toNat - 16 := by
    rw [VG.Arm.FrameStack.sub_toNat' (sp := s₀.sp) (k := 4 * argRegs.length)
      (by simp only [List.length_cons, List.length_nil]; omega)]
    simp only [List.length_cons, List.length_nil]
  rcases hr with rfl | rfl | rfl | hr
  · exact big _ _ (by rw [f0]; omega) (by rw [f0]; omega)
  · exact big _ _ (by rw [f1]; omega) (by rw [f1]; simp only [List.length_cons, List.length_nil]; omega)
  · exact big _ _ (by rw [f2]; omega) (by rw [f2]; simp only [List.length_cons, List.length_nil]; omega)
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
    show 1024 ≤ blocksN s₀ * 1024; omega
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
    · omega
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
  rw [addr_add (by omega), ← Mem.readW_byte m _ (Nat.mod_lt _ (by decide)), BitVec.add_assoc,
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
      exact hw k (by omega) (hk k hk₁ hk₂)
    · simp only at hk₁ hk₂ ⊢
      refine hw k (by omega) ?_
      have e : 4 * (k / 4) = Impl.Argon2.Arm.Derive.argOff ((k - 184) / 4) := by
        simp only [Impl.Argon2.Arm.Derive.argOff, Impl.Argon2.Arm.Derive.locals]; omega
      rw [e, h₁.arg hp₁ (by omega), h₂.arg hp₂ (by omega), pb.2 _ (by omega)]

end VG.Proof.Argon2.Arm.Derive
