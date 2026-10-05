import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Impl.Clear.X86_64

/-!
# Returning without secret residue (x86-64)

`X86_64.noResidue` (`Artifact.clearsResidue`) asks what a function leaves in
registers and below the stack pointer to be zero, public or its caller's.

* `Verified.clear`: code `c` followed by `Impl.Clear.X86_64.clear rs avx`
  (zero the SSE registers, and the general-purpose registers `rs`) is
  verified against the contract `c` is, and leaves no residue, given what
  `c` leaves in the registers it does not clear and below the stack pointer.
* `Exec.stackRes`: code without frames leaves below the stack pointer only
  what was there and its calls' return addresses.
* `Exec.uppers`: code without VEX or EVEX instructions keeps the upper halves
  of the vector registers.
-/

namespace VG.X86_64

open Impl.Clear.X86_64

/-- Whether an instruction may write the upper halves (bits 511:128) of the
vector registers: the VEX and EVEX ones that write vector registers. -/
def writesUpper : Instr → Bool
  | .vop _ | .zop _ | .vmovdquLoad .. | .vbroadcasti128 .. | .vmovdqu32Load ..
  | .vbroadcasti32x4 .. | .zbcst .. => true
  | _ => false

/-- Every instruction keeps the unknowns; those that `writesUpper` rejects
keep the upper halves of the vector registers. -/
theorem exec_keeps {i : Instr} {s s' : State} (h : exec i s = some s') :
    s'.unknowns = s.unknowns ∧
      (writesUpper i = false → s'.ymmHi = s.ymmHi ∧ s'.zmmHi = s.zmmHi) := by
  cases i with
  | ldmxcsr m =>
    simp only [exec, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, h⟩ := h; split at h <;> cases h; exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  | alu op d src =>
    simp only [exec, Taint.execAlu_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h; split <;> exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  | alu32 op d src =>
    simp only [exec, Taint.execAlu32_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h; split <;> exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  | shift32 op d n =>
    simp only [exec, execShift32] at h
    split at h <;> [skip; cases h]
    cases op <;> (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩)
  | shift op d n =>
    simp only [exec, execShift] at h
    split at h <;> [skip; cases h]
    cases op <;> (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩)
  | xop op =>
    simp only [exec, Option.some.injEq] at h; subst h; rw [Taint.XOp.exec_eq op s]
    exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  | vop op =>
    simp only [exec, Option.some.injEq] at h; subst h; rw [Taint.VOp.exec_eq op s]
    exact ⟨rfl, fun h => by cases h⟩
  | zop op =>
    simp only [exec, Option.some.injEq] at h; subst h; rw [Taint.ZOp.exec_eq op s]
    exact ⟨rfl, fun h => by cases h⟩
  | vmovdquLoad len d m =>
    cases len <;> simp only [exec, Option.map_eq_some_iff] at h <;> obtain ⟨_, _, rfl⟩ := h <;>
      exact ⟨rfl, fun h => by cases h⟩
  | vbroadcasti128 | vmovdqu32Load | vbroadcasti32x4 | zbcst =>
    simp only [exec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h
    exact ⟨rfl, fun h => by cases h⟩
  | vmovdquStore len m r =>
    cases len
    · simp only [exec, State.store128] at h; split at h <;> cases h; exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
    · simp only [exec, State.store256] at h; split at h <;> cases h; exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  | store m r =>
    simp only [exec, State.store64] at h; split at h <;> cases h; exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  | store32 m r =>
    simp only [exec, State.store32] at h; split at h <;> cases h; exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  | store8 m r =>
    simp only [exec, State.store8] at h; split at h <;> cases h; exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  | movdquStore m r =>
    simp only [exec, State.store128] at h; split at h <;> cases h; exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  | stmxcsr m =>
    simp only [exec, State.store32] at h; split at h <;> cases h; exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  | vmovdqu32Store m r =>
    simp only [exec, State.store512] at h; split at h <;> cases h; exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  | mov | mov32 | movzx8 | movdquLoad =>
    simp only [exec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h
    exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  | bswap32 | bswap | movImm64 | lfence | mul | andn32 | andn | vpmovmskb =>
    simp only [exec, Option.some.injEq] at h; subst h; exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  | rorx32 =>
    simp only [exec, execRorx32] at h; split at h <;> cases h; exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  | rorx =>
    simp only [exec, execRorx] at h; split at h <;> cases h; exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  | mulx =>
    simp only [exec, execMulx] at h; split at h
    · cases h
    · simp only [Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h
      exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  | adcx =>
    simp only [exec, execAdcx] at h; split at h
    · cases h
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, _, _, rfl⟩ := h; exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  | adox =>
    simp only [exec, execAdox] at h; split at h
    · cases h
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, _, _, rfl⟩ := h; exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  | push | pop | alloc | free => simp only [exec, reduceCtorEq] at h

theorem execBlock_keeps {is : List Instr} {s s' : State} {t : List Leak}
    (h : execBlock isa is s = some (s', t)) :
    s'.unknowns = s.unknowns ∧
      ((is.all fun i => !writesUpper i) = true → s'.ymmHi = s.ymmHi ∧ s'.zmmHi = s.zmmHi) := by
  induction is generalizing s t with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]; exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  | cons i is ih =>
    simp only [execBlock] at h
    split at h <;> [cases h; skip]
    rename_i s₁ he
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s₂, t₂⟩, h2, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨u₁, v₁⟩ := exec_keeps (i := i) (s := s) (s' := s₁) he
    obtain ⟨u₂, v₂⟩ := ih h2
    refine ⟨u₂.trans u₁, fun hw => ?_⟩
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hw
    obtain ⟨a₂, b₂⟩ := v₂ hw.2
    obtain ⟨a₁, b₁⟩ := v₁ hw.1
    exact ⟨a₂.trans a₁, b₂.trans b₁⟩

/-! ## Upper halves -/

theorem pushRegs_uppers (s : State) (rs : List Reg) :
    (pushRegs s rs).ymmHi = s.ymmHi ∧ (pushRegs s rs).zmmHi = s.zmmHi := by
  induction rs generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons r rs ih => exact ih _

theorem popReg_uppers (s : State) (r : Reg) (k : Nat) :
    (popReg s r k).ymmHi = s.ymmHi ∧ (popReg s r k).zmmHi = s.zmmHi := by
  induction k generalizing s with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih => exact ih _

/-- Code without VEX or EVEX instructions writing vector registers keeps
their upper halves. -/
theorem Exec.uppers {c : Prog isa} (hc : ∀ i ∈ instrs c, writesUpper i = false)
    {s s' : State} {t : List Leak} (h : Exec isa c s t s') : (s'.ymmHi, s'.zmmHi) = (s.ymmHi, s.zmmHi) :=
  Exec.keep (fun s : State => (s.ymmHi, s.zmmHi)) (ok := fun i => writesUpper i = false)
    (fun {i s s'} hi he => by
      obtain ⟨a, b⟩ := (exec_keeps (i := i) (s := s) (s' := s') he).2 hi
      rw [a, b])
    (fun {i j s s₁ s₂ s'} _ hp hq hb => by
      have h₁ : s₁.ymmHi = s.ymmHi ∧ s₁.zmmHi = s.zmmHi := by
        cases i <;> simp only [isa, push, reduceCtorEq] at hp
        case push => split at hp <;> cases hp; exact pushRegs_uppers _ _
        case alloc => split at hp <;> cases hp; exact ⟨rfl, rfl⟩
      have h₂ : s'.ymmHi = s₂.ymmHi ∧ s'.zmmHi = s₂.zmmHi := by
        cases j <;> simp only [isa, pop, reduceCtorEq] at hq
        case pop => split at hq <;> cases hq; exact popReg_uppers _ _ _
        case free => split at hq <;> cases hq; exact ⟨rfl, rfl⟩
      simp only [Prod.mk.injEq] at hb ⊢
      exact ⟨h₂.1.trans (hb.1.trans h₁.1), h₂.2.trans (hb.2.trans h₁.2)⟩)
    hc
    (.inr fun s s₁ s₂ s' hc' hr hb => by
      simp only [isa, call, Option.some.injEq] at hc'; subst hc'
      simp only [isa, ret] at hr; split at hr <;> cases hr
      simpa [State.setReg] using hb)
    h

/-! ## The stack below the stack pointer -/

/-- A byte of one of the return addresses the state supplies. -/
def IsRa (s : State) (b : Byte) : Prop := ∃ j, ∃ k < 8, b = (s.unknowns j).extractLsb' (8 * k) 8

theorem IsRa.shift {s s' : State} {m : Nat} (hu : ∀ j, s'.unknowns j = s.unknowns (j + m)) {b : Byte}
    (h : IsRa s' b) : IsRa s b := by
  obtain ⟨j, k, hk, rfl⟩ := h
  exact ⟨j + m, k, hk, by rw [hu]⟩

/-- What code leaves in the `D` bytes below the stack pointer: what was
there, or bytes of its calls' return addresses; and it uses the unknowns in
order. -/
def StackRes (D : Nat) (s s' : State) : Prop :=
  (∃ m, ∀ j, s'.unknowns j = s.unknowns (j + m)) ∧
  ∀ x, (below (s.gpr .rsp) D).Contains x 1 → s'.mem x = s.mem x ∨ IsRa s (s'.mem x)

theorem StackRes.trans {D : Nat} {s s₂ s₃ : State} (hsp : s₂.gpr .rsp = s.gpr .rsp)
    (h₁ : StackRes D s s₂) (h₂ : StackRes D s₂ s₃) : StackRes D s s₃ := by
  obtain ⟨⟨m₁, u₁⟩, f₁⟩ := h₁
  obtain ⟨⟨m₂, u₂⟩, f₂⟩ := h₂
  refine ⟨⟨m₂ + m₁, fun j => by rw [u₂, u₁, Nat.add_assoc]⟩, fun x hx => ?_⟩
  rcases f₂ x (hsp ▸ hx) with e | r
  · rw [e]; exact f₁ x hx
  · exact .inr (r.shift u₁)

theorem contains_below_split {sp x : Addr} {D : Nat} (h8 : 8 ≤ D) (hD : D < 2 ^ 64)
    (hx : (below sp D).Contains x 1) :
    (⟨sp - 8, 8⟩ : Region).Contains x 1 ∨ (below (sp - 8) (D - 8)).Contains x 1 := by
  simp only [Region.Contains] at hx ⊢
  bv_omega

theorem slot_not_below {sp x : Addr} {n : Nat} (hn : n + 8 < 2 ^ 64)
    (hx : (⟨sp - 8, 8⟩ : Region).Contains x 1) : ¬ (below (sp - 8) n).Contains x 1 := by
  simp only [Region.Contains] at hx ⊢
  bv_omega

theorem slot_in_below {sp x : Addr} {D : Nat} (h8 : 8 ≤ D) (hD : D < 2 ^ 64)
    (hx : (⟨sp - 8, 8⟩ : Region).Contains x 1) : (below sp D).Contains x 1 := by
  simp only [Region.Contains] at hx ⊢
  bv_omega

theorem slot_byte {m : Mem} {sp x : Addr} {v : BitVec 64} (hx : (⟨sp - 8, 8⟩ : Region).Contains x 1) :
    ∃ k < 8, m.writeW (sp - 8) v x = v.extractLsb' (8 * k) 8 := by
  simp only [Region.Contains] at hx
  refine ⟨(x - (sp - 8)).toNat, by omega, ?_⟩
  simp only [Mem.writeW, Mem.write, show (x - (sp - 8)).toNat < 64 / 8 by omega, ite_true]
  rfl

theorem slot_other {m : Mem} {sp x : Addr} {v : BitVec 64} (hx : ¬ (⟨sp - 8, 8⟩ : Region).Contains x 1) :
    m.writeW (sp - 8) v x = m x := by
  simp only [Region.Contains] at hx
  exact Mem.write_apply (by omega)

/-- Code without frames leaves, in the `D` bytes below the stack pointer
(which its calls' return addresses fit in, and its writable regions do not
overlap), only what was there and bytes of its calls' return addresses. -/
theorem Exec.stackRes {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s')
    (hc : NoSp c) {D : Nat} (hd : 8 * c.depth ≤ D) (hD : D + 8 < 2 ^ 64)
    (hwr : ∀ r ∈ s.wr, ∀ x, (below (s.gpr .rsp) D).Contains x 1 → ¬ r.Contains x 1) :
    StackRes D s s' := by
  induction h generalizing D with
  | block h =>
    obtain ⟨-, -, f⟩ := execBlock_regions h
    refine ⟨⟨0, fun j => by rw [(execBlock_keeps h).1]; rfl⟩, fun x hx => .inl ?_⟩
    exact f x fun r hr => hwr r hr x hx
  | @seq c₁ c₂ _ s₂ _ _ _ h₁ _ ih₁ ih₂ =>
    have hc₁ : NoSp c₁ := fun i hi => hc i (List.mem_append_left _ hi)
    have hc₂ : NoSp c₂ := fun i hi => hc i (List.mem_append_right _ hi)
    simp only [Code.depth] at hd
    have hsp : s₂.gpr .rsp = _ := Exec.gpr hc₁ h₁
    have hw : s₂.wr = _ := (Exec.rdwr h₁).2
    exact StackRes.trans hsp (ih₁ hc₁ (by omega) hD hwr)
      (ih₂ hc₂ (by omega) hD (by rw [hw, hsp]; exact hwr))
  | iteT _ _ ih =>
    simp only [Code.depth] at hd
    exact ih (fun i hi => hc i (List.mem_append_left _ hi)) (by omega) hD hwr
  | iteF _ _ ih =>
    simp only [Code.depth] at hd
    exact ih (fun i hi => hc i (List.mem_append_right _ hi)) (by omega) hD hwr
  | loopExit _ _ ih => exact ih hc hd hD hwr
  | @loopNext body _ _ s₂ _ _ _ h₁ _ _ ih₁ ih₂ =>
    have hcb : NoSp body := hc
    have hsp : s₂.gpr .rsp = _ := Exec.gpr hcb h₁
    have hw : s₂.wr = _ := (Exec.rdwr h₁).2
    exact StackRes.trans hsp (ih₁ hc hd hD hwr) (ih₂ hc hd hD (by rw [hw, hsp]; exact hwr))
  | @frame i _ _ _ _ _ _ _ hp =>
    have hi := hc i (List.mem_cons_self ..)
    cases i <;> simp only [isa, push, reduceCtorEq] at hp
    all_goals simp [Taint.clobbers] at hi
  | @call _ b s₀ s₁ s₂ s₃ _ hc₁ hb hr ih =>
    simp only [Code.depth] at hd
    have e₁ : s₁ = s₀.callEntry := (Option.some.inj ((call_callEntry s₀).symm.trans hc₁)).symm
    subst e₁
    have e₃ : s₃ = s₂.setReg .rsp (s₂.gpr .rsp + 8) := by
      simp only [isa, ret] at hr; split at hr <;> cases hr; rfl
    subst e₃
    have hwr₁ : ∀ r ∈ s₀.callEntry.wr, ∀ x, (below (s₀.callEntry.gpr .rsp) (D - 8)).Contains x 1 →
        ¬ r.Contains x 1 := by
      intro r hr x hx
      simp only [State.callEntry_wr, State.callEntry_rsp] at hr hx
      exact hwr r hr x (by
        have := below_callee (s₀.gpr .rsp) (D - 8) x hx
        rwa [show D - 8 + 8 = D by omega] at this)
    obtain ⟨⟨m, u⟩, f⟩ := ih hc (D := D - 8) (by omega) (by omega) hwr₁
    have hu₁ : ∀ j, s₀.callEntry.unknowns j = s₀.unknowns (j + 1) := fun _ => rfl
    refine ⟨⟨m + 1, fun j => by
      show s₂.unknowns j = _
      rw [u, hu₁, Nat.add_assoc]⟩, fun x hx => ?_⟩
    show s₂.mem x = s₀.mem x ∨ IsRa s₀ (s₂.mem x)
    rcases contains_below_split (by omega) (by omega) hx with hs | hl
    · -- the return address's slot, which the callee does not write
      have fs := Exec.frameSp hb hc (by omega)
      have e : s₂.mem x = s₀.callEntry.mem x := fs x fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · exact hwr r hr x (slot_in_below (by omega) (by omega) hs)
        · simp only [List.mem_singleton] at hr; subst hr
          simp only [State.callEntry_rsp]
          exact slot_not_below (by omega) hs
      rw [e, State.callEntry_mem]
      obtain ⟨k, hk, hb'⟩ := slot_byte (m := s₀.mem) (v := s₀.unknowns 0) hs
      exact .inr ⟨0, k, hk, hb'⟩
    · have hx' : (below (s₀.callEntry.gpr .rsp) (D - 8)).Contains x 1 := by
        simpa only [State.callEntry_rsp] using hl
      have hns : ¬ (⟨s₀.gpr .rsp - 8, 8⟩ : Region).Contains x 1 := fun hs =>
        slot_not_below (n := D - 8) (by omega) hs hl
      rcases f x hx' with e | r
      · rw [e, State.callEntry_mem, slot_other hns]; exact .inl rfl
      · exact .inr (r.shift (m := 1) hu₁)

/-! ## Clearing the registers -/
def State.clearedV (xs : List XReg) (avx : Bool) (s : State) : State :=
  { s with
    xmm := fun x => if x ∈ xs then 0 else s.xmm x
    ymmHi := fun x => if avx ∧ x ∈ xs then 0 else s.ymmHi x
    zmmHi := fun x => if avx ∧ x ∈ xs then 0 else s.zmmHi x }

theorem execBlock_vecs (avx : Bool) (xs : List XReg) (s : State) :
    execBlock isa (xs.map (zeroVec avx)) s = some (s.clearedV xs avx, []) := by
  induction xs generalizing s with
  | nil => simp [execBlock, State.clearedV]
  | cons x xs ih =>
    cases avx
    all_goals
      simp only [List.map_cons, execBlock, zeroVec, isa, exec, ih, addrs, Bool.false_eq_true, ↓reduceIte, Option.map_some, List.map_nil, List.nil_append]
      simp only [State.clearedV, XOp.exec, VOp.exec, State.setXmm, State.setV, XBinOp.eval, VBinOp.sse, BitVec.xor_self, List.mem_cons, Option.some.injEq, Prod.mk.injEq, and_true]
      simp only [State.mk.injEq, true_and, and_true, Bool.false_eq_true, false_and, ite_false]
      first
        | (funext y; by_cases h1 : y = x <;> by_cases h2 : y ∈ xs <;> simp [h1, h2])
        | (refine ⟨?_, ?_, ?_⟩ <;> funext y <;> by_cases h1 : y = x <;> by_cases h2 : y ∈ xs <;>
          simp [h1, h2])

def State.clearedG (rs : List Reg) (s : State) : State :=
  { s with
    gpr := fun r => if r ∈ rs then 0 else s.gpr r
    cf := some false, of := some false, zf := some true, sf := some false }

theorem execBlock_gprs (rs : List Reg) (hrs : rs ≠ []) (s : State) :
    execBlock isa (rs.map zeroGpr) s = some (s.clearedG rs, []) := by
  induction rs generalizing s with
  | nil => exact absurd rfl hrs
  | cons r rs ih =>
    simp only [List.map_cons, execBlock, zeroGpr, isa, exec, addrs, srcAddrs, execAlu32, readSrc32,
      Option.bind_some, BitVec.xor_self, List.map_nil, List.nil_append]
    by_cases hn : rs = []
    · subst hn
      simp only [List.map_nil, execBlock, Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
      simp only [State.clearedG, arithFlags, State.setFlags, State.setReg32, State.setReg, List.mem_singleton]
      simp
    · rw [ih hn]
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
      simp only [State.clearedG, arithFlags, State.setFlags, State.setReg32, State.setReg, List.mem_cons]
      simp only [State.mk.injEq, and_true]
      funext y; by_cases h1 : y = r <;> by_cases h2 : y ∈ rs <;> simp [h1, h2]

/-- The state `clear rs avx` leaves. -/
abbrev State.cleared (rs : List Reg) (avx : Bool) (s : State) : State :=
  (s.clearedV xregs avx).clearedG rs

theorem execBlock_clear {rs : List Reg} (hrs : rs ≠ []) (avx : Bool) (s : State) :
    execBlock isa (clear rs avx) s = some (s.cleared rs avx, []) := by
  rw [clear, execBlock_append, execBlock_vecs]
  simp only [Option.bind_some, execBlock_gprs rs hrs, Option.map_some, List.append_nil]

theorem mem_xregs (x : XReg) : x ∈ xregs := by cases x <;> decide


theorem exec_clear_inv {c : Prog isa} {rs : List Reg} (hrs : rs ≠ []) {avx : Bool} {s s' : State}
    {t : List Leak} (h : Exec isa (.seq c (.block (clear rs avx))) s t s') :
    ∃ s₂, Exec isa c s t s₂ ∧ s' = s₂.cleared rs avx := by
  cases h with
  | seq h₁ h₂ =>
    rw [Exec.block_iff, execBlock_clear hrs] at h₂
    cases h₂
    exact ⟨_, by rwa [List.append_nil], rfl⟩

/-- The postcondition of a contract `Sig.contract` derives depends only on
the memory and on the result in `rax`, which `clear` keeps (if it is not one
of `rs`, or the function has no result). -/
theorem post_cleared {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {n : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {rs : List Reg} (avx : Bool)
    (hret : Reg.rax ∉ rs ∨ sig.ret = none) {s s' : State}
    (h : (sig.contract abi pre post wa n leak).post s s') :
    (sig.contract abi pre post wa n leak).post s (s'.cleared rs avx) := by
  have e : ((s'.cleared rs avx).gpr .rax).setWidth (sig.retBits abi.ptrBits) =
      (s'.gpr .rax).setWidth (sig.retBits abi.ptrBits) := by
    rcases hret with hr | hr
    · simp [State.cleared, State.clearedG, State.clearedV, hr]
    · exact BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_setWidth, Sig.retBits, hr, Nat.pow_zero, Nat.mod_one])
  simp only [Sig.contract] at h ⊢
  exact e ▸ h

/-- Running `clear rs avx` after `c`, which keeps the calling convention's
obligations if `rs` has no callee-saved register. -/
theorem run_clear {c : Prog isa} {rs : List Reg} (hrs : rs ≠ []) (hsaved : ∀ r ∈ rs, r ∉ calleeSaved)
    (avx : Bool) {s s' : State} {t : List Leak} (he : Exec isa c s t s') (ha : abiPreserved s s') :
    Exec isa (.seq c (.block (clear rs avx))) s (t ++ []) (s'.cleared rs avx) ∧
      abiPreserved s (s'.cleared rs avx) := by
  obtain ⟨hg, hm, hx⟩ := ha
  refine ⟨.seq he (.block (execBlock_clear hrs avx s')), fun r hr => ?_, hm, hx⟩
  have : r ∉ rs := fun h => hsaved r h hr
  simp only [State.cleared, State.clearedG, this, ite_false, State.clearedV]
  exact hg r hr

/-- Code `c`, then `clear rs avx` (which must not clear a callee-saved
register): verified against the contract `c` is, given what `c` leaves (`R`,
proven with its correctness), and leaving no residue if `R` and the clearing
imply it. -/
theorem Verified.clear {c : Prog isa} {k : Contract isa} {sig : Sig} {n : Nat} {rs : List Reg}
    {avx : Bool} (hrs : rs ≠ []) (hsaved : ∀ r ∈ rs, r ∉ calleeSaved) (R : State → State → Prop)
    (hc : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s' ∧ R s s')
    (hct : ConstantTime isa k.pre k.pub c) (hsat : ∃ s, k.pre s)
    (hpost : ∀ s s', k.post s s' → k.post s (s'.cleared rs avx))
    (hres : ∀ s s', k.pre s → R s s' → noResidue sig n s (s'.cleared rs avx)) :
    Verified target (.seq c (.block (clear rs avx))) k ∧
      ∀ s t s', k.pre s → Exec isa (.seq c (.block (clear rs avx))) s t s' → noResidue sig n s s' := by
  refine ⟨⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩, fun s t s' hs he => ?_⟩
  · obtain ⟨t, s', he, ha, hp, -⟩ := hc s hs
    obtain ⟨he', ha'⟩ := run_clear hrs hsaved avx he ha
    exact ⟨_, _, he', ha', hpost s s' hp⟩
  · obtain ⟨_, e₁, -⟩ := exec_clear_inv hrs e₁
    obtain ⟨_, e₂, -⟩ := exec_clear_inv hrs e₂
    exact hct s₁ s₂ t₁ t₂ _ _ h₁ h₂ hp e₁ e₂
  · obtain ⟨s₂, e, rfl⟩ := exec_clear_inv hrs he
    obtain ⟨_, s₃, e', -, -, hR⟩ := hc s hs
    rw [(Exec.det e e').2]
    exact hres s s₃ hs hR

/-! ## The residue after `clear` -/

theorem cleared_gpr {rs : List Reg} {r : Reg} (h : r ∉ rs) (avx : Bool) (s : State) :
    (s.cleared rs avx).gpr r = s.gpr r := by
  simp only [State.cleared, State.clearedG, h, ite_false, State.clearedV]


def allRegs : List Reg :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem mem_allRegs (r : Reg) : r ∈ allRegs := by cases r <;> decide

/-- Every caller-saved register (but `rax` if it holds the result) is
cleared (`rs`) or kept holding the pointer argument passed in the `i`-th
argument register (`kept`). -/
def covers (sig : Sig) (rs : List Reg) (kept : List (Reg × Nat)) : Bool :=
  allRegs.all fun r => calleeSaved.contains r || (r == .rax && sig.ret.isSome) || rs.contains r ||
    kept.any fun p => p.1 == r && decide (p.2 < argRegs.length) && (sig.words 64)[p.2]? == some .addr

theorem StackRes.below {n : Nat} {s s' : State} (h : StackRes n s s') (i : Nat)
    (hi : i < n) :
    s'.mem (s.gpr .rsp - BitVec.ofNat 64 (i + 1)) = s.mem (s.gpr .rsp - BitVec.ofNat 64 (i + 1)) ∨
      ∃ j, ∃ k < 8, s'.mem (s.gpr .rsp - BitVec.ofNat 64 (i + 1)) = (s.unknowns j).extractLsb' (8 * k) 8 :=
  h.2 _ (by simp only [Region.Contains]; bv_omega)

/-- What `clear rs avx` leaves after code that keeps the registers `kept`
(and, unless `avx`, the upper halves of the vector registers) and leaves
`stack` below the stack pointer: no residue, if `covers sig rs kept`. -/
theorem noResidue_cleared {sig : Sig} {n : Nat} {rs : List Reg} {avx : Bool} {s s₂ : State}
    (kept : List (Reg × Nat)) (hcov : covers sig rs kept = true)
    (hk : ∀ p ∈ kept, s₂.gpr p.1 = s.gpr (argRegs.getD p.2 .rax))
    (hup : avx = false → s₂.ymmHi = s.ymmHi ∧ s₂.zmmHi = s.zmmHi)
    (hst : ∀ i < n, s₂.mem (s.gpr .rsp - BitVec.ofNat 64 (i + 1)) = s.mem (s.gpr .rsp - BitVec.ofNat 64 (i + 1)) ∨
      ∃ j, ∃ k < 8, s₂.mem (s.gpr .rsp - BitVec.ofNat 64 (i + 1)) = (s.unknowns j).extractLsb' (8 * k) 8) :
    noResidue sig n s (s₂.cleared rs avx) := by
  refine ⟨fun r hr hrax => ?_, rfl, rfl, rfl, rfl, fun x => ?_, hst⟩
  · have h := List.all_eq_true.mp hcov r (mem_allRegs r)
    simp only [Bool.or_eq_true, List.contains_iff_mem, Bool.and_eq_true, beq_iff_eq, List.any_eq_true,
      decide_eq_true_eq] at h
    rcases h with ((hc | ⟨hra, hret⟩) | hrs) | ⟨p, hp, ⟨hpr, hlt⟩, hw⟩
    · exact absurd hc hr
    · simp [hrax hra] at hret
    · left; simp [State.cleared, State.clearedG, hrs]
    · subst hpr
      by_cases hrs : p.1 ∈ rs
      · left; simp [State.cleared, State.clearedG, hrs]
      · right
        refine ⟨p.2, hlt, hw, ?_⟩
        simp only [State.cleared, State.clearedG, hrs, ite_false, State.clearedV]
        rw [hk p hp, List.getD_eq_getElem?_getD]
  · refine ⟨.inl (by simp [State.cleared, State.clearedG, State.clearedV, mem_xregs]), ?_, ?_⟩ <;>
    cases avx
    · exact .inr (by simp [State.cleared, State.clearedG, State.clearedV, (hup rfl).1])
    · exact .inl (by simp [State.cleared, State.clearedG, State.clearedV, mem_xregs])
    · exact .inr (by simp [State.cleared, State.clearedG, State.clearedV, (hup rfl).2])
    · exact .inl (by simp [State.cleared, State.clearedG, State.clearedV, mem_xregs])

end VG.X86_64
