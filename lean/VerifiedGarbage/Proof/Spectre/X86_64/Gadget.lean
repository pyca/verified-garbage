import VerifiedGarbage.Proof.Framework.X86_64.Spectre

/-!
# Spectre v1: a bounds-check-bypass gadget and safe examples (x86-64)

`gadget` is Kocher et al.'s variant 1 example,
`if (i < len) { y = b[a[i]]; }`:

```
cmp   rsi, rdx              ; i < len?
jae   skip
movzx eax, byte [rdi + rsi] ; a[i]
movzx r8d, byte [rcx + rax] ; b[a[i]]
skip:
```

* `gadget_ct`: it is constant time sequentially, when `a[0..len)` is public.
* `gadget_not_sct`: it is not speculatively constant time: a misprediction
  reads a secret byte past `a`, and leaks it through the address of the
  load from `b`.
* `gadget_rejected`: so no hint makes the taint check succeed (by
  `Taint.specConstantTime`), and the analysis indeed fails on it.
* `copy_sct`, `copyLoop_sct`: a branch-free copy and a copy loop with a
  public count are accepted, hence speculatively constant time.
-/

namespace VG.Proof.SpectreDemo

open VG.X86_64 VG.X86_64.Spectre

def gadget : Prog isa :=
  .seq (.block [.alu .cmp .rsi (.reg .rdx)])
    (.ite .b (.block [.movzx8 .rax ⟨.rdi, some .rsi, 1, 0⟩, .movzx8 .r8 ⟨.rcx, some .rax, 1, 0⟩])
      (.block []))

/-- `a` (`rdi`, `len = rdx` bytes) and `b` (`rcx`, 256 bytes) are readable. -/
def Pre (s : State) : Prop :=
  s.rd = [⟨s.gpr .rdi, (s.gpr .rdx).toNat⟩, ⟨s.gpr .rcx, 256⟩]

/-- The pointers, the index, the length and the contents of `a` are public. -/
def Pub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧
    ∀ k : Nat, k < (s₁.gpr .rdx).toNat →
      s₁.mem (s₁.gpr .rdi + BitVec.ofNat 64 k) = s₂.mem (s₂.gpr .rdi + BitVec.ofNat 64 k)

/-! ## Sequential constant time -/

theorem execBlock_two {i j : Instr} {s s' : State} {t : List Leak}
    (h : execBlock isa [i, j] s = some (s', t)) :
    ∃ s₁, exec i s = some s₁ ∧ t = (addrs i s).map .addr ++ (addrs j s₁).map .addr := by
  simp only [execBlock] at h
  split at h
  · cases h
  rename_i s₁ e
  refine ⟨s₁, e, ?_⟩
  split at h
  · cases h
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, List.append_nil] at h
  exact h.2.symm

theorem movzx8_gpr {d : Reg} {m : MemOp} {s s₁ : State} (h : exec (.movzx8 d m) s = some s₁) :
    s₁.gpr d = (s.mem (s.ea m)).setWidth 64 := by
  simp only [exec, State.load8] at h
  split at h
  · simp only [Option.map_some, Option.some.injEq] at h
    subst h; simp [State.setReg]
  · cases h

theorem movzx8_other {d r : Reg} {m : MemOp} {s s₁ : State} (h : exec (.movzx8 d m) s = some s₁)
    (hr : r ≠ d) : s₁.gpr r = s.gpr r := by
  simp only [exec, State.load8] at h
  split at h
  · simp only [Option.map_some, Option.some.injEq] at h
    subst h; simp [State.setReg, hr]
  · cases h

/-- Sequentially, the gadget is constant time: the index is in bounds
whenever `a[i]` is loaded. -/
theorem gadget_ct : ConstantTime isa Pre Pub gadget := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨hdi, hsi, hdx, hcx, hm⟩ := hp
  cases e₁ with | seq a₁ b₁ => cases e₂ with | seq a₂ b₂ =>
  cases a₁ with | block x₁ => cases a₂ with | block x₂ =>
  simp only [execBlock, isa, exec, execAlu, readSrc, Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at x₁ x₂
  obtain ⟨hs₁, rfl⟩ := x₁
  obtain ⟨hs₂, rfl⟩ := x₂
  cases b₁ with
  | iteT c₁ x₁ =>
    cases b₂ with
    | iteF c₂ _ =>
      subst hs₁ hs₂
      simp only [eval, arithFlags, State.setFlags, Option.some.injEq, decide_eq_true_eq, decide_eq_false_iff_not, hsi, hdx] at c₁ c₂
      exact absurd c₁ c₂
    | iteT c₂ x₂ =>
      cases x₁ with | block x₁ => cases x₂ with | block x₂ =>
      subst hs₁ hs₂
      simp only [eval, arithFlags, State.setFlags, Option.some.injEq, decide_eq_true_eq] at c₁
      obtain ⟨u₁, e₁, rfl⟩ := execBlock_two x₁
      obtain ⟨u₂, e₂, rfl⟩ := execBlock_two x₂
      have g₁ := movzx8_gpr e₁
      have g₂ := movzx8_gpr e₂
      have r₁ := movzx8_other e₁ (r := .rcx) (by decide)
      have r₂ := movzx8_other e₂ (r := .rcx) (by decide)
      have hk := hm (s₁.gpr .rsi).toNat c₁
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, hdi, hsi] at hk
      simp only [arithFlags, State.setFlags, State.ea] at g₁ g₂ r₁ r₂ ⊢
      simp [addrs, srcAddrs, State.ea, g₁, g₂, r₁, r₂, hdi, hsi, hcx, hk]
  | iteF c₁ x₁ =>
    cases b₂ with
    | iteT c₂ _ =>
      subst hs₁ hs₂
      simp only [eval, arithFlags, State.setFlags, Option.some.injEq, decide_eq_true_eq, decide_eq_false_iff_not, hsi, hdx] at c₁ c₂
      exact absurd c₂ c₁
    | iteF c₂ x₂ =>
      cases x₁ with | block x₁ => cases x₂ with | block x₂ =>
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at x₁ x₂
      rw [← x₁.2, ← x₂.2]; rfl

/-! ## The counterexample -/

def s₀ (m : Mem) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 1 | .rdx => 1 | .rcx => 0x2000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := m
  rd := [⟨0x1000, 1⟩, ⟨0x2000, 256⟩]
  wr := []

/-- Memory past the end of `a` (at `a + 1`) holds a secret: 0 in one run, 1 in the other. -/
def secret (v : Byte) : Mem := fun x => if x = 0x1001 then v else 0

theorem gadget_not_sct : ¬ SpecConstantTime spectre Pre Pub gadget := by
  intro h
  have := h (s₀ (secret 0)) (s₀ (secret 1)) [true] 3 _ _ _ _ rfl rfl
    ⟨rfl, rfl, rfl, rfl, fun k hk => by
      have : k = 0 := by simp [s₀] at hk; omega
      subst this; rfl⟩
    (.seq (.blockDone (.cons rfl .nil)) (.iteT (.blockDone (.cons rfl (.cons rfl .nil)))))
    (.seq (.blockDone (.cons rfl .nil)) (.iteT (.blockDone (.cons rfl (.cons rfl .nil)))))
  revert this
  decide +kernel

/-- The analysis cannot certify the gadget, whatever the hint. -/
theorem gadget_rejected (hc : Taint.Hint taint.T) :
    (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) gadget hc).isSome = false := by
  cases h : (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) gadget hc).isSome
  · rfl
  · exact absurd (Taint.specConstantTime specSound (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx])
      (fun _ _ _ _ ⟨h1, h2, h3, h4, _⟩ => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) h) gadget_not_sct

/-- And the analysis does fail on it (the hint search finds nothing). -/
theorem gadget_hint_fails : Taint.hint taint (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) gadget = none := by
  decide +kernel

/-! ## Spectre v1.1: a transient out-of-bounds store

`gadget11` stores a public value (`r9`) at `[r10]`, then, if `i < len`,
`a[i] = x` with a secret `x` (`r11`), then reads `[r10]` back and loads
`b[[r10]]`. Transiently, with `i` out of bounds, `a + i = r10`: the secret
reaches the address of the last load through the store buffer. -/

def gadget11 : Prog isa :=
  .seq (.block [.store ⟨.r10, none, 1, 0⟩ .r9, .alu .cmp .rsi (.reg .rdx)])
    (.seq (.ite .b (.block [.store8 ⟨.rdi, some .rsi, 1, 0⟩ .r11]) (.block []))
      (.block [.movzx8 .rax ⟨.r10, none, 1, 0⟩, .movzx8 .r8 ⟨.rcx, some .rax, 1, 0⟩]))

/-- Everything but `r11` (and memory) is public. -/
def Pub11 (s₁ s₂ : State) : Prop :=
  ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r9, .r10], s₁.gpr r = s₂.gpr r

def t₀ (x : BitVec 64) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 1 | .rcx => 0x2000 | .r10 => 0x3000
    | .r11 => x | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 256⟩]
  wr := [⟨0x1000, 1⟩, ⟨0x3000, 8⟩]

theorem gadget11_not_sct : ¬ SpecConstantTime spectre (fun _ => True) Pub11 gadget11 := by
  intro h
  have := h (t₀ 0) (t₀ 1) [true] 5 _ _ _ _ trivial trivial (by simp [Pub11, t₀])
    (.seq (.blockDone (.cons rfl (.cons rfl .nil)))
      (.seq (.iteT (.blockDone (.cons rfl .nil))) (.blockDone (.cons rfl (.cons rfl .nil)))))
    (.seq (.blockDone (.cons rfl (.cons rfl .nil)))
      (.seq (.iteT (.blockDone (.cons rfl .nil))) (.blockDone (.cons rfl (.cons rfl .nil)))))
  revert this
  decide +kernel

/-! ## Safe examples -/

/-- `out[0] = a[i]`, branch-free. -/
def copy : Prog isa :=
  .block [.movzx8 .rax ⟨.rdi, some .rsi, 1, 0⟩, .store8 ⟨.rcx, none, 1, 0⟩ .rax]

theorem copy_sct : SpecConstantTime spectre (fun _ => True)
    (fun s₁ s₂ => ∀ r ∈ [Reg.rdi, .rsi, .rcx], s₁.gpr r = s₂.gpr r) copy :=
  Taint.specConstantTime specSound (Taint.ofRegs [.rdi, .rsi, .rcx])
    (fun _ _ _ _ hp => Taint.agree_ofRegs hp) (by taint_decide)

/-- `do { *out++ = *in++; } while (--n != 0)`: a loop on a public count. -/
def copyLoop : Prog isa :=
  .loop (.block [.movzx8 .rax ⟨.rdi, none, 1, 0⟩, .store8 ⟨.rcx, none, 1, 0⟩ .rax,
    .alu .add .rdi (.imm 1), .alu .add .rcx (.imm 1), .alu .sub .rdx (.imm 1)]) .ne

theorem copyLoop_sct : SpecConstantTime spectre (fun _ => True)
    (fun s₁ s₂ => ∀ r ∈ [Reg.rdi, .rcx, .rdx], s₁.gpr r = s₂.gpr r) copyLoop :=
  Taint.specConstantTime specSound (Taint.ofRegs [.rdi, .rcx, .rdx])
    (fun _ _ _ _ hp => Taint.agree_ofRegs hp) (by taint_decide)

end VG.Proof.SpectreDemo
