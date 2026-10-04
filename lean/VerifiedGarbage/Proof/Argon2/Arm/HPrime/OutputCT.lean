import VerifiedGarbage.Proof.Argon2.Arm.HPrime.Finish
import VerifiedGarbage.Proof.Argon2.Arm.HPrime.CallsCT

/-!
# Argon2 H′ on ARMv7: the output, in two runs

Two runs of H′ with the same public data (`Same`: the stack pointer and the
arguments) write their output through the same addresses (`copy_rel`,
`emit_rel`, `copyRemaining_rel`, from states with the same number of output
bytes written), take the same branches (the output length decides them) and
the same number of chain iterations: `finishOutput_rel`.
-/

namespace VG.Proof.Argon2.Arm.HPrime

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Argon2.Arm.HPrime (copy copyLoop emitPrefix copyRemaining next cmpLeft chain extendDigest
  finishOutput)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add op2_reg op2_imm)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

/-- The public data of two runs. -/
structure Same (s₀ s₀' : State) : Prop where
  sp : sp₀ s₀' = sp₀ s₀
  r0 : s₀'.gpr .r0 = s₀.gpr .r0
  r1 : s₀'.gpr .r1 = s₀.gpr .r1
  r2 : s₀'.gpr .r2 = s₀.gpr .r2
  r3 : s₀'.gpr .r3 = s₀.gpr .r3
  scr : scr s₀' = scr s₀

theorem Same.of_pub {s₀ s₀' : State} (h : hPrimeArm.pub s₀ s₀') : Same s₀ s₀' :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.1.symm, h.2.2.2.2.2.symm⟩

theorem Same.ol_eq {s₀ s₀' : State} (q : Same s₀ s₀') : ol s₀' = ol s₀ := by
  show (s₀'.gpr .r3).toNat = (s₀.gpr .r3).toNat; rw [q.r3]

theorem Same.inl_eq {s₀ s₀' : State} (q : Same s₀ s₀') : inl s₀' = inl s₀ := by
  show (s₀'.gpr .r1).toNat = (s₀.gpr .r1).toNat; rw [q.r1]

/-- A register write outside `kept` keeps what the hash macros keep. -/
theorem keeps_upd {B SP : BitVec 32} {s t : State} {d : Reg} {v : BitVec 32} (u : Upd s t d v)
    (hd : d ∉ kept) : Keeps B SP s t :=
  Keeps.same (fun r hr => u.other r fun h => hd (h ▸ hr)) u.sp u.mem u.rd u.wr

/-- Two runs agree on the registers the body keeps. -/
theorem agree_body {s₀ s₀' : State} (q : Same s₀ s₀') {t₁ t₂ : State} (b₁ : Body s₀ t₁)
    (b₂ : Body s₀' t₂) : ∀ r ∈ [Reg.r4, .r5, .r6], t₁.gpr r = t₂.gpr r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [b₁.r4, b₂.r4, q.scr]
  · rw [b₁.r5, b₂.r5]; exact q.r0.symm
  · rw [b₁.r6, b₂.r6, q.r1]

/-- The code taint checks from nothing public, in two runs. -/
theorem rel_none {P : State → State → Prop} {c : Prog isa}
    (hc : ∃ hc, (VG.Taint.check taint (Taint.ofRegs []) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs fun _ h => nomatch h) hc

theorem rel_nil {P Q : State → State → Prop} (h : ∀ x y, P x y → Q x y) : RelCT isa P (.block []) Q :=
  ((rel_none (P := P) ⟨_, by taint_decide⟩).wpDep (F := fun s t => t = s)
    fun _ _ _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩).mono (fun _ _ h => h)
    fun _ _ ⟨_, _, _, hp, e₁, e₂⟩ => e₁ ▸ e₂ ▸ h _ _ hp

/-- `eval .ne`, from `eval .eq`. -/
theorem ne_of_eq {t : State} {p : Prop} [Decidable p] (h : isa.eval .eq t = some (decide p)) :
    isa.eval .ne t = some (!decide p) := by
  have h' : VG.Arm.eval .eq t = _ := h
  rw [MdStream.Arm.eval_eq, Option.some.injEq] at h'
  show VG.Arm.eval .ne t = _
  rw [MdStream.Arm.eval_ne, h']

/-! ## `copy` -/

/-- What `copy` needs: the body, `k` bytes of output written, and `n` to copy. -/
def CopyIn (s₀ : State) (k n : Nat) (s : State) : Prop :=
  Body s₀ s ∧ s.gpr .r7 = op s₀ + BitVec.ofNat 32 k ∧ s.gpr .r10 = BitVec.ofNat 32 n

/-- The registers of the copy loop. -/
def CopyRegs (s₀ : State) (k n : Nat) (t : State) : Prop :=
  t.gpr .r9 = scr s₀ + 768 ∧ t.gpr .r7 = op s₀ + BitVec.ofNat 32 k ∧ t.gpr .r10 = BitVec.ofNat 32 n

theorem copy_blk {s₀ : State} {k n : Nat} {s : State} (h : CopyIn s₀ k n s) :
    WP isa (.block [.dp .add .r9 .r4 (.imm 768)]) s (CopyRegs s₀ k n) := by
  obtain ⟨b, hk, hn⟩ := h
  exact wp_add (op2_imm (by decide)) fun s₁ u₁ => WP.block_nil
    ⟨by rw [u₁.gpr, b.r4], by rw [u₁.other _ (by decide), hk], by rw [u₁.other _ (by decide), hn]⟩

theorem copy_rel {s₀ s₀' : State} (q : Same s₀ s₀') {k n : Nat} :
    RelCT isa (fun t₁ t₂ => CopyIn s₀ k n t₁ ∧ CopyIn s₀' k n t₂) copy fun _ _ => True := by
  unfold copy
  refine RelCT.seq (rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => copy_blk h) (fun _ h => copy_blk h)) ?_
  exact RelCT.taint (A := taint) (Taint.ofRegs [.r9, .r7, .r10])
    (fun t₁ t₂ ⟨⟨a₁, b₁, c₁⟩, ⟨a₂, b₂, c₂⟩⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a₁, a₂, q.scr]
      · rw [b₁, b₂]; exact congrArg (· + _) q.r2.symm
      · rw [c₁, c₂]) (by taint_decide)

/-- The body, with `L` output bytes written. -/
def OutAt (s₀ : State) (L : Nat) (s : State) : Prop :=
  Body s₀ s ∧ ∃ xs, Out s₀ s xs ∧ xs.length = L

theorem emit_blk {s₀ : State} {L : Nat} {s : State} (h : OutAt s₀ L s) :
    WP isa (.block [.mov .r10 (.imm 32)]) s (CopyIn s₀ L 32) := by
  obtain ⟨b, xs, o, hx⟩ := h
  exact wp_mov (op2_imm (by decide)) fun s₁ u₁ => WP.block_nil
    ⟨b.upd u₁ (by decide) (by decide) (by decide), by rw [u₁.other _ (by decide), o.ptr, hx], u₁.gpr⟩

theorem emit_rel {s₀ s₀' : State} (q : Same s₀ s₀') {L : Nat} :
    RelCT isa (fun t₁ t₂ => OutAt s₀ L t₁ ∧ OutAt s₀' L t₂) emitPrefix fun _ _ => True := by
  unfold emitPrefix
  exact RelCT.seq (rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => emit_blk h) (fun _ h => emit_blk h))
    (RelCT.seq (copy_rel q) (rel_none ⟨_, by taint_decide⟩))

theorem rem_blk {s₀ : State} {L : Nat} {s : State} (h : OutAt s₀ L s) :
    WP isa (.block [.mov .r10 (.reg .r8)]) s (CopyIn s₀ L (ol s₀ - L)) := by
  obtain ⟨b, xs, o, hx⟩ := h
  exact wp_mov (op2_reg _ _) fun s₁ u₁ => WP.block_nil
    ⟨b.upd u₁ (by decide) (by decide) (by decide), by rw [u₁.other _ (by decide), o.ptr, hx],
      by rw [u₁.gpr, o.left, hx]⟩

theorem copyRemaining_rel {s₀ s₀' : State} (q : Same s₀ s₀') {L : Nat} :
    RelCT isa (fun t₁ t₂ => OutAt s₀ L t₁ ∧ OutAt s₀' L t₂) copyRemaining fun _ _ => True := by
  unfold copyRemaining
  refine RelCT.seq (rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => rem_blk h) (fun _ h => rem_blk h)) ?_
  rw [q.ol_eq]
  exact copy_rel q

/-! ## The chain -/

/-- `ChainInv`, for some digest `V` and `r11`. -/
def ChainAt (s₀ : State) (j : Nat) (s : State) : Prop :=
  ∃ (V : List Byte) (e : BitVec 32), V.length = 64 ∧ ChainInv s₀ e V j s

theorem ChainAt.outAt {s₀ : State} {j : Nat} {s : State} (h : ChainAt s₀ j s) :
    OutAt s₀ (32 + 32 * j) s :=
  let ⟨_, _, hV, i⟩ := h
  ⟨i.body, _, i.out, chainOut_length hV j⟩

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (q : Same s₀ s₀')

include hp in
theorem OutAt.keeps {L : Nat} {s t : State} (h : OutAt s₀ L s) (k : Keeps (scr s₀) (sp₀ s₀) s t) :
    OutAt s₀ L t :=
  let ⟨b, xs, o, hx⟩ := h
  ⟨b.keeps hp k, xs, o.keeps hp k, hx⟩

include hp in
theorem next_out_ok {n L : Nat} (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) {s : State}
    (h : InitIn (scr s₀) (sp₀ s₀) n s ∧ OutAt s₀ L s) : WP isa next s (OutAt s₀ L) := by
  obtain ⟨⟨c, e⟩, o⟩ := h
  exact (next_ok c e hn₁ hn₂).mono fun t ⟨_, k⟩ => o.keeps hp k

include hp hp' q in
theorem next_out_rel {n L : Nat} (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    RelCT isa (fun t₁ t₂ => (InitIn (scr s₀) (sp₀ s₀) n t₁ ∧ OutAt s₀ L t₁) ∧
      (InitIn (scr s₀) (sp₀ s₀) n t₂ ∧ OutAt s₀' L t₂)) next
      fun t₁ t₂ => OutAt s₀ L t₁ ∧ OutAt s₀' L t₂ :=
  rel_wp ((next_rel hn₁ hn₂).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h)
    (fun _ h => next_out_ok hp hn₁ hn₂ h)
    (fun _ h => next_out_ok hp' hn₁ hn₂ ⟨by rw [q.scr, q.sp]; exact h.1, h.2⟩)

include hp in
/-- Setting `r1` keeps the body and the output. -/
theorem r1_blk {L n : Nat} (hn : encodable (BitVec.ofNat 32 n) = true) {s : State} (h : OutAt s₀ L s) :
    WP isa (.block [.mov .r1 (.imm (BitVec.ofNat 32 n))]) s fun t =>
      InitIn (scr s₀) (sp₀ s₀) n t ∧ OutAt s₀ L t := by
  refine wp_mov (op2_imm hn) fun s₁ u₁ => WP.block_nil ?_
  have o₁ := h.keeps hp (keeps_upd u₁ (by decide))
  exact ⟨⟨o₁.1.ctx hp, u₁.gpr⟩, o₁⟩

include hp hp' q in
/-- One iteration of the chain. -/
theorem body_rel {j : Nat} :
    RelCT isa (fun t₁ t₂ => ChainAt s₀ j t₁ ∧ ChainAt s₀' j t₂)
      (.seq (.block [.mov .r1 (.imm 64)]) (.seq next (.seq emitPrefix (.block cmpLeft))))
      fun _ _ => True := by
  refine RelCT.seq (rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => r1_blk (n := 64) hp (by decide) h.outAt)
    (fun _ h => (r1_blk (n := 64) hp' (by decide) h.outAt).mono fun _ h =>
      ⟨by rw [← q.scr, ← q.sp]; exact h.1, h.2⟩))
    (RelCT.seq (next_out_rel hp hp' q (by decide) (by decide))
      (RelCT.seq (emit_rel q) (rel_none ⟨_, by taint_decide⟩)))

/-- What the chain leaves: `j` iterations, and 33 to 64 bytes left. -/
def ChainDone (s₀ s₀' : State) (t₁ t₂ : State) : Prop :=
  ∃ j, ChainAt s₀ j t₁ ∧ ChainAt s₀' j t₂ ∧ 33 ≤ ol s₀ - (32 + 32 * j) ∧
    ol s₀ - (32 + 32 * j) ≤ 64 ∧ 32 + 32 * j ≤ ol s₀

include hp hp' q in
theorem chain_rel :
    RelCT isa (fun t₁ t₂ => ∃ j, 65 ≤ ol s₀ - (32 + 32 * j) ∧ ChainAt s₀ j t₁ ∧ ChainAt s₀' j t₂)
      chain (ChainDone s₀ s₀') := by
  have ho := q.ol_eq
  refine fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨j, h65, h₁, h₂⟩ e₁ e₂ =>
    RelCT.loop (M := isa) (Q := ChainDone s₀ s₀')
      (fun m t₁ t₂ => ∃ j, m = ol s₀ - (32 + 32 * j) ∧ 65 ≤ m ∧ ChainAt s₀ j t₁ ∧ ChainAt s₀' j t₂)
      (fun m => ?_) _ s₁ s₂ t₁ t₂ s₁' s₂' ⟨j, rfl, h65, h₁, h₂⟩ e₁ e₂
  refine RelCT.of_pre fun _ _ ⟨j, hm, h65, _, _⟩ => ?_
  subst hm
  have it := (body_rel hp hp' q (j := j)).wp
    (F₁ := fun (t : State) => ChainAt s₀ (j + 1) t ∧
      isa.eval .eq t = some (decide (ol s₀ - (32 + 32 * (j + 1)) ≤ 64)))
    (F₂ := fun (t : State) => ChainAt s₀' (j + 1) t ∧
      isa.eval .eq t = some (decide (ol s₀' - (32 + 32 * (j + 1)) ≤ 64)))
    fun t₁ t₂ ⟨⟨V, e, hV, i₁⟩, ⟨V', e', hV', i₂⟩⟩ =>
      ⟨(iter_ok hp hV i₁ (by omega) (by omega)).mono fun _ h => ⟨⟨V, e, hV, h.1⟩, h.2⟩,
       (iter_ok hp' hV' i₂ (by omega) (by omega)).mono fun _ h => ⟨⟨V', e', hV', h.1⟩, h.2⟩⟩
  refine it.mono (fun t₁ t₂ ⟨j', hj, _, a₁, a₂⟩ => ?_) fun t₁ t₂ ⟨_, ⟨c₁, f₁⟩, ⟨c₂, f₂⟩⟩ => ?_
  · have : j' = j := by omega
    subst this; exact ⟨a₁, a₂⟩
  · rw [ho] at f₂
    have n₁ := ne_of_eq f₁
    have n₂ := ne_of_eq f₂
    refine ⟨by rw [n₁, n₂], fun hf => ?_, fun ht => ?_⟩
    · rw [n₁] at hf
      have : ol s₀ - (32 + 32 * (j + 1)) ≤ 64 := by simpa using hf
      exact ⟨j + 1, c₁, c₂, by omega, by omega, by omega⟩
    · rw [n₁] at ht
      have : ¬ ol s₀ - (32 + 32 * (j + 1)) ≤ 64 := by simpa using ht
      exact ⟨_, by omega, j + 1, rfl, by omega, c₁, c₂⟩

/-! ## Extending the digest -/

/-- The state `finishOutput` starts from. -/
def ExtIn (s₀ s : State) : Prop := Body s₀ s ∧ Out s₀ s []

include hp in
theorem ext_emit {s : State} (h : ExtIn s₀ s) (hol : 32 ≤ ol s₀) :
    WP isa emitPrefix s (ChainAt s₀ 0) := by
  obtain ⟨b, o⟩ := h
  refine (emit_ok hp b o (by simp only [List.length_nil]; omega)).mono fun t ⟨bt, et, ot, dt⟩ =>
    ⟨digest s₀ s, s.gpr .r11, by simp [digest, bytesAt], bt, et, ?_, dt⟩
  rw [List.nil_append] at ot
  simpa [chainOut, chainPrefixes] using ot

include hp in
theorem ChainAt.keeps {j : Nat} {s t : State} (h : ChainAt s₀ j s)
    (k : Keeps (scr s₀) (sp₀ s₀) s t) (m : t.mem = s.mem) : ChainAt s₀ j t :=
  let ⟨V, e, hV, i⟩ := h
  ⟨V, e, hV, i.body.keeps hp k, (k.gpr _ (by decide)).trans i.r11, i.out.keeps hp k,
    by show bytesAt _ _ _ = _; rw [m]; exact i.digest⟩

include hp in
theorem chain_cmp {j : Nat} (hl : 32 + 32 * j < ol s₀) {s : State} (h : ChainAt s₀ j s) :
    WP isa (.block cmpLeft) s fun t => ChainAt s₀ j t ∧
      isa.eval .eq t = some (decide (ol s₀ - (32 + 32 * j) ≤ 64)) := by
  obtain ⟨V, e, hV, i⟩ := h
  refine (cmp_ok i.out (by rw [chainOut_length hV]; exact hl)).mono fun t ⟨cf, k, m⟩ =>
    ⟨ChainAt.keeps hp ⟨V, e, hV, i⟩ k m, ?_⟩
  rw [cf, chainOut_length hV]

include hp in
theorem left_blk {j : Nat} {s : State} (h : ChainAt s₀ j s) :
    WP isa (.block [.mov .r1 (.reg .r8)]) s fun t =>
      InitIn (scr s₀) (sp₀ s₀) (ol s₀ - (32 + 32 * j)) t ∧ OutAt s₀ (32 + 32 * j) t := by
  have o := h.outAt
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => WP.block_nil ?_
  have o₁ := o.keeps hp (keeps_upd u₁ (by decide))
  obtain ⟨_, xs, ox, hx⟩ := o
  exact ⟨⟨o₁.1.ctx hp, by rw [u₁.gpr, ox.left, hx]⟩, o₁⟩

/-- `L` bytes written, and at most 64 left. -/
def Last (s₀ s₀' : State) (t₁ t₂ : State) : Prop :=
  ∃ L, OutAt s₀ L t₁ ∧ OutAt s₀' L t₂ ∧ L < ol s₀ ∧ ol s₀ - L ≤ 64

include hp hp' q in
theorem last_rel :
    RelCT isa (ChainDone s₀ s₀') (.seq (.block [.mov .r1 (.reg .r8)]) next) (Last s₀ s₀') := by
  have ho := q.ol_eq
  refine RelCT.of_pre fun _ _ ⟨j, _, _, l₁, l₂, l₃⟩ => ?_
  refine (RelCT.seq (rel_regs [] (F₁ := ChainAt s₀ j) (F₂ := ChainAt s₀' j)
      (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
      (fun _ h => left_blk hp h)
      (fun _ h => (left_blk hp' h).mono fun _ h => ⟨by rw [← q.scr, ← q.sp, ← ho]; exact h.1, h.2⟩))
    (next_out_rel hp hp' q (n := ol s₀ - (32 + 32 * j)) (by omega) l₂)).mono ?_ ?_
  · intro t₁ t₂ ⟨j', c₁, c₂, m₁, m₂, m₃⟩
    have : j' = j := by omega
    subst this; exact ⟨c₁, c₂⟩
  · intro t₁ t₂ ⟨o₁, o₂⟩
    exact ⟨_, o₁, o₂, by omega, by omega⟩

include hp hp' q in
theorem extend_rel (hol : 65 ≤ ol s₀) :
    RelCT isa (fun t₁ t₂ => ExtIn s₀ t₁ ∧ ExtIn s₀' t₂) extendDigest (Last s₀ s₀') := by
  have ho := q.ol_eq
  have hol' : 65 ≤ ol s₀' := by rw [ho]; exact hol
  unfold extendDigest
  refine RelCT.seq (rel_wp ((emit_rel q (L := 0)).mono
      (fun _ _ ⟨⟨b₁, o₁⟩, ⟨b₂, o₂⟩⟩ => ⟨⟨b₁, [], o₁, rfl⟩, ⟨b₂, [], o₂, rfl⟩⟩) fun _ _ h => h)
      (fun _ h => ext_emit hp h (by omega)) (fun _ h => ext_emit hp' h (by omega))) ?_
  refine RelCT.seq (rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => chain_cmp hp (by omega) h) (fun _ h => chain_cmp hp' (by omega) h)) ?_
  refine RelCT.seq (RelCT.ite (fun t₁ t₂ ⟨⟨_, f₁⟩, ⟨_, f₂⟩⟩ => by rw [f₁, f₂, ho])
    (rel_nil fun _ _ ⟨⟨⟨c₁, f₁⟩, ⟨c₂, _⟩⟩, ht⟩ => ⟨0, c₁, c₂, by
      rw [f₁] at ht; have := of_decide_eq_true (Option.some.inj ht); omega,
      by rw [f₁] at ht; have := of_decide_eq_true (Option.some.inj ht); omega, by omega⟩)
    ((chain_rel hp hp' q).mono (fun _ _ ⟨⟨⟨c₁, f₁⟩, ⟨c₂, _⟩⟩, hf⟩ =>
      ⟨0, by rw [f₁] at hf; have := of_decide_eq_false (Option.some.inj hf); omega, c₁, c₂⟩)
      fun _ _ h => h))
    (last_rel hp hp' q)

include hp in
theorem ext_cmp {s : State} (h : ExtIn s₀ s) :
    WP isa (.block cmpLeft) s fun t => ExtIn s₀ t ∧ isa.eval .eq t = some (decide (ol s₀ ≤ 64)) := by
  obtain ⟨b, o⟩ := h
  refine (cmp_ok o (by have := hp.ol_pos; simp only [List.length_nil]; omega)).mono
    fun t ⟨cf, k, _⟩ => ⟨⟨b.keeps hp k, o.keeps hp k⟩, ?_⟩
  rw [cf]; simp

include hp hp' q in
theorem finishOutput_rel :
    RelCT isa (fun t₁ t₂ => ExtIn s₀ t₁ ∧ ExtIn s₀' t₂) finishOutput fun _ _ => True := by
  have ho := q.ol_eq
  have hpos := hp.ol_pos
  unfold finishOutput
  refine RelCT.seq (rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => ext_cmp hp h) (fun _ h => ext_cmp hp' h)) ?_
  refine RelCT.seq (R := Last s₀ s₀') (RelCT.ite (fun t₁ t₂ ⟨⟨_, f₁⟩, ⟨_, f₂⟩⟩ => by rw [f₁, f₂, ho])
    (rel_nil fun _ _ ⟨⟨⟨⟨b₁, o₁⟩, f₁⟩, ⟨⟨b₂, o₂⟩, _⟩⟩, ht⟩ =>
      ⟨0, ⟨b₁, [], o₁, rfl⟩, ⟨b₂, [], o₂, rfl⟩, by omega,
        by rw [f₁] at ht; have := of_decide_eq_true (Option.some.inj ht); omega⟩)
    (RelCT.of_pre fun _ _ ⟨⟨⟨_, f₁⟩, _⟩, hf⟩ => (extend_rel hp hp' q (by
        rw [f₁] at hf; have := of_decide_eq_false (Option.some.inj hf); omega)).mono
      (fun _ _ ⟨⟨⟨e₁, _⟩, ⟨e₂, _⟩⟩, _⟩ => ⟨e₁, e₂⟩) fun _ _ h => h)) ?_
  exact RelCT.mono (RelCT.exists_ fun L => (copyRemaining_rel q (L := L)).mono
    (fun _ _ h => ⟨h.1, h.2.1⟩) fun _ _ h => h) (fun _ _ ⟨L, h⟩ => ⟨L, h⟩) fun _ _ h => h

end

end VG.Proof.Argon2.Arm.HPrime
