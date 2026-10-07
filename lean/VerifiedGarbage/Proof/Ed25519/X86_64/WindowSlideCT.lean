import VerifiedGarbage.Proof.Ed25519.X86_64.WindowCT

/-!
# Verification's windows: what their traces depend on

The windows branch on the digits and on the counter, and address the tables by the digits, so
their traces depend on the digits alone, which both runs share (`fA`, `fB`): the digits and the
counter are read from the scratch, the same in both runs by correctness; everything else is
public by the taint analysis.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off Keeps)

variable {fld : Arith} [EdArith fld]

section
variable (R₀ : State → Prop) (base kp sp T : Addr) (A : EPoint dZ) (fA fB : Nat → Nat) (top : Nat)

/-- A run before the digits at `p` are added. -/
def MidRun (p : Nat) (x : State) : Prop := ∃ s₀, R₀ s₀ ∧ WinMid s₀ base kp sp T A fA fB top p x

/-- A run after `k`'s digit at `p` is added. -/
def HalfRun (p : Nat) (x : State) : Prop := ∃ s₀, R₀ s₀ ∧ WinHalf s₀ base kp sp T A fA fB top p x

/-- A run with the counter at `c` and the accumulator representing `v`. -/
def AtRun (v : EPoint dZ) (c : Nat) (x : State) : Prop := ∃ s₀, R₀ s₀ ∧ WinAt s₀ base kp sp T A fA fB v c x

/-- A run of the skipping, with the counter at `q`. -/
def SkipAtRun (q : Nat) (x : State) : Prop := ∃ s₀, R₀ s₀ ∧ SkipAt s₀ base kp sp T A fA fB top q x

end

/-- The counter, doubled into `rax`: the index of the digits at its position. -/
theorem counterLoad_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi)
    (.block [.mov .rax (.mem (Impl.X25519.X86_64.sc 56)), .alu .add .rax (.reg .rax)]) (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) (by fld_taint_decide)

theorem agree_rdi_rax {x y : State} (h : x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rax = y.gpr .rax) :
    VG.X86_64.Taint.Agree (Taint.ofRegs [.rdi, .rax]) x y :=
  Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2

/-- Code after the counter's load whose trace depends on `rdi` and `rax`, from runs at the same
counter `p`: the counter is read from the scratch, the same in both runs by correctness. -/
theorem counterIdx_ct {P : State → Prop} {base : Addr} {p : Nat} {l : List Instr}
    (hP : ∀ x, P x → Scratch x base ∧ x.mem.readW (off base 56) 64 = BitVec.ofNat 64 p)
    (h : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rax = y.gpr .rax) (.block l)
      (fun _ _ => True)) :
    RelCT isa (fun x y => P x ∧ P y)
      (.block (([.mov .rax (.mem (Impl.X25519.X86_64.sc 56)), .alu .add .rax (.reg .rax)] : List Instr) ++ l))
      (fun _ _ => True) :=
  RelCT.block_append (seq_same (rdi_ct (fun x h => (hP x h).1.rdi) counterLoad_ct)
    (F := fun u => u.gpr .rax = BitVec.ofNat 64 (2 * p) ∧ u.gpr .rdi = base)
    (fun x h => WP.mono (counter_ok (hP x h).1 (hP x h).2) fun _ ⟨ur, ku⟩ =>
      ⟨ur, (ku.1 _ (by decide)).trans (hP x h).1.rdi⟩)
    (h.mono (fun _ _ hh => ⟨hh.1.2.trans hh.2.2.symm, hh.1.1.trans hh.2.1.symm⟩) (fun _ _ h => h)))

theorem digitLoad_ct (dst : Nat) (hd : dst < 2) : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rax = y.gpr .rax)
    (.block [.movzx8 .rbx { base := .rdi, index := some .rax, disp := ((2048 + dst : Nat) : Int) },
      .alu .test .rbx (.reg .rbx)]) (fun _ _ => True) := by
  obtain _ | _ | d := dst
  · exact taintFld (Taint.ofRegs [.rdi, .rax]) (fun _ _ h => agree_rdi_rax h) (by fld_taint_decide)
  · exact taintFld (Taint.ofRegs [.rdi, .rax]) (fun _ _ h => agree_rdi_rax h) (by fld_taint_decide)
  · omega

theorem digitsLoad_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rax = y.gpr .rax)
    (.block [.movzx8 .rbx { base := .rdi, index := some .rax, disp := 2048 },
      .movzx8 .rcx { base := .rdi, index := some .rax, disp := 2049 }, .alu .or .rbx (.reg .rcx)])
    (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi, .rax]) (fun _ _ h => agree_rdi_rax h) (by fld_taint_decide)

theorem digitAt_ct {P : State → Prop} {base : Addr} {p : Nat} (dst : Nat) (hd : dst < 2)
    (hP : ∀ x, P x → Scratch x base ∧ x.mem.readW (off base 56) 64 = BitVec.ofNat 64 p) :
    RelCT isa (fun x y => P x ∧ P y) (.block (digitAt dst)) (fun _ _ => True) :=
  counterIdx_ct hP (digitLoad_ct dst hd)

theorem digitsAt_ct {P : State → Prop} {base : Addr} {p : Nat}
    (hP : ∀ x, P x → Scratch x base ∧ x.mem.readW (off base 56) 64 = BitVec.ofNat 64 p) :
    RelCT isa (fun x y => P x ∧ P y) (.block digitsAt) (fun _ _ => True) :=
  counterIdx_ct hP digitsLoad_ct

/-- The counter moved down from `p + 1`, then both digits at `p`. -/
theorem skipLoadTop_ct {P : State → Prop} {base : Addr} {p : Nat}
    (hP : ∀ x, P x → Scratch x base ∧ x.mem.readW (off base 56) 64 = BitVec.ofNat 64 (p + 1)) :
    RelCT isa (fun x y => P x ∧ P y) (.block (batchBegin ++ digitsAt)) (fun _ _ => True) :=
  RelCT.block_append (seq_same (rdi_ct (fun x h => (hP x h).1.rdi) batchBegin_ct)
    (F := fun u => Scratch u base ∧ u.mem.readW (off base 56) 64 = BitVec.ofNat 64 p)
    (fun x h => WP.mono (batchBegin_ok (hP x h).1 p (hP x h).2) fun a ⟨_, ac, ag, ar, aw, am⟩ =>
      ⟨ByteKeep.scratch (s := x) ⟨fun r _ hb _ => ag r hb, ar, aw, am.mono (by decide) (by decide)⟩ (hP x h).1, ac⟩)
    (digitsAt_ct fun _ h => h))

theorem cmpSelf_ct :
    RelCT isa (fun _ _ => True) (.block [.alu .cmp .rax (.reg .rax)]) (fun _ _ => True) :=
  taintFld (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by fld_taint_decide)

theorem dblBlock_ct (t : Bool) :
    RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block (fieldCode fld (dblOps t))) (fun _ _ => True) := by
  cases t
  · exact taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) (by fld_taint_decide)
  · exact taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) (by fld_taint_decide)

/-- `k`'s digit at `p`: the branch is on it, its entry's address from it. -/
theorem addA_ct {R₀ : State → Prop} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top p : Nat}
    (tb : Bool) (hdg : Digits fA fB top) (hp : p ≤ top) :
    RelCT isa (fun x y => MidRun R₀ base kp sp T A fA fB top p x ∧ MidRun R₀ base kp sp T A fA fB top p y)
      (.seq (.block (digitAt 0)) (addDigit 5376 (fieldCode fld (addCachedOps tb)))) (fun _ _ => True) := by
  have w (x : State) (h : MidRun R₀ base kp sp T A fA fB top p x) : WP isa (.block (digitAt 0)) x fun u =>
      u.gpr .rdi = base ∧ u.gpr .rbx = BitVec.ofNat 64 (fA p) ∧ u.zf = some (decide (fA p = 0)) := by
    obtain ⟨_, _, h⟩ := h
    refine WP.mono (digitAt_ok h.ctx.scratch (by have := hdg.top; omega) (by decide) h.counter)
      fun u ⟨ub, uz, ku⟩ => ?_
    rw [(h.digits p (by have := hdg.top; omega)).1] at ub uz
    exact ⟨(ku.1 _ (by decide)).trans h.ctx.scratch.rdi, ub, uz⟩
  refine seq_same (digitAt_ct 0 (by decide) fun x h => by obtain ⟨_, _, h⟩ := h; exact ⟨h.ctx.scratch, h.counter⟩) w ?_
  rw [addDigit]
  refine VG.RelCT.ite (fun x y h => by simp only [eval, h.1.2.2, h.2.2.2]) ?_
    (VG.RelCT.block_nil fun _ _ _ => trivial)
  exact (addDigitA_ct tb).mono (fun x y h => ⟨h.1.1.1.trans h.1.2.1.symm, h.1.1.2.1.trans h.1.2.2.1.symm⟩)
    (fun _ _ h => h)

/-- `S`'s digit at `p`: the branch is on it, its entry's address from it and the static's. -/
theorem addB_ct {R₀ : State → Prop} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top p : Nat}
    (hdg : Digits fA fB top) (hp : p ≤ top) :
    RelCT isa (fun x y => HalfRun R₀ base kp sp T A fA fB top p x ∧ HalfRun R₀ base kp sp T A fA fB top p y)
      (.seq (.block (digitAt 1)) (addBase fld)) (fun _ _ => True) := by
  have w (x : State) (h : HalfRun R₀ base kp sp T A fA fB top p x) : WP isa (.block (digitAt 1)) x
      (BasePre base T (fB p)) := by
    obtain ⟨_, _, h⟩ := h
    refine WP.mono (digitAt_ok h.ctx.scratch (by have := hdg.top; omega) (by decide) h.counter)
      fun u ⟨ub, uz, ku⟩ => ?_
    rw [(h.digits p (by have := hdg.top; omega)).2] at ub uz
    have kw : WinKeep base x u := WinKeep.of_keeps ku (by decide)
    have hu := h.ctx.of_keep kw
    exact ⟨hu.scratch, hu.bHeader, ub, uz, hdg.b p⟩
  exact seq_same (digitAt_ct 1 (by decide) fun x h => by obtain ⟨_, _, h⟩ := h; exact ⟨h.ctx.scratch, h.counter⟩) w
    addBase_ct

theorem addsAt_ct {R₀ : State → Prop} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top p : Nat}
    (hdg : Digits fA fB top) (hp : p ≤ top) :
    RelCT isa (fun x y => MidRun R₀ base kp sp T A fA fB top p x ∧ MidRun R₀ base kp sp T A fA fB top p y)
      (addsAt fld) (fun _ _ => True) := by
  rw [addsAt]
  have w (x : State) (h : MidRun R₀ base kp sp T A fA fB top p x) : WP isa (.block (digitAt 1)) x fun u =>
      u.zf = some (decide (fB p = 0)) ∧ MidRun R₀ base kp sp T A fA fB top p u := by
    obtain ⟨s₀, r₀, h⟩ := h
    refine WP.mono (digitAt_ok h.ctx.scratch (by have := hdg.top; omega) (by decide) h.counter)
      fun u ⟨_, uz, ku⟩ => ?_
    rw [(h.digits p (by have := hdg.top; omega)).2] at uz
    exact ⟨uz, s₀, r₀, h.of_byte (ByteKeep.of_keeps ku (by decide)) (fun i _ => by rw [ku.2.1])
      (by rw [ku.2.1])⟩
  refine VG.RelCT.seq (R := fun (x y : State) => (x.zf = some (decide (fB p = 0)) ∧
    MidRun R₀ base kp sp T A fA fB top p x) ∧ (y.zf = some (decide (fB p = 0)) ∧
    MidRun R₀ base kp sp T A fA fB top p y))
    ((VG.RelCT.wp (digitAt_ct 1 (by decide) fun x h => by
      obtain ⟨_, _, h⟩ := h; exact ⟨h.ctx.scratch, h.counter⟩) fun x y h => ⟨w x h.1, w y h.2⟩).mono
      (fun _ _ h => h) (fun _ _ h => h.2)) ?_
  refine VG.RelCT.ite (fun x y h => by simp only [eval, h.1.1, h.2.1]) ?_ ?_
  · refine (show RelCT isa (fun x y => MidRun R₀ base kp sp T A fA fB top p x ∧
        MidRun R₀ base kp sp T A fA fB top p y) _ _ from ?_).mono (fun x y h => ⟨h.1.1.2, h.1.2.2⟩)
      (fun _ _ h => h)
    apply RelCT.assoc
    exact seq_same (addA_ct true hdg hp) (fun x h => by
      obtain ⟨s₀, r₀, h⟩ := h; exact WP.mono (addA_ok hdg hp h fun _ => rfl) fun u hu => ⟨s₀, r₀, hu⟩)
      (addB_ct hdg hp)
  · exact (addA_ct false hdg hp).mono (fun x y h => ⟨h.1.1.2, h.1.2.2⟩) (fun _ _ h => h)

/-- The doubling: the branch is on whether a digit at `p` is nonzero. -/
theorem dblAt_ct {R₀ : State → Prop} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top p : Nat}
    (hdg : Digits fA fB top) (hp : p ≤ top) :
    RelCT isa (fun x y => AtRun R₀ base kp sp T A fA fB (winVal A fA fB top (p + 1)) p x ∧
      AtRun R₀ base kp sp T A fA fB (winVal A fA fB top (p + 1)) p y) (dblAt fld) (fun _ _ => True) := by
  have w (x : State) (h : AtRun R₀ base kp sp T A fA fB (winVal A fA fB top (p + 1)) p x) :
      WP isa (.block digitsAt) x fun u => u.gpr .rdi = base ∧ u.zf = some (decide (fA p = 0 ∧ fB p = 0)) := by
    obtain ⟨_, _, h⟩ := h
    refine WP.mono (digitsAt_ok h.ctx.scratch (by have := hdg.top; omega) h.counter) fun u ⟨uz, ku⟩ => ?_
    rw [(h.digits p (by have := hdg.top; omega)).1, (h.digits p (by have := hdg.top; omega)).2] at uz
    exact ⟨(ku.1 _ (by decide)).trans h.ctx.scratch.rdi, uz⟩
  rw [dblAt]
  refine seq_same (digitsAt_ct fun x h => by obtain ⟨_, _, h⟩ := h; exact ⟨h.ctx.scratch, h.counter⟩) w ?_
  refine VG.RelCT.ite (fun x y h => by simp only [eval, h.1.2, h.2.2]) ?_ ?_
  · exact (dblBlock_ct true).mono (fun x y h => h.1.1.1.trans h.1.2.1.symm) (fun _ _ h => h)
  · exact (dblBlock_ct false).mono (fun x y h => h.1.1.1.trans h.1.2.1.symm) (fun _ _ h => h)

theorem stepAt_ct {R₀ : State → Prop} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top p : Nat}
    (hdg : Digits fA fB top) (hp : p ≤ top) :
    RelCT isa (fun x y => LoopRun R₀ base kp sp T A fA fB top (p + 1) x ∧
      LoopRun R₀ base kp sp T A fA fB top (p + 1) y) (stepAt fld) (fun _ _ => True) := by
  have w1 (x : State) (h : LoopRun R₀ base kp sp T A fA fB top (p + 1) x) : WP isa (.block batchBegin) x
      (AtRun R₀ base kp sp T A fA fB (winVal A fA fB top (p + 1)) p) := by
    obtain ⟨s₀, r₀, h⟩ := h
    refine WP.mono (batchBegin_ok h.ctx.scratch p h.counter) fun a ⟨_, ac, ag, ar, aw, am⟩ => ?_
    have ka : ByteKeep base x a := ⟨fun r _ hb _ => ag r hb, ar, aw, am.mono (by decide) (by decide)⟩
    exact ⟨s₀, r₀, h.ctx.of_byte ka, by rw [header_env am]; exact h.d, ac, h.digits.of_byte ka.mem,
      by rw [header_env am]; exact h.value, h.keep.trans ka⟩
  rw [stepAt]
  refine seq_same (rdi_ct (fun x h => by obtain ⟨_, _, h⟩ := h; exact h.ctx.scratch.rdi) batchBegin_ct) w1 ?_
  refine seq_same (dblAt_ct hdg hp) (F := MidRun R₀ base kp sp T A fA fB top p) (fun x h => by
    obtain ⟨s₀, r₀, h⟩ := h; exact WP.mono (dblAt_ok hdg hp h) fun u hu => ⟨s₀, r₀, hu⟩) ?_
  exact seq_same (addsAt_ct hdg hp) (F := LoopRun R₀ base kp sp T A fA fB top p) (fun x h => by
    obtain ⟨s₀, r₀, h⟩ := h; exact WP.mono (addsAt_ok hdg hp h) fun u hu => ⟨s₀, r₀, hu⟩)
    (rdi_ct (fun x h => by obtain ⟨_, _, h⟩ := h; exact h.ctx.scratch.rdi) batchTest_ct)

theorem skipTop_ct {R₀ : State → Prop} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top p : Nat}
    (hdg : Digits fA fB top) :
    RelCT isa (fun x y => SkipAtRun R₀ base kp sp T A fA fB top (p + 1) x ∧
      SkipAtRun R₀ base kp sp T A fA fB top (p + 1) y) skipTop (fun _ _ => True) := by
  have w (x : State) (h : SkipAtRun R₀ base kp sp T A fA fB top (p + 1) x) :
      WP isa (.block (batchBegin ++ digitsAt)) x fun u => u.gpr .rdi = base ∧
        u.zf = some (decide (fA p = 0 ∧ fB p = 0)) := by
    obtain ⟨_, _, h⟩ := h
    have hle := h.le
    have hl := h.loop
    rw [WP.block_append_iff]
    refine WP.mono (batchBegin_ok hl.ctx.scratch p hl.counter) fun a ⟨_, ac, ag, ar, aw, am⟩ => ?_
    have ka : ByteKeep base x a := ⟨fun r _ hb _ => ag r hb, ar, aw, am.mono (by decide) (by decide)⟩
    refine WP.mono (digitsAt_ok (ka.scratch hl.ctx.scratch) (by have := hdg.top; omega) ac) fun u ⟨uz, ku⟩ => ?_
    have hd := hl.digits.of_byte ka.mem p (by have := hdg.top; omega)
    rw [hd.1, hd.2] at uz
    exact ⟨(ku.1 _ (by decide)).trans (ka.scratch hl.ctx.scratch).rdi, uz⟩
  rw [skipTop]
  refine seq_same (skipLoadTop_ct fun x h => by obtain ⟨_, _, h⟩ := h; exact ⟨h.loop.ctx.scratch, h.loop.counter⟩) w ?_
  refine VG.RelCT.ite (fun x y h => by simp only [eval, h.1.2, h.2.2]) ?_ ?_
  · exact cmpSelf_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact batchTest_ct.mono (fun x y h => h.1.1.1.trans h.1.2.1.symm) (fun _ _ h => h)

/-- The windows' trace depends on the digits alone. -/
theorem windows_ct {R₀ : State → Prop} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top : Nat}
    (hdg : Digits fA fB top) :
    RelCT isa (fun x y => StartRun R₀ base kp sp T A fA fB top x ∧ StartRun R₀ base kp sp T A fA fB top y)
      (windows fld) (fun _ _ => True) := by
  rw [windows]
  -- The skipping, a step at a time, from the same counter in both runs.
  refine VG.RelCT.seq (Q := fun _ _ => True) (R := fun x y => ∃ p, p ≤ top ∧
    MidRun R₀ base kp sp T A fA fB top p x ∧ MidRun R₀ base kp sp T A fA fB top p y) ?_ ?_
  · refine (VG.RelCT.loop (M := isa) (fun q x y => SkipAtRun R₀ base kp sp T A fA fB top q x ∧
      SkipAtRun R₀ base kp sp T A fA fB top q y) ?_ (top + 1)).mono (fun x y h => ⟨h.1, h.2⟩) (fun _ _ h => h)
    intro q
    rcases q with _ | p
    · exact VG.RelCT.of_false fun _ _ h => by obtain ⟨_, _, h⟩ := h.1; exact Nat.lt_irrefl 0 h.pos
    have hw (x : State) (h : SkipAtRun R₀ base kp sp T A fA fB top (p + 1) x) : WP isa skipTop x fun u =>
        u.zf = some (skipStops fA fB p) ∧
        (skipStops fA fB p = true → MidRun R₀ base kp sp T A fA fB top p u ∧ p ≤ top) ∧
        (skipStops fA fB p = false → SkipAtRun R₀ base kp sp T A fA fB top p u) := by
      obtain ⟨s₀, r₀, h⟩ := h
      have hle := h.le
      exact WP.mono (skipTop_ok hdg h) fun u ⟨uz, ut, uf⟩ =>
        ⟨uz, fun ht => ⟨⟨s₀, r₀, ut ht⟩, by omega⟩, fun hf => ⟨s₀, r₀, uf hf⟩⟩
    refine (VG.RelCT.wp (skipTop_ct (p := p) hdg) fun x y h => ⟨hw x h.1, hw y h.2⟩).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨xz, xt, xf⟩, ⟨yz, yt, yf⟩⟩
    have ex : isa.eval .ne x = some (!skipStops fA fB p) := by
      show eval .ne x = _; simp only [eval, xz, Option.map_some]
    have ey : isa.eval .ne y = some (!skipStops fA fB p) := by
      show eval .ne y = _; simp only [eval, yz, Option.map_some]
    refine ⟨ex.trans ey.symm, fun he => ?_, fun he => ?_⟩
    · have hs : skipStops fA fB p = true := by
        rw [ex] at he; simpa using he
      exact ⟨p, (xt hs).2, (xt hs).1, (yt hs).1⟩
    · have hs : skipStops fA fB p = false := by
        rw [ex] at he; simpa using he
      exact ⟨p, by omega, xf hs, yf hs⟩
  -- From the position the skipping stopped at.
  refine VG.RelCT.exists_ fun p => ?_
  refine (VG.RelCT.exists_ (P := fun (_ : p ≤ top) x y => MidRun R₀ base kp sp T A fA fB top p x ∧
    MidRun R₀ base kp sp T A fA fB top p y) fun hp => ?_).mono (fun x y h => ⟨h.1, h.2⟩) (fun _ _ h => h)
  refine seq_same (addsAt_ct hdg hp) (F := LoopRun R₀ base kp sp T A fA fB top p) (fun x h => by
    obtain ⟨s₀, r₀, h⟩ := h; exact WP.mono (addsAt_ok hdg hp h) fun u hu => ⟨s₀, r₀, hu⟩) ?_
  have wt (x : State) (h : LoopRun R₀ base kp sp T A fA fB top p x) : WP isa (.block batchTest) x fun u =>
      u.zf = some (decide (p = 0)) ∧ LoopRun R₀ base kp sp T A fA fB top p u := by
    obtain ⟨s₀, r₀, hb⟩ := h
    refine WP.mono (counterTest_ok hb.ctx.scratch (by have := hdg.top; omega) hb.counter) fun c ⟨cz, kc⟩ => ?_
    have kc' := ByteKeep.of_keeps (base := base) kc (by decide)
    exact ⟨cz, s₀, r₀, hb.ctx.of_byte kc', by rw [kc.2.1]; exact hb.d, by rw [kc.2.1]; exact hb.counter,
      by rw [kc.2.1]; exact hb.digits, by rw [kc.2.1]; exact hb.value, hb.keep.trans kc'⟩
  refine seq_same (rdi_ct (fun x h => by obtain ⟨_, _, h⟩ := h; exact h.ctx.scratch.rdi) batchTest_ct) wt ?_
  have ec (x : State) (h : x.zf = some (decide (p = 0))) : isa.eval .ne x = some (!decide (p = 0)) := by
    show eval .ne x = _; simp only [eval, h, Option.map_some]
  refine VG.RelCT.ite (fun x y h => (ec x h.1.1).trans (ec y h.2.1).symm) ?_
    (VG.RelCT.block_nil fun _ _ _ => trivial)
  have hp0 (x y : State) (h : ((x.zf = some (decide (p = 0)) ∧ LoopRun R₀ base kp sp T A fA fB top p x) ∧
      (y.zf = some (decide (p = 0)) ∧ LoopRun R₀ base kp sp T A fA fB top p y)) ∧
      isa.eval .ne x = some true) : 0 < p := by
    rw [ec x h.1.1.1] at h
    have := h.2
    simp only [Option.some.injEq, Bool.not_eq_true', decide_eq_false_iff_not] at this
    omega
  refine (VG.RelCT.loop (M := isa) (fun n x y => LoopRun R₀ base kp sp T A fA fB top n x ∧
    LoopRun R₀ base kp sp T A fA fB top n y ∧ 0 < n ∧ n ≤ top) ?_ p).mono
    (fun x y h => ⟨h.1.1.2, h.1.2.2, hp0 x y h, hp⟩) (fun _ _ h => h)
  intro n
  rcases n with _ | m
  · exact VG.RelCT.of_false fun _ _ h => Nat.lt_irrefl 0 h.2.2.1
  by_cases hm : m + 1 ≤ top
  swap
  · exact VG.RelCT.of_false fun _ _ h => hm h.2.2.2
  have ws (x : State) (h : LoopRun R₀ base kp sp T A fA fB top (m + 1) x) : WP isa (stepAt fld) x fun u =>
      u.zf = some (decide (m = 0)) ∧ LoopRun R₀ base kp sp T A fA fB top m u := by
    obtain ⟨s₀, r₀, h⟩ := h
    exact WP.mono (stepAt_ok hdg (by omega) h) fun u ⟨uz, hu⟩ => ⟨uz, s₀, r₀, hu⟩
  refine (VG.RelCT.wp (stepAt_ct hdg (by omega)) fun x y h => ⟨ws x h.1, ws y h.2⟩).mono
    (fun x y h => ⟨h.1, h.2.1⟩) ?_
  have em (x : State) (h : x.zf = some (decide (m = 0))) : isa.eval .ne x = some (!decide (m = 0)) := by
    show eval .ne x = _; simp only [eval, h, Option.map_some]
  intro x y ⟨_, ⟨xz, xl⟩, ⟨yz, yl⟩⟩
  refine ⟨(em x xz).trans (em y yz).symm, fun _ => trivial, fun he => ⟨m, by omega, xl, yl, ?_, by omega⟩⟩
  rw [em x xz] at he
  simp only [Option.some.injEq, Bool.not_eq_true', decide_eq_false_iff_not] at he
  omega

instance : EdWindows (windows fld) where
  ok hdg h := windows_ok hdg h
  ct hdg := ((VG.RelCT.wp (windows_ct hdg) fun x y h => by
      obtain ⟨⟨s₀, r₀, hx⟩, ⟨t₀, q₀, hy⟩⟩ := h
      exact ⟨WP.mono (windows_ok hdg hx) fun u hu => (⟨s₀, r₀, hu⟩ : LoopRun _ _ _ _ _ _ _ _ _ 0 u),
        WP.mono (windows_ok hdg hy) fun u hu => (⟨t₀, q₀, hu⟩ : LoopRun _ _ _ _ _ _ _ _ _ 0 u)⟩).mono
    (fun _ _ h => h) (fun _ _ h => h.2))

end VG.Proof.Ed25519.X86_64
