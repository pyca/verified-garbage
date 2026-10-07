import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.VerifyWin
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.VerifyLit
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowSlideCT

/-!
# Ed25519 verification with AVX512_IFMA: the windows' trace

`Ifma.windows` leaks what `windows` does: its branches are on the counter and
on the digits of the public scalars, and its addresses are the
scratch plus constants, the counter or a digit. The blocks between the
branches are checked by the taint analysis, with the scratch's address public
and, for an entry's addition, its digit.
-/

namespace VG.Proof.Ed25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Ifma VG.Proof.Ed25519
  VG.Proof.Ed25519.X86_64 Edwards
open VG.Proof.X25519.X86_64 (Outside off clob Keeps)

/-! ## The blocks -/

theorem vdbl_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block vdbl) (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) ⟨_, by taint_decide⟩

theorem agree_rdi_rbx {x y : State} (h : x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rbx = y.gpr .rbx) :
    VG.X86_64.Taint.Agree (Taint.ofRegs [.rdi, .rbx]) x y :=
  Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2

theorem vaddBodyA_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rbx = y.gpr .rbx)
    (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ tableAddr 5376 ++ vrows ++ esplit ++ vadd))
    (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi, .rbx]) (fun _ _ h => agree_rdi_rbx h) ⟨_, by taint_decide⟩

theorem vbaseAddPart_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rax = y.gpr .rax)
    (.block (vrows ++ esplit ++ vadd)) (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi, .rax]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2) ⟨_, by taint_decide⟩

theorem vprep_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi)
    (.block (VG.Impl.X25519.X86_64.Ifma.consts ++ vload)) (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) ⟨_, by taint_decide⟩

theorem vstore_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block vstore) (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) ⟨_, by taint_decide⟩

theorem mxSave_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block mxSave) (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) ⟨_, by taint_decide⟩

theorem mxLoad_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block mxLoad) (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) ⟨_, by taint_decide⟩

theorem mxRestore_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block mxRestore)
    (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) ⟨_, by taint_decide⟩

theorem lfence_ct : RelCT isa (fun _ _ => True) (.block [.lfence]) (fun _ _ => True) :=
  taintFld (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp)) ⟨_, by taint_decide⟩

/-- The addition of `S`'s digit in the lanes: the branch is on the digit, its entry's address
`T + 128 (v - 1)` the same in both runs. -/
theorem vaddBase_ct {base T : Addr} {v : Nat} :
    RelCT isa (fun x y => BasePre base T v x ∧ BasePre base T v y) vaddBase (fun _ _ => True) := by
  rw [vaddBase]
  refine VG.RelCT.ite (fun x y h => by simp only [eval, h.1.zf, h.2.zf]) ?_
    (VG.RelCT.block_nil fun _ _ _ => trivial)
  have hw (x : State) (h : BasePre base T v x) (hv : v ≠ 0) :
      WP isa (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ baseAddr)) x fun u =>
        u.gpr .rdi = base ∧ u.gpr .rax = off T (128 * (v - 1)) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hv
    rw [WP.block_append_iff]
    refine WP.mono (accumulateDec_ok x n h.rbx) fun b ⟨bc, kb⟩ => ?_
    refine WP.mono (baseAddr_ok (T := T) (h.scratch.of_keeps kb (by decide)) (by rw [kb.2.1]; exact h.header) n
      (by have := h.bound; omega) bc) fun u ⟨ua, ku⟩ => ?_
    exact ⟨(ku.1 _ (by decide)).trans ((kb.1 _ (by decide)).trans h.scratch.rdi), ua⟩
  rw [show (([.alu .sub .rbx (.imm 1)] : List Instr) ++ baseAddr ++ vrows ++ esplit ++ vadd) =
    (([.alu .sub .rbx (.imm 1)] : List Instr) ++ baseAddr) ++ (vrows ++ esplit ++ vadd) by
      simp only [List.append_assoc]]
  have hv (x : State) (h : BasePre base T v x) (he : isa.eval .ne x = some true) : v ≠ 0 := by
    intro h0
    simp only [eval, h.zf, h0, decide_true, Option.map_some, Bool.not_true, Option.some.injEq,
      Bool.false_eq_true] at he
  refine blockAppend_ct ((VG.RelCT.wp (baseAddrPart_ct.mono
    (fun x y h => ⟨h.1.1.scratch.rdi.trans h.1.2.scratch.rdi.symm, h.1.1.rbx.trans h.1.2.rbx.symm⟩)
    (fun _ _ h => h)) fun x y h => ⟨hw x h.1.1 (hv x h.1.1 h.2), hw y h.1.2 (hv x h.1.1 h.2)⟩).mono
    (fun _ _ h => h) ?_) vbaseAddPart_ct
  intro x y ⟨_, hx, hy⟩
  exact ⟨hx.1.trans hy.1.symm, hx.2.trans hy.2.symm⟩

/-- `seq_same`, keeping a property of both runs at the end. -/
theorem seq_both {P F G : State → Prop} {c₁ c₂ : Prog isa}
    (h₁ : RelCT isa (fun x y => P x ∧ P y) c₁ (fun _ _ => True)) (w : ∀ x, P x → WP isa c₁ x F)
    (h₂ : RelCT isa (fun x y => F x ∧ F y) c₂ (fun x y => G x ∧ G y)) :
    RelCT isa (fun x y => P x ∧ P y) (.seq c₁ c₂) (fun x y => G x ∧ G y) :=
  VG.RelCT.seq ((VG.RelCT.wp h₁ fun x y h => ⟨w x h.1, w y h.2⟩).mono
    (fun _ _ h => h) (fun _ _ h => h.2)) h₂

/-- A program checked by the taint analysis, keeping a property of both runs at the end. -/
theorem last_both {P G : State → Prop} {c : Prog isa}
    (h : RelCT isa (fun x y => P x ∧ P y) c (fun _ _ => True)) (w : ∀ x, P x → WP isa c x G) :
    RelCT isa (fun x y => P x ∧ P y) c (fun x y => G x ∧ G y) :=
  (VG.RelCT.wp h fun x y h => ⟨w x h.1, w y h.2⟩).mono (fun _ _ h => h) (fun _ _ h => h.2)

/-! ## Positions -/

section
variable (R₀ : State → Prop) (base kp sp T : Addr) (A : EPoint dZ) (fA fB : Nat → Nat) (top : Nat)

/-- A run in the lanes with the counter at `c` and the point representing `v`. -/
def VAtRun (v : EPoint dZ) (c : Nat) (x : State) : Prop :=
  VRun R₀ base (fun s₃ => VAt s₃ base kp sp T A fA fB v c) x

/-- A run in the lanes after position `p`. -/
def VLoopRun (p : Nat) (x : State) : Prop :=
  VRun R₀ base (fun s₃ => VLoop s₃ base kp sp T A fA fB top p) x

/-- A run of the skipping in the lanes, with the counter at `q`. -/
def VSkipRun (q : Nat) (x : State) : Prop :=
  VRun R₀ base (fun s₃ => VSkip s₃ base kp sp T A fA fB top q) x

end

theorem VAtRun.at {R₀ : State → Prop} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat}
    {v : EPoint dZ} {c : Nat} {x : State} (h : VAtRun R₀ base kp sp T A fA fB v c x) :
    Scratch x base ∧ x.mem.readW (off base 56) 64 = BitVec.ofNat 64 c := by
  obtain ⟨_, _, _, _, _, h⟩ := h
  exact ⟨h.ctx.scratch, h.counter⟩

/-- `k`'s digit at `p`: the branch is on it, its entry's address from it. -/
theorem vaddA_ct {R₀ : State → Prop} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat}
    {v : EPoint dZ} {top p : Nat} (hdg : Digits fA fB top) (hp : p ≤ top) :
    RelCT isa (fun x y => VAtRun R₀ base kp sp T A fA fB v p x ∧ VAtRun R₀ base kp sp T A fA fB v p y)
      (.seq (.block (digitAt 0)) (vaddDigit 5376)) (fun _ _ => True) := by
  have w (x : State) (h : VAtRun R₀ base kp sp T A fA fB v p x) : WP isa (.block (digitAt 0)) x fun u =>
      u.gpr .rdi = base ∧ u.gpr .rbx = BitVec.ofNat 64 (fA p) ∧ u.zf = some (decide (fA p = 0)) := by
    obtain ⟨_, _, _, _, _, h⟩ := h
    refine WP.mono (digitAt_ok h.ctx.scratch (by have := hdg.top; omega) (by decide) h.counter)
      fun u ⟨ub, uz, ku⟩ => ?_
    rw [(h.digits p (by have := hdg.top; omega)).1] at ub uz
    exact ⟨(ku.1 _ (by decide)).trans h.ctx.scratch.rdi, ub, uz⟩
  refine seq_same (digitAt_ct 0 (by decide) fun x h => h.at) w ?_
  rw [vaddDigit]
  refine VG.RelCT.ite (fun x y h => by simp only [eval, h.1.2.2, h.2.2.2]) ?_
    (VG.RelCT.block_nil fun _ _ _ => trivial)
  exact vaddBodyA_ct.mono (fun x y h => ⟨h.1.1.1.trans h.1.2.1.symm, h.1.1.2.1.trans h.1.2.2.1.symm⟩)
    (fun _ _ h => h)

/-- `S`'s digit at `p`: the branch is on it, its entry's address from it and the static's. -/
theorem vaddB_ct {R₀ : State → Prop} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat}
    {v : EPoint dZ} {top p : Nat} (hdg : Digits fA fB top) (hp : p ≤ top) :
    RelCT isa (fun x y => VAtRun R₀ base kp sp T A fA fB v p x ∧ VAtRun R₀ base kp sp T A fA fB v p y)
      (.seq (.block (digitAt 1)) vaddBase) (fun _ _ => True) := by
  have w (x : State) (h : VAtRun R₀ base kp sp T A fA fB v p x) : WP isa (.block (digitAt 1)) x
      (BasePre base T (fB p)) := by
    obtain ⟨_, _, _, _, _, h⟩ := h
    refine WP.mono (digitAt_ok h.ctx.scratch (by have := hdg.top; omega) (by decide) h.counter)
      fun u ⟨ub, uz, ku⟩ => ?_
    rw [(h.digits p (by have := hdg.top; omega)).2] at ub uz
    have hu := h.ctx.of_keep (WinKeep.of_keeps ku (by decide))
    exact ⟨hu.scratch, hu.bHeader, ub, uz, hdg.b p⟩
  exact seq_same (digitAt_ct 1 (by decide) fun x h => h.at) w vaddBase_ct

theorem vaddsAt_ct {R₀ : State → Prop} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat}
    {v : EPoint dZ} {top p : Nat} (hdg : Digits fA fB top) (hp : p ≤ top) :
    RelCT isa (fun x y => VAtRun R₀ base kp sp T A fA fB v p x ∧ VAtRun R₀ base kp sp T A fA fB v p y)
      vaddsAt (fun _ _ => True) := by
  rw [vaddsAt]
  apply RelCT.assoc
  exact seq_same (vaddA_ct hdg hp) (F := VAtRun R₀ base kp sp T A fA fB (v + (Recode.dec (fA p)) • A) p)
    (fun x h => by
      obtain ⟨s₀, s₃, r₀, k, m, h⟩ := h
      exact WP.mono (vaddA_ok hdg hp h) fun u hu => ⟨s₀, s₃, r₀, k, m, hu⟩) (vaddB_ct hdg hp)

theorem vstepAt_ct {R₀ : State → Prop} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat}
    {top p : Nat} (hdg : Digits fA fB top) (hp : p ≤ top) :
    RelCT isa (fun x y => VLoopRun R₀ base kp sp T A fA fB top (p + 1) x ∧
      VLoopRun R₀ base kp sp T A fA fB top (p + 1) y) vstepAt (fun _ _ => True) := by
  have w1 (x : State) (h : VLoopRun R₀ base kp sp T A fA fB top (p + 1) x) : WP isa (.block batchBegin) x
      (VAtRun R₀ base kp sp T A fA fB (winVal A fA fB top (p + 1)) p) := by
    obtain ⟨s₀, s₃, r₀, k, m, h⟩ := h
    refine WP.mono (vbatchBegin_ok h.ctx.scratch p h.counter) fun a ⟨ac, ka, ax, ay⟩ => ?_
    obtain ⟨pa, sa⟩ := lanePt_vec ax ay
    exact ⟨s₀, s₃, r₀, k, m, h.of_keep ka ac (by rw [pa]; exact h.value) (sa h.small)⟩
  have w2 (x : State) (h : VAtRun R₀ base kp sp T A fA fB (winVal A fA fB top (p + 1)) p x) :
      WP isa (.block vdbl) x (VAtRun R₀ base kp sp T A fA fB ((2 : Int) • winVal A fA fB top (p + 1)) p) := by
    obtain ⟨s₀, s₃, r₀, k, m, h⟩ := h
    exact WP.mono (vdblAt_ok h) fun u hu => ⟨s₀, s₃, r₀, k, m, hu⟩
  have w3 (x : State) (h : VAtRun R₀ base kp sp T A fA fB ((2 : Int) • winVal A fA fB top (p + 1)) p x) :
      WP isa vaddsAt x (Scratch · base) := by
    obtain ⟨s₀, s₃, r₀, k, m, h⟩ := h
    exact WP.mono (vaddsAt_ok hdg hp h) fun u hu => hu.ctx.scratch
  rw [vstepAt]
  refine seq_same (rdi_ct (fun x h => by obtain ⟨_, _, _, _, _, h⟩ := h; exact h.ctx.scratch.rdi)
    batchBegin_ct) w1 ?_
  refine seq_same (rdi_ct (fun x h => h.at.1.rdi) vdbl_ct) w2 ?_
  exact seq_same (vaddsAt_ct hdg hp) w3 (rdi_ct (fun x h => h.rdi) batchTest_ct)

theorem vskipTop_ct {R₀ : State → Prop} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat}
    {top p : Nat} (hdg : Digits fA fB top) :
    RelCT isa (fun x y => VSkipRun R₀ base kp sp T A fA fB top (p + 1) x ∧
      VSkipRun R₀ base kp sp T A fA fB top (p + 1) y) skipTop (fun _ _ => True) := by
  have w (x : State) (h : VSkipRun R₀ base kp sp T A fA fB top (p + 1) x) :
      WP isa (.block (batchBegin ++ digitsAt)) x fun u => u.gpr .rdi = base ∧
        u.zf = some (decide (fA p = 0 ∧ fB p = 0)) := by
    obtain ⟨_, _, _, _, _, h⟩ := h
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
  refine seq_same (skipLoadTop_ct fun x h => by
    obtain ⟨_, _, _, _, _, h⟩ := h; exact ⟨h.loop.ctx.scratch, h.loop.counter⟩) w ?_
  refine VG.RelCT.ite (fun x y h => by simp only [eval, h.1.2, h.2.2]) ?_ ?_
  · exact cmpSelf_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact batchTest_ct.mono (fun x y h => h.1.1.1.trans h.1.2.1.symm) (fun _ _ h => h)

/-- The windows in the lanes, `vstore` aside: the trace depends on the digits alone. -/
theorem vloops_ct {R₀ : State → Prop} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat}
    {top : Nat} (hdg : Digits fA fB top) {G : State → Prop}
    (hst : RelCT isa (fun x y => VLoopRun R₀ base kp sp T A fA fB top 0 x ∧
      VLoopRun R₀ base kp sp T A fA fB top 0 y) (.block vstore) (fun x y => G x ∧ G y)) :
    RelCT isa (fun x y => VSkipRun R₀ base kp sp T A fA fB top (top + 1) x ∧
      VSkipRun R₀ base kp sp T A fA fB top (top + 1) y)
      (.seq (.loop skipTop .ne) (.seq vaddsAt (.seq (.block batchTest)
        (.seq (.ite .ne (.loop vstepAt .ne) (.block [])) (.block vstore))))) (fun x y => G x ∧ G y) := by
  -- The skipping, a step at a time, from the same counter in both runs.
  refine VG.RelCT.seq (R := fun x y => ∃ p, p ≤ top ∧
    VAtRun R₀ base kp sp T A fA fB ((2 : Int) • winVal A fA fB top (p + 1)) p x ∧
    VAtRun R₀ base kp sp T A fA fB ((2 : Int) • winVal A fA fB top (p + 1)) p y) ?_ ?_
  · refine (VG.RelCT.loop (M := isa) (fun q x y => VSkipRun R₀ base kp sp T A fA fB top q x ∧
      VSkipRun R₀ base kp sp T A fA fB top q y) ?_ (top + 1)).mono (fun x y h => ⟨h.1, h.2⟩) (fun _ _ h => h)
    intro q
    rcases q with _ | p
    · exact VG.RelCT.of_false fun _ _ h => by
        obtain ⟨_, _, _, _, _, h⟩ := h.1; exact Nat.lt_irrefl 0 h.pos
    have hw (x : State) (h : VSkipRun R₀ base kp sp T A fA fB top (p + 1) x) : WP isa skipTop x fun u =>
        u.zf = some (skipStops fA fB p) ∧
        (skipStops fA fB p = true →
          VAtRun R₀ base kp sp T A fA fB ((2 : Int) • winVal A fA fB top (p + 1)) p u ∧ p ≤ top) ∧
        (skipStops fA fB p = false → VSkipRun R₀ base kp sp T A fA fB top p u) := by
      obtain ⟨s₀, s₃, r₀, k, m, h⟩ := h
      have hle := h.le
      exact WP.mono (vskipTop_ok hdg h) fun u ⟨uz, ut, uf⟩ =>
        ⟨uz, fun ht => ⟨⟨s₀, s₃, r₀, k, m, ut ht⟩, by omega⟩, fun hf => ⟨s₀, s₃, r₀, k, m, uf hf⟩⟩
    refine (VG.RelCT.wp (vskipTop_ct (p := p) hdg) fun x y h => ⟨hw x h.1, hw y h.2⟩).mono
      (fun _ _ h => h) ?_
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
      exact ⟨p, by obtain ⟨_, _, _, _, _, h⟩ := xf hs; have := h.le; omega, xf hs, yf hs⟩
  -- From the position the skipping stopped at.
  refine VG.RelCT.exists_ fun p => ?_
  refine (VG.RelCT.exists_ (P := fun (_ : p ≤ top) x y =>
    VAtRun R₀ base kp sp T A fA fB ((2 : Int) • winVal A fA fB top (p + 1)) p x ∧
    VAtRun R₀ base kp sp T A fA fB ((2 : Int) • winVal A fA fB top (p + 1)) p y) fun hp => ?_).mono
    (fun x y h => ⟨h.1, h.2⟩) (fun _ _ h => h)
  refine seq_both (vaddsAt_ct hdg hp) (F := VLoopRun R₀ base kp sp T A fA fB top p) (fun x h => by
    obtain ⟨s₀, s₃, r₀, k, m, h⟩ := h
    exact WP.mono (vaddsAt_ok hdg hp h) fun u hu =>
      ⟨s₀, s₃, r₀, k, m, hu.congr (by rw [winVal_step A fA fB hp])⟩) ?_
  have wt (x : State) (h : VLoopRun R₀ base kp sp T A fA fB top p x) : WP isa (.block batchTest) x fun u =>
      u.zf = some (decide (p = 0)) ∧ VLoopRun R₀ base kp sp T A fA fB top p u := by
    obtain ⟨s₀, s₃, r₀, k, m, hb⟩ := h
    exact WP.mono (WP.vk (counterTest_ok hb.ctx.scratch (by have := hdg.top; omega) hb.counter))
      fun c ⟨⟨cz, kc⟩, cx, cy⟩ => ⟨cz, s₀, s₃, r₀, k, m, hb.of_scalar kc (by decide) cx cy⟩
  refine VG.RelCT.seq (R := fun (x y : State) => (x.zf = some (decide (p = 0)) ∧
    VLoopRun R₀ base kp sp T A fA fB top p x) ∧ (y.zf = some (decide (p = 0)) ∧
    VLoopRun R₀ base kp sp T A fA fB top p y)) ((VG.RelCT.wp (rdi_ct (fun x h => by
      obtain ⟨_, _, _, _, _, h⟩ := h; exact h.ctx.scratch.rdi) batchTest_ct)
    fun x y h => ⟨wt x h.1, wt y h.2⟩).mono (fun _ _ h => h) (fun _ _ h => h.2)) ?_
  have ec (x : State) (h : x.zf = some (decide (p = 0))) : isa.eval .ne x = some (!decide (p = 0)) := by
    show eval .ne x = _; simp only [eval, h, Option.map_some]
  refine VG.RelCT.seq (R := fun x y => VLoopRun R₀ base kp sp T A fA fB top 0 x ∧
    VLoopRun R₀ base kp sp T A fA fB top 0 y) ?_ hst
  refine VG.RelCT.ite (fun x y h => (ec x h.1.1).trans (ec y h.2.1).symm) ?_ ?_
  · have hp0 (x y : State) (h : ((x.zf = some (decide (p = 0)) ∧ VLoopRun R₀ base kp sp T A fA fB top p x) ∧
        (y.zf = some (decide (p = 0)) ∧ VLoopRun R₀ base kp sp T A fA fB top p y)) ∧
        isa.eval .ne x = some true) : 0 < p := by
      rw [ec x h.1.1.1] at h
      have := h.2
      simp only [Option.some.injEq, Bool.not_eq_true', decide_eq_false_iff_not] at this
      omega
    refine (VG.RelCT.loop (M := isa) (fun n x y => VLoopRun R₀ base kp sp T A fA fB top n x ∧
      VLoopRun R₀ base kp sp T A fA fB top n y ∧ 0 < n ∧ n ≤ top) ?_ p).mono
      (fun x y h => ⟨h.1.1.2, h.1.2.2, hp0 x y h, hp⟩) (fun _ _ h => h)
    intro n
    rcases n with _ | m
    · exact VG.RelCT.of_false fun _ _ h => Nat.lt_irrefl 0 h.2.2.1
    by_cases hm : m + 1 ≤ top
    swap
    · exact VG.RelCT.of_false fun _ _ h => hm h.2.2.2
    have ws (x : State) (h : VLoopRun R₀ base kp sp T A fA fB top (m + 1) x) : WP isa vstepAt x fun u =>
        u.zf = some (decide (m = 0)) ∧ VLoopRun R₀ base kp sp T A fA fB top m u := by
      obtain ⟨s₀, s₃, r₀, k, mm, h⟩ := h
      exact WP.mono (vstepAt_ok hdg (by omega) h) fun u ⟨uz, hu⟩ => ⟨uz, s₀, s₃, r₀, k, mm, hu⟩
    refine (VG.RelCT.wp (vstepAt_ct hdg (by omega)) fun x y h => ⟨ws x h.1, ws y h.2⟩).mono
      (fun x y h => ⟨h.1, h.2.1⟩) ?_
    have em (x : State) (h : x.zf = some (decide (m = 0))) : isa.eval .ne x = some (!decide (m = 0)) := by
      show eval .ne x = _; simp only [eval, h, Option.map_some]
    intro x y ⟨_, ⟨xz, xl⟩, ⟨yz, yl⟩⟩
    refine ⟨(em x xz).trans (em y yz).symm, fun he => ?_, fun he => ⟨m, by omega, xl, yl, ?_, by omega⟩⟩
    · rw [em x xz] at he
      simp only [Option.some.injEq, Bool.not_eq_false', decide_eq_true_eq] at he
      subst he
      exact ⟨xl, yl⟩
    · rw [em x xz] at he
      simp only [Option.some.injEq, Bool.not_eq_true', decide_eq_false_iff_not] at he
      omega
  · refine VG.RelCT.block_nil fun x y h => ?_
    have hp0 : p = 0 := by
      have := h.2; rw [ec x h.1.1.1] at this; simpa using this
    subst hp0
    exact ⟨h.1.1.2, h.1.2.2⟩

/-! ## The windows -/

theorem windows_ct {R₀ : State → Prop} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat}
    {top : Nat} (hdg : Digits fA fB top) :
    RelCT isa (fun x y => StartRun R₀ base kp sp T A fA fB top x ∧ StartRun R₀ base kp sp T A fA fB top y)
      Impl.Ed25519.X86_64.Ifma.windows (fun _ _ => True) := by
  let G₁ : State → Prop := fun t₁ => t₁.gpr .rdi = base ∧
    WP isa (.block mxRestore) t₁ (LoopRun R₀ base kp sp T A fA fB top 0)
  let G₀ : State → Prop := fun t₀ => t₀.gpr .rdi = base ∧ WP isa (.block [.lfence]) t₀ G₁
  -- The windows, from the lanes' start to the end of `vstore`.
  have hX := vloops_ct (R₀ := R₀) (base := base) (kp := kp) (sp := sp) (T := T) (A := A) hdg (G := G₀)
    (last_both (rdi_ct (fun x h => by obtain ⟨_, _, _, _, _, h⟩ := h; exact h.ctx.scratch.rdi) vstore_ct)
      fun x h => exit_ok h)
  have hXL := VG.RelCT.seq hX (last_both (lfence_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h))
      fun x h => h.2)
  rw [Impl.Ed25519.X86_64.Ifma.windows, withMx_eq]
  refine seq_same (rdi_ct (fun x h => by obtain ⟨_, _, h⟩ := h; exact h.loop.ctx.scratch.rdi) vprep_ct)
    (fun x h => enter_ok h) ?_
  refine seq_same (rdi_ct (fun x h => h.1) mxSave_ct) (fun x h => h.2) ?_
  refine VG.RelCT.seq (seq_both (rdi_ct (fun x h => h.1) mxLoad_ct) (fun x h => h.2) hXL) ?_
  exact rdi_ct (fun x h => h.1) mxRestore_ct |>.mono (fun _ _ h => h) (fun _ _ h => h)

instance : EdWindows Impl.Ed25519.X86_64.Ifma.windows where
  ok hdg h := by
    refine WP.mono (windows_ok (R₀ := (· = _)) hdg ⟨_, rfl, h⟩) fun t ht => ?_
    obtain ⟨_, rfl, ht⟩ := ht
    exact ht
  ct hdg := (VG.RelCT.wp (windows_ct hdg) fun x y h =>
    ⟨windows_ok hdg h.1, windows_ok hdg h.2⟩).mono (fun _ _ h => h) (fun _ _ h => h.2)

end VG.Proof.Ed25519.X86_64.Ifma
