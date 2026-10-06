import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.VerifyWin
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.VerifyLit

/-!
# Ed25519 verification with AVX512_IFMA: the windows' trace

`Ifma.windows` leaks what `windows` does: its branches are on the counter and
on the digits of the public scalars (`DigitCT`), and its addresses are the
scratch plus constants, the counter or a digit. The blocks between the
branches are checked by the taint analysis, with the scratch's address public
and, for an entry's addition, its digit.
-/

namespace VG.Proof.Ed25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Ifma VG.Proof.Ed25519
  VG.Proof.Ed25519.X86_64 Edwards
open VG.Proof.X25519.X86_64 (Outside off clob Keeps)

/-! ## The blocks -/

theorem vdbl4_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) vdbl4 (fun _ _ => True) :=
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

/-! ## Windows -/

/-- A window's start in the lanes, in one run: its digit is `v`, and the counter `C`. -/
structure VWinPre (base kp sp T : Addr) (A : EPoint dZ) (C : Addr) (digit : List Instr) (v : Nat)
    (s : State) : Prop where
  ctx : WinCtx base kp sp T A s
  consts : EConsts s.mem base
  small : Small s
  value : ∃ a, Rep (lanePt s) a
  counter : s.mem.readW (off base 56) 64 = C
  digit : DigitSpec base s digit v
  bound : v < 16

theorem vdigitAdd_ct {base kp sp T : Addr} {A : EPoint dZ} {C : Addr} {digit : List Instr} {v o : Nat}
    (hdig : DigitCT base kp sp T A C digit)
    (hadd : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rbx = y.gpr .rbx)
      (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ tableAddr o ++ vrows ++ esplit ++ vadd))
      (fun _ _ => True)) :
    RelCT isa (fun x y => VWinPre base kp sp T A C digit v x ∧ VWinPre base kp sp T A C digit v y)
      (.seq (.block digit) (vaddDigit o)) (fun _ _ => True) := by
  have hw (x : State) (h : VWinPre base kp sp T A C digit v x) : WP isa (.block digit) x fun u =>
      u.gpr .rdi = base ∧ u.gpr .rbx = BitVec.ofNat 64 v ∧ u.zf = some (decide (v = 0)) :=
    WP.mono (h.digit x (WinKeep.refl _ _)) fun u ⟨uv, uz, ku⟩ =>
      ⟨(ku.1 _ (by decide)).trans h.ctx.scratch.rdi, uv, uz⟩
  refine VG.RelCT.seq (VG.RelCT.wp (hdig.mono (fun _ _ h => ⟨⟨h.1.ctx, h.1.counter⟩,
    ⟨h.2.ctx, h.2.counter⟩⟩) (fun _ _ h => h)) fun x y h => ⟨hw x h.1, hw y h.2⟩) ?_
  rw [vaddDigit]
  refine VG.RelCT.ite (fun x y h => ?_) ?_ (VG.RelCT.block_nil fun _ _ _ => trivial)
  · simp only [eval, h.2.1.2.2, h.2.2.2.2]
  · exact hadd.mono (fun x y h => ⟨h.1.2.1.1.trans h.1.2.2.1.symm, h.1.2.1.2.1.trans h.1.2.2.2.1.symm⟩)
      (fun _ _ h => h)

theorem vwindowA_ct {base kp sp T : Addr} {A : EPoint dZ} {C : Addr} {digit : List Instr} {v : Nat}
    (hdig : DigitCT base kp sp T A C digit) :
    RelCT isa (fun x y => VWinPre base kp sp T A C digit v x ∧ VWinPre base kp sp T A C digit v y)
      (vwindowA digit) (fun _ _ => True) := by
  have hw (x : State) (h : VWinPre base kp sp T A C digit v x) :
      WP isa vdbl4 x (VWinPre base kp sp T A C digit v) := by
    obtain ⟨a, ha⟩ := h.value
    refine WP.mono (vdbl4_ok h.ctx.scratch h.consts h.small ha) fun b ⟨bg, brd, bwr, bo, bsm, br⟩ => ?_
    have kb : LKeep base x b := ⟨fun r _ _ hr => bg r hr, bg _ (by decide), brd, bwr, bo⟩
    exact ⟨h.ctx.of_keep kb.win, kb.consts h.consts, bsm, ⟨_, br⟩, kb.win.counter.trans h.counter,
      h.digit.of_keep kb.win, h.bound⟩
  rw [vwindowA]
  exact seq_same (rdi_ct (fun x h => h.ctx.scratch.rdi) vdbl4_ct) hw (vdigitAdd_ct hdig vaddBodyA_ct)

/-- After a window of `k` alone, the next digit's start. -/
theorem vwindowA_next {base kp sp T : Addr} {A : EPoint dZ} {C : Addr} {digit next : List Instr}
    {v w : Nat} {x : State} (hsc : digit.all scalarI = true)
    (h : VWinPre base kp sp T A C digit v x ∧ DigitSpec base x next w ∧ w < 16) :
    WP isa (vwindowA digit) x (VWinPre base kp sp T A C next w) := by
  obtain ⟨a, ha⟩ := h.1.value
  refine WP.mono (vwindowA_ok h.1.ctx h.1.consts h.1.small ha hsc h.1.bound h.1.digit)
    fun b ⟨br, bsm, kb⟩ => ?_
  exact ⟨h.1.ctx.of_keep kb.win, kb.consts h.1.consts, bsm, ⟨_, br⟩, kb.win.counter.trans h.1.counter,
    h.2.1.of_keep kb.win, h.2.2⟩

/-- The addition of `S`'s byte in the lanes: the branch is on the byte, its entry's address
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

/-! ## Bytes -/

/-- After `batchBegin`: the counter is `i`, and the scalars' bytes are those of `K` and `S`. -/
theorem vbyteBegin_ok {s₃ x : State} {base kp sp T : Addr} {A : EPoint dZ} {K S i : Nat} (hi : i < 64)
    (h : VLoop s₃ base kp sp T A K S (i + 1) x) :
    WP isa (.block batchBegin) x fun a => WinCtx base kp sp T A a ∧ EConsts a.mem base ∧ Small a ∧
      (∃ v, Rep (lanePt a) v) ∧ a.mem.readW (off base 56) 64 = BitVec.ofNat 64 i ∧
      (a.mem (off kp i)).toNat = K / 256 ^ i % 256 ∧
      (i < 32 → (a.mem (off (off sp 32) i)).toNat = S / 256 ^ i % 256) := by
  refine WP.mono (vbatchBegin_ok h.ctx.scratch i h.counter) fun a ⟨av, ka, ax, ay⟩ => ?_
  obtain ⟨pa, sa⟩ := lanePt_vec ax ay
  refine ⟨h.ctx.of_byte ka.byte, ka.consts h.consts, sa h.small, ⟨_, by rw [pa]; exact h.value⟩, av, ?_,
    fun hi32 => ?_⟩
  · rw [scalar_byte (n := 64) hi, ka.byte.bytesK h.ctx, h.kVal]
  · rw [scalar_byte (n := 32) hi32, ka.byte.bytesS h.ctx, h.sVal]

theorem vbyteStepA_ct {base kp sp T : Addr} {A : EPoint dZ} {K S i : Nat} (hi : i < 64) :
    RelCT isa (fun x y => (∃ s₃, VLoop s₃ base kp sp T A K S (i + 1) x) ∧
      (∃ s₃, VLoop s₃ base kp sp T A K S (i + 1) y)) vbyteStepA (fun _ _ => True) := by
  let C := BitVec.ofNat 64 i
  let vH := K / 256 ^ i % 256 / 16
  let vL := K / 256 ^ i % 256 % 16
  have w1 (x : State) (h : ∃ s₃, VLoop s₃ base kp sp T A K S (i + 1) x) :
      WP isa (.block batchBegin) x fun a => VWinPre base kp sp T A C (digitHigh 7952 0) vH a ∧
        DigitSpec base a (digitLow 7952 0) vL ∧ vL < 16 := by
    obtain ⟨s₃, h⟩ := h
    refine WP.mono (vbyteBegin_ok hi h) fun a ⟨actx, ak, asm, av, ac, akb, _⟩ => ?_
    refine ⟨⟨actx, ak, asm, av, ac, ?_, nibble_lt _⟩, ?_, Nat.mod_lt _ (by decide)⟩
    · rw [show vH = (a.mem (off kp i)).toNat / 16 by rw [akb]]; exact digitKHigh actx hi ac
    · rw [show vL = (a.mem (off kp i)).toNat % 16 by rw [akb]]; exact digitKLow actx hi ac
  have w3 (x : State) (h : VWinPre base kp sp T A C (digitLow 7952 0) vL x) :
      WP isa (vwindowA (digitLow 7952 0)) x fun c => c.gpr .rdi = base := by
    obtain ⟨a, ha⟩ := h.value
    exact WP.mono (vwindowA_ok h.ctx h.consts h.small ha (by decide) h.bound h.digit) fun _ ⟨_, _, kc⟩ =>
      (kc.scratch h.ctx.scratch).rdi
  rw [vbyteStepA]
  refine seq_same (rdi_ct (fun x h => by obtain ⟨_, h⟩ := h; exact h.ctx.scratch.rdi) batchBegin_ct)
    w1 ?_
  refine seq_same ((vwindowA_ct digitKHigh_ct).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) (fun _ _ h => h))
    (fun x h => vwindowA_next (by decide) h) ?_
  exact seq_same (vwindowA_ct digitKLow_ct) w3 (rdi_ct (fun _ h => h) counterCmp_ct)

/-- After a byte's windows of `k` in the lanes, before `S`'s byte `v` is read and added. -/
structure VSPre (base kp sp T : Addr) (A : EPoint dZ) (C : Addr) (i v : Nat) (x : State) : Prop where
  ctx : WinCtx base kp sp T A x
  consts : EConsts x.mem base
  small : Small x
  value : ∃ a, Rep (lanePt x) a
  counter : x.mem.readW (off base 56) 64 = C
  byte : (x.mem (off (off sp 32) i)).toNat = v
  hi : i < 32

theorem vbyteStepAB_ct {base kp sp T : Addr} {A : EPoint dZ} {K S i : Nat} (hi : i < 32) :
    RelCT isa (fun x y => (∃ s₃, VLoop s₃ base kp sp T A K S (i + 1) x) ∧
      (∃ s₃, VLoop s₃ base kp sp T A K S (i + 1) y)) vbyteStepAB (fun _ _ => True) := by
  let C := BitVec.ofNat 64 i
  let kH := K / 256 ^ i % 256 / 16
  let kL := K / 256 ^ i % 256 % 16
  let vS := S / 256 ^ i % 256
  have w1 (x : State) (h : ∃ s₃, VLoop s₃ base kp sp T A K S (i + 1) x) :
      WP isa (.block batchBegin) x fun a =>
        (VWinPre base kp sp T A C (digitHigh 7952 0) kH a ∧ (DigitSpec base a (digitLow 7952 0) kL ∧
          kL < 16)) ∧ (a.mem (off (off sp 32) i)).toNat = vS := by
    obtain ⟨s₃, h⟩ := h
    refine WP.mono (vbyteBegin_ok (by omega) h) fun a ⟨actx, ak, asm, av, ac, akb, asb⟩ => ?_
    refine ⟨⟨⟨actx, ak, asm, av, ac, ?_, nibble_lt _⟩, ?_, Nat.mod_lt _ (by decide)⟩, asb hi⟩
    · rw [show kH = (a.mem (off kp i)).toNat / 16 by rw [akb]]; exact digitKHigh actx (by omega) ac
    · rw [show kL = (a.mem (off kp i)).toNat % 16 by rw [akb]]; exact digitKLow actx (by omega) ac
  have whi (x : State) (h : (VWinPre base kp sp T A C (digitHigh 7952 0) kH x ∧
      (DigitSpec base x (digitLow 7952 0) kL ∧ kL < 16)) ∧ (x.mem (off (off sp 32) i)).toNat = vS) :
      WP isa (vwindowA (digitHigh 7952 0)) x fun b =>
        VWinPre base kp sp T A C (digitLow 7952 0) kL b ∧ (b.mem (off (off sp 32) i)).toNat = vS := by
    obtain ⟨a, ha⟩ := h.1.1.value
    refine WP.mono (vwindowA_ok h.1.1.ctx h.1.1.consts h.1.1.small ha (by decide) h.1.1.bound
      h.1.1.digit) fun b ⟨br, bsm, kb⟩ => ?_
    exact ⟨⟨h.1.1.ctx.of_keep kb.win, kb.consts h.1.1.consts, bsm, ⟨_, br⟩,
      kb.win.counter.trans h.1.1.counter, h.1.2.1.of_keep kb.win, h.1.2.2⟩,
      by rw [h.1.1.ctx.byteS kb.win hi]; exact h.2⟩
  have wlo (x : State) (h : VWinPre base kp sp T A C (digitLow 7952 0) kL x ∧
      (x.mem (off (off sp 32) i)).toNat = vS) :
      WP isa (vwindowA (digitLow 7952 0)) x (VSPre base kp sp T A C i vS) := by
    obtain ⟨a, ha⟩ := h.1.value
    refine WP.mono (vwindowA_ok h.1.ctx h.1.consts h.1.small ha (by decide) h.1.bound h.1.digit)
      fun b ⟨br, bsm, kb⟩ => ?_
    exact ⟨h.1.ctx.of_keep kb.win, kb.consts h.1.consts, bsm, ⟨_, br⟩,
      kb.win.counter.trans h.1.counter, by rw [h.1.ctx.byteS kb.win hi]; exact h.2, hi⟩
  have wS (x : State) (h : VSPre base kp sp T A C i vS x) :
      WP isa (.block digitS) x fun u => BasePre base T vS u ∧ VSPre base kp sp T A C i vS u := by
    refine WP.mono (WP.vk (digitS_ok h.ctx.scratch h.ctx.sHeader i h.counter (h.ctx.sRead i hi)))
      fun u ⟨⟨uv, uz, ku⟩, ux, uy⟩ => ?_
    have kw : LKeep base x u := LKeep.of_keeps ku (by decide)
    have hu := h.ctx.of_keep kw.win
    obtain ⟨pu, su⟩ := lanePt_vec ux uy
    refine ⟨⟨hu.scratch, hu.bHeader, by rw [uv, h.byte], by rw [uz, h.byte],
      by rw [← h.byte]; have := (x.mem (off (off sp 32) i)).isLt; omega⟩,
      ⟨hu, kw.consts h.consts, su h.small, by rw [pu]; exact h.value, kw.win.counter.trans h.counter,
      by rw [h.ctx.byteS kw.win hi]; exact h.byte, hi⟩⟩
  have wB (x : State) (h : BasePre base T vS x ∧ VSPre base kp sp T A C i vS x) :
      WP isa vaddBase x fun c => c.gpr .rdi = base := by
    obtain ⟨a, ha⟩ := h.2.value
    refine WP.mono (vaddBase_ok h.1.scratch h.2.consts h.2.small h.1.header h.2.ctx.bTab vS h.1.bound
      h.1.rbx h.1.zf ha) fun _ ⟨_, _, kc⟩ => (kc.win.scratch h.1.scratch).rdi
  rw [vbyteStepAB]
  refine seq_same (rdi_ct (fun x h => by obtain ⟨_, h⟩ := h; exact h.ctx.scratch.rdi) batchBegin_ct)
    w1 ?_
  refine seq_same ((vwindowA_ct digitKHigh_ct).mono (fun _ _ h => ⟨h.1.1.1, h.2.1.1⟩) (fun _ _ h => h))
    whi ?_
  refine seq_same ((vwindowA_ct digitKLow_ct).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) (fun _ _ h => h))
    wlo ?_
  refine seq_same (digitS_ct.mono (fun _ _ h => ⟨⟨h.1.ctx, h.1.counter⟩, ⟨h.2.ctx, h.2.counter⟩⟩)
    (fun _ _ h => h)) wS ?_
  exact seq_same (vaddBase_ct.mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) (fun _ _ h => h)) wB
    (rdi_ct (fun _ h => h) batchTest_ct)

/-! ## Loops -/

theorem VRun.loop {R₀ : State → Prop} {base kp sp T : Addr} {A : EPoint dZ} {K S c : Nat} {x : State}
    (h : VRun R₀ base kp sp T A K S c x) : ∃ s₃, VLoop s₃ base kp sp T A K S c x :=
  let ⟨_, s₃, _, _, _, h⟩ := h; ⟨s₃, h⟩

theorem VRun.rdi {R₀ : State → Prop} {base kp sp T : Addr} {A : EPoint dZ} {K S c : Nat} {x : State}
    (h : VRun R₀ base kp sp T A K S c x) : x.gpr .rdi = base :=
  let ⟨_, _, _, _, _, h⟩ := h; h.ctx.scratch.rdi

theorem vloopA_ct {R₀ : State → Prop} {base kp sp T : Addr} {A : EPoint dZ} {K S : Nat} (n : Nat)
    (hn0 : 0 < n) (hn : n ≤ 32) :
    RelCT isa (fun x y => VRun R₀ base kp sp T A K S (32 + n) x ∧ VRun R₀ base kp sp T A K S (32 + n) y)
      (.loop vbyteStepA .ne)
      (fun x y => VRun R₀ base kp sp T A K S 32 x ∧ VRun R₀ base kp sp T A K S 32 y) := by
  refine (VG.RelCT.loop (M := isa) (fun n x y => (VRun R₀ base kp sp T A K S (32 + n) x ∧
    VRun R₀ base kp sp T A K S (32 + n) y) ∧ 0 < n ∧ n ≤ 32) ?_ n).mono
      (fun _ _ h => ⟨h, hn0, hn⟩) (fun _ _ h => h)
  intro n
  rcases n with _ | j
  · exact VG.RelCT.of_false fun _ _ h => Nat.lt_irrefl 0 h.2.1
  by_cases hj : j < 32
  · have hw (x : State) (h : VRun R₀ base kp sp T A K S (32 + (j + 1)) x) :
        WP isa vbyteStepA x fun u => u.zf = some (decide (j = 0)) ∧
          VRun R₀ base kp sp T A K S (32 + j) u := by
      obtain ⟨s₀, s₃, r₀, k₀, m₀, h⟩ := h
      exact WP.mono (vstepA_ok hj h) fun u ⟨uz, hu⟩ => ⟨uz, s₀, s₃, r₀, k₀, m₀, hu⟩
    refine (VG.RelCT.wp ((vbyteStepA_ct (i := 32 + j) (by omega)).mono
      (fun x y h => ⟨h.1.1.loop, h.1.2.loop⟩) (fun _ _ h => h))
      fun x y h => ⟨hw x h.1.1, hw y h.1.2⟩).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨xz, hx⟩, ⟨yz, hy⟩⟩
    have ex : isa.eval .ne x = some (!decide (j = 0)) := by
      show eval .ne x = _; simp only [eval, xz, Option.map_some]
    have ey : isa.eval .ne y = some (!decide (j = 0)) := by
      show eval .ne y = _; simp only [eval, yz, Option.map_some]
    refine ⟨ex.trans ey.symm, fun he => ?_, fun he => ?_⟩
    · have : j = 0 := by
        by_contra hne
        rw [ex, decide_eq_false hne] at he
        cases he
      subst this
      exact ⟨hx, hy⟩
    · have : j ≠ 0 := by
        intro hz
        rw [ex, hz] at he
        cases he
      exact ⟨j, by omega, ⟨hx, hy⟩, by omega, by omega⟩
  · exact VG.RelCT.of_false fun _ _ h => hj (by omega)

theorem vloopB_ct {R₀ : State → Prop} {base kp sp T : Addr} {A : EPoint dZ} {K S : Nat} :
    RelCT isa (fun x y => VRun R₀ base kp sp T A K S 32 x ∧ VRun R₀ base kp sp T A K S 32 y)
      (.loop vbyteStepAB .ne)
      (fun x y => VRun R₀ base kp sp T A K S 0 x ∧ VRun R₀ base kp sp T A K S 0 y) := by
  refine (VG.RelCT.loop (M := isa) (fun n x y => (VRun R₀ base kp sp T A K S n x ∧
    VRun R₀ base kp sp T A K S n y) ∧ 0 < n ∧ n ≤ 32) ?_ 32).mono
      (fun _ _ h => ⟨h, by decide, by decide⟩) (fun _ _ h => h)
  intro n
  rcases n with _ | j
  · exact VG.RelCT.of_false fun _ _ h => Nat.lt_irrefl 0 h.2.1
  by_cases hj : j < 32
  · have hw (x : State) (h : VRun R₀ base kp sp T A K S (j + 1) x) :
        WP isa vbyteStepAB x fun u => u.zf = some (decide (j = 0)) ∧ VRun R₀ base kp sp T A K S j u := by
      obtain ⟨s₀, s₃, r₀, k₀, m₀, h⟩ := h
      exact WP.mono (vstepB_ok hj h) fun u ⟨uz, hu⟩ => ⟨uz, s₀, s₃, r₀, k₀, m₀, hu⟩
    refine (VG.RelCT.wp ((vbyteStepAB_ct (i := j) hj).mono
      (fun x y h => ⟨h.1.1.loop, h.1.2.loop⟩) (fun _ _ h => h))
      fun x y h => ⟨hw x h.1.1, hw y h.1.2⟩).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨xz, hx⟩, ⟨yz, hy⟩⟩
    have ex : isa.eval .ne x = some (!decide (j = 0)) := by
      show eval .ne x = _; simp only [eval, xz, Option.map_some]
    have ey : isa.eval .ne y = some (!decide (j = 0)) := by
      show eval .ne y = _; simp only [eval, yz, Option.map_some]
    refine ⟨ex.trans ey.symm, fun he => ?_, fun he => ?_⟩
    · have : j = 0 := by
        by_contra hne
        rw [ex, decide_eq_false hne] at he
        cases he
      subst this
      exact ⟨hx, hy⟩
    · have : j ≠ 0 := by
        intro hz
        rw [ex, hz] at he
        cases he
      exact ⟨j, by omega, ⟨hx, hy⟩, by omega, by omega⟩
  · exact VG.RelCT.of_false fun _ _ h => hj (by omega)

theorem vwindowsA_ct {R₀ : State → Prop} {base kp sp T : Addr} {A : EPoint dZ} {K S c : Nat}
    (hc32 : 32 ≤ c) (hc64 : c ≤ 64) :
    RelCT isa (fun x y => VRun R₀ base kp sp T A K S c x ∧ VRun R₀ base kp sp T A K S c y) vwindowsA
      (fun x y => VRun R₀ base kp sp T A K S 32 x ∧ VRun R₀ base kp sp T A K S 32 y) := by
  have hw (x : State) (h : VRun R₀ base kp sp T A K S c x) : WP isa (.block counterCmp) x fun u =>
      u.zf = some (decide (c = 32)) ∧ VRun R₀ base kp sp T A K S c u := by
    obtain ⟨s₀, s₃, r₀, k₀, m₀, h⟩ := h
    rw [counterCmp]
    refine WP.mono (WP.vk (counterCmp_ok h.ctx.scratch c hc64 h.counter)) fun u ⟨⟨uz, ku⟩, ux, uy⟩ => ?_
    obtain ⟨pu, su⟩ := lanePt_vec ux uy
    have kb : BKeep base x u := BKeep.of_keeps ku (by decide)
    exact ⟨uz, s₀, s₃, r₀, k₀, m₀, h.ctx.of_byte kb.byte, by rw [kb.d]; exact h.d,
      by rw [ku.2.1]; exact h.counter, by rw [kb.byte.bytesK h.ctx, h.kVal],
      by rw [kb.byte.bytesS h.ctx, h.sVal], by rw [pu]; exact h.value, su h.small, kb.consts h.consts,
      h.keep.trans kb⟩
  have hcmp : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block counterCmp) (fun _ _ => True) := by
    rw [counterCmp]; exact counterCmp_ct
  rw [vwindowsA]
  refine VG.RelCT.seq ((VG.RelCT.wp (rdi_ct (fun x h => h.rdi) hcmp)
    fun x y h => ⟨hw x h.1, hw y h.2⟩).mono (fun _ _ h => h) (fun _ _ h => h.2)) ?_
  refine VG.RelCT.ite (fun x y h => by simp only [eval, h.1.1, h.2.1]) ?_ ?_
  · obtain ⟨n, rfl⟩ : ∃ n, c = 32 + n := ⟨c - 32, by omega⟩
    by_cases hn : n = 0
    · subst hn
      exact VG.RelCT.of_false fun x y h => by
        have := h.2; simp only [eval, h.1.1.1, Option.map_some] at this; simp at this
    · exact (vloopA_ct n (by omega) (by omega)).mono (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩)
        (fun _ _ h => h)
  · refine VG.RelCT.block_nil fun x y h => ?_
    have hc : c = 32 := by
      have := h.2; simp only [eval, h.1.1.1, Option.map_some] at this; simpa using this
    subst hc
    exact ⟨h.1.1.2, h.1.2.2⟩

/-! ## The windows -/

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

theorem windows_ct {R₀ : State → Prop} {base kp sp T : Addr} {A : EPoint dZ} {K S c : Nat}
    (hc32 : 32 ≤ c) (hc64 : c ≤ 64) :
    RelCT isa (fun x y => LoopRun R₀ base kp sp T A K S c x ∧ LoopRun R₀ base kp sp T A K S c y)
      Impl.Ed25519.X86_64.Ifma.windows (fun _ _ => True) := by
  let G₁ : State → Prop := fun t₁ => t₁.gpr .rdi = base ∧
    WP isa (.block mxRestore) t₁ (LoopRun R₀ base kp sp T A K S 0)
  let G₀ : State → Prop := fun t₀ => t₀.gpr .rdi = base ∧ WP isa (.block [.lfence]) t₀ G₁
  -- The windows, from the lanes' start to the end of `vstore`.
  have hX : RelCT isa (fun x y => VStart R₀ base kp sp T A K S c x ∧ VStart R₀ base kp sp T A K S c y)
      (.seq vwindowsA (.seq (.loop vbyteStepAB .ne) (.block vstore))) (fun x y => G₀ x ∧ G₀ y) :=
    VG.RelCT.seq ((vwindowsA_ct hc32 hc64).mono (fun _ _ h => ⟨h.1.run, h.2.run⟩) (fun _ _ h => h))
      (VG.RelCT.seq vloopB_ct (last_both (rdi_ct (fun x h => h.rdi) vstore_ct) fun x h => exit_ok h))
  have hXL : RelCT isa (fun x y => VStart R₀ base kp sp T A K S c x ∧ VStart R₀ base kp sp T A K S c y)
      (.seq (.seq vwindowsA (.seq (.loop vbyteStepAB .ne) (.block vstore))) (.block [.lfence]))
      (fun x y => G₁ x ∧ G₁ y) :=
    VG.RelCT.seq hX (last_both (lfence_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h))
      fun x h => h.2)
  rw [Impl.Ed25519.X86_64.Ifma.windows, withMx_eq]
  refine seq_same (rdi_ct (fun x h => by obtain ⟨_, _, h⟩ := h; exact h.ctx.scratch.rdi) vprep_ct)
    (fun x h => enter_ok h) ?_
  refine seq_same (rdi_ct (fun x h => h.1) mxSave_ct) (fun x h => h.2) ?_
  refine VG.RelCT.seq (seq_both (rdi_ct (fun x h => h.1) mxLoad_ct) (fun x h => h.2) hXL) ?_
  exact rdi_ct (fun x h => h.1) mxRestore_ct |>.mono (fun _ _ h => h) (fun _ _ h => h)

instance : EdWindows Impl.Ed25519.X86_64.Ifma.windows where
  ok hc32 hc64 h := by
    refine WP.mono (windows_ok (R₀ := (· = _)) hc32 hc64 ⟨_, rfl, h⟩) fun t ht => ?_
    obtain ⟨_, rfl, ht⟩ := ht
    exact ht
  ct hc32 hc64 := (VG.RelCT.wp (windows_ct hc32 hc64) fun x y h =>
    ⟨windows_ok hc32 hc64 h.1, windows_ok hc32 hc64 h.2⟩).mono (fun _ _ h => h) (fun _ _ h => h.2)

end VG.Proof.Ed25519.X86_64.Ifma
