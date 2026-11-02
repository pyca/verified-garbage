module

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.MulFn
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Weierstrass.PointFacts
import VerifiedGarbage.Proof.P384.Point
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.MulLit
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.MulFn
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Weierstrass.PointFacts
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.MulLit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-!
# `vg_p384_mul` on RISC-V: the contract

The facts of `Impl.Weierstrass.Mul.Curve.mulInRangeContract` for P-384 on
RISC-V, by register (`mulRVc`: `ws` in `a0`), and `mulFn` meets them
(`mul_rv`), given the group law: the saves of `s0`, `s1` and `ra` (past the
numbered slots, in the contract's tail), `mulBody_ok`, and the loads that
restore them. The coordinates the specification decodes are the proofs'
(`Point.dec_eq`, given Fermat's little theorem from the group law), and
`Represents` is `Rep`. What the function writes is its own working space or
the result's (`keeps_of_unch`).

`mul_verified` adds the function's constant time, by taint tracking (only the
pointer, in `a0`, public: every address is `s0` plus a constant or plus the
counter's word, and the only branches are on the counter and on the field
functions' pointers), and a state satisfying the precondition (`satState`:
the constants and `G` in Montgomery's form at their slots).
-/

-- `p`, below `2^384`, is evaluated.
set_option exponentiation.threshold 512

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P384

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Spec.Weierstrass (Curve Fe Point)

/-- P-384's curve of `Proof/Weierstrass/MulContract.lean`. -/
abbrev MC : Impl.Weierstrass.Mul.Curve := Impl.Weierstrass.Mul.p384

/-- `vg_p384_mul(ws = a0)`. -/
def mulRVc : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .a0, 8192⟩] ∧ (s.gpr .a0).toNat + 8192 ≤ 2 ^ 64 ∧
    (s.gpr .a0).toNat % 8 = 0 ∧ MC.ConstsOk (s.gpr .a0) s.mem ∧ MC.PointOk (s.gpr .a0) s.mem
  post s s' := MC.ResultInRange (MC.scalar (s.gpr .a0) s.mem) (MC.point (s.gpr .a0) s.mem) (s.gpr .a0) s.mem s'.mem
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0

/-- `Represents` is the proofs' `Rep`. -/
theorem represents_of_rep {C : Curve} {X Y Z : Fe C} {P : Point C}
    (h : Rep C X Y Z P) : Impl.Weierstrass.MulBase.Represents X Y Z P := by
  cases P <;> exact h

/-- The coordinate at an offset below `2³²` is the number `wordsVal` reads. -/
theorem coordAt_eq (m : Mem) (ws : Addr) {o : Nat} (ho : o < 2 ^ 32) :
    MC.toPoint.coordAt m ws o = wordsVal m ws o 6 := by
  unfold Impl.Weierstrass.Point.Curve.coordAt
  rw [Impl.Weierstrass.Mont.numAt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
  exact read_eq_wordsVal m ws 6 o

/-- The saves, at `mulSave = 2224`. -/
abbrev saves : List (Nat × Nat) := [(2224, 8), (2232, 8), (2240, 8)]

/-- What the function writes is its own working space or the result's. -/
theorem keeps_of_unch {ws : Addr} {m m' : Mem} (hu : Unch ws (saves ++ mulBW) m m') : MC.Keeps ws m m' := by
  intro i hi hown hp
  have h8 : Impl.Weierstrass.Mont.wsBytes = 8192 := rfl
  refine hu _ fun w hw => ?_
  rw [show ws + BitVec.ofNat 64 i = off ws i from rfl, ofs_off0 ws (by omega)]
  have hw' := (by decide : ∀ w ∈ saves ++ mulBW, (880 ≤ w.1 ∧ w.1 + w.2 ≤ 1552) ∨ (w.1 = 160 ∧ w.2 = 48) ∨
    2224 ≤ w.1 ∨ (736 ≤ w.1 ∧ w.1 + w.2 ≤ 880)) w hw
  simp only [Impl.Weierstrass.Mul.Curve.Own, Impl.Weierstrass.Mul.Curve.slot, Impl.Weierstrass.Mul.Curve.tmpAt,
    Impl.Weierstrass.Mul.Curve.bitsAt, Impl.Weierstrass.Mul.Curve.pAt, Impl.Weierstrass.Mul.Curve.ptBytes,
    MC, Impl.Weierstrass.Mul.p384, true_and] at hown hp
  omega

/-- `sd t, d(a0)` (`sdAt`) at the working space's base. -/
theorem sdAt_a0 {s : State} {base : Addr} {is : List Instr} {Q : State → Prop} (h0 : s.gpr .a0 = base)
    (hwr : (⟨base, 8192⟩ : Region) ∈ s.wr) (hal : base.toNat % 8 = 0) {t : Reg} (ht : t ≠ .a0) {d : Nat}
    (hd : d + 8 ≤ 4096) (hd8 : d % 8 = 0)
    (k : ∀ s', Mupd s s' (s.mem.writeW (off base d) (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (sdAt t .a0 d ++ is)) s Q :=
  wp_sdAt (by omega) ht (by rw [h0]) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    ⟨_, hwr, Offset.contains_base base (by omega) (by omega)⟩ k

/-- `vg_p384_mul` meets `mulRVc`, given the group law. -/
theorem mul_rv (hL : VG.Proof.Weierstrass.Law W) (s : State) (hs : mulRVc.pre s) :
    ∃ t s', Exec isa mulP384 s t s' ∧ abiPreserved s s' ∧ mulRVc.post s s' := by
  obtain ⟨-, hwr, hfit, hal, ⟨-, hz, hone, ha, hb3⟩, ⟨hx, hy, hon⟩⟩ := hs
  generalize hb : s.gpr .a0 = base at hwr hfit hal hz hone ha hb3 hx hy hon
  have hwr' : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_singleton_self _
  have hpR := unit
  have hp0 : 0 < W.p := by decide
  have ca : ∀ (m : Mem) {o : Nat}, o < 4096 → MC.toPoint.coordAt m base o = wordsVal m base o 6 :=
    fun m _ ho => coordAt_eq m base (by omega)
  have dq : ∀ x, MC.toPoint.dec x = toM W.p (2 ^ 384) x :=
    VG.Proof.Weierstrass.Point.dec_eq MC.toPoint hL.one_ne_zero (VG.Proof.Weierstrass.Point.fermat_of_law hL) hpR
  -- The saves and `s0 = a0`.
  suffices h : WP isa mulP384 s fun s' => abiPreserved s s' ∧ mulRVc.post s s' by
    obtain ⟨t, s', he, h⟩ := h; exact ⟨t, s', he, h⟩
  rw [mulP384, Cfg.mulFn, show p384.mulSave = 2224 from rfl]
  simp only [List.append_assoc]
  rw [← List.append_nil (ldAt .s0 .s0 2224)]
  refine WP.seq (sdAt_a0 hb hwr' hal (by decide) (d := 2224) (by decide) (by decide) fun s₁ u₁ => ?_)
  refine sdAt_a0 (by rw [u₁.gpr]; exact hb) (by rw [u₁.wr]; exact hwr') hal (by decide) (d := 2232) (by decide)
    (by decide) fun s₂ u₂ => ?_
  refine sdAt_a0 (by rw [u₂.gpr, u₁.gpr]; exact hb) (by rw [u₂.wr, u₁.wr]; exact hwr') hal (by decide)
    (d := 2240) (by decide) (by decide) fun s₃ u₃ => wp_mv fun s₄ u₄ => WP.block_nil ?_
  have g₄ : ∀ r, r ≠ .s0 → s₄.gpr r = s.gpr r := fun r hr => by
    rw [u₄.other r hr, u₃.gpr, u₂.gpr, u₁.gpr]
  have hw₄ : WsReg s₄ base := ⟨by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, hb],
    by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hwr', hfit, hal⟩
  have m₄ : s₄.mem = ((s.mem.writeW (off base 2224) (s.gpr .s0)).writeW (off base 2232) (s.gpr .s1)).writeW
      (off base 2240) (s.gpr .ra) := by
    simp only [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr]
  have O₄ : Unch base saves s.mem s₄.mem := by
    rw [m₄]
    exact (((writeW_outside _ _ _ (by omega)).unch.trans (writeW_outside _ _ _ (by omega)).unch).trans
      (writeW_outside _ _ _ (by omega)).unch)
  have sv₄ : ∀ i, i < 45 → sv base s₄ i = sv base s i := fun i hi =>
    O₄.wordsVal (fun w hw => by
      simp only [saves, List.mem_cons, List.not_mem_nil, or_false] at hw
      have : p384.sl i + 48 ≤ 2224 := by simp only [Cfg.sl, slot, p384]; omega
      rcases hw with rfl | rfl | rfl <;> (simp only; omega)) (by simp only [Cfg.sl, slot, p384]; omega)
  have cs : ∀ i, i < 45 → MC.toPoint.coordAt s.mem base (p384.sl i) = sv base s i := fun i hi =>
    ca s.mem (by simp only [Cfg.sl, slot, p384]; omega)
  -- The slots' values, from the contract's.
  have hz' : sv base s₄ ZERO = 0 := by rw [sv₄ _ (by decide)]; exact (cs ZERO (by decide)).symm.trans hz
  have hone' : sv base s₄ ONEP = 2 ^ 384 % W.p := by
    rw [sv₄ _ (by decide)]; refine (cs ONEP (by decide)).symm.trans (hone.trans ?_)
    simp only [Impl.Weierstrass.Mul.Curve.mont, Nat.one_mul]; rfl
  have ha' : sv base s₄ AP = 2 ^ 384 * W.a % W.p := by
    rw [sv₄ _ (by decide)]; refine (cs AP (by decide)).symm.trans (ha.trans ?_)
    simp only [Impl.Weierstrass.Mul.Curve.mont]; rw [Nat.mul_comm]; rfl
  have hb3' : sv base s₄ B3P = 2 ^ 384 * (3 * W.b) % W.p := by
    rw [sv₄ _ (by decide)]; refine (cs B3P (by decide)).symm.trans (hb3.trans ?_)
    simp only [Impl.Weierstrass.Mul.Curve.mont]; rw [Nat.mul_comm]; rfl
  have tm : ∀ x, toM W.p (2 ^ 384) (2 ^ 384 * x % W.p) = Fin.ofNat W.p x := fun x => by
    rw [Nat.mul_comm]; exact toM_mont hpR
  have qx : (MC.qCoords base s.mem).1 = sv base s₄ RX := by rw [sv₄ _ (by decide)]; exact cs RX (by decide)
  have qy : (MC.qCoords base s.mem).2 = sv base s₄ RY := by
    rw [sv₄ _ (by decide), ← cs RY (by decide)]; rfl
  have eP : MC.point base s.mem = .affine (toM W.p (2 ^ 384) (sv base s₄ RX)) (toM W.p (2 ^ 384) (sv base s₄ RY)) := by
    unfold Impl.Weierstrass.Mul.Curve.point
    rw [qx, qy, dq, dq]
  have hon' := hon
  rw [eP] at hon'
  -- The body.
  refine WP.seq (WP.mono (mulBody_ok hL hw₄ hz' hone' (by rw [ha']; exact tm _) (by rw [hb3']; exact tm _)
    (by rw [ha']; exact Nat.mod_lt _ hp0) (by rw [hb3']; exact Nat.mod_lt _ hp0) (qx ▸ hx) (qy ▸ hy) hon')
    fun s₅ ⟨K₅, U₅, lt₅, R₅⟩ => ?_)
  -- The loads.
  have hw₅ := hw₄.of_kc K₅
  have far : ∀ d ∈ [2224, 2232, 2240], word s₅.mem base d = word s₄.mem base d := fun d hd =>
    U₅.word (fun w hw => by
      have := (by decide : ∀ w ∈ mulBW, w.1 + w.2 ≤ 2224 ∨ 3712 ≤ w.1) w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      omega) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; omega)
  have w20 : word s₅.mem base 2240 = s.gpr .ra := by
    rw [far 2240 (by simp), m₄, word_writeW_self]
  have w12 : word s₅.mem base 2232 = s.gpr .s1 := by
    rw [far 2232 (by simp), m₄, (writeW_outside (d := 2240) _ base _ (by omega)).word (by omega) (by omega), word_writeW_self]
  have w04 : word s₅.mem base 2224 = s.gpr .s0 := by
    rw [far 2224 (by simp), m₄, (writeW_outside (d := 2240) _ base _ (by omega)).word (by omega) (by omega),
      (writeW_outside (d := 2232) _ base _ (by omega)).word (by omega) (by omega), word_writeW_self]
  refine ldAt_ws hw₅ (d := 2240) (by decide) (by decide) fun s₆ u₆ => ?_
  refine ldAt_ws (hw₅.of_kp (Kp.of_upd u₆)) (d := 2232) (by decide) (by decide) fun s₇ u₇ => ?_
  have hw₇ : WsReg s₇ base := ⟨by rw [u₇.other .s0 (by decide), u₆.other .s0 (by decide)]; exact hw₅.s0,
    by rw [u₇.wr, u₆.wr]; exact hw₅.wr, hfit, hal⟩
  refine ldAt_ws hw₇ (d := 2224) (by decide) (by decide) fun s₈ u₈ => WP.block_nil ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · have m₇ : s₇.mem = s₅.mem := by rw [u₇.mem, u₆.mem]
    by_cases h0 : r = .s0
    · subst h0; rw [u₈.gpr, m₇, w04]
    by_cases h1 : r = .s1
    · subst h1; rw [u₈.other _ (by decide), u₇.gpr, u₆.mem, w12]
    rw [u₈.other _ h0, u₇.other _ h1, u₆.other _ (fun e => by subst e; revert hr; decide),
      K₅.gpr r hr h1, g₄ r h0]
  · rw [u₈.sp, u₇.sp, u₆.sp, K₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, w20]
  · have m₈ : s₈.mem = s₅.mem := by rw [u₈.mem, u₇.mem, u₆.mem]
    show MC.ResultInRange _ _ (s.gpr .a0) s.mem s₈.mem
    rw [hb, eP, m₈]
    refine ⟨fun _ _ => ?_, keeps_of_unch (O₄.trans U₅)⟩
    have e : MC.scalar base s.mem = sv base s₄ K := by rw [sv₄ _ (by decide)]; exact cs K (by decide)
    have c5 : ∀ i, i < 45 → MC.toPoint.coordAt s₅.mem base (p384.sl i) = sv base s₅ i := fun i hi =>
      ca s₅.mem (by simp only [Cfg.sl, slot, p384]; omega)
    have x0 : MC.toPoint.coordAt s₅.mem base MC.pAt = sv base s₅ RX := c5 RX (by decide)
    have x1 : MC.toPoint.coordAt s₅.mem base (MC.pAt + Impl.Weierstrass.Point.elemBytes MC.toPoint.k) =
        sv base s₅ RY := c5 RY (by decide)
    have x2 : MC.toPoint.coordAt s₅.mem base (MC.pAt + 2 * Impl.Weierstrass.Point.elemBytes MC.toPoint.k) =
        sv base s₅ RZ := c5 RZ (by decide)
    rw [e]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at lt₅
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x0]; exact lt₅.1
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x1]; exact lt₅.2.1
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x2]; exact lt₅.2.2
    · rw [Impl.Weierstrass.Point.Curve.pointAt, x0, x1, x2, dq, dq, dq]
      exact represents_of_rep R₅

/-! ## Constant time, and a state satisfying the precondition -/

theorem mul_ct : ConstantTime isa mulRVc.pre mulRVc.pub mulP384 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0])
    (fun _ _ _ _ hp => ⟨hp.1, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr; exact hp.2⟩) (by taint_decide)

/-- Byte `a` of the number `x` at slot `i` of a working space at `0x1000`,
if `a` is in that slot. -/
def satByte (a : Addr) (i x : Nat) : Option (BitVec 8) :=
  if 0x1000 + p384.sl i ≤ a.toNat ∧ a.toNat < 0x1000 + p384.sl i + 48 then
    some (BitVec.ofNat 8 (x >>> (8 * (a.toNat - (0x1000 + p384.sl i)))))
  else none

/-- `x R mod p`. -/
abbrev mont (x : Nat) : Nat := x * 2 ^ 384 % W.p

/-- The memory of `satState`: `p`, and one, `a`, `3 b` and `G`'s coordinates
in Montgomery's form, at their slots for `ws = 0x1000`, zeros elsewhere. -/
def satMem : Mem := fun a =>
  ((satByte a MP W.p).orElse fun _ => (satByte a ONEP (mont 1)).orElse fun _ =>
    (satByte a AP (mont W.a)).orElse fun _ => (satByte a B3P (mont (3 * W.b))).orElse fun _ =>
    (satByte a RX (mont W.gx)).orElse fun _ => satByte a RY (mont W.gy)).getD 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | _ => 0
  sp := 0x10000
  mem := satMem
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem sat_consts : MC.ConstsOk 0x1000 satMem := by
  unfold Impl.Weierstrass.Mul.Curve.ConstsOk
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem sat_x : (MC.qCoords 0x1000 satMem).1 = mont W.gx := by decide +kernel

theorem sat_y : (MC.qCoords 0x1000 satMem).2 = mont W.gy := by decide +kernel

theorem sat_point (hL : VG.Proof.Weierstrass.Law W) : MC.PointOk 0x1000 satMem := by
  have dq : ∀ x, MC.toPoint.dec x = toM W.p (2 ^ 384) x :=
    VG.Proof.Weierstrass.Point.dec_eq MC.toPoint hL.one_ne_zero (VG.Proof.Weierstrass.Point.fermat_of_law hL) unit
  have hp0 : 0 < W.p := by decide
  refine ⟨by rw [sat_x]; exact Nat.mod_lt _ hp0, by rw [sat_y]; exact Nat.mod_lt _ hp0, ?_⟩
  have eG : MC.point 0x1000 satMem = Spec.Weierstrass.G W := by
    unfold Impl.Weierstrass.Mul.Curve.point
    rw [sat_x, sat_y, dq, dq]
    exact congrArg₂ Point.affine (toM_mont unit) (toM_mont unit)
  rw [eG]
  exact VG.Proof.P384.onCurve_G

theorem mul_verified (hL : VG.Proof.Weierstrass.Law W) :
    Verified RISCV64.target mulP384 (MC.mulInRangeContract RISCV64.abi) :=
  Verified.of_correct (mul_rv hL) mul_ct
    { pre := by sig_implies_pre [Impl.Weierstrass.Mul.Curve.mulInRangeContract, Impl.Weierstrass.MulBase.sig,
        mulRVc, RISCV64.abi, RISCV64.argRegs]
      post := by sig_implies_post [Impl.Weierstrass.Mul.Curve.mulInRangeContract, Impl.Weierstrass.MulBase.sig,
        mulRVc, RISCV64.abi, RISCV64.argRegs]
      pub := by sig_implies_pub [Impl.Weierstrass.Mul.Curve.mulInRangeContract, Impl.Weierstrass.MulBase.sig,
        mulRVc, RISCV64.abi, RISCV64.argRegs]
      sat := ⟨satState, Sig.contract_pre_of_check (by decide +kernel) (by
        sig_reduce [Sig.wfPre, Impl.Weierstrass.MulBase.sig, RISCV64.abi, RISCV64.argRegs, satState]
        exact ⟨by decide, sat_consts, sat_point hL⟩)⟩ }

end VG.Proof.Ecdsa.RISCV64.P384
