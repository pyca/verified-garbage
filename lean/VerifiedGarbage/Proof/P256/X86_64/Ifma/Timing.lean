module

public import VerifiedGarbage.Proof.P256.X86_64.Ifma.Window
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointMulTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointPairedTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.RegFieldTiming
public import VerifiedGarbage.Proof.Framework.X86_64.TaintSym
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacZero
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointSeed
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointLoopTiming

/-!
# P-256 on x86-64 with AVX512_IFMA: the joint multiplication's timing

Two runs of `vwindow` from equal public scalars and field inputs take the same
branches and addresses (`vwindow_relCT`), given the taint checks of its parts
(`VChecks`): each part is run from registers that agree, by what each run
leaves (`Window.lean`), which is the same accumulator in both.
-/

@[expose] public section

namespace VG.Proof.P256.X86_64.Ifma

open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma
open Spec.Weierstrass VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Impl.Mont.X86_64 (sc)

/-- The taint checks of the joint multiplication's code in vectors. -/
structure VChecks (c : Joint.Cfg) : Prop where
  head : RegCT [.rdi, .r10, .r11, .rbx] (.seq (.block [.alu .sub .rbx (.imm 1), .alu .test .r11 (.reg .r11)])
    (.ite .e (.block []) (.block dblPieces.flatten)))
  qRead : RegCT [.rdi, .rbx] (.block (Naf.digitRead c.K))
  qBody : RegCT [.rdi, .r10, .r8, .r11] qBody
  gRead : RegCT [.rdi, .rbx] (.block (Joint.fixedRead c))
  gBody : ConstantTime isa (fun _ => True)
    (X86_64.Taint.AgreeS [c.tsym] (Taint.ofRegs [.rdi, .r10, .r8, .r11])) (gBody c)
  init : RegCT [.rdi] (.block (fill kwords KB ++ (vregs (64 * c.K.M.n + 1) ++ zeroAcc)))
  out : RegCT [.rdi, .r10, .r11] (.seq (.block [.alu .test .r11 (.reg .r11)])
    (.ite .e (.block []) (.block (outPieces.flatten ++ storeOut))))
  mov : RegCT [] (.block [.mov .rbx (.reg .r11), .vop .vzeroupper])
  tab : RegCT [.rdi, .r10] (.seq (vtab c) (.block zeroAcc))
  mx1 : RegCT [.rdi] (.block [.stmxcsr (sc MXV), .mov32 .r12 (.mem (sc MXV)), .alu32 .and .r12 (.imm 0xFFFF)])
  mx2 : RegCT [.rdi] (.block [.mov32 .rax (.imm 0x1FBF), .store32 (sc (MXV + 4)) .rax, .ldmxcsr (sc (MXV + 4)),
    .lfence])
  lf : RegCT [] (.block [.lfence])
  mx4 : RegCT [.rdi] (.block [.store32 (sc MXV) .r12, .ldmxcsr (sc MXV)])
  pack : RegCT [.rdi, .rbx] (packR c)
  ctr0 : RegCT [] (.block [.mov32 .rbx (.imm 0)])

/-- Code the taint analysis proves constant time, from registers that agree. -/
theorem regCT_rel {rs : List Reg} {c : Prog isa} (hc : RegCT rs c) {P : State → State → Prop}
    (hp : ∀ s t, P s t → ∀ r ∈ rs, s.gpr r = t.gpr r) : RelCT isa P c (fun _ _ => True) :=
  fun _ _ _ _ _ _ h es et => ⟨hc _ _ _ _ _ _ trivial trivial (Taint.agree_ofRegs (hp _ _ h)) es et, trivial⟩

/-- A part of the code: constant time from registers that agree, where each run leaves `F`. -/
theorem rel_stage {rs : List Reg} {c : Prog isa} (hc : RegCT rs c) {I F : State → Prop}
    (hr : ∀ s t, I s → I t → ∀ r ∈ rs, s.gpr r = t.gpr r) (hw : ∀ s, I s → WP isa c s F) :
    RelCT isa (fun s t => I s ∧ I t) c (fun s t => F s ∧ F t) :=
  ((regCT_rel hc (fun s t h => hr s t h.1 h.2)).wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

theorem accSt_r11 {s t : State} {acc : Option (Fin pN × Fin pN × Fin pN)} (hs : AccSt s acc) (ht : AccSt t acc) :
    s.gpr .r11 = t.gpr .r11 := by
  cases acc with
  | none => exact hs.trans ht.symm
  | some a => exact hs.1.trans ht.1.symm

section
variable {c : Joint.Cfg} {base T K : Addr} {size u v : Nat} {G Q : Point Cv}
  {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {E : Nat → Fe Cv}

/-- The registers the loop's code reads through or branches on are the same in two runs. -/
theorem VInv.regs {j : Nat} {acc : Option (Fin pN × Fin pN × Fin pN)} {s t : State}
    (hs : VInv c base T K size u v Q row E j acc s) (ht : VInv c base T K size u v Q row E j acc t) :
    ∀ r ∈ [Reg.rdi, .r10, .r11, .rbx], s.gpr r = t.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hs.core.field.scr.rdi.trans ht.core.field.scr.rdi.symm
  · exact hs.k.trans ht.k.symm
  · exact accSt_r11 hs.acc ht.acc
  · exact hs.rbx.trans ht.rbx.symm

/-- A digit of `Q`'s scalar, in two runs. -/
theorem vq_relCT (hk : VChecks c) (hV : VLay c size) {j : Nat} (hj : j < 257)
    {acc : Option (Fin pN × Fin pN × Fin pN)} :
    RelCT isa (fun s t => VInv c base T K size u v Q row E j acc s ∧ VInv c base T K size u v Q row E j acc t)
      (qPass c) (fun s t => VInv c base T K size u v Q row E j (qNext (tqE c E) v j acc) s ∧
        VInv c base T K size u v Q row E j (qNext (tqE c E) v j acc) t) := by
  have tr : RelCT isa (fun s t => VInv c base T K size u v Q row E j acc s ∧
      VInv c base T K size u v Q row E j acc t) (qPass c) (fun _ _ => True) := by
    rw [qPass]
    refine RelCT.seq (rel_stage hk.qRead (fun s t hs ht r hr => VInv.regs hs ht r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl <;> simp)) (fun s h => vqRead_ok hV hj h)) ?_
    refine RelCT.ite (fun s t h => ?_) (RelCT.block_nil fun _ _ _ => trivial) ?_
    · show s.zf = t.zf
      exact h.1.2.2.trans h.2.2.2.symm
    · refine regCT_rel hk.qBody fun s t h r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact VInv.regs h.1.1.1 h.1.2.1 _ (by simp)
      · exact VInv.regs h.1.1.1 h.1.2.1 _ (by simp)
      · exact h.1.1.2.1.trans h.1.2.2.1.symm
      · exact VInv.regs h.1.1.1 h.1.2.1 _ (by simp)
  exact (tr.wp (fun s t h => ⟨WP.mono (vq_ok hV hj h.1) (fun _ x => x.1),
    WP.mono (vq_ok hV hj h.2) (fun _ x => x.1)⟩)).mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem VInv.tsym {j : Nat} {acc : Option (Fin pN × Fin pN × Fin pN)} {s : State}
    (hs : VInv c base T K size u v Q row E j acc s) : s.syms c.tsym = T :=
  (hs.core.input.external 1 (Nat.le_refl 1) (by unfold jointGTop; split <;> omega) (by decide)).symbol

/-- A digit of the generator's scalar, in two runs. -/
theorem vg_relCT (hk : VChecks c) (hV : VLay c size) (h9 : c.gw = 9) {j : Nat}
    (hj : j < 257) {acc : Option (Fin pN × Fin pN × Fin pN)} :
    RelCT isa (fun s t => VInv c base T K size u v Q row E j acc s ∧ VInv c base T K size u v Q row E j acc t)
      (gPass c) (fun s t => VInv c base T K size u v Q row E j (gNext c row u j acc) s ∧
        VInv c base T K size u v Q row E j (gNext c row u j acc) t) := by
  have tr : RelCT isa (fun s t => VInv c base T K size u v Q row E j acc s ∧
      VInv c base T K size u v Q row E j acc t) (gPass c) (fun _ _ => True) := by
    rw [gPass]
    refine RelCT.seq (rel_stage hk.gRead (fun s t hs ht r hr => VInv.regs hs ht r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl <;> simp)) (fun s h => vgRead_ok hV h9 hj h)) ?_
    refine RelCT.ite (fun s t h => ?_) (RelCT.block_nil fun _ _ _ => trivial) ?_
    · show s.zf = t.zf
      exact h.1.2.2.trans h.2.2.2.symm
    · intro s t ts tt s' t' h es et
      refine ⟨hk.gBody _ _ _ _ _ _ trivial trivial ⟨Taint.agree_ofRegs fun r hr => ?_, fun n hn => ?_⟩ es et, trivial⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact VInv.regs h.1.1.1 h.1.2.1 _ (by simp)
        · exact VInv.regs h.1.1.1 h.1.2.1 _ (by simp)
        · exact h.1.1.2.1.trans h.1.2.2.1.symm
        · exact VInv.regs h.1.1.1 h.1.2.1 _ (by simp)
      · rw [List.mem_singleton] at hn; subst hn
        exact h.1.1.1.tsym.trans h.1.2.1.tsym.symm
  exact (tr.wp (fun s t h => ⟨WP.mono (vg_ok hV h9 hj h.1) (fun _ x => x.1),
    WP.mono (vg_ok hV h9 hj h.2) (fun _ x => x.1)⟩)).mono (fun _ _ h => h) (fun _ _ h => h.2)

/-- A digit of each scalar, in two runs. -/
theorem vstep_relCT (hk : VChecks c) (hV : VLay c size) (h9 : c.gw = 9) {j : Nat}
    (hj : j < 257) {acc : Option (Fin pN × Fin pN × Fin pN)} :
    RelCT isa (fun s t => VInv c base T K size u v Q row E (j + 1) acc s ∧
        VInv c base T K size u v Q row E (j + 1) acc t) (vstep c)
      (fun s t => (VInv c base T K size u v Q row E j (stepAcc c row (tqE c E) u v j acc) s ∧ s.zf = some (decide (j = 0))) ∧
        VInv c base T K size u v Q row E j (stepAcc c row (tqE c E) u v j acc) t ∧ t.zf = some (decide (j = 0))) := by
  rw [vstep]
  apply RelCT.assoc
  refine RelCT.seq (rel_stage hk.head (fun s t hs ht => VInv.regs hs ht)
    (fun s h => WP.mono (vhead_ok hV hj h) fun _ x => x.1)) ?_
  refine RelCT.seq (vq_relCT hk hV hj) ?_
  refine RelCT.seq (vg_relCT hk hV h9 hj) ?_
  exact rel_stage jointTestCT (fun s t hs ht r hr => VInv.regs hs ht r (by
    rw [List.mem_singleton] at hr; subst hr; simp))
    (fun s h => WP.mono (vtail_ok hV hj h) fun _ x => x.1)

/-- The loop over the digits, in two runs. -/
theorem vdigits_relCT (hk : VChecks c) (hV : VLay c size) (h9 : c.gw = 9) :
    RelCT isa (fun s t => VInv c base T K size u v Q row E 257 none s ∧ VInv c base T K size u v Q row E 257 none t)
      (.loop (vstep c) .ne)
      (fun s t => VInv c base T K size u v Q row E 0 (accN c row (tqE c E) u v 257) s ∧
        VInv c base T K size u v Q row E 0 (accN c row (tqE c E) u v 257) t) := by
  let R := fun (j : Nat) (s t : State) => VInv c base T K size u v Q row E j (accN c row (tqE c E) u v (257 - j)) s ∧
    VInv c base T K size u v Q row E j (accN c row (tqE c E) u v (257 - j)) t
  let I := fun (j : Nat) (s t : State) => 1 ≤ j ∧ j ≤ 257 ∧ R j s t
  have hs : ∀ j, RelCT isa (I j) (vstep c) (fun s t =>
      eval .ne s = eval .ne t ∧ (eval .ne s = some false → R 0 s t) ∧
      (eval .ne s = some true → ∃ n < j, I n s t)) := by
    intro j
    by_cases hj : 1 ≤ j
    · by_cases hb : j ≤ 257
      · have he : j - 1 + 1 = j := by omega
        have ea : accN c row (tqE c E) u v (257 - (j - 1)) =
            stepAcc c row (tqE c E) u v (j - 1) (accN c row (tqE c E) u v (257 - j)) := by
          rw [show 257 - (j - 1) = (257 - j) + 1 by omega, accN, show 256 - (257 - j) = j - 1 by omega]
        refine (vstep_relCT hk hV h9 (j := j - 1) (by omega) (acc := accN c row (tqE c E) u v (257 - j))).mono
          (P' := I j) (fun _ _ h => by rw [he]; exact h.2.2) ?_
        intro s t ⟨⟨is, sz⟩, it, tz⟩
        have se : eval .ne s = some (!decide (j - 1 = 0)) := by change s.zf.map (!·) = _; rw [sz]; rfl
        have te : eval .ne t = some (!decide (j - 1 = 0)) := by change t.zf.map (!·) = _; rw [tz]; rfl
        have hp : R (j - 1) s t := by
          show VInv c base T K size u v Q row E (j - 1) (accN c row (tqE c E) u v (257 - (j - 1))) s ∧ _
          rw [ea]; exact ⟨is, it⟩
        refine ⟨se.trans te.symm, ?_, ?_⟩
        · intro he'
          have hz : j - 1 = 0 := by
            by_contra hz
            simp only [se, hz, decide_false, Bool.not_false] at he'
            cases he'
          exact hz ▸ hp
        · intro he'
          have hz : j - 1 ≠ 0 := by
            intro hz
            simp only [se, hz, decide_true, Bool.not_true] at he'
            cases he'
          exact ⟨j - 1, by omega, by omega, by omega, hp⟩
      · exact RelCT.of_false (fun _ _ h => hb h.2.1)
    · exact RelCT.of_false (fun _ _ h => hj h.1)
  exact (RelCT.loop I hs 257).mono (fun _ _ h => ⟨by decide, by decide, h⟩) (fun _ _ h => h)

/-- The loop and what is around it, in two runs. -/
theorem vloop_relCT (hk : VChecks c) (hV : VLay c size) (h9 : c.gw = 9) :
    RelCT isa (fun s t => VBase c base T size u v Q row E s ∧ VBase c base T size u v Q row E t) (vloop c)
      (fun s t => VOut c base T size u v Q row E (accN c row (tqE c E) u v 257) s ∧
        VOut c base T size u v Q row E (accN c row (tqE c E) u v 257) t) := by
  rw [vloop]
  refine RelCT.seq (rel_stage hk.init (fun s t hs ht r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact hs.core.field.scr.rdi.trans ht.core.field.scr.rdi.symm)
    (fun s h => WP.mono (vinit_ok hV h) fun _ x => x.1)) ?_
  refine RelCT.seq (rel_stage hk.tab (fun s t hs ht r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.1.core.field.scr.rdi.trans ht.1.core.field.scr.rdi.symm
      · exact hs.2.2.2.2.2.trans ht.2.2.2.2.2.symm)
    (fun s h => WP.mono (vtabs_ok hV h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2) fun _ x => x.1)) ?_
  refine RelCT.seq (vdigits_relCT hk hV h9) ?_
  exact rel_stage hk.out (fun s t hs ht r hr => VInv.regs hs ht r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp)) (fun s h => WP.mono (vout_ok hV h) fun _ x => x.1)

theorem packSt_rbx {s t : State} {acc : Option (Fin pN × Fin pN × Fin pN)} (hs : PackSt s acc) (ht : PackSt t acc) :
    s.gpr .rbx = t.gpr .rbx := by
  cases acc with
  | none => exact hs.trans ht.symm
  | some a => exact hs.1.trans ht.1.symm

/-- The loop in vectors, into `R`, in two runs. -/
theorem vmain_relCT (hk : VChecks c) (hV : VLay c size) (hL : JointLayout c size)
    (hN : Lay c.K.M size (· ∈ nafSlots c.K)) (h9 : c.gw = 9) {A : Point Cv}
    (hpt : AccPt (accN c row (tqE c E) u v 257) A) :
    RelCT isa (fun s t => VBase c base T size u v Q row E s ∧ VBase c base T size u v Q row E t) (vmain c)
      (fun s t => VFin c base T size u v Q row E (accN c row (tqE c E) u v 257) A s ∧
        VFin c base T size u v Q row E (accN c row (tqE c E) u v 257) A t) := by
  have rdi1 : ∀ s t : State, VBase c base T size u v Q row E s → VBase c base T size u v Q row E t →
      ∀ r ∈ [Reg.rdi], s.gpr r = t.gpr r := by
    intro s t hs ht r hr
    rw [List.mem_singleton] at hr; subst hr
    exact hs.core.field.scr.rdi.trans ht.core.field.scr.rdi.symm
  let I1 : State → Prop := fun s => VBase c base T size u v Q row E s ∧ MxOk s
  let I3 : State → Prop := fun s => VOut c base T size u v Q row E (accN c row (tqE c E) u v 257) s ∧ MxOk s
  let I4 : State → Prop := fun s => VPack c base T size u v Q row E (accN c row (tqE c E) u v 257) s ∧ MxOk s
  let I5 : State → Prop := VPack c base T size u v Q row E (accN c row (tqE c E) u v 257)
  rw [vmain, regionAt]
  refine RelCT.seq (R := fun s t => I5 s ∧ I5 t) ?_ (rel_stage hk.pack (I := I5)
    (fun s t hs ht r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.core.field.scr.rdi.trans ht.core.field.scr.rdi.symm
      · exact packSt_rbx hs.pack ht.pack)
    (fun s h => WP.mono (packR_ok hV hL hN h.core hpt h.pack) fun w x => x.1))
  refine RelCT.seq (R := fun s t => I1 s ∧ I1 t)
    (rel_stage hk.mx1 rdi1 (fun s h => WP.mono (mxSave_vs hV h) fun _ x => x.1)) ?_
  refine RelCT.seq (R := fun s t => I4 s ∧ I4 t) ?_ (rel_stage hk.mx4 (I := I4) (fun s t hs ht r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact hs.1.core.field.scr.rdi.trans ht.1.core.field.scr.rdi.symm)
      (fun s h => WP.mono (mxRestore_vs hV h.1 h.2) fun _ x => x.1))
  refine RelCT.seq (R := fun s t => I1 s ∧ I1 t) (rel_stage hk.mx2 (I := I1) (fun s t hs ht => rdi1 s t hs.1 ht.1)
    (fun s h => WP.mono (mxSet_vs hV h.1 h.2) fun _ x => x.1)) ?_
  refine RelCT.seq (R := fun s t => I4 s ∧ I4 t) ?_ (rel_stage hk.lf (I := I4)
    (fun _ _ _ _ _ hr => absurd hr List.not_mem_nil) (fun s h => WP.block_cons_iff.2 ⟨s, rfl, WP.block_nil h⟩))
  refine RelCT.seq (R := fun s t => I3 s ∧ I3 t) ?_ (rel_stage hk.mov (I := I3)
    (fun _ _ _ _ _ hr => absurd hr List.not_mem_nil) (fun s h => WP.mono (vmov_ok hV h.1 h.2) fun _ x => x.1))
  have r₀ := (vloop_relCT (E := E) (u := u) (v := v) (Q := Q) (row := row) (base := base) (T := T) hk hV
    h9).mono (P' := fun s t => I1 s ∧ I1 t) (fun _ _ h => ⟨h.1.1, h.2.1⟩) (fun _ _ h => h)
  exact (r₀.wp (F₁ := MxOk) (F₂ := MxOk) (fun s t h =>
    ⟨WP.mono (vloop_vs hV h9 h.1.1 h.1.2) (fun _ x => x.1.2),
      WP.mono (vloop_vs hV h9 h.2.1 h.2.2) (fun _ x => x.1.2)⟩)).mono (fun _ _ h => h)
    (fun _ _ ⟨⟨a, b⟩, x, y⟩ => ⟨⟨a, x⟩, b, y⟩)

/-- What the test of `R`'s `Z` leaves in each run: the fields `Joint.window` reads, and its input. -/
def VZ (c : Joint.Cfg) (base T : Addr) (size u v : Nat) {G : Point Cv} (Q : Point Cv)
    (row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)) (E : Nat → Fe Cv)
    (acc : Option (Fin pN × Fin pN × Fin pN)) (e : State) : Prop :=
  Inv c.K.M base size Cv.p (· ∈ nafSlots c.K) (winRo c.K) E e ∧ JointWindowInput c Cv base T size u v Q row e ∧
    e.zf = some (decide (zFin acc = 0))

theorem vzero_ok (hL : JointLayout c size) (hN : Lay c.K.M size (· ∈ nafSlots c.K))
    (hm : UnitMod Cv.p (2 ^ (64 * c.K.M.n))) {acc : Option (Fin pN × Fin pN × Fin pN)} {A : Point Cv} {w : State}
    (h : VFin c base T size u v Q row E acc A w) :
    WP isa (.block (Jacobian.zeroTest c.K.M.n c.K.R.z)) w (VZ c base T size u v Q row E acc) := by
  have mz : c.K.R.z ∈ winRo c.K ++ jacCoords c.K.R := List.mem_append_right _ (by simp [jacCoords])
  refine WP.mono_syms (zeroField_ok hN hm h.field mz) fun e ⟨ez, ie, ke⟩ ye => ?_
  have kw : ProgKeep c.K.M base (jointWork c) w e := ke.mono (fun _ h => absurd h List.not_mem_nil)
  have we := jwi_work hL h.field.scr h.field.mod.tmp h.input kw ye
  exact ⟨⟨ie.scr, ie.mod, fun x hx => ie.sl x (List.mem_append_left _ hx),
      fun x hx => ie.lt x (List.mem_append_left _ hx),
      fun x hx => (ie.val x (List.mem_append_left _ hx)).trans (h.ro x hx)⟩, we.1, by rw [ez, h.z]⟩

/-- The fields the vectors' code only reads are those both runs started with. -/
theorem VBase.congr {E' : Nat → Fe Cv} {s : State} (h : VBase c base T size u v Q row E s)
    (he : ∀ x ∈ winRo c.K, E x = E' x) : VBase c base T size u v Q row E' s :=
  ⟨⟨h.core.field, fun x hx => (h.core.ro x hx).trans (he x hx), h.core.rz, h.core.input⟩, h.gtab⟩

/-- The joint multiplication with the loop in vectors, in two runs. -/
theorem vwindow_relCT (hC : Law Cv) (hO : PrimeOrder Cv) (ha : AM3 Cv) (hk : VChecks c) {double : Prog isa}
    (hV : VLay c size) (hL : JointAddLayout c size) (hInit : JointInitLayout c size) (h9 : c.gw = 9)
    (hm : UnitMod Cv.p (2 ^ (64 * c.K.M.n))) (hd : JDblOk Cv c.dbl) (hD : JointDoubler c Cv size double)
    (hOne : c.K.one < Cv.p) (hOneVal : toM Cv.p (2 ^ (64 * c.K.M.n)) c.K.one = 1)
    (hG : onCurve Cv G = true) (hQ : onCurve Cv Q = true) (hZ : c.coZ = true → PrimeOrder Cv ∧ 17 ≤ Cv.n ∧ AM3 Cv)
    (hc : JointCachedChecks c) (hf : JointFixedChecks c) (ht : JointTableChecks c)
    (hcache : ScratchCT (Joint.cacheCode c).inline) (hseed : ScratchCT (.block (Jacobian.infinity c.K c.K.R)))
    (hctr : ScratchCT (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 (Joint.top c)))]))
    (hzero : ScratchCT (.block (Jacobian.zeroTest c.K.M.n c.K.R.z)))
    (hu : u < 2 ^ (64 * c.K.M.n)) (hv : v < 2 ^ (64 * c.K.M.n)) {E₀ : Nat → Fe Cv} :
    RelCT isa (fun s t => FieldPair c.K.M base size Cv.p (· ∈ nafSlots c.K) (winRo c.K) E₀ s t ∧
        (JointWindowInput c Cv base T size u v Q row s ∧ GTab base T size s) ∧
        JointWindowInput c Cv base T size u v Q row t ∧ GTab base T size t)
      (vwindow c double).inline (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base) := by
  have hLl := hL.lookup.layout
  have hN := hInit.naf.lay
  have hn := hV.n
  -- The test of `Z` and what follows it.
  have rest (acc : Option (Fin pN × Fin pN × Fin pN)) (A : Point Cv) : RelCT isa (fun s t =>
      VFin c base T size u v Q row E₀ acc A s ∧ VFin c base T size u v Q row E₀ acc A t)
      (.seq (.block (Jacobian.zeroTest c.K.M.n c.K.R.z))
        (.ite .e (Joint.window c double).inline (.block [.mov32 .rbx (.imm 0)])))
      (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base) := by
    refine RelCT.seq (rel_stage (rs := [.rdi]) hzero (fun s t hs ht r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact hs.field.scr.rdi.trans ht.field.scr.rdi.symm) (fun s h => vzero_ok hLl hN hm h)) ?_
    refine RelCT.ite (fun s t h => ?_) ?_ ?_
    · show s.zf = t.zf
      exact h.1.2.2.trans h.2.2.2.symm
    · -- `Z` is zero: the whole of `Joint.window`
      exact (jointMulWindow_relCT (base := base) (T := T) (row := row) (E := E₀) hL hInit hm hC hd hD hOne hOneVal
        hG hQ hZ hc hf ht hcache hseed hctr hu hv).mono (fun s t h => ⟨⟨h.1.1.1, h.1.2.1⟩, h.1.1.2.1, h.1.2.2.1⟩)
        (fun s t h => ⟨h.2.1.field.scr.rdi, h.2.2.1.field.scr.rdi⟩)
    · -- `Z` is not zero: `R` is the sum
      exact (rel_stage hk.ctr0 (I := VZ c base T size u v Q row E₀ acc) (F := fun f => f.gpr .rdi = base)
        (fun _ _ _ _ _ hr => absurd hr List.not_mem_nil)
        (fun e he => WP.mono (jointCounter_ok e (n := 0) (by decide)) fun f ⟨_, kf⟩ =>
          (kf.1 .rdi (by decide)).trans he.1.scr.rdi)).mono (fun s t h => h.1) (fun s t h => h)
  rw [vwindow]
  simp only [Code.inline]
  refine RelCT.seq (R := fun s t => VBase c base T size u v Q row E₀ s ∧ VBase c base T size u v Q row E₀ t) ?_ ?_
  · exact (rel_stage (rs := [.rdi]) hseed
      (I := fun s => Inv c.K.M base size Cv.p (· ∈ nafSlots c.K) (winRo c.K) E₀ s ∧
        JointWindowInput c Cv base T size u v Q row s ∧ GTab base T size s)
      (F := VBase c base T size u v Q row E₀)
      (fun s t hs ht r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact hs.1.scr.rdi.trans ht.1.scr.rdi.symm)
      (fun s h => WP.mono (vseed_ok hC hLl hN hOne h.1.to_tmv h.2.1 h.2.2) fun b x =>
        x.1.congr (fun y hy => h.1.val y hy))).mono
      (fun s t h => ⟨⟨h.1.1, h.2.1.1, h.2.1.2⟩, h.1.2, h.2.2.1, h.2.2.2⟩) (fun s t h => h)
  · intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
    have hpt := accN_pt hC ha row h9 (tabQ_pts hC hO ha hQ (vcore_affine hp.1.core)) hG hQ
      (by rw [hn] at hu; exact hu) (by rw [hn] at hv; exact hv) 257 (Nat.le_refl _)
    rw [show 257 - 257 = 0 from rfl, jointPoint_zero (gw := 9)] at hpt
    exact RelCT.seq (vmain_relCT hk hV hLl hN h9 hpt) (rest _ _) _ _ _ _ _ _ hp e₁ e₂

end

end VG.Proof.P256.X86_64.Ifma
