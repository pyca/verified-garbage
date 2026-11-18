module

public import VerifiedGarbage.Impl.Ffdh.Arm.NormalizedPrepare
public import VerifiedGarbage.Proof.Ffdh.Arm.Prepare
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareCT
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Impl.Bignum.Arm.NormalizedPrecompute
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
import VerifiedGarbage.Proof.Bignum.Arm.ImportModulus
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeInverse
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleCountMemory
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Bignum.Arm.NormalizedR2
import VerifiedGarbage.Proof.Bignum.Arm.SharedR2CT
import VerifiedGarbage.Proof.Bignum.Arm.NormalizedR2
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Impl.Bignum.Arm.NormalizedR2
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! ### `Bignum.Arm.NormalizedR2CT`, which only this module used -/

section

/-! Normalized R-squared preparation reveals only public workspace dimensions. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.NormalizedR2
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (wp_ldr)

 theorem constants_ct {base : BitVec 32} {len w : Nat} :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      VG.Impl.Bignum.Arm.NormalizedR2.constants (fun _ _ => True) := by
  have first := relCT_keep_sp
    (smallConst_ct (base := base) (len := len) (w := w) (o := 4) 0
      (by decide) (by decide) (by decide)) (fun _ _ h => h.2.2)
  have post (s : State) (h : ArithmeticReady base len w s) :
      WP isa (smallConst 4 0) s (ArithmeticReady base len w) :=
    WP.mono (smallConst_ok s 0 h (o := 4) (by decide) (by decide) (by decide) (by decide))
      (fun _ h => h.1)
  have setup := first.wp (fun s t h => ⟨post s h.1, post t h.2.1⟩)
  exact (setup.mono (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩)).seq
    (smallConst_ct 2 (o := 7) (by decide) (by decide) (by decide))

 theorem seed_ct {base : BitVec 32} {len w : Nat} :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t)
      (.block VG.Impl.Bignum.Arm.NormalizedR2.seed) (fun _ _ => True) := by
  let Q := fun s : State => s.gpr .r0 = base ∧ s.gpr .r1 = BitVec.ofNat 32 w
  have load : RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t)
      (.block [.ldr .r1 .r0 48]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    exact Taint.agree_ofRegs (by simpa using h.1.ptr.trans h.2.ptr.symm)
  have post (s : State) (h : ArithmeticReady base len w s) :
      WP isa (.block [.ldr .r1 .r0 48]) s Q := by
    have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
    rw [h.width] at header
    have fits := h.width ▸ h.layout.2.2.1
    have size : 52 ≤ 8 * len := by
      simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] at fits
      omega_using [fits]
    refine wp_ldr (by decide) (by rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega_using [size, this])) (h.workspace.read size) fun t u => WP.block_nil ?_
    exact ⟨(u.other .r0 (by decide)).trans h.ptr, u.gpr.trans header.1⟩
  unfold VG.Impl.Bignum.Arm.NormalizedR2.seed VG.Impl.Bignum.Arm.NormalizedR2.top
  apply RelCT.block_append (M := isa) (l₁ := [.ldr .r1 .r0 48])
  refine ((load.wp (fun s t h => ⟨post s h.1, post t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)).seq ?_
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r1]) _ (by taint_decide)
  intro s t h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.trans h.2.1.symm
  · exact h.1.2.trans h.2.2.symm

theorem init_ct {base : BitVec 32} {len w : Nat} :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      VG.Impl.Bignum.Arm.NormalizedR2.init (fun _ _ => True) := by
  have setup := (constants_ct (base := base) (len := len) (w := w)).wp
    (fun s t h => ⟨WP.mono (normalizedR2Constants_ok s h.1) (fun _ h => h.1),
      WP.mono (normalizedR2Constants_ok t h.2.1) (fun _ h => h.1)⟩)
  exact setup.seq (seed_ct.mono (fun _ _ h => ⟨h.2.1, h.2.2⟩) (fun _ _ h => h))

abbrev LoopReady (base : BitVec 32) (len w : Nat) (P : State → Prop) (s : State) : Prop :=
  (DoubleLoopReady base len w (w + 64) s ∧
    Proof.Rsa.Mont.numAt s.mem (State.addr base) w 4 = 2 ^ (64 * (w - 1)) ∧
    1 < Proof.Rsa.Mont.numAt s.mem (State.addr base) w 0) ∧ P s

theorem r2_ct {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (ct : TwoExp.MontgomeryTiming K)
    (countFits : 128 * w < 2 ^ 32) :
    RelCT isa (fun s t =>
      (ArithmeticReady base len w s ∧ P s ∧ 2 ^ (64 * (w - 1)) ≤ Proof.Rsa.Mont.numAt s.mem (State.addr base) w 0) ∧
      (ArithmeticReady base len w t ∧ P t ∧ 2 ^ (64 * (w - 1)) ≤ Proof.Rsa.Mont.numAt t.mem (State.addr base) w 0) ∧ s.sp = t.sp)
      (VG.Impl.Bignum.Arm.NormalizedR2.r2 K.op) (fun _ _ => True) := by
  have initPost (s : State) (h : ArithmeticReady base len w s ∧ P s ∧
      2 ^ (64 * (w - 1)) ≤ Proof.Rsa.Mont.numAt s.mem (State.addr base) w 0) :
      WP isa VG.Impl.Bignum.Arm.NormalizedR2.init s (LoopReady base len w P) := by
    refine WP.mono (normalizedR2Init_ok s h.1 h.2.2) ?_
    rintro t ⟨ready, seed, modulus, frame, rest⟩
    exact ⟨⟨ready, seed, by rw [modulus]; exact h.1.modulus⟩, K.stable frame rest h.2.1⟩
  have init := (relCT_keep_sp ((init_ct (base := base) (len := len) (w := w)).mono
    (P' := fun (s t : State) =>
      (ArithmeticReady base len w s ∧ P s ∧ 2 ^ (64 * (w - 1)) ≤ Proof.Rsa.Mont.numAt s.mem (State.addr base) w 0) ∧
      (ArithmeticReady base len w t ∧ P t ∧ 2 ^ (64 * (w - 1)) ≤ Proof.Rsa.Mont.numAt t.mem (State.addr base) w 0) ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h))
    (fun _ _ h => h.2.2)).wp (fun s t h => ⟨initPost s h.1, initPost t h.2.1⟩)
  have loopPost (s : State) (h : LoopReady base len w P s) :
      WP isa doubleLoop s (SharedR2.SqReady base len w P w) := by
    refine WP.mono (normalizedR2Loop_ok s h.1.1 h.1.2.1 h.1.2.2 countFits) ?_
    rintro t ⟨sq, frame, rest⟩
    exact ⟨⟨_, sq⟩, K.stable frame rest h.2⟩
  have loop : RelCT isa (fun s t => s.sp = t.sp ∧ LoopReady base len w P s ∧ LoopReady base len w P t)
      doubleLoop (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    have hw : 2 ≤ w := h.2.1.1.1.width ▸ h.2.1.1.1.layout.1
    exact doubleLoop_ct (by omega_using []) (by omega_using [countFits]) s t tr1 tr2 u v ⟨h.2.1.1.1, h.2.2.1.1, h.1⟩ e1 e2
  have loopCT := (relCT_keep_sp loop (fun _ _ h => h.1)).wp
    (fun s t h => ⟨loopPost s h.2.1, loopPost t h.2.2⟩)
  unfold VG.Impl.Bignum.Arm.NormalizedR2.r2
  exact init.seq (loopCT.seq ((SharedR2.squares_ct K ct).mono
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)))

end VG.Proof.Bignum.Arm.NormalizedR2

end

end

/-! # FFDH setup uses shared constant-time Montgomery precomputation -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/NormalizedPrecomputeCT.lean`, which only this module imported.
section

/-! # Shared modulus precomputation has a public trace -/

section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem normalizedPrecompute_ct {base src : BitVec 32} {len w k : Nat}
    {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (ct : TwoExp.MontgomeryTiming K)
    (countFits : 128 * w < 2 ^ 32) :
    RelCT isa (fun s t => (PrecomputeInput base src len w k s ∧ P s ∧ 2 ^ (64 * (w - 1)) ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)) ∧
      (PrecomputeInput base src len w k t ∧ P t ∧ 2 ^ (64 * (w - 1)) ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (State.addr src) k)) ∧ s.sp = t.sp)
      (NormalizedPrecompute.precompute K.op) (fun _ _ => True) := by
  have imported (s : State) (h : PrecomputeInput base src len w k s ∧ P s ∧ 2 ^ (64 * (w - 1)) ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)) :
      WP isa importModulus s fun t => PrecomputeModulus base len w t ∧ P t ∧ 2 ^ (64 * (w - 1)) ≤ Proof.Rsa.Mont.numAt t.mem (State.addr base) w 0 := by
    refine (importModulus_ready s h.1).and ?_
    refine WP.mono (importModulus_ok s h.1.workspace h.1.layout h.1.width h.1.positive h.1.fits h.1.sourceFits
      h.1.readable h.1.separate h.1.ptr h.1.source h.1.count h.1.stackRead h.1.stackSep h.1.saved) ?_
    rintro t ⟨_, _, _, modulus, frame, rest⟩
    exact ⟨K.stable frame rest h.2.1, by rw [modulus]; exact h.2.2⟩
  have inverse (s : State) (h : PrecomputeModulus base len w s ∧ P s ∧ 2 ^ (64 * (w - 1)) ≤ Proof.Rsa.Mont.numAt s.mem (State.addr base) w 0) :
      WP isa precomputeInverse s fun t => ArithmeticReady base len w t ∧ P t ∧ 2 ^ (64 * (w - 1)) ≤ Proof.Rsa.Mont.numAt t.mem (State.addr base) w 0 := by
    refine (precomputeInverse_ready s h.1).and ?_
    refine WP.mono (precomputeInverse_ok s h.1.workspace h.1.layout h.1.width h.1.ptr h.1.odd h.1.large
      h.1.stackRead h.1.stackSep h.1.saved) ?_
    rintro t ⟨_, modulus, frame, rest⟩
    exact ⟨K.stable frame rest h.2.1, by rw [modulus]; exact h.2.2⟩
  unfold NormalizedPrecompute.precompute
  refine relCT_chain ((importModulus_ct (base := base) (src := src) (len := len) (w := w) (k := k)).mono
    (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)) imported imported ?_
  exact relCT_chain ((precomputeInverse_ct (base := base) (len := len) (w := w)).mono
    (fun _ _ h => ⟨h.1.1, h.2.1.1⟩) (fun _ _ h => h)) inverse inverse (NormalizedR2.r2_ct K ct countFits)

end VG.Proof.Bignum.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem normalizedPrepare_ct {base src : BitVec 32} {len k : Nat}
    {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len (Spec.Rsa.modulusWords k) P regions)
    (ct : TwoExp.MontgomeryTiming K) (countFits : 128 * Spec.Rsa.modulusWords k < 2 ^ 32) :
    RelCT isa (fun s t => (PrepareInput base src len k s ∧ P s ∧ 2 ^ (64 * (Spec.Rsa.modulusWords k - 1)) ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)) ∧
      (PrepareInput base src len k t ∧ P t ∧ 2 ^ (64 * (Spec.Rsa.modulusWords k - 1)) ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (State.addr src) k)) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.NormalizedPrepare.code K.op) (fun _ _ => True) := by
  have ready (s : State) (h : PrepareInput base src len k s ∧ P s ∧ 2 ^ (64 * (Spec.Rsa.modulusWords k - 1)) ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)) :
      WP isa VG.Impl.Bignum.Arm.PublicFn.prepare s fun t =>
        PrecomputeInput base src len (Spec.Rsa.modulusWords k) k t ∧ P t ∧ 2 ^ (64 * (Spec.Rsa.modulusWords k - 1)) ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (State.addr src) k) :=
    by
    refine WP.mono (prepare_input s h.1) ?_
    rintro t ⟨ready, frame, rest⟩
    have bytes := rsa_bytes_frame (src := State.addr src) (k := k) frame
      (by have := h.1.maxLength; omega_using [this]) (by simpa using h.1.separate)
    exact ⟨ready, K.stable frame rest h.2.1, by rw [bytes]; exact h.2.2⟩
  unfold VG.Impl.Ffdh.Arm.NormalizedPrepare.code
  exact relCT_chain (prepareInput_ct.mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h))
    ready ready (normalizedPrecompute_ct K ct countFits)

end VG.Proof.Ffdh.Arm
