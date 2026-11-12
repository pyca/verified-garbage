module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.TimeBaseW
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.FBatchRel
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Kinds2
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Slots
import VerifiedGarbage.Proof.Rsa.X86.Rd.TimeW2
import VerifiedGarbage.Proof.Rsa.X86.Rd.GcdW
import VerifiedGarbage.Proof.Rsa.X86.Rd.Ops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.FBatch
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.FScatter
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.FFinish
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.FInit
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.InitWords
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
import VerifiedGarbage.Proof.Divstep.Alg32
import Mathlib.Algebra.Order.Ring.Abs
meta import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.FBatchRel
meta import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Kinds2
meta import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Rsa.X86.Rd.TimeBaseW

/-! # The fused GCD's timing on i686 by words

`gcdFused` counts its double batches in the header word 100 and reads its arrays' addresses and the
rows' width from the header's slots, which the taint analysis forgets at each secret store; so each
of its operations is checked on its own (`InvBatchRt.Time`'s leaves, at rows of `w + 2` words),
between states that both runs reach with the same slots and count (`gwB`). The runs' stages around
it (`GW0`, `GW1`) are each run's own, from its correctness (`gwFused_ok`).
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.InvBatchRt (Ref Term win fgArr fgSz coefMasks row scatter gather selIn maskAt nBytes slots
  halfSlot)
open VG.Proof.Rsa.X86.InvBatchRt (rv Bx)
open VG.Proof.Rsa.X86.InvBatchRt.Time (Pre Pre0 Ok relOp leafU leaf0 stable_true ws1 relEvenMask relSelIn
  relChainAdd relChainSub relMaskAtNot relScatter relGather relWinOne relWordSteps relCountDown relStartF
  relCoefMasks relRow RowHyp RowChecks ms4 tU tV tQ tR)
open VG.Proof.Rsa.X86.KeyRt (kw)
open VG.Impl.Rsa.X86.Keys (seqs)
open VG.Impl.Mont.X86 (sc)
open VG.Impl.Weierstrass.X86 (decCounter testCounter)

/-- Both runs between the GCD's operations: the context with rows of `w + 2` words, the call's
public data, and `C` of the batch count. -/
abbrev gwB (g : Geo) (C : Nat → Prop) : State → State → Prop :=
  VG.Proof.Rsa.X86.InvBatchRt.Time.Both wid g.B g.Z (16 * g.n + 24) 22 (g.w + 2) g.args g.sp C
    fun _ => True ∧ True

/-- The analysis checks `c` from `τS` of the wide layout. -/
abbrev gwOk (c : Prog isa) : Prop := Ok wid c

theorem gw_rv (g : Geo) (x : Ref) :
    rv (kw (16 * g.n + 24)) x (g.w + 2) = 160 + x.arr * (4 * g.W + 8) + x.half * (4 * (g.w + 2)) + x.byte := by
  simp only [rv, VG.Impl.Rsa.X86.InvBatchRt.offset, kw_wid]

theorem gw_lenE (g : Geo) : ∀ a, kw (wid.toLen a) = kw (16 * g.n + 24) → kw (nar.toLen a) = kw (8 * g.n + 8) :=
  fun a ea => by
    simp only [VG.Impl.Rsa.X86.KeyRt.Lay.toLen, VG.Impl.Rsa.X86.RecoverRt.lay, VG.Proof.Rsa.X86.KeyRt.kw,
      VG.Proof.Bignum.X86.PublicRt.wb, Spec.Rsa.modulusWords] at ea ⊢
    omega

section
variable {g : Geo} {C : Nat → Prop}

/-- What the operations need of the geometry: the narrow layout's bound, and the 22 wide arrays fit. -/
structure GwFit (g : Geo) : Prop where
  up : g.n ≤ 128
  lo : 1 ≤ g.n
  fit : 160 + 22 * (4 * g.W + 8) ≤ g.Z

/-! ## The operations that `InvBatchRt.Time` has no lemma for -/

/-- The slots, and the rows' width `w + 2`. -/
theorem gwEntry (F : GwFit g) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (VG.Proof.Rsa.X86.InvBatchRt.Time.τ0 wid)
      (.block (slots wid ++ VG.Impl.Rsa.X86.RecoverDetRt.gN)) hc).isSome = true) :
    RelCT isa (fun s t => Pre0 wid g.B g.Z (16 * g.n + 24) 22 g.args g.sp s ∧
        Pre0 wid g.B g.Z (16 * g.n + 24) 22 g.args g.sp t)
      (.block (slots wid ++ VG.Impl.Rsa.X86.RecoverDetRt.gN)) (gwB g fun _ => True) := by
  have up := F.up
  refine leaf0 (fun s ps => VG.Proof.Rsa.X86.InvBatchRt.slots_ok ps.1 ps.2.1 fun u H K O =>
    WP.mono (G.gN_ok H (G.lenNar H.ws (gw_lenE g)) (by omega) (by rw [kw_nar]; simp only [VG.Impl.Rsa.X86.Recover.width]; omega))
      fun t ⟨H', K', O'⟩ => ?_) h
  have hn := H.nowrap
  have hZ := H'.halfZ
  have e52 : VG.Impl.Rsa.X86.InvBatchRt.slotBase = 52 := rfl
  have e96 : halfSlot = 96 := rfl
  rw [kw_nar] at H'
  refine ⟨H', ps.2.2.keep ((K.mono (by decide)).trans (K'.mono (by decide))) (regs := [.eax, .ecx, .edx])
    (by decide) ((O.mono (Nat.zero_le _) (by omega)).trans (O'.mono (Nat.zero_le _) (by omega))),
    trivial, trivial, trivial⟩

/-- `zeroWide wid j`. -/
theorem gwZeroW (F : GwFit g) {j : Nat} (hj : j < 22) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (VG.Proof.Rsa.X86.InvBatchRt.Time.τS wid)
      (VG.Impl.Rsa.X86.KeyRt.zeroWide wid j) hc).isSome = true) :
    RelCT isa (gwB g C) (VG.Impl.Rsa.X86.KeyRt.zeroWide wid j) (gwB g C) := by
  have fit := F.fit
  have hjS : j * (4 * g.W + 8) + (4 * g.W + 8) ≤ 22 * (4 * g.W + 8) := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
  exact relOp (rs := [.eax, .ecx, .edx, .ebp]) (ws := [(160 + j * (4 * g.W + 8), 4 * g.W + 8)]) (by decide) (stable_true _)
    (ws1 (by omega) (by omega))
    (fun s hb _ => WP.mono (VG.Proof.Rsa.X86.KeyRt.zeroWide_ok hb.ws hj) fun t ⟨_, k, _, K⟩ => by
      have O := G.keep_outside k
      simp only [VG.Proof.Rsa.X86.Keys.arr, VG.Proof.Rsa.X86.Keys.S, VG.Impl.Rsa.X86.Keys.hdr, kw_wid] at O
      rw [show 4 * (VG.Impl.Rsa.X86.Recover.wide g.n + 2) = 4 * g.W + 8 by simp only [Geo.W]; omega] at O
      exact ⟨hb.keep K (by decide) (by decide) O (by omega) (by omega), K, O.unch, trivial⟩) h

/-- `copy nar o a`. -/
theorem gwCopyN (F : GwFit g) {o a : Nat} (ho : o < 44) (ha : a < 44) (hoa : o ≠ a)
    {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (VG.Proof.Rsa.X86.InvBatchRt.Time.τS wid)
      (VG.Impl.Rsa.X86.KeyRt.copy nar o a) hc).isSome = true) :
    RelCT isa (gwB g C) (VG.Impl.Rsa.X86.KeyRt.copy nar o a) (gwB g C) := by
  have fit := F.fit
  have hW : g.W = 2 * g.w + 2 := rfl
  have hoS : o * (4 * g.w + 8) + (4 * g.w + 8) ≤ 44 * (4 * g.w + 8) := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ ho
  exact relOp (rs := [.eax, .ebx, .ecx, .edx, .ebp]) (ws := [(160 + o * (4 * g.w + 8), 4 * g.w)]) (by decide) (stable_true _)
    (ws1 (by omega) (by omega))
    (fun s hb _ => WP.mono (copyOut_ok (G.rtNar hb.ws F.up) ho ha hoa) fun t ⟨_, O, _, K⟩ => by
      simp only [VG.Proof.Rsa.X86.Keys.arr, VG.Proof.Rsa.X86.Keys.S, VG.Impl.Rsa.X86.Keys.hdr, kw_nar] at O
      rw [show 4 * (VG.Impl.Rsa.X86.Recover.width g.n + 2) = 4 * g.w + 8 by simp only [Geo.w]; omega,
        show VG.Impl.Rsa.X86.Recover.width g.n = g.w from rfl] at O
      exact ⟨hb.keep K (by decide) (by decide) O (by omega) (by omega), K, O.unch, trivial⟩) h

/-- `zeroWide nar j`. -/
theorem gwZeroN (F : GwFit g) {j : Nat} (hj : j < 44) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (VG.Proof.Rsa.X86.InvBatchRt.Time.τS wid)
      (VG.Impl.Rsa.X86.KeyRt.zeroWide nar j) hc).isSome = true) :
    RelCT isa (gwB g C) (VG.Impl.Rsa.X86.KeyRt.zeroWide nar j) (gwB g C) := by
  have fit := F.fit
  have hW : g.W = 2 * g.w + 2 := rfl
  have hjS : j * (4 * g.w + 8) + (4 * g.w + 8) ≤ 44 * (4 * g.w + 8) := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
  exact relOp (rs := [.eax, .ecx, .edx, .ebp]) (ws := [(160 + j * (4 * g.w + 8), 4 * g.w + 8)]) (by decide) (stable_true _)
    (ws1 (by omega) (by omega))
    (fun s hb _ => WP.mono (VG.Proof.Rsa.X86.KeyRt.zeroWide_ok (G.rtNar hb.ws F.up) hj) fun t ⟨_, k, _, K⟩ => by
      have O := G.keep_outside k
      simp only [VG.Proof.Rsa.X86.Keys.arr, VG.Proof.Rsa.X86.Keys.S, VG.Impl.Rsa.X86.Keys.hdr, kw_nar] at O
      rw [show 4 * (VG.Impl.Rsa.X86.Recover.width g.n + 2) = 4 * g.w + 8 by simp only [Geo.w]; omega] at O
      exact ⟨hb.keep K (by decide) (by decide) O (by omega) (by omega), K, O.unch, trivial⟩) h

/-- The block of the double batches' count, `(3 w + 6) / 2`. -/
abbrev gwCountCode : Prog isa :=
  .block (VG.Impl.Rsa.X86.KeyRt.bytesB nar .eax ++ ([.shift .shr .eax 2, .mov .ecx (.reg .eax),
    .alu .add .eax (.reg .ecx), .alu .add .eax (.reg .ecx), .alu .add .eax (.imm 6), .shift .shr .eax 1,
    .store (sc 100) .eax] : List Instr))

theorem gwCount (F : GwFit g) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (VG.Proof.Rsa.X86.InvBatchRt.Time.τS wid) gwCountCode hc).isSome = true) :
    RelCT isa (gwB g C) gwCountCode (gwB g (· = (3 * g.w + 6) / 2)) := by
  have up := F.up
  have fit := F.fit
  refine leafU (fun s ps => WP.mono (G.countG_ok ps.1 (G.lenNar ps.1.ws (gw_lenE g)) (by omega))
    fun t ⟨H, M, K⟩ => ?_) h
  have hn := ps.1.nowrap
  have hZ := ps.1.halfZ
  have e96 : halfSlot = 96 := rfl
  have O : Outside g.B 100 4 s.mem t.mem := by rw [M]; exact writeW32_outside _ _ _ (by omega)
  refine ⟨H, ps.2.1.keep K (by decide) (O.mono (Nat.zero_le _) (by omega)), ?_, trivial, trivial⟩
  show w32 t.mem g.B 100 = (3 * g.w + 6) / 2
  rw [M, w32_write_self, BitVec.toNat_ofNat, kw_nar, show VG.Impl.Rsa.X86.Recover.width g.n = g.w from rfl]
  have : g.w = 2 * g.n + 2 := rfl
  omega


/-! ## A batch, and the loop of double batches -/

/-- The analysis's checks of a batch's parts, from the elements' byte `i` to byte `o`. -/
structure GwChecks (i o : Nat) : Prop where
  start : gwOk (.block (VG.Proof.Rsa.X86.InvBatchRt.F.startF wid i))
  steps : gwOk (VG.Impl.Weierstrass.X86.Inv.wordSteps win 30)
  masks : gwOk (.block coefMasks)
  r₁ : RowChecks wid false fgArr fgSz o [tU i, tV i] [tU i, tV i]
  r₂ : RowChecks wid false fgArr fgSz (o + 4) [tQ i, tR i] [tQ i, tR i]

theorem gw_eW (g : Geo) : g.W = 4 * g.n + 6 := by
  simp only [Geo.W, VG.Impl.Rsa.X86.Recover.wide, VG.Impl.Rsa.X86.Recover.width]; omega

theorem gw_nw (F : GwFit g) : 160 + 16 * (8 * VG.Proof.Rsa.X86.InvBatchRt.nw (16 * g.n + 24) + 8) ≤ g.Z := by
  have fit := F.fit
  have eW := gw_eW g
  simp only [VG.Proof.Rsa.X86.InvBatchRt.nw, kw_wid, show VG.Impl.Rsa.X86.Recover.wide g.n = g.W from rfl]
  omega

theorem gwBatchCode (F : GwFit g) {i o : Nat} (hio : i = 0 ∧ o = 8 ∨ i = 8 ∧ o = 0) (K : GwChecks i o) :
    RelCT isa (gwB g C) (seqs [.block (VG.Proof.Rsa.X86.InvBatchRt.F.startF wid i),
      VG.Impl.Weierstrass.X86.Inv.wordSteps win 30, .block coefMasks,
      row wid false fgArr fgSz o [tU i, tV i] [tU i, tV i],
      row wid false fgArr fgSz (o + 4) [tQ i, tR i] [tQ i, tR i]]) (gwB g C) := by
  have fit := F.fit
  have lo := F.lo
  have eW := gw_eW g
  have hw : g.w = 2 * g.n + 2 := rfl
  have r4 : rv (kw (16 * g.n + 24)) { arr := fgArr } (g.w + 2) = 160 + 4 * (4 * g.W + 8) := by
    rw [gw_rv]; show 160 + 4 * _ + 0 * _ + 0 = _; omega
  have hnw := gw_nw F
  have eP : VG.Impl.Rsa.X86.InvBatchRt.sP = 176 := rfl
  have eU : VG.Impl.Rsa.X86.InvBatchRt.sMu = 160 := rfl
  have e16 : win = 16 := rfl
  have efs : fgSz = 16 := rfl
  have hi : i ≤ 8 := by omega
  have ho : o ≤ 8 := by omega
  have hm4 : ∀ t ∈ ms4 i,
      t.c + 4 ≤ rv (kw (16 * g.n + 24)) { arr := fgArr } (g.w + 2) ∧
      t.m + 4 ≤ rv (kw (16 * g.n + 24)) { arr := fgArr } (g.w + 2) ∧
      (t.c + 4 ≤ VG.Impl.Rsa.X86.InvBatchRt.sP ∨ VG.Impl.Rsa.X86.InvBatchRt.sP + 8 ≤ t.c) ∧
      (t.m + 4 ≤ VG.Impl.Rsa.X86.InvBatchRt.sP ∨ VG.Impl.Rsa.X86.InvBatchRt.sP + 8 ≤ t.m) := by
    intro t ht
    simp only [ms4, List.mem_cons, List.not_mem_nil, or_false] at ht
    rw [r4]
    rcases ht with rfl | rfl | rfl | rfl <;> simp only [tU, tV, tQ, tR] <;> omega
  have H₁ : RowHyp (16 * g.n + 24) g.Z (g.w + 2) fgArr fgSz o [tU i, tV i] [tU i, tV i] (ms4 i) :=
    ⟨by omega, by omega, .inl rfl, by omega, by rw [r4, efs]; omega, by rw [r4, eP]; omega, hm4, fun t ht => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> exact ⟨by simp [ms4], by simp only [tU, tV]; omega⟩, fun _ h => h⟩
  have H₂ : RowHyp (16 * g.n + 24) g.Z (g.w + 2) fgArr fgSz (o + 4) [tQ i, tR i] [tQ i, tR i] (ms4 i) :=
    ⟨by omega, by omega, .inl rfl, by omega, by rw [r4, efs]; omega, by rw [r4, eP]; omega, hm4, fun t ht => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> exact ⟨by simp [ms4], by simp only [tQ, tR]; omega⟩, fun _ h => h⟩
  simp only [seqs]
  refine RelCT.seq (relStartF (by omega) hnw K.start) ?_
  refine RelCT.seq (relWordSteps (stable_true _) hnw K.steps.choose_spec) ?_
  refine RelCT.seq (relCoefMasks (i := i) K.masks) ?_
  refine RelCT.seq (relRow H₁ K.r₁) ?_
  exact (relRow H₂ K.r₂).mono (fun _ _ h => h)
    fun _ _ ⟨ps, pt⟩ => ⟨⟨ps.1, ps.2.1, ps.2.2.1, trivial, trivial⟩, ⟨pt.1, pt.2.1, pt.2.2.1, trivial, trivial⟩⟩

theorem gw_batchT : VG.Impl.Rsa.X86.RecoverDetRt.batchG true = seqs [.block (VG.Proof.Rsa.X86.InvBatchRt.F.startF wid 0),
    VG.Impl.Weierstrass.X86.Inv.wordSteps win 30, .block coefMasks,
    row wid false fgArr fgSz 8 [tU 0, tV 0] [tU 0, tV 0],
    row wid false fgArr fgSz (8 + 4) [tQ 0, tR 0] [tQ 0, tR 0]] := rfl

theorem gw_batchF : VG.Impl.Rsa.X86.RecoverDetRt.batchG false = seqs [.block (VG.Proof.Rsa.X86.InvBatchRt.F.startF wid 8),
    VG.Impl.Weierstrass.X86.Inv.wordSteps win 30, .block coefMasks,
    row wid false fgArr fgSz 0 [tU 8, tV 8] [tU 8, tV 8],
    row wid false fgArr fgSz (0 + 4) [tQ 8, tR 8] [tQ 8, tR 8]] := rfl

theorem gwChecks₀ : GwChecks 0 8 :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩⟩

theorem gwChecks₈ : GwChecks 8 0 :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩⟩

theorem gwBatch (F : GwFit g) (b : Bool) :
    RelCT isa (gwB g C) (VG.Impl.Rsa.X86.RecoverDetRt.batchG b) (gwB g C) := by
  cases b
  · rw [gw_batchF]; exact gwBatchCode F (.inr ⟨rfl, rfl⟩) gwChecks₈
  · rw [gw_batchT]; exact gwBatchCode F (.inl ⟨rfl, rfl⟩) gwChecks₀

/-- The loop's body: two batches, then their count down by one. -/
abbrev gwDoubleCode : Prog isa :=
  seqs [VG.Impl.Rsa.X86.RecoverDetRt.batchG true, VG.Impl.Rsa.X86.RecoverDetRt.batchG false,
    .block [.mov .esi (.mem (sc 100)), decCounter, .store (sc 100) .esi, testCounter]]

theorem gwDouble {k : Nat} (F : GwFit g) (hk : 1 ≤ k) (hk32 : k < 2 ^ 32) :
    RelCT isa (gwB g (· = k)) gwDoubleCode
      (fun s t => gwB g (· = k - 1) s t ∧ s.zf = some (decide (k - 1 = 0)) ∧ t.zf = some (decide (k - 1 = 0))) := by
  simp only [gwDoubleCode, seqs]
  exact RelCT.seq (gwBatch F true) (RelCT.seq (gwBatch F false) (relCountDown hk hk32 (by taint_decide)))

/-- The double batches, from the count `K`. -/
theorem gwLoop (F : GwFit g) (K : Nat) :
    RelCT isa (fun s t => gwB g (· = K) s t ∧ 1 ≤ K ∧ K < 2 ^ 32) (.loop gwDoubleCode .ne) (gwB g (· = 0)) := by
  refine RelCT.loop (M := isa) (fun k s t => gwB g (· = k) s t ∧ 1 ≤ k ∧ k < 2 ^ 32) (fun k => ?_) K
  by_cases hk : 1 ≤ k ∧ k < 2 ^ 32
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2
  refine (gwDouble F hk.1 hk.2).mono (fun _ _ h => h.1) fun s t ⟨hb, zs, zt⟩ => ?_
  have es : isa.eval .ne s = s.zf.map (!·) := rfl
  have et : isa.eval .ne t = t.zf.map (!·) := rfl
  refine ⟨by rw [es, et, zs, zt], fun hf => ?_, fun ht => ⟨k - 1, by omega, hb, ?_, by omega⟩⟩
  · rw [es, zs] at hf
    have h0 : k - 1 = 0 := by by_contra h0; simp_all
    rw [h0] at hb
    exact hb
  · rw [es, zs] at ht
    by_contra h0
    simp_all

/-! ## The whole GCD in both runs -/

theorem gwTrace (F : GwFit g) :
    RelCT isa (fun s t => Pre0 wid g.B g.Z (16 * g.n + 24) 22 g.args g.sp s ∧
        Pre0 wid g.B g.Z (16 * g.n + 24) 22 g.args g.sp t)
      VG.Impl.Rsa.X86.RecoverDetRt.gcdFused (gwB g (· = 0)) := by
  have fit := F.fit
  have lo := F.lo
  have up := F.up
  have eW := gw_eW g
  have hw : g.w = 2 * g.n + 2 := rfl
  have eP : VG.Impl.Rsa.X86.InvBatchRt.sP = 176 := rfl
  have efs : fgSz = 16 := rfl
  have hnw := gw_nw F
  have rA : ∀ j h, rv (kw (16 * g.n + 24)) { arr := j, half := h } (g.w + 2) =
      160 + j * (4 * g.W + 8) + h * (4 * (g.w + 2)) := fun j h => by rw [gw_rv]; rfl
  have r4 : rv (kw (16 * g.n + 24)) { arr := fgArr } (g.w + 2) = 160 + 4 * (4 * g.W + 8) := by
    rw [gw_rv]; show 160 + 4 * _ + 0 * _ + 0 = _; omega
  have r7 := rA 7 0; have r8 := rA 8 0; have r9 := rA 9 0; have r12 := rA 12 0; have r14 := rA 14 0
  have r14h := rA 14 1
  have f1 : fgSz * (g.w + 2 + 1) = 16 * (g.w + 3) := rfl
  have f2 : fgSz * (g.w + 2 + 2) = 16 * (g.w + 4) := rfl
  unfold VG.Impl.Rsa.X86.RecoverDetRt.gcdFused
  simp only [seqs]
  refine RelCT.seq (gwEntry F (by taint_decide)) ?_
  refine RelCT.seq (gwZeroW F (j := 7) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (gwCopyN F (o := 14) (a := VG.Impl.Rsa.X86.RecoverDetRt.aGm) (by decide) (by decide)
    (by decide) (by taint_decide)) ?_
  refine RelCT.seq (gwZeroW F (j := 8) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (gwCopyN F (o := 16) (a := VG.Impl.Rsa.X86.RecoverDetRt.aGx) (by decide) (by decide)
    (by decide) (by taint_decide)) ?_
  refine RelCT.seq (gwZeroW F (j := 9) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (relEvenMask (stable_true _) (by taint_decide)) ?_
  refine RelCT.seq (relSelIn (stable_true _) (by decide) (by omega) (by omega)
    (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relChainAdd (X := fun _ => True) (stable_true _) (fun _ _ => trivial) (by decide) rfl
    (by omega) (by omega) (by omega)
    (.inl (Nat.le_refl _)) (.inl (by omega)) (by taint_decide)) ?_
  refine RelCT.seq (relScatter (by decide) (by omega) (by omega)
    (by omega) (.inr (by omega)) ⟨_, by taint_decide⟩) ?_
  refine RelCT.seq (relScatter (by decide) (by omega) (by omega)
    (by omega) (.inr (by omega)) ⟨_, by taint_decide⟩) ?_
  refine RelCT.seq (relWinOne (stable_true _) hnw (by taint_decide)) ?_
  refine RelCT.seq (gwCount F (by taint_decide)) ?_
  refine RelCT.seq ((gwLoop F ((3 * g.w + 6) / 2)).mono (fun _ _ h => ⟨h, by omega, by omega⟩)
    fun _ _ h => h) ?_
  refine RelCT.seq (gwBatch F true) ?_
  refine RelCT.seq (relGather (by decide) (by omega) (by omega)
    (.inr (by omega)) ⟨_, by taint_decide⟩) ?_
  refine RelCT.seq (gwZeroW F (j := 12) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (relChainSub (X := fun _ => True) (stable_true _) (fun _ _ => trivial) (by decide) rfl
    (by omega) (by omega) (by omega)
    (.inl (Nat.le_refl _)) (.inl (by omega)) (by taint_decide)) ?_
  refine RelCT.seq (relMaskAtNot (stable_true _) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relSelIn (stable_true _) (by decide) (by omega) (by omega)
    (.inl (by omega)) (by taint_decide)) ?_
  refine RelCT.seq (gwCopyN F (o := VG.Impl.Rsa.X86.RecoverDetRt.aG) (a := 24) (by decide) (by decide)
    (by decide) (by taint_decide)) ?_
  exact gwZeroN F (j := VG.Impl.Rsa.X86.Keys.aZero) (by decide) (by taint_decide)

end

end VG.Proof.Rsa.X86.Recover

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86

theorem gw_frame {g : Geo} {n : Nat} {s : State} (hs : GW0 g n s) :
    WP isa VG.Impl.Rsa.X86.RecoverDetRt.gcdFused s (GW1 g n) := by
  obtain ⟨s0, A, AW, V, h, odd, hn⟩ := hs
  exact WP.mono (G.gcdFusedCore_ok h rfl rfl odd) fun t ⟨A', h', _, z, n'⟩ => ⟨s0, A', AW, V, h', z, n'.trans hn⟩

theorem gw_fit {g : Geo} {n : Nat} {s : State} (hs : GW0 g n s) : GwFit g := by
  obtain ⟨_, _, _, _, k, _, _⟩ := hs
  have hf : VG.Impl.Rsa.X86.Keys.hdr + 22 * VG.Proof.Rsa.X86.Keys.S (VG.Proof.Rsa.X86.KeyRt.kw (16 * g.n + 24)) ≤ g.Z :=
    k.rtW.ws.fits
  simp only [VG.Proof.Rsa.X86.Keys.S, VG.Impl.Rsa.X86.Keys.hdr, kw_wid,
    show VG.Impl.Rsa.X86.Recover.wide g.n = g.W from rfl] at hf
  exact ⟨k.upper, by have := k.lower; omega, by omega⟩

theorem gcdFused_relCT {g : Geo} (pg : PubG g) (n : Nat) :
    RelCT isa (RA (GW0 g n) (GW0 g n)) VG.Impl.Rsa.X86.RecoverDetRt.gcdFused (RA (GW1 g n) (GW1 g n)) := by
  intro s t tr ur sf tf ⟨_, hs, ht⟩ es et
  have ps : P0 g s := let ⟨_, _, _, _, k, _⟩ := hs; k.pre0 pg
  have pt : P0 g t := let ⟨_, _, _, _, k, _⟩ := ht; k.pre0 pg
  obtain ⟨e, -⟩ := gwTrace (gw_fit hs) s t tr ur sf tf ⟨ps, pt⟩ es et
  exact ⟨e, RA.of pg (fun _ h => let ⟨_, _, _, _, k, _⟩ := h; ⟨_, _, _, _, _, _, _, k⟩)
    (wpRes (gw_frame hs) es) (wpRes (gw_frame ht) et)⟩

end VG.Proof.Rsa.X86.Recover
