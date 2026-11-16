module
public import VerifiedGarbage.Proof.Dsa.AArch64.SharedDigitsCT
public import VerifiedGarbage.Proof.Dsa.AArch64.SharedCombine
public import VerifiedGarbage.Proof.Dsa.AArch64.SharedTable
import VerifiedGarbage.Proof.Dsa.AArch64.SharedBody
import VerifiedGarbage.Proof.Dsa.AArch64.SharedBucket
import VerifiedGarbage.Proof.Dsa.AArch64.OneScanCT
import VerifiedGarbage.Proof.Dsa.AArch64.OneScan
import VerifiedGarbage.Proof.Dsa.AArch64.PublicSelect
import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtTab
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedDigitsCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedCombine
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedTable
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedBody
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedBucket
meta import VerifiedGarbage.Proof.Dsa.AArch64.OneScanCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.OneScan
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicSelect
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtTab
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # The table's start, the exponents' pointers, the products and the order check

None of them reads or branches on a secret: the buckets' products read the
entries in a fixed order, and whether `g^q = 1` goes into a mask. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.SharedPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64 VG.Impl.Dsa.AArch64.SharedPower VG.Proof.Dsa.Shared

theorem FGood.goodW {p : XPub} {s : State} (h : FGood (off p.B p.o) p.wx s) : GoodW p.ws s :=
  let ⟨mi, hg⟩ := h; ⟨mi, hg, Nat.le_refl _⟩

/-! ## The table's start -/

/-- After `j` of the table's entries. -/
def TLoop (p : XPub) (j : Nat) (s : State) : Prop :=
  ∃ (s₀ : State) (mi : BitVec 64) (N Xc : Nat), TabInv s₀ (off p.B p.o) p.wx mi N Xc j s ∧ 2 ≤ p.wx ∧
    p.wx < 2 ^ 30 ∧ Xc < N

theorem tabStart_post {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc : Nat}
    (hc : CExpCtx s P wx minv N Xc) (hw' : wx < 2 ^ 30) :
    WP isa (.block (([ldh .x3 (sArr aOne), ldh .x4 sW, .addImm .x .x4 .x4 2, .lsl .x .x4 .x4 3,
      .add .x .x3 .x3 .x4, sth .x3 Crt.sTab, sth .x3 Crt.sEnt] : List Instr) ++
        ([movi .x3 16, sth .x3 Crt.sBit] : List Instr))) s fun v => TabInv v P wx minv N Xc 0 v := by
  rw [WP.block_append_iff]
  refine WP.mono (tabInit_ok hc hw') fun u ⟨hmu, ku⟩ => ?_
  have ou : Outside P 136 120 s.mem u.mem := by
    rw [hmu]
    exact (fn_outside _ P _ (by decide) (by decide)).trans (fn_outside _ P _ (by decide) (by decide))
  have hcu := ctx_of_fn hc ou ku.wr (ku.gpr .x0 (by decide))
  refine WP.mono (WP.keep [.x3] (Q := fun v => v.mem = u.mem.writeW (off P (8 * Crt.sBit)) (BitVec.ofNat 64 16))
    (by
      brun [hcu.good.x0, hdr_enc (show Crt.sBit < 32 by decide), hcu.st (i := Crt.sBit) (by decide)]
      rfl) rfl rfl rfl) fun v ⟨hmv, kv⟩ => ?_
  have ov : Outside P 136 120 u.mem v.mem := by rw [hmv]; exact fn_outside _ P _ (by decide) (by decide)
  exact ⟨ctx_of_fn hcu ov kv.wr (kv.gpr .x0 (by decide)), by
      rw [hmv, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hmu,
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self],
    by rw [hmv, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hmu, word_writeW_self],
    by rw [hmv, word_writeW_self], fun _ h => by omega, fun _ _ => rfl, fun _ _ _ _ _ => rfl, Frm.refl _ _ _,
    Keep.refl _ _⟩

/-- The table's sixteen copies of `Y`. -/
theorem tableInit_ct : RelCT isa (Two XCtx) (seqs tableInit) (fun _ _ => True) := by
  rw [tableInit_eq]
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < 16 ∧ TLoop p 0 s) [.x0]
    (pins_x0B (fun p : XPub => off p.B p.o) fun _ _ h => h.x0) (by taint_decide)
    fun p s ⟨mi, N, Xc, hc, hA, hw, hw'⟩ => WP.mono (tabStart_post hc hw') fun v hI =>
      ⟨by decide, v, mi, N, Xc, hI, hw, hw', hA⟩) ?_
  refine (two_loop (Φ := TLoop) (Ψ := fun _ _ => True) (fun _ => 16) ?_ ?_).mono (fun _ _ h => h)
    fun _ _ _ => trivial
  · refine RelCT.seqs_append (by simp [Crt.toEnt]) (by simp) (RelCT.seq (two_post
      (Ψ := fun (q : XPub × Nat) s => s.gpr .x0 = off q.1.B q.1.o)
      (two_map (fun q : XPub × Nat => q) (fun q s ⟨hj, _, mi, N, Xc, hI, hw, hw', hA⟩ =>
        ⟨⟨mi, N, Xc, hI.ctx, hA, hw, hw'⟩, hI.ent, hj, by decide⟩) (toEnt_ct (a := aY) (by taint_decide)))
      fun q s ⟨hj, _, mi, N, Xc, hI, hw, hw', hA⟩ => WP.mono (toEnt_ok hI.ctx hw hw' (a := aY) (by decide) hj hI.ent)
        fun t ⟨_, _, k⟩ => (k.gpr .x0 (by decide)).trans hI.ctx.good.x0) ?_)
    simp only [seqs]
    exact x0_ct (fun q : XPub × Nat => off q.1.B q.1.o) (fun _ _ h => h) (by unfold Crt.nextEnt; taint_decide)
  · rintro p j s hj ⟨s₀, mi, N, Xc, hI, hw, hw', hA⟩
    exact WP.mono (tabStep_ok hw hw' hj hI) fun t ⟨hI', hz⟩ =>
      ⟨eval_nz_count hj hz, fun _ => ⟨s₀, mi, N, Xc, hI', hw, hw', hA⟩, fun _ => trivial⟩

/-! ## The exponents' pointers -/

/-- The exponents' pointers and length are read through the link to the
parent workspace, which the layout fixes. -/
theorem expInit_ct : RelCT isa (Two fun (p : XPub) s => ∃ minv, SubCtx s p.B p.Z p.o p.w p.wx minv)
    (.block SharedPower.expInit) (fun _ _ => True) := by
  unfold SharedPower.expInit
  refine RelCT.block_append (l₁ := ([ldh .x5 Crt.sLink] : List Instr))
    (l₂ := ([Crt.ldw .x3 .x5 arg2, sth .x3 Crt.sExp, .ldr .x .x3 .x5 Field.q.offset, sth .x3 Crt.sSrc,
      Crt.ldw .x3 .x5 arg2Len, sth .x3 Crt.sI] : List Instr))
    (RelCT.seq (two_piece (Ψ := fun (p : XPub) t => t.gpr .x0 = off p.B p.o ∧ t.gpr .x5 = p.B) [.x0]
      (pins_x0B (fun p : XPub => off p.B p.o)
        fun p s (h : ∃ minv, SubCtx s p.B p.Z p.o p.w p.wx minv) => let ⟨_, hc⟩ := h; hc.x0) (by taint_decide)
      fun p s h => ?_)
    (two_taint [.x0, .x5] (pins_of (fun p r => if r = .x0 then off p.B p.o else p.B) fun p s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1
      · exact h.2) (by taint_decide)))
  obtain ⟨_, hc⟩ := h
  exact WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = p.B)
    (by brun [hc.x0, hdr_enc (show Crt.sLink < 32 by decide), hc.ld' (show Crt.sLink < 32 by decide), hc.link'])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨h1, k⟩ => ⟨(k.gpr .x0 (by decide)).trans hc.x0, h1⟩

/-! ## The products -/

/-- `combine_ok`'s hypotheses. -/
def CombPre (b0 : Nat) (p : XPub) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (N Xc g : Nat) (b : Nat → Nat), CExpCtx s (off p.B p.o) p.wx mi N Xc ∧ 2 ≤ p.wx ∧
    p.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * p.wx)) N ∧ 1 < N ∧
    word s.mem (off p.B p.o) (8 * Crt.sTab) = off (off p.B p.o) (slot p.wx 8) ∧
    (∀ d < 8, d ≠ 0 → wv s.mem (off p.B p.o) (slot p.wx (8 + (b0 + d))) p.wx < N) ∧
    (∀ d < 8, d ≠ 0 → wv s.mem (off p.B p.o) (slot p.wx (8 + (b0 + d))) p.wx % N =
      g ^ b d * 2 ^ (64 * p.wx) % N) ∧
    wv s.mem (off p.B p.o) (slot p.wx aOne) p.wx = 1

/-- After `i` buckets below the seventh. -/
def CLoop (b0 : Nat) (p : XPub) (i : Nat) (t : State) : Prop :=
  ∃ (s : State) (mi : BitVec 64) (N Xc g : Nat) (b : Nat → Nat),
    CmbInv s (off p.B p.o) p.wx mi N Xc g b i t ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * p.wx)) N ∧
    word s.mem (off p.B p.o) (8 * Crt.sTab) = off (off p.B p.o) (slot p.wx 8) ∧
    (∀ d < 8, d ≠ 0 → wv s.mem (off p.B p.o) (slot p.wx (8 + (b0 + d))) p.wx < N) ∧
    (∀ d < 8, d ≠ 0 → wv s.mem (off p.B p.o) (slot p.wx (8 + (b0 + d))) p.wx % N =
      g ^ b d * 2 ^ (64 * p.wx) % N)

theorem cmbBody_ct' (M : Mont) {b0 : Nat} (hoff : b0 = 0 ∨ b0 = 8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block [ldh .x3 Crt.sBit, .addImm .x .x3 .x3 b0, sth .x3 Crt.sNib]) hc).isSome = true) :
    RelCT isa (Two fun (q : XPub × Nat) s => q.2 < 6 ∧ CLoop b0 q.1 q.2 s) (cmbBody M.mm b0)
      (fun _ _ => True) := by
  unfold cmbBody
  simp only [seqs]
  refine RelCT.seq (two_piece [.x0] (pins_x0B (fun q : XPub × Nat => off q.1.B q.1.o)
      fun _ _ ⟨_, _, _, _, _, _, _, hI, _⟩ => hI.ctx.good.x0) hT
    fun q s ⟨hi, s₀, mi, N, Xc, g, b, hI, hw, hw', hR, ht, hlt, hb⟩ =>
      cmbStep_steps M hw hw' hR hoff hi ht hlt hb hI (K := fun _ => True) fun _ _ => trivial) ?_
  refine RelCT.seq (two_post (two_map (fun q : XPub × Nat => (q.1, b0 + (6 - q.2))) (fun _ _ h => h.1)
    PublicPower.select_ct) fun _ _ h => h.2) ?_
  refine RelCT.seq (two_post (two_map (fun q : XPub × Nat => q.1.ws) (fun _ _ h => h.1.goodW)
    (M.ct (o := aY) (a := aY) (b := Crt.aT) (by unfold MmUse; decide))) fun _ _ h => h.2) ?_
  refine RelCT.seq (two_post (two_map (fun q : XPub × Nat => q.1.ws) (fun _ _ h => h.1.goodW)
    (M.ct (o := aX) (a := aX) (b := aY) (by unfold MmUse; decide))) fun _ _ h => h.2) ?_
  exact x0_ct (fun q : XPub × Nat => off q.1.B q.1.o) (fun _ _ h => let ⟨_, hg⟩ := h.1; hg.x0) (by taint_decide)

theorem cmbBody_ct (M : Mont) {b0 : Nat} (hoff : b0 = 0 ∨ b0 = 8) :
    RelCT isa (Two fun (q : XPub × Nat) s => q.2 < 6 ∧ CLoop b0 q.1 q.2 s) (cmbBody M.mm b0)
      (fun _ _ => True) := by
  rcases hoff with rfl | rfl
  · exact cmbBody_ct' M (Or.inl rfl) (by taint_decide)
  · exact cmbBody_ct' M (Or.inr rfl) (by taint_decide)

theorem combine_ct' (M : Mont) {b0 : Nat} (hoff : b0 = 0 ∨ b0 = 8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block [movi .x3 (b0 + 7), sth .x3 Crt.sNib]) hc).isSome = true) :
    RelCT isa (Two (CombPre b0)) (combine M.mm b0) (fun _ _ => True) := by
  rw [combine_eq]
  refine RelCT.seqs_append (by simp) (by simp [Crt.copyArr]) ?_
  simp only [seqs]
  unfold pick
  refine RelCT.seq (RelCT.seq (two_piece [.x0] (pins_x0B (fun p : XPub => off p.B p.o)
      fun _ _ ⟨_, _, _, _, _, hc, _⟩ => hc.good.x0) hT
    fun p s ⟨mi, N, Xc, g, b, hc, hw, hw', hR, hN, ht, hlt, hb, hone⟩ =>
      combineHead_steps hc hw hw' hoff ht hlt hb (K := fun t => 0 < 6 ∧ CLoop b0 p 0 t) fun t I0 =>
        ⟨by decide, s, mi, N, Xc, g, b, I0, hw, hw', hR, ht, hlt, hb⟩)
    (two_post (two_map (fun p : XPub => (p, b0 + 7)) (fun _ _ h => h.1) PublicPower.select_ct)
      fun _ _ h => h.2)) ?_
  refine RelCT.seqs_append (by simp [Crt.copyArr]) (by simp [Crt.copyArr]) (RelCT.seq (two_post
    (two_map (fun p : XPub => p.ws) (fun _ _ h => h.1.goodW)
      (copyArr_ct (o := aY) (a := Crt.aT) (by decide) (by decide) (by taint_decide))) fun _ _ h => h.2) ?_)
  refine RelCT.seqs_append (by simp [Crt.copyArr]) (by simp) (RelCT.seq (two_post
    (two_map (fun p : XPub => p.ws) (fun _ _ h => h.1.goodW)
      (copyArr_ct (o := aX) (a := Crt.aT) (by decide) (by decide) (by taint_decide))) fun _ _ h => h.2) ?_)
  simp only [seqs]
  refine RelCT.seq (two_post (x0_ct (fun p : XPub => off p.B p.o) (fun _ _ h => let ⟨_, hg⟩ := h.1; hg.x0)
    (by taint_decide)) fun _ _ h => h.2) ?_
  refine RelCT.seq (two_loop (Φ := CLoop b0) (Ψ := fun p s => GoodW p.ws s) (fun _ => 6) (cmbBody_ct M hoff) ?_)
    (two_map (fun p : XPub => p.ws) (fun _ _ h => h) (M.ct (o := Crt.aT) (a := aX) (b := aOne) (by unfold MmUse; decide)))
  rintro p i s hi ⟨s₀, mi, N, Xc, g, b, hI, hw, hw', hR, ht, hlt, hb⟩
  exact WP.mono (cmbStep_ok M hw hw' hR hoff hi ht hlt hb hI) fun t ⟨hI', hz⟩ =>
    ⟨eval_nz_count hi hz, fun _ => ⟨s₀, mi, N, Xc, g, b, hI', hw, hw', hR, ht, hlt, hb⟩,
      fun _ => ⟨mi, hI'.ctx.good, Nat.le_refl _⟩⟩

/-- The buckets' product reads them in a fixed order. -/
theorem combine_ct (M : Mont) {b0 : Nat} (hoff : b0 = 0 ∨ b0 = 8) :
    RelCT isa (Two (CombPre b0)) (combine M.mm b0) (fun _ _ => True) := by
  rcases hoff with rfl | rfl
  · exact combine_ct' M (Or.inl rfl) (by taint_decide)
  · exact combine_ct' M (Or.inr rfl) (by taint_decide)

/-! ## The order check -/

/-- `orderCheck_ok`'s hypotheses. -/
def OrdPre (p : XPub) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (N Xc : Nat), CExpCtx s (off p.B p.o) p.wx mi N Xc ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 30

/-- Whether `[aT] = 1` goes into a mask. -/
theorem orderCheck_ct : RelCT isa (Two OrdPre) orderCheck (fun _ _ => True) := by
  unfold orderCheck
  refine RelCT.seqs_append (by simp [Crt.copyArr]) (by simp) (RelCT.seq (two_post (Ψ := OrdPre)
    (two_map (fun p : XPub => p.ws) (fun _ _ ⟨mi, _, _, hc, _⟩ => ⟨mi, hc.good, Nat.le_refl _⟩)
      (copyArr_ct (o := aX) (a := Crt.aT) (by decide) (by decide) (by taint_decide)))
    fun p s ⟨mi, N, Xc, hc, hw, hw'⟩ => ?_) ?_)
  · have hn := hc.scrT.nowrap
    refine WP.mono (copyArr_ok hc.good (Nat.le_refl _) (by omega_arith) (by omega_arith) (o := aX) (a := Crt.aT)
      (by decide) (by decide) (by decide)) fun u ⟨_, ou, ku⟩ => ?_
    have au : Arrays (off p.B p.o) p.wx [aX] s.mem u.mem :=
      Arrays.of_outside (List.mem_singleton_self _) ou (Nat.le_refl _) (by omega_arith)
    exact ⟨mi, N, Xc, ctx_of_arrays hc au (by decide) (by decide) ku.wr (ku.gpr .x0 (by decide)), hw, hw'⟩
  simp only [seqs]
  refine RelCT.seq (two_post (Ψ := fun (p : XPub) s => s.gpr .x0 = off p.B p.o)
    (two_map (fun p : XPub => p.ws) (fun _ _ ⟨mi, _, _, hc, _⟩ => ⟨mi, hc.good, Nat.le_refl _⟩) oneScan_ct)
    fun p s ⟨mi, N, Xc, hc, hw, hw'⟩ => ?_) ?_
  · exact WP.mono (oneScan_ok hc.good (Nat.le_refl _) hw (by omega_arith)) fun v ⟨_, _, kv⟩ =>
      (kv.gpr .x0 (by decide)).trans hc.good.x0
  · exact x0_ct (fun p : XPub => off p.B p.o) (fun _ _ h => h) (by unfold Checks.zeroMask; taint_decide)

end VG.Proof.Dsa.AArch64.SharedPower
