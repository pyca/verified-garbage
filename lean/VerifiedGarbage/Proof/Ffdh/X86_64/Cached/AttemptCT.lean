module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.AttemptCorrect
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.CombCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.StagesCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.MainCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.CoreCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.SetupCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.PublicOutputCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.R2CT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Sample
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Scalar
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Start
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Zero
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Math
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.AttemptCorrect
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.CombCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.StagesCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase

/-! # FFDH key generation from the context on x86-64: the attempt in constant time

`vg_ffdh_generate_key`'s stages, each with what the attempt keeps of the
context (`CtxIn`) and `rsp`, and the context's own stages: the width's mask
(`metaLoad`) and the comb. -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Impl.Ffdh.X86_64.Cached.Generate (metaLoad)
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.Ffdh.X86_64.GenerateKey

/-- The attempt's public data: `vg_ffdh_generate_key`'s and the context. -/
abbrev AQ : Type := GkP × Addr

/-- The cut at the context's width. -/
def Cut (p : GkP) : Prop :=
  1 ≤ Spec.Ffdh.generationScalarBits p.params ∧ Spec.Ffdh.generationScalarBits p.params ≤ 8 * p.k ∧
    p.ld = p.k - (Spec.Ffdh.generationScalarBits p.params + 7) / 8 ∧
    p.msk = cgMask (Spec.Ffdh.generationScalarBits p.params) ∧ p.sf = Spec.Ffdh.vettedScalarOfOctets p.params

/-- What the attempt keeps of the context. -/
def X (q : AQ) (s : State) : Prop := CtxIn q.1 q.2 s ∧ s.gpr .rsp = q.1.sp ∧ Cut q.1

theorem X.keep {q : AQ} {s t : State} {rs : List Reg} (h : X q s) (hf : RunFrame q.1 s.mem t.mem) (k : Keep rs s t)
    (hr : .rsp ∉ rs) : X q t :=
  ⟨h.1.keep hf k.2.1 k.2.2, (k.gpr hr).trans h.2.1, h.2.2⟩

/-- Before the cut. -/
def IVc (q : AQ) (s : State) : Prop := I q.1 s ∧ q.1.mv = true ∧ X q s

def MSc (q : AQ) (s : State) : Prop := MS q.1 s ∧ X q s

theorem metaLoad_ct : RelCT isa (Two IVc) (.block metaLoad) (Two MSc) := by
  change RelCT isa (Two IVc) (.block ([.mov .rax (.mem (VG.Impl.Rsa.X86_64.Crt.stk 6))] ++ metaLoad.drop 1)) _
  refine RelCT.block_append (pin_ct [.rdi, .rsp] [.rdi, .rax] (fun q r => if r = .rdi then q.1.B else q.2)
    (pins_of (fun q r => if r = .rdi then q.1.B else q.1.sp) fun q s h r hr => by
      obtain ⟨⟨rb, hi⟩, _, hx⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hi.rdi
      · exact hx.2.1) (by taint_decide) (fun q s h => ?_) (by taint_decide) (fun q s h => ?_))
  · obtain ⟨⟨rb, hi⟩, _, hc, hsp, _⟩ := h
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = q.2) (by
      xrun [State.ea, VG.Impl.Rsa.X86_64.Crt.stk, hsp, hdrOff, hc.sprd, hc.sp]) rfl) fun t ⟨hax, k⟩ r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (k.gpr (by decide)).trans hi.rdi
    · exact hax
  · obtain ⟨⟨rb, hi⟩, hm, hx⟩ := h
    obtain ⟨h1, h8, hld, hmsk, _⟩ := hx.2.2
    have hw := metaLoad_inputs hi hx.1 hx.2.1 h1 h8 hld hmsk
    rw [show metaLoad = [.mov .rax (.mem (VG.Impl.Rsa.X86_64.Crt.stk 6))] ++ metaLoad.drop 1 from rfl,
      WP.block_append_iff] at hw
    refine WP.seq (WP.mono hw fun t ht => WP.mono ht fun u ⟨hu, hn, hmk, hf, k⟩ => ⟨⟨rb, hu, hn, hmk, hm⟩, ?_⟩)
    have hZ := hi.base.hZ
    exact hx.keep (.of_frm hf fun r hr => Nat.le_trans (scanRanges_end r hr) (by omega)) k (by decide)

/-- `Sliced`, with the random bytes' length. -/
def SlicedC (q : AQ) (s : State) : Prop := (∃ rb, CheckPrivate.Base q.1.kp (q.1.xb rb) s ∧
  s.gpr .rdi = q.1.B ∧ word s.mem q.1.B (8 * sG) = off q.1.dp q.1.k ∧
  word s.mem q.1.B (8 * sQ) = off q.1.dp (2 * q.1.k) ∧ q.1.mv = true ∧ Buffers q.1 rb s ∧ rb.length = q.1.k) ∧ X q s

theorem SlicedC.sliced {q : AQ} {s : State} (h : SlicedC q s) : Sliced q.1 s := by
  obtain ⟨⟨rb, hb, hd, hG, hQ, hm, hbuf, _⟩, _⟩ := h
  exact ⟨rb, hb, hd, hG, hQ, hm, hbuf⟩

theorem scalar_slicedC (q : AQ) (s : State) (h : IVc q s) :
    WP isa (seqs VG.Impl.Ffdh.X86_64.Cached.Generate.scalar) s (SlicedC q) := by
  obtain ⟨⟨rb, hi⟩, hm, hx⟩ := h
  obtain ⟨h1, h8, hld, hmsk, _⟩ := hx.2.2
  refine WP.mono (scalarC_ok hi hx.1 hx.2.1 hm h1 h8 hld hmsk) fun t ⟨⟨hb, hxs, hd, hG, hQ, _, hf, k⟩, hc⟩ => ?_
  refine ⟨⟨rb, hb, hd, hG, hQ, hm, ⟨hxs, ⟨fun i hi' => by rw [k.2.2]; exact hi.base.x.wr i hi', hi.base.x.sep⟩,
    ⟨fun i hi' => by rw [k.2.2]; exact hi.base.y.wr i hi', hi.base.y.sep⟩, hi.base.xy, hi.base.cut_length,
    hi.base.ld_lt⟩, hi.base.rl⟩, hc, (k.gpr (by decide)).trans hx.2.1, hx.2.2⟩

theorem sampleC_ct : RelCT isa (Two IVc) (seqs VG.Impl.Ffdh.X86_64.Cached.Generate.scalar) (Two SlicedC) := by
  refine two_post ?_ scalar_slicedC
  change RelCT isa (Two IVc) (.seq (.block metaLoad) (.seq (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.cutSetup)
    (.seq (.loop (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.cutBody) .ne)
      (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.cutFinish)))) _
  refine RelCT.seq metaLoad_ct (two_map Prod.fst (fun _ _ h => h.1) ((pin_ct [.rdi] [.rdi, .r8, .r10, .r11, .rcx, .r14]
    cutVal (pins_rdiB GkP.B fun _ _ h => by obtain ⟨_, hi, _⟩ := h; exact hi.rdi)
    (by taint_decide) cut_regs (by taint_decide) cut_stage).mono (fun _ _ h => h) fun _ _ _ => trivial))

/-! ## The tail -/

/-- `WorkIn`, with the random bytes' length and the context. -/
def WorkInC (q : AQ) (s : State) : Prop := (∃ rb mi, CheckPrivate.Work q.1.kp (q.1.xb rb) mi s ∧
  s.gpr .rdi = off q.1.B (VG.Proof.Ffdh.X86_64.inner q.1.w) ∧ q.1.mv = true ∧ Buffers q.1 rb s ∧
  rb.length = q.1.k) ∧ X q s

theorem WorkInC.workIn {q : AQ} {s : State} (h : WorkInC q s) : WorkIn q.1 s := by
  obtain ⟨⟨rb, mi, hw, hd, hm, hb, _⟩, _⟩ := h
  exact ⟨rb, mi, hw, hd, hm, hb⟩

def ReadyInC (q : AQ) (s : State) : Prop := (∃ rb, CheckPrivate.Ready q.1.kp (q.1.xb rb) s ∧ Buffers q.1 rb s ∧
  rb.length = q.1.k) ∧ q.1.mv = true ∧ X q s

/-- `-p⁻¹ mod 2⁶⁴`, which every run's inner workspace has. -/
noncomputable def canonMi (P : Nat) : BitVec 64 :=
  Classical.epsilon fun mi : BitVec 64 => (P % 2 ^ 64 * mi.toNat + 1) % 2 ^ 64 = 0

theorem canonMi_eq {s : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64} {P : Nat} (hc : ModCtx s B Z o w mi P) :
    mi = canonMi P := by
  have hn0 : (word s.mem (off B o) (slot w aN)).toNat = P % 2 ^ 64 := by
    have := word_of_wv s.mem (off B o) (slot w aN) w (q := 0) (by have := hc.w2; omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.div_one] at this
    rw [this, hc.xv.n]
  have h := hc.xv.inv
  rw [hn0] at h
  have hs := Classical.epsilon_spec (p := fun mi : BitVec 64 => (P % 2 ^ 64 * mi.toNat + 1) % 2 ^ 64 = 0) ⟨mi, h⟩
  exact minv_unique (n := P % 2 ^ 64) (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact hc.odd) h hs

/-- The comb's public data for the attempt's. -/
noncomputable def combQ (q : AQ) : CQ :=
  (cgT q.1 (canonMi q.1.P) q.2, off q.1.xp q.1.ld, q.1.n, q.1.sp)

/-- The scalar's value is below the width's power. -/
theorem xb_lt {p : GkP} {rb : List Byte} (hc : Cut p) (hrl : rb.length = p.k) (hk : 1 ≤ p.k) :
    Spec.Rsa.os2ip (p.xb rb) < 2 ^ Spec.Ffdh.generationScalarBits p.params := by
  obtain ⟨h1, h8, hld, hmsk, _⟩ := hc
  change Spec.Rsa.os2ip ((p.cut rb).drop p.ld) < _
  rw [VG.Proof.Ffdh.KeyScalar.os2ip_cut_drop]
  have hw : ScalarWidth.width (Spec.Ffdh.generationScalarBits p.params) =
      (Spec.Ffdh.generationScalarBits p.params + 7) / 8 := by unfold ScalarWidth.width; omega
  change Spec.Rsa.os2ip (VG.Proof.Ffdh.KeyScalar.cut rb p.ld (p.msk.setWidth 8)) < _
  rw [hmsk, cgMask_byte h1, hld, ← hrl, ← hw, ScalarWidth.cut_value (by omega) (by omega)]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem ready_q0 (q : AQ) (s : State) (h : ReadyInC q s) : Q0 (combQ q) s := by
  obtain ⟨⟨rb, ⟨mi, hb, hcm, hG⟩, hbuf, hrl⟩, hm, hc, hsp, hcut⟩ := h
  have hmi := canonMi_eq hcm
  subst hmi
  have hk := hb.k2
  have hk1 := hb.k1
  have h1 := hcut.1
  have h8 := hcut.2.1
  have h8' : Spec.Ffdh.generationScalarBits q.1.params ≤ 8192 := by
    have : q.1.k = q.1.kp.k := rfl; omega
  have hrs := Rsa.FixedBaseComb.rows_small h8'
  have hrp := Rsa.FixedBaseComb.rows_pos (show 0 < Spec.Ffdh.generationScalarBits q.1.params by omega)
  have hxl : (q.1.xb rb).length = q.1.kp.xl := hb.xlen
  have hxk : q.1.kp.xl ≤ q.1.kp.k := hb.xl2
  refine ⟨q.1.xb rb, hxl, ⟨hcm, by rw [hsp]; exact hc.sprd, fun hm' => by rw [hsp]; exact hc.sp_inScr hm',
    by rw [hsp]; exact hc.sp, hb.hdr (sX, q.1.kp.xp) (by simp [CheckPrivate.KpP.headers]),
    by rw [hxl]; exact hb.hdr (sXl, BitVec.ofNat 64 q.1.kp.xl) (by simp [CheckPrivate.KpP.headers]),
    hc.reg, hc.hdr.2.2, hc.ent _, hb.x, hrp,
    show 5 * Spec.Rsa.FixedBaseComb.rows (Spec.Ffdh.generationScalarBits q.1.params) < 2 ^ 31 by omega,
    by rw [hxl]; change 8 * q.1.kp.xl < 2 ^ 32; omega, xb_lt hcut hrl (by omega)⟩, hsp⟩


theorem work_readyC (Mo : Mont) (R : R2Impl Mo) (q : AQ) (s : State) (h : WorkInC q s) :
    WP isa (.seq (.block r2Head) R.code) s (ReadyInC q) := by
  obtain ⟨⟨rb, mi, hw, hd, hm, hb, hrl⟩, hx⟩ := h
  exact WP.mono (CheckPrivate.work_ready Mo R hw hd hm) fun _ ⟨hr, hi, _, k⟩ =>
    ⟨⟨rb, hr, hb.keep hi k, hrl⟩, hm, hx.keep (.of_scr hi) k (by decide)⟩

theorem ready_valueC (Mo : Mont) (q : AQ) (s : State) (h : ReadyInC q s) :
    WP isa (seqs (VG.Impl.Ffdh.X86_64.Cached.Generate.comb Mo.mm)) s (ValueIn q.1) := by
  obtain ⟨⟨rb, hr, hb, hrl⟩, _, hc, hsp, hcut⟩ := h
  have hk := hr.choose_spec.1.k2
  have hk1 := hr.choose_spec.1.k1
  have h8 := hcut.2.1
  have h8' : Spec.Ffdh.generationScalarBits q.1.params ≤ 8192 := by
    have : q.1.k = q.1.kp.k := rfl; omega
  exact WP.mono (ready_comb Mo hr hc hsp hcut.1 h8' (xb_lt hcut hrl (by have : q.1.k = q.1.kp.k := rfl; omega))) fun _ ⟨hv, hi, _, k⟩ =>
    ⟨rb, hv, hb.keep hi k⟩

theorem tailC_ct (Mo : Mont) (R : R2Impl Mo) :
    RelCT isa (Two WorkInC)
      (seqs (VG.Impl.Ffdh.X86_64.Cached.Generate.tail Mo.mm (.seq (.block r2Head) R.code)))
      fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Cached.Generate.tail
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine seqs_cons_ct (by simp [VG.Impl.Ffdh.X86_64.Cached.Generate.comb]) (RelCT.seq (R := Two ReadyInC)
    (two_post (two_map (fun q : AQ => q.1.kp) (fun _ _ h => work_inner _ _ h.workIn)
      ((CheckPrivate.r2_ct Mo R).mono (fun _ _ h => h) (fun _ _ _ => trivial))) (work_readyC Mo R)) ?_)
  refine RelCT.seqs_append (a := VG.Impl.Ffdh.X86_64.Cached.Generate.comb Mo.mm)
    (b := VG.Impl.Ffdh.X86_64.Domain.GenerateKey.publicOutput ++
      [VG.Impl.Ffdh.X86_64.Domain.GenerateKey.maskX, .block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.status])
    (by simp [VG.Impl.Ffdh.X86_64.Cached.Generate.comb]) (by simp) (RelCT.seq (R := Two fun q : AQ => ValueIn q.1)
      (two_post (two_map combQ ready_q0 (comb_ct Mo)) (ready_valueC Mo)) ?_)
  exact two_map Prod.fst (fun _ _ h => h) (RelCT.seqs_append (a := VG.Impl.Ffdh.X86_64.Domain.GenerateKey.publicOutput)
    (by simp [VG.Impl.Ffdh.X86_64.Domain.GenerateKey.publicOutput]) (by simp)
    (RelCT.seq public_mask_ct mask_status_ct))


/-! ## The core -/

theorem sliced_workC (q : AQ) (s : State) (h : SlicedC q s) :
    WP isa (seqs ((([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup) ++
      VG.Impl.Rsa.X86_64.Crt.loadArr aXm sX sXl)) s (WorkInC q) := by
  obtain ⟨⟨rb, hb, hd, hG, hQ, hm, hbuf, hrl⟩, hx⟩ := h
  exact WP.mono (CheckPrivate.setup_work hb hd hG hQ hm) fun t ⟨⟨mi, hw, hdi⟩, hi, _, k⟩ =>
    ⟨⟨rb, mi, hw, hdi, hm, hbuf.keep hi k, hrl⟩, hx.keep (.of_scr hi) k (by decide)⟩

/-- `CS`, with the random bytes' length and the context. -/
def CSc (q : AQ) (s : State) : Prop := WorkInC q s ∧ s.gpr .rax = bit (q.1.sv = true)

def CBc (q : AQ) (s : State) : Prop :=
  WorkInC q s ∧ s.zf = some (!decide (q.1.sv = true)) ∧ s.gpr .rax = bit (q.1.sv = true)

theorem CBc.cb {q : AQ} {s : State} (h : CBc q s) : CB q.1 s := ⟨h.1.workIn, h.2⟩

theorem scalarC_stage (q : AQ) (s : State) (h : WorkInC q s) :
    WP isa (seqs VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange) s (CSc q) := by
  obtain ⟨⟨rb, mi, hw, hd, hm, hb, hrl⟩, hx⟩ := h
  exact WP.mono (CheckPrivate.scalar_ok hw hd (valid_facts hm hw.base.k1).1)
    fun _ ⟨⟨hw', hd', ha⟩, hi, _, k⟩ => ⟨⟨⟨rb, mi, hw', hd', hm, hb.keep hi k, hrl⟩,
      hx.keep (.of_scr hi) k (by decide)⟩, ha⟩

theorem testC_stage (q : AQ) (s : State) (h : CSc q s) :
    WP isa (.block [.alu .test .rax (.reg .rax)]) s (CBc q) := by
  obtain ⟨⟨⟨rb, mi, hw, hd, hm, hb, hrl⟩, hx⟩, ha⟩ := h
  refine WP.mono (test_bit_ok ha) fun t ⟨hz, hmem, k⟩ => ?_
  have hf : InScr q.1.B q.1.Z s.mem t.mem := by intro a _; rw [hmem]
  exact ⟨⟨⟨rb, mi, hw.keep hmem k, (k.gpr (by decide)).trans hd, hm, hb.keep hf k, hrl⟩,
    hx.keep (.of_scr hf) k (by decide)⟩, hz, (k.gpr (by decide)).trans ha⟩

theorem coreC_ct (Mo : Mont) (R : R2Impl Mo) :
    RelCT isa (Two SlicedC)
      (seqs (VG.Impl.Ffdh.X86_64.Cached.Generate.core Mo.mm (.seq (.block r2Head) R.code)))
      fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Cached.Generate.core
  simp only [List.append_assoc]
  refine RelCT.seqs_append (a := ([.block VG.Impl.Rsa.X86_64.head] ++ pSetup ++
      VG.Impl.Rsa.X86_64.Crt.loadArr aXm sX sXl))
    (b := VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange ++ [.block [.alu .test .rax (.reg .rax)],
      .ite .e (seqs [.block [VG.Impl.Rsa.X86_64.Crt.leave], VG.Impl.Ffdh.X86_64.Domain.GenerateKey.maskX, ret 2])
        (seqs (VG.Impl.Ffdh.X86_64.Cached.Generate.tail Mo.mm (.seq (.block r2Head) R.code)))])
    (by simp [pSetup]) (by simp) (RelCT.seq (R := Two WorkInC)
      (two_post (two_map Prod.fst (fun _ _ h => h.sliced) (setup_load_ct.mono (fun _ _ h => h) fun _ _ _ => trivial)) sliced_workC) ?_)
  refine RelCT.seqs_append (a := VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange)
    (by simp [VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange, isNonzero, geArr, cmpArr]) (by simp)
    (RelCT.seq (R := Two CSc)
      (two_post (two_map (fun q : AQ => q.1.kp) (fun _ _ h => work_inner _ _ h.workIn)
        CheckPrivate.scalar_ct) scalarC_stage) ?_)
  simp only [seqs]
  refine RelCT.seq (R := Two CBc)
    (two_piece [] (fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide) testC_stage) ?_
  exact two_ite (fun _ _ _ h₁ h₂ => by rw [branch_eval h₁.cb, branch_eval h₂.cb])
    (two_map Prod.fst (fun _ _ h => ⟨h.1.cb, h.2⟩) reject_ct)
    (two_map id (fun _ _ h => h.1.1) (tailC_ct Mo R))


/-! ## The attempt -/

def ZeroPreC (q : AQ) (s : State) : Prop := (∃ rb, Base q.1 rb s ∧ s.gpr .rdi = q.1.B ∧
  word s.mem q.1.B (8 * sG) = off q.1.dp q.1.k ∧ word s.mem q.1.B (8 * sQ) = off q.1.dp (2 * q.1.k)) ∧
    q.1.mv = true ∧ X q s

theorem zero_inputsC (q : AQ) (s : State) (h : ZeroPreC q s) :
    WP isa (VG.Impl.Rsa.X86_64.Keys.zeroOut sY sK) s (IVc q) := by
  obtain ⟨⟨rb, hb, hd, hG, hQ⟩, hm, hx⟩ := h
  have hZ := hb.hZ
  refine WP.mono (zero_ok hb hd) fun t ⟨hb', hy, hf, hh, k⟩ => ?_
  exact ⟨⟨rb, hb', (k.gpr (by decide)).trans hd, hy,
    (hh _ (by change 224 ≤ q.1.Z; omega)).trans hG,
    (hh _ (by change 232 ≤ q.1.Z; omega)).trans hQ⟩, hm, hx.keep (RunFrame.of_y hf) k (by decide)⟩

theorem zeroC_ct : RelCT isa (Two ZeroPreC) (VG.Impl.Rsa.X86_64.Keys.zeroOut sY sK) (Two IVc) :=
  pin_ct [.rdi] [.rsi, .rcx] (fun q => zeroVal q.1)
    (pins_rdiB (fun q : AQ => q.1.B) fun _ _ h => by obtain ⟨⟨_, _, hd, _⟩, _⟩ := h; exact hd)
    (by taint_decide) (fun q s h => zero_regs q.1 s (by obtain ⟨⟨rb, hb, hd, _⟩, _⟩ := h; exact ⟨rb, hb, hd⟩))
    (by taint_decide) zero_inputsC

theorem mainC_ct (Mo : Mont) (R : R2Impl Mo) :
    RelCT isa (Two ZeroPreC)
      (VG.Impl.Ffdh.X86_64.Cached.Generate.main Mo.mm (.seq (.block r2Head) R.code)) fun _ _ => True := by
  change RelCT isa (Two ZeroPreC) (.seq (VG.Impl.Rsa.X86_64.Keys.zeroOut sY sK)
    (seqs (VG.Impl.Ffdh.X86_64.Cached.Generate.scalar ++
      VG.Impl.Ffdh.X86_64.Cached.Generate.core Mo.mm (.seq (.block r2Head) R.code)))) _
  exact RelCT.seq zeroC_ct (RelCT.seqs_append
    (a := VG.Impl.Ffdh.X86_64.Cached.Generate.scalar)
    (by simp [VG.Impl.Ffdh.X86_64.Cached.Generate.scalar])
    (by simp [VG.Impl.Ffdh.X86_64.Cached.Generate.core, pSetup])
    (RelCT.seq sampleC_ct (coreC_ct Mo R)))

/-- The contract's caller, and its public data. -/
def CRc (q : AQ) (s : State) : Prop := cgPre s ∧ (cgOf s, stackArg s 5) = q

def E1c (q : AQ) (s : State) : Prop := (∃ rb, Base q.1 rb s ∧ s.gpr .rdi = q.1.B) ∧ X q s

def ELc (q : AQ) (s : State) : Prop := s.gpr .rax = q.1.B ∧ WP isa (.block entryTail) s (E1c q)

theorem cut_cgOf {s : State} (hv : Spec.Ffdh.domainValid (stackArg s 0).toNat (gkDom s) = true) : Cut (cgOf s) :=
  ⟨(genBits_facts hv).1, (genBits_facts hv).2, rfl, rfl, rfl⟩

theorem entryC_ct : RelCT isa (Two CRc) (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.entry) (Two E1c) := by
  change RelCT isa (Two CRc) (.block (loads ++ entryTail)) (Two E1c)
  refine RelCT.block_append (RelCT.seq (R := Two ELc)
    (two_piece [.rsp] (pins_of (fun q _ => q.1.sp) fun q s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [← h.2]; rfl)
      (by taint_decide) ?_) ?_)
  · intro q s h
    obtain ⟨c, hci, hv⟩ := cgCtx_of h.1
    have hw : WP isa (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.entry) s (E1c q) :=
      WP.mono (entry_base c) fun t ⟨hb, hd, hi, _, k⟩ => by
        rw [← h.2]
        exact ⟨⟨gkRand s, hb.cached hv, hd⟩, hci.keep (.of_scr hi) k.2.1 k.2.2, (k.gpr (by decide)).trans rfl,
          cut_cgOf hv⟩
    change WP isa (.block (loads ++ entryTail)) s (E1c q) at hw
    refine WP.and ?_ (WP.block_append_iff.mp hw)
    exact WP.mono (loads_ok s c) fun t hh => by rw [← h.2]; exact hh
  exact two_piece [.rax] (pins_of (fun q _ => q.1.B) fun _ _ h _ hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.1) (by taint_decide) fun _ _ h => h.2

theorem e1c_dhp (q : AQ) (s : State) (h : E1c q s) : DHP q.1.d s := by
  obtain ⟨⟨rb, hb, hd⟩, _⟩ := h
  have hZ := hb.hZ
  exact ⟨hb.scr, hd, by change 256 ≤ q.1.Z; omega,
    hb.hdr (sDom, q.1.dp) (by simp [GkP.headers]),
    hb.hdr (sK, BitVec.ofNat 64 q.1.k) (by simp [GkP.headers])⟩

def CEc (q : AQ) (s : State) : Prop := (∃ rb, Base q.1 rb s ∧ s.gpr .rdi = q.1.B ∧
  word s.mem q.1.B (8 * sG) = off q.1.dp q.1.k ∧ word s.mem q.1.B (8 * sQ) = off q.1.dp (2 * q.1.k)) ∧
    s.zf = some q.1.mv ∧ X q s

theorem e1c_ce (q : AQ) (s : State) (h : E1c q s) : WP isa (.block domHead) s (CEc q) := by
  obtain ⟨⟨rb, hb, hd⟩, hx⟩ := h
  exact WP.mono (dom_base hb hd) fun _ ⟨hb', hz, hd', hG, hQ, hi, _, k⟩ =>
    ⟨⟨rb, hb', hd', hG, hQ⟩, hz, hx.keep (.of_scr hi) k (by decide)⟩

theorem cec_eval {q : AQ} {s : State} (h : CEc q s) : isa.eval .ne s = some (!q.1.mv) := by
  simp [eval, h.2.1]

theorem cec_zero (q : AQ) (s : State) (h : CEc q s ∧ isa.eval .ne s = some false) : ZeroPreC q s := by
  have he := h.2
  rw [cec_eval h.1] at he
  have hm : q.1.mv = true := by simpa using he
  exact ⟨h.1.1, hm, h.1.2.2⟩

theorem bodyC_ct (Mo : Mont) (R : R2Impl Mo) :
    RelCT isa (Two CRc) (VG.Impl.Ffdh.X86_64.Cached.Generate.body Mo.mm (.seq (.block r2Head) R.code))
      fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Cached.Generate.body
  refine RelCT.seq (R := Two CEc) (RelCT.block_append (RelCT.seq entryC_ct
    (two_post (two_map (fun q : AQ => q.1.d) e1c_dhp domHead_ct) e1c_ce))) ?_
  exact two_ite (fun _ _ _ h₁ h₂ => by rw [cec_eval h₁, cec_eval h₂])
    (two_taint [] (fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide))
    (two_map id cec_zero (mainC_ct Mo R))

theorem codeC_ct (Mo : Mont) (R : R2Impl Mo) :
    RelCT isa (Two CRc) (VG.Impl.Ffdh.X86_64.Cached.Generate.code Mo.mm (.seq (.block r2Head) R.code))
      fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Cached.Generate.code
  refine RelCT.seq (R := Two fun (q : AQ) s => s.gpr .rdi = q.1.B)
    (two_post (bodyC_ct Mo R) fun q s h =>
      WP.mono (cgBody_ok Mo R h.1) fun t ⟨_, hd, _⟩ => by rw [← h.2]; exact hd)
    (two_taint [.rdi] (pins_rdiB (fun q : AQ => q.1.B) fun _ _ h => h) (by taint_decide))


theorem cg_constantTime (Mo : Mont) (R : R2Impl Mo) :
    ConstantTime isa cgContract.pre cgContract.pub
      (VG.Impl.Ffdh.X86_64.Cached.Generate.code Mo.mm (.seq (.block r2Head) R.code)) := by
  refine RelCT.constantTime ((codeC_ct Mo R).mono
    (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨(cgOf s₁, stackArg s₁ 5), ⟨h₁, rfl⟩, h₂, ?_⟩) fun _ _ h => h)
  obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, a0, a1, a2, a3, a4, a5, a6⟩ := hp
  unfold cgLeak at hl
  obtain ⟨hd, hstatus⟩ := List.append_inj hl (by simp [cgDom, Spec.Rsa.bytesAt, r5])
  have hdom := ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hd)
  have hs := (List.cons.inj hstatus).1
  have hfalse : ((cgOf s₁).sv = false) ↔ ((cgOf s₂).sv = false) := by
    change (Spec.Ffdh.privateValid (cgA s₁) (cgS s₁) = false) ↔
      (Spec.Ffdh.privateValid (cgA s₂) (cgS s₂) = false)
    rw [← keyStatus_scalar _ _, ← keyStatus_scalar _ _, hs]
  have hsv : (cgOf s₁).sv = (cgOf s₂).sv := by
    cases h₁ : (cgOf s₁).sv <;> cases h₂ : (cgOf s₂).sv <;> simp_all
  have hA : gkA s₂ = gkA s₁ := by simp only [gkA, a0, hdom]
  have hD : gkDom s₂ = gkDom s₁ := hdom.symm
  simp only [cgOf, gkOf, cgBits, cgEl, r0, r2, r4, r5, a0, a1, a3, a4, a5, hsp, hD, hA]
  congr 2
  simpa only [cgOf, gkOf, r0, r1, r2, r3, r4, r5, a0, a1, a2, a3, a4, hsp, hD, hA] using hsv.symm

end VG.Proof.Ffdh.X86_64.Cached
