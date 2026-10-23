module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Exchange.Correct
import VerifiedGarbage.Proof.Ffdh.AArch64.OutMaskCT
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.CT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExpCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Exchange.Correct
meta import VerifiedGarbage.Proof.Ffdh.AArch64.OutMaskCT
meta import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.CT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExpCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# `vg_ffdh_exchange` on AArch64: constant time

Runs with the same public data (`ExP`: all but the scalar's octets) leak the
same (`ex_constantTime`): the exponentiation is RSA's, constant time in the
exponent, and the shared value is stored masked by its flag, without a
branch.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Exchange

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Ffdh.AArch64.CheckDomain (ct_post pins_nil)

/-- A stage of some scalar. -/
def Ex (Φ : ExP → List Byte → State → Prop) (p : ExP) (t : State) : Prop := ∃ xb, Φ p xb t

theorem ex_post {Φ Ψ : ExP → List Byte → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two (Ex Φ)) c fun _ _ => True)
    (hw : ∀ p xb s, Φ p xb s → WP isa c s fun u => Ψ p xb u ∧ KX s u) : RelCT isa (Two (Ex Φ)) c (Two (Ex Ψ)) :=
  two_post hct fun p s ⟨xb, h⟩ => WP.mono (hw p xb s h) fun _ h => ⟨xb, h.1⟩

/-- The entry's registers but `x8`. -/
def entryRegs (p : ExP) (r : Reg) : BitVec 64 :=
  if r = .x0 then p.op else if r = .x2 then p.dp else if r = .x3 then BitVec.ofNat 64 p.dl else
    if r = .x4 then BitVec.ofNat 64 p.k else if r = .x5 then p.xp else if r = .x6 then BitVec.ofNat 64 p.xl else
      if r = .x7 then p.yp else p.B

theorem cr_regs (p : ExP) (xb : List Byte) (s : State) (h : CR p xb s) :
    ∀ r ∈ [Reg.x0, .x2, .x3, .x4, .x5, .x6, .x7], s.gpr r = entryRegs p r := by
  obtain ⟨-, -, -, -, hk, hdl, hdp, -, hop, hxp, hxl, hyp, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [entryRegs, reduceCtorEq, ↓reduceIte]
  · exact hop
  · exact hdp
  · rw [← hdl, ofNat_toNat64]
  · rw [← hk, ofNat_toNat64]
  · exact hxp
  · rw [← hxl, ofNat_toNat64]
  · exact hyp

/-- After the entry's first instruction. -/
def EA (p : ExP) (xb : List Byte) (t : State) : Prop :=
  (∀ r ∈ [Reg.x0, .x2, .x3, .x4, .x5, .x6, .x7, .x8], t.gpr r = entryRegs p r) ∧
    WP isa (.block (Exchange.entry.drop 1)) t fun u => E1 (p.D xb) u ∧ Dst p u

theorem entry_split : Exchange.entry ++ domHead = ([.ldrSp .x8 8] : List Instr) ++ (Exchange.entry.drop 1 ++ domHead) := rfl

theorem cr_ea (p : ExP) (xb : List Byte) (s : State) (h : CR p xb s) :
    WP isa (.block [.ldrSp .x8 8]) s (EA p xb) := by
  have c := exCtx_of h.1
  have hw := cr_e1 p xb s h
  rw [show Exchange.entry = [.ldrSp .x8 8] ++ Exchange.entry.drop 1 from rfl, WP.block_append_iff] at hw
  refine WP.mono (wp_and (ldrSp_ok h.2.2.1 c.ha1) hw) fun t ⟨⟨⟨h8, _⟩, k⟩, hr⟩ => ⟨fun r hr' => ?_,
    WP.mono hr fun u hu => hu.1⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    have hc := cr_regs p xb s h
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [k.gpr _ (by decide)]; exact hc _ (by simp)
    · rw [k.gpr _ (by decide)]; exact hc _ (by simp)
    · rw [k.gpr _ (by decide)]; exact hc _ (by simp)
    · rw [k.gpr _ (by decide)]; exact hc _ (by simp)
    · rw [k.gpr _ (by decide)]; exact hc _ (by simp)
    · rw [k.gpr _ (by decide)]; exact hc _ (by simp)
    · rw [k.gpr _ (by decide)]; exact hc _ (by simp)
    · rw [h8]; rfl

/-- After the entry's first instruction, with the inputs' lengths. -/
def EA' (p : ExP) (xb : List Byte) (t : State) : Prop := EA p xb t ∧ Ok p xb

/-- After the entry. -/
def E1' (p : ExP) (xb : List Byte) (t : State) : Prop := E1 (p.D xb) t ∧ Dst p t ∧ Ok p xb

/-- After `domHead`. -/
def CE' (p : ExP) (xb : List Byte) (t : State) : Prop := CE (p.D xb) t ∧ Dst p t ∧ Ok p xb

/-- The working space, as the arithmetic sees it. -/
abbrev ExP.ws (p : ExP) : Ws := ⟨off p.B (inner ((p.k + 7) / 8)), slot ((p.k + 7) / 8) 8, (p.k + 7) / 8⟩

/-- The inner workspace's base. -/
abbrev ExP.g (p : ExP) : Addr := off p.B (inner ((p.k + 7) / 8))

/-- The main part, for a valid p. -/
theorem main_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two fun p s => Ex CE' p s ∧ isa.eval (.zero .x .x9) s = some false)
      (Exchange.main W.code S.code M.mm) fun _ _ => True := by
  rw [main_eq]
  refine RelCT.seqs_append (by simp [pSetup]) (by simp [r2Steps]) (RelCT.seq (R := Two (Ex X1))
    (two_post (two_map (fun p : ExP => (⟨p.B, p.Z, p.k, p.dp⟩ : DPub)) (fun p s ⟨⟨xb, h⟩, he⟩ =>
      ce_setupP _ s h.1 he) setup_ct) fun p s ⟨⟨xb, h⟩, he⟩ => WP.mono (ce_in _ s h.1 he) fun u ⟨hu, k⟩ =>
        ⟨xb, hu, h.2.1.keep k, h.2.2⟩) ?_)
  refine RelCT.seqs_append (by simp [r2Steps]) (by simp [pow]) (RelCT.seq (R := Two (Ex X2))
    (ex_post ((r2_ct M).mono (fun _ _ h => two_bind (fun p s₁ s₂ ⟨xb₁, ⟨mi₁, hI₁⟩, _⟩ ⟨xb₂, ⟨mi₂, hI₂⟩, _⟩ => by
      have hb := hI₁.1
      have ew := hb.ew
      have := hb.k1
      obtain ⟨hodd, -⟩ := valid_facts hI₁.2.2.2.2.2 hb.k1
      obtain rfl : mi₁ = mi₂ := xvals_minv (show 1 ≤ (p.D xb₁).w by omega) hodd hI₁.2.2.1 hI₂.2.2.1
      exact ⟨_, hI₁.r2pre, hI₂.r2pre⟩) h) fun _ _ h => h) (x1_x2 M)) ?_)
  refine RelCT.seqs_append (by simp [pow]) (by simp) (RelCT.seq (R := Two (Ex X3))
    (ex_post (two_map ExP.pw (fun p s ⟨xb, h⟩ => x2_ps0 p xb s h)
      (pow_ct W M S (loadArr_ct (by decide) (by taint_decide) (by taint_decide))
        (expLoop_ct W M S (by taint_decide)) (by taint_decide) (by taint_decide) (by taint_decide)))
      (x2_x3 W M S)) ?_)
  refine RelCT.seqs_append (by simp [range]) (by simp) (RelCT.seq (R := Two (Ex X6))
    (ex_post (two_map (fun p : ExP => ((p.D []).pub, p.op)) (fun p _ ⟨xb, ⟨mi, hM, hY⟩, hd, _⟩ =>
      ⟨p.D xb, zv p xb, rfl, ⟨mi, hM.inn, hY⟩, List.mem_cons_self .., hd⟩)
      (OutMask.outMask_ct.mono (fun _ _ h => h) fun _ _ _ => trivial)) x3_x6) ?_)
  rw [seqs_one]
  exact two_taint [.x0] (pins_x0B ExP.g fun _ _ ⟨_, h⟩ => h.2.1) (by taint_decide)

/-- `Exchange.code` leaks the same in runs with the same public data. -/
theorem ex_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two (Ex CR)) (Exchange.code W.code S.code M.mm) fun _ _ => True := by
  unfold Exchange.code
  rw [entry_split]
  refine RelCT.seq (R := Two (Ex CE')) (RelCT.block_append (RelCT.seq (two_piece (Ψ := Ex EA') []
      (pins_nil _) (by taint_decide) fun p s ⟨xb, h⟩ => WP.mono (cr_ea p xb s h) fun _ h' => ⟨xb, h', cr_ok h⟩)
    (RelCT.block_append (RelCT.seq (two_piece (Ψ := Ex E1') [.x0, .x2, .x3, .x4, .x5, .x6, .x7, .x8]
      (pins_of entryRegs fun p s ⟨_, h, _⟩ => h.1) (by taint_decide)
      fun p s ⟨xb, h, ho⟩ => WP.mono h.2 fun _ h' => ⟨xb, h'.1, h'.2, ho⟩)
    (ex_post (two_map (fun p : ExP => (⟨p.B, p.Z, p.k, p.dp⟩ : DPub)) (fun p s ⟨_, h, _⟩ => h.dhp) domHead_ct)
      fun p xb s h => WP.mono (e1_ce _ s h.1) fun u ⟨hu, k⟩ => ⟨⟨hu, h.2.1.keep k, h.2.2⟩, k⟩))))) ?_
  exact two_ite (fun p s₁ s₂ ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ => by rw [ce_eval h₁, ce_eval h₂]; rfl)
    (two_taint [] (pins_nil _) (by taint_decide)) (main_ct W M S)

/-- The public data of a state. -/
theorem cr_pub {s₁ s₂ : State} (h₁ : exPre s₁) (h₂ : exPre s₂) (hp : exPub s₁ s₂) : CR (exOf s₁) (exX s₂) s₂ := by
  obtain ⟨hr, hsp, ha, hl⟩ := hp
  simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := hr
  rw [stackArgs_three, stackArgs_three] at ha
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨a0, a1, a2⟩ := ha
  unfold exLeak at hl
  have c₁ := exCtx_of h₁
  have c₂ := exCtx_of h₂
  simp only [List.append_assoc] at hl
  obtain ⟨hd, hl'⟩ := List.append_inj hl (by simp [exDom, Spec.Rsa.bytesAt, r3])
  obtain ⟨hy, -⟩ := List.append_inj hl' (by simp [exY, Spec.Rsa.bytesAt, a0])
  refine ⟨h₂, hsp.symm, a1.symm, by rw [← a2]; rfl, by rw [← r4]; rfl, by rw [← r3]; rfl, r2.symm, ?_, r0.symm,
    r5.symm, by rw [← r6]; rfl, r7.symm, ?_, rfl⟩
  · exact ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hd).symm
  · exact ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hy).symm

/-- `vg_ffdh_exchange` is constant time. -/
theorem ex_constantTime (W : Window) (M : Mont) (S : Selector) :
    ConstantTime isa exContract.pre exContract.pub (Exchange.code W.code S.code M.mm) :=
  RelCT.constantTime ((ex_ct W M S).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ =>
    ⟨exOf s₁, ⟨exX s₁, cr_of s₁ h₁⟩, ⟨exX s₂, cr_pub h₁ h₂ hp⟩, hp.2.1⟩) fun _ _ h => h)

end VG.Proof.Ffdh.AArch64.Exchange
