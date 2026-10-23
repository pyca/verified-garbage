module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Derive.Correct
import VerifiedGarbage.Proof.Ffdh.AArch64.OutMaskCT
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.CT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExpCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Derive.Correct
meta import VerifiedGarbage.Proof.Ffdh.AArch64.OutMaskCT
meta import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.CT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExpCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ffdh.AArch64.ScalarRangeCT

/-!
# `vg_ffdh_derive_public` on AArch64: constant time

Runs with the same public data (`DvP`: all but x's octets, and whether x is
in range) leak the same (`dv_constantTime`): x's range checks run over all
the words (`ScalarRange.scalarRange_ct`), the exponentiation is RSA's,
constant time in the exponent, y is stored masked by its range, without a
branch (`OutMask.outMask_ct`), and the only branch on x is on its range,
which the status gives.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Derive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Ffdh.AArch64.CheckDomain (pins_nil)
open VG.Spec.Ffdh

/-- A stage of some scalar. -/
def Ex (Φ : DvP → List Byte → State → Prop) (p : DvP) (t : State) : Prop := ∃ xb, Φ p xb t

theorem ex_post {Φ Ψ : DvP → List Byte → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two (Ex Φ)) c fun _ _ => True)
    (hw : ∀ p xb s, Φ p xb s → WP isa c s fun u => Ψ p xb u ∧ KX s u) : RelCT isa (Two (Ex Φ)) c (Two (Ex Ψ)) :=
  two_post hct fun p s ⟨xb, h⟩ => WP.mono (hw p xb s h) fun _ h => ⟨xb, h.1⟩

theorem ex_post' {Φ Ψ : DvP → List Byte → State → Prop} {c : Prog isa} {P : DvP → State → Prop}
    (hct : RelCT isa (Two fun p s => Ex Φ p s ∧ P p s) c fun _ _ => True)
    (hw : ∀ p xb s, Φ p xb s → P p s → WP isa c s fun u => Ψ p xb u ∧ KX s u) :
    RelCT isa (Two fun p s => Ex Φ p s ∧ P p s) c (Two (Ex Ψ)) :=
  two_post hct fun p s ⟨⟨xb, h⟩, hp⟩ => WP.mono (hw p xb s h hp) fun _ h => ⟨xb, h.1⟩

/-- After the entry. -/
def E1' (p : DvP) (xb : List Byte) (t : State) : Prop := E1 (p.D xb) t ∧ Dst p t ∧ Ok p xb

/-- After `domHead`. -/
def CE' (p : DvP) (xb : List Byte) (t : State) : Prop := CE (p.D xb) t ∧ Dst p t ∧ Ok p xb

/-- The public part of the run's data. -/
abbrev DvP.pub (p : DvP) : FD := (p.D []).pub

/-- The inner workspace's base. -/
abbrev DvP.g (p : DvP) : Addr := off p.B (inner ((p.k + 7) / 8))

/-- `zeroOut sOut sK`, to y. -/
theorem zo_ct : RelCT isa (Two V3o) (Keys.zeroOut VG.Impl.Ffdh.AArch64.Domain.sOut sK) (Two V3o) := by
  have post : ∀ p t, V3o p t → WP isa (Keys.zeroOut VG.Impl.Ffdh.AArch64.Domain.sOut sK) t (V3o p) :=
    fun p t h => WP.mono (o_z p t h) fun _ h => h.1.2
  unfold Keys.zeroOut
  refine RelCT.seq (R := Two fun p t => (t.gpr .x1 = p.op ∧ t.gpr .x2 = BitVec.ofNat 64 p.k) ∧
      WP isa (countLoop .x2 [.strb .x3 .x1 0, .addImm .x .x1 .x1 1]) t (V3o p))
    (two_piece [.x0] (pins_x0B DvP.B fun _ _ h => h.2.1) (by taint_decide) fun p t h => ?_) ?_
  · obtain ⟨hs, h0, hZ, -, -, hO, hK, -⟩ := id h
    have hn := hs.nowrap
    have hw := post p t h
    unfold Keys.zeroOut at hw
    exact wp_and (zoBlk_ok h0 (by decide) hO hK fun i hi => hs.ld (by omega)) (WP.seq_iff.mp hw)
  · exact two_post (two_taint [.x1, .x2] (pins_of (fun (p : DvP) r => if r = .x1 then p.op else
      BitVec.ofNat 64 p.k) fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1.1
        · exact h.1.2) (by taint_decide)) fun p t h => h.2

/-- x out of range: zeros to y, and 2 returned. -/
theorem fail_ct :
    RelCT isa (Two fun p s => Ex V3 p s ∧ isa.eval (.zero .x .x9) s = some true) DerivePublic.fail
      fun _ _ => True := by
  unfold DerivePublic.fail
  simp only [seqs]
  refine RelCT.seq (R := Two V3o) (two_piece [.x0] (pins_x0B DvP.g fun (p : DvP) s (h : Ex V3 p s ∧ _) => by
      obtain ⟨⟨_, ⟨_, hI, _⟩, _⟩, _⟩ := h; exact hI.2.1.x0) (by taint_decide)
    fun p s ⟨⟨xb, h⟩, _⟩ => WP.mono (v3_o p xb s h) fun _ h => h.1) ?_
  exact RelCT.seq zo_ct (two_taint [] (pins_nil _) (by taint_decide))

/-- x in range: y, masked by its range, and the status. -/
theorem tail_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two fun p s => Ex V3 p s ∧ isa.eval (.zero .x .x9) s = some false)
      (seqs (DerivePublic.tail W.code S.code M.mm)) fun _ _ => True := by
  rw [tail_eq]
  refine RelCT.seqs_append (by simp [r2Steps]) (by simp) (RelCT.seq (R := Two (Ex T1))
    (ex_post' ((r2_ct M).mono (fun _ _ h => two_bind (fun p s₁ s₂ ⟨⟨xb₁, ⟨mi₁, hI₁, _⟩, _⟩, _⟩
        ⟨⟨xb₂, ⟨mi₂, hI₂, _⟩, _⟩, _⟩ => by
      have hb := hI₁.1
      have ew := hb.ew
      have := hb.k1
      obtain ⟨hodd, -⟩ := valid_facts hI₁.2.2.2.2.2 hb.k1
      obtain rfl : mi₁ = mi₂ := xvals_minv (show 1 ≤ (p.D xb₁).w by omega) hodd hI₁.2.2.1 hI₂.2.2.1
      exact ⟨_, hI₁.r2pre, hI₂.r2pre⟩) h) fun _ _ h => h)
      fun p xb s h he => t0_t1 M p xb s (v3_t0 h he)) ?_)
  refine RelCT.seqs_append (by simp [pow]) (by simp) (RelCT.seq (R := Two (Ex T2))
    (ex_post (two_map DvP.pwG (fun p s ⟨xb, h⟩ => t1_pre p xb s h)
      (pow_ct W M S (loadArr_ct (by decide) (by taint_decide) (by taint_decide))
        (expLoop_ct W M S (by taint_decide)) (by taint_decide) (by taint_decide) (by taint_decide)))
      (t1_t2 W M S)) ?_)
  refine RelCT.seqs_append (by simp [range]) (by simp) (RelCT.seq (R := Two (Ex T3))
    (ex_post (two_map (fun p : DvP => (p.pub, p.op)) (fun p _ ⟨xb, h⟩ => ⟨p.D xb, yv p xb, rfl, t2_o3 h⟩)
      (OutMask.outMask_ct.mono (fun _ _ h => h) fun _ _ _ => trivial)) t2_t3) ?_)
  rw [seqs_one]
  exact two_taint [.x0] (pins_x0B DvP.g fun _ _ ⟨_, h⟩ => h.1.2.1) (by taint_decide)

/-- The main part, for a valid p. -/
theorem main_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two fun p s => Ex CE' p s ∧ isa.eval (.zero .x .x9) s = some false)
      (DerivePublic.main W.code S.code M.mm) fun _ _ => True := by
  rw [main_eq]
  refine RelCT.seqs_append (by simp [pSetup]) (by simp [Crt.loadArr]) (RelCT.seq (R := Two (Ex V1))
    (two_post (two_map (fun p : DvP => (⟨p.B, p.Z, p.k, p.dp⟩ : DPub)) (fun p s ⟨⟨xb, h⟩, he⟩ =>
      ce_setupP _ s h.1 he) setup_ct) fun p s ⟨⟨xb, h⟩, he⟩ => WP.mono (ce_in _ s h.1 he) fun u ⟨hu, k⟩ =>
        ⟨xb, hu, OutMask.Dst.keep h.2.1 k, h.2.2⟩) ?_)
  refine RelCT.seqs_append (by simp [Crt.loadArr]) (by simp [CheckPrivate.scalarRange]) (RelCT.seq
    (R := Two (Ex V2)) (ex_post (two_map (fun p : DvP => (⟨⟨p.B, p.Z, inner ((p.k + 7) / 8), (p.k + 7) / 8,
      (p.k + 7) / 8⟩, p.xp, p.xl⟩ : BPub)) (fun p s ⟨xb, h⟩ => v1_lpre p xb s h)
      (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) v1_v2) ?_)
  refine RelCT.seqs_append (by simp [CheckPrivate.scalarRange]) (by simp) (RelCT.seq (R := Two (Ex V3))
    (ex_post (two_map DvP.pub (fun p _ ⟨xb, ⟨mi, hI, hx⟩, _⟩ => ⟨p.D xb, X xb, rfl, mi, hI, hx⟩)
      (ScalarRange.scalarRange_ct.mono (fun _ _ h => h) fun _ _ _ => trivial)) v2_v3) ?_)
  rw [seqs_one]
  exact two_ite (fun p s₁ s₂ ⟨_, h₁⟩ ⟨_, h₂⟩ => by rw [v3_eval h₁, v3_eval h₂]) fail_ct (tail_ct W M S)

/-- `DerivePublic.code` leaks the same in runs with the same public data. -/
theorem dv_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two (Ex CR)) (DerivePublic.code W.code S.code M.mm) fun _ _ => True := by
  unfold DerivePublic.code
  refine RelCT.seq (R := Two (Ex CE')) (RelCT.block_append (RelCT.seq (two_piece (Ψ := Ex E1')
      [.x0, .x2, .x3, .x4, .x5, .x6, .x7] (pins_of entryRegs fun p s ⟨xb, h⟩ => cr_regs p xb s h) (by taint_decide)
      fun p s ⟨xb, h⟩ => WP.mono (cr_e1 p xb s h) fun _ h' => ⟨xb, h'.1.1, h'.1.2, cr_ok h⟩)
    (ex_post (two_map (fun p : DvP => (⟨p.B, p.Z, p.k, p.dp⟩ : DPub)) (fun p s ⟨_, h, _⟩ => h.dhp) domHead_ct)
      fun p xb s h => WP.mono (e1_ce _ s h.1) fun u ⟨hu, k⟩ => ⟨⟨hu, OutMask.Dst.keep h.2.1 k, h.2.2⟩, k⟩))) ?_
  exact two_ite (fun p s₁ s₂ ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ => by rw [ce_eval h₁, ce_eval h₂]; rfl)
    (two_taint [] (pins_nil _) (by taint_decide)) (main_ct W M S)

/-- The public data of the second run. -/
theorem cr_pub {s₁ s₂ : State} (h₂ : dvPre s₂) (hp : dvPub s₁ s₂) : CR (dvOf s₁) (dvX s₂) s₂ := by
  obtain ⟨hr, hsp, ha, hl⟩ := hp
  simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := hr
  rw [stackArgs_one, stackArgs_one] at ha
  simp only [List.cons.injEq, and_true] at ha
  unfold dvLeak at hl
  obtain ⟨hd, hs⟩ := List.append_inj hl (by simp [dvDom, Spec.Rsa.bytesAt, r3])
  have hd' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hd
  simp only [List.cons.injEq, and_true] at hs
  refine ⟨h₂, hsp.symm, r7.symm, by rw [← ha]; rfl, by rw [← r4]; rfl, by rw [← r3]; rfl, r2.symm, hd'.symm,
    r0.symm, r5.symm, by rw [← r6]; rfl, rfl, ?_⟩
  -- Whether x is in range, from the statuses.
  show privateValid (domainOf (s₁.gpr .x4).toNat (dvDom s₁)) (Spec.Rsa.os2ip (dvX s₁)) =
    privateValid (domainOf (s₁.gpr .x4).toNat (dvDom s₁)) (Spec.Rsa.os2ip (dvX s₂))
  simp only [dvA] at hs
  rw [r4, hd'] at hs ⊢
  unfold keyStatus at hs
  generalize privateValid _ (Spec.Rsa.os2ip (dvX s₁)) = b₁ at hs ⊢
  generalize privateValid _ (Spec.Rsa.os2ip (dvX s₂)) = b₂ at hs ⊢
  cases b₁ <;> cases b₂ <;> simp at hs ⊢ <;> split at hs <;> simp at hs

/-- `vg_ffdh_derive_public` is constant time. -/
theorem dv_constantTime (W : Window) (M : Mont) (S : Selector) :
    ConstantTime isa dvContract.pre dvContract.pub (DerivePublic.code W.code S.code M.mm) :=
  RelCT.constantTime ((dv_ct W M S).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ =>
    ⟨dvOf s₁, ⟨dvX s₁, cr_of s₁ h₁⟩, ⟨dvX s₂, cr_pub h₂ hp⟩, hp.2.1⟩) fun _ _ h => h)

end VG.Proof.Ffdh.AArch64.Derive
