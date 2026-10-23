module

import VerifiedGarbage.Proof.Ffdh.X86_64.DerivePublic.Correct
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.StagesCT
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.CT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.TailCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Scalar
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Math
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.PublicOutputCT
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Ffdh.X86_64.DerivePublic.Correct
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.StagesCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.CT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.TailCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Scalar
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Math
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.PublicOutputCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.DerivePublic.Start

/-! # FFDH public-value derivation on x86-64: constant time

Private-key validation's stages, with y's writability carried beside them
(`two_out`), then the power's and key generation's output timing proofs. -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.DerivePublic

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.CheckPrivate (KpP Base Inner CE BeforeX CScalar CBranch)

private theorem pins_nil {α : Type} (Φ : α → State → Prop) : Pins Φ [] :=
  fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

/-- A stage that keeps y writable, as every stage does. -/
theorem two_out {Φ Ψ : KpP → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two Φ) c fun _ _ => True) (hw : ∀ p s, Φ p s → WP isa c s (Ψ p)) :
    RelCT isa (Two fun p s => Φ p s ∧ YOut p s) c (Two fun p s => Ψ p s ∧ YOut p s) :=
  two_post (two_map id (fun _ _ h => h.1) hct) fun p s h => by
    obtain ⟨tr, t, he, hq⟩ := hw p s h.1
    exact ⟨tr, t, he, hq, h.2.of_wr (Exec.rdwr he).2⟩

def DR (p : KpP) (s : State) : Prop := dvPre s ∧ dvOf s = p

def D0 (p : KpP) (s : State) : Prop := ∃ xb, Pre0 p xb s ∧ s.gpr .rdi = p.B

abbrev D1 (p : KpP) (s : State) : Prop := CheckPrivate.E1 p s ∧ YOut p s

private def loads : List Instr :=
  [.mov .rax (.mem (VG.Impl.Rsa.X86_64.Crt.stk 2)), .mov .r10 (.mem (VG.Impl.Rsa.X86_64.Crt.stk 1))]

private def entryTail : List Instr := save .rax ++
  [.store (VG.Impl.Rsa.X86_64.Crt.ws .rax sDom) .rdx,
    .store (VG.Impl.Rsa.X86_64.Crt.ws .rax sDomLen) .rcx, .store (VG.Impl.Rsa.X86_64.Crt.ws .rax sK) .r8,
    .store (VG.Impl.Rsa.X86_64.Crt.ws .rax sY) .rdi, .store (VG.Impl.Rsa.X86_64.Crt.ws .rax sX) .r9,
    .store (VG.Impl.Rsa.X86_64.Crt.ws .rax sXl) .r10, .mov .rdi (.reg .rax)]

private def EL (p : KpP) (s : State) : Prop := s.gpr .rax = p.B ∧ WP isa (.block entryTail) s (D0 p)

private theorem loads_ok (s : State) (c : DvCtx s) : WP isa (.block loads) s
    fun t => t.gpr .rax = stackArg s 1 := by
  have h1 : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) 16) 8 := c.ha 1 (by decide)
  have h0 : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) 8) 8 := c.ha 0 (by decide)
  unfold loads VG.Impl.Rsa.X86_64.Crt.stk
  xrun [State.ea, hdrOff, h1, h0]
  rfl

theorem entry_ct : RelCT isa (Two DR) (.block VG.Impl.Ffdh.X86_64.Domain.DerivePublic.entry) (Two D0) := by
  change RelCT isa (Two DR) (.block (loads ++ entryTail)) (Two D0)
  refine RelCT.block_append (RelCT.seq (R := Two EL)
    (two_piece [.rsp] (pins_of (fun p _ => p.sp) fun p s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact congrArg KpP.sp h.2) (by taint_decide) ?_) ?_)
  · intro p s h
    have c := dvCtx_of h.1
    have he : WP isa (.block VG.Impl.Ffdh.X86_64.Domain.DerivePublic.entry) s (D0 p) :=
      WP.mono (entry_pre0 c) fun t ⟨hb, hd, _⟩ => by rw [h.2] at hb hd; exact ⟨dvX s, hb, hd⟩
    change WP isa (.block (loads ++ entryTail)) s (D0 p) at he
    refine WP.and ?_ (WP.block_append_iff.mp he)
    exact WP.mono (loads_ok s c) fun t hh => by rw [← h.2]; exact hh
  exact two_piece [.rax] (pins_of (fun p _ => p.B) fun _ _ h _ hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.1) (by taint_decide) fun _ _ h => h.2

private def zeroLoads : List Instr :=
  [.mov .rsi (.mem (hdr sY)), .mov .rcx (.mem (hdr sK)), .mov32 .rax (.imm 0)]

private def zeroVal (p : KpP) : Reg → BitVec 64
  | .rsi => p.yp | .rcx => BitVec.ofNat 64 p.k | _ => 0

private theorem zero_regs (p : KpP) (s : State) (h : D0 p s) :
    WP isa (.block zeroLoads) s fun t => ∀ r ∈ [.rsi, .rcx], t.gpr r = zeroVal p r := by
  obtain ⟨xb, hb, hd⟩ := h
  have hZ := hb.hZ
  refine WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t => t.gpr .rsi = p.yp ∧
      t.gpr .rcx = BitVec.ofNat 64 p.k) (by
    unfold zeroLoads
    xrun [State.ea, hdr, hd, hdrOff,
      hb.scr.ld (d := 8 * sY) (by change 160 ≤ p.Z; omega),
      hb.scr.ld (d := 8 * sK) (by change 152 ≤ p.Z; omega),
      hb.hdr (sY, p.yp) (by simp [KpP.headers]),
      hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [KpP.headers])]) rfl)
    fun t ⟨⟨hy, hk⟩, _⟩ r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hy
  · exact hk

private theorem zero_d1 (p : KpP) (s : State) (h : D0 p s) :
    WP isa (VG.Impl.Rsa.X86_64.Keys.zeroOut sY sK) s (D1 p) := by
  obtain ⟨xb, hb, hd⟩ := h
  exact WP.mono (zero_base hb hd) fun _ ⟨hb', hy, hd', _⟩ => ⟨⟨xb, hb', hd'⟩, hy⟩

theorem zero_ct : RelCT isa (Two D0) (VG.Impl.Rsa.X86_64.Keys.zeroOut sY sK) (Two D1) :=
  pin_ct [.rdi] [.rsi, .rcx] zeroVal (pins_rdiB KpP.B fun _ _ h => by obtain ⟨_, _, hd⟩ := h; exact hd)
    (by taint_decide) zero_regs (by taint_decide) zero_d1

private theorem scalar_stage (p : KpP) (s : State) (h : Inner p s) :
    WP isa (seqs VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange) s (CScalar p) := by
  obtain ⟨xb, mi, hw, hd, hm⟩ := h
  exact WP.mono (CheckPrivate.scalar_ok hw hd (valid_facts hm hw.base.k1).1)
    fun t ⟨⟨hw', hd', ha⟩, _⟩ => ⟨⟨xb, mi, hw', hd', hm⟩, ha⟩

private theorem test_stage (p : KpP) (s : State) (h : CScalar p s) :
    WP isa (.block [.alu .test .rax (.reg .rax)]) s (CBranch p) := by
  obtain ⟨⟨xb, mi, hw, hd, hm⟩, ha⟩ := h
  exact WP.mono (test_bit_ok ha) fun t ⟨hz, hmem, k⟩ =>
    ⟨⟨xb, mi, hw.keep hmem k, (k.gpr (by decide)).trans hd, hm⟩, hz⟩

private theorem branch_eval {p : KpP} {s : State} (h : CBranch p s) :
    isa.eval .e s = some (!decide (p.sv = true)) := by simp [eval, h.2]

private theorem r2_stage (M : Mont) (R : R2Impl M) (p : KpP) (s : State) (h : Inner p s) :
    WP isa (.seq (.block r2Head) R.code) s (CheckPrivate.C2 p) := by
  obtain ⟨xb, mi, hw, hd, hm⟩ := h
  exact WP.mono (CheckPrivate.work_ready M R hw hd hm) fun _ ⟨hr, _⟩ => ⟨xb, hr⟩

private theorem pow_stage (M : Mont) (E : CrtExpL M) (p : KpP) (s : State) (h : CheckPrivate.C2 p s) :
    WP isa (seqs (pow M.mm E.code sG sK sX sXl)) s (CheckPrivate.C3 p) := by
  obtain ⟨xb, hr⟩ := h
  exact WP.mono (CheckPrivate.ready_value M E hr) fun _ ⟨hv, _⟩ => ⟨xb, hv⟩

private theorem public_rdi (p : KpP) (s : State) (h : GenerateKey.KBV p s) :
    WP isa (seqs GenerateKey.publicOutput) s fun t => t.gpr .rdi = p.B := by
  obtain ⟨xb, hv, ho⟩ := h
  exact WP.mono (public_ok hv ho) fun _ ⟨_, _, hd, _⟩ => hd

theorem tail_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sX sXl) :
    RelCT isa (Two fun p s => Inner p s ∧ YOut p s)
      (seqs (VG.Impl.Ffdh.X86_64.Domain.DerivePublic.tail M.mm E.code (.seq (.block r2Head) R.code)))
      fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Domain.DerivePublic.tail
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine seqs_cons_ct (by simp [pow]) (RelCT.seq (R := Two fun p s => CheckPrivate.C2 p s ∧ YOut p s)
    (two_out ((CheckPrivate.r2_ct M R).mono (fun _ _ h => h) (fun _ _ _ => trivial)) (r2_stage M R)) ?_)
  refine RelCT.seqs_append (a := pow M.mm E.code sG sK sX sXl)
    (b := GenerateKey.publicOutput ++ [.block VG.Impl.Ffdh.X86_64.Domain.DerivePublic.status])
    (by simp [pow]) (by simp) (RelCT.seq (R := Two fun p s => CheckPrivate.C3 p s ∧ YOut p s)
      (two_out ((CheckPrivate.generator_power_ct M E hE).mono (fun _ _ h => h) (fun _ _ _ => trivial))
        (pow_stage M E)) ?_)
  refine RelCT.seqs_append (a := GenerateKey.publicOutput) (by simp [GenerateKey.publicOutput]) (by simp)
    (RelCT.seq (R := Two fun (p : KpP) s => s.gpr .rdi = p.B)
      (two_map id (fun _ _ h => by obtain ⟨⟨xb, hv⟩, ho⟩ := h; exact ⟨xb, hv, ho⟩)
        (two_post GenerateKey.public_ct public_rdi)) ?_)
  exact two_taint [] (pins_nil _) (by taint_decide)

theorem main_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sX sXl) :
    RelCT isa (Two fun p s => (CE p s ∧ YOut p s) ∧ isa.eval .ne s = some false)
      (VG.Impl.Ffdh.X86_64.Domain.DerivePublic.main M.mm E.code (.seq (.block r2Head) R.code)) fun _ _ => True := by
  rw [main_eq]
  refine RelCT.seqs_append (by simp [pSetup, VG.Impl.Rsa.X86_64.Crt.loadArr]) (by simp)
    (RelCT.seq (R := Two fun p s => Inner p s ∧ YOut p s) ?_ ?_)
  · refine RelCT.seqs_append (by simp [pSetup]) (by simp [VG.Impl.Rsa.X86_64.Crt.loadArr])
      (RelCT.seq (R := Two fun p s => BeforeX p s ∧ YOut p s)
        (two_map id (fun _ _ h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩)
          (two_out (two_map CheckPrivate.KpP.d CheckPrivate.ce_setup setup_ct) CheckPrivate.ce_beforeX)) ?_)
    exact two_out (two_map CheckPrivate.KpP.xlPub CheckPrivate.beforeX_load
      (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) CheckPrivate.beforeX_inner
  refine RelCT.seqs_append (a := VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange)
    (by simp [VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange, isNonzero, geArr, cmpArr])
    (by simp) (RelCT.seq (R := Two fun p s => CScalar p s ∧ YOut p s)
      (two_out CheckPrivate.scalar_ct scalar_stage) ?_)
  simp only [seqs]
  refine RelCT.seq (R := Two fun p s => CBranch p s ∧ YOut p s)
    (two_out (two_taint [] (pins_nil _) (by taint_decide)) test_stage) ?_
  exact two_ite (fun _ _ _ h₁ h₂ => by rw [branch_eval h₁.1, branch_eval h₂.1])
    (two_taint [.rdi] (pins_rdiB (fun p => off p.B (inner p.w)) fun _ _ h => by
      obtain ⟨_, _, _, hd, _⟩ := h.1.1.1; exact hd) (by taint_decide))
    (two_map id (fun _ _ h => ⟨h.1.1.1, h.1.2⟩) (tail_ct M E R hE))

theorem body_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sX sXl) :
    RelCT isa (Two DR) (VG.Impl.Ffdh.X86_64.Domain.DerivePublic.body M.mm E.code (.seq (.block r2Head) R.code))
      fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Domain.DerivePublic.body
  refine RelCT.seq entry_ct (RelCT.seq zero_ct (RelCT.seq (R := Two fun p s => CE p s ∧ YOut p s)
    (two_out (two_map CheckPrivate.KpP.d CheckPrivate.e1_dhp domHead_ct) CheckPrivate.e1_ce) ?_))
  exact two_ite (fun _ _ _ h₁ h₂ => by rw [CheckPrivate.ce_eval h₁.1, CheckPrivate.ce_eval h₂.1])
    (two_taint [] (pins_nil _) (by taint_decide)) (main_ct M E R hE)

theorem code_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sX sXl) :
    RelCT isa (Two DR) (VG.Impl.Ffdh.X86_64.Domain.DerivePublic.code M.mm E.code (.seq (.block r2Head) R.code))
      fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Domain.DerivePublic.code
  refine RelCT.seq (R := Two fun (p : KpP) s => s.gpr .rdi = p.B)
    (two_post (body_ct M E R hE) fun p s h =>
      WP.mono (body_ok M E R h.1) fun t ⟨_, hd, _⟩ => by rw [h.2] at hd; exact hd)
    (two_taint [.rdi] (pins_rdiB KpP.B fun _ _ h => h) (by taint_decide))

theorem dv_constantTime (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sX sXl) :
    ConstantTime isa dvContract.pre dvContract.pub
      (VG.Impl.Ffdh.X86_64.Domain.DerivePublic.code M.mm E.code (.seq (.block r2Head) R.code)) := by
  refine RelCT.constantTime ((code_ct M E R hE).mono
    (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨dvOf s₁, ⟨h₁, rfl⟩, h₂, ?_⟩) fun _ _ h => h)
  obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, a0, a1, a2⟩ := hp
  unfold dvLeak at hl
  obtain ⟨hd, hstatus⟩ := List.append_inj hl (by simp [dvDom, Spec.Rsa.bytesAt, r3])
  have hdom := ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hd)
  have hs := (List.cons.inj hstatus).1
  have hfalse : ((dvOf s₁).sv = false) ↔ ((dvOf s₂).sv = false) := by
    change (Spec.Ffdh.privateValid (dvA s₁) (Spec.Rsa.os2ip (dvX s₁)) = false) ↔
      (Spec.Ffdh.privateValid (dvA s₂) (Spec.Rsa.os2ip (dvX s₂)) = false)
    rw [← VG.Proof.Ffdh.keyStatus_scalar _ _, ← VG.Proof.Ffdh.keyStatus_scalar _ _, hs]
  have hsv : (dvOf s₁).sv = (dvOf s₂).sv := by
    cases h₁ : (dvOf s₁).sv <;> cases h₂ : (dvOf s₂).sv <;> simp_all
  simp only [dvOf, r0, r2, r3, r4, r5, a0, a1, a2, hsp, hdom]
  congr 1
  simpa only [dvOf, r0, r1, r2, r3, r4, r5, a0, a1, a2, hsp, hdom] using hsv.symm

end VG.Proof.Ffdh.X86_64.DerivePublic
