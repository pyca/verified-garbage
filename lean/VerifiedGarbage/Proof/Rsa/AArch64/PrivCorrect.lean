module
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivArgs
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivImpl
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivPub

import VerifiedGarbage.Proof.Rsa.AArch64.PrivCheckOk
import VerifiedGarbage.Proof.Rsa.AArch64.PrivTail
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivCrt
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# `vg_rsa_private_checked` on AArch64: correctness

The frames' pushes, the CRT's arguments and call (`crtArgs_ok`,
`crt_call`), the check (`check_ok`) and the pops: `code_correct`, for every
implementation of the CRT.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked
open VG.Proof.Rsa (released checkResult)

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

namespace Ctx
variable {t : State} (hc : Ctx L g vv m₀ t) (hL : L.Ok)
include hc hL

omit hL in
/-- A buffer the code only reads is as it was on entry. -/
theorem ro_bytes {R : Region} (ho : R.Disjoint L.OUT) (hs : R.Disjoint L.SC) (hk : L.STK.Disjoint R)
    (hR : R.base.toNat + R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt m₀ R.base R.len :=
  frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [ho, hs, hk.symm]) (by omega_using [hR])

/-- The key, as the CRT reads it. -/
theorem key_bytes :
    Spec.Rsa.bytesAt t.mem L.p L.pl.toNat = Spec.Rsa.bytesAt m₀ L.p L.pl.toNat ∧
    Spec.Rsa.bytesAt t.mem L.q L.ql.toNat = Spec.Rsa.bytesAt m₀ L.q L.ql.toNat ∧
    Spec.Rsa.bytesAt t.mem L.dp L.pl.toNat = Spec.Rsa.bytesAt m₀ L.dp L.pl.toNat ∧
    Spec.Rsa.bytesAt t.mem L.dq L.ql.toNat = Spec.Rsa.bytesAt m₀ L.dq L.ql.toNat ∧
    Spec.Rsa.bytesAt t.mem L.qi L.pl.toNat = Spec.Rsa.bytesAt m₀ L.qi L.pl.toNat := by
  have hdp := hc.ro_bytes hL.odp.symm hL.dpsc hL.kdp hL.bdp
  have hdq := hc.ro_bytes hL.odq.symm hL.dqsc hL.kdq hL.bdq
  have hqi := hc.ro_bytes hL.oqi.symm hL.qisc hL.kqi hL.bqi
  simp only [hL.dpl, hL.dql, hL.qil] at hdp hdq hqi
  exact ⟨hc.ro_bytes hL.op.symm hL.psc hL.kp hL.bp, hc.ro_bytes hL.oq.symm hL.qsc hL.kq hL.bq,
    hdp, hdq, hqi⟩

end Ctx

/-- The CRT's arguments, from the inner frame's entry. -/
theorem crtArgs_ok (hL : L.Ok) (ha : ArgsAt L m₀) {t : State} (hc : Ctx L g vv m₀ t) (hr : Regs L t) :
    WP isa (.block crtArgs) t fun t' => Ctx L g vv m₀ t' ∧ Slots L t'.mem ∧ CrtArgs L t' := by
  rw [crtArgs, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (saveSlots_ok hL hc hr) fun t₁ ⟨hc₁, hs₁, hr₁, h15, _⟩ => ?_
  refine WP.mono (copyArgs_upto hL (t₀ := t₁) 10 (by omega_using []) t₁
    ⟨hc₁, hs₁, hr₁, h15, Frame.refl _ _, fun _ h => absurd h (by omega_using [])⟩) fun t₂ hI => ?_
  exact WP.mono (crtRegs_ok hL ha hI) fun t₃ ⟨hc₃, hs₃, a₃, _⟩ => ⟨hc₃, hs₃, a₃⟩

theorem freed_mem (b : Nat) (s : State) : (freed b s).mem = s.mem := rfl
theorem freed_sp (b : Nat) (s : State) : (freed b s).sp = s.sp + BitVec.ofNat 64 b := rfl
theorem freed_gpr (b : Nat) (s : State) : (freed b s).gpr = s.gpr := rfl
theorem freed_v (b : Nat) (s : State) : (freed b s).v = s.v := rfl
theorem popped_mem (s : State) : (popped .x30 s).mem = s.mem := rfl
theorem popped_sp (s : State) : (popped .x30 s).sp = s.sp + 16 := rfl
theorem popped_v (s : State) : (popped .x30 s).v = s.v := rfl
theorem popped_gpr (s : State) (r : Reg) :
    (popped .x30 s).gpr r = if r = .x30 then s.mem.read s.sp 8 else s.gpr r := by
  show (s.write .x .x30 _).gpr r = _
  rw [RegUpd.gpr_write, BitVec.setWidth_eq]

theorem body_eq (crtName : String) (crt : Prog isa) (pcName : String) (pc : Prog isa) (pdName : String)
    (pd : Prog isa) :
    body crtName crt pcName pc pdName pd =
      .seq (.block crtArgs) (.seq (.call crtName crt) (seqs (check pcName pc pdName pd))) := rfl

/-- `vg_rsa_private_checked`, calling the CRT `v` and its public operation. -/
abbrev privCodeOf (v : CrtImpl) : Prog isa := code v.name v.code v.pcName v.pc v.pdName v.pd

/-- `vg_rsa_private_checked`'s frames and calls, calling the CRT `C`, with
`stage` writing `n`'s values. -/
abbrev codeWith (C : CrtCallee) (v : CrtImpl) (stage : Prog isa) : Prog isa :=
  .frame (.push .x30) (.frame (.alloc frameBytes)
    (seqs ([.block crtArgs, .call C.name C.code] ++ checkWith stage v.pdName v.pd)) (.free frameBytes))
    (.pop .x30)

/-- What `stage` does in place of calling `vg_rsa_public_precompute`. -/
abbrev StageOk (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (stage : Prog isa) : Prop :=
  ∀ t, Ctx L g vv m₀ t → Slots L t.mem → PcArgs L t →
    WP isa stage t fun t' => Ctx L g vv m₀ t' ∧ Slots L t'.mem ∧ Frame (pcWr L) t.mem t'.mem ∧
      PcOut L t.mem t'.mem (t'.gpr .x0)

/-- The frames, the CRT `C` and the check, for a call that may also read `X`
(`chkA` holding of it reading the rest, `R₀`), whatever `stage` writes `n`'s
values, given that the CRT's call states have `C.K`. -/
theorem codeWith_correct (C : CrtCallee) (v : CrtImpl) (stage : Prog isa) {s : State} {R₀ X : List Region}
    (h : chkA.pre (s.withRegions R₀ s.wr)) (hX : s.rd = R₀ ++ X)
    (hst : StageOk (layW s X) s.gpr s.v s.mem stage)
    (hK : ∀ t, Ctx (layW s X) s.gpr s.v s.mem t → CrtArgs (layW s X) t →
      C.K (t.callEntry.withRegions (crtRd (layW s X)) (crtWr (layW s X)))) :
    WP isa (codeWith C v stage) s fun s' => abiPreserved s s' ∧ chkA.post s s' := by
  have hL : (layW s X).Ok := (lay_ok h).withX X
  have hst0 : stackBytes ≤ s.sp.toNat := h.1
  have hnB := hL.nB
  refine WP.frame (by unfold stackBytes at hst0; omega_using [hst0]) ?_
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by
    show frameBytes ≤ (s.sp - 16).toNat
    rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.toNat_sub_ofNat]
    simp only [frameBytes, stackBytes] at hst0 ⊢
    omega_using [hst0]) ?_
  show WP isa (seqs _) (entered s) _
  have ha : ArgsAt (layW s X) s.mem := argsAt_entry s
  refine WP.seq (WP.mono (crtArgs_ok hL ha (entered_ctxW h hX) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    fun t₁ ⟨hc₁, hs₁, a₁⟩ => ?_)
  refine WP.seq (WP.mono (crt_call C hL hc₁ hs₁ a₁ (hK t₁ hc₁ a₁)) fun t₂ ⟨hc₂, hs₂, _, hcrt⟩ => ?_)
  refine WP.mono (checkWith_ok v stage hL ha hst hc₂ hs₂) fun t₃ ⟨hc₃, hax, hout, _⟩ => ?_
  have hsp₃ : (freed frameBytes t₃).sp = (layW s X).B + BitVec.ofNat 64 frameBytes := by
    rw [freed_sp, hc₃.sp]
  refine ⟨⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, ?_⟩
  · rw [popped_gpr]
    split
    · rename_i h; subst h; rw [hsp₃, freed_mem, read8]; exact hc₃.lr
    · rename_i h; rw [freed_gpr]; exact hc₃.cs r hr h
  · rw [popped_sp, hsp₃, BitVec.add_assoc]
    exact lay_top s
  · rw [popped_v, freed_v]; exact hc₃.vs r hr
  · -- The outcome.
    obtain ⟨kp, kq, kdp, kdq, kqi⟩ := hc₁.key_bytes hL
    simp only [CrtOut] at hcrt
    rw [hc₁.n_bytes hL, hc₁.inp_bytes hL, kp, kq, kdp, kdq, kqi] at hcrt
    show Spec.Rsa.writtenOutcome (popped .x30 (freed frameBytes t₃)).mem (s.gpr .x0) (s.gpr .x3).toNat
      (((popped .x30 (freed frameBytes t₃)).gpr .x0).setWidth 32) _
    rw [popped_mem, freed_mem, popped_gpr, freed_gpr, ite_neg' (by decide)]
    exact Proof.Rsa.outcome_eq (Proof.Rsa.bytesAt_length' _ _ _) (Proof.Rsa.bytesAt_length' _ _ _) hcrt hax hout

theorem code_correct (v : CrtImpl) (s : State) (h : chkA.pre s) :
    ∃ t s', Exec isa (privCodeOf v) s t s' ∧ abiPreserved s s' ∧ chkA.post s s' := by
  have hL := lay_ok h
  obtain ⟨t, s', he, hq⟩ := codeWith_correct v.callee v (.call v.pcName v.pc) (R₀ := s.rd) (X := [])
    (by exact h) (List.append_nil _).symm (fun _ hc hs pa => pc_call v ((lay_ok h).withX []) hc hs pa)
    fun _ _ _ => trivial
  exact ⟨t, s', he, hq⟩

end

end VG.Proof.Rsa.AArch64
