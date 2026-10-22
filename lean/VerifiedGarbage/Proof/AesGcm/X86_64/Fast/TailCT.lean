module

import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Tail
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.CT
public import VerifiedGarbage.Impl.AesGcm.X86_64.Fast
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Tail
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Split.CT
meta import VerifiedGarbage.Impl.AesGcm.X86_64.Fast
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# AES-GCM `seal_split`'s path for TLS records: at most 16 bytes left, in two runs

Untrusted: everything here is checked by Lean. `Short.finishP` loads `H'`
and `H'²` from the key context's address, which is public, and then ends as
`Short.finishWith` does (`Short.finRest_rel`): `finishP_rel`. Two runs test
the same public number of bytes left, so `Fast.run` takes `Fast.tail` in
both or `SealSplit.body` in both (`fbody_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Fast

variable {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24}

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Proof.AesGcm.X86_64
open VG.Proof.AesGcm.X86_64.Split (BodyRel FinRel body_ct fixTlen_check fixTlen_oneS)
open VG.Proof.AesGcm.X86_64.Short (KsOk KsRel FinI finRest_rel rel_env_regs rel_next)
open VG.Proof.AesGcm.X86_64.StreamTo (step)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

/-- `finishP ks` in two runs with the same rounds and bytes left, the
prepared key context readable. -/
theorem finishP_rel {ks : Prog isa} (hks : KsOk ks) (hkr : KsRel ks) {Ctx W SP D : Addr} {R r : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hr : r < 2 ^ 64) :
    RelCT isa (fun s₁ s₂ => (FinI Ctx W SP D R r s₁ ∧ Covers [⟨Ctx, 1024⟩] (s₁.rd ++ s₁.wr)) ∧
        (FinI Ctx W SP D R r s₂ ∧ Covers [⟨Ctx, 1024⟩] (s₂.rd ++ s₂.wr)))
      (Short.finishP ks) fun _ _ => True := by
  have wPow : ∀ s, FinI Ctx W SP D R r s ∧ Covers [⟨Ctx, 1024⟩] (s.rd ++ s.wr) →
      WP isa (.block Short.finPowP) s (FinI Ctx W SP D R r) := fun s h =>
    WP.mono (finPowP_run s h.1.env.r13 (in_off h.2 (show 272 + 16 ≤ 1024 by decide) (by exact (by decide : (1024 : Nat) < 2 ^ 64)))
      (in_off h.2 (show 256 + 16 ≤ 1024 by decide) (by exact (by decide : (1024 : Nat) < 2 ^ 64)))) fun _ ⟨_, _, _, _, o⟩ =>
      h.1.keep (fun g hg => o.gpr g (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl <;> decide)) o.rd o.wr (by rw [o.mem]; exact Frame.refl _ _)
  have p := rel_next (rel_env_regs [] (fun _ h => h.1.env) (fun _ h => h.1.env) (fun _ _ _ _ _ hr => by cases hr)
    (c := .block Short.finPowP) ⟨_, by taint_decide⟩) wPow wPow
  unfold Short.finishP
  exact RelCT.seq p (finRest_rel hks hkr hR hr)

theorem lenTest_check :
    ∃ hc, (taint.check (Taint.ofRegs [.r15]) (.block [.mov .rax (.mem (at_ .r15 lenO)), .alu .cmp .rax (imm 17)])
      hc).isSome = true := ⟨_, by taint_decide⟩

/-- `Fast.run`'s code after `prefix`, in two runs. -/
theorem fbody_rel {ks : Prog isa} (hks : KsOk ks) (hkr : KsRel ks) (B : BlkFn (CtxMode.preparedN np hpn)) {fin : Prog isa}
    (hfin : FinRel (CtxMode.preparedN np hpn) fin) :
    BodyRel (CtxMode.preparedN np hpn) (.seq (.block [.mov .rax (.mem (at_ .r15 lenO)), .alu .cmp .rax (imm 17)])
      (.ite .b (Impl.AesGcm.X86_64.Fast.tail ks)
        (.frame (.push [.rax]) (.seq (oneBlocks B.enc) (.seq (.block SealSplit.fixTlen) fin)) (.pop .rax 1)))) := by
  intro Ctx W SP A D R al n L kw kd kM ka sp N
  let G : State → Prop := fun s => OneS (CtxMode.preparedN np hpn) Ctx W SP R A al D n none s ∧
    s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 N
  have hw : ∀ s, G s → WP isa (.block [.mov .rax (.mem (at_ .r15 lenO)), .alu .cmp .rax (imm 17)]) s
      fun t => t.cf = some (decide (n < 17)) ∧ G t := fun s g =>
    WP.mono (lenTest_ok g.1.dD.ok.lt s g.1.env g.1.len) fun t ⟨cf, gg, m, rd, wr⟩ =>
      ⟨cf, g.1.keep (fun r hr => gg r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide)) m rd wr, by rw [m]; exact g.2⟩
  have t := step [.r15] lenTest_check (P := fun s₁ s₂ => G s₁ ∧ G s₂)
    (fun _ _ g r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [g.1.1.env.r15, g.2.1.env.r15])
    (fun _ _ g => g) hw hw
  refine RelCT.seq t (RelCT.ite (fun _ _ h => by
    show _ = _; exact h.1.1.trans h.2.1.symm) ?_ ?_)
  · -- At most 16 bytes left: `tail`.
    refine StreamTo.RelCT.of_imp (n ≤ 16 ∧ (R = 10 ∨ R = 12 ∨ R = 14) ∧ n < 2 ^ 64) (fun _ _ h => by
      have e := h.1.1.1.symm.trans h.2
      simp only [Option.some.injEq, decide_eq_true_eq] at e
      exact ⟨by omega, h.1.1.2.1.rounds.2, h.1.1.2.1.dD.ok.lt⟩) fun ⟨_, hR, hn⟩ => ?_
    unfold Impl.AesGcm.X86_64.Fast.tail
    have fx := step [.r15] fixTlen_check
      (P := fun s₁ s₂ => ((s₁.cf = some (decide (n < 17)) ∧ G s₁) ∧ s₂.cf = some (decide (n < 17)) ∧ G s₂) ∧
        isa.eval .b s₁ = some true)
      (fun _ _ g r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [g.1.1.2.1.env.r15, g.1.2.2.1.env.r15])
      (fun _ _ g => ⟨g.1.1.2, g.1.2.2⟩) (fun _ g => fixTlen_oneS L g.1 g.2) (fun _ g => fixTlen_oneS L g.1 g.2)
    refine RelCT.seq fx ((finishP_rel hks hkr (Ctx := Ctx) (W := W) (SP := SP) (D := D) hR hn).mono
      (fun _ _ g => ⟨⟨⟨g.1.env, g.1.rounds.1, g.1.dat, g.1.len⟩, g.1.ext.cov⟩,
        ⟨⟨g.2.env, g.2.rounds.1, g.2.dat, g.2.len⟩, g.2.ext.cov⟩⟩) fun _ _ g => g)
  · -- More: `body`.
    exact (body_ct L kw kd kM ka sp B hfin (N := N)).mono (fun _ _ g => ⟨g.1.1.2, g.1.2.2⟩) fun _ _ g => g

end VG.Proof.AesGcm.X86_64.Fast
