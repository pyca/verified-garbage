module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTAbsorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTAbsorb
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
meta import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Impl.AesGcm.RISCV64

/-!
# AES-GCM on RISCV64: `textAbsorb` is constant time

Untrusted: everything here is checked by Lean. The invariant fixes the
context, the state, `W`, the stack pointer, the data's address and length
and the lengths of the additional data and of the text so far, all of which
the environment holds in registers (`TA`); `flush` and `absorb` are constant
time by `flush_ct` and `absorb_ct`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Gcm (blockAt)

/-- What `textAbsorb` needs: `len` (`N`) bytes at `data` (`D`), after
`aad_len` (`A`) bytes of additional data and `text_len` (`T`) of text. -/
def TA (c st w sp D : Addr) (N A T : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s9 = D ∧ V .s8 = N ∧ V .s10 = A ∧
    V .s11 = T ∧ Env V sp s ∧ DataOk st w s D N.toNat

section
variable {c st w sp : Addr} (L : Lay c st w)
include L

theorem textAbsorb_ct {D : Addr} {N A T : BitVec 64} : CT (TA c st w sp D N A T) textAbsorb := by
  refine CT.ite (decide (N.toNat = 0)) (fun s ⟨_, _, _, _, _, h19, _, _, he, _⟩ =>
    eval_zero (by rw [he.ofNat (r := .s8) (by decide), h19]) N.isLt) (fun _ => CT.skip) fun _ => ?_
  -- the additional data padded, before the first text
  refine CT.seq (J := TA c st w sp D N A T) ?_ (fun s ⟨V, h29, h30, h31, h20, h19, h22, h23, he, hd⟩ => ?_) ?_
  · refine CT.ite (decide (T.toNat = 0)) (fun s ⟨_, _, _, _, _, _, _, h23, he, _⟩ =>
      eval_zero (by rw [he.ofNat (r := .s11) (by decide), h23]) T.isLt) (fun _ => ?_) (fun _ => CT.skip)
    refine CT.seq (J := fun s => EnvC c st w sp s ∧ s.gpr .s6 = BitVec.ofNat 64 (A.toNat % 16)) ?_
      (fun s ⟨V, h29, h30, h31, _, _, h22, _, he, _⟩ => ?_) (flush_ct L (.inr rfl) (Nat.mod_lt _ (by decide)))
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s10])
          (.block [.logicImm .and .s6 .s10 15]) h).isSome = true := ⟨_, by taint_decide⟩
      refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, a22, _, e₁, _⟩ ⟨_, _, _, _, _, _, b22, _, e₂, _⟩ =>
        ⟨e₁.sp.trans e₂.sp.symm, fun r hr => ?_⟩) hc
      simp only [List.mem_singleton] at hr; subst hr
      rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a22, b22]
    · have h22' := he.fr .s10 (by decide)
      have hand := and15 (V .s10)
      have h₃ : WP isa (.block [.logicImm .and .s6 .s10 15]) s fun s₃ =>
          s₃.gpr .s6 = BitVec.ofNat 64 ((V .s10).toNat % 16) ∧
            (∀ r, r ≠ .t0 → r ≠ .s6 → s₃.gpr r = s.gpr r) ∧ Keeps s s₃ := by
        crun [Int.reduceNatCast', h22', hand]
        exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl⟩⟩
      refine WP.mono h₃ fun s₃ ⟨h26, hg, hk⟩ => ⟨⟨V, h29, h30, h31, he.keep (fun r hr => hg r
        (by revert r; decide) (by revert r; decide)) hk.sp hk.rd hk.wr⟩, by rw [h26, h22]⟩
  · refine WP.ite (decide (T.toNat = 0)) (eval_zero (by rw [he.ofNat (r := .s11) (by decide), h23]) T.isLt)
      (fun _ => ?_) (fun _ => WP.block_nil ⟨V, h29, h30, h31, h20, h19, h22, h23, he, hd⟩)
    have h22' := he.fr .s10 (by decide)
    have hand := and15 (V .s10)
    have h₃ : WP isa (.block [.logicImm .and .s6 .s10 15]) s fun s₃ =>
        s₃.gpr .s6 = BitVec.ofNat 64 ((V .s10).toNat % 16) ∧
          (∀ r, r ≠ .t0 → r ≠ .s6 → s₃.gpr r = s.gpr r) ∧ Keeps s s₃ := by
      crun [Int.reduceNatCast', h22', hand]
      exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl⟩⟩
    refine WP.seq (WP.mono h₃ fun s₃ ⟨h26, hg, hk⟩ => ?_)
    have he₃ := he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide)) hk.sp hk.rd hk.wr
    refine WP.mono (WP.with_rdwr (flush_ok (L.v h29 h30 h31) (yo := 16) (.inr rfl)
      (x := List.replicate ((V .s10).toNat % 16) 0) ⟨he₃, rfl⟩ (by simp [h26])))
      fun s₄ ⟨fl, rd, wr, _⟩ => ⟨V, h29, h30, h31, h20, h19, h22, h23, fl.env,
        hd.of_eq (rd.trans hk.rd) (wr.trans hk.wr)⟩
  -- the arguments of `absorb`
  refine CT.seq (J := AbsI c st w sp 16 D N.toNat (T.toNat % 16)) ?_
    (fun s ⟨V, h29, h30, h31, h20, h19, h22, h23, he, hd⟩ => ?_) (absorb_ct L (.inr rfl) (Nat.mod_lt _ (by decide)))
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s8, .s9, .s11])
        (.block textArgs) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, a20, a19, _, a23, e₁, _⟩ ⟨_, _, _, _, b20, b19, _, b23, e₂, _⟩ =>
      ⟨e₁.sp.trans e₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a19, b19]
    · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a20, b20]
    · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a23, b23]
  · refine WP.mono textArgs_ok fun s₅ ⟨h24, h25, h26, hg, hk⟩ => ?_
    have he₅ := he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide)) hk.sp hk.rd hk.wr
    refine ⟨V, blockAt s₅.mem (V .s2 + BitVec.ofNat 64 240), List.replicate (T.toNat % 16) 0, h29, h30, h31,
      by simp, he₅, ?_, ?_, ?_, ?_, rfl⟩
    · rw [h24, he.fr _ (by decide), h20]
    · rw [h25, he.fr _ (by decide), h19, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [h26, he.fr _ (by decide), h23]; simp
    · rw [h30, h31]; exact hd.of_eq hk.rd hk.wr

end

end VG.Proof.AesGcm.RISCV64
