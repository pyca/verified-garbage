import VerifiedGarbage.Proof.AesSiv.X86.FinishLong

/-!
# AES-SIV on x86: finishing S2V

Untrusted: everything here is checked by Lean. `finish out` takes the short
case (`finishShort_ok`) for a last string of fewer than 16 bytes and the long
case (`finishLong_ok`) otherwise (`finish_ok`).
-/

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 copyLoop)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 slotv CT)

theorem cmp16_ok {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) {k : Nat}
    (hk : slotv s.mem W slenO = BitVec.ofNat 32 k) (hk32 : k < 2 ^ 32) :
    ∃ s', runBlock isa [.mov .ecx (slot slenO), .alu .cmp .ecx (imm 16)] s = some s' ∧
      s'.cf = some (decide (k < 16)) ∧ (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hk], ?_, fun r h₁ => ?_, ?_, ?_, ?_⟩
  · cmems [hk, toNat_ofNat32 hk32]; rfl
  · cregs []
  all_goals cmems []

theorem CmacPre.of_eq {C W SP : BitVec 32} {R : Nat} {P : BitVec 32} {k : Nat} {s s' : State}
    (h : CmacPre C W SP R P k s) (hbp : s'.gpr .ebp = s.gpr .ebp) (hsp : s'.gpr .esp = s.gpr .esp)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : CmacPre C W SP R P k s' :=
  ⟨⟨by rw [hbp]; exact h.env.ebp, by rw [hsp]; exact h.env.esp, h.env.perm.of_eq hrd hwr⟩,
    by rw [hm]; exact h.ctx, by rw [hm]; exact h.rounds, by rw [hm]; exact h.str, by rw [hm]; exact h.slen, h.k32,
    h.buf.of_eq hrd hwr⟩

theorem FinPost.of_eq {C W SP : BitVec 32} {R out : Nat} {P : BitVec 32} {k : Nat} {s s₁ s' : State}
    (h : FinPost C W SP R out P k s₁ s') (hm : s₁.mem = s.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) :
    FinPost C W SP R out P k s s' :=
  ⟨h.env, h.rd.trans hrd, h.wr.trans hwr, by rw [← hm]; exact h.frame, by rw [← hm]; exact h.out⟩

/-- `finish out`: S2V's end, from `D` and the string at `W + strO`, at
`W + out`. -/
theorem finish_ok (v : Ctr32Impl) {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32} {k : Nat} {s : State} (h : CmacPre C W SP R P k s)
    {out : Nat} (hout : out = 0 ∨ out = 112) :
    WP isa (finish v.callee v.suffix out) s (FinPost C W SP R out P k s) := by
  obtain ⟨s₁, run₁, cf₁, g₁, m₁, rd₁, wr₁⟩ := cmp16_ok L h.env h.slen h.k32
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have h₁ := h.of_eq (g₁ _ (by decide)) (g₁ _ (by decide)) m₁ rd₁ wr₁
  refine WP.ite (decide (k < 16)) (eval_b cf₁) (fun ht => ?_) (fun hf => ?_)
  · exact WP.mono (finishShort_ok v L hR h₁ (of_decide_eq_true ht) hout) fun _ p => p.of_eq m₁ rd₁ wr₁
  · exact WP.mono (finishLong_ok v L hR h₁ (by have := of_decide_eq_false hf; omega) hout)
      fun _ p => p.of_eq m₁ rd₁ wr₁

end VG.Proof.AesSiv.X86
