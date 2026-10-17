module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Run
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Entry
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# AES-GCM on AArch64: `vg_aes_gcm_seal` with the path for TLS records

Untrusted: everything here is checked by Lean. After the entry
(`fastEntry_ok`), `cond` sets `x10` to 0 exactly for a 12-byte nonce and at
most 16 bytes of additional data (`cond_ok`); then `run` (`run_ok`) or
`sealRest` (`sealRest_ok`) (`seal_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64

theorem ofNat_sub_ofNat_eq_zero {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · subst h; rw [BitVec.sub_self, decide_eq_true rfl]; rfl
  · have hne : BitVec.ofNat 64 a - BitVec.ofNat 64 b ≠ 0 := fun e => h (by
      have h' := congrArg BitVec.toNat e
      simp [BitVec.toNat_sub] at h'
      omega)
    rw [beq_eq_false_iff_ne.mpr hne, decide_eq_false h]

/-- `cond`: `x10 = 0` exactly for at most 16 bytes of additional data and a
12-byte nonce. -/
theorem cond_ok {s : State} {al nl : Nat} (h5 : s.gpr .x5 = BitVec.ofNat 64 al) (hal : al < 2 ^ 64)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 nl) (hnl : nl < 2 ^ 64) :
    WP isa Impl.AesGcm.AArch64.Fast.cond s fun s' =>
      s'.gpr .x10 = BitVec.ofNat 64 (if al ≤ 16 ∧ nl = 12 then 0 else 1) ∧ Regs [.x9, .x10] s s' := by
  unfold Impl.AesGcm.AArch64.Fast.cond
  obtain ⟨s₁, run₁, x10₁, x9₁, r₁⟩ : ∃ s₁, runBlock isa [imm .x10 0, .lsr .x .x9 .x5 4] s = some s₁ ∧
      s₁.gpr .x10 = BitVec.ofNat 64 0 ∧ s₁.gpr .x9 = BitVec.ofNat 64 (al / 2 ^ 4) ∧ Regs [.x9, .x10] s s₁ := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write], by simp [gpr_write, h5, lsr_ofNat _ _ hal], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.gpr .x10 = BitVec.ofNat 64 (if al ≤ 16 then 0 else 1) ∧
      Regs [.x9, .x10] s s₂)
    (WP.ite (decide (al / 2 ^ 4 = 0)) (eval_zero x9₁ (by omega)) (fun ht => ?_) (fun hf => ?_))
    fun s₂ ⟨x10₂, r₂⟩ => ?_)
  · have : al < 16 := by have := of_decide_eq_true ht; omega
    exact WP.block_nil ⟨by rw [x10₁, ite_eq_left (by omega)], r₁⟩
  · have h16 : 16 ≤ al := by have := of_decide_eq_false hf; omega
    obtain ⟨s₂, run₂, x9₂, r₂⟩ : ∃ s₂, runBlock isa [.subImm .x .x9 .x5 16] s₁ = some s₂ ∧
        s₂.gpr .x9 = BitVec.ofNat 64 (al - 16) ∧ Regs [.x9] s₁ s₂ := by
      refine ⟨_, by arun [], ?_⟩
      exact ⟨by simp [gpr_write, r₁.others .x5 (by decide), h5, ofNat_sub h16 hal], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    refine WP.ite (decide (al - 16 = 0)) (eval_zero x9₂ (by omega)) (fun ht => ?_) (fun hf => ?_)
    · have : al = 16 := by have := of_decide_eq_true ht; omega
      exact WP.block_nil ⟨by rw [r₂.others _ (by decide), x10₁, ite_eq_left (by omega)], r₁.trans r₂⟩
    · have : al ≠ 16 := by have := of_decide_eq_false hf; omega
      obtain ⟨s₃, run₃, x10₃, r₃⟩ : ∃ s₃, runBlock isa [imm .x10 1] s₂ = some s₃ ∧
          s₃.gpr .x10 = BitVec.ofNat 64 1 ∧ Regs [.x10] s₂ s₃ := by
        refine ⟨_, by arun [], ?_⟩
        exact ⟨by simp [gpr_write], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
      exact WP.of_runBlock ⟨s₃, run₃, by rw [x10₃]; simp [show ¬ al ≤ 16 by omega], (r₁.trans r₂).trans r₃⟩
  obtain ⟨s₃, run₃, x9₃, r₃⟩ : ∃ s₃, runBlock isa [.subImm .x .x9 .x24 12] s₂ = some s₃ ∧
      s₃.gpr .x9 = BitVec.ofNat 64 nl - BitVec.ofNat 64 12 ∧ Regs [.x9] s₂ s₃ := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write, r₂.others .x24 (by decide), h24], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have ev : isa.eval (.zero .x .x9) s₃ = some (decide (nl = 12)) := by
    show some (s₃.read .x .x9 == 0) = _
    rw [State.read, x9₃, BitVec.setWidth_eq, ofNat_sub_ofNat_eq_zero hnl (by decide)]
  refine WP.ite (decide (nl = 12)) ev (fun ht => ?_) (fun hf => ?_)
  · have : nl = 12 := of_decide_eq_true ht
    exact WP.block_nil ⟨by rw [r₃.others _ (by decide), x10₂]; simp [this], r₂.trans r₃⟩
  · have : nl ≠ 12 := of_decide_eq_false hf
    obtain ⟨s₄, run₄, x10₄, r₄⟩ : ∃ s₄, runBlock isa [imm .x10 1] s₃ = some s₄ ∧
        s₄.gpr .x10 = BitVec.ofNat 64 1 ∧ Regs [.x10] s₃ s₄ := by
      refine ⟨_, by arun [], ?_⟩
      exact ⟨by simp [gpr_write], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    exact WP.of_runBlock ⟨s₄, run₄, by rw [x10₄]; simp [this], (r₂.trans r₃).trans r₄⟩

/-- `SealEntry` after code that writes only `x9` and `x10`. -/
theorem SealEntry.of_regs {w : Nat} {s s₁ s₂ : State} (h : SealEntry w s s₁) (r : Regs [.x9, .x10] s₁ s₂) :
    SealEntry w s s₂ :=
  ⟨h.env.of_regs r, by rw [r.others _ (by decide), h.x22], by rw [r.others _ (by decide), h.x23],
    by rw [r.others _ (by decide), h.x24], by rw [r.others _ (by decide), h.x26],
    by rw [r.others _ (by decide), h.x27], by rw [r.others _ (by decide), h.x28],
    by rw [r.mem, h.sA], by rw [r.mem, h.sL], by rw [r.mem, h.sD], by rw [r.mem, h.sN], by rw [r.mem, h.sT],
    by rw [r.mem]; exact h.frame, by rw [r.mem]; exact h.saved, by rw [r.rd, h.rd], by rw [r.wr, h.wr]⟩

/-- `vg_aes_gcm_seal` with the path for TLS records, `work` the stack
argument `w`, and its whole blocks hashed by `cl`, which hashes as a call of
`vg_ghash` when run with memory changed since the entry only in the working
space and the text. -/
theorem sealWithE_wp (v : GcmImpl) (cl : Prog isa) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) {w : Nat}
    (hw : w = 1 ∨ w = 2) {extra : List Region} {s : State} (hs : sealPreXW w extra s)
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg s w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg s w)) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [workR (stackArg s w), ⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.mem s'.mem →
      WP isa cl s' (GhPost s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb)) :
    WP isa (Impl.AesGcm.AArch64.Fast.sealWithE v.callees (8 * w) cl) s fun s' =>
      GprAbi s s' ∧ sealAArch64.post s s' := by
  refine WP.seq (WP.mono (fastEntry_ok hw hs) fun s₁ ⟨h₁, hx⟩ => ?_)
  refine WP.seq (WP.mono (cond_ok (al := (s.gpr .x5).toNat) (nl := (s.gpr .x3).toNat)
    (by rw [hx .x5 (by simp), ofNat_toNat']) (s.gpr .x5).isLt (by rw [h₁.x24, ofNat_toNat']) (s.gpr .x3).isLt)
    fun s₂ ⟨x10₂, r₂⟩ => ?_)
  have h₂ := SealEntry.of_regs h₁ r₂
  have hx₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₂.gpr r = s.gpr r := fun r hr => by
    rw [r₂.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), hx r hr]
  by_cases hc : (s.gpr .x5).toNat ≤ 16 ∧ (s.gpr .x3).toNat = 12
  · refine WP.ite true (by rw [eval_zero x10₂ (by split <;> decide)]; simp [hc]) (fun _ => ?_) (fun h => by cases h)
    exact runWithP_ok v cl hMK hs hgh h₂ hx₂ hc.2 hc.1
  · refine WP.ite false (by rw [eval_zero x10₂ (by split <;> decide)]; simp [hc]) (fun h => by cases h) (fun _ => ?_)
    exact sealRest_ok v hs h₂

/-- `sealWithE_wp` for a TLS record (a 12-byte nonce and at most 16 bytes of
additional data), whose call may also write `ex` and establish `I`
(`runWithPX_ok`). -/
theorem sealWithEX_wp (v : GcmImpl) (cl : Prog isa) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) {w : Nat}
    (hw : w = 1 ∨ w = 2) {extra : List Region} {s : State} {ex : List Region} {I : Mem → Prop}
    (hs : sealPreXW w extra s) (hc : (s.gpr .x5).toNat ≤ 16 ∧ (s.gpr .x3).toNat = 12)
    (hexW : ∀ r ∈ ex, (workR (stackArg s w)).Disjoint r)
    (hexD : ∀ r ∈ ex, (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region).Disjoint r)
    (hexC : ∀ r ∈ ex, (⟨s.gpr .x0, 256⟩ : Region).Disjoint r)
    (hI : ∀ {m m' : Mem}, I m → Frame [workR (stackArg s w), ⟨stackArg s 0, 16⟩] m m' → I m')
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg s w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg s w)) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [workR (stackArg s w), ⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.mem s'.mem →
      WP isa cl s' fun t => GhPost s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb t ex ∧ I t.mem) :
    WP isa (Impl.AesGcm.AArch64.Fast.sealWithE v.callees (8 * w) cl) s fun s' =>
      (GprAbi s s' ∧ sealAArch64.post s s') ∧ I s'.mem := by
  refine WP.seq (WP.mono (fastEntry_ok hw hs) fun s₁ ⟨h₁, hx⟩ => ?_)
  refine WP.seq (WP.mono (cond_ok (al := (s.gpr .x5).toNat) (nl := (s.gpr .x3).toNat)
    (by rw [hx .x5 (by simp), ofNat_toNat']) (s.gpr .x5).isLt (by rw [h₁.x24, ofNat_toNat']) (s.gpr .x3).isLt)
    fun s₂ ⟨x10₂, r₂⟩ => ?_)
  have h₂ := SealEntry.of_regs h₁ r₂
  have hx₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₂.gpr r = s.gpr r := fun r hr => by
    rw [r₂.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), hx r hr]
  refine WP.ite true (by rw [eval_zero x10₂ (by split <;> decide)]; simp [hc]) (fun _ => ?_) (fun h => by cases h)
  exact runWithPX_ok v cl hMK hs hexW hexD hexC hI hgh h₂ hx₂ hc.2 hc.1

/-- `vg_aes_gcm_seal` with the path for TLS records, its whole blocks hashed
by `gh`, which hashes as `vg_ghash` when called with memory changed since the
entry only in the working space and the text. -/
theorem sealWith_wp (v : GcmImpl) (gh : Fn) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) {extra : List Region}
    {s : State} (hs : sealPreX extra s)
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg s 1)) → Region.Sub ⟨S, 256⟩ (workR (stackArg s 1)) →
      s'.rd = s.rd → s'.wr = s.wr →
      Frame [workR (stackArg s 1), ⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.mem s'.mem →
      WP isa (.call gh.name gh.code) s' (GhPost s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb)) :
    WP isa (Impl.AesGcm.AArch64.Fast.sealWith v.callees gh) s fun s' => GprAbi s s' ∧ sealAArch64.post s s' :=
  sealWithE_wp (w := 1) v _ hMK (.inl rfl) (sealPreX_W hs) fun s' _ _ _ _ c y z r w _ f => hgh s' c y z r w f

/-- `vg_aes_gcm_seal` with the path for TLS records. -/
theorem seal_wp (v : GcmImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) {s : State} (hs : sealAArch64.pre s) :
    WP isa (Impl.AesGcm.AArch64.Fast.«seal» v.callees) s fun s' => GprAbi s s' ∧ sealAArch64.post s s' :=
  sealWith_wp (extra := []) v v.gh.fn hMK hs fun _ _ _ _ _ hc _ _ _ _ _ => gh_call v.gh hc

end VG.Proof.AesGcm.AArch64.Fast
