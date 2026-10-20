module

import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Run
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Tables
public import VerifiedGarbage.Proof.AesGcm.AArch64.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Entry
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Run
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Spec
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortSeal

/-!
# AES-GCM on AArch64, interleaved: `seal`'s code with the interleaved loops (`sealWithS`)

Untrusted: everything here is checked by Lean. `sealWithS` is `sealWithE`
(`Fast/Seal.lean`) with `runWithS` on the path for TLS records: after the
entry and `cond`, `runWithS` (`runWithSX_ok`) or `sealRest` (`sealWithS_wp`,
`sealWithSX_wp`), for any `tb` that writes the table of keys (`TblPost`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

/-- `powTbl` writes the table, for any `mul` of prepared powers that is one. -/
theorem powTbl_for (hP : Proof.Gcm.AArch64.Pmull.PrepPow) (w : Nat) (s : State) :
    TbFor Impl.AesGcm.AArch64.Stitch.powTbl w s :=
  fun _ he _ _ _ key => Stitch.powTbl_ok hP he key

/-- `runWithPX_ok` for `runWithS`, with a `tb` that writes the table. -/
theorem runWithSX_ok' (v : GcmImpl) (cl : Prog isa) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) (gh : Gh8Ok)
    {tb : List Instr} {w : Nat} {extra extraW : List Region} {s s₁ : State}
    {ex : List Region} {I : Mem → Prop}
    (hs : sealPreXW w extra s extraW)
    (hexW : ∀ r ∈ ex, (workR (stackArg s w)).Disjoint r)
    (hexD : ∀ r ∈ ex, (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region).Disjoint r)
    (hexC : ∀ r ∈ ex, (⟨s.gpr .x0, 256⟩ : Region).Disjoint r)
    (hI : ∀ {m m' : Mem}, I m → Frame [workR (stackArg s w), ⟨stackArg s 0, 16⟩] m m' → I m')
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg s w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg s w)) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [workR (stackArg s w), ⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region) →
      WP isa cl s' fun t => GhPost s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb t ex ∧ I t.mem)
    (htb : TbFor tb w s)
    (h₁ : SealEntry w s s₁) (hx : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₁.gpr r = s.gpr r)
    (h12 : (s.gpr .x3).toNat = 12) (h16 : (s.gpr .x5).toNat ≤ 16) :
    WP isa (Impl.AesGcm.AArch64.Stitch.runWithS v.callees tb cl) s₁ fun s' =>
      (GprAbi s s' ∧ sealAArch64.post s s') ∧ I s'.mem :=
  runWithSX_ok v cl hMK gh hs hexW hexD hexC hI hgh (fun u he hrd hwr hf key => htb u he hrd hwr hf key) h₁ hx
    h12 h16

/-- `sealWithEX_wp` for `sealWithS`. -/
theorem sealWithSX_wp (v : GcmImpl) (cl : Prog isa) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) (gh : Gh8Ok)
    {tb : List Instr} {w : Nat}
    (hw : w = 1 ∨ w = 2) {extra extraW : List Region} {s : State} {ex : List Region} {I : Mem → Prop}
    (hs : sealPreXW w extra s extraW) (hc : (s.gpr .x5).toNat ≤ 16 ∧ (s.gpr .x3).toNat = 12)
    (hexW : ∀ r ∈ ex, (workR (stackArg s w)).Disjoint r)
    (hexD : ∀ r ∈ ex, (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region).Disjoint r)
    (hexC : ∀ r ∈ ex, (⟨s.gpr .x0, 256⟩ : Region).Disjoint r)
    (hI : ∀ {m m' : Mem}, I m → Frame [workR (stackArg s w), ⟨stackArg s 0, 16⟩] m m' → I m')
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg s w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg s w)) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [workR (stackArg s w), ⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region) →
      WP isa cl s' fun t => GhPost s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb t ex ∧ I t.mem)
    (htb : TbFor tb w s) :
    WP isa (Impl.AesGcm.AArch64.Stitch.sealWithS v.callees (8 * w) tb cl) s fun s' =>
      (GprAbi s s' ∧ sealAArch64.post s s') ∧ I s'.mem := by
  refine WP.seq (WP.mono (fastEntry_ok hw hs) fun s₁ ⟨h₁, hx⟩ => ?_)
  refine WP.seq (WP.mono (cond_ok (al := (s.gpr .x5).toNat) (nl := (s.gpr .x3).toNat)
    (by rw [hx .x5 (by simp), ofNat_toNat']) (s.gpr .x5).isLt (by rw [h₁.x24, ofNat_toNat']) (s.gpr .x3).isLt)
    fun s₂ ⟨x10₂, r₂⟩ => ?_)
  have h₂ := SealEntry.of_regs h₁ r₂
  have hx₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₂.gpr r = s.gpr r := fun r hr => by
    rw [r₂.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), hx r hr]
  refine WP.ite true (by rw [eval_zero x10₂ (by split <;> decide)]; simp [hc]) (fun _ => ?_) (fun h => by cases h)
  refine WP.seq (WP.mono (Stitch.thr_ok s₂) fun s₃ ⟨_, r₃⟩ => ?_)
  have h₃ := SealEntry.of_regs h₂ r₃
  have hx₃ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₃.gpr r = s.gpr r := fun r hr => by
    rw [r₃.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), hx₂ r hr]
  refine WP.ite _ (eval_zero (a := (s₃.gpr .x9).toNat) (by rw [ofNat_toNat']) (s₃.gpr .x9).isLt)
    (fun _ => ?_) (fun _ => ?_)
  · exact runWithPX_ok v cl hMK hs hexW hexD hexC hI hgh h₃ hx₃ hc.2 hc.1
  · exact runWithSX_ok' v cl hMK gh hs hexW hexD hexC hI hgh htb h₃ hx₃ hc.2 hc.1

/-- `sealWithE_wp` for `sealWithS`. -/
theorem sealWithS_wp (v : GcmImpl) (cl : Prog isa) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) (gh : Gh8Ok)
    {tb : List Instr} {w : Nat}
    (hw : w = 1 ∨ w = 2) {extra extraW : List Region} {s : State} (hs : sealPreXW w extra s extraW)
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg s w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg s w)) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [workR (stackArg s w), ⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.mem s'.mem →
      WP isa cl s' (GhPost s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb))
    (htb : TbFor tb w s) :
    WP isa (Impl.AesGcm.AArch64.Stitch.sealWithS v.callees (8 * w) tb cl) s fun s' =>
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
    refine WP.seq (WP.mono (Stitch.thr_ok s₂) fun s₃ ⟨_, r₃⟩ => ?_)
    have h₃ := SealEntry.of_regs h₂ r₃
    have hx₃ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₃.gpr r = s.gpr r := fun r hr => by
      rw [r₃.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), hx₂ r hr]
    refine WP.ite _ (eval_zero (a := (s₃.gpr .x9).toNat) (by rw [ofNat_toNat']) (s₃.gpr .x9).isLt)
      (fun _ => ?_) (fun _ => ?_)
    · exact runWithP_ok v cl hMK hs hgh h₃ hx₃ hc.2 hc.1
    · exact WP.mono (runWithSX_ok' v cl hMK gh (ex := []) (I := fun _ => True) hs (by simp) (by simp) (by simp)
        (fun _ _ => trivial) (fun s' _ _ _ _ hc sY sS hrd hwr hsp hf _ =>
          WP.mono (hgh s' hc sY sS hrd hwr hsp hf) fun _ g => ⟨g, trivial⟩) htb h₃ hx₃ hc.2 hc.1) fun _ q => q.1
  · refine WP.ite false (by rw [eval_zero x10₂ (by split <;> decide)]; simp [hc]) (fun h => by cases h) (fun _ => ?_)
    exact sealRest_ok v hs h₂

/-- `sealWithS` with the path for short records (`sh`), for a `tb` that
writes the table without `H'` (`TbForP`). -/
theorem sealWithSh_wp (v : GcmImpl) (cl : Prog isa) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) (gh : Gh8Ok)
    {tb : List Instr} {w : Nat}
    (hw : w = 1 ∨ w = 2) {extra extraW : List Region} {s : State} (hs : sealPreXW w extra s extraW)
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg s w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg s w)) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [workR (stackArg s w), ⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.mem s'.mem →
      WP isa cl s' (GhPost s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb))
    (htb : TbForP tb w s) :
    WP isa (Impl.AesGcm.AArch64.Stitch.sealWithS v.callees (8 * w) tb cl true) s fun s' =>
      GprAbi s s' ∧ sealAArch64.post s s' := by
  obtain ⟨ol, -, -, -⟩ := sealLay hs
  have hnb : (s.gpr .x7).toNat + 2560 ≤ 2 ^ 64 := len_of_disjoint ol.data ol.dw ol.lay.ww
  refine WP.seq (WP.mono (fastEntry_ok hw hs) fun s₁ ⟨h₁, hx⟩ => ?_)
  refine WP.seq (WP.mono (cond_ok (al := (s.gpr .x5).toNat) (nl := (s.gpr .x3).toNat)
    (by rw [hx .x5 (by simp), ofNat_toNat']) (s.gpr .x5).isLt (by rw [h₁.x24, ofNat_toNat']) (s.gpr .x3).isLt)
    fun s₂ ⟨x10₂, r₂⟩ => ?_)
  have h₂ := SealEntry.of_regs h₁ r₂
  have hx₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₂.gpr r = s.gpr r := fun r hr => by
    rw [r₂.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), hx r hr]
  by_cases hc : (s.gpr .x5).toNat ≤ 16 ∧ (s.gpr .x3).toNat = 12
  · refine WP.ite true (by rw [eval_zero x10₂ (by split <;> decide)]; simp [hc]) (fun _ => ?_) (fun h => by cases h)
    simp only [ite_true]
    refine WP.seq (WP.mono (shortThr_ok (n := (s.gpr .x7).toNat) s₂ (by rw [hx₂ .x7 (by simp), ofNat_toNat'])
      (by omega)) fun s₃ ⟨x9₃, r₃⟩ => ?_)
    have h₃ := SealEntry.of_regs h₂ r₃
    have hx₃ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₃.gpr r = s.gpr r := fun r hr => by
      rw [r₃.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), hx₂ r hr]
    refine WP.ite _ (eval_zero x9₃ (by omega)) (fun hz => ?_) (fun _ => ?_)
    · refine WP.seq (WP.mono (shortMin_ok (n := (s.gpr .x7).toNat) s₃ (by rw [hx₃ .x7 (by simp), ofNat_toNat'])
        (by omega)) fun s₄ ⟨x9₄, r₄⟩ => ?_)
      have h₄ := SealEntry.of_regs h₃ r₄
      have hx₄ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₄.gpr r = s.gpr r := fun r hr => by
        rw [r₄.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), hx₃ r hr]
      refine WP.ite _ (eval_zero x9₄ (by omega)) (fun _ => ?_) (fun hz' => ?_)
      · exact runWithP_ok v cl hMK hs hgh h₄ hx₄ hc.2 hc.1
      · have h₁ := of_decide_eq_true hz
        have h₂ := of_decide_eq_false hz'
        exact sealShort_ok gh hs htb h₄ hx₄ hc.2 hc.1 (by omega) (by omega)
    · refine WP.seq (WP.mono (Stitch.thr_ok s₃) fun s₄ ⟨_, r₄⟩ => ?_)
      have h₄ := SealEntry.of_regs h₃ r₄
      have hx₄ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₄.gpr r = s.gpr r := fun r hr => by
        rw [r₄.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), hx₃ r hr]
      refine WP.ite _ (eval_zero (a := (s₄.gpr .x9).toNat) (by rw [ofNat_toNat']) (s₄.gpr .x9).isLt)
        (fun _ => ?_) (fun _ => ?_)
      · exact runWithP_ok v cl hMK hs hgh h₄ hx₄ hc.2 hc.1
      · exact WP.mono (runWithSX_ok' v cl hMK gh (ex := []) (I := fun _ => True) hs (by simp) (by simp) (by simp)
          (fun _ _ => trivial) (fun s' _ _ _ _ hc sY sS hrd hwr hsp hf _ =>
            WP.mono (hgh s' hc sY sS hrd hwr hsp hf) fun _ g => ⟨g, trivial⟩) htb.tbFor h₄ hx₄ hc.2 hc.1)
          fun _ q => q.1
  · refine WP.ite false (by rw [eval_zero x10₂ (by split <;> decide)]; simp [hc]) (fun h => by cases h) (fun _ => ?_)
    exact sealRest_ok v hs h₂

end VG.Proof.AesGcm.AArch64.Fast
