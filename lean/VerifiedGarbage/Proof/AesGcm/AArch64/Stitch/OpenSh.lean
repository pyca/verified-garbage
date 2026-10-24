module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenW
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortOpen
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Mul
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Entry
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Open
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortSeal

/-!
# AES-GCM on AArch64, short records: `openWithS` with the short path

Untrusted: everything here is checked by Lean. `openWithS` with `sh` takes
`openShortF` for records of 17 to `shortMax` bytes (`shortThr`, `shortMin`), which
leaves what `open` must (`openShort_post`), and otherwise the paths of
`openWithS_wp`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxH ctxCiph)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

/-- `TbForO` without the key `H'` at `W + hO`, which `pwTbl` does not read. -/
def TbForOP (tb : List Instr) (Ctx W SP D : Addr) (n : Nat) (s₀ : State) : Prop :=
  ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = s₀.rd → u.wr = s₀.wr →
    Frame [workR W, ⟨D, n⟩] s₀.mem u.mem → WP isa (.block tb) u (Stitch.TblPost W (Spec.Gcm.ctxH s₀.mem Ctx) u)

theorem TbForOP.tbFor {tb : List Instr} {Ctx W SP D : Addr} {n : Nat} {s₀ : State}
    (h : TbForOP tb Ctx W SP D n s₀) : TbForO tb Ctx W SP D n s₀ :=
  fun u he hrd hwr hf _ => h u he hrd hwr hf

/-- `openWithS` with the path for short records (`sh`), for a `tb` that writes
the table without `H'` (`TbForOP`). -/
theorem openWithSh_wp (v : GcmImpl) (cl : Prog isa) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) (gh : Gh8Ok)
    {tb : List Instr} {w : Nat} (hw : w = 2 ∨ w = 3) {extra extraW : List Region}
    {s : State} (hs : openPreXW w extra s extraW)
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg s w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg s w)) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [workR (stackArg s w), ⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.mem s'.mem →
      WP isa cl s' (GhPost s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb))
    (htb : TbForOP tb (s.gpr .x0) (stackArg s w) s.sp (s.gpr .x6) (s.gpr .x7).toNat s) :
    WP isa (Impl.AesGcm.AArch64.Stitch.openWithS v.callees (8 * w) tb cl true) s fun s' =>
      GprAbi s s' ∧ openAArch64.post s s' := by
  obtain ⟨ol, -, -⟩ := openLay hs
  have hnb : (s.gpr .x7).toNat + 2560 ≤ 2 ^ 64 := len_of_disjoint ol.data ol.dw ol.lay.ww
  unfold Impl.AesGcm.AArch64.Stitch.openWithS
  refine WP.seq (WP.mono (WP.gprs (rs := [.x4, .x5, .x6, .x7]) (openEntry_ok hw hs)
    (by rcases hw with rfl | rfl <;> decide) (by rcases hw with rfl | rfl <;> decide))
    fun s₁ ⟨⟨o₁, x12₁⟩, hx₁⟩ => ?_)
  refine WP.seq (WP.mono (cond_ok (al := (s.gpr .x5).toNat) (nl := (s.gpr .x3).toNat)
    (by rw [hx₁ .x5 (by simp), ofNat_toNat']) (s.gpr .x5).isLt o₁.x24 (s.gpr .x3).isLt)
    fun s₂ ⟨x10₂, r₂⟩ => ?_)
  have o₂ := o₁.of_regs r₂
  have x12₂ : s₂.gpr .x12 = stackArg s 0 := by rw [r₂.others _ (by decide), x12₁]
  have hx₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₂.gpr r = s.gpr r := fun r hr => by
    rw [r₂.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), hx₁ r hr]
  by_cases hc : (s.gpr .x5).toNat ≤ 16 ∧ (s.gpr .x3).toNat = 12
  · refine WP.ite true (by rw [eval_zero x10₂ (by split <;> decide)]; simp [hc]) (fun _ => ?_) (fun h => by cases h)
    simp only [↓reduceIte]
    refine WP.seq (WP.mono (shortThr_ok (n := (s.gpr .x7).toNat) s₂ (by rw [hx₂ .x7 (by simp), ofNat_toNat'])
      (by omega)) fun s₃ ⟨x9₃, r₃⟩ => ?_)
    have o₃ := o₂.of_regs r₃
    have x12₃ : s₃.gpr .x12 = stackArg s 0 := by rw [r₃.others _ (by decide), x12₂]
    have hx₃ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₃.gpr r = s.gpr r := fun r hr => by
      rw [r₃.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), hx₂ r hr]
    refine WP.ite _ (eval_zero x9₃ (by omega)) (fun hz => ?_) (fun _ => ?_)
    · refine WP.seq (WP.mono (shortMin_ok (n := (s.gpr .x7).toNat) s₃ (by rw [hx₃ .x7 (by simp), ofNat_toNat'])
        (by omega)) fun s₄ ⟨x9₄, r₄⟩ => ?_)
      have o₄ := o₃.of_regs r₄
      have x12₄ : s₄.gpr .x12 = stackArg s 0 := by rw [r₄.others _ (by decide), x12₃]
      have hx₄ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₄.gpr r = s.gpr r := fun r hr => by
        rw [r₄.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), hx₃ r hr]
      refine WP.ite _ (eval_zero x9₄ (by omega)) (fun _ => ?_) (fun _ => ?_)
      · unfold Impl.AesGcm.AArch64.Fast.openFastP
        refine openRestWith_wp o₄ x12₄ fun o' hT hok hx' => ?_
        have hx (r : Reg) (hr : r ∈ [Reg.x4, .x5, .x6, .x7]) := (hx' r hr).trans (hx₄ r hr)
        exact openRunWith_post cl v hMK o' hc.2 (hx .x4 (by simp)) (by rw [hx .x5 (by simp), ofNat_toNat'])
          (hx .x6 (by simp)) (by rw [hx .x7 (by simp), ofNat_toNat']) hc.1 hT hok hgh
      · unfold Impl.AesGcm.AArch64.Stitch.openShortF
        refine openRestWith_wp o₄ x12₄ fun o' hT hok hx' => ?_
        have hx (r : Reg) (hr : r ∈ [Reg.x4, .x5, .x6, .x7]) := (hx' r hr).trans (hx₄ r hr)
        have h96 := of_decide_eq_true hz
        rw [hc.2] at o' ⊢
        exact openShort_post gh o' (hx .x4 (by simp)) (by rw [hx .x5 (by simp), ofNat_toNat'])
          (hx .x6 (by simp)) (by rw [hx .x7 (by simp), ofNat_toNat']) hc.1 (by omega) hT hok
          fun u he hrd hwr hf => htb u he hrd hwr hf
    · refine WP.seq (WP.mono (Stitch.thr_ok s₃) fun s₄ ⟨_, r₄⟩ => ?_)
      have o₄ := o₃.of_regs r₄
      have x12₄ : s₄.gpr .x12 = stackArg s 0 := by rw [r₄.others _ (by decide), x12₃]
      have hx₄ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₄.gpr r = s.gpr r := fun r hr => by
        rw [r₄.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), hx₃ r hr]
      refine WP.ite _ (eval_zero (a := (s₄.gpr .x9).toNat) (by rw [ofNat_toNat']) (s₄.gpr .x9).isLt)
        (fun _ => ?_) (fun _ => ?_)
      · unfold Impl.AesGcm.AArch64.Fast.openFastP
        refine openRestWith_wp o₄ x12₄ fun o' hT hok hx' => ?_
        have hx (r : Reg) (hr : r ∈ [Reg.x4, .x5, .x6, .x7]) := (hx' r hr).trans (hx₄ r hr)
        exact openRunWith_post cl v hMK o' hc.2 (hx .x4 (by simp)) (by rw [hx .x5 (by simp), ofNat_toNat'])
          (hx .x6 (by simp)) (by rw [hx .x7 (by simp), ofNat_toNat']) hc.1 hT hok hgh
      · unfold Impl.AesGcm.AArch64.Stitch.openFastS
        refine openRestWith_wp o₄ x12₄ fun o' hT hok hx' => ?_
        have hx (r : Reg) (hr : r ∈ [Reg.x4, .x5, .x6, .x7]) := (hx' r hr).trans (hx₄ r hr)
        exact WP.mono (openRunWithS_postX v cl hMK gh (ex := []) (I := fun _ => True) o' hc.2 (hx .x4 (by simp))
          (by rw [hx .x5 (by simp), ofNat_toNat']) (hx .x6 (by simp)) (by rw [hx .x7 (by simp), ofNat_toNat']) hc.1
          hT hok (by simp) (by simp) (by simp) (fun _ _ => trivial)
          (fun s' _ _ _ _ hc sY sS hr hw hsp hf _ => WP.mono (hgh s' hc sY sS hr hw hsp hf) fun _ g => ⟨g, trivial⟩)
          htb.tbFor) fun _ q => q.1
  · refine WP.ite false (by rw [eval_zero x10₂ (by split <;> decide)]; simp [hc]) (fun h => by cases h) (fun _ => ?_)
    exact openRestWith_wp o₂ x12₂ fun o' hT hok _ => openMain_post v o' hT hok

end VG.Proof.AesGcm.AArch64.Fast
