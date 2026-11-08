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

Untrusted: everything here is checked by Lean. `openWithSG c to` with `sh`
takes `openShortFG` for records of 17 to `shortMax` bytes (`shortThr`,
`shortMin`), which leaves what `open` (or out of place `open_to`) must
(`openShort_post`), and otherwise the other paths (`openSelS_wp`): in place
`openWithSh_wp`, out of place `openToWithSh_wp`.
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

/-- The branch on the tag length failing: 0 returned, and out of place the
output zeroed (in place, the text as it was). -/
theorem failG_ok {to : Bool} {Ctx W SP Np A D O Tg : Addr} {R nl al n tl : Nat} {s₀ s₃ : State}
    (o : OpenInG to Ctx W SP Np A D O Tg R nl al n tl s₀ s₃) (hok : Spec.Gcm.tagLenOk tl = false) :
    WP isa (.seq (.block [imm .x0 0]) (wipeG to)) s₃ (OpenPostG Ctx W SP Np A O Tg R nl al n tl
      (bytesAt s₀.mem D n) (fun m => bytesAt m O n = cond to (List.replicate n 0) (bytesAt s₀.mem D n)) s₀) := by
  cases to with
  | true => exact failTo_ok o hok
  | false =>
    have e : O = D := o.out
    subst e
    exact WP.seq (WP.mono (failZero_ok (C := bytesAt s₀.mem O n) (F := fun m => bytesAt m O n = bytesAt s₀.mem O n)
      o o.vals.2.2.2.2 hok) fun u q => WP.block_nil q)

/-- `openWithSG c to w tb cl sh` after its entry. -/
def openSelS (c : Callees) (to : Bool) (tb : List Instr) (cl : Prog isa) (sh : Bool) : Prog isa :=
  .seq Impl.AesGcm.AArch64.Fast.cond (.ite (.zero .x .x10)
      (if sh then
        .seq (.block Impl.AesGcm.AArch64.Stitch.shortThr) (.ite (.zero .x .x9)
          (.seq (.block Impl.AesGcm.AArch64.Stitch.shortMin) (.ite (.zero .x .x9)
            (Impl.AesGcm.AArch64.Fast.openFastPG c to cl) (Impl.AesGcm.AArch64.Stitch.openShortFG to tb)))
          (.seq (.block Impl.AesGcm.AArch64.Stitch.thr) (.ite (.zero .x .x9)
            (Impl.AesGcm.AArch64.Fast.openFastPG c to cl) (Impl.AesGcm.AArch64.Stitch.openFastSG c to tb cl))))
      else .seq (.block Impl.AesGcm.AArch64.Stitch.thr) (.ite (.zero .x .x9)
        (Impl.AesGcm.AArch64.Fast.openFastPG c to cl) (Impl.AesGcm.AArch64.Stitch.openFastSG c to tb cl)))
      (openRestG c to))

theorem openWithSG_eq (c : Callees) (to : Bool) (w : Nat) (tb : List Instr) (cl : Prog isa) (sh : Bool) :
    Impl.AesGcm.AArch64.Stitch.openWithSG c to w tb cl sh = .seq (.block (openEntryG to w)) (openSelS c to tb cl sh) :=
  rfl

/-- What `openWithSG c to` leaves, from `s`, of the text at `x6` and the
output at `O`: the plaintext there if the tag is right, and otherwise the
text as it was in place, zeros out of place. -/
abbrev OpenSPost (to : Bool) (O Tg : Addr) (tl : Nat) (s s' : State) : Prop :=
  GprAbi s s' ∧
    match Spec.Gcm.openResult (ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (ctxH s.mem (s.gpr .x0)) tl
        (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
        (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) (bytesAt s.mem Tg tl) with
    | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem O (s.gpr .x7).toNat = pt
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
        bytesAt s'.mem O (s.gpr .x7).toNat = cond to (List.replicate (s.gpr .x7).toNat 0)
          (bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)

/-- `openSelS`, after the entry of `open` or `open_to` (`to`) from `s`, with
the text at `x6` and the output at `O`, for a `tb` that writes the table
without `H'` (`TbForOP`) and a `cl` that hashes as `vg_ghash` when run with
memory changed since the entry only in the working space and the output. -/
theorem openSelS_wp (v : GcmImpl) (cl : Prog isa) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) (gh : Gh8Ok)
    {tb : List Instr} {to sh : Bool} {s s₁ : State} {W O Tg : Addr} {tl : Nat}
    (o₁ : OpenInG to (s.gpr .x0) W s.sp (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) O Tg (s.gpr .x1).toNat
      (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat tl s s₁)
    (x12₁ : s₁.gpr .x12 = Tg) (hx₁ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₁.gpr r = s.gpr r)
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [workR W, ⟨O, (s.gpr .x7).toNat⟩] s.mem s'.mem →
      WP isa cl s' (GhPost s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb))
    (htb : TbForOP tb (s.gpr .x0) W s.sp O (s.gpr .x7).toNat s) :
    WP isa (openSelS v.callees to tb cl sh) s₁ (OpenSPost to O Tg tl s) := by
  have hdk := dataOk_of o₁.dat
  have hnb : (s.gpr .x7).toNat + 2560 ≤ 2 ^ 64 := len_of_disjoint hdk.w hdk.wrap o₁.lay.ww
  have doD : ∀ r ∈ ([] : List Region), (⟨O, (s.gpr .x7).toNat⟩ : Region).Disjoint r := by simp
  -- The branch on the tag length, and then `m`.
  have rest : ∀ {m : Prog isa} {s₄ : State}, OpenInG to (s.gpr .x0) W s.sp (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) O Tg
      (s.gpr .x1).toNat (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat tl s s₄ → s₄.gpr .x12 = Tg →
      (∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₄.gpr r = s.gpr r) →
      (∀ {t : State}, OpenInG to (s.gpr .x0) W s.sp (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) O Tg (s.gpr .x1).toNat
          (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat tl s t →
        bytesAt t.mem W tl = bytesAt s.mem Tg tl → Spec.Gcm.tagLenOk tl = true →
        (∀ r ∈ [Reg.x4, .x5, .x6, .x7], t.gpr r = s.gpr r) →
        WP isa m t (OpenPostG (s.gpr .x0) W s.sp (s.gpr .x2) (s.gpr .x4) O Tg (s.gpr .x1).toNat
          (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat tl (bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
          (fun m => bytesAt m O (s.gpr .x7).toNat = cond to (List.replicate (s.gpr .x7).toNat 0)
            (bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)) s)) →
      WP isa (.seq tagLenOk (.seq (.ite (.zero .x .x9) (.seq (.block [imm .x0 0]) (wipeG to)) (.seq tagIn m))
        (.block restore))) s₄ (OpenSPost to O Tg tl s) := fun {m s₄} o₄ x12₄ hx₄ hm => by
    refine WP.mono (openRestWithFl_wp (fl := .seq (.block [imm .x0 0]) (wipeG to)) (m := m)
      (C := bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
      (F := fun m => bytesAt m O (s.gpr .x7).toNat = cond to (List.replicate (s.gpr .x7).toNat 0)
        (bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)) o₄ x12₄ (fun o' _ _ hok => ?_)
      fun o' hT hok hx' => hm o' hT hok fun r hr => (hx' r hr).trans (hx₄ r hr)) fun _ h => h
    exact failG_ok o' hok
  unfold openSelS
  refine WP.seq (WP.mono (cond_ok (al := (s.gpr .x5).toNat) (nl := (s.gpr .x3).toNat)
    (by rw [hx₁ .x5 (by simp), ofNat_toNat']) (s.gpr .x5).isLt o₁.x24 (s.gpr .x3).isLt)
    fun s₂ ⟨x10₂, r₂⟩ => ?_)
  have o₂ := o₁.of_regs r₂
  have x12₂ : s₂.gpr .x12 = Tg := by rw [r₂.others _ (by decide), x12₁]
  have hx₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₂.gpr r = s.gpr r := fun r hr => by
    rw [r₂.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), hx₁ r hr]
  by_cases hc : (s.gpr .x5).toNat ≤ 16 ∧ (s.gpr .x3).toNat = 12
  · refine WP.ite true (by rw [eval_zero x10₂ (by split <;> decide)]; simp [hc]) (fun _ => ?_) (fun h => by cases h)
    -- The three paths for TLS records, once the tag is read.
    have fastP : ∀ {s₄ : State}, OpenInG to (s.gpr .x0) W s.sp (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) O Tg
        (s.gpr .x1).toNat (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat tl s s₄ → s₄.gpr .x12 = Tg →
        (∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₄.gpr r = s.gpr r) →
        WP isa (Impl.AesGcm.AArch64.Fast.openFastPG v.callees to cl) s₄ (OpenSPost to O Tg tl s) :=
      fun o₄ x12₄ hx₄ => rest o₄ x12₄ hx₄ fun o' hT hok hx =>
        openRunWithG_postE cl v hMK (ex := []) o' hc.2 (hx .x4 (by simp)) (by rw [hx .x5 (by simp), ofNat_toNat'])
          (hx .x6 (by simp)) (by rw [hx .x7 (by simp), ofNat_toNat']) hc.1 hT hok (by simp) (by simp) (by simp)
          fun s' _ _ _ _ c sY sS hr hw hsp hf _ => hgh s' c sY sS hr hw hsp (frame_wD hf)
    have fastS : ∀ {s₄ : State}, OpenInG to (s.gpr .x0) W s.sp (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) O Tg
        (s.gpr .x1).toNat (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat tl s s₄ → s₄.gpr .x12 = Tg →
        (∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₄.gpr r = s.gpr r) →
        WP isa (Impl.AesGcm.AArch64.Stitch.openFastSG v.callees to tb cl) s₄ (OpenSPost to O Tg tl s) :=
      fun o₄ x12₄ hx₄ => rest o₄ x12₄ hx₄ fun o' hT hok hx =>
        WP.mono (openRunWithS_postX v cl hMK gh (ex := []) (I := fun _ => True) o' hc.2 (hx .x4 (by simp))
          (by rw [hx .x5 (by simp), ofNat_toNat']) (hx .x6 (by simp)) (by rw [hx .x7 (by simp), ofNat_toNat']) hc.1
          hT hok (by simp) (by simp) (by simp) (by simp) (fun _ _ => trivial)
          (fun s' _ _ _ _ hc sY sS hr hw hsp hf _ => WP.mono (hgh s' hc sY sS hr hw hsp hf) fun _ g => ⟨g, trivial⟩)
          htb.tbFor) fun _ q => q.1
    cases sh with
    | true =>
      simp only [↓reduceIte]
      refine WP.seq (WP.mono (shortThr_ok (n := (s.gpr .x7).toNat) s₂ (by rw [hx₂ .x7 (by simp), ofNat_toNat'])
        (by omega)) fun s₃ ⟨x9₃, r₃⟩ => ?_)
      have o₃ := o₂.of_regs r₃
      have x12₃ : s₃.gpr .x12 = Tg := by rw [r₃.others _ (by decide), x12₂]
      have hx₃ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₃.gpr r = s.gpr r := fun r hr => by
        rw [r₃.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), hx₂ r hr]
      refine WP.ite _ (eval_zero x9₃ (by omega)) (fun hz => ?_) (fun _ => ?_)
      · refine WP.seq (WP.mono (shortMin_ok (n := (s.gpr .x7).toNat) s₃ (by rw [hx₃ .x7 (by simp), ofNat_toNat'])
          (by omega)) fun s₄ ⟨x9₄, r₄⟩ => ?_)
        have o₄ := o₃.of_regs r₄
        have x12₄ : s₄.gpr .x12 = Tg := by rw [r₄.others _ (by decide), x12₃]
        have hx₄ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₄.gpr r = s.gpr r := fun r hr => by
          rw [r₄.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), hx₃ r hr]
        refine WP.ite _ (eval_zero x9₄ (by omega)) (fun _ => fastP o₄ x12₄ hx₄) (fun _ => ?_)
        unfold Impl.AesGcm.AArch64.Stitch.openShortFG
        refine rest o₄ x12₄ hx₄ fun o' hT hok hx => ?_
        have h96 := of_decide_eq_true hz
        rw [hc.2] at o' ⊢
        exact openShort_post gh o' (hx .x4 (by simp)) (by rw [hx .x5 (by simp), ofNat_toNat'])
          (hx .x6 (by simp)) (by rw [hx .x7 (by simp), ofNat_toNat']) hc.1 (by omega) hT hok
          fun u he hrd hwr hf => htb u he hrd hwr hf
      · refine WP.seq (WP.mono (Stitch.thr_ok s₃) fun s₄ ⟨_, r₄⟩ => ?_)
        have o₄ := o₃.of_regs r₄
        have x12₄ : s₄.gpr .x12 = Tg := by rw [r₄.others _ (by decide), x12₃]
        have hx₄ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₄.gpr r = s.gpr r := fun r hr => by
          rw [r₄.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), hx₃ r hr]
        refine WP.ite _ (eval_zero (a := (s₄.gpr .x9).toNat) (by rw [ofNat_toNat']) (s₄.gpr .x9).isLt)
          (fun _ => fastP o₄ x12₄ hx₄) (fun _ => fastS o₄ x12₄ hx₄)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine WP.seq (WP.mono (Stitch.thr_ok s₂) fun s₄ ⟨_, r₄⟩ => ?_)
      have o₄ := o₂.of_regs r₄
      have x12₄ : s₄.gpr .x12 = Tg := by rw [r₄.others _ (by decide), x12₂]
      have hx₄ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₄.gpr r = s.gpr r := fun r hr => by
        rw [r₄.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), hx₂ r hr]
      refine WP.ite _ (eval_zero (a := (s₄.gpr .x9).toNat) (by rw [ofNat_toNat']) (s₄.gpr .x9).isLt)
        (fun _ => fastP o₄ x12₄ hx₄) (fun _ => fastS o₄ x12₄ hx₄)
  · refine WP.ite false (by rw [eval_zero x10₂ (by split <;> decide)]; simp [hc]) (fun h => by cases h) (fun _ => ?_)
    unfold openRestG
    exact rest o₂ x12₂ hx₂ fun o' hT hok _ => openMainG_post v to o' hT hok

/-- `vg_aes_gcm_open` with the interleaved path and the path for short
records (`sh`), `work` the stack argument `w`, for a `tb` that writes the
table without `H'` (`TbForOP`). -/
theorem openWithSh_wp (v : GcmImpl) (cl : Prog isa) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) (gh : Gh8Ok)
    {tb : List Instr} {w : Nat} (hw : w = 2 ∨ w = 3) {extra extraW : List Region}
    {s : State} (hs : openPreXW w extra s extraW)
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg s w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg s w)) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [workR (stackArg s w), ⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.mem s'.mem →
      WP isa cl s' (GhPost s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb))
    (htb : TbForOP tb (s.gpr .x0) (stackArg s w) s.sp (s.gpr .x6) (s.gpr .x7).toNat s) :
    WP isa (Impl.AesGcm.AArch64.Stitch.openWithSG v.callees false w tb cl true) s fun s' =>
      GprAbi s s' ∧ openAArch64.post s s' := by
  rw [openWithSG_eq, show openEntryG false w = oneEntry (8 * w) ++ stashArg 8 ++ ([.ldrSp .x12 0] : List Instr) by
    simp only [openEntryG, Bool.cond_false, List.append_nil]]
  refine WP.seq (WP.mono (WP.gprs (rs := [.x4, .x5, .x6, .x7]) (openEntry_ok hw hs)
    (by rcases hw with rfl | rfl <;> decide) (by rcases hw with rfl | rfl <;> decide))
    fun s₁ ⟨⟨o₁, x12₁⟩, hx₁⟩ => ?_)
  exact WP.mono (openSelS_wp v cl hMK gh o₁ x12₁ hx₁ hgh htb) fun _ h => h

/-- `vg_aes_gcm_open_to` with the interleaved path and the path for short
records (`sh`), `work` the stack argument `w`, for a `tb` that writes the
table without `H'` (`TbForOP`), in one pass. -/
theorem openToWithSh_wp (v : GcmImpl) (cl : Prog isa) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) (gh : Gh8Ok)
    {tb : List Instr} {w : Nat} (hw : w = 4 ∨ w = 5) {extra extraW : List Region}
    {s : State} (hs : openToPreXW w extra s extraW)
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg s w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg s w)) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [workR (stackArg s w), ⟨stackArg s 0, (s.gpr .x7).toNat⟩] s.mem s'.mem →
      WP isa cl s' (GhPost s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb))
    (htb : TbForOP tb (s.gpr .x0) (stackArg s w) s.sp (stackArg s 0) (s.gpr .x7).toNat s) :
    WP isa (Impl.AesGcm.AArch64.Stitch.openWithSG v.callees true w tb cl true) s fun s' =>
      GprAbi s s' ∧ openToPostOf s s' := by
  rw [openWithSG_eq]
  refine WP.seq (WP.mono (WP.gprs (rs := [.x4, .x5, .x6, .x7]) (openEntryTo_ok (by omega) hs)
    (by rcases hw with rfl | rfl <;> decide) (by rcases hw with rfl | rfl <;> decide))
    fun s₁ ⟨⟨o₁, x12₁⟩, hx₁⟩ => ?_)
  exact WP.mono (openSelS_wp v cl hMK gh o₁ x12₁ hx₁ hgh htb) fun _ h => h

end VG.Proof.AesGcm.AArch64.Fast
