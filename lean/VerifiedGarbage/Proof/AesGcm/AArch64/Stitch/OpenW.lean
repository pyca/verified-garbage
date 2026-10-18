module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Open
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Tables
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal

/-!
# AES-GCM on AArch64, interleaved: `open`'s code with the interleaved loops (`openWithS`)

Untrusted: everything here is checked by Lean. `openRunWithS` is `openRunAS`
then `omBS` (`openRunWithS_split`), which together leave `OpenPost`, as
`openRunWithP` does (`openRunWithS_postX`); then `openWithS` as `openWithE`
(`openWithSX_wp`, `openWithS_wp`), for any `tb` that writes the table of keys.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxH ctxCiph)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

/-- What `tb` must do, in `open` from `s₀`: write the table of keys of the
context's hash subkey (`Stitch.TblPost`). -/
def TbForO (tb : List Instr) (Ctx W SP D : Addr) (n : Nat) (s₀ : State) : Prop :=
  ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = s₀.rd → u.wr = s₀.wr →
    Frame [workR W, ⟨D, n⟩] s₀.mem u.mem → KeyAt (Spec.Gcm.ctxH s₀.mem Ctx) u.mem W →
    WP isa (.block tb) u (Stitch.TblPost W (Spec.Gcm.ctxH s₀.mem Ctx) u)

/-- `openRunWith_postX` for `openRunWithS`. -/
theorem openRunWithS_postX (v : GcmImpl) (cl : Prog isa) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) (gh : Gh8Ok)
    {tb : List Instr} {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat}
    {s₀ t : State} {ex : List Region} {I : Mem → Prop} (o : OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ t)
    (h12 : nl = 12)
    (h4 : t.gpr .x4 = A) (h5 : t.gpr .x5 = BitVec.ofNat 64 al) (h6 : t.gpr .x6 = D)
    (h7 : t.gpr .x7 = BitVec.ofNat 64 n) (hal : al ≤ 16) (hT₃ : bytesAt t.mem W tl = bytesAt s₀.mem Tg tl)
    (hok : Spec.Gcm.tagLenOk tl = true)
    (hexW : ∀ r ∈ ex, (workR W).Disjoint r) (hexD : ∀ r ∈ ex, (⟨D, n⟩ : Region).Disjoint r)
    (hexC : ∀ r ∈ ex, (⟨Ctx, 256⟩ : Region).Disjoint r)
    (hI : ∀ {m m' : Mem}, I m → Frame [workR W, ⟨D, n⟩] m m' → I m')
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) →
      s'.rd = s₀.rd → s'.wr = s₀.wr → s'.sp = SP → Frame [workR W, ⟨D, n⟩] s₀.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      WP isa cl s' fun u => GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex ∧ I u.mem)
    (htb : TbForO tb Ctx W SP D n s₀) :
    WP isa (Impl.AesGcm.AArch64.Stitch.openRunWithS v.callees tb cl) t fun u =>
      OpenPost Ctx W SP Np A D Tg R nl al n tl s₀ u ∧ I u.mem := by
  subst h12
  have L := o.lay
  have F₀ : Frame [workR W, ⟨D, n⟩] s₀.mem t.mem :=
    o.fr.sub fun r hr => ⟨_, List.mem_cons_self .., entry16_work W r hr⟩
  obtain ⟨hc₃, hH₃, hN₃, hA₃, hD₃⟩ := o.vals
  refine (openRunWithS_split v.callees cl tb).symm.wp (WP.seq (WP.mono (openRunASX_ok cl v hMK gh o h4 h5 h6 h7
    hal hok hexW hexD hexC (fun hi f => hI hi (f.sub fun r hr => ⟨workR W, List.mem_cons_self .., by
      simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩))
    (fun s' _ _ _ _ hc sY sS hrd hwr hsp hf hd => hgh s' hc sY sS (hrd.trans o.rd₀) (hwr.trans o.wr₀) hsp
      (F₀.trans hf) hd)
    (fun u he hrd hwr hf key => by
      rw [hH₃] at key ⊢
      exact htb u he (hrd.trans o.rd₀) (hwr.trans o.wr₀) (F₀.trans hf) key))
    fun _ ⟨mo, i₇⟩ => WP.mono (omBS_ok L v o.rounds mo) fun s₄ ⟨hpost, f₈⟩ => ?_))
  have I₄ : I s₄.mem := hI i₇ (f₈.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self .., stW (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩)
  obtain ⟨he₄, x0₄, d₄⟩ := hpost
  have F₄ := (mo.frame.mono fun r hr => List.mem_append_left _ hr).trans
    (f₈.mono fun r hr => List.mem_append_right (⟨D, Stitch.pre n⟩ :: (fastFrame W ++ ex)) hr)
  refine ⟨⟨he₄, o.sv.frame F₄ fun r hr => ?_, ?_⟩, I₄⟩
  · rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_cons.mp hr with h | hr
      · subst h
        exact ((o.ddW.sub_left (Region.sub_prefix (Nat.mul_div_le n 128))).sub_right (Lay.wSub (by decide))).symm
      rcases List.mem_append.mp hr with hr | hr
      · exact saved_fastFrame W r hr
      · exact (hexW r hr).sub_left (Lay.wSub (by decide))
    · exact saved_crFrame L o.dat r hr
  · rw [hc₃, hH₃, hN₃, hA₃, hD₃, hT₃] at x0₄ d₄
    rw [Spec.Gcm.openResult, ite_eq_left hok, Spec.Gcm.decryptWith]
    by_cases hc : (Spec.Gcm.fullTag (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12)
        (bytesAt s₀.mem A al) (bytesAt s₀.mem D n)).take tl = bytesAt s₀.mem Tg tl
    · rw [ite_eq_left hc]
      simp only [hc, decide_true, ite_true] at x0₄ d₄
      exact ⟨by rw [x0₄]; rfl, d₄⟩
    · rw [ite_eq_right hc]
      simp only [hc, decide_false, Bool.false_eq_true, ite_false] at x0₄ d₄
      exact ⟨by rw [x0₄]; rfl, d₄⟩

/-- `openWithEX_wp` for `openWithS`. -/
theorem openWithSX_wp (v : GcmImpl) (cl : Prog isa) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) (gh : Gh8Ok)
    {tb : List Instr} {w : Nat} (hw : w = 2 ∨ w = 3) {extra extraW : List Region}
    {s : State} {ex : List Region} {I : Mem → Prop} (hs : openPreXW w extra s extraW)
    (hc : (s.gpr .x5).toNat ≤ 16 ∧ (s.gpr .x3).toNat = 12) (htl : Spec.Gcm.tagLenOk (stackArg s 1).toNat = true)
    (hexW : ∀ r ∈ ex, (workR (stackArg s w)).Disjoint r)
    (hexD : ∀ r ∈ ex, (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region).Disjoint r)
    (hexC : ∀ r ∈ ex, (⟨s.gpr .x0, 256⟩ : Region).Disjoint r)
    (hI : ∀ {m m' : Mem}, I m → Frame [workR (stackArg s w), ⟨s.gpr .x6, (s.gpr .x7).toNat⟩] m m' → I m')
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg s w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg s w)) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [workR (stackArg s w), ⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region) →
      WP isa cl s' fun u => GhPost s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb u ex ∧ I u.mem)
    (htb : TbForO tb (s.gpr .x0) (stackArg s w) s.sp (s.gpr .x6) (s.gpr .x7).toNat s) :
    WP isa (Impl.AesGcm.AArch64.Stitch.openWithS v.callees (8 * w) tb cl) s fun s' =>
      (GprAbi s s' ∧ openAArch64.post s s') ∧ I s'.mem := by
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
  refine WP.ite true (by rw [eval_zero x10₂ (by split <;> decide)]; simp [hc]) (fun _ => ?_) (fun h => by cases h)
  unfold Impl.AesGcm.AArch64.Stitch.openFastS
  refine openRestWithX_wp o₂ x12₂ htl fun o' hT hx' => ?_
  have hx (r : Reg) (hr : r ∈ [Reg.x4, .x5, .x6, .x7]) := (hx' r hr).trans (hx₂ r hr)
  exact openRunWithS_postX v cl hMK gh o' hc.2 (hx .x4 (by simp)) (by rw [hx .x5 (by simp), ofNat_toNat'])
    (hx .x6 (by simp)) (by rw [hx .x7 (by simp), ofNat_toNat']) hc.1 hT htl hexW hexD hexC hI hgh htb

/-- `openWithE_wp` for `openWithS`. -/
theorem openWithS_wp (v : GcmImpl) (cl : Prog isa) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) (gh : Gh8Ok)
    {tb : List Instr} {w : Nat} (hw : w = 2 ∨ w = 3) {extra extraW : List Region}
    {s : State} (hs : openPreXW w extra s extraW)
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg s w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg s w)) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [workR (stackArg s w), ⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.mem s'.mem →
      WP isa cl s' (GhPost s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb))
    (htb : TbForO tb (s.gpr .x0) (stackArg s w) s.sp (s.gpr .x6) (s.gpr .x7).toNat s) :
    WP isa (Impl.AesGcm.AArch64.Stitch.openWithS v.callees (8 * w) tb cl) s fun s' =>
      GprAbi s s' ∧ openAArch64.post s s' := by
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
    unfold Impl.AesGcm.AArch64.Stitch.openFastS
    refine openRestWith_wp o₂ x12₂ fun o' hT hok hx' => ?_
    have hx (r : Reg) (hr : r ∈ [Reg.x4, .x5, .x6, .x7]) := (hx' r hr).trans (hx₂ r hr)
    exact WP.mono (openRunWithS_postX v cl hMK gh (ex := []) (I := fun _ => True) o' hc.2 (hx .x4 (by simp))
      (by rw [hx .x5 (by simp), ofNat_toNat']) (hx .x6 (by simp)) (by rw [hx .x7 (by simp), ofNat_toNat']) hc.1 hT
      hok (by simp) (by simp) (by simp) (fun _ _ => trivial)
      (fun s' _ _ _ _ hc sY sS hr hw hsp hf _ => WP.mono (hgh s' hc sY sS hr hw hsp hf) fun _ g => ⟨g, trivial⟩)
      htb) fun _ q => q.1
  · refine WP.ite false (by rw [eval_zero x10₂ (by split <;> decide)]; simp [hc]) (fun h => by cases h) (fun _ => ?_)
    exact openRestWith_wp o₂ x12₂ fun o' hT hok _ => openMain_post v o' hT hok

/-- `powTbl` writes the table, in `open`. -/
theorem powTbl_forO (hP : Proof.Gcm.AArch64.Pmull.PrepPow) (Ctx W SP D : Addr) (n : Nat) (s : State) :
    TbForO Impl.AesGcm.AArch64.Stitch.powTbl Ctx W SP D n s :=
  fun _ he _ _ _ key => Stitch.powTbl_ok hP he key

end VG.Proof.AesGcm.AArch64.Fast
