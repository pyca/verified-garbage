module

public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.OneShot
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Cmp
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Fn
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Save

/-!
# SM4-GCM on AArch64: `vg_sm4_gcm_seal`

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/AArch64/Seal.lean`): the entry and `front_ok` start the state
at `W + 16` and absorb the additional data, and keep `tag` (`x7`) at
`W + 248`; `encBody` encrypts the data and absorbs the ciphertext, `finBody 0`
writes the tag to `W`, and `tagOut` copies it to `tag` (`seal_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO dataO lenO tlO mov ptr imm restore tagOut)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput inc32 gctr)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Spec.Gcm (ctxH)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

theorem slots_bodyFrame {D : Addr} {n : Nat} (hd : (⟨D, n⟩ : Region).Disjoint (workR W)) :
    ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W SP D n, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hd.sub_right (Lay.wSub (by decide))).symm
      · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
      · exact (L.stk_w (by decide)).symm
  · exact slots_absFrame L r hr

theorem saved_bodyFrame {D : Addr} {n : Nat} (hd : (⟨D, n⟩ : Region).Disjoint (workR W)) :
    ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W SP D n, (savedR W).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · exact saved_tFrame L (.inr rfl) r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hd.sub_right (Lay.wSub (by decide))).symm
      · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
      · exact (L.stk_w (by decide)).symm
  · exact saved_absFrame L (.inr rfl) r hr

theorem st0_bodyFrame {D : Addr} {n : Nat} (hd : (⟨D, n⟩ : Region).Disjoint (workR W)) :
    ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W SP D n, (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact st0_disj L (by decide) (by decide)
      · exact st0_w L ⟨by decide, by decide⟩
      · exact st0_w L ⟨by decide, by decide⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hd.sub_right (Lay.wSub (by decide))).symm
      · exact st0_disj L (by decide) (by decide)
      · exact (L.stk_w (by decide)).symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact st0_disj L (by decide) (by decide)
    · exact st0_disj L (by decide) (by decide)
    · exact st0_w L ⟨by decide, by decide⟩

end

theorem ofNat_toNat' (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `finPrep`: the lengths from their slots. -/
theorem finPrep_ok {s : State} {W : Addr} (h19 : s.gpr .x19 = W) (hr : Covers [⟨W, 768⟩] (s.rd ++ s.wr))
    {al n : Nat} (sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (sN : s.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n) :
    WP isa (.block finPrep) s fun s' => s'.gpr .x26 = BitVec.ofNat 64 al ∧ s'.gpr .x27 = BitVec.ofNat 64 n ∧
      Regs [.x26, .x27] s s' := by
  have q₁ := in_off hr (show 224 + 8 ≤ 768 by decide) (by decide)
  have q₂ := in_off hr (show 240 + 8 ≤ 768 by decide) (by decide)
  refine WP.run ⟨_, by simp only [finPrep]; arun [h19, q₁, q₂], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
    rw [show s.mem.read (W + 224#64) 8 = s.mem.readW (W + BitVec.ofNat 64 224) 64 from rfl, sL]; rfl
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
    rw [show s.mem.read (W + 240#64) 8 = s.mem.readW (W + BitVec.ofNat 64 240) 64 from rfl, sN]; rfl

/-- The load of the slot at `W + 248` into `x28`. -/
theorem ldr28_ok {Ctx W SP : Addr} {V : BitVec 64} {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (sT : s.mem.readW (W + BitVec.ofNat 64 248) 64 = V) :
    WP isa (.block [.ldr .x .x28 .x19 tlO]) s fun s' => s'.gpr .x28 = V ∧ Regs [.x28] s s' := by
  have q := he.perm.wR (show 248 + 8 ≤ 768 by decide)
  refine WP.run ⟨_, by arun [he.x19, q], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
  rw [show s.mem.read (W + 248#64) 8 = s.mem.readW (W + BitVec.ofNat 64 248) 64 from rfl, sT]; rfl

/-- `x7` kept at `W + 248` and in `x28`. -/
theorem stash7_ok {s : State} {W : Addr} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 768⟩] s.wr) :
    WP isa (.block [.str .x .x7 .x19 tlO, mov .x28 .x7]) s fun s' =>
      s'.gpr .x28 = s.gpr .x7 ∧ s'.mem = s.mem.writeW (W + BitVec.ofNat 64 248) (s.gpr .x7) ∧
      Others [.x28] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have w := in_off hw (show 248 + 8 ≤ 768 by decide) (by decide)
  refine WP.run ⟨_, by arun [h19, w], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨by simp [gpr_write], ?_, by others_tac, rfl, rfl, rfl⟩
  simp only [mem_write, Mem.writeW, gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]

/-- `sealPre`'s common arguments. -/
theorem sealCore {s : State} (hs : sealPre s) : oneCore 1 0 s := by
  simp only [sealPre] at hs
  sig_split hs
  rename_i hsp hrd hwr dcd dct dcw dnd dnt dnw dad dat daw ddt ddw dda dtw dta dwa kc kn ka kd kt kw wc wn wa wd
    wt ww
  have wsp := hs
  clear hs
  exact ⟨by rw [hrd]; simp, by rw [hrd]; simp, by rw [hrd]; simp, by rw [hrd]; simp, by rw [hwr]; simp,
    by rw [hwr]; simp, dcd, dcw, dnd, dnw, dad, daw, ddw, dda, dwa, kc, kn, ka, kd, kw, wc, wn, wa, wd, ww,
    by omega, hsp⟩

/-- What `sealPre` gives. -/
theorem sealLay {s : State} (hs : sealPre s) :
    OneLay s 1 0 ∧ Covers [⟨s.gpr .x7, 16⟩] s.wr ∧
      (⟨s.gpr .x7, 16⟩ : Region).Disjoint (workR (stackArg s 0)) ∧
      (⟨s.gpr .x5, (s.gpr .x6).toNat⟩ : Region).Disjoint ⟨s.gpr .x7, 16⟩ := by
  have hs' := hs
  simp only [sealPre] at hs'
  obtain ⟨-, -, hwr, -, -, -, -, -, -, -, -, -, ddt, -, -, dtw, -⟩ := hs'
  exact ⟨oneLay (sealCore hs), covers_of_mem (by rw [hwr]; simp), dtw, ddt⟩

/-- What the entry of `seal` leaves, from `s`. -/
structure SealEntry (s s₁ : State) : Prop where
  env : Env (s.gpr .x0) (stackArg s 0 + BitVec.ofNat 64 16) (stackArg s 0) s.sp s₁
  x23 : s₁.gpr .x23 = s.gpr .x1
  x24 : s₁.gpr .x24 = s.gpr .x2
  x26 : s₁.gpr .x26 = s.gpr .x2
  x27 : s₁.gpr .x27 = 0
  x28 : s₁.gpr .x28 = s.gpr .x7
  sA : s₁.mem.readW (stackArg s 0 + BitVec.ofNat 64 216) 64 = s.gpr .x3
  sL : s₁.mem.readW (stackArg s 0 + BitVec.ofNat 64 224) 64 = s.gpr .x4
  sD : s₁.mem.readW (stackArg s 0 + BitVec.ofNat 64 232) 64 = s.gpr .x5
  sN : s₁.mem.readW (stackArg s 0 + BitVec.ofNat 64 240) 64 = s.gpr .x6
  sT : s₁.mem.readW (stackArg s 0 + BitVec.ofNat 64 248) 64 = s.gpr .x7
  frame : Frame [entryR (stackArg s 0)] s.mem s₁.mem
  saved : SavedAt s₁.mem (stackArg s 0) s
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

/-- The entry of `seal`. -/
theorem sealEntry_ok {s : State} (hs : sealPre s) :
    WP isa (.block (oneEntry 0 ++ ([.str .x .x7 .x19 tlO, mov .x28 .x7] : List Instr))) s (SealEntry s) := by
  obtain ⟨ol, -, -, -⟩ := sealLay hs
  have hW0 : s.mem.readW (s.sp + BitVec.ofNat 64 0) 64 = stackArg s 0 := rfl
  refine WP.block_append (WP.mono (oneEntry_ok (by decide) hW0 (ol.hsp 0 (by omega)) rfl ol.perm)
    fun s₁ ⟨he₁, x23₁, x24₁, x26₁, x27₁, x7₁, sl₁, sl₂, sl₃, sl₄, f₁, sv₁, rd₁, wr₁⟩ =>
      WP.mono (stash7_ok he₁.x19 he₁.perm.w) fun s₂ ⟨x28₂, m₂, og₂, sp₂, rd₂, wr₂⟩ => ?_)
  have so (d : Nat) (hd : d + 8 ≤ 248) : s₂.mem.readW (stackArg s 0 + BitVec.ofNat 64 d) 64 =
      s₁.mem.readW (stackArg s 0 + BitVec.ofNat 64 d) 64 := by
    rw [m₂, readW_writeW_other _ _ _ (.inl hd) (by omega) (by decide)]
  have g₂ : ∀ r ∈ [Reg.x7, .x23, .x24, .x26, .x27], s₂.gpr r = s₁.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact og₂ r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨he₁.keep (fun r hr => og₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₂ rd₂ wr₂,
    by rw [g₂ .x23 (by simp), x23₁], by rw [g₂ .x24 (by simp), x24₁],
    by rw [g₂ .x26 (by simp), x26₁], by rw [g₂ .x27 (by simp), x27₁], by rw [x28₂, x7₁],
    by rw [so 216 (by decide), sl₁], by rw [so 224 (by decide), sl₂], by rw [so 232 (by decide), sl₃],
    by rw [so 240 (by decide), sl₄], by rw [m₂, Mem.readW_writeW_self64, x7₁], ?_, ?_, by rw [rd₂, rd₁],
    by rw [wr₂, wr₁]⟩
  · rw [m₂]; exact f₁.writeW (List.mem_singleton_self _) _ (entry_contains _ (by decide) (by decide))
  · rw [m₂]
    exact sv₁.frame (rs := [⟨stackArg s 0 + BitVec.ofNat 64 248, 8⟩])
      ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))

/-- `seal` after its entry. -/
theorem sealRest_ok (v : GcmImpl) {s s₁ : State} (hs : sealPre s) (h₁ : SealEntry s s₁) :
    WP isa (sealRest v.callees) s₁ fun s' => GprAbi s s' ∧ sealAArch64.post s s' := by
  obtain ⟨he₁, x23₁, x24₁, x26₁, x27₁, _, sl₁, sl₂, sl₃, sl₄, sl₅, f₁, sv₁, rd₁, wr₁⟩ := h₁
  obtain ⟨ol, tW, dtw, ddt⟩ := sealLay hs
  simp only [sealAArch64]
  obtain ⟨L, perm, hsp, dnW, daW, ddW, dcW, daA, dnd, dad, dcd, wn, wa, wd, kn, ka, kd, nR, aR, dW⟩ := ol
  have h2 := ofNat_toNat' (s.gpr .x2)
  have h4 := ofNat_toNat' (s.gpr .x4)
  have h6 := ofNat_toNat' (s.gpr .x6)
  generalize hW : stackArg s 0 = W at *
  generalize hTg : s.gpr .x7 = Tg at *
  generalize hCtx : s.gpr .x0 = Ctx at *
  generalize hNp : s.gpr .x1 = Np at *
  generalize hnl : (s.gpr .x2).toNat = nl at *
  generalize hA : s.gpr .x3 = A at *
  generalize hal : (s.gpr .x4).toNat = al at *
  generalize hD : s.gpr .x5 = D at *
  generalize hn : (s.gpr .x6).toNat = n at *
  generalize hSP : s.sp = SP at *
  have hnlt : n < 2 ^ 64 := hn ▸ (s.gpr .x6).isLt
  unfold sealRest
  rw [← h4] at sl₂
  rw [← h6] at sl₄
  have sub16 : Region.Sub ⟨W + BitVec.ofNat 64 16, 80⟩ (workR W) := Lay.wSub (by decide)
  have kc := keep_of_sub (entryR_work W) (dcW.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide)))
  have hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := blockAt_frame f₁ kc
  have hnon : DataOk (W + BitVec.ofNat 64 16) W s₁ Np nl :=
    ⟨by rw [rd₁, wr₁]; exact nR, hnl ▸ (s.gpr .x2).isLt, wn, dnW.sub_right sub16, dnW⟩
  have haad : DataOk (W + BitVec.ofNat 64 16) W s₁ A al :=
    ⟨by rw [rd₁, wr₁]; exact aR, hal ▸ (s.gpr .x4).isLt, wa, daW.sub_right sub16, daW⟩
  have iv₁ : bytesAt s₁.mem Np nl = bytesAt s.mem Np nl :=
    bytesAt_frame f₁ (keep_of_sub (entryR_work W) dnW) (by omega)
  have a₁ : bytesAt s₁.mem A al = bytesAt s.mem A al :=
    bytesAt_frame f₁ (keep_of_sub (entryR_work W) daW) (by omega)
  refine front_ok L v he₁ (fun _ _ => rfl : Kept s₁.gpr s₁) x23₁ (by rw [x24₁, ← h2])
    (by rw [x26₁, ← h2]) x27₁ hnon haad hH₁ sl₁ sl₂ sl₃ sl₄ fun s₂ h₂ => ?_
  rw [iv₁, a₁] at h₂
  have hdat₂ : DataW Ctx (W + BitVec.ofNat 64 16) W SP s₂ D n :=
    ⟨⟨covers_left (by rw [h₂.wr, wr₁]; exact dW), hnlt, wd, ddW.sub_right sub16, ddW⟩,
      by rw [h₂.wr, wr₁]; exact dW, dcd, kd⟩
  have hB : BodyIn Ctx (W + BitVec.ofNat 64 16) W SP s₂.gpr n 0 D (bytesAt s.mem A al) [] (ctxH s.mem Ctx) s₂ :=
    ⟨h₂.env, fun _ _ => rfl, h₂.x25, h₂.x26, h₂.x27, h₂.x28, rfl, by decide, hdat₂, h₂.hH⟩
  refine WP.seq (WP.mono (WP.with_rdwr (encBody_ok L v hB (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx)
    (bytesAt s.mem Np nl))))) fun s₃ ⟨h₃, rd₃, wr₃⟩ => ?_)
  obtain ⟨o₁, o₂, o₃⟩ := h₃.post h₂.abs (Proof.Gcm.ctr_zero _ _ _ _ h₂.cb)
  have slot₃ : ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂' => by
    rw [slot_kept h₃.frame (slots_bodyFrame L ddW) h₁ h₂', slot_kept h₂.frame (slots_frontFrame L) h₁ h₂']
  refine WP.seq (WP.mono (finPrep_ok (al := al) (n := n) h₃.env.x19 (covers_left h₃.env.perm.w)
    (by rw [slot₃ 224 (by decide) (by decide), sl₂]) (by rw [slot₃ 240 (by decide) (by decide), sl₄]))
    fun s₄ ⟨x26₄, x27₄, r₄⟩ => ?_)
  have he₄ := h₃.env.of_regs r₄
  refine WP.seq (WP.mono (ldr28_ok (V := Tg) he₄ (by rw [r₄.mem, slot₃ 248 (by decide) (by decide), sl₅]))
    fun s₄' ⟨x28₄', r₄'⟩ => ?_)
  have he₄' := he₄.of_regs r₄'
  have x26₄' : s₄'.gpr .x26 = BitVec.ofNat 64 al := by rw [r₄'.others _ (by decide), x26₄]
  have x27₄' : s₄'.gpr .x27 = BitVec.ofNat 64 n := by rw [r₄'.others _ (by decide), x27₄]
  have m₄ : s₄'.mem = s₃.mem := by rw [r₄'.mem, r₄.mem]
  have kcd : ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W SP D n, (⟨Ctx, 256⟩ : Region).Disjoint r :=
    keep_body dcW dcd L.kc.symm
  have hc₃ : ciphOf s₃.mem Ctx = ciphOf s.mem Ctx := by
    rw [ciph_frame h₃.frame kcd, ciph_frame h₂.frame (keep_of_sub (frontFrame_work W) dcW),
      ciph_frame f₁ (keep_of_sub (entryR_work W) dcW)]
  have hD₂ : bytesAt s₂.mem D n = bytesAt s.mem D n := by
    rw [bytesAt_frame h₂.frame (keep_of_sub (frontFrame_work W) ddW) (by omega),
      bytesAt_frame f₁ (keep_of_sub (entryR_work W) ddW) (by omega)]
  have hc₂ : ciphOf s₂.mem Ctx = ciphOf s.mem Ctx := by
    rw [ciph_frame h₂.frame (keep_of_sub (frontFrame_work W) dcW),
      ciph_frame f₁ (keep_of_sub (entryR_work W) dcW)]
  have hH₄ : blockAt s₄'.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [m₄, blockAt_frame h₃.frame fun r hr => (kcd r hr).sub_left (Lay.ctxSub (by decide)), h₂.hH]
  have hlen : ([] ++ xorKs (ciphOf s₂.mem Ctx) (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl))) 0
      (bytesAt s₂.mem D n)).length = n := by
    rw [List.nil_append, Proof.Gcm.length_xorKs, length_bytesAt]
  refine WP.seq (WP.mono (WP.with_rdwr (finBody_ok L v (.inl rfl) (a := bytesAt s.mem A al) (H := ctxH s.mem Ctx)
    (c := [] ++ xorKs (ciphOf s₂.mem Ctx) (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl))) 0
      (bytesAt s₂.mem D n))
    he₄' (fun _ _ => rfl) (by rw [x26₄', length_bytesAt]) (by rw [x27₄', hlen]) (by rw [hlen]; exact hnlt)
    hH₄)) fun s₅ ⟨⟨he₅, hk₅, f₅, out₅⟩, _, wr₅⟩ => ?_)
  have sv₅ : SavedAt s₅.mem W s := by
    have := (sv₁.frame h₂.frame (saved_frontFrame L)).frame h₃.frame (saved_bodyFrame L ddW)
    rw [← m₄] at this
    exact this.frame f₅ (saved_finFrame L (.inl rfl))
  have x28₅ : s₅.gpr .x28 = Tg := by rw [hk₅ .x28 (by decide), x28₄']
  have wr₅' : s₅.wr = s.wr := by rw [wr₅, r₄'.wr, r₄.wr, wr₃, h₂.wr, wr₁]
  refine WP.seq (WP.mono (tagOut_ok he₅.x19 x28₅ (covers_left he₅.perm.w) (by rw [wr₅']; exact tW)
    (dtw.sub_right (Region.sub_prefix (by decide)))) fun s₆ ⟨out₆, f₆, og₆, sp₆, rd₆, wr₆⟩ => ?_)
  have he₆ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₆ := he₅.keep (fun r hr => og₆ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₆ rd₆ wr₆
  have sv₆ : SavedAt s₆.mem W s := sv₅.frame f₆ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (dtw.sub_right (Lay.wSub (by decide))).symm
  refine WP.mono (exit_ok he₆.x19 (by rw [he₆.sp, hSP]) (covers_left he₆.perm.w) sv₆)
    fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  rw [hm]
  have hdata : bytesAt s₆.mem D n = gctr (ctxCiph s.mem Ctx)
      (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl))) (bytesAt s.mem D n) := by
    rw [bytesAt_frame f₆ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ddt) (by omega),
      bytesAt_frame f₅ (keep_fin (.inl rfl) ddW kd.symm) (by omega), m₄, o₃, hc₂, hD₂,
      Proof.Gcm.gctr_eq]
    rfl
  have hj₄ : blockAt s₄'.mem (W + BitVec.ofNat 64 16) = Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl) := by
    rw [m₄, blockAt_frame h₃.frame (st0_bodyFrame L ddW), h₂.j0]
  have htag := out₅ (by rw [m₄]; exact o₁)
  rw [add_ofNat_zero, m₄, hc₃, ← m₄, hj₄] at htag
  have he : [] ++ xorKs (ciphOf s₂.mem Ctx) (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl))) 0
      (bytesAt s₂.mem D n) = gctr (ctxCiph s.mem Ctx)
        (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl))) (bytesAt s.mem D n) := by
    rw [List.nil_append, hc₂, hD₂, Proof.Gcm.gctr_eq]; rfl
  rw [he] at htag
  rw [hdata, out₆, htag, Spec.Gcm.encryptWith, Proof.Gcm.fullTag_eq,
    List.take_of_length_le (by rw [Proof.Cmac.toBytes_length])]
  rfl

theorem seal_wp (v : GcmImpl) {s : State} (hs : sealAArch64.pre s) :
    WP isa («seal» v.callees) s fun s' => GprAbi s s' ∧ sealAArch64.post s s' :=
  WP.seq (WP.mono (sealEntry_ok hs) fun _ h₁ => sealRest_ok v hs h₁)

end VG.Proof.Sm4Gcm.AArch64
