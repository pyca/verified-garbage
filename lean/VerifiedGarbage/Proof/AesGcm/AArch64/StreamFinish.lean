import VerifiedGarbage.Proof.AesGcm.AArch64.FinTag
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamCrypt

/-!
# AES-GCM on AArch64: `vg_aes_gcm_stream_finish`

Untrusted: everything here is checked by Lean. The entry saves our caller's
registers, keeps the lengths in `x26` and `x27` (`finEntry_ok`) and `tag`
in `x28` (`finishEntry_ok`); `finBody 0` writes the tag to `W`, for any
message of those lengths (`WP.forall_det`), and `tagOut` copies it to
`tag`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks ghashInput StreamRepr ofBytes toBytes ctxCiph ctxH)
open VG.Proof.Gcm (Absorbed lensBlock padded)

/-- After the entry, with `work` in `w`: the lengths. -/
theorem finEntry_ok {s : State} {Ctx St W : Addr} {w : Reg} (hCtx : s.gpr .x0 = Ctx) (hSt : s.gpr .x2 = St)
    (hW : s.gpr w = W) (hperm : Perm Ctx St W s) :
    WP isa (.block (finEntry w)) s fun s' => Env Ctx St W s.sp s' ∧ Kept s'.gpr s' ∧
      s'.gpr .x22 = BitVec.ofNat 64 (s.gpr .x1).toNat ∧ s'.gpr .x26 = s.gpr .x3 ∧ s'.gpr .x27 = s.gpr .x4 ∧
      s'.gpr .x5 = s.gpr .x5 ∧ s'.gpr .x6 = s.gpr .x6 ∧ s'.mem = savedMem s.mem W s.gpr ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s w hW hperm.w
  obtain ⟨s₂, run₂, x19₂, x20₂, x21₂, x22₂, x26₂, x27₂, x5₂, x6₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 w, mov .x20 .x2, mov .x21 .x0, mov .x22 .x1, mov .x26 .x3, mov .x27 .x4] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x20 = St ∧ s₂.gpr .x21 = Ctx ∧
      s₂.gpr .x22 = BitVec.ofNat 64 (s.gpr .x1).toNat ∧ s₂.gpr .x26 = s.gpr .x3 ∧ s₂.gpr .x27 = s.gpr .x4 ∧
      s₂.gpr .x5 = s.gpr .x5 ∧ s₂.gpr .x6 = s.gpr .x6 ∧ s₂.sp = s₁.sp ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩ <;> simp [gpr_write, g₁, hW, hSt, hCtx]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  exact ⟨⟨x19₂, x20₂, x21₂, by rw [sp₂, sp₁], hperm.of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])⟩,
    fun _ _ => rfl, x22₂, x26₂, x27₂, x5₂, x6₂, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

/-- The entry of `finish`: `tag` in `x28`. -/
theorem finishEntry_ok {s : State} {Ctx St W : Addr} (hCtx : s.gpr .x0 = Ctx) (hSt : s.gpr .x2 = St)
    (hW : s.gpr .x6 = W) (hperm : Perm Ctx St W s) :
    WP isa (.block (finEntry .x6 ++ [mov .x28 .x5])) s fun s' => Env Ctx St W s.sp s' ∧ Kept s'.gpr s' ∧
      s'.gpr .x22 = BitVec.ofNat 64 (s.gpr .x1).toNat ∧ s'.gpr .x26 = s.gpr .x3 ∧ s'.gpr .x27 = s.gpr .x4 ∧
      s'.gpr .x28 = s.gpr .x5 ∧ s'.mem = savedMem s.mem W s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.block_append (WP.mono (finEntry_ok hCtx hSt hW hperm)
    fun s₁ ⟨he₁, _, x22₁, x26₁, x27₁, x5₁, _, m₁, rd₁, wr₁⟩ => ?_)
  refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  have r : Regs [.x28] s₁ (s₁.write .x .x28 (s₁.gpr .x5 + BitVec.ofNat 64 0)) :=
    ⟨by others_tac, rfl, rfl, rfl, rfl⟩
  exact ⟨he₁.of_regs r, fun _ _ => rfl, by rw [r.others _ (by decide), x22₁],
    by rw [r.others _ (by decide), x26₁], by rw [r.others _ (by decide), x27₁], by simp [gpr_write, x5₁],
    by rw [r.mem, m₁], by rw [r.rd, rd₁], by rw [r.wr, wr₁]⟩

/-- What `finPre` gives. -/
theorem lay_of_fin {s : State} (hs : finPre s) :
    Lay (s.gpr .x0) (s.gpr .x2) (s.gpr .x6) ∧ Perm (s.gpr .x0) (s.gpr .x2) (s.gpr .x6) s ∧
      rounds (s.gpr .x1) ∧ Covers [⟨s.gpr .x5, 16⟩] s.wr ∧
      (⟨s.gpr .x5, 16⟩ : Region).Disjoint ⟨s.gpr .x6, 2560⟩ := by
  simp only [finPre] at hs
  obtain ⟨hrd, hwr, dcs, -, dcw, -, dsw, dtw, wc, ws, -, ww, hR⟩ := hs
  exact ⟨Lay.of wc ws ww dcs dcw dsw,
    ⟨covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩, hR,
    covers_of_mem (by rw [hwr]; simp), dtw⟩

/-- What writes to the parts `rs` of `W` keep, outside the state. -/
theorem fin_inv {Ctx St W : Addr} (L : Lay Ctx St W) {rs : List Region}
    (hrs : ∀ r ∈ rs, (⟨St, 80⟩ : Region).Disjoint r ∧ Region.Sub r ⟨W, 2560⟩) {m₀ m : Mem} (hf : Frame rs m₀ m)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) {x : List Byte} :
    ciphOf m Ctx R = ciphOf m₀ Ctx R ∧ blockAt m St = blockAt m₀ St ∧
      blockAt m (Ctx + BitVec.ofNat 64 240) = ctxH m₀ Ctx ∧
      (Absorbed m₀ (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (ctxH m₀ Ctx) x →
        Absorbed m (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (ctxH m₀ Ctx) x) :=
  ⟨ciph_frame hf (fun r hr => L.cw'.sub_right (hrs r hr).2) hR,
    blockAt_frame hf (fun r hr => (hrs r hr).1.sub_left (Region.sub_prefix (by decide))),
    blockAt_frame hf (fun r hr => (L.cw'.sub_left (Lay.ctxSub (by decide))).sub_right (hrs r hr).2),
    fun ha => Absorbed.frame hf (fun r hr => (hrs r hr).1.sub_left (Lay.stSub (by decide))) ha⟩

/-- The saved registers' slots are parts of `W` outside the state. -/
theorem savedR_inv {Ctx St W : Addr} (L : Lay Ctx St W) :
    ∀ r ∈ [savedR W], (⟨St, 80⟩ : Region).Disjoint r ∧ Region.Sub r ⟨W, 2560⟩ := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨L.sb.sub_right (Lay.bSub (by decide) (by decide)), Lay.wSub (by decide)⟩

/-- One run of `stream_finish`, for a message `a`, `c` of those lengths. -/
theorem fin_run (v : GcmImpl) {s : State} (hs : streamFinishAArch64.pre s) {a c : List Byte}
    (h3 : s.gpr .x3 = BitVec.ofNat 64 a.length) (h4 : s.gpr .x4 = BitVec.ofNat 64 c.length)
    (hc : c.length < 2 ^ 64) :
    WP isa (streamFinish v.callees) s fun s' => GprAbi s s' ∧
      (Absorbed s.mem (s.gpr .x2 + BitVec.ofNat 64 16) (s.gpr .x2 + BitVec.ofNat 64 32)
          (ctxH s.mem (s.gpr .x0)) (ghashInput a c) →
        bytesAt s'.mem (s.gpr .x5) 16 =
          toBytes (ghashFrom (ctxH s.mem (s.gpr .x0)) (ghash (ctxH s.mem (s.gpr .x0)) (blocks (padded a c)))
            [ofBytes (lensBlock a.length c.length)] ^^^
            ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat (blockAt s.mem (s.gpr .x2)))) := by
  have hs' : finPre s := hs
  obtain ⟨L, perm, hR, tW, dtw⟩ := lay_of_fin hs'
  refine WP.seq (WP.mono (finishEntry_ok rfl rfl rfl perm)
    fun s₁ ⟨he₁, hk₁, x22₁, x26₁, x27₁, x28₁, m₁, rd₁, wr₁⟩ => ?_)
  have fsv : Frame [savedR (s.gpr .x6)] s.mem s₁.mem := by rw [m₁]; exact savedMem_frame _ _ _
  obtain ⟨hc₁, hj₁, hH₁, hA₁⟩ := fin_inv L (savedR_inv L) fsv hR (x := ghashInput a c)
  refine WP.seq (WP.mono (WP.with_rdwr (finBody_ok L v (.inl rfl) (a := a) (c := c) he₁ hk₁ x22₁ hR
    (by rw [x26₁, h3]) (by rw [x27₁, h4]) hc hH₁)) fun s₂ ⟨⟨he₂, hk₂, f₂, out₂⟩, _, wr₂⟩ => ?_)
  have hsv : SavedAt s₂.mem (s.gpr .x6) s := by
    have := savedAt_save s.mem (s.gpr .x6) s
    rw [← m₁] at this
    exact this.frame f₂ (saved_finFrame L (.inl rfl))
  have x28₂ : s₂.gpr .x28 = s.gpr .x5 := by rw [hk₂ .x28 (by decide), x28₁]
  refine WP.seq (WP.mono (tagOut_ok he₂.x19 x28₂ (covers_left he₂.perm.w) (by rw [wr₂, wr₁]; exact tW)
    (dtw.sub_right (Region.sub_prefix (by decide)))) fun s₃ ⟨out₃, f₃, og₃, sp₃, rd₃, wr₃⟩ => ?_)
  have he₃ : Env (s.gpr .x0) (s.gpr .x2) (s.gpr .x6) s.sp s₃ := he₂.keep (fun r hr => og₃ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₃ rd₃ wr₃
  have hsv₃ : SavedAt s₃.mem (s.gpr .x6) s := hsv.frame f₃ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (dtw.sub_right (Lay.wSub (by decide))).symm
  refine WP.mono (exit_ok he₃.x19 he₃.sp (covers_left he₃.perm.w) hsv₃) fun s' ⟨ga, hm, _⟩ =>
    ⟨ga, fun ha => ?_⟩
  rw [hm, out₃, ← hc₁, ← hj₁]
  have := out₂ (hA₁ ha)
  rw [add_ofNat_zero] at this
  exact this

theorem streamFinish_wp (v : GcmImpl) {s : State} (hs : streamFinishAArch64.pre s) :
    WP isa (streamFinish v.callees) s fun s' => GprAbi s s' ∧ streamFinishAArch64.post s s' := by
  have h3 : s.gpr .x3 = BitVec.ofNat 64 (Spec.Gcm.zeros (s.gpr .x3).toNat).length := by
    rw [Proof.Gcm.length_zeros, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h4 : s.gpr .x4 = BitVec.ofNat 64 (Spec.Gcm.zeros (s.gpr .x4).toNat).length := by
    rw [Proof.Gcm.length_zeros, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h4' : (Spec.Gcm.zeros (s.gpr .x4).toNat).length < 2 ^ 64 := by
    rw [Proof.Gcm.length_zeros]; exact (s.gpr .x4).isLt
  let ciph := ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat
  let h := ctxH s.mem (s.gpr .x0)
  refine WP.mono (WP.forall_det (P := fun (i : List Byte × List Byte × List Byte) =>
      StreamRepr s.mem (s.gpr .x2) ciph h i.1 i.2.1 i.2.2 ∧
        s.gpr .x3 = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .x4).toNat = i.2.2.length)
    (Q := fun i s' => bytesAt s'.mem (s.gpr .x5) 16 = Spec.Gcm.fullTag ciph h i.1 i.2.1 i.2.2)
    (fin_run v hs h3 h4 h4') fun ⟨iv, a, c⟩ ⟨hr, hl, hc⟩ => ?_) fun s' ⟨r₀, hq⟩ =>
      ⟨r₀.1, fun iv a c hr hl hc => hq ⟨iv, a, c⟩ ⟨hr, hl, hc⟩⟩
  have hc : (s.gpr .x4).toNat = c.length := hc
  have hl : s.gpr .x3 = BitVec.ofNat 64 a.length := hl
  have h4c : s.gpr .x4 = BitVec.ofNat 64 c.length := by rw [← hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (fin_run v hs hl h4c (hc ▸ (s.gpr .x4).isLt)) fun s' ⟨_, hout⟩ => ?_
  obtain ⟨hj, habs, _⟩ := Proof.Gcm.streamRepr_iff.mp hr
  show _ = Spec.Gcm.fullTag ciph h iv a c
  rw [hout habs, Proof.Gcm.fullTag_eq, hj]
  rfl

end VG.Proof.AesGcm.AArch64
