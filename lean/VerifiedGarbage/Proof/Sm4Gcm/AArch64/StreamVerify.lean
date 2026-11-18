module

public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Tag
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Save
public import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Cmp
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamInit
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.FinTag
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Body
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.AesGcm.AArch64.Save

/-! ### `Sm4Gcm.AArch64.StreamFinish`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on AArch64: `vg_sm4_gcm_stream_finish`

Untrusted: everything here is checked by Lean. The entry saves our caller's
registers, keeps the lengths in `x26` and `x27` (`finEntry_ok`) and `tag`
in `x28` (`finishEntry_ok`); `finBody 0` writes the tag to `W`, for any
message of those lengths (`WP.forall_det`), and `tagOut` copies it to
`tag`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks ghashInput StreamRepr ofBytes toBytes)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Spec.Gcm (ctxH)
open VG.Proof.Gcm (Absorbed lensBlock padded)

/-- After the entry, with `work` in `w`: the lengths. -/
theorem finEntry_ok {s : State} {Ctx St W : Addr} {w : Reg} (hCtx : s.gpr .x0 = Ctx) (hSt : s.gpr .x1 = St)
    (hW : s.gpr w = W) (hperm : Perm Ctx St W s) :
    WP isa (.block (finEntry w)) s fun s' => Env Ctx St W s.sp s' ∧ Kept s'.gpr s' ∧
      s'.gpr .x26 = s.gpr .x2 ∧ s'.gpr .x27 = s.gpr .x3 ∧
      s'.gpr .x4 = s.gpr .x4 ∧ s'.gpr .x5 = s.gpr .x5 ∧ s'.mem = savedMem s.mem W s.gpr ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s w hW hperm.w
  obtain ⟨s₂, run₂, x19₂, x20₂, x21₂, x26₂, x27₂, x5₂, x6₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 w, mov .x20 .x1, mov .x21 .x0, mov .x26 .x2, mov .x27 .x3] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x20 = St ∧ s₂.gpr .x21 = Ctx ∧
      s₂.gpr .x26 = s.gpr .x2 ∧ s₂.gpr .x27 = s.gpr .x3 ∧
      s₂.gpr .x4 = s.gpr .x4 ∧ s₂.gpr .x5 = s.gpr .x5 ∧ s₂.sp = s₁.sp ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩ <;> simp [gpr_write, g₁, hW, hSt, hCtx]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  exact ⟨⟨x19₂, x20₂, x21₂, by rw [sp₂, sp₁], hperm.of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])⟩,
    fun _ _ => rfl, x26₂, x27₂, x5₂, x6₂, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

/-- The entry of `finish`: `tag` in `x28`. -/
theorem finishEntry_ok {s : State} {Ctx St W : Addr} (hCtx : s.gpr .x0 = Ctx) (hSt : s.gpr .x1 = St)
    (hW : s.gpr .x5 = W) (hperm : Perm Ctx St W s) :
    WP isa (.block (finEntry .x5 ++ [mov .x28 .x4])) s fun s' => Env Ctx St W s.sp s' ∧ Kept s'.gpr s' ∧
      s'.gpr .x26 = s.gpr .x2 ∧ s'.gpr .x27 = s.gpr .x3 ∧
      s'.gpr .x28 = s.gpr .x4 ∧ s'.mem = savedMem s.mem W s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.block_append (WP.mono (finEntry_ok hCtx hSt hW hperm)
    fun s₁ ⟨he₁, _, x26₁, x27₁, x5₁, _, m₁, rd₁, wr₁⟩ => ?_)
  refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  have r : Regs [.x28] s₁ (s₁.write .x .x28 (s₁.gpr .x4 + BitVec.ofNat 64 0)) :=
    ⟨by others_tac, rfl, rfl, rfl, rfl⟩
  exact ⟨he₁.of_regs r, fun _ _ => rfl,
    by rw [r.others _ (by decide), x26₁], by rw [r.others _ (by decide), x27₁], by simp [gpr_write, x5₁],
    by rw [r.mem, m₁], by rw [r.rd, rd₁], by rw [r.wr, wr₁]⟩

/-- What `finPre` gives. -/
theorem lay_of_fin {s : State} (hs : finPre s) :
    Lay (s.gpr .x0) (s.gpr .x1) (s.gpr .x5) s.sp ∧ Perm (s.gpr .x0) (s.gpr .x1) (s.gpr .x5) s ∧
      Covers [⟨s.gpr .x4, 16⟩] s.wr ∧
      (⟨s.gpr .x4, 16⟩ : Region).Disjoint ⟨s.gpr .x5, 768⟩ := by
  simp only [finPre] at hs
  obtain ⟨hsp, hrd, hwr, dcs, -, dcw, -, dsw, dtw, sC, sS, -, sW', wc, ws, -, ww⟩ := hs
  exact ⟨Lay.of wc ws ww dcs dcw dsw hsp sC sS sW',
    ⟨covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩,
    covers_of_mem (by rw [hwr]; simp), dtw⟩

/-- What writes to the parts `rs` of `W` keep, outside the state. -/
theorem fin_inv {Ctx St W SP : Addr} (L : Lay Ctx St W SP) {rs : List Region}
    (hrs : ∀ r ∈ rs, (⟨St, 80⟩ : Region).Disjoint r ∧ Region.Sub r ⟨W, 768⟩) {m₀ m : Mem} (hf : Frame rs m₀ m)
    {x : List Byte} :
    ciphOf m Ctx = ciphOf m₀ Ctx ∧ blockAt m St = blockAt m₀ St ∧
      blockAt m (Ctx + BitVec.ofNat 64 240) = ctxH m₀ Ctx ∧
      (Absorbed m₀ (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (ctxH m₀ Ctx) x →
        Absorbed m (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (ctxH m₀ Ctx) x) :=
  ⟨ciph_frame hf (fun r hr => L.cw'.sub_right (hrs r hr).2),
    blockAt_frame hf (fun r hr => (hrs r hr).1.sub_left (Region.sub_prefix (by decide))),
    blockAt_frame hf (fun r hr => (L.cw'.sub_left (Lay.ctxSub (by decide))).sub_right (hrs r hr).2),
    fun ha => Absorbed.frame hf (fun r hr => (hrs r hr).1.sub_left (Lay.stSub (by decide))) ha⟩

/-- The saved registers' slots are parts of `W` outside the state. -/
theorem savedR_inv {Ctx St W SP : Addr} (L : Lay Ctx St W SP) :
    ∀ r ∈ [savedR W], (⟨St, 80⟩ : Region).Disjoint r ∧ Region.Sub r ⟨W, 768⟩ := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨L.sb.sub_right (Lay.bSub (by decide) (by decide)), Lay.wSub (by decide)⟩

/-- One run of `stream_finish`, for a message `a`, `c` of those lengths. -/
theorem fin_run (v : GcmImpl) {s : State} (hs : streamFinishAArch64.pre s) {a c : List Byte}
    (h3 : s.gpr .x2 = BitVec.ofNat 64 a.length) (h4 : s.gpr .x3 = BitVec.ofNat 64 c.length)
    (hc : c.length < 2 ^ 64) :
    WP isa (streamFinish v.callees) s fun s' => GprAbi s s' ∧
      (Absorbed s.mem (s.gpr .x1 + BitVec.ofNat 64 16) (s.gpr .x1 + BitVec.ofNat 64 32)
          (ctxH s.mem (s.gpr .x0)) (ghashInput a c) →
        bytesAt s'.mem (s.gpr .x4) 16 =
          toBytes (ghashFrom (ctxH s.mem (s.gpr .x0)) (ghash (ctxH s.mem (s.gpr .x0)) (blocks (padded a c)))
            [ofBytes (lensBlock a.length c.length)] ^^^
            ciphOf s.mem (s.gpr .x0) (blockAt s.mem (s.gpr .x1)))) := by
  have hs' : finPre s := hs
  obtain ⟨L, perm, tW, dtw⟩ := lay_of_fin hs'
  refine WP.seq (WP.mono (finishEntry_ok rfl rfl rfl perm)
    fun s₁ ⟨he₁, hk₁, x26₁, x27₁, x28₁, m₁, rd₁, wr₁⟩ => ?_)
  have fsv : Frame [savedR (s.gpr .x5)] s.mem s₁.mem := by rw [m₁]; exact savedMem_frame _ _ _
  obtain ⟨hc₁, hj₁, hH₁, hA₁⟩ := fin_inv L (savedR_inv L) fsv (x := ghashInput a c)
  refine WP.seq (WP.mono (WP.with_rdwr (finBody_ok L v (.inl rfl) (a := a) (c := c) he₁ hk₁
    (by rw [x26₁, h3]) (by rw [x27₁, h4]) hc hH₁)) fun s₂ ⟨⟨he₂, hk₂, f₂, out₂⟩, _, wr₂⟩ => ?_)
  have hsv : SavedAt s₂.mem (s.gpr .x5) s := by
    have := savedAt_save s.mem (s.gpr .x5) s
    rw [← m₁] at this
    exact this.frame f₂ (saved_finFrame L (.inl rfl))
  have x28₂ : s₂.gpr .x28 = s.gpr .x4 := by rw [hk₂ .x28 (by decide), x28₁]
  refine WP.seq (WP.mono (tagOut_ok he₂.x19 x28₂ (covers_left he₂.perm.w) (by rw [wr₂, wr₁]; exact tW)
    (dtw.sub_right (Region.sub_prefix (by decide)))) fun s₃ ⟨out₃, f₃, og₃, sp₃, rd₃, wr₃⟩ => ?_)
  have he₃ : Env (s.gpr .x0) (s.gpr .x1) (s.gpr .x5) s.sp s₃ := he₂.keep (fun r hr => og₃ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₃ rd₃ wr₃
  have hsv₃ : SavedAt s₃.mem (s.gpr .x5) s := hsv.frame f₃ fun r hr => by
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
  have h3 : s.gpr .x2 = BitVec.ofNat 64 (Spec.Gcm.zeros (s.gpr .x2).toNat).length := by
    rw [Proof.Gcm.length_zeros, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h4 : s.gpr .x3 = BitVec.ofNat 64 (Spec.Gcm.zeros (s.gpr .x3).toNat).length := by
    rw [Proof.Gcm.length_zeros, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h4' : (Spec.Gcm.zeros (s.gpr .x3).toNat).length < 2 ^ 64 := by
    rw [Proof.Gcm.length_zeros]; exact (s.gpr .x3).isLt
  let ciph := ctxCiph s.mem (s.gpr .x0)
  let h := ctxH s.mem (s.gpr .x0)
  refine WP.mono (WP.forall_det (P := fun (i : List Byte × List Byte × List Byte) =>
      StreamRepr s.mem (s.gpr .x1) ciph h i.1 i.2.1 i.2.2 ∧
        s.gpr .x2 = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .x3).toNat = i.2.2.length)
    (Q := fun i s' => bytesAt s'.mem (s.gpr .x4) 16 = Spec.Gcm.fullTag ciph h i.1 i.2.1 i.2.2)
    (fin_run v hs h3 h4 h4') fun ⟨iv, a, c⟩ ⟨hr, hl, hc⟩ => ?_) fun s' ⟨r₀, hq⟩ =>
      ⟨r₀.1, fun iv a c hr hl hc => hq ⟨iv, a, c⟩ ⟨hr, hl, hc⟩⟩
  have hc : (s.gpr .x3).toNat = c.length := hc
  have hl : s.gpr .x2 = BitVec.ofNat 64 a.length := hl
  have h4c : s.gpr .x3 = BitVec.ofNat 64 c.length := by rw [← hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (fin_run v hs hl h4c (hc ▸ (s.gpr .x3).isLt)) fun s' ⟨_, hout⟩ => ?_
  obtain ⟨hj, habs, _⟩ := Proof.Gcm.streamRepr_iff.mp hr
  show _ = Spec.Gcm.fullTag ciph h iv a c
  rw [hout habs, Proof.Gcm.fullTag_eq, hj]
  rfl

end VG.Proof.Sm4Gcm.AArch64

end

end

/-!
# SM4-GCM on AArch64: `vg_sm4_gcm_stream_verify`

Untrusted: everything here is checked by Lean. After the entry, `tagLenOk`
checks the tag length (a public value); if `tagLenOk` does not allow it, 0 is
returned; otherwise `tagIn` copies the received tag to `W`, `finBody 112`
writes the tag at `W + 112`, `cmpSeg` compares its first `tag_len` bytes with
the received ones without a branch, and `verRet` returns 1 or 0
(`ver_run`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks ghashInput StreamRepr ofBytes toBytes zeros)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Spec.Gcm (ctxH)
open VG.Proof.Gcm (Absorbed lensBlock padded)

theorem tagLenOk_le {t : Nat} (h : Spec.Gcm.tagLenOk t = true) : t ≤ 16 := by
  simp only [Spec.Gcm.tagLenOk, Bool.and_eq_true, decide_eq_true_eq] at h
  omega_using [h]

/-- The entry of `verify`: `tag_len` in `x28` and `tag` in `x12`. -/
theorem verEntry_ok {s : State} {Ctx St W : Addr} (hCtx : s.gpr .x0 = Ctx) (hSt : s.gpr .x1 = St)
    (hW : s.gpr .x6 = W) (hperm : Perm Ctx St W s) :
    WP isa (.block (finEntry .x6 ++ [mov .x28 .x5, mov .x12 .x4])) s fun s' => Env Ctx St W s.sp s' ∧
      Kept s'.gpr s' ∧ s'.gpr .x26 = s.gpr .x2 ∧
      s'.gpr .x27 = s.gpr .x3 ∧ s'.gpr .x28 = s.gpr .x5 ∧ s'.gpr .x12 = s.gpr .x4 ∧
      s'.mem = savedMem s.mem W s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.block_append (WP.mono (finEntry_ok hCtx hSt hW hperm)
    fun s₁ ⟨he₁, _, x26₁, x27₁, x5₁, x6₁, m₁, rd₁, wr₁⟩ => ?_)
  refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
  have r : Regs [.x28, .x12] s₁ s' := by subst hs'; exact ⟨by others_tac, rfl, rfl, rfl, rfl⟩
  have x28' : s'.gpr .x28 = s₁.gpr .x5 := by subst hs'; simp [gpr_write]
  have x12' : s'.gpr .x12 = s₁.gpr .x4 := by subst hs'; simp [gpr_write]
  exact ⟨he₁.of_regs r, fun _ _ => rfl,
    by rw [r.others _ (by decide), x26₁], by rw [r.others _ (by decide), x27₁], by rw [x28', x6₁],
    by rw [x12', x5₁], by rw [r.mem, m₁], by rw [r.rd, rd₁], by rw [r.wr, wr₁]⟩

/-- What `verPre` gives. -/
theorem lay_of_ver {s : State} (hs : verPre s) :
    Lay (s.gpr .x0) (s.gpr .x1) (s.gpr .x6) s.sp ∧ Perm (s.gpr .x0) (s.gpr .x1) (s.gpr .x6) s ∧
      Covers [⟨s.gpr .x4, (s.gpr .x5).toNat⟩] (s.rd ++ s.wr) ∧
      (⟨s.gpr .x4, (s.gpr .x5).toNat⟩ : Region).Disjoint ⟨s.gpr .x6, 768⟩ := by
  simp only [verPre] at hs
  obtain ⟨hsp, hrd, hwr, dcs, dcw, -, dsw, dtw, sC, sS, -, sW', wc, ws, -, ww⟩ := hs
  exact ⟨Lay.of wc ws ww dcs dcw dsw hsp sC sS sW',
    ⟨covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩,
    covers_mem (by rw [hrd, hwr]; simp), dtw⟩

/-- The parts of `W` that the entry and `tagIn` write. -/
theorem tag16_inv {Ctx St W SP : Addr} (L : Lay Ctx St W SP) :
    ∀ r ∈ [savedR W, ⟨W, 16⟩], (⟨St, 80⟩ : Region).Disjoint r ∧ Region.Sub r ⟨W, 768⟩ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact savedR_inv L _ (List.mem_singleton_self _)
  · exact ⟨L.sa, Region.sub_prefix (by decide)⟩

/-- One run of `stream_verify`, for a message `a`, `c` of those lengths. -/
theorem ver_run (v : GcmImpl) {s : State} (hs : streamVerifyAArch64.pre s) {a c : List Byte}
    (h3 : s.gpr .x2 = BitVec.ofNat 64 a.length) (h4 : s.gpr .x3 = BitVec.ofNat 64 c.length)
    (hc : c.length < 2 ^ 64) :
    WP isa (streamVerify v.callees) s fun s' => GprAbi s s' ∧
      (Absorbed s.mem (s.gpr .x1 + BitVec.ofNat 64 16) (s.gpr .x1 + BitVec.ofNat 64 32)
          (ctxH s.mem (s.gpr .x0)) (ghashInput a c) →
        let T := toBytes (ghashFrom (ctxH s.mem (s.gpr .x0)) (ghash (ctxH s.mem (s.gpr .x0)) (blocks (padded a c)))
            [ofBytes (lensBlock a.length c.length)] ^^^
            ciphOf s.mem (s.gpr .x0) (blockAt s.mem (s.gpr .x1)))
        if Spec.Gcm.tagLenOk (s.gpr .x5).toNat ∧ T.take (s.gpr .x5).toNat =
            bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat then (s'.gpr .x0).setWidth 32 = 1
        else (s'.gpr .x0).setWidth 32 = 0) := by
  have hs' : verPre s := hs
  obtain ⟨L, perm, tR, dtw⟩ := lay_of_ver hs'
  generalize hT : toBytes (ghashFrom (ctxH s.mem (s.gpr .x0)) (ghash (ctxH s.mem (s.gpr .x0)) (blocks (padded a c)))
      [ofBytes (lensBlock a.length c.length)] ^^^
      ciphOf s.mem (s.gpr .x0) (blockAt s.mem (s.gpr .x1))) = T
  generalize htl : (s.gpr .x5).toNat = tl at tR dtw ⊢
  have htl' : tl < 2 ^ 64 := htl ▸ (s.gpr .x5).isLt
  -- The entry.
  refine WP.seq (WP.mono (verEntry_ok rfl rfl rfl perm)
    fun s₂ ⟨he₂, hk₂, x26₂, x27₂, x28₂, x12₂, m₂, rd₂, wr₂⟩ => ?_)
  have x28₂' : s₂.gpr .x28 = BitVec.ofNat 64 tl := by rw [x28₂, ← htl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have fsv : Frame [savedR (s.gpr .x6)] s.mem s₂.mem := by rw [m₂]; exact savedMem_frame _ _ _
  refine WP.seq (WP.mono (tagLenOk_ok s₂ x28₂' htl') fun s₃ ⟨x9₃, r₃⟩ => ?_)
  have he₃ := he₂.of_regs r₃
  have hk₃ := hk₂.of_others r₃.others
  have m₃ : s₃.mem = s₂.mem := r₃.mem
  have sv₃ : SavedAt s₃.mem (s.gpr .x6) s := by
    have := savedAt_save s.mem (s.gpr .x6) s
    rwa [← m₂, ← m₃] at this
  have ev : isa.eval (.zero .x .x9) s₃ =
      some (decide ((if Spec.Gcm.tagLenOk tl then 1 else 0) = 0)) :=
    eval_zero x9₃ (by split <;> decide)
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => Env (s.gpr .x0) (s.gpr .x1) (s.gpr .x6) s.sp s₄ ∧
      SavedAt s₄.mem (s.gpr .x6) s ∧
      (Absorbed s.mem (s.gpr .x1 + BitVec.ofNat 64 16) (s.gpr .x1 + BitVec.ofNat 64 32)
          (ctxH s.mem (s.gpr .x0)) (ghashInput a c) →
        if Spec.Gcm.tagLenOk tl ∧ T.take tl = bytesAt s.mem (s.gpr .x4) tl then (s₄.gpr .x0).setWidth 32 = 1
        else (s₄.gpr .x0).setWidth 32 = 0))
    (WP.ite _ ev (fun ht => ?_) (fun hf => ?_)) fun s₄ ⟨he₄, sv₄, post₄⟩ => ?_)
  · have hok : Spec.Gcm.tagLenOk tl = false := by
      revert ht; cases Spec.Gcm.tagLenOk tl <;> simp
    refine WP.run ⟨_, by arun [], rfl⟩ fun s₄ hs₄ => ?_
    subst hs₄
    refine ⟨he₃.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl, sv₃, fun _ => ?_⟩
    rw [ite_eq_right (by simp [hok])]
    simp [gpr_write]
  · have hok : Spec.Gcm.tagLenOk tl = true := by
      revert hf; cases Spec.Gcm.tagLenOk tl <;> simp
    have hle := tagLenOk_le hok
    have x12₃ : s₃.gpr .x12 = s.gpr .x4 := by rw [r₃.others _ (by decide), x12₂]
    have x28₃ : s₃.gpr .x28 = BitVec.ofNat 64 tl := by rw [r₃.others _ (by decide), x28₂']
    refine WP.seq (WP.mono (tagIn_ok he₃.x19 x12₃ x28₃ hle (by rw [r₃.rd, r₃.wr, rd₂, wr₂]; exact tR)
      he₃.perm.w (dtw.sub_right (Region.sub_prefix (by decide))))
      fun s₄ ⟨in₄, f₄, og₄, sp₄, rd₄, wr₄⟩ => ?_)
    have he₄ : Env (s.gpr .x0) (s.gpr .x1) (s.gpr .x6) s.sp s₄ := he₃.keep (fun r hr => og₄ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₄ rd₄ wr₄
    have hk₄ : Kept s₃.gpr s₄ := Kept.of_others (fun _ _ => rfl) og₄
    have F₄ : Frame [savedR (s.gpr .x6), ⟨s.gpr .x6, 16⟩] s.mem s₄.mem :=
      (fsv.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩).trans
        (by rw [← m₃]; exact f₄.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp,
          fun _ h => h⟩)
    obtain ⟨hc₄, hj₄, hH₄, hA₄⟩ := fin_inv L (tag16_inv L) F₄ (x := ghashInput a c)
    have x26₄ : s₄.gpr .x26 = BitVec.ofNat 64 a.length := by
      rw [hk₄ .x26 (by decide), r₃.others _ (by decide), x26₂, h3]
    have x27₄ : s₄.gpr .x27 = BitVec.ofNat 64 c.length := by
      rw [hk₄ .x27 (by decide), r₃.others _ (by decide), x27₂, h4]
    refine WP.seq (WP.mono (finBody_ok L v (.inr rfl) (a := a) (c := c) (H := ctxH s.mem (s.gpr .x0)) he₄ hk₄
      x26₄ x27₄ hc hH₄) fun s₅ ⟨he₅, hk₅, f₅, out₅⟩ => ?_)
    have x28₅ : s₅.gpr .x28 = BitVec.ofNat 64 tl := by rw [hk₅ .x28 (by decide), x28₃]
    refine WP.seq (WP.mono (cmp_ok L he₅ hk₅ x28₅ hle) fun s₆ ⟨x10₆, he₆, _, _, f₆⟩ => ?_)
    refine WP.mono (verRet_ok
      (b := decide (bytesAt s₅.mem (s.gpr .x6 + BitVec.ofNat 64 112) tl = bytesAt s₅.mem (s.gpr .x6) tl))
      (by rw [x10₆]; by_cases hp : bytesAt s₅.mem (s.gpr .x6 + BitVec.ofNat 64 112) tl =
            bytesAt s₅.mem (s.gpr .x6) tl <;> simp [hp]))
      fun s₇ ⟨x0₇, r₇⟩ =>
        ⟨he₆.of_regs r₇, by
          rw [r₇.mem]
          exact (((sv₃.frame f₄ (saved_tag16 L)).frame f₅ (saved_finFrame L (.inr rfl))).frame f₆ (saved_cmp L)),
          fun ha => ?_⟩
    have hT₅ : bytesAt s₅.mem (s.gpr .x6 + BitVec.ofNat 64 112) 16 = T := by
      rw [out₅ (hA₄ ha), hc₄, hj₄, ← hT]
    have hW₅ : bytesAt s₅.mem (s.gpr .x6) tl = bytesAt s.mem (s.gpr .x4) tl := by
      have dW : ∀ r ∈ finFrame (s.gpr .x1) (s.gpr .x6) s.sp 112, (⟨s.gpr .x6, tl⟩ : Region).Disjoint r := by
        intro r hr
        refine Region.Disjoint.sub_left ?_ (Region.sub_prefix hle)
        have ww : ∀ e j, 16 ≤ e → e + j ≤ 768 →
            (⟨s.gpr .x6, 16⟩ : Region).Disjoint ⟨s.gpr .x6 + BitVec.ofNat 64 e, j⟩ := fun e j h₁ h₂ => by
          simpa using L.w_w (a := 0) (n := 16) (d := e) (k := j) (.inl h₁) (by decide) h₂
        rcases List.mem_append.mp hr with hr | hr
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact (L.sa.sub_left (Lay.stSub (by decide))).symm
          · exact ww _ _ (by decide) (by decide)
          · exact ww _ _ (by decide) (by decide)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl
          · exact (L.sa.sub_left (Region.sub_prefix (by decide))).symm
          · exact ww _ _ (by decide) (by decide)
          · exact ww _ _ (by decide) (by decide)
          · exact ww _ _ (by decide) (by decide)
          · simpa using (L.stk_w (a := 0) (n := 16) (by decide)).symm
      rw [bytesAt_frame f₅ dW (by omega_using [htl]), in₄, m₃]
      refine bytesAt_frame fsv (fun r hr => ?_) (by omega_using [htl])
      simp only [List.mem_singleton] at hr; subst hr
      exact dtw.sub_right (Lay.wSub (by decide))
    have hb : (bytesAt s₅.mem (s.gpr .x6 + BitVec.ofNat 64 112) tl = bytesAt s₅.mem (s.gpr .x6) tl) ↔
        T.take tl = bytesAt s.mem (s.gpr .x4) tl := by
      rw [← bytesAt_take _ _ hle, hT₅, hW₅]
    by_cases hp : T.take tl = bytesAt s.mem (s.gpr .x4) tl
    · rw [ite_eq_left ⟨hok, hp⟩]
      have hb' := hb.mpr hp
      simp only [hb', decide_true, ite_true] at x0₇
      rw [x0₇]; rfl
    · rw [ite_eq_right (fun h => hp h.2)]
      have hb' : ¬ (bytesAt s₅.mem (s.gpr .x6 + BitVec.ofNat 64 112) tl = bytesAt s₅.mem (s.gpr .x6) tl) :=
        fun h => hp (hb.mp h)
      simp only [hb', decide_false, Bool.false_eq_true, ite_false] at x0₇
      rw [x0₇]; rfl
  refine WP.mono (exit_ok he₄.x19 he₄.sp (covers_left he₄.perm.w) sv₄) fun s' ⟨ga, _, hx0, _⟩ =>
    ⟨ga, fun ha => ?_⟩
  rw [hx0]
  exact post₄ ha

theorem streamVerify_wp (v : GcmImpl) {s : State} (hs : streamVerifyAArch64.pre s) :
    WP isa (streamVerify v.callees) s fun s' => GprAbi s s' ∧ streamVerifyAArch64.post s s' := by
  have h3 : s.gpr .x2 = BitVec.ofNat 64 (Spec.Gcm.zeros (s.gpr .x2).toNat).length := by
    rw [Proof.Gcm.length_zeros, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h4 : s.gpr .x3 = BitVec.ofNat 64 (Spec.Gcm.zeros (s.gpr .x3).toNat).length := by
    rw [Proof.Gcm.length_zeros, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h4' : (Spec.Gcm.zeros (s.gpr .x3).toNat).length < 2 ^ 64 := by
    rw [Proof.Gcm.length_zeros]; exact (s.gpr .x3).isLt
  let ciph := ctxCiph s.mem (s.gpr .x0)
  let h := ctxH s.mem (s.gpr .x0)
  let tl := (s.gpr .x5).toNat
  refine WP.mono (WP.forall_det (P := fun (i : List Byte × List Byte × List Byte) =>
      StreamRepr s.mem (s.gpr .x1) ciph h i.1 i.2.1 i.2.2 ∧
        s.gpr .x2 = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .x3).toNat = i.2.2.length)
    (Q := fun i s' =>
      if Spec.Gcm.tagLenOk tl ∧ (Spec.Gcm.fullTag ciph h i.1 i.2.1 i.2.2).take tl = bytesAt s.mem (s.gpr .x4) tl then
        (s'.gpr .x0).setWidth 32 = 1
      else (s'.gpr .x0).setWidth 32 = 0)
    (ver_run v hs h3 h4 h4') fun ⟨iv, a, c⟩ ⟨hr, hl, hc⟩ => ?_) fun s' ⟨r₀, hq⟩ =>
      ⟨r₀.1, fun iv a c hr hl hc => hq ⟨iv, a, c⟩ ⟨hr, hl, hc⟩⟩
  have hc : (s.gpr .x3).toNat = c.length := hc
  have hl : s.gpr .x2 = BitVec.ofNat 64 a.length := hl
  have h4c : s.gpr .x3 = BitVec.ofNat 64 c.length := by rw [← hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (ver_run v hs hl h4c (hc ▸ (s.gpr .x3).isLt)) fun s' ⟨_, hout⟩ => ?_
  obtain ⟨hj, habs, _⟩ := Proof.Gcm.streamRepr_iff.mp hr
  have ht : Spec.Gcm.fullTag ciph h iv a c =
      toBytes (ghashFrom (ctxH s.mem (s.gpr .x0)) (ghash (ctxH s.mem (s.gpr .x0)) (blocks (padded a c)))
        [ofBytes (lensBlock a.length c.length)] ^^^
        ciphOf s.mem (s.gpr .x0) (blockAt s.mem (s.gpr .x1))) := by
    rw [Proof.Gcm.fullTag_eq, hj]; rfl
  show if Spec.Gcm.tagLenOk tl ∧ (Spec.Gcm.fullTag ciph h iv a c).take tl = _ then _ else _
  rw [ht]
  exact hout habs

end VG.Proof.Sm4Gcm.AArch64
