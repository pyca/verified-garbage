module

public import VerifiedGarbage.Proof.Sm4Gcm.X86.StreamCrypt
meta import VerifiedGarbage.Proof.Sm4Gcm.X86.StreamCrypt
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.Impl.Sm4Gcm.X86
meta import VerifiedGarbage.Proof.Sm4Gcm.X86.Crypt
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.State
meta import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Sm4Gcm.X86.CryptTail
public import VerifiedGarbage.Proof.Sm4Gcm.X86.Crypt
meta import VerifiedGarbage.Proof.Sm4Gcm.X86.CryptTail

/-!
# SM4-GCM on x86: `vg_aes_gcm_stream_encrypt`

Untrusted: everything here is checked by Lean. The entry, the text
encrypted (`crypt`), the ciphertext absorbed (`textAbsorb`) and the exit,
as one `Pc` (`streamEncrypt_pc`): correct (`streamEncrypt_correct`) and
constant time (`streamEncrypt_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86

variable {vg : VG.Proof.AesGcm.X86.GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.Sm4Gcm.X86 VG.WriteBytes VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 hiding ctrCall keyCall ctrArgs cryptWhole cryptTail crypt tag init cryptEntry
  streamEncrypt streamDecrypt finEntry finTag streamFinish streamVerify oneEntry oneTag oneCrypt «seal» «open»
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr gctr inc32 j0)
open VG.Spec.Gcm (ctxH)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

theorem streamEncrypt_eq : (streamEncrypt vg.callees) = .seq (entry 8 (([.mov .esi (argOp 1)] : List Instr) ++
    (crKeeps.flatMap (fun p => keep p.1 p.2) ++ [])))
    (.seq (.block setText) (.seq crypt (.seq (textAbsorb vg.callees) (.block restore)))) := rfl

/-- After `setText`: the text ready for `crypt`. -/
structure CSet (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  ent : ∃ s₁, CEnt p s₀ s₁ ∧ Frame [pslotR (p.2 8)] s₁.mem s.mem ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr
  cr : CrIn (p.2 0) (p.2 1) (p.2 8) p.1 1536 (p.2 6) (p.2 7).toNat (p.2 5 ++ p.2 4).toNat s

theorem cr_dataW {p : BitVec 32 × (Nat → BitVec 32)} (hc : CrPure p) {s₀ s : State} (hpre : streamCryptPre s₀)
    (hpub : pubOf 9 s₀ = p) (hwr : s.wr = s₀.wr) :
    DataW (p.2 0) (p.2 1) (p.2 8) p.1 1536 s (p.2 6) (p.2 7).toNat := by
  have hp := hpre
  simp only [streamCryptPre] at hp
  have hw : Covers [⟨w64 (p.2 6), (p.2 7).toNat⟩] s.wr := by
    rw [hwr, hp.2.1, ← pubOf_arg hpub (i := 6) (by decide), ← pubOf_arg hpub (i := 7) (by decide)]
    exact covers_of_mem (by simp)
  exact ⟨⟨covers_left hw, hc.fd, hc.dst, hc.dw, hc.dstk⟩, hw, hc.dctx⟩

theorem setText_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (CEnt p) (.block setText) (CSet p) := by
  refine Pc.taint [.ebp] (fun s₀ s h => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp]) (by taint_decide)
  have hc := crPure_of h.pre h.pub
  have L := hc.lay
  obtain ⟨s', run, d, n, b, fr, bp, si, sp, rd, wr⟩ := setText_ok L h.env h.ta
  refine WP.of_runBlock ⟨s', run, ⟨s, h, fr, rd, wr⟩, ?_⟩
  have kP : ∀ r ∈ [pslotR (p.2 8)], (keptR (p.2 8)).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  refine ⟨h.env.keep bp si sp rd wr (slot_frame fr fun r hr => (kP r hr).sub_left (Offset.sub _ (by decide)
    (by decide))), d, n, by rw [b, append_toNat32]; congr 1; omega, (p.2 7).isLt,
    cr_dataW hc h.pre h.pub (by rw [wr, h.wr])⟩

/-- The streaming state's regions are apart from what `crypt` and `textAbsorb` write, but their own. -/
theorem st_crFrame {p : BitVec 32 × (Nat → BitVec 32)} (hc : CrPure p) {d k : Nat} (hk : d + k ≤ 48) :
    ∀ r ∈ crFrame (p.2 1) (p.2 8) p.1 1536 (p.2 6) (p.2 7).toNat,
      (⟨w64 (p.2 1) + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  have L := hc.lay
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hc.dst.sub_right (Lay.stSub (by omega))).symm
  · exact Lay.st_st (.inl (by omega)) (by omega) (by decide)
  · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · exact (L.stk_st (by omega)).symm

theorem st_taFrame {p : BitVec 32 × (Nat → BitVec 32)} (hc : CrPure p) {d k : Nat}
    (hk : d + k ≤ 16 ∨ (48 ≤ d ∧ d + k ≤ 80)) :
    ∀ r ∈ taFrame (p.2 1) (p.2 8) p.1 28, (⟨w64 (p.2 1) + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  have L := hc.lay
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Lay.st_st (by omega) (by omega) (by decide)
  · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · exact (L.lay.stk_st (by omega)).symm

theorem ret_crFrame {p : BitVec 32 × (Nat → BitVec 32)} (hc : CrPure p) :
    ∀ r ∈ crFrame (p.2 1) (p.2 8) p.1 1536 (p.2 6) (p.2 7).toNat, (⟨w64 p.1, 4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hc.r_d
  · exact hc.r_s.sub_right (Lay.stSub (by decide))
  · exact hc.r_w.sub_right (Lay.wSub (by decide))
  · exact ret_below hc.sp

theorem ret_taFrame {p : BitVec 32 × (Nat → BitVec 32)} (hc : CrPure p) :
    ∀ r ∈ taFrame (p.2 1) (p.2 8) p.1 28, (⟨w64 p.1, 4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hc.r_s.sub_right (Lay.stSub (by decide))
  · exact hc.r_w.sub_right (Lay.wSub (by decide))
  · exact hc.r_w.sub_right (Lay.wSub (by decide))
  · exact ret_below (by have := hc.sp; omega)

/-- The entry's and `setText`'s writes, within `W`. -/
theorem cset_frame {p : BitVec 32 × (Nat → BitVec 32)} {s₀ s₁ s : State} (h₁ : CEnt p s₀ s₁)
    (fr : Frame [pslotR (p.2 8)] s₁.mem s.mem) : Frame [⟨w64 (p.2 8) + BitVec.ofNat 64 96, 2464⟩] s₀.mem s.mem :=
  (h₁.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩).trans (fr.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩)

/-- The exit of `encrypt` and `decrypt`, after `crypt` and `textAbsorb` in either order. -/
theorem cr_exit {p : BitVec 32 × (Nat → BitVec 32)} (hc : CrPure p) {s₀ s₁ s : State} (h₁ : CEnt p s₀ s₁)
    (he : Env (p.2 0) (p.2 1) (p.2 8) p.1 s)
    (hf : Frame (pslotR (p.2 8) :: crFrame (p.2 1) (p.2 8) p.1 1536 (p.2 6) (p.2 7).toNat ++
      taFrame (p.2 1) (p.2 8) p.1 28) s₁.mem s.mem) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem := by
  have L := hc.lay
  have esp := pubOf_esp h₁.pub
  have hsv : SavedAt s.mem (p.2 8) s₀ := h₁.saved.frameK hf fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact Lay.w_w (a := 128) (n := 112) (d := 272) (k := 12) (.inl (by decide)) (by decide) (by decide)
    rcases List.mem_append.mp hr with hr | hr
    · exact kept_crFrame L (cr_dataW hc h₁.pre h₁.pub h₁.wr) r hr
    · exact kept_taFrame L.lay r hr
  have rT : ∀ r ∈ pslotR (p.2 8) :: crFrame (p.2 1) (p.2 8) p.1 1536 (p.2 6) (p.2 7).toNat ++
      taFrame (p.2 1) (p.2 8) p.1 28, (⟨w64 p.1, 4⟩ : Region).Disjoint r := fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hc.r_w.sub_right (Lay.wSub (d := 272) (n := 12) (by decide))
    rcases List.mem_append.mp hr with hr | hr
    · exact ret_crFrame hc r hr
    · exact ret_taFrame hc r hr
  have rE : ∀ r ∈ [(⟨w64 (p.2 8) + BitVec.ofNat 64 128, 2432⟩ : Region)], (⟨w64 p.1, 4⟩ : Region).Disjoint r :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hc.r_w.sub_right (Lay.wSub (by decide))
  have hret : s.mem.readW (w64 (s₀.gpr .esp)) 32 = s₀.mem.readW (w64 (s₀.gpr .esp)) 32 := by
    rw [esp, ret_kept hf rT, ret_kept h₁.frame rE]
  exact WP.mono (exit_ok he.ebp (by rw [he.esp, esp]) (covers_left he.wW) L.fw hsv hret)
    fun s' ⟨abi, m', _, _, _⟩ => ⟨abi, m'⟩

theorem streamEncrypt_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => streamCryptPre s₀ ∧ pubOf 9 s₀ = p ∧ s = s₀) (streamEncrypt vg.callees)
      (fun s₀ s' => abiPreserved s₀ s' ∧ streamEncryptX86.post s₀ s') := by
  by_cases hex : ∃ s₀, streamCryptPre s₀ ∧ pubOf 9 s₀ = p
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have hc := crPure_of hz hzp
  have L := hc.lay
  rw [streamEncrypt_eq]
  refine Pc.seq (crEntry_pc p) (Pc.seq (setText_pc p) ?_)
  refine Pc.seq (Pc.lift (Pc.forall fun icb => crypt_pc L rfl (icb := icb) (D := p.2 6)
    (n := (p.2 7).toNat) (P := (p.2 5 ++ p.2 4).toNat)) (fun _ s => s.mem) fun s₀ s h => ⟨h.cr, rfl⟩) ?_
  refine Pc.seq (Pc.lift (textAbsorb_pc L.lay (D := p.2 6) (n := (p.2 7).toNat) (al := p.2 2) (ah := p.2 3)
    (xl := p.2 4) (xh := p.2 5)) (fun _ s => s.mem) fun s₀ s' ⟨s, h, co, rd, wr⟩ => ⟨?_, rfl⟩) ?_
  · obtain ⟨s₁, h₁, fr, rd₁, wr₁⟩ := h.ent
    have dw := cr_dataW hc h₁.pre h₁.pub (s := s') (by rw [wr, wr₁, h₁.wr])
    refine ⟨(co default).env, (h₁.ta.frame fr fun r hr => ?_).frame (co default).frame
      (kept_crFrame L h.cr.data), (p.2 7).isLt, DataOk.mono dw.ok (by decide) L.sp⟩
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  refine Pc.taint [.ebp] (fun s₀ s₄ ⟨s₃, ⟨s₂, h₂, co, rd₃, wr₃⟩, ta, rd₄, wr₄⟩ => ?_)
    (fun _ _ s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp]) (by taint_decide)
  obtain ⟨s₁, h₁, fr, rd₁, wr₁⟩ := h₂.ent
  have hf : Frame (pslotR (p.2 8) :: crFrame (p.2 1) (p.2 8) p.1 1536 (p.2 6) (p.2 7).toNat ++
      taFrame (p.2 1) (p.2 8) p.1 28) s₁.mem s₄.mem :=
    ((fr.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..).trans
      ((co default).frame.mono fun r hr => List.mem_cons_of_mem _ (List.mem_append_left _ hr))).trans
      (ta.frame.mono fun r hr => List.mem_cons_of_mem _ (List.mem_append_right _ hr))
  refine WP.mono (cr_exit hc h₁ ta.env hf) fun s' ⟨abi, m'⟩ => ⟨abi, fun iv a pt hr hl hpt => ?_⟩
  have hA : ∀ i, i < 9 → arg s₀ i = p.2 i := fun i hi => pubOf_arg h₁.pub hi
  dsimp only
  rw [hA 0 (by decide), hA 1 (by decide)] at hr
  rw [hA 2 (by decide), hA 3 (by decide)] at hl
  rw [hA 4 (by decide), hA 5 (by decide)] at hpt
  rw [hA 0 (by decide), hA 1 (by decide), hA 6 (by decide), hA 7 (by decide), m']
  generalize hci : ctxCiph s₀.mem (w64 (p.2 0)) = ciph at hr ⊢
  generalize hH : ctxH s₀.mem (w64 (p.2 0)) = H at hr ⊢
  have fW := cset_frame h₁ fr
  have hC2 : ciphOf s₂.mem (p.2 0) = ciph := by
    rw [← hci]; exact ciph_frame fW (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cw.sub_right (Lay.wSub (by decide)))
  have hH2 : Hk s₂.mem (p.2 0) = H := by
    rw [← hH, ctxH_eq]; exact blockAt_frame fW fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
  have hr₂ := streamRepr_frame fW (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.sb) hr
  rw [← hC2, ← hH2] at hr₂
  rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit] at hr₂
  obtain ⟨hj, ha, hct⟩ := hr₂
  rw [hH2] at hj
  rw [hC2, hH2] at ha hct
  have hP : (gctr ciph (inc32 (j0 H iv)) pt).length = (p.2 5 ++ p.2 4).toNat := by
    rw [Proof.Gcm.length_gctr, hpt]
  rw [hP] at hct
  have hco := co (inc32 (j0 H iv))
  have hct' : CtrS s₂.mem (p.2 1) (ciphOf s₂.mem (p.2 0)) (inc32 (j0 H iv))
      (p.2 5 ++ p.2 4).toNat := by rw [hC2]; exact hct
  have hct₃ := hco.ctr hct'
  have hout := hco.out hct'
  rw [hC2] at hct₃ hout
  have hd := h₂.cr.data
  have hfit := hd.ok.fit
  have hD2 : bytesAt s₂.mem (w64 (p.2 6)) (p.2 7).toNat = bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat :=
    bytesAt_frame fW (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hc.dw.sub_right (Lay.wSub (by decide))) (by omega)
  rw [hD2] at hout
  have hH3 : Hk s₃.mem (p.2 0) = H := by
    rw [← hH2]; exact blockAt_frame hco.frame fun r hr =>
      (ctx_crFrame L hd r hr).sub_left (Lay.ctxSub (by decide))
  have ha₃ : Absorbed s₃.mem (w64 (p.2 1) + BitVec.ofNat 64 16) (w64 (p.2 1) + BitVec.ofNat 64 32)
      (Hk s₃.mem (p.2 0)) (Spec.Gcm.ghashInput a (gctr ciph (inc32 (j0 H iv)) pt)) := by
    rw [hH3]
    exact ha.congr (blockAt_frame hco.frame (st_crFrame hc (by decide)))
      (bytesAt_frame hco.frame (st_crFrame hc (d := 32) (k := (Spec.Gcm.ghashInput a _).length % 16) (by omega))
        (by omega))
  have hab := ta.abs a (gctr ciph (inc32 (j0 H iv)) pt) ⟨hl, by rw [Proof.Gcm.length_gctr, hpt]⟩ ha₃
  rw [hout, hH3] at hab
  have hcnew : gctr ciph (inc32 (j0 H iv)) (pt ++ bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat) =
      gctr ciph (inc32 (j0 H iv)) pt ++
        xorKs ciph (inc32 (j0 H iv)) (p.2 5 ++ p.2 4).toNat (bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat) := by
    rw [Proof.Gcm.gctr_append, hpt]
  have dT := data_taFrame (D := p.2 6) (n := (p.2 7).toNat) (DataOk.mono hd.ok (k := 28) (by decide) L.sp)
  refine ⟨?_, ?_⟩
  · rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit, hcnew]
    refine ⟨?_, hab, ?_⟩
    · have e₁ := blockAt_frame ta.frame (st_taFrame hc (d := 0) (k := 16) (.inl (by decide)))
      have e₂ := blockAt_frame hco.frame (st_crFrame hc (d := 0) (k := 16) (by decide))
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at e₁ e₂
      rw [e₁, e₂, hj]
    · rw [List.length_append, Proof.Gcm.length_gctr, Proof.Gcm.length_xorKs, length_bytesAt, ← hpt]
      exact hct₃.congr (blockAt_frame ta.frame (st_taFrame hc (.inr ⟨by decide, by decide⟩)))
        (blockAt_frame ta.frame (st_taFrame hc (.inr ⟨by decide, by decide⟩)))
  · rw [bytesAt_frame ta.frame dT (by omega), hout, hcnew,
      List.drop_left' (by rw [Proof.Gcm.length_gctr])]

theorem streamEncrypt_correct (s : State) (hs : streamEncryptX86.pre s) :
    ∃ t s', Exec isa (streamEncrypt vg.callees) s t s' ∧ abiPreserved s s' ∧ streamEncryptX86.post s s' :=
  (streamEncrypt_pc (pubOf 9 s)).wp s s ⟨hs, rfl, rfl⟩

theorem streamEncrypt_ct : ConstantTime isa streamEncryptX86.pre streamEncryptX86.pub (streamEncrypt vg.callees) :=
  Pc.constantTime (pubOf 9) (fun _ _ _ _ h => pubOf_eq h) streamEncrypt_pc fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.Sm4Gcm.X86
