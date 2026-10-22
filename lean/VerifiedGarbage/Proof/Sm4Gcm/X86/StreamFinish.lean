module

public import VerifiedGarbage.Proof.Sm4Gcm.X86.FinTag
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.AesGcm.X86.Cmp
public import VerifiedGarbage.Proof.AesGcm.X86.Top
public import VerifiedGarbage.Proof.Sm4Gcm.X86.Contract
meta import VerifiedGarbage.Proof.Sm4Gcm.X86.FinTag
meta import VerifiedGarbage.Proof.AesGcm.X86.Cmp
meta import VerifiedGarbage.Proof.AesGcm.X86.Top
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.Impl.Sm4Gcm.X86
meta import VerifiedGarbage.Proof.Framework.X86.Call
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.State
meta import VerifiedGarbage.TCB.X86.Target

/-!
# SM4-GCM on x86: `vg_aes_gcm_stream_finish`

Untrusted: everything here is checked by Lean. The entry, the tag
(`finTag 0`), its copy to `tag` (`tagOut 0`) and the exit, as one `Pc`
(`streamFinish_pc`): correct (`streamFinish_correct`) and constant time
(`streamFinish_ct`). The entry is shared with `vg_aes_gcm_stream_verify`
(`finEntry_pc`), whose `W` is its last argument too: the pieces find it at 7
in the public data (`pubSw`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86

variable {vg : VG.Proof.AesGcm.X86.GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.Sm4Gcm.X86 VG.WriteBytes VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 hiding ctrCall keyCall ctrArgs cryptWhole cryptTail crypt tag init cryptEntry
  streamEncrypt streamDecrypt finEntry finTag streamFinish streamVerify oneEntry oneTag oneCrypt «seal» «open»
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr)
open VG.Spec.Gcm (ctxH)
open VG.Spec.Sm4.Gcm (ctxCiph)

abbrev finKeeps : List (Nat × Nat) := [(0, ctxO), (2, alO), (3, ahO), (4, xlO), (5, xhO)]

theorem streamFinish_eq : (streamFinish vg.callees) = .seq (entry 7 (([.mov .esi (argOp 1)] : List Instr) ++
    ((finKeeps ++ [(6, tpO)]).flatMap (fun (p : Nat × Nat) => keep p.1 p.2) ++ [])))
    (.seq (finTag vg.callees 0) (.seq (tagOut 0) (.block restore))) := rfl

/-- What the precondition of `finish` and `verify` (with `nA` arguments, `W`
the last, `w`) gives. -/
structure FinPre (nA w : Nat) (s : State) : Prop where
  cR : Covers [⟨w64 (arg s 0), 256⟩] (s.rd ++ s.wr)
  sW : Covers [⟨w64 (arg s 1), 80⟩] s.wr
  wW : Covers [⟨w64 (arg s w), 2560⟩] s.wr
  aR : Covers [⟨argAddr s 0, 4 * nA⟩] (s.rd ++ s.wr)
  cs : (⟨w64 (arg s 0), 256⟩ : Region).Disjoint ⟨w64 (arg s 1), 80⟩
  cw : (⟨w64 (arg s 0), 256⟩ : Region).Disjoint ⟨w64 (arg s w), 2560⟩
  sw : (⟨w64 (arg s 1), 80⟩ : Region).Disjoint ⟨w64 (arg s w), 2560⟩
  wa : (⟨w64 (arg s w), 2560⟩ : Region).Disjoint ⟨argAddr s 0, 4 * nA⟩
  r_s : (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 (arg s 1), 80⟩
  r_w : (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 (arg s w), 2560⟩
  k_c : (below (s.gpr .esp) 1536).Disjoint ⟨w64 (arg s 0), 256⟩
  k_s : (below (s.gpr .esp) 1536).Disjoint ⟨w64 (arg s 1), 80⟩
  k_w : (below (s.gpr .esp) 1536).Disjoint ⟨w64 (arg s w), 2560⟩
  fc : (arg s 0).toNat + 256 ≤ 2 ^ 32
  fs : (arg s 1).toNat + 80 ≤ 2 ^ 32
  fw : (arg s w).toNat + 2560 ≤ 2 ^ 32
  sp : 1536 ≤ (s.gpr .esp).toNat
  fa : (s.gpr .esp).toNat + 4 + 4 * nA ≤ 2 ^ 32

theorem finPre_of {s : State} (h : finPre s) : FinPre 8 7 s := by
  simp only [finPre] at h
  sig_split h
  rename_i hrd hwr d_cs hdrop3 d_cw hdrop5 hdrop6 d_sw hdrop8 hdrop9 hdrop10 d_wa hdrop12 r_s hdrop14 r_w
    hdrop16 k_c k_s hdrop19 k_w hdrop21 fc fs hdrop24 fw sp
  clear hdrop3 hdrop5 hdrop6 hdrop8 hdrop9 hdrop10 hdrop12 hdrop14 hdrop16 hdrop19 hdrop21 hdrop24
  have fa := h
  clear h
  rw [ofNat_lit, below_eq sp] at k_c k_s k_w
  exact ⟨by rw [hrd, hwr]; exact covers_of_mem (by simp), by rw [hwr]; exact covers_of_mem (by simp),
    by rw [hwr]; exact covers_of_mem (by simp), by rw [hrd, hwr]; exact covers_of_mem (by simp), d_cs, d_cw, d_sw,
    d_wa, r_s, r_w, k_c, k_s, k_w, fc, fs, fw, sp, by omega⟩

/-- The tag `finish` writes. -/
theorem finPre_tag {s : State} (h : finPre s) : Covers [⟨w64 (arg s 6), 16⟩] s.wr ∧
    (arg s 6).toNat + 16 ≤ 2 ^ 32 ∧ (⟨w64 (arg s 6), 16⟩ : Region).Disjoint ⟨w64 (arg s 7), 2560⟩ ∧
    (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 (arg s 6), 16⟩ := by
  simp only [finPre] at h
  sig_split h
  rename_i hdrop0 hwr hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 hdrop7 hdrop8 d_tw hdrop10 hdrop11 hdrop12 hdrop13
    r_t hdrop15 hdrop16 hdrop17 hdrop18 hdrop19 hdrop20 hdrop21 hdrop22 hdrop23 ft hdrop25 hdrop26
  clear hdrop0 hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 hdrop7 hdrop8 hdrop10 hdrop11 hdrop12 hdrop13 hdrop15
    hdrop16 hdrop17 hdrop18 hdrop19 hdrop20 hdrop21 hdrop22 hdrop23 hdrop25 hdrop26
  clear h
  exact ⟨by rw [hwr]; exact covers_of_mem (by simp), ft, d_tw, r_t⟩

theorem verifyPre_of {s : State} (h : verifyPre s) : FinPre 9 8 s := by
  simp only [verifyPre] at h
  sig_split h
  rename_i hrd hwr d_cs d_cw hdrop4 hdrop5 hdrop6 hdrop7 d_sw hdrop9 d_wa hdrop11 r_s hdrop13 r_w hdrop15 k_c
    k_s hdrop18 k_w hdrop20 fc fs hdrop23 fw sp
  clear hdrop4 hdrop5 hdrop6 hdrop7 hdrop9 hdrop11 hdrop13 hdrop15 hdrop18 hdrop20 hdrop23
  have fa := h
  clear h
  rw [ofNat_lit, below_eq sp] at k_c k_s k_w
  exact ⟨by rw [hrd, hwr]; exact covers_of_mem (by simp), by rw [hwr]; exact covers_of_mem (by simp),
    by rw [hwr]; exact covers_of_mem (by simp), by rw [hrd, hwr]; exact covers_of_mem (by simp), d_cs, d_cw, d_sw,
    d_wa, r_s, r_w, k_c, k_s, k_w, fc, fs, fw, sp, by omega⟩

/-- The tag `verify` reads. -/
theorem verifyPre_tag {s : State} (h : verifyPre s) :
    Covers [⟨w64 (arg s 6), (arg s 7).toNat⟩] (s.rd ++ s.wr) ∧ (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32 ∧
      (⟨w64 (arg s 6), (arg s 7).toNat⟩ : Region).Disjoint ⟨w64 (arg s 8), 2560⟩ := by
  simp only [verifyPre] at h
  sig_split h
  rename_i hrd hwr hdrop2 hdrop3 hdrop4 hdrop5 d_tw hdrop7 hdrop8 hdrop9 hdrop10 hdrop11 hdrop12 hdrop13
    hdrop14 hdrop15 hdrop16 hdrop17 hdrop18 hdrop19 hdrop20 hdrop21 hdrop22 ft hdrop24 hdrop25
  clear hdrop2 hdrop3 hdrop4 hdrop5 hdrop7 hdrop8 hdrop9 hdrop10 hdrop11 hdrop12 hdrop13 hdrop14 hdrop15
    hdrop16 hdrop17 hdrop18 hdrop19 hdrop20 hdrop21 hdrop22 hdrop24 hdrop25
  clear h
  exact ⟨by rw [hrd, hwr]; exact covers_of_mem (by simp), ft, d_tw⟩

theorem FinPre.lay {nA w : Nat} {s : State} (h : FinPre nA w s) :
    Lay4 (arg s 0) (arg s 1) (arg s w) (s.gpr .esp) 1536 :=
  Lay4.of h.fc h.fs h.fw (by decide) h.sp h.cs h.cw (h.sw.sub_right (Region.sub_prefix (by decide)))
    (h.sw.sub_right (Lay.wSub (by decide))) h.k_c h.k_s h.k_w

/-- The layout of `finish` and `verify`, for the public data `p` (`W` at 6). -/
structure FinL (p : BitVec 32 × (Nat → BitVec 32)) : Prop where
  L : Lay4 (p.2 0) (p.2 1) (p.2 6) p.1 1536
  r_s : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 1), 80⟩
  r_w : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 6), 2560⟩

theorem FinPre.fl {nA w : Nat} {s : State} (h : FinPre nA w s) (hw : nA = w + 1) (h7 : 7 ≤ w)
    {p : BitVec 32 × (Nat → BitVec 32)} (hp : pubSw nA 6 s = p) : FinL p := by
  have a : ∀ i, i < 6 → arg s i = p.2 i := fun i hi => pubSw_arg hp (by omega) (by omega) (by omega)
  have aW : arg s w = p.2 6 := pubSw_W hp (by omega) hw
  have esp := pubSw_esp hp
  have L := h.lay
  have r_s := h.r_s
  have r_w := h.r_w
  rw [a 0 (by decide), a 1 (by decide), aW, esp] at L
  rw [esp, a 1 (by decide)] at r_s
  rw [esp, aW] at r_w
  exact ⟨L, r_s, r_w⟩

/-- After the entry of `finish` or `verify`. -/
structure FinEnt (nA w : Nat) (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  pre : FinPre nA w s₀
  pub : pubSw nA 6 s₀ = p
  fin : FinIn (p.2 0) (p.2 1) (p.2 6) p.1 (p.2 2) (p.2 3) (p.2 4) (p.2 5) s
  saved : SavedAt s.mem (p.2 6) s₀
  frame : Frame [⟨w64 (p.2 6) + BitVec.ofNat 64 128, 2432⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The entry of `finish` and `verify`, copying also the arguments `ex`. -/
theorem finEntry_pc (nA w : Nat) (hw : nA = w + 1) (h7 : 7 ≤ w) (ex : List (Nat × Nat))
    (hex : ∀ q ∈ finKeeps ++ ex, q.1 < nA ∧ 144 ≤ q.2 ∧ q.2 + 4 ≤ 2560 ∧ q.2 % 4 = 0)
    (hnd : ((finKeeps ++ ex).map (·.2)).Nodup) (Pre : State → Prop) (hPre : ∀ s, Pre s → FinPre nA w s)
    (p : BitVec 32 × (Nat → BitVec 32)) {hh₀ hh : Taint.Hint VG.X86.taint.T}
    (ht₀ : (VG.X86.taint.check (τr [.esp]) (.block [.mov .eax (argOp w)]) hh₀).isSome = true)
    (ht : (VG.X86.taint.check (τr [.eax, .esp]) (.block (saveAt ++ (([.mov .esi (argOp 1)] : List Instr) ++
      ((finKeeps ++ ex).flatMap (fun p => keep p.1 p.2) ++ [])))) hh).isSome = true) :
    Pc (fun (s₀ : State) s => Pre s₀ ∧ pubSw nA 6 s₀ = p ∧ s = s₀)
      (entry w (([.mov .esi (argOp 1)] : List Instr) ++ ((finKeeps ++ ex).flatMap (fun p => keep p.1 p.2) ++ [])))
      (fun s₀ s => FinEnt nA w p s₀ s ∧ (∀ q ∈ ex, slotv s.mem (p.2 6) q.2 = arg s₀ q.1) ∧ Pre s₀) := by
  refine ⟨fun s₀ s ⟨hpre, hpub, hs⟩ => ?_, ?_⟩
  · subst s
    have h := hPre _ hpre
    have L := h.lay
    have a : ∀ i, i < 6 → arg s₀ i = p.2 i := fun i hi => pubSw_arg hpub (by omega) (by omega) (by omega)
    have aW : arg s₀ w = p.2 6 := pubSw_W hpub (by omega) hw
    have esp := pubSw_esp hpub
    have rA : Covers [argsR (s₀.gpr .esp) nA] (s₀.rd ++ s₀.wr) := by rw [argsR_eq]; exact h.aR
    have aw : (argsR (s₀.gpr .esp) nA).Disjoint ⟨w64 (arg s₀ w), 2560⟩ := by rw [argsR_eq]; exact h.wa.symm
    refine entry_ok (finKeeps ++ ex) [] (by omega) (by omega) hex hnd rfl rfl h.wW rA aw h.fa h.fw fun s₂ e => ?_
    have he : Env (arg s₀ 0) (arg s₀ 1) (arg s₀ w) (s₀.gpr .esp) s₂ :=
      ⟨e.ebp, e.esi, e.esp, by rw [e.rd, e.wr]; exact h.cR, by rw [e.wr]; exact h.sW, by rw [e.wr]; exact h.wW,
        e.slots (0, ctxO) (by simp)⟩
    refine ⟨s₂, rfl, ⟨h, hpub, ?_, ?_, ?_, e.rd, e.wr⟩, fun q hq => by rw [← aW]; exact e.slots q (by simp [hq]),
      hpre⟩
    · rw [← a 0 (by omega), ← a 1 (by omega), ← a 2 (by omega), ← a 3 (by omega), ← a 4 (by omega),
        ← a 5 (by omega), ← aW, ← esp]
      exact ⟨he, e.slots (2, alO) (by simp), e.slots (3, ahO) (by simp), e.slots (4, xlO) (by simp),
        e.slots (5, xhO) (by simp)⟩
    · rw [← aW]; exact e.saved
    · rw [← aW]; exact e.frame
  · refine CT.seq (J := fun s => s.gpr .eax = p.2 6 ∧ s.gpr .esp = p.1)
      (CT.taint [.esp] (fun s₁ s₂ ⟨a₁, _, h₁, e₁⟩ ⟨a₂, _, h₂, e₂⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; subst e₁; subst e₂
        rw [pubSw_esp h₁, pubSw_esp h₂]) ht₀) (fun s ⟨s₀, hpre, hpub, hs⟩ => ?_)
      (CT.taint [.eax, .esp] (fun s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2, h₂.2]) ht)
    subst s
    have h := hPre _ hpre
    have rA : Covers [argsR (s₀.gpr .esp) nA] (s₀.rd ++ s₀.wr) := by rw [argsR_eq]; exact h.aR
    exact WP.mono (arg0_ok (argIn_of rA h.fa (by omega))) fun s' ⟨ax, sp⟩ =>
      ⟨by rw [ax]; exact pubSw_W hpub (by omega) hw, by rw [sp]; exact pubSw_esp hpub⟩

/-- Our caller's registers, outside the regions the tag is computed in. -/
theorem saved_tagFrame {Ctx St W SP : BitVec 32} (L : Lay4 Ctx St W SP 1536) :
    ∀ r ∈ tagFrame St W SP 0, (savedR W).Disjoint r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using (L.st_w (a := 0) (n := 32) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

/-- The return address, outside the regions the tag is computed in. -/
theorem ret_tagFrame {p : BitVec 32 × (Nat → BitVec 32)} (FL : FinL p) :
    ∀ r ∈ tagFrame (p.2 1) (p.2 6) p.1 0, (⟨w64 p.1, 4⟩ : Region).Disjoint r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact FL.r_s.sub_right (Region.sub_prefix (by decide))
  · exact FL.r_w.sub_right (Lay.wSub (by decide))
  · exact FL.r_w.sub_right (Lay.wSub (by decide))
  · exact FL.r_w.sub_right (Lay.wSub (by decide))
  · exact ret_below FL.L.sp

/-- The exit of `finish` and `verify`, after the pieces wrote within `rs`,
apart from our caller's registers and the return address. -/
theorem fin_exit {nA w : Nat} {p : BitVec 32 × (Nat → BitVec 32)} {s₀ s₁ s : State} (h₁ : FinEnt nA w p s₀ s₁)
    (FL : FinL p) (he : Env (p.2 0) (p.2 1) (p.2 6) p.1 s) {rs : List Region} (hf : Frame rs s₁.mem s.mem)
    (hS : ∀ r ∈ rs, (savedR (p.2 6)).Disjoint r) (hR : ∀ r ∈ rs, (⟨w64 p.1, 4⟩ : Region).Disjoint r) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .eax = s.gpr .eax := by
  have esp := pubSw_esp h₁.pub
  have hsv : SavedAt s.mem (p.2 6) s₀ := h₁.saved.frame hf hS
  have rE : ∀ r ∈ [(⟨w64 (p.2 6) + BitVec.ofNat 64 128, 2432⟩ : Region)], (⟨w64 p.1, 4⟩ : Region).Disjoint r :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact FL.r_w.sub_right (Lay.wSub (by decide))
  have hret : s.mem.readW (w64 (s₀.gpr .esp)) 32 = s₀.mem.readW (w64 (s₀.gpr .esp)) 32 := by
    rw [esp, ret_kept hf hR, ret_kept h₁.frame rE]
  exact WP.mono (exit_ok he.ebp (by rw [he.esp, esp]) (covers_left he.wW) FL.L.fw hsv hret)
    fun s' ⟨abi, m', ax, _, _⟩ => ⟨abi, m', ax⟩

/-- The streaming state and the key context, as the pieces see them after the entry. -/
theorem fin_repr {nA w : Nat} {p : BitVec 32 × (Nat → BitVec 32)} {s₀ s₁ : State} (h₁ : FinEnt nA w p s₀ s₁)
    (L : Lay4 (p.2 0) (p.2 1) (p.2 6) p.1 1536) {iv a c : List Byte}
    (hr : StreamRepr s₀.mem (w64 (p.2 1)) (ctxCiph s₀.mem (w64 (p.2 0))) (ctxH s₀.mem (w64 (p.2 0))) iv a c) :
    StreamRepr s₁.mem (w64 (p.2 1)) (ciphOf s₁.mem (p.2 0)) (Hk s₁.mem (p.2 0)) iv a c ∧
      ciphOf s₁.mem (p.2 0) = ctxCiph s₀.mem (w64 (p.2 0)) ∧ Hk s₁.mem (p.2 0) = ctxH s₀.mem (w64 (p.2 0)) := by
  have hC : ciphOf s₁.mem (p.2 0) = ctxCiph s₀.mem (w64 (p.2 0)) :=
    ciph_frame h₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cw.sub_right (Lay.wSub (by decide)))
  have hH : Hk s₁.mem (p.2 0) = ctxH s₀.mem (w64 (p.2 0)) := by
    rw [ctxH_eq]
    exact blockAt_frame h₁.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
  refine ⟨?_, hC, hH⟩
  rw [hC, hH]
  exact streamRepr_frame h₁.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    simpa using L.st_w (a := 0) (n := 80) (d := 128) (k := 2432) (by decide) (.inr ⟨by decide, by decide⟩)) hr

/-- A word of `W` outside the regions the tag is computed in. -/
theorem slot_tagFrame {Ctx St W SP : BitVec 32} (L : Lay4 Ctx St W SP 1536) {m m' : Mem}
    (hf : Frame (tagFrame St W SP 0) m m') {o : Nat} (h₁ : 128 ≤ o) (h₂ : o + 4 ≤ 240) :
    slotv m' W o = slotv m W o := by
  rw [slotv_eq, slotv_eq]
  refine slot_frame hf fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · have := (L.st_w (a := 0) (n := 32) (d := o) (k := 4) (by decide) (.inr ⟨by omega, by omega⟩)).symm
    rwa [BitVec.add_zero] at this
  · exact Lay.w_w (d := 96) (k := 16) (.inr (by omega)) (by omega) (by decide)
  · exact Lay.w_w (d := 0) (k := 16) (.inr (by omega)) (by omega) (by decide)
  · exact Lay.w_w (d := 240) (k := 2320) (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w (by omega)).symm

theorem streamFinish_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => finPre s₀ ∧ pubSw 8 6 s₀ = p ∧ s = s₀) (streamFinish vg.callees)
      (fun s₀ s' => abiPreserved s₀ s' ∧ streamFinishX86.post s₀ s') := by
  by_cases hex : ∃ s₀, finPre s₀ ∧ pubSw 8 6 s₀ = p
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have FL : FinL p := (finPre_of hz).fl rfl (by decide) hzp
  have L := FL.L
  obtain ⟨-, fT, tw, rt⟩ := finPre_tag hz
  rw [pubSw_last hzp (m := 7) (by decide) rfl] at fT
  rw [pubSw_last hzp (m := 7) (by decide) rfl, pubSw_W hzp (m := 7) (by decide) rfl] at tw
  rw [pubSw_last hzp (m := 7) (by decide) rfl, pubSw_esp hzp] at rt
  rw [streamFinish_eq]
  refine Pc.seq (finEntry_pc 8 7 rfl (by decide) [(6, tpO)] (by decide) (by decide) finPre (fun _ h => finPre_of h) p
    (by taint_decide) (by taint_decide)) (Pc.seq (Pc.lift (finTag_pc L (o := 0) (.inl rfl)) (fun _ s => s.mem)
      fun s₀ s h => ⟨h.1.fin, rfl⟩) ?_)
  -- The tag copied to `tag`.
  refine Pc.seq (Pc.of (I := fun s => WEnv (p.2 6) s ∧ slotv s.mem (p.2 6) tpO = p.2 7 ∧
      Covers [⟨w64 (p.2 7), 16⟩] s.wr)
    (R := fun s s' => bytesAt s'.mem (w64 (p.2 7)) 16 = bytesAt s.mem (w64 (p.2 6) + BitVec.ofNat 64 0) 16 ∧
      Frame [⟨w64 (p.2 7), 16⟩] s.mem s'.mem ∧ s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
    (fun s hs => tagOut_ok hs.1 (by decide) hs.2.1 hs.2.2 fT) (tagOut_ct rfl fun s hs => ⟨hs.1, hs.2.1⟩) _
    (fun s₀ s' ⟨s, ⟨h₁, hv, hpre⟩, fo, rd, wr⟩ => ⟨⟨fo.env.ebp, fo.env.wW, L.fw⟩, by
      rw [slot_tagFrame L fo.frame (by decide) (by decide), hv (6, tpO) (by simp),
        pubSw_last h₁.pub (m := 7) (by decide) rfl], by
      rw [wr, h₁.wr, ← pubSw_last h₁.pub (m := 7) (by decide) rfl]; exact (finPre_tag hpre).1⟩)) ?_
  -- The exit.
  refine Pc.taint [.ebp] (fun s₀ s'' ⟨s', ⟨s, ⟨h₁, _, _⟩, fo, _, _⟩, b, f, bp, si, sp, rd, wr⟩ => ?_)
    (fun _ _ s₁ s₂ ⟨_, ⟨_, _, h₁, _⟩, _, _, e₁, _⟩ ⟨_, ⟨_, _, h₂, _⟩, _, _, e₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [e₁, e₂, h₁.env.ebp, h₂.env.ebp]) (by taint_decide)
  have tS : ∀ r ∈ [(⟨w64 (p.2 7), 16⟩ : Region)], (⟨w64 (p.2 6) + BitVec.ofNat 64 ctxO, 4⟩ : Region).Disjoint r :=
    fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (tw.sub_right (Lay.wSub (by decide))).symm
  have he : Env (p.2 0) (p.2 1) (p.2 6) p.1 s'' := fo.env.keep bp si sp rd wr (slot_frame f tS)
  have hf : Frame (tagFrame (p.2 1) (p.2 6) p.1 0 ++ [⟨w64 (p.2 7), 16⟩]) s.mem s''.mem :=
    (fo.frame.mono fun r hr => List.mem_append_left _ hr).trans (f.mono fun r hr => List.mem_append_right _ hr)
  refine WP.mono (fin_exit h₁ FL he hf (fun r hr => ?_) (fun r hr => ?_)) fun s₃ ⟨abi, m', _⟩ =>
    ⟨abi, fun iv a c hr hl ht => ?_⟩
  · rcases List.mem_append.mp hr with hr | hr
    · exact saved_tagFrame L r hr
    · simp only [List.mem_singleton] at hr; subst hr; exact (tw.sub_right (Lay.wSub (by decide))).symm
  · rcases List.mem_append.mp hr with hr | hr
    · exact ret_tagFrame FL r hr
    · simp only [List.mem_singleton] at hr; subst hr; exact rt
  have hA : ∀ i, i < 6 → arg s₀ i = p.2 i := fun i hi => pubSw_arg h₁.pub (by omega) (by omega) (by omega)
  rw [hA 0 (by decide), hA 1 (by decide)] at hr
  rw [hA 2 (by decide), hA 3 (by decide)] at hl
  rw [hA 4 (by decide), hA 5 (by decide)] at ht
  rw [hA 0 (by decide), pubSw_last h₁.pub (m := 7) (by decide) rfl, m', b]
  obtain ⟨hr₁, hC, hH⟩ := fin_repr h₁ L hr
  have := fo.tag iv a c hr₁ hl ht
  rw [hC, hH] at this
  exact this

theorem streamFinish_correct (s : State) (hs : streamFinishX86.pre s) :
    ∃ t s', Exec isa (streamFinish vg.callees) s t s' ∧ abiPreserved s s' ∧ streamFinishX86.post s s' :=
  (streamFinish_pc (pubSw 8 6 s)).wp s s ⟨hs, rfl, rfl⟩

theorem streamFinish_ct : ConstantTime isa streamFinishX86.pre streamFinishX86.pub (streamFinish vg.callees) :=
  Pc.constantTime (pubSw 8 6) (fun _ _ _ _ h => pubSw_eq (by decide) h) streamFinish_pc fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.Sm4Gcm.X86
