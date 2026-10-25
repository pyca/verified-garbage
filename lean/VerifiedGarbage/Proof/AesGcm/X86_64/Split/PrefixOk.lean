module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Prefix
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# AES-GCM `seal_split` on x86-64: `prefix`

Untrusted: everything here is checked by Lean. `prefix` leaves the
`q = ⌊sl / 16⌋` whole blocks at `src` encrypted to `dst` and absorbed, the
counter block advanced by `q`, the `sl mod 16` bytes left copied after them,
`len` kept at `auxO` and the data from those bytes on as the data
(`prefix_ok`), having written only the counter block and `Y`, the blocks and
the bytes copied, the slots it keeps, the call's working space and the 56
bytes below `SP`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

/-- The counter block and `Y` of the state. -/
abbrev cbA (W : Addr) : Addr := W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48
abbrev yA (W : Addr) : Addr := W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16

/-- After the call (or none, for no whole block): what it did. -/
structure Mid2 (Ctx W SP D S : Addr) (R sl : Nat) (s s₂ : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  frame : Frame (callWr W D (sl / 16) ++ [below SP 56]) s.mem s₂.mem
  blocks : blocksAt s₂.mem D (sl / 16) = ctr32 (ctxCiph s.mem Ctx R) (blockAt s.mem (cbA W)) (blocksAt s.mem S (sl / 16))
  ctr : blockAt s₂.mem (cbA W) = Nat.repeat inc32 (sl / 16) (blockAt s.mem (cbA W))
  y : blockAt s₂.mem (yA W) = ghashFrom (ctxH s.mem Ctx) (blockAt s.mem (yA W)) (blocksAt s₂.mem D (sl / 16))

/-- What `prefix` leaves. -/
structure PPost (Ctx W SP D S : Addr) (R n sl : Nat) (s s' : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame (callWr W D (sl / 16) ++ [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩,
    ⟨W + BitVec.ofNat 64 200, 24⟩, below SP 56]) s.mem s'.mem
  blocks : blocksAt s'.mem D (sl / 16) = ctr32 (ctxCiph s.mem Ctx R) (blockAt s.mem (cbA W)) (blocksAt s.mem S (sl / 16))
  ctr : blockAt s'.mem (cbA W) = Nat.repeat inc32 (sl / 16) (blockAt s.mem (cbA W))
  y : blockAt s'.mem (yA W) = ghashFrom (ctxH s.mem Ctx) (blockAt s.mem (yA W)) (blocksAt s'.mem D (sl / 16))
  tail : bytesAt s'.mem (D + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16) =
    bytesAt s.mem (S + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16)
  dat : s'.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (16 * (sl / 16))
  len : s'.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - 16 * (sl / 16))
  aux : s'.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n

section
variable {M : CtxMode} {Ctx W SP D S : Addr} {R n sl : Nat} {s : State} (h : PP M Ctx W SP D S R n sl s)
include h

/-- A slot of `W` from `W + 128` on is apart from what the call writes. -/
theorem slot_disj {q d : Nat} (hq : q * 16 ≤ n) (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 448) :
    ∀ r ∈ callWr W D q ++ [below SP 56], (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  have L := h.lay
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | rfl
  · rw [add_ofNat_assoc]; exact L.w_w (.inr (by omega)) (by omega) (by decide)
  · rw [add_ofNat_assoc]; exact L.w_w (.inr (by omega)) (by omega) (by decide)
  · exact ((h.data.ok.w.sub_left (Region.sub_prefix hq)).sub_right (Lay.wSub (by omega))).symm
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (h.kw.sub_right (Lay.wSub (by omega))).symm

/-- `src` is apart from what the call writes. -/
theorem src_disj {q : Nat} (hq : q * 16 ≤ n) {p : Addr} {k : Nat} (hs : Region.Sub ⟨p, k⟩ ⟨S, sl⟩) :
    ∀ r ∈ callWr W D q ++ [below SP 56], (⟨p, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | rfl
  · exact (h.sW.sub_left hs).sub_right (fun a hc => st_w a (cb_sub a hc))
  · exact (h.sW.sub_left hs).sub_right (fun a hc => st_w a (y_sub a hc))
  · exact (h.sD.sub_left hs).sub_right (Region.sub_prefix hq)
  · exact (h.sW.sub_left hs).sub_right sc_w
  · exact (h.ks.sub_right hs).symm

/-- A slot of `W` from `W + 128` on is apart from what the call and the copy write. -/
theorem slot_disj2 {d : Nat} (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 448) :
    ∀ r ∈ callWr W D (sl / 16) ++ [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩, below SP 56],
      (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  have hsl := h.sl_le
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact slot_disj h (by omega) h₁ h₂ r (List.mem_append_left _ hr)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((h.data.ok.w.sub_left (Offset.sub_base D (by omega))).sub_right (Lay.wSub (by omega))).symm
    · exact slot_disj h (q := sl / 16) (by omega) h₁ h₂ _ (List.mem_append_right _ (List.mem_singleton_self _))

/-- `rest`, after the bytes left are copied (or none): what `prefix` leaves. -/
theorem rest_ok {s₄ : State} (he₄ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₄) (rd₄ : s₄.rd = s.rd)
    (wr₄ : s₄.wr = s.wr)
    (fr₄ : Frame (callWr W D (sl / 16) ++ [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩, below SP 56])
      s.mem s₄.mem)
    (bl₄ : blocksAt s₄.mem D (sl / 16) =
      ctr32 (ctxCiph s.mem Ctx R) (blockAt s.mem (cbA W)) (blocksAt s.mem S (sl / 16)))
    (ct₄ : blockAt s₄.mem (cbA W) = Nat.repeat inc32 (sl / 16) (blockAt s.mem (cbA W)))
    (y₄ : blockAt s₄.mem (yA W) = ghashFrom (ctxH s.mem Ctx) (blockAt s.mem (yA W)) (blocksAt s₄.mem D (sl / 16)))
    (tl₄ : bytesAt s₄.mem (D + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16) =
      bytesAt s.mem (S + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16)) :
    WP isa (.block SealSplit.rest) s₄ (PPost Ctx W SP D S R n sl s) := by
  have L := h.lay
  have hn := h.data.ok.lt
  have hsl := h.sl_le
  have kp : ∀ d, 128 ≤ d → d + 8 ≤ 448 → s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => fr₄.readW (Region.contains_self _ _) (slot_disj2 h h₁ h₂) (by decide)
  refine WP.mono (pre4_ok (D := D) hn hsl he₄ (by rw [kp 200 (by decide) (by decide)]; exact h.dat)
    (by rw [kp 208 (by decide) (by decide)]; exact h.len) (by rw [kp 192 (by decide) (by decide)]; exact h.slen))
    fun s₅ ⟨d₅, l₅, a₅, f₅, g₅, rd₅, wr₅⟩ => ?_
  have W200 : ∀ {p : Addr} {k : Nat}, (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ →
      ∀ r ∈ [(⟨W + BitVec.ofNat 64 200, 24⟩ : Region)], (⟨p, k⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd.sub_right (Lay.wSub (by decide))
  have dB : (⟨D, 16 * (sl / 16)⟩ : Region).Disjoint ⟨W, 2560⟩ := h.data.ok.w.sub_left (Region.sub_prefix (by omega))
  have dT : (⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩ : Region).Disjoint ⟨W, 2560⟩ :=
    h.data.ok.w.sub_left (Offset.sub_base D (by omega))
  have cW : ∀ {p : Addr}, (⟨p, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 200, 24⟩ →
      ∀ r ∈ [(⟨W + BitVec.ofNat 64 200, 24⟩ : Region)], (⟨p, 16⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  have eB : blocksAt s₅.mem D (sl / 16) = blocksAt s₄.mem D (sl / 16) :=
    blocksAt_frame f₅ (W200 dB) (by omega)
  have eC : blockAt s₅.mem (cbA W) = blockAt s₄.mem (cbA W) :=
    blockAt_frame f₅ (cW (by simp only [cbA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide)))
  have eY : blockAt s₅.mem (yA W) = blockAt s₄.mem (yA W) :=
    blockAt_frame f₅ (cW (by simp only [yA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide)))
  refine ⟨he₄.keep g₅ rd₅ wr₅, rd₅.trans rd₄, wr₅.trans wr₄, ?_, by rw [eB, bl₄], by rw [eC, ct₄],
    by rw [eY, eB, y₄], by rw [bytesAt_frame f₅ (W200 dT) (by omega), tl₄], d₅, l₅, a₅⟩
  refine (fr₄.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp, fun _ h => h⟩

/-- After the call (or none): the bytes left copied, and `rest`. -/
theorem tail_ok {s₂ : State} (H : Mid2 Ctx W SP D S R sl s s₂) :
    WP isa (.seq (.block SealSplit.copyArgs) (.seq (.ite .e (.block []) copyLoop) (.block SealSplit.rest))) s₂
      (PPost Ctx W SP D S R n sl s) := by
  have L := h.lay
  have hn := h.data.ok.lt
  have hsl := h.sl_le
  have kp : ∀ d, 128 ≤ d → d + 8 ≤ 448 → s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => H.frame.readW (Region.contains_self _ _) (slot_disj h (q := sl / 16) (by omega) h₁ h₂) (by decide)
  refine WP.seq (WP.mono (pre3_ok (D := D) (S := S) (sl := sl) (by omega) H.env (by rw [kp 200 (by decide) (by decide)]; exact h.dat)
    (by rw [kp 224 (by decide) (by decide)]; exact h.src) (by rw [kp 192 (by decide) (by decide)]; exact h.slen))
    fun s₃ ⟨cx₃, si₃, di₃, zf₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  have he₃ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₃ := H.env.keep g₃ rd₃ wr₃
  have fr₂ : Frame (callWr W D (sl / 16) ++ [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩, below SP 56])
      s.mem s₂.mem := H.frame.mono fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · simp only [List.mem_singleton] at hr; subst hr; simp
  have hs₂ : bytesAt s₂.mem (S + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16) =
      bytesAt s.mem (S + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16) :=
    bytesAt_frame H.frame (src_disj h (q := sl / 16) (by omega) (Offset.sub_base S (by omega))) (by omega)
  refine WP.seq (WP.ite (decide (sl % 16 = 0)) (by simp only [eval, zf₃]) (fun h0 => ?_) (fun h0 => ?_))
  · have h0' : sl % 16 = 0 := of_decide_eq_true h0
    refine WP.block_nil (rest_ok h he₃ (rd₃.trans H.rd) (wr₃.trans H.wr) (by rw [m₃]; exact fr₂)
      (by rw [m₃]; exact H.blocks) (by rw [m₃]; exact H.ctr) (by rw [m₃]; exact H.y) ?_)
    rw [h0']; rfl
  · have h0' : sl % 16 ≠ 0 := of_decide_eq_false h0
    have e1 : 16 * (sl / 16) + sl % 16 ≤ sl := by omega
    have e2 : 16 * (sl / 16) + sl % 16 ≤ n := by omega
    have sl64 : sl < 2 ^ 64 := by omega
    have c1 : Covers [⟨S + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩] (s₃.rd ++ s₃.wr) := by
      rw [rd₃, wr₃, H.rd, H.wr]; exact covers_off' h.srcCov e1 sl64
    have c2 : Covers [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩] s₃.wr := by
      rw [wr₃, H.wr]; exact covers_off' h.data.wr e2 hn
    have hlp : LoopPre s₃ (S + BitVec.ofNat 64 (16 * (sl / 16))) (D + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16) :=
      ⟨si₃, di₃, cx₃, by omega, by omega, c1, c2,
        (h.sD.sub_left (Offset.sub_base S (by omega))).sub_right (Offset.sub_base D (by omega))⟩
    refine WP.mono (copyLoop_ok s₃ hlp) fun s₄ ⟨m₄, g₄, rd₄, wr₄⟩ => ?_
    have he₄ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ := he₃.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₄ _ (by decide) (by decide)) rd₄ wr₄
    have fC : Frame [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩] s₃.mem s₄.mem := by
      rw [m₄]; exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Region.contains_self _ _)
    have one : ∀ {p : Addr} {k : Nat}, (⟨p, k⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩ →
        ∀ r ∈ [(⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩ : Region)], (⟨p, k⟩ : Region).Disjoint r :=
      fun hd r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd
    have dDT := h.data.ok.w
    have dBT : (⟨D, 16 * (sl / 16)⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩ := by
      have hw := h.data.ok.wrap
      simpa using Offset.disjoint D (d := 0) (n := 16 * (sl / 16)) (e := 16 * (sl / 16))
        (k := sl % 16) (.inl (by omega)) (by omega) (by omega)
    have eB : blocksAt s₄.mem D (sl / 16) = blocksAt s₃.mem D (sl / 16) :=
      blocksAt_frame fC (one dBT) (by omega)
    have tW : (⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩ : Region).Disjoint ⟨W, 2560⟩ :=
      dDT.sub_left (Offset.sub_base D (by omega))
    have eC : blockAt s₄.mem (cbA W) = blockAt s₃.mem (cbA W) :=
      blockAt_frame fC (one ((tW.sub_right (fun a hc => st_w a (cb_sub a hc))).symm))
    have eY : blockAt s₄.mem (yA W) = blockAt s₃.mem (yA W) :=
      blockAt_frame fC (one ((tW.sub_right (fun a hc => st_w a (y_sub a hc))).symm))
    have fC' : Frame (callWr W D (sl / 16) ++ [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩, below SP 56])
        s₂.mem s₄.mem := by
      rw [← m₃]
      exact fC.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    refine rest_ok h he₄ (rd₄.trans (rd₃.trans H.rd)) (wr₄.trans (wr₃.trans H.wr)) (fr₂.trans fC')
      (by rw [eB, m₃]; exact H.blocks) (by rw [eC, m₃]; exact H.ctr) (by rw [eY, eB, m₃]; exact H.y) ?_
    rw [m₄]
    have := bytesAt_writeBytes_self s₃.mem (D + BitVec.ofNat 64 (16 * (sl / 16)))
      (bytesAt s₃.mem (S + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16)) (by rw [length_bytesAt]; omega)
    rw [length_bytesAt] at this
    rw [this, m₃, hs₂]

/-- The call of `prefix` for the `sl / 16` whole blocks at `src`, from a
state `s₁` with their number in `rax` and `s`'s memory: what `Mid2` says. -/
theorem call_ok (T : BlkToFn M) {s₁ : State} (he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁)
    (ax₁ : s₁.gpr .rax = BitVec.ofNat 64 (sl / 16)) (m₁ : s₁.mem = s.mem) (rd₁ : s₁.rd = s.rd)
    (wr₁ : s₁.wr = s.wr) :
    WP isa (.seq (.block SealSplit.preArgs)
      (.frame (.push [.rax, .r10, .r11]) (.call T.fn.name T.fn.code) (.pop .rax 3))) s₁
      (Mid2 Ctx W SP D S R sl s) := by
  have hn := h.data.ok.lt
  have hsl := h.sl_le
  refine WP.seq (WP.mono (pre2_ok (R := R) (D := D) (S := S) he₁ (by rw [m₁]; exact h.rounds) (by rw [m₁]; exact h.dat)
    (by rw [m₁]; exact h.src)) fun s₂ ⟨di₂, si₂, dx₂, cx₂, r8₂, r9₂, r10₂, r11₂, ax₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  have he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁.keep g₂ rd₂ wr₂
  exact WP.mono (preCall_ok h T (q := sl / 16) (by omega) he₂.rsp (rd₂.trans rd₁) (wr₂.trans wr₁)
    (m₂.trans m₁) di₂ si₂ dx₂ cx₂ r8₂ (by rw [r9₂, ax₁]) (by rw [r10₂, ax₁]) r11₂ ax₂)
    fun s₃ ⟨cs₃, rd₃, wr₃, fr₃, bl₃, ct₃, y₃⟩ => ⟨he₂.keep (fun r hr => cs₃ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved])) rd₃ wr₃,
      rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), by rw [m₂, m₁] at fr₃; exact fr₃, bl₃, ct₃, y₃⟩

/-- `prefix`: the whole blocks at `src` encrypted to `dst` and absorbed by a
call of `vg_aes_gcm_encrypt_blocks_to` (`T`), the bytes left copied, and
`len` and the data from them on kept. -/
theorem prefix_ok (T : BlkToFn M) :
    WP isa (SealSplit.prefix T.fn) s (PPost Ctx W SP D S R n sl s) := by
  have L := h.lay
  have hn := h.data.ok.lt
  have hsl := h.sl_le
  have he := h.env
  unfold SealSplit.prefix
  refine WP.seq (WP.mono (pre1_ok (sl := sl) (by omega) he h.slen) fun s₁ ⟨ax₁, zf₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) rd₁ wr₁
  refine WP.seq (WP.ite (decide (sl / 16 = 0)) (by simp only [eval, zf₁]) (fun h0 => ?_) (fun h0 => ?_))
  · -- No whole block at `src`.
    have h0' : sl / 16 = 0 := of_decide_eq_true h0
    refine WP.block_nil (tail_ok h ⟨he₁, rd₁, wr₁, by rw [m₁]; exact Frame.refl _ _, ?_, ?_, ?_⟩)
    · rw [h0']; rfl
    · rw [h0', m₁]; rfl
    · rw [h0', m₁]; rfl
  · exact WP.mono (call_ok h T he₁ ax₁ m₁ rd₁ wr₁) fun _ H => tail_ok h H

end

end VG.Proof.AesGcm.X86_64.Split
