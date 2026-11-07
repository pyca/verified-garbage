module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixOk
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksToDec.Fn
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.BlkCall
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Steps
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# AES-GCM `open_split` on x86-64: the whole blocks at `src`

Untrusted: everything here is checked by Lean. `seal_split`'s `prefix`, with
a call of `vg_aes_gcm_decrypt_blocks_to` in place of
`vg_aes_gcm_encrypt_blocks_to` (`prefixD_ok`): as `Split.prefix_ok` proves,
from the same state (`Split.PP`), with `Y` continued over the ciphertext at
`src`, which the call absorbs (`preCallToDec_ok`), rather than over what it
writes (`Mid2D`, `PPostD`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.OpenSplit

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Proof.AesGcm.X86_64.Split
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (covers_cons' covers_nil' sub_add_ofNat off_bound stackArg_entry)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

/-- After the call (or none, for no whole block): what it did. -/
structure Mid2D (Ctx W SP D S : Addr) (R sl : Nat) (s s₂ : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  frame : Frame (callWr W D (sl / 16) ++ [below SP 56]) s.mem s₂.mem
  blocks : blocksAt s₂.mem D (sl / 16) = ctr32 (ctxCiph s.mem Ctx R) (blockAt s.mem (cbA W)) (blocksAt s.mem S (sl / 16))
  ctr : blockAt s₂.mem (cbA W) = Nat.repeat inc32 (sl / 16) (blockAt s.mem (cbA W))
  y : blockAt s₂.mem (yA W) = ghashFrom (ctxH s.mem Ctx) (blockAt s.mem (yA W)) (blocksAt s.mem S (sl / 16))

/-- What `prefix` leaves. -/
structure PPostD (Ctx W SP D S : Addr) (R n sl : Nat) (s s' : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame (callWr W D (sl / 16) ++ [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩,
    ⟨W + BitVec.ofNat 64 200, 24⟩, below SP 56]) s.mem s'.mem
  blocks : blocksAt s'.mem D (sl / 16) = ctr32 (ctxCiph s.mem Ctx R) (blockAt s.mem (cbA W)) (blocksAt s.mem S (sl / 16))
  ctr : blockAt s'.mem (cbA W) = Nat.repeat inc32 (sl / 16) (blockAt s.mem (cbA W))
  y : blockAt s'.mem (yA W) = ghashFrom (ctxH s.mem Ctx) (blockAt s.mem (yA W)) (blocksAt s.mem S (sl / 16))
  tail : bytesAt s'.mem (D + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16) =
    bytesAt s.mem (S + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16)
  dat : s'.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (16 * (sl / 16))
  len : s'.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - 16 * (sl / 16))
  aux : s'.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n

section
variable {M : CtxMode} {Ctx W SP D S : Addr} {R n sl : Nat} {s : State} (h : PP M Ctx W SP D S R n sl s)
include h

/-- The call of `vg_aes_gcm_decrypt_blocks_to` on the `q` whole blocks at
`S`, to `D`, with `D`, `q` and the working space pushed for it. -/
theorem preCallToDec_ok (T : BlkToDecFn M) {q : Nat} (hq : 16 * q ≤ sl) {st : State}
    (hsp : st.gpr .rsp = SP) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) (hm : st.mem = s.mem)
    (h_di : st.gpr .rdi = Ctx) (h_si : st.gpr .rsi = BitVec.ofNat 64 R)
    (h_dx : st.gpr .rdx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)
    (h_cx : st.gpr .rcx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (h_8 : st.gpr .r8 = S)
    (h_9 : st.gpr .r9 = BitVec.ofNat 64 q) (h_10 : st.gpr .r10 = BitVec.ofNat 64 q) (h_11 : st.gpr .r11 = D)
    (h_ax : st.gpr .rax = W + BitVec.ofNat 64 448) :
    WP isa (.frame (.push [.rax, .r10, .r11]) (.call T.fn.name T.fn.code) (.pop .rax 3)) st fun st' =>
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.rd = st.rd ∧ st'.wr = st.wr ∧
      Frame (callWr W D q ++ [below SP 56]) st.mem st'.mem ∧
      blocksAt st'.mem D q = ctr32 (ctxCiph s.mem Ctx R) (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48))
        (blocksAt s.mem S q) ∧
      blockAt st'.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
        Nat.repeat inc32 q (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)) ∧
      blockAt st'.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) =
        ghashFrom (ctxH s.mem Ctx) (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16)) (blocksAt s.mem S q) := by
  have L := h.lay
  have sp := h.sp56
  have hn := h.data.ok.lt
  have hqs : q * 16 ≤ sl := by omega_arith
  have hn8 : 8 * [Reg.rax, .r10, .r11].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega_arith
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.rax, .r10, .r11] (by decide) hn8
  have hP : (pushed [.rax, .r10, .r11] st).gpr .rsp = SP - BitVec.ofNat 64 24 := by rw [pushed_rsp, hsp]; rfl
  have hpf' : Frame [⟨SP - BitVec.ofNat 64 24, 24⟩] st.mem (pushed [.rax, .r10, .r11] st).mem := by
    rw [hsp] at hpf; exact hpf
  have hE : Frame [⟨SP - BitVec.ofNat 64 32, 8⟩] (pushed [.rax, .r10, .r11] st).mem
      (pushed [.rax, .r10, .r11] st).callEntry.mem := by
    have := callEntry_frame (pushed [.rax, .r10, .r11] st)
    rw [hP] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  have b56 : ∀ {a k : Nat}, a ≤ 56 → k ≤ a → ∃ r ∈ [below SP 56], Region.Sub ⟨SP - BitVec.ofNat 64 a, k⟩ r :=
    fun ha hk => ⟨_, List.mem_singleton_self _, stk56_sub ha hk⟩
  have fS : Frame [below SP 56] st.mem (pushed [.rax, .r10, .r11] st).callEntry.mem :=
    (hpf'.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact b56 (by decide) (by decide)).trans
      (hE.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact b56 (by decide) (by decide))
  have kM := h.kM
  obtain ⟨hpre, cr, cw, gU, -, a0, -, -⟩ := callIn h hq hsp hrd hwr hm h_di h_si h_dx h_cx h_8 h_9 h_10 h_11 h_ax
  -- What the push and the return address leave as it was.
  have keep : ∀ {p : Addr} {k : Nat}, (⟨p, k⟩ : Region).Disjoint (below SP 56) → k ≤ 2 ^ 64 →
      bytesAt (pushed [.rax, .r10, .r11] st).callEntry.mem p k = bytesAt s.mem p k := fun hd hk => by
    rw [← hm]
    exact bytesAt_frame fS (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) hk
  have keepB : ∀ {p : Addr}, (⟨p, 16⟩ : Region).Disjoint (below SP 56) →
      blockAt (pushed [.rax, .r10, .r11] st).callEntry.mem p = blockAt s.mem p := fun hd => by
    rw [blockAt, blockAt, keep hd (by decide)]
  have cW : Region.Sub (cbR W) ⟨W, 2560⟩ := fun a hc => st_w a (cb_sub a hc)
  have yW : Region.Sub (yR W) ⟨W, 2560⟩ := fun a hc => st_w a (y_sub a hc)
  have eC := keepB ((h.kw.sub_right cW).symm)
  have eY := keepB ((h.kw.sub_right yW).symm)
  have eS : blocksAt (pushed [.rax, .r10, .r11] st).callEntry.mem S q = blocksAt s.mem S q := by
    rw [Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq,
      keep ((h.ks.sub_right (Region.sub_prefix (by omega_arith))).symm) (by have := h.sWrap; omega_arith)]
  have hRb : 16 * (R + 1) ≤ 256 := by rcases h.rounds.2 with h | h | h <;> subst h <;> decide
  have eK : ctxCiph (pushed [.rax, .r10, .r11] st).callEntry.mem Ctx R = ctxCiph s.mem Ctx R := by
    simp only [ctxCiph]
    rw [keep ((kM.sub_right (Region.sub_prefix (Nat.le_trans hRb M.ge))).symm) (Nat.le_trans hRb (by decide))]
  have eH : ctxH (pushed [.rax, .r10, .r11] st).callEntry.mem Ctx = ctxH s.mem Ctx := by
    simp only [ctxH]
    exact keepB ((kM.sub_right (Offset.sub_base _ (by have := M.ge; omega_arith))).symm)
  have hqn : (BitVec.ofNat 64 q).toNat = q := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.sl_le; omega_arith)
  have hRn : (BitVec.ofNat 64 R).toNat = R := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by rcases h.rounds.2 with h | h | h <;> subst h <;> decide)
  refine WP.frame (by simp) (by decide) (by decide) hn8 (WP.call_sp_mx (k := Proof.AesGcm.decryptBlocksToX86_64M M)
    T.ok T.sp (by have := T.xd; omega_arith) hpre cr cw fun s' hrd' hwr' hcs hfr _ ⟨s₂, hm₂, _, hpost⟩ _ => ?_)
  have r₃ := hcs _ (by decide : Reg.rsp ∈ calleeSaved)
  simp only [Proof.AesGcm.decryptBlocksToX86_64M, Proof.AesGcm.blocksToDecPost, Proof.AesGcm.arg, a0,
    State.withRegions_mem, gU _ (by decide : Reg.rdi ≠ .rsp), gU _ (by decide : Reg.rsi ≠ .rsp),
    gU _ (by decide : Reg.rdx ≠ .rsp), gU _ (by decide : Reg.rcx ≠ .rsp), gU _ (by decide : Reg.r8 ≠ .rsp),
    gU _ (by decide : Reg.r9 ≠ .rsp), h_di, h_si, h_dx, h_cx, h_8, h_9, h_11, hqn, hRn, hm₂, eK, eH,
    eC, eY, eS] at hpost
  obtain ⟨o₁, o₂, o₃⟩ := hpost
  refine ⟨r₃, hwr', fun r hr => ?_, by rw [popped_rd, hrd', pushed_rd], by rw [popped_wr, hwr', pushed_wr]; rfl,
    ?_, ?_, ?_, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'; rw [popped_rsp, r₃, hP, hsp]
      show SP - BitVec.ofNat 64 24 + BitVec.ofNat 64 24 = SP
      exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ hr' (fun e => by subst e; simp [calleeSaved] at hr), hcs r hr, pushed_gpr _ _ hr']
  · rw [popped_mem]
    have bT : Region.Sub (below ((pushed [.rax, .r10, .r11] st).gpr .rsp) (T.fn.code.x86_64Depth + 8)) (below SP 56) := by
      have h₁ := below_sub (sp := (pushed [.rax, .r10, .r11] st).gpr .rsp) (a := T.fn.code.x86_64Depth + 8) (b := 32)
        (by have := T.xd; omega_arith) (by decide)
      have e : below (SP - BitVec.ofNat 64 24) 32 = ⟨SP - BitVec.ofNat 64 56, 32⟩ := by
        simp only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add]
      rw [hP] at h₁ ⊢
      rw [e] at h₁
      exact fun a h' => stk56_sub (by decide) (by decide) a (h₁ a h')
    refine (hpf'.sub fun r hr => ?_).trans (hfr.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨below SP 56, by simp, stk56_sub (by decide) (by decide)⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨below SP 56, by simp, bT⟩
  · rw [popped_mem]; exact o₁
  · rw [popped_mem]; exact o₂
  · rw [popped_mem]; exact o₃

/-- `rest`, after the bytes left are copied (or none): what `prefix` leaves. -/
theorem restD_ok {s₄ : State} (he₄ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₄) (rd₄ : s₄.rd = s.rd)
    (wr₄ : s₄.wr = s.wr)
    (fr₄ : Frame (callWr W D (sl / 16) ++ [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩, below SP 56])
      s.mem s₄.mem)
    (bl₄ : blocksAt s₄.mem D (sl / 16) =
      ctr32 (ctxCiph s.mem Ctx R) (blockAt s.mem (cbA W)) (blocksAt s.mem S (sl / 16)))
    (ct₄ : blockAt s₄.mem (cbA W) = Nat.repeat inc32 (sl / 16) (blockAt s.mem (cbA W)))
    (y₄ : blockAt s₄.mem (yA W) = ghashFrom (ctxH s.mem Ctx) (blockAt s.mem (yA W)) (blocksAt s.mem S (sl / 16)))
    (tl₄ : bytesAt s₄.mem (D + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16) =
      bytesAt s.mem (S + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16)) :
    WP isa (.block SealSplit.rest) s₄ (PPostD Ctx W SP D S R n sl s) := by
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
  have dB : (⟨D, 16 * (sl / 16)⟩ : Region).Disjoint ⟨W, 2560⟩ := h.data.ok.w.sub_left (Region.sub_prefix (by omega_arith))
  have dT : (⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩ : Region).Disjoint ⟨W, 2560⟩ :=
    h.data.ok.w.sub_left (Offset.sub_base D (by omega_arith))
  have cW : ∀ {p : Addr}, (⟨p, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 200, 24⟩ →
      ∀ r ∈ [(⟨W + BitVec.ofNat 64 200, 24⟩ : Region)], (⟨p, 16⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  have eB : blocksAt s₅.mem D (sl / 16) = blocksAt s₄.mem D (sl / 16) :=
    blocksAt_frame f₅ (W200 dB) (by omega_arith)
  have eC : blockAt s₅.mem (cbA W) = blockAt s₄.mem (cbA W) :=
    blockAt_frame f₅ (cW (by simp only [cbA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide)))
  have eY : blockAt s₅.mem (yA W) = blockAt s₄.mem (yA W) :=
    blockAt_frame f₅ (cW (by simp only [yA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide)))
  refine ⟨he₄.keep g₅ rd₅ wr₅, rd₅.trans rd₄, wr₅.trans wr₄, ?_, by rw [eB, bl₄], by rw [eC, ct₄],
    by rw [eY, y₄], by rw [bytesAt_frame f₅ (W200 dT) (by omega_arith), tl₄], d₅, l₅, a₅⟩
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
theorem tailD_ok {s₂ : State} (H : Mid2D Ctx W SP D S R sl s s₂) :
    WP isa (.seq (.block SealSplit.copyArgs) (.seq (.ite .e (.block []) copyLoop) (.block SealSplit.rest))) s₂
      (PPostD Ctx W SP D S R n sl s) := by
  have L := h.lay
  have hn := h.data.ok.lt
  have hsl := h.sl_le
  have kp : ∀ d, 128 ≤ d → d + 8 ≤ 448 → s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => H.frame.readW (Region.contains_self _ _) (slot_disj h (q := sl / 16) (by omega_arith) h₁ h₂) (by decide)
  refine WP.seq (WP.mono (pre3_ok (D := D) (S := S) (sl := sl) (by omega_arith) H.env (by rw [kp 200 (by decide) (by decide)]; exact h.dat)
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
    bytesAt_frame H.frame (src_disj h (q := sl / 16) (by omega_arith) (Offset.sub_base S (by omega_arith))) (by omega_arith)
  refine WP.seq (WP.ite (decide (sl % 16 = 0)) (by simp only [eval, zf₃]) (fun h0 => ?_) (fun h0 => ?_))
  · have h0' : sl % 16 = 0 := of_decide_eq_true h0
    refine WP.block_nil (restD_ok h he₃ (rd₃.trans H.rd) (wr₃.trans H.wr) (by rw [m₃]; exact fr₂)
      (by rw [m₃]; exact H.blocks) (by rw [m₃]; exact H.ctr) (by rw [m₃]; exact H.y) ?_)
    rw [h0']; rfl
  · have h0' : sl % 16 ≠ 0 := of_decide_eq_false h0
    have e1 : 16 * (sl / 16) + sl % 16 ≤ sl := by omega_arith
    have e2 : 16 * (sl / 16) + sl % 16 ≤ n := by omega_arith
    have sl64 : sl < 2 ^ 64 := by omega_arith
    have c1 : Covers [⟨S + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩] (s₃.rd ++ s₃.wr) := by
      rw [rd₃, wr₃, H.rd, H.wr]; exact covers_off' h.srcCov e1 sl64
    have c2 : Covers [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩] s₃.wr := by
      rw [wr₃, H.wr]; exact covers_off' h.data.wr e2 hn
    have hlp : LoopPre s₃ (S + BitVec.ofNat 64 (16 * (sl / 16))) (D + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16) :=
      ⟨si₃, di₃, cx₃, by omega_arith, by omega_arith, c1, c2,
        (h.sD.sub_left (Offset.sub_base S (by omega_arith))).sub_right (Offset.sub_base D (by omega_arith))⟩
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
        (k := sl % 16) (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    have eB : blocksAt s₄.mem D (sl / 16) = blocksAt s₃.mem D (sl / 16) :=
      blocksAt_frame fC (one dBT) (by omega_arith)
    have tW : (⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩ : Region).Disjoint ⟨W, 2560⟩ :=
      dDT.sub_left (Offset.sub_base D (by omega_arith))
    have eC : blockAt s₄.mem (cbA W) = blockAt s₃.mem (cbA W) :=
      blockAt_frame fC (one ((tW.sub_right (fun a hc => st_w a (cb_sub a hc))).symm))
    have eY : blockAt s₄.mem (yA W) = blockAt s₃.mem (yA W) :=
      blockAt_frame fC (one ((tW.sub_right (fun a hc => st_w a (y_sub a hc))).symm))
    have fC' : Frame (callWr W D (sl / 16) ++ [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩, below SP 56])
        s₂.mem s₄.mem := by
      rw [← m₃]
      exact fC.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    refine restD_ok h he₄ (rd₄.trans (rd₃.trans H.rd)) (wr₄.trans (wr₃.trans H.wr)) (fr₂.trans fC')
      (by rw [eB, m₃]; exact H.blocks) (by rw [eC, m₃]; exact H.ctr) (by rw [eY, m₃]; exact H.y) ?_
    rw [m₄]
    have := bytesAt_writeBytes_self s₃.mem (D + BitVec.ofNat 64 (16 * (sl / 16)))
      (bytesAt s₃.mem (S + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16)) (by rw [length_bytesAt]; omega_arith)
    rw [length_bytesAt] at this
    rw [this, m₃, hs₂]

/-- The call of `prefix` for the `sl / 16` whole blocks at `src`, from a
state `s₁` with their number in `rax` and `s`'s memory: what `Mid2D` says. -/
theorem callD_ok (T : BlkToDecFn M) {s₁ : State} (he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁)
    (ax₁ : s₁.gpr .rax = BitVec.ofNat 64 (sl / 16)) (m₁ : s₁.mem = s.mem) (rd₁ : s₁.rd = s.rd)
    (wr₁ : s₁.wr = s.wr) :
    WP isa (.seq (.block SealSplit.preArgs)
      (.frame (.push [.rax, .r10, .r11]) (.call T.fn.name T.fn.code) (.pop .rax 3))) s₁
      (Mid2D Ctx W SP D S R sl s) := by
  have hn := h.data.ok.lt
  have hsl := h.sl_le
  refine WP.seq (WP.mono (pre2_ok (R := R) (D := D) (S := S) he₁ (by rw [m₁]; exact h.rounds) (by rw [m₁]; exact h.dat)
    (by rw [m₁]; exact h.src)) fun s₂ ⟨di₂, si₂, dx₂, cx₂, r8₂, r9₂, r10₂, r11₂, ax₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  have he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁.keep g₂ rd₂ wr₂
  exact WP.mono (preCallToDec_ok h T (q := sl / 16) (by omega_arith) he₂.rsp (rd₂.trans rd₁) (wr₂.trans wr₁)
    (m₂.trans m₁) di₂ si₂ dx₂ cx₂ r8₂ (by rw [r9₂, ax₁]) (by rw [r10₂, ax₁]) r11₂ ax₂)
    fun s₃ ⟨cs₃, rd₃, wr₃, fr₃, bl₃, ct₃, y₃⟩ => ⟨he₂.keep (fun r hr => cs₃ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved])) rd₃ wr₃,
      rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), by rw [m₂, m₁] at fr₃; exact fr₃, bl₃, ct₃, y₃⟩

/-- `prefix`: the whole blocks at `src` decrypted to `dst` and absorbed by a
call of `vg_aes_gcm_decrypt_blocks_to` (`T`), the bytes left copied, and
`len` and the data from them on kept. -/
theorem prefixD_ok (T : BlkToDecFn M) :
    WP isa (SealSplit.prefix T.fn) s (PPostD Ctx W SP D S R n sl s) := by
  have L := h.lay
  have hn := h.data.ok.lt
  have hsl := h.sl_le
  have he := h.env
  unfold SealSplit.prefix
  refine WP.seq (WP.mono (pre1_ok (sl := sl) (by omega_arith) he h.slen) fun s₁ ⟨ax₁, zf₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) rd₁ wr₁
  refine WP.seq (WP.ite (decide (sl / 16 = 0)) (by simp only [eval, zf₁]) (fun h0 => ?_) (fun h0 => ?_))
  · -- No whole block at `src`.
    have h0' : sl / 16 = 0 := of_decide_eq_true h0
    refine WP.block_nil (tailD_ok h ⟨he₁, rd₁, wr₁, by rw [m₁]; exact Frame.refl _ _, ?_, ?_, ?_⟩)
    · rw [h0']; rfl
    · rw [h0', m₁]; rfl
    · rw [h0', m₁]; rfl
  · exact WP.mono (callD_ok h T he₁ ax₁ m₁ rd₁ wr₁) fun _ H => tailD_ok h H

end

end VG.Proof.AesGcm.X86_64.OpenSplit
