module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixOk
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksToDec.Fn
public import VerifiedGarbage.Impl.AesGcm.X86_64.OpenSplit
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

Untrusted: everything here is checked by Lean. `Impl.AesGcm.X86_64.OpenSplit.prefix`, `seal_split`'s
`prefix` with a call of `vg_aes_gcm_decrypt_blocks_to` in place of
`vg_aes_gcm_encrypt_blocks_to` and no copy (`prefixD_ok`): from the same
state as `Split.prefix_ok` (`Split.PP`), with `Y` continued over the
ciphertext at `src`, which the call absorbs (`preCallToDec_ok`), rather than
over what it writes (`Mid2D`), and the bytes left at `src` kept as the data
(`restS_ok`, `PPostD`).
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
structure PPostD (Ctx W SP D S : Addr) (R sl : Nat) (s s' : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame (callWr W D (sl / 16) ++ [⟨W + BitVec.ofNat 64 200, 16⟩, below SP 56]) s.mem s'.mem
  blocks : blocksAt s'.mem D (sl / 16) = ctr32 (ctxCiph s.mem Ctx R) (blockAt s.mem (cbA W)) (blocksAt s.mem S (sl / 16))
  ctr : blockAt s'.mem (cbA W) = Nat.repeat inc32 (sl / 16) (blockAt s.mem (cbA W))
  y : blockAt s'.mem (yA W) = ghashFrom (ctxH s.mem Ctx) (blockAt s.mem (yA W)) (blocksAt s.mem S (sl / 16))
  dat : s'.mem.readW (W + BitVec.ofNat 64 200) 64 = S + BitVec.ofNat 64 (16 * (sl / 16))
  len : s'.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (sl % 16)

/-- `Impl.AesGcm.X86_64.OpenSplit.rest`: the bytes after the `16 ⌊sl / 16⌋` at `S` kept as the
data, and their number as its length. -/
theorem restS_ok {Ctx W SP S : Addr} {sl : Nat} (hsl : sl < 2 ^ 64) {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hsrc : s.mem.readW (W + BitVec.ofNat 64 224) 64 = S)
    (hslot : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 sl) :
    WP isa (.block Impl.AesGcm.X86_64.OpenSplit.rest) s fun s₄ =>
      s₄.mem.readW (W + BitVec.ofNat 64 200) 64 = S + BitVec.ofNat 64 (16 * (sl / 16)) ∧
      s₄.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (sl % 16) ∧
      Frame [⟨W + BitVec.ofNat 64 200, 16⟩] s.mem s₄.mem ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s₄.gpr r = s.gpr r) ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr := by
  have q₁ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have q₃ := he.perm.wR (show 224 + 8 ≤ 2560 by decide)
  have w₁ := he.perm.wW (show 200 + 8 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 208 + 8 ≤ 2560 by decide)
  have e15 := and15 (BitVec.ofNat 64 sl)
  rw [toNat_ofNat_of_lt hsl, imm_eq (by decide)] at e15
  have esub : BitVec.ofNat 64 sl - BitVec.ofNat 64 (sl % 16) = BitVec.ofNat 64 (16 * (sl / 16)) := by
    rw [ofNat_sub (Nat.mod_le _ _) hsl]; congr 1; omega_arith
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2560 → d + 8 ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 a) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep W h (by have := he.perm; omega_arith) (by omega_arith)
  have hsrc' : (s.mem.writeW (W + BitVec.ofNat 64 208) (BitVec.ofNat 64 (sl % 16))).readW
      (W + BitVec.ofNat 64 224) 64 = S := by
    rw [Mem.readW_writeW_sep (sep 224 208 (by decide) (by decide) (by decide)) (by decide), hsrc]
  have q₃' : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 224) 8 := q₃
  unfold Impl.AesGcm.X86_64.OpenSplit.rest
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r15, q₁, q₃', w₁, w₂, hslot, e15, esub, hsrc'], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [mem_arithFlags, mem_setReg, Mem.readW_writeW_self64, BitVec.add_comm]
  · simp only [mem_arithFlags, mem_setReg]
    rw [Mem.readW_writeW_sep (sep 208 200 (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]
  · have c : ∀ d, 200 ≤ d → d + 8 ≤ 216 → (⟨W + BitVec.ofNat 64 200, 16⟩ : Region).Contains
        (W + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ => Offset.contains _ h₁ (by omega_arith) (by have := he.perm; omega_arith)
    simp only [mem_arithFlags, mem_setReg]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 208 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 200 (by decide) (by decide))
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
  all_goals simp [rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

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

/-- After the call (or none): `rest`. -/
theorem restD_ok {s₂ : State} (H : Mid2D Ctx W SP D S R sl s s₂) :
    WP isa (.block Impl.AesGcm.X86_64.OpenSplit.rest) s₂ (PPostD Ctx W SP D S R sl s) := by
  have L := h.lay
  have hn := h.data.ok.lt
  have hsl := h.sl_le
  have kp : ∀ d, 128 ≤ d → d + 8 ≤ 448 → s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => H.frame.readW (Region.contains_self _ _) (slot_disj h (q := sl / 16) (by omega_arith) h₁ h₂) (by decide)
  refine WP.mono (restS_ok (S := S) (sl := sl) (by omega_arith) H.env (by rw [kp 224 (by decide) (by decide)]; exact h.src)
    (by rw [kp 192 (by decide) (by decide)]; exact h.slen)) fun s₅ ⟨d₅, l₅, f₅, g₅, rd₅, wr₅⟩ => ?_
  have cW : ∀ {p : Addr}, (⟨p, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 200, 16⟩ →
      ∀ r ∈ [(⟨W + BitVec.ofNat 64 200, 16⟩ : Region)], (⟨p, 16⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  have dB : (⟨D, 16 * (sl / 16)⟩ : Region).Disjoint ⟨W, 2560⟩ := h.data.ok.w.sub_left (Region.sub_prefix (by omega_arith))
  have eB : blocksAt s₅.mem D (sl / 16) = blocksAt s₂.mem D (sl / 16) :=
    blocksAt_frame f₅ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dB.sub_right (Lay.wSub (by decide))) (by omega_arith)
  have eC : blockAt s₅.mem (cbA W) = blockAt s₂.mem (cbA W) :=
    blockAt_frame f₅ (cW (by simp only [cbA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide)))
  have eY : blockAt s₅.mem (yA W) = blockAt s₂.mem (yA W) :=
    blockAt_frame f₅ (cW (by simp only [yA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide)))
  refine ⟨H.env.keep g₅ rd₅ wr₅, rd₅.trans H.rd, wr₅.trans H.wr, ?_, by rw [eB, H.blocks], by rw [eC, H.ctr],
    by rw [eY, H.y], d₅, l₅⟩
  refine (H.frame.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp, fun _ h => h⟩

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
call of `vg_aes_gcm_decrypt_blocks_to` (`T`), and the bytes left at `src`
kept as the data. -/
theorem prefixD_ok (T : BlkToDecFn M) :
    WP isa (Impl.AesGcm.X86_64.OpenSplit.prefix T.fn) s (PPostD Ctx W SP D S R sl s) := by
  have L := h.lay
  have hn := h.data.ok.lt
  have hsl := h.sl_le
  have he := h.env
  unfold Impl.AesGcm.X86_64.OpenSplit.prefix
  refine WP.seq (WP.mono (pre1_ok (sl := sl) (by omega_arith) he h.slen) fun s₁ ⟨ax₁, zf₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) rd₁ wr₁
  refine WP.seq (WP.ite (decide (sl / 16 = 0)) (by simp only [eval, zf₁]) (fun h0 => ?_) (fun h0 => ?_))
  · -- No whole block at `src`.
    have h0' : sl / 16 = 0 := of_decide_eq_true h0
    refine WP.block_nil (restD_ok h ⟨he₁, rd₁, wr₁, by rw [m₁]; exact Frame.refl _ _, ?_, ?_, ?_⟩)
    · rw [h0']; rfl
    · rw [h0', m₁]; rfl
    · rw [h0', m₁]; rfl
  · exact WP.mono (callD_ok h T he₁ ax₁ m₁ rd₁ wr₁) fun _ H => restD_ok h H

end

end VG.Proof.AesGcm.X86_64.OpenSplit
