module

public import VerifiedGarbage.Proof.AesCcm.Scratch
public import VerifiedGarbage.Proof.AesCcm.Arm.CTFn
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.AesCcm.Arm.Args
import VerifiedGarbage.Proof.AesCcm.Arm.Mask
import VerifiedGarbage.Proof.AesCcm.Bytes
import VerifiedGarbage.Proof.AesCcm.Arm.Seal
import VerifiedGarbage.Proof.AesCcm.Arm.Mac
import VerifiedGarbage.Proof.AesCcm.Arm.Ctrs
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Spec.Ccm.Contract
public import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Proof.Framework.Arm.StackScratch
import VerifiedGarbage.Proof.Framework.Arm.ScratchLost

/-! ### `AesCcm.Arm.Verified`, which only this module used -/

section

/-! ### `AesCcm.Arm.Open`, which only this module used -/

section

/-!
# AES-CCM on ARMv7: `vg_aes_ccm_open`

Untrusted: everything here is checked by Lean. `open` is the entry, `Ctr₀`,
counter mode over the data (which decrypts it), the encrypted MAC of the
plaintext at `W + 112`, then the comparison of its first `t` bytes with the
received tag at `tag` (`recv`, `cmp`), the mask of the data and `restore`
(`open_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (zeros)
open VG.Impl.AesGcm.Arm (imm recv cmp uO restore)
open VG.Proof.AesGcm.Arm (savedR SavedAt restore_ok covers_left bytesAt_frame Keeps)
open VG.Proof.AesCcm (ctxCiph_frame length_bytesAt xorFrom length_xorFrom crypt_eq take_xorFrom_zero mac_eq
  BlockCipher bytesAt_prefix bytesAt_writeBytes_base cryptTag_eq_iff)

/-- Whether the received tag `tag` is that of the decrypted `ct`. -/
abbrev tagOk (ciph : Spec.Ccm.Cipher) (tl : Nat) (nonce ct aad tag : List Byte) : Bool :=
  decide (Spec.Ccm.cryptTag ciph tl nonce tag = Spec.Ccm.mac ciph tl nonce aad (Spec.Ccm.crypt ciph nonce ct))

/-- `vg_aes_ccm_open`, for its arguments. -/
theorem open_wp' {s₀ : State} {k w N A D T : BitVec 32} {R nl al n tl : Nat} (Ar : Args s₀ k w N A D R nl al n tl)
    (Tb : TagB w s₀.sp D n T tl) (hTr : Covers [⟨State.addr T, tl⟩] (s₀.rd ++ s₀.wr)) (h0 : s₀.gpr .r0 = k) (h1 : s₀.gpr .r1 = BitVec.ofNat 32 R) (h2 : s₀.gpr .r2 = N)
    (h3 : s₀.gpr .r3 = BitVec.ofNat 32 nl) (eA : stackArg s₀ 0 = A) (eal : stackArg s₀ 1 = BitVec.ofNat 32 al)
    (eD : stackArg s₀ 2 = D) (en : stackArg s₀ 3 = BitVec.ofNat 32 n) (eT : stackArg s₀ 4 = T)
    (etl : stackArg s₀ 5 = BitVec.ofNat 32 tl) (eW : stackArg s₀ 6 = w) :
    WP isa «open» s₀ fun s' => abiPreserved s₀ s' ∧
      s'.gpr .r0 = (if tagOk (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R) tl (bytesAt s₀.mem (State.addr N) nl)
        (bytesAt s₀.mem (State.addr D) n) (bytesAt s₀.mem (State.addr A) al) (bytesAt s₀.mem (State.addr T) tl)
        then 1 else 0) ∧
      bytesAt s'.mem (State.addr D) n =
        (if tagOk (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R) tl (bytesAt s₀.mem (State.addr N) nl)
          (bytesAt s₀.mem (State.addr D) n) (bytesAt s₀.mem (State.addr A) al) (bytesAt s₀.mem (State.addr T) tl)
          then Spec.Ccm.crypt (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R) (bytesAt s₀.mem (State.addr N) nl)
            (bytesAt s₀.mem (State.addr D) n)
          else zeros n) := by
  have L := Ar.lay
  obtain hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
  obtain hsavedK : (⟨State.addr k, 240⟩ : Region).Disjoint (savedR w) := L.k_w' (by decide)
  have t16 := Ar.t16
  have t4 := Ar.t4
  refine WP.seq (WP.mono (entry_wp Ar h0 h1 eW) fun s₁ ⟨he₁, g₁, rd₁, wr₁, sv₁, f₁⟩ => ?_)
  obtain hent : ∀ {P : BitVec 32} {len : Nat}, Buf w s₀.sp s₀ P len →
      bytesAt s₁.mem (State.addr P) len = bytesAt s₀.mem (State.addr P) len := fun hP =>
    bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega_arith)
  obtain hK₁ : Spec.Ccm.ctxCiph s₁.mem (State.addr k) R = Spec.Ccm.ctxCiph s₀.mem (State.addr k) R :=
    ctxCiph_frame f₁ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsavedK) hRb
  obtain hk₁ : Stk w s₀ s₁ := Ar.stk.frame f₁ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Ar.stk.aw.sub_right (Lay.wSub (by decide)))
    he₁.sp rd₁ wr₁
  -- `Ctr₀`.
  obtain hN₁ := Ar.nonce.of_eq rd₁ wr₁
  refine WP.seq (WP.mono (ctrs_ok L he₁ hN₁ (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), h2])
    (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), h3]) Ar.h7 Ar.h13)
    fun s₂ ⟨c₂, h10₂, f₂, g₂, rd₂, wr₂, sp₂⟩ => ?_)
  rw [hent Ar.nonce] at c₂
  obtain he₂ : Env k w s₀.sp R (14 - nl) s₂ :=
    ⟨by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he₁.r8],
      by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he₁.r9], h10₂,
      by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he₁.r11],
      by rw [sp₂, he₁.sp], he₁.perm.of_eq rd₂ wr₂⟩
  obtain f₂' : Frame (wR w s₀.sp) s₁.mem s₂.mem := f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact w_wR (.inl (by decide))
  obtain F₂ : Frame (mutR w s₀.sp D n) s₁.mem s₂.mem := f₂'.sub wR_mut
  obtain hk₂ := hk₁.frame F₂ (args_mut Ar) sp₂ rd₂ wr₂
  obtain rd₁₂ : s₂.rd = s₀.rd := rd₂.trans rd₁
  obtain wr₁₂ : s₂.wr = s₀.wr := wr₂.trans wr₁
  obtain hnl := length_bytesAt s₀.mem (State.addr N) nl
  obtain h7 : 7 ≤ (bytesAt s₀.mem (State.addr N) nl).length := by rw [hnl]; exact Ar.h7
  obtain h13 : (bytesAt s₀.mem (State.addr N) nl).length ≤ 13 := by rw [hnl]; exact Ar.h13
  -- Counter mode: the plaintext.
  refine WP.seq (WP.mono (ctr_ok L he₂ hk₂ Ar.rounds h7 h13 c₂ eD en (Ar.data.of_eq rd₁₂ wr₁₂)
    (by rw [hnl]; exact Ar.hn) Ar.n32) fun s₃ ⟨he₃, rd₃, wr₃, _, f₃, o₃⟩ => ?_)
  obtain F₃ : Frame (mutR w s₀.sp D n) s₁.mem s₃.mem := F₂.trans (f₃.sub ctrR_mut)
  obtain rd₁₃ : s₃.rd = s₀.rd := rd₃.trans rd₁₂
  obtain wr₁₃ : s₃.wr = s₀.wr := wr₃.trans wr₁₂
  obtain hk₃ := hk₁.frame F₃ (args_mut Ar) (by rw [he₃.sp, he₁.sp]) (by rw [rd₁₃, rd₁]) (by rw [wr₁₃, wr₁])
  obtain c₃ : bytesAt s₃.mem (State.addr w + BitVec.ofNat 64 48) 16 =
      Spec.Ccm.ctrBlock (bytesAt s₀.mem (State.addr N) nl) 0 := by
    rw [bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm
      · exact (Ar.data.buf.w.sub_right (Lay.wSub (by decide))).symm) (by decide), c₂]
  obtain a₃ : bytesAt s₃.mem (State.addr A) al = bytesAt s₀.mem (State.addr A) al := by
    rw [bytesAt_frame F₃ (aad_mut Ar) (by have := Ar.aad.lt; omega_arith), hent Ar.aad]
  -- The MAC of the plaintext, encrypted, at `W + 112`.
  refine WP.seq (WP.mono (mac_ok L he₃ hk₃ rfl Ar.rounds eA eal eD en etl hnl Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te
    Ar.al32 Ar.n32 Ar.hn c₃ (y := uO) (.inr rfl) (Ar.aad.of_eq rd₁₃ wr₁₃) (Ar.data.buf.of_eq rd₁₃ wr₁₃))
    fun s₄ M => ?_)
  obtain c₄ : bytesAt s₄.mem (State.addr w + BitVec.ofNat 64 48) 16 =
      Spec.Ccm.ctrBlock (bytesAt s₀.mem (State.addr N) nl) 0 := by
    rw [bytesAt_frame M.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) (by decide), c₃]
  refine WP.seq (WP.mono (tag_ok L M.env Ar.rounds h7 h13 c₄ (y := uO) (.inr rfl))
    fun s₅ ⟨he₅, rd₅, wr₅, g₅, f₅, o₅⟩ => ?_)
  obtain f₅' : Frame (wR w s₀.sp) s₄.mem s₅.mem := f₅.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact w_wR (.inl (by decide))
    · exact w_wR (.inl (by decide))
    · exact w_wR (.inr ⟨by decide, by decide⟩)
    · exact ⟨_, by simp, fun _ h => h⟩
  obtain G₅ : Frame (wR w s₀.sp) s₃.mem s₅.mem := (M.frame.sub (macR_wR (.inr rfl))).trans f₅'
  obtain F₅ : Frame (mutR w s₀.sp D n) s₁.mem s₅.mem := F₃.trans (G₅.sub wR_mut)
  obtain rd₁₅ : s₅.rd = s₀.rd := by rw [rd₅, M.rd, rd₁₃]
  obtain wr₁₅ : s₅.wr = s₀.wr := by rw [wr₅, M.wr, wr₁₃]
  obtain hk₅ := hk₁.frame F₅ (args_mut Ar) (by rw [he₅.sp, he₁.sp]) (by rw [rd₁₅, rd₁]) (by rw [wr₁₅, wr₁])
  obtain hT₅ : bytesAt s₅.mem (State.addr T) tl = bytesAt s₀.mem (State.addr T) tl := by
    rw [bytesAt_frame F₅ (tag_mut Tb) (by omega_arith), bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Tb.w.sub_right (Lay.wSub (by decide))) (by omega_arith)]
  -- `t`, and the received tag padded at `W + 256`.
  obtain ⟨i5, v5⟩ := hk₅.at 5 (by decide) (show 4 * 5 = 20 from rfl)
  obtain ⟨s₆, run₆, h6₆, g₆, k₆⟩ : ∃ s₆, runBlock isa [.ldrSp .r6 20] s₅ = some s₆ ∧
      s₆.gpr .r6 = BitVec.ofNat 32 tl ∧ (∀ r, r ≠ .r6 → s₆.gpr r = s₅.gpr r) ∧ Keeps s₅ s₆ := by
    refine ⟨_, by arun [i5, v5], ?_, ?_, ?_⟩
    · simp [gpr_setReg, v5, etl]
    · intro r a; simp [gpr_setReg, a]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  obtain he₆ := he₅.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₆ _ (by decide)) k₆.sp k₆.rd k₆.wr
  obtain ⟨i4, v4⟩ := (hk₅.of_eq k₆.mem k₆.sp k₆.rd k₆.wr).at 4 (by decide) (show 4 * 4 = 16 from rfl)
  rw [eT] at v4
  refine WP.seq (WP.mono (recv_ok L he₆ i4 v4
      (by rw [k₆.rd, k₆.wr, rd₁₅, wr₁₅]; exact hTr) Tb.wrap (Tb.w.sub_right (Lay.wSub (by decide))) h6₆
      (by omega_arith) t16) fun s₇ ⟨hR₇, fr₇, g₇, rd₇, wr₇, sp₇⟩ => ?_)
  obtain he₇ := he₆.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide))
    sp₇ rd₇ wr₇
  obtain h6₇ : s₇.gpr .r6 = BitVec.ofNat 32 tl := by
    rw [g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide), h6₆]
  -- The comparison.
  refine WP.seq (WP.mono (cmp_ok L he₇ (o := uO) (.inr rfl) h6₇ (by omega_arith) t16)
    fun s₈ ⟨h0₈, fr₈, g₈, rd₈, wr₈, sp₈⟩ => ?_)
  obtain ⟨s₉, run₉, h7₉, g₉, k₉⟩ : ∃ s₉, runBlock isa [.mov .r7 (.reg .r0)] s₈ = some s₉ ∧
      s₉.gpr .r7 = s₈.gpr .r0 ∧ (∀ r, r ≠ .r7 → s₉.gpr r = s₈.gpr r) ∧ Keeps s₈ s₉ := by
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · intro r a; simp [gpr_setReg, a]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₉, run₉, ?_⟩)
  obtain he₉ := he₇.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [g₉ _ (by decide), g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)])
    (k₉.sp.trans sp₈) (k₉.rd.trans rd₈) (k₉.wr.trans wr₈)
  obtain f₅₉ : Frame (wR w s₀.sp) s₅.mem s₉.mem := by
    rw [k₉.mem, ← k₆.mem] at *
    refine (fr₇.sub fun r hr => ?_).trans (fr₈.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact w_wR (.inr ⟨by decide, by decide⟩)
    · simp only [List.mem_singleton] at hr; subst hr; exact w_wR (.inr ⟨by decide, by decide⟩)
  obtain F₉ : Frame (mutR w s₀.sp D n) s₁.mem s₉.mem := F₅.trans (f₅₉.sub wR_mut)
  obtain rd₁₉ : s₉.rd = s₀.rd := by rw [k₉.rd, rd₈, rd₇, k₆.rd, rd₁₅]
  obtain wr₁₉ : s₉.wr = s₀.wr := by rw [k₉.wr, wr₈, wr₇, k₆.wr, wr₁₅]
  obtain hk₉ := hk₁.frame F₉ (args_mut Ar) (by rw [he₉.sp, he₁.sp]) (by rw [rd₁₉, rd₁]) (by rw [wr₁₉, wr₁])
  -- What the comparison compares.
  obtain hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m (State.addr k) R) := fun _ x =>
    Proof.Cmac.aesWith_length _ _ x
  obtain cK : ∀ {m : Mem}, Frame (mutR w s₀.sp D n) s₁.mem m →
      Spec.Ccm.ctxCiph m (State.addr k) R = Spec.Ccm.ctxCiph s₀.mem (State.addr k) R := fun hf => by
    rw [ctxCiph_frame hf (k_mut Ar) hRb, hK₁]
  obtain d₂ : bytesAt s₂.mem (State.addr D) n = bytesAt s₀.mem (State.addr D) n := by
    rw [buf_wR Ar.data.buf f₂', hent Ar.data.buf]
  obtain p₃ : bytesAt s₃.mem (State.addr D) n = Spec.Ccm.crypt (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R)
      (bytesAt s₀.mem (State.addr N) nl) (bytesAt s₀.mem (State.addr D) n) := by
    rw [o₃, cK F₂, d₂, crypt_eq (hBC _)]
  obtain p₉ : bytesAt s₉.mem (State.addr D) n = bytesAt s₃.mem (State.addr D) n := by
    rw [buf_wR Ar.data.buf f₅₉, buf_wR Ar.data.buf G₅]
  obtain hl : (bytesAt s₀.mem (State.addr N) nl).length ≤ 15 := by rw [hnl]; have := Ar.h13; omega_arith
  have mo := M.out
  rw [cK F₃, a₃, p₃] at mo
  rw [cK (F₃.trans (M.frame.sub (macR_mut (.inr rfl)))), mo] at o₅
  obtain hY := congrArg List.length o₅
  rw [length_bytesAt, length_xorFrom] at hY
  obtain hV : bytesAt s₇.mem (State.addr w + BitVec.ofNat 64 uO) tl =
      Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R) tl (bytesAt s₀.mem (State.addr N) nl)
        (Spec.Ccm.mac (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R) tl (bytesAt s₀.mem (State.addr N) nl)
          (bytesAt s₀.mem (State.addr A) al) (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R)
            (bytesAt s₀.mem (State.addr N) nl) (bytesAt s₀.mem (State.addr D) n))) := by
    rw [bytesAt_prefix _ _ t16, bytesAt_frame fr₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide), k₆.mem, o₅, take_xorFrom_zero (hBC _) _ hY.symm t16, ← mac_eq _ _ hl]
  obtain hRv : bytesAt s₇.mem (State.addr w + BitVec.ofNat 64 256) 16 =
      bytesAt s₀.mem (State.addr T) tl ++ Spec.Gcm.zeros (16 - tl) := by
    rw [hR₇, k₆.mem, hT₅]
  obtain hML : (Spec.Ccm.mac (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R) tl (bytesAt s₀.mem (State.addr N) nl)
      (bytesAt s₀.mem (State.addr A) al) (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R)
        (bytesAt s₀.mem (State.addr N) nl) (bytesAt s₀.mem (State.addr D) n))).length = tl := by
    rw [mac_eq _ _ hl, List.length_take, ← mo, length_bytesAt]; omega_arith
  obtain key : decide (bytesAt s₇.mem (State.addr w + BitVec.ofNat 64 uO) tl ++ Spec.Gcm.zeros (16 - tl) =
      bytesAt s₇.mem (State.addr w + BitVec.ofNat 64 256) 16) =
      tagOk (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R) tl (bytesAt s₀.mem (State.addr N) nl)
        (bytesAt s₀.mem (State.addr D) n) (bytesAt s₀.mem (State.addr A) al) (bytesAt s₀.mem (State.addr T) tl) := by
    rw [hV, hRv, tagOk, decide_eq_decide, List.append_left_inj,
      cryptTag_eq_iff (hBC _) t16 _ (length_bytesAt _ _ _) hML, eq_comm]
  obtain h7' : s₉.gpr .r7 = if decide (bytesAt s₇.mem (State.addr w + BitVec.ofNat 64 uO) tl ++
      Spec.Gcm.zeros (16 - tl) = bytesAt s₇.mem (State.addr w + BitVec.ofNat 64 256) 16) then 1 else 0 := by
    rw [h7₉, h0₈]; simp only [decide_eq_true_eq]
  -- The mask.
  refine WP.seq (WP.mono (mask_ok he₉ hk₉ eD en (Ar.data.of_eq rd₁₉ wr₁₉) Ar.n32 h7')
    fun s₁₀ ⟨he₁₀, rd₁₀, wr₁₀, g₁₀, m₁₀⟩ => ?_)
  rw [key] at m₁₀
  obtain F₁₀ : Frame (mutR w s₀.sp D n) s₁.mem s₁₀.mem := F₉.trans (by
    rw [m₁₀]
    exact (writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  -- `ok` in `r0`, and `restore`.
  show WP isa (.block ([.mov .r0 (.reg .r7)] ++ restore)) s₁₀ _
  refine WP.block_append (WP.of_runBlock ⟨s₁₀.setReg .r0 (s₁₀.gpr .r7), by arun [], ?_⟩)
  refine WP.mono (restore_ok (by simp [gpr_setReg, he₁₀.r11]) L.ww
    (by simp only [rd_setReg, wr_setReg]; exact covers_left he₁₀.perm.w)
    (by simp only [mem_setReg]; exact sv₁.frame F₁₀ (saved_mut Ar)) (by simp only [sp_setReg]; exact he₁₀.sp))
    fun s' ⟨ab, hm, h0', _, _⟩ => ⟨ab, ?_, ?_⟩
  · rw [h0', gpr_setReg_self, g₁₀ _ (by decide) (by decide) (by decide) (by decide), h7']
    rw [key]
  · rw [hm, mem_setReg, m₁₀, bytesAt_writeBytes_base _ _ _ (by rw [length_mask]) (by have := Ar.data.buf.lt; omega_arith),
      length_mask, List.drop_eq_nil_of_le (by rw [length_bytesAt]), List.append_nil, p₉, p₃]

theorem openPost {s s' : State} {c : Prop} [Decidable c] {pt : List Byte}
    (hres : openRes s = if c then some pt else none) (h0 : s'.gpr .r0 = if decide c then 1 else 0)
    (hd : bytesAt s'.mem (State.addr (arg s 2)) (arg s 3).toNat =
      if decide c then pt else zeros (arg s 3).toNat) : openArm.post s s' := by
  by_cases hc : c
  · simp only [hc, decide_true, ite_true] at hres h0 hd
    simp only [openArm, hres]; exact ⟨h0, hd⟩
  · simp only [hc, decide_false, Bool.false_eq_true, ite_false] at hres h0 hd
    simp only [openArm, hres]; exact ⟨h0, hd⟩

/-- `vg_aes_ccm_open`. -/
theorem open_wp {s : State} (h : openArm.pre s) :
    WP isa «open» s fun s' => abiPreserved s s' ∧ openArm.post s s' :=
  have A := args_of_open h
  WP.mono (open_wp' A.1.1 A.1.2 A.2 rfl (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl
    (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl)
    fun _ ⟨ab, h0, hd⟩ => ⟨ab, openPost rfl h0 hd⟩

end VG.Proof.AesCcm.Arm

end

end


/-!
# AES-CCM on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, states satisfying the preconditions, and the shared contracts of
`Spec/Ccm/Contract.lean` with the working space as a last argument
(`Proof/AesCcm/Scratch.lean`), with 16 bytes of stack: each call pushes two
words, and `vg_cmac_aes_update` pushes two more for its own call of
`vg_aes_ctr32`. `Frame.lean` allocates the working space.
-/

@[expose] public section

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Impl.AesCcm.Arm

/-- The entry invariant of a run, from the arguments. -/
theorem entI_of {s : State} {T : BitVec 32} {tl : Nat}
    (Ar : Args s (s.gpr .r0) (arg s 6) (s.gpr .r2) (arg s 0) (arg s 2) (s.gpr .r1).toNat (s.gpr .r3).toNat
      (arg s 1).toNat (arg s 3).toNat tl) (hT : arg s 4 = T) (htl : arg s 5 = BitVec.ofNat 32 tl)
    (hwr : ∀ r ∈ s.wr, (args s 7).Disjoint r) :
    EntI (s.gpr .r0) (arg s 6) s.sp (s.gpr .r2) (arg s 0) (arg s 2) T (s.gpr .r1).toNat (s.gpr .r3).toNat
      (arg s 1).toNat (arg s 3).toNat tl s :=
  ⟨⟨Ar, rfl, hwr, rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm, hT, htl, rfl⟩,
    rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm⟩

/-- The entry invariant of `seal`'s runs. -/
theorem entI_seal {s : State} (h : sealArm.pre s) :
    EntI (s.gpr .r0) (arg s 6) s.sp (s.gpr .r2) (arg s 0) (arg s 2) (arg s 4) (s.gpr .r1).toNat (s.gpr .r3).toNat
      (arg s 1).toNat (arg s 3).toNat (arg s 5).toNat s := by
  obtain A := args_of_seal h
  refine entI_of A.1.1 rfl (ofNat_toNat32 _).symm fun r hr => ?_
  rw [h.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact A.1.1.da.symm
  · exact A.2.2.symm
  · exact A.1.1.stk.aw

/-- The entry invariant of `open`'s runs. -/
theorem entI_open {s : State} (h : openArm.pre s) :
    EntI (s.gpr .r0) (arg s 6) s.sp (s.gpr .r2) (arg s 0) (arg s 2) (arg s 4) (s.gpr .r1).toNat (s.gpr .r3).toNat
      (arg s 1).toNat (arg s 3).toNat (arg s 5).toNat s := by
  obtain A := args_of_open h
  refine entI_of A.1.1 rfl (ofNat_toNat32 _).symm fun r hr => ?_
  rw [h.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact A.1.1.da.symm
  · exact A.1.1.stk.aw

/-- The second run, with the first's public arguments. -/
theorem entI_pub {pre : State → Prop}
    (hpre : ∀ {s}, pre s → EntI (s.gpr .r0) (arg s 6) s.sp (s.gpr .r2) (arg s 0) (arg s 2) (arg s 4)
      (s.gpr .r1).toNat (s.gpr .r3).toNat (arg s 1).toNat (arg s 3).toNat (arg s 5).toNat s)
    {s₁ s₂ : State} (h₂ : pre s₂) (hq : onePub s₁ s₂) :
    EntI (s₁.gpr .r0) (arg s₁ 6) s₁.sp (s₁.gpr .r2) (arg s₁ 0) (arg s₁ 2) (arg s₁ 4) (s₁.gpr .r1).toNat
      (s₁.gpr .r3).toNat (arg s₁ 1).toNat (arg s₁ 3).toNat (arg s₁ 5).toNat s₂ := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := hq
  obtain e := hpre h₂
  rwa [← q₀, ← q₁, ← q₂, ← q₃, ← q₄, ← qa 0 (by decide), ← qa 1 (by decide), ← qa 2 (by decide),
    ← qa 3 (by decide), ← qa 4 (by decide), ← qa 5 (by decide), ← qa 6 (by decide)] at e

theorem one_ct {pre : State → Prop}
    (hpre : ∀ {s}, pre s → EntI (s.gpr .r0) (arg s 6) s.sp (s.gpr .r2) (arg s 0) (arg s 2) (arg s 4)
      (s.gpr .r1).toNat (s.gpr .r3).toNat (arg s 1).toNat (arg s 3).toNat (arg s 5).toNat s)
    {c : Prog isa}
    (hc : ∀ {k w sp N A D T : BitVec 32} {R nl al n tl : Nat}, Lay k w sp → (R = 10 ∨ R = 12 ∨ R = 14) →
      al < 2 ^ 32 → 7 ≤ nl → nl ≤ 13 → n < 256 ^ (15 - nl) → n < 2 ^ 32 →
      Proof.AesGcm.Arm.CT (EntI k w sp N A D T R nl al n tl) c)
    {pub : State → State → Prop} (hp : ∀ s₁ s₂, pub s₁ s₂ → onePub s₁ s₂) :
    ConstantTime isa pre pub c := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain Ar := (hpre h₁).1.ar
  exact (hc Ar.lay Ar.rounds Ar.al32 Ar.h7 Ar.h13 Ar.hn Ar.n32 _ _ _ _ _ _ ⟨hpre h₁, entI_pub hpre h₂ (hp _ _ hq)⟩
    e₁ e₂).1

theorem seal_ct : ConstantTime isa sealArm.pre sealArm.pub «seal» :=
  one_ct entI_seal (fun L hR hal h7 h13 hn hn4 => seal_ctI L hR hal h7 h13 hn hn4) fun _ _ h => h

theorem open_ct : ConstantTime isa openArm.pre openArm.pub «open» :=
  one_ct entI_open (fun L hR hal h7 h13 hn hn4 => open_ctI L hR hal h7 h13 hn hn4) fun _ _ h => h.1

/-- A state satisfying the precondition of `vg_aes_ccm_seal`: a 7-byte nonce,
no associated data, no data, a 4-byte tag at `0x3000` and `work` at 0. -/
def sealSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | .r3 => 7 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8014 then 4 else if a = 0x8011 then 0x30 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0, 0⟩, ⟨0x8000, 28⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0, 2560⟩]

/-- A state satisfying the precondition of `vg_aes_ccm_open`: as `sealSat`,
with the tag read only. -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0x8000, 28⟩], wr := [⟨0, 0⟩, ⟨0, 2560⟩] }

theorem seal_verified : Verified Arm.target «seal» (Proof.AesCcm.sealScratchContract Arm.abi 16) :=
  Verified.of_correct (fun _ hs => seal_wp hs) seal_ct (by
    sig_implies [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre, Proof.AesCcm.sealRoundsPost,
      sealArm, sealPre, oneLay, onePub, bel16, arg, args, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, Arm.State.addr]
      [sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sealSat)

theorem open_verified : Verified Arm.target «open» (Proof.AesCcm.openScratchContract Arm.abi 16) :=
  Verified.of_correct (fun _ hs => open_wp hs) open_ct
    { pre := by
        sig_implies_pre [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre, Spec.Ccm.openLeak,
          openArm, openPre, oneLay, onePub, openLeak, bel16, arg, args, roundsOk, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Proof.AesCcm.openRoundsPost, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [openArm, openRes, ciph, Arm.State.addr] at h
        obtain e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        intro _
        rw [e]
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre, Spec.Ccm.openLeak,
          openArm, openPre, oneLay, onePub, openLeak, bel16, arg, args, roundsOk, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
        obtain ⟨hsp, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6⟩ := h
        refine ⟨⟨hsp, h0, h1, h2, h3, fun i hi => ?_⟩, hl⟩
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega_using [hi]) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact a0
        · exact a1
        · exact a2
        · exact a3
        · exact a4
        · exact a5
        · exact a6
      sat := by
        sig_implies_sat [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre, Spec.Ccm.openLeak,
          openArm, openPre, oneLay, onePub, openLeak, bel16, arg, args, roundsOk, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [openSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using openSat }

end VG.Proof.AesCcm.Arm

end

end


/-!
# AES-CCM on ARMv7, with its working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (`Verified.lean`), in a frame that allocates it
(`Verified.stackScratchLost`): their working space is their seventh stack
argument, after `aad`, `aad_len`, `data`, `len`, `tag` and `tag_len`, so the
frame of 2592 bytes holds a copy of those six words, the address of the
working space, the saved `lr` and the working space. The copies are read
only where the pre- and postconditions read the buffers, and `open`'s leak,
whether it succeeds, reads only its buffers (`Proof/AesCcm/Scratch.lean`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Impl.AesCcm.Arm

/-- A state satisfying `vg_aes_ccm_seal`'s precondition, without the working
space: its six words of stack arguments at `0x8000`. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0, 0⟩, ⟨0x8000, 24⟩],
                 wr := [⟨0, 0⟩, ⟨0x3000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesCcm.sealRoundsContract Arm.abi 2608).pre s := by
  implies_sat [Proof.AesCcm.sealRoundsContract, Spec.Ccm.sealSig, Spec.Ccm.sealPre, Proof.AesCcm.sealRoundsPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [sealFrameSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2592 6 «seal»)
      (Proof.AesCcm.sealRoundsContract Arm.abi 2608) :=
  Arm.Verified.stackScratchLost (sig := Spec.Ccm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.sealPre Arm.abi.ptrBits)
    (post := Proof.AesCcm.sealRoundsPost Arm.abi.ptrBits) (wa := true) (stack := 16)
    (m := 6) seal_verified (by decide) (by decide) (by decide) (by decide)
    (sealPre_local _) (sealPost_local _) (sealPostOut_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_ccm_open`'s precondition, without the working
space: its six words of stack arguments at `0x8000`. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0x8000, 24⟩],
                 wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesCcm.openRoundsContract Arm.abi 2608).pre s := by
  implies_sat [Proof.AesCcm.openRoundsContract, Spec.Ccm.openSig, Spec.Ccm.openPre, Proof.AesCcm.openRoundsPost,
    Spec.Ccm.openLeak, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [openFrameSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using openFrameSat

theorem open_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2592 6 «open»)
      (Proof.AesCcm.openRoundsContract Arm.abi 2608) :=
  Arm.Verified.stackScratchLost (sig := Spec.Ccm.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.openPre Arm.abi.ptrBits)
    (post := Proof.AesCcm.openRoundsPost Arm.abi.ptrBits) (wa := true) (stack := 16)
    (leak := some (Spec.Ccm.openLeak Arm.abi.ptrBits))
    (m := 6) open_verified (by decide) (by decide) (by decide) (by decide)
    (openPre_local _) (openPost_local _) (openPostOut_local _) openFrameSat_pre
    (hleak := openLeak_local _)

end VG.Proof.AesCcm.Arm
