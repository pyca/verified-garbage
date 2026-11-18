module

public import VerifiedGarbage.Proof.AesGcm.Arm.CTBase
public import VerifiedGarbage.Proof.AesGcm.Arm.Crypt
import VerifiedGarbage.Proof.AesGcm.Arm.Tag
meta import VerifiedGarbage.Proof.AesGcm.Arm.Tag
import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
import VerifiedGarbage.Proof.AesGcm.Arm.Entry
import VerifiedGarbage.Proof.AesGcm.Arm.Ghash1
import VerifiedGarbage.Proof.AesGcm.Arm.Loops
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Impl.Aes.Arm.Alloc
meta import VerifiedGarbage.Proof.AesGcm.Arm.Entry
meta import VerifiedGarbage.Proof.AesGcm.Arm.Ghash1
meta import VerifiedGarbage.Proof.AesGcm.Arm.Loops
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Bytes
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Proof.AesGcm.Arm.Fn
meta import VerifiedGarbage.Proof.AesGcm.Arm.CTBase
import VerifiedGarbage.Proof.AesGcm.Arm.Flush
meta import VerifiedGarbage.Proof.AesGcm.Arm.Flush
import VerifiedGarbage.Proof.AesGcm.Arm.StreamFinish
import VerifiedGarbage.Proof.AesGcm.Arm.Compare
import VerifiedGarbage.Proof.AesGcm.Arm.Init
public import VerifiedGarbage.Proof.AesGcm.Arm.Args
import VerifiedGarbage.Proof.Framework.SigEval
public import VerifiedGarbage.Proof.Gcm.Arm.Ghash
public import VerifiedGarbage.Impl.AesGcm.Arm
public import VerifiedGarbage.Proof.AesGcm.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.AesGcm.Arm.StreamFinish
meta import VerifiedGarbage.Proof.AesGcm.Arm.Compare
meta import VerifiedGarbage.Proof.AesGcm.Arm.Init
meta import VerifiedGarbage.Proof.AesGcm.Arm.Args
meta import VerifiedGarbage.Proof.AesGcm.Arm.Fn
meta import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.Gcm.Arm.Ghash
meta import VerifiedGarbage.Impl.AesGcm.Arm
meta import VerifiedGarbage.Proof.AesGcm.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Semantics

/-! ### `AesGcm.Arm.CTAbsorb`, which this module and modules that import it used -/

section

/-! ### `AesGcm.Arm.Open`, which this module and modules that import it used -/

section

/-! ### `AesGcm.Arm.StreamVerify`, which this module and modules that import it used -/

section

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_stream_verify`

Untrusted: everything here is checked by Lean. `stream_verify` saves our
caller's registers in `work` (`W`), checks the tag length, and, if it is
allowed, copies the received tag (at `tag`) to `W + 256`, writes the tag to
`W` and compares the first `tag_len` bytes of each; if the length is not
allowed the result is 0 (`streamVerify_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput fullTag zeros)
open VG.Proof.Cmac (store4)

theorem bytesAt_take (m : Mem) (p : Addr) {k n : Nat} (h : k ≤ n) : bytesAt m p k = (bytesAt m p n).take k := by
  rw [show n = k + (n - k) by omega_using [h], bytesAt_add, List.take_left' (length_bytesAt _ _ _)]

theorem tagLenOk_bounds {tl : Nat} (h : Spec.Gcm.tagLenOk tl = true) : 1 ≤ tl ∧ tl ≤ 16 := by
  simp only [Spec.Gcm.tagLenOk, Bool.and_eq_true, decide_eq_true_eq] at h
  omega_using [h]

/-- What `verify` promises, for the additional data `a` and the text `ct`. -/
def VerPost (s₀ : State) (a ct : List Byte) (s : State) : Prop :=
  ∀ iv, StreamRepr s₀.mem (State.addr (s₀.gpr .r2)) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct → arg64 s₀ 0 = BitVec.ofNat 64 a.length →
    let t := fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct
    if Spec.Gcm.tagLenOk (arg s₀ 5).toNat ∧ t.take (arg s₀ 5).toNat = bytesAt s₀.mem (State.addr (arg s₀ 4))
        (arg s₀ 5).toNat then s.gpr .r0 = 1
    else s.gpr .r0 = 0

theorem ver_run [VG.Proof.Gcm.Arm.GhashLaw] {s₀ : State} (h : streamVerifyPreArm s₀) {a ct : List Byte} (ha : a.length % 16 = (arg s₀ 0).toNat % 16)
    (hP : (arg s₀ 3 ++ arg s₀ 2).toNat = ct.length) :
    WP isa streamVerify s₀ fun s' => abiPreserved s₀ s' ∧ VerPost s₀ a ct s' := by
  obtain h' : finPre 7 6 s₀ := streamVerifyPreArm.fin h
  obtain L := finLay h'
  have hR := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have spf := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have fW := h'.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ 7 ∈ s₀.rd := h'.1.2
  obtain ⟨hrd, -, -, -, -, -, -, tW, -, -, -, -, -, -, -, fT, -⟩ := h
  obtain hTr : Covers [⟨State.addr (arg s₀ 4), (arg s₀ 5).toNat⟩] (s₀.rd ++ s₀.wr) :=
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
  obtain dT : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨State.addr (arg s₀ 4), (arg s₀ 5).toNat⟩ : Region).Disjoint
      ⟨State.addr (arg s₀ 6) + BitVec.ofNat 64 d, k⟩ := fun hd => tW.sub_right (Lay.wSub hd)
  obtain dW : ∀ {d k : Nat}, d + k ≤ 2560 → (164 ≤ d ∨ d + k ≤ 128) →
      (savedR (arg s₀ 6)).Disjoint ⟨State.addr (arg s₀ 6) + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ h₂ => Lay.w_w (by omega_using [h₂]) (by decide) h₁
  refine WP.seq (WP.block_append (fin1_wp (wi := 6) h' (by decide) (by decide) fun s₁ h1 => ?_))
  obtain ⟨i5, v5⟩ := h1.args.at spf hin 5 (by decide) (show 4 * 5 = 20 from rfl)
  obtain ⟨s₂, run₂, h6₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [.ldrSp .r6 20] s₁ = some s₂ ∧
      s₂.gpr .r6 = BitVec.ofNat 32 (arg s₀ 5).toNat ∧ (∀ r, r ≠ .r6 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    refine ⟨_, by arun [i5, v5], ?_, ?_, ?_⟩
    · simp [gpr_setReg, v5]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  obtain he₂ := h1.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide)) k₂.sp k₂.rd k₂.wr
  refine WP.seq (WP.mono (tagLenOk_ok h6₂ (arg s₀ 5).isLt) fun s₃ ⟨hz₃, g₃, k₃⟩ => ?_)
  obtain k₁₃ := k₂.trans k₃
  obtain he₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide)) k₃.sp k₃.rd k₃.wr
  obtain hk₃ := h1.args.of_eq k₁₃.mem k₁₃.sp k₁₃.rd k₁₃.wr
  obtain sv₃ : SavedAt s₃.mem (arg s₀ 6) s₀ := k₁₃.mem ▸ h1.saved
  obtain mid : WP isa (.ite .eq (.block [.mov .r0 (imm 0)]) (.seq recv (.seq (finTag 0) (.seq (.block [.ldrSp .r6 20])
      (cmp 0))))) s₃ fun s' => (∃ k7, Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp k7
        (s₀.gpr .r1) s') ∧ SavedAt s'.mem (arg s₀ 6) s₀ ∧ VerPost s₀ a ct s' := by
    refine WP.ite _ (eval_eq' hz₃) (fun ht => ?_) (fun hf => ?_)
    · have hbad : Spec.Gcm.tagLenOk (arg s₀ 5).toNat = false := by simpa using ht
      refine WP.of_runBlock ⟨s₃.setReg .r0 (BitVec.ofNat 32 0), by arun [], ⟨_, he₃.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl) rfl rfl rfl⟩, sv₃, fun iv _ _ => ?_⟩
      simp only [hbad, Bool.false_eq_true, false_and, ite_false]
      simp [gpr_setReg]
    · have hok : Spec.Gcm.tagLenOk (arg s₀ 5).toNat = true := by simpa using hf
      obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
      obtain h6₃ : s₃.gpr .r6 = BitVec.ofNat 32 (arg s₀ 5).toNat := by rw [g₃ _ (by decide), h6₂]
      obtain ⟨i4, v4⟩ := hk₃.at spf hin 4 (by decide) (show 4 * 4 = 16 from rfl)
      refine WP.seq (WP.mono (recv_ok L he₃ i4 v4 (by rw [hk₃.rd, hk₃.wr]; exact hTr) fT (dT (by decide)) h6₃ t1 t16)
        fun s₄ hh => ?_)
      obtain ⟨hb₄, hf₄, g₄, rd₄, wr₄, sp₄⟩ := hh
      obtain he₄ := he₃.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₄ _ (by decide) (by decide) (by decide) (by decide)
          (by decide)) sp₄ rd₄ wr₄
      obtain dA : ∀ {d k : Nat}, d + k ≤ 2560 → (args s₀ 7).Disjoint ⟨State.addr (arg s₀ 6) + BitVec.ofNat 64 d, k⟩ :=
        fun hd => (h'.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
      obtain hk₄ := hk₃.frame spf hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dA (by decide)) sp₄ rd₄ wr₄
      obtain f₀₄ : Frame [savedR (arg s₀ 6), ⟨State.addr (arg s₀ 6) + BitVec.ofNat 64 256, 16⟩] s₀.mem s₄.mem :=
        (h1.frame.mono (by simp)).trans ((k₁₃.mem ▸ hf₄ : Frame _ s₁.mem s₄.mem).mono (by simp))
      obtain dc₀₄ : ∀ r ∈ [savedR (arg s₀ 6), ⟨State.addr (arg s₀ 6) + BitVec.ofNat 64 256, 16⟩],
          (⟨State.addr (s₀.gpr .r0), 256⟩ : Region).Disjoint r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact L.cw'.sub_right (Lay.wSub (by decide))
        · exact L.cw'.sub_right (Lay.wSub (by decide))
      obtain ds₀₄ : ∀ r ∈ [savedR (arg s₀ 6), ⟨State.addr (arg s₀ 6) + BitVec.ofNat 64 256, 16⟩],
          (⟨State.addr (s₀.gpr .r2), 80⟩ : Region).Disjoint r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · simpa using L.st_w (a := 0) (n := 80) (d := 128) (k := 36) (by decide) (.inr ⟨by decide, by decide⟩)
        · simpa using L.st_w (a := 0) (n := 80) (d := 256) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
      refine WP.seq (WP.mono (WP.with_rdwr (finTag_ok L (na := 7) (by decide) (o := 0) (.inl rfl) he₄ hk₄ spf hin
        (fin_argsTag h' (.inl rfl)) (show s₀.gpr .r1 = BitVec.ofNat 32 (s₀.gpr .r1).toNat by simp) hR
        (ctxH_keep f₀₄ dc₀₄) ha hP)) fun s₅ hh => ?_)
      obtain ⟨fo, rd₅, wr₅, sp₅⟩ := hh
      obtain ⟨k7₅, he₅⟩ := fo.env
      obtain ⟨j5, w5⟩ := fo.args.at spf hin 5 (by decide) (show 4 * 5 = 20 from rfl)
      obtain ⟨s₆, run₆, h6₆, g₆, k₆⟩ : ∃ s₆, runBlock isa [.ldrSp .r6 20] s₅ = some s₆ ∧
          s₆.gpr .r6 = BitVec.ofNat 32 (arg s₀ 5).toNat ∧ (∀ r, r ≠ .r6 → s₆.gpr r = s₅.gpr r) ∧ Keeps s₅ s₆ := by
        refine ⟨_, by arun [j5, w5], ?_, ?_, ?_⟩
        · simp [gpr_setReg, w5]
        · intro r hr; simp [gpr_setReg, hr]
        · exact ⟨rfl, rfl, rfl, rfl⟩
      refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
      obtain he₆ := he₅.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₆ _ (by decide)) k₆.sp k₆.rd k₆.wr
      refine WP.mono (cmp_ok L he₆ (o := 0) (.inl rfl) h6₆ t1 t16) fun s₇ hh => ?_
      obtain ⟨h0₇, hf₇, g₇, rd₇, wr₇, sp₇⟩ := hh
      refine ⟨⟨k7₅, he₆.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₇ _ (by decide) (by decide) (by decide) (by decide)
          (by decide)) sp₇ rd₇ wr₇⟩, ?_, fun iv hs hl => ?_⟩
      · have sv₅ := (sv₃.frame hf₄ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact dW (by decide) (.inl (by decide)))).frame fo.frame
          (saved_tagFrame L (.inl rfl))
        obtain sv₆ : SavedAt s₆.mem (arg s₀ 6) s₀ := k₆.mem ▸ sv₅
        refine sv₆.frame hf₇ ?_
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact dW (by decide) (.inl (by decide))
      · have ht' : bytesAt s₆.mem (State.addr (arg s₀ 6) + BitVec.ofNat 64 0) 16 =
            fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
              (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct := by
          rw [k₆.mem]; exact fin_out h' f₀₄ dc₀₄ ds₀₄ fo hs hl
        obtain hrc : bytesAt s₆.mem (State.addr (arg s₀ 6) + BitVec.ofNat 64 256) 16 =
            bytesAt s₀.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat ++ zeros (16 - (arg s₀ 5).toNat) := by
          rw [k₆.mem, bytesAt_frame fo.frame (fun r hr => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl | rfl | rfl | rfl
              · have := L.st_w (a := 0) (n := 32) (d := 256) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
                simp only [add_ofNat_zero] at this
                exact this.symm
              · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
              · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
              · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
              · exact (L.stk_w (by decide)).symm) (by decide), hb₄, k₁₃.mem,
            bytesAt_frame h1.frame (fun r hr => by
              simp only [List.mem_singleton] at hr; subst hr
              exact dT (d := 128) (k := 36) (by decide)) (by omega_using [])]
        obtain hX : (bytesAt s₆.mem (State.addr (arg s₀ 6) + BitVec.ofNat 64 0) (arg s₀ 5).toNat ++
              zeros (16 - (arg s₀ 5).toNat) = bytesAt s₆.mem (State.addr (arg s₀ 6) + BitVec.ofNat 64 256) 16) ↔
            (fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
              (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct).take (arg s₀ 5).toNat =
              bytesAt s₀.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat := by
          rw [bytesAt_take _ _ t16, ht', hrc, List.append_cancel_right_eq]
        simp only [hok, true_and]
        by_cases e : (fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
              (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct).take (arg s₀ 5).toNat =
              bytesAt s₀.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat
        · simp only [e, ite_true]
          rw [h0₇]; simp only [hX.mpr e, ite_true]
        · simp only [e, ite_false]
          rw [h0₇]; simp only [show ¬ _ from fun x => e (hX.mp x), ite_false]
  refine WP.seq (WP.mono mid fun s₄ hh => ?_)
  obtain ⟨⟨k7, he⟩, sv, vp⟩ := hh
  refine WP.mono (restore_ok he.r11 fW (covers_left he.perm.w) sv he.sp) fun s' hh => ⟨hh.1, fun iv hs hl => ?_⟩
  have := vp iv hs hl
  rw [hh.2.2.1]; exact this

theorem streamVerify_wp [VG.Proof.Gcm.Arm.GhashLaw] {s₀ : State} (h : streamVerifyArm.pre s₀) :
    WP isa streamVerify s₀ fun s' => abiPreserved s₀ s' ∧ streamVerifyArm.post s₀ s' := by
  obtain h₀ := ver_run h (a := List.replicate ((arg s₀ 0).toNat % 16) 0)
    (ct := List.replicate (arg s₀ 3 ++ arg s₀ 2).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte =>
      arg64 s₀ 0 = BitVec.ofNat 64 i.1.length ∧ (arg64 s₀ 2).toNat = i.2.length)
    fun i hi => WP.mono (ver_run h (a := i.1) (ct := i.2) (low_mod16 hi.1).symm hi.2) fun _ hh => hh.2)
    fun s' hh => ⟨hh.1, fun iv a c hs hl hp => hh.2 ⟨a, c⟩ ⟨hl, hp⟩ iv hs hl⟩

end VG.Proof.AesGcm.Arm

end

end

/-! ### `AesGcm.Arm.Seal`, which this module and modules that import it used -/

section

/-! ### `AesGcm.Arm.OneShot`, which this module and modules that import it used -/

section

/-!
# AES-GCM on ARMv7: the pieces of `vg_aes_gcm_seal` and `vg_aes_gcm_open`

Untrusted: everything here is checked by Lean. Both keep a streaming state at
`W + 16`: the entry saves our caller's registers (`one1_wp`), `oneAad` writes
`J₀` and absorbs the additional data, padded (`oneAad_ok`), `oneCrypt` runs
counter mode over the data from the first counter block (`oneCrypt_ok`), and
`oneTag o` absorbs the data as ciphertext, padded, then the lengths block,
and writes the tag to `W + o` (`oneTag_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph ghashInput fullTag zeros padLen j0 inc32 gctr ghash ghashFrom blocks
  toBytes ofBytes)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock padded)

section
variable {n wi : Nat}

/-- The state, at `W + 16`. -/
abbrev oSt (s₀ : State) (wi : Nat) : BitVec 32 := arg s₀ wi + BitVec.ofNat 32 16

theorem oneLay {s₀ : State} (h : onePre n wi s₀) : Lay (s₀.gpr .r0) (oSt s₀ wi) (arg s₀ wi) s₀.sp := by
  sig_split h
  rename_i hdrop0 hdrop1 hdrop2 dcW hdrop4 hdrop5 hdrop6 hdrop7 hdrop8 hdrop9 hdrop10 bc hdrop12 hdrop13
    hdrop14 bW fc hdrop17 hdrop18 hdrop19 fW sp8 hdrop22
  clear hdrop0 hdrop1 hdrop2 hdrop4 hdrop5 hdrop6 hdrop7 hdrop8 hdrop9 hdrop10 hdrop12 hdrop13 hdrop14 hdrop17
    hdrop18 hdrop19 hdrop22
  clear h
  exact initLay fc fW sp8 dcW bc bW

theorem oSt_addr {s₀ : State} (h : onePre n wi s₀) :
    State.addr (oSt s₀ wi) = State.addr (arg s₀ wi) + BitVec.ofNat 64 16 :=
  addr_add (by have := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega_arith)

/-- A buffer apart from `W` is apart from the state. -/
theorem oSt_disj {s₀ : State} (h : onePre n wi s₀) {R : Region} (hR : R.Disjoint ⟨State.addr (arg s₀ wi), 2560⟩) :
    R.Disjoint ⟨State.addr (oSt s₀ wi), 80⟩ := by
  rw [oSt_addr h]; exact hR.sub_right (Lay.wSub (by decide))

/-- After the entry, from `s₀`. -/
structure SO1 (n wi : Nat) (s₀ s₁ : State) : Prop where
  env : Env (s₀.gpr .r0) (oSt s₀ wi) (arg s₀ wi) s₀.sp (s₀.gpr .r7) (s₀.gpr .r1) s₁
  r4 : s₁.gpr .r4 = s₀.gpr .r2
  r5 : s₁.gpr .r5 = s₀.gpr .r3
  args : ArgsKeep n s₀ s₁
  saved : SavedAt s₁.mem (arg s₀ wi) s₀
  frame : Frame [savedR (arg s₀ wi)] s₀.mem s₁.mem

theorem one1_wp {s₀ : State} (h : onePre n wi s₀) (hn : wi < n) (hwi : 4 * wi < 4096) {Q : State → Prop}
    (k : ∀ s₁, SO1 n wi s₀ s₁ → Q s₁) : WP isa (.block (oneEntry (4 * wi))) s₀ Q := by
  obtain hst := oSt_addr h
  have ww := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨⟨hc, -, -, hin⟩, ⟨-, hw, -⟩, -, -, -, -, -, -, -, -, dWA, -, -, -, -, -, -, -, -, -, fW, -, spf, -⟩ := h
  obtain hA : ∀ r ∈ [savedR (arg s₀ wi)], (args s₀ n).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (dWA.sub_left (Lay.wSub (by decide))).symm
  obtain hC : Covers [⟨State.addr (s₀.gpr .r0), 256⟩] (s₀.rd ++ s₀.wr) :=
    covers_of_mem (List.mem_append_left _ hc)
  obtain hW : Covers [⟨State.addr (arg s₀ wi), 2560⟩] s₀.wr := covers_of_mem hw
  obtain hS : Covers [⟨State.addr (oSt s₀ wi), 80⟩] s₀.wr := by rw [hst]; exact covers_off hW (by decide) (by decide)
  obtain ha : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 (4 * wi))) 4 := arg_in hn spf hin
  refine entry_ok (off := 4 * wi) hwi ha fW hW fun s₁ g12 g rd wr sp sv fr => ?_
  obtain hk : ArgsKeep n s₀ s₁ := (ArgsKeep.refl n s₀).frame spf fr hA sp rd wr
  refine WP.of_runBlock ⟨_, by arun [], ?_⟩
  refine k _ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩, ?_, ?_, ?_, sv, fr⟩
  any_goals (simp [gpr_setReg, g, g12]; done)
  · simp [gpr_setReg, g, g12]; rfl
  · simp [gpr_setReg, g, g12]; rfl
  · exact sp
  · change Covers _ (s₁.rd ++ s₁.wr); rw [rd, wr]; exact hC
  · change Covers _ s₁.wr; rw [wr]; exact hS
  · change Covers _ s₁.wr; rw [wr]; exact hW
  · exact hk.of_eq rfl rfl rfl rfl

end

theorem abs16_sub {st w sp : BitVec 32} : ∀ r ∈ absFrame st w sp 16, ∃ r' ∈ j0Frame st w sp, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem t16_sub {st w sp : BitVec 32} : ∀ r ∈ tFrame st w sp 16, ∃ r' ∈ j0Frame st w sp, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem abs16_j0Frame {st w sp : BitVec 32} {m m' : Mem} (h : Frame (absFrame st w sp 16) m m') :
    Frame (j0Frame st w sp) m m' := h.sub abs16_sub

theorem t16_j0Frame {st w sp : BitVec 32} {m m' : Mem} (h : Frame (tFrame st w sp 16) m m') :
    Frame (j0Frame st w sp) m m' := h.sub t16_sub

section
variable {n wi : Nat}

/-- The stack arguments are apart from what `j0` (and the other pieces) write. -/
theorem one_argsJ0 {s₀ : State} (h : onePre n wi s₀) :
    ∀ r ∈ j0Frame (oSt s₀ wi) (arg s₀ wi) s₀.sp, (args s₀ n).Disjoint r := by
  obtain hst := oSt_addr h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, dWA, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [hst]; exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (below_args s₀ spf).symm

/-- A buffer apart from `W` and the stack below `sp` is apart from what `j0` writes. -/
theorem one_dataJ0 {s₀ : State} (h : onePre n wi s₀) {R : Region} (hW : R.Disjoint ⟨State.addr (arg s₀ wi), 2560⟩)
    (hb : (below s₀.sp).Disjoint R) : ∀ r ∈ j0Frame (oSt s₀ wi) (arg s₀ wi) s₀.sp, R.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact oSt_disj h hW
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hb.symm

/-- After `oneAad`, from `m₁`. -/
structure OA (n wi : Nat) (s₀ : State) (m₁ : Mem) (s : State) : Prop where
  env : ∃ k7, Env (s₀.gpr .r0) (oSt s₀ wi) (arg s₀ wi) s₀.sp k7 (s₀.gpr .r1) s
  args : ArgsKeep n s₀ s
  j : blockAt s.mem (State.addr (oSt s₀ wi)) =
    j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat)
  cb : blockAt s.mem (State.addr (oSt s₀ wi) + BitVec.ofNat 64 48) =
    inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat))
  abs : Absorbed s.mem (State.addr (oSt s₀ wi) + BitVec.ofNat 64 16) (State.addr (oSt s₀ wi) + BitVec.ofNat 64 32)
    (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
    (bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat ++
      zeros (padLen (bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat).length))
  hH : blockAt s.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0))
  frame : Frame (j0Frame (oSt s₀ wi) (arg s₀ wi) s₀.sp) m₁ s.mem

theorem oneAad_ok [VG.Proof.Gcm.Arm.GhashLaw] {s₀ s₁ : State} (h : onePre n wi s₀) (hn : 5 ≤ n) (h1 : SO1 n wi s₀ s₁) :
    WP isa oneAad s₁ (OA n wi s₀ s₁.mem) := by
  obtain L := oneLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ n ∈ s₀.rd := h.1.2.2.2
  have hp := h
  sig_split hp
  rename_i hrd hdrop1 hdrop2 hdrop3 hdrop4 dnW hdrop6 daW hdrop8 hdrop9 hdrop10 hdrop11 bn ba hdrop14 hdrop15
    hdrop16 fn fa hdrop19 hdrop20 hdrop21 hdrop22
  clear hdrop1 hdrop2 hdrop3 hdrop4 hdrop6 hdrop8 hdrop9 hdrop10 hdrop11 hdrop14 hdrop15 hdrop16 hdrop19
    hdrop20 hdrop21 hdrop22
  clear hp
  obtain hH₁ := ctxH_keep h1.frame (ctx_saved L)
  obtain ji : J0In (s₀.gpr .r0) (oSt s₀ wi) (arg s₀ wi) s₀.sp (s₀.gpr .r7) (s₀.gpr .r1)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (s₀.gpr .r2) (s₀.gpr .r3).toNat s₁ :=
    ⟨h1.env, hH₁, h1.r4, by rw [h1.r5]; simp, ⟨by
      rw [h1.args.rd, h1.args.wr]; exact covers_of_mem (List.mem_append_left _ hrd.2.1),
      (s₀.gpr .r3).isLt, fn, oSt_disj h dnW, dnW, bn⟩⟩
  refine WP.seq (WP.mono (WP.with_rdwr (j0_ok L ji)) fun s₂ hh => ?_)
  obtain ⟨jo, rd₂, wr₂, sp₂⟩ := hh
  obtain ⟨k7, he₂⟩ := jo.env
  obtain hiv : bytesAt s₁.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat =
      bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat :=
    bytesAt_frame h1.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dnW.sub_right (Lay.wSub (by decide))) (by omega_arith)
  rw [hiv] at jo
  obtain hk₂ := h1.args.frame spf jo.frame (one_argsJ0 h) sp₂ rd₂ wr₂
  obtain ⟨a0, v0⟩ := hk₂.at spf hin 0 (by omega_arith) (show 4 * 0 = 0 from rfl)
  obtain ⟨a1, v1⟩ := hk₂.at spf hin 1 (by omega_arith) (show 4 * 1 = 4 from rfl)
  obtain ⟨s₃, run₃, h4₃, h5₃, h6₃, g₃, k₃⟩ : ∃ s₃, runBlock isa [.ldrSp .r4 0, .ldrSp .r5 4, .mov .r6 (imm 0)] s₂ =
      some s₃ ∧ s₃.gpr .r4 = arg s₀ 0 ∧ s₃.gpr .r5 = arg s₀ 1 ∧ s₃.gpr .r6 = BitVec.ofNat 32 0 ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ := by
    refine ⟨_, by arun [a0, v0, a1, v1], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, v0]
    · simp [gpr_setReg, v1]
    · simp [gpr_setReg]
    · intro r x y z; simp [gpr_setReg, x, y, z]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  obtain he₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide) (by decide)) k₃.sp k₃.rd k₃.wr
  obtain hk₃ := hk₂.of_eq k₃.mem k₃.sp k₃.rd k₃.wr
  obtain hda : DataOk (oSt s₀ wi) (arg s₀ wi) s₀.sp s₃ (arg s₀ 0) (arg s₀ 1).toNat :=
    ⟨by rw [hk₃.rd, hk₃.wr]; exact covers_of_mem (List.mem_append_left _ hrd.2.2.1), (arg s₀ 1).isLt, fa,
      oSt_disj h daW, daW, ba⟩
  obtain haad : bytesAt s₃.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat =
      bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat := by
    rw [k₃.mem, bytesAt_frame jo.frame (one_dataJ0 h daW ba) (by omega_arith),
      bytesAt_frame h1.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact daW.sub_right (Lay.wSub (by decide))) (by omega_arith)]
  obtain ai : AbsIn (s₀.gpr .r0) (oSt s₀ wi) (arg s₀ wi) s₀.sp k7 (s₀.gpr .r1) 16 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) []
      (arg s₀ 0) (arg s₀ 1).toNat s₃ :=
    ⟨he₃, h4₃, by rw [h5₃]; simp, by rw [h6₃]; rfl, hda, by rw [k₃.mem]; exact jo.hH⟩
  refine WP.seq (WP.mono (WP.with_rdwr (absorb_ok L (.inr rfl) ai)) fun s₄ hh => ?_)
  obtain ⟨ab, rd₄, wr₄, sp₄⟩ := hh
  rw [haad, List.nil_append] at ab
  obtain hk₄ := hk₃.frame spf ab.frame (disj_sub (one_argsJ0 h) abs16_sub) sp₄ rd₄ wr₄
  obtain ⟨b1, w1⟩ := hk₄.at spf hin 1 (by omega_arith) (show 4 * 1 = 4 from rfl)
  obtain ⟨s₅, run₅, h6₅, g₅, k₅⟩ : ∃ s₅, runBlock isa [.ldrSp .r6 4, .dp .and .r6 .r6 (imm 15)] s₄ = some s₅ ∧
      s₅.gpr .r6 = BitVec.ofNat 32 ((arg s₀ 1).toNat % 16) ∧ (∀ r, r ≠ .r6 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    refine ⟨_, by arun [b1, w1], ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, w1, and15]
    · intro r x; simp [gpr_setReg, x]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  obtain he₅ := ab.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₅ _ (by decide)) k₅.sp k₅.rd k₅.wr
  obtain hk₅ := hk₄.of_eq k₅.mem k₅.sp k₅.rd k₅.wr
  obtain hH₄ : blockAt s₄.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0)) := by
    rw [blockAt_frame ab.frame (ctx_absFrame L (.inr rfl)), k₃.mem]; exact jo.hH
  refine WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl)
    (x := bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat) (H := ctxH s₀.mem (State.addr (s₀.gpr .r0)))
    ⟨he₅, by rw [k₅.mem]; exact hH₄⟩ (by rw [h6₅, length_bytesAt]))) fun s₆ hh => ?_
  obtain ⟨fl, rd₆, wr₆, sp₆⟩ := hh
  rw [k₅.mem] at fl
  obtain keepA : ∀ {d : Nat}, (d = 0 ∨ d = 48) → ∀ r ∈ absFrame (oSt s₀ wi) (arg s₀ wi) s₀.sp 16,
      (⟨State.addr (oSt s₀ wi) + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.st_st (by omega_arith) (by omega_arith) (by decide)
    · exact Lay.st_st (by omega_arith) (by omega_arith) (by decide)
    · exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)
    · exact (L.stk_st (by omega_arith)).symm
  obtain keepT : ∀ {d : Nat}, (d = 0 ∨ d = 48) → ∀ r ∈ tFrame (oSt s₀ wi) (arg s₀ wi) s₀.sp 16,
      (⟨State.addr (oSt s₀ wi) + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.st_st (by omega_arith) (by omega_arith) (by decide)
    · exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)
    · exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)
    · exact (L.stk_st (by omega_arith)).symm
  obtain blk : ∀ {d : Nat}, (d = 0 ∨ d = 48) → blockAt s₆.mem (State.addr (oSt s₀ wi) + BitVec.ofNat 64 d) =
      blockAt s₂.mem (State.addr (oSt s₀ wi) + BitVec.ofNat 64 d) := fun hd => by
    rw [blockAt_frame fl.frame (keepT hd), blockAt_frame ab.frame (keepA hd), k₃.mem]
  refine ⟨⟨k7, fl.env⟩, hk₄.frame spf fl.frame (disj_sub (one_argsJ0 h) t16_sub) (sp₆.trans k₅.sp) (rd₆.trans k₅.rd)
    (wr₆.trans k₅.wr), ?_, ?_, ?_, fl.hH, ?_⟩
  · have := blk (d := 0) (.inl rfl); rw [add_ofNat_zero] at this; rw [this]; exact jo.j0
  · rw [blk (.inr rfl)]; exact jo.cb
  · exact fl.abs (ab.abs (by rw [k₃.mem]; exact Proof.Gcm.absorbed_nil _ jo.y))
  · rw [k₃.mem] at ab
    exact (jo.frame.trans (abs16_j0Frame ab.frame)).trans (t16_j0Frame fl.frame)

/-- The data, for `crypt` and `absorb`. -/
theorem one_dataOk {s₀ s : State} (h : onePre n wi s₀) (hk : ArgsKeep n s₀ s) :
    DataOk (oSt s₀ wi) (arg s₀ wi) s₀.sp s (arg s₀ 2) (arg s₀ 3).toNat := by
  have hp := h
  sig_split hp
  rename_i hdrop0 hwr hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 hdrop7 dDW hdrop9 hdrop10 hdrop11 hdrop12 hdrop13 bD
    hdrop15 hdrop16 hdrop17 hdrop18 fD hdrop20 hdrop21 hdrop22
  clear hdrop0 hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 hdrop7 hdrop9 hdrop10 hdrop11 hdrop12 hdrop13 hdrop15
    hdrop16 hdrop17 hdrop18 hdrop20 hdrop21 hdrop22
  clear hp
  exact ⟨by rw [hk.rd, hk.wr]; exact covers_of_mem hwr.1, (arg s₀ 3).isLt, fD,
    oSt_disj h dDW, dDW, bD⟩

theorem dataArgs_run {s₀ s : State} (hk : ArgsKeep n s₀ s) (hf : s₀.sp.toNat + 4 * n ≤ 2 ^ 32)
    (hin : args s₀ n ∈ s₀.rd) (hn : 5 ≤ n) :
    ∃ s', runBlock isa dataArgs s = some s' ∧ s'.gpr .r4 = arg s₀ 2 ∧ s'.gpr .r5 = arg s₀ 3 ∧
      s'.gpr .r6 = BitVec.ofNat 32 0 ∧ (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain ⟨a2, v2⟩ := hk.at hf hin 2 (by omega_arith) (show 4 * 2 = 8 from rfl)
  obtain ⟨a3, v3⟩ := hk.at hf hin 3 (by omega_arith) (show 4 * 3 = 12 from rfl)
  refine ⟨_, by simp only [dataArgs]; arun [a2, v2, a3, v3], ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, v2]
  · simp [gpr_setReg, v3]
  · simp [gpr_setReg]
  · intro r x y z; simp [gpr_setReg, x, y, z]
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- After `oneCrypt`, from `m₀`. -/
structure OC (n wi : Nat) (s₀ : State) (k7 : BitVec 32) (icb : Block) (m₀ : Mem) (s : State) : Prop where
  env : Env (s₀.gpr .r0) (oSt s₀ wi) (arg s₀ wi) s₀.sp k7 (s₀.gpr .r1) s
  args : ArgsKeep n s₀ s
  out : bytesAt s.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat =
    gctr (ciphOf m₀ (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat) icb (bytesAt m₀ (State.addr (arg s₀ 2)) (arg s₀ 3).toNat)
  frame : Frame (crFrame (oSt s₀ wi) (arg s₀ wi) s₀.sp (arg s₀ 2) (arg s₀ 3).toNat) m₀ s.mem

theorem oneCrypt_ok {s₀ s : State} (h : onePre n wi s₀)
    (hw : (⟨State.addr (arg s₀ 2), (arg s₀ 3).toNat⟩ : Region) ∈ s₀.wr) (hn : 5 ≤ n) {k7 : BitVec 32}
    (he : Env (s₀.gpr .r0) (oSt s₀ wi) (arg s₀ wi) s₀.sp k7 (s₀.gpr .r1) s) (hk : ArgsKeep n s₀ s) {icb : Block}
    (hcb : blockAt s.mem (State.addr (oSt s₀ wi) + BitVec.ofNat 64 48) = icb) :
    WP isa oneCrypt s (OC n wi s₀ k7 icb s.mem) := by
  obtain L := oneLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hin : args s₀ n ∈ s₀.rd := h.1.2.2.2
  obtain dcD := h.2.2.1 hw
  obtain ⟨s₁, run₁, h4, h5, h6, g₁, k₁⟩ := dataArgs_run hk spf hin hn
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  obtain hk₁ := hk.of_eq k₁.mem k₁.sp k₁.rd k₁.wr
  obtain ci : CrIn (s₀.gpr .r0) (oSt s₀ wi) (arg s₀ wi) s₀.sp k7 (s₀.gpr .r1) (s₀.gpr .r1).toNat icb 0 (arg s₀ 2)
      (arg s₀ 3).toNat s₁ :=
    ⟨he₁, h4, by rw [h5]; simp, by rw [h6], by rw [he₁.r8]; simp, hR,
      ⟨one_dataOk h hk₁, by rw [hk₁.wr]; exact covers_of_mem hw, dcD⟩⟩
  refine WP.mono (WP.with_rdwr (crypt_ok L ci)) fun s₂ hh => ?_
  obtain ⟨co, rd₂, wr₂, sp₂⟩ := hh
  obtain hA : ∀ r ∈ crFrame (oSt s₀ wi) (arg s₀ wi) s₀.sp (arg s₀ 2) (arg s₀ 3).toNat, (args s₀ n).Disjoint r := by
    obtain hst := oSt_addr h
    obtain ⟨-, -, -, -, -, -, -, -, -, dDA, dWA, -⟩ := h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (dDA hw).symm
    · rw [hst, add_ofNat_assoc]; exact (dWA.sub_left (Lay.wSub (by decide))).symm
    · exact (dWA.sub_left (Lay.wSub (by decide))).symm
    · exact (below_args s₀ spf).symm
  rw [k₁.mem] at co
  obtain c0 := Proof.Gcm.ctr_zero s.mem _ (State.addr (oSt s₀ wi) + BitVec.ofNat 64 64)
    (ciphOf s.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat) hcb
  exact ⟨co.env, hk₁.frame spf (k₁.mem ▸ co.frame) hA sp₂ rd₂ wr₂, by rw [co.out c0, Proof.Gcm.gctr_eq],
    co.frame⟩

end

theorem padded_eq (a c : List Byte) :
    (a ++ zeros (padLen a.length) ++ c) ++ zeros (padLen (a ++ zeros (padLen a.length) ++ c).length) = padded a c := by
  by_cases hc : c = []
  · subst hc
    obtain h0 : padLen (a ++ zeros (padLen a.length) ++ []).length = 0 := by
      apply Proof.Gcm.padLen_of_mod
      simp only [List.append_nil, List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
    rw [h0]; simp [padded, Proof.Gcm.ghashInput_nil, zeros]
  · simp only [padded, Proof.Gcm.ghashInput_of_ne hc]

/-- The regions `oneTag o` writes. -/
abbrev otFrame (st w sp : BitVec 32) (o : Nat) : List Region :=
  [⟨State.addr st, 48⟩, ⟨State.addr w + BitVec.ofNat 64 96, 16⟩, ⟨State.addr w + BitVec.ofNat 64 o, 16⟩,
    ⟨State.addr w + BitVec.ofNat 64 512, 2048⟩, below sp]

theorem abs_otSub {st w sp : BitVec 32} {o : Nat} : ∀ r ∈ absFrame st w sp 16, ∃ r' ∈ otFrame st w sp o, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 512, 2048⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem t_otSub {st w sp : BitVec 32} {o : Nat} : ∀ r ∈ tFrame st w sp 16, ∃ r' ∈ otFrame st w sp o, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 512, 2048⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem tag_otSub {st w sp : BitVec 32} {o : Nat} : ∀ r ∈ tagFrame st w sp o, ∃ r' ∈ otFrame st w sp o, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

section
variable {n wi : Nat}

/-- After `oneTag o`, from `m₀`, for the tag of `a` and the bytes at `data`. -/
structure OT (n wi : Nat) (s₀ : State) (o : Nat) (a : List Byte) (J : Block) (m₀ : Mem) (s : State) : Prop where
  env : ∃ k7, Env (s₀.gpr .r0) (oSt s₀ wi) (arg s₀ wi) s₀.sp k7 (s₀.gpr .r1) s
  args : ArgsKeep n s₀ s
  out : bytesAt s.mem (State.addr (arg s₀ wi) + BitVec.ofNat 64 o) 16 =
    toBytes (ghashFrom (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (ghash (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (blocks (padded a (bytesAt m₀ (State.addr (arg s₀ 2)) (arg s₀ 3).toNat))))
      [ofBytes (lensBlock a.length (bytesAt m₀ (State.addr (arg s₀ 2)) (arg s₀ 3).toNat).length)] ^^^
      ciphOf m₀ (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat J)
  frame : Frame (otFrame (oSt s₀ wi) (arg s₀ wi) s₀.sp o) m₀ s.mem

theorem one_argsOt {s₀ : State} (h : onePre n wi s₀) {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ otFrame (oSt s₀ wi) (arg s₀ wi) s₀.sp o, (args s₀ n).Disjoint r := by
  obtain hst := oSt_addr h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, dWA, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [hst]; exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by omega_arith))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (below_args s₀ spf).symm

theorem oneTag_ok [VG.Proof.Gcm.Arm.GhashLaw] {s₀ s : State} (h : onePre n wi s₀) (hn : 5 ≤ n) {o : Nat} (ho : o = 0 ∨ o = 112) {k7 : BitVec 32}
    (he : Env (s₀.gpr .r0) (oSt s₀ wi) (arg s₀ wi) s₀.sp k7 (s₀.gpr .r1) s) (hk : ArgsKeep n s₀ s)
    (hH : blockAt s.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0)))
    {a : List Byte} (hl : (arg s₀ 1).toNat = a.length)
    (hab : Absorbed s.mem (State.addr (oSt s₀ wi) + BitVec.ofNat 64 16) (State.addr (oSt s₀ wi) + BitVec.ofNat 64 32)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (a ++ zeros (padLen a.length))) :
    WP isa (oneTag o) s (OT n wi s₀ o a (blockAt s.mem (State.addr (oSt s₀ wi))) s.mem) := by
  obtain L := oneLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hin : args s₀ n ∈ s₀.rd := h.1.2.2.2
  obtain hA := one_argsOt h ho
  obtain dC : ∀ r ∈ otFrame (oSt s₀ wi) (arg s₀ wi) s₀.sp o, (⟨State.addr (s₀.gpr .r0), 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.cs.sub_right (Region.sub_prefix (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by omega_arith))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.kc.symm
  obtain dJ : ∀ r ∈ absFrame (oSt s₀ wi) (arg s₀ wi) s₀.sp 16 ++ tFrame (oSt s₀ wi) (arg s₀ wi) s₀.sp 16,
      (⟨State.addr (oSt s₀ wi), 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain e1 : ∀ {d k : Nat}, 16 ≤ d → d + k ≤ 80 →
        (⟨State.addr (oSt s₀ wi), 16⟩ : Region).Disjoint ⟨State.addr (oSt s₀ wi) + BitVec.ofNat 64 d, k⟩ := fun h1 h2 => by
      have := Lay.st_st (st := oSt s₀ wi) (a := 0) (n := 16) (.inl h1) (by decide) h2
      rwa [add_ofNat_zero] at this
    obtain e2 : ∀ {d k : Nat}, 96 ≤ d → d + k ≤ 2560 →
        (⟨State.addr (oSt s₀ wi), 16⟩ : Region).Disjoint ⟨State.addr (arg s₀ wi) + BitVec.ofNat 64 d, k⟩ := fun h1 h2 => by
      have := L.st_w (a := 0) (n := 16) (by decide) (.inr ⟨h1, h2⟩)
      rwa [add_ofNat_zero] at this
    obtain e3 : (⟨State.addr (oSt s₀ wi), 16⟩ : Region).Disjoint (below s₀.sp) := by
      have := (L.stk_st (a := 0) (n := 16) (by decide)).symm
      rwa [add_ofNat_zero] at this
    rcases hr with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
    · exact e1 (by decide) (by decide)
    · exact e1 (by decide) (by decide)
    · exact e2 (by decide) (by decide)
    · exact e3
    · exact e1 (by decide) (by decide)
    · exact e2 (by decide) (by decide)
    · exact e2 (by decide) (by decide)
    · exact e3
  obtain hx : (a ++ zeros (padLen a.length)).length % 16 = 0 := by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  obtain ⟨s₁, run₁, h4, h5, h6, g₁, k₁⟩ := dataArgs_run hk spf hin hn
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  obtain hk₁ := hk.of_eq k₁.mem k₁.sp k₁.rd k₁.wr
  obtain ai : AbsIn (s₀.gpr .r0) (oSt s₀ wi) (arg s₀ wi) s₀.sp k7 (s₀.gpr .r1) 16 (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (a ++ zeros (padLen a.length)) (arg s₀ 2) (arg s₀ 3).toNat s₁ :=
    ⟨he₁, h4, by rw [h5]; simp, by rw [h6, hx], one_dataOk h hk₁, by rw [k₁.mem]; exact hH⟩
  refine WP.seq (WP.mono (WP.with_rdwr (absorb_ok L (.inr rfl) ai)) fun s₂ hh => ?_)
  obtain ⟨ab, rd₂, wr₂, sp₂⟩ := hh
  rw [k₁.mem] at ab
  obtain hk₂ := hk₁.frame spf (k₁.mem ▸ ab.frame) (disj_sub hA abs_otSub) sp₂ rd₂ wr₂
  obtain ⟨b3, w3⟩ := hk₂.at spf hin 3 (by omega_arith) (show 4 * 3 = 12 from rfl)
  obtain ⟨s₃, run₃, h6₃, g₃, k₃⟩ : ∃ s₃, runBlock isa [.ldrSp .r6 12, .dp .and .r6 .r6 (imm 15)] s₂ = some s₃ ∧
      s₃.gpr .r6 = BitVec.ofNat 32 ((arg s₀ 3).toNat % 16) ∧ (∀ r, r ≠ .r6 → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ := by
    refine ⟨_, by arun [b3, w3], ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, w3, and15]
    · intro r x; simp [gpr_setReg, x]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  obtain he₃ := ab.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide)) k₃.sp k₃.rd k₃.wr
  obtain hk₃ := hk₂.of_eq k₃.mem k₃.sp k₃.rd k₃.wr
  obtain hH₂ : blockAt s₂.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0)) := by
    rw [blockAt_frame ab.frame (ctx_absFrame L (.inr rfl))]; exact hH
  let ct := bytesAt s.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat
  obtain hlx : ((a ++ zeros (padLen a.length)) ++ ct).length % 16 = (arg s₀ 3).toNat % 16 := by
    simp only [List.length_append, Proof.Gcm.length_zeros, ct, length_bytesAt] at hx ⊢; omega_arith
  refine WP.seq (WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl)
    (x := (a ++ zeros (padLen a.length)) ++ ct) (H := ctxH s₀.mem (State.addr (s₀.gpr .r0)))
    ⟨he₃, by rw [k₃.mem]; exact hH₂⟩ (by rw [h6₃, hlx]))) fun s₄ hh => ?_)
  obtain ⟨fl, rd₄, wr₄, sp₄⟩ := hh
  rw [k₃.mem] at fl
  obtain hk₄ := hk₂.frame spf fl.frame (disj_sub hA t_otSub) (sp₄.trans k₃.sp) (rd₄.trans k₃.rd) (wr₄.trans k₃.wr)
  obtain ⟨c1, x1⟩ := hk₄.at spf hin 1 (by omega_arith) (show 4 * 1 = 4 from rfl)
  obtain ⟨c3, x3⟩ := hk₄.at spf hin 3 (by omega_arith) (show 4 * 3 = 12 from rfl)
  obtain ⟨s₅, run₅, h4₅, h5₅, h6₅, h7₅, g₅, k₅⟩ : ∃ s₅, runBlock isa [.ldrSp .r4 4, .mov .r5 (imm 0), .ldrSp .r6 12,
      .mov .r7 (imm 0)] s₄ = some s₅ ∧ s₅.gpr .r4 = arg s₀ 1 ∧ s₅.gpr .r5 = 0 ∧ s₅.gpr .r6 = arg s₀ 3 ∧
      s₅.gpr .r7 = 0 ∧ (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    refine ⟨_, by arun [c1, x1, c3, x3], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, x1]
    · simp [gpr_setReg]
    · simp [gpr_setReg, x3]
    · simp [gpr_setReg]
    · intro r x y z q; simp [gpr_setReg, x, y, z, q]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  obtain he₅ := fl.env.set7 h7₅ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₅ _ (by decide) (by decide) (by decide) (by decide))
    k₅.sp k₅.rd k₅.wr
  obtain hk₅ := hk₄.of_eq k₅.mem k₅.sp k₅.rd k₅.wr
  refine WP.mono (WP.with_rdwr (tag_ok L ho he₅ (show s₀.gpr .r1 = BitVec.ofNat 32 (s₀.gpr .r1).toNat by simp) hR
    (H := ctxH s₀.mem (State.addr (s₀.gpr .r0))) (by rw [k₅.mem]; exact fl.hH) rfl)) fun s₆ hh => ?_
  obtain ⟨tg, rd₆, wr₆, sp₆⟩ := hh
  rw [h4₅, h5₅, h6₅, h7₅, k₅.mem] at tg
  obtain f₄ : Frame (absFrame (oSt s₀ wi) (arg s₀ wi) s₀.sp 16 ++ tFrame (oSt s₀ wi) (arg s₀ wi) s₀.sp 16) s.mem s₄.mem :=
    (ab.frame.mono (fun r hr => List.mem_append_left _ hr)).trans
      ((k₃.mem ▸ fl.frame : Frame _ s₂.mem s₄.mem).mono (fun r hr => List.mem_append_right _ hr))
  refine ⟨⟨_, tg.env⟩, hk₄.frame spf tg.frame (disj_sub hA tag_otSub) (sp₆.trans k₅.sp) (rd₆.trans k₅.rd)
    (wr₆.trans k₅.wr), ?_, ?_⟩
  · rw [tg.out]
    obtain hw := (fl.abs (ab.abs hab)).whole_eq (by
      simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _)
    rw [padded_eq] at hw
    rw [hw, ciph_frame f₄ (disj_sub dC (fun r hr => by
        simp only [List.mem_append] at hr
        rcases hr with hr | hr
        · exact abs_otSub r hr
        · exact t_otSub r hr)) hR,
      blockAt_frame f₄ dJ]
    have z0 : (0 : BitVec 32).toNat = 0 := rfl
    obtain l1 : ((0 : BitVec 32) ++ arg s₀ 1).toNat = a.length := by
      rw [Proof.Gcm.toNat_append, ← hl, z0, Nat.zero_mul, Nat.zero_add]
    obtain l3 : ((0 : BitVec 32) ++ arg s₀ 3).toNat = ct.length := by
      rw [Proof.Gcm.toNat_append, length_bytesAt, z0, Nat.zero_mul, Nat.zero_add]
    rw [l1, l3]
  · refine (f₄.sub fun r hr => ?_).trans (tg.frame.sub tag_otSub)
    simp only [List.mem_append] at hr
    rcases hr with hr | hr
    · exact abs_otSub r hr
    · exact t_otSub r hr

end

end VG.Proof.AesGcm.Arm

end

end

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_seal`

Untrusted: everything here is checked by Lean. `seal` keeps a streaming
state at `W + 16`: `J₀` and the additional data (`oneAad`), the data
encrypted in place (`oneCrypt`), and the tag of the ciphertext into `W`
(`oneTag 0`), copied to `tag` (`tagOut`) (`seal_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph ghashInput fullTag zeros padLen j0 inc32 gctr encryptWith toBytes)
open VG.Proof.Gcm (Absorbed)

section
variable {n wi : Nat}

theorem one_dataW {s₀ s : State} (h : onePre n wi s₀)
    (hw : (⟨State.addr (arg s₀ 2), (arg s₀ 3).toNat⟩ : Region) ∈ s₀.wr) (hk : ArgsKeep n s₀ s) (k7 k8 : BitVec 32) :
    DataW (s₀.gpr .r0) (oSt s₀ wi) (arg s₀ wi) s₀.sp k7 k8 s (arg s₀ 2) (arg s₀ 3).toNat :=
  ⟨one_dataOk h hk, by rw [hk.wr]; exact covers_of_mem hw, h.2.2.1 hw⟩

theorem saved_otFrame {s₀ : State} (h : onePre n wi s₀) {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ otFrame (oSt s₀ wi) (arg s₀ wi) s₀.sp o, (savedR (arg s₀ wi)).Disjoint r := by
  have L := oneLay h
  have hst := oSt_addr h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [hst]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inr (by omega_using [ho])) (by decide) (by omega_using [ho])
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

/-- What `seal`'s pieces leave, from the entry on. -/
theorem seal_mid {s₀ s₁ s₂ s₃ : State} (h : onePre n wi s₀)
    (hw : (⟨State.addr (arg s₀ 2), (arg s₀ 3).toNat⟩ : Region) ∈ s₀.wr) (h1 : SO1 n wi s₀ s₁) (oa : OA n wi s₀ s₁.mem s₂)
    {k7 : BitVec 32} (oc : OC n wi s₀ k7 (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat))) s₂.mem s₃) :
    blockAt s₃.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0)) ∧
    Absorbed s₃.mem (State.addr (oSt s₀ wi) + BitVec.ofNat 64 16) (State.addr (oSt s₀ wi) + BitVec.ofNat 64 32)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat ++
        zeros (padLen (bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat).length)) ∧
    blockAt s₃.mem (State.addr (oSt s₀ wi)) =
      j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat) ∧
    ciphOf s₃.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
      ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat ∧
    bytesAt s₃.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat =
      gctr (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
        (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
          (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat)))
        (bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat) ∧
    SavedAt s₃.mem (arg s₀ wi) s₀ := by
  have L := oneLay h
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hd := one_dataW h hw oa.args 0 0
  have dCr := ctx_crFrame L hd
  have dc₂ : ∀ r ∈ [savedR (arg s₀ wi)] ++ j0Frame (oSt s₀ wi) (arg s₀ wi) s₀.sp,
      (⟨State.addr (s₀.gpr .r0), 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | hr
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.cs
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.kc.symm
  have f₂ : Frame ([savedR (arg s₀ wi)] ++ j0Frame (oSt s₀ wi) (arg s₀ wi) s₀.sp) s₀.mem s₂.mem :=
    (h1.frame.mono fun r hr => List.mem_append_left _ hr).trans (oa.frame.mono fun r hr => List.mem_append_right _ hr)
  have hc₂ := ciph_keep f₂ dc₂ hR
  have hD₂ : bytesAt s₂.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat =
      bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat := by
    have hp := h
    obtain ⟨-, -, -, -, -, -, -, -, dDW, -, -, -, -, -, bD, -⟩ := hp
    exact bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with rfl | hr
      · exact dDW.sub_right (Lay.wSub (by decide))
      · exact one_dataJ0 h dDW bD r hr) (by have := hd.ok.lt; omega_using [])
  have hb := Nat.mod_lt (bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat ++
    zeros (padLen (bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat).length)).length (show 16 > 0 by decide)
  refine ⟨?_, (oa.abs.congr (blockAt_frame oc.frame (stp_crFrame L hd (by decide)))
      (bytesAt_frame oc.frame (stp_crFrame L hd (by omega_using [])) (by omega_using []))), ?_,
    by rw [ciph_frame oc.frame dCr hR, hc₂], by rw [oc.out, hc₂, hD₂],
    (h1.saved.frame oa.frame (saved_j0Frame L)).frame oc.frame (saved_crFrame L hd)⟩
  · rw [blockAt_frame oc.frame (fun r hr => (dCr r hr).sub_left (Lay.ctxSub (by decide)))]; exact oa.hH
  · rw [blockAt_frame oc.frame (by simpa using stp_crFrame L hd (d := 0) (k := 16) (by decide))]; exact oa.j

end

theorem seal_wp [VG.Proof.Gcm.Arm.GhashLaw] {s₀ : State} (h : sealArm.pre s₀) :
    WP isa «seal» s₀ fun s' => abiPreserved s₀ s' ∧ sealArm.post s₀ s' := by
  have h' : onePre 6 5 s₀ := sealPreArm.one h
  have L := oneLay h'
  have fW := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ 6 ∈ s₀.rd := h'.1.2.2.2
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, dT, -, -, tW, -, -, -, -, -, -, -, -, -, -, -, -, fT, -⟩ := h
  have dTW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨State.addr (arg s₀ 4), 16⟩ : Region).Disjoint
      ⟨State.addr (arg s₀ 5) + BitVec.ofNat 64 d, k⟩ := fun hd => tW.sub_right (Lay.wSub hd)
  refine WP.seq (one1_wp (wi := 5) h' (by decide) (by decide) fun s₁ h1 =>
    WP.seq (WP.mono (oneAad_ok h' (by decide) h1) fun s₂ oa => ?_))
  obtain ⟨k7, he₂⟩ := oa.env
  have hw : (⟨State.addr (arg s₀ 2), (arg s₀ 3).toNat⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.seq (WP.mono (oneCrypt_ok h' hw (by decide) he₂ oa.args oa.cb) fun s₃ oc => ?_)
  have he₃ := oc.env
  obtain ⟨hH₃, hab₃, hj₃, hc₃, hD₃, sv₃⟩ := seal_mid h' hw h1 oa oc
  refine WP.seq (WP.mono (oneTag_ok h' (by decide) (o := 0) (.inl rfl) he₃ oc.args hH₃ (length_bytesAt _ _ _).symm hab₃)
    fun s₄ ot => ?_)
  obtain ⟨k7'', he₄⟩ := ot.env
  obtain ⟨i4, v4⟩ := ot.args.at spf hin 4 (by decide) (show 4 * 4 = 16 from rfl)
  obtain ⟨s₅, run₅, hb₅, hf₅, g₅, rd₅, wr₅, sp₅⟩ := tagOut_ok L he₄ i4 v4
    (by rw [ot.args.wr, hwr]; exact covers_of_mem (by simp)) fT (by simpa using dTW (d := 0) (k := 16) (by decide))
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₅ _ (by decide) (by decide)) sp₅ rd₅ wr₅
  have sv₅ := (sv₃.frame ot.frame (saved_otFrame h' (.inl rfl))).frame hf₅ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (dTW (by decide)).symm)
  refine WP.mono (restore_ok he₅.r11 fW (covers_left he₅.perm.w) sv₅ he₅.sp) fun s' hh => ⟨hh.1, ?_⟩
  have hm := hh.2.1
  have hpre := h'
  obtain ⟨-, -, -, -, -, -, -, -, dDW, -, -, -, -, -, bD, -⟩ := hpre
  have hD₄ : bytesAt s₄.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat =
      bytesAt s₃.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat := by
    refine bytesAt_frame ot.frame (fun r hr => ?_) (by omega_using [])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [oSt_addr h']; exact dDW.sub_right (Lay.wSub (by decide))
    · exact dDW.sub_right (Lay.wSub (by decide))
    · exact dDW.sub_right (Lay.wSub (by decide))
    · exact dDW.sub_right (Lay.wSub (by decide))
    · exact bD.symm
  have hD₅ : bytesAt s₅.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat =
      bytesAt s₄.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat :=
    bytesAt_frame hf₅ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dT) (by omega_using [])
  have ho := ot.out
  rw [hc₃, hj₃, add_ofNat_zero, ← Proof.Gcm.fullTag_eq] at ho
  simp only [sealArm, encryptWith, hm, hD₅, hD₄, hD₃, hb₅, ho]
  refine Prod.ext rfl ?_
  exact List.take_of_length_le (by
    rw [Spec.Gcm.fullTag, Proof.Gcm.length_gctr, Cmac.toBytes_length])

end VG.Proof.AesGcm.Arm

end

end

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_open`

Untrusted: everything here is checked by Lean. `open` checks the tag length;
if it is allowed, it computes the tag of the ciphertext into `W + 112`
(`oneAad`, `oneTag 112`), copies the received tag (at `tag`) to `W + 256`, compares
the first `tag_len` bytes of each, and decrypts the data in place only if
they are equal; `r0` is the result (`open_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph ghashInput fullTag zeros padLen j0 inc32 gctr decryptWith openResult toBytes)
open VG.Proof.Gcm (Absorbed)

theorem SO1.keep {n wi : Nat} {s₀ s₁ s₂ : State} (h1 : SO1 n wi s₀ s₁)
    (hg : ∀ r, r ≠ .r0 → r ≠ .r6 → s₂.gpr r = s₁.gpr r) (hk : Keeps s₁ s₂) : SO1 n wi s₀ s₂ :=
  ⟨h1.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hk.sp hk.rd hk.wr,
    by rw [hg _ (by decide) (by decide)]; exact h1.r4, by rw [hg _ (by decide) (by decide)]; exact h1.r5,
    h1.args.of_eq hk.mem hk.sp hk.rd hk.wr, hk.mem ▸ h1.saved, hk.mem ▸ h1.frame⟩

/-! ## The layout of `open` and `open_to` -/

/-- The words of stack arguments, `work` included: 7 in place, 9 out of place. -/
abbrev oNa : Bool → Nat | false => 7 | true => 9
/-- The index of `work`. -/
abbrev oWi : Bool → Nat | false => 6 | true => 8
/-- The index of `tag`. -/
abbrev oTi : Bool → Nat | false => 4 | true => 6
/-- The index of `tag_len`. -/
abbrev oLi : Bool → Nat | false => 5 | true => 7
/-- Where the text is written: `data` in place, `dst` out of place. -/
abbrev oDi : Bool → Nat | false => 2 | true => 4

theorem tagOff_eq (to : Bool) : 4 * oTi to = tagOff to := by cases to <;> rfl
theorem tagLenOff_eq (to : Bool) : 4 * oLi to = tagLenOff to := by cases to <;> rfl
theorem workOff_eq (to : Bool) : 4 * oWi to = workOff to := by cases to <;> rfl
theorem tagOff_lt (to : Bool) : tagOff to < 4096 := by cases to <;> decide
theorem tagLenOff_lt (to : Bool) : tagLenOff to < 4096 := by cases to <;> decide

/-- The destination, apart from everything the code writes but it, and (out
of place) from the source; out of place, the 12 bytes below the stack
pointer that the call of `vg_aes_ctr32_to` pushes are apart from what that
call reads and writes. -/
def DstOk : Bool → State → Prop
  | false, s => (⟨State.addr (arg s 2), (arg s 3).toNat⟩ : Region) ∈ s.wr
  | true, s =>
    let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
    let src : Region := ⟨State.addr (arg s 2), (arg s 3).toNat⟩
    let dst : Region := ⟨State.addr (arg s 4), (arg s 3).toNat⟩
    let work : Region := ⟨State.addr (arg s 8), 2560⟩
    dst ∈ s.wr ∧ ctx.Disjoint dst ∧ src.Disjoint dst ∧ dst.Disjoint work ∧ dst.Disjoint (args s 9) ∧
      (bel s).Disjoint dst ∧ (arg s 4).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧ 12 ≤ s.sp.toNat ∧
      (below12 s.sp).Disjoint ctx ∧ (below12 s.sp).Disjoint src ∧ (below12 s.sp).Disjoint dst ∧
      (below12 s.sp).Disjoint work

/-- What `open` (`to = false`) and `open_to` need: `onePre`, the received tag
readable, apart from `W` and the stack, and the destination. -/
structure OPre (to : Bool) (s₀ : State) : Prop where
  one : onePre (oNa to) (oWi to) s₀
  trd : (⟨State.addr (arg s₀ (oTi to)), (arg s₀ (oLi to)).toNat⟩ : Region) ∈ s₀.rd
  tW : (⟨State.addr (arg s₀ (oTi to)), (arg s₀ (oLi to)).toNat⟩ : Region).Disjoint ⟨State.addr (arg s₀ (oWi to)), 2560⟩
  bT : (bel s₀).Disjoint ⟨State.addr (arg s₀ (oTi to)), (arg s₀ (oLi to)).toNat⟩
  fT : (arg s₀ (oTi to)).toNat + (arg s₀ (oLi to)).toNat ≤ 2 ^ 32
  dst : DstOk to s₀

theorem openPreArm.oPre {s₀ : State} (ho : openPreArm s₀) : OPre false s₀ :=
  have t := openPreArm.tag ho
  ⟨openPreArm.one ho, t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩

/-- What `open` promises, given the result `r0` and the data. -/
def OpenPost (s₀ s : State) : Prop :=
  match openRes s₀ with
  | some pt => s.gpr .r0 = 1 ∧ bytesAt s.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = pt
  | none => s.gpr .r0 = 0 ∧
      bytesAt s.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat

theorem openPost_none {s₀ s : State} (h : openRes s₀ = none) (h0 : s.gpr .r0 = 0)
    (hd : bytesAt s.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat) :
    OpenPost s₀ s := by
  unfold OpenPost; rw [h]; exact ⟨h0, hd⟩

theorem openPost_some {s₀ s : State} {pt : List Byte} (h : openRes s₀ = some pt) (h0 : s.gpr .r0 = 1)
    (hd : bytesAt s.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = pt) : OpenPost s₀ s := by
  unfold OpenPost; rw [h]; exact ⟨h0, hd⟩

/-- Whether the computed tag, cut to the tag length, is the received one. -/
abbrev openTagOk (to : Bool) (s₀ : State) : Prop :=
  (fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat) (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat)
      (bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat)
      (bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat)).take (arg s₀ (oLi to)).toNat =
    bytesAt s₀.mem (State.addr (arg s₀ (oTi to))) (arg s₀ (oLi to)).toNat

/-- After the tags are compared, with the result in `r7` and `Z`. -/
structure OpenMid (to : Bool) (s₀ s : State) : Prop where
  env : Env (s₀.gpr .r0) (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp (s.gpr .r7) (s₀.gpr .r1) s
  args : ArgsKeep (oNa to) s₀ s
  saved : SavedAt s.mem (arg s₀ (oWi to)) s₀
  dat : bytesAt s.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat
  ciph : ciphOf s.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
    ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat
  cb : blockAt s.mem (State.addr (oSt s₀ (oWi to)) + BitVec.ofNat 64 48) =
    inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat))
  r7 : s.gpr .r7 = if openTagOk to s₀ then 1 else 0
  z : s.z = decide (¬ openTagOk to s₀)

/-- `open` up to the comparison of the tags, followed by any `T`. -/
theorem open_head [VG.Proof.Gcm.Arm.GhashLaw] {to : Bool} {s₀ s₂ : State} (ho : OPre to s₀) (h2 : SO1 (oNa to) (oWi to) s₀ s₂)
    (hok : Spec.Gcm.tagLenOk (arg s₀ (oLi to)).toNat = true) {T : Prog isa} {Q : State → Prop}
    (k : ∀ s₈, OpenMid to s₀ s₈ → WP isa T s₈ Q) :
    WP isa (.seq oneAad (.seq (oneTag uO) (.seq (.block [.ldrSp .r6 (tagLenOff to)]) (.seq (recvAt (tagOff to))
      (.seq (cmp uO) (.seq (.block [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)]) T)))))) s₂ Q := by
  have h : onePre (oNa to) (oWi to) s₀ := ho.one
  have tW := ho.tW
  have bT := ho.bT
  have fT := ho.fT
  obtain dTW : ∀ {d k : Nat}, d + k ≤ 2560 →
      (⟨State.addr (arg s₀ (oTi to)), (arg s₀ (oLi to)).toNat⟩ : Region).Disjoint
      ⟨State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 d, k⟩ := fun hd => tW.sub_right (Lay.wSub hd)
  obtain L := oneLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hin : args s₀ (oNa to) ∈ s₀.rd := h.1.2.2.2
  obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
  obtain dW : ∀ {d k : Nat}, d + k ≤ 2560 → (164 ≤ d ∨ d + k ≤ 128) →
      (savedR (arg s₀ (oWi to))).Disjoint ⟨State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ h₂ => Lay.w_w (by omega_using [h₂]) (by decide) h₁
  refine WP.seq (WP.mono (oneAad_ok h (by cases to <;> decide) h2) fun s₃ oa => ?_)
  obtain ⟨k7, he₃⟩ := oa.env
  refine WP.seq (WP.mono (oneTag_ok h (by cases to <;> decide) (o := 112) (.inr rfl) he₃ oa.args oa.hH (length_bytesAt _ _ _).symm
    oa.abs) fun s₄ ot => ?_)
  obtain ⟨k7₄, he₄⟩ := ot.env
  obtain ⟨j5, w5⟩ := ot.args.at spf hin (oLi to) (by cases to <;> decide) (tagLenOff_eq to)
  obtain htl := tagLenOff_lt to
  obtain ⟨s₅, run₅, h6₅, g₅, k₅⟩ : ∃ s₅, runBlock isa [.ldrSp .r6 (tagLenOff to)] s₄ = some s₅ ∧
      s₅.gpr .r6 = BitVec.ofNat 32 (arg s₀ (oLi to)).toNat ∧ (∀ r, r ≠ .r6 → s₅.gpr r = s₄.gpr r) ∧
      Keeps s₄ s₅ := by
    refine ⟨_, by arun [j5, w5, htl], ?_, ?_, ?_⟩
    · simp [gpr_setReg, w5]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  obtain he₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₅ _ (by decide)) k₅.sp k₅.rd k₅.wr
  obtain hk₅ := ot.args.of_eq k₅.mem k₅.sp k₅.rd k₅.wr
  obtain ⟨i4, v4⟩ := hk₅.at spf hin (oTi to) (by cases to <;> decide) (tagOff_eq to)
  refine WP.seq (WP.mono (recvAt_ok L (tagOff_lt to) he₅ i4 v4
    (by rw [hk₅.rd, hk₅.wr]; exact covers_of_mem (List.mem_append_left _ ho.trd)) fT
    (dTW (by decide)) h6₅ t1 t16) fun s₆ hh => ?_)
  obtain ⟨hb₆, hf₆, g₆, rd₆, wr₆, sp₆⟩ := hh
  obtain he₆ := he₅.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₆ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)) sp₆ rd₆ wr₆
  obtain h6₆ : s₆.gpr .r6 = BitVec.ofNat 32 (arg s₀ (oLi to)).toNat := by
    rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), h6₅]
  refine WP.seq (WP.mono (cmp_ok L he₆ (o := 112) (.inr rfl) h6₆ t1 t16) fun s₇ hh => ?_)
  obtain ⟨h0₇, hf₇, g₇, rd₇, wr₇, sp₇⟩ := hh
  obtain he₇ := he₆.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₇ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)) sp₇ rd₇ wr₇
  -- what the pieces leave
  let rs : List Region := [savedR (arg s₀ (oWi to))] ++ j0Frame (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp ++
    otFrame (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp 112 ++
    [⟨State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 256, 16⟩, ⟨State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 240, 16⟩]
  obtain F₇ : Frame rs s₀.mem s₇.mem := by
    have e₂ : Frame [savedR (arg s₀ (oWi to))] s₀.mem s₂.mem := h2.frame
    refine ((((e₂.mono ?_).trans (oa.frame.mono ?_)).trans (ot.frame.mono ?_)).trans
      ((k₅.mem ▸ hf₆ : Frame _ s₄.mem s₆.mem).mono ?_)).trans (hf₇.mono ?_)
    all_goals intro r hr; simp only [rs, List.mem_append]
    · exact .inl (.inl (.inl hr))
    · exact .inl (.inl (.inr hr))
    · exact .inl (.inr hr)
    · simp only [List.mem_singleton] at hr; exact .inr (by simp [hr])
    · simp only [List.mem_singleton] at hr; exact .inr (by simp [hr])
  have hp := h
  obtain ⟨-, -, dcD, dcW, -, -, -, -, dDW, -, -, bc, -, -, bD, bW, -⟩ := hp
  obtain dC : ∀ r ∈ rs, (⟨State.addr (s₀.gpr .r0), 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [rs, List.mem_append] at hr
    rcases hr with ((hr | hr) | hr) | hr
    · simp only [List.mem_singleton] at hr; subst hr; exact L.cw'.sub_right (Lay.wSub (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.cs
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.kc.symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact L.cs.sub_right (Region.sub_prefix (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.kc.symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
  obtain dD : ∀ r ∈ rs, (⟨State.addr (arg s₀ 2), (arg s₀ 3).toNat⟩ : Region).Disjoint r := by
    intro r hr
    simp only [rs, List.mem_append] at hr
    rcases hr with ((hr | hr) | hr) | hr
    · simp only [List.mem_singleton] at hr; subst hr; exact dDW.sub_right (Lay.wSub (by decide))
    · exact one_dataJ0 h dDW bD r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [oSt_addr h]; exact dDW.sub_right (Lay.wSub (by decide))
      · exact dDW.sub_right (Lay.wSub (by decide))
      · exact dDW.sub_right (Lay.wSub (by decide))
      · exact dDW.sub_right (Lay.wSub (by decide))
      · exact bD.symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dDW.sub_right (Lay.wSub (by decide))
      · exact dDW.sub_right (Lay.wSub (by decide))
  let ciph := ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat
  let H := ctxH s₀.mem (State.addr (s₀.gpr .r0))
  let iv := bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat
  let aad := bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat
  let dat := bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat
  let tl := (arg s₀ (oLi to)).toNat
  let tag₀ := bytesAt s₀.mem (State.addr (arg s₀ (oTi to))) tl
  obtain F₃ : Frame ([savedR (arg s₀ (oWi to))] ++ j0Frame (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp) s₀.mem s₃.mem :=
    (h2.frame.mono fun r hr => List.mem_append_left _ hr).trans (oa.frame.mono fun r hr => List.mem_append_right _ hr)
  obtain sub₃ : ∀ r ∈ [savedR (arg s₀ (oWi to))] ++ j0Frame (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp, r ∈ rs := fun r hr => by
    simp only [rs, List.mem_append] at hr ⊢; exact .inl (.inl hr)
  obtain hD₃ : bytesAt s₃.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = dat :=
    bytesAt_frame F₃ (fun r hr => dD r (sub₃ r hr)) (by omega_using [])
  obtain hT₄ : bytesAt s₄.mem (State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 112) 16 = fullTag ciph H iv aad dat := by
    rw [ot.out, hD₃, ciph_keep F₃ (fun r hr => dC r (sub₃ r hr)) hR, oa.j, ← Proof.Gcm.fullTag_eq]
  obtain F₄ : Frame ([savedR (arg s₀ (oWi to))] ++ j0Frame (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp ++ otFrame (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp 112)
      s₀.mem s₄.mem :=
    (F₃.mono fun r hr => List.mem_append_left _ hr).trans (ot.frame.mono fun r hr => List.mem_append_right _ hr)
  obtain hR₀ : bytesAt s₄.mem (State.addr (arg s₀ (oTi to))) tl = tag₀ := by
    refine bytesAt_frame F₄ (fun r hr => ?_) (by omega_using [])
    obtain hst := oSt_addr h
    obtain z : ∀ {d k : Nat}, d + k ≤ 2560 → 16 ≤ d →
        (⟨State.addr (arg s₀ (oTi to)), tl⟩ : Region).Disjoint ⟨State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 d, k⟩ :=
      fun h₁ _ => dTW h₁
    simp only [List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · simp only [List.mem_singleton] at hr; subst hr; exact z (by decide) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [hst]; exact z (by decide) (by decide)
      · exact z (by decide) (by decide)
      · exact z (by decide) (by decide)
      · exact bT.symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [hst]; exact z (by decide) (by decide)
      · exact z (by decide) (by decide)
      · exact z (by decide) (by decide)
      · exact z (by decide) (by decide)
      · exact bT.symm
  obtain hX : (bytesAt s₆.mem (State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 112) tl ++ zeros (16 - tl) =
      bytesAt s₆.mem (State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 256) 16) ↔ (fullTag ciph H iv aad dat).take tl = tag₀ := by
    rw [hb₆, k₅.mem, hR₀, bytesAt_frame hf₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega)) (by omega) (by decide))
        (by omega_using []), k₅.mem, bytesAt_take _ _ t16, hT₄, List.append_cancel_right_eq]
  let X : Prop := bytesAt s₆.mem (State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 112) tl ++ zeros (16 - tl) =
      bytesAt s₆.mem (State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 256) 16
  obtain ⟨s₈, run₈, h7₈, hz₈, g₈, k₈⟩ : ∃ s₈, runBlock isa [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)] s₇ = some s₈ ∧
      s₈.gpr .r7 = s₇.gpr .r0 ∧ s₈.z = decide ((s₇.gpr .r0).toNat = 0) ∧ (∀ r, r ≠ .r7 → s₈.gpr r = s₇.gpr r) ∧
      Keeps s₇ s₈ := by
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · simp only [z_subFlags, gpr_setReg, reduceCtorEq, ite_false]; exact z_sub0 _
    · intro r hr; simp only [gpr_subFlags, gpr_setReg, hr, ite_false]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₈, run₈, ?_⟩)
  obtain he₈ := he₇.set7 h7₈ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₈ _ (by decide)) k₈.sp k₈.rd k₈.wr
  obtain dA6 : ∀ {d : Nat}, d + 16 ≤ 2560 → ∀ r ∈ [(⟨State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 d, 16⟩ : Region)],
      (args s₀ (oNa to)).Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (h.2.2.2.2.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
  obtain hk₈ : ArgsKeep (oNa to) s₀ s₈ :=
    ((((ot.args.of_eq k₅.mem k₅.sp k₅.rd k₅.wr).frame spf hf₆ (dA6 (by decide)) sp₆ rd₆ wr₆).frame spf hf₇
      (dA6 (by decide)) sp₇ rd₇ wr₇).of_eq k₈.mem k₈.sp k₈.rd k₈.wr)
  obtain F₈ : Frame rs s₀.mem s₈.mem := by rw [k₈.mem]; exact F₇
  obtain hdat₈ : bytesAt s₈.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = dat := bytesAt_frame F₈ dD (by omega_using [])
  obtain hc₈ : ciphOf s₈.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat = ciph := ciph_keep F₈ dC hR
  obtain hcb₈ : blockAt s₈.mem (State.addr (oSt s₀ (oWi to)) + BitVec.ofNat 64 48) = inc32 (j0 H iv) := by
    obtain F₃₈ : Frame (otFrame (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp 112 ++
        [⟨State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 256, 16⟩, ⟨State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 240, 16⟩])
        s₃.mem s₈.mem := by
      rw [k₈.mem]
      refine ((ot.frame.mono fun r hr => List.mem_append_left _ hr).trans
        ((k₅.mem ▸ hf₆ : Frame _ s₄.mem s₆.mem).mono fun r hr => ?_)).trans (hf₇.mono fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; simp [hr]
      · simp only [List.mem_singleton] at hr; simp [hr]
    rw [blockAt_frame F₃₈ (fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
      · have := Lay.st_st (st := oSt s₀ (oWi to)) (a := 48) (n := 16) (d := 0) (k := 48) (.inr (by decide)) (by decide)
          (by decide)
        rwa [add_ofNat_zero] at this
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact (L.stk_st (by decide)).symm
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩))]
    exact oa.cb
  obtain F₂₈ : Frame (j0Frame (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp ++ otFrame (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp 112 ++
      [⟨State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 256, 16⟩, ⟨State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 240, 16⟩])
      s₂.mem s₈.mem := by
    rw [k₈.mem]
    refine (((oa.frame.mono ?_).trans (ot.frame.mono ?_)).trans
      ((k₅.mem ▸ hf₆ : Frame _ s₄.mem s₆.mem).mono ?_)).trans (hf₇.mono ?_)
    all_goals intro r hr; simp only [List.mem_append]
    · exact .inl (.inl hr)
    · exact .inl (.inr hr)
    · simp only [List.mem_singleton] at hr; exact .inr (by simp [hr])
    · simp only [List.mem_singleton] at hr; exact .inr (by simp [hr])
  obtain sv₈ : SavedAt s₈.mem (arg s₀ (oWi to)) s₀ := by
    refine h2.saved.frame F₂₈ fun r hr => ?_
    simp only [List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact saved_j0Frame L r hr
    · exact saved_otFrame h (.inr rfl) r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dW (by decide) (.inl (by decide))
      · exact dW (by decide) (.inl (by decide))
  obtain hX0 : (s₇.gpr .r0).toNat = 0 ↔ ¬X := by
    rw [h0₇]
    split
    · next hx => exact ⟨fun e => absurd e (by decide), fun e => absurd hx e⟩
    · next hx => exact ⟨fun _ => hx, fun _ => rfl⟩
  refine k s₈ ⟨by rw [h7₈]; exact he₈, hk₈, sv₈, hdat₈, hc₈, hcb₈, ?_, ?_⟩
  · rw [h7₈, h0₇]; exact ite_congr (propext hX) (fun _ => rfl) (fun _ => rfl)
  · rw [hz₈]; exact decide_eq_decide.mpr (hX0.trans (not_congr hX))

/-! ## Out of place -/

theorem below12_args (s : State) {n : Nat} (hf : s.sp.toNat + 4 * n ≤ 2 ^ 32) (h12 : 12 ≤ s.sp.toNat) :
    (below12 s.sp).Disjoint (args s n) := by
  simp only [args, argAddr_zero]
  exact (VG.Offset.base_disjoint_below (State.addr s.sp) (n := 12) (k := 4 * n) (by omega)).symm

theorem dataArgsTo_run {s₀ s : State} (hk : ArgsKeep 9 s₀ s) (hf : s₀.sp.toNat + 4 * 9 ≤ 2 ^ 32)
    (hin : args s₀ 9 ∈ s₀.rd) :
    ∃ s', runBlock isa dataArgsTo s = some s' ∧ s'.gpr .r4 = arg s₀ 2 ∧ s'.gpr .r5 = arg s₀ 3 ∧
      s'.gpr .r6 = arg s₀ 4 ∧ (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain ⟨a2, v2⟩ := hk.at hf hin 2 (by decide) (show 4 * 2 = 8 from rfl)
  obtain ⟨a3, v3⟩ := hk.at hf hin 3 (by decide) (show 4 * 3 = 12 from rfl)
  obtain ⟨a4, v4⟩ := hk.at hf hin 4 (by decide) (show 4 * 4 = 16 from rfl)
  refine ⟨_, by simp only [dataArgsTo]; arun [a2, v2, a3, v3, a4, v4], ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, v2]
  · simp [gpr_setReg, v3]
  · simp [gpr_setReg, v4]
  · intro r x y z; simp [gpr_setReg, x, y, z]
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- After `oneCryptG true`, from `m₀`. -/
structure OCTo (s₀ : State) (k7 : BitVec 32) (icb : Block) (m₀ : Mem) (s : State) : Prop where
  env : Env (s₀.gpr .r0) (oSt s₀ (oWi true)) (arg s₀ (oWi true)) s₀.sp k7 (s₀.gpr .r1) s
  args : ArgsKeep (oNa true) s₀ s
  out : bytesAt s.mem (State.addr (arg s₀ 4)) (arg s₀ 3).toNat =
    gctr (ciphOf m₀ (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat) icb (bytesAt m₀ (State.addr (arg s₀ 2)) (arg s₀ 3).toNat)
  frame : Frame (crFrameG true (oSt s₀ (oWi true)) (arg s₀ (oWi true)) s₀.sp (arg s₀ 4) (arg s₀ 3).toNat) m₀ s.mem

/-- After `dataArgsTo`, with the public values named: `cryptTo` runs from
the first counter block, keeping the stack arguments. -/
theorem cryptTo_in {s₀ s₁ : State} (ho : OPre true s₀) {c st w sp k7 k8 S T : BitVec 32} {R n : Nat}
    (ec : s₀.gpr .r0 = c) (ew : arg s₀ (oWi true) = w) (est : oSt s₀ (oWi true) = st) (esp : s₀.sp = sp)
    (ek : s₀.gpr .r1 = k8) (eR : (s₀.gpr .r1).toNat = R) (eS : arg s₀ 2 = S) (eT : arg s₀ 4 = T)
    (en : (arg s₀ 3).toNat = n) (he : Env c st w sp k7 k8 s₁) (hk : ArgsKeep (oNa true) s₀ s₁)
    (h4 : s₁.gpr .r4 = S) (h5 : s₁.gpr .r5 = BitVec.ofNat 32 n) (h6 : s₁.gpr .r6 = T) (icb : Block) :
    CrMidG true c st w sp k7 k8 R icb 0 S T n s₁.mem 0 s₁ ∧
      WP isa cryptTo s₁ fun s₂ => CrOutG true c st w sp k7 k8 R icb 0 S T n s₁.mem s₂ ∧
        ArgsKeep (oNa true) s₀ s₂ := by
  subst ec ew est esp ek eR eS eT en
  have h := ho.one
  obtain L := oneLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have dWA := h.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨dw, cD, sD, dW, dA, bD, fD, sp12, b12c, b12s, b12d, b12w⟩ := ho.dst
  obtain hst := oSt_addr h
  obtain dok : DataOk (oSt s₀ (oWi true)) (arg s₀ (oWi true)) s₀.sp s₁ (arg s₀ 4) (arg s₀ 3).toNat :=
    ⟨by rw [hk.rd, hk.wr]; exact covers_left (covers_of_mem dw), (arg s₀ 3).isLt, fD, oSt_disj h dW, dW, bD⟩
  obtain ci : CrMidG true (s₀.gpr .r0) (oSt s₀ (oWi true)) (arg s₀ (oWi true)) s₀.sp k7 (s₀.gpr .r1)
      (s₀.gpr .r1).toNat icb 0 (arg s₀ 2) (arg s₀ 4) (arg s₀ 3).toNat s₁.mem 0 s₁ :=
    ⟨he, Nat.zero_le _, by rw [h4, add_ofNat_zero], by rw [h5, Nat.sub_zero], by rw [he.r8]; simp, hR,
      ⟨dok, by rw [hk.wr]; exact covers_of_mem dw, cD⟩, fun hc₀ => by simpa using hc₀,
      fun _ => by simp [bytesAt]; rfl, by rw [add_ofNat_zero], .inr (by decide), Frame.refl _ _,
      fun _ => by rw [h6, add_ofNat_zero], one_dataOk h hk,
      ⟨sD, sp12, b12c, by rw [hst]; exact b12w.sub_right (Lay.wSub (by decide)), b12w, b12s, b12d⟩⟩
  refine ⟨ci, WP.mono (WP.with_rdwr (cryptTo_ok L ci)) fun s₂ hh => ?_⟩
  obtain ⟨co, rd₂, wr₂, sp₂⟩ := hh
  obtain hA : ∀ r ∈ crFrameG true (oSt s₀ (oWi true)) (arg s₀ (oWi true)) s₀.sp (arg s₀ 4) (arg s₀ 3).toNat,
      (args s₀ (oNa true)).Disjoint r := by
    intro r hr
    simp only [crFrameG, crFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl) | rfl
    · exact dA.symm
    · rw [hst, add_ofNat_assoc]; exact (dWA.sub_left (Lay.wSub (by decide))).symm
    · exact (dWA.sub_left (Lay.wSub (by decide))).symm
    · exact (below_args s₀ spf).symm
    · exact (below12_args s₀ spf sp12).symm
  exact ⟨co, hk.frame spf co.frame hA sp₂ rd₂ wr₂⟩

/-- The source decrypted to the destination, from the first counter block. -/
theorem oneCryptTo_ok {s₀ s : State} (ho : OPre true s₀) {k7 : BitVec 32}
    (he : Env (s₀.gpr .r0) (oSt s₀ (oWi true)) (arg s₀ (oWi true)) s₀.sp k7 (s₀.gpr .r1) s)
    (hk : ArgsKeep (oNa true) s₀ s) {icb : Block}
    (hcb : blockAt s.mem (State.addr (oSt s₀ (oWi true)) + BitVec.ofNat 64 48) = icb) :
    WP isa (oneCryptG true) s (OCTo s₀ k7 icb s.mem) := by
  have spf := ho.one.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ (oNa true) ∈ s₀.rd := ho.one.1.2.2.2
  obtain ⟨s₁, run₁, h4, h5, h6, g₁, k₁⟩ := dataArgsTo_run hk spf hin
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  obtain hk₁ := hk.of_eq k₁.mem k₁.sp k₁.rd k₁.wr
  refine WP.mono (cryptTo_in ho rfl rfl rfl rfl rfl rfl rfl rfl rfl he₁ hk₁ h4 (by rw [h5]; simp) h6 icb).2
    fun s₂ ⟨co, hk₂⟩ => ?_
  rw [k₁.mem] at co
  obtain c0 := Proof.Gcm.ctr_zero s.mem _ (State.addr (oSt s₀ (oWi true)) + BitVec.ofNat 64 64)
    (ciphOf s.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat) hcb
  exact ⟨co.env, hk₂, by rw [co.out c0, Proof.Gcm.gctr_eq], co.frame⟩

/-! ## The body -/

/-- What `vg_aes_gcm_open` and `vg_aes_gcm_open_to` compute. -/
abbrev openResG (to : Bool) (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) (ctxH s.mem (State.addr (s.gpr .r0)))
    (arg s (oLi to)).toNat (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
    (bytesAt s.mem (State.addr (arg s 2)) (arg s 3).toNat) (bytesAt s.mem (State.addr (arg s 0)) (arg s 1).toNat)
    (bytesAt s.mem (State.addr (arg s (oTi to))) (arg s (oLi to)).toNat)

/-- What the body leaves: the result in `r0` and the text at the destination
if it is 1; in place, the data as it was if it is 0 (out of place, the
destination is wiped after). -/
def OpenPostG (to : Bool) (s₀ s : State) : Prop :=
  match openResG to s₀ with
  | some pt => s.gpr .r0 = 1 ∧ bytesAt s.mem (State.addr (arg s₀ (oDi to))) (arg s₀ 3).toNat = pt
  | none => s.gpr .r0 = 0 ∧ (to = false →
      bytesAt s.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat)

/-- The code of the body once the tag length is known to be allowed. -/
abbrev openGood (to : Bool) : Prog isa :=
  .seq oneAad (.seq (oneTag uO) (.seq (.block [.ldrSp .r6 (tagLenOff to)]) (.seq (recvAt (tagOff to))
    (.seq (cmp uO) (.seq (.block [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)]) (.seq (.ite .eq (.block []) (oneCryptG to))
      (.block [.mov .r0 (.reg .r7)])))))))

/-- What the body leaves, from `s₀`. -/
structure OB (to : Bool) (s₀ s : State) : Prop where
  env : ∃ k7, Env (s₀.gpr .r0) (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp k7 (s₀.gpr .r1) s
  saved : SavedAt s.mem (arg s₀ (oWi to)) s₀
  args : ArgsKeep (oNa to) s₀ s
  post : OpenPostG to s₀ s

theorem open_good [VG.Proof.Gcm.Arm.GhashLaw] {to : Bool} {s₀ s₂ : State} (ho : OPre to s₀) (h2 : SO1 (oNa to) (oWi to) s₀ s₂)
    (hok : Spec.Gcm.tagLenOk (arg s₀ (oLi to)).toNat = true) : WP isa (openGood to) s₂ (OB to s₀) := by
  have h := ho.one
  obtain L := oneLay h
  refine open_head ho h2 hok fun s₈ om => ?_
  let pt := gctr (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
    (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat)))
    (bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat)
  -- the data decrypted only if the tags are equal
  obtain mid : WP isa (.ite .eq (.block []) (oneCryptG to)) s₈ fun s₉ =>
      Env (s₀.gpr .r0) (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp (s₈.gpr .r7) (s₀.gpr .r1) s₉ ∧
      SavedAt s₉.mem (arg s₀ (oWi to)) s₀ ∧ ArgsKeep (oNa to) s₀ s₉ ∧
      (openTagOk to s₀ → bytesAt s₉.mem (State.addr (arg s₀ (oDi to))) (arg s₀ 3).toNat = pt) ∧
      (¬openTagOk to s₀ → to = false → bytesAt s₉.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat =
        bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat) := by
    refine WP.ite _ (eval_eq' om.z) (fun ht => ?_) (fun hf => ?_)
    · have hx : ¬openTagOk to s₀ := of_decide_eq_true ht
      exact WP.block_nil ⟨om.env, om.saved, om.args, fun x => absurd x hx, fun _ _ => om.dat⟩
    · have hx : openTagOk to s₀ := Classical.not_not.mp (of_decide_eq_false hf)
      cases to
      · have hw : (⟨State.addr (arg s₀ 2), (arg s₀ 3).toNat⟩ : Region) ∈ s₀.wr := ho.dst
        refine WP.mono (oneCrypt_ok h hw (by decide) om.env om.args om.cb) fun s₉ oc => ?_
        exact ⟨oc.env, om.saved.frame oc.frame (saved_crFrame L (one_dataW h hw om.args 0 0)), oc.args,
          fun _ => by show bytesAt s₉.mem (State.addr (arg s₀ 2)) _ = _; rw [oc.out, om.ciph, om.dat],
          fun x => absurd hx x⟩
      · refine WP.mono (oneCryptTo_ok ho om.env om.args om.cb) fun s₉ oc => ?_
        obtain ⟨dw, cD, sD, dW, dA, bD, fD, sp12, b12c, b12s, b12d, b12w⟩ := ho.dst
        obtain sv : ∀ r ∈ crFrameG true (oSt s₀ (oWi true)) (arg s₀ (oWi true)) s₀.sp (arg s₀ 4) (arg s₀ 3).toNat,
            (savedR (arg s₀ (oWi true))).Disjoint r := by
          intro r hr
          simp only [crFrameG, List.mem_append, List.mem_singleton] at hr
          rcases hr with hr | rfl
          · exact saved_crFrame L (c := s₀.gpr .r0) (k7 := 0) (k8 := 0) (s := s₉)
              ⟨⟨covers_left (covers_of_mem (by rw [oc.args.wr]; exact dw)), (arg s₀ 3).isLt, fD, oSt_disj h dW, dW,
                bD⟩, covers_of_mem (by rw [oc.args.wr]; exact dw), cD⟩ r hr
          · exact (b12w.sub_right (Lay.wSub (by decide))).symm
        exact ⟨oc.env, om.saved.frame oc.frame sv, oc.args,
          fun _ => by show bytesAt s₉.mem (State.addr (arg s₀ 4)) _ = _; rw [oc.out, om.ciph, om.dat],
          fun _ h => nomatch h⟩
  refine WP.seq (WP.mono mid fun s₉ hh => ?_)
  obtain ⟨he₉, sv₉, hk₉, hd₁, hd₂⟩ := hh
  refine WP.of_runBlock ⟨s₉.setReg .r0 (s₉.gpr .r7), by arun [], ⟨⟨_, he₉.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl) rfl rfl rfl⟩, sv₉, hk₉.of_eq rfl rfl rfl rfl, ?_⟩⟩
  obtain hres : openResG to s₀ = if openTagOk to s₀ then some pt else none := by
    simp only [openResG, openResult, hok, ite_true, decryptWith]; rfl
  obtain r0 : (s₉.setReg .r0 (s₉.gpr .r7)).gpr .r0 = if openTagOk to s₀ then 1 else 0 := by
    rw [gpr_setReg_self, he₉.r7, om.r7]
  unfold OpenPostG
  by_cases e : openTagOk to s₀
  · rw [hres, ite_eq_left_iff.mpr (fun h => absurd e h)]
    exact ⟨r0.trans (ite_eq_left_iff.mpr (fun h => absurd e h)), hd₁ e⟩
  · rw [hres, ite_eq_right_iff.mpr (fun h => absurd h e)]
    exact ⟨r0.trans (ite_eq_right_iff.mpr (fun h => absurd h e)), hd₂ e⟩

/-- The branch on the tag length. -/
theorem openMid_wp [VG.Proof.Gcm.Arm.GhashLaw] {to : Bool} {s₀ s₃ : State} (ho : OPre to s₀) (h3 : SO1 (oNa to) (oWi to) s₀ s₃)
    (hz₃ : s₃.z = !Spec.Gcm.tagLenOk (arg s₀ (oLi to)).toNat) :
    WP isa (.ite .eq (.block [.mov .r0 (imm 0)]) (openGood to)) s₃ (OB to s₀) := by
  have h' := ho.one
  refine WP.ite _ (eval_eq' hz₃) (fun ht => ?_) (fun hf => open_good ho h3 (by simpa using hf))
  obtain hbad : Spec.Gcm.tagLenOk (arg s₀ (oLi to)).toNat = false := by simpa using ht
  refine WP.of_runBlock ⟨s₃.setReg .r0 (BitVec.ofNat 32 0), by arun [], ⟨_, h3.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl) rfl rfl rfl⟩, h3.saved, h3.args.of_eq rfl rfl rfl rfl, ?_⟩
  unfold OpenPostG
  rw [show openResG to s₀ = none by simp only [openResG, openResult, hbad]; rfl]
  refine ⟨by simp [gpr_setReg], fun _ => ?_⟩
  show bytesAt s₃.mem _ _ = _
  exact bytesAt_frame h3.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h'.2.2.2.2.2.2.2.2.1.sub_right (Lay.wSub (by decide))) (by omega_using [])

/-- The entry, with the tag length in `r6`. -/
theorem openEntry_wp {to : Bool} {s₀ : State} (h : onePre (oNa to) (oWi to) s₀) :
    WP isa (.block (oneEntry (workOff to) ++ ([.ldrSp .r6 (tagLenOff to)] : List Instr))) s₀ fun s =>
      SO1 (oNa to) (oWi to) s₀ s ∧ s.gpr .r6 = BitVec.ofNat 32 (arg s₀ (oLi to)).toNat := by
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ (oNa to) ∈ s₀.rd := h.1.2.2.2
  rw [← workOff_eq to]
  refine WP.block_append (one1_wp h (by cases to <;> decide) (by cases to <;> decide) fun s₁ h1 => ?_)
  obtain ⟨i5, v5⟩ := h1.args.at spf hin (oLi to) (by cases to <;> decide) (tagLenOff_eq to)
  obtain htl := tagLenOff_lt to
  refine WP.of_runBlock ⟨_, by arun [i5, v5, htl], ?_⟩
  exact ⟨h1.keep (fun r _ b => by simp [gpr_setReg, b]) ⟨rfl, rfl, rfl, rfl⟩, by simp [gpr_setReg, v5]⟩

/-- The body of `open` (`to = false`) and `open_to`, up to their ends. -/
theorem openBody_wp [VG.Proof.Gcm.Arm.GhashLaw] {to : Bool} {s₀ : State} (ho : OPre to s₀) {Q : State → Prop}
    (k : ∀ s, OB to s₀ s → WP isa (openEnd to) s Q) : WP isa (openG to) s₀ Q := by
  have h' := ho.one
  obtain L := oneLay h'
  have spf := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ (oNa to) ∈ s₀.rd := h'.1.2.2.2
  unfold openG
  rw [← workOff_eq to]
  refine WP.seq (WP.block_append (one1_wp (wi := oWi to) h' (by cases to <;> decide) (by cases to <;> decide)
    fun s₁ h1 => ?_))
  obtain ⟨i5, v5⟩ := h1.args.at spf hin (oLi to) (by cases to <;> decide) (tagLenOff_eq to)
  obtain htl := tagLenOff_lt to
  obtain ⟨s₂, run₂, h6₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [.ldrSp .r6 (tagLenOff to)] s₁ = some s₂ ∧
      s₂.gpr .r6 = BitVec.ofNat 32 (arg s₀ (oLi to)).toNat ∧ (∀ r, r ≠ .r6 → s₂.gpr r = s₁.gpr r) ∧
      Keeps s₁ s₂ := by
    refine ⟨_, by arun [i5, v5, htl], ?_, ?_, ?_⟩
    · simp [gpr_setReg, v5]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  refine WP.seq (WP.mono (tagLenOk_ok h6₂ (arg s₀ (oLi to)).isLt) fun s₃ ⟨hz₃, g₃, k₃⟩ => ?_)
  obtain h3 : SO1 (oNa to) (oWi to) s₀ s₃ := (h1.keep (fun r a b => g₂ r b) k₂).keep (fun r a b => g₃ r a) k₃
  exact WP.seq (WP.mono (openMid_wp ho h3 hz₃) k)

theorem open_wp [VG.Proof.Gcm.Arm.GhashLaw] {s₀ : State} (h : openArm.pre s₀) :
    WP isa «open» s₀ fun s' => abiPreserved s₀ s' ∧ openArm.post s₀ s' := by
  obtain ho := openPreArm.oPre h
  have h' := ho.one
  have fW := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine openBody_wp ho fun s₄ ob => ?_
  obtain ⟨⟨k7, he⟩, sv, -, op⟩ := ob
  refine WP.mono (restore_ok he.r11 fW (covers_left he.perm.w) sv he.sp) fun s' hh => ⟨hh.1, ?_⟩
  show match openRes s₀ with
    | some pt => s'.gpr .r0 = 1 ∧ bytesAt s'.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = pt
    | none => s'.gpr .r0 = 0 ∧
        bytesAt s'.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat
  unfold OpenPostG at op
  rw [hh.2.1, hh.2.2.1]
  show match openResG false s₀ with
    | some pt => _ | none => _
  split
  · next pt e => rw [e] at op; exact op
  · next e => rw [e] at op; exact ⟨op.1, op.2 rfl⟩

end VG.Proof.AesGcm.Arm

end

end

/-!
# AES-GCM on ARMv7: `ghash1`, `absorb`, `flush` and `lens` are constant time

Untrusted: everything here is checked by Lean. The invariants fix the
context, the state, `W`, the stack pointer, the data's address and length and
the number of bytes absorbed so far modulo 16, and leave the rest
existential.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

theorem Env.pin {c st w sp a b a' b' : BitVec 32} {s₁ s₂ : State} (h₁ : Env c st w sp a b s₁)
    (h₂ : Env c st w sp a' b' s₂) {r : Reg} (hr : r = .r9 ∨ r = .r10 ∨ r = .r11) : s₁.gpr r = s₂.gpr r := by
  rcases hr with rfl | rfl | rfl
  · rw [h₁.r9, h₂.r9]
  · rw [h₁.r10, h₂.r10]
  · rw [h₁.r11, h₂.r11]

/-- Before `ghash1 yo b o`, for the block at `P`. -/
structure GhIn (c st w sp : BitVec 32) (b : Reg) (o : Nat) (P : BitVec 32) (s : State) : Prop where
  env : ∃ k7 k8, Env c st w sp k7 k8 s
  hP : s.gpr b + BitVec.ofNat 32 o = P
  hpr : Covers [⟨State.addr P, 16⟩] (s.rd ++ s.wr)

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp)
include L

theorem ghash1_ct [VG.Proof.Gcm.Arm.GhashLaw] {yo : Nat} (hyo : yo = 0 ∨ yo = 16) {b : Reg} {o : Nat}
    (hbo : (b = .r10 ∧ o = 32) ∨ (b = .r11 ∧ o = 96)) {P : BitVec 32} (hfit : P.toNat + 16 ≤ 2 ^ 32)
    (hpy : (⟨State.addr st + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨State.addr P, 16⟩)
    (hpw : (⟨State.addr P, 16⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 512, 256⟩)
    (hpk : (below sp).Disjoint ⟨State.addr P, 16⟩) :
    CT (GhIn c st w sp b o P) (ghash1 yo b o) := by
  have hb : b = .r10 ∨ b = .r11 := by rcases hbo with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have he : encodable (BitVec.ofNat 32 o) = true := by rcases hbo with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  have hey : encodable (BitVec.ofNat 32 yo) = true := by rcases hyo with rfl | rfl <;> decide
  let J : State → Prop := fun s => GhCall s (c + BitVec.ofNat 32 240) (st + BitVec.ofNat 32 yo) P
    (w + BitVec.ofNat 32 512) 1 ∧ s.sp = sp
  refine CT.seq (J := J) ?_ (fun s ⟨⟨k7, k8, hs⟩, hP, hpr⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r9, .r10, .r11])
        (.block [addI .r0 .r9 240, addI .r1 .r10 yo, addI .r2 b o, .mov .r3 (imm 1), addI .r12 .r11 scrO]) h).isSome =
        true := by
      rcases hyo with rfl | rfl <;> rcases hbo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨_, by taint_decide⟩
    exact CT.taint [.r9, .r10, .r11] (fun s₁ s₂ ⟨⟨_, _, h₁⟩, _, _⟩ ⟨⟨_, _, h₂⟩, _, _⟩ r hr => h₁.pin h₂ (by simpa using hr))
      hc
  · obtain ⟨s₁, run₁, h0, h1, h2, h3, h12, hkeep, hk⟩ := ghArgs_ok hs yo b o hb hey he
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    have he₁ : Env c st w sp k7 k8 s₁ := hs.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hkeep _ (by decide) (by decide) (by decide) (by decide)
        (by decide)) hk.sp hk.rd hk.wr
    exact ⟨ghCall_mk L hyo he₁ h0 h1 (by rw [h2, hP]) h3 h12 (by omega_arith) (by simpa using hpy) (by simpa using hpw)
      (by simpa using hpk) (by rw [hk.rd, hk.wr]; simpa using hpr), he₁.sp⟩
  · exact CT.gh fun s₁ s₂ h₁ h₂ => ⟨_, _, _, _, _, h₁.1, h₂.1, h₁.2.trans h₂.2.symm⟩

end

/-- Before `absorb yo`: `q` bytes in the buffer. -/
def AbsI (c st w sp : BitVec 32) (yo : Nat) (D : BitVec 32) (n q : Nat) (s : State) : Prop :=
  ∃ k7 k8 H x, x.length % 16 = q ∧ AbsIn c st w sp k7 k8 yo H x D n s

/-- Part of the way, `j` bytes absorbed. -/
def MidI (c st w sp : BitVec 32) (yo : Nat) (D : BitVec 32) (n q j : Nat) (s : State) : Prop :=
  ∃ k7 k8 H x m₀, x.length % 16 = q ∧ AbsMid c st w sp k7 k8 yo H x D n m₀ j s

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

theorem absorbHead_ct [VG.Proof.Gcm.Arm.GhashLaw] {D : BitVec 32} {n q : Nat} (hn : n ≠ 0) (hq : q ≠ 0) :
    CT (AbsI c st w sp yo D n q) (absorbHead yo) := by
  let J : State → Prop := fun s => ∃ k7 k8 H x m₀ k, x.length % 16 = q ∧ HeadMid c st w sp k7 k8 yo H x D n m₀ k s
  refine CT.seq (J := J) ?_ (fun s ⟨k7, k8, H, x, hx, hs⟩ => WP.mono (headPre_ok L hyo hs hn (by omega_arith))
    fun s' ⟨k, hm⟩ => ⟨k7, k8, H, x, s.mem, k, hx, hm⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5, .r6, .r10]) headPre h).isSome =
        true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, x₁, hx₁, h₁⟩ ⟨_, _, _, x₂, hx₂, h₂⟩ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.r4, h₂.r4]
    · rw [h₁.r5, h₂.r5]
    · rw [h₁.r6, h₂.r6, hx₁, hx₂]
    · exact h₁.env.pin h₂.env (by simp)
  · refine CT.ite (decide (q + min (16 - q) n = 16)) (fun s ⟨_, _, _, _, _, _, hx, hm⟩ => by
      rw [hm.z, hm.kmin, hx]) (fun _ => ?_) (fun _ => CT.skip)
    have eB := L.stA (d := 32) (by decide)
    have hf : (st + BitVec.ofNat 32 32).toNat + 16 ≤ 2 ^ 32 := by rw [L.stN (by decide)]; have := L.sw; omega_arith
    refine (ghash1_ct L hyo (.inl ⟨rfl, rfl⟩) (P := st + BitVec.ofNat 32 32) hf ?_ ?_ ?_).mono
      fun s ⟨k7, k8, _, _, _, _, _, hm⟩ => ⟨⟨k7, k8, hm.env⟩, by rw [hm.env.r10], ?_⟩
    · rw [eB]; exact Lay.st_st (.inl (by omega_arith)) (by omega_arith) (by decide)
    · rw [eB]; exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
    · rw [eB]; exact L.stk_st (by decide)
    · rw [eB]; exact covers_left (hm.env.perm.stC (by decide))

theorem absorbFill_ct [VG.Proof.Gcm.Arm.GhashLaw] {D : BitVec 32} {n q : Nat} (hn : n ≠ 0) (_hq : q < 16) :
    CT (AbsI c st w sp yo D n q) (absorbFill yo) := by
  refine CT.seq (J := fun s => AbsI c st w sp yo D n q s ∧ s.z = decide (q = 0)) ?_
    (fun s ⟨k7, k8, H, x, hx, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r6]) (.block [.cmp .r6 (imm 0)]) h).isSome =
        true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, x₁, hx₁, h₁⟩ ⟨_, _, _, x₂, hx₂, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r6, h₂.r6, hx₁, hx₂]) hc
  · obtain ⟨s₂, run₂, hz₂, hg₂, hm₂, hrd₂, hwr₂, hsp₂⟩ := cmp0_ok s .r6 hs.r6 (by omega_arith)
    exact WP.of_runBlock ⟨s₂, run₂, ⟨k7, k8, H, x, hx, hs.keep hg₂ ⟨hm₂, hrd₂, hwr₂, hsp₂⟩⟩, by rw [hz₂, hx]⟩
  · exact CT.ite (decide (q = 0)) (fun s h => h.2) (fun _ => CT.skip) fun hb =>
      (absorbHead_ct L hyo hn (by simpa using hb)).mono fun s h => h.1

theorem absorbWhole_ct [VG.Proof.Gcm.Arm.GhashLaw] {D : BitVec 32} {n q j : Nat} : CT (MidI c st w sp yo D n q j) (absorbWhole yo) := by
  let nb := (n - j) / 16
  let J₁ : State → Prop := fun s => ∃ k7 k8, Env c st w sp k7 k8 s ∧ DataOk st w sp s D n ∧ j ≤ n ∧
    s.gpr .r2 = D + BitVec.ofNat 32 j ∧ s.gpr .r3 = BitVec.ofNat 32 nb ∧ s.z = decide (nb = 0)
  refine CT.seq (J := J₁) ?_ (fun s ⟨k7, k8, H, x, m₀, hx, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5]) (.block splitWhole) h).isSome =
        true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, _, h₂⟩ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.r4, h₂.r4]
    · rw [h₁.r5, h₂.r5]
  · obtain ⟨s₁, run₁, h2, h3, -, -, hz, hg₁, hk₁⟩ := split_ok hs.le hs.data.lt32 hs.r4 hs.r5
    refine WP.of_runBlock ⟨s₁, run₁, k7, k8, hs.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) hk₁.sp hk₁.rd hk₁.wr, hs.data.of_eq hk₁.rd hk₁.wr, hs.le, h2, h3, hz⟩
  · refine CT.ite (decide (nb = 0)) (fun s h => by obtain ⟨_, _, _, _, _, _, _, hz⟩ := h; exact hz)
      (fun _ => CT.skip) fun hb => ?_
    have h0 : nb ≠ 0 := by simpa using hb
    let J₂ : State → Prop := fun s => ∃ k7 k8, Env c st w sp k7 k8 s ∧ DataOk st w sp s D n ∧ j ≤ n ∧
      s.gpr .r0 = c + BitVec.ofNat 32 240 ∧ s.gpr .r1 = st + BitVec.ofNat 32 yo ∧
      s.gpr .r2 = D + BitVec.ofNat 32 j ∧ s.gpr .r3 = BitVec.ofNat 32 nb ∧ s.gpr .r12 = w + BitVec.ofNat 32 512
    refine CT.seq (J := J₂) ?_ (fun s ⟨k7, k8, he, hd, hj, h2, h3, _⟩ => ?_) ?_
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r9, .r10, .r11])
          (.block [addI .r0 .r9 240, addI .r1 .r10 yo, addI .r12 .r11 scrO]) h).isSome = true := by
        rcases hyo with rfl | rfl <;> exact ⟨_, by taint_decide⟩
      exact CT.taint _ (fun s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => h₁.pin h₂ (by simpa using hr)) hc
    · have h9 := he.r9; have h10 := he.r10; have h11 := he.r11
      have ey : encodable (BitVec.ofNat 32 yo) = true := by rcases hyo with rfl | rfl <;> decide
      refine WP.of_runBlock ⟨((s.setReg .r0 (s.gpr .r9 + BitVec.ofNat 32 240)).setReg .r1
        (s.gpr .r10 + BitVec.ofNat 32 yo)).setReg .r12 (s.gpr .r11 + BitVec.ofNat 32 512), by arun [ey], k7, k8, he.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hd.of_eq rfl rfl, hj, ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, h9]
      · simp [gpr_setReg, h10]
      · simp [gpr_setReg, h2]
      · simp [gpr_setReg, h3]
      · simp [gpr_setReg, h11]
    · refine CT.gh fun s₁ s₂ ⟨_, _, he₁, hd₁, hj₁, a0, a1, a2, a3, a12⟩ ⟨_, _, he₂, hd₂, hj₂, b0, b1, b2, b3, b12⟩ => ?_
      have hdj₁ := hd₁.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith)
      have hdj₂ := hd₂.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith)
      exact ⟨_, _, _, _, _, ghCall_mk L hyo he₁ a0 a1 a2 a3 a12 (by have := hdj₁.fit; omega_arith)
        (hdj₁.st.sub_right (Lay.stSub (by omega_arith))).symm (hdj₁.w.sub_right (Lay.wSub (by decide))) hdj₁.stk hdj₁.rd,
        ghCall_mk L hyo he₂ b0 b1 b2 b3 b12 (by have := hdj₂.fit; omega_arith)
        (hdj₂.st.sub_right (Lay.stSub (by omega_arith))).symm (hdj₂.w.sub_right (Lay.wSub (by decide))) hdj₂.stk hdj₂.rd,
        he₁.sp.trans he₂.sp.symm⟩

omit L hyo in
theorem absorbTail_ct {D : BitVec 32} {n q j : Nat} : CT (MidI c st w sp yo D n q j) absorbTail := by
  obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5, .r10]) absorbTail h).isSome =
      true := ⟨_, by taint_decide⟩
  refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, _, h₂⟩ r hr => ?_) hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h₁.r4, h₂.r4]
  · rw [h₁.r5, h₂.r5]
  · exact h₁.env.pin h₂.env (by simp)

theorem absorb_ct [VG.Proof.Gcm.Arm.GhashLaw] {D : BitVec 32} {n q : Nat} (hq : q < 16) : CT (AbsI c st w sp yo D n q) (absorb yo) := by
  refine CT.seq (J := fun s => AbsI c st w sp yo D n q s ∧ s.z = decide (n = 0)) ?_
    (fun s ⟨k7, k8, H, x, hx, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5]) (.block [.cmp .r5 (imm 0)]) h).isSome =
        true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r5, h₂.r5]) hc
  · obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r5 hs.r5 hs.data.lt32
    exact WP.of_runBlock ⟨s₁, run₁, ⟨k7, k8, H, x, hx, hs.keep hg₁ ⟨hm₁, hrd₁, hwr₁, hsp₁⟩⟩, hz⟩
  refine CT.ite (decide (n = 0)) (fun s h => h.2) (fun _ => CT.skip) fun hb => ?_
  have h0 : n ≠ 0 := by simpa using hb
  let j₁ := if q = 0 then 0 else min (16 - q) n
  refine CT.seq (J := MidI c st w sp yo D n q j₁) ((absorbFill_ct L hyo h0 hq).mono fun s h => h.1)
    (fun s ⟨⟨k7, k8, H, x, hx, hs⟩, _⟩ => WP.mono (absorbFill_ok L hyo hs h0) fun s' ⟨j, hj, hm⟩ =>
      ⟨k7, k8, H, x, s.mem, hx, by rw [hj, hx] at hm; exact hm⟩) ?_
  refine CT.seq (J := MidI c st w sp yo D n q (j₁ + 16 * ((n - j₁) / 16))) (absorbWhole_ct L hyo)
    (fun s ⟨k7, k8, H, x, m₀, hx, hs⟩ => WP.mono (whole_ok L hyo hs (hs.data_eq hyo)) fun s' ⟨j, hj, hm, _⟩ =>
      ⟨k7, k8, H, x, m₀, hx, by rw [hj] at hm; exact hm⟩) absorbTail_ct

/-- `ghash1 yo .r11 96`, of `T`. -/
theorem ghT_ct [VG.Proof.Gcm.Arm.GhashLaw] : CT (GhIn c st w sp .r11 96 (w + BitVec.ofNat 32 96)) (ghash1 yo .r11 tO) := by
  have eT := L.wA (d := 96) (by decide)
  have hf : (w + BitVec.ofNat 32 96).toNat + 16 ≤ 2 ^ 32 := by rw [L.wN (by decide)]; have := L.ww; omega_arith
  refine ghash1_ct L hyo (.inr ⟨rfl, rfl⟩) hf ?_ ?_ ?_
  · rw [eT]; exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)
  · rw [eT]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · rw [eT]; exact L.stk_w (by decide)

omit hyo in
theorem ghIn_T {s : State} {k7 k8 : BitVec 32} (he : Env c st w sp k7 k8 s) :
    GhIn c st w sp .r11 96 (w + BitVec.ofNat 32 96) s :=
  ⟨⟨k7, k8, he⟩, by rw [he.r11], by rw [L.wA (d := 96) (by decide)]; exact covers_left (he.perm.wC (by decide))⟩

/-- Before `flush yo`: `q` buffered bytes. -/
theorem flush_ct [VG.Proof.Gcm.Arm.GhashLaw] {q : Nat} (hq : q < 16) :
    CT (fun s => ∃ k7 k8, Env c st w sp k7 k8 s ∧ s.gpr .r6 = BitVec.ofNat 32 q) (flush yo) := by
  refine CT.seq (J := fun s => (∃ k7 k8, Env c st w sp k7 k8 s ∧ s.gpr .r6 = BitVec.ofNat 32 q) ∧
    s.z = decide (q = 0)) ?_ (fun s ⟨k7, k8, he, h6⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r6]) (.block [.cmp .r6 (imm 0)]) h).isSome =
        true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) hc
  · obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r6 h6 (by omega_arith)
    exact WP.of_runBlock ⟨s₁, run₁, ⟨k7, k8, he.keep (fun r _ => by rw [hg₁]) hsp₁ hrd₁ hwr₁, by rw [hg₁, h6]⟩, hz⟩
  refine CT.ite (decide (q = 0)) (fun s h => h.2) (fun _ => CT.skip) fun hb => ?_
  have h0 : q ≠ 0 := by simpa using hb
  refine CT.seq (J := GhIn c st w sp .r11 96 (w + BitVec.ofNat 32 96)) ?_ (fun s ⟨⟨k7, k8, he, h6⟩, _⟩ =>
    WP.mono (flushCopy_ok L hyo (H := blockAt s.mem (State.addr c + BitVec.ofNat 64 240)) ⟨he, rfl⟩ h6 hq h0)
      fun s' hm => ghIn_T L hm.env) (ghT_ct L hyo)
  obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r6, .r10, .r11])
      (.seq (.block flushPre) copyLoop) h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.taint _ (fun s₁ s₂ ⟨⟨_, _, h₁, a₁⟩, _⟩ ⟨⟨_, _, h₂, a₂⟩, _⟩ r hr => ?_) hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a₁, a₂]
  · exact h₁.pin h₂ (by simp)
  · exact h₁.pin h₂ (by simp)

/-- `lens yo`: the lengths are not needed, only `W`. -/
theorem lens_ct [VG.Proof.Gcm.Arm.GhashLaw] : CT (fun s => ∃ k7 k8, Env c st w sp k7 k8 s) (lens yo) := by
  refine CT.seq (J := GhIn c st w sp .r11 96 (w + BitVec.ofNat 32 96)) ?_ (fun s ⟨k7, k8, he⟩ =>
    WP.mono (lensStore_ok L he) fun s' ⟨_, hg, hrd, hwr, hsp⟩ => ghIn_T L (k7 := k7) (k8 := k8)
      (he.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide)) hsp hrd hwr)) (ghT_ct L hyo)
  obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r11])
      (.block (be64Store .r4 .r5 tO ++ be64Store .r6 .r7 (tO + 8))) h).isSome = true := ⟨_, by taint_decide⟩
  exact CT.taint _ (fun s₁ s₂ ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr => h₁.pin h₂ (by simp at hr; simp [hr])) hc

end

end VG.Proof.AesGcm.Arm

end

end

/-!
# AES-GCM on ARMv7: `crypt` and `tag` are constant time

Untrusted: everything here is checked by Lean. The invariants fix the
context, the state, `W`, the stack pointer, the number of rounds (in `r8`),
the data's address and length, and the length of the text so far modulo 16.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- Before `crypt`. -/
def CrI (c st w sp k8 : BitVec 32) (R : Nat) (D : BitVec 32) (n q : Nat) (s : State) : Prop :=
  ∃ k7 icb P, P % 16 = q ∧ CrIn c st w sp k7 k8 R icb P D n s

/-- Part of the way: `j` bytes done, from `S` to `T`. -/
def CrMG (to : Bool) (c st w sp k8 : BitVec 32) (R : Nat) (S T : BitVec 32) (n q j : Nat) (s : State) : Prop :=
  ∃ k7 icb P m₀, P % 16 = q ∧ CrMidG to c st w sp k7 k8 R icb P S T n m₀ j s

/-- In place. -/
abbrev CrM (c st w sp k8 : BitVec 32) (R : Nat) (D : BitVec 32) (n q j : Nat) (s : State) : Prop :=
  CrMG false c st w sp k8 R D D n q j s

theorem pin8 {c st w sp a b a' b' : BitVec 32} {s₁ s₂ : State} (h₁ : Env c st w sp a b s₁)
    (h₂ : Env c st w sp a' b' s₂) {R : Nat} (e₁ : s₁.gpr .r8 = BitVec.ofNat 32 R) (e₂ : s₂.gpr .r8 = BitVec.ofNat 32 R)
    {r : Reg} (hr : r = .r8 ∨ r = .r9 ∨ r = .r10 ∨ r = .r11) : s₁.gpr r = s₂.gpr r := by
  rcases hr with rfl | hr
  · rw [e₁, e₂]
  · exact h₁.pin h₂ hr

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp)
include L

theorem cryptWhole_ct {to : Bool} {k8 : BitVec 32} {R : Nat} {S T : BitVec 32} {n q j : Nat} :
    CT (CrMG to c st w sp k8 R S T n q j) (cryptWholeG to) := by
  let nb := (n - j) / 16
  let J₁ : State → Prop := fun s => ∃ k7, Env c st w sp k7 k8 s ∧ DataW c st w sp k7 k8 s T n ∧
    DataOk st w sp s S n ∧ CrMode to c st w sp S T n ∧ j ≤ n ∧
    s.gpr .r8 = BitVec.ofNat 32 R ∧ (R = 10 ∨ R = 12 ∨ R = 14) ∧
    s.gpr .r3 = S + BitVec.ofNat 32 j ∧ s.gpr .r12 = BitVec.ofNat 32 nb ∧ s.z = decide (nb = 0) ∧
    (to = true → s.gpr .r6 = T + BitVec.ofNat 32 j)
  refine CT.seq (J := J₁) ?_ (fun s ⟨k7, icb, P, m₀, hP, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5]) (.block splitCtr) h).isSome =
        true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, h₂⟩ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.r4, h₂.r4]
    · rw [h₁.r5, h₂.r5]
  · obtain ⟨s₁, run₁, h3, h12, -, -, hz, hg₁, hk₁⟩ := splitCtr_ok hs.le hs.data.ok.lt32 hs.r4 hs.r5
    refine WP.of_runBlock ⟨s₁, run₁, k7, hs.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) hk₁.sp hk₁.rd hk₁.wr, hs.data.of_eq hk₁.rd hk₁.wr, hs.src.of_eq hk₁.rd hk₁.wr,
      hs.mode, hs.le,
      by rw [hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hs.r8], hs.rounds,
      h3, h12, hz, fun ht => by
        rw [hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hs.r6 ht]⟩
  · refine CT.ite (decide (nb = 0)) (fun s h => by obtain ⟨_, _, _, _, _, _, _, _, _, _, hz, _⟩ := h; exact hz)
      (fun _ => CT.skip) fun hb => ?_
    have h0 : nb ≠ 0 := by simpa using hb
    cases to
    · let J₂ : State → Prop := fun s => ∃ k7, Env c st w sp k7 k8 s ∧ DataW c st w sp k7 k8 s T n ∧ j ≤ n ∧
        (R = 10 ∨ R = 12 ∨ R = 14) ∧ s.gpr .r0 = c ∧ s.gpr .r1 = BitVec.ofNat 32 R ∧
        s.gpr .r2 = st + BitVec.ofNat 32 48 ∧ s.gpr .r3 = S + BitVec.ofNat 32 j ∧
        s.gpr .r12 = BitVec.ofNat 32 nb ∧ s.gpr .lr = w + BitVec.ofNat 32 512 ∧ S = T
      refine CT.seq (J := J₂) ?_ (fun s ⟨k7, he, hd, _, hm, hj, h8, hR, h3, h12, _⟩ => ?_) ?_
      · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r8, .r9, .r10, .r11])
            (.block [.mov .r0 (.reg .r9), .mov .r1 (.reg .r8), addI .r2 .r10 48, addI .lr .r11 scrO]) h).isSome =
            true := ⟨_, by taint_decide⟩
        exact CT.taint _ (fun s₁ s₂ ⟨_, h₁, _, _, _, _, e₁, _⟩ ⟨_, h₂, _, _, _, _, e₂, _⟩ r hr =>
          pin8 h₁ h₂ e₁ e₂ (by simpa using hr)) hc
      · obtain ⟨s₂, run₂, h0', h1', h2', hlr', hg₂, hk₂⟩ := wholeArgs_ok he
        refine WP.of_runBlock ⟨s₂, run₂, k7, he.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide) (by decide))
          hk₂.sp hk₂.rd hk₂.wr, hd.of_eq hk₂.rd hk₂.wr, hj, hR, h0', by rw [h1', h8], h2',
          by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h3],
          by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h12], hlr', hm⟩
      · refine CT.ctr fun s₁ s₂ ⟨_, he₁, hd₁, hj₁, hR, a0, a1, a2, a3, a12, alr, e⟩
          ⟨_, he₂, hd₂, _, _, b0, b1, b2, b3, b12, blr, _⟩ => ?_
        subst e
        exact ⟨_, _, _, _, _, _, ctrWhole_mk L he₁ a0 a1 a2 a3 a12 alr hR (hd₁.sub (by omega_using [h0]) (by omega_using [h0])),
          ctrWhole_mk L he₂ b0 b1 b2 b3 b12 blr hR (hd₂.sub (by omega_using [h0]) (by omega_using [h0])), he₁.sp.trans he₂.sp.symm⟩
    · -- Out of place: the destination and the count to the stack arguments, the call, and the
      -- destination advanced.
      let J₂ : State → Prop := fun s => ∃ k7, Env c st w sp k7 k8 s ∧ DataW c st w sp k7 k8 s T n ∧
        DataOk st w sp s S n ∧ CrMode true c st w sp S T n ∧ j ≤ n ∧ (R = 10 ∨ R = 12 ∨ R = 14) ∧
        s.gpr .r0 = BitVec.ofNat 32 nb ∧ s.gpr .r1 = w + BitVec.ofNat 32 512 ∧
        s.gpr .r2 = T + BitVec.ofNat 32 j ∧ s.gpr .r3 = S + BitVec.ofNat 32 j ∧
        s.gpr .r8 = BitVec.ofNat 32 R ∧ s.gpr .r6 = T + BitVec.ofNat 32 j
      let J₃ : State → Prop := fun s => s.gpr .r6 = T + BitVec.ofNat 32 j ∧ s.gpr .r12 = BitVec.ofNat 32 nb
      refine CT.seq (J := J₂) ?_ (fun s ⟨k7, he, hd, hsr, hm, hj, h8, hR, h3, h12, _, h6⟩ => ?_) ?_
      · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r6, .r11, .r12])
            (.block [.mov .r2 (.reg .r6), .mov .r0 (.reg .r12), addI .r1 .r11 scrO]) h).isSome =
            true := ⟨_, by taint_decide⟩
        refine CT.taint _ (fun s₁ s₂ ⟨_, h₁, _, _, _, _, _, _, _, a12, _, a6⟩ ⟨_, h₂, _, _, _, _, _, _, _, b12, _, b6⟩
          r hr => ?_) hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [a6 rfl, b6 rfl]
        · exact h₁.pin h₂ (by simp)
        · rw [a12, b12]
      · obtain ⟨s₂, run₂, h0', h1', h2', hg₂, hk₂⟩ : ∃ s₂, runBlock isa
            [.mov .r2 (.reg .r6), .mov .r0 (.reg .r12), addI .r1 .r11 scrO] s = some s₂ ∧
            s₂.gpr .r0 = BitVec.ofNat 32 nb ∧ s₂.gpr .r1 = w + BitVec.ofNat 32 512 ∧
            s₂.gpr .r2 = T + BitVec.ofNat 32 j ∧
            (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s₂.gpr r = s.gpr r) ∧ Keeps s s₂ := by
          refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_⟩
          · simp [gpr_setReg, h12]
          · simp [gpr_setReg, he.r11]
          · simp [gpr_setReg, h6 rfl]
          · intro r a b d; simp [gpr_setReg, a, b, d]
          · exact ⟨rfl, rfl, rfl, rfl⟩
        exact WP.of_runBlock ⟨s₂, run₂, k7, he.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide))
          hk₂.sp hk₂.rd hk₂.wr, hd.of_eq hk₂.rd hk₂.wr, hsr.of_eq hk₂.rd hk₂.wr, hm, hj, hR, h0', h1', h2',
          by rw [hg₂ _ (by decide) (by decide) (by decide), h3], by rw [hg₂ _ (by decide) (by decide) (by decide), h8],
          by rw [hg₂ _ (by decide) (by decide) (by decide), h6 rfl]⟩
      have mk : ∀ s, J₂ s → CtrToCall s c (st + BitVec.ofNat 32 48) (S + BitVec.ofNat 32 j) (T + BitVec.ofNat 32 j)
          (w + BitVec.ofNat 32 512) R nb := by
        intro s ⟨k7, he, hd, hsr, hm, hj, hR, a0, a1, a2, a3, a8, _⟩
        obtain ⟨dST, sp12, bc, bst, bw, bS, bT⟩ := hm
        have hdj := hd.sub (j := j) (k := 16 * nb) (by omega_using [h0]) (by omega_using [h0])
        have hsj := hsr.sub (j := j) (k := 16 * nb) (by omega_using [h0]) (by omega_using [h0])
        have eD := hd.ok.addr (j := j) (by omega)
        have eS := hsr.addr (j := j) (by omega)
        have eC := L.stA (d := 48) (by decide)
        have eW := L.wA (d := 512) (by decide)
        have hk := he.sp
        refine ⟨he.r9, a8, by rw [he.r10], a3, a0, a1, a2, hR, by rw [hk]; exact sp12,
          by have := L.cw; omega_using [this], by rw [L.stN (by decide)]; have := L.sw; omega_using [this], hsj.fit, hdj.ok.fit,
          by rw [L.wN (by decide)]; have := L.ww; omega_using [this], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals try simp only [eC, eW]
        · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide))
        · exact hdj.ctx.sub_left (Region.sub_prefix (by decide))
        · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
        · exact (hdj.ok.st.sub_right (Lay.stSub (by decide))).symm
        · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
        · exact hdj.ok.w.sub_right (Lay.wSub (by decide))
        · exact hsj.st.sub_right (Lay.stSub (by decide))
        · rw [eS, eD]
          exact (dST.sub_left (Offset.sub_base _ (by omega_using [h0]))).sub_right (Offset.sub_base _ (by omega_using [h0]))
        · exact hsj.w.sub_right (Lay.wSub (by decide))
        · rw [hk]; exact bc.sub_right (Region.sub_prefix (by decide))
        · rw [hk]; exact bst.sub_right (Lay.stSub (by decide))
        · rw [hk, eS]; exact bS.sub_right (Offset.sub_base _ (by omega_using [h0]))
        · rw [hk, eD]; exact bT.sub_right (Offset.sub_base _ (by omega_using [h0]))
        · rw [hk]; exact bw.sub_right (Lay.wSub (by decide))
        · exact covers_cons (covers_prefix he.perm.ctx (by decide)) hsj.rd
        · exact covers_cons (he.perm.stC (by decide)) (covers_cons hdj.wr (he.perm.wC (by decide)))
      have spJ : ∀ s, J₂ s → s.sp = sp := fun s ⟨_, he, _⟩ => he.sp
      refine CT.seq (J := J₃) (CT.ctrTo fun s₁ s₂ h₁ h₂ => ⟨_, _, _, _, _, _, _, mk s₁ h₁, mk s₂ h₂,
        (spJ s₁ h₁).trans (spJ s₂ h₂).symm⟩) (fun s hs => WP.mono (ctrTo_call (mk s hs)) fun s' g => ⟨?_, ?_⟩) ?_
      · obtain ⟨_, he, _, _, _, _, _, _, _, _, _, _, h6⟩ := hs
        rw [g.saved _ (by decide) (by decide), h6]
      · obtain ⟨_, _, _, _, _, _, _, a0, _⟩ := hs
        rw [g.r12, a0]
      · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r6, .r12])
            (.block [.dp .add .r6 .r6 (.shifted .r12 .lsl 4)]) h).isSome = true := ⟨_, by taint_decide⟩
        refine CT.taint _ (fun s₁ s₂ ⟨a6, a12⟩ ⟨b6, b12⟩ r hr => ?_) hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [a6, b6]
        · rw [a12, b12]

theorem cryptTail_ct {to : Bool} {k8 : BitVec 32} {R : Nat} {S T : BitVec 32} {n q j : Nat} :
    CT (CrMG to c st w sp k8 R S T n q j) (cryptTailG to) := by
  refine CT.seq (J := fun s => CrMG to c st w sp k8 R S T n q j s ∧ s.z = decide (n - j = 0)) ?_
    (fun s ⟨k7, icb, P, m₀, hP, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5]) (.block [.cmp .r5 (imm 0)]) h).isSome =
        true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r5, h₂.r5]) hc
  · obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r5 hs.r5 (by have := hs.data.ok.lt32; omega_using [this])
    refine WP.of_runBlock ⟨s₁, run₁, ⟨k7, icb, P, m₀, hP, ?_⟩, hz⟩
    exact ⟨hs.env.keep (fun r _ => by rw [hg₁]) hsp₁ hrd₁ hwr₁, hs.le, by rw [hg₁, hs.r4], by rw [hg₁, hs.r5],
      by rw [hg₁, hs.r8], hs.rounds, hs.data.of_eq hrd₁ hwr₁, fun h => by rw [hm₁]; exact hs.ctr h,
      fun h => by rw [hm₁]; exact hs.done h, by rw [hm₁]; exact hs.rest, hs.whole, by rw [hm₁]; exact hs.frame,
      fun h => by rw [hg₁]; exact hs.r6 h, hs.src.of_eq hrd₁ hwr₁, hs.mode⟩
  refine CT.ite (decide (n - j = 0)) (fun s h => h.2) (fun _ => CT.skip) fun _ => ?_
  let J₁ : State → Prop := fun s => ∃ k7, Env c st w sp k7 k8 s ∧ (R = 10 ∨ R = 12 ∨ R = 14) ∧ s.gpr .r0 = c ∧
    s.gpr .r1 = BitVec.ofNat 32 R ∧ s.gpr .r2 = st + BitVec.ofNat 32 48 ∧ s.gpr .r3 = st + BitVec.ofNat 32 64 ∧
    s.gpr .r12 = BitVec.ofNat 32 1 ∧ s.gpr .lr = w + BitVec.ofNat 32 512
  let J₂ : State → Prop := fun s => ∃ k7 icb P m₀ s₀, TailKs to c st w sp k7 k8 R icb P S T n m₀ j s₀ s
  refine CT.seq (J := J₂) (CT.seq (J := J₁) ?_ (fun s ⟨⟨k7, icb, P, m₀, hP, hs⟩, _⟩ => ?_) ?_)
    (fun s ⟨⟨k7, icb, P, m₀, hP, hs⟩, _⟩ => WP.mono (tailKs_ok L hs (CrMidG.ciph L hs)) fun s' h =>
      ⟨k7, icb, P, m₀, s, h⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r8, .r9, .r10, .r11]) (.block tailArgs)
        h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, _, _, h₁⟩, _⟩ ⟨⟨_, _, _, _, _, h₂⟩, _⟩ r hr =>
      pin8 h₁.env h₂.env h₁.r8 h₂.r8 (by simpa using hr)) hc
  · obtain ⟨s₂, run₂, -, h0, h1, h2, h3, h12, hlr, hg₂, hrd₂, hwr₂, hsp₂⟩ := tailArgs_ok L hs.env
    exact WP.of_runBlock ⟨s₂, run₂, k7, hs.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        exact hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hsp₂ hrd₂ hwr₂,
      hs.rounds, h0, by rw [h1, hs.r8], h2, h3, h12, hlr⟩
  · exact CT.ctr fun s₁ s₂ ⟨_, he₁, hR, a0, a1, a2, a3, a12, alr⟩ ⟨_, he₂, _, b0, b1, b2, b3, b12, blr⟩ =>
      ⟨_, _, _, _, _, _, ctrTail_mk L he₁ a0 a1 a2 a3 a12 alr hR, ctrTail_mk L he₂ b0 b1 b2 b3 b12 blr hR,
        he₁.sp.trans he₂.sp.symm⟩
  · cases to
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5, .r10]) (tailXor false)
          h).isSome = true := ⟨_, by taint_decide⟩
      refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, h₂⟩ r hr => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.r4, h₂.r4]
      · rw [h₁.r5, h₂.r5]
      · exact h₁.env.pin h₂.env (by simp)
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5, .r6, .r10]) (tailXor true)
          h).isSome = true := ⟨_, by taint_decide⟩
      refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, h₂⟩ r hr => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.r4, h₂.r4]
      · rw [h₁.r5, h₂.r5]
      · rw [h₁.r6 rfl, h₂.r6 rfl]
      · exact h₁.env.pin h₂.env (by simp)

/-- `cryptTo`, from the start of a whole block. -/
theorem cryptTo_ct {k8 : BitVec 32} {R : Nat} {S T : BitVec 32} {n : Nat} :
    CT (CrMG true c st w sp k8 R S T n 0 0) cryptTo := by
  refine CT.seq (J := fun s => CrMG true c st w sp k8 R S T n 0 0 s ∧ s.z = decide (n - 0 = 0)) ?_
    (fun s ⟨k7, icb, P, m₀, hP, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5]) (.block [.cmp .r5 (imm 0)]) h).isSome =
        true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r5, h₂.r5]) hc
  · obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r5 hs.r5 (by have := hs.data.ok.lt32; omega_using [this])
    refine WP.of_runBlock ⟨s₁, run₁, ⟨k7, icb, P, m₀, hP, ?_⟩, hz⟩
    exact ⟨hs.env.keep (fun r _ => by rw [hg₁]) hsp₁ hrd₁ hwr₁, hs.le, by rw [hg₁, hs.r4], by rw [hg₁, hs.r5],
      by rw [hg₁, hs.r8], hs.rounds, hs.data.of_eq hrd₁ hwr₁, fun h => by rw [hm₁]; exact hs.ctr h,
      fun h => by rw [hm₁]; exact hs.done h, by rw [hm₁]; exact hs.rest, hs.whole, by rw [hm₁]; exact hs.frame,
      fun h => by rw [hg₁]; exact hs.r6 h, hs.src.of_eq hrd₁ hwr₁, hs.mode⟩
  refine CT.ite (decide (n - 0 = 0)) (fun s h => h.2) (fun _ => CT.skip) fun _ => ?_
  refine CT.seq (J := CrMG true c st w sp k8 R S T n 0 (0 + 16 * ((n - 0) / 16)))
    (CT.mono (cryptWhole_ct L) fun _ h => h.1)
    (fun s ⟨⟨k7, icb, P, m₀, hP, hs⟩, _⟩ => WP.mono (cryptWholeG_ok L hs (CrMidG.ciph L hs)) fun s' ⟨j, hj, hm, _⟩ =>
      ⟨k7, icb, P, m₀, hP, by rw [hj] at hm; exact hm⟩) (cryptTail_ct L)

theorem crypt_ct {k8 : BitVec 32} {R : Nat} {D : BitVec 32} {n q : Nat} :
    CT (CrI c st w sp k8 R D n q) crypt := by
  refine CT.seq (J := fun s => CrI c st w sp k8 R D n q s ∧ s.z = decide (n = 0)) ?_
    (fun s ⟨k7, icb, P, hP, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5]) (.block [.cmp .r5 (imm 0)]) h).isSome =
        true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r5, h₂.r5]) hc
  · obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r5 hs.r5 hs.data.ok.lt32
    exact WP.of_runBlock ⟨s₁, run₁, ⟨k7, icb, P, hP, hs.keep hg₁ ⟨hm₁, hrd₁, hwr₁, hsp₁⟩⟩, hz⟩
  refine CT.ite (decide (n = 0)) (fun s h => h.2) (fun _ => CT.skip) fun hb => ?_
  have h0 : n ≠ 0 := by simpa using hb
  let j₁ := if q = 0 then 0 else min (16 - q) n
  refine CT.seq (J := CrM c st w sp k8 R D n q j₁) ?_
    (fun s ⟨⟨k7, icb, P, hP, hs⟩, _⟩ => WP.mono (cryptFill_ok L hs h0) fun s' ⟨j, hj, hm⟩ =>
      ⟨k7, icb, P, s.mem, hP, by rw [hj, hP] at hm; exact hm⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5, .r6, .r10]) cryptFill h).isSome =
        true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, hP₁, h₁⟩, _⟩ ⟨⟨_, _, _, hP₂, h₂⟩, _⟩ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.r4, h₂.r4]
    · rw [h₁.r5, h₂.r5]
    · rw [h₁.r6, h₂.r6, hP₁, hP₂]
    · exact h₁.env.pin h₂.env (by simp)
  refine CT.seq (J := CrM c st w sp k8 R D n q (j₁ + 16 * ((n - j₁) / 16))) (cryptWhole_ct L)
    (fun s ⟨k7, icb, P, m₀, hP, hs⟩ => WP.mono (cryptWholeG_ok L hs (CrMidG.ciph L hs)) fun s' ⟨j, hj, hm, _⟩ =>
      ⟨k7, icb, P, m₀, hP, by rw [hj] at hm; exact hm⟩) (cryptTail_ct L)

/-- `tag o`, from an environment with the number of rounds in `r8`. -/
theorem tag_ct [VG.Proof.Gcm.Arm.GhashLaw] {o R : Nat} (ho : o = 0 ∨ o = 112) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    CT (fun s => ∃ k7, Env c st w sp k7 (BitVec.ofNat 32 R) s) (tag o) := by
  refine CT.seq (J := fun s => ∃ k7, Env c st w sp k7 (BitVec.ofNat 32 R) s)
    ((lens_ct L (yo := 16) (.inr rfl)).mono fun s ⟨k7, he⟩ => ⟨k7, _, he⟩)
    (fun s ⟨k7, he⟩ => WP.mono (lens_ok L (yo := 16) (.inr rfl) (H := blockAt s.mem (State.addr c + BitVec.ofNat 64 240))
      he rfl) fun s' h => ⟨k7, h.1⟩) ?_
  let J : State → Prop := fun s => ∃ k7, Env c st w sp k7 (BitVec.ofNat 32 R) s ∧ s.gpr .r0 = c ∧
    s.gpr .r1 = BitVec.ofNat 32 R ∧ s.gpr .r2 = st ∧ s.gpr .r3 = w + BitVec.ofNat 32 o ∧
    s.gpr .r12 = BitVec.ofNat 32 1 ∧ s.gpr .lr = w + BitVec.ofNat 32 512
  refine CT.seq (J := J) ?_ (fun s ⟨k7, he⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r8, .r9, .r10, .r11]) (.block (tagArgs o))
        h).isSome = true := by rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, h₁⟩ ⟨_, h₂⟩ r hr => pin8 h₁ h₂ h₁.r8 h₂.r8 (by simpa using hr)) hc
  · obtain ⟨s₂, run₂, -, h0, h1, h2, h3, h12, hlr, hg₂, hrd₂, hwr₂, hsp₂⟩ := tagArgs_ok L ho he
    exact WP.of_runBlock ⟨s₂, run₂, k7, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        exact hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hsp₂ hrd₂ hwr₂,
      h0, h1, h2, h3, h12, hlr⟩
  · exact CT.ctr fun s₁ s₂ ⟨_, he₁, a0, a1, a2, a3, a12, alr⟩ ⟨_, he₂, b0, b1, b2, b3, b12, blr⟩ =>
      ⟨_, _, _, _, _, _, ctrTag_mk L ho he₁ a0 a1 a2 a3 a12 alr hR, ctrTag_mk L ho he₂ b0 b1 b2 b3 b12 blr hR,
        he₁.sp.trans he₂.sp.symm⟩

end

end VG.Proof.AesGcm.Arm
