module

public import VerifiedGarbage.Proof.AesGcm.Arm.Fn
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.AesGcm.Arm.Entry
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.AesGcm.Arm.TextAbsorb
import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
import VerifiedGarbage.Proof.Framework.SigEval
public import VerifiedGarbage.Proof.AesGcm.Arm.Args
public import VerifiedGarbage.Proof.AesGcm.Arm.Tag

/-! ### `AesGcm.Arm.FinTag`, which this module and modules that import it used -/

section

/-!
# AES-GCM on ARMv7: the tag of a streaming state (`finTag o`)

Untrusted: everything here is checked by Lean. `finTag o` pads the buffered
bytes (of the additional data if there is no text, of the text otherwise)
and absorbs them, then the lengths block, and writes the tag to `W + o`
(`finTag_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput ghash ghashFrom blocks zeros padLen toBytes ofBytes)
open VG.Proof.Gcm (Absorbed lensBlock padded)

theorem disj_sub {X : Region} {rs rs' : List Region} (h : ∀ r ∈ rs', X.Disjoint r)
    (hs : ∀ r ∈ rs, ∃ r' ∈ rs', Region.Sub r r') : ∀ r ∈ rs, X.Disjoint r := fun r hr => by
  obtain ⟨r', hr', hsub⟩ := hs r hr; exact (h r' hr').sub_right hsub

/-- `tFrame` is within `tagFrame`. -/
theorem tFrame_sub {st w sp : BitVec 32} {o : Nat} :
    ∀ r ∈ tFrame st w sp 16, ∃ r' ∈ tagFrame st w sp o, Region.Sub r r' := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., by simpa using Offset.sub_base (State.addr st) (show 16 + 16 ≤ 32 by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 512, 2048⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem t_tagFrame {st w sp : BitVec 32} {o : Nat} {m m' : Mem} (h : Frame (tFrame st w sp 16) m m') :
    Frame (tagFrame st w sp o) m m' := h.sub tFrame_sub

/-- After `finTag o`, from `m₀`. -/
structure FinOut (c st w sp k8 : BitVec 32) (na : Nat) (s₀ : State) (o R : Nat) (H : Block) (a ct : List Byte)
    (m₀ : Mem) (s : State) : Prop where
  env : ∃ k7, Env c st w sp k7 k8 s
  args : ArgsKeep na s₀ s
  out : Absorbed m₀ (State.addr st + BitVec.ofNat 64 16) (State.addr st + BitVec.ofNat 64 32) H (ghashInput a ct) →
    bytesAt s.mem (State.addr w + BitVec.ofNat 64 o) 16 =
      toBytes (ghashFrom H (ghash H (blocks (padded a ct))) [ofBytes (lensBlock (arg s₀ 1 ++ arg s₀ 0).toNat ct.length)]
        ^^^ ciphOf m₀ (State.addr c) R (blockAt m₀ (State.addr st)))
  frame : Frame (tagFrame st w sp o) m₀ s.mem

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp)
include L

theorem finTag_ok [VG.Proof.Gcm.Arm.GhashLaw] {na : Nat} (hna : 4 ≤ na) {s₀ s : State} {o R : Nat} (ho : o = 0 ∨ o = 112) {H : Block}
    {a ct : List Byte} (he : Env c st w sp k7 k8 s) (hk : ArgsKeep na s₀ s) (hf : s₀.sp.toNat + 4 * na ≤ 2 ^ 32)
    (hin : args s₀ na ∈ s₀.rd) (hA : ∀ r ∈ tagFrame st w sp o, (args s₀ na).Disjoint r)
    (h8 : k8 = BitVec.ofNat 32 R) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H)
    (ha : a.length % 16 = (arg s₀ 0).toNat % 16) (hP : (arg s₀ 3 ++ arg s₀ 2).toNat = ct.length) :
    WP isa (finTag o) s (FinOut c st w sp k8 na s₀ o R H a ct s.mem) := by
  have hlt := Nat.mod_lt (ghashInput a ct).length (show 16 > 0 by decide)
  obtain ⟨i2, v2⟩ := hk.at hf hin 2 (by omega_arith) (show 4 * 2 = 8 from rfl)
  obtain ⟨i3, v3⟩ := hk.at hf hin 3 (by omega_arith) (show 4 * 3 = 12 from rfl)
  obtain ⟨s₁, run₁, hz₁, hg₁, hK₁⟩ : ∃ s₁, runBlock isa tlenZero s = some s₁ ∧
      s₁.z = decide (ct.length = 0) ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by simp only [tlenZero]; arun [i2, v2, i3, v3], ?_, ?_, ?_⟩
    · simp only [z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, v2, v3]
      rw [z_sub0, ← hP]
      exact decide_eq_decide.mpr (or_zero_iff _ _)
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hk₁ := hk.of_eq hK₁.mem hK₁.sp hK₁.rd hK₁.wr
  -- `r6`: the length of the buffered bytes, modulo 16
  have mid : WP isa (.ite .eq (.block [.ldrSp .r6 0]) (.block [.ldrSp .r6 8])) s₁ fun s₂ =>
      (s₂.gpr .r6).toNat % 16 = (ghashInput a ct).length % 16 ∧ (∀ r, r ≠ .r6 → s₂.gpr r = s₁.gpr r) ∧
        Keeps s₁ s₂ := by
    refine WP.ite _ (eval_eq' hz₁) (fun ht => ?_) (fun hf₁ => ?_)
    · have hc : ct = [] := List.eq_nil_of_length_eq_zero (by simpa using ht)
      subst hc
      obtain ⟨i0, v0⟩ := hk₁.at hf hin 0 (by omega_arith) (show 4 * 0 = 0 from rfl)
      refine WP.of_runBlock ⟨_, by arun [i0, v0], ?_, ?_, ?_⟩
      · simp [gpr_setReg, v0, Proof.Gcm.ghashInput_nil, ha]
      · intro r hr; simp [gpr_setReg, hr]
      · exact ⟨rfl, rfl, rfl, rfl⟩
    · have hc : ct ≠ [] := fun e => by subst e; simp at hf₁
      obtain ⟨i2', v2'⟩ := hk₁.at hf hin 2 (by omega_arith) (show 4 * 2 = 8 from rfl)
      refine WP.of_runBlock ⟨_, by arun [i2', v2'], ?_, ?_, ?_⟩
      · simp only [gpr_setReg, ite_true, v2', Proof.Gcm.ghashInput_of_ne hc, List.length_append,
          Proof.Gcm.length_zeros, lowTo_mod16 hP]
        have := Proof.Gcm.length_pad_mod a.length; omega_arith
      · intro r hr; simp [gpr_setReg, hr]
      · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.mono mid fun s₂ ⟨h6₂, hg₂, hK₂⟩ => ?_)
  obtain ⟨s₃, run₃, h6₃, hg₃, hK₃⟩ : ∃ s₃, runBlock isa [.dp .and .r6 .r6 (imm 15)] s₂ = some s₃ ∧
      s₃.gpr .r6 = BitVec.ofNat 32 ((ghashInput a ct).length % 16) ∧ (∀ r, r ≠ .r6 → s₃.gpr r = s₂.gpr r) ∧
      Keeps s₂ s₃ := by
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, and15, h6₂]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have hK₀₃ : Keeps s s₃ := (hK₁.trans hK₂).trans hK₃
  have he₃ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [hg₃ _ (by decide), hg₂ _ (by decide), hg₁ _ (by decide) (by decide)]) hK₀₃.sp hK₀₃.rd hK₀₃.wr
  have hk₃ := hk.of_eq hK₀₃.mem hK₀₃.sp hK₀₃.rd hK₀₃.wr
  refine WP.seq (WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl) (x := ghashInput a ct) (H := H)
    ⟨he₃, by rw [hK₀₃.mem]; exact hH⟩ h6₃)) fun s₄ hh => ?_)
  obtain ⟨hfl, rd₄, wr₄, sp₄⟩ := hh
  have hk₄ := hk₃.frame hf hfl.frame (disj_sub hA tFrame_sub) sp₄ rd₄ wr₄
  have hf₄ := hfl.frame
  rw [hK₀₃.mem] at hf₄
  -- the lengths
  obtain ⟨j0, w0⟩ := hk₄.at hf hin 0 (by omega_arith) (show 4 * 0 = 0 from rfl)
  obtain ⟨j1, w1⟩ := hk₄.at hf hin 1 (by omega_arith) (show 4 * 1 = 4 from rfl)
  obtain ⟨j2, w2⟩ := hk₄.at hf hin 2 (by omega_arith) (show 4 * 2 = 8 from rfl)
  obtain ⟨j3, w3⟩ := hk₄.at hf hin 3 (by omega_arith) (show 4 * 3 = 12 from rfl)
  obtain ⟨s₅, run₅, h4₅, h5₅, h6₅, h7₅, hg₅, hK₅⟩ : ∃ s₅, runBlock isa [.ldrSp .r4 0, .ldrSp .r5 4, .ldrSp .r6 8,
      .ldrSp .r7 12] s₄ = some s₅ ∧ s₅.gpr .r4 = arg s₀ 0 ∧ s₅.gpr .r5 = arg s₀ 1 ∧ s₅.gpr .r6 = arg s₀ 2 ∧
      s₅.gpr .r7 = arg s₀ 3 ∧ (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    refine ⟨_, by arun [j0, w0, j1, w1, j2, w2, j3, w3], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, w0]
    · simp [gpr_setReg, w1]
    · simp [gpr_setReg, w2]
    · simp [gpr_setReg, w3]
    · intro r a b d e; simp [gpr_setReg, a, b, d, e]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ := hfl.env.set7 h7₅ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide) (by decide) (by decide))
    hK₅.sp hK₅.rd hK₅.wr
  have hk₅ := hk₄.of_eq hK₅.mem hK₅.sp hK₅.rd hK₅.wr
  refine WP.mono (WP.with_rdwr (tag_ok L ho he₅ h8 hR (H := H) (by rw [hK₅.mem]; exact hfl.hH) rfl)) fun s₆ hh => ?_
  obtain ⟨tg, rd₆, wr₆, sp₆⟩ := hh
  rw [h4₅, h5₅, h6₅, h7₅, hP, hK₅.mem] at tg
  refine ⟨⟨_, tg.env⟩, hk₄.frame hf tg.frame hA (sp₆.trans hK₅.sp) (rd₆.trans hK₅.rd) (wr₆.trans hK₅.wr), fun hab => ?_, ?_⟩
  · rw [tg.out]
    have hw := (hfl.abs (by rw [hK₀₃.mem]; exact hab)).whole_eq (by
      simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _)
    rw [show ghashInput a ct ++ zeros (padLen (ghashInput a ct).length) = padded a ct from rfl] at hw
    rw [hw, ciph_frame hf₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact L.cs.sub_right (Lay.stSub (by decide))
        · exact L.cw'.sub_right (Lay.wSub (by decide))
        · exact L.cw'.sub_right (Lay.wSub (by decide))
        · exact L.kc.symm) hR,
      blockAt_frame hf₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · simpa using Lay.st_st (st := st) (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide)
            (by decide)
        · simpa using L.st_w (a := 0) (n := 16) (d := 96) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
        · simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 256) (by decide) (.inr ⟨by decide, by decide⟩)
        · simpa using (L.stk_st (a := 0) (n := 16) (by decide)).symm)]
  · exact (t_tagFrame hf₄).trans tg.frame

end

end VG.Proof.AesGcm.Arm

end

end

/-! ### `AesGcm.Arm.StreamCrypt`, which this module and modules that import it used -/

section

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt`

Untrusted: everything here is checked by Lean. Both save our caller's
registers in `scratch` (`W`); `encrypt` XORs the keystream into the data
(`crypt`) and then absorbs the ciphertext into GHASH (`textAbsorb`), and
`decrypt` the other way round (`streamEncrypt_wp`, `streamDecrypt_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32 j0)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

theorem scLay {s₀ : State} (h : streamCryptPre s₀) : Lay (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp := by
  sig_split h
  rename_i hdrop0 hdrop1 dcs hdrop3 dcW hdrop5 dsW hdrop7 hdrop8 hdrop9 hdrop10 bc bs hdrop13 bW fc fs hdrop17
    fW sp8 hdrop20
  clear hdrop0 hdrop1 hdrop3 hdrop5 hdrop7 hdrop8 hdrop9 hdrop10 hdrop13 hdrop17 hdrop20
  clear h
  exact Lay.of fc fs fW sp8 dcs dcW dsW bc bs bW

/-- The rounds, as `r1` holds them. -/
abbrev scR (s₀ : State) : Nat := (s₀.gpr .r1).toNat

/-- After the entry, from `s₀`. -/
structure SC1 (s₀ s₁ : State) : Prop where
  env : Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp (s₀.gpr .r7) (s₀.gpr .r1) s₁
  args : ArgsKeep 7 s₀ s₁
  saved : SavedAt s₁.mem (arg s₀ 6) s₀
  frame : Frame [savedR (arg s₀ 6)] s₀.mem s₁.mem

theorem sc_argsW {s₀ : State} (h : streamCryptPre s₀) : ∀ r ∈ [savedR (arg s₀ 6)], (args s₀ 7).Disjoint r := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, dWA, -⟩ := h
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact (dWA.sub_left (Lay.wSub (by decide))).symm

theorem sc1_wp {s₀ : State} (h : streamCryptPre s₀) {Q : State → Prop} (k : ∀ s₁, SC1 s₀ s₁ → Q s₁) :
    WP isa (.block cryptEntry) s₀ Q := by
  have hA := sc_argsW h
  sig_split h
  rename_i hrd hwr hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 hdrop7 hdrop8 hdrop9 hdrop10 hdrop11 hdrop12 hdrop13
    hdrop14 hdrop15 hdrop16 hdrop17 fW hdrop19 spf
  clear hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 hdrop7 hdrop8 hdrop9 hdrop10 hdrop11 hdrop12 hdrop13 hdrop14
    hdrop15 hdrop16 hdrop17 hdrop19
  clear h
  have hC : Covers [⟨State.addr (s₀.gpr .r0), 256⟩] (s₀.rd ++ s₀.wr) := by
    rw [hrd]; exact covers_of_mem (by simp)
  have hS : Covers [⟨State.addr (s₀.gpr .r2), 80⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have hW : Covers [⟨State.addr (arg s₀ 6), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have ha : ∀ i < 7, InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 (4 * i))) 4 :=
    fun i hi => arg_in (n := 7) hi spf (by rw [hrd]; simp)
  refine entry_ok (off := 24) (by decide) (ha 6 (by decide)) fW hW fun s₁ g12 g rd wr sp sv fr => ?_
  have hk : ArgsKeep 7 s₀ s₁ := (ArgsKeep.refl 7 s₀).frame spf fr hA sp rd wr
  refine WP.of_runBlock ⟨_, by arun [], ?_⟩
  refine k _ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩, ?_, sv, fr⟩
  any_goals (simp [gpr_setReg, g, g12]; done)
  · simp [gpr_setReg, g, g12]; rfl
  · exact sp
  · change Covers _ (s₁.rd ++ s₁.wr); rw [rd, wr]; exact hC
  · change Covers _ s₁.wr; rw [wr]; exact hS
  · change Covers _ s₁.wr; rw [wr]; exact hW
  · exact hk.of_eq rfl rfl rfl rfl

theorem textArgs_run {s₀ s : State} (hk : ArgsKeep 7 s₀ s) (hf : s₀.sp.toNat + 4 * 7 ≤ 2 ^ 32)
    (hin : args s₀ 7 ∈ s₀.rd) :
    ∃ s', runBlock isa textArgs s = some s' ∧
      s'.gpr .r4 = arg s₀ 4 ∧ s'.gpr .r5 = arg s₀ 5 ∧ s'.gpr .r6 = BitVec.ofNat 32 ((arg s₀ 2).toNat % 16) ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain ⟨i4, v4⟩ := hk.at hf hin 4 (by decide) (show 4 * 4 = 16 from rfl)
  obtain ⟨i5, v5⟩ := hk.at hf hin 5 (by decide) (show 4 * 5 = 20 from rfl)
  obtain ⟨i2, v2⟩ := hk.at hf hin 2 (by decide) (show 4 * 2 = 8 from rfl)
  refine ⟨_, by simp only [textArgs]; arun [i4, v4, i5, v5, i2, v2], ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, v4]
  · simp [gpr_setReg, v5]
  · simp only [gpr_setReg, ite_true, v2, and15]
  · intro r a b d; simp [gpr_setReg, a, b, d]
  · exact ⟨rfl, rfl, rfl, rfl⟩

section
variable {s₀ : State} (h : streamCryptPre s₀)
include h

/-- The data, as `crypt` needs it. -/
theorem sc_dataW {k7 : BitVec 32} {s : State} (hk : ArgsKeep 7 s₀ s) :
    DataW (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) s (arg s₀ 4) (arg s₀ 5).toNat := by
  sig_split h
  rename_i hrd hwr hdrop2 dcD hdrop4 dsD hdrop6 hdrop7 dDW hdrop9 hdrop10 hdrop11 hdrop12 bD hdrop14 hdrop15
    hdrop16 fD hdrop18 hdrop19 hdrop20
  clear hdrop2 hdrop4 hdrop6 hdrop7 hdrop9 hdrop10 hdrop11 hdrop12 hdrop14 hdrop15 hdrop16 hdrop18 hdrop19
    hdrop20
  clear h
  have hD : Covers [⟨State.addr (arg s₀ 4), (arg s₀ 5).toNat⟩] s.wr := by
    rw [hk.wr, hwr]; exact covers_of_mem (by simp)
  exact ⟨⟨covers_left hD, (arg s₀ 5).isLt, fD, dsD.symm, dDW, bD⟩, hD, dcD⟩

/-- The input of `crypt`, for `P` bytes of text so far. -/
theorem sc_crIn {k7 : BitVec 32} {s : State} (he : Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) s)
    (hk : ArgsKeep 7 s₀ s) (h4 : s.gpr .r4 = arg s₀ 4) (h5 : s.gpr .r5 = arg s₀ 5)
    (h6 : s.gpr .r6 = BitVec.ofNat 32 ((arg s₀ 2).toNat % 16)) (icb : Block) {P : Nat}
    (hP : (arg s₀ 3 ++ arg s₀ 2).toNat = P) :
    CrIn (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) (scR s₀) icb P (arg s₀ 4) (arg s₀ 5).toNat s :=
  ⟨he, h4, by rw [h5]; simp, by rw [h6, lowTo_mod16 hP], by rw [he.r8]; simp, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    sc_dataW h hk⟩

/-- The stack arguments are apart from what the pieces write. -/
theorem sc_argsCr : ∀ r ∈ crFrame (s₀.gpr .r2) (arg s₀ 6) s₀.sp (arg s₀ 4) (arg s₀ 5).toNat, (args s₀ 7).Disjoint r := by
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, dsA, -, dDA, dWA, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact dDA.symm
  · exact (dsA.sub_left (Lay.stSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (below_args s₀ spf).symm

theorem sc_argsTa : ∀ r ∈ taFrame (s₀.gpr .r2) (arg s₀ 6) s₀.sp, (args s₀ 7).Disjoint r := by
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, dsA, -, -, dWA, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (dsA.sub_left (Lay.stSub (by decide))).symm
  · exact (dsA.sub_left (Lay.stSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (below_args s₀ spf).symm

end

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp)
include L

theorem stp_crFrame {k7 k8 : BitVec 32} {s : State} {D : BitVec 32} {n : Nat} (hd : DataW c st w sp k7 k8 s D n)
    {d k : Nat} (h1 : d + k ≤ 48) :
    ∀ r ∈ crFrame st w sp D n, (⟨State.addr st + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.ok.st.sub_right (Lay.stSub (by omega_arith))).symm
  · exact Lay.st_st (.inl h1) (by omega_arith) (by decide)
  · exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)
  · exact (L.stk_st (by omega_arith)).symm

theorem stp_taFrame {d k : Nat} (hd : d + k ≤ 16 ∨ 48 ≤ d ∧ d + k ≤ 80) :
    ∀ r ∈ taFrame st w sp, (⟨State.addr st + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Lay.st_st (by omega_arith) (by omega_arith) (by decide)
  · exact Lay.st_st (by omega_arith) (by omega_arith) (by decide)
  · exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)
  · exact (L.stk_st (by omega_arith)).symm

theorem stp_saved {d k : Nat} (h1 : d + k ≤ 80) :
    ∀ r ∈ [savedR w], (⟨State.addr st + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact L.st_w h1 (.inr ⟨by decide, by decide⟩)

theorem ctx_saved : ∀ r ∈ [savedR w], (⟨State.addr c, 256⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact L.cw'.sub_right (Lay.wSub (by decide))

theorem ctx_taFrame : ∀ r ∈ taFrame st w sp, (⟨State.addr c, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.kc.symm

omit L in
theorem data_taFrame {s : State} {D : BitVec 32} {n : Nat} (hd : DataOk st w sp s D n) :
    ∀ r ∈ taFrame st w sp, (⟨State.addr D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hd.st.sub_right (Lay.stSub (by decide))
  · exact hd.st.sub_right (Lay.stSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))
  · exact hd.stk.symm

omit L in
theorem data_saved {s : State} {D : BitVec 32} {n : Nat} (hd : DataOk st w sp s D n) :
    ∀ r ∈ [savedR w], (⟨State.addr D, n⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact hd.w.sub_right (Lay.wSub (by decide))

theorem saved_taFrame : ∀ r ∈ taFrame st w sp, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

omit L in
/-- `ciphOf` is `ctxCiph`, and a frame apart from the context keeps it. -/
theorem ciph_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨State.addr c, 256⟩ : Region).Disjoint r) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    ciphOf m' (State.addr c) R = ctxCiph m (State.addr c) R := ciph_frame hf hd hR

omit L in
theorem ctxH_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨State.addr c, 256⟩ : Region).Disjoint r) :
    blockAt m' (State.addr c + BitVec.ofNat 64 240) = ctxH m (State.addr c) := by
  rw [ctxH_eq, blockAt_frame hf (fun r hr => (hd r hr).sub_left (Lay.ctxSub (by decide)))]

end

/-- What `encrypt` (or `decrypt`) does, for the counter block `icb`, the
additional data `a` and the text `ct` so far (only their lengths matter to
the code). -/
structure EncOut (s₀ : State) (icb : Block) (a ct : List Byte) (dec : Bool) (s : State) : Prop where
  ctr : Ctr s₀.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48) (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (scR s₀)) icb ct.length →
    Ctr s.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48) (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (scR s₀)) icb (ct.length + (arg s₀ 5).toNat)
  out : Ctr s₀.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48) (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (scR s₀)) icb ct.length →
    bytesAt s.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat =
      xorKs (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (scR s₀)) icb ct.length
        (bytesAt s₀.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat)
  abs : Ctr s₀.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48) (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (scR s₀)) icb ct.length →
    Absorbed s₀.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 16) (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 32)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (ghashInput a ct) →
    Absorbed s.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 16) (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 32)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (ghashInput a (ct ++ if dec then bytesAt s₀.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat else
        xorKs (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (scR s₀)) icb ct.length
          (bytesAt s₀.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat)))
  j : blockAt s.mem (State.addr (s₀.gpr .r2)) = blockAt s₀.mem (State.addr (s₀.gpr .r2))

theorem enc_run [VG.Proof.Gcm.Arm.GhashLaw] {s₀ : State} (h : streamCryptPre s₀) (icb : Block) {a ct : List Byte}
    (ha : a.length % 16 = (arg s₀ 0).toNat % 16) (hP : (arg s₀ 3 ++ arg s₀ 2).toNat = ct.length) :
    WP isa streamEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ EncOut s₀ icb a ct false s' := by
  have L := scLay h
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have fW := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ 7 ∈ s₀.rd := by rw [h.1]; simp
  refine WP.seq (WP.block_append (sc1_wp h fun s₁ h1 => ?_))
  obtain ⟨s₂, run₂, h4, h5, h6, hg₂, hK₂⟩ := textArgs_run h1.args spf hin
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have he₂ := h1.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hK₂.sp hK₂.rd hK₂.wr
  have hk₂ := h1.args.of_eq hK₂.mem hK₂.sp hK₂.rd hK₂.wr
  have ci := sc_crIn h he₂ hk₂ h4 h5 h6 icb hP
  have hd₂ := ci.data
  refine WP.seq (WP.mono (WP.with_rdwr (crypt_ok L ci)) fun s₃ hh => ?_)
  obtain ⟨co, rd₃, wr₃, sp₃⟩ := hh
  have hk₃ := hk₂.frame spf co.frame (sc_argsCr h) sp₃ rd₃ wr₃
  have hd₃ := (sc_dataW (k7 := s₀.gpr .r7) h hk₃).ok
  have f₂ : Frame [savedR (arg s₀ 6)] s₀.mem s₂.mem := by rw [hK₂.mem]; exact h1.frame
  have hH₃ : blockAt s₃.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0)) := by
    rw [blockAt_frame co.frame (fun r hr => (ctx_crFrame L hd₂ r hr).sub_left (Lay.ctxSub (by decide))),
      ctxH_keep f₂ (ctx_saved L)]
  refine WP.seq (WP.mono (WP.with_rdwr (textAbsorb_ok L co.env hk₃ spf hin (sc_argsTa h) hH₃ hd₃ ha hP))
    fun s₄ hh => ?_)
  obtain ⟨ta, rd₄, wr₄, sp₄⟩ := hh
  have sv₄ : SavedAt s₄.mem (arg s₀ 6) s₀ :=
    (((hK₂.mem ▸ h1.saved : SavedAt s₂.mem (arg s₀ 6) s₀)).frame co.frame (saved_crFrame L hd₂)).frame ta.frame
      (saved_taFrame L)
  refine WP.mono (restore_ok ta.env.r11 fW (covers_left ta.env.perm.w) sv₄ ta.env.sp) fun s' hh => ⟨hh.1, ?_⟩
  have hm : s'.mem = s₄.mem := hh.2.1
  have hc : ciphOf s₂.mem (State.addr (s₀.gpr .r0)) (scR s₀) = ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (scR s₀) :=
    ciph_keep f₂ (ctx_saved L) hR
  have ctr₂ : ∀ {P : Nat}, Ctr s₀.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48)
      (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (scR s₀)) icb P →
      Ctr s₂.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48)
      (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64) (ciphOf s₂.mem (State.addr (s₀.gpr .r0)) (scR s₀)) icb P :=
    fun hc₀ => by
      rw [hc]
      exact hc₀.congr (blockAt_frame f₂ (stp_saved L (by decide))) (blockAt_frame f₂ (stp_saved L (by decide)))
  have dat₂ : bytesAt s₂.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat =
      bytesAt s₀.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat :=
    bytesAt_frame f₂ (data_saved hd₂.ok) (by have := hd₂.ok.lt; omega_arith)
  have out₃ : Ctr s₀.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48)
      (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (scR s₀)) icb ct.length →
      bytesAt s₃.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat =
        xorKs (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (scR s₀)) icb ct.length
          (bytesAt s₀.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat) := fun hc₀ => by
    rw [co.out (ctr₂ hc₀), hc, dat₂]
  refine ⟨fun hc₀ => ?_, fun hc₀ => ?_, fun hc₀ hab => ?_, ?_⟩
  · rw [hm]
    have := co.ctr (ctr₂ hc₀)
    rw [hc] at this
    exact this.congr (blockAt_frame ta.frame (stp_taFrame L (.inr ⟨by decide, by decide⟩)))
      (blockAt_frame ta.frame (stp_taFrame L (.inr ⟨by decide, by decide⟩)))
  · rw [hm, bytesAt_frame ta.frame (data_taFrame hd₃) (by have := hd₃.lt; omega_arith)]
    exact out₃ hc₀
  · rw [hm]
    have hb := Nat.mod_lt (ghashInput a ct).length (show 16 > 0 by decide)
    have hab₃ : Absorbed s₃.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 16)
        (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 32) (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (ghashInput a ct) :=
      (hab.congr (blockAt_frame f₂ (stp_saved L (by decide)))
        (bytesAt_frame f₂ (stp_saved L (by omega_arith)) (by omega_arith))).congr
        (blockAt_frame co.frame (stp_crFrame L hd₂ (by decide)))
        (bytesAt_frame co.frame (stp_crFrame L hd₂ (by omega_arith)) (by omega_arith))
    have := ta.abs hab₃
    rw [out₃ hc₀] at this
    exact this
  · rw [hm, blockAt_frame ta.frame (by simpa using stp_taFrame L (d := 0) (k := 16) (.inl (by decide))),
      blockAt_frame co.frame (by simpa using stp_crFrame L hd₂ (d := 0) (k := 16) (by decide)),
      blockAt_frame f₂ (by simpa using stp_saved L (d := 0) (k := 16) (by decide))]

theorem dec_run [VG.Proof.Gcm.Arm.GhashLaw] {s₀ : State} (h : streamCryptPre s₀) (icb : Block) {a ct : List Byte}
    (ha : a.length % 16 = (arg s₀ 0).toNat % 16) (hP : (arg s₀ 3 ++ arg s₀ 2).toNat = ct.length) :
    WP isa streamDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ EncOut s₀ icb a ct true s' := by
  have L := scLay h
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have fW := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ 7 ∈ s₀.rd := by rw [h.1]; simp
  refine WP.seq (sc1_wp h fun s₁ h1 => ?_)
  have hd₁ := (sc_dataW (k7 := s₀.gpr .r7) h h1.args).ok
  have hH₁ : blockAt s₁.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0)) :=
    ctxH_keep h1.frame (ctx_saved L)
  refine WP.seq (WP.mono (WP.with_rdwr (textAbsorb_ok L h1.env h1.args spf hin (sc_argsTa h) hH₁ hd₁ ha hP))
    fun s₂ hh => ?_)
  obtain ⟨ta, rd₂, wr₂, sp₂⟩ := hh
  obtain ⟨s₃, run₃, h4, h5, h6, hg₃, hK₃⟩ := textArgs_run ta.args spf hin
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ := ta.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide) (by decide)) hK₃.sp hK₃.rd hK₃.wr
  have hk₃ := ta.args.of_eq hK₃.mem hK₃.sp hK₃.rd hK₃.wr
  have ci := sc_crIn h he₃ hk₃ h4 h5 h6 icb hP
  have hd₃ := ci.data
  refine WP.seq (WP.mono (WP.with_rdwr (crypt_ok L ci)) fun s₄ hh => ?_)
  obtain ⟨co, rd₄, wr₄, sp₄⟩ := hh
  have f₃ : Frame (taFrame (s₀.gpr .r2) (arg s₀ 6) s₀.sp) s₁.mem s₃.mem := by rw [hK₃.mem]; exact ta.frame
  have sv₄ : SavedAt s₄.mem (arg s₀ 6) s₀ :=
    ((h1.saved.frame f₃ (saved_taFrame L))).frame co.frame (saved_crFrame L hd₃)
  refine WP.mono (restore_ok co.env.r11 fW (covers_left co.env.perm.w) sv₄ co.env.sp) fun s' hh => ⟨hh.1, ?_⟩
  have hm : s'.mem = s₄.mem := hh.2.1
  have hc : ciphOf s₃.mem (State.addr (s₀.gpr .r0)) (scR s₀) = ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (scR s₀) := by
    rw [ciph_keep f₃ (ctx_taFrame L) hR]; exact ciph_keep h1.frame (ctx_saved L) hR
  have ctr₃ : ∀ {P : Nat}, Ctr s₀.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48)
      (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (scR s₀)) icb P →
      Ctr s₃.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48)
      (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64) (ciphOf s₃.mem (State.addr (s₀.gpr .r0)) (scR s₀)) icb P :=
    fun hc₀ => by
      rw [hc]
      exact (hc₀.congr (blockAt_frame h1.frame (stp_saved L (by decide)))
        (blockAt_frame h1.frame (stp_saved L (by decide)))).congr
        (blockAt_frame f₃ (stp_taFrame L (.inr ⟨by decide, by decide⟩)))
        (blockAt_frame f₃ (stp_taFrame L (.inr ⟨by decide, by decide⟩)))
  have dat₁ : bytesAt s₁.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat =
      bytesAt s₀.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat :=
    bytesAt_frame h1.frame (data_saved hd₁) (by have := hd₁.lt; omega_arith)
  have dat₃ : bytesAt s₃.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat =
      bytesAt s₀.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat := by
    rw [bytesAt_frame f₃ (data_taFrame hd₁) (by have := hd₁.lt; omega_arith), dat₁]
  refine ⟨fun hc₀ => ?_, fun hc₀ => ?_, fun hc₀ hab => ?_, ?_⟩
  · rw [hm]
    have := co.ctr (ctr₃ hc₀)
    rwa [hc] at this
  · rw [hm, co.out (ctr₃ hc₀), hc, dat₃]
  · rw [hm]
    have hb := Nat.mod_lt (ghashInput a ct).length (show 16 > 0 by decide)
    have hab₂ := ta.abs ((hab.congr (blockAt_frame h1.frame (stp_saved L (by decide)))
        (bytesAt_frame h1.frame (stp_saved L (by omega_arith)) (by omega_arith))))
    rw [dat₁] at hab₂
    rw [← hK₃.mem] at hab₂
    have hb' := Nat.mod_lt (ghashInput a (ct ++ bytesAt s₀.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat)).length
      (show 16 > 0 by decide)
    exact hab₂.congr (blockAt_frame co.frame (stp_crFrame L hd₃ (by decide)))
      (bytesAt_frame co.frame (stp_crFrame L hd₃ (by omega_arith)) (by omega_arith))
  · rw [hm, blockAt_frame co.frame (by simpa using stp_crFrame L hd₃ (d := 0) (k := 16) (by decide)),
      blockAt_frame f₃ (by simpa using stp_taFrame L (d := 0) (k := 16) (.inl (by decide))),
      blockAt_frame h1.frame (by simpa using stp_saved L (d := 0) (k := 16) (by decide))]

theorem streamEncrypt_wp [VG.Proof.Gcm.Arm.GhashLaw] {s₀ : State} (h : streamEncryptArm.pre s₀) :
    WP isa streamEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ streamEncryptArm.post s₀ s' := by
  have h' : streamCryptPre s₀ := h
  have h₀ := enc_run h' 0 (a := List.replicate ((arg s₀ 0).toNat % 16) 0)
    (ct := List.replicate (arg s₀ 3 ++ arg s₀ 2).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte × List Byte =>
      let ciph := ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat
      let hh := ctxH s₀.mem (State.addr (s₀.gpr .r0))
      StreamRepr s₀.mem (State.addr (s₀.gpr .r2)) ciph hh i.1 i.2.1 (gctr ciph (inc32 (j0 hh i.1)) i.2.2) ∧
        arg64 s₀ 0 = BitVec.ofNat 64 i.2.1.length ∧ (arg64 s₀ 2).toNat = i.2.2.length)
    fun i hi => enc_run h' (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) i.1)) (a := i.2.1)
      (ct := gctr (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
        (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) i.1)) i.2.2)
      (low_mod16 hi.2.1).symm (by rw [Proof.Gcm.length_gctr]; exact hi.2.2))
    fun s' hh => ⟨hh.1, fun iv a p hs hl hp => ?_⟩
  obtain ⟨-, eo⟩ := hh.2 ⟨iv, a, p⟩ ⟨hs, hl, hp⟩
  rw [Proof.Gcm.streamRepr_iff] at hs
  obtain ⟨hj, hab, hct⟩ := hs
  simp only [ofNat_lit] at hab hct
  have hl' : (gctr (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
      (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv)) p).length = p.length := Proof.Gcm.length_gctr _ _ _
  have eo₁ := eo.ctr hct
  have eo₂ := eo.out hct
  have eo₃ := eo.abs hct hab
  simp only [Bool.false_eq_true, ite_false] at eo₃
  rw [hl'] at eo₁ eo₂ eo₃
  rw [← Proof.Gcm.gctr_append] at eo₃
  refine ⟨?_, ?_⟩
  · rw [Proof.Gcm.streamRepr_iff]
    simp only [ofNat_lit]
    refine ⟨eo.j.trans hj, eo₃, ?_⟩
    rw [Proof.Gcm.length_gctr, List.length_append, length_bytesAt]; exact eo₁
  · rw [eo₂, Proof.Gcm.gctr_append, List.drop_left' hl']

theorem streamDecrypt_wp [VG.Proof.Gcm.Arm.GhashLaw] {s₀ : State} (h : streamDecryptArm.pre s₀) :
    WP isa streamDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ streamDecryptArm.post s₀ s' := by
  have h' : streamCryptPre s₀ := h
  have h₀ := dec_run h' 0 (a := List.replicate ((arg s₀ 0).toNat % 16) 0)
    (ct := List.replicate (arg s₀ 3 ++ arg s₀ 2).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte × List Byte =>
      let ciph := ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat
      let hh := ctxH s₀.mem (State.addr (s₀.gpr .r0))
      StreamRepr s₀.mem (State.addr (s₀.gpr .r2)) ciph hh i.1 i.2.1 i.2.2 ∧
        arg64 s₀ 0 = BitVec.ofNat 64 i.2.1.length ∧ (arg64 s₀ 2).toNat = i.2.2.length)
    fun i hi => dec_run h' (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) i.1)) (a := i.2.1) (ct := i.2.2)
      (low_mod16 hi.2.1).symm hi.2.2)
    fun s' hh => ⟨hh.1, fun iv a c hs hl hp => ?_⟩
  obtain ⟨-, eo⟩ := hh.2 ⟨iv, a, c⟩ ⟨hs, hl, hp⟩
  rw [Proof.Gcm.streamRepr_iff] at hs
  obtain ⟨hj, hab, hct⟩ := hs
  simp only [ofNat_lit] at hab hct
  have eo₁ := eo.ctr hct
  have eo₂ := eo.out hct
  have eo₃ := eo.abs hct hab
  simp only [ite_true] at eo₃
  refine ⟨?_, ?_⟩
  · rw [Proof.Gcm.streamRepr_iff]
    simp only [ofNat_lit]
    refine ⟨eo.j.trans hj, eo₃, ?_⟩
    rw [List.length_append, length_bytesAt]; exact eo₁
  · rw [eo₂, Proof.Gcm.gctr_append, List.drop_left' (Proof.Gcm.length_gctr _ _ _)]

end VG.Proof.AesGcm.Arm

end

end

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_stream_finish`

Untrusted: everything here is checked by Lean. `stream_finish` saves our
caller's registers in `work` (`W`), writes the tag to its first 16 bytes
with `finTag` and copies it to `tag` (`tagOut_ok`, `streamFinish_wp`). The
entry is shared with `stream_verify` (`fin1_wp`, for `n` words of stack
arguments, `work` the `wi`-th).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput fullTag)
open VG.Proof.Gcm (Absorbed lensBlock)
open VG.Proof.Cmac (store4)

theorem lensBlock_mod (L c : Nat) : lensBlock (L % 2 ^ 64) c = lensBlock L c := by
  simp only [lensBlock]
  rw [← Proof.Gcm.be64_mod (8 * (L % 2 ^ 64)), ← Proof.Gcm.be64_mod (8 * L)]
  congr 2; omega_using []

theorem toNat_of_eq {x : BitVec 64} {L : Nat} (h : x = BitVec.ofNat 64 L) : x.toNat = L % 2 ^ 64 := by
  rw [h, BitVec.toNat_ofNat]

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp)
include L

/-- `tagOut`: the tag at `W` copied to `T`, the stack argument at `[sp + 16]`. -/
theorem tagOut_ok {s : State} (he : Env c st w sp k7 k8 s) {T : BitVec 32}
    (hTi : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 16)) 4)
    (hTv : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 16)) 32 = T)
    (hTw : Covers [⟨State.addr T, 16⟩] s.wr) (hTf : T.toNat + 16 ≤ 2 ^ 32)
    (hTd : (⟨State.addr T, 16⟩ : Region).Disjoint ⟨State.addr w, 16⟩) :
    ∃ s', runBlock isa tagOut s = some s' ∧ bytesAt s'.mem (State.addr T) 16 = bytesAt s.mem (State.addr w) 16 ∧
      Frame [⟨State.addr T, 16⟩] s.mem s'.mem ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h11 := he.r11
  have eW : ∀ d, d < 2560 → State.addr (w + BitVec.ofNat 32 d) = State.addr w + BitVec.ofNat 64 d :=
    fun d hd => L.wA hd
  have eT : ∀ d, d < 16 → State.addr (T + BitVec.ofNat 32 d) = State.addr T + BitVec.ofNat 64 d :=
    fun d hd => addr_add (by omega_using [hTf, hd])
  have r₀ := he.perm.wR (show 0 + 4 ≤ 2560 by decide)
  have r₁ := he.perm.wR (show 4 + 4 ≤ 2560 by decide)
  have r₂ := he.perm.wR (show 8 + 4 ≤ 2560 by decide)
  have r₃ := he.perm.wR (show 12 + 4 ≤ 2560 by decide)
  have w₀ := in_off hTw (show 0 + 4 ≤ 16 by decide) (by decide)
  have w₁ := in_off hTw (show 4 + 4 ≤ 16 by decide) (by decide)
  have w₂ := in_off hTw (show 8 + 4 ≤ 16 by decide) (by decide)
  have w₃ := in_off hTw (show 12 + 4 ≤ 16 by decide) (by decide)
  have q : ∀ (m : Mem) (a b : Nat) (v : BitVec 32), a + 4 ≤ 16 → b + 4 ≤ 16 →
      (m.writeW (State.addr T + BitVec.ofNat 64 b) v).readW (State.addr w + BitVec.ofNat 64 a) 32 =
        m.readW (State.addr w + BitVec.ofNat 64 a) 32 := fun m a b v ha hb =>
    sepW (m := m) ((hTd.symm.sub_left (Offset.sub_base _ ha)).sub_right (Offset.sub_base _ hb))
  have p₁ := fun m v => q m 4 0 v (by decide) (by decide)
  have p₂ := fun m v => q m 8 0 v (by decide) (by decide)
  have p₃ := fun m v => q m 8 4 v (by decide) (by decide)
  have p₄ := fun m v => q m 12 0 v (by decide) (by decide)
  have p₅ := fun m v => q m 12 4 v (by decide) (by decide)
  have p₆ := fun m v => q m 12 8 v (by decide) (by decide)
  obtain ⟨s', run, hm, hg, hk⟩ : ∃ s', runBlock isa tagOut s = some s' ∧
      s'.mem = store4 s.mem (State.addr T + BitVec.ofNat 64 0) (s.mem.readW (State.addr w + BitVec.ofNat 64 0) 32)
        (s.mem.readW (State.addr w + BitVec.ofNat 64 4) 32) (s.mem.readW (State.addr w + BitVec.ofNat 64 8) 32)
        (s.mem.readW (State.addr w + BitVec.ofNat 64 12) 32) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    refine ⟨_, by simp only [tagOut]; arun [hTi, hTv, h11, eW, eT, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, p₁, p₂, p₃, p₄,
      p₅, p₆], ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc]
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl⟩
  simp only [add_ofNat_zero] at hm
  refine ⟨s', run, by rw [hm]; exact bytesAt_copy4 _ _ _, by rw [hm]; exact Cmac.frame_store4 _ _ _ _ _, hg, hk.1,
    hk.2.1, hk.2.2⟩

end

section
variable {n wi : Nat}

theorem finLay {s₀ : State} (h : finPre n wi s₀) : Lay (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ wi) s₀.sp := by
  obtain ⟨-, -, dcs, dcW, dsW, -, -, bc, bs, bW, fc, fs, fW, sp8, -, -⟩ := h
  exact Lay.of fc fs fW sp8 dcs dcW dsW bc bs bW

/-- After the entry, from `s₀`. -/
structure SF1 (n wi : Nat) (s₀ s₁ : State) : Prop where
  env : Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ wi) s₀.sp (s₀.gpr .r7) (s₀.gpr .r1) s₁
  args : ArgsKeep n s₀ s₁
  saved : SavedAt s₁.mem (arg s₀ wi) s₀
  frame : Frame [savedR (arg s₀ wi)] s₀.mem s₁.mem

theorem fin1_wp {s₀ : State} (h : finPre n wi s₀) (hn : wi < n) (hwi : 4 * wi < 4096) {Q : State → Prop}
    (k : ∀ s₁, SF1 n wi s₀ s₁ → Q s₁) : WP isa (.block (finEntry (4 * wi))) s₀ Q := by
  obtain ⟨⟨hc, hin⟩, ⟨hs, hw, -⟩, -, -, -, -, dWA, -, -, -, -, -, fW, -, spf, -⟩ := h
  have hA : ∀ r ∈ [savedR (arg s₀ wi)], (args s₀ n).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (dWA.sub_left (Lay.wSub (by decide))).symm
  have hC : Covers [⟨State.addr (s₀.gpr .r0), 256⟩] (s₀.rd ++ s₀.wr) :=
    covers_of_mem (List.mem_append_left _ hc)
  have hS : Covers [⟨State.addr (s₀.gpr .r2), 80⟩] s₀.wr := covers_of_mem hs
  have hW : Covers [⟨State.addr (arg s₀ wi), 2560⟩] s₀.wr := covers_of_mem hw
  have ha : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 (4 * wi))) 4 :=
    arg_in (n := n) hn spf hin
  refine entry_ok (off := 4 * wi) hwi ha fW hW fun s₁ g12 g rd wr sp sv fr => ?_
  have hk : ArgsKeep n s₀ s₁ := (ArgsKeep.refl n s₀).frame spf fr hA sp rd wr
  refine WP.of_runBlock ⟨_, by arun [], ?_⟩
  refine k _ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩, ?_, sv, fr⟩
  any_goals (simp [gpr_setReg, g, g12]; done)
  · simp [gpr_setReg, g, g12]; rfl
  · exact sp
  · change Covers _ (s₁.rd ++ s₁.wr); rw [rd, wr]; exact hC
  · change Covers _ s₁.wr; rw [wr]; exact hS
  · change Covers _ s₁.wr; rw [wr]; exact hW
  · exact hk.of_eq rfl rfl rfl rfl

theorem fin_argsTag {s₀ : State} (h : finPre n wi s₀) {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ tagFrame (s₀.gpr .r2) (arg s₀ wi) s₀.sp o, (args s₀ n).Disjoint r := by
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, dsA, dWA, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (dsA.sub_left (Region.sub_prefix (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by omega_using [ho]))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (below_args s₀ spf).symm

/-- The tag, from the entry. -/
theorem fin_tag [VG.Proof.Gcm.Arm.GhashLaw] {s₀ s₁ : State} (h : finPre n wi s₀) (hn : 4 ≤ n) (h1 : SF1 n wi s₀ s₁) {o : Nat}
    (ho : o = 0 ∨ o = 112) {a ct : List Byte} (ha : a.length % 16 = (arg s₀ 0).toNat % 16)
    (hP : (arg s₀ 3 ++ arg s₀ 2).toNat = ct.length) :
    WP isa (finTag o) s₁ (FinOut (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ wi) s₀.sp (s₀.gpr .r1) n s₀ o (s₀.gpr .r1).toNat
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) a ct s₁.mem) := by
  have L := finLay h
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact finTag_ok L hn ho h1.env h1.args spf h.1.2 (fin_argsTag h ho) (by simp) hR
    (ctxH_keep h1.frame (ctx_saved L)) ha hP

/-- The tag, for a state that represents `a` and `ct`, from a memory `m₀` that
differs from the entry's only apart from the context and the state. -/
theorem fin_out {s₀ s : State} {m₀ : Mem} (h : finPre n wi s₀) {rs : List Region} (hf₀ : Frame rs s₀.mem m₀)
    (hdc : ∀ r ∈ rs, (⟨State.addr (s₀.gpr .r0), 256⟩ : Region).Disjoint r)
    (hds : ∀ r ∈ rs, (⟨State.addr (s₀.gpr .r2), 80⟩ : Region).Disjoint r) {o : Nat} {iv a ct : List Byte}
    (hf : FinOut (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ wi) s₀.sp (s₀.gpr .r1) n s₀ o (s₀.gpr .r1).toNat
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) a ct m₀ s)
    (hs : StreamRepr s₀.mem (State.addr (s₀.gpr .r2)) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct) (hl : arg64 s₀ 0 = BitVec.ofNat 64 a.length) :
    bytesAt s.mem (State.addr (arg s₀ wi) + BitVec.ofNat 64 o) 16 =
      fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat) (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
        iv a ct := by
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [Proof.Gcm.streamRepr_iff] at hs
  obtain ⟨hj, hab, -⟩ := hs
  simp only [ofNat_lit] at hab hj
  have hb := Nat.mod_lt (ghashInput a ct).length (show 16 > 0 by decide)
  have dS : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ rs, (⟨State.addr (s₀.gpr .r2) + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun hd r hr => (hds r hr).sub_left (Lay.stSub hd)
  rw [hf.out (hab.congr (blockAt_frame hf₀ (dS (by decide)))
      (bytesAt_frame hf₀ (dS (by omega_using [])) (by omega_using []))),
    ciph_keep hf₀ hdc hR,
    blockAt_frame hf₀ (by simpa using dS (d := 0) (k := 16) (by decide)), hj,
    toNat_of_eq hl, lensBlock_mod, Proof.Gcm.fullTag_eq]

end

theorem streamFinish_wp [VG.Proof.Gcm.Arm.GhashLaw] {s₀ : State} (h : streamFinishArm.pre s₀) :
    WP isa streamFinish s₀ fun s' => abiPreserved s₀ s' ∧ streamFinishArm.post s₀ s' := by
  have h' : finPre 6 5 s₀ := streamFinishPreArm.fin h
  have L := finLay h'
  have fW := h'.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hrd, hwr, -, -, -, -, -, -, tW, tA, -, -, -, -, -, -, -, fT, -⟩ := h
  have hin : args s₀ 6 ∈ s₀.rd := h'.1.2
  have hTw : Covers [⟨State.addr (arg s₀ 4), 16⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have dW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨State.addr (arg s₀ 4), 16⟩ : Region).Disjoint
      ⟨State.addr (arg s₀ 5) + BitVec.ofNat 64 d, k⟩ := fun hd => tW.sub_right (Lay.wSub hd)
  have run : ∀ {a ct : List Byte}, a.length % 16 = (arg s₀ 0).toNat % 16 → (arg s₀ 3 ++ arg s₀ 2).toNat = ct.length →
      WP isa streamFinish s₀ fun s' => abiPreserved s₀ s' ∧ ∀ iv,
        StreamRepr s₀.mem (State.addr (s₀.gpr .r2)) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
          (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct → arg64 s₀ 0 = BitVec.ofNat 64 a.length →
        bytesAt s'.mem (State.addr (arg s₀ 4)) 16 =
          fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
            (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct := fun ha hP =>
    WP.seq (fin1_wp (wi := 5) h' (by decide) (by decide) fun s₁ h1 =>
      WP.seq (WP.mono (fin_tag h' (by decide) h1 (.inl rfl) ha hP) fun s₂ hf => by
        obtain ⟨k7, he⟩ := hf.env
        obtain ⟨i4, v4⟩ := hf.args.at spf hin 4 (by decide) (show 4 * 4 = 16 from rfl)
        obtain ⟨s₃, run₃, hb₃, hf₃, g₃, rd₃, wr₃, sp₃⟩ := tagOut_ok L he i4 v4
          (by rw [hf.args.wr]; exact hTw) fT (by simpa using dW (d := 0) (k := 16) (by decide))
        refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
        have he₃ := he.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide)) sp₃ rd₃ wr₃
        have sv₂ := h1.saved.frame hf.frame (saved_tagFrame L (.inl rfl))
        exact WP.mono (restore_ok he₃.r11 fW (covers_left he₃.perm.w)
          (sv₂.frame hf₃ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact (dW (by decide)).symm)) he₃.sp)
          fun s' hh => ⟨hh.1, fun iv hs hl => by
            have := fin_out h' h1.frame (ctx_saved L) (fun r hr => by
              simp only [List.mem_singleton] at hr; subst hr; simpa using L.st_w (a := 0) (n := 80) (d := 128) (k := 36) (by decide) (.inr ⟨by decide, by decide⟩)) hf hs hl
            rw [add_ofNat_zero] at this
            rw [hh.2.1, hb₃, this]⟩))
  have h₀ := run (a := List.replicate ((arg s₀ 0).toNat % 16) 0)
    (ct := List.replicate (arg s₀ 3 ++ arg s₀ 2).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte × List Byte =>
      StreamRepr s₀.mem (State.addr (s₀.gpr .r2)) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
          (ctxH s₀.mem (State.addr (s₀.gpr .r0))) i.1 i.2.1 i.2.2 ∧
        arg64 s₀ 0 = BitVec.ofNat 64 i.2.1.length ∧ (arg64 s₀ 2).toNat = i.2.2.length)
    fun i hi => WP.mono (run (a := i.2.1) (ct := i.2.2) (low_mod16 hi.2.1).symm hi.2.2)
      fun s' hh => hh.2 i.1 hi.1 hi.2.1)
    fun s' hh => ⟨hh.1, fun iv a c hs hl hp => hh.2 ⟨iv, a, c⟩ ⟨hs, hl, hp⟩⟩

end VG.Proof.AesGcm.Arm
