import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCorrect
import VerifiedGarbage.Proof.RsaPkcs1Sig.Recover

/-!
# `vg_rsa_pkcs1_recover` on x86-64: correctness

After the call (`afterPub_ok`): the encoding of the last `out_len` bytes of
`EM₁` into `EM₂` (`encode_ok`), their comparison (`compare_ok`) and the
release of those bytes to `out`, or zeros, which is BoringSSL's recovery
(`recover_eq_recoverEnc`). With the length check, the frame's push, the call
(`pub_call`) and the pop: `code_correct`.
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64.Rec

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Recover
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (frameBytes oEM1 oEM2 sp arg arg0 lea test0 ret0 cmpArgs)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64 VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.X86_64.Ver (fb kb stkR scrR fb_eq fb_sub8 toNat_off frame_sub below_sub kb_sub
  ret_disjoint outside_frame stackArgAddr_fb stackArgAddr_eq ea_sp word_wo allocState_gpr arg_ea
  stackArg_entry stackArgAddr_entry callEntry_frame sub_refl slot_keep test0_ok result_ok bytesAt_eq_iff setWidth_byte_eq_zero word_wo0 word_self0 freed wp_alloc arg0_ea)
open Spec.RsaPkcs1Sig

/-! ## Memory in the frame and in `out` -/

/-- `Env` past changes of the registers but `rsp`, and of memory in the
frame from `EM₁` on or in `out`. -/
theorem Env.of {s t u : State} (he : Env s t) (hp : PreR s) (hsp : u.gpr .rsp = t.gpr .rsp) (hrd : u.rd = t.rd)
    (hwr : u.wr = t.wr) {rs : List Region} (hf : Frame rs t.mem u.mem)
    (hs : ∀ r ∈ rs, (∃ d n, r = ⟨off (fb s) d, n⟩ ∧ oEM1 ≤ d ∧ d + n ≤ frameBytes) ∨ r = outR s) : Env s u := by
  have hsl : ∀ {d}, 32 ≤ d → d + 8 ≤ oEM1 → word u.mem (fb s) d = word t.mem (fb s) d := fun hd hd' =>
    slot_keep hf fun r hr => by
      rcases hs r hr with ⟨d', n, rfl, h₁, h₂⟩ | rfl
      · exact Offset.disjoint _ (.inl (by omega)) (by unfold frameBytes at *; omega)
          (by unfold frameBytes at *; omega)
      · exact (hp.dKo.sub_left (frame_sub s (by unfold oEM1 frameBytes at *; omega)))
  refine ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr, frame_call he.mem hf fun r hr => ?_,
    (hsl (by decide) (by decide)).trans he.sOut, (hsl (by decide) (by decide)).trans he.sOl,
    (hsl (by decide) (by decide)).trans he.sN, (hsl (by decide) (by decide)).trans he.sK,
    (hsl (by decide) (by decide)).trans he.sE, (hsl (by decide) (by decide)).trans he.sEl⟩
  rcases hs r hr with ⟨d, n, rfl, -, h₂⟩ | rfl
  · exact .inl (frame_sub s h₂)
  · exact .inr (.inl (sub_refl _))

/-- `Env` past changes of the registers but `rsp`. -/
theorem Env.regs {s t u : State} (he : Env s t) (hsp : u.gpr .rsp = t.gpr .rsp) (hm : u.mem = t.mem)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) : Env s u :=
  ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr, hm ▸ he.mem, hm ▸ he.sOut, hm ▸ he.sOl, hm ▸ he.sN,
    hm ▸ he.sK, hm ▸ he.sE, hm ▸ he.sEl⟩

theorem frame_bytes' {s : State} {d n : Nat} (hp : PreR s) (h : d + n ≤ frameBytes) :
    ∀ i < n, InRegions (⟨fb s, frameBytes⟩ :: s.wr) (off (fb s) d + BitVec.ofNat 64 i) 1 := by
  have := fb_toNat hp
  intro i hi
  refine ⟨_, List.mem_cons_self .., ?_⟩
  rw [show off (fb s) d + BitVec.ofNat 64 i = off (fb s) (d + i) from off_off _ _ _]
  exact Offset.contains_base _ (by omega) (by unfold frameBytes at *; omega)

/-- `out` is writable. -/
theorem out_wr {s : State} {wr : List Region} (hwr : outR s ∈ wr) :
    ∀ i < (s.gpr .rsi).toNat, InRegions wr (s.gpr .rdi + BitVec.ofNat 64 i) 1 := fun i hi =>
  ⟨_, hwr, Offset.contains_base _ (by omega) (by omega)⟩

/-! ## Zeros to `out` -/

/-- Zeros to the `n` bytes at `rdi`. -/
theorem zeroOut_ok {u : State} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64) (hsi : u.gpr .rsi = BitVec.ofNat 64 n)
    (hw : ∀ i < n, InRegions u.wr (u.gpr .rdi + BitVec.ofNat 64 i) 1) :
    WP isa zeroOut u fun t => Keep [.r8, .r10, .rax, .rdi, .rsi, .r9, .r11] u t ∧
      t.mem = writeBytes u.mem (u.gpr .rdi) (List.replicate n 0) ∧ t.gpr .rax = 0 := by
  unfold zeroOut
  refine WP.seq (WP.mono (WP.keep [.r8, .r10, .rax] (Q := fun t => t.mem = u.mem ∧ t.gpr .r8 = u.gpr .rdi ∧
      t.gpr .r10 = BitVec.ofNat 64 n ∧ t.gpr .rax = 0) (by xrun [hsi]) rfl) fun u₁ ⟨⟨hm₁, h8, h10, hax⟩, k₁⟩ => ?_)
  have hdi : u₁.gpr .rdi = u₁.gpr .r8 := by rw [k₁.gpr (by decide), h8]
  have hb : Buf u₁ n := fun i hi => by rw [k₁.2.2, h8]; exact hw i hi
  have hW : W u₁ [] u₁ := ⟨Keep.refl _ _, by rw [writeBytes_nil], by rw [hdi]; simp⟩
  refine WP.mono (psLoop_ok hb hn' hn (by simp) hW 0 (by rw [hax]; rfl) h10) fun t ⟨hW', hK'⟩ =>
    ⟨(k₁.trans hW'.1).mono (by simp [clob]), ?_, by rw [hK'.gpr (by decide), hax]⟩
  rw [hW'.2.1, hm₁, h8, List.nil_append]

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- Zeros to `out`, with its address and length from the slots: the result
`none`. -/
theorem zeroSlots_ok {s t : State} (hp : PreR s) (he : Env s t) :
    WP isa zeroSlots t fun u => Env s u ∧
      Spec.Rsa.written u.mem (s.gpr .rdi) (s.gpr .rsi).toNat ((u.gpr .rax).setWidth 32) none := by
  have hs := he.scr hp
  have ol := hp.ol
  unfold zeroSlots
  refine WP.seq (WP.mono (WP.keep [.rdi, .rsi] (Q := fun u => u.mem = t.mem ∧ u.gpr .rdi = s.gpr .rdi ∧
      u.gpr .rsi = s.gpr .rsi) (by
    xrun [ea_sp, he.rsp, hs.ld (d := oOut) (by decide), hs.ld (d := oOl) (by decide), he.sOut, he.sOl]) rfl)
    fun t₁ ⟨⟨hm₁, hdi, hsi⟩, k₁⟩ => ?_)
  have hwr : outR s ∈ t₁.wr := by rw [k₁.2.2, he.wr, hp.hwr]; simp [outR]
  refine WP.mono (zeroOut_ok (n := (s.gpr .rsi).toNat) (by omega) (by omega) (by rw [hsi, ofNat_toNat64])
    (by rw [hdi]; exact out_wr hwr)) fun u ⟨hK, hm, hax⟩ => ⟨?_, ?_, ?_⟩
  · refine Env.of (he.regs (k₁.gpr (by decide)) hm₁ k₁.2.1 k₁.2.2) hp (hK.gpr (by decide)) hK.2.1 hK.2.2
      (hm ▸ frame_writeBytes _ _ _) fun r hr => .inr ?_
    rw [List.mem_singleton.mp hr, hdi, List.length_replicate]; rfl
  · rw [hax]; rfl
  · rw [hm, hdi]
    have := bytesAt_writeBytes t₁.mem (s.gpr .rdi) (List.replicate (s.gpr .rsi).toNat 0) (by simp; omega)
    rwa [List.length_replicate] at this

theorem valPtr_eq (p a b : Addr) (h : b.toNat ≤ a.toNat) :
    p + a - b = p + BitVec.ofNat 64 (a.toNat - b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := a.isLt; have := b.isLt; have := p.isLt
  rw [Nat.mod_eq_of_lt (show a.toNat - b.toNat < 2 ^ 64 by omega)]
  omega

/-- The hash value's place in `EM₁`. -/
abbrev valA (s : State) : Addr := off (fb s) (oEM1 + ((s.gpr .rcx).toNat - (s.gpr .rsi).toNat))

theorem valPtr_ok {s t : State} (hp : PreR s) (hsp : t.gpr .rsp = fb s) (hcx : t.gpr .rcx = s.gpr .rcx)
    (h9 : t.gpr .r9 = s.gpr .rsi) :
    WP isa (.block valPtr) t fun u => Keep [.rsi] t u ∧ u.mem = t.mem ∧ u.gpr .rsi = valA s := by
  have ol := hp.ol
  have hk1 := hp.k1
  refine WP.mono (WP.keep [.rsi] (Q := fun u => u.mem = t.mem ∧ u.gpr .rsi = valA s) (by
    xrun [valPtr, lea, List.cons_append, List.nil_append, hsp, hcx, h9, sx_ofNat (show oEM1 < 2 ^ 31 by decide)]
    rw [valPtr_eq _ _ _ (by omega)]; exact off_off _ _ _) rfl) fun u ⟨h, k⟩ => ⟨k, h⟩

theorem encArgs_ok {s t : State} (hp : PreR s) (he : Env s t) :
    WP isa (.block encArgs) t fun u => Keep [.r8, .rcx, .rdx, .r9, .rsi] t u ∧ u.mem = t.mem ∧
      u.gpr .r8 = off (fb s) oEM2 ∧ u.gpr .rcx = s.gpr .rcx ∧
      u.gpr .rdx = ((stackArg s 0).setWidth 32).setWidth 64 ∧ u.gpr .r9 = s.gpr .rsi ∧ u.gpr .rsi = valA s := by
  have hs := he.scr hp
  unfold encArgs
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r8, .rcx, .rdx, .r9] (Q := fun u => u.mem = t.mem ∧
      u.gpr .r8 = off (fb s) oEM2 ∧ u.gpr .rcx = s.gpr .rcx ∧
      u.gpr .rdx = ((stackArg s 0).setWidth 32).setWidth 64 ∧ u.gpr .r9 = s.gpr .rsi) (by
    xrun [lea, List.cons_append, List.nil_append, @arg_ea s, ea_sp, he.rsp,
      sx_ofNat (show oEM2 < 2 ^ 31 by decide), hs.ld (d := oK) (by decide), hs.ld (d := oOl) (by decide),
      arg_in hp he.rd (show 0 < 5 by decide), he.arg hp (show 0 < 5 by decide), he.sK, he.sOl]) rfl)
    fun t₁ ⟨⟨hm₁, h8, hcx, hdx, h9⟩, k₁⟩ => ?_
  refine WP.mono (valPtr_ok hp ((k₁.gpr (by decide)).trans he.rsp) hcx h9) fun u ⟨k, hm, hsi⟩ =>
    ⟨(k₁.trans k).mono (by simp), hm.trans hm₁, by rw [k.gpr (by decide), h8], by rw [k.gpr (by decide), hcx],
      by rw [k.gpr (by decide), hdx], by rw [k.gpr (by decide), h9], hsi⟩

/-- The hash value's place in `EM₁` is in the frame. -/
theorem valA_sub {s : State} (hp : PreR s) : Region.Sub ⟨valA s, (s.gpr .rsi).toNat⟩ (stkR s) := by
  have := hp.ol; have := hp.k2; have := hp.k1
  exact frame_sub s (by unfold oEM1 frameBytes; omega)

/-- The value to `out`, and 1 returned. -/
theorem copyOut_ok {s t : State} (hp : PreR s) (he : Env s t) (hcx : t.gpr .rcx = s.gpr .rcx) :
    WP isa copyOut t fun u => Env s u ∧ (u.gpr .rax).setWidth 32 = 1 ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
        Spec.Rsa.bytesAt t.mem (valA s) (s.gpr .rsi).toNat := by
  have hs := he.scr hp
  have ol := hp.ol
  have hk2 := hp.k2
  have hk1 := hp.k1
  have hF := fb_toNat hp
  unfold copyOut
  rw [WP.seq_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r8, .rdi, .r9] (Q := fun u => u.mem = t.mem ∧ u.gpr .r8 = s.gpr .rdi ∧
      u.gpr .rdi = s.gpr .rdi ∧ u.gpr .r9 = s.gpr .rsi) (by
    xrun [ea_sp, he.rsp, hs.ld (d := oOut) (by decide), hs.ld (d := oOl) (by decide), he.sOut, he.sOl]) rfl)
    fun t₀ ⟨⟨hm₀, h8₀, hdi₀, h9₀⟩, k₀⟩ => ?_
  refine WP.mono (valPtr_ok hp ((k₀.gpr (by decide)).trans he.rsp) ((k₀.gpr (by decide)).trans hcx) h9₀)
    fun t₁ ⟨k₁, hm₁, hsi₁⟩ => ?_
  have h8 : t₁.gpr .r8 = s.gpr .rdi := by rw [k₁.gpr (by decide), h8₀]
  have hdi : t₁.gpr .rdi = s.gpr .rdi := by rw [k₁.gpr (by decide), hdi₀]
  have h9 : t₁.gpr .r9 = BitVec.ofNat 64 (s.gpr .rsi).toNat := by rw [k₁.gpr (by decide), h9₀, ofNat_toNat64]
  have hwr : outR s ∈ t₁.wr := by rw [k₁.2.2, k₀.2.2, he.wr, hp.hwr]; simp [outR]
  have hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t₁.wr := by rw [k₁.2.2, k₀.2.2, he.wr]; exact List.mem_cons_self ..
  have hb : Buf t₁ (s.gpr .rsi).toNat := fun i hi => by rw [h8]; exact out_wr hwr i hi
  have hW : W t₁ [] t₁ := ⟨Keep.refl _ _, by rw [writeBytes_nil], by rw [hdi, h8]; simp⟩
  have hr : ∀ j < (s.gpr .rsi).toNat, InRegions (t₁.rd ++ t₁.wr) (t₁.gpr .rsi + BitVec.ofNat 64 j) 1 :=
    fun j hj => ⟨_, List.mem_append_right _ hfr, by
      rw [hsi₁, show valA s + BitVec.ofNat 64 j = off (fb s) (oEM1 + ((s.gpr .rcx).toNat - (s.gpr .rsi).toNat) + j)
        from off_off _ _ _]
      exact Offset.contains_base _ (by unfold oEM1 frameBytes; omega) (by unfold oEM1 frameBytes at *; omega)⟩
  have hd : ∀ j < (s.gpr .rsi).toNat, ∀ i < (s.gpr .rsi).toNat,
      t₁.gpr .rsi + BitVec.ofNat 64 j ≠ t₁.gpr .r8 + BitVec.ofNat 64 i := fun j hj i hi => by
    rw [hsi₁, h8]
    exact ne_of_disjoint ((hp.dKo.sub_left (valA_sub hp))) (by omega) (by omega) hj hi
  refine WP.seq (WP.mono (copyLoop_ok hb (by omega) (by omega) (by simp) hW rfl h9 hr hd) fun t₂ hW₂ => ?_)
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = t₂.mem ∧ u.gpr .rax = 1) (by xrun) rfl)
    fun u ⟨⟨hm, hax⟩, hK⟩ => ⟨?_, by rw [hax]; rfl, ?_⟩
  · have hm' : u.mem = writeBytes t₁.mem (s.gpr .rdi)
        (Spec.Rsa.bytesAt t₁.mem (t₁.gpr .rsi) (s.gpr .rsi).toNat) := by
      rw [hm, hW₂.2.1, h8, List.nil_append]
    have heT : Env s t₁ := (he.regs (k₀.gpr (by decide)) hm₀ k₀.2.1 k₀.2.2).regs (k₁.gpr (by decide)) hm₁
      k₁.2.1 k₁.2.2
    refine Env.of heT hp ((hK.gpr (by decide)).trans (hW₂.1.gpr (by decide))) (hK.2.1.trans hW₂.1.2.1)
      (hK.2.2.trans hW₂.1.2.2) (hm' ▸ frame_writeBytes _ _ _) fun r hr => .inr ?_
    rw [List.mem_singleton.mp hr, bytesAt_length]; rfl
  · rw [hm, hW₂.2.1, h8, List.nil_append, hsi₁, hm₁, hm₀]
    have := bytesAt_writeBytes t.mem (s.gpr .rdi) (Spec.Rsa.bytesAt t.mem (valA s) (s.gpr .rsi).toNat)
      (by rw [bytesAt_length]; omega)
    rwa [bytesAt_length] at this

theorem cmpArgs_ok {s t : State} (he : Env s t) :
    WP isa (.block cmpArgs) t fun u => Keep [.rdi, .rsi] t u ∧ u.mem = t.mem ∧
      u.gpr .rdi = off (fb s) oEM1 ∧ u.gpr .rsi = off (fb s) oEM2 := by
  refine WP.mono (WP.keep [.rdi, .rsi] (Q := fun u => u.mem = t.mem ∧
      u.gpr .rdi = off (fb s) oEM1 ∧ u.gpr .rsi = off (fb s) oEM2) (by
    xrun [cmpArgs, lea, List.cons_append, List.nil_append, he.rsp,
      sx_ofNat (show oEM1 < 2 ^ 31 by decide), sx_ofNat (show oEM2 < 2 ^ 31 by decide)]) rfl)
    fun u ⟨h, hK⟩ => ⟨hK, h⟩

theorem test_ok (t : State) :
    WP isa (.block [.alu .test .rdx (.reg .rdx)]) t fun u => SameF t u ∧ u.zf = some (t.gpr .rdx == 0) := by
  xrun
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, by rw [BitVec.and_self]⟩

theorem bytesAt_drop (m : Mem) (p : Addr) (d n : Nat) :
    (Spec.Rsa.bytesAt m p (d + n)).drop d = Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 d) n := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i h₁ h₂
  simp only [List.getElem_drop, Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, BitVec.add_assoc,
    ← BitVec.ofNat_add]

/-- Recovery's result, for a signature of `k` bytes. -/
def recOut (nB eB : List Byte) (h : Hash) (sig : List Byte) : Option (List Byte) :=
  match Spec.Rsa.publicOpChecked nB eB sig with
  | some em =>
    if Spec.RsaPkcs1Sig.encode h (em.drop (nB.length - h.len)) nB.length = some em then
      some (em.drop (nB.length - h.len))
    else none
  | none => none

/-- After the encoding into `EM₂`, whose result is `o`: the comparison with
`EM₁` and the release. -/
theorem tail_ok {s t₂ t₃ : State} (hp : PreR s) (he₂ : Env s t₂) (hK₃ : Keep clob t₂ t₃) {h : Hash}
    {em : List Byte} (hcx₂ : t₂.gpr .rcx = s.gpr .rcx) (h8₂ : t₂.gpr .r8 = off (fb s) oEM2)
    (hem : Spec.Rsa.bytesAt t₂.mem (off (fb s) oEM1) (s.gpr .rcx).toNat = em)
    (hval : Spec.Rsa.bytesAt t₂.mem (valA s) (s.gpr .rsi).toNat = em.drop ((s.gpr .rcx).toNat - (s.gpr .rsi).toNat))
    {o : Option (List Byte)} (ho : Spec.RsaPkcs1Sig.encode h (em.drop ((s.gpr .rcx).toNat - h.len))
      (s.gpr .rcx).toNat = o)
    (hpost : EOut t₂ t₃ o) :
    WP isa tail t₃ fun u => Env s u ∧ Spec.Rsa.written u.mem (s.gpr .rdi) (s.gpr .rsi).toNat
      ((u.gpr .rax).setWidth 32)
      (if o = some em then some (em.drop ((s.gpr .rcx).toNat - (s.gpr .rsi).toNat)) else none) := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have ol := hp.ol
  have hF := fb_toNat hp
  set k := (s.gpr .rcx).toNat with hkdef
  have dVE : (⟨valA s, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨off (fb s) oEM2, k⟩ :=
    Offset.disjoint _ (.inl (by unfold oEM1 oEM2; omega)) (by unfold oEM1 frameBytes at *; omega)
      (by unfold oEM2 frameBytes at *; omega)
  unfold tail
  refine WP.seq (WP.mono (test0_ok t₃) fun t₄ ⟨hs₄, hz₄⟩ => ?_)
  cases o with
  | none =>
    obtain ⟨hax, hm₃⟩ := hpost
    have he₄ : Env s t₄ := he₂.regs (by rw [hs₄.1, hK₃.gpr (by decide)]) (hs₄.2.1.trans hm₃)
      (hs₄.2.2.1.trans hK₃.2.1) (hs₄.2.2.2.trans hK₃.2.2)
    refine WP.ite true (by simp [eval, hz₄, hax]) (fun _ => ?_) (by simp)
    simp only [reduceCtorEq, ↓reduceIte]
    exact zeroSlots_ok hp he₄
  | some em' =>
    obtain ⟨hax, hm₃⟩ := hpost
    have hl' : em'.length = k := VG.Proof.RsaPkcs1Sig.encode_length ho
    have he₃ : Env s t₃ := Env.of he₂ hp (hK₃.gpr (by decide)) hK₃.2.1 hK₃.2.2 (hm₃ ▸ frame_writeBytes _ _ _)
      fun r hr => .inl ⟨oEM2, k, by rw [List.mem_singleton.mp hr, h8₂, hl'], by decide,
        by unfold oEM2 frameBytes; omega⟩
    have he₄ : Env s t₄ := he₃.regs (by rw [hs₄.1]) hs₄.2.1 hs₄.2.2.1 hs₄.2.2.2
    refine WP.ite false (by simp [eval, hz₄, hax]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (cmpArgs_ok he₄) fun t₅ ⟨hK₅, hm₅, hdi₅, hsi₅⟩ => ?_)
    have hcx₅ : t₅.gpr .rcx = s.gpr .rcx := by
      rw [hK₅.gpr (by decide), hs₄.1, hK₃.gpr (by decide), hcx₂]
    have he₅ : Env s t₅ := he₄.regs (hK₅.gpr (by decide)) hm₅ hK₅.2.1 hK₅.2.2
    have hr5 : ∀ i < k, InRegions (t₅.rd ++ t₅.wr) (t₅.gpr .rdi + BitVec.ofNat 64 i) 1 ∧
        InRegions (t₅.rd ++ t₅.wr) (t₅.gpr .rsi + BitVec.ofNat 64 i) 1 := fun i hi => by
      rw [hdi₅, hsi₅, he₅.wr]
      obtain ⟨r₁, h₁, c₁⟩ := frame_bytes' hp (d := oEM1) (n := k) (by unfold oEM1 frameBytes; omega) i hi
      obtain ⟨r₂, h₂, c₂⟩ := frame_bytes' hp (d := oEM2) (n := k) (by unfold oEM2 frameBytes; omega) i hi
      exact ⟨⟨r₁, List.mem_append_right _ h₁, c₁⟩, ⟨r₂, List.mem_append_right _ h₂, c₂⟩⟩
    refine WP.seq (WP.mono (compare_ok (by rw [hcx₅]) (by omega) hr5) fun t₆ ⟨hK₆, hm₆, hdx₆⟩ => ?_)
    have he₆ : Env s t₆ := he₅.regs (hK₆.gpr (by decide)) hm₆ hK₆.2.1 hK₆.2.2
    have hmem : ∀ {p : Addr} {n : Nat}, (⟨p, n⟩ : Region).Disjoint ⟨off (fb s) oEM2, em'.length⟩ → n ≤ 2 ^ 64 →
        Spec.Rsa.bytesAt t₃.mem p n = Spec.Rsa.bytesAt t₂.mem p n := fun {p n} hd hn => by
      rw [hm₃, h8₂]
      simp only [Spec.Rsa.bytesAt]
      exact List.map_congr_left fun i hi =>
        (frame_writeBytes t₂.mem _ em').bytes (R := ⟨p, n⟩) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd)
          hn (List.mem_range.mp hi)
    have d12 : (⟨off (fb s) oEM1, k⟩ : Region).Disjoint ⟨off (fb s) oEM2, em'.length⟩ := by
      rw [hl']
      exact Offset.disjoint _ (.inl (by unfold oEM1 oEM2; omega)) (by unfold oEM1 frameBytes at *; omega)
        (by unfold oEM2 frameBytes at *; omega)
    have h1 : Spec.Rsa.bytesAt t₃.mem (off (fb s) oEM1) k = em := by
      rw [hmem d12 (by omega), hem]
    have h2 : Spec.Rsa.bytesAt t₃.mem (off (fb s) oEM2) k = em' := by
      have := bytesAt_writeBytes t₂.mem (off (fb s) oEM2) em' (by omega)
      rw [hl'] at this
      rw [hm₃, h8₂]; exact this
    have hdiff : (t₆.gpr .rdx = 0) ↔ em = em' := by
      rw [hdx₆, hdi₅, hsi₅, setWidth_byte_eq_zero, VG.Proof.Ct.diff_zero, ← bytesAt_eq_iff, hm₅, hs₄.2.1, h1, h2]
    unfold release
    refine WP.seq (WP.mono (test_ok t₆) fun t₇ ⟨hs₇, hz₇⟩ => ?_)
    have he₇ : Env s t₇ := he₆.regs (by rw [hs₇.1]) hs₇.2.1 hs₇.2.2.1 hs₇.2.2.2
    by_cases hq : em = em'
    · subst hq
      refine WP.ite false (by simp [eval, hz₇, hdiff.2 rfl]) (by simp) (fun _ => ?_)
      refine WP.mono (copyOut_ok hp he₇ (by rw [hs₇.1, hK₆.gpr (by decide), hcx₅])) fun u ⟨heu, hax', hout⟩ =>
        ⟨heu, ?_⟩
      have hv : Spec.Rsa.bytesAt t₇.mem (valA s) (s.gpr .rsi).toNat = em.drop (k - (s.gpr .rsi).toNat) := by
        rw [hs₇.2.1, hm₆, hm₅, hs₄.2.1, hmem (by rw [hl']; exact dVE) (by omega), hval]
      simp only [↓reduceIte]
      exact ⟨hax', hout.trans hv⟩
    · have hne : t₆.gpr .rdx ≠ 0 := fun h' => hq (hdiff.1 h')
      rw [show (t₆.gpr .rdx == 0) = false from beq_eq_false_iff_ne.mpr hne] at hz₇
      refine WP.ite true (by simp [eval, hz₇]) (fun _ => ?_) (by simp)
      rw [ite_eq_right_iff.mpr (fun h' => absurd (Option.some.inj h').symm hq)]
      exact zeroSlots_ok hp he₇

theorem afterPub_ok {s t : State} (hp : PreR s) (he : Env s t) {h : Hash}
    (hid : Hash.ofId ((stackArg s 0).setWidth 32).toNat = some h)
    (hw : Spec.Rsa.written t.mem (off (fb s) oEM1) (s.gpr .rcx).toNat ((t.gpr .rax).setWidth 32)
      (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .rcx).toNat))) :
    WP isa afterPub t fun u => Env s u ∧ Spec.Rsa.written u.mem (s.gpr .rdi) (s.gpr .rsi).toNat
      ((u.gpr .rax).setWidth 32)
      (recOut (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) h
        (Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .rcx).toNat)) := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have ol := hp.ol
  have hF := fb_toNat hp
  have hol : (s.gpr .rsi).toNat = h.len := by
    obtain ⟨h', hid', hl⟩ := hp.hash; rw [hid] at hid'; cases hid'; exact hl
  set k := (s.gpr .rcx).toNat with hkdef
  set nB := Spec.Rsa.bytesAt s.mem (s.gpr .rdx) k
  set eB := Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat
  set gB := Spec.Rsa.bytesAt s.mem (stackArg s 1) k
  set x := (stackArg s 0).setWidth 32
  have hnl : nB.length = k := bytesAt_length _ _ _
  unfold afterPub
  refine WP.seq (WP.mono (test0_ok t) fun t₁ ⟨hs₁, hz₁⟩ => ?_)
  have he₁ : Env s t₁ := he.regs (by rw [hs₁.1]) hs₁.2.1 hs₁.2.2.1 hs₁.2.2.2
  have hz : ∀ u, Env s u → recOut nB eB h gB = none → WP isa zeroSlots u fun v => Env s v ∧
      Spec.Rsa.written v.mem (s.gpr .rdi) (s.gpr .rsi).toNat ((v.gpr .rax).setWidth 32) (recOut nB eB h gB) :=
    fun u hu hr => by rw [hr]; exact zeroSlots_ok hp hu
  cases hpo : Spec.Rsa.publicOpChecked nB eB gB with
  | none =>
    rw [hpo] at hw
    obtain ⟨hr, -⟩ := hw
    refine WP.ite true (by simp [eval, hz₁, hr]) (fun _ => hz t₁ he₁ (by simp [recOut, hpo])) (by simp)
  | some em =>
    rw [hpo] at hw
    obtain ⟨hr, hem⟩ := hw
    refine WP.ite false (by simp [eval, hz₁, hr]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (encArgs_ok hp he₁) fun t₂ ⟨hK₂, hm₂, h8₂, hcx₂, hdx₂, h9₂, hsi₂⟩ => ?_)
    have he₂ : Env s t₂ := he₁.regs (hK₂.gpr (by decide)) hm₂ hK₂.2.1 hK₂.2.2
    have sE2 : Region.Sub ⟨off (fb s) oEM2, k⟩ (stkR s) := frame_sub s (by unfold oEM2 frameBytes; omega)
    have dVE : (⟨valA s, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨off (fb s) oEM2, k⟩ :=
      Offset.disjoint _ (.inl (by unfold oEM1 oEM2; omega)) (by unfold oEM1 frameBytes at *; omega)
        (by unfold oEM2 frameBytes at *; omega)
    have hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t₂.wr := by rw [he₂.wr]; exact List.mem_cons_self ..
    have hpre : EPre t₂ x k := {
      rdx := by rw [hdx₂]; apply BitVec.eq_of_toNat_eq; simp [x]
      hk := by rw [hcx₂]
      kle := hk2
      buf := fun i hi => by
        rw [h8₂, he₂.wr]; exact frame_bytes' hp (by unfold oEM2 frameBytes; omega) i hi
      rd := fun j hj => by
        rw [hsi₂]
        rw [h9₂] at hj
        exact ⟨_, List.mem_append_right _ hfr, by
          rw [show valA s + BitVec.ofNat 64 j = off (fb s) (oEM1 + ((s.gpr .rcx).toNat - (s.gpr .rsi).toNat) + j)
            from off_off _ _ _]
          exact Offset.contains_base _ (by unfold oEM1 frameBytes; omega) (by unfold oEM1 frameBytes at *; omega)⟩
      sep := fun j hj i hi => by
        rw [hsi₂, h8₂]
        rw [h9₂] at hj
        exact ne_of_disjoint dVE (by omega) (by omega) hj hi }
    have hH : Spec.Rsa.bytesAt t₂.mem (t₂.gpr .rsi) (t₂.gpr .r9).toNat = em.drop (nB.length - h.len) := by
      rw [hsi₂, h9₂, hm₂, hs₁.2.1, hnl, ← hol, ← hem]
      have := bytesAt_drop t.mem (off (fb s) oEM1) (k - (s.gpr .rsi).toNat) (s.gpr .rsi).toNat
      rw [show k - (s.gpr .rsi).toNat + (s.gpr .rsi).toNat = k by omega] at this
      rw [this]
      exact congrArg (Spec.Rsa.bytesAt t.mem · _) (off_off _ _ _).symm
    have hE : ∀ H, encodeId x H k = Spec.RsaPkcs1Sig.encode h H k := fun H => by simp only [encodeId, hid]
    refine WP.seq (WP.mono (encode_ok hpre) fun t₃ ⟨hK₃, hpost⟩ => ?_)
    rw [hH, hE, hnl] at hpost
    have hem₂ : Spec.Rsa.bytesAt t₂.mem (off (fb s) oEM1) k = em := by rw [hm₂, hs₁.2.1, hem]
    have hval : Spec.Rsa.bytesAt t₂.mem (valA s) (s.gpr .rsi).toNat = em.drop (k - (s.gpr .rsi).toNat) := by
      have := hH
      rw [hsi₂, h9₂, hnl, ← hol] at this
      exact this
    refine WP.mono (tail_ok (h := h) (o := Spec.RsaPkcs1Sig.encode h (em.drop (k - h.len)) k) hp he₂ hK₃ hcx₂ h8₂
      hem₂ hval rfl hpost) fun u ⟨heu, hwu⟩ => ⟨heu, ?_⟩
    simp only [recOut, hpo, hnl]
    simp only [hol] at hwu ⊢
    exact hwu

/-! ## The arguments and the frame -/

/-- The frame's push and the arguments of the call. -/
theorem pubArgs_ok {s A : State} (hp : PreR s) (hA : Keep [.rax] (allocState frameBytes s) A)
    (hAm : A.mem = s.mem) :
    WP isa (.block pubArgs) A fun t => Env s t ∧
      word t.mem (fb s) 0 = stackArg s 1 ∧ word t.mem (fb s) 8 = s.gpr .rcx ∧
      word t.mem (fb s) 16 = stackArg s 3 ∧ word t.mem (fb s) 24 = stackArg s 4 ∧
      t.gpr .rdi = off (fb s) oEM1 ∧ t.gpr .rsi = s.gpr .rcx ∧ t.gpr .rdx = s.gpr .rdx ∧
      t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r9 = s.gpr .r9 ∧
      (∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r) := by
  have hF := fb_toNat hp
  rw [pubArgs_eq, WP.block_append_iff]
  refine WP.mono (slotStores_ok hp hA hAm) fun t₁ ⟨k₁, ho₁, hO, hOl, hN, hK, hE, hEl⟩ => ?_
  refine WP.mono (callArgs_ok hp k₁ ho₁) fun t ⟨k, hm, hdi, hsi⟩ => ?_
  have k' := k₁.trans k
  have g : ∀ r, r ≠ .rsp → r ∉ [Reg.rax] ++ [Reg.rax, .rdi, .rsi, .r10, .r11] → t.gpr r = s.gpr r :=
    fun r h h' => by rw [k'.gpr h']; simp [allocState_gpr, h]
  have hw : ∀ d, 32 ≤ d → d + 8 ≤ frameBytes → word t.mem (fb s) d = word t₁.mem (fb s) d := fun d hd hd' => by
    unfold frameBytes at hd'
    rw [hm, word_wo _ _ _ (d := 24) (.inl (by omega)) (by decide) (by omega),
      word_wo _ _ _ (d := 16) (.inl (by omega)) (by decide) (by omega),
      word_wo _ _ _ (d := 8) (.inl (by omega)) (by decide) (by omega), word_wo0 _ _ _ (by omega) (by omega)]
  refine ⟨⟨(k'.gpr (by decide)).trans rfl, k'.2.1, k'.2.2, frame_of_outside ?_,
      (hw _ (by decide) (by decide)).trans hO, (hw _ (by decide) (by decide)).trans hOl,
      (hw _ (by decide) (by decide)).trans hN, (hw _ (by decide) (by decide)).trans hK,
      (hw _ (by decide) (by decide)).trans hE, (hw _ (by decide) (by decide)).trans hEl⟩, ?_, ?_, ?_, ?_,
    hdi, hsi, g _ (by decide) (by decide), g _ (by decide) (by decide), g _ (by decide) (by decide),
    g _ (by decide) (by decide), fun r hr hr' => g r hr' (by
      simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all)⟩
  · rw [hm]
    intro x hx
    have hx' : frameBytes ≤ ofs (fb s) x := by unfold frameBytes at hx ⊢; omega
    unfold frameBytes at hx hx'
    rw [writeW_outside _ _ _ (d := 24) (by omega) x (by omega), writeW_outside _ _ _ (d := 16) (by omega) x (by omega),
      writeW_outside _ _ _ (d := 8) (by omega) x (by omega)]
    have := writeW_outside t₁.mem (fb s) (stackArg s 1) (d := 0) (by omega) x (by omega)
    simp only [off, BitVec.add_zero] at this
    rw [this]; exact ho₁ x hx
  · rw [hm]; simp (disch := decide) only [word_wo]; exact word_self0 _ _ _
  · rw [hm]; simp (disch := decide) only [word_wo, word_writeW_self]
  · rw [hm]; simp (disch := decide) only [word_wo, word_writeW_self]
  · rw [hm]; exact word_writeW_self _ _ _ _

theorem lenCheck_ok {s : State} (hp : PreR s) :
    WP isa (.block lenCheck) s fun t => Keep [.rax] s t ∧ t.mem = s.mem ∧
      t.zf = some (stackArg s 2 == s.gpr .rcx) := by
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem ∧ t.zf = some (stackArg s 2 == s.gpr .rcx)) (by
    xrun [lenCheck, arg0_ea, arg_in hp rfl (show 2 < 5 by decide), sub_beq64]
    rfl) rfl) fun t ⟨h, hK⟩ => ⟨hK, h⟩

theorem recover_eq_recOut {nB eB sig : List Byte} (h : Hash) (hs : sig.length = nB.length) :
    recover nB eB h sig = recOut nB eB h sig := by
  rw [VG.Proof.RsaPkcs1Sig.recover_eq_recoverEnc]
  unfold VG.Proof.RsaPkcs1Sig.recoverEnc recOut
  rw [ite_eq_left hs]
  cases Spec.Rsa.publicOpChecked nB eB sig <;> rfl

theorem recover_len {nB eB sig : List Byte} (h : Hash) (hs : sig.length ≠ nB.length) :
    recover nB eB h sig = none := by
  unfold recover; rw [ite_eq_right_iff.mpr (fun h' => absurd h' hs)]

/-- The return address is outside everything the function writes. -/
theorem ret_frame {s : State} (hp : PreR s) {m : Mem} (h : Frame [stkR s, outR s, scrR s] s.mem m) :
    m.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  have hsp2 := hp.sp2
  refine h.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · have := Offset.disjoint_below (s.gpr .rsp) (n := verStack) (d := 0) (k := 8)
      (by unfold verStack; omega)
    simpa only [stkR, kb, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  · exact hp.dRo
  · exact hp.dRs

theorem code_correct (v : PubImpl) (s : State) (h : recContract.pre s) :
    ∃ t s', Exec isa (code v.name v.code) s t s' ∧ abiPreserved s s' ∧ recContract.post s s' := by
  have hp := preR_of h
  have hk2 := hp.k2
  have ol := hp.ol
  obtain ⟨hh, hid, hol⟩ := hp.hash
  suffices hw : WP isa (code v.name v.code) s fun s' => abiPreserved s s' ∧ recContract.post s s' by
    obtain ⟨t, s', he, hq⟩ := hw
    exact ⟨t, s', he, hq⟩
  have hpost : ∀ (u : State) (o : Option (List Byte)), Spec.Rsa.written u.mem (s.gpr .rdi) (s.gpr .rsi).toNat
      ((u.gpr .rax).setWidth 32) o →
      (o = recover (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) hh
        (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)) → recContract.post s u := by
    intro u o hw ho h' hid'
    rw [hid] at hid'; cases hid'
    rw [← ho]; exact hw
  unfold code
  refine WP.seq (WP.mono_mx (by decide) (lenCheck_ok hp) fun t₀ ⟨k₀, hm₀, hz₀⟩ hmx₀ => ?_)
  have g₀ : ∀ r, r ≠ .rax → t₀.gpr r = s.gpr r := fun r h => k₀.gpr (by simpa using h)
  by_cases hsig : stackArg s 2 = s.gpr .rcx
  · refine WP.ite false (by simp [eval, hz₀, hsig]) (by simp) (fun _ => ?_)
    have hsp₀ : t₀.gpr .rsp = s.gpr .rsp := g₀ _ (by decide)
    have hA : Keep [.rax] (allocState frameBytes s) (allocState frameBytes t₀) :=
      ⟨fun r hr => by
        simp only [allocState_gpr, fb, hsp₀]
        split
        · rfl
        · exact g₀ r (by simpa using hr), k₀.2.1, by simp only [allocState, hsp₀, k₀.2.2]⟩
    have hfb : fb t₀ = fb s := by simp only [fb, hsp₀]
    refine wp_alloc (s := t₀) (by rw [hsp₀]; have := hp.sp1; unfold verStack at this; unfold frameBytes; omega) ?_
    unfold body
    refine WP.seq (WP.mono_mx (by decide) (pubArgs_ok hp hA hm₀)
      fun t₁ ⟨he₁, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, hcs₁⟩ hmx₁ => ?_)
    refine WP.seq (WP.mono (pub_call v hp hsig he₁ hw0 hw1 hw2 hw3 hdi hsi hdx hcx h8 h9)
      fun t₂ ⟨he₂, hw, hcs₂, hmx₂⟩ => ?_)
    refine WP.mono_mx (by decide +kernel) (WP.keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]
      (afterPub_ok hp he₂ hid hw) (by decide +kernel)) fun t₃ ⟨⟨he₃, hwu⟩, k₃⟩ hmx₃ => ?_
    refine ⟨he₃.rsp.trans hfb.symm, by rw [he₃.wr]; simp only [allocState, hsp₀, k₀.2.2],
      ⟨fun r hr => ?_, ret_frame hp he₃.mem, ?_⟩, hpost _ _ hwu ?_⟩
    · by_cases hr' : r = .rsp
      · subst hr'
        show t₃.gpr .rsp + BitVec.ofNat 64 frameBytes = s.gpr .rsp
        rw [he₃.rsp, BitVec.sub_add_cancel]
      · show (if r = .rsp then _ else t₃.gpr r) = s.gpr r
        simp only [hr', ↓reduceIte]
        have hr'' : r ∉ [Reg.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] := by
          simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
        rw [k₃.gpr hr'', hcs₂ r hr, hcs₁ r hr hr']
    · show t₃.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
      rw [hmx₃, hmx₂, hmx₁]; exact congrArg _ hmx₀
    · rw [hsig, recover_eq_recOut _ (by simp only [bytesAt_length])]
  · refine WP.ite true (by simp [eval, hz₀, hsig]) (fun _ => ?_) (by simp)
    have hwr : outR s ∈ t₀.wr := by rw [k₀.2.2, hp.hwr]; simp [outR]
    refine WP.mono_mx (by decide) (zeroOut_ok (n := (s.gpr .rsi).toNat) (by omega) (by omega)
      (by rw [g₀ _ (by decide), ofNat_toNat64]) (by rw [g₀ _ (by decide)]; exact out_wr hwr))
      fun u ⟨hK, hm, hax⟩ hmx => ⟨⟨fun r hr => ?_, ?_, by rw [hmx, hmx₀]⟩, hpost u none ⟨by rw [hax]; rfl, ?_⟩ ?_⟩
    · rw [hK.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp),
        k₀.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)]
    · rw [hm, g₀ _ (by decide)]
      refine ((frame_writeBytes t₀.mem _ _).readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _)
        (fun r hr => ?_) (by decide)).trans (by rw [hm₀])
      rw [List.mem_singleton.mp hr, List.length_replicate]; exact hp.dRo
    · rw [hm, g₀ _ (by decide)]
      have := bytesAt_writeBytes t₀.mem (s.gpr .rdi) (List.replicate (s.gpr .rsi).toNat 0) (by simp; omega)
      rwa [List.length_replicate] at this
    · rw [recover_len _ (by simp only [bytesAt_length]; intro h'; exact hsig (BitVec.eq_of_toNat_eq h'))]

/-! ## Facts for constant time -/

/-- After an encoding `em'` into `EM₂`: `Env`, `EM₁` kept, `EM₂` the encoding,
and what lies apart from `EM₂` kept. -/
theorem encDone {s t₂ t₃ : State} (hp : PreR s) (he₂ : Env s t₂) (hK₃ : Keep clob t₂ t₃)
    (h8₂ : t₂.gpr .r8 = off (fb s) oEM2) {em' : List Byte} (hl' : em'.length = (s.gpr .rcx).toNat)
    (hpost : EOut t₂ t₃ (some em')) :
    Env s t₃ ∧ t₃.gpr .rax = 1 ∧ Spec.Rsa.bytesAt t₃.mem (off (fb s) oEM2) (s.gpr .rcx).toNat = em' ∧
      ∀ {p : Addr} {n : Nat}, (⟨p, n⟩ : Region).Disjoint ⟨off (fb s) oEM2, (s.gpr .rcx).toNat⟩ → n ≤ 2 ^ 64 →
        Spec.Rsa.bytesAt t₃.mem p n = Spec.Rsa.bytesAt t₂.mem p n := by
  have hk2 := hp.k2
  have hk1 := hp.k1
  obtain ⟨hax, hm₃⟩ := hpost
  refine ⟨Env.of he₂ hp (hK₃.gpr (by decide)) hK₃.2.1 hK₃.2.2 (hm₃ ▸ frame_writeBytes _ _ _)
      fun r hr => .inl ⟨oEM2, (s.gpr .rcx).toNat, by rw [List.mem_singleton.mp hr, h8₂, hl'], by decide,
        by unfold oEM2 frameBytes; omega⟩, hax, ?_, fun {p n} hd hn => ?_⟩
  · have := bytesAt_writeBytes t₂.mem (off (fb s) oEM2) em' (by omega)
    rw [hl'] at this
    rw [hm₃, h8₂]; exact this
  · rw [hm₃, h8₂]
    simp only [Spec.Rsa.bytesAt]
    exact List.map_congr_left fun i hi =>
      (frame_writeBytes t₂.mem _ em').bytes (R := ⟨p, n⟩) (fun r hr => by
        rw [List.mem_singleton.mp hr, hl']; exact hd) hn (List.mem_range.mp hi)

theorem EM12_disjoint {s : State} (hp : PreR s) :
    (⟨off (fb s) oEM1, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨off (fb s) oEM2, (s.gpr .rcx).toNat⟩ := by
  have hk2 := hp.k2; have := fb_toNat hp
  exact Offset.disjoint _ (.inl (by unfold oEM1 oEM2; omega)) (by unfold oEM1 frameBytes at *; omega)
    (by unfold oEM2 frameBytes at *; omega)

theorem valA_disjoint {s : State} (hp : PreR s) :
    (⟨valA s, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨off (fb s) oEM2, (s.gpr .rcx).toNat⟩ := by
  have hk2 := hp.k2; have hk1 := hp.k1; have ol := hp.ol; have := fb_toNat hp
  exact Offset.disjoint _ (.inl (by unfold oEM1 oEM2; omega)) (by unfold oEM1 frameBytes at *; omega)
    (by unfold oEM2 frameBytes at *; omega)

/-- The head of `copyOut`. -/
theorem copyHead_ok {s t : State} (hp : PreR s) (he : Env s t) (hcx : t.gpr .rcx = s.gpr .rcx) :
    WP isa (.block (([.mov .r8 (.mem (sp oOut)), .mov .rdi (.reg .r8), .mov .r9 (.mem (sp oOl))] : List Instr) ++ valPtr)) t
      fun u => Keep [.r8, .rdi, .r9, .rsi] t u ∧ u.mem = t.mem ∧ u.gpr .r8 = s.gpr .rdi ∧
        u.gpr .rdi = s.gpr .rdi ∧ u.gpr .r9 = s.gpr .rsi ∧ u.gpr .rsi = valA s := by
  have hs := he.scr hp
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r8, .rdi, .r9] (Q := fun u => u.mem = t.mem ∧ u.gpr .r8 = s.gpr .rdi ∧
      u.gpr .rdi = s.gpr .rdi ∧ u.gpr .r9 = s.gpr .rsi) (by
    xrun [ea_sp, he.rsp, hs.ld (d := oOut) (by decide), hs.ld (d := oOl) (by decide), he.sOut, he.sOl]) rfl)
    fun t₀ ⟨⟨hm₀, h8₀, hdi₀, h9₀⟩, k₀⟩ => ?_
  refine WP.mono (valPtr_ok hp ((k₀.gpr (by decide)).trans he.rsp) ((k₀.gpr (by decide)).trans hcx) h9₀)
    fun u ⟨k, hm, hsi⟩ => ⟨(k₀.trans k).mono (by simp), hm.trans hm₀, by rw [k.gpr (by decide), h8₀],
      by rw [k.gpr (by decide), hdi₀], by rw [k.gpr (by decide), h9₀], hsi⟩

/-- The head of `zeroSlots`. -/
theorem zeroHead_ok {s t : State} (hp : PreR s) (he : Env s t) :
    WP isa (.block [.mov .rdi (.mem (sp oOut)), .mov .rsi (.mem (sp oOl))]) t
      fun u => Keep [.rdi, .rsi] t u ∧ u.mem = t.mem ∧ u.gpr .rdi = s.gpr .rdi ∧ u.gpr .rsi = s.gpr .rsi := by
  have hs := he.scr hp
  refine WP.mono (WP.keep [.rdi, .rsi] (Q := fun u => u.mem = t.mem ∧ u.gpr .rdi = s.gpr .rdi ∧
      u.gpr .rsi = s.gpr .rsi) (by
    xrun [ea_sp, he.rsp, hs.ld (d := oOut) (by decide), hs.ld (d := oOl) (by decide), he.sOut, he.sOl]) rfl)
    fun u ⟨h, k⟩ => ⟨k, h⟩

/-- What `encode` needs, from `encArgs`. -/
theorem encPre {s t₂ : State} (hp : PreR s) (he₂ : Env s t₂) (h8₂ : t₂.gpr .r8 = off (fb s) oEM2)
    (hcx₂ : t₂.gpr .rcx = s.gpr .rcx) (hdx₂ : t₂.gpr .rdx = ((stackArg s 0).setWidth 32).setWidth 64)
    (h9₂ : t₂.gpr .r9 = s.gpr .rsi) (hsi₂ : t₂.gpr .rsi = valA s) :
    EPre t₂ ((stackArg s 0).setWidth 32) (s.gpr .rcx).toNat := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have ol := hp.ol
  have hF := fb_toNat hp
  have hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t₂.wr := by rw [he₂.wr]; exact List.mem_cons_self ..
  exact {
    rdx := by rw [hdx₂]; apply BitVec.eq_of_toNat_eq; simp
    hk := by rw [hcx₂]
    kle := hk2
    buf := fun i hi => by
      rw [h8₂, he₂.wr]; exact frame_bytes' hp (by unfold oEM2 frameBytes; omega) i hi
    rd := fun j hj => by
      rw [hsi₂]
      rw [h9₂] at hj
      exact ⟨_, List.mem_append_right _ hfr, by
        rw [show valA s + BitVec.ofNat 64 j = off (fb s) (oEM1 + ((s.gpr .rcx).toNat - (s.gpr .rsi).toNat) + j)
          from off_off _ _ _]
        exact Offset.contains_base _ (by unfold oEM1 frameBytes; omega) (by unfold oEM1 frameBytes at *; omega)⟩
    sep := fun j hj i hi => by
      rw [hsi₂, h8₂]
      rw [h9₂] at hj
      exact ne_of_disjoint (valA_disjoint hp) (by omega) (by omega) hj hi }

/-- The hash value's place in `EM₁` holds its last `out_len` bytes. -/
theorem valBytes {s : State} (hp : PreR s) (m : Mem) :
    Spec.Rsa.bytesAt m (valA s) (s.gpr .rsi).toNat =
      (Spec.Rsa.bytesAt m (off (fb s) oEM1) (s.gpr .rcx).toNat).drop ((s.gpr .rcx).toNat - (s.gpr .rsi).toNat) := by
  have hk1 := hp.k1
  have ol := hp.ol
  have := bytesAt_drop m (off (fb s) oEM1) ((s.gpr .rcx).toNat - (s.gpr .rsi).toNat) (s.gpr .rsi).toNat
  rw [show (s.gpr .rcx).toNat - (s.gpr .rsi).toNat + (s.gpr .rsi).toNat = (s.gpr .rcx).toNat by omega] at this
  rw [this]
  exact congrArg (Spec.Rsa.bytesAt m · _) (off_off _ _ _).symm

end VG.Proof.RsaPkcs1Sig.X86_64.Rec
