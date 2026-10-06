import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignFrame
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCorrect

/-!
# `vg_rsa_pkcs1_sign` on x86-64: the blocks around the encoding and the call

The frame's push, the slots and the arguments of `encode` (`head_ok`, and
`encPre`, what `encode` needs), the zeros to `out` if it fails
(`zeroSlots_ok`), the arguments of `vg_rsa_private_checked` (`callArgs_ok`),
and the zeros to `EM` after the call (`wipe_ok`).
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64.Sgn

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Sign
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (sp lea)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64 VG.WriteBytes

/-! ## Memory in the frame -/

/-- `Env` past changes of the registers but `rsp`, and of memory in the
frame outside its slots or in `out`. -/
theorem Env.of {s t u : State} (he : Env s t) (hp : PreS s) (hsp : u.gpr .rsp = t.gpr .rsp) (hrd : u.rd = t.rd)
    (hwr : u.wr = t.wr) {rs : List Region} (hf : Frame rs t.mem u.mem)
    (hs : ∀ r ∈ rs, (∃ d n, r = ⟨off (fb s) d, n⟩ ∧ (d + n ≤ oOut ∨ oEM ≤ d) ∧ d + n ≤ frameBytes) ∨
      r = outR s) : Env s u := by
  have hsl : ∀ {d}, oOut ≤ d → d + 8 ≤ oEM → word u.mem (fb s) d = word t.mem (fb s) d := fun hd hd' =>
    hf.readW (Region.contains_self _ _) (fun r hr => by
      rcases hs r hr with ⟨d', n, rfl, h₁, h₂⟩ | rfl
      · exact Offset.disjoint _ (by unfold oOut oEM at *; omega) (by unfold frameBytes oEM at *; omega)
          (by unfold frameBytes at *; omega)
      · exact (hp.dKo.sub_left (frame_sub s (by unfold oEM frameBytes at *; omega)))) (by decide)
  refine ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr, he.mem.trans (hf.sub fun r hr => ?_),
    (hsl (by decide) (by decide)).trans he.sOut, (hsl (by decide) (by decide)).trans he.sOl,
    (hsl (by decide) (by decide)).trans he.sN, (hsl (by decide) (by decide)).trans he.sK,
    (hsl (by decide) (by decide)).trans he.sE, (hsl (by decide) (by decide)).trans he.sEl⟩
  rcases hs r hr with ⟨d, n, rfl, -, h₂⟩ | rfl
  · exact ⟨_, List.mem_cons_self .., frame_sub s h₂⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩

/-- `Env` past changes of the registers but `rsp`. -/
theorem Env.regs {s t u : State} (he : Env s t) (hsp : u.gpr .rsp = t.gpr .rsp) (hm : u.mem = t.mem)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) : Env s u :=
  ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr, hm ▸ he.mem, hm ▸ he.sOut, hm ▸ he.sOl, hm ▸ he.sN,
    hm ▸ he.sK, hm ▸ he.sE, hm ▸ he.sEl⟩

theorem frame_bytes {s : State} {d n : Nat} (hp : PreS s) (h : d + n ≤ frameBytes) :
    ∀ i < n, InRegions (⟨fb s, frameBytes⟩ :: s.wr) (off (fb s) d + BitVec.ofNat 64 i) 1 := by
  have := fb_toNat hp
  intro i hi
  refine ⟨_, List.mem_cons_self .., ?_⟩
  rw [show off (fb s) d + BitVec.ofNat 64 i = off (fb s) (d + i) from off_off _ _ _]
  exact Offset.contains_base _ (by omega) (by unfold frameBytes at *; omega)

/-! ## The head -/

/-- The frame's push, the slots and the arguments of `encode`. -/
theorem head_ok {s : State} (hp : PreS s) :
    WP isa (.block (slotStores ++ encArgs)) (allocState frameBytes s) fun t => Env s t ∧
      t.gpr .r8 = off (fb s) oEM ∧ t.gpr .rcx = s.gpr .rcx ∧
      t.gpr .rdx = ((stackArg s 0).setWidth 32).setWidth 64 ∧ t.gpr .rsi = stackArg s 1 ∧
      t.gpr .r9 = stackArg s 2 ∧ (∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r) := by
  have hF := fb_toNat hp
  set A := allocState frameBytes s with hA
  have hsp : A.gpr .rsp = fb s := rfl
  have hs : Scr A (fb s) frameBytes := Scr.of_mem (List.mem_cons_self ..) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [] (Q := fun t => t.mem =
      (((((s.mem.writeW (off (fb s) oOut) (s.gpr .rdi)).writeW (off (fb s) oOl) (s.gpr .rsi)).writeW
        (off (fb s) oN) (s.gpr .rdx)).writeW (off (fb s) oK) (s.gpr .rcx)).writeW (off (fb s) oE)
        (s.gpr .r8)).writeW (off (fb s) oEl) (s.gpr .r9)) (by
    xrun [slotStores, ea_sp, hsp, hs.st (d := oOut) (by decide), hs.st (d := oOl) (by decide),
      hs.st (d := oN) (by decide), hs.st (d := oK) (by decide), hs.st (d := oE) (by decide),
      hs.st (d := oEl) (by decide)]
    rfl) rfl) fun t₁ ⟨hm₁, k₁⟩ => ?_
  have ho₁ : Outside (fb s) 0 frameBytes s.mem t₁.mem := by
    rw [hm₁]
    intro x hx
    have hx' : frameBytes ≤ ofs (fb s) x := by unfold frameBytes at hx ⊢; omega
    unfold frameBytes at hx hx'
    simp only [oOut, oOl, oN, oK, oE, oEl] at *
    rw [writeW_outside _ _ _ (by omega) x (by omega), writeW_outside _ _ _ (by omega) x (by omega),
      writeW_outside _ _ _ (by omega) x (by omega), writeW_outside _ _ _ (by omega) x (by omega),
      writeW_outside _ _ _ (by omega) x (by omega), writeW_outside _ _ _ (by omega) x (by omega)]
  have hslots : word t₁.mem (fb s) oOut = s.gpr .rdi ∧ word t₁.mem (fb s) oOl = s.gpr .rsi ∧
      word t₁.mem (fb s) oN = s.gpr .rdx ∧ word t₁.mem (fb s) oK = s.gpr .rcx ∧
      word t₁.mem (fb s) oE = s.gpr .r8 ∧ word t₁.mem (fb s) oEl = s.gpr .r9 := by
    rw [hm₁]
    simp (disch := decide) only [word_wo, word_writeW_self, oOut, oOl, oN, oK, oE, oEl, and_self]
  have hsp₁ : t₁.gpr .rsp = fb s := (k₁.gpr (by decide)).trans hsp
  have hrd : t₁.rd = s.rd := k₁.2.1
  have g : ∀ r, r ≠ .rsp → t₁.gpr r = s.gpr r := fun r h => by
    rw [k₁.gpr (by simp)]; simp [hA, allocState_gpr, h]
  refine WP.mono (WP.keep [.r8, .rdx, .rsi, .r9] (Q := fun t => t.mem = t₁.mem ∧ t.gpr .r8 = off (fb s) oEM ∧
      t.gpr .rdx = ((stackArg s 0).setWidth 32).setWidth 64 ∧ t.gpr .rsi = stackArg s 1 ∧
      t.gpr .r9 = stackArg s 2) (by
    xrun [encArgs, lea, List.cons_append, List.nil_append, @arg_ea s, ea_sp, hsp₁,
      sx_ofNat (show oEM < 2 ^ 31 by decide), arg_in hp hrd (show 0 < 15 by decide),
      arg_in hp hrd (show 1 < 15 by decide), arg_in hp hrd (show 2 < 15 by decide),
      arg_outside hp ho₁ (show 0 < 15 by decide), arg_outside hp ho₁ (show 1 < 15 by decide),
      arg_outside hp ho₁ (show 2 < 15 by decide)]) rfl) fun t ⟨⟨hm, h8, hdx, hsi, h9⟩, k⟩ => ?_
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hslots
  refine ⟨⟨(k.gpr (by decide)).trans hsp₁, k.2.1.trans hrd, k.2.2.trans k₁.2.2, frame_of_outside (hm ▸ ho₁),
    hm ▸ h1, hm ▸ h2, hm ▸ h3, hm ▸ h4, hm ▸ h5, hm ▸ h6⟩, h8, by rw [k.gpr (by decide), g _ (by decide)],
    hdx, hsi, h9, fun r hr hr' => ?_⟩
  rw [k.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all),
    g r hr']

/-- What `encode` needs, from the head. -/
theorem encPre {s t : State} (hp : PreS s) (he : Env s t) (h8 : t.gpr .r8 = off (fb s) oEM)
    (hcx : t.gpr .rcx = s.gpr .rcx) (hdx : t.gpr .rdx = ((stackArg s 0).setWidth 32).setWidth 64)
    (hsi : t.gpr .rsi = stackArg s 1) (h9 : t.gpr .r9 = stackArg s 2) :
    EPre t ((stackArg s 0).setWidth 32) (s.gpr .rcx).toNat := by
  have hk2 := hp.k2
  have hdl := hp.wD
  have sEM : Region.Sub ⟨off (fb s) oEM, (s.gpr .rcx).toNat⟩ (stkR s) :=
    frame_sub s (by unfold oEM frameBytes; omega)
  exact {
    rdx := by rw [hdx]; apply BitVec.eq_of_toNat_eq; simp
    hk := by rw [hcx]
    kle := hk2
    buf := fun i hi => by rw [h8, he.wr]; exact frame_bytes hp (by unfold oEM frameBytes; omega) i hi
    rd := fun j hj => by
      rw [hsi, he.rd, he.wr]
      rw [h9] at hj
      exact ⟨⟨stackArg s 1, (stackArg s 2).toNat⟩, List.mem_append_left _ (by rw [hp.hrd]; simp),
        Offset.contains_base _ (by omega) (by omega)⟩
    sep := fun j hj i hi => by
      rw [hsi, h8]
      rw [h9] at hj
      exact ne_of_disjoint (hp.dKd.sub_left sEM).symm (by omega) (by omega) hj hi }

/-! ## Zeros to `out` -/

/-- The address and length of `out`, from their slots. -/
theorem zeroHead_ok {s t : State} (hp : PreS s) (he : Env s t) :
    WP isa (.block [.mov .rdi (.mem (sp oOut)), .mov .rsi (.mem (sp oOl))]) t
      fun u => Keep [.rdi, .rsi] t u ∧ u.mem = t.mem ∧ u.gpr .rdi = s.gpr .rdi ∧ u.gpr .rsi = s.gpr .rsi := by
  have hs := he.scr hp
  refine WP.mono (WP.keep [.rdi, .rsi] (Q := fun u => u.mem = t.mem ∧ u.gpr .rdi = s.gpr .rdi ∧
      u.gpr .rsi = s.gpr .rsi) (by
    xrun [ea_sp, he.rsp, hs.ld (d := oOut) (by decide), hs.ld (d := oOl) (by decide), he.sOut, he.sOl]) rfl)
    fun u ⟨h, k⟩ => ⟨k, h⟩

theorem zeroSlots_ok {s t : State} (hp : PreS s) (he : Env s t) :
    WP isa zeroSlots t fun u => Env s u ∧ (u.gpr .rax).setWidth 32 = 0 ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (s.gpr .rcx).toNat = List.replicate (s.gpr .rcx).toNat 0 := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hsiK := hp.hsi
  unfold zeroSlots
  refine WP.seq (WP.mono (zeroHead_ok hp he) fun t₁ ⟨k₁, hm₁, hdi, hsi⟩ => ?_)
  have hwr : outR s ∈ t₁.wr := by rw [k₁.2.2, he.wr, hp.hwr]; simp [outR]
  refine WP.mono (Rec.zeroOut_ok (n := (s.gpr .rsi).toNat) (by omega) (by omega)
    (by rw [hsi, Rec.ofNat_toNat64]) (by
      rw [hdi]; intro i hi; exact ⟨_, hwr, Offset.contains_base _ (by have := hp.wO; omega) (by omega)⟩))
    fun u ⟨hK, hm, hax⟩ => ⟨?_, by rw [hax]; rfl, ?_⟩
  · refine Env.of (he.regs (k₁.gpr (by decide)) hm₁ k₁.2.1 k₁.2.2) hp (hK.gpr (by decide)) hK.2.1 hK.2.2
      (hm ▸ frame_writeBytes _ _ _) fun r hr => .inr ?_
    rw [List.mem_singleton.mp hr, hdi, List.length_replicate]; rfl
  · rw [hm, hdi, ← hsiK]
    have := bytesAt_writeBytes t₁.mem (s.gpr .rdi) (List.replicate (s.gpr .rsi).toNat 0) (by simp; omega)
    rwa [List.length_replicate] at this

/-! ## The arguments of the call -/

/-- The call's stack argument `i`: `EM`, `n_len`, then the function's stack
arguments from `p` on. -/
def callArg (s : State) : Nat → BitVec 64
  | 0 => off (fb s) oEM
  | 1 => s.gpr .rcx
  | i + 2 => stackArg s (i + 3)

/-- Stack argument `j + 3` to the frame's word `j + 2`. -/
theorem copyArg_ok {s t : State} (hp : PreS s) (he : Env s t) {j : Nat} (hj : j < 12) :
    WP isa (.block (copyArg j)) t fun t' => Env s t' ∧
      t'.mem = t.mem.writeW (off (fb s) (8 * (j + 2))) (stackArg s (j + 3)) ∧ Keep [.rax] t t' := by
  have hs := he.scr hp
  refine WP.mono (WP.keep [.rax] (Q := fun t' =>
      t'.mem = t.mem.writeW (off (fb s) (8 * (j + 2))) (stackArg s (j + 3))) (by
    xrun [copyArg, @arg_ea s, ea_sp, he.rsp, arg_in hp he.rd (show j + 3 < 15 by omega),
      he.arg hp (show j + 3 < 15 by omega), hs.st (d := 8 * (j + 2)) (by unfold frameBytes; omega)]) rfl)
    fun t' ⟨hm, k⟩ => ⟨Env.of he hp (k.gpr (by decide)) k.2.1 k.2.2 (hm ▸ (Frame.refl _ _).writeW
      (List.mem_singleton_self _) _ (Region.contains_self _ _)) fun r hr => .inl
      ⟨8 * (j + 2), 8, List.mem_singleton.mp hr, .inl (by unfold oOut; omega), by unfold frameBytes; omega⟩, hm, k⟩

/-- The first `n` copies. -/
theorem copies_ok {s : State} (hp : PreS s) : ∀ (n : Nat), n ≤ 12 → ∀ (t : State), Env s t →
    WP isa (.block ((List.range n).flatMap copyArg)) t fun t' => Env s t' ∧
      (∀ i < n, word t'.mem (fb s) (8 * (i + 2)) = stackArg s (i + 3)) ∧
      (∀ d, d + 8 ≤ 16 ∨ 16 + 8 * n ≤ d → d + 8 ≤ frameBytes → word t'.mem (fb s) d = word t.mem (fb s) d) ∧
      Frame [⟨fb s, 112⟩] t.mem t'.mem ∧ Keep [.rax] t t'
  | 0, _, t, he => WP.block_nil ⟨he, fun _ h => absurd h (by omega), fun _ _ _ => rfl, Frame.refl _ _,
      Keep.refl _ _⟩
  | n + 1, hn, t, he => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (copies_ok hp n (by omega) t he) fun t₁ ⟨he₁, hw₁, hk₁, hf₁, k₁⟩ => ?_
    refine WP.mono (copyArg_ok hp he₁ (show n < 12 by omega)) fun t' ⟨he', hm, k'⟩ =>
      ⟨he', fun i hi => ?_, fun d hd hd' => ?_, hf₁.trans (hm ▸ (Frame.refl _ _).writeW
        (List.mem_singleton_self _) _ (Offset.contains_base (fb s) (d := 8 * (n + 2)) (n := 8) (k := 112)
          (by omega) (by omega))), (k₁.trans k').mono (by decide)⟩
    · rw [hm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [word_wo _ _ _ (.inr (by omega)) (by unfold frameBytes at *; omega) (by unfold frameBytes at *; omega)]
        exact hw₁ i hi
      · exact word_writeW_self _ _ _ _
    · rw [hm, word_wo _ _ _ (by omega) (by unfold frameBytes at *; omega) (by unfold frameBytes at *; omega)]
      exact hk₁ d (by omega) hd'

theorem callArgs_eq : callArgs =
    (([.mov .rdi (.mem (sp oOut)), .mov .rsi (.mem (sp oOl)), .mov .rdx (.mem (sp oN)), .mov .rcx (.mem (sp oK)),
      .mov .r8 (.mem (sp oE)), .mov .r9 (.mem (sp oEl))] : List Instr) ++ lea .rax oEM ++
      ([.store (sp 0) .rax, .store (sp 8) .rcx] : List Instr)) ++ (List.range 12).flatMap copyArg := by
  simp only [callArgs, List.append_assoc]

/-- The arguments of `vg_rsa_private_checked`. -/
theorem callArgs_ok {s t : State} (hp : PreS s) (he : Env s t) :
    WP isa (.block callArgs) t fun t' => Env s t' ∧ (∀ i < 14, word t'.mem (fb s) (8 * i) = callArg s i) ∧
      t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rsi = s.gpr .rsi ∧ t'.gpr .rdx = s.gpr .rdx ∧
      t'.gpr .rcx = s.gpr .rcx ∧ t'.gpr .r8 = s.gpr .r8 ∧ t'.gpr .r9 = s.gpr .r9 ∧
      Frame [⟨fb s, 112⟩] t.mem t'.mem ∧ Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] t t' := by
  have hs := he.scr hp
  have h0 : InRegions t.wr (fb s) 8 := by
    simpa only [off, BitVec.add_zero] using hs.st (d := 0) (by decide)
  rw [callArgs_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun u =>
      u.mem = (t.mem.writeW (fb s) (off (fb s) oEM)).writeW (off (fb s) 8) (s.gpr .rcx) ∧
      u.gpr .rdi = s.gpr .rdi ∧ u.gpr .rsi = s.gpr .rsi ∧ u.gpr .rdx = s.gpr .rdx ∧
      u.gpr .rcx = s.gpr .rcx ∧ u.gpr .r8 = s.gpr .r8 ∧ u.gpr .r9 = s.gpr .r9) (by
    have h8 : InRegions t.wr (fb s + 8) 8 := hs.st (d := 8) (by decide)
    xrun [lea, List.cons_append, List.nil_append, ea_sp, he.rsp, h0, h8, hs.st (d := 8) (by decide),
      hs.ld (d := oOut) (by decide), hs.ld (d := oOl) (by decide), hs.ld (d := oN) (by decide),
      hs.ld (d := oK) (by decide), hs.ld (d := oE) (by decide), hs.ld (d := oEl) (by decide),
      he.sOut, he.sOl, he.sN, he.sK, he.sE, he.sEl, sx_ofNat (show oEM < 2 ^ 31 by decide)]) rfl) fun u ⟨⟨hm, hdi, hsi, hdx, hcx, h8, h9⟩, k⟩ => ?_
  have f : Frame [⟨fb s, 64 / 8⟩, ⟨off (fb s) 8, 64 / 8⟩] t.mem u.mem := by
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (Region.contains_self _ _)).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (Region.contains_self _ _)
  have f' : Frame [⟨fb s, 112⟩] t.mem u.mem := f.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_singleton_self _, Offset.sub_base (fb s) (d := 8) (n := 8) (k := 112) (by decide)⟩
  have heu : Env s u := by
    refine Env.of he hp (k.gpr (by decide)) k.2.1 k.2.2 f fun r hr => .inl ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨0, 8, by simp [off], .inl (by decide), by decide⟩
    · exact ⟨8, 8, rfl, .inl (by decide), by decide⟩
  refine WP.mono (copies_ok hp 12 (Nat.le_refl _) u heu) fun t' ⟨he', hw, hk, hf', k'⟩ =>
    ⟨he', fun i hi => ?_, by rw [k'.gpr (by decide), hdi], by rw [k'.gpr (by decide), hsi],
      by rw [k'.gpr (by decide), hdx], by rw [k'.gpr (by decide), hcx], by rw [k'.gpr (by decide), h8],
      by rw [k'.gpr (by decide), h9], f'.trans hf', (k.trans k').mono (by decide)⟩
  match i, hi with
  | 0, _ =>
    rw [hk 0 (.inl (by decide)) (by decide), hm]
    have := word_wo (t.mem.writeW (fb s) (off (fb s) oEM)) (fb s) (d := 8) (d' := 0) (s.gpr .rcx)
      (.inr (by decide)) (by decide) (by decide)
    rw [this]; exact Ver.word_self0 _ _ _
  | 1, _ =>
    rw [hk 8 (.inl (by decide)) (by decide), hm]; exact word_writeW_self _ _ _ _
  | i + 2, hi => exact hw i (by omega)

/-- The count and address of `EM`'s bytes, and the zero byte. -/
theorem wipeHead_ok {s t : State} (hp : PreS s) (he : Env s t) :
    WP isa (.block (([.mov .r11 (.mem (sp oK)), .mov32 .rdx (.imm 0)] : List Instr) ++ lea .r10 oEM)) t fun u =>
      Keep [.r11, .rdx, .r10] t u ∧ u.mem = t.mem ∧ u.gpr .r11 = BitVec.ofNat 64 (s.gpr .rcx).toNat ∧
      u.gpr .rdx = 0 ∧ u.gpr .r10 = off (fb s) oEM := by
  have hs := he.scr hp
  refine WP.mono (WP.keep [.r11, .rdx, .r10] (Q := fun u => u.mem = t.mem ∧
      u.gpr .r11 = BitVec.ofNat 64 (s.gpr .rcx).toNat ∧ u.gpr .rdx = 0 ∧ u.gpr .r10 = off (fb s) oEM) (by
    xrun [lea, List.cons_append, List.nil_append, ea_sp, he.rsp, hs.ld (d := oK) (by decide), he.sK,
      sx_ofNat (show oEM < 2 ^ 31 by decide), Rec.ofNat_toNat64]) rfl) fun u ⟨h, k⟩ => ⟨k, h⟩

/-- `EM` overwritten with zeros, keeping `rax`. -/
theorem wipe_ok {s t : State} (hp : PreS s) (he : Env s t) :
    WP isa wipe t fun u => Env s u ∧ u.gpr .rax = t.gpr .rax ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (s.gpr .rcx).toNat = Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat := by
  have hs := he.scr hp
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hF := fb_toNat hp
  unfold wipe
  refine WP.seq (WP.mono (wipeHead_ok hp he) fun t₁ ⟨k₁, hm₁, h11, hdx, h10⟩ => ?_)
  have he₁ : Env s t₁ := he.regs (k₁.gpr (by decide)) hm₁ k₁.2.1 k₁.2.2
  refine wp_countdown (cnt := .r11) (N := (s.gpr .rcx).toNat) (by omega) (by omega)
    (fun i u => Env s u ∧ Keep [.r11, .rdx, .r10] t₁ u ∧ u.gpr .rdx = 0 ∧
      u.gpr .r10 = off (fb s) (oEM + i) ∧
      u.mem = writeBytes t₁.mem (off (fb s) oEM) (List.replicate i 0)) ?_ (fun u ⟨heu, ku, _, _, hmu⟩ => ?_)
    ⟨he₁, Keep.refl _ _, hdx, by rw [h10]; rfl, by simp only [List.replicate_zero, writeBytes_nil]⟩ h11
  · intro i hi u ⟨heu, ku, hdxu, h10u, hmu⟩ _
    have hA : InRegions u.wr (u.gpr .r10) 1 := by
      rw [h10u, heu.wr]
      obtain ⟨r, h, c⟩ := frame_bytes hp (d := oEM + i) (n := 1) (by unfold oEM frameBytes; omega) 0 (by decide)
      exact ⟨r, h, by simpa only [BitVec.add_zero, off] using c⟩
    refine WP.mono (WP.keep [.r10, .r11] (Q := fun u' => u'.mem = u.mem.writeW (u.gpr .r10) (0 : Byte) ∧
        u'.gpr .r10 = u.gpr .r10 + 1 ∧ u'.gpr .r11 = u.gpr .r11 - 1 ∧ u'.zf = some (u.gpr .r11 - 1 == 0)) (by
      xrun [ea0, hA, hdxu]; rfl) rfl) fun u' ⟨⟨hm', h10', h11', hz⟩, k'⟩ => ⟨⟨?_, (ku.trans k').mono (by simp),
        by rw [k'.gpr (by decide), hdxu], ?_, ?_⟩, h11', hz⟩
    · refine Env.of heu hp (k'.gpr (by decide)) k'.2.1 k'.2.2 (hm' ▸ (Frame.refl _ _).writeW
        (List.mem_singleton_self _) _ (Region.contains_self _ _)) fun r hr => .inl
        ⟨oEM + i, 1, by rw [List.mem_singleton.mp hr, h10u], .inr (by unfold oEM; omega),
          by unfold oEM frameBytes; omega⟩
    · rw [h10', h10u]; exact off_off _ _ _
    · rw [hm', hmu, h10u, List.replicate_succ', writeBytes_snoc _ _ _ _ (by simp; omega), List.length_replicate,
        show off (fb s) oEM + BitVec.ofNat 64 i = off (fb s) (oEM + i) from off_off _ _ _]
  · refine ⟨heu, ku.gpr (by decide) |>.trans (k₁.gpr (by decide)), ?_⟩
    rw [hmu, hm₁]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => (frame_writeBytes t.mem _ _).bytes (R := ⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩)
      (fun r hr => ?_) (by dsimp only; omega) (List.mem_range.mp hi)
    rw [List.mem_singleton.mp hr, List.length_replicate]
    have h := hp.dKo.sub_left (frame_sub s (d := oEM) (n := (s.gpr .rcx).toNat)
      (by unfold oEM frameBytes; omega))
    rw [hp.hsi] at h
    exact h.symm

end VG.Proof.RsaPkcs1Sig.X86_64.Sgn
