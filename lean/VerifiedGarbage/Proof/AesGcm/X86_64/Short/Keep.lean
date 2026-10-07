import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Open

/-!
# AES-GCM's short path on x86-64: what each piece keeps

Untrusted: everything here is checked by Lean. For the constant-time proofs,
which relate two runs piece by piece: every piece of the short path keeps
`SM` (what stays in `W`, so the lengths and counts that each piece loads
first) and, after `powers`, the constants in every lane of `xmm0` and
`xmm1` (`SJ`), whatever it computes; and the registers the first block of a
piece leaves, from which the rest of it addresses memory and counts
(`lensHead_ok`, `tagMov_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- `SM`, and the constants in every lane of `xmm0` and `xmm1`. -/
structure SJ (s₀ : State) (Ctx W SP A D : Addr) (R al n : Nat) (J : Block) (tl : BitVec 64) (s : State) :
    Prop where
  sm : SM s₀ Ctx W SP A D R al n J tl s
  z0 : ∀ l < 4, s.zlane .xmm0 l = revMask
  z1 : ∀ l < 4, s.zlane .xmm1 l = poly

section
variable {k : Nat} {s₀ s : State} {Ctx W SP Np A D : Addr} {nl al n R : Nat} {J : Block} {tl : BitVec 64}

theorem powers_sj (hF : ShortFacts) (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (h32 : nb16 al + nb16 n < 32)
    (S : SM s₀ Ctx W SP A D R al n J tl s) : WP isa powers s (SJ s₀ Ctx W SP A D R al n J tl) := by
  have h32' := h32
  simp only [nb16] at h32'
  have hg1 : 1 ≤ grp al n := by simp only [grp, nb16]; omega
  have hg8 : grp al n ≤ 8 := by simp only [grp, nb16]; omega
  exact WP.mono (hF.powers s S.env S.r288 hg1 hg8) fun t ⟨_, fT, z0, z1, g, rd, wr⟩ =>
    ⟨S.keep C.dE fT (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact wk_T)
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact g _ (by decide) (by decide)) rd wr, z0, z1⟩

theorem zeroG_sj (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (S : SJ s₀ Ctx W SP A D R al n J tl s) :
    WP isa (.block zeroG) s (SJ s₀ Ctx W SP A D R al n J tl) :=
  WP.mono (zeroG_ok s S.sm.env.r15 (S.sm.env.perm.wC (by decide))) fun t ⟨m, g, rd, wr, z⟩ =>
    ⟨S.sm.keep C.dE (by rw [m]; exact writeBytes_frame' _ (List.length_replicate ..)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl (Region.sub_prefix (by decide))))
      (fun r _ => by rw [g]) rd wr,
      fun l hl => by rw [z _ (by decide) l hl, S.z0 l hl], fun l hl => by rw [z _ (by decide) l hl, S.z1 l hl]⟩

theorem copyA_sj (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (hal5 : al < 512)
    (h32 : nb16 al + nb16 n < 32) (S : SJ s₀ Ctx W SP A D R al n J tl s) :
    WP isa copyA s (SJ s₀ Ctx W SP A D R al n J tl) := by
  have h32' := h32
  simp only [nb16] at h32'
  have hlead : 4 * grp al n - (nb16 al + nb16 n + 1) < 4 := by simp only [grp, nb16]; omega
  have hna : 16 * nb16 al < al + 16 := by simp only [nb16]; omega
  refine WP.seq ?_
  obtain ⟨s₁, run₁, di₁, si₁, cx₁, g₁, m₁, rd₁, wr₁, z₁⟩ := copyAArgs_ok s S.sm.env.r15 S.sm.env.perm.w S.sm.r296
    S.sm.r232 S.sm.r184 (by omega)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have cp : CopyPre s₁ A (W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1)))) al :=
    ⟨si₁, di₁, cx₁, by omega, by rw [rd₁, wr₁, S.sm.rd, S.sm.wr]; exact C.aad.rd,
      by rw [wr₁]; exact S.sm.env.perm.wC (by omega), C.aad.w.sub_right (Lay.wSub (by omega))⟩
  refine WP.mono (copyBytes_ok s₁ cp) fun s₂ ⟨m₂, g₂, rd₂, wr₂, z₂⟩ => ⟨S.sm.keep C.dE (rs :=
      [⟨W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1))), al⟩])
      (by rw [m₂, m₁]; exact writeBytes_frame' _ (length_bytesAt _ _ _))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact wk_G (by omega))
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;>
          rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide)])
      (rd₂.trans rd₁) (wr₂.trans wr₁),
    fun l hl => by rw [z₂ _ (by decide) l hl, z₁, S.z0 l hl], fun l hl => by rw [z₂ _ (by decide) l hl, z₁, S.z1 l hl]⟩

theorem keystream_sj (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (h32 : nb16 al + nb16 n < 32) (S : SJ s₀ Ctx W SP A D R al n J tl s) :
    WP isa keystream s (SJ s₀ Ctx W SP A D R al n J tl) :=
  WP.mono (keystream_ok s S.sm.env C.lay S.sm.r176 S.sm.r280 (by omega) hR S.z0)
    fun t ⟨_, fK, gK, rdK, wrK, zK, m0K⟩ =>
    ⟨S.sm.keep C.dE fK (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl (Offset.sub W (by decide) (by decide))))
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact gK _ (by decide)) rdK wrK,
      m0K, fun l hl => by rw [zK _ (by decide) l hl, S.z1 l hl]⟩

theorem text_sm (g : Bool) (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (hn5 : n < 512)
    (h32 : nb16 al + nb16 n < 32) (S : SM s₀ Ctx W SP A D R al n J tl s) :
    WP isa (.seq (.block textArgs) (xorText g)) s fun t => SM s₀ Ctx W SP A D R al n J tl t ∧ ZKeep [.xmm4] s t := by
  have dD := C.dE
  have h32' := h32
  simp only [nb16] at h32'
  have hlead : 4 * grp al n - (nb16 al + nb16 n + 1) < 4 := by simp only [grp, nb16]; omega
  have hmp : 4 * grp al n = (4 * grp al n - (nb16 al + nb16 n + 1)) + nb16 al + nb16 n + 1 := by
    simp only [grp, nb16]; omega
  have hnc : n ≤ 16 * nb16 n := by simp only [nb16]; omega
  have hg8 : grp al n ≤ 8 := by simp only [grp, nb16]; omega
  refine WP.seq ?_
  obtain ⟨s₁, run₁, di₁, si₁, dx₁, cx₁, g₁, m₁, rd₁, wr₁, z₁⟩ := textArgs_ok s S.env.r15 S.env.perm.w
    S.r296 S.r272 S.r200 S.r208 (by omega)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have xp : XorPre g s₁ D (W + BitVec.ofNat 64 1040)
      (W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1) + nb16 al))) n :=
    ⟨si₁, dx₁, di₁, cx₁, by omega, by rw [rd₁, wr₁, S.rd, S.wr]; exact C.data.ok.rd,
      by rw [rd₁, wr₁]; exact covers_left (S.env.perm.wC (by omega)),
      by rw [wr₁, S.wr]; exact C.data.wr, fun _ => by rw [wr₁]; exact S.env.perm.wC (by omega),
      dD.sub_right (Lay.wSub (by omega)), fun _ => dD.sub_right (Lay.wSub (by omega)),
      fun _ => Offset.disjoint W (.inr (by omega)) (by omega) (by omega)⟩
  refine WP.mono (xorText_ok g s₁ xp) fun s₂ ⟨m₂, g₂, rd₂, wr₂, z₂⟩ => ?_
  have fX : Frame [⟨D, n⟩, ⟨W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1) + nb16 al)), n⟩]
      s.mem s₂.mem := by
    rw [m₂, m₁]; have := xw_frame g s.mem D (W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n -
      (nb16 al + nb16 n + 1) + nb16 al))) (xb s.mem D (W + BitVec.ofNat 64 1040) n)
    rwa [length_xb] at this
  refine ⟨S.keep dD fX (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (.inr (.inl fun _ h => h))
      · exact wk_G (by omega))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        rw [g₂ _ (by decide) (by decide) (by decide) (by decide),
          g₁ _ (by decide) (by decide) (by decide) (by decide)])
    (rd₂.trans rd₁) (wr₂.trans wr₁), fun r hr l hl => by rw [z₂ r hr l hl, z₁]⟩

theorem text_sj (g : Bool) (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (hn5 : n < 512)
    (h32 : nb16 al + nb16 n < 32) (S : SJ s₀ Ctx W SP A D R al n J tl s) :
    WP isa (.seq (.block textArgs) (xorText g)) s (SJ s₀ Ctx W SP A D R al n J tl) :=
  WP.mono (text_sm g C hn5 h32 S.sm) fun _ ⟨S', z⟩ =>
    ⟨S', fun l hl => by rw [z _ (by decide) l hl, S.z0 l hl], fun l hl => by rw [z _ (by decide) l hl, S.z1 l hl]⟩

theorem copyC_sj (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (hn5 : n < 512)
    (h32 : nb16 al + nb16 n < 32) (S : SJ s₀ Ctx W SP A D R al n J tl s) :
    WP isa copyC s (SJ s₀ Ctx W SP A D R al n J tl) := by
  have dD := C.dE
  have h32' := h32
  simp only [nb16] at h32'
  have hlead : 4 * grp al n - (nb16 al + nb16 n + 1) < 4 := by simp only [grp, nb16]; omega
  have hmp : 4 * grp al n = (4 * grp al n - (nb16 al + nb16 n + 1)) + nb16 al + nb16 n + 1 := by
    simp only [grp, nb16]; omega
  have hnc : n ≤ 16 * nb16 n := by simp only [nb16]; omega
  have hg8 : grp al n ≤ 8 := by simp only [grp, nb16]; omega
  refine WP.seq ?_
  obtain ⟨s₁, run₁, di₁, si₁, cx₁, g₁, m₁, rd₁, wr₁, z₁⟩ := copyCArgs_ok s S.sm.env.r15 S.sm.env.perm.w S.sm.r296
    S.sm.r272 S.sm.r200 S.sm.r208 (by omega)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have cp : CopyPre s₁ D (W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1) + nb16 al))) n :=
    ⟨si₁, di₁, cx₁, by omega, by rw [rd₁, wr₁, S.sm.rd, S.sm.wr]; exact C.data.ok.rd,
      by rw [wr₁]; exact S.sm.env.perm.wC (by omega), dD.sub_right (Lay.wSub (by omega))⟩
  refine WP.mono (copyBytes_ok s₁ cp) fun s₂ ⟨m₂, g₂, rd₂, wr₂, z₂⟩ => ⟨S.sm.keep dD (rs :=
      [⟨W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1) + nb16 al)), n⟩])
      (by rw [m₂, m₁]; exact writeBytes_frame' _ (length_bytesAt _ _ _))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact wk_G (by omega))
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;>
          rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide)])
      (rd₂.trans rd₁) (wr₂.trans wr₁),
    fun l hl => by rw [z₂ _ (by decide) l hl, z₁, S.z0 l hl], fun l hl => by rw [z₂ _ (by decide) l hl, z₁, S.z1 l hl]⟩

theorem lens_sj (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (hal5 : al < 512) (hn5 : n < 512)
    (h32 : nb16 al + nb16 n < 32) (S : SJ s₀ Ctx W SP A D R al n J tl s) :
    WP isa (.block Short.lens) s (SJ s₀ Ctx W SP A D R al n J tl) := by
  have h32' := h32
  simp only [nb16] at h32'
  have hg1 : 1 ≤ grp al n := by simp only [grp, nb16]; omega
  have hg8 : grp al n ≤ 8 := by simp only [grp, nb16]; omega
  obtain ⟨t, run, fL, -, g, rd, wr, z⟩ := lensG_ok s S.sm.env.r15 S.sm.env.perm.w S.sm.r288 (by omega) (by omega)
    S.sm.r184 S.sm.r208 (by omega) (by omega)
  exact WP.of_runBlock ⟨t, run, S.sm.keep C.dE fL (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl (Offset.sub W (by omega) (by omega))))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g _ (by decide) (by decide)) rd wr,
    fun l hl => by rw [z, S.z0 l hl], fun l hl => by rw [z, S.z1 l hl]⟩

theorem ghash_sj (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (h32 : nb16 al + nb16 n < 32)
    (S : SJ s₀ Ctx W SP A D R al n J tl s) : WP isa ghash s (SJ s₀ Ctx W SP A D R al n J tl) := by
  have h32' := h32
  simp only [nb16] at h32'
  have hg1 : 1 ≤ grp al n := by simp only [grp, nb16]; omega
  have hg8 : grp al n ≤ 8 := by simp only [grp, nb16]; omega
  exact WP.mono (ghash_ok s S.sm.env.r15 S.sm.r288 hg1 hg8 S.sm.env.perm.w S.z0 S.z1)
    fun t ⟨_, _, g, m, rd, wr, z⟩ =>
    ⟨S.sm.keep C.dE (rs := []) (by rw [m]; exact Frame.refl _ _) (by simp)
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact g _ (by decide) (by decide) (by decide)) rd wr,
      fun l hl => by rw [z _ (by decide) l hl, S.z0 l hl], fun l hl => by rw [z _ (by decide) l hl, S.z1 l hl]⟩

theorem tagK_sm (C : OneCtx s₀ k Ctx W SP Np A D nl al n) {o : Nat} (ho : o = 0 ∨ o = 112)
    (S : SJ s₀ Ctx W SP A D R al n J tl s) : WP isa (.block (tagK o)) s (SM s₀ Ctx W SP A D R al n J tl) := by
  obtain ⟨t, run, -, fU, g, rd, wr⟩ := tagK_ok (o := o) s S.sm.env.r15 S.sm.env.perm.w (by omega)
    (by rw [show s.xmm .xmm0 = s.zlane .xmm0 0 from rfl, S.z0 0 (by decide)])
  refine WP.of_runBlock ⟨t, run, S.sm.keep C.dE fU (fun r hr => ?_) (fun r _ => by rw [g]) rd wr⟩
  simp only [List.mem_singleton] at hr; subst hr
  rcases ho with rfl | rfl
  · exact .inl (by simpa using Region.sub_prefix (base := W) (Nat.le_refl 16))
  · exact .inr (.inr (.inr (.inl fun _ h => h)))

/-- `lens`' first instructions: `rdi` at the lengths block, the last of `mp`. -/
theorem lensHead_ok {W : Addr} {mp : Nat} (s : State) (h15 : s.gpr .r15 = W) (hw : Covers [⟨W, 2560⟩] s.wr)
    (hmp : s.mem.readW (W + BitVec.ofNat 64 288) 64 = BitVec.ofNat 64 mp) (hmp32 : mp ≤ 32) :
    WP isa (.block [.mov .rdi (.mem (at_ .r15 mpO)), .shift .shl .rdi 4, .alu .add .rdi (.reg .r15),
        .alu .add .rdi (imm (gO - 16))]) s fun t => t.gpr .rdi = W + BitVec.ofNat 64 (496 + 16 * mp) := by
  have r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 288) 8 := in_left (in_off hw (by decide) (by decide))
  have e₁ : BitVec.ofNat 64 mp <<< 4 + W + BitVec.ofNat 64 496 = W + BitVec.ofNat 64 (496 + 16 * mp) := by
    rw [shl_ofNat (by omega), BitVec.add_comm _ W, add_ofNat_ofNat]; congr 2; omega
  refine WP.of_runBlock ⟨_, by xrun [execShift, h15, hmp, r₁, mpO, gO, e₁], ?_⟩
  simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, h15, e₁]

/-- `tagK uO`, then the tag's length and the received tag's address. -/
theorem tagMov_ok {k : Nat} {s₀ s : State} {Ctx W SP Np A D Tp : Addr} {nl al n R t : Nat} {J : Block}
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (S : SJ s₀ Ctx W SP A D R al n J (BitVec.ofNat 64 t) s)
    (hTa : s₀.mem.readW (SP + BitVec.ofNat 64 24) 64 = Tp)
    (hTar : InRegions (s₀.rd ++ s₀.wr) (SP + BitVec.ofNat 64 24) 8)
    (oA : OutWDS W D SP n ⟨SP + BitVec.ofNat 64 24, 8⟩) :
    WP isa (.block (tagK uO ++ ([.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))] : List Instr))) s
      fun u =>
      SM s₀ Ctx W SP A D R al n J (BitVec.ofNat 64 t) u ∧ u.gpr .rbx = BitVec.ofNat 64 t ∧ u.gpr .rsi = Tp := by
  refine WP.block_append (WP.mono (tagK_sm C (.inr rfl) S) fun s₅ S₅ => ?_)
  have q₁ := S₅.env.perm.wR (show 224 + 8 ≤ 2560 by decide)
  have q₂ : InRegions (s₅.rd ++ s₅.wr) (SP + BitVec.ofNat 64 24) 8 := by rw [S₅.rd, S₅.wr]; exact hTar
  have hTa₅ : s₅.mem.readW (SP + BitVec.ofNat 64 24) 64 = Tp := by
    rw [S₅.frame.readW (r := ⟨SP + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _) (OutWDS.frame3 oA) (by decide),
      hTa]
  have htl₅ := S₅.r224
  obtain ⟨s₆, run₆, hbx₆, hsi₆, hg₆, hm₆, hrd₆, hwr₆⟩ : ∃ s₆, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO)),
      .mov .rsi (.mem (at_ .rsp 24))] s₅ = some s₆ ∧ s₆.gpr .rbx = BitVec.ofNat 64 t ∧ s₆.gpr .rsi = Tp ∧
      (∀ r, r ≠ .rbx → r ≠ .rsi → s₆.gpr r = s₅.gpr r) ∧ s₆.mem = s₅.mem ∧ s₆.rd = s₅.rd ∧ s₆.wr = s₅.wr := by
    refine ⟨_, by xrun [S₅.env.r15, S₅.env.rsp, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, htl₅]
    · simp [gpr_setReg, hTa₅]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  exact WP.of_runBlock ⟨s₆, run₆, S₅.keep C.dE (rs := []) (by rw [hm₆]; exact Frame.refl _ _) (by simp)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₆ _ (by decide) (by decide)) hrd₆ hwr₆, hbx₆, hsi₆⟩

end

end VG.Proof.AesGcm.X86_64.Short
