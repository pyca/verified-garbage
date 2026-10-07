import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Front

/-!
# AES-GCM's short path on x86-64: `seal`

Untrusted: everything here is checked by Lean. After `front_ok`, the text
is encrypted in place with the keystream and copied to `G`
(`xorText true`), the lengths block ends `G` (`lens`), `GHASH` of `G`
(`ghash`), and the tag at `W` (`tagK 0`): `sealBack_ok`. With
`shortStart_ok` and `front_ok`, `sealShort_ok` leaves what `sealRun_ok`
does.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt blocks inc32 zeros ctxH ctxCiph gctr ghash ghashFrom ofBytes toBytes)
open VG.Proof.Gcm (padded lensBlock)

theorem bytesAt_toBytes' (m : Mem) (p : Addr) : bytesAt m p 16 = toBytes (blockAt m p) := by
  rw [blockAt, Proof.Cmac.toBytes_ofBytes (length_bytesAt _ _ _)]

/-- What `seal` leaves (`sealRun_ok`'s postcondition). -/
abbrev SealPost (s₀ : State) (Ctx W SP D : Addr) (n R al : Nat) (H J : Block) (a : List Byte) (s : State) :
    Prop :=
  Env Ctx (W + BitVec.ofNat 64 16) W SP s ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
    SavedAt s.mem W s₀ ∧ Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP 24] s₀.mem s.mem ∧
    bytesAt s.mem D n = gctr (ctxCiph s₀.mem Ctx R) (inc32 J) (bytesAt s₀.mem D n) ∧
    bytesAt s.mem W 16 = toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt s.mem D n))))
      [ofBytes (lensBlock al n)] ^^^ ctxCiph s₀.mem Ctx R J)

/-- After `front_ok`: the text, `G`'s lengths block, `GHASH` and the tag. -/
theorem sealBack_ok (hF : ShortFacts) {k : Nat} {s₀ s : State} {Ctx W SP Np A D : Addr} {nl al n R : Nat} {J : Block} {tl : BitVec 64}
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (hal5 : al < 512) (hn5 : n < 512) (h32 : nb16 al + nb16 n < 32)
    (F : Front s₀ Ctx W SP A D R al n J tl (bytesAt s₀.mem A al) s) :
    WP isa (.seq (.seq (.block textArgs) (xorText true)) (.seq sealShort.ghash' (.block (tagK 0)))) s
      (SealPost s₀ Ctx W SP D n R al (ctxH s₀.mem Ctx) J (bytesAt s₀.mem A al)) := by
  have L := C.lay
  have dD := C.dE
  have h32' := h32
  simp only [nb16] at h32'
  have hg1 : 1 ≤ grp al n := by simp only [grp, nb16]; omega
  have hg8 : grp al n ≤ 8 := by simp only [grp, nb16]; omega
  have hmp : 4 * grp al n = (4 * grp al n - (nb16 al + nb16 n + 1)) + nb16 al + nb16 n + 1 := by
    simp only [grp, nb16]; omega
  have hlead : 4 * grp al n - (nb16 al + nb16 n + 1) < 4 := by simp only [grp, nb16]; omega
  have hna : al ≤ 16 * nb16 al ∧ 16 * nb16 al < al + 16 := by simp only [nb16]; omega
  have hnc : n ≤ 16 * nb16 n ∧ 16 * nb16 n < n + 16 := by simp only [nb16]; omega
  have S := F.sm
  -- The text.
  refine WP.seq (WP.seq ?_)
  obtain ⟨s₁, run₁, di₁, si₁, dx₁, cx₁, g₁, m₁, rd₁, wr₁, z₁⟩ := textArgs_ok s S.env.r15 S.env.perm.w S.r296 S.r272
    S.r200 S.r208 (by omega)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have xp : XorPre true s₁ D (W + BitVec.ofNat 64 1040)
      (W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1) + nb16 al))) n :=
    ⟨si₁, dx₁, di₁, cx₁, by omega, by rw [rd₁, wr₁, S.rd, S.wr]; exact C.data.ok.rd,
      by rw [rd₁, wr₁]; exact covers_left (S.env.perm.wC (by omega)),
      by rw [wr₁, S.wr]; exact C.data.wr, fun _ => by rw [wr₁]; exact S.env.perm.wC (by omega),
      dD.sub_right (Lay.wSub (by omega)), fun _ => dD.sub_right (Lay.wSub (by omega)),
      fun _ => Offset.disjoint W (.inr (by omega)) (by omega) (by omega)⟩
  refine WP.mono (xorText_ok true s₁ xp) fun s₂ ⟨m₂, g₂, rd₂, wr₂, z₂⟩ => ?_
  have S₁ := S.keep dD (rs := []) (by rw [m₁]; exact Frame.refl _ _) (by simp)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide) (by decide)) rd₁ wr₁
  have fX : Frame [⟨D, n⟩, ⟨W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1) + nb16 al)), n⟩]
      s₁.mem s₂.mem := by
    rw [m₂]; have := xw_frame true s₁.mem D (W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1) +
      nb16 al))) (xb s₁.mem D (W + BitVec.ofNat 64 1040) n)
    rwa [length_xb] at this
  have S₂ := S₁.keep dD fX (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (.inr (.inl fun _ h => h))
      · exact wk_G (by omega))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide) (by decide) (by decide)) rd₂ wr₂
  -- The lengths block.
  refine WP.seq (WP.seq ?_)
  obtain ⟨s₃, run₃, fL, hL, g₃, rd₃, wr₃, z₃⟩ := lensG_ok s₂ S₂.env.r15 S₂.env.perm.w S₂.r288 (by omega) (by omega)
    S₂.r184 S₂.r208 (by omega) (by omega)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have S₃ := S₂.keep dD fL (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl (Offset.sub W (by omega) (by omega))))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide)) rd₃ wr₃
  -- `GHASH` of `G`.
  have zz : ∀ r, r ≠ .xmm4 → ∀ l < 4, s₃.zlane r l = s.zlane r l := fun r h l hl => by
    rw [z₃ r l, z₂ r (by simp [h]) l hl, z₁ r l]
  refine WP.mono (ghash_ok s₃ S₃.env.r15 S₃.r288 hg1 hg8 S₃.env.perm.w
    (fun l hl => by rw [zz _ (by decide) l hl, F.z0 l hl]) (fun l hl => by rw [zz _ (by decide) l hl, F.z1 l hl]))
    fun s₄ ⟨y0, y1, g₄, m₄, rd₄, wr₄, z₄⟩ => ?_
  have S₄ := S₃.keep dD (rs := []) (by rw [m₄]; exact Frame.refl _ _) (by simp)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₄ _ (by decide) (by decide) (by decide)) rd₄ wr₄
  -- The tag.
  have x0 : s₄.xmm .xmm0 = revMask := by
    rw [show s₄.xmm .xmm0 = s₄.zlane .xmm0 0 from rfl, z₄ _ (by decide) 0 (by decide), zz _ (by decide) 0 (by decide),
      F.z0 0 (by decide)]
  obtain ⟨s₅, run₅, tag₅, fW, g₅, rd₅, wr₅⟩ := tagK_ok (o := 0) s₄ S₄.env.r15 S₄.env.perm.w (by decide) x0
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have S₅ := S₄.keep dD fW (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inl (by simpa using Region.sub_prefix (base := W) (Nat.le_refl 16)))
    (fun r _ => by rw [g₅]) rd₅ wr₅
  have Ftab := F.tab
  have Fks := F.ks
  have Fdat := F.dat
  obtain ⟨mZ, hZ, fK⟩ := F.gz
  -- Shorthands for the counts and the addresses.
  generalize hl : 4 * grp al n - (nb16 al + nb16 n + 1) = lead at *
  generalize hna' : nb16 al = na at *
  generalize hnc' : nb16 n = nc at *
  generalize hg' : grp al n = g at *
  have hmp' : 4 * g = lead + na + nc + 1 := by omega
  -- The ciphertext.
  generalize hc : xb s₁.mem D (W + BitVec.ofNat 64 1040) n = c at m₂
  have hcl : c.length = n := by rw [← hc, length_xb]
  have dWD : ∀ {d j : Nat}, d + j ≤ 2560 → (⟨D, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, j⟩ :=
    fun h => dD.sub_right (Lay.wSub h)
  have hct : bytesAt s₅.mem D n = c := by
    rw [bytesAt_frame fW (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dWD (by decide)) (by omega),
      m₄, bytesAt_frame fL (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dWD (by omega)) (by omega),
      m₂]
    simp only [xw, ↓reduceIte]
    rw [bytesAt_frame (writeBytes_frame' _ hcl) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dWD (by omega)) (by omega), ← hcl]
    exact bytesAt_writeBytes_self _ _ _ (by omega)
  have hcg : c = gctr (ctxCiph s₀.mem Ctx R) (inc32 J) (bytesAt s₀.mem D n) := by
    rw [← hc, ← Fdat, ← m₁]
    refine xb_gctr fun b hb => ?_
    rw [m₁, show W + BitVec.ofNat 64 1040 + BitVec.ofNat 64 (16 * b) =
        W + BitVec.ofNat 64 1024 + BitVec.ofNat 64 (16 * (b + 1)) by
      rw [add_ofNat_ofNat, add_ofNat_ofNat, show 1040 + 16 * b = 1024 + 16 * (b + 1) by omega]]
    exact Fks (b + 1) (by omega)
  refine ⟨S₅.env, S₅.rd, S₅.wr, S₅.saved, S₅.frame, by rw [hct, hcg], ?_⟩
  rw [hct, bytesAt_toBytes']
  have T₁ : TabOk s₁.mem (W + BitVec.ofNat 64 1536) (ctxH s₀.mem Ctx) g := by rw [m₁]; exact Ftab
  have T₃ : TabOk s₃.mem (W + BitVec.ofNat 64 1536) (ctxH s₀.mem Ctx) g :=
    (T₁.keep hg8 fX fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (dWD (by decide)).symm
      · exact Offset.disjoint W (.inr (by omega)) (by omega) (by omega)).keep hg8 fL fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W (.inr (by omega)) (by omega) (by omega)
  have hx2 : s₄.xmm .xmm2 = ghashFrom (ctxH s₀.mem Ctx) 0 (blocksAt s₃.mem (W + BitVec.ofNat 64 512) (4 * g)) := by
    rw [show s₄.xmm .xmm2 = s₄.zlane .xmm2 0 from rfl, y0, hF.ghash T₃]
  have hK₀ : blockAt s₄.mem (W + BitVec.ofNat 64 1024) = ctxCiph s₀.mem Ctx R J := by
    rw [m₄, blockAt_frame fL (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W (.inr (by omega)) (by omega) (by omega)),
      blockAt_frame fX (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (dWD (by decide)).symm
        · exact Offset.disjoint W (.inr (by omega)) (by omega) (by omega)), m₁]
    have := Fks 0 (by omega)
    simpa [Nat.repeat] using this
  -- `G`.
  have hlay := gLayout (G := W + BitVec.ofNat 64 512) (lead := lead) (na := na) (nc := nc)
    (a := bytesAt s₀.mem A al) (c := c) (lens := lensBlock al n) (mZ := mZ) (mK := s₁.mem) (mX := s₂.mem)
    (mL := s₃.mem) (by rw [length_bytesAt]; omega) (by omega) (by omega) hZ
    (by rw [m₁, add_ofNat_ofNat]; exact fK)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide))
    (rsX := [⟨D, n⟩, ⟨W + BitVec.ofNat 64 (512 + 16 * (lead + na)), n⟩]) fX
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (dD.sub_right (Lay.wSub (by decide))).symm
      · exact .inl (by rw [hcl, add_ofNat_ofNat]))
    (by
      rw [m₂, add_ofNat_ofNat, hcl]
      simp only [xw, ↓reduceIte]
      rw [← hcl]; exact bytesAt_writeBytes_self _ _ _ (by omega))
    (by rw [add_ofNat_ofNat, show 512 + 16 * (lead + na + nc) = 496 + 16 * (4 * g) by omega]; exact fL)
    (by rw [add_ofNat_ofNat, show 512 + 16 * (lead + na + nc) = 496 + 16 * (4 * g) by omega]; exact hL)
  have hpad := padded_layout (bytesAt s₀.mem A al) c
  rw [length_bytesAt, hcl, hna', hnc'] at hpad
  rw [length_bytesAt, hcl] at hlay
  have hG : bytesAt s₃.mem (W + BitVec.ofNat 64 512) (16 * (4 * g)) =
      zeros (16 * lead) ++ padded (bytesAt s₀.mem A al) c ++
        lensBlock (bytesAt s₀.mem A al).length c.length := by
    rw [hmp', hlay, ← hpad, length_bytesAt, hcl]; simp only [List.append_assoc]
  have t5 : blockAt s₅.mem W = s₄.xmm .xmm2 ^^^ blockAt s₄.mem (W + BitVec.ofNat 64 1024) := by
    simpa using tag₅
  refine congrArg toBytes ?_
  rw [t5, hx2, hK₀, Proof.Gcm.blocksAt_eq, hG, gBlocks, List.append_assoc, ghashFrom_zeros,
    Proof.Gcm.ghashFrom_append, length_bytesAt, hcl]
  rfl

/-- The short `seal`, after the entry, for a 12-byte nonce and at most 32
blocks to hash: what `sealRun_ok` leaves. -/
theorem sealShort_ok (hF : ShortFacts) {k : Nat} {s₀ s₁ : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (E : OneEntry s₀ Ctx W SP A D n s₁)
    (hNp : s₀.gpr .rdx = Np) (hnl' : (s₀.gpr .rcx).toNat = nl) (hal' : (s₀.gpr .r9).toNat = al)
    (hnl : nl = 12) (hal5 : al < 512) (hn5 : n < 512) (h32 : nb16 al + nb16 n < 32) :
    WP isa sealShort s₁ (SealPost s₀ Ctx W SP D n (s₀.gpr .rsi).toNat al (ctxH s₀.mem Ctx)
      (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl)) (bytesAt s₀.mem A al)) := by
  subst hnl
  exact WP.seq (WP.mono (shortStart_ok C E hNp hnl' rfl hal' hal5 hn5) fun s₂ ⟨S, haad, hdat⟩ =>
    front_ok hF C rfl hal5 hn5 h32 S haad hdat fun t F => sealBack_ok hF C hal5 hn5 h32 F)

end VG.Proof.AesGcm.X86_64.Short
