import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Seal
import VerifiedGarbage.Proof.AesGcm.X86_64.Open

/-!
# AES-GCM's short path on x86-64: `open`

Untrusted: everything here is checked by Lean. After `front_ok`, the
ciphertext is copied to `G` (`copyC`), the lengths block ends `G` (`lens`),
`GHASH` of `G` (`ghash`) and the tag at `W + 112` (`tagK uO`), compared
with the received one (`recv`, `cmp uO`, as `open` does), and the data is
decrypted in place only if they match (`xorText false`): `openChk_ok` up to
the comparison, `openTail_ok` after it.
With `shortStart_ok` and `front_ok`, `openShort_ok`.
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

/-- What `open`'s short path leaves: the tag compared and the data decrypted
if it matches. -/
abbrev OpenPost (s₀ : State) (Ctx W SP D : Addr) (n R al t : Nat) (Tp : Addr) (H J : Block) (a : List Byte)
    (s : State) : Prop :=
  Env Ctx (W + BitVec.ofNat 64 16) W SP s ∧ SavedAt s.mem W s₀ ∧
    Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP 24] s₀.mem s.mem ∧
    let T := toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt s₀.mem D n)))) [ofBytes (lensBlock al n)] ^^^
      ctxCiph s₀.mem Ctx R J)
    s.gpr .rax = BitVec.ofNat 64 (if T.take t = bytesAt s₀.mem Tp t then 1 else 0) ∧
    bytesAt s.mem D n = if T.take t = bytesAt s₀.mem Tp t then gctr (ctxCiph s₀.mem Ctx R) (inc32 J) (bytesAt s₀.mem D n)
      else bytesAt s₀.mem D n

/-- `SM.keep` for a step that keeps the environment. -/
theorem SM.keepE {s₀ : State} {Ctx W SP A D : Addr} {R al n : Nat} {J : Block} {tl : BitVec 64} {s s' : State}
    (S : SM s₀ Ctx W SP A D R al n J tl s) (dD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {rs : List Region} (f : Frame rs s.mem s'.mem) (hrs : ∀ r ∈ rs, Wk W D n r)
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    SM s₀ Ctx W SP A D R al n J tl s' :=
  S.keep dD f hrs (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [he.r13, S.env.r13]
    · rw [he.r14, S.env.r14]
    · rw [he.r15, S.env.r15]
    · rw [he.rsp, S.env.rsp]) hrd hwr

theorem OutWDS.frame3 {W D SP : Addr} {n : Nat} {X : Region} (h : OutWDS W D SP n X) :
    ∀ r ∈ [(⟨W, 2560⟩ : Region), ⟨D, n⟩, below SP 24], X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h _ (.inl fun _ h => h)
  · exact h _ (.inr (.inl fun _ h => h))
  · exact h _ (.inr (.inr fun _ h => h))

/-- The comparison's result: 1 if the first `t` bytes of the tag of the
ciphertext at `D` are the received ones at `Tp`, 0 if not. -/
abbrev openK (s₀ : State) (Ctx A D : Addr) (R al n : Nat) (J : Block) (t : Nat) (Tp : Addr) : Nat :=
  if (toBytes (ghashFrom (ctxH s₀.mem Ctx) (ghash (ctxH s₀.mem Ctx)
      (blocks (padded (bytesAt s₀.mem A al) (bytesAt s₀.mem D n)))) [ofBytes (lensBlock al n)] ^^^
      ctxCiph s₀.mem Ctx R J)).take t = bytesAt s₀.mem Tp t then 1 else 0

/-- After `openChk`: the comparison's result `k` at `W + 216` and in ZF, the
data and the keystream after `K[0]` as `front_ok` left them. -/
structure OpenChk (s₀ : State) (Ctx W SP A D : Addr) (R al n : Nat) (J : Block) (t k : Nat) (s : State) :
    Prop where
  sm : SM s₀ Ctx W SP A D R al n J (BitVec.ofNat 64 t) s
  zf : s.zf = some (decide (k = 0))
  aux : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k
  dat : bytesAt s.mem D n = bytesAt s₀.mem D n
  ks : ∀ b, 16 * b < n → blockAt s.mem (W + BitVec.ofNat 64 1040 + BitVec.ofNat 64 (16 * b)) =
    ctxCiph s₀.mem Ctx R (Nat.repeat inc32 (b + 1) J)

/-- After `front_ok`: the ciphertext into `G`, the tag and the comparison. -/
theorem openChk_ok (hF : ShortFacts) {k : Nat} {s₀ s : State} {Ctx W SP Np A D : Addr} {nl al n R : Nat} {J : Block} {t : Nat}
    {Tp : Addr} (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (hal5 : al < 512) (hn5 : n < 512)
    (h32 : nb16 al + nb16 n < 32)
    (F : Front s₀ Ctx W SP A D R al n J (BitVec.ofNat 64 t) (bytesAt s₀.mem A al) s) (h1 : 1 ≤ t) (h16 : t ≤ 16)
    (hTa : s₀.mem.readW (SP + BitVec.ofNat 64 24) 64 = Tp)
    (hTar : InRegions (s₀.rd ++ s₀.wr) (SP + BitVec.ofNat 64 24) 8) (hTr : Covers [⟨Tp, t⟩] (s₀.rd ++ s₀.wr))
    (oT : OutWDS W D SP n ⟨Tp, t⟩) (oA : OutWDS W D SP n ⟨SP + BitVec.ofNat 64 24, 8⟩) :
    WP isa openChk s (OpenChk s₀ Ctx W SP A D R al n J t (openK s₀ Ctx A D R al n J t Tp)) := by
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
  have dWD : ∀ {d j : Nat}, d + j ≤ 2560 → (⟨D, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, j⟩ :=
    fun h => dD.sub_right (Lay.wSub h)
  -- The ciphertext copied to `G`.
  refine WP.seq (WP.seq ?_)
  obtain ⟨s₁, run₁, di₁, si₁, cx₁, g₁, m₁, rd₁, wr₁, z₁⟩ := copyCArgs_ok s S.env.r15 S.env.perm.w S.r296 S.r272
    S.r200 S.r208 (by omega)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have cp : CopyPre s₁ D (W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1) + nb16 al))) n :=
    ⟨si₁, di₁, cx₁, by omega, by rw [rd₁, wr₁, S.rd, S.wr]; exact C.data.ok.rd,
      by rw [wr₁]; exact S.env.perm.wC (by omega), dWD (by omega)⟩
  refine WP.mono (copyBytes_ok s₁ cp) fun s₂ ⟨m₂, g₂, rd₂, wr₂, z₂⟩ => ?_
  rw [m₁, F.dat] at m₂
  have fC : Frame [⟨W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1) + nb16 al)), n⟩]
      s.mem s₂.mem := by
    rw [m₂]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  have S₂ := S.keep dD fC (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact wk_G (by omega))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide)])
    (rd₂.trans rd₁) (wr₂.trans wr₁)
  -- The lengths block.
  refine WP.seq ?_
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
  refine WP.seq (WP.mono (ghash_ok s₃ S₃.env.r15 S₃.r288 hg1 hg8 S₃.env.perm.w
    (fun l hl => by rw [zz _ (by decide) l hl, F.z0 l hl]) (fun l hl => by rw [zz _ (by decide) l hl, F.z1 l hl]))
    fun s₄ ⟨y0, y1, g₄, m₄, rd₄, wr₄, z₄⟩ => ?_)
  have S₄ := S₃.keep dD (rs := []) (by rw [m₄]; exact Frame.refl _ _) (by simp)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₄ _ (by decide) (by decide) (by decide)) rd₄ wr₄
  -- The tag, at `W + 112`.
  have x0 : s₄.xmm .xmm0 = revMask := by
    rw [show s₄.xmm .xmm0 = s₄.zlane .xmm0 0 from rfl, z₄ _ (by decide) 0 (by decide), zz _ (by decide) 0 (by decide),
      F.z0 0 (by decide)]
  refine WP.seq (WP.block_append ?_)
  obtain ⟨s₅, run₅, tag₅, fU, g₅, rd₅, wr₅⟩ := tagK_ok (o := 112) s₄ S₄.env.r15 S₄.env.perm.w (by decide) x0
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have S₅ := S₄.keep dD fU (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inr (.inr (.inl fun _ h => h))))
    (fun r _ => by rw [g₅]) rd₅ wr₅
  have hT₅ : bytesAt s₅.mem (W + BitVec.ofNat 64 112) 16 =
      toBytes (ghashFrom (ctxH s₀.mem Ctx) (ghash (ctxH s₀.mem Ctx)
        (blocks (padded (bytesAt s₀.mem A al) (bytesAt s₀.mem D n)))) [ofBytes (lensBlock al n)] ^^^
        ctxCiph s₀.mem Ctx R J) := by
    have Ftab := F.tab
    have Fks := F.ks
    obtain ⟨mZ, hZ, fK⟩ := F.gz
    generalize hl : 4 * grp al n - (nb16 al + nb16 n + 1) = lead at *
    generalize hna' : nb16 al = na at *
    generalize hnc' : nb16 n = nc at *
    generalize hg' : grp al n = g at *
    have hmp' : 4 * g = lead + na + nc + 1 := by omega
    have T₃ : TabOk s₃.mem (W + BitVec.ofNat 64 1536) (ctxH s₀.mem Ctx) g :=
      (Ftab.keep hg8 fC fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (.inr (by omega)) (by omega) (by omega)).keep hg8 fL fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W (.inr (by omega)) (by omega) (by omega)
    have hx2 : s₄.xmm .xmm2 = ghashFrom (ctxH s₀.mem Ctx) 0 (blocksAt s₃.mem (W + BitVec.ofNat 64 512) (4 * g)) := by
      rw [show s₄.xmm .xmm2 = s₄.zlane .xmm2 0 from rfl, y0, hF.ghash T₃]
    have hK₀ : blockAt s₄.mem (W + BitVec.ofNat 64 1024) = ctxCiph s₀.mem Ctx R J := by
      rw [m₄, blockAt_frame fL (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint W (.inr (by omega)) (by omega) (by omega)),
        blockAt_frame fC (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint W (.inr (by omega)) (by omega) (by omega))]
      have := Fks 0 (by omega)
      simpa [Nat.repeat] using this
    have hcl : (bytesAt s₀.mem D n).length = n := length_bytesAt _ _ _
    have hlay := gLayout (G := W + BitVec.ofNat 64 512) (lead := lead) (na := na) (nc := nc)
      (a := bytesAt s₀.mem A al) (c := bytesAt s₀.mem D n) (lens := lensBlock al n) (mZ := mZ) (mK := s.mem)
      (mX := s₂.mem) (mL := s₃.mem) (by rw [length_bytesAt]; omega) (by omega) (by omega) hZ
      (by rw [add_ofNat_ofNat]; exact fK)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide))
      (rsX := [⟨W + BitVec.ofNat 64 (512 + 16 * (lead + na)), n⟩]) fC
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact .inl (by rw [hcl, add_ofNat_ofNat]))
      (by
        rw [m₂, add_ofNat_ofNat]
        exact bytesAt_writeBytes_self _ _ _ (by omega))
      (by rw [add_ofNat_ofNat, show 512 + 16 * (lead + na + nc) = 496 + 16 * (4 * g) by omega]; exact fL)
      (by rw [add_ofNat_ofNat, show 512 + 16 * (lead + na + nc) = 496 + 16 * (4 * g) by omega]; exact hL)
    have hpad := padded_layout (bytesAt s₀.mem A al) (bytesAt s₀.mem D n)
    rw [length_bytesAt, hcl, hna', hnc'] at hpad
    rw [length_bytesAt, hcl] at hlay
    have hG : bytesAt s₃.mem (W + BitVec.ofNat 64 512) (16 * (4 * g)) =
        zeros (16 * lead) ++ padded (bytesAt s₀.mem A al) (bytesAt s₀.mem D n) ++
          lensBlock (bytesAt s₀.mem A al).length (bytesAt s₀.mem D n).length := by
      rw [hmp', hlay, ← hpad, length_bytesAt, hcl]; simp only [List.append_assoc]
    have t5 : blockAt s₅.mem (W + BitVec.ofNat 64 112) = s₄.xmm .xmm2 ^^^ blockAt s₄.mem (W + BitVec.ofNat 64 1024) :=
      tag₅
    rw [bytesAt_toBytes']
    refine congrArg toBytes ?_
    rw [t5, hx2, hK₀, Proof.Gcm.blocksAt_eq, hG, gBlocks, List.append_assoc, ghashFrom_zeros,
      Proof.Gcm.ghashFrom_append, length_bytesAt, hcl]
    rfl
  -- The tag's length and address.
  have q₁ := S₅.env.perm.wR (show 224 + 8 ≤ 2560 by decide)
  have q₂ : InRegions (s₅.rd ++ s₅.wr) (SP + BitVec.ofNat 64 24) 8 := by rw [S₅.rd, S₅.wr]; exact hTar
  have hTa₅ : s₅.mem.readW (SP + BitVec.ofNat 64 24) 64 = Tp := by
    rw [S₅.frame.readW (r := ⟨SP + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _) (OutWDS.frame3 oA) (by decide), hTa]
  have htl₅ := S₅.r224
  obtain ⟨s₆, run₆, hbx₆, hsi₆, hg₆, hm₆, hrd₆, hwr₆⟩ : ∃ s₆, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO)),
      .mov .rsi (.mem (at_ .rsp 24))] s₅ = some s₆ ∧ s₆.gpr .rbx = BitVec.ofNat 64 t ∧ s₆.gpr .rsi = Tp ∧
      (∀ r, r ≠ .rbx → r ≠ .rsi → s₆.gpr r = s₅.gpr r) ∧ s₆.mem = s₅.mem ∧ s₆.rd = s₅.rd ∧ s₆.wr = s₅.wr := by
    refine ⟨_, by xrun [S₅.env.r15, S₅.env.rsp, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, htl₅]
    · simp [gpr_setReg, hTa₅]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  have S₆ := S₅.keep dD (rs := []) (by rw [hm₆]; exact Frame.refl _ _) (by simp)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₆ _ (by decide) (by decide)) hrd₆ hwr₆
  -- The received tag, padded, and the comparison.
  refine WP.seq (WP.mono (WP.with_rdwr (recv_ok S₆.env hbx₆ h1 h16 hsi₆
    (by rw [S₆.rd, S₆.wr]; exact hTr) (oT _ (.inl (Lay.wSub (by decide))))))
    fun s₇ ⟨⟨he₇, hr₇, f₇, hbx₇⟩, hrd₇, hwr₇⟩ => ?_)
  have S₇ := S₆.keepE dD f₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inr (.inr (.inr (.inr (.inr (Offset.sub W (by decide) (by decide)))))))
    he₇ hrd₇ hwr₇
  rw [hbx₆] at hbx₇
  refine WP.seq (WP.mono (WP.with_rdwr (cmp_ok L (o := 112) (.inr rfl) he₇ hbx₇ h1 h16 (length_bytesAt _ _ _) hr₇))
    fun s₈ ⟨⟨he₈, hax₈, f₈⟩, hrd₈, hwr₈⟩ => ?_)
  have S₈ := S₇.keepE dD f₈ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inr (.inr (.inr (.inr (.inr (Offset.sub W (by decide) (by decide)))))))
    he₈ hrd₈ hwr₈
  have hU : bytesAt s₇.mem (W + BitVec.ofNat 64 112) t = (bytesAt s₅.mem (W + BitVec.ofNat 64 112) 16).take t := by
    rw [bytesAt_take _ _ h16, bytesAt_frame f₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide), hm₆]
  have hTp₅ : bytesAt s₅.mem Tp t = bytesAt s₀.mem Tp t := bytesAt_frame S₅.frame (OutWDS.frame3 oT) (by omega)
  rw [hU, hm₆, hTp₅, ite_ofNat] at hax₈
  generalize hk : (if (bytesAt s₅.mem (W + BitVec.ofNat 64 112) 16).take t = bytesAt s₀.mem Tp t then 1 else 0) = k
    at hax₈
  have hk1 : k < 2 ^ 64 := by rw [← hk]; split <;> decide
  -- The result kept at `W + 216`.
  have w₉ := he₈.perm.wW (show 216 + 8 ≤ 2560 by decide)
  obtain ⟨s₉, run₉, hz₉, hg₉, hm₉, hrd₉, hwr₉⟩ : ∃ s₉, runBlock isa [.store (at_ .r15 auxO) .rax,
      .alu .test .rax (.reg .rax)] s₈ = some s₉ ∧ s₉.zf = some (decide (k = 0)) ∧ (∀ r, s₉.gpr r = s₈.gpr r) ∧
      s₉.mem = s₈.mem.writeW (W + BitVec.ofNat 64 216) (BitVec.ofNat 64 k) ∧ s₉.rd = s₈.rd ∧ s₉.wr = s₈.wr := by
    refine ⟨_, by xrun [he₈.r15, w₉], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, gpr_setReg, ite_true, hax₈, mem_setReg]
      exact congrArg some (and_self_beq hk1)
    · intro r; simp [gpr_arithFlags, gpr_setReg]
    · simp [mem_arithFlags, mem_setReg, hax₈]
    all_goals simp [rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.of_runBlock ⟨s₉, run₉, ?_⟩
  have f₉ : Frame [⟨W + BitVec.ofNat 64 216, 8⟩] s₈.mem s₉.mem := by
    rw [hm₉]; exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  have S₉ := S₈.keep dD f₉ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inr (.inr (.inr (.inl fun _ h => h)))))
    (fun r _ => hg₉ r) hrd₉ hwr₉
  have hax₉ : s₉.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k := by
    rw [hm₉, Mem.readW_writeW_self64]
  -- `G`, the tag and the result written since `s`, and nothing else.
  have wo : ∀ {d j e i : Nat}, e ≤ d → d + j ≤ e + i →
      ∀ r ∈ [(⟨W + BitVec.ofNat 64 d, j⟩ : Region)], ∃ r' ∈ [(⟨W + BitVec.ofNat 64 e, i⟩ : Region)], r.Sub r' :=
    fun h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, Offset.sub W h₁ h₂⟩
  let Wo : List Region := [⟨W + BitVec.ofNat 64 512, 512⟩, ⟨W + BitVec.ofNat 64 112, 16⟩,
    ⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 240, 32⟩]
  have fO : Frame Wo s.mem s₉.mem :=
    (fC.sub (rs' := Wo) fun r hr => by
      obtain ⟨r', hr', hs⟩ := wo (e := 512) (i := 512) (by omega) (by omega) r hr
      exact ⟨r', by simp only [List.mem_singleton] at hr'; subst hr'; simp [Wo], hs⟩).trans <|
    (fL.sub (rs' := Wo) fun r hr => by
      obtain ⟨r', hr', hs⟩ := wo (e := 512) (i := 512) (by omega) (by omega) r hr
      exact ⟨r', by simp only [List.mem_singleton] at hr'; subst hr'; simp [Wo], hs⟩).trans <|
    (by rw [m₄]; exact Frame.refl _ _ : Frame Wo s₃.mem s₄.mem).trans <|
    (fU.sub (rs' := Wo) fun r hr => by
      obtain ⟨r', hr', hs⟩ := wo (e := 112) (i := 16) (by omega) (by omega) r hr
      exact ⟨r', by simp only [List.mem_singleton] at hr'; subst hr'; simp [Wo], hs⟩).trans <|
    (by rw [hm₆]; exact Frame.refl _ _ : Frame Wo s₅.mem s₆.mem).trans <|
    (f₇.sub (rs' := Wo) fun r hr => by
      obtain ⟨r', hr', hs⟩ := wo (e := 240) (i := 32) (by omega) (by omega) r hr
      exact ⟨r', by simp only [List.mem_singleton] at hr'; subst hr'; simp [Wo], hs⟩).trans <|
    (f₈.sub (rs' := Wo) fun r hr => by
      obtain ⟨r', hr', hs⟩ := wo (e := 240) (i := 32) (by omega) (by omega) r hr
      exact ⟨r', by simp only [List.mem_singleton] at hr'; subst hr'; simp [Wo], hs⟩).trans <|
    (f₉.mono (by simp [Wo]))
  have dO : ∀ {d j : Nat}, 1024 ≤ d → d + j ≤ 2560 → ∀ r ∈ Wo, (⟨W + BitVec.ofNat 64 d, j⟩ : Region).Disjoint r := by
    intro d j h₁ h₂ r hr
    simp only [Wo, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact Offset.disjoint W (.inr (by omega)) (by omega) (by omega)
  have hD₉ : bytesAt s₉.mem D n = bytesAt s₀.mem D n := by
    rw [bytesAt_frame fO (fun r hr => by
      simp only [Wo, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact dWD (by decide)) (by omega), F.dat]
  have hK₉ : ∀ b, 16 * b < n → blockAt s₉.mem (W + BitVec.ofNat 64 1040 + BitVec.ofNat 64 (16 * b)) =
      ctxCiph s₀.mem Ctx R (Nat.repeat inc32 (b + 1) J) := fun b hb => by
    rw [show W + BitVec.ofNat 64 1040 + BitVec.ofNat 64 (16 * b) =
        W + BitVec.ofNat 64 1024 + BitVec.ofNat 64 (16 * (b + 1)) by
      rw [add_ofNat_ofNat, add_ofNat_ofNat, show 1040 + 16 * b = 1024 + 16 * (b + 1) by omega]]
    rw [blockAt_frame fO (by rw [add_ofNat_ofNat]; exact dO (by omega) (by omega))]
    exact F.ks (b + 1) (by omega)
  rw [hT₅] at hk
  subst hk
  exact ⟨S₉, hz₉, hax₉, hD₉, hK₉⟩

/-- After `openChk`: the data decrypted if the tags match, and `rax` the
comparison's result. -/
theorem openTail_ok {k : Nat} {s₀ s : State} {Ctx W SP Np A D : Addr} {nl al n R : Nat} {J : Block} {t K : Nat}
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (hal5 : al < 512) (hn5 : n < 512)
    (h32 : nb16 al + nb16 n < 32) (O : OpenChk s₀ Ctx W SP A D R al n J t K s) :
    WP isa (.seq (.ite .e (.block []) (.seq (.block textArgs) (xorText false)))
        (.block [.mov .rax (.mem (at_ .r15 auxO))])) s fun s' =>
      SM s₀ Ctx W SP A D R al n J (BitVec.ofNat 64 t) s' ∧ s'.gpr .rax = BitVec.ofNat 64 K ∧
      bytesAt s'.mem D n = if K = 0 then bytesAt s₀.mem D n
        else gctr (ctxCiph s₀.mem Ctx R) (inc32 J) (bytesAt s₀.mem D n) := by
  have dD := C.dE
  have h32' := h32
  simp only [nb16] at h32'
  have hlead : 4 * grp al n - (nb16 al + nb16 n + 1) < 4 := by simp only [grp, nb16]; omega
  have hna : al ≤ 16 * nb16 al ∧ 16 * nb16 al < al + 16 := by simp only [nb16]; omega
  have hnc : n ≤ 16 * nb16 n ∧ 16 * nb16 n < n + 16 := by simp only [nb16]; omega
  have dWD : ∀ {d j : Nat}, d + j ≤ 2560 → (⟨D, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, j⟩ :=
    fun h => dD.sub_right (Lay.wSub h)
  have S₉ := O.sm
  have hz₉ := O.zf
  have hax₉ := O.aux
  have hD₉ := O.dat
  have hK₉ := O.ks
  -- The data decrypted if the tags match.
  refine WP.seq (WP.mono (Q := fun (s₁₀ : State) => SM s₀ Ctx W SP A D R al n J (BitVec.ofNat 64 t) s₁₀ ∧
      s₁₀.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 K ∧
      bytesAt s₁₀.mem D n = if K = 0 then bytesAt s₀.mem D n
        else gctr (ctxCiph s₀.mem Ctx R) (inc32 J) (bytesAt s₀.mem D n))
    (WP.ite (decide (K = 0)) (eval_e hz₉) (fun ht => ?_) (fun hf => ?_)) fun s₁₀ h₁₀ => ?_)
  · have h0 : K = 0 := by simpa using ht
    exact WP.block_nil ⟨S₉, hax₉, by simp only [h0, ↓reduceIte]; exact hD₉⟩
  · have h0 : K ≠ 0 := by simpa using hf
    refine WP.seq ?_
    obtain ⟨s₁₀, run₁₀, di₁₀, si₁₀, dx₁₀, cx₁₀, g₁₀, m₁₀, rd₁₀, wr₁₀, z₁₀⟩ := textArgs_ok s S₉.env.r15
      S₉.env.perm.w S₉.r296 S₉.r272 S₉.r200 S₉.r208 (by omega)
    refine WP.of_runBlock ⟨s₁₀, run₁₀, ?_⟩
    have xp : XorPre false s₁₀ D (W + BitVec.ofNat 64 1040)
        (W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1) + nb16 al))) n :=
      ⟨si₁₀, dx₁₀, di₁₀, cx₁₀, by omega, by rw [rd₁₀, wr₁₀, S₉.rd, S₉.wr]; exact C.data.ok.rd,
        by rw [rd₁₀, wr₁₀]; exact covers_left (S₉.env.perm.wC (by omega)),
        by rw [wr₁₀, S₉.wr]; exact C.data.wr, fun h => absurd h (by decide),
        dWD (by omega), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
    refine WP.mono (xorText_ok false s₁₀ xp) fun s₁₁ ⟨m₁₁, g₁₁, rd₁₁, wr₁₁, _⟩ => ?_
    simp only [xw, Bool.false_eq_true, ↓reduceIte] at m₁₁
    have hxl : (xb s₁₀.mem D (W + BitVec.ofNat 64 1040) n).length = n := length_xb ..
    have f₁₁ : Frame [⟨D, n⟩] s.mem s₁₁.mem := by
      rw [m₁₁, m₁₀]; exact writeBytes_frame' _ (length_xb ..)
    have S₁₁ := S₉.keep dD f₁₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inr (.inl fun _ h => h)))
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;>
          rw [g₁₁ _ (by decide) (by decide) (by decide) (by decide),
            g₁₀ _ (by decide) (by decide) (by decide) (by decide)])
      (rd₁₁.trans rd₁₀) (wr₁₁.trans wr₁₀)
    refine ⟨S₁₁, ?_, ?_⟩
    · rw [f₁₁.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (w := 64) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dWD (by decide)).symm) (by decide), hax₉]
    · simp only [h0, ↓reduceIte]
      have e := bytesAt_writeBytes_self s₁₀.mem D (xb s₁₀.mem D (W + BitVec.ofNat 64 1040) n) (by rw [hxl]; omega)
      rw [hxl] at e
      rw [m₁₁, e, m₁₀, xb_gctr hK₉, hD₉]
  · obtain ⟨S₁₀, hax₁₀, hD₁₀⟩ := h₁₀
    have q₁₀ := S₁₀.env.perm.wR (show 216 + 8 ≤ 2560 by decide)
    refine WP.run (Q := fun s₁₂ => s₁₂.gpr .rax = BitVec.ofNat 64 K ∧ (∀ r, r ≠ .rax → s₁₂.gpr r = s₁₀.gpr r) ∧
        s₁₂.mem = s₁₀.mem ∧ s₁₂.rd = s₁₀.rd ∧ s₁₂.wr = s₁₀.wr)
      ⟨_, by xrun [S₁₀.env.r15, q₁₀], by simp [gpr_setReg, hax₁₀], fun r hr => by simp [gpr_setReg, hr], by rfl,
        by rfl, by rfl⟩
      fun s₁₂ ⟨hax₁₂, hg₁₂, hm₁₂, hrd₁₂, hwr₁₂⟩ => ?_
    have S₁₂ := S₁₀.keep dD (rs := []) (by rw [hm₁₂]; exact Frame.refl _ _) (by simp)
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁₂ _ (by decide)) hrd₁₂ hwr₁₂
    exact ⟨S₁₂, hax₁₂, by rw [hm₁₂, hD₁₀]⟩


/-- The short `open`, after the entry and the tag's length checked, for a
12-byte nonce and at most 32 blocks to hash. -/
theorem openShort_ok (hF : ShortFacts) {k : Nat} {s₀ s₁ : State} {Ctx W SP Np A D : Addr} {nl al n t : Nat} {Tp : Addr}
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (E : OneEntry s₀ Ctx W SP A D n s₁)
    (hNp : s₀.gpr .rdx = Np) (hnl' : (s₀.gpr .rcx).toNat = nl) (hal' : (s₀.gpr .r9).toNat = al)
    (hnl : nl = 12) (hal5 : al < 512) (hn5 : n < 512) (h32 : nb16 al + nb16 n < 32)
    (htl : s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) (h1 : 1 ≤ t) (h16 : t ≤ 16)
    (hTa : s₀.mem.readW (SP + BitVec.ofNat 64 24) 64 = Tp)
    (hTar : InRegions (s₀.rd ++ s₀.wr) (SP + BitVec.ofNat 64 24) 8) (hTr : Covers [⟨Tp, t⟩] (s₀.rd ++ s₀.wr))
    (oT : OutWDS W D SP n ⟨Tp, t⟩) (oA : OutWDS W D SP n ⟨SP + BitVec.ofNat 64 24, 8⟩) :
    WP isa openShort s₁ (OpenPost s₀ Ctx W SP D n (s₀.gpr .rsi).toNat al t Tp (ctxH s₀.mem Ctx)
      (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl)) (bytesAt s₀.mem A al)) := by
  subst hnl
  refine WP.seq (WP.mono (shortStart_ok C E hNp hnl' rfl hal' hal5 hn5) fun s₂ ⟨S, haad, hdat⟩ =>
    WP.seq (WP.mono (front_ok hF C rfl hal5 hn5 h32 (htl ▸ S) haad hdat fun _ F =>
      openChk_ok hF C hal5 hn5 h32 F h1 h16 hTa hTar hTr oT oA) fun s₃ O =>
    WP.mono (openTail_ok C hal5 hn5 h32 O) fun s' ⟨S', hax, hD⟩ => ⟨S'.env, S'.saved, S'.frame, ?_⟩))
  refine ⟨hax, ?_⟩
  rw [hD]
  simp only [openK]
  split <;> rename_i h <;> simp [h]

end VG.Proof.AesGcm.X86_64.Short
