import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Layout
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Tab

/-!
# AES-GCM's short path on x86-64: the powers, `G` and the keystream

Untrusted: everything here is checked by Lean. `front_ok`: after `J₀` and
the counts, what `seal` and `open` share: the table of powers (`powers`),
`G` zeroed with the additional data copied in after its zero blocks
(`zeroG`, `copyA`), and the keystream (`keystream`), each written in its own
part of `W` (`Front`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt inc32 zeros ctxH ctxCiph)

/-- After the powers, `G` and the keystream. -/
structure Front (s₀ : State) (Ctx W SP A D : Addr) (R al n : Nat) (J : Block) (tl : BitVec 64) (a : List Byte)
    (s : State) :
    Prop where
  sm : SM s₀ Ctx W SP A D R al n J tl s
  tab : TabOk s.mem (W + BitVec.ofNat 64 1536) (ctxH s₀.mem Ctx) (grp al n)
  z0 : ∀ l < 4, s.zlane .xmm0 l = revMask
  z1 : ∀ l < 4, s.zlane .xmm1 l = poly
  ks : ∀ b < 4 * ((nb16 n + 4) / 4), blockAt s.mem (W + BitVec.ofNat 64 1024 + BitVec.ofNat 64 (16 * b)) =
    ctxCiph s₀.mem Ctx R (Nat.repeat inc32 b J)
  gz : ∃ mZ, bytesAt mZ (W + BitVec.ofNat 64 512) 512 = zeros 512 ∧
    Frame [⟨W + BitVec.ofNat 64 1024, 512⟩]
      (writeBytes mZ (W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1)))) a) s.mem
  dat : bytesAt s.mem D n = bytesAt s₀.mem D n

/-- What the code may write, outside the key context. -/
theorem ctx_frame {k : Nat} {s₀ : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) {m : Mem} (f : Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP 24] s₀.mem m)
    {p : Addr} {j : Nat} (hs : Region.Sub ⟨p, j⟩ ⟨Ctx, 256⟩) (hj : j ≤ 256) : bytesAt m p j = bytesAt s₀.mem p j :=
  bytesAt_frame f (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact C.lay.cw'.sub_left hs
    · exact C.data.ctx.sub_left hs
    · exact C.t_c.symm.sub_left hs) (by omega)

theorem ctxH_frame {k : Nat} {s₀ : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) {m : Mem} (f : Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP 24] s₀.mem m) :
    ctxH m Ctx = ctxH s₀.mem Ctx := by
  rw [ctxH_eq, ctxH_eq, blockAt, blockAt, ctx_frame C f (Lay.ctxSub (by decide)) (by decide)]

theorem ciph_frame' {k : Nat} {s₀ : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) {m : Mem} (f : Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP 24] s₀.mem m)
    {R : Nat} (hR : R ≤ 14) : ciphOf m Ctx R = ctxCiph s₀.mem Ctx R := by
  simp only [ciphOf, ctxCiph]
  rw [ctx_frame C f (Region.sub_prefix (by omega)) (by omega)]

theorem wk_T {W D : Addr} {n : Nat} : Wk W D n ⟨W + BitVec.ofNat 64 1536, 512⟩ :=
  .inr (.inl (Offset.sub W (by decide) (by decide)))

theorem wk_G {W D : Addr} {n : Nat} {o k : Nat} (h : o + k ≤ 1536) : Wk W D n ⟨W + BitVec.ofNat 64 (512 + o), k⟩ :=
  .inr (.inl (Offset.sub W (by omega) (by omega)))

/-- The powers, `G` and the keystream, then `rest`. -/
theorem front_ok (hF : ShortFacts) {k : Nat} {s₀ s : State} {Ctx W SP Np A D : Addr} {nl al n R : Nat} {J : Block} {tl : BitVec 64}
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (hR : R = (s₀.gpr .rsi).toNat)
    (hal5 : al < 512) (hn5 : n < 512) (h32 : nb16 al + nb16 n < 32)
    (S : SM s₀ Ctx W SP A D R al n J tl s) (haad : bytesAt s.mem A al = bytesAt s₀.mem A al)
    (hdat : bytesAt s.mem D n = bytesAt s₀.mem D n)
    {rest : Prog isa} {Q : State → Prop}
    (hrest : ∀ t, Front s₀ Ctx W SP A D R al n J tl (bytesAt s₀.mem A al) t → WP isa rest t Q) :
    WP isa (.seq powers (.seq (.block zeroG) (.seq copyA (.seq keystream rest)))) s Q := by
  have L := C.lay
  have dD := C.dE
  have h32' := h32
  simp only [nb16] at h32'
  have hg1 : 1 ≤ grp al n := by simp only [grp, nb16]; omega
  have hg8 : grp al n ≤ 8 := by simp only [grp, nb16]; omega
  have hlead : 4 * grp al n - (nb16 al + nb16 n + 1) < 4 := by simp only [grp, nb16]; omega
  have hR' : R = 10 ∨ R = 12 ∨ R = 14 := hR ▸ C.rounds
  -- The powers.
  refine WP.seq (WP.mono (hF.powers s S.env S.r288 hg1 hg8) fun s₃ ⟨tab₃, fT, z0₃, z1₃, g₃, rd₃, wr₃⟩ => ?_)
  have S₃ := S.keep dD fT (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact wk_T)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide)) rd₃ wr₃
  rw [ctxH_frame C S.frame] at tab₃
  have dT : ∀ {m m' : Mem}, Frame [⟨W + BitVec.ofNat 64 1536, 512⟩] m m' → ∀ {p : Addr} {j : Nat},
      (⟨p, j⟩ : Region).Disjoint ⟨W, 2560⟩ → j ≤ 2 ^ 64 → bytesAt m' p j = bytesAt m p j := fun f _ _ h hj =>
    bytesAt_frame f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.sub_right (Lay.wSub (by decide))) hj
  have haad₃ : bytesAt s₃.mem A al = bytesAt s₀.mem A al := by rw [dT fT C.aad.w (by omega), haad]
  have hdat₃ : bytesAt s₃.mem D n = bytesAt s₀.mem D n := by rw [dT fT dD (by omega), hdat]
  -- `G` zeroed.
  refine WP.seq (WP.mono (zeroG_ok s₃ S₃.env.r15 (S₃.env.perm.wC (by decide)))
    fun s₄ ⟨m₄, g₄, rd₄, wr₄, z₄⟩ => ?_)
  have fG : Frame [⟨W + BitVec.ofNat 64 512, 512⟩] s₃.mem s₄.mem := by rw [m₄]; exact writeBytes_frame' _ (List.length_replicate ..)
  have S₄ := S₃.keep dD fG (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl (Region.sub_prefix (by decide))))
    (fun r _ => by rw [g₄]) rd₄ wr₄
  have tab₄ := tab₃.keep hg8 fG fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
  have dG : ∀ {p : Addr} {j : Nat}, (⟨p, j⟩ : Region).Disjoint ⟨W, 2560⟩ → j ≤ 2 ^ 64 →
      bytesAt s₄.mem p j = bytesAt s₃.mem p j := fun h hj =>
    bytesAt_frame fG (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.sub_right (Lay.wSub (by decide))) hj
  have hZ : bytesAt s₄.mem (W + BitVec.ofNat 64 512) 512 = zeros 512 := by
    have := bytesAt_writeBytes_self s₃.mem (W + BitVec.ofNat 64 512) (List.replicate 512 0)
      (by rw [List.length_replicate]; decide)
    rw [List.length_replicate] at this
    rw [m₄, this]; rfl
  -- The additional data copied to `G`.
  refine WP.seq (WP.seq ?_)
  obtain ⟨s₄', run₄', di₄, si₄, cx₄, g₄', m₄', rd₄', wr₄', z₄'⟩ := copyAArgs_ok s₄ S₄.env.r15 S₄.env.perm.w S₄.r296
    S₄.r232 S₄.r184 (by omega)
  refine WP.of_runBlock ⟨s₄', run₄', ?_⟩
  have hal63 : al < 2 ^ 63 := by omega
  have cp : CopyPre s₄' A (W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1)))) al :=
    ⟨si₄, di₄, cx₄, hal63, by rw [rd₄', wr₄', S₄.rd, S₄.wr]; exact C.aad.rd,
      by rw [wr₄']; exact S₄.env.perm.wC (by omega),
      C.aad.w.sub_right (Lay.wSub (by omega))⟩
  refine WP.mono (copyBytes_ok s₄' cp) fun s₅ ⟨m₅, g₅, rd₅, wr₅, z₅⟩ => ?_
  have ha₄ : bytesAt s₄.mem A al = bytesAt s₀.mem A al := by rw [dG C.aad.w (by omega), haad₃]
  rw [m₄', ha₄] at m₅
  have fA : Frame [⟨W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1))), al⟩] s₄.mem s₅.mem := by
    rw [m₅]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  have S₅ := S₄.keep dD fA (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact wk_G (by omega))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        rw [g₅ _ (by decide) (by decide) (by decide), g₄' _ (by decide) (by decide) (by decide)])
    (rd₅.trans rd₄') (wr₅.trans wr₄')
  have tab₅ := tab₄.keep hg8 fA fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W (.inr (by omega)) (by omega) (by omega)
  have hdat₅ : bytesAt s₅.mem D n = bytesAt s₀.mem D n := by
    rw [bytesAt_frame fA (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dD.sub_right (Lay.wSub (by omega))) (by omega),
      dG dD (by omega), hdat₃]
  have zz : ∀ r, r ≠ .xmm2 → r ≠ .xmm4 → ∀ l < 4, s₅.zlane r l = s₃.zlane r l := fun r h₂ h₄ l hl => by
    rw [z₅ r (by simp [h₄]) l hl, z₄' r l, z₄ r (by simp [h₂]) l hl]
  -- The keystream.
  refine WP.seq (WP.mono (keystream_ok s₅ S₅.env L (hR ▸ S₅.r176) S₅.r280 (by omega) (hR ▸ hR')
    (fun l hl => by rw [zz _ (by decide) (by decide) l hl, z0₃ l hl]))
    fun s₆ ⟨kb, fK, gK, rdK, wrK, zK, m0K⟩ => ?_)
  have S₆ := S₅.keep dD fK (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl (Offset.sub W (by decide) (by decide))))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact gK _ (by decide)) rdK wrK
  refine hrest s₆ ⟨S₆, tab₅.keep hg8 fK fun r hr => ?_, m0K, fun l hl => ?_, fun b hb => ?_,
    ⟨s₄.mem, hZ, by rw [← m₅]; exact fK⟩, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
  · rw [zK _ (by decide) l hl, zz _ (by decide) (by decide) l hl, z1₃ l hl]
  · rw [kb b hb, S₅.j0, ciph_frame' C S₅.frame (by omega), hR]
  · rw [bytesAt_frame fK (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dD.sub_right (Lay.wSub (by decide))) (by omega),
      hdat₅]

end VG.Proof.AesGcm.X86_64.Short
