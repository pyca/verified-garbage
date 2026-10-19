module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Tab
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Mid
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Ks
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# AES-GCM's short path on x86-64: the powers, `G` and the keystream

Untrusted: everything here is checked by Lean. `front_ok`: after `J₀` and
the counts, what `seal` and `open` share: the table of powers (`powers`,
or any code `pw` that leaves the same, `PowFrom`),
`G` zeroed with the additional data copied in after its zero blocks
(`zeroG`, `copyA`), and the keystream (`keystream`), each written in its own
part of `W` (`Front`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Proof.Gcm.X86_64.Pclmul (reduceB)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt inc32 zeros ctxH ctxCiph)

/-- How GHASH sees the table of powers: in `tm m`, the memory `m` with the
table at `W + 1536` as GHASH reads it (`m` itself when it reads the table
there; with a prepared key context, the context's powers put there). What
it reads of the table is kept by writes in `W` below the table or in the
data, and `tm m` is `m` but for the table. -/
structure TabView (tm : Mem → Mem) (W D : Addr) (n : Nat) : Prop where
  keep : ∀ {rs : List Region} {m m' : Mem}, Frame rs m m' →
    (∀ r ∈ rs, (⟨W + BitVec.ofNat 64 1536, 512⟩ : Region).Disjoint r ∧
      (Region.Sub r ⟨W, 1536⟩ ∨ Region.Sub r ⟨D, n⟩)) →
    ∀ j < 8, ∀ l < 4, (tm m').readW (W + BitVec.ofNat 64 1536 + BitVec.ofNat 64 (64 * j + 16 * l)) 128 =
      (tm m).readW (W + BitVec.ofNat 64 1536 + BitVec.ofNat 64 (64 * j + 16 * l)) 128
  out : ∀ m, Frame [⟨W + BitVec.ofNat 64 1536, 512⟩] m (tm m)

/-- GHASH reading the table at `W + 1536`. -/
theorem TabView.id {W D : Addr} {n : Nat} : TabView (fun m => m) W D n :=
  ⟨fun f hd j hj l hl => f.readW (r := ⟨W + BitVec.ofNat 64 1536 + BitVec.ofNat 64 (64 * j + 16 * l), 16⟩)
      (Region.contains_self _ _) (fun r hr => (hd r hr).1.sub_left (Offset.sub_base _ (by omega))) (by decide),
    fun _ => Frame.refl _ _⟩

theorem TabOk.view {tm : Mem → Mem} {W D : Addr} {n : Nat} (tv : TabView tm W D n) {m m' : Mem} {H : Block}
    {g : Nat} (h : TabOk (tm m) (W + BitVec.ofNat 64 1536) H g) (hg : g ≤ 8) {rs : List Region}
    (f : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 1536, 512⟩ : Region).Disjoint r ∧
      (Region.Sub r ⟨W, 1536⟩ ∨ Region.Sub r ⟨D, n⟩)) :
    TabOk (tm m') (W + BitVec.ofNat 64 1536) H g :=
  fun j hj l hl => by rw [tv.keep f hd j (by omega) l hl]; exact h j hj l hl

/-- What a GHASH code leaves, from `s` to `t`, with the table as `tm` sees
it: what `ghash_ok` says of `ghash`. -/
def GhPost (tm : Mem → Mem) (W : Addr) (g : Nat) (s t : State) : Prop :=
  t.zlane .xmm2 0 =
    (reduceB (gacc (tm s.mem) (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 1536) g 0 g) ^^^
      reduceB (gacc (tm s.mem) (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 1536) g 2 g)) ^^^
    (reduceB (gacc (tm s.mem) (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 1536) g 1 g) ^^^
      reduceB (gacc (tm s.mem) (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 1536) g 3 g)) ∧
  (∀ l, 1 ≤ l → l < 4 → t.zlane .xmm2 l = 0) ∧
  (∀ r, r ≠ .rdx → r ≠ .r9 → r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
  ZKeep [.xmm2, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12] s t

/-- `gh` leaves `GhPost` for `g` groups, in the states after the entry `s₀`
with its permissions. -/
def GhFrom (gh : Prog isa) (tm : Mem → Mem) (s₀ : State) (Ctx W SP : Addr) : Prop :=
  ∀ {g : Nat} (s : State), Env Ctx (W + BitVec.ofNat 64 16) W SP s →
    s.mem.readW (W + BitVec.ofNat 64 288) 64 = BitVec.ofNat 64 (4 * g) → 1 ≤ g → g ≤ 8 →
    (∀ l < 4, s.zlane .xmm0 l = revMask) → (∀ l < 4, s.zlane .xmm1 l = poly) →
    s.rd = s₀.rd → s.wr = s₀.wr → WP isa gh s (GhPost tm W g s)

theorem ghFrom_ghash {s₀ : State} {Ctx W SP : Addr} : GhFrom ghash (fun m => m) s₀ Ctx W SP :=
  fun s he hmp hg1 hg h0 h1 _ _ => ghash_ok s he.r15 hmp hg1 hg he.perm.w h0 h1

/-- After the powers, `G` and the keystream. -/
structure Front (tm : Mem → Mem) (s₀ : State) (Ctx W SP A D : Addr) (R al n : Nat) (J : Block) (tl : BitVec 64)
    (a : List Byte) (s : State) :
    Prop where
  sm : SM s₀ Ctx W SP A D R al n J tl s
  tab : TabOk (tm s.mem) (W + BitVec.ofNat 64 1536) (ctxH s₀.mem Ctx) (grp al n)
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

/-- What a table of powers' code `pw` leaves, from `s` to `t`: the table at
`W + 1536`, as `tm` sees it, for the hash subkey of `s`, nothing else
written, the constants in every lane of `zmm0` and `zmm1`, and the registers
but `rax` and `r11`. -/
def PowPost (tm : Mem → Mem) (Ctx W : Addr) (g : Nat) (s t : State) : Prop :=
  TabOk (tm t.mem) (W + BitVec.ofNat 64 1536) (ctxH s.mem Ctx) g ∧
    Frame [⟨W + BitVec.ofNat 64 1536, 512⟩] s.mem t.mem ∧
    (∀ l < 4, t.zlane .xmm0 l = revMask) ∧ (∀ l < 4, t.zlane .xmm1 l = poly) ∧
    (∀ r, r ≠ .rax → r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr

/-- `pw` leaves `PowPost` for `g` groups from the states the short path runs
it in after the entry `s₀`, which wrote only `W`, the data and the stack
below `SP`; and `gh` computes GHASH from the table as `tm` sees it. -/
structure PowFrom (pw gh : Prog isa) (tm : Mem → Mem) (s₀ : State) (Ctx W SP D : Addr) (n : Nat) : Prop where
  view : TabView tm W D n
  gh : GhFrom gh tm s₀ Ctx W SP
  run : ∀ {g : Nat} (s : State), Env Ctx (W + BitVec.ofNat 64 16) W SP s →
    s.mem.readW (W + BitVec.ofNat 64 288) 64 = BitVec.ofNat 64 (4 * g) → 1 ≤ g → g ≤ 8 →
    Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP 24] s₀.mem s.mem → s.rd = s₀.rd → s.wr = s₀.wr →
    WP isa pw s (PowPost tm Ctx W g s)

/-- `powers` and `ghash`, from the hash subkey at `ctx + 240`. -/
theorem powFrom_powers (hF : ShortFacts) {s₀ : State} {Ctx W SP D : Addr} {n : Nat} :
    PowFrom powers ghash (fun m => m) s₀ Ctx W SP D n :=
  ⟨TabView.id, ghFrom_ghash, fun s he h1 h2 h3 _ _ _ => hF.powers s he h1 h2 h3⟩

/-- The powers (from `pw`), `G` and the keystream, then `rest`. -/
theorem front_ok {pw gh : Prog isa} {tm : Mem → Mem} {k : Nat} {s₀ s : State} {Ctx W SP Np A D : Addr}
    {nl al n R : Nat} {J : Block} {tl : BitVec 64}
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (hpw : PowFrom pw gh tm s₀ Ctx W SP D n) (hR : R = (s₀.gpr .rsi).toNat)
    (hal5 : al < 512) (hn5 : n < 512) (h32 : nb16 al + nb16 n < 32)
    (S : SM s₀ Ctx W SP A D R al n J tl s) (haad : bytesAt s.mem A al = bytesAt s₀.mem A al)
    (hdat : bytesAt s.mem D n = bytesAt s₀.mem D n)
    {rest : Prog isa} {Q : State → Prop}
    (hrest : ∀ t, Front tm s₀ Ctx W SP A D R al n J tl (bytesAt s₀.mem A al) t → WP isa rest t Q) :
    WP isa (.seq pw (.seq (.block zeroG) (.seq copyA (.seq keystream rest)))) s Q := by
  have L := C.lay
  have dD := C.dE
  have h32' := h32
  simp only [nb16] at h32'
  have hg1 : 1 ≤ grp al n := by simp only [grp, nb16]; omega
  have hg8 : grp al n ≤ 8 := by simp only [grp, nb16]; omega
  have hlead : 4 * grp al n - (nb16 al + nb16 n + 1) < 4 := by simp only [grp, nb16]; omega
  have hR' : R = 10 ∨ R = 12 ∨ R = 14 := hR ▸ C.rounds
  -- The powers.
  refine WP.seq (WP.mono (hpw.run s S.env S.r288 hg1 hg8 S.frame S.rd S.wr)
    fun s₃ ⟨tab₃, fT, z0₃, z1₃, g₃, rd₃, wr₃⟩ => ?_)
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
  have tab₄ := TabOk.view hpw.view tab₃ hg8 fG fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨Offset.disjoint W (.inr (by decide)) (by decide) (by decide), .inl (Offset.sub_base W (by decide))⟩
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
  have tab₅ := TabOk.view hpw.view tab₄ hg8 fA fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨Offset.disjoint W (.inr (by omega)) (by omega) (by omega), .inl (Offset.sub_base W (by omega))⟩
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
  refine hrest s₆ ⟨S₆, TabOk.view hpw.view tab₅ hg8 fK fun r hr => ?_, m0K, fun l hl => ?_, fun b hb => ?_,
    ⟨s₄.mem, hZ, by rw [← m₅]; exact fK⟩, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨Offset.disjoint W (.inr (by decide)) (by decide) (by decide), .inl (Offset.sub_base W (by decide))⟩
  · rw [zK _ (by decide) l hl, zz _ (by decide) (by decide) l hl, z1₃ l hl]
  · rw [kb b hb, S₅.j0, ciph_frame' C S₅.frame (by omega), hR]
  · rw [bytesAt_frame fK (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dD.sub_right (Lay.wSub (by decide))) (by omega),
      hdat₅]

end VG.Proof.AesGcm.X86_64.Short
