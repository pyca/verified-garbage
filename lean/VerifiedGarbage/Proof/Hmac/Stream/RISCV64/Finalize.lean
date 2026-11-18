module

public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Init
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc

/-! ### `Hmac.Stream.RISCV64.InitMain`, which the modules that import this one used -/

section

/-!
# HMAC over any streaming hash function on RISC-V: `init`

`init` allocates its frame (`WP.alloc`), saves our caller's `ra` and
`s7`–`s11` in it and sets up ours (`prologue_ok`), and compares the key's
length with a block (`entry_ok`). A longer key is hashed with the streaming
functions into the frame (`longKey_ok`), and its digest made the key; then
`core_ok` (`Init.lean`) runs.
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.RISCV64.Init

open VG.RISCV64
open VG.RISCV64.Steps (Upd wp_li wp_mv wp_addi wp_addSp)
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey)

variable {H : Hash} {s₀ : State}

theorem K_length (s₀ : State) : (K s₀).length = kl s₀ := by simp [bytesAt]

/-- The key `K₀` is made from, for a key of at most a block: the key. -/
theorem blockKey_short (hH : HashOK H) (h : kl s₀ ≤ H.B) :
    PadKey.K0 (K s₀) H.B = blockKey hH.SH.H (K s₀) := by
  simp only [blockKey, PadKey.K0, hH.hB, K_length, show ¬ (H.B < kl s₀) by omega_using [h], ite_false]

/-- For a longer key: its digest. -/
theorem blockKey_long (hH : HashOK H) (h : H.B < kl s₀) :
    PadKey.K0 (hH.SH.H.hash (K s₀)) H.B = blockKey hH.SH.H (K s₀) := by
  simp only [blockKey, PadKey.K0, hH.hB, K_length, h, ite_true]

theorem ofNat_kl (s₀ : State) : BitVec.ofNat 64 (kl s₀) = s₀.gpr .a3 := by
  rw [kl, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The key, for a key of at most a block. -/
theorem keyOK_short (hp : Pre H s₀) (h : kl s₀ ≤ H.B) : KeyOK H s₀ (kp s₀) (kl s₀) :=
  ⟨h, fun j hj => ⟨kR s₀, by rw [hp.rd]; exact List.mem_append_left _ (List.mem_singleton_self _),
    Offset.contains_base _ (show j + 1 ≤ kl s₀ by omega_using [hj])
      (by have : kl s₀ < 2 ^ 64 := (s₀.gpr .a3).isLt; omega_using [hj, this])⟩,
    hp.k_i, hp.k_o, hp.s_k.symm⟩

/-- The long key's digest, in the frame. -/
theorem keyOK_long (hp : Pre H s₀) (hl : Lay H) : KeyOK H s₀ (fr s₀ + BitVec.ofNat 64 H.S) H.D := by
  have hD := hl.D
  have hB := hl.B
  have hiso := hl.iso
  have hib := hl.ibytes
  obtain hw : frR H s₀ ∈ s₀.rd ++ s₀.wr := by
    rw [hp.wr]; exact List.mem_append_right _ (List.mem_cons_self ..)
  refine ⟨by omega_using [hD, hB], fun j hj => ⟨frR H s₀, hw, ?_⟩, hp.f_i.sub_left (ldg_sub hl),
    hp.f_o.sub_left (ldg_sub hl), hp.f_s.sub_left (ldg_sub hl)⟩
  rw [Offset.add_add]
  exact Offset.contains_base _ (show H.S + j + 1 ≤ H.ibytes by omega_using [hiso, hib, hj]) (by omega_using [hiso, hib, hj])

/-- The saved registers survive writes in the long key's state and digest,
and below the frame. -/
theorem sv_keep (hp : Pre H s₀) (hl : Lay H) {m m' : Mem}
    (h : Spill.Saved (fr s₀) s₀.gpr (Hash.savedAt H.iso) m) {rs : List Region} (hf : Frame rs m m')
    (hrs : ∀ r ∈ rs, r = ⟨fr s₀, H.S⟩ ∨ r = ⟨fr s₀ + BitVec.ofNat 64 H.S, H.D⟩ ∨ r = stk H s₀) :
    Spill.Saved (fr s₀) s₀.gpr (Hash.savedAt H.iso) m' :=
  h.frame_in savedAt_in hf fun r hr => by
    rcases hrs r hr with rfl | rfl | rfl
    exacts [(lst_sv hl).symm, (ldg_sv hl).symm, hp.f_s.sub_left (sv_sub hl)]

variable (hH : HashOK H)
include hH

/-- A key longer than a block: hashed into the streaming state at the start
of the frame, and its digest, after it, made the key. -/
theorem longKey_ok (hp : Pre H s₀) {s : State} (hr : Regs s₀ s) (hv : Vars s₀ s (kp s₀) (kl s₀))
    (hk : bytesAt s.mem (kp s₀) (kl s₀) = K s₀)
    (hsv : Spill.Saved (fr s₀) s₀.gpr (Hash.savedAt H.iso) s.mem) :
    WP isa H.longKey s fun s' =>
      St (H := H) s₀ s' (fr s₀ + BitVec.ofNat 64 H.S) H.D (hH.SH.H.hash (K s₀)) := by
  have hl := hH.lay
  have hD := hl.D
  have hiso := hl.iso
  have hib := hl.ibytes
  obtain hS : H.S < 2048 := by omega_using [hiso, hib]
  obtain hwf : frR H s₀ ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_self ..
  obtain hrk : kR s₀ ∈ s₀.rd := by rw [hp.rd]; exact List.mem_singleton_self _
  obtain kS : (kR s₀).Disjoint ⟨fr s₀, H.S⟩ := hp.f_k.symm.sub_right (lst_sub hl)
  obtain sS : (stk H s₀).Disjoint ⟨fr s₀, H.S⟩ := hp.f_s.symm.sub_right (lst_sub hl)
  obtain sD : (stk H s₀).Disjoint ⟨fr s₀ + BitVec.ofNat 64 H.S, H.D⟩ := hp.f_s.symm.sub_right (ldg_sub hl)
  obtain kl_lt : kl s₀ < 2 ^ 64 := (s₀.gpr .a3).isLt
  unfold Hash.longKey
  -- The streaming state's hash value.
  refine WP.seq (wp_mv fun s₁ u₁ => WP.block_nil ?_)
  obtain r₁ : Regs s₀ s₁ := ⟨by rw [u₁.rd, hr.rd], by rw [u₁.wr, hr.wr], by rw [u₁.sp, hr.sp]⟩
  obtain v₁ : Vars s₀ s₁ (kp s₀) (kl s₀) := hv.of_keep fun r a _ _ _ _ _ _ _ _ _ => u₁.other r a
  refine WP.seq (hH.callInit_ok (st := fr s₀) (by rw [u₁.gpr, hv.s8])
    (by rw [r₁.rd, r₁.wr]; exact cover_pre (List.mem_append_right _ hwf) (show H.S ≤ H.ibytes by omega_using [hiso, hib]))
    (by rw [r₁.wr]; exact cover_pre hwf (show H.S ≤ H.ibytes by omega_using [hiso, hib])) fun s₂ rd₂ wr₂ sp₂ f₂ cs₂ hrS₂ => ?_)
  rw [r₁.sp, u₁.mem] at f₂
  obtain r₂ : Regs s₀ s₂ := ⟨rd₂.trans r₁.rd, wr₂.trans r₁.wr, sp₂.trans r₁.sp⟩
  obtain v₂ := v₁.of_pres cs₂
  obtain hrs₂ : ∀ r ∈ [(⟨fr s₀, H.S⟩ : Region)] ++ [stk H s₀], r = ⟨fr s₀, H.S⟩ ∨
      r = ⟨fr s₀ + BitVec.ofNat 64 H.S, H.D⟩ ∨ r = stk H s₀ := by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [.inl rfl, .inr (.inr rfl)]
  obtain sv₂ := sv_keep hp hl hsv f₂ hrs₂
  obtain k₂ : bytesAt s₂.mem (kp s₀) (kl s₀) = K s₀ := by
    rw [← hk]
    refine Proof.Sha256.Stream.bytesAt_congr fun i hi => f₂.bytes (R := kR s₀) (fun r hr => ?_)
      (by show kl s₀ ≤ 2 ^ 64; omega_using [kl_lt]) hi
    rcases hrs₂ r hr with rfl | rfl | rfl
    exacts [kS, hp.f_k.symm.sub_right (ldg_sub hl), hp.s_k.symm]
  -- Absorb the key.
  refine WP.seq (wp_mv fun s₃ u₃ => wp_li (by decide) fun s₄ u₄ => wp_mv fun s₅ u₅ =>
    wp_mv fun s₆ u₆ => WP.block_nil ?_)
  obtain r₆ : Regs s₀ s₆ := ⟨by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, r₂.rd], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, r₂.wr],
    by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, r₂.sp]⟩
  obtain m₆ : s₆.mem = s₂.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  obtain v₆ : Vars s₀ s₆ (kp s₀) (kl s₀) := v₂.of_keep fun r a b c d _ _ _ _ _ _ => by
    rw [u₆.other r d, u₅.other r c, u₄.other r b, u₃.other r a]
  obtain a1₆ : s₆.gpr .a1 = BitVec.ofNat 64 ([] : List Byte).length := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; rfl
  refine WP.seq (hH.callUpd_ok (st := fr s₀) (dat := kp s₀) (len := kl s₀)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, v₂.s8])
    (by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), v₂.s10])
    (by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), v₂.s11,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt kl_lt])
    kS (by rw [r₆.sp]; exact hp.al) (by rw [r₆.sp]; exact hp.spF) (by rw [r₆.sp]; exact sS)
    (by rw [r₆.sp]; exact hp.s_k)
    (by
      rw [r₆.rd, r₆.wr]
      exact VG.Covers.append_left (cover_self (List.mem_append_left _ hrk))
        (cover_pre (List.mem_append_right _ hwf) (show H.S ≤ H.ibytes by omega_using [hiso, hib])))
    (by rw [r₆.wr]; exact cover_pre hwf (show H.S ≤ H.ibytes by omega_using [hiso, hib])) fun s₇ rd₇ wr₇ sp₇ f₇ cs₇ hup => ?_)
  rw [r₆.sp, m₆] at f₇
  obtain r₇ : Regs s₀ s₇ := ⟨rd₇.trans r₆.rd, wr₇.trans r₆.wr, sp₇.trans r₆.sp⟩
  obtain v₇ := v₆.of_pres cs₇
  obtain sv₇ := sv_keep hp hl sv₂ f₇ hrs₂
  obtain hrS₇ : hH.SH.Repr s₇.mem (fr s₀) (K s₀) := by
    have := hup [] (by rw [m₆]; exact hrS₂) a1₆
    rwa [List.nil_append, m₆, k₂] at this
  -- Its digest, after the streaming state.
  refine WP.seq (wp_mv fun s₈ u₈ => wp_mv fun s₉ u₉ => wp_addi (by omega_using [hS]) fun s₁₀ u₁₀ => WP.block_nil ?_)
  obtain r₁₀ : Regs s₀ s₁₀ := ⟨by rw [u₁₀.rd, u₉.rd, u₈.rd, r₇.rd], by rw [u₁₀.wr, u₉.wr, u₈.wr, r₇.wr],
    by rw [u₁₀.sp, u₉.sp, u₈.sp, r₇.sp]⟩
  obtain m₁₀ : s₁₀.mem = s₇.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem]
  obtain v₁₀ : Vars s₀ s₁₀ (kp s₀) (kl s₀) := v₇.of_keep fun r a b c _ _ _ _ _ _ _ => by
    rw [u₁₀.other r c, u₉.other r b, u₈.other r a]
  obtain hcov : VG.Covers [⟨fr s₀, H.S⟩, ⟨fr s₀ + BitVec.ofNat 64 H.S, H.D⟩] s₀.wr :=
    VG.Covers.pair (cover_pre hwf (show H.S ≤ H.ibytes by omega_using [hiso, hib]))
      (cover_off hwf (show H.S + H.D ≤ H.ibytes by omega_using [hiso, hib]))
  refine WP.seq (hH.callFin_ok (st := fr s₀) (o := fr s₀ + BitVec.ofNat 64 H.S)
    (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, v₇.s8])
    (by rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), v₇.s8])
    (lst_ldg hl) (by rw [r₁₀.sp]; exact hp.al) (by rw [r₁₀.sp]; exact hp.spF) (by rw [r₁₀.sp]; exact sS)
    (by rw [r₁₀.sp]; exact sD) (by rw [r₁₀.rd, r₁₀.wr]; exact hcov.right) (by rw [r₁₀.wr]; exact hcov)
    fun s₁₁ rd₁₁ wr₁₁ sp₁₁ f₁₁ cs₁₁ hfin => ?_)
  rw [r₁₀.sp, m₁₀] at f₁₁
  obtain r₁₁ : Regs s₀ s₁₁ := ⟨rd₁₁.trans r₁₀.rd, wr₁₁.trans r₁₀.wr, sp₁₁.trans r₁₀.sp⟩
  obtain v₁₁ := v₁₀.of_pres cs₁₁
  obtain sv₁₁ := sv_keep hp hl sv₇ f₁₁ (by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [.inl rfl, .inr (.inl rfl), .inr (.inr rfl)])
  obtain hdg : bytesAt s₁₁.mem (fr s₀ + BitVec.ofNat 64 H.S) H.D = hH.SH.H.hash (K s₀) :=
    hfin (K s₀) (by rw [m₁₀]; exact hrS₇) (by rw [K_length]; exact kl_lt)
      (by rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), v₇.s11, K_length])
  -- The key is the digest.
  refine wp_addi (by omega_using [hS]) fun s₁₂ u₁₂ => wp_li (by omega_using [hD]) fun s₁₃ u₁₃ => WP.block_nil ?_
  obtain m₁₃ : s₁₃.mem = s₁₁.mem := by rw [u₁₃.mem, u₁₂.mem]
  refine ⟨⟨by rw [u₁₃.rd, u₁₂.rd, r₁₁.rd], by rw [u₁₃.wr, u₁₂.wr, r₁₁.wr], by rw [u₁₃.sp, u₁₂.sp, r₁₁.sp]⟩,
    ⟨by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), v₁₁.s7],
      by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), v₁₁.s8],
      by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), v₁₁.s9],
      by rw [u₁₃.other _ (by decide), u₁₂.gpr, v₁₁.s8],
      by rw [u₁₃.gpr],
      fun r hr => by
        rw [u₁₃.other r (by revert r; decide), u₁₂.other r (by revert r; decide)]
        exact v₁₁.nv r hr⟩,
    by rw [m₁₃]; exact hdg, by rw [m₁₃]; exact sv₁₁⟩

omit hH in
/-- `initMain`, split at the long key. -/
theorem initMain_eq (H : Hash) : H.initMain =
    .seq (.block (.addSp .t0 0 :: (Spill.saveCode .t0 (Hash.savedAt H.iso) ++
      ([mov .s7 .a0, mov .s8 .t0, mov .s9 .a1, mov .s10 .a2, mov .s11 .a3] ++ H.entryCmp))))
      (.seq (.ite (.zero .t1) (.block []) H.longKey) (core H)) := by
  simp only [Hash.initMain, saveAt_eq, core, List.cons_append, List.append_assoc]

/-- `init`, in its frame. -/
theorem initMain_ok (hp : Pre H s₀) : WP isa H.initMain s₀ (Post hH s₀) := by
  have hl := hH.lay
  have hiso := hl.iso
  have hib := hl.ibytes
  obtain hal8 : (fr s₀).toNat % 8 = 0 := by show s₀.sp.toNat % 8 = 0; have := hp.al; omega_using [this]
  rw [initMain_eq]
  refine WP.seq (wp_addSp (imm := 0) (by decide) fun s₁ u₁ => ?_)
  obtain t0₁ : s₁.gpr .t0 = fr s₀ := by rw [u₁.gpr, BitVec.add_zero]
  refine Spill.save_ok (by rw [t0₁]; exact hal8) (savedAt_off ⟨hiso.2, by omega_using [hib]⟩)
    (fun p hp' => ⟨frR H s₀, by rw [u₁.wr, hp.wr]; exact List.mem_cons_self,
      (by
        rw [t0₁]
        have := savedAt_in p hp'
        exact Offset.contains_base (k := H.ibytes) _ (by omega_using [hib, this]) (by omega_using [hib, this]))⟩) ?_
  refine wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ =>
    wp_mv fun s₇ u₇ => entry_ok hH.hb fun u gu mu rdu wru spu cu => WP.block_nil ?_
  -- The state after the prologue.
  obtain g₇ : ∀ r, r ≠ .s7 → r ≠ .s8 → r ≠ .s9 → r ≠ .s10 → r ≠ .s11 → r ≠ .t0 → s₇.gpr r = s₀.gpr r :=
    fun r a b c d e f => by
      rw [u₇.other r e, u₆.other r d, u₅.other r c, u₄.other r b, u₃.other r a]
      exact u₁.other r f
  obtain gU : ∀ r, r ≠ .s7 → r ≠ .s8 → r ≠ .s9 → r ≠ .s10 → r ≠ .s11 → r ≠ .t0 → r ≠ .t1 → r ≠ .t2 →
      u.gpr r = s₀.gpr r := fun r a b c d e f g h => by rw [gu r g h]; exact g₇ r a b c d e f
  obtain hr : Regs s₀ u := ⟨by rw [rdu, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd]; exact u₁.rd,
    by rw [wru, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr]; exact u₁.wr,
    by rw [spu, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp]; exact u₁.sp⟩
  obtain hv : Vars s₀ u (kp s₀) (kl s₀) :=
    ⟨by rw [gu _ (by decide) (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]; exact u₁.other _ (by decide),
      by rw [gu _ (by decide) (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide)]; exact t0₁,
      by rw [gu _ (by decide) (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
        u₄.other _ (by decide), u₃.other _ (by decide)]; exact u₁.other _ (by decide),
      by rw [gu _ (by decide) (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide)]; exact u₁.other _ (by decide),
      by rw [gu _ (by decide) (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide), u₁.other _ (by decide), ofNat_kl],
      fun r hr => gU r (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide)⟩
  obtain hmu : u.mem = Spill.saveMem s₀.mem (fr s₀) s₁.gpr (Hash.savedAt H.iso) := by
    rw [mu, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, t0₁, u₁.mem]
  obtain hfu : Frame [svR H s₀] s₀.mem u.mem := by
    rw [hmu]; exact Spill.saveMem_frame savedAt_in (by have := hp.top; omega_using [hib]) _ _ _
  obtain hk : bytesAt u.mem (kp s₀) (kl s₀) = K s₀ :=
    Proof.Sha256.Stream.bytesAt_congr fun i hi => hfu.bytes (R := kR s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.f_k.symm.sub_right (sv_sub hl))
      (by show kl s₀ ≤ 2 ^ 64; have : kl s₀ < 2 ^ 64 := (s₀.gpr .a3).isLt; omega_using [this]) hi
  obtain hsv : Spill.Saved (fr s₀) s₀.gpr (Hash.savedAt H.iso) u.mem := by
    rw [hmu]
    intro p hp'
    rw [Spill.saveMem_saved (savedAt_fits ⟨hiso.2, by omega_using [hib]⟩) _ _ _ p hp']
    refine u₁.other _ ?_
    simp only [Hash.savedAt, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  obtain hz : isa.eval (.zero .t1) u = some (decide (kl s₀ ≤ H.B)) := by
    rw [Steps.eval_zero, cu, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₁.other _ (by decide)]
  refine WP.seq (WP.ite _ hz (fun hb => ?_) (fun hb => ?_))
  · have hkl : kl s₀ ≤ H.B := of_decide_eq_true hb
    exact WP.block_nil (core_ok hH hp (keyOK_short hp hkl) (blockKey_short hH hkl) ⟨hr, hv, hk, hsv⟩)
  · have hkl : H.B < kl s₀ := by have := of_decide_eq_false hb; omega_using [this]
    exact WP.mono (longKey_ok hH hp hr hv hk hsv) fun s' h =>
      core_ok hH hp (keyOK_long hp hl) (blockKey_long hH hkl) h

/-- The state the frame's body starts in, from `init`'s precondition. -/
theorem pre_alloc {s : State} (hp : (initG hH.SH (H.ibytes + H.F)).pre s) : Pre H (allocd H.ibytes s) := by
  have hl := hH.lay
  have hib := hl.ibytes
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hp
  rw [hH.hS] at h2 h3 h4 h5 h8 h9
  obtain hsp := toNat_sub (sp := s.sp) (n := H.ibytes) (by omega_using [h7]) (by omega_using [hib])
  obtain subF : Region.Sub ⟨s.sp - BitVec.ofNat 64 H.ibytes, H.ibytes⟩ (below s.sp (H.ibytes + H.F)) :=
    Offset.sub_below s.sp (by omega_using []) (by omega_using [])
  obtain subS : Region.Sub (below (s.sp - BitVec.ofNat 64 H.ibytes) H.F) (below s.sp (H.ibytes + H.F)) := by
    have := below_body' s.sp H.ibytes H.F
    rwa [Nat.add_comm H.F] at this
  have hsp' : (allocd H.ibytes s).sp = s.sp - BitVec.ofNat 64 H.ibytes := rfl
  refine ⟨h1, by show _ :: s.wr = _; rw [h2]; rfl, h3, h4, h5, h8.sub_left subF, h9.sub_left subF, h10.sub_left subF,
    ?_, ?_, ?_, h8.sub_left subS, h9.sub_left subS, h10.sub_left subS⟩
  · rw [hsp', hsp]; omega_using [hib, h6]
  · rw [hsp', hsp]; omega_using [h7]
  · rw [hsp', hsp]; have := s.sp.isLt; omega_using [hib]

/-- HMAC's `init`, for a key of any length. -/
theorem correct {s : State} (hp : (initG hH.SH (H.ibytes + H.F)).pre s) :
    WP isa H.init s fun s' => abiPreserved s s' ∧ (initG hH.SH (H.ibytes + H.F)).post s s' := by
  have hl := hH.lay
  have hib := hl.ibytes
  obtain hsp : H.ibytes ≤ s.sp.toNat := by have := hp.2.2.2.2.2.2.1; omega_using [this]
  refine WP.alloc ⟨by omega_using [hib], hib.2.1, hib.2.2⟩ hsp
    (WP.mono (initMain_ok hH (pre_alloc hH hp)) fun s' ⟨hk, hra, hsp', hwr, hI, hO⟩ m u f => ?_)
  rw [freed_eq hwr hsp']
  -- The `free` loses the frame's bytes, which lie apart from the two states.
  have hq := pre_alloc hH hp
  exact ⟨⟨hk, rfl, hra⟩,
    hH.congr _ _ _ _ (fun i hi => lost_byte f (R := inR H (allocd H.ibytes s)) hq.f_i.symm hi) hI,
    hH.congr _ _ _ _ (fun i hi => lost_byte f (R := outR H (allocd H.ibytes s)) hq.f_o.symm hi) hO⟩

end VG.Proof.Hmac.Stream.RISCV64.Init

end

end

/-!
# HMAC over any streaming hash function on RISC-V: `finalize`

`finalize` allocates its frame (`fr`, `fbytes` bytes: the inner digest, then
our caller's `ra` and `s7`–`s11` at `fso`), finalizes the inner state into
it with the streaming `finalize`, copies the outer state's hash value over
the inner one's a byte at a time (`copy8_ok`; the inner state then represents
the outer block, `HashOK.reloc`), absorbs the inner digest with `update`,
finalizes again into `out`, and restores the registers (`finalizeMain_ok`).
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.RISCV64.Finalize

open VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_li wp_mv wp_addi wp_addSp wp_lbu wp_sb)
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.Proof.Hmac.Stream.RISCV64.Init (Regs cover_self cover_pre hv_sub nv_pres)
open VG.WriteBytes (writeBytes writeBytes_nil)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad hmacBlockKey)

/-! ## Copying bytes -/

theorem bytesAt_succ (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p (n + 1) = bytesAt m p n ++ [m (p + BitVec.ofNat 64 n)] := by
  simp [bytesAt, List.range_succ]

/-- `n` bytes copied from `src` to `dst`, a byte at a time through `t1`. -/
theorem copy8_ok {src dst : Reg} (hs : src ≠ .t1) (hd : dst ≠ .t1) (n : Nat) (hn : n ≤ 2048) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 k) 1) →
    (∀ k < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 k) 1) →
    Mem.Sep (s.gpr src) n (s.gpr dst) n →
    (∀ s', (∀ r, r ≠ .t1 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (s.gpr dst) (bytesAt s.mem (s.gpr src) n) → WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (fun k => [.load .b .t1 src k, .store .b .t1 dst k]) ++ rest))
      s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl rfl (by
      rw [VG.Proof.Hmac.Common.bytesAt_zero, writeBytes_nil])
  | succ n ih =>
    intro rest s Q hin hout hsep k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega_using [hn]) _ s Q (fun j hj => hin j (by omega_using [hj])) (fun j hj => hout j (by omega_using [hj]))
      (fun x hx hy => hsep x (by omega_using [hx]) (by omega_using [hy])) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_lbu (a := s.gpr src + BitVec.ofNat 64 n) (by omega_using [hn]) (by rw [g₁ _ hs])
      (by rw [rd₁, wr₁]; exact hin n (by omega_using [])) fun s₂ u₂ => ?_
    refine wp_sb (a := s.gpr dst + BitVec.ofNat 64 n) (by omega_using [hn]) (by rw [u₂.other _ hd, g₁ _ hd])
      (by rw [u₂.wr, wr₁]; exact hout n (by omega_using [])) fun s₃ u₃ =>
      k s₃ (fun r hr => by rw [u₃.gpr, u₂.other r hr, g₁ r hr])
        (by rw [u₃.rd, u₂.rd, rd₁]) (by rw [u₃.wr, u₂.wr, wr₁]) (by rw [u₃.sp, u₂.sp, sp₁]) ?_
    obtain hrd : s₁.mem (s.gpr src + BitVec.ofNat 64 n) = s.mem (s.gpr src + BitVec.ofNat 64 n) := by
      rw [m₁]
      refine VG.Proof.Hmac.Common.writeBytes_other _ _ _ ?_
      rw [VG.Proof.Hmac.Common.bytesAt_length]
      intro hlt
      refine hsep (s.gpr src + BitVec.ofNat 64 n) ?_ (by omega_using [hlt])
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      omega_using []
    rw [u₃.mem, u₂.gpr, u₂.mem, m₁, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq,
      ← m₁, hrd, m₁, bytesAt_succ,
      VG.WriteBytes.writeBytes_snoc _ _ _ _ (by rw [VG.Proof.Hmac.Common.bytesAt_length]; omega_using [hn]),
      VG.Proof.Hmac.Common.bytesAt_length]

theorem contains_start {p : Addr} {n len : Nat} (h : n ≤ len) : (⟨p, len⟩ : Region).Contains p n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [h]

/-! ## The precondition -/

section
variable (H : Hash) (s₀ : State)

/-- The frame. -/
abbrev fr : Addr := s₀.sp
abbrev inn : Addr := s₀.gpr .a0
abbrev out : Addr := s₀.gpr .a1
abbrev mac : Addr := s₀.gpr .a3
abbrev inR : Region := ⟨inn s₀, H.S⟩
abbrev outR : Region := ⟨out s₀, H.S⟩
abbrev macR : Region := ⟨mac s₀, H.D⟩
abbrev frR : Region := ⟨fr s₀, H.fbytes⟩
/-- The inner digest, at the start of the frame. -/
abbrev digR : Region := ⟨fr s₀, H.D⟩
abbrev stk : Region := below (fr s₀) H.F
abbrev svR : Region := ⟨fr s₀ + BitVec.ofNat 64 H.fso, 48⟩

end

/-- The state the frame's body starts in. -/
structure Pre (H : Hash) (s₀ : State) : Prop where
  rd : s₀.rd = [outR H s₀]
  wr : s₀.wr = [frR H s₀, inR H s₀, macR H s₀]
  i_o : (inR H s₀).Disjoint (outR H s₀)
  i_m : (inR H s₀).Disjoint (macR H s₀)
  o_m : (outR H s₀).Disjoint (macR H s₀)
  f_i : (frR H s₀).Disjoint (inR H s₀)
  f_o : (frR H s₀).Disjoint (outR H s₀)
  f_m : (frR H s₀).Disjoint (macR H s₀)
  al : s₀.sp.toNat % 16 = 0
  spF : H.F ≤ s₀.sp.toNat
  top : s₀.sp.toNat + H.fbytes ≤ 2 ^ 64
  s_i : (stk H s₀).Disjoint (inR H s₀)
  s_o : (stk H s₀).Disjoint (outR H s₀)
  s_m : (stk H s₀).Disjoint (macR H s₀)

/-- Our variables in `s7`–`s10`, and the callee-saved registers we never
write. -/
structure Vars (s₀ s : State) : Prop where
  s7 : s.gpr .s7 = inn s₀
  s8 : s.gpr .s8 = fr s₀
  s9 : s.gpr .s9 = out s₀
  s10 : s.gpr .s10 = mac s₀
  nv : ∀ r ∈ nvRegs, s.gpr r = s₀.gpr r

variable {H : Hash} {s₀ : State}

theorem Vars.of_pres {s s' : State} (h : Vars s₀ s) (hc : ∀ r ∈ preserved, s'.gpr r = s.gpr r) :
    Vars s₀ s' :=
  ⟨(hc _ (by decide)).trans h.s7, (hc _ (by decide)).trans h.s8, (hc _ (by decide)).trans h.s9,
    (hc _ (by decide)).trans h.s10, fun r hr => (hc r (nv_pres r hr)).trans (h.nv r hr)⟩

/-- `Vars` after code writing only `a0`–`a3` and `t1`. -/
theorem Vars.of_keep {s s' : State} (h : Vars s₀ s)
    (hc : ∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → r ≠ .t1 → s'.gpr r = s.gpr r) : Vars s₀ s' := by
  obtain k : ∀ r ∈ [Reg.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10], s'.gpr r = s.gpr r := by
    intro r hr
    exact hc r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide)
  exact ⟨(k _ (by simp)).trans h.s7, (k _ (by simp)).trans h.s8, (k _ (by simp)).trans h.s9,
    (k _ (by simp)).trans h.s10, fun r hr => (k r (by revert r; decide)).trans (h.nv r hr)⟩

theorem Pre.f_s (hp : Pre H s₀) : (frR H s₀).Disjoint (stk H s₀) :=
  Offset.base_disjoint_below _ (by have := hp.top; have := hp.spF; have := s₀.sp.isLt; omega_arith)

theorem dig_sub (hl : Lay H) : Region.Sub (digR H s₀) (frR H s₀) :=
  Region.sub_prefix (by have := hl.fso; have := hl.fbytes; omega_arith)

theorem sv_sub (hl : Lay H) : Region.Sub (svR H s₀) (frR H s₀) :=
  Offset.sub_base _ hl.fbytes.1

theorem dig_sv (hl : Lay H) : Region.Disjoint (digR H s₀) (svR H s₀) :=
  Offset.base_disjoint _ hl.fso.1 (by have := hl.fbytes; omega_arith)

/-- The hypotheses of `finalize`'s postcondition. -/
def Hyp (hH : HashOK H) (s₀ : State) (k0 text : List Byte) : Prop :=
  k0.length = hH.SH.H.blockSize ∧ k0.length + text.length < 2 ^ 64 ∧
    hH.SH.Repr s₀.mem (inn s₀) (xorPad k0 ipad ++ text) ∧
    s₀.gpr .a2 = BitVec.ofNat 64 (hH.SH.H.blockSize + text.length) ∧
    hH.SH.Repr s₀.mem (out s₀) (xorPad k0 opad)

/-- `finalize`'s postcondition, in its frame. -/
def Post (hH : HashOK H) (s₀ s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧ s'.sp = s₀.sp ∧ s'.wr = s₀.wr ∧
    ∀ k0 text, Hyp hH s₀ k0 text → bytesAt s'.mem (mac s₀) H.D = hmacBlockKey hH.SH.H k0 text

/-- `finalizeMain`, with `saveAt` as `Spill`'s. -/
theorem finalizeMain_eq (H : Hash) : H.finalizeMain =
    .seq (.block (.addSp .t0 0 :: (Spill.saveCode .t0 (Hash.savedAt H.fso) ++
      [mov .s7 .a0, mov .s8 .t0, mov .s9 .a1, mov .s10 .a3, mov .a1 .a2, mov .a2 .t0])))
    (.seq H.callFin
    (.seq (.block ((List.range H.N).flatMap (fun k => [.load .b .t1 .s9 k, .store .b .t1 .s7 k]) ++
        [mov .a0 .s7, .li .a1 H.B, mov .a2 .s8, .li .a3 H.D]))
    (.seq H.callUpd
    (.seq (.block [mov .a0 .s7, .li .a1 (H.B + H.D), mov .a2 .s10])
    (.seq H.callFin
      (.block (Spill.restoreCode .s8 (restList H.fso)))))))) := by
  simp only [Hash.finalizeMain, saveAt_eq, restoreAt_eq, Hash.copyHV, List.cons_append]

variable (hH : HashOK H)
include hH

/-- `finalize`, in its frame. -/
theorem finalizeMain_ok (hp : Pre H s₀) : WP isa H.finalizeMain s₀ (Post hH s₀) := by
  have hl := hH.lay
  have hN := hl.N
  have hB := hl.B
  have hD := hl.D
  have hfso := hl.fso
  have hfb := hl.fbytes
  have hS : H.S = H.N + H.B := rfl
  obtain hal8 : (fr s₀).toNat % 8 = 0 := by show s₀.sp.toNat % 8 = 0; have := hp.al; omega_using [this]
  obtain hwf : frR H s₀ ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_self
  obtain hwi : inR H s₀ ∈ s₀.wr := by simp [hp.wr]
  obtain hwm : macR H s₀ ∈ s₀.wr := by simp [hp.wr]
  obtain hro : outR H s₀ ∈ s₀.rd := by simp [hp.rd]
  obtain i_d : (inR H s₀).Disjoint (digR H s₀) := hp.f_i.symm.sub_right (dig_sub hl)
  obtain s_d : (stk H s₀).Disjoint (digR H s₀) := hp.f_s.symm.sub_right (dig_sub hl)
  obtain sv_i : (svR H s₀).Disjoint (inR H s₀) := hp.f_i.sub_left (sv_sub hl)
  obtain sv_m : (svR H s₀).Disjoint (macR H s₀) := hp.f_m.sub_left (sv_sub hl)
  obtain sv_s : (svR H s₀).Disjoint (stk H s₀) := hp.f_s.sub_left (sv_sub hl)
  obtain hcovD : VG.Covers [digR H s₀] s₀.wr := cover_pre hwf (show H.D ≤ H.fbytes by omega_using [hfso, hfb])
  -- Writes outside the outer state, which keep it.
  obtain out_keep : ∀ {rs : List Region} {m m' : Mem}, Frame rs m m' → (∀ r ∈ rs, (outR H s₀).Disjoint r) →
      ∀ i < H.S, m' (out s₀ + BitVec.ofNat 64 i) = m (out s₀ + BitVec.ofNat 64 i) :=
    fun hf hd i hi => hf.bytes (R := outR H s₀) hd (by show H.S ≤ 2 ^ 64; omega_using [hN, hB, hS]) hi
  rw [finalizeMain_eq]
  -- Save our caller's registers, and set up ours and `finalize`'s arguments.
  refine WP.seq (wp_addSp (imm := 0) (by decide) fun s₁ u₁ => ?_)
  obtain t0₁ : s₁.gpr .t0 = fr s₀ := by rw [u₁.gpr, BitVec.add_zero]
  refine Spill.save_ok (by rw [t0₁]; exact hal8) (savedAt_off ⟨hfso.2, by omega_using [hfb]⟩)
    (fun p hp' => ⟨frR H s₀, by rw [u₁.wr]; exact hwf,
      (by
        rw [t0₁]
        have := savedAt_in p hp'
        exact Offset.contains_base (k := H.fbytes) _ (by omega_using [hfb, this]) (by omega_using [hfb, this]))⟩) ?_
  refine wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ =>
    wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ => WP.block_nil ?_
  obtain r₈ : Regs s₀ s₈ := ⟨by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd]; exact u₁.rd,
    by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr]; exact u₁.wr,
    by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp]; exact u₁.sp⟩
  obtain v₈ : Vars s₀ s₈ :=
    ⟨by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]; exact u₁.other _ (by decide),
      by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide)]; exact t0₁,
      by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
        u₄.other _ (by decide), u₃.other _ (by decide)]; exact u₁.other _ (by decide),
      by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide)]; exact u₁.other _ (by decide),
      fun r hr => by
        rw [u₈.other r (by revert r; decide), u₇.other r (by revert r; decide),
          u₆.other r (by revert r; decide), u₅.other r (by revert r; decide),
          u₄.other r (by revert r; decide), u₃.other r (by revert r; decide)]
        exact u₁.other r (by revert r; decide)⟩
  obtain a0₈ : s₈.gpr .a0 = inn s₀ := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide)]; exact u₁.other _ (by decide)
  obtain a1₈ : s₈.gpr .a1 = s₀.gpr .a2 := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide)]; exact u₁.other _ (by decide)
  obtain a2₈ : s₈.gpr .a2 = fr s₀ := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide)]; exact t0₁
  obtain m₈ : s₈.mem = Spill.saveMem s₀.mem (fr s₀) s₁.gpr (Hash.savedAt H.fso) := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, t0₁, u₁.mem]
  obtain f₈ : Frame [svR H s₀] s₀.mem s₈.mem := by
    rw [m₈]; exact Spill.saveMem_frame savedAt_in (by have := hp.top; omega_using [hfb]) _ _ _
  obtain sv₈ : Spill.Saved (fr s₀) s₀.gpr (Hash.savedAt H.fso) s₈.mem := by
    rw [m₈]
    intro p hp'
    rw [Spill.saveMem_saved (savedAt_fits ⟨hfso.2, by omega_using [hfb]⟩) _ _ _ p hp']
    refine u₁.other _ ?_
    simp only [Hash.savedAt, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  obtain hlen : ∀ k0 text, Hyp hH s₀ k0 text → (xorPad k0 ipad ++ text).length = H.B + text.length := by
    intro k0 text h; simp [xorPad, h.1, hH.hB]
  obtain hrI₈ : ∀ k0 text, Hyp hH s₀ k0 text → hH.SH.Repr s₈.mem (inn s₀) (xorPad k0 ipad ++ text) :=
    fun k0 text h => hH.congr s₀.mem s₈.mem (inn s₀) _ (fun i hi => f₈.bytes (R := inR H s₀) (by
      simp only [List.mem_singleton]; rintro r rfl; exact sv_i.symm)
      (by show H.S ≤ 2 ^ 64; omega_using [hN, hB, hS]) hi) h.2.2.1
  -- The inner digest, into the frame.
  refine WP.seq (hH.callFin_ok (st := inn s₀) (o := fr s₀) a0₈ a2₈ i_d (by rw [r₈.sp]; exact hp.al)
    (by rw [r₈.sp]; exact hp.spF) (by rw [r₈.sp]; exact hp.s_i) (by rw [r₈.sp]; exact s_d)
    (by rw [r₈.rd, r₈.wr]; exact (VG.Covers.pair (cover_self hwi) hcovD).right)
    (by rw [r₈.wr]; exact VG.Covers.pair (cover_self hwi) hcovD)
    fun s₉ rd₉ wr₉ sp₉ f₉ cs₉ hfin₉ => ?_)
  rw [r₈.sp] at f₉
  obtain r₉ : Regs s₀ s₉ := ⟨rd₉.trans r₈.rd, wr₉.trans r₈.wr, sp₉.trans r₈.sp⟩
  obtain v₉ := v₈.of_pres cs₉
  obtain hrs₉ : ∀ r ∈ [inR H s₀, digR H s₀] ++ [stk H s₀], (outR H s₀).Disjoint r ∧ (svR H s₀).Disjoint r := by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact ⟨hp.i_o.symm, sv_i⟩
    · exact ⟨hp.f_o.symm.sub_right (dig_sub hl), (dig_sv hl).symm⟩
    · exact ⟨hp.s_o.symm, sv_s⟩
  obtain sv₉ := sv₈.frame_in savedAt_in f₉ fun r hr => (hrs₉ r hr).2
  obtain hdg₉ : ∀ k0 text, Hyp hH s₀ k0 text →
      bytesAt s₉.mem (fr s₀) H.D = hH.SH.H.hash (xorPad k0 ipad ++ text) := fun k0 text h =>
    hfin₉ _ (hrI₈ k0 text h) (by rw [hlen k0 text h, ← hH.hB, ← h.1]; exact h.2.1)
      (by rw [a1₈, hlen k0 text h, ← hH.hB]; exact h.2.2.2.1)
  -- The outer hash value over the inner one's.
  obtain e0 : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => by simp
  refine WP.seq (copy8_ok (src := .s9) (dst := .s7) (by decide) (by decide) H.N (by omega_using [hN]) _ s₉ _
    (fun k hk => ⟨outR H s₀, by rw [r₉.rd, r₉.wr]; exact List.mem_append_left _ hro, by
      rw [v₉.s9]; exact Offset.contains_base _ (show k + 1 ≤ H.S by omega_using [hS, hk]) (by omega_using [hN, hk])⟩)
    (fun k hk => ⟨inR H s₀, by rw [r₉.wr]; exact hwi, by
      rw [v₉.s7]; exact Offset.contains_base _ (show k + 1 ≤ H.S by omega_using [hS, hk]) (by omega_using [hN, hk])⟩)
    (by
      rw [v₉.s9, v₉.s7]
      exact hp.i_o.symm.sep (contains_start (show H.N ≤ H.S by omega_using [hS]))
        (contains_start (show H.N ≤ H.S by omega_using [hS])))
    fun s₁₀ g₁₀ rd₁₀ wr₁₀ sp₁₀ m₁₀ => ?_)
  rw [v₉.s7, v₉.s9] at m₁₀
  refine wp_mv fun s₁₁ u₁₁ => wp_li (by omega_using [hB]) fun s₁₂ u₁₂ => wp_mv fun s₁₃ u₁₃ =>
    wp_li (by omega_using [hD]) fun s₁₄ u₁₄ => WP.block_nil ?_
  obtain r₁₄ : Regs s₀ s₁₄ := ⟨by rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, rd₁₀, r₉.rd],
    by rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, wr₁₀, r₉.wr], by rw [u₁₄.sp, u₁₃.sp, u₁₂.sp, u₁₁.sp, sp₁₀, r₉.sp]⟩
  obtain m₁₄ : s₁₄.mem = s₁₀.mem := by rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem]
  obtain v₁₄ : Vars s₀ s₁₄ := v₉.of_keep fun r a b c d e => by
    rw [u₁₄.other r d, u₁₃.other r c, u₁₂.other r b, u₁₁.other r a, g₁₀ r e]
  obtain fC : Frame [inR H s₀] s₉.mem s₁₀.mem := by
    rw [m₁₀]
    exact VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [VG.Proof.Hmac.Common.bytesAt_length]
      exact contains_start (show H.N ≤ H.S by omega_using [hS]))
  obtain sv₁₄ : Spill.Saved (fr s₀) s₀.gpr (Hash.savedAt H.fso) s₁₄.mem := by
    rw [m₁₄]
    exact sv₉.frame_in savedAt_in fC (by simp only [List.mem_singleton]; rintro r rfl; exact sv_i)
  obtain hrO₁₄ : ∀ k0 text, Hyp hH s₀ k0 text → hH.SH.Repr s₁₄.mem (inn s₀) (xorPad k0 opad) := by
    intro k0 text h
    refine hH.reloc s₀.mem s₁₄.mem (out s₀) (inn s₀) _ (by simp [xorPad, h.1, hH.hB]) (fun i hi => ?_)
      h.2.2.2.2
    rw [m₁₄, m₁₀, VG.Proof.Hmac.Common.writeBytes_at _ _ _
      (by rw [VG.Proof.Hmac.Common.bytesAt_length]; exact hi)
      (by rw [VG.Proof.Hmac.Common.bytesAt_length]; omega_using [hN]), VG.Proof.Hmac.Common.bytesAt_getD' _ _ hi,
      out_keep f₉ (fun r hr => (hrs₉ r hr).1) i (by omega_using [hS, hi])]
    exact out_keep f₈ (by simp only [List.mem_singleton]; rintro r rfl
                          exact hp.f_o.symm.sub_right (sv_sub hl)) i (by omega_using [hS, hi])
  obtain hdg₁₄ : ∀ k0 text, Hyp hH s₀ k0 text →
      bytesAt s₁₄.mem (fr s₀) H.D = hH.SH.H.hash (xorPad k0 ipad ++ text) := by
    intro k0 text h
    rw [← hdg₉ k0 text h, m₁₄]
    exact Proof.Sha256.Stream.bytesAt_congr fun i hi => fC.bytes (R := digR H s₀) (by
      simp only [List.mem_singleton]; rintro r rfl; exact i_d.symm)
      (by show H.D ≤ 2 ^ 64; omega_using [hD]) hi
  -- Absorb the inner digest.
  refine WP.seq (hH.callUpd_ok (st := inn s₀) (dat := fr s₀) (len := H.D)
    (by rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr,
      g₁₀ _ (by decide), v₉.s7])
    (by rw [u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      g₁₀ _ (by decide), v₉.s8])
    (by rw [u₁₄.gpr, BitVec.toNat_ofNat]; omega_using [hD])
    i_d.symm (by rw [r₁₄.sp]; exact hp.al) (by rw [r₁₄.sp]; exact hp.spF)
    (by rw [r₁₄.sp]; exact hp.s_i) (by rw [r₁₄.sp]; exact s_d)
    (by rw [r₁₄.rd, r₁₄.wr]; exact (VG.Covers.append_left hcovD (cover_self hwi)).right)
    (by rw [r₁₄.wr]; exact cover_self hwi)
    fun s₁₅ rd₁₅ wr₁₅ sp₁₅ f₁₅ cs₁₅ hup₁₅ => ?_)
  rw [r₁₄.sp] at f₁₅
  obtain r₁₅ : Regs s₀ s₁₅ := ⟨rd₁₅.trans r₁₄.rd, wr₁₅.trans r₁₄.wr, sp₁₅.trans r₁₄.sp⟩
  obtain v₁₅ := v₁₄.of_pres cs₁₅
  obtain a1₁₄ : s₁₄.gpr .a1 = BitVec.ofNat 64 H.B := by
    rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr]
  obtain hrI₁₅ : ∀ k0 text, Hyp hH s₀ k0 text →
      hH.SH.Repr s₁₅.mem (inn s₀) (xorPad k0 opad ++ hH.SH.H.hash (xorPad k0 ipad ++ text)) := by
    intro k0 text h
    have := hup₁₅ _ (hrO₁₄ k0 text h) (by rw [a1₁₄]; simp [xorPad, h.1, hH.hB])
    rwa [hdg₁₄ k0 text h] at this
  obtain sv₁₅ := sv₁₄.frame_in savedAt_in f₁₅ (by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [sv_i, sv_s])
  -- The MAC, into `out`.
  refine WP.seq (wp_mv fun s₁₆ u₁₆ => wp_li (by omega_using [hB, hD]) fun s₁₇ u₁₇ => wp_mv fun s₁₈ u₁₈ => WP.block_nil ?_)
  obtain r₁₈ : Regs s₀ s₁₈ := ⟨by rw [u₁₈.rd, u₁₇.rd, u₁₆.rd, r₁₅.rd], by rw [u₁₈.wr, u₁₇.wr, u₁₆.wr, r₁₅.wr],
    by rw [u₁₈.sp, u₁₇.sp, u₁₆.sp, r₁₅.sp]⟩
  obtain m₁₈ : s₁₈.mem = s₁₅.mem := by rw [u₁₈.mem, u₁₇.mem, u₁₆.mem]
  obtain v₁₈ : Vars s₀ s₁₈ := v₁₅.of_keep fun r a b c _ _ => by
    rw [u₁₈.other r c, u₁₇.other r b, u₁₆.other r a]
  refine WP.seq (hH.callFin_ok (st := inn s₀) (o := mac s₀)
    (by rw [u₁₈.other _ (by decide), u₁₇.other _ (by decide), u₁₆.gpr, v₁₅.s7])
    (by rw [u₁₈.gpr, u₁₇.other _ (by decide), u₁₆.other _ (by decide), v₁₅.s10])
    hp.i_m (by rw [r₁₈.sp]; exact hp.al) (by rw [r₁₈.sp]; exact hp.spF) (by rw [r₁₈.sp]; exact hp.s_i)
    (by rw [r₁₈.sp]; exact hp.s_m)
    (by rw [r₁₈.rd, r₁₈.wr]; exact (VG.Covers.pair (cover_self hwi) (cover_self hwm)).right)
    (by rw [r₁₈.wr]; exact VG.Covers.pair (cover_self hwi) (cover_self hwm))
    fun s₁₉ rd₁₉ wr₁₉ sp₁₉ f₁₉ cs₁₉ hfin₁₉ => ?_)
  rw [r₁₈.sp] at f₁₉
  obtain r₁₉ : Regs s₀ s₁₉ := ⟨rd₁₉.trans r₁₈.rd, wr₁₉.trans r₁₈.wr, sp₁₉.trans r₁₈.sp⟩
  obtain v₁₉ := v₁₈.of_pres cs₁₉
  obtain hmac₁₉ : ∀ k0 text, Hyp hH s₀ k0 text →
      bytesAt s₁₉.mem (mac s₀) H.D = hmacBlockKey hH.SH.H k0 text := by
    intro k0 text h
    obtain hl' : (xorPad k0 opad ++ hH.SH.H.hash (xorPad k0 ipad ++ text)).length = H.B + H.D := by
      simp [xorPad, h.1, hH.hB, hH.hashLen]
    exact hfin₁₉ _ (by rw [m₁₈]; exact hrI₁₅ k0 text h) (by rw [hl']; omega_using [hB, hD])
      (by rw [hl', u₁₈.other _ (by decide), u₁₇.gpr])
  obtain sv₁₉ := (by rw [m₁₈]; exact sv₁₅ : Spill.Saved (fr s₀) s₀.gpr (Hash.savedAt H.fso) s₁₈.mem).frame_in
    savedAt_in f₁₉ (by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      exacts [sv_i, sv_m, sv_s])
  -- Restore our caller's registers.
  rw [← List.append_nil (Spill.restoreCode _ _)]
  refine Spill.restore_ok (B := fr s₀) hal8 v₁₉.s8
    (fun p hp' => savedAt_off ⟨hfso.2, by omega_using [hfb]⟩ p (restList_mem.mp hp')) (restorable _)
    (fun p hp' => ⟨frR H s₀, by rw [r₁₉.rd, r₁₉.wr]; exact List.mem_append_right _ hwf,
      Offset.contains_base _ (by have := savedAt_in p (restList_mem.mp hp'); omega_using [hfb, this])
        (by have := savedAt_in p (restList_mem.mp hp'); omega_using [hfb, this])⟩)
    (sv₁₉.sub fun p hp' => restList_mem.mp hp') fun s' hs' => WP.block_nil ?_
  refine ⟨preserved_of (so := H.fso) (fun p hp' => hs'.gpr p (restList_mem.mpr hp')) fun r hr => ?_,
    hs'.gpr (.ra, H.fso) (by simp [restList]), by rw [hs'.sp, r₁₉.sp], by rw [hs'.wr, r₁₉.wr],
    fun k0 text h => by rw [hs'.mem]; exact hmac₁₉ k0 text h⟩
  rw [hs'.other r (by rw [restList_fst]; revert r; decide)]
  exact v₁₉.nv r hr

/-- The state the frame's body starts in, from `finalize`'s precondition. -/
theorem pre_alloc {s : State} (hp : (finG hH.SH (H.fbytes + H.F)).pre s) : Pre H (allocd H.fbytes s) := by
  have hl := hH.lay
  have hfb := hl.fbytes
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hp
  rw [hH.hS, hH.hD] at *
  obtain hsp := toNat_sub (sp := s.sp) (n := H.fbytes) (by omega_using [h7]) (by omega_using [hfb])
  obtain subF : Region.Sub ⟨s.sp - BitVec.ofNat 64 H.fbytes, H.fbytes⟩ (below s.sp (H.fbytes + H.F)) :=
    Offset.sub_below s.sp (by omega_using []) (by omega_using [])
  obtain subS : Region.Sub (below (s.sp - BitVec.ofNat 64 H.fbytes) H.F) (below s.sp (H.fbytes + H.F)) := by
    have := below_body' s.sp H.fbytes H.F
    rwa [Nat.add_comm H.F] at this
  have hsp' : (allocd H.fbytes s).sp = s.sp - BitVec.ofNat 64 H.fbytes := rfl
  refine ⟨h1, by show _ :: s.wr = _; rw [h2]; rfl, h3, h4, h5, h8.sub_left subF, h9.sub_left subF,
    h10.sub_left subF, ?_, ?_, ?_, h8.sub_left subS, h9.sub_left subS, h10.sub_left subS⟩
  · rw [hsp', hsp]; omega_using [hfb, h6]
  · rw [hsp', hsp]; omega_using [h7]
  · rw [hsp', hsp]; have := s.sp.isLt; omega_using [hfb]

/-- HMAC's `finalize`. -/
theorem correct {s : State} (hp : (finG hH.SH (H.fbytes + H.F)).pre s) :
    WP isa H.finalize s fun s' => abiPreserved s s' ∧ (finG hH.SH (H.fbytes + H.F)).post s s' := by
  have hl := hH.lay
  have hfb := hl.fbytes
  obtain hsp : H.fbytes ≤ s.sp.toNat := by have := hp.2.2.2.2.2.2.1; omega_using [this]
  refine WP.alloc ⟨by omega_using [hfb], hfb.2.1, hfb.2.2⟩ hsp
    (WP.mono (finalizeMain_ok hH (pre_alloc hH hp)) fun s' ⟨hk, hra, hsp', hwr, hmac⟩ m u f => ?_)
  rw [freed_eq hwr hsp']
  -- The `free` loses the frame's bytes, which lie apart from the MAC.
  refine ⟨⟨hk, rfl, hra⟩, fun k0 text hk0 hlt hI hc hO => ?_⟩
  rw [hH.hD]
  refine Eq.trans ?_ (hmac k0 text ⟨hk0, hlt, hI, hc, hO⟩)
  exact Proof.Sha256.Stream.bytesAt_congr fun i hi =>
    lost_byte f (R := macR H (allocd H.fbytes s)) (pre_alloc hH hp).f_m.symm hi

end VG.Proof.Hmac.Stream.RISCV64.Finalize
