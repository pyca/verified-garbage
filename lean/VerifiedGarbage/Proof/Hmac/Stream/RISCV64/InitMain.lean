module

public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Init
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc

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
  simp only [blockKey, PadKey.K0, hH.hB, K_length, show ¬ (H.B < kl s₀) by omega, ite_false]

/-- For a longer key: its digest. -/
theorem blockKey_long (hH : HashOK H) (h : H.B < kl s₀) :
    PadKey.K0 (hH.SH.H.hash (K s₀)) H.B = blockKey hH.SH.H (K s₀) := by
  simp only [blockKey, PadKey.K0, hH.hB, K_length, h, ite_true]

theorem ofNat_kl (s₀ : State) : BitVec.ofNat 64 (kl s₀) = s₀.gpr .a3 := by
  rw [kl, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The key, for a key of at most a block. -/
theorem keyOK_short (hp : Pre H s₀) (h : kl s₀ ≤ H.B) : KeyOK H s₀ (kp s₀) (kl s₀) :=
  ⟨h, fun j hj => ⟨kR s₀, by rw [hp.rd]; exact List.mem_append_left _ (List.mem_singleton_self _),
    Offset.contains_base _ (show j + 1 ≤ kl s₀ by omega)
      (by have : kl s₀ < 2 ^ 64 := (s₀.gpr .a3).isLt; omega)⟩,
    hp.k_i, hp.k_o, hp.s_k.symm⟩

/-- The long key's digest, in the frame. -/
theorem keyOK_long (hp : Pre H s₀) (hl : Lay H) : KeyOK H s₀ (fr s₀ + BitVec.ofNat 64 H.S) H.D := by
  have hD := hl.D
  have hB := hl.B
  have hiso := hl.iso
  have hib := hl.ibytes
  have hw : frR H s₀ ∈ s₀.rd ++ s₀.wr := by
    rw [hp.wr]; exact List.mem_append_right _ (List.mem_cons_self ..)
  refine ⟨by omega, fun j hj => ⟨frR H s₀, hw, ?_⟩, hp.f_i.sub_left (ldg_sub hl),
    hp.f_o.sub_left (ldg_sub hl), hp.f_s.sub_left (ldg_sub hl)⟩
  rw [Offset.add_add]
  exact Offset.contains_base _ (show H.S + j + 1 ≤ H.ibytes by omega) (by omega)

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
  have hS : H.S < 2048 := by omega
  have hwf : frR H s₀ ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_self ..
  have hrk : kR s₀ ∈ s₀.rd := by rw [hp.rd]; exact List.mem_singleton_self _
  have kS : (kR s₀).Disjoint ⟨fr s₀, H.S⟩ := hp.f_k.symm.sub_right (lst_sub hl)
  have sS : (stk H s₀).Disjoint ⟨fr s₀, H.S⟩ := hp.f_s.symm.sub_right (lst_sub hl)
  have sD : (stk H s₀).Disjoint ⟨fr s₀ + BitVec.ofNat 64 H.S, H.D⟩ := hp.f_s.symm.sub_right (ldg_sub hl)
  have kl_lt : kl s₀ < 2 ^ 64 := (s₀.gpr .a3).isLt
  unfold Hash.longKey
  -- The streaming state's hash value.
  refine WP.seq (wp_mv fun s₁ u₁ => WP.block_nil ?_)
  have r₁ : Regs s₀ s₁ := ⟨by rw [u₁.rd, hr.rd], by rw [u₁.wr, hr.wr], by rw [u₁.sp, hr.sp]⟩
  have v₁ : Vars s₀ s₁ (kp s₀) (kl s₀) := hv.of_keep fun r a _ _ _ _ _ _ _ _ _ => u₁.other r a
  refine WP.seq (hH.callInit_ok (st := fr s₀) (by rw [u₁.gpr, hv.s8])
    (by rw [r₁.rd, r₁.wr]; exact cover_pre (List.mem_append_right _ hwf) (show H.S ≤ H.ibytes by omega))
    (by rw [r₁.wr]; exact cover_pre hwf (show H.S ≤ H.ibytes by omega)) fun s₂ rd₂ wr₂ sp₂ f₂ cs₂ hrS₂ => ?_)
  rw [r₁.sp, u₁.mem] at f₂
  have r₂ : Regs s₀ s₂ := ⟨rd₂.trans r₁.rd, wr₂.trans r₁.wr, sp₂.trans r₁.sp⟩
  have v₂ := v₁.of_pres cs₂
  have hrs₂ : ∀ r ∈ [(⟨fr s₀, H.S⟩ : Region)] ++ [stk H s₀], r = ⟨fr s₀, H.S⟩ ∨
      r = ⟨fr s₀ + BitVec.ofNat 64 H.S, H.D⟩ ∨ r = stk H s₀ := by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [.inl rfl, .inr (.inr rfl)]
  have sv₂ := sv_keep hp hl hsv f₂ hrs₂
  have k₂ : bytesAt s₂.mem (kp s₀) (kl s₀) = K s₀ := by
    rw [← hk]
    refine Proof.Sha256.Stream.bytesAt_congr fun i hi => f₂.bytes (R := kR s₀) (fun r hr => ?_)
      (by show kl s₀ ≤ 2 ^ 64; omega) hi
    rcases hrs₂ r hr with rfl | rfl | rfl
    exacts [kS, hp.f_k.symm.sub_right (ldg_sub hl), hp.s_k.symm]
  -- Absorb the key.
  refine WP.seq (wp_mv fun s₃ u₃ => wp_li (by decide) fun s₄ u₄ => wp_mv fun s₅ u₅ =>
    wp_mv fun s₆ u₆ => WP.block_nil ?_)
  have r₆ : Regs s₀ s₆ := ⟨by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, r₂.rd], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, r₂.wr],
    by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, r₂.sp]⟩
  have m₆ : s₆.mem = s₂.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have v₆ : Vars s₀ s₆ (kp s₀) (kl s₀) := v₂.of_keep fun r a b c d _ _ _ _ _ _ => by
    rw [u₆.other r d, u₅.other r c, u₄.other r b, u₃.other r a]
  have a1₆ : s₆.gpr .a1 = BitVec.ofNat 64 ([] : List Byte).length := by
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
        (cover_pre (List.mem_append_right _ hwf) (show H.S ≤ H.ibytes by omega)))
    (by rw [r₆.wr]; exact cover_pre hwf (show H.S ≤ H.ibytes by omega)) fun s₇ rd₇ wr₇ sp₇ f₇ cs₇ hup => ?_)
  rw [r₆.sp, m₆] at f₇
  have r₇ : Regs s₀ s₇ := ⟨rd₇.trans r₆.rd, wr₇.trans r₆.wr, sp₇.trans r₆.sp⟩
  have v₇ := v₆.of_pres cs₇
  have sv₇ := sv_keep hp hl sv₂ f₇ hrs₂
  have hrS₇ : hH.SH.Repr s₇.mem (fr s₀) (K s₀) := by
    have := hup [] (by rw [m₆]; exact hrS₂) a1₆
    rwa [List.nil_append, m₆, k₂] at this
  -- Its digest, after the streaming state.
  refine WP.seq (wp_mv fun s₈ u₈ => wp_mv fun s₉ u₉ => wp_addi (by omega) fun s₁₀ u₁₀ => WP.block_nil ?_)
  have r₁₀ : Regs s₀ s₁₀ := ⟨by rw [u₁₀.rd, u₉.rd, u₈.rd, r₇.rd], by rw [u₁₀.wr, u₉.wr, u₈.wr, r₇.wr],
    by rw [u₁₀.sp, u₉.sp, u₈.sp, r₇.sp]⟩
  have m₁₀ : s₁₀.mem = s₇.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem]
  have v₁₀ : Vars s₀ s₁₀ (kp s₀) (kl s₀) := v₇.of_keep fun r a b c _ _ _ _ _ _ _ => by
    rw [u₁₀.other r c, u₉.other r b, u₈.other r a]
  have hcov : VG.Covers [⟨fr s₀, H.S⟩, ⟨fr s₀ + BitVec.ofNat 64 H.S, H.D⟩] s₀.wr :=
    VG.Covers.pair (cover_pre hwf (show H.S ≤ H.ibytes by omega))
      (cover_off hwf (show H.S + H.D ≤ H.ibytes by omega))
  refine WP.seq (hH.callFin_ok (st := fr s₀) (o := fr s₀ + BitVec.ofNat 64 H.S)
    (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, v₇.s8])
    (by rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), v₇.s8])
    (lst_ldg hl) (by rw [r₁₀.sp]; exact hp.al) (by rw [r₁₀.sp]; exact hp.spF) (by rw [r₁₀.sp]; exact sS)
    (by rw [r₁₀.sp]; exact sD) (by rw [r₁₀.rd, r₁₀.wr]; exact hcov.right) (by rw [r₁₀.wr]; exact hcov)
    fun s₁₁ rd₁₁ wr₁₁ sp₁₁ f₁₁ cs₁₁ hfin => ?_)
  rw [r₁₀.sp, m₁₀] at f₁₁
  have r₁₁ : Regs s₀ s₁₁ := ⟨rd₁₁.trans r₁₀.rd, wr₁₁.trans r₁₀.wr, sp₁₁.trans r₁₀.sp⟩
  have v₁₁ := v₁₀.of_pres cs₁₁
  have sv₁₁ := sv_keep hp hl sv₇ f₁₁ (by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [.inl rfl, .inr (.inl rfl), .inr (.inr rfl)])
  have hdg : bytesAt s₁₁.mem (fr s₀ + BitVec.ofNat 64 H.S) H.D = hH.SH.H.hash (K s₀) :=
    hfin (K s₀) (by rw [m₁₀]; exact hrS₇) (by rw [K_length]; exact kl_lt)
      (by rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), v₇.s11, K_length])
  -- The key is the digest.
  refine wp_addi (by omega) fun s₁₂ u₁₂ => wp_li (by omega) fun s₁₃ u₁₃ => WP.block_nil ?_
  have m₁₃ : s₁₃.mem = s₁₁.mem := by rw [u₁₃.mem, u₁₂.mem]
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
  have hal8 : (fr s₀).toNat % 8 = 0 := by show s₀.sp.toNat % 8 = 0; have := hp.al; omega
  rw [initMain_eq]
  refine WP.seq (wp_addSp (imm := 0) (by decide) fun s₁ u₁ => ?_)
  have t0₁ : s₁.gpr .t0 = fr s₀ := by rw [u₁.gpr, BitVec.add_zero]
  refine Spill.save_ok (by rw [t0₁]; exact hal8) (savedAt_off ⟨hiso.2, by omega⟩)
    (fun p hp' => ⟨frR H s₀, by rw [u₁.wr, hp.wr]; exact List.mem_cons_self,
      (by
        rw [t0₁]
        have := savedAt_in p hp'
        exact Offset.contains_base (k := H.ibytes) _ (by omega) (by omega))⟩) ?_
  refine wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ =>
    wp_mv fun s₇ u₇ => entry_ok hH.hb fun u gu mu rdu wru spu cu => WP.block_nil ?_
  -- The state after the prologue.
  have g₇ : ∀ r, r ≠ .s7 → r ≠ .s8 → r ≠ .s9 → r ≠ .s10 → r ≠ .s11 → r ≠ .t0 → s₇.gpr r = s₀.gpr r :=
    fun r a b c d e f => by
      rw [u₇.other r e, u₆.other r d, u₅.other r c, u₄.other r b, u₃.other r a]
      exact u₁.other r f
  have gU : ∀ r, r ≠ .s7 → r ≠ .s8 → r ≠ .s9 → r ≠ .s10 → r ≠ .s11 → r ≠ .t0 → r ≠ .t1 → r ≠ .t2 →
      u.gpr r = s₀.gpr r := fun r a b c d e f g h => by rw [gu r g h]; exact g₇ r a b c d e f
  have hr : Regs s₀ u := ⟨by rw [rdu, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd]; exact u₁.rd,
    by rw [wru, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr]; exact u₁.wr,
    by rw [spu, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp]; exact u₁.sp⟩
  have hv : Vars s₀ u (kp s₀) (kl s₀) :=
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
  have hmu : u.mem = Spill.saveMem s₀.mem (fr s₀) s₁.gpr (Hash.savedAt H.iso) := by
    rw [mu, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, t0₁, u₁.mem]
  have hfu : Frame [svR H s₀] s₀.mem u.mem := by
    rw [hmu]; exact Spill.saveMem_frame savedAt_in (by have := hp.top; omega) _ _ _
  have hk : bytesAt u.mem (kp s₀) (kl s₀) = K s₀ :=
    Proof.Sha256.Stream.bytesAt_congr fun i hi => hfu.bytes (R := kR s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.f_k.symm.sub_right (sv_sub hl))
      (by show kl s₀ ≤ 2 ^ 64; have : kl s₀ < 2 ^ 64 := (s₀.gpr .a3).isLt; omega) hi
  have hsv : Spill.Saved (fr s₀) s₀.gpr (Hash.savedAt H.iso) u.mem := by
    rw [hmu]
    intro p hp'
    rw [Spill.saveMem_saved (savedAt_fits ⟨hiso.2, by omega⟩) _ _ _ p hp']
    refine u₁.other _ ?_
    simp only [Hash.savedAt, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  have hz : isa.eval (.zero .t1) u = some (decide (kl s₀ ≤ H.B)) := by
    rw [Steps.eval_zero, cu, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₁.other _ (by decide)]
  refine WP.seq (WP.ite _ hz (fun hb => ?_) (fun hb => ?_))
  · have hkl : kl s₀ ≤ H.B := of_decide_eq_true hb
    exact WP.block_nil (core_ok hH hp (keyOK_short hp hkl) (blockKey_short hH hkl) ⟨hr, hv, hk, hsv⟩)
  · have hkl : H.B < kl s₀ := by have := of_decide_eq_false hb; omega
    exact WP.mono (longKey_ok hH hp hr hv hk hsv) fun s' h =>
      core_ok hH hp (keyOK_long hp hl) (blockKey_long hH hkl) h

/-- The state the frame's body starts in, from `init`'s precondition. -/
theorem pre_alloc {s : State} (hp : (initG hH.SH (H.ibytes + H.F)).pre s) : Pre H (allocd H.ibytes s) := by
  have hl := hH.lay
  have hib := hl.ibytes
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hp
  rw [hH.hS] at h2 h3 h4 h5 h8 h9
  have hsp := toNat_sub (sp := s.sp) (n := H.ibytes) (by omega) (by omega)
  have subF : Region.Sub ⟨s.sp - BitVec.ofNat 64 H.ibytes, H.ibytes⟩ (below s.sp (H.ibytes + H.F)) :=
    Offset.sub_below s.sp (by omega) (by omega)
  have subS : Region.Sub (below (s.sp - BitVec.ofNat 64 H.ibytes) H.F) (below s.sp (H.ibytes + H.F)) := by
    have := below_body' s.sp H.ibytes H.F
    rwa [Nat.add_comm H.F] at this
  have hsp' : (allocd H.ibytes s).sp = s.sp - BitVec.ofNat 64 H.ibytes := rfl
  refine ⟨h1, by show _ :: s.wr = _; rw [h2]; rfl, h3, h4, h5, h8.sub_left subF, h9.sub_left subF, h10.sub_left subF,
    ?_, ?_, ?_, h8.sub_left subS, h9.sub_left subS, h10.sub_left subS⟩
  · rw [hsp', hsp]; omega
  · rw [hsp', hsp]; omega
  · rw [hsp', hsp]; have := s.sp.isLt; omega

/-- HMAC's `init`, for a key of any length. -/
theorem correct {s : State} (hp : (initG hH.SH (H.ibytes + H.F)).pre s) :
    WP isa H.init s fun s' => abiPreserved s s' ∧ (initG hH.SH (H.ibytes + H.F)).post s s' := by
  have hl := hH.lay
  have hib := hl.ibytes
  have hsp : H.ibytes ≤ s.sp.toNat := by have := hp.2.2.2.2.2.2.1; omega
  refine WP.alloc ⟨by omega, hib.2.1, hib.2.2⟩ hsp
    (WP.mono (initMain_ok hH (pre_alloc hH hp)) fun s' ⟨hk, hra, hsp', hwr, hI, hO⟩ => ?_)
  rw [freed_eq hwr hsp']
  exact ⟨⟨hk, rfl, hra⟩, hI, hO⟩

end VG.Proof.Hmac.Stream.RISCV64.Init
