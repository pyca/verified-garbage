import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha256
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Scrypt.X86.Whole.Calls

section

/-!
# scrypt on x86 (32-bit): correctness

As on x86-64 (`Proof/Scrypt/X86_64/Whole/Correct.lean`): step 1 leaves the
blocks `X k` of `PBKDF2-HMAC-SHA256 (P, S, 1, 128 blen)` in `b` (`step1_ok`);
the loop replaces them by their scryptROMix one at a time (`Inv`, `loop_ok`);
step 3 derives the key from them (`step3_ok`). `scrypt_ok` puts the frame
around it (`push_ctx`), for any implementation `pbk` of PBKDF2 verified
against its shared contract that uses at most 76 bytes of stack.
-/

namespace VG.Proof.Scrypt.X86.Whole

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (bytesAt)

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## The password, the salt and the blocks -/

namespace Ctx

variable {t : State} (hc : Ctx L g m₀ t) (hL : L.Ok)
include hc hL

theorem pw_bytes : bytesAt t.mem (L.pw.setWidth 64) L.pwl.toNat = bytesAt m₀ (L.pw.setWidth 64) L.pwl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.pb, hL.pv, hL.pc, hL.po, hL.kp.symm]) (by have := hL.np; omega)

theorem salt_bytes :
    bytesAt t.mem (L.salt.setWidth 64) L.sl.toNat = bytesAt m₀ (L.salt.setWidth 64) L.sl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.sb, hL.sv, hL.sc, hL.so, hL.ks.symm]) (by have := hL.ns; omega)

end Ctx

/-- Block `k` of step 1. -/
def X (L : Lay) (m₀ : Mem) (k : Nat) : List Byte :=
  (Spec.Scrypt.blocks (bytesAt m₀ (L.pw.setWidth 64) L.pwl.toNat) (bytesAt m₀ (L.salt.setWidth 64) L.sl.toNat)
    L.r.toNat L.pp).getD k []

/-- The derived key of step 1, from the password and the salt on entry. -/
abbrev Step1 (L : Lay) (m₀ : Mem) (B : List Byte) : Prop :=
  Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ (L.pw.setWidth 64) L.pwl.toNat)
    (bytesAt m₀ (L.salt.setWidth 64) L.sl.toNat) 1 (L.blen.toNat * 128) = some B

theorem X_of (hL : L.Ok) {m : Mem} (h : Step1 L m₀ (bytesAt m (L.b.setWidth 64) (L.blen.toNat * 128))) {k : Nat}
    (hk : k < L.pp) : X L m₀ k = bytesAt m (blk L k) (128 * L.r.toNat) := by
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have h' : Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ (L.pw.setWidth 64) L.pwl.toNat)
      (bytesAt m₀ (L.salt.setWidth 64) L.sl.toNat) 1 (L.pp * 128 * L.r.toNat) =
      some (bytesAt m (L.b.setWidth 64) (L.pp * 128 * L.r.toNat)) := by rw [e]; exact h
  have hl : k < (Spec.Scrypt.blocks (bytesAt m₀ (L.pw.setWidth 64) L.pwl.toNat)
      (bytesAt m₀ (L.salt.setWidth 64) L.sl.toNat) L.r.toNat L.pp).length := by
    rw [Whole.blocks_length]; exact hk
  rw [X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some,
    Whole.blocks_getElem h' hl]

theorem blk_le' (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    128 * L.r.toNat * i + 128 * L.r.toNat ≤ L.blen.toNat * 128 := by
  have := blk_le hL hi; rw [Nat.mul_comm L.r.toNat 128] at this; exact this

/-- Distinct blocks are disjoint. -/
theorem blk_disj (hL : L.Ok) {k i : Nat} (hk : k < L.pp) (hi : i < L.pp) (hne : k ≠ i) :
    Region.Disjoint ⟨blk L k, 128 * L.r.toNat⟩ ⟨blk L i, L.r.toNat * 128⟩ := by
  have h₁ := blk_le hL hk
  have h₂ := blk_le hL hi
  have := hL.nb
  have hr := hL.rpos
  refine Offset.disjoint _ ?_ (by omega) (by omega)
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · left
    have : 128 * L.r.toNat * k + 128 * L.r.toNat ≤ 128 * L.r.toNat * i := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    omega
  · right
    have : 128 * L.r.toNat * i + 128 * L.r.toNat ≤ 128 * L.r.toNat * k := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    omega

theorem blk_sub (hL : L.Ok) {k : Nat} (hk : k < L.pp) :
    Region.Sub ⟨blk L k, 128 * L.r.toNat⟩ L.BB := by
  have := blk_le' hL hk
  exact Offset.sub_base _ (by omega)

theorem scr_sub (hL : L.Ok) : Region.Sub ⟨L.scr.setWidth 64, 200 * 8⟩ L.SC :=
  Within.sub (within_base _ (by have := hL.slen17; omega))

/-- A range in `b` misses the stack. -/
theorem b_stk (hL : L.Ok) {p : Addr} {n : Nat} (h : Region.Sub ⟨p, n⟩ L.BB) {d k : Nat} (hd : d + k ≤ 116) :
    Region.Disjoint ⟨p, n⟩ ⟨L.A + BitVec.ofNat 64 d, k⟩ :=
  (hL.kb.symm.sub_left h).sub_right (Offset.sub_base _ hd)

theorem toNat_blen (hL : L.Ok) : (BitVec.ofNat 32 (L.blen.toNat * 128)).toNat = L.blen.toNat * 128 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL.blen_lt]

/-! ## Step 1 -/

section
variable {pbk : Prog isa} (hv : Verified X86.target pbk (Spec.Hmac.sha256I.pbkdf2Contract X86.abi 76))
  (hsp : NoSp pbk) (hst : stackUse pbk ≤ 76) (name : String)
include hv hsp hst

omit hv hsp hst in
theorem pbk1_regions (hL : L.Ok) :
    PbkRegions L L.salt L.sl L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) := by
  refine ⟨⟨L.SALT, by simp, within_base _ (Nat.le_refl _)⟩, ?_, ?_, hL.sc.sub_right (scr_sub hL), ?_, hL.ks,
    hL.ns, ?_, ?_⟩
  · rw [toNat_blen hL]; exact .inl (within_base _ (Nat.le_refl _))
  · rw [toNat_blen hL]; exact hL.sb
  · rw [toNat_blen hL]; exact hL.bc.sub_right (scr_sub hL)
  · rw [toNat_blen hL]; exact hL.nb
  · rw [toNat_blen hL]; exact hL.ol1

theorem step1_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (pbkCall name pbk pbk1Args) t fun t' => Ctx L g m₀ t' ∧
      Step1 L m₀ (bytesAt t'.mem (L.b.setWidth 64) (L.blen.toNat * 128)) := by
  refine WP.seq (pbk1Args_ok hL hc fun t₁ hc₁ _ ha₁ => ?_)
  refine WP.mono (pbk_call hv hsp hst name hL hc₁ ha₁ (pbk1_regions hL)) fun t₂ ⟨hc₂, _, hp⟩ => ⟨hc₂, ?_⟩
  rw [toNat_blen hL, hc₁.pw_bytes hL, hc₁.salt_bytes hL] at hp
  exact hp

end

/-! ## The loop -/

/-- After `i` iterations of the loop: the next block is `i`, and blocks
`0, …, i - 1` are scryptROMix of those of step 1. -/
structure InvB (L : Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.mem.readW (L.A + BitVec.ofNat 64 112) 32 = cur L i
  blks : ∀ k < L.pp, bytesAt t.mem (blk L k) (128 * L.r.toNat) =
    if k < i then Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) else X L m₀ k

abbrev Inv (L : Lay) (g : Reg → BitVec 32) (m₀ : Mem) (i : Nat) (t : State) : Prop :=
  Ctx L g m₀ t ∧ InvB L m₀ i t

/-- In iteration `i`, after the call of ROMix: blocks `0, …, i` are scryptROMix
of those of step 1. -/
structure Mid (L : Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.mem.readW (L.A + BitVec.ofNat 64 112) 32 = cur L i
  blks : ∀ k < L.pp, bytesAt t.mem (blk L k) (128 * L.r.toNat) =
    if k < i + 1 then Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) else X L m₀ k

theorem cur0' (L : Lay) : cur L 0 = L.b := by
  simp only [cur, Nat.mul_zero]; exact BitVec.add_zero _

/-- The bytes of a block, across a change of the frame. -/
theorem blk_fr (hL : L.Ok) {k : Nat} (hk : k < L.pp) {m m' : Mem} (hf : Frame [L.FR] m m') :
    bytesAt m' (blk L k) (128 * L.r.toNat) = bytesAt m (blk L k) (128 * L.r.toNat) :=
  Memory.frame_bytesAt hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact b_stk hL (blk_sub hL hk) (by omega))
    (by have := hL.blen_lt; have := blk_le hL hk; omega)

theorem start_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t)
    (h1 : Step1 L m₀ (bytesAt t.mem (L.b.setWidth 64) (L.blen.toNat * 128))) :
    WP isa (.block cur0) t (Inv L g m₀ 0) :=
  cur0_ok hL hc fun t' hc' hf hb => ⟨hc', hb.trans (cur0' L).symm, fun k hk => by
    simp only [Nat.not_lt_zero, ite_false]
    rw [blk_fr hL hk hf, X_of hL h1 hk]⟩

theorem next_eq (L : Lay) (i : Nat) :
    cur L i + BitVec.ofNat 32 (L.r.toNat * 128) = cur L (i + 1) := by
  simp only [cur]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_succ (128 * L.r.toNat) i, Nat.mul_comm L.r.toNat 128]

theorem beq32 {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (BitVec.ofNat 32 x - BitVec.ofNat 32 y == 0) = decide (x = y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  bv_omega

theorem zf_eq (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    (cur L (i + 1) - (BitVec.ofNat 32 (L.blen.toNat * 128) + L.b) == 0) = decide (i + 1 = L.pp) := by
  have h₁ := blk_le hL hi
  have hb := hL.blen_lt
  have hr := hL.rpos
  have e₁ : 128 * L.r.toNat * (i + 1) < 2 ^ 32 := by
    rw [Nat.mul_succ]; omega
  rw [BitVec.add_comm (BitVec.ofNat 32 _) L.b]
  simp only [cur]
  rw [Offset.add_sub_add_left, ← hL.len_b, beq32 e₁ (by rw [hL.len_b]; exact hb)]
  refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => by rw [h]⟩
  exact Nat.eq_of_mul_eq_mul_left (by omega) h

theorem call_step (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (hc : Ctx L g m₀ t)
    (hb : InvB L m₀ i t) (ha : RomixArgs L (cur L i) t.mem) :
    WP isa (.call "vg_scrypt_romix" Impl.Scrypt.X86.roMix) t fun t' => Ctx L g m₀ t' ∧ Mid L m₀ i t' := by
  have hnB := hL.nB
  refine WP.mono (romix_call hL hc hi ha) fun t₂ ⟨hc₂, hf₂, hr₂⟩ => ⟨hc₂, ?_, fun k hk => ?_⟩
  · rw [← hb.cur]
    refine hf₂.readW (r := ⟨L.A + BitVec.ofNat 64 112, 4⟩) (Region.contains_self _ _) (fun r hr => ?_)
      (by decide)
    simp only [romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hL.stk_in (by omega) (blk_in hL hi)
    · exact hL.stk_in (by omega) (.inr (.inl (within_base _ (Nat.le_refl _))))
    · exact hL.stk_in (by omega) (.inr (.inr (.inl (within_base _ (by have := hL.slen; omega)))))
    · exact Offset.disjoint_base _ (by omega) (by omega)
  · by_cases hki : k = i
    · subst hki
      rw [hr₂, hb.blks k hk]
      simp only [Nat.lt_irrefl, ite_false, Nat.lt_succ_self, ite_true]
    · have e₂ : bytesAt t₂.mem (blk L k) (128 * L.r.toNat) = bytesAt t.mem (blk L k) (128 * L.r.toNat) :=
        Memory.frame_bytesAt hf₂ (fun r hr => by
          simp only [romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact blk_disj hL hk hi hki
          · exact hL.bv.sub_left (blk_sub hL hk)
          · exact (hL.bc.sub_left (blk_sub hL hk)).sub_right
              (Within.sub (within_base _ (by have := hL.slen; omega)))
          · exact (hL.kb.symm.sub_left (blk_sub hL hk)).sub_right (Region.sub_prefix (by omega)))
          (by have := hL.blen_lt; have := blk_le hL hk; omega)
      rw [e₂, hb.blks k hk]
      by_cases hlt : k < i
      · have : k < i + 1 := by omega
        simp only [hlt, this, ite_true]
      · have : ¬ k < i + 1 := by omega
        simp only [hlt, this, ite_false]

theorem body_ok (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (h : Inv L g m₀ i t) :
    WP isa (.seq (.block romixArgs) (.seq (.call "vg_scrypt_romix" Impl.Scrypt.X86.roMix)
      (.block nextBlock))) t fun t' => Inv L g m₀ (i + 1) t' ∧ t'.zf = some (decide (i + 1 = L.pp)) :=
  WP.seq (romixArgs_ok hL h.1 h.2.cur fun t₁ hc₁ hf₁ ha₁ hcur₁ =>
    WP.seq (WP.mono (call_step hL hi hc₁ ⟨hcur₁, fun k hk => by rw [blk_fr hL hk hf₁]; exact h.2.blks k hk⟩ ha₁)
      fun t₂ ⟨hc₂, hm₂⟩ => nextBlock_ok hL hc₂ hm₂.cur fun t₃ hc₃ hf₃ hb₃ hz₃ =>
        ⟨⟨hc₃, by rw [hb₃, next_eq], fun k hk => by rw [blk_fr hL hk hf₃]; exact hm₂.blks k hk⟩,
          by rw [hz₃, next_eq, zf_eq hL hi]⟩))

theorem loop_ok (hL : L.Ok) {t : State} (h : Inv L g m₀ 0 t) : WP isa romixLoop t (Inv L g m₀ L.pp) :=
  count_loop hL.pp_pos (Inv L g m₀) (fun _ hi _ h => body_ok hL hi h) h

/-! ## Step 3 -/

section
variable {pbk : Prog isa} (hv : Verified X86.target pbk (Spec.Hmac.sha256I.pbkdf2Contract X86.abi 76))
  (hsp : NoSp pbk) (hst : stackUse pbk ≤ 76) (name : String)
include hv hsp hst

omit hv hsp hst in
/-- The blocks after the loop, as one string. -/
theorem final_bytes' (hL : L.Ok) {t : State} (h : Inv L g m₀ L.pp t) :
    bytesAt t.mem (L.b.setWidth 64) (L.blen.toNat * 128) =
      (List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) := by
  rw [← hL.len_b, Whole.bytesAt_chunks]
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [h.2.blks k hk]; simp only [hk, ite_true]

omit hv hsp hst in
theorem pbk2_regions (hL : L.Ok) :
    PbkRegions L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) L.out L.ol := by
  refine ⟨⟨L.BB, by simp, ?_⟩, .inr (.inr (.inr (within_base _ (Nat.le_refl _)))), ?_,
    ?_, hL.co.symm.sub_right (scr_sub hL), ?_, ?_, hL.no, hL.olb⟩
  · rw [toNat_blen hL]; exact within_base _ (Nat.le_refl _)
  · rw [toNat_blen hL]; exact hL.bo
  · rw [toNat_blen hL]; exact hL.bc.sub_right (scr_sub hL)
  · rw [toNat_blen hL]; exact hL.kb
  · rw [toNat_blen hL]; exact hL.nb

theorem step3_ok (hL : L.Ok) {t : State} (h : Inv L g m₀ L.pp t) :
    WP isa (pbkCall name pbk pbk2Args) t fun t' => Ctx L g m₀ t' ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ (L.pw.setWidth 64) L.pwl.toNat)
        ((List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k)) 1 L.ol.toNat =
        some (bytesAt t'.mem (L.out.setWidth 64) L.ol.toNat) := by
  refine WP.seq (pbk2Args_ok hL h.1 fun t₁ hc₁ hf₁ ha₁ => ?_)
  refine WP.mono (pbk_call hv hsp hst name hL hc₁ ha₁ (pbk2_regions hL)) fun t₂ ⟨hc₂, _, hp⟩ => ⟨hc₂, ?_⟩
  have e : bytesAt t₁.mem (L.b.setWidth 64) (L.blen.toNat * 128) =
      bytesAt t.mem (L.b.setWidth 64) (L.blen.toNat * 128) :=
    Memory.frame_bytesAt hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact b_stk hL (fun _ h => h) (by omega))
      (by have := hL.blen_lt; omega)
  rw [toNat_blen hL, hc₁.pw_bytes hL, e, final_bytes' hL h] at hp
  exact hp

/-- The frame's body. -/
theorem body_scrypt_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (scryptBody name pbk) t fun t' => Ctx L g m₀ t' ∧
      Spec.Scrypt.scrypt (bytesAt m₀ (L.pw.setWidth 64) L.pwl.toNat) (bytesAt m₀ (L.salt.setWidth 64) L.sl.toNat)
        L.NN L.r.toNat L.pp L.ol.toNat = some (bytesAt t'.mem (L.out.setWidth 64) L.ol.toNat) := by
  refine WP.seq (WP.mono (step1_ok hv hsp hst name hL hc) fun t₁ ⟨hc₁, h1⟩ => ?_)
  refine WP.seq (WP.mono (start_ok hL hc₁ h1) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (loop_ok hL h₂) fun t₃ h₃ => ?_)
  refine WP.mono (step3_ok hv hsp hst name hL h₃) fun t₄ ⟨hc₄, hp⟩ => ⟨hc₄, ?_⟩
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  refine Whole.scrypt_eq hL.valid (B := bytesAt t₁.mem (L.b.setWidth 64) (L.blen.toNat * 128))
    (by rw [e]; exact h1) ?_
  refine Eq.trans (congrArg (fun x => Spec.Pbkdf2.pbkdf2HmacSha256 _ x 1 _) ?_) hp
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [X_of hL h1 hk, Whole.chunk_bytesAt _ _ (blk_le' hL hk)]

end

/-! ## The whole function -/

theorem sub36 (x : BitVec 32) : x - BitVec.ofNat 32 (4 * 9) = x - BitVec.ofNat 32 116 + BitVec.ofNat 32 80 := by
  rw [Offset.sub_ofNat_eq x (show 4 * 9 ≤ 116 by omega)]

theorem push_ctx {s : State} (h : Proof.Scrypt.scryptX86.pre s) :
    Ctx (lay s) s.gpr s.mem (pushed pushRs s) := by
  have h116 := h.1
  have h56 := h.2.1
  have hn : 4 * pushRs.length ≤ (s.gpr .esp).toNat := by show 4 * 9 ≤ _; omega
  have hL := lay_ok h
  have hnB := hL.nB
  have hf := pushed_frame (s := s) (rs := pushRs) (by decide) hn
  have hfr : below (s.gpr .esp) (4 * pushRs.length) = (lay s).FR := by
    show (⟨(s.gpr .esp - BitVec.ofNat 32 (4 * 9)).setWidth 64, 36⟩ : Region) = _
    rw [sub36, show s.gpr .esp - BitVec.ofNat 32 116 = (lay s).B from rfl, addr_B (by omega)]
  rw [hfr] at hf
  have ha : ∀ i, i < 13 → (pushed pushRs s).mem.readW ((lay s).A + BitVec.ofNat 64 (120 + 4 * i)) 32 =
      arg s i := fun i hi => by
    have e : (lay s).A + BitVec.ofNat 64 (120 + 4 * i) = argAddr s i := by
      rw [Lay.A, ← addr_B (by rw [lay_B h116]; omega), argAddr]
      congr 1
      rw [show 120 + 4 * i = 116 + (4 + 4 * i) by omega, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc]
      simp only [lay]; rw [BitVec.sub_add_cancel]
    rw [arg, ← e]
    refine hf.readW (r := ⟨(lay s).A + BitVec.ofNat 64 (120 + 4 * i), 4⟩) (Region.contains_self _ _)
      (fun R hR => ?_) (by decide)
    simp only [List.mem_singleton] at hR; subst hR
    exact Offset.disjoint _ (by omega) (by omega) (by omega)
  refine ⟨by rw [pushed_rd, h.2.2.1]; rfl, ?_, ?_, fun r _ hr => pushed_gpr _ _ hr,
    ⟨ha 0 (by omega), ha 1 (by omega), ha 2 (by omega), ha 3 (by omega), ha 4 (by omega), ha 5 (by omega),
      ha 6 (by omega), ha 7 (by omega), ha 8 (by omega), ha 9 (by omega), ha 11 (by omega),
      ha 12 (by omega)⟩, ?_⟩
  · rw [pushed_wr, hfr, h.2.2.2.1, ← lay_args h116 h56]; rfl
  · rw [pushed_esp]; show s.gpr .esp - BitVec.ofNat 32 (4 * 9) = _; rw [sub36]; rfl
  · refine Frame.sub hf fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(lay s).STK, by simp, Offset.sub_base _ (by omega)⟩

theorem ne_cs {r d : Reg} (hr : r ∈ calleeSaved) (hd : d ∉ calleeSaved) : r ≠ d :=
  fun e => hd (e ▸ hr)

theorem pop_esp (B : BitVec 32) : B + BitVec.ofNat 32 80 + BitVec.ofNat 32 (4 * 9) = B + BitVec.ofNat 32 116 := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

section
variable {pbk : Prog isa} (hv : Verified X86.target pbk (Spec.Hmac.sha256I.pbkdf2Contract X86.abi 76))
  (hsp : NoSp pbk) (hst : stackUse pbk ≤ 76) (name : String)
include hv hsp hst

omit hv hst in
theorem body_nosp : NoSp (scryptBody name pbk) := by
  have hb : ∀ is : List Instr, is.all (fun i => !Taint.clobbers i .esp) = true →
      ∀ i ∈ is, Taint.clobbers i .esp = false := fun is h i hi => by
    simpa using List.all_eq_true.mp h i hi
  intro i hi
  replace hi : i ∈ (pbk1Args ++ VG.instrs pbk) ++ (cur0 ++ ((romixArgs ++
      (VG.instrs Impl.Scrypt.X86.roMix ++ nextBlock)) ++ (pbk2Args ++ VG.instrs pbk))) := hi
  simp only [List.mem_append, or_assoc] at hi
  rcases hi with h | h | h | h | h | h | h | h
  · exact hb _ (by decide) i h
  · exact hsp i h
  · exact hb _ (by decide) i h
  · exact hb _ (by decide) i h
  · exact roMix_nosp i h
  · exact hb _ (by decide) i h
  · exact hb _ (by decide) i h
  · exact hsp i h

/-- `vg_scrypt` meets `scryptX86` and the calling convention. -/
theorem scrypt_ok {s : State} (h : Proof.Scrypt.scryptX86.pre s) :
    ∃ t s', Exec isa (scrypt name pbk) s t s' ∧ abiPreserved s s' ∧ Proof.Scrypt.scryptX86.post s s' := by
  have hL := lay_ok h
  have hc := push_ctx h
  have hnB := hL.nB
  refine WP.frame (rs := pushRs) (r := .eax) (by decide) (by decide) (by decide)
    (by show 4 * 9 ≤ _; have := h.1; omega) (body_nosp hsp name)
    (WP.mono (body_scrypt_ok hv hsp hst name hL hc) fun u ⟨hu, ho⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩)
  · by_cases hr' : r = .esp
    · subst hr'
      rw [popped_esp, hu.esp, show pushRs.length = 9 from rfl, pop_esp, lay_esp]
    · rw [popped_gpr _ _ _ hr' (ne_cs hr (by decide)), hu.cs r hr hr']
  · rw [popped_mem]
    refine hu.frame.readW (r := (lay s).RET) ?_ ?_ (by decide)
    · rw [Lay.RET, lay_ret h.1 h.2.1]; exact Region.contains_self _ _
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl | rfl)
      exacts [hL.rb, hL.rv, hL.rc, hL.ro, Offset.disjoint_base _ (by omega) (by omega)]
  · simp only [Proof.Scrypt.scryptX86, popped_mem]
    exact ho

end

end VG.Proof.Scrypt.X86.Whole

end

section

/-!
# scrypt on x86 (32-bit): constant time, up to the indices `j`

As on x86-64 (`Proof/Scrypt/X86_64/Whole/CT.lean`): two runs whose public data
agree have the same layout, so between the frame's push and pop they are
related by `Two`: both satisfy `Ctx` with that layout (and `Φ`, what the next
piece needs), whatever their secrets, and the indices of all the scryptROMix
calls agree (`LeakEq`, from the contract's leakage). The blocks address only
the stack, from `esp` (the taint analysis); each call is of constant-time code
whose public data agree (`RelCT.call`): for PBKDF2 its arguments, for
scryptROMix also the indices of its block, which `LeakEq` gives (`leak_X`);
the loop's branch agrees since both runs count the same blocks.
-/

namespace VG.Proof.Scrypt.X86.Whole

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (bytesAt roMixIndices)

/-- The indices of every scryptROMix agree in two runs from `m₁` and `m₂`. -/
def LeakEq (L : Lay) (m₁ m₂ : Mem) : Prop :=
  (Spec.Scrypt.blocks (bytesAt m₁ (L.pw.setWidth 64) L.pwl.toNat) (bytesAt m₁ (L.salt.setWidth 64) L.sl.toNat)
      L.r.toNat L.pp).flatMap (roMixIndices L.r.toNat L.NN) =
    (Spec.Scrypt.blocks (bytesAt m₂ (L.pw.setWidth 64) L.pwl.toNat) (bytesAt m₂ (L.salt.setWidth 64) L.sl.toNat)
      L.r.toNat L.pp).flatMap (roMixIndices L.r.toNat L.NN)

theorem leak_X {L : Lay} {m₁ m₂ : Mem} (h : LeakEq L m₁ m₂) {k : Nat} (hk : k < L.pp) :
    roMixIndices L.r.toNat L.NN (X L m₁ k) = roMixIndices L.r.toNat L.NN (X L m₂ k) := by
  have h₁ : k < (Spec.Scrypt.blocks (bytesAt m₁ (L.pw.setWidth 64) L.pwl.toNat)
      (bytesAt m₁ (L.salt.setWidth 64) L.sl.toNat) L.r.toNat L.pp).length := by
    rw [Whole.blocks_length]; exact hk
  have h₂ : k < (Spec.Scrypt.blocks (bytesAt m₂ (L.pw.setWidth 64) L.pwl.toNat)
      (bytesAt m₂ (L.salt.setWidth 64) L.sl.toNat) L.r.toNat L.pp).length := by
    rw [Whole.blocks_length]; exact hk
  simp only [X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂,
    Option.getD_some]
  exact Whole.indices_eq h h₁ h₂

/-- What each of two runs has, between the frame's push and pop. -/
abbrev Env := Lay × (Reg → BitVec 32) × (Reg → BitVec 32) × Mem × Mem

/-- Two runs with the same layout, each satisfying `Ctx` and `Φ`. -/
def Two (Φ : Lay → Mem → State → Prop) (a b : State) : Prop :=
  ∃ e : Env, e.1.Ok ∧ LeakEq e.1 e.2.2.2.1 e.2.2.2.2 ∧ Ctx e.1 e.2.1 e.2.2.2.1 a ∧
    Ctx e.1 e.2.2.1 e.2.2.2.2 b ∧ Φ e.1 e.2.2.2.1 a ∧ Φ e.1 e.2.2.2.2 b

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Lay → Mem → State → Prop}
    (hct : RelCT isa (Two Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → Ctx L g m₀ t → Φ L m₀ t →
      WP isa c t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) c (Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨⟨L, g₁, g₂, m₁, m₂⟩, hL, hk, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ m₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ m₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, ⟨L, g₁, g₂, m₁, m₂⟩, hL, hk, y₁.1, y₂.1, y₁.2, y₂.2⟩

theorem esp_two {L : Lay} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) : t₁.gpr .esp = t₂.gpr .esp :=
  c₁.esp.trans c₂.esp.symm

/-- A block whose addresses depend only on `esp`, with what it establishes. -/
theorem two_blk {is : List Instr} {Φ Ψ : Lay → Mem → State → Prop}
    (h : ∃ hc, (VG.Taint.check taint (τr [.esp]) (.block is) hc).isSome = true)
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → Ctx L g m₀ t → Φ L m₀ t →
      WP isa (.block is) t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) (.block is) (Two Ψ) := by
  obtain ⟨_, h⟩ := h
  exact two_wp (RelCT.taint (A := taint) (τr [.esp])
    (fun _ _ ⟨_, _, _, c₁, c₂, _, _⟩ => agree_regs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact esp_two c₁ c₂) h) hw

/-- A call of verified code, with the same regions in both runs, after which
`Ψ` holds. -/
theorem two_call {n : String} {c : Prog isa} {k : Contract isa} {Φ Ψ : Lay → Mem → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g m₀ (t : State), L.Ok → Ctx L g m₀ t → Φ L m₀ t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ (L : Lay) t₁ t₂ g₁ g₂ m₁ m₂, L.Ok → LeakEq L m₁ m₂ → Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ →
      Φ L m₁ t₁ → Φ L m₂ t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (hsub : ∀ (L : Lay) m₀ (t : State), L.Ok → Φ L m₀ t → ∀ r ∈ rd L ++ wr L, ∃ R ∈ L.regions, Within r R)
    (hwsub : ∀ (L : Lay) m₀ (t : State), L.Ok → Φ L m₀ t → ∀ r ∈ wr L, InBuf L r ∨ Within r L.FR)
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → Ctx L g m₀ t → Φ L m₀ t →
      WP isa (.call n c) t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) (.call n c) (Two Ψ) :=
  two_wp (RelCT.exists_ fun (e : Env) => RelCT.call hv hct (rd e.1) (wr e.1) (P := fun a b => e.1.Ok ∧
    LeakEq e.1 e.2.2.2.1 e.2.2.2.2 ∧ Ctx e.1 e.2.1 e.2.2.2.1 a ∧ Ctx e.1 e.2.2.1 e.2.2.2.2 b ∧
    Φ e.1 e.2.2.2.1 a ∧ Φ e.1 e.2.2.2.2 b) fun _ _ ⟨hL, hk, c₁, c₂, f₁, f₂⟩ =>
    ⟨hpre _ _ _ _ hL c₁ f₁, hpre _ _ _ _ hL c₂ f₂,
      hpub _ _ _ _ _ _ _ hL hk c₁ c₂ f₁ f₂, (covers c₁ (hsub _ _ _ hL f₁) (hwsub _ _ _ hL f₁)).1,
      (covers c₁ (hsub _ _ _ hL f₁) (hwsub _ _ _ hL f₁)).2,
      (covers c₂ (hsub _ _ _ hL f₂) (hwsub _ _ _ hL f₂)).1,
      (covers c₂ (hsub _ _ _ hL f₂) (hwsub _ _ _ hL f₂)).2, esp_two c₁ c₂⟩) hw

/-! ## The calls -/

theorem pbk_pub_two {L : Lay} (hL : L.Ok) {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem} {t₁ t₂ : State}
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) {salt sl out ol : BitVec 32}
    (a₁ : PbkArgs L salt sl out ol t₁.mem) (a₂ : PbkArgs L salt sl out ol t₂.mem) :
    pbkK.pub (t₁.callEntry.withRegions (pbkRd L salt sl) (pbkWr L out ol))
      (t₂.callEntry.withRegions (pbkRd L salt sl) (pbkWr L out ol)) := by
  refine ⟨by rw [c₁.ce_esp, c₂.ce_esp], fun i hi => ?_⟩
  rw [c₁.ce_arg hL _ _ i (by omega), c₂.ce_arg hL _ _ i (by omega)]
  match i, hi with
  | 0, _ => exact a₁.a0.trans a₂.a0.symm
  | 1, _ => exact a₁.a1.trans a₂.a1.symm
  | 2, _ => exact a₁.a2.trans a₂.a2.symm
  | 3, _ => exact a₁.a3.trans a₂.a3.symm
  | 4, _ => exact a₁.a4.trans a₂.a4.symm
  | 5, _ => exact a₁.a5.trans a₂.a5.symm
  | 6, _ => exact a₁.a6.trans a₂.a6.symm
  | 7, _ => exact a₁.a7.trans a₂.a7.symm

/-- The block ROMix works on in iteration `i`, on entry to it. -/
theorem romix_bytes {L : Lay} (hL : L.Ok) {g : Reg → BitVec 32} {m₀ : Mem} {t : State}
    (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.pp) (hb : ∀ k < L.pp, bytesAt t.mem (blk L k) (128 * L.r.toNat) =
      if k < i then Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) else X L m₀ k) (rd wr : List Region) :
    bytesAt (t.callEntry.withRegions rd wr).mem (blk L i) (128 * L.r.toNat) = X L m₀ i := by
  rw [hc.ce_bytesAt hL _ _ (hL.stk_in (by omega) (by simpa [Nat.mul_comm] using blk_in hL hi)).symm
    (by have := hL.blen_lt; have := blk_le hL hi; omega), hb i hi]
  simp only [Nat.lt_irrefl, ite_false]

theorem romix_pub_two {L : Lay} (hL : L.Ok) {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem} {t₁ t₂ : State}
    (hk : LeakEq L m₁ m₂) (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) {i : Nat} (hi : i < L.pp)
    (b₁ : InvB L m₁ i t₁) (b₂ : InvB L m₂ i t₂) (a₁ : RomixArgs L (cur L i) t₁.mem)
    (a₂ : RomixArgs L (cur L i) t₂.mem) :
    Proof.Scrypt.roMixX86.pub (t₁.callEntry.withRegions (romixRd L) (romixWr L i))
      (t₂.callEntry.withRegions (romixRd L) (romixWr L i)) := by
  refine ⟨by rw [c₁.ce_esp, c₂.ce_esp], fun j hj => ?_, ?_⟩
  · rw [c₁.ce_arg hL _ _ j (by omega), c₂.ce_arg hL _ _ j (by omega)]
    match j, hj with
    | 0, _ => exact a₁.a0.trans a₂.a0.symm
    | 1, _ => exact a₁.a1.trans a₂.a1.symm
    | 2, _ => exact a₁.a2.trans a₂.a2.symm
    | 3, _ => exact a₁.a3.trans a₂.a3.symm
    | 4, _ => exact a₁.a4.trans a₂.a4.symm
    | 5, _ => exact a₁.a5.trans a₂.a5.symm
  · have a := c₁.ce_arg hL (romixRd L) (romixWr L i)
    have a' := c₂.ce_arg hL (romixRd L) (romixWr L i)
    simp only [a 0 (by omega), a 1 (by omega), a 3 (by omega), a' 0 (by omega), a' 1 (by omega),
      a' 3 (by omega), Nat.reduceMul, Nat.reduceAdd, a₁.a0, a₁.a1, a₁.a3, a₂.a0, a₂.a1, a₂.a3, cur_eq hL hi,
      romix_bytes hL c₁ hi b₁.blks, romix_bytes hL c₂ hi b₂.blks]
    exact leak_X hk hi

/-! ## The pieces -/

/-- Iteration `pp - n` of the loop is next. -/
abbrev LoopAt (n : Nat) (L : Lay) (m₀ : Mem) (t : State) : Prop :=
  0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n) t

theorem body_ct (n : Nat) :
    RelCT isa (Two (LoopAt n)) (.seq (.block romixArgs) (.seq (.call "vg_scrypt_romix"
      Impl.Scrypt.X86.roMix) (.block nextBlock)))
      (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n + 1) t ∧
        t.zf = some (decide (L.pp - n + 1 = L.pp))) := by
  have a : RelCT isa (Two (LoopAt n)) (.block romixArgs) (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧
      InvB L m₀ (L.pp - n) t ∧ RomixArgs L (cur L (L.pp - n)) t.mem) :=
    two_blk ⟨_, by taint_decide⟩ fun _ _ _ _ hL hc ⟨h0, hn, hb⟩ =>
      romixArgs_ok hL hc hb.cur fun _ hc' hf ha hcur => ⟨hc', h0, hn,
        ⟨hcur, fun k hk => by rw [blk_fr hL hk hf]; exact hb.blks k hk⟩, ha⟩
  have b : RelCT isa (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n) t ∧
      RomixArgs L (cur L (L.pp - n)) t.mem) (.call "vg_scrypt_romix" Impl.Scrypt.X86.roMix)
      (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ Mid L m₀ (L.pp - n) t) :=
    two_call RoMix.roMix_correct RoMix.roMix_ct (fun L => romixRd L) (fun L => romixWr L (L.pp - n))
      (fun _ _ _ _ hL hc ⟨h0, hn, _, ha⟩ => romix_pre hL hc (by omega) ha)
      (fun _ _ _ _ _ _ _ hL hk c₁ c₂ ⟨h0, hn, b₁, a₁⟩ ⟨_, _, b₂, a₂⟩ =>
        romix_pub_two hL hk c₁ c₂ (by omega) b₁ b₂ a₁ a₂)
      (fun _ _ _ hL ⟨h0, hn, _⟩ => romix_sub hL (by omega))
      (fun _ _ _ hL ⟨h0, hn, _⟩ => romix_wsub hL (by omega))
      (fun _ _ _ _ hL hc ⟨h0, hn, hb, ha⟩ =>
        WP.mono (call_step hL (by omega) hc hb ha) fun _ ⟨hc', hm⟩ => ⟨hc', h0, hn, hm⟩)
  have c : RelCT isa (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ Mid L m₀ (L.pp - n) t) (.block nextBlock)
      (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n + 1) t ∧
        t.zf = some (decide (L.pp - n + 1 = L.pp))) :=
    two_blk ⟨_, by taint_decide⟩ fun _ _ _ _ hL hc ⟨h0, hn, hm⟩ =>
      nextBlock_ok hL hc hm.cur fun _ hc' hf hb hz => ⟨hc', h0, hn,
        ⟨by rw [hb, next_eq], fun k hk => by rw [blk_fr hL hk hf]; exact hm.blks k hk⟩,
        by rw [hz, next_eq, zf_eq hL (by omega)]⟩
  exact a.seq (b.seq c)

theorem loop_ct :
    RelCT isa (Two fun L m₀ t => InvB L m₀ 0 t) romixLoop (Two fun L m₀ t => InvB L m₀ L.pp t) := by
  have ev : ∀ x : State, isa.eval .ne x = x.zf.map (!·) := fun _ => rfl
  have h := fun n => RelCT.loop (M := isa) (c := .ne) (Q := Two fun L m₀ t => InvB L m₀ L.pp t)
    (fun n => Two (LoopAt n)) (fun n => (body_ct n).mono (fun _ _ h => h) fun a b hab => by
      obtain ⟨e, hL, hk, c₁, c₂, ⟨h0, hn, b₁, z₁⟩, ⟨-, -, b₂, z₂⟩⟩ := hab
      rw [ev, ev, z₁, z₂]
      refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
      · have hl : e.1.pp - n + 1 = e.1.pp := by simpa using hf
        exact ⟨e, hL, hk, c₁, c₂, show InvB e.1 _ e.1.pp a from hl ▸ b₁,
          show InvB e.1 _ e.1.pp b from hl ▸ b₂⟩
      · have hl : e.1.pp - n + 1 ≠ e.1.pp := by simpa using ht
        have e₁ : e.1.pp - (n - 1) = e.1.pp - n + 1 := by omega
        exact ⟨n - 1, by omega, e, hL, hk, c₁, c₂, ⟨by omega, by omega, e₁ ▸ b₁⟩,
          ⟨by omega, by omega, e₁ ▸ b₂⟩⟩) n
  refine (RelCT.exists_ h).mono (fun a b ⟨e, hL, hk, c₁, c₂, b₁, b₂⟩ => ⟨e.1.pp, e, hL, hk, c₁, c₂,
    ⟨hL.pp_pos, Nat.le_refl _, by rw [Nat.sub_self]; exact b₁⟩,
    ⟨hL.pp_pos, Nat.le_refl _, by rw [Nat.sub_self]; exact b₂⟩⟩) fun _ _ h => h

/-! ## The whole function -/

section
variable {pbk : Prog isa} (hv : Verified X86.target pbk (Spec.Hmac.sha256I.pbkdf2Contract X86.abi 76))
  (hsp : NoSp pbk) (hst : stackUse pbk ≤ 76) (name : String)
include hv hsp hst

theorem scryptBody_ct : RelCT isa (Two fun _ _ _ => True) (scryptBody name pbk) fun _ _ => True := by
  have p1a : RelCT isa (Two fun _ _ _ => True) (.block pbk1Args)
      (Two fun L _ t => PbkArgs L L.salt L.sl L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) t.mem) :=
    two_blk ⟨_, by taint_decide⟩ fun _ _ _ _ hL hc _ => pbk1Args_ok hL hc fun _ hc' _ ha => ⟨hc', ha⟩
  have p1c : RelCT isa (Two fun L _ t => PbkArgs L L.salt L.sl L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) t.mem)
      (.call name pbk) (Two fun L m₀ t => Step1 L m₀ (bytesAt t.mem (L.b.setWidth 64) (L.blen.toNat * 128))) :=
    two_call (pbk_correct hv) (pbk_ct hv) (fun L => pbkRd L L.salt L.sl)
      (fun L => pbkWr L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)))
      (fun _ _ _ _ hL hc ha => pbk_pre' hL hc ha (pbk1_regions hL))
      (fun _ _ _ _ _ _ _ hL _ c₁ c₂ a₁ a₂ => pbk_pub_two hL c₁ c₂ a₁ a₂)
      (fun _ _ _ hL _ => pbk_sub hL (pbk1_regions hL)) (fun _ _ _ hL _ => pbk_wsub hL (pbk1_regions hL).ow)
      (fun _ _ _ _ hL hc ha => WP.mono (pbk_call hv hsp hst name hL hc ha (pbk1_regions hL))
        fun _ ⟨hc', _, hp⟩ => ⟨hc', by rw [toNat_blen hL, hc.pw_bytes hL, hc.salt_bytes hL] at hp; exact hp⟩)
  have c0 : RelCT isa (Two fun L m₀ t => Step1 L m₀ (bytesAt t.mem (L.b.setWidth 64) (L.blen.toNat * 128)))
      (.block cur0) (Two fun L m₀ t => InvB L m₀ 0 t) :=
    two_blk ⟨_, by taint_decide⟩ fun _ _ _ _ hL hc h1 => start_ok hL hc h1
  have p2a : RelCT isa (Two fun L m₀ t => InvB L m₀ L.pp t) (.block pbk2Args)
      (Two fun L _ t => PbkArgs L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) L.out L.ol t.mem) :=
    two_blk ⟨_, by taint_decide⟩ fun _ _ _ _ hL hc _ => pbk2Args_ok hL hc fun _ hc' _ ha => ⟨hc', ha⟩
  have p2c : RelCT isa (Two fun L _ t => PbkArgs L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) L.out L.ol t.mem)
      (.call name pbk) (Two fun _ _ _ => True) :=
    two_call (pbk_correct hv) (pbk_ct hv) (fun L => pbkRd L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)))
      (fun L => pbkWr L L.out L.ol)
      (fun _ _ _ _ hL hc ha => pbk_pre' hL hc ha (pbk2_regions hL))
      (fun _ _ _ _ _ _ _ hL _ c₁ c₂ a₁ a₂ => pbk_pub_two hL c₁ c₂ a₁ a₂)
      (fun _ _ _ hL _ => pbk_sub hL (pbk2_regions hL)) (fun _ _ _ hL _ => pbk_wsub hL (pbk2_regions hL).ow)
      (fun _ _ _ _ hL hc ha =>
        WP.mono (pbk_call hv hsp hst name hL hc ha (pbk2_regions hL)) fun _ h => ⟨h.1, trivial⟩)
  exact ((p1a.seq p1c).seq (c0.seq (loop_ct.seq (p2a.seq p2c)))).mono (fun _ _ h => h)
    fun _ _ _ => trivial

theorem scrypt_ct :
    ConstantTime isa Proof.Scrypt.scryptX86.pre Proof.Scrypt.scryptX86.pub (scrypt name pbk) := by
  refine RelCT.constantTime (RelCT.frame (fun _ _ h => h.2.2.1)
    (RelCT.mono (scryptBody_ct hv hsp hst name) ?_ fun _ _ _ => trivial))
  rintro _ _ ⟨s₁, s₂, ⟨h₁, h₂, hsp', ha, hlk⟩, rfl, rfl⟩
  have e : lay s₂ = lay s₁ := by
    simp only [lay, ← ha 0 (by omega), ← ha 1 (by omega), ← ha 2 (by omega), ← ha 3 (by omega),
      ← ha 4 (by omega), ← ha 5 (by omega), ← ha 6 (by omega), ← ha 7 (by omega), ← ha 8 (by omega),
      ← ha 9 (by omega), ← ha 10 (by omega), ← ha 11 (by omega), ← ha 12 (by omega), hsp']
  refine ⟨⟨lay s₁, s₁.gpr, s₂.gpr, s₁.mem, s₂.mem⟩, lay_ok h₁, ?_, push_ctx h₁, e ▸ push_ctx h₂,
    trivial, trivial⟩
  rw [← ha 0 (by omega), ← ha 1 (by omega), ← ha 2 (by omega), ← ha 3 (by omega), ← ha 4 (by omega),
    ← ha 6 (by omega), ← ha 8 (by omega)] at hlk
  exact hlk

end

end VG.Proof.Scrypt.X86.Whole

end

/-!
# scrypt on x86 (32-bit): the shared contract

`vg_scrypt`, calling any implementation of PBKDF2-HMAC-SHA256 verified against
its shared contract that never writes `esp` and uses at most 76 bytes of
stack, is verified against `Spec.Scrypt.scryptContract` for the 116 bytes of
stack its frame and calls use (`scrypt_verified_of`); and so is the one
calling the `vg_pbkdf2_hmac_sha256` made with any SHA-256 backend
(`scrypt_verified`), whose code never writes `esp` but by the frame
(`scrypt_spSafe`).
-/

namespace VG.Proof.Scrypt.X86.Whole

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Proof.Pbkdf2.Whole.X86 (argVal32 setWidth32_64 toNat_setWidth64 setWidth_inj32)
open VG.Proof.Sha256.X86.Variants (Backend)

/-- Memory holding the arguments `0x1000, 0, 0x1100, 0, 1, 0x3000, 1, 0x4000, 2, 0x5000, 17, 0x6000, 1`
at `0x8004`. -/
def satMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x800D then 0x11 else if a = 0x8014 then 1 else
  if a = 0x8019 then 0x30 else if a = 0x801C then 1 else if a = 0x8021 then 0x40 else
  if a = 0x8024 then 2 else if a = 0x8029 then 0x50 else if a = 0x802C then 17 else
  if a = 0x8031 then 0x60 else if a = 0x8034 then 1 else 0

/-- A state satisfying the precondition: `N = 2`, `r = 1`, `p = 1`, a
one-byte key and an empty password and salt. -/
def satState : State where
  gpr r := match r with
    | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x1000, 0⟩, ⟨0x1100, 0⟩]
  wr := [⟨0x3000, 128⟩, ⟨0x4000, 256⟩, ⟨0x5000, 2176⟩, ⟨0x6000, 1⟩, ⟨0x8004, 52⟩]

theorem scrypt_implies : Proof.Scrypt.scryptX86.Implies (Spec.Scrypt.scryptContract X86.abi 116) := by
  exact
    { pre := by
        intro s h
        sig_pre [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86, X86.abi] at h
        simp only [argVal32, setWidth32_64, toNat_setWidth64,
          show argBytes [32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32] = 52 from rfl] at h
        sig_split h
        sig_reduce [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86, X86.abi]
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | with_reducible exact Region.Disjoint.symm ‹_›
      post := by
        rintro s s' - h
        sig_post [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86, X86.abi]
        simp only [argVal32, setWidth32_64]
        exact h
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86, X86.abi] at h
        simp only [argVal32] at h
        obtain ⟨e, hlk, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
        refine ⟨e, fun i hi => ?_, ?_⟩
        · match i, hi with
          | 0, _ => exact setWidth_inj32 a0
          | 1, _ => exact setWidth_inj32 a1
          | 2, _ => exact setWidth_inj32 a2
          | 3, _ => exact setWidth_inj32 a3
          | 4, _ => exact setWidth_inj32 a4
          | 5, _ => exact setWidth_inj32 a5
          | 6, _ => exact setWidth_inj32 a6
          | 7, _ => exact setWidth_inj32 a7
          | 8, _ => exact setWidth_inj32 a8
          | 9, _ => exact setWidth_inj32 a9
          | 10, _ => exact setWidth_inj32 a10
          | 11, _ => exact setWidth_inj32 a11
          | 12, _ => exact setWidth_inj32 a12
        · simpa only [setWidth32_64, List.flatMap_def] using hlk
      sat := by
        sig_implies_sat [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, X86.abi, X86.argSlots,
          X86.argVal, X86.argBytes] [satState, satMem] using satState }

section
variable {pbk : Prog isa} (hv : Verified X86.target pbk (Spec.Hmac.sha256I.pbkdf2Contract X86.abi 76))
  (hsp : NoSp pbk) (hst : stackUse pbk ≤ 76) (name : String)
include hv hsp hst

/-- `vg_scrypt`, calling the implementation `pbk` of PBKDF2 named `name`. -/
theorem scrypt_verified_of :
    Verified X86.target (scrypt name pbk) (Spec.Scrypt.scryptContract X86.abi 116) :=
  Verified.of_correct (fun _ h => scrypt_ok hv hsp hst name h) (scrypt_ct hv hsp hst name) scrypt_implies

end

/-! ## With the PBKDF2 made with a SHA-256 backend -/

theorem clobbers_esp (i : Instr) : Taint.clobbers i .esp = isa.writesSp i := by
  cases i <;> rfl

theorem all_eq (p : Instr → Bool) (c : Prog isa) : c.all p = (VG.instrs c).all p := by
  induction c <;> simp_all [Code.all, VG.instrs, List.all_append, Bool.and_assoc]

/-- Code whose instructions never write `esp`, but by its frames, keeps it. -/
theorem nosp_of_all {c : Prog isa} (h : c.all (fun i => !isa.writesSp i) = true) : NoSp c := by
  intro i hi
  rw [all_eq, List.all_eq_true] at h
  rw [clobbers_esp]
  simpa using h i hi

variable (v : Backend)

/-- PBKDF2-HMAC-SHA256 made with `v`. -/
abbrev pbkOf : Prog isa := v.F.pbkdf2

/-- Its name. -/
abbrev pbkName : String := Spec.Hmac.sha256I.pbkdf2Api.name ++ v.suffix

theorem pbk_stack : stackUse (pbkOf v) ≤ 76 := by
  have := v.stream.updSU; have := v.stream.finSU; have := v.initStack; have := v.finalizeStack; have := v.iterStack
  have hi : stackUse Impl.Sha256.X86.Stream.init ≤ 20 := by lit_decide
  simp only [pbkOf, Impl.Pbkdf2.Whole.X86.Fns.pbkdf2, Impl.Pbkdf2.Whole.X86.Fns.key,
    Impl.Pbkdf2.Whole.X86.Fns.hashKey, Impl.Pbkdf2.Whole.X86.Fns.setup, Impl.Pbkdf2.Whole.X86.Fns.block,
    Impl.Pbkdf2.Whole.X86.Fns.outLen, Impl.Pbkdf2.Whole.X86.Fns.outLoop, Impl.Pbkdf2.Stream.X86.copy,
    Impl.Pbkdf2.Stream.X86.Hash.callInit, Backend.F, Proof.Sha256.X86.Variants.pbkdf2Fns,
    Proof.Sha256.X86.Variants.fns, Proof.Sha256.X86.Variants.hmacHash, Proof.Pbkdf2.Md.X86.sha256M,
    stackUse, frameBytes, List.length_cons, List.length_nil, Nat.max_le] at *
  omega

/-- `vg_scrypt` made with `v`. -/
theorem scrypt_verified :
    Verified X86.target (scrypt (pbkName v) (pbkOf v)) (Spec.Scrypt.scryptContract X86.abi 116) :=
  scrypt_verified_of (Proof.Pbkdf2.Whole.X86.sha256_verified v) (nosp_of_all v.pbkdf2Sp) (pbk_stack v) _

/-- No instruction writes `esp` but the frame's push and pop. -/
theorem scrypt_spSafe : (scrypt (pbkName v) (pbkOf v)).all (fun i => !isa.writesSp i) = true := by
  have hr : Impl.Scrypt.X86.roMix.all (fun i => !isa.writesSp i) = true :=
    Code.all_of_allInstrs (by lit_decide)
  simp only [pbkOf, scrypt, scryptBody, pbkCall, romixLoop, Code.all, v.pbkdf2Sp, hr, Bool.and_true,
    Bool.true_and]
  decide

end VG.Proof.Scrypt.X86.Whole
