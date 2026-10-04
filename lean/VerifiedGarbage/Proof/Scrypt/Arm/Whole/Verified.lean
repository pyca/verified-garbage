import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha256
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Scrypt.Arm.Whole.Calls

section

section

/-!
# scrypt on 32-bit ARM: correctness

As on the other targets (`Proof/Scrypt/AArch64/Whole/Correct.lean`): our
caller's registers are saved (`entry_ok`); step 1 leaves the blocks `X k` of
`PBKDF2-HMAC-SHA256 (P, S, 1, 128 blen)` in `b` (`step1_ok`); the loop
replaces them by their scryptROMix one at a time (`Inv`, `loop_ok`); step 3
derives the key from them (`step3_ok`); our caller's registers are restored
(`scrypt_ok`).
-/

namespace VG.Proof.Scrypt.Arm.Whole

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Arm.FrameStack
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt toNat_add_ofNat)
open VG.Spec.Scrypt (bytesAt)

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem}

theorem t32 {x : Nat} (h : x < 2 ^ 32) : (BitVec.ofNat 32 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-! ## The password, the salt and the blocks -/

namespace Ctx

variable {t : State} (hc : Ctx L g m₀ t) (hL : L.Ok)
include hc hL

theorem pw_bytes : bytesAt t.mem (State.addr L.pw) L.pwl.toNat = bytesAt m₀ (State.addr L.pw) L.pwl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.pb, hL.pv, hL.pc, hL.po, hL.kp.symm]) (by have := L.pwl.isLt; omega)

theorem salt_bytes : bytesAt t.mem (State.addr L.salt) L.sl.toNat = bytesAt m₀ (State.addr L.salt) L.sl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.sb, hL.sv, hL.sc, hL.so, hL.ks.symm]) (by have := L.sl.isLt; omega)

end Ctx

/-- Block `k` of step 1. -/
def X (L : Lay) (m₀ : Mem) (k : Nat) : List Byte :=
  (Spec.Scrypt.blocks (bytesAt m₀ (State.addr L.pw) L.pwl.toNat) (bytesAt m₀ (State.addr L.salt) L.sl.toNat)
    L.r.toNat L.pp).getD k []

/-- The derived key of step 1, from the password and the salt on entry. -/
abbrev Step1 (L : Lay) (m₀ : Mem) (B : List Byte) : Prop :=
  Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ (State.addr L.pw) L.pwl.toNat)
    (bytesAt m₀ (State.addr L.salt) L.sl.toNat) 1 (L.blen.toNat * 128) = some B

theorem X_of (hL : L.Ok) {m : Mem} (h : Step1 L m₀ (bytesAt m (State.addr L.b) (L.blen.toNat * 128))) {k : Nat}
    (hk : k < L.pp) : X L m₀ k = bytesAt m (blkA L k) (128 * L.r.toNat) := by
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have h' : Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ (State.addr L.pw) L.pwl.toNat)
      (bytesAt m₀ (State.addr L.salt) L.sl.toNat) 1 (L.pp * 128 * L.r.toNat) =
      some (bytesAt m (State.addr L.b) (L.pp * 128 * L.r.toNat)) := by rw [e]; exact h
  have hl : k < (Spec.Scrypt.blocks (bytesAt m₀ (State.addr L.pw) L.pwl.toNat)
      (bytesAt m₀ (State.addr L.salt) L.sl.toNat) L.r.toNat L.pp).length := by
    rw [Whole.blocks_length]; exact hk
  rw [X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some,
    Whole.blocks_getElem h' hl]

/-- Distinct blocks are disjoint. -/
theorem blk_disj (hL : L.Ok) {k i : Nat} (hk : k < L.pp) (hi : i < L.pp) (hne : k ≠ i) :
    Region.Disjoint ⟨blkA L k, 128 * L.r.toNat⟩ ⟨blkA L i, L.r.toNat * 128⟩ := by
  have h₁ := blk_le hL hk
  have h₂ := blk_le hL hi
  have := hL.blen_lt
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
    Region.Sub ⟨blkA L k, 128 * L.r.toNat⟩ L.BB := by
  have := blk_le hL hk
  exact Offset.sub_base _ (by omega)

theorem blk_le' (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    128 * L.r.toNat * i + 128 * L.r.toNat ≤ L.blen.toNat * 128 := by
  have := blk_le hL hi; rw [Nat.mul_comm L.r.toNat 128] at this; exact this

theorem blk0 (L : Lay) : blkAt L 0 = L.b := by
  simp only [blkAt, Nat.mul_zero]; exact BitVec.add_zero _

/-! ## Entry -/

/-- The state on entry. -/
theorem entry_E {s : State} (h : Proof.Scrypt.scryptArm.pre s) : E (lay s) s.gpr s.mem s := by
  have hL := lay_ok h
  have a : ∀ k, k + 4 ≤ 36 → s.mem.readW (State.addr (lay s).sp + BitVec.ofNat 64 k) 32 =
      s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 k)) 32 := fun k hk => by
    rw [← hL.arg_addr hk]; rfl
  refine ⟨?_, h.2.2.2.1, rfl, fun _ _ _ => rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, Frame.refl _ _, rfl, rfl,
    rfl, rfl⟩
  · rw [h.2.2.1, ← lay_args]; rfl
  all_goals (rw [a _ (by omega)]; rfl)

/-! ## Step 1 -/

section
variable {pbk : Prog isa} (hv : Verified Arm.target pbk (Spec.Hmac.sha256I.pbkdf2Contract Arm.abi 24))
  (hst : armStack pbk ≤ 24) (name : String)
include hv hst

omit hv hst in
theorem scr_sub (hL : L.Ok) : Region.Sub (scr1600 L) L.SC :=
  Within.sub (within_base _ (by have := hL.slen17; omega))

omit hv hst in
theorem pbk1_regions (hL : L.Ok) :
    PbkRegions L L.salt L.sl L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) := by
  have hb := hL.blen_lt
  have e : (BitVec.ofNat 32 (L.blen.toNat * 128)).toNat = L.blen.toNat * 128 := t32 hb
  refine ⟨⟨L.SALT, by simp, within_base _ (Nat.le_refl _)⟩, ?_, ?_, ?_, hL.sc.sub_right (scr_sub hL), ?_,
    hL.ks, hL.ns, ?_, ?_⟩
  · rw [e]; exact .inl (within_base _ (Nat.le_refl _))
  · rw [e]; exact (hL.bc.sub_right hL.sv_sc)
  · rw [e]; exact hL.sb
  · rw [e]; exact hL.bc.sub_right (scr_sub hL)
  · rw [e]; exact hL.nb
  · rw [e]; exact hL.ol1

theorem step1_ok (hL : L.Ok) {t₁ : State} (hc₁ : Ctx L g m₀ t₁) (h4 : t₁.gpr .r4 = L.b)
    (ha₁ : PbkArgs L L.salt L.sl L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) t₁) :
    WP isa (pbkCall name pbk) t₁ fun t' => Ctx L g m₀ t' ∧
      t'.gpr .r4 = L.b ∧ Step1 L m₀ (bytesAt t'.mem (State.addr L.b) (L.blen.toNat * 128)) ∧
      ∀ k < L.pp, bytesAt t'.mem (blkA L k) (128 * L.r.toNat) = X L m₀ k := by
  have hb := hL.blen_lt
  refine WP.mono (pbk_call hv hst name hL hc₁ ha₁ (pbk1_regions hL)) fun t₂ ⟨hc₂, h4₂, _, hp⟩ =>
    ⟨hc₂, h4₂.trans h4, ?_, fun k hk => ?_⟩
  · rw [t32 hb, hc₁.pw_bytes hL, hc₁.salt_bytes hL] at hp
    exact hp
  · rw [t32 hb, hc₁.pw_bytes hL, hc₁.salt_bytes hL] at hp
    exact (X_of hL hp hk).symm

end

/-! ## The loop -/

/-- After `i` iterations of the loop: the next block is `i`, and blocks
`0, …, i - 1` are scryptROMix of those of step 1. -/
structure InvB (L : Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.gpr .r4 = blkAt L i
  blks : ∀ k < L.pp, bytesAt t.mem (blkA L k) (128 * L.r.toNat) =
    if k < i then Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) else X L m₀ k

abbrev Inv (L : Lay) (g : Reg → BitVec 32) (m₀ : Mem) (i : Nat) (t : State) : Prop :=
  Ctx L g m₀ t ∧ InvB L m₀ i t

/-- In iteration `i`, after the call of ROMix: blocks `0, …, i` are scryptROMix
of those of step 1. -/
structure Mid (L : Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.gpr .r4 = blkAt L i
  blks : ∀ k < L.pp, bytesAt t.mem (blkA L k) (128 * L.r.toNat) =
    if k < i + 1 then Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) else X L m₀ k

theorem next_eq (L : Lay) (i : Nat) :
    blkAt L i + BitVec.ofNat 32 (L.r.toNat * 128) = blkAt L (i + 1) := by
  simp only [blkAt]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_succ (128 * L.r.toNat) i, Nat.mul_comm L.r.toNat 128]

theorem z_eq (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    (blkAt L (i + 1) - (L.b + BitVec.ofNat 32 (L.blen.toNat * 128)) == 0) = decide (i + 1 = L.pp) := by
  have h₁ := blk_le hL hi
  have hb := hL.blen_lt
  have hr := hL.rpos
  simp only [blkAt]
  rw [Offset.add_sub_add_left, ← hL.len_b]
  have e₁ : 128 * L.r.toNat * (i + 1) < 2 ^ 32 := by
    rw [Nat.mul_succ]; rw [← hL.len_b] at h₁ hb; omega
  have e₂ : 128 * L.r.toNat * L.pp < 2 ^ 32 := by rw [hL.len_b]; exact hb
  rw [VG.Proof.MdStream.Arm.sub_beq e₁ e₂]
  refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => by rw [h]⟩
  exact Nat.eq_of_mul_eq_mul_left (by omega) h

theorem call_step (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (hc : Ctx L g m₀ t)
    (hb : InvB L m₀ i t) (ha : RomixArgs L (blkAt L i) t) :
    WP isa (.frame (.push [.r12, .lr]) (.call "vg_scrypt_romix" Impl.Scrypt.Arm.roMix) (.pop .r12 8)) t
      fun t' => Ctx L g m₀ t' ∧ Mid L m₀ i t' := by
  refine WP.mono (romix_call hL hc hi ha) fun t₂ ⟨hc₂, h4, hf₂, hr₂⟩ => ⟨hc₂, h4.trans hb.cur, fun k hk => ?_⟩
  by_cases hki : k = i
  · subst hki
    rw [hr₂, hb.blks k hk]
    simp only [Nat.lt_irrefl, ite_false, Nat.lt_succ_self, ite_true]
  · have e₂ : bytesAt t₂.mem (blkA L k) (128 * L.r.toNat) = bytesAt t.mem (blkA L k) (128 * L.r.toNat) :=
      Memory.frame_bytesAt hf₂ (fun r hr => by
        simp only [romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact blk_disj hL hk hi hki
        · exact hL.bv.sub_left (blk_sub hL hk)
        · exact (hL.bc.sub_left (blk_sub hL hk)).sub_right
            (Within.sub (within_base _ (by have := hL.slen; omega)))
        · exact (hL.kb.symm.sub_left (blk_sub hL hk)))
        (by have := hL.blen_lt; have := blk_le hL hk; omega)
    rw [e₂, hb.blks k hk]
    by_cases hlt : k < i
    · have : k < i + 1 := by omega
      simp only [hlt, this, ite_true]
    · have : ¬ k < i + 1 := by omega
      simp only [hlt, this, ite_false]

theorem body_ok (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (h : Inv L g m₀ i t) :
    WP isa (.seq (.block romixArgs) (.seq (.frame (.push [.r12, .lr]) (.call "vg_scrypt_romix"
      Impl.Scrypt.Arm.roMix) (.pop .r12 8)) (.block nextBlock))) t fun t' =>
        Inv L g m₀ (i + 1) t' ∧ t'.z = decide (i + 1 = L.pp) := by
  refine WP.seq (WP.mono (romixArgs_ok hL h.1) fun t₁ ⟨hc₁, hm₁, h4₁, ha₁⟩ => ?_)
  rw [h.2.cur] at ha₁
  refine WP.seq (WP.mono (call_step hL hi hc₁ ⟨h4₁.trans h.2.cur, by rw [hm₁]; exact h.2.blks⟩ ha₁)
    fun t₂ ⟨hc₂, hm₂⟩ => ?_)
  refine WP.mono (nextBlock_ok hc₂) fun t₃ ⟨hc₃, hm₃, h4₃, hz₃⟩ =>
    ⟨⟨hc₃, ⟨by rw [h4₃, hm₂.cur, next_eq], by rw [hm₃]; exact hm₂.blks⟩⟩, ?_⟩
  rw [hz₃, hm₂.cur, next_eq, z_eq hL hi]

theorem loop_ok (hL : L.Ok) {t : State} (h : Inv L g m₀ 0 t) : WP isa romixLoop t (Inv L g m₀ L.pp) :=
  RoMix.count_loop hL.pp_pos (Inv L g m₀) (fun _ hi _ h => body_ok hL hi h) h

/-! ## Step 3 -/

section
variable {pbk : Prog isa} (hv : Verified Arm.target pbk (Spec.Hmac.sha256I.pbkdf2Contract Arm.abi 24))
  (hst : armStack pbk ≤ 24) (name : String)
include hv hst

omit hv hst in
/-- The blocks after the loop, as one string. -/
theorem final_bytes' (hL : L.Ok) {t : State} (h : Inv L g m₀ L.pp t) :
    bytesAt t.mem (State.addr L.b) (L.blen.toNat * 128) =
      (List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) := by
  rw [← hL.len_b, Whole.bytesAt_chunks]
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [h.2.blks k hk]; simp only [hk, ite_true]

omit hv hst in
theorem pbk2_regions (hL : L.Ok) :
    PbkRegions L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) L.out L.ol := by
  have hb := hL.blen_lt
  have e : (BitVec.ofNat 32 (L.blen.toNat * 128)).toNat = L.blen.toNat * 128 := t32 hb
  have sc : Region.Sub (scr1600 L) L.SC := Within.sub (within_base _ (by have := hL.slen17; omega))
  refine ⟨⟨L.BB, by simp, ?_⟩, .inr (.inr (.inr (within_base _ (Nat.le_refl _)))),
    hL.co.symm.sub_right hL.sv_sc, ?_, ?_, hL.co.symm.sub_right sc, ?_, ?_, hL.no, hL.olb⟩
  · rw [e]; exact within_base _ (Nat.le_refl _)
  · rw [e]; exact hL.bo
  · rw [e]; exact hL.bc.sub_right sc
  · rw [e]; exact hL.kb
  · rw [e]; exact hL.nb

theorem step3_ok (hL : L.Ok) {t t₁ : State} (h : Inv L g m₀ L.pp t) (hc₁ : Ctx L g m₀ t₁)
    (hm₁ : t₁.mem = t.mem) (ha₁ : PbkArgs L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) L.out L.ol t₁) :
    WP isa (pbkCall name pbk) t₁ fun t' => Ctx L g m₀ t' ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ (State.addr L.pw) L.pwl.toNat)
        ((List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k)) 1 L.ol.toNat =
        some (bytesAt t'.mem (State.addr L.out) L.ol.toNat) := by
  have hb := hL.blen_lt
  refine WP.mono (pbk_call hv hst name hL hc₁ ha₁ (pbk2_regions hL)) fun t₂ ⟨hc₂, _, _, hp⟩ => ⟨hc₂, ?_⟩
  rw [t32 hb, hc₁.pw_bytes hL, hm₁, final_bytes' hL h] at hp
  exact hp

end

/-! ## The whole function -/

/-- scrypt, from the two derivations and the blocks. -/
theorem body_post (hL : L.Ok) {m : Mem} {out : List Byte}
    (h1 : Step1 L m₀ (bytesAt m (State.addr L.b) (L.blen.toNat * 128)))
    (hp : Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ (State.addr L.pw) L.pwl.toNat)
      ((List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k)) 1 L.ol.toNat = some out) :
    Spec.Scrypt.scrypt (bytesAt m₀ (State.addr L.pw) L.pwl.toNat) (bytesAt m₀ (State.addr L.salt) L.sl.toNat)
      L.NN L.r.toNat L.pp L.ol.toNat = some out := by
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  refine Whole.scrypt_eq hL.valid (B := bytesAt m (State.addr L.b) (L.blen.toNat * 128)) (by rw [e]; exact h1) ?_
  refine Eq.trans (congrArg (fun x => Spec.Pbkdf2.pbkdf2HmacSha256 _ x 1 _) ?_) hp
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [X_of hL h1 hk, Whole.chunk_bytesAt _ _ (blk_le' hL hk)]

section
variable {pbk : Prog isa} (hv : Verified Arm.target pbk (Spec.Hmac.sha256I.pbkdf2Contract Arm.abi 24))
  (hst : armStack pbk ≤ 24) (name : String)
include hv hst

/-- `vg_scrypt` meets `scryptArm` and the calling convention. -/
theorem scrypt_ok {s : State} (h : Proof.Scrypt.scryptArm.pre s) :
    WP isa (scrypt name pbk) s fun s' => abiPreserved s s' ∧ Proof.Scrypt.scryptArm.post s s' := by
  have hL := lay_ok h
  refine WP.seq (WP.mono (save1_ok hL (entry_E h) rfl) fun t₁ ⟨e₁, _, r₁, w₁⟩ => ?_)
  refine WP.seq (WP.mono (save2_ok hL e₁ r₁ w₁) fun t₂ ⟨e₂, r₂, w₂, s₂⟩ => ?_)
  refine WP.seq (WP.mono (save3_ok hL e₂ r₂ w₂ s₂) fun t₃ ⟨e₃, s₃⟩ => ?_)
  refine WP.seq (WP.mono (pbk1Args_ok hL e₃ s₃) fun t₄ ⟨hc₄, _, h4₄, ha₄⟩ => ?_)
  refine WP.seq (WP.mono (step1_ok hv hst name hL hc₄ h4₄ ha₄) fun t₅ ⟨hc₅, h4₅, h1, hx⟩ => ?_)
  have i0 : Inv (lay s) s.gpr s.mem 0 t₅ := ⟨hc₅, by rw [h4₅, blk0], fun k hk => by
    rw [hx k hk]; simp only [Nat.not_lt_zero, ite_false]⟩
  refine WP.seq (WP.mono (loop_ok hL i0) fun t₆ h₆ => ?_)
  refine WP.seq (WP.mono (pbk2Args_ok hL h₆.1) fun t₇ ⟨hc₇, hm₇, ha₇⟩ => ?_)
  refine WP.seq (WP.mono (step3_ok hv hst name hL h₆ hc₇ hm₇ ha₇) fun t₈ ⟨hc₈, hp⟩ => ?_)
  refine WP.mono (restore_ok hL hc₈) fun t₉ ⟨hr₉, hsp₉, hm₉⟩ => ⟨⟨hr₉, hsp₉.trans hc₈.sp⟩, ?_⟩
  simp only [Proof.Scrypt.scryptArm, hm₉]
  exact body_post hL h1 hp

end

end VG.Proof.Scrypt.Arm.Whole

end

/-!
# scrypt on 32-bit ARM: constant time, up to the indices `j`

As on the other targets (`Proof/Scrypt/AArch64/Whole/CT.lean`): two runs whose
public data agree have the same layout, so they are related by `Two P`: both
satisfy `P` with that layout (each with its own registers on entry and
memory), whatever their secrets, and the indices of all the scryptROMix calls
agree (`LeakEq`). The blocks address only our stack arguments, from `sp`, and
`scratch` from registers that hold the same in both runs (the taint analysis,
with the stack arguments public); each call is of constant-time code whose
public data agree (`frame4_rel`, `frame2_rel`); the loop's branch agrees since
both runs count the same blocks.
-/

namespace VG.Proof.Scrypt.Arm.Whole

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Arm.FrameStack
open VG.Spec.Scrypt (bytesAt roMixIndices)
open VG.Proof.Pbkdf2.Whole.Arm (frame2_rel p2_arg0 p2_arg1)

/-- The indices of every scryptROMix agree in two runs from `m₁` and `m₂`. -/
def LeakEq (L : Lay) (m₁ m₂ : Mem) : Prop :=
  (Spec.Scrypt.blocks (bytesAt m₁ (State.addr L.pw) L.pwl.toNat) (bytesAt m₁ (State.addr L.salt) L.sl.toNat)
      L.r.toNat L.pp).flatMap (roMixIndices L.r.toNat L.NN) =
    (Spec.Scrypt.blocks (bytesAt m₂ (State.addr L.pw) L.pwl.toNat) (bytesAt m₂ (State.addr L.salt) L.sl.toNat)
      L.r.toNat L.pp).flatMap (roMixIndices L.r.toNat L.NN)

theorem leak_X {L : Lay} {m₁ m₂ : Mem} (h : LeakEq L m₁ m₂) {k : Nat} (hk : k < L.pp) :
    roMixIndices L.r.toNat L.NN (X L m₁ k) = roMixIndices L.r.toNat L.NN (X L m₂ k) := by
  have h₁ : k < (Spec.Scrypt.blocks (bytesAt m₁ (State.addr L.pw) L.pwl.toNat)
      (bytesAt m₁ (State.addr L.salt) L.sl.toNat) L.r.toNat L.pp).length := by
    rw [Whole.blocks_length]; exact hk
  have h₂ : k < (Spec.Scrypt.blocks (bytesAt m₂ (State.addr L.pw) L.pwl.toNat)
      (bytesAt m₂ (State.addr L.salt) L.sl.toNat) L.r.toNat L.pp).length := by
    rw [Whole.blocks_length]; exact hk
  simp only [X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂,
    Option.getD_some]
  exact Whole.indices_eq h h₁ h₂

/-- The layout of two runs, and what each has on entry. -/
structure Env where
  L : Lay
  g₁ : Reg → BitVec 32
  g₂ : Reg → BitVec 32
  m₁ : Mem
  m₂ : Mem

/-- What one run has, from its layout, its registers and memory on entry. -/
abbrev Pred := Lay → (Reg → BitVec 32) → Mem → State → Prop

/-- Two runs with the same layout, each satisfying `P`. -/
def Two (P : Pred) (a b : State) : Prop :=
  ∃ e : Env, e.L.Ok ∧ LeakEq e.L e.m₁ e.m₂ ∧ P e.L e.g₁ e.m₁ a ∧ P e.L e.g₂ e.m₂ b

/-- `Ctx` and `Φ`. -/
abbrev C (Φ : Lay → Mem → State → Prop) : Pred := fun L g m₀ t => Ctx L g m₀ t ∧ Φ L m₀ t

/-- Code whose runs leak the same, and which establishes `Q`. -/
theorem two_wp {c : Prog isa} {P Q : Pred} (hct : RelCT isa (Two P) c fun _ _ => True)
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → P L g m₀ t → WP isa c t (Q L g m₀)) :
    RelCT isa (Two P) c (Two Q) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨e, hL, hk, c₁, c₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw _ _ _ s₁ hL c₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw _ _ _ s₂ hL c₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, e, hL, hk, y₁, y₂⟩

/-- Two states agree on the taint with the stack arguments and `rs` public. -/
theorem agree_L {L : Lay} (hL : L.Ok) {a b : State} (ha : a.sp = L.sp) (hb : b.sp = L.sp)
    (wa : a.wr = [L.BB, L.VV, L.SC, L.OUT]) (wb : b.wr = [L.BB, L.VV, L.SC, L.OUT])
    (ka : Args L a.mem) (kb : Args L b.mem) {rs : List Reg} (hr : ∀ r ∈ rs, a.gpr r = b.gpr r) :
    VG.Arm.Taint.Agree (argTaint rs 36) a b := by
  have hA := hL.nA
  have out : ∀ (t : State), t.sp = L.sp → t.wr = [L.BB, L.VV, L.SC, L.OUT] →
      t.sp.toNat + 36 ≤ 2 ^ 32 ∧ ∀ r ∈ t.wr, Region.Disjoint ⟨State.addr t.sp, 36⟩ r := fun t hs hw => by
    refine ⟨by rw [hs]; exact hA, fun r hr => ?_⟩
    rw [hw] at hr
    rw [hs]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [hL.ba.symm, hL.va.symm, hL.ca.symm, hL.oa.symm]
  refine agree_argTaint hr (ha.trans hb.symm) (out a ha wa) (out b hb wb)
    (argMem_of (j := 9) (ha.trans hb.symm) (by rw [ha]; exact hA) fun i hi => ?_)
  have st : ∀ (t : State), t.sp = L.sp → ∀ i < 9,
      stackArg t i = t.mem.readW (State.addr L.sp + BitVec.ofNat 64 (4 * i)) 32 := fun t hs i hi => by
    simp only [stackArg, stackArgAddr, hs]
    rw [hL.arg_addr (by omega)]
  rw [st a ha i hi, st b hb i hi]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [ka.r.trans kb.r.symm, ka.b.trans kb.b.symm, ka.blen.trans kb.blen.symm, ka.v.trans kb.v.symm,
    ka.vlen.trans kb.vlen.symm, ka.scr.trans kb.scr.symm, ka.slen.trans kb.slen.symm,
    ka.out.trans kb.out.symm, ka.ol.trans kb.ol.symm]

/-- What every `P` of a piece of straight-line code gives the taint analysis. -/
structure Wfp (P : Pred) : Prop where
  sp : ∀ L g m₀ (t : State), P L g m₀ t → t.sp = L.sp
  wr : ∀ L g m₀ (t : State), P L g m₀ t → t.wr = [L.BB, L.VV, L.SC, L.OUT]
  args : ∀ L g m₀ (t : State), P L g m₀ t → Args L t.mem

theorem Wfp.ctx (Φ : Lay → Mem → State → Prop) : Wfp (C Φ) :=
  ⟨fun _ _ _ _ h => h.1.sp, fun _ _ _ _ h => h.1.wr, fun _ _ _ _ h => h.1.args⟩

/-- A block the taint analysis accepts with the stack arguments and `rs` public. -/
theorem two_blk {is : List Instr} {P Q : Pred} (hP : Wfp P) (rs : List Reg)
    (hr : ∀ (L : Lay) g₁ g₂ m₁ m₂ (a b : State), L.Ok → P L g₁ m₁ a → P L g₂ m₂ b → ∀ r ∈ rs, a.gpr r = b.gpr r)
    {hc : VG.Taint.Hint VG.Arm.Taint.T} (h : (taint.check (argTaint rs 36) (.block is) hc).isSome = true)
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → P L g m₀ t → WP isa (.block is) t (Q L g m₀)) :
    RelCT isa (Two P) (.block is) (Two Q) :=
  two_wp (RelCT.taint (A := taint) (argTaint rs 36) (fun _ _ ⟨_, hL, _, c₁, c₂⟩ =>
    agree_L hL (hP.sp _ _ _ _ c₁) (hP.sp _ _ _ _ c₂) (hP.wr _ _ _ _ c₁) (hP.wr _ _ _ _ c₂)
      (hP.args _ _ _ _ c₁) (hP.args _ _ _ _ c₂) (hr _ _ _ _ _ _ _ hL c₁ c₂)) h) hw

/-! ## The calls -/

/-- A call in a frame of four words, of verified code whose contract and
public data hold in both runs. -/
theorem two_call4 {n : String} {c : Prog isa} {k : Contract isa} {P Q : Pred}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g m₀ (t : State), L.Ok → P L g m₀ t →
      k.pre ((pushed fr4 t).callEntry.withRegions (rd L) (wr L)) ∧
      Covers (rd L ++ wr L) ((pushed fr4 t).rd ++ (pushed fr4 t).wr) ∧ Covers (wr L) (pushed fr4 t).wr)
    (hpub : ∀ (L : Lay) g₁ g₂ m₁ m₂ (a b : State), L.Ok → LeakEq L m₁ m₂ → P L g₁ m₁ a → P L g₂ m₂ b →
      a.sp = b.sp ∧ k.pub ((pushed fr4 a).callEntry.withRegions (rd L) (wr L))
        ((pushed fr4 b).callEntry.withRegions (rd L) (wr L)))
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → P L g m₀ t →
      WP isa (.frame (.push fr4) (.call n c) (.pop .r12 16)) t (Q L g m₀)) :
    RelCT isa (Two P) (.frame (.push fr4) (.call n c) (.pop .r12 16)) (Two Q) :=
  two_wp (fun s₁ s₂ _ _ _ _ hp e₁ e₂ => by
    obtain ⟨e, hL, hk, c₁, c₂⟩ := hp
    obtain ⟨hsp, hpb⟩ := hpub _ _ _ _ _ _ _ hL hk c₁ c₂
    obtain ⟨p₁, v₁, w₁⟩ := hpre _ _ _ _ hL c₁
    obtain ⟨p₂, v₂, w₂⟩ := hpre _ _ _ _ hL c₂
    exact frame4_rel hv hct (P := fun a b => a = s₁ ∧ b = s₂) (rd e.L) (wr e.L)
      (fun _ _ ⟨h₁, h₂⟩ => by subst h₁ h₂; exact ⟨hsp, p₁, p₂, hpb, v₁, w₁, v₂, w₂⟩)
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂) hw

/-- The same for a frame of two words. -/
theorem two_call2 {n : String} {c : Prog isa} {k : Contract isa} {P Q : Pred}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g m₀ (t : State), L.Ok → P L g m₀ t →
      k.pre ((pushed [.r12, .lr] t).callEntry.withRegions (rd L) (wr L)) ∧
      Covers (rd L ++ wr L) ((pushed [.r12, .lr] t).rd ++ (pushed [.r12, .lr] t).wr) ∧
      Covers (wr L) (pushed [.r12, .lr] t).wr)
    (hpub : ∀ (L : Lay) g₁ g₂ m₁ m₂ (a b : State), L.Ok → LeakEq L m₁ m₂ → P L g₁ m₁ a → P L g₂ m₂ b →
      a.sp = b.sp ∧ k.pub ((pushed [.r12, .lr] a).callEntry.withRegions (rd L) (wr L))
        ((pushed [.r12, .lr] b).callEntry.withRegions (rd L) (wr L)))
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → P L g m₀ t →
      WP isa (.frame (.push [.r12, .lr]) (.call n c) (.pop .r12 8)) t (Q L g m₀)) :
    RelCT isa (Two P) (.frame (.push [.r12, .lr]) (.call n c) (.pop .r12 8)) (Two Q) :=
  two_wp (fun s₁ s₂ _ _ _ _ hp e₁ e₂ => by
    obtain ⟨e, hL, hk, c₁, c₂⟩ := hp
    obtain ⟨hsp, hpb⟩ := hpub _ _ _ _ _ _ _ hL hk c₁ c₂
    obtain ⟨p₁, v₁, w₁⟩ := hpre _ _ _ _ hL c₁
    obtain ⟨p₂, v₂, w₂⟩ := hpre _ _ _ _ hL c₂
    exact frame2_rel (by decide) hv hct (P := fun a b => a = s₁ ∧ b = s₂) (rd e.L) (wr e.L)
      (fun _ _ ⟨h₁, h₂⟩ => by subst h₁ h₂; exact ⟨hsp, p₁, p₂, hpb, v₁, w₁, v₂, w₂⟩)
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂) hw

theorem pbk_pub_two {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem} {a b : State}
    (c₁ : Ctx L g₁ m₁ a) (c₂ : Ctx L g₂ m₂ b) (hL : L.Ok) {salt sl out ol : BitVec 32}
    (a₁ : PbkArgs L salt sl out ol a) (a₂ : PbkArgs L salt sl out ol b) :
    a.sp = b.sp ∧ pbkA.pub ((pushed fr4 a).callEntry.withRegions (pbkRd L salt sl) (pbkWr L out ol))
      ((pushed fr4 b).callEntry.withRegions (pbkRd L salt sl) (pbkWr L out ol)) := by
  have s1 : 16 ≤ a.sp.toNat := by rw [c₁.sp]; have := hL.nS; omega
  have s2 : 16 ≤ b.sp.toNat := by rw [c₂.sp]; have := hL.nS; omega
  refine ⟨c₁.sp.trans c₂.sp.symm, ?_⟩
  simp only [pbkA, State.withRegions_sp, State.callEntry_sp, p4_sp, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    pushed_gpr, p4_a0 s1, p4_a1 s1, p4_a2 s1, p4_a3 s1, p4_a0 s2, p4_a1 s2, p4_a2 s2, p4_a3 s2,
    c₁.sp, c₂.sp, a₁.r0, a₁.r1, a₁.r2, a₁.r3, a₁.r10, a₁.r11, a₁.r12, a₁.lr, a₂.r0, a₂.r1, a₂.r2, a₂.r3,
    a₂.r10, a₂.r11, a₂.r12, a₂.lr, and_self]

/-- The block ROMix works on in iteration `i`, on entry to it. -/
theorem romix_bytes {L : Lay} (hL : L.Ok) {g : Reg → BitVec 32} {m₀ : Mem} {t : State}
    (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.pp) (hb : InvB L m₀ i t) (rd wr : List Region) :
    bytesAt ((pushed [.r12, .lr] t).callEntry.withRegions rd wr).mem (blkA L i) (128 * L.r.toNat) =
      X L m₀ i := by
  have hS := hL.nS
  have f₀ := pushed_frameA (rs := [Reg.r12, Reg.lr]) (s := t)
    (by simp only [List.length_cons, List.length_nil]; rw [hc.sp]; omega)
  rw [State.withRegions_mem, State.callEntry_mem, Memory.frame_bytesAt f₀ (fun R hR => by
      simp only [List.mem_singleton] at hR; subst hR
      have hs : Region.Sub ⟨State.addr (t.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)),
          4 * [Reg.r12, Reg.lr].length⟩ L.STK := by
        rw [hc.sp]; exact args8_sub hL
      rw [Nat.mul_comm]
      exact ((hL.stk_in (blk_in hL hi)).sub_left hs).symm) (by have := hL.r_lt; omega), hb.blks i hi]
  simp only [Nat.lt_irrefl, ite_false]

theorem romix_pub_two {L : Lay} (hL : L.Ok) {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem} {a b : State}
    (hk : LeakEq L m₁ m₂) (c₁ : Ctx L g₁ m₁ a) (c₂ : Ctx L g₂ m₂ b) {i : Nat} (hi : i < L.pp)
    (b₁ : InvB L m₁ i a) (b₂ : InvB L m₂ i b) (a₁ : RomixArgs L (blkAt L i) a)
    (a₂ : RomixArgs L (blkAt L i) b) :
    a.sp = b.sp ∧ Proof.Scrypt.roMixArm.pub ((pushed [.r12, .lr] a).callEntry.withRegions (romixRd L) (romixWr L i))
      ((pushed [.r12, .lr] b).callEntry.withRegions (romixRd L) (romixWr L i)) := by
  have s1 : 8 ≤ a.sp.toNat := by rw [c₁.sp]; have := hL.nS; omega
  have s2 : 8 ≤ b.sp.toNat := by rw [c₂.sp]; have := hL.nS; omega
  have y₁ := romix_bytes hL c₁ hi b₁ (romixRd L) (romixWr L i)
  have y₂ := romix_bytes hL c₂ hi b₂ (romixRd L) (romixWr L i)
  refine ⟨c₁.sp.trans c₂.sp.symm, ?_⟩
  simp only [Proof.Scrypt.roMixArm, State.withRegions_sp, State.callEntry_sp, pushed_sp, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    pushed_gpr, p2_arg0 s1, p2_arg1, p2_arg0 s2, c₁.sp, c₂.sp, a₁.r0, a₁.r1, a₁.r2, a₁.r3, a₁.r12, a₁.lr,
    a₂.r0, a₂.r1, a₂.r2, a₂.r3, a₂.r12, a₂.lr, addr_blk hL hi, true_and]
  rw [y₁, y₂]
  exact leak_X hk hi

/-! ## The pieces -/

theorem Wfp.e {P : Pred} (h : ∀ L g m₀ t, P L g m₀ t → E L g m₀ t) : Wfp P :=
  ⟨fun _ _ _ _ hp => (h _ _ _ _ hp).sp, fun _ _ _ _ hp => (h _ _ _ _ hp).wr,
    fun _ _ _ _ hp => (h _ _ _ _ hp).args⟩

abbrev P0 : Pred := fun L g m₀ t => E L g m₀ t ∧ t.gpr .lr = g .lr
abbrev P1 : Pred := fun L g m₀ t => E L g m₀ t ∧ t.gpr .r12 = L.scr ∧ t.mem.readW (State.addr L.scr) 32 = g .lr
abbrev P2 : Pred := fun L g m₀ t =>
  E L g m₀ t ∧ t.gpr .r12 = L.svb ∧ t.mem.readW (State.addr L.scr) 32 = g .lr ∧ Saved8 L g t.mem
abbrev P3 : Pred := fun L g m₀ t => E L g m₀ t ∧ Saved L g t.mem

theorem save1_ct : RelCT isa (Two P0) (.block save1) (Two P1) :=
  two_blk (Wfp.e fun _ _ _ _ h => h.1) [] (fun _ _ _ _ _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
    fun _ _ _ _ hL ⟨he, hl⟩ => WP.mono (save1_ok hL he hl) fun _ ⟨e, _, r, w⟩ => ⟨e, r, w⟩

theorem save2_ct : RelCT isa (Two P1) (.block save2) (Two P2) :=
  two_blk (Wfp.e fun _ _ _ _ h => h.1) [.r12]
    (fun _ _ _ _ _ _ _ _ c₁ c₂ r h => by
      simp only [List.mem_singleton] at h; subst h; exact c₁.2.1.trans c₂.2.1.symm) (by taint_decide)
    fun _ _ _ _ hL ⟨he, hr, hw⟩ => save2_ok hL he hr hw

theorem save3_ct : RelCT isa (Two P2) (.block save3) (Two P3) :=
  two_blk (Wfp.e fun _ _ _ _ h => h.1) [.r12]
    (fun _ _ _ _ _ _ _ _ c₁ c₂ r h => by
      simp only [List.mem_singleton] at h; subst h; exact c₁.2.1.trans c₂.2.1.symm) (by taint_decide)
    fun _ _ _ _ hL ⟨he, hr, hw, h8⟩ => save3_ok hL he hr hw h8

/-- Iteration `pp - n` of the loop is next. -/
abbrev LoopAt (n : Nat) (L : Lay) (m₀ : Mem) (t : State) : Prop :=
  0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n) t

theorem body_ct (n : Nat) :
    RelCT isa (Two (C (LoopAt n))) (.seq (.block romixArgs) (.seq (.frame (.push [.r12, .lr])
      (.call "vg_scrypt_romix" Impl.Scrypt.Arm.roMix) (.pop .r12 8)) (.block nextBlock)))
      (Two (C fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n + 1) t ∧
        t.z = decide (L.pp - n + 1 = L.pp))) := by
  have a : RelCT isa (Two (C (LoopAt n))) (.block romixArgs) (Two (C fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧
      InvB L m₀ (L.pp - n) t ∧ RomixArgs L (blkAt L (L.pp - n)) t)) :=
    two_blk (Wfp.ctx _) [] (fun _ _ _ _ _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
      fun _ _ _ _ hL ⟨hc, h0, hn, hb⟩ =>
        WP.mono (romixArgs_ok hL hc) fun _ ⟨hc', hm, h4, ha⟩ =>
          ⟨hc', h0, hn, ⟨h4.trans hb.cur, by rw [hm]; exact hb.blks⟩, by rw [hb.cur] at ha; exact ha⟩
  have b : RelCT isa (Two (C fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n) t ∧
      RomixArgs L (blkAt L (L.pp - n)) t)) (.frame (.push [.r12, .lr])
      (.call "vg_scrypt_romix" Impl.Scrypt.Arm.roMix) (.pop .r12 8))
      (Two (C fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ Mid L m₀ (L.pp - n) t)) :=
    two_call2 RoMix.roMix_correct RoMix.roMix_ct (fun L => romixRd L) (fun L => romixWr L (L.pp - n))
      (fun L _ _ _ hL ⟨hc, h0, hn, _, ha⟩ => ⟨romix_pre hL hc (i := L.pp - n) (by omega) ha,
        romix_cov hL hc (i := L.pp - n) (by omega)⟩)
      (fun _ _ _ _ _ _ _ hL hk ⟨c₁, h0, hn, b₁, a₁⟩ ⟨c₂, _, _, b₂, a₂⟩ =>
        romix_pub_two hL hk c₁ c₂ (by omega) b₁ b₂ a₁ a₂)
      (fun _ _ _ _ hL ⟨hc, h0, hn, hb, ha⟩ =>
        WP.mono (call_step hL (by omega) hc hb ha) fun _ ⟨hc', hm⟩ => ⟨hc', h0, hn, hm⟩)
  have c : RelCT isa (Two (C fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ Mid L m₀ (L.pp - n) t)) (.block nextBlock)
      (Two (C fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n + 1) t ∧
        t.z = decide (L.pp - n + 1 = L.pp))) :=
    two_blk (Wfp.ctx _) [] (fun _ _ _ _ _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
      fun _ _ _ _ hL ⟨hc, h0, hn, hm⟩ =>
        WP.mono (nextBlock_ok hc) fun _ ⟨hc', hm', h4, hz⟩ =>
          ⟨hc', h0, hn, ⟨by rw [h4, hm.cur, next_eq], by rw [hm']; exact hm.blks⟩,
            by rw [hz, hm.cur, next_eq, z_eq hL (by omega)]⟩
  exact a.seq (b.seq c)

theorem loop_ct :
    RelCT isa (Two (C fun L m₀ t => InvB L m₀ 0 t)) romixLoop (Two (C fun L m₀ t => InvB L m₀ L.pp t)) := by
  have ev : ∀ x : State, isa.eval .ne x = some (!x.z) := fun x => VG.Proof.MdStream.Arm.eval_ne x
  have h := fun n => RelCT.loop (M := isa) (c := .ne) (Q := Two (C fun L m₀ t => InvB L m₀ L.pp t))
    (fun n => Two (C (LoopAt n))) (fun n => (body_ct n).mono (fun _ _ h => h) fun a b hab => by
      obtain ⟨e, hL, hk, ⟨c₁, h0, hn, b₁, z₁⟩, ⟨c₂, -, -, b₂, z₂⟩⟩ := hab
      rw [ev, ev, z₁, z₂]
      refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
      · have hl : e.L.pp - n + 1 = e.L.pp := by simpa using hf
        exact ⟨e, hL, hk, ⟨c₁, show InvB e.L e.m₁ e.L.pp a from hl ▸ b₁⟩,
          ⟨c₂, show InvB e.L e.m₂ e.L.pp b from hl ▸ b₂⟩⟩
      · have hl : e.L.pp - n + 1 ≠ e.L.pp := by simpa using ht
        have e₁ : e.L.pp - (n - 1) = e.L.pp - n + 1 := by omega
        exact ⟨n - 1, by omega, e, hL, hk, ⟨c₁, by omega, by omega, e₁ ▸ b₁⟩,
          ⟨c₂, by omega, by omega, e₁ ▸ b₂⟩⟩) n
  refine (RelCT.exists_ h).mono (fun a b ⟨e, hL, hk, ⟨c₁, b₁⟩, ⟨c₂, b₂⟩⟩ => ⟨e.L.pp, e, hL, hk,
    ⟨c₁, hL.pp_pos, Nat.le_refl _, by rw [Nat.sub_self]; exact b₁⟩,
    ⟨c₂, hL.pp_pos, Nat.le_refl _, by rw [Nat.sub_self]; exact b₂⟩⟩) fun _ _ h => h

/-! ## The whole function -/

abbrev Args1 (L : Lay) (_ : Mem) (t : State) : Prop :=
  t.gpr .r4 = L.b ∧ PbkArgs L L.salt L.sl L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) t
abbrev Args2 (L : Lay) (_ : Mem) (t : State) : Prop :=
  PbkArgs L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) L.out L.ol t

theorem pbk1_ct : RelCT isa (Two P3) (.block pbk1Args) (Two (C Args1)) :=
  two_blk (Wfp.e fun _ _ _ _ h => h.1) [] (fun _ _ _ _ _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
    fun _ _ _ _ hL ⟨he, hs⟩ => WP.mono (pbk1Args_ok hL he hs) fun _ ⟨hc, _, h4, ha⟩ => ⟨hc, h4, ha⟩

theorem pbk2_ct : RelCT isa (Two (C fun L m₀ t => InvB L m₀ L.pp t)) (.block pbk2Args) (Two (C Args2)) :=
  two_blk (Wfp.ctx _) [] (fun _ _ _ _ _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
    fun _ _ _ _ hL ⟨hc, _⟩ => WP.mono (pbk2Args_ok hL hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩

theorem restore_ct : RelCT isa (Two (C fun _ _ _ => True)) (.block restore) fun _ _ => True :=
  (two_blk (Q := fun _ _ _ _ => True) (Wfp.ctx _) [.r6, .r7]
    (fun _ _ _ _ _ _ _ _ c₁ c₂ r h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact c₁.1.r6.trans c₂.1.r6.symm
      · exact c₁.1.r7.trans c₂.1.r7.symm) (by taint_decide)
    fun _ _ _ _ hL ⟨hc, _⟩ => WP.mono (restore_ok hL hc) fun _ _ => trivial).mono (fun _ _ h => h)
    fun _ _ _ => trivial

section
variable {pbk : Prog isa} (hv : Verified Arm.target pbk (Spec.Hmac.sha256I.pbkdf2Contract Arm.abi 24))
  (hst : armStack pbk ≤ 24) (name : String)
include hv hst

theorem call1_ct : RelCT isa (Two (C Args1)) (pbkCall name pbk) (Two (C fun L m₀ t => InvB L m₀ 0 t)) :=
  two_call4 (pbk_correct hv) (pbk_ct hv) (fun L => pbkRd L L.salt L.sl)
    (fun L => pbkWr L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)))
    (fun _ _ _ _ hL ⟨hc, _, ha⟩ => ⟨pbk_pre' hL hc ha (pbk1_regions hL), pbk_cov hL hc (pbk1_regions hL)⟩)
    (fun _ _ _ _ _ _ _ hL _ ⟨c₁, _, a₁⟩ ⟨c₂, _, a₂⟩ => pbk_pub_two c₁ c₂ hL a₁ a₂)
    (fun _ _ _ _ hL ⟨hc, h4, ha⟩ => WP.mono (step1_ok hv hst name hL hc h4 ha) fun _ ⟨hc', h4', _, hx⟩ =>
      ⟨hc', by rw [h4', blk0], fun k hk => by rw [hx k hk]; simp only [Nat.not_lt_zero, ite_false]⟩)

theorem call2_ct : RelCT isa (Two (C Args2)) (pbkCall name pbk) (Two (C fun _ _ _ => True)) :=
  two_call4 (pbk_correct hv) (pbk_ct hv) (fun L => pbkRd L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)))
    (fun L => pbkWr L L.out L.ol)
    (fun _ _ _ _ hL ⟨hc, ha⟩ => ⟨pbk_pre' hL hc ha (pbk2_regions hL), pbk_cov hL hc (pbk2_regions hL)⟩)
    (fun _ _ _ _ _ _ _ hL _ ⟨c₁, a₁⟩ ⟨c₂, a₂⟩ => pbk_pub_two c₁ c₂ hL a₁ a₂)
    (fun _ _ _ _ hL ⟨hc, ha⟩ => WP.mono (pbk_call hv hst name hL hc ha (pbk2_regions hL)) fun _ h =>
      ⟨h.1, trivial⟩)

theorem scrypt_ct :
    ConstantTime isa Proof.Scrypt.scryptArm.pre Proof.Scrypt.scryptArm.pub (scrypt name pbk) := by
  refine RelCT.constantTime ((save1_ct.seq (save2_ct.seq (save3_ct.seq (pbk1_ct.seq
    ((call1_ct hv hst name).seq (loop_ct.seq (pbk2_ct.seq ((call2_ct hv hst name).seq restore_ct)))))))).mono
    ?_ fun _ _ _ => trivial)
  rintro s₁ s₂ ⟨h₁, h₂, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, hsp, hlk⟩
  have e : lay s₂ = lay s₁ := by
    simp only [lay, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, hsp]
  refine ⟨⟨lay s₁, s₁.gpr, s₂.gpr, s₁.mem, s₂.mem⟩, lay_ok h₁, ?_, ⟨entry_E h₁, rfl⟩,
    ⟨e ▸ entry_E h₂, rfl⟩⟩
  rw [← h0, ← h1, ← h2, ← h3, ← a0, ← a2, ← a4] at hlk
  exact hlk

end

end VG.Proof.Scrypt.Arm.Whole

end

/-!
# scrypt on 32-bit ARM: the shared contract

`vg_scrypt`, calling any implementation of PBKDF2-HMAC-SHA256 verified against
its shared contract whose frames use at most 24 bytes of stack, is verified
against `Spec.Scrypt.scryptContract` for the 40 bytes of stack its calls use
(`scrypt_verified_of`); and so is the one calling `vg_pbkdf2_hmac_sha256`
(`scrypt_verified`).
-/

namespace VG.Proof.Scrypt.Arm.Whole

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Arm.FrameStack

theorem map_range9 {α : Type} (f : Nat → α) :
    List.map f (List.range 9) = [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8] := rfl

/-- A state satisfying the precondition: `N = 2`, `r = 1`, `p = 1`, a
one-byte key and an empty password and salt; the stack arguments are the
words at `0x9000`. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r2 => 0x2000
    | _ => 0
  sp := 0x9000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x9000 then 1 else if a = 0x9005 then 0x30 else if a = 0x9008 then 1
    else if a = 0x900D then 0x40 else if a = 0x9010 then 2 else if a = 0x9015 then 0x50
    else if a = 0x9018 then 17 else if a = 0x901D then 0x60 else if a = 0x9020 then 1 else 0
  rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩, ⟨0x9000, 36⟩]
  wr := [⟨0x3000, 128⟩, ⟨0x4000, 256⟩, ⟨0x5000, 2176⟩, ⟨0x6000, 1⟩]

theorem scrypt_implies :
    Proof.Scrypt.scryptArm.Implies (Spec.Scrypt.scryptContract Arm.abi 40) := by
  exact
    { pre := by
        intro s h
        sig_pre [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptArm, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, map_range9, List.append_eq] at h
        sig_split h
        sig_reduce [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptArm, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, map_range9, List.append_eq]
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | with_reducible exact Region.Disjoint.symm ‹_›
      post := by
        rintro s s' - h
        sig_post [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptArm, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, map_range9, List.append_eq]
        sig_reduce [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptArm, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, map_range9, List.append_eq] at h
        exact h
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptArm, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, map_range9, List.append_eq] at h
        sig_split h
        rename_i hsp hlk h0 h1 h2 h3 a0 a1 a2 a3 a4 a5 a6 a7
        exact ⟨h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, h, hsp, hlk⟩
      sat := by
        sig_implies_sat [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, map_range9, List.append_eq, satState] [satState]
          using satState }

section
variable {pbk : Prog isa} (hv : Verified Arm.target pbk (Spec.Hmac.sha256I.pbkdf2Contract Arm.abi 24))
  (hst : armStack pbk ≤ 24) (name : String)
include hv hst

/-- `vg_scrypt`, calling the implementation `pbk` of PBKDF2 named `name`. -/
theorem scrypt_verified_of :
    Verified Arm.target (scrypt name pbk) (Spec.Scrypt.scryptContract Arm.abi 40) :=
  Verified.of_correct (fun _ h => by
    obtain ⟨t, s', he, hp⟩ := scrypt_ok hv hst name h
    exact ⟨t, s', he, hp⟩) (scrypt_ct hv hst name) scrypt_implies

end

/-! ## With `vg_pbkdf2_hmac_sha256` -/

theorem armStack_zero {c : Prog isa} (h : c.noFrames = true) : armStack c = 0 := by
  induction c <;> simp_all [Code.noFrames, armStack]

/-- How much stack the frames of `pbkdf2` use. -/
theorem pbkdf2_stack {F : Impl.Pbkdf2.Whole.Arm.Fns} (hi : F.H.initC.noFrames = true)
    (hu : F.H.updC.noFrames = true) (hf : F.H.finC.noFrames = true) (h₁ : armStack F.hiC ≤ 16)
    (h₂ : armStack F.hfC ≤ 16) (h₃ : armStack F.itC ≤ 16) : armStack F.pbkdf2 ≤ 24 := by
  simp only [Impl.Pbkdf2.Whole.Arm.Fns.pbkdf2, Impl.Pbkdf2.Whole.Arm.Fns.key,
    Impl.Pbkdf2.Whole.Arm.Fns.hashKey, Impl.Pbkdf2.Whole.Arm.Fns.setup, Impl.Pbkdf2.Whole.Arm.Fns.block,
    Impl.Pbkdf2.Whole.Arm.Fns.outLen, Impl.Pbkdf2.Whole.Arm.Fns.outLoop, Impl.Pbkdf2.Stream.Arm.copy,
    Impl.Pbkdf2.Stream.Arm.Hash.callInit, armStack, armStack_zero hi, armStack_zero hu, armStack_zero hf,
    List.length_cons, List.length_nil, Nat.max_le]
  omega

/-- The code of `vg_pbkdf2_hmac_sha256`. -/
abbrev pbkC : Prog isa := Proof.Pbkdf2.Whole.Arm.sha256F.pbkdf2

theorem pbk_stack : armStack pbkC ≤ 24 :=
  pbkdf2_stack Proof.Pbkdf2.Stream.Arm.sha256OK.initNF Proof.Pbkdf2.Stream.Arm.sha256OK.updNF
    Proof.Pbkdf2.Stream.Arm.sha256OK.finNF Proof.Pbkdf2.Whole.Arm.sha256OKF.hiSt
    Proof.Pbkdf2.Whole.Arm.sha256OKF.hfSt Proof.Pbkdf2.Whole.Arm.sha256OKF.itSt

/-- `vg_scrypt`. -/
theorem scrypt_verified :
    Verified Arm.target (scrypt Spec.Hmac.sha256I.pbkdf2Api.name pbkC) (Spec.Scrypt.scryptContract Arm.abi 40) :=
  scrypt_verified_of Proof.Pbkdf2.Whole.Arm.sha256 pbk_stack _

end VG.Proof.Scrypt.Arm.Whole
