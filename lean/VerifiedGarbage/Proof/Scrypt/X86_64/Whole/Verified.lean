import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Scrypt.X86_64.Whole.Calls

section

/-!
# scrypt on x86-64: correctness

Step 1 leaves the blocks `X k` of `PBKDF2-HMAC-SHA256 (P, S, 1, 128 blen)` in
`b` (`step1_ok`); the loop replaces them by their scryptROMix one at a time
(`Inv`, `loop_ok`); step 3 derives the key from them (`step3_ok`). `scrypt_ok`
puts the frame around it, for any implementation `pbk` of PBKDF2 verified
against its shared contract.
-/

namespace VG.Proof.Scrypt.X86_64.Whole

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt toNat_add_ofNat)
open VG.Spec.Scrypt (bytesAt)

variable {L : Lay} {g : Reg → BitVec 64} {m₀ : Mem}

/-! ## The password, the salt and the blocks -/

namespace Ctx

variable {t : State} (hc : Ctx L g m₀ t) (hL : L.Ok)
include hc hL

theorem pw_bytes : bytesAt t.mem L.pw L.pwl.toNat = bytesAt m₀ L.pw L.pwl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.pb, hL.pv, hL.pc, hL.po, hL.kp.symm]) (by have := hL.np; omega)

theorem salt_bytes : bytesAt t.mem L.salt L.sl.toNat = bytesAt m₀ L.salt L.sl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.sb, hL.sv, hL.sc, hL.so, hL.ks.symm]) (by have := hL.ns; omega)

end Ctx

/-- Block `k` of step 1. -/
def X (L : Lay) (m₀ : Mem) (k : Nat) : List Byte :=
  (Spec.Scrypt.blocks (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) L.r.toNat L.pp).getD k []

/-- The derived key of step 1, from the password and the salt on entry. -/
abbrev Step1 (L : Lay) (m₀ : Mem) (B : List Byte) : Prop :=
  Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) 1
    (L.blen.toNat * 128) = some B

theorem X_of (hL : L.Ok) {m : Mem} (h : Step1 L m₀ (bytesAt m L.b (L.blen.toNat * 128))) {k : Nat}
    (hk : k < L.pp) : X L m₀ k = bytesAt m (blkAt L k) (128 * L.r.toNat) := by
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have h' : Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) 1
      (L.pp * 128 * L.r.toNat) = some (bytesAt m L.b (L.pp * 128 * L.r.toNat)) := by rw [e]; exact h
  have hl : k < (Spec.Scrypt.blocks (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat)
      L.r.toNat L.pp).length := by rw [Whole.blocks_length]; exact hk
  rw [X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some,
    Whole.blocks_getElem h' hl]

/-- Distinct blocks are disjoint. -/
theorem blk_disj (hL : L.Ok) {k i : Nat} (hk : k < L.pp) (hi : i < L.pp) (hne : k ≠ i) :
    Region.Disjoint ⟨blkAt L k, 128 * L.r.toNat⟩ ⟨blkAt L i, L.r.toNat * 128⟩ := by
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
    Region.Sub ⟨blkAt L k, 128 * L.r.toNat⟩ L.BB := by
  have := blk_le hL hk
  exact Offset.sub_base _ (by omega)

theorem scr_sub (hL : L.Ok) : Region.Sub ⟨L.scr, 200 * 8⟩ L.SC :=
  Within.sub (within_base _ (by have := hL.slen17; omega))

/-! ## Step 1 -/

section
variable {pbk : Prog isa} (hv : Verified X86_64.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract X86_64.abi 24))
  (hsp : NoSp pbk) (hd : pbk.depth ≤ 3) (name : String)
include hv hsp hd

omit hv hsp hd in
theorem pbk1_regions (hL : L.Ok) :
    PbkRegions L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) := by
  have hb := hL.blen_lt
  refine ⟨⟨L.SALT, by simp, within_base _ (Nat.le_refl _)⟩, ?_, ?_, ?_, ?_, hL.ks, hL.ns, ?_, ?_⟩
  · rw [toNat_ofNat_lt hb]; exact .inl (within_base _ (Nat.le_refl _))
  · rw [toNat_ofNat_lt hb]; exact hL.sb
  · exact hL.sc.sub_right (scr_sub hL)
  · rw [toNat_ofNat_lt hb]
    exact hL.bc.sub_right (scr_sub hL)
  · rw [toNat_ofNat_lt hb]; exact hL.nb
  · rw [toNat_ofNat_lt hb]; exact hL.ol1

/-- The call of step 1. -/
theorem pbk1_call_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t)
    (ha : PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t) :
    WP isa (.call name pbk) t fun t' => Ctx L g m₀ t' ∧
      Step1 L m₀ (bytesAt t'.mem L.b (L.blen.toNat * 128)) ∧
      ∀ k < L.pp, bytesAt t'.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k := by
  have hb := hL.blen_lt
  refine WP.mono (pbk_call hv hsp hd name hL hc ha (pbk1_regions hL)) fun t₂ ⟨hc₂, _, hp⟩ =>
    ⟨hc₂, ?_, fun k hk => ?_⟩
  · rw [toNat_ofNat_lt hb, hc.pw_bytes hL, hc.salt_bytes hL] at hp
    exact hp
  · rw [toNat_ofNat_lt hb, hc.pw_bytes hL, hc.salt_bytes hL] at hp
    exact (X_of hL hp hk).symm

theorem step1_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (he : Entry L t) :
    WP isa (pbkCall name pbk pbk1Args) t fun t' => Ctx L g m₀ t' ∧
      Step1 L m₀ (bytesAt t'.mem L.b (L.blen.toNat * 128)) ∧
      ∀ k < L.pp, bytesAt t'.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k :=
  WP.seq (WP.mono (pbk1Args_ok hL hc he) fun _ ⟨hc₁, ha₁, _⟩ => pbk1_call_ok hv hsp hd name hL hc₁ ha₁)

end

/-! ## The loop -/

/-- After `i` iterations of the loop: the next block is `i`, and blocks
`0, …, i - 1` are scryptROMix of those of step 1. -/
structure InvB (L : Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.mem.readW (L.B + BitVec.ofNat 64 48) 64 = blkAt L i
  blks : ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) =
    if k < i then Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) else X L m₀ k

abbrev Inv (L : Lay) (g : Reg → BitVec 64) (m₀ : Mem) (i : Nat) (t : State) : Prop :=
  Ctx L g m₀ t ∧ InvB L m₀ i t

/-- In iteration `i`, after the call of ROMix: blocks `0, …, i` are scryptROMix
of those of step 1. -/
structure Mid (L : Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.mem.readW (L.B + BitVec.ofNat 64 48) 64 = blkAt L i
  blks : ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) =
    if k < i + 1 then Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) else X L m₀ k

theorem blk_le' (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    128 * L.r.toNat * i + 128 * L.r.toNat ≤ L.blen.toNat * 128 := by
  have := blk_le hL hi; rw [Nat.mul_comm L.r.toNat 128] at this; exact this

theorem blk0 (L : Lay) : blkAt L 0 = L.b := by
  simp only [blkAt, Nat.mul_zero]; exact BitVec.add_zero _

/-- A block of `b` misses the frame's first three words. -/
theorem blk_fr (hL : L.Ok) {k : Nat} (hk : k < L.pp) :
    Region.Disjoint ⟨blkAt L k, 128 * L.r.toNat⟩ ⟨L.B + BitVec.ofNat 64 32, 24⟩ :=
  (hL.kb.symm.sub_left (blk_sub hL hk)).sub_right (Offset.sub_base _ (by omega))

theorem start_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t)
    (hx : ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k) :
    WP isa (.block cur0) t (Inv L g m₀ 0) :=
  WP.mono (cur0_ok hL hc) fun t' ⟨hc', hb, hf⟩ => ⟨hc', hb.trans (blk0 L).symm, fun k hk => by
    simp only [Nat.not_lt_zero, ite_false]
    rw [← hx k hk]
    exact Memory.frame_bytesAt hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact blk_fr hL hk)
      (by have := hL.blen_lt; have := blk_le hL hk; omega)⟩

theorem next_eq (L : Lay) (i : Nat) :
    blkAt L i + BitVec.ofNat 64 (L.r.toNat * 128) = blkAt L (i + 1) := by
  simp only [blkAt]
  rw [add_add, Nat.mul_succ (128 * L.r.toNat) i, Nat.mul_comm L.r.toNat 128]

theorem zf_eq (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    (blkAt L (i + 1) - (BitVec.ofNat 64 (L.blen.toNat * 128) + L.b) == 0) = decide (i + 1 = L.pp) := by
  have h₁ := blk_le hL hi
  have hb := hL.blen_lt
  have hr := hL.rpos
  rw [BitVec.add_comm (BitVec.ofNat 64 _) L.b]
  simp only [blkAt]
  rw [Offset.add_sub_add_left, ← hL.len_b]
  have e₁ : 128 * L.r.toNat * (i + 1) < 2 ^ 64 := by
    rw [Nat.mul_succ]; rw [← hL.len_b] at h₁ hb; omega
  have e₂ : 128 * L.r.toNat * L.pp < 2 ^ 64 := by rw [hL.len_b]; exact hb
  rw [Offset.ofNat_sub_ofNat_beq e₁ e₂]
  refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => by rw [h]⟩
  exact Nat.eq_of_mul_eq_mul_left (by omega) h

theorem call_step (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (hc : Ctx L g m₀ t)
    (hb : InvB L m₀ i t) (ha : RomixArgs L (blkAt L i) t) :
    WP isa (.call "vg_scrypt_romix" Impl.Scrypt.X86_64.roMix) t fun t' => Ctx L g m₀ t' ∧ Mid L m₀ i t' := by
  refine WP.mono (romix_call hL hc hi ha) fun t₂ ⟨hc₂, hf₂, hr₂⟩ => ⟨hc₂, ?_, fun k hk => ?_⟩
  · rw [← hb.cur]
    refine hf₂.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hL.stk_in (by omega) (blk_in hL hi)
    · exact hL.stk_in (by omega) (.inr (.inl (within_base _ (Nat.le_refl _))))
    · exact hL.stk_in (by omega) (.inr (.inr (.inl (within_base _ (by have := hL.slen; omega)))))
    · exact Offset.disjoint_base _ (by omega) (by have := hL.nB; omega)
  · by_cases hki : k = i
    · subst hki
      rw [hr₂, hb.blks k hk]
      simp only [Nat.lt_irrefl, ite_false, Nat.lt_succ_self, ite_true]
    · have e₂ : bytesAt t₂.mem (blkAt L k) (128 * L.r.toNat) = bytesAt t.mem (blkAt L k) (128 * L.r.toNat) :=
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

theorem next_step (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (hc : Ctx L g m₀ t)
    (hm : Mid L m₀ i t) :
    WP isa (.block nextBlock) t fun t' => Ctx L g m₀ t' ∧ InvB L m₀ (i + 1) t' ∧
      t'.zf = some (decide (i + 1 = L.pp)) :=
  WP.mono (nextBlock_ok hL hc hm.cur) fun t₃ ⟨hc₃, hf₃, hb₃, hz₃⟩ =>
    ⟨hc₃, ⟨by rw [hb₃, next_eq], fun k hk => by
      rw [← hm.blks k hk]
      exact Memory.frame_bytesAt hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact blk_fr hL hk)
        (by have := hL.blen_lt; have := blk_le hL hk; omega)⟩,
      by rw [hz₃, next_eq, zf_eq hL hi]⟩

theorem body_ok (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (h : Inv L g m₀ i t) :
    WP isa (.seq (.block romixArgs) (.seq (.call "vg_scrypt_romix" Impl.Scrypt.X86_64.roMix)
      (.block nextBlock))) t fun t' => Inv L g m₀ (i + 1) t' ∧ t'.zf = some (decide (i + 1 = L.pp)) :=
  WP.seq (WP.mono (romixArgs_ok hL h.1 h.2.cur) fun t₁ ⟨hc₁, hm₁, ha₁⟩ =>
    WP.seq (WP.mono (call_step hL hi hc₁ ⟨by rw [hm₁]; exact h.2.cur, by rw [hm₁]; exact h.2.blks⟩ ha₁) fun t₂ ⟨hc₂, hm₂⟩ =>
      WP.mono (next_step hL hi hc₂ hm₂) fun _ ⟨hc₃, hb₃, hz₃⟩ => ⟨⟨hc₃, hb₃⟩, hz₃⟩))

theorem loop_ok (hL : L.Ok) {t : State} (h : Inv L g m₀ 0 t) : WP isa romixLoop t (Inv L g m₀ L.pp) :=
  RoMix.count_loop hL.pp_pos (Inv L g m₀) (fun _ hi _ h => body_ok hL hi h) h

/-! ## Step 3 -/

section
variable {pbk : Prog isa} (hv : Verified X86_64.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract X86_64.abi 24))
  (hsp : NoSp pbk) (hd : pbk.depth ≤ 3) (name : String)
include hv hsp hd

omit hv hsp hd in
/-- The blocks after the loop, as one string. -/
theorem final_bytes' (hL : L.Ok) {t : State} (h : Inv L g m₀ L.pp t) :
    bytesAt t.mem L.b (L.blen.toNat * 128) =
      (List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) := by
  rw [← hL.len_b, Whole.bytesAt_chunks]
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [h.2.blks k hk]; simp only [hk, ite_true]

omit hv hsp hd in
theorem pbk2_regions (hL : L.Ok) :
    PbkRegions L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol := by
  have hb := hL.blen_lt
  refine ⟨⟨L.BB, by simp, ?_⟩, .inr (.inr (.inr (within_base _ (Nat.le_refl _)))), ?_,
    ?_, hL.co.symm.sub_right (scr_sub hL), ?_, ?_, hL.no, hL.olb⟩
  · rw [toNat_ofNat_lt hb]; exact within_base _ (Nat.le_refl _)
  · rw [toNat_ofNat_lt hb]; exact hL.bo
  · rw [toNat_ofNat_lt hb]; exact hL.bc.sub_right (scr_sub hL)
  · rw [toNat_ofNat_lt hb]; exact hL.kb
  · rw [toNat_ofNat_lt hb]; exact hL.nb

theorem step3_ok (hL : L.Ok) {t : State} (h : Inv L g m₀ L.pp t) :
    WP isa (pbkCall name pbk pbk2Args) t fun t' => Ctx L g m₀ t' ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ L.pw L.pwl.toNat)
        ((List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k)) 1 L.ol.toNat =
        some (bytesAt t'.mem L.out L.ol.toNat) := by
  have hb := hL.blen_lt
  refine WP.seq (WP.mono (pbk2Args_ok hL h.1) fun t₁ ⟨hc₁, ha₁, hf₁⟩ => ?_)
  refine WP.mono (pbk_call hv hsp hd name hL hc₁ ha₁ (pbk2_regions hL)) fun t₂ ⟨hc₂, _, hp⟩ => ⟨hc₂, ?_⟩
  · have e : bytesAt t₁.mem L.b (L.blen.toNat * 128) = bytesAt t.mem L.b (L.blen.toNat * 128) :=
      Memory.frame_bytesAt hf₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hL.kb.symm.sub_right (Offset.sub_base _ (by omega)))
        (by omega)
    rw [toNat_ofNat_lt hb, hc₁.pw_bytes hL, e, final_bytes' hL h] at hp
    exact hp

/-- The frame's body. -/
theorem body_scrypt_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (he : Entry L t) :
    WP isa (scryptBody name pbk) t fun t' => Ctx L g m₀ t' ∧
      Spec.Scrypt.scrypt (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) L.NN L.r.toNat L.pp
        L.ol.toNat = some (bytesAt t'.mem L.out L.ol.toNat) := by
  refine WP.seq (WP.mono (step1_ok hv hsp hd name hL hc he) fun t₁ ⟨hc₁, h1, hx⟩ => ?_)
  refine WP.seq (WP.mono (start_ok hL hc₁ hx) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (loop_ok hL h₂) fun t₃ h₃ => ?_)
  refine WP.mono (step3_ok hv hsp hd name hL h₃) fun t₄ ⟨hc₄, hp⟩ => ⟨hc₄, ?_⟩
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  refine Whole.scrypt_eq hL.valid (B := bytesAt t₁.mem L.b (L.blen.toNat * 128)) (by rw [e]; exact h1) ?_
  refine Eq.trans (congrArg (fun x => Spec.Pbkdf2.pbkdf2HmacSha256 _ x 1 _) ?_) hp
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [X_of hL h1 hk, Whole.chunk_bytesAt _ _ (blk_le' hL hk)]

end

/-! ## The whole function -/

theorem push_entry (s : State) : Entry (lay s) (pushed pushRs s) :=
  ⟨pushed_gpr _ _ (by decide), pushed_gpr _ _ (by decide), pushed_gpr _ _ (by decide),
    pushed_gpr _ _ (by decide), pushed_gpr _ _ (by decide)⟩

theorem pop_rsp (B : Addr) : B + BitVec.ofNat 64 32 + BitVec.ofNat 64 (8 * 7) = B + BitVec.ofNat 64 88 := by
  rw [add_add]

theorem ne_cs {r d : Reg} (hr : r ∈ calleeSaved) (hd : d ∉ calleeSaved) : r ≠ d :=
  fun e => hd (e ▸ hr)


section
variable {pbk : Prog isa} (hv : Verified X86_64.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract X86_64.abi 24))
  (hsp : NoSp pbk) (hd : pbk.depth ≤ 3) (name : String)
include hv hsp hd

/-- `vg_scrypt` meets `scryptX86_64` and the calling convention but for MXCSR. -/
theorem scrypt_ok {s : State} (h : Proof.Scrypt.scryptX86_64.pre s) :
    WP isa (scrypt name pbk) s fun s' => gprPreserved s s' ∧ Proof.Scrypt.scryptX86_64.post s s' := by
  have hL := lay_ok h
  have hc := push_ctx h
  have he := push_entry s
  refine WP.frame (rs := pushRs) (by decide) (by decide) (by decide)
    (by show 8 * 7 ≤ _; have := h.1; omega)
    (WP.mono (body_scrypt_ok hv hsp hd name hL hc he) fun u ⟨hu, ho⟩ =>
      ⟨hu.rsp.trans hc.rsp.symm, hu.wr.trans hc.wr.symm, ?_, ?_⟩)
  · have hrsp : (popped .rax pushRs.length u).gpr .rsp = s.gpr .rsp := by
      rw [popped_rsp, hu.rsp, show pushRs.length = 7 from rfl, pop_rsp, lay_ret]
    refine ⟨fun r hr => ?_, ?_⟩
    · by_cases hr' : r = .rsp
      · subst hr'; exact hrsp
      · rw [popped_gpr _ _ _ hr' (ne_cs hr (by decide)), hu.cs r hr hr']
    · rw [popped_mem]
      have hnB := hL.nB
      refine hu.frame.readW (r := (lay s).RET) ?_ ?_ (by decide)
      · rw [Lay.RET, lay_ret]; exact Region.contains_self _ _
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl | rfl | rfl | rfl)
        exacts [hL.rb, hL.rv, hL.rc, hL.ro, Offset.disjoint_base _ (by omega) (by omega)]
  · simp only [Proof.Scrypt.scryptX86_64, popped_mem]
    exact ho

/-- `vg_scrypt` meets `scryptX86_64` and the calling convention, if no
instruction (of it or the functions it calls) loads MXCSR. -/
theorem scrypt_correct (hmx : (scrypt name pbk).allInstrs (fun i => !loadsMxcsr i) = true) (s : State)
    (h : Proof.Scrypt.scryptX86_64.pre s) :
    ∃ t s', Exec isa (scrypt name pbk) s t s' ∧ abiPreserved s s' ∧ Proof.Scrypt.scryptX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := scrypt_ok hv hsp hd name h
  exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hp⟩

end

end VG.Proof.Scrypt.X86_64.Whole

end

section

/-!
# scrypt on x86-64: constant time, up to the indices `j`

Two runs whose public data agree have the same layout, so between the frame's
push and pop they are related by `Two`: both satisfy `Ctx` with that layout
(and `Φ`, what the next piece needs), whatever their secrets, and the indices
of all the scryptROMix calls agree (`LeakEq`, from the contract's leakage).
The blocks address only the stack, from `rsp` (the taint analysis); each call
is of constant-time code whose public data agree (`RelCT.callEx`): for PBKDF2
its pointers and lengths, for scryptROMix also the indices of its block, which
`LeakEq` gives (`leak_X`); the loop's branch agrees since both runs count the
same blocks.
-/

namespace VG.Proof.Scrypt.X86_64.Whole

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt roMixIndices)

/-- The indices of every scryptROMix agree in two runs from `m₁` and `m₂`. -/
def LeakEq (L : Lay) (m₁ m₂ : Mem) : Prop :=
  (Spec.Scrypt.blocks (bytesAt m₁ L.pw L.pwl.toNat) (bytesAt m₁ L.salt L.sl.toNat) L.r.toNat L.pp).flatMap
      (roMixIndices L.r.toNat L.NN) =
    (Spec.Scrypt.blocks (bytesAt m₂ L.pw L.pwl.toNat) (bytesAt m₂ L.salt L.sl.toNat) L.r.toNat L.pp).flatMap
      (roMixIndices L.r.toNat L.NN)

theorem leak_X {L : Lay} {m₁ m₂ : Mem} (h : LeakEq L m₁ m₂) {k : Nat} (hk : k < L.pp) :
    roMixIndices L.r.toNat L.NN (X L m₁ k) = roMixIndices L.r.toNat L.NN (X L m₂ k) := by
  have h₁ : k < (Spec.Scrypt.blocks (bytesAt m₁ L.pw L.pwl.toNat) (bytesAt m₁ L.salt L.sl.toNat)
      L.r.toNat L.pp).length := by rw [Whole.blocks_length]; exact hk
  have h₂ : k < (Spec.Scrypt.blocks (bytesAt m₂ L.pw L.pwl.toNat) (bytesAt m₂ L.salt L.sl.toNat)
      L.r.toNat L.pp).length := by rw [Whole.blocks_length]; exact hk
  simp only [X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂,
    Option.getD_some]
  exact Whole.indices_eq h h₁ h₂

/-- What each of two runs has, between the frame's push and pop. -/
abbrev Env := Lay × (Reg → BitVec 64) × (Reg → BitVec 64) × Mem × Mem

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

theorem rsp_two {L : Lay} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem}
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) : t₁.gpr .rsp = t₂.gpr .rsp :=
  c₁.rsp.trans c₂.rsp.symm

/-- A block whose addresses depend only on `rsp`, with what it establishes. -/
theorem two_blk {is : List Instr} {Φ Ψ : Lay → Mem → State → Prop}
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rsp]) (.block is) hc).isSome = true)
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → Ctx L g m₀ t → Φ L m₀ t →
      WP isa (.block is) t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) (.block is) (Two Ψ) :=
  two_wp (RelCT.taint (A := taint) (Taint.ofRegs [.rsp])
    (fun _ _ ⟨_, _, _, c₁, c₂, _, _⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact rsp_two c₁ c₂) h) hw

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
    (hwsub : ∀ (L : Lay) m₀ (t : State), L.Ok → Φ L m₀ t → ∀ r ∈ wr L, InBuf L r)
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → Ctx L g m₀ t → Φ L m₀ t →
      WP isa (.call n c) t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) (.call n c) (Two Ψ) :=
  two_wp (RelCT.callEx hv hct fun _ _ ⟨⟨L, _⟩, hL, hk, c₁, c₂, f₁, f₂⟩ =>
    ⟨rd L, wr L, rd L, wr L, hpre _ _ _ _ hL c₁ f₁, hpre _ _ _ _ hL c₂ f₂,
      hpub _ _ _ _ _ _ _ hL hk c₁ c₂ f₁ f₂, (covers c₁ (hsub L _ _ hL f₁) (hwsub L _ _ hL f₁)).1,
      (covers c₁ (hsub L _ _ hL f₁) (hwsub L _ _ hL f₁)).2,
      (covers c₂ (hsub L _ _ hL f₂) (hwsub L _ _ hL f₂)).1,
      (covers c₂ (hsub L _ _ hL f₂) (hwsub L _ _ hL f₂)).2, rsp_two c₁ c₂⟩) hw

/-! ## The calls -/

theorem pbk_pub_two {L : Lay} (hL : L.Ok) {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem} {t₁ t₂ : State}
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) {salt : Addr} {sl : BitVec 64} {out : Addr}
    {ol : BitVec 64} (a₁ : PbkArgs L salt sl out ol t₁) (a₂ : PbkArgs L salt sl out ol t₂) :
    pbkK.pub (t₁.callEntry.withRegions (pbkRd L salt sl) (pbkWr L out ol))
      (t₂.callEntry.withRegions (pbkRd L salt sl) (pbkWr L out ol)) := by
  simp only [pbkK, Proof.Pbkdf2.Md.X86_64.pbkG, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
    gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
    gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp),
    gpr_ce _ _ _ (by decide : Reg.r9 ≠ .rsp), a₁.rdi, a₁.rsi, a₁.rdx, a₁.rcx, a₁.r8, a₁.r9, a₂.rdi,
    a₂.rsi, a₂.rdx, a₂.rcx, a₂.r8, a₂.r9, pbk_e0 hL c₁ a₁, pbk_e0 hL c₂ a₂, pbk_e1 hL c₁ a₁,
    pbk_e1 hL c₂ a₂, c₁.ce_rsp, c₂.ce_rsp, and_self]

/-- The block ROMix works on in iteration `i`, on entry to it. -/
theorem romix_bytes {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {m₀ : Mem} {t : State}
    (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.pp) (hb : InvB L m₀ i t) (rd wr : List Region) :
    bytesAt (t.callEntry.withRegions rd wr).mem (blkAt L i) (128 * L.r.toNat) = X L m₀ i := by
  rw [State.withRegions_mem, ce_bytesAt t (by
      rw [hc.ret]; exact hL.stk_in (by omega) (by simpa [Nat.mul_comm] using blk_in hL hi))
    (by have := hL.blen_lt; have := blk_le hL hi; omega), hb.blks i hi]
  simp only [Nat.lt_irrefl, ite_false]

theorem romix_pub_two {L : Lay} (hL : L.Ok) {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem} {t₁ t₂ : State}
    (hk : LeakEq L m₁ m₂) (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) {i : Nat} (hi : i < L.pp)
    (b₁ : InvB L m₁ i t₁) (b₂ : InvB L m₂ i t₂) (a₁ : RomixArgs L (blkAt L i) t₁)
    (a₂ : RomixArgs L (blkAt L i) t₂) :
    Proof.Scrypt.roMixX86_64.pub (t₁.callEntry.withRegions [] (romixWr L i))
      (t₂.callEntry.withRegions [] (romixWr L i)) := by
  simp only [Proof.Scrypt.roMixX86_64, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
    gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
    gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp),
    gpr_ce _ _ _ (by decide : Reg.r9 ≠ .rsp), a₁.rdi, a₁.rsi, a₁.rdx, a₁.rcx, a₁.r8, a₁.r9, a₂.rdi,
    a₂.rsi, a₂.rdx, a₂.rcx, a₂.r8, a₂.r9, c₁.ce_rsp, c₂.ce_rsp, true_and,
    romix_bytes hL c₁ hi b₁, romix_bytes hL c₂ hi b₂]
  exact leak_X hk hi

/-! ## The pieces -/

/-- Iteration `pp - n` of the loop is next. -/
abbrev LoopAt (n : Nat) (L : Lay) (m₀ : Mem) (t : State) : Prop :=
  0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n) t

theorem body_ct (n : Nat) :
    RelCT isa (Two (LoopAt n)) (.seq (.block romixArgs) (.seq (.call "vg_scrypt_romix"
      Impl.Scrypt.X86_64.roMix) (.block nextBlock)))
      (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n + 1) t ∧
        t.zf = some (decide (L.pp - n + 1 = L.pp))) := by
  have a : RelCT isa (Two (LoopAt n)) (.block romixArgs) (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧
      InvB L m₀ (L.pp - n) t ∧ RomixArgs L (blkAt L (L.pp - n)) t) :=
    two_blk (by taint_decide) fun _ _ _ _ hL hc ⟨h0, hn, hb⟩ =>
      WP.mono (romixArgs_ok hL hc hb.cur) fun _ ⟨hc', hm, ha⟩ =>
        ⟨hc', h0, hn, ⟨by rw [hm]; exact hb.cur, by rw [hm]; exact hb.blks⟩, ha⟩
  have b : RelCT isa (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n) t ∧
      RomixArgs L (blkAt L (L.pp - n)) t) (.call "vg_scrypt_romix" Impl.Scrypt.X86_64.roMix)
      (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ Mid L m₀ (L.pp - n) t) :=
    two_call RoMix.roMix_correct RoMix.roMix_ct (fun _ => []) (fun L => romixWr L (L.pp - n))
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
    two_blk (by taint_decide) fun _ _ _ _ hL hc ⟨h0, hn, hm⟩ =>
      WP.mono (next_step hL (by omega) hc hm) fun _ ⟨hc', hb, hz⟩ => ⟨hc', h0, hn, hb, hz⟩
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
variable {pbk : Prog isa} (hv : Verified X86_64.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract X86_64.abi 24))
  (hsp : NoSp pbk) (hd : pbk.depth ≤ 3) (name : String)
include hv hsp hd

theorem scryptBody_ct : RelCT isa (Two fun L _ t => Entry L t) (scryptBody name pbk) fun _ _ => True := by
  have p1a : RelCT isa (Two fun L _ t => Entry L t) (.block pbk1Args)
      (Two fun L _ t => PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t) :=
    two_blk (by taint_decide) fun _ _ _ _ hL hc he =>
      WP.mono (pbk1Args_ok hL hc he) fun _ ⟨hc', ha, _⟩ => ⟨hc', ha⟩
  have p1c : RelCT isa (Two fun L _ t => PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t)
      (.call name pbk)
      (Two fun L m₀ t => ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k) :=
    two_call (pbk_correct hv) (pbk_ct hv) (fun L => pbkRd L L.salt L.sl)
      (fun L => pbkWr L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)))
      (fun _ _ _ _ hL hc ha => pbk_pre' hL hc ha (pbk1_regions hL))
      (fun _ _ _ _ _ _ _ hL _ c₁ c₂ a₁ a₂ => pbk_pub_two hL c₁ c₂ a₁ a₂)
      (fun _ _ _ hL _ => pbk_sub hL (pbk1_regions hL)) (fun _ _ _ hL _ => pbk_wsub hL (pbk1_regions hL))
      (fun _ _ _ _ hL hc ha =>
        WP.mono (pbk1_call_ok hv hsp hd name hL hc ha) fun _ ⟨hc', _, hx⟩ => ⟨hc', hx⟩)
  have c0 : RelCT isa (Two fun L m₀ t => ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k)
      (.block cur0) (Two fun L m₀ t => InvB L m₀ 0 t) :=
    two_blk (by taint_decide) fun _ _ _ _ hL hc hx => start_ok hL hc hx
  have p2a : RelCT isa (Two fun L m₀ t => InvB L m₀ L.pp t) (.block pbk2Args)
      (Two fun L _ t => PbkArgs L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol t) :=
    two_blk (by taint_decide) fun _ _ _ _ hL hc _ =>
      WP.mono (pbk2Args_ok hL hc) fun _ ⟨hc', ha, _⟩ => ⟨hc', ha⟩
  have p2c : RelCT isa (Two fun L _ t => PbkArgs L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol t)
      (.call name pbk) (Two fun _ _ _ => True) :=
    two_call (pbk_correct hv) (pbk_ct hv) (fun L => pbkRd L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)))
      (fun L => pbkWr L L.out L.ol)
      (fun _ _ _ _ hL hc ha => pbk_pre' hL hc ha (pbk2_regions hL))
      (fun _ _ _ _ _ _ _ hL _ c₁ c₂ a₁ a₂ => pbk_pub_two hL c₁ c₂ a₁ a₂)
      (fun _ _ _ hL _ => pbk_sub hL (pbk2_regions hL)) (fun _ _ _ hL _ => pbk_wsub hL (pbk2_regions hL))
      (fun _ _ _ _ hL hc ha =>
        WP.mono (pbk_call hv hsp hd name hL hc ha (pbk2_regions hL)) fun _ h => ⟨h.1, trivial⟩)
  exact ((p1a.seq p1c).seq (c0.seq (loop_ct.seq (p2a.seq p2c)))).mono (fun _ _ h => h)
    fun _ _ _ => trivial

theorem scrypt_ct :
    ConstantTime isa Proof.Scrypt.scryptX86_64.pre Proof.Scrypt.scryptX86_64.pub (scrypt name pbk) := by
  refine RelCT.constantTime (RelCT.frame (fun _ _ h => h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (RelCT.mono (scryptBody_ct hv hsp hd name) ?_ fun _ _ _ => trivial))
  rintro _ _ ⟨s₁, s₂, ⟨h₁, h₂, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, hsp', hlk⟩, rfl, rfl⟩
  have e : lay s₂ = lay s₁ := by
    simp only [lay, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, hsp']
  refine ⟨⟨lay s₁, s₁.gpr, s₂.gpr, s₁.mem, s₂.mem⟩, lay_ok h₁, ?_, push_ctx h₁, e ▸ push_ctx h₂,
    push_entry s₁, e ▸ push_entry s₂⟩
  rw [← hdi, ← hsi, ← hdx, ← hcx, ← h8, ← a0, ← a2] at hlk
  exact hlk

end

end VG.Proof.Scrypt.X86_64.Whole

end

/-!
# scrypt on x86-64: the shared contract

`vg_scrypt`, calling any implementation of PBKDF2-HMAC-SHA256 verified against
its shared contract, is verified against `Spec.Scrypt.scryptContract` for the
88 bytes of stack its frame and calls use (`scrypt_verified_of`); for the
PBKDF2 made with an implementation `c` of SHA-256's compression function
(`scrypt_verified`), whose code never writes `rsp` but by the frame
(`scrypt_spSafe`).
-/

namespace VG.Proof.Scrypt.X86_64.Whole

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (core core_pbkdf2 nosp_of)

/-- A state satisfying the precondition: `N = 2`, `r = 1`, `p = 1`, a
one-byte key and an empty password and salt; the stack arguments are the
bytes at `0x90008`. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x10000 | .rdx => 0x20000 | .r8 => 1 | .r9 => 0x30000 | .rsp => 0x90000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x90008 then 1 else if a = 0x90012 then 4 else if a = 0x90018 then 2
    else if a = 0x90022 then 5 else if a = 0x90028 then 17 else if a = 0x90032 then 6
    else if a = 0x90038 then 1 else 0
  rd := [⟨0x10000, 0⟩, ⟨0x20000, 0⟩, ⟨0x90008, 56⟩]
  wr := [⟨0x30000, 128⟩, ⟨0x40000, 256⟩, ⟨0x50000, 2176⟩, ⟨0x60000, 1⟩]

theorem scrypt_implies :
    Proof.Scrypt.scryptX86_64.Implies (Spec.Scrypt.scryptContract X86_64.abi 88) := by
  exact
    { pre := by
        intro s h
        sig_pre [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86_64, X86_64.abi,
          X86_64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at h
        sig_split h
        sig_reduce [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86_64, X86_64.abi,
          X86_64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | with_reducible exact Region.Disjoint.symm ‹_›
      post := by
        rintro s s' - h
        sig_post [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86_64,
          X86_64.abi, X86_64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
        sig_reduce [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86_64,
          X86_64.abi, X86_64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at h
        exact h
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86_64,
          X86_64.abi, X86_64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at h
        sig_split h
        rename_i hrsp hlk h1 h2 h3 h4 h5 h6 a0 a1 a2 a3 a4 a5
        exact ⟨h1, h2, h3, h4, h5, h6, a0, a1, a2, a3, a4, a5, h, hrsp, hlk⟩
      sat := by
        sig_implies_sat [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, X86_64.abi, X86_64.argRegs,
          _root_.List.range, _root_.List.range.loop, List.append_eq, satState] [satState] using satState }

section
variable {pbk : Prog isa} (hv : Verified X86_64.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract X86_64.abi 24))
  (hsp : NoSp pbk) (hd : pbk.depth ≤ 3) (name : String)
include hv hsp hd

/-- `vg_scrypt`, calling the implementation `pbk` of PBKDF2 named `name`, if
no instruction of it (or of the functions it calls) loads MXCSR. -/
theorem scrypt_verified_of (hmx : (scrypt name pbk).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (scrypt name pbk) (Spec.Scrypt.scryptContract X86_64.abi 88) :=
  Verified.of_correct (scrypt_correct hv hsp hd name hmx) (scrypt_ct hv hsp hd name) scrypt_implies

end

/-! ## With PBKDF2 made with an implementation of SHA-256's compression function -/

open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

/-- How deeply calls nest in `pbkdf2`, from its own code. -/
theorem core_pbkdf2_depth {H : Hash} (hc : H.compC.depth = 0) (hi : H.initC.depth = 0)
    (h : (core H).pbkdf2.depth ≤ 3) : H.pbkdf2.depth ≤ 3 := by
  simp only [Hash.pbkdf2, Hash.key, Hash.hashKey, Hash.setup, Hash.block, Hash.outLen, Hash.outLoop,
    Hash.hmacInit, Hash.hmacFin, Hash.iterate, Impl.Pbkdf2.X86_64.iterate, Impl.Pbkdf2.X86_64.body,
    Impl.Pbkdf2.X86_64.compressBlock, Hash.updC, Hash.finC, Hash.stream, Hash.initKeys,
    Impl.Pbkdf2.Md.X86_64.Stream.callInit, Impl.Pbkdf2.Md.X86_64.Stream.callFin,
    Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody, Impl.MdStream.X86_64.updateTail,
    Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    core, Code.depth, hc, hi] at h ⊢
  exact h

variable (c : Proof.Sha256.X86_64.Compress)

/-- PBKDF2-HMAC-SHA256 made with `c`. -/
abbrev pbkOf : Prog isa := (Proof.Pbkdf2.Md.X86_64.Sha256.hash c).pbkdf2

/-- Its name. -/
abbrev pbkName : String := Spec.Hmac.sha256I.pbkdf2ScratchApi.name ++ c.suffix

theorem pbk_verified :
    Verified X86_64.target (pbkOf c) (Spec.Hmac.sha256I.pbkdf2ScratchContract X86_64.abi 24) :=
  (Proof.Pbkdf2.Md.X86_64.Sha256.variant c).pbkdf2

theorem pbk_nosp : NoSp (pbkOf c) :=
  nosp_of (core_pbkdf2 (Proof.Pbkdf2.Md.X86_64.Sha256.callees c).cNs
    (Proof.Pbkdf2.Md.X86_64.Sha256.callees c).iNs
    (by decide +kernel : Proof.Pbkdf2.Md.X86_64.Sha256.coreH.pbkdf2.allInstrs
      (fun i => !Taint.clobbers i .rsp) = true))

theorem pbk_depth : (pbkOf c).depth ≤ 3 :=
  core_pbkdf2_depth (Proof.Pbkdf2.Md.X86_64.Sha256.callees c).cD
    (Proof.Pbkdf2.Md.X86_64.Sha256.callees c).iD
    (by decide +kernel : Proof.Pbkdf2.Md.X86_64.Sha256.coreH.pbkdf2.depth ≤ 3)

theorem pbk_mx : (pbkOf c).allInstrs (fun i => !loadsMxcsr i) = true :=
  core_pbkdf2 (Proof.Pbkdf2.Md.X86_64.Sha256.callees c).cMx (Proof.Pbkdf2.Md.X86_64.Sha256.callees c).iMx
    Proof.Pbkdf2.Md.X86_64.Sha256.coreOK.pbkMx

theorem scrypt_mx : (scrypt (pbkName c) (pbkOf c)).allInstrs (fun i => !loadsMxcsr i) = true := by
  have hr : Impl.Scrypt.X86_64.roMix.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide
  simp only [scrypt, scryptBody, pbkCall, romixLoop, Code.allInstrs, pbk_mx c, hr, Bool.and_true,
    Bool.true_and]
  decide

/-- `vg_scrypt` made with `c`. -/
theorem scrypt_verified :
    Verified X86_64.target (scrypt (pbkName c) (pbkOf c)) (Spec.Scrypt.scryptContract X86_64.abi 88) :=
  scrypt_verified_of (pbk_verified c) (pbk_nosp c) (pbk_depth c) (pbkName c) (scrypt_mx c)

/-- No instruction writes `rsp` but the frame's push and pop. -/
theorem scrypt_spSafe : (scrypt (pbkName c) (pbkOf c)).all (fun i => !isa.writesSp i) = true := by
  have hp : (pbkOf c).all (fun i => !isa.writesSp i) = true :=
    (Proof.Pbkdf2.Md.X86_64.Sha256.variant c).pbkdf2Sp
  have hr : Impl.Scrypt.X86_64.roMix.all (fun i => !isa.writesSp i) = true :=
    Code.all_of_allInstrs (by lit_decide)
  simp only [scrypt, scryptBody, pbkCall, romixLoop, Code.all, hp, hr, Bool.and_true, Bool.true_and]
  decide

end VG.Proof.Scrypt.X86_64.Whole
