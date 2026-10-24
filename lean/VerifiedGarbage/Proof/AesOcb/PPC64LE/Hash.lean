module

public import VerifiedGarbage.Proof.AesOcb.PPC64LE.HashChunk
import VerifiedGarbage.Proof.AesOcb.PPC64LE.HashFill
import VerifiedGarbage.Proof.AesOcb.PPC64LE.Nonce
import VerifiedGarbage.Proof.AesOcb.PPC64LE.PadTo
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-OCB on PPC64LE: `HASH` (`hash`)

Untrusted: everything here is checked by Lean. `hash` zeroes the sum and the
offset and leaves `HInv` at 0 (`hashHead_ok`), runs the chunks
(`hashLoop_ok`, `hashChunk_ok`), and adds the padded rest of the associated
data, if any (`hashRest_ok`), leaving `HASH(K, A)` at `W + sumO`
(`hash_ok`, `Proof.Ocb.hash_eq`). As on AArch64
(`Proof/AesOcb/AArch64/Hash.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Impl.AesOcb.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem blockAt lAt ntz ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt hsum blockAtMem_frame)
open VG.Proof.AesGcm.PPC64LE (in_left in_off eval_zero Keeps and15 shr4)
open VG.Proof.ChaCha20Poly1305.PPC64LE renaming wp_or → cwp_or, wp_lsr → cwp_lsr, wp_std → cwp_std,
  wp_li → cwp_li, wp_and → cwp_and

/-- What `HASH` leaves. -/
structure HashOut (V : Reg → BitVec 64) (sp : Addr) (ciph : Cipher) (l : Block) (a : List Byte) (s₀ t : State) :
    Prop where
  env : Env V sp t
  frame : Frame (hashR (V .r31)) s₀.mem t.mem
  sum : blockAtMem t.mem (V .r31 + BitVec.ofNat 64 sumO) = Spec.Ocb.hash ciph l a
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr

/-- The padded rest of the associated data, after its `m` whole blocks. -/
theorem hashRest_ok {V : Reg → BitVec 64} {sp : Addr} {D : Addr} {n R : Nat} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : HCtx (V .r29) (V .r31) D n R ciph l A a s₀)
    (h28 : V .r28 = BitVec.ofNat 64 R) {t : State} (H : HInv V sp ciph l A a s₀ t (a.length / 16))
    (hr : 0 < a.length % 16) (h25 : t.gpr .r25 = BitVec.ofNat 64 (a.length % 16)) :
    WP isa hashRest t (HashOut V sp ciph l a s₀) := by
  have L := C.lay
  have E := H.env
  have hs := C.short
  generalize hm : a.length / 16 = m at H
  have hrest : a.length - 16 * m = a.length % 16 := by omega
  unfold hashRest
  -- `Offset_m ⊕ L_*`
  refine WP.seq (WP.mono (xorB_ok (s := t) (pd := ohO) (qd := 240) (cd := ohO) (by decide) (by decide)
    (by decide) E.r31 E.r29 E.r31 (by decide) (by decide) (by decide) (E.perm.wR (by decide))
    (E.perm.wR (by decide)) (E.perm.kR (by decide)) (E.perm.kR (by decide)) (E.perm.wW (by decide))
    (E.perm.wW (by decide)) (Offset.sep _ (by decide) (by decide) (by decide))
    ((L.k_w' (a := 248) (n := 8) (d := 272) (k := 8) (by decide) (by decide)).sep (Region.contains_self _ _)
      (Region.contains_self _ _))) fun t₁ B₁ => ?_)
  have E₁ := E.others B₁.gpr B₁.sp B₁.rd B₁.wr
  have oh₁ : blockAtMem t₁.mem (V .r31 + BitVec.ofNat 64 ohO) = offAt 0 l m ^^^ l := by
    rw [B₁.val, H.oh, ← C.lstar' (hashR_mut H.frame)]; rfl
  have fr₁ : Frame (hashR (V .r31)) s₀.mem t₁.mem := H.frame.trans (B₁.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact in_hashR (e := 272) (n := 16) (by simp) (by decide) (by decide))
  -- `pad(A_*)`
  have hB := C.buf.slice (a := 16 * m) (k := a.length % 16) (by omega)
  have hS : Covers [⟨A + BitVec.ofNat 64 (16 * m), a.length % 16⟩] (t₁.rd ++ t₁.wr) := by
    rw [B₁.rd, B₁.wr, H.rd, H.wr]; exact hB.rd
  have hSD : (⟨A + BitVec.ofNat 64 (16 * m), a.length % 16⟩ : Region).Disjoint
      ⟨V .r31 + BitVec.ofNat 64 bufO, 16⟩ :=
    hB.w.sub_right (Lay.wSub (by decide))
  have hrestb : bytesAt t₁.mem (A + BitVec.ofNat 64 (16 * m)) (a.length % 16) = a.drop (16 * m) := by
    have hd := Proof.Ocb.bytesAt_drop s₀.mem A (a := 16 * m) (n := a.length) (by omega)
    rw [C.aad, hrest] at hd
    rw [Proof.Cmac.bytesAt_frame (hashR_mut (D := D) (n := n) fr₁) (fun r hr =>
      (C.a_mut r hr).sub_left (Offset.sub_base A (by omega))) (by omega), hd]
  refine WP.seq (WP.mono (padTo_ok E₁.r31 E₁.perm.w hr (by omega) (by decide)
    (by rw [B₁.gpr _ (by decide), H.r24]) (by rw [B₁.gpr _ (by decide), h25]) hS hSD) fun t₂ P₂ => ?_)
  have pad₂ := P₂.val
  rw [hrestb] at pad₂
  have E₂ := E₁.others P₂.gpr P₂.sp P₂.rd P₂.wr
  have oh₂ : blockAtMem t₂.mem (V .r31 + BitVec.ofNat 64 ohO) = offAt 0 l m ^^^ l := by
    rw [blockAtMem_frame P₂.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide), oh₁]
  -- XORed with the offset
  refine WP.seq (WP.mono (xorB_ok (s := t₂) (pd := bufO) (qd := ohO) (cd := bufO) (by decide) (by decide)
    (by decide) E₂.r31 E₂.r31 E₂.r31 (by decide) (by decide) (by decide) (E₂.perm.wR (by decide))
    (E₂.perm.wR (by decide)) (E₂.perm.wR (by decide)) (E₂.perm.wR (by decide)) (E₂.perm.wW (by decide))
    (E₂.perm.wW (by decide)) (Offset.sep _ (by decide) (by decide) (by decide))
    (Offset.sep _ (by decide) (by decide) (by decide))) fun t₃ B₃ => ?_)
  have E₃ := E₂.others B₃.gpr B₃.sp B₃.rd B₃.wr
  have buf₃ : blockAtMem t₃.mem (V .r31 + BitVec.ofNat 64 bufO) = pad (a.drop (16 * m)) ^^^ (offAt 0 l m ^^^ l) := by
    rw [B₃.val, pad₂, oh₂]
  have fr₃ : Frame (hashR (V .r31)) s₀.mem t₃.mem := fr₁.trans ((P₂.frame.trans B₃.frame).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact in_hashR (e := 384) (n := 2176) (by simp) (by decide) (by decide))
  -- enciphered
  refine WP.seq (WP.mono (encOne_ok L C.rounds h28 E₃ (d := bufO) (by decide)) fun t₄ P₄ => ?_)
  have E₄ := P₄.env E₃
  have buf₄ : blockAtMem t₄.mem (V .r31 + BitVec.ofNat 64 bufO) =
      ciph (pad (a.drop (16 * m)) ^^^ (offAt 0 l m ^^^ l)) := by
    rw [P₄.enc0, buf₃]
    exact congrFun (C.ciph' (hashR_mut fr₃)) _
  have fr₄ : Frame (hashR (V .r31)) s₀.mem t₄.mem := fr₃.trans (P₄.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact in_hashR (e := 384) (n := 2176) (by simp) (by decide) (by decide)
    · exact in_hashR (e := 384) (n := 2176) (by simp) (by decide) (by decide))
  have kSum : ∀ {m m' : Mem}, Frame [⟨V .r31 + BitVec.ofNat 64 bufO, 16⟩] m m' →
      blockAtMem m' (V .r31 + BitVec.ofNat 64 sumO) = blockAtMem m (V .r31 + BitVec.ofNat 64 sumO) := fun h =>
    blockAtMem_frame h fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have sum₄ : blockAtMem t₄.mem (V .r31 + BitVec.ofNat 64 sumO) = hsum ciph l a m := by
    rw [blockAtMem_frame P₄.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)),
      kSum B₃.frame, kSum P₂.frame, blockAtMem_frame B₁.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), H.sum]
  -- added to the sum
  refine WP.mono (xorB_ok (s := t₄) (pd := sumO) (qd := bufO) (cd := sumO) (by decide) (by decide)
    (by decide) E₄.r31 E₄.r31 E₄.r31 (by decide) (by decide) (by decide) (E₄.perm.wR (by decide))
    (E₄.perm.wR (by decide)) (E₄.perm.wR (by decide)) (E₄.perm.wR (by decide)) (E₄.perm.wW (by decide))
    (E₄.perm.wW (by decide)) (Offset.sep _ (by decide) (by decide) (by decide))
    (Offset.sep _ (by decide) (by decide) (by decide))) fun t₅ B₅ => ?_
  refine ⟨E₄.others B₅.gpr B₅.sp B₅.rd B₅.wr, fr₄.trans (B₅.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact in_hashR (e := 48) (n := 16) (by simp) (by decide) (by decide)), ?_,
    by rw [B₅.rd, P₄.rd, B₃.rd, P₂.rd, B₁.rd, H.rd], by rw [B₅.wr, P₄.wr, B₃.wr, P₂.wr, B₁.wr, H.wr]⟩
  rw [B₅.val, sum₄, buf₄, Proof.Ocb.hash_eq]
  have hlen : (a.drop (16 * m)).length = a.length % 16 := by simp; omega
  simp only [hlen, show a.length % 16 > 0 from hr, ↓reduceIte, hm]

/-- `HASH(K, A)` with `aad` and `aad_len` in `r21` and `r22`: `HInv` at 0. -/
theorem hashHead_ok {V : Reg → BitVec 64} {sp : Addr} {D : Addr} {n R : Nat} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : HCtx (V .r29) (V .r31) D n R ciph l A a s₀) (E : Env V sp s₀)
    (h21 : V .r21 = A) (h22 : V .r22 = BitVec.ofNat 64 a.length)
    (hl0 : blockAtMem s₀.mem (V .r31 + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa (.block (zero16 sumO ++ zero16 ohO ++ ([Impl.AesGcm.PPC64LE.mov .r24 .r21, .lsr .d .r3 .r22 4,
      .store .d .r3 .r31 hlO, .li .r26 1] : List Instr))) s₀ fun s => HInv V sp ciph l A a s₀ s 0 := by
  have L := C.lay
  have hs := C.short
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (zero16_ok (s := s₀) (d := sumO) (by decide) E.r31 (E.perm.wW (by decide))
    (E.perm.wW (by decide))) fun s₁ B₁ => ?_)
  have E₁ := E.others B₁.gpr B₁.sp B₁.rd B₁.wr
  refine WP.block_append (WP.mono (zero16_ok (s := s₁) (d := ohO) (by decide) E₁.r31 (E₁.perm.wW (by decide))
    (E₁.perm.wW (by decide))) fun s₂ B₂ => ?_)
  have E₂ := E₁.others B₂.gpr B₂.sp B₂.rd B₂.wr
  refine cwp_or fun s₃ u₃ => cwp_lsr (by decide) fun s₄ u₄ =>
    cwp_std (a := V .r31 + BitVec.ofNat 64 hlO) (by decide) (by decide)
      (by rw [u₄.other _ (by decide), u₃.other _ (by decide), E₂.r31])
      (by rw [u₄.wr, u₃.wr]; exact E₂.perm.wW (by decide)) fun s₅ u₅ => cwp_li (by decide) fun s₆ u₆ =>
    WP.block_nil ?_
  have r3₄ : s₄.gpr .r3 = BitVec.ofNat 64 (a.length / 16) := by
    rw [u₄.gpr, u₃.other _ (by decide), E₂.r22, h22, shr4 hs]
  have f₂ : Frame [⟨V .r31 + BitVec.ofNat 64 sumO, 16⟩, ⟨V .r31 + BitVec.ofNat 64 ohO, 16⟩] s₀.mem s₂.mem :=
    (B₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp))
  have m₆ : s₆.mem = s₂.mem.writeW (V .r31 + BitVec.ofNat 64 hlO) (BitVec.ofNat 64 (a.length / 16)) := by
    rw [u₆.mem, u₅.mem, r3₄, u₄.mem, u₃.mem]
  have f₆ : Frame [⟨V .r31 + BitVec.ofNat 64 hlO, 8⟩] s₂.mem s₆.mem := by
    rw [m₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have kb : ∀ {d : Nat}, (d + 16 ≤ 304 ∨ 312 ≤ d) → d + 16 ≤ 2560 →
      blockAtMem s₆.mem (V .r31 + BitVec.ofNat 64 d) = blockAtMem s₂.mem (V .r31 + BitVec.ofNat 64 d) :=
    fun h₁ h₂ => blockAtMem_frame f₆ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by simp only [hlO]; omega) h₂ (by decide)
  have g₆ : ∀ r, r ∉ [.r0, .r3, .r24, .r26] → s₆.gpr r = s₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other _ hr.2.2.2, u₅.gpr, u₄.other _ hr.2.1, u₃.other _ hr.2.2.1, B₂.gpr r (by simp [hr.1]),
      B₁.gpr r (by simp [hr.1])]
  refine
    { env := E.others g₆ (by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, B₂.sp, B₁.sp])
        (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, B₂.rd, B₁.rd]) (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, B₂.wr, B₁.wr])
      frame := ((f₂.mono (rs' := [⟨V .r31 + BitVec.ofNat 64 sumO, 16⟩, ⟨V .r31 + BitVec.ofNat 64 ohO, 16⟩,
          ⟨V .r31 + BitVec.ofNat 64 hlO, 8⟩]) (by simp)).trans (f₆.mono (by simp))).sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact in_hashR (e := 48) (n := 16) (by simp) (by decide) (by decide)
        · exact in_hashR (e := 272) (n := 16) (by simp) (by decide) (by decide)
        · exact in_hashR (e := 296) (n := 16) (by simp) (by decide) (by decide)
      rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, B₂.rd, B₁.rd]
      wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, B₂.wr, B₁.wr]
      le := Nat.zero_le _
      sum := by
        rw [kb (by decide) (by decide), blockAtMem_frame B₂.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)),
          B₁.val]; rfl
      oh := by rw [kb (by decide) (by decide), B₂.val]; rfl
      r24 := by
        rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.gpr, BitVec.or_self, E₂.r21, h21]
        simp
      r26 := by rw [u₆.gpr]
      r3 := by rw [u₆.other _ (by decide), u₅.gpr, r3₄]; rfl
      hl := by rw [m₆, Mem.readW_writeW_self64]; rfl
      l0 := by
        rw [kb (by decide) (by decide), blockAtMem_frame f₂ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact L.w_w (.inr (by decide)) (by decide) (by decide)
          · exact L.w_w (.inl (by decide)) (by decide) (by decide)), hl0] }

/-- The chunks of `HASH`, from the first. -/
theorem hashLoop_ok {V : Reg → BitVec 64} {sp : Addr} {D : Addr} {n R : Nat} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : HCtx (V .r29) (V .r31) D n R ciph l A a s₀)
    (h28 : V .r28 = BitVec.ofNat 64 R) {t : State} (H₀ : HInv V sp ciph l A a s₀ t 0) (hm : 0 < a.length / 16) :
    WP isa (.loop hashChunk (.nonzero .d .r3)) t fun u => HInv V sp ciph l A a s₀ u (a.length / 16) := by
  have hs := C.short
  refine WP.loop (M := isa)
    (fun (k : Nat) (u : State) => ∃ j, k = a.length / 16 - j ∧ j < a.length / 16 ∧
      HInv V sp ciph l A a s₀ u j) ?_ (a.length / 16 - 0) _ ⟨0, rfl, hm, H₀⟩
  rintro k u ⟨j, rfl, hj, H⟩
  refine WP.mono (hashChunk_ok C h28 H hj) fun u' H' => ?_
  have ev := eval_nonzero H'.r3 (by omega)
  by_cases he : a.length / 16 - (j + min 8 (a.length / 16 - j)) = 0
  · left
    have hje : j + min 8 (a.length / 16 - j) = a.length / 16 := by omega
    exact ⟨ev.trans (by simp [he]), hje ▸ H'⟩
  · right
    exact ⟨ev.trans (by simp [he]), a.length / 16 - (j + min 8 (a.length / 16 - j)), by omega,
      j + min 8 (a.length / 16 - j), rfl, by omega, H'⟩

/-- After the whole blocks: the rest, if any. -/
theorem hashTail_ok {V : Reg → BitVec 64} {sp : Addr} {D : Addr} {n R : Nat} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : HCtx (V .r29) (V .r31) D n R ciph l A a s₀)
    (h28 : V .r28 = BitVec.ofNat 64 R) (h22 : V .r22 = BitVec.ofNat 64 a.length) {t : State}
    (H : HInv V sp ciph l A a s₀ t (a.length / 16)) :
    WP isa (.seq (.block [.li .r0 15, .logic .and .r25 .r22 .r0]) (.ite (.zero .d .r25) (.block []) hashRest)) t
      (HashOut V sp ciph l a s₀) := by
  have hs := C.short
  refine WP.seq (cwp_li (by decide) fun t₁ u₁ => cwp_and fun t₂ u₂ => WP.block_nil ?_)
  have h25 : t₂.gpr .r25 = BitVec.ofNat 64 (a.length % 16) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), H.env.r22, h22, and15, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs]
  have g₂ : ∀ r, r ∉ [.r0, .r25] → t₂.gpr r = t.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₂.other _ hr.2, u₁.other _ hr.1]
  have H₁ : HInv V sp ciph l A a s₀ t₂ (a.length / 16) :=
    { H with
      env := H.env.others g₂ (by rw [u₂.sp, u₁.sp]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
      frame := by rw [u₂.mem, u₁.mem]; exact H.frame
      rd := by rw [u₂.rd, u₁.rd, H.rd]
      wr := by rw [u₂.wr, u₁.wr, H.wr]
      sum := by rw [u₂.mem, u₁.mem, H.sum]
      oh := by rw [u₂.mem, u₁.mem, H.oh]
      r24 := by rw [g₂ _ (by decide), H.r24]
      r26 := by rw [g₂ _ (by decide), H.r26]
      r3 := by rw [g₂ _ (by decide), H.r3]
      hl := by rw [u₂.mem, u₁.mem, H.hl]
      l0 := by rw [u₂.mem, u₁.mem, H.l0] }
  refine WP.ite (decide (a.length % 16 = 0)) (eval_zero h25 (by omega)) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have h0 : a.length % 16 = 0 := of_decide_eq_true hb
    refine ⟨H₁.env, H₁.frame, ?_, H₁.rd, H₁.wr⟩
    rw [H₁.sum, Proof.Ocb.hash_eq]
    have hlen : (a.drop (16 * (a.length / 16))).length = 0 := by simp; omega
    simp [hlen]
  · exact hashRest_ok C h28 H₁ (by have := of_decide_eq_false hb; omega) h25

/-- `HASH(K, A)` to `W + sumO`, with `aad` and `aad_len` in `r21` and `r22`. -/
theorem hash_ok {V : Reg → BitVec 64} {sp : Addr} {D : Addr} {n R : Nat} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : HCtx (V .r29) (V .r31) D n R ciph l A a s₀) (E : Env V sp s₀)
    (h28 : V .r28 = BitVec.ofNat 64 R) (h21 : V .r21 = A) (h22 : V .r22 = BitVec.ofNat 64 a.length)
    (hl0 : blockAtMem s₀.mem (V .r31 + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa Impl.AesOcb.PPC64LE.hash s₀ (HashOut V sp ciph l a s₀) := by
  have hs := C.short
  unfold Impl.AesOcb.PPC64LE.hash
  refine WP.seq (WP.mono (hashHead_ok C E h21 h22 hl0) fun s₃ H₀ => ?_)
  refine WP.seq (WP.mono (?_ : WP isa (.ite (.zero .d .r3) (.block []) (.loop hashChunk (.nonzero .d .r3))) s₃
    fun u => HInv V sp ciph l A a s₀ u (a.length / 16)) fun u H => hashTail_ok C h28 h22 H)
  refine WP.ite (decide (a.length / 16 = 0)) (eval_zero H₀.r3 (by omega)) (fun hb => WP.block_nil ?_)
    (fun hb => hashLoop_ok C h28 H₀ (Nat.pos_of_ne_zero (of_decide_eq_false hb)))
  exact (of_decide_eq_true hb) ▸ H₀

end VG.Proof.AesOcb.PPC64LE
