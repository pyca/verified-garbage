import VerifiedGarbage.Proof.AesOcb.AArch64.HashChunk

/-!
# AES-OCB on AArch64: `HASH` (`hash`)

Untrusted: everything here is checked by Lean. `hash` zeroes the sum and the
offset, loads the associated data and its length from `W`, takes the whole
blocks a chunk at a time (`hashChunk_ok`), and the rest, padded, XORed with
`Offset_m ⊕ L_*` and enciphered (`hashRest_ok`): the sum is §4.1's
`HASH(K, A)` (`hash_ok`, `Proof.Ocb.hash_eq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem blockAt lAt ntz ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt hsum blockAtMem_frame)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (in_left in_off eval_zero eval_nonzero toNat_ofNat_of_lt lsr_ofNat and15)

/-- The padded rest of the associated data, after its `m` whole blocks. -/
theorem hashRest_ok (v : BlocksImpl) {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : HCtx K W D n R ciph l A a s₀) {t : State}
    (H : HInv K W D R n SP ciph l A a s₀ t (a.length / 16)) (hr : 0 < a.length % 16)
    (h24 : t.gpr .x24 = BitVec.ofNat 64 (a.length % 16)) :
    WP isa (hashRest (callees v)) t fun t' => Env K W D R n SP t' ∧ Frame (hashR W) s₀.mem t'.mem ∧
      blockAtMem t'.mem (W + BitVec.ofNat 64 sumO) = Spec.Ocb.hash ciph l a ∧ t'.rd = s₀.rd ∧ t'.wr = s₀.wr := by
  have L := C.lay
  have E := H.env
  have hs := C.short
  generalize hm : a.length / 16 = m at H
  have hrest : a.length - 16 * m = a.length % 16 := by omega
  -- `Offset_m ⊕ L_*`
  obtain ⟨t₁, run₁, B₁⟩ := xor16_ok (s := t) (b := .x20) (a := 240) (d := ohO) (by decide) (by decide) E.x19 E.x20
    (by decide) (by decide) (by decide) (E.perm.kR (by decide)) (E.perm.kR (by decide)) (E.perm.wW (by decide))
    (E.perm.wW (by decide))
  have E₁ := E.others B₁.gpr B₁.sp B₁.rd B₁.wr
  have oh₁ : blockAtMem t₁.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l m ^^^ l := by
    rw [B₁.val, H.oh, ← C.lstar' (hashR_mut H.frame)]; rfl
  have fr₁ : Frame (hashR W) s₀.mem t₁.mem := H.frame.trans (B₁.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩)
  -- `pad(A_*)`
  have hB := C.buf.slice (a := 16 * m) (k := a.length % 16) (by omega)
  have hS : Covers [⟨A + BitVec.ofNat 64 (16 * m), a.length % 16⟩] (t₁.rd ++ t₁.wr) := by
    rw [B₁.rd, B₁.wr, H.rd, H.wr]; exact hB.rd
  have hSD : (⟨A + BitVec.ofNat 64 (16 * m), a.length % 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 bufO, 16⟩ :=
    hB.w.sub_right (Lay.wSub (by decide))
  have hrestb : bytesAt t₁.mem (A + BitVec.ofNat 64 (16 * m)) (a.length % 16) = a.drop (16 * m) := by
    have hd := Proof.Ocb.bytesAt_drop s₀.mem A (a := 16 * m) (n := a.length) (by omega)
    rw [C.aad, hrest] at hd
    rw [Proof.Cmac.bytesAt_frame (hashR_mut (D := D) (n := n) fr₁) (fun r hr =>
      (C.a_mut r hr).sub_left (Offset.sub_base A (by omega))) (by omega), hd]
  unfold hashRest
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (padTo_ok E₁.x19 E₁.perm.w hr (by omega) (by decide)
    (by rw [B₁.gpr _ (by decide), H.x23]) (by rw [B₁.gpr _ (by decide), h24]) hS hSD)
    fun t₂ ⟨fr₂, pad₂, g₂, sp₂, rd₂, wr₂⟩ => ?_)
  rw [hrestb] at pad₂
  have E₂ := E₁.others g₂ sp₂ rd₂ wr₂
  have oh₂ : blockAtMem t₂.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l m ^^^ l := by
    rw [blockAtMem_frame fr₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide), oh₁]
  -- XORed with the offset
  obtain ⟨t₃, run₃, B₃⟩ := xor16_ok (s := t₂) (b := .x19) (a := ohO) (d := bufO) (by decide) (by decide) E₂.x19
    E₂.x19 (by decide) (by decide) (by decide) (E₂.perm.wR (by decide)) (E₂.perm.wR (by decide))
    (E₂.perm.wW (by decide)) (E₂.perm.wW (by decide))
  have E₃ := E₂.others B₃.gpr B₃.sp B₃.rd B₃.wr
  have buf₃ : blockAtMem t₃.mem (W + BitVec.ofNat 64 bufO) = pad (a.drop (16 * m)) ^^^ (offAt 0 l m ^^^ l) := by
    rw [B₃.val, pad₂, oh₂]
  have fr₃ : Frame (hashR W) s₀.mem t₃.mem := fr₁.trans ((fr₂.trans B₃.frame).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp, Offset.sub W (e := 384) (k := 2176) (by decide) (by decide)⟩)
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  -- enciphered
  refine WP.seq (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) (b := v.enc) v.encOk v.encNoFrames L E₃
    C.rounds (oneBlock_ok E₃.x19 bufO (by decide)) (dstW L E₃.perm (d := bufO) (n := 1) (by decide))) fun t₄ P₄ => ?_)
  have E₄ := E₃.of_saved P₄.saved P₄.sp P₄.rd P₄.wr
  have buf₄ : blockAtMem t₄.mem (W + BitVec.ofNat 64 bufO) = ciph (pad (a.drop (16 * m)) ^^^ (offAt 0 l m ^^^ l)) := by
    rw [P₄.enc0, buf₃]
    exact congrFun (C.ciph' (hashR_mut fr₃)) _
  have fr₄ : Frame (hashR W) s₀.mem t₄.mem := fr₃.trans (P₄.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, Offset.sub W (e := 384) (k := 2176) (by decide) (by decide)⟩
    · exact ⟨_, by simp, Offset.sub W (e := 384) (k := 2176) (by decide) (by decide)⟩)
  have kSum : ∀ {u u' : State}, Frame [⟨W + BitVec.ofNat 64 bufO, 16⟩] u.mem u'.mem →
      blockAtMem u'.mem (W + BitVec.ofNat 64 sumO) = blockAtMem u.mem (W + BitVec.ofNat 64 sumO) := fun h =>
    blockAtMem_frame h fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have sum₄ : blockAtMem t₄.mem (W + BitVec.ofNat 64 sumO) = hsum ciph l a m := by
    rw [blockAtMem_frame P₄.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)),
      kSum B₃.frame, kSum fr₂, blockAtMem_frame B₁.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), H.sum]
  -- added to the sum
  obtain ⟨t₅, run₅, B₅⟩ := xor16_ok (s := t₄) (b := .x19) (a := bufO) (d := sumO) (by decide) (by decide) E₄.x19
    E₄.x19 (by decide) (by decide) (by decide) (E₄.perm.wR (by decide)) (E₄.perm.wR (by decide))
    (E₄.perm.wW (by decide)) (E₄.perm.wW (by decide))
  refine WP.of_runBlock ⟨t₅, run₅, E₄.others B₅.gpr B₅.sp B₅.rd B₅.wr, fr₄.trans (B₅.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩), ?_,
    by rw [B₅.rd, P₄.rd, B₃.rd, rd₂, B₁.rd, H.rd], by rw [B₅.wr, P₄.wr, B₃.wr, wr₂, B₁.wr, H.wr]⟩
  rw [B₅.val, sum₄, buf₄, Proof.Ocb.hash_eq]
  have hlen : (a.drop (16 * m)).length = a.length % 16 := by simp; omega
  simp only [hlen, show a.length % 16 > 0 from hr, ↓reduceIte, hm]

/-- The first block of `hash`: the sum and the offset zeroed, the associated
data and its length loaded. -/
theorem hashHead1_ok {K W : Addr} (L : Lay K W) {s₀ : State} (h19 : s₀.gpr .x19 = W)
    (hw : Covers [⟨W, 2560⟩] s₀.wr) {A : Addr} {al : Nat}
    (haad : s₀.mem.readW (W + BitVec.ofNat 64 aadO) 64 = A)
    (halen : s₀.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 al) :
    ∃ s, runBlock isa (zero16 sumO ++ zero16 ohO ++ [ld .x23 .x19 aadO, ld .x26 .x19 alenO]) s₀ = some s ∧
      s.gpr .x23 = A ∧ s.gpr .x26 = BitVec.ofNat 64 al ∧ (∀ r, r ∉ [.x9, .x23, .x26] → s.gpr r = s₀.gpr r) ∧
      Frame [⟨W + BitVec.ofNat 64 sumO, 16⟩, ⟨W + BitVec.ofNat 64 ohO, 16⟩] s₀.mem s.mem ∧
      blockAtMem s.mem (W + BitVec.ofNat 64 sumO) = 0 ∧ blockAtMem s.mem (W + BitVec.ofNat 64 ohO) = 0 ∧
      s.sp = s₀.sp ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  obtain ⟨s₁, run₁, B₁⟩ := zero16_ok (s := s₀) (d := sumO) (by decide) h19 (in_off hw (by decide) (by decide))
    (in_off hw (by decide) (by decide))
  have h19₁ : s₁.gpr .x19 = W := by rw [B₁.gpr _ (by decide), h19]
  obtain ⟨s₂, run₂, B₂⟩ := zero16_ok (s := s₁) (d := ohO) (by decide) h19₁ (by rw [B₁.wr]; exact in_off hw (by decide) (by decide))
    (by rw [B₁.wr]; exact in_off hw (by decide) (by decide))
  have h19₂ : s₂.gpr .x19 = W := by rw [B₂.gpr _ (by decide), h19₁]
  have kA : ∀ {d : Nat}, (d + 8 ≤ 48 ∨ (64 ≤ d ∧ d + 8 ≤ 144) ∨ 160 ≤ d) → d + 8 ≤ 2560 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₀.mem.readW (W + BitVec.ofNat 64 d) 64 := fun h₁ h₂ => by
    rw [B₂.frame.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (a := _) (d := 144) (k := 16) (by omega) h₂ (by decide)) (by decide),
      B₁.frame.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (a := _) (d := 48) (k := 16) (by omega) h₂ (by decide)) (by decide)]
  have haad₂ := (kA (d := aadO) (by decide) (by decide)).trans haad
  have halen₂ := (kA (d := alenO) (by decide) (by decide)).trans halen
  have r₁ : InRegions (s₂.rd ++ s₂.wr) (W + BitVec.ofNat 64 aadO) 8 := by
    rw [B₂.rd, B₂.wr, B₁.rd, B₁.wr]; exact in_left (in_off hw (by decide) (by decide))
  have r₂ : InRegions (s₂.rd ++ s₂.wr) (W + BitVec.ofNat 64 alenO) 8 := by
    rw [B₂.rd, B₂.wr, B₁.rd, B₁.wr]; exact in_left (in_off hw (by decide) (by decide))
  simp only [aadO, alenO] at haad₂ halen₂ r₁ r₂
  refine ⟨_, by rw [runBlock_append, runBlock_append, run₁, Option.bind_some, run₂, Option.bind_some]; orun [h19₂,
    r₁, r₂], ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, haad₂]
  · simp [gpr_write, halen₂]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.2.1, hr.2.2, ite_false]
    rw [B₂.gpr r (by simp [hr.1]), B₁.gpr r (by simp [hr.1])]
  · exact (B₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp))
  · simp only [mem_write]
    rw [blockAtMem_frame B₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), B₁.val]
  · simp only [mem_write]; exact B₂.val
  · simp only [sp_write]; rw [B₂.sp, B₁.sp]
  · simp only [rd_write]; rw [B₂.rd, B₁.rd]
  · simp only [wr_write]; rw [B₂.wr, B₁.wr]

/-- `HASH(K, A)` to `W + sumO`, with `aad` and `aad_len` in `W`: `HInv` at 0. -/
theorem hashHead_ok {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : HCtx K W D n R ciph l A a s₀) (E : Env K W D R n SP s₀)
    (haad : s₀.mem.readW (W + BitVec.ofNat 64 aadO) 64 = A)
    (halen : s₀.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a.length)
    (hl0 : blockAtMem s₀.mem (W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa (.seq (.block (zero16 sumO ++ zero16 ohO ++ [ld .x23 .x19 aadO, ld .x26 .x19 alenO]))
      (.block [.lsr .x .x26 .x26 4, Impl.AesGcm.AArch64.imm .x25 1])) s₀ fun s =>
      HInv K W D R n SP ciph l A a s₀ s 0 := by
  have L := C.lay
  have hs := C.short
  obtain ⟨s₁, run₁, x23₁, x26₁, g₁, f₁, sum₁, oh₁, sp₁, rd₁, wr₁⟩ := hashHead1_ok L E.x19 E.perm.w haad halen
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine Proof.AesGcm.AArch64.WP.run (Q := fun s => s = (s₁.write .x .x26 (s₁.gpr .x26 >>> 4)).write .x .x25
    (BitVec.ofNat 64 1)) ⟨_, by orun [], rfl⟩ fun s hs' => ?_
  subst hs'
  refine
    { env := E.others (rs := [.x9, .x23, .x25, .x26]) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp only [gpr_write, hr.2.2.1, hr.2.2.2, ite_false]; exact g₁ r (by simp [hr.1, hr.2.1, hr.2.2.2]))
        (by simp only [sp_write]; exact sp₁) (by simp only [rd_write]; exact rd₁) (by simp only [wr_write]; exact wr₁)
      frame := by
        simp only [mem_write]
        exact f₁.sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
          · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
      rd := by simp only [rd_write]; exact rd₁
      wr := by simp only [wr_write]; exact wr₁
      le := Nat.zero_le _
      sum := by simp only [mem_write]; rw [sum₁]; rfl
      oh := by simp only [mem_write]; rw [oh₁]; rfl
      x23 := by simp [gpr_write, x23₁]
      x25 := by simp [gpr_write]
      x26 := by simp [gpr_write, x26₁, lsr_ofNat _ _ hs]
      l0 := by
        simp only [mem_write]
        rw [blockAtMem_frame f₁ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact L.w_w (.inr (by decide)) (by decide) (by decide)
          · exact L.w_w (.inl (by decide)) (by decide) (by decide)), hl0] }

/-- The chunks of `HASH`, from the first. -/
theorem hashLoop_ok (v : BlocksImpl) {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : HCtx K W D n R ciph l A a s₀) {t : State}
    (H₀ : HInv K W D R n SP ciph l A a s₀ t 0) (hm : 0 < a.length / 16) :
    WP isa (.loop (hashChunk (callees v)) (.nonzero .x .x26)) t fun u =>
      HInv K W D R n SP ciph l A a s₀ u (a.length / 16) := by
  have hs := C.short
  refine WP.loop (M := isa)
    (fun (k : Nat) (u : State) => ∃ j, k = a.length / 16 - j ∧ j < a.length / 16 ∧
      HInv K W D R n SP ciph l A a s₀ u j) ?_ (a.length / 16 - 0) _ ⟨0, rfl, hm, H₀⟩
  rintro k u ⟨j, rfl, hj, H⟩
  refine WP.mono (hashChunk_ok v C H hj) fun u' H' => ?_
  have ev := eval_nonzero H'.x26 (by omega)
  by_cases he : a.length / 16 - (j + min 8 (a.length / 16 - j)) = 0
  · left
    have hje : j + min 8 (a.length / 16 - j) = a.length / 16 := by omega
    exact ⟨ev.trans (by simp [he]), hje ▸ H'⟩
  · right
    exact ⟨ev.trans (by simp [he]), a.length / 16 - (j + min 8 (a.length / 16 - j)), by omega,
      j + min 8 (a.length / 16 - j), rfl, by omega, H'⟩

/-- The length of the rest of the associated data. -/
theorem tailHead_ok {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : HCtx K W D n R ciph l A a s₀)
    (halen : s₀.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a.length) {t : State}
    (H : HInv K W D R n SP ciph l A a s₀ t (a.length / 16)) :
    WP isa (.block [ld .x24 .x19 alenO, Impl.AesGcm.AArch64.imm .x10 15, .logic .and .x .x24 .x24 .x10]) t
      fun t₁ => HInv K W D R n SP ciph l A a s₀ t₁ (a.length / 16) ∧
        t₁.gpr .x24 = BitVec.ofNat 64 (a.length % 16) := by
  have hs := C.short
  have r₁ : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 alenO) 8 := H.env.perm.wR (by decide)
  have al : t.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a.length := by
    rw [kept_read C.lay C.dw (hashR_mut H.frame) (by decide), halen]
  simp only [alenO] at r₁ al
  refine Proof.AesGcm.AArch64.WP.run (Q := fun t₁ => t₁ = ((t.write .x .x24 (BitVec.ofNat 64 a.length)).write .x .x10
    (BitVec.ofNat 64 15)).write .x .x24 (BitVec.ofNat 64 a.length &&& BitVec.ofNat 64 15))
    ⟨_, by orun [H.env.x19, r₁, al], rfl⟩ fun t₁ ht₁ => ?_
  subst ht₁
  refine ⟨{ H with
      env := H.env.others (rs := [.x10, .x24]) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; simp [gpr_write, hr.1, hr.2])
        rfl rfl rfl
      frame := H.frame
      x23 := by simp [gpr_write, H.x23]
      x25 := by simp [gpr_write, H.x25]
      x26 := by simp [gpr_write, H.x26] }, ?_⟩
  simp [gpr_write, and15, toNat_ofNat_of_lt hs]

/-- After the whole blocks: the rest, if any. -/
theorem hashTail_ok (v : BlocksImpl) {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : HCtx K W D n R ciph l A a s₀)
    (halen : s₀.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a.length) {t : State}
    (H : HInv K W D R n SP ciph l A a s₀ t (a.length / 16)) :
    WP isa (.seq (.block [ld .x24 .x19 alenO, Impl.AesGcm.AArch64.imm .x10 15, .logic .and .x .x24 .x24 .x10])
      (.ite (.zero .x .x24) (.block []) (hashRest (callees v)))) t fun t' => Env K W D R n SP t' ∧
        Frame (hashR W) s₀.mem t'.mem ∧
        blockAtMem t'.mem (W + BitVec.ofNat 64 sumO) = Spec.Ocb.hash ciph l a ∧ t'.rd = s₀.rd ∧ t'.wr = s₀.wr := by
  have hs := C.short
  refine WP.seq (WP.mono (tailHead_ok C halen H) fun t₁ ⟨H₁, h24⟩ => ?_)
  refine WP.ite (decide (a.length % 16 = 0)) (eval_zero h24 (by omega)) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have h0 : a.length % 16 = 0 := of_decide_eq_true hb
    refine ⟨H₁.env, H₁.frame, ?_, H₁.rd, H₁.wr⟩
    rw [H₁.sum, Proof.Ocb.hash_eq]
    have hlen : (a.drop (16 * (a.length / 16))).length = 0 := by simp; omega
    simp [hlen]
  · exact hashRest_ok v C H₁ (by have := of_decide_eq_false hb; omega) h24

/-- The chunks, if any. -/
theorem hashBody_ok (v : BlocksImpl) {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : HCtx K W D n R ciph l A a s₀) {t : State}
    (H₀ : HInv K W D R n SP ciph l A a s₀ t 0) :
    WP isa (.ite (.zero .x .x26) (.block []) (.loop (hashChunk (callees v)) (.nonzero .x .x26))) t fun u =>
      HInv K W D R n SP ciph l A a s₀ u (a.length / 16) := by
  have hs := C.short
  refine WP.ite (decide (a.length / 16 = 0)) (eval_zero H₀.x26 (by omega)) (fun hb => WP.block_nil ?_)
    (fun hb => hashLoop_ok v C H₀ (Nat.pos_of_ne_zero (of_decide_eq_false hb)))
  exact (of_decide_eq_true hb) ▸ H₀

/-- `HASH(K, A)` to `W + sumO`, with `aad` and `aad_len` in `W + aadO` and
`W + alenO`. -/
theorem hash_ok (v : BlocksImpl) {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : HCtx K W D n R ciph l A a s₀) (E : Env K W D R n SP s₀)
    (haad : s₀.mem.readW (W + BitVec.ofNat 64 aadO) 64 = A)
    (halen : s₀.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a.length)
    (hl0 : blockAtMem s₀.mem (W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa (Impl.AesOcb.AArch64.hash (callees v)) s₀ fun t' => Env K W D R n SP t' ∧
      Frame (hashR W) s₀.mem t'.mem ∧
      blockAtMem t'.mem (W + BitVec.ofNat 64 sumO) = Spec.Ocb.hash ciph l a ∧ t'.rd = s₀.rd ∧ t'.wr = s₀.wr := by
  unfold Impl.AesOcb.AArch64.hash
  refine WP.assoc (WP.seq (WP.mono (hashHead_ok C E haad halen hl0) fun s₃ H₀ => ?_))
  exact WP.seq (WP.mono (hashBody_ok v C H₀) fun u H => hashTail_ok v C halen H)

end VG.Proof.AesOcb.AArch64
