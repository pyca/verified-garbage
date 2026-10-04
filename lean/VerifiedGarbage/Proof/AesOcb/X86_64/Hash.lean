import VerifiedGarbage.Proof.AesOcb.X86_64.HashChunk

/-!
# AES-OCB on x86-64: `HASH` (`hash`)

Untrusted: everything here is checked by Lean. `hash` zeroes the sum and the
offset, keeps the number of whole blocks of the associated data and the
length of the rest in `W`, takes the whole blocks a chunk at a time
(`hashChunk_ok`), and the rest, padded, XORed with `Offset_m ⊕ L_*` and
enciphered (`hashRest_ok`): the sum is §4.1's `HASH(K, A)` (`hash_ok`,
`Proof.Ocb.hash_eq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem blockAt lAt ntz ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt hsum)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append toNat_ofNat_of_lt imm_eq eval_e eval_ne bytesAt_frame)

/-- The padded rest of the associated data, after its `m` whole blocks. -/
theorem hashRest_ok (v : BlocksImpl) {K W SP D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : HCtx K W SP D n R ciph l A a s₀) {t : State}
    (H : HInv K W SP D n ciph l A a s₀ t (a.length / 16)) (hr : 0 < a.length % 16)
    (h12 : t.gpr .r12 = BitVec.ofNat 64 (a.length % 16)) :
    WP isa (hashRest (callees v)) t fun t' => Env K W SP t' ∧ Frame (hashR W SP) s₀.mem t'.mem ∧
      blockAtMem t'.mem (W + BitVec.ofNat 64 sumO) = Spec.Ocb.hash ciph l a ∧ t'.rd = s₀.rd ∧ t'.wr = s₀.wr := by
  have L := C.lay
  have E := H.env
  have hs := C.short
  generalize hm : a.length / 16 = m at H
  have hrest : a.length - 16 * m = a.length % 16 := by omega
  -- `Offset_m ⊕ L_*`
  obtain ⟨t₁, run₁, B₁⟩ := xor16_ok (s := t) (b := .r14) (a := 240) (d := ohO) E.r15 E.r14 (by decide) (by decide)
    (E.perm.kR (by decide)) (E.perm.kR (by decide)) (E.perm.wW (by decide)) (E.perm.wW (by decide))
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => B₁.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    B₁.rd B₁.wr
  have oh₁ : blockAtMem t₁.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l m ^^^ l := by
    rw [B₁.val, H.oh, ← C.lstar' (hashR_mut H.frame)]; rfl
  have fr₁ : Frame (hashR W SP) s₀.mem t₁.mem := H.frame.trans (B₁.frame.sub fun r hr => by
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
    rw [bytesAt_frame (hashR_mut (D := D) (n := n) fr₁) (fun r hr =>
      (C.a_mut r hr).sub_left (Offset.sub_base A (by omega))) (by omega), hd]
  unfold hashRest
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (padTo_ok E₁ hr (by omega) (by decide) (by rw [B₁.gpr _ (by decide), H.rbx])
    (by rw [B₁.gpr _ (by decide), h12]) hS hSD) fun t₂ ⟨fr₂, pad₂, g₂, rd₂, wr₂⟩ => ?_)
  rw [hrestb] at pad₂
  have E₂ : Env K W SP t₂ := E₁.keep (fun r hr => g₂ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    rd₂ wr₂
  have oh₂ : blockAtMem t₂.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l m ^^^ l := by
    rw [blockAtMem_frame fr₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide), oh₁]
  -- XORed with the offset
  obtain ⟨t₃, run₃, B₃⟩ := xor16_ok (s := t₂) (b := .r15) (a := ohO) (d := bufO) E₂.r15 E₂.r15 (by decide) (by decide)
    (E₂.perm.wR (by decide)) (E₂.perm.wR (by decide)) (E₂.perm.wW (by decide)) (E₂.perm.wW (by decide))
  have E₃ : Env K W SP t₃ := E₂.keep (fun r hr => B₃.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    B₃.rd B₃.wr
  have buf₃ : blockAtMem t₃.mem (W + BitVec.ofNat 64 bufO) =
      pad (a.drop (16 * m)) ^^^ (offAt 0 l m ^^^ l) := by rw [B₃.val, pad₂, oh₂]
  have fr₃ : Frame (hashR W SP) s₀.mem t₃.mem := fr₁.trans ((fr₂.trans B₃.frame).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp, sub_wC (by decide) (by decide)⟩)
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  -- enciphered
  refine WP.seq (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) (b := v.enc) v.encOk v.encNosp v.encDepth L E₃
    C.rounds (C.rnd' (hashR_mut fr₃)) (oneBlock_ok E₃.r15 bufO (by decide))
    (dstW L E₃.perm (d := bufO) (n := 1) (by decide))) fun t₄ P₄ => ?_)
  have E₄ : Env K W SP t₄ := E₃.of_saved P₄.saved P₄.rd P₄.wr
  have buf₄ : blockAtMem t₄.mem (W + BitVec.ofNat 64 bufO) = ciph (pad (a.drop (16 * m)) ^^^ (offAt 0 l m ^^^ l)) := by
    have := P₄.enc (i := 0) (by decide)
    simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [this, buf₃]
    exact congrFun (C.ciph' (hashR_mut fr₃)) _
  have fr₄ : Frame (hashR W SP) s₀.mem t₄.mem := fr₃.trans (P₄.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, sub_wC (by decide) (by decide)⟩
    · exact ⟨_, by simp, sub_wC (by decide) (by decide)⟩
    · rw [E₃.rsp]; exact ⟨_, by simp, fun _ h => h⟩)
  have kSum : ∀ {u u' : State}, Frame [⟨W + BitVec.ofNat 64 bufO, 16⟩] u.mem u'.mem →
      blockAtMem u'.mem (W + BitVec.ofNat 64 sumO) = blockAtMem u.mem (W + BitVec.ofNat 64 sumO) := fun h =>
    blockAtMem_frame h fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have sum₄ : blockAtMem t₄.mem (W + BitVec.ofNat 64 sumO) = hsum ciph l a m := by
    rw [blockAtMem_frame P₄.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · rw [E₃.rsp]; exact (L.stk_w' (by decide)).symm),
      kSum B₃.frame, kSum fr₂, blockAtMem_frame B₁.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), H.sum]
  -- added to the sum
  obtain ⟨t₅, run₅, B₅⟩ := xor16_ok (s := t₄) (b := .r15) (a := bufO) (d := sumO) E₄.r15 E₄.r15 (by decide) (by decide)
    (E₄.perm.wR (by decide)) (E₄.perm.wR (by decide)) (E₄.perm.wW (by decide)) (E₄.perm.wW (by decide))
  refine WP.of_runBlock ⟨t₅, run₅, E₄.keep (fun r hr => B₅.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    B₅.rd B₅.wr, fr₄.trans (B₅.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩), ?_,
    by rw [B₅.rd, P₄.rd, B₃.rd, rd₂, B₁.rd, H.rd], by rw [B₅.wr, P₄.wr, B₃.wr, wr₂, B₁.wr, H.wr]⟩
  rw [B₅.val, sum₄, buf₄, Proof.Ocb.hash_eq]
  have hlen : (a.drop (16 * m)).length = a.length % 16 := by simp; omega
  simp only [hlen, show a.length % 16 > 0 from hr, ↓reduceIte, hm]

/-- After the whole blocks: the rest, if any. -/
theorem hashTail_ok (v : BlocksImpl) {K W SP D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : HCtx K W SP D n R ciph l A a s₀) {t : State}
    (H : HInv K W SP D n ciph l A a s₀ t (a.length / 16)) :
    WP isa (.seq (.block [ld .r12 .r15 tmpO, .alu .test .r12 (.reg .r12)]) (.ite .e (.block []) (hashRest (callees v))))
      t fun t' => Env K W SP t' ∧ Frame (hashR W SP) s₀.mem t'.mem ∧
        blockAtMem t'.mem (W + BitVec.ofNat 64 sumO) = Spec.Ocb.hash ciph l a ∧ t'.rd = s₀.rd ∧ t'.wr = s₀.wr := by
  have r₁ : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 112) 8 := H.env.perm.wR (by decide)
  have rest := H.rest
  simp only [tmpO] at rest
  obtain ⟨t₁, run₁, r12₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [ld .r12 .r15 tmpO, .alu .test .r12 (.reg .r12)] t =
      some t₁ ∧ t₁.gpr .r12 = BitVec.ofNat 64 (a.length % 16) ∧ t₁.zf = some (decide (a.length % 16 = 0)) ∧
      (∀ r, r ≠ .r12 → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by orun [H.env.r15, r₁, rest], ?_, ?_, fun r h => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true]
    · simp only [zf_arithFlags, gpr_setReg, ite_true,
        Proof.AesCcm.X86_64.and_self_beq (show a.length % 16 < 2 ^ 64 by omega)]
    · simp only [gpr_setReg, gpr_arithFlags, h, ite_false]
    all_goals rfl
  have H₁ : HInv K W SP D n ciph l A a s₀ t₁ (a.length / 16) :=
    { H with
      env := H.env.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₁ wr₁
      frame := by rw [m₁]; exact H.frame
      rd := by rw [rd₁, H.rd]
      wr := by rw [wr₁, H.wr]
      sum := by rw [m₁, H.sum]
      oh := by rw [m₁, H.oh]
      rbx := by rw [g₁ _ (by decide), H.rbx]
      rbp := by rw [g₁ _ (by decide), H.rbp]
      alen := by rw [m₁, H.alen]
      rest := by rw [m₁, H.rest]
      l0 := by rw [m₁, H.l0] }
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite (decide (a.length % 16 = 0)) (eval_e zf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have h0 : a.length % 16 = 0 := of_decide_eq_true hb
    refine ⟨H₁.env, H₁.frame, ?_, H₁.rd, H₁.wr⟩
    rw [H₁.sum, Proof.Ocb.hash_eq]
    have hlen : (a.drop (16 * (a.length / 16))).length = 0 := by simp; omega
    simp [hlen]
  · exact hashRest_ok v C H₁ (by have := of_decide_eq_false hb; omega) r12₁

/-- `HASH(K, A)` to `W + sumO`, with `aad` and `aad_len` in `W`. -/
theorem hashHead_ok {K W SP D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : HCtx K W SP D n R ciph l A a s₀) (E : Env K W SP s₀)
    (haad : s₀.mem.readW (W + BitVec.ofNat 64 aadO) 64 = A)
    (halen : s₀.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a.length)
    (hl0 : blockAtMem s₀.mem (W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa (.block (zero16 sumO ++ zero16 ohO ++
      [ld .rbx .r15 aadO, ld .rax .r15 alenO, mvr .rcx .rax, .alu .and .rcx (.imm 15),
       st .r15 tmpO .rcx, .shift .shr .rax 4, st .r15 alenO .rax, .mov .rbp (.imm 1),
       .alu .test .rax (.reg .rax)])) s₀ fun s =>
      HInv K W SP D n ciph l A a s₀ s 0 ∧ s.zf = some (decide (a.length / 16 = 0)) := by
  have L := C.lay
  have hs := C.short
  -- the sum, the offset, the counts
  obtain ⟨s₁, run₁, B₁⟩ := zero16_ok (s := s₀) (d := sumO) E.r15 (E.perm.wW (by decide)) (E.perm.wW (by decide))
  have h15₁ : s₁.gpr .r15 = W := by rw [B₁.gpr _ (by decide), E.r15]
  obtain ⟨s₂, run₂, B₂⟩ := zero16_ok (s := s₁) (d := ohO) h15₁ (by rw [B₁.wr]; exact E.perm.wW (by decide))
    (by rw [B₁.wr]; exact E.perm.wW (by decide))
  have h15₂ : s₂.gpr .r15 = W := by rw [B₂.gpr _ (by decide), h15₁]
  have kA : ∀ {d : Nat}, (d + 8 ≤ 48 ∨ (64 ≤ d ∧ d + 8 ≤ 144) ∨ 160 ≤ d) → d + 8 ≤ 2560 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₀.mem.readW (W + BitVec.ofNat 64 d) 64 := fun h₁ h₂ => by
    rw [B₂.frame.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (a := _) (d := 144) (k := 16) (by omega) h₂ (by decide)) (by decide),
      B₁.frame.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (a := _) (d := 48) (k := 16) (by omega) h₂ (by decide)) (by decide)]
  have haad₂ := (kA (d := 240) (by decide) (by decide)).trans haad
  have halen₂ := (kA (d := 248) (by decide) (by decide)).trans halen
  have r₁ : InRegions (s₂.rd ++ s₂.wr) (W + BitVec.ofNat 64 240) 8 := by rw [B₂.rd, B₂.wr, B₁.rd, B₁.wr]; exact E.perm.wR (by decide)
  have r₂ : InRegions (s₂.rd ++ s₂.wr) (W + BitVec.ofNat 64 248) 8 := by rw [B₂.rd, B₂.wr, B₁.rd, B₁.wr]; exact E.perm.wR (by decide)
  have w₁ : InRegions s₂.wr (W + BitVec.ofNat 64 112) 8 := by rw [B₂.wr, B₁.wr]; exact E.perm.wW (by decide)
  have w₂ : InRegions s₂.wr (W + BitVec.ofNat 64 248) 8 := by rw [B₂.wr, B₁.wr]; exact E.perm.wW (by decide)
  have e15 : BitVec.signExtend 64 (15 : BitVec 32) = 15#64 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 := by decide
  obtain ⟨s₃, run₃, rbx₃, rbp₃, zf₃, m₃, g₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa
      [ld .rbx .r15 aadO, ld .rax .r15 alenO, mvr .rcx .rax, .alu .and .rcx (.imm 15),
       st .r15 tmpO .rcx, .shift .shr .rax 4, st .r15 alenO .rax, .mov .rbp (.imm 1),
       .alu .test .rax (.reg .rax)] s₂ = some s₃ ∧
      s₃.gpr .rbx = A ∧ s₃.gpr .rbp = BitVec.ofNat 64 1 ∧ s₃.zf = some (decide (a.length / 16 = 0)) ∧
      s₃.mem = (s₂.mem.writeW (W + BitVec.ofNat 64 112) (BitVec.ofNat 64 (a.length % 16))).writeW
        (W + BitVec.ofNat 64 248) (BitVec.ofNat 64 (a.length / 16)) ∧
      (∀ r, r ≠ .rbx → r ≠ .rax → r ≠ .rcx → r ≠ .rbp → s₃.gpr r = s₂.gpr r) ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by orun [h15₂, r₁, r₂, w₁, w₂, haad₂, halen₂], ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, e1]
    · simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
        Proof.AesCcm.X86_64.shr4 _ (show a.length < 2 ^ 64 by omega),
        Proof.AesCcm.X86_64.and_self_beq (show a.length / 16 < 2 ^ 64 by omega)]
    · simp only [mem_setReg, mem_setFlags, mem_arithFlags, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true,
        ite_false, reduceCtorEq, e15, Proof.AesCcm.X86_64.and15', toNat_ofNat_of_lt (show a.length < 2 ^ 64 by omega),
        Proof.AesCcm.X86_64.shr4 _ (show a.length < 2 ^ 64 by omega)]
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, h1, h2, h3, h4, ite_false]
    all_goals try rfl
  have f₁₁₂ : ∀ (M : Mem) (x y : BitVec 64), Frame [⟨W + BitVec.ofNat 64 112, 8⟩, ⟨W + BitVec.ofNat 64 248, 8⟩] M
      ((M.writeW (W + BitVec.ofNat 64 112) x).writeW (W + BitVec.ofNat 64 248) y) := fun M x y =>
    ((Frame.refl _ _).writeW (List.mem_cons_self ..) x (Region.contains_self (W + BitVec.ofNat 64 112) 8)).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) y (Region.contains_self (W + BitVec.ofNat 64 248) 8)
  have kB : ∀ {d : Nat}, (d + 16 ≤ 112 ∨ (120 ≤ d ∧ d + 16 ≤ 248)) →
      blockAtMem s₃.mem (W + BitVec.ofNat 64 d) = blockAtMem s₂.mem (W + BitVec.ofNat 64 d) :=
    fun hd => by
      rw [m₃]
      exact blockAtMem_frame (f₁₁₂ _ _ _) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact L.w_w (by omega) (by omega) (by decide)
        · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  have H₀ : HInv K W SP D n ciph l A a s₀ s₃ 0 :=
    { env := E.keep (fun r hr => by
          simp at hr
          rcases hr with rfl | rfl | rfl <;>
            rw [g₃ _ (by decide) (by decide) (by decide) (by decide), B₂.gpr _ (by decide), B₁.gpr _ (by decide)])
        (by rw [rd₃, B₂.rd, B₁.rd]) (by rw [wr₃, B₂.wr, B₁.wr])
      frame := by
        rw [m₃]
        refine (B₁.frame.sub fun r hr => ?_).trans ((B₂.frame.sub fun r hr => ?_).trans ((f₁₁₂ _ _ _).sub fun r hr => ?_))
        · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
        · simp only [List.mem_singleton] at hr; subst hr
          exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
          · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
      rd := by rw [rd₃, B₂.rd, B₁.rd]
      wr := by rw [wr₃, B₂.wr, B₁.wr]
      le := Nat.zero_le _
      sum := by
        rw [kB (by decide), blockAtMem_frame B₂.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), B₁.val]
        rfl
      oh := by rw [kB (by decide), B₂.val]; rfl
      rbx := by rw [rbx₃]; simp
      rbp := rbp₃
      alen := by rw [m₃]; simp only [alenO, Nat.sub_zero]; exact Mem.readW_writeW_self64 _ _ _
      rest := by
        rw [m₃]; simp only [tmpO]
        rw [Mem.readW_writeW_sep (Offset.sep W (by decide) (by decide) (by decide)) (by decide),
          Mem.readW_writeW_self64]
      l0 := by
        rw [kB (by decide), blockAtMem_frame B₂.frame (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)),
          blockAtMem_frame B₁.frame (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)), hl0] }
  exact WP.of_runBlock ⟨s₃, by rw [runBlock_append, runBlock_append, run₁, Option.bind_some, run₂,
    Option.bind_some, run₃], H₀, zf₃⟩

/-- The chunks of `HASH`, from the first. -/
theorem hashLoop_ok (v : BlocksImpl) {K W SP D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : HCtx K W SP D n R ciph l A a s₀) {t : State}
    (H₀ : HInv K W SP D n ciph l A a s₀ t 0) (hm : 0 < a.length / 16) :
    WP isa (.loop (hashChunk (callees v)) .ne) t fun u => HInv K W SP D n ciph l A a s₀ u (a.length / 16) := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (u : State) => ∃ j, k = a.length / 16 - j ∧ j < a.length / 16 ∧
      HInv K W SP D n ciph l A a s₀ u j) ?_ (a.length / 16 - 0) _ ⟨0, rfl, hm, H₀⟩
  rintro k u ⟨j, rfl, hj, H⟩
  refine WP.mono (hashChunk_ok v C H hj) fun u' ⟨H', hz⟩ => ?_
  by_cases he : a.length / 16 - (j + min 8 (a.length / 16 - j)) = 0
  · left
    have hje : j + min 8 (a.length / 16 - j) = a.length / 16 := by omega
    exact ⟨(eval_ne hz).trans (by simp [he]), hje ▸ H'⟩
  · right
    exact ⟨(eval_ne hz).trans (by simp [he]), a.length / 16 - (j + min 8 (a.length / 16 - j)), by omega,
      j + min 8 (a.length / 16 - j), rfl, by omega, H'⟩

theorem hash_ok (v : BlocksImpl) {K W SP D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : HCtx K W SP D n R ciph l A a s₀) (E : Env K W SP s₀)
    (haad : s₀.mem.readW (W + BitVec.ofNat 64 aadO) 64 = A)
    (halen : s₀.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a.length)
    (hl0 : blockAtMem s₀.mem (W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa (Impl.AesOcb.X86_64.hash (callees v)) s₀ fun t' => Env K W SP t' ∧ Frame (hashR W SP) s₀.mem t'.mem ∧
      blockAtMem t'.mem (W + BitVec.ofNat 64 sumO) = Spec.Ocb.hash ciph l a ∧ t'.rd = s₀.rd ∧ t'.wr = s₀.wr := by
  unfold Impl.AesOcb.X86_64.hash
  refine WP.seq (WP.mono (hashHead_ok C E haad halen hl0) fun s₃ ⟨H₀, zf₃⟩ => ?_)
  refine WP.seq (WP.ite (decide (a.length / 16 = 0)) (eval_e zf₃) (fun hb => WP.block_nil ?_) (fun hb => ?_))
  · have h0 : a.length / 16 = 0 := of_decide_eq_true hb
    exact hashTail_ok v C (h0 ▸ H₀)
  · exact WP.mono (hashLoop_ok v C H₀ (Nat.pos_of_ne_zero (of_decide_eq_false hb))) fun u H => hashTail_ok v C H

end VG.Proof.AesOcb.X86_64
