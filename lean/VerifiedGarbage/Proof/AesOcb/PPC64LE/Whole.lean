module

public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Pass
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Args
import VerifiedGarbage.Proof.AesOcb.PPC64LE.Words
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-OCB on PPC64LE: the whole blocks (`whole`)

Untrusted: everything here is checked by Lean. `whole f pre post` runs a
pass with `pre` over the `m` whole blocks of the data, calls `f` on all of
them (`callBlocks_ok`), copies `Offset_0` back and runs a pass with `post`
(`whole_ok`): each block becomes `G (X ⊕ Offset_i) ⊕ Offset_i`, and the
checksum is the second pass's. As on AArch64
(`Proof/AesOcb/AArch64/Whole.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Impl.AesOcb.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.PPC64LE (in_left in_off shr4 Keeps)
open VG.Proof.ChaCha20Poly1305.PPC64LE renaming wp_or → cwp_or, wp_lsr → cwp_lsr, wp_li → cwp_li

/-- What `whole` writes: the offset and the checksum, `L_{ntz(i)}`, the
working space of the functions called and the data. -/
abbrev wholeR (W D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 32⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨D, n⟩]

theorem wholeR_mut {W D : Addr} {n : Nat} {m m' : Mem} (h : Frame (wholeR W D n) m m') :
    Frame (mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact in_mutA (by decide)
  · exact in_mutA (by decide)
  · exact in_mutB (by decide) (by decide)
  · exact in_mutD fun _ h => h

/-- The first `k` bytes of a buffer, as a buffer at the same place. -/
theorem DBuf.take' {K W : Addr} {s : State} {D : Addr} {n k : Nat} (h : DBuf K W s D n) (hk : k ≤ n) :
    DBuf K W s D k := by
  have := h.slice (a := 0) (k := k) (by omega)
  rwa [BitVec.add_zero] at this

/-- The `m` blocks of the data, `len` (in `r23`) bytes at `r27`. -/
theorem dataArgs_ok {D : Addr} {t : State} (h27 : t.gpr .r27 = D) {len : Nat} (hl : len < 2 ^ 64)
    (h23 : t.gpr .r23 = BitVec.ofNat 64 len) :
    ArgsOk [Impl.AesGcm.PPC64LE.mov .r5 .r27, .lsr .d .r6 .r23 4] t D (len / 16) := by
  refine ⟨(t.write .r5 (t.gpr .r27 ||| t.gpr .r27)).write .r6 ((t.write .r5 (t.gpr .r27 ||| t.gpr .r27)).gpr .r23 >>> 4),
    ?_, by rw [gpr_write_of_ne _ _ (by decide), gpr_write_self, BitVec.or_self, h27],
    by rw [gpr_write_self, gpr_write_of_ne _ _ (by decide), h23, shr4 hl],
    fun r h5 h6 => by rw [gpr_write_of_ne _ _ h6, gpr_write_of_ne _ _ h5], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  simp only [Impl.AesGcm.PPC64LE.mov, runBlock_cons, runStep_some, runBlock_nil, exec_logic,
    exec_lsr_d (show 4 < 64 by decide), Option.bind_some]

/-- The start of a pass: `r24 ← D`, `r25 ← m`, `r26 ← 1`. -/
theorem passStart_ok {D : Addr} {t : State} (h27 : t.gpr .r27 = D) {len : Nat} (hl : len < 2 ^ 64)
    (h23 : t.gpr .r23 = BitVec.ofNat 64 len) :
    WP isa (.block passStart) t fun t' =>
      t'.gpr .r24 = D + BitVec.ofNat 64 (16 * 0) ∧ t'.gpr .r25 = BitVec.ofNat 64 (len / 16 - 0) ∧
      t'.gpr .r26 = BitVec.ofNat 64 (0 + 1) ∧ (∀ r, r ∉ [.r24, .r25, .r26] → t'.gpr r = t.gpr r) ∧ Keeps t t' := by
  refine cwp_or fun t₁ u₁ => cwp_lsr (by decide) fun t₂ u₂ => cwp_li (by decide) fun t₃ u₃ => WP.block_nil
    ⟨?_, ?_, ?_, fun r hr => ?_, ⟨by rw [u₃.mem, u₂.mem, u₁.mem], by rw [u₃.rd, u₂.rd, u₁.rd],
      by rw [u₃.wr, u₂.wr, u₁.wr], by rw [u₃.sp, u₂.sp, u₁.sp], by rw [u₃.lr, u₂.lr, u₁.lr]⟩⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, BitVec.or_self, h27]; simp
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h23, shr4 hl]; rfl
  · rw [u₃.gpr]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₃.other _ hr.2.2, u₂.other _ hr.2.1, u₁.other _ hr.1]

/-- What `whole` leaves. -/
structure WholePost (V : Reg → BitVec 64) (sp D : Addr) (m : Nat) (O0 l : Block) (Z : Nat → Block) (ck : Block)
    (t t' : State) : Prop where
  env : Env V sp t'
  frame : Frame (wholeR (V .r31) D (16 * m)) t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  blk : ∀ k < m, blockAtMem t'.mem (D + BitVec.ofNat 64 (16 * k)) = Z k ^^^ offAt O0 l (k + 1)
  ofs : blockAtMem t'.mem (V .r31 + BitVec.ofNat 64 ofsO) = offAt O0 l m
  ck : blockAtMem t'.mem (V .r31 + BitVec.ofNat 64 ckO) = ck

theorem whole_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksPPC64LE f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksPPC64LE f).post s s')
    (nf : c.noFrames = true) {G : List Byte → Cipher}
    (hcall : ∀ {s s' : State} {K D S : Addr} {R n : Nat}, BPost f s K D S R n s' → ∀ i < n,
      blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) = G (bytesAt s.mem K (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))))
    {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    (hB1 : ∀ {W}, BodyOk W pre (fun b o => b ^^^ o) fC1) (hB2 : ∀ {W}, BodyOk W post (fun b o => b ^^^ o) fC2)
    {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r31)) {t : State} (E : Env V sp t)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V .r28 = BitVec.ofNat 64 R) {len : Nat}
    (h23 : V .r23 = BitVec.ofNat 64 len) (hD : DBuf (V .r29) (V .r31) t (V .r27) len) (hm0 : 0 < len / 16)
    {O0 l : Block}
    (hofs : blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem t.mem (V .r31 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem t.mem (V .r31 + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem t.mem (V .r27 + BitVec.ofNat 64 (16 * i)))
      (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 (len / 16))
    (hckF2 : ∀ i, ckF2 (i + 1) = fC2 (ckF2 i)
      (G (bytesAt t.mem (V .r29) (16 * (R + 1)))
        (blockAtMem t.mem (V .r27 + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
      (offAt O0 l (i + 1))) :
    WP isa (whole (.call name c) pre post) t (WholePost V sp (V .r27) (len / 16) O0 l
      (fun k => G (bytesAt t.mem (V .r29) (16 * (R + 1)))
        (blockAtMem t.mem (V .r27 + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
      (ckF2 (len / 16)) t) := by
  have hl := hD.lt
  generalize hmd : len / 16 = m at *
  have hmn : 16 * m ≤ len := by omega
  have hm : m < 2 ^ 60 := by omega
  have hDm := hD.take' hmn
  -- the first pass
  unfold whole
  refine WP.seq (WP.mono (passStart_ok E.r27 hl (E.r23.trans h23)) fun s₁ ⟨r24₁, r25₁, r26₁, g₁, k₁⟩ => ?_)
  rw [hmd] at r25₁
  have E₁ := E.others g₁ k₁.sp k₁.rd k₁.wr
  have hD₁ : DBuf (V .r29) (V .r31) s₁ (V .r27) (16 * m) := hDm.of_eq k₁.rd k₁.wr
  have P₀ : PassInv V sp (V .r27) m O0 l (fun k => blockAtMem s₁.mem (V .r27 + BitVec.ofNat 64 (16 * k)))
      (fun b o => b ^^^ o) ckF1 s₁ s₁ 0 :=
    { env := E₁, frame := Frame.refl _ _, rd := rfl, wr := rfl, r24 := r24₁, r26 := r26₁, r25 := r25₁
      ofs := by rw [k₁.mem, hofs]; rfl
      ck := by rw [k₁.mem, hck]
      blk := fun k _ => by simp
      l0 := by rw [k₁.mem, hl0]
      gpr := fun _ _ => rfl }
  refine WP.seq (WP.mono (pass_ok L hB1 (fun i _ => by rw [hckF1, k₁.mem]) hD₁ hm0 hm P₀) fun s₂ P₂ => ?_)
  have hw := hD.wrap
  have hD₂ : DBuf (V .r29) (V .r31) s₂ (V .r27) (16 * m) := hD₁.of_eq P₂.rd P₂.wr
  refine WP.assoc (WP.seq (WP.mono (callBlocks_ok (f := f) L ok nf hR h28 P₂.env
    (fun s₃ g₃ k₃ => by
      have := dataArgs_ok (t := s₃) (by rw [g₃ _ (by decide) (by decide) (by decide), P₂.env.r27]) hl
        (by rw [g₃ _ (by decide) (by decide) (by decide), P₂.env.r23, h23])
      rwa [hmd] at this) (dstD hD₂)) fun s₃ P₃ => ?_))
  have E₃ := P₃.env P₂.env
  have kC : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨V .r27, 16 * m⟩ →
      (⟨Q, 16⟩ : Region).Disjoint ⟨V .r31 + BitVec.ofNat 64 512, 2048⟩ → blockAtMem s₃.mem Q = blockAtMem s₂.mem Q :=
    fun h₁ h₂ => blockAtMem_frame P₃.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁
      · exact h₂
  have kWP : ∀ {d : Nat}, (d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 96) ∨ (112 ≤ d ∧ d + 16 ≤ 512)) →
      blockAtMem s₃.mem (V .r31 + BitVec.ofNat 64 d) = blockAtMem s₁.mem (V .r31 + BitVec.ofNat 64 d) := fun hd => by
    rw [kC ((hD₂.w.sub_right (Lay.wSub (by omega))).symm) (L.w_w (.inl (by omega)) (by omega) (by decide)),
      blockAtMem_frame P₂.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (a := _) (d := 96) (k := 16) (by omega) (by omega) (by decide)
      · exact L.w_w (a := _) (d := 16) (k := 16) (by omega) (by omega) (by decide)
      · exact L.w_w (a := _) (d := 32) (k := 16) (by omega) (by omega) (by decide)
      · exact (hD₁.w.sub_right (Lay.wSub (by omega))).symm)]
  have o0₃ : blockAtMem s₃.mem (V .r31 + BitVec.ofNat 64 o0O) = O0 := by rw [kWP (by decide), k₁.mem, ho0]
  -- `Offset_0` again
  refine WP.seq (WP.block_append (WP.mono (copy16_ok (s := s₃) (a := o0O) (d := ofsO) (by decide) (by decide)
    E₃.r31 (E₃.perm.wR (by decide)) (E₃.perm.wR (by decide)) (E₃.perm.wW (by decide)) (E₃.perm.wW (by decide)))
    fun s₄a B₄ => WP.mono (passStart_ok (t := s₄a) (D := V .r27) (len := len) (by rw [B₄.gpr _ (by decide), E₃.r27]) hl
      (by rw [B₄.gpr _ (by decide), E₃.r23, h23])) fun s₄ ⟨r24₄, r25₄, r26₄, g₄, k₄⟩ => ?_))
  have E₄a := E₃.others B₄.gpr B₄.sp B₄.rd B₄.wr
  rw [hmd] at r25₄
  have E₄ := E₄a.others g₄ k₄.sp k₄.rd k₄.wr
  have hD₄ : DBuf (V .r29) (V .r31) s₄ (V .r27) (16 * m) :=
    hD₂.of_eq (by rw [k₄.rd, B₄.rd, P₃.rd]) (by rw [k₄.wr, B₄.wr, P₃.wr])
  have kB₄ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨V .r31, 2560⟩ → blockAtMem s₄.mem Q = blockAtMem s₃.mem Q :=
    fun hQ => by
      rw [k₄.mem]; exact blockAtMem_frame B₄.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hQ.sub_right (Lay.wSub (by decide))
  have hK : bytesAt s₂.mem (V .r29) (16 * (R + 1)) = bytesAt t.mem (V .r29) (16 * (R + 1)) := by
    have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
    rw [Proof.Cmac.bytesAt_frame P₂.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact hD₁.k.sub_left (Region.sub_prefix hRb)) (by omega), k₁.mem]
  have X₄ : ∀ k < m, blockAtMem s₄.mem (V .r27 + BitVec.ofNat 64 (16 * k)) =
      G (bytesAt t.mem (V .r29) (16 * (R + 1)))
        (blockAtMem t.mem (V .r27 + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)) :=
    fun k hk => by
      rw [kB₄ (hD₂.slice (a := 16 * k) (k := 16) (by omega)).w, hcall P₃ k hk, hK, P₂.blk k hk]
      simp only [hk, ↓reduceIte, k₁.mem]
  have ck₃ : blockAtMem s₃.mem (V .r31 + BitVec.ofNat 64 ckO) = ckF2 0 := by
    rw [kC ((hD₂.w.sub_right (Lay.wSub (by decide))).symm) (L.w_w (.inl (by decide)) (by decide) (by decide)),
      P₂.ck, hckF2₀]
  have P₀' : PassInv V sp (V .r27) m O0 l (fun k => blockAtMem s₄.mem (V .r27 + BitVec.ofNat 64 (16 * k)))
      (fun b o => b ^^^ o) ckF2 s₄ s₄ 0 :=
    { env := E₄, frame := Frame.refl _ _, rd := rfl, wr := rfl, r24 := r24₄, r26 := r26₄, r25 := r25₄
      ofs := by rw [k₄.mem, B₄.val, o0₃]; rfl
      ck := by
        rw [k₄.mem, blockAtMem_frame B₄.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)), ck₃]
      blk := fun k _ => by simp
      l0 := by
        rw [k₄.mem, blockAtMem_frame B₄.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
          kWP (by decide), k₁.mem, hl0]
      gpr := fun _ _ => rfl }
  refine WP.mono (pass_ok L hB2 (fun i hi => by rw [hckF2, X₄ i hi]) hD₄ hm0 hm P₀') fun s₅ P₅ => ?_
  have subW : ∀ r ∈ [(⟨V .r31 + BitVec.ofNat 64 lO, 16⟩ : Region), ⟨V .r31 + BitVec.ofNat 64 ofsO, 16⟩,
      ⟨V .r31 + BitVec.ofNat 64 ckO, 16⟩, ⟨V .r27, 16 * m⟩], ∃ r' ∈ wholeR (V .r31) (V .r27) (16 * m),
        Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (d := 16) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (d := 32) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
    · exact ⟨⟨V .r27, 16 * m⟩, by simp, fun _ h => h⟩
  refine ⟨P₅.env, ?_, by rw [P₅.rd, k₄.rd, B₄.rd, P₃.rd, P₂.rd, k₁.rd],
    by rw [P₅.wr, k₄.wr, B₄.wr, P₃.wr, P₂.wr, k₁.wr], fun k hk => ?_, P₅.ofs, P₅.ck⟩
  · rw [← k₁.mem]
    refine (P₂.frame.sub subW).trans ((P₃.frame.sub fun r hr => ?_).trans ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨V .r27, 16 * m⟩, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · have F₅ := P₅.frame
      rw [k₄.mem] at F₅
      exact (B₄.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., Offset.sub _ (d := 16) (n := 16) (e := 16) (k := 32) (by decide)
          (by decide)⟩).trans (F₅.sub subW)
  · rw [P₅.blk k hk]
    simp only [hk, ↓reduceIte]
    rw [X₄ k hk]

end VG.Proof.AesOcb.PPC64LE
