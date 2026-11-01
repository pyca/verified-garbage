module

public import VerifiedGarbage.Proof.AesOcb.RISCV64.Pass
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Args
import VerifiedGarbage.Proof.AesOcb.RISCV64.Words
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-OCB on RISCV64: the whole blocks (`whole`)

Untrusted: everything here is checked by Lean. `whole f pre post` runs a
pass with `pre` over the `m` whole blocks of the data, calls `f` on all of
them (`callBlocks_ok`), copies `Offset_0` back and runs a pass with `post`
(`whole_ok`): each block becomes `G (X ⊕ Offset_i) ⊕ Offset_i`, and the
checksum is the second pass's. As on PPC64LE
(`Proof/AesOcb/PPC64LE/Whole.lean`), but the data's address is loaded from
its slot in `W` (`Slots`), which the passes and the call keep.
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.RISCV64.Steps VG.Impl.AesOcb.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.RISCV64 (in_left in_off shr4 Keeps)
open VG.Impl.AesGcm.RISCV64 (dataO)

/-- What `whole` writes: the offset and the checksum, `L_{ntz(i)}`, the
copy of a block, the working space of the functions called and the data. -/
abbrev wholeR (W D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 32⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 256, 16⟩,
    ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨D, n⟩]

theorem wholeR_mut {W D : Addr} {n : Nat} {m m' : Mem} (h : Frame (wholeR W D n) m m') :
    Frame (mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact in_mutA (by decide)
  · exact in_mutA (by decide)
  · exact in_mutB (by decide) (by decide)
  · exact in_mutB (by decide) (by decide)
  · exact in_mutD fun _ h => h

/-- The data's address, in its slot, after writes within `wholeR`. -/
theorem slot_kept {K W D : Addr} {n : Nat} (L : Lay K W) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {m m' : Mem} (h : Frame (wholeR W D n) m m') :
    m'.readW (W + BitVec.ofNat 64 dataO) 64 = m.readW (W + BitVec.ofNat 64 dataO) 64 :=
  (wholeR_mut h).readW (r := ⟨W + BitVec.ofNat 64 dataO, 8⟩) (Region.contains_self _ _)
    (kept_mut L hD ⟨by decide, by decide⟩) (by decide)

/-- The first `k` bytes of a buffer, as a buffer at the same place. -/
theorem DBuf.take' {K W : Addr} {s : State} {D : Addr} {n k : Nat} (h : DBuf K W s D n) (hk : k ≤ n) :
    DBuf K W s D k := by
  have := h.slice (a := 0) (k := k) (by omega)
  rwa [BitVec.add_zero] at this

/-- The `m` blocks of the data, `len` (in `s11`) bytes at the address in
its slot. -/
theorem dataArgs_ok {W D : Addr} {t : State} (hs0 : t.gpr .s0 = W)
    (hal : (W + BitVec.ofNat 64 dataO).toNat % 8 = 0) (hin : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 dataO) 8)
    (hS : t.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D) {len : Nat} (hl : len < 2 ^ 64)
    (h11 : t.gpr .s11 = BitVec.ofNat 64 len) :
    ArgsOk [.load .d .a2 .s0 dataO, .shift .srl .d .a3 .s11 4] t D (len / 16) := by
  refine ⟨(t.write .a2 (t.mem.readW (t.gpr .s0 + BitVec.ofNat 64 dataO) 64)).write .a3
      ((t.write .a2 (t.mem.readW (t.gpr .s0 + BitVec.ofNat 64 dataO) 64)).gpr .s11 >>> 4), ?_,
    by rw [gpr_write_of_ne _ _ (by decide), gpr_write_self, hs0, hS],
    by rw [gpr_write_self, gpr_write_of_ne _ _ (by decide), h11, shr4 hl],
    fun r h5 h6 => by rw [gpr_write_of_ne _ _ h6, gpr_write_of_ne _ _ h5], ⟨rfl, rfl, rfl, rfl⟩⟩
  simp only [runBlock_cons, runStep_some,
    exec_load_d (show dataO < 2048 by decide) (by rw [hs0]; exact hal) (by rw [hs0]; exact hin)]
  rfl

/-- The start of a pass: `s4 ← D`, `s5 ← m`, `s6 ← 1`. -/
theorem passStart_ok {W D : Addr} {t : State} (hs0 : t.gpr .s0 = W)
    (hal : (W + BitVec.ofNat 64 dataO).toNat % 8 = 0) (hin : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 dataO) 8)
    (hS : t.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D) {len : Nat} (hl : len < 2 ^ 64)
    (h11 : t.gpr .s11 = BitVec.ofNat 64 len) :
    WP isa (.block passStart) t fun t' =>
      t'.gpr .s4 = D + BitVec.ofNat 64 (16 * 0) ∧ t'.gpr .s5 = BitVec.ofNat 64 (len / 16 - 0) ∧
      t'.gpr .s6 = BitVec.ofNat 64 (0 + 1) ∧ (∀ r, r ∉ [.s4, .s5, .s6] → t'.gpr r = t.gpr r) ∧ Keeps t t' := by
  unfold passStart
  refine wp_ld (a := W + BitVec.ofNat 64 dataO) (by decide) (by rw [hs0]) hal hin fun t₁ u₁ =>
    wp_srl (by decide) fun t₂ u₂ => wp_li (imm := 1) (by decide) fun t₃ u₃ => WP.block_nil
    ⟨?_, ?_, ?_, fun r hr => ?_, ⟨by rw [u₃.mem, u₂.mem, u₁.mem], by rw [u₃.rd, u₂.rd, u₁.rd],
      by rw [u₃.wr, u₂.wr, u₁.wr], by rw [u₃.sp, u₂.sp, u₁.sp]⟩⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hS]; simp
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h11, shr4 hl]; rfl
  · rw [u₃.gpr]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₃.other _ hr.2.2, u₂.other _ hr.2.1, u₁.other _ hr.1]

/-- What `whole` leaves. -/
structure WholePost (V : Reg → BitVec 64) (sp D : Addr) (m : Nat) (O0 l : Block) (Z : Nat → Block) (ck : Block)
    (t t' : State) : Prop where
  env : Env V sp t'
  frame : Frame (wholeR (V .s0) D (16 * m)) t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  blk : ∀ k < m, blockAtMem t'.mem (D + BitVec.ofNat 64 (16 * k)) = Z k ^^^ offAt O0 l (k + 1)
  ofs : blockAtMem t'.mem (V .s0 + BitVec.ofNat 64 ofsO) = offAt O0 l m
  ck : blockAtMem t'.mem (V .s0 + BitVec.ofNat 64 ckO) = ck

/-- A pass's writes, within `wholeR`. -/
theorem pass_sub {W D : Addr} {n : Nat} :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 lO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 ofsO, 16⟩,
      ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩, ⟨D, n⟩], ∃ r' ∈ wholeR W D n,
        Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
  · exact ⟨_, List.mem_cons_self .., Offset.sub _ (d := 16) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Offset.sub _ (d := 32) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
  · exact ⟨⟨D, n⟩, by simp, fun _ h => h⟩

theorem whole_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksRISCV64 f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksRISCV64 f).post s s')
    (nf : c.noFrames = true) {G : List Byte → Cipher}
    (hcall : ∀ {s s' : State} {K D S : Addr} {R n : Nat}, BPost f s K D S R n s' → ∀ i < n,
      blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) = G (bytesAt s.mem K (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))))
    {pre post : Prog isa} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    {V : Reg → BitVec 64} {sp : Addr}
    (hB1 : BodyOk (V .s0) pre (fun b o => b ^^^ o) fC1) (hB2 : BodyOk (V .s0) post (fun b o => b ^^^ o) fC2)
    (L : Lay (V .s2) (V .s0)) {t : State} (E : Env V sp t)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) {len : Nat}
    (h11 : V .s11 = BitVec.ofNat 64 len) {D : Addr} (hS : t.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hD : DBuf (V .s2) (V .s0) t D len) (hm0 : 0 < len / 16)
    {O0 l : Block}
    (hofs : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * i)))
      (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 (len / 16))
    (hckF2 : ∀ i, ckF2 (i + 1) = fC2 (ckF2 i)
      (G (bytesAt t.mem (V .s2) (16 * (R + 1)))
        (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
      (offAt O0 l (i + 1))) :
    WP isa (whole (.call name c) pre post) t (WholePost V sp D (len / 16) O0 l
      (fun k => G (bytesAt t.mem (V .s2) (16 * (R + 1)))
        (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
      (ckF2 (len / 16)) t) := by
  have hl := hD.lt
  generalize hmd : len / 16 = m at *
  have hmn : 16 * m ≤ len := by omega
  have hDm := hD.take' hmn
  have hal := L.alW (d := dataO) (by decide)
  -- the first pass
  unfold whole
  refine WP.seq (WP.mono (passStart_ok E.s0 hal (E.perm.wR (by decide)) hS hl (E.s11.trans h11))
    fun s₁ ⟨s4₁, s5₁, s6₁, g₁, k₁⟩ => ?_)
  rw [hmd] at s5₁
  have E₁ := E.others g₁ k₁.sp k₁.rd k₁.wr
  have hD₁ : DBuf (V .s2) (V .s0) s₁ D (16 * m) := hDm.of_eq k₁.rd k₁.wr
  have P₀ : PassInv V sp D m O0 l (fun k => blockAtMem s₁.mem (D + BitVec.ofNat 64 (16 * k)))
      (fun b o => b ^^^ o) ckF1 s₁ s₁ 0 :=
    { env := E₁, frame := Frame.refl _ _, rd := rfl, wr := rfl, s4 := s4₁, s6 := s6₁, s5 := s5₁
      ofs := by rw [k₁.mem, hofs]; rfl
      ck := by rw [k₁.mem, hck]
      blk := fun k _ => by simp
      l0 := by rw [k₁.mem, hl0]
      gpr := fun _ _ => rfl }
  refine WP.seq (WP.mono (pass_ok L hB1 (fun i _ => by rw [hckF1, k₁.mem]) hD₁ hm0 P₀) fun s₂ P₂ => ?_)
  have hD₂ : DBuf (V .s2) (V .s0) s₂ D (16 * m) := hD₁.of_eq P₂.rd P₂.wr
  have F₂ : Frame (wholeR (V .s0) D (16 * m)) t.mem s₂.mem := by rw [← k₁.mem]; exact P₂.frame.sub pass_sub
  have S₂ : s₂.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D := by rw [slot_kept L hD₁.w F₂, hS]
  refine WP.assoc (WP.seq (WP.mono (callBlocks_ok (f := f) L ok nf hR hs3 P₂.env
    (fun s₃ g₃ k₃ => by
      have := dataArgs_ok (t := s₃) (by rw [g₃ _ (by decide) (by decide) (by decide), P₂.env.s0]) hal
        (by rw [k₃.rd, k₃.wr]; exact P₂.env.perm.wR (by decide)) (by rw [k₃.mem, S₂]) hl
        (by rw [g₃ _ (by decide) (by decide) (by decide), P₂.env.s11, h11])
      rwa [hmd] at this) (dstD hD₂)) fun s₃ P₃ => ?_))
  have E₃ := P₃.env P₂.env
  have kC : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨D, 16 * m⟩ →
      (⟨Q, 16⟩ : Region).Disjoint ⟨V .s0 + BitVec.ofNat 64 512, 2048⟩ → blockAtMem s₃.mem Q = blockAtMem s₂.mem Q :=
    fun h₁ h₂ => blockAtMem_frame P₃.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁
      · exact h₂
  have kWP : ∀ {d : Nat}, (d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 96) ∨ (112 ≤ d ∧ d + 16 ≤ 256) ∨
      (272 ≤ d ∧ d + 16 ≤ 512)) →
      blockAtMem s₃.mem (V .s0 + BitVec.ofNat 64 d) = blockAtMem s₁.mem (V .s0 + BitVec.ofNat 64 d) := fun hd => by
    rw [kC ((hD₂.w.sub_right (Lay.wSub (by omega))).symm) (L.w_w (.inl (by omega)) (by omega) (by decide)),
      blockAtMem_frame P₂.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact L.w_w (a := _) (d := 96) (k := 16) (by omega) (by omega) (by decide)
      · exact L.w_w (a := _) (d := 16) (k := 16) (by omega) (by omega) (by decide)
      · exact L.w_w (a := _) (d := 32) (k := 16) (by omega) (by omega) (by decide)
      · exact L.w_w (a := _) (d := 256) (k := 16) (by omega) (by omega) (by decide)
      · exact (hD₁.w.sub_right (Lay.wSub (by omega))).symm)]
  have o0₃ : blockAtMem s₃.mem (V .s0 + BitVec.ofNat 64 o0O) = O0 := by rw [kWP (by decide), k₁.mem, ho0]
  have F₃ : Frame (wholeR (V .s0) D (16 * m)) t.mem s₃.mem :=
    F₂.trans (P₃.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨D, 16 * m⟩, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩)
  -- `Offset_0` again
  refine WP.seq (WP.block_append (WP.mono (copy16_ok (s := s₃) (a := o0O) (d := ofsO) L.wal (by decide)
    (by decide) E₃.s0 (E₃.perm.wR (by decide)) (E₃.perm.wR (by decide)) (E₃.perm.wW (by decide))
    (E₃.perm.wW (by decide))) fun s₄a B₄ => ?_))
  have F₄a : Frame (wholeR (V .s0) D (16 * m)) t.mem s₄a.mem :=
    F₃.trans (B₄.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub _ (d := 16) (n := 16) (e := 16) (k := 32) (by decide)
        (by decide)⟩)
  refine WP.mono (passStart_ok (t := s₄a) (D := D) (by rw [B₄.gpr _ (by decide), E₃.s0]) hal
    (by rw [B₄.rd, B₄.wr]; exact E₃.perm.wR (by decide)) (by rw [slot_kept L hD₁.w F₄a, hS]) hl
    (by rw [B₄.gpr _ (by decide), E₃.s11, h11])) fun s₄ ⟨s4₄, s5₄, s6₄, g₄, k₄⟩ => ?_
  have E₄a := E₃.others B₄.gpr B₄.sp B₄.rd B₄.wr
  rw [hmd] at s5₄
  have E₄ := E₄a.others g₄ k₄.sp k₄.rd k₄.wr
  have hD₄ : DBuf (V .s2) (V .s0) s₄ D (16 * m) :=
    hD₂.of_eq (by rw [k₄.rd, B₄.rd, P₃.rd]) (by rw [k₄.wr, B₄.wr, P₃.wr])
  have kB₄ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨V .s0, 2560⟩ → blockAtMem s₄.mem Q = blockAtMem s₃.mem Q :=
    fun hQ => by
      rw [k₄.mem]; exact blockAtMem_frame B₄.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hQ.sub_right (Lay.wSub (by decide))
  have hK : bytesAt s₂.mem (V .s2) (16 * (R + 1)) = bytesAt t.mem (V .s2) (16 * (R + 1)) := by
    have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
    rw [Proof.Cmac.bytesAt_frame P₂.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact hD₁.k.sub_left (Region.sub_prefix hRb)) (by omega), k₁.mem]
  have X₄ : ∀ k < m, blockAtMem s₄.mem (D + BitVec.ofNat 64 (16 * k)) =
      G (bytesAt t.mem (V .s2) (16 * (R + 1)))
        (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)) :=
    fun k hk => by
      rw [kB₄ (hD₂.slice (a := 16 * k) (k := 16) (by omega)).w, hcall P₃ k hk, hK, P₂.blk k hk]
      simp only [hk, ↓reduceIte, k₁.mem]
  have ck₃ : blockAtMem s₃.mem (V .s0 + BitVec.ofNat 64 ckO) = ckF2 0 := by
    rw [kC ((hD₂.w.sub_right (Lay.wSub (by decide))).symm) (L.w_w (.inl (by decide)) (by decide) (by decide)),
      P₂.ck, hckF2₀]
  have P₀' : PassInv V sp D m O0 l (fun k => blockAtMem s₄.mem (D + BitVec.ofNat 64 (16 * k)))
      (fun b o => b ^^^ o) ckF2 s₄ s₄ 0 :=
    { env := E₄, frame := Frame.refl _ _, rd := rfl, wr := rfl, s4 := s4₄, s6 := s6₄, s5 := s5₄
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
  refine WP.mono (pass_ok L hB2 (fun i hi => by rw [hckF2, X₄ i hi]) hD₄ hm0 P₀') fun s₅ P₅ => ?_
  refine ⟨P₅.env, ?_, by rw [P₅.rd, k₄.rd, B₄.rd, P₃.rd, P₂.rd, k₁.rd],
    by rw [P₅.wr, k₄.wr, B₄.wr, P₃.wr, P₂.wr, k₁.wr], fun k hk => ?_, P₅.ofs, P₅.ck⟩
  · have F₅ := P₅.frame
    rw [k₄.mem] at F₅
    exact F₄a.trans (F₅.sub pass_sub)
  · rw [P₅.blk k hk]
    simp only [hk, ↓reduceIte]
    rw [X₄ k hk]

end VG.Proof.AesOcb.RISCV64
