import VerifiedGarbage.Proof.AesOcb.X86.Hash

/-!
# AES-OCB on x86: a pass over the whole blocks (`pass`)

Untrusted: everything here is checked by Lean. `pass body` goes over the
`m` whole blocks of the data at `D`: for block `i` it computes
`Offset_{i+1}` (`lNtz_ok`, `xor16W_ok`), then runs `body` on the block, which
replaces it with `fB` of it and the offset, and the checksum with `fC` of
them (`BodyOk`: `xorOfs`, `addCk ++ xorOfs`, `xorOfs ++ addCk`); `pass_ok`
gives the blocks and the checksum after all `m`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq runBlock_app_of toNat_ofNat32 toNat_add32 covers_off in_off
  in_left toNat_w64 add_ofNat_assoc32)

/-- A block of `B` that the code may read and write, apart from `W`. -/
structure BBlk (p : Prm) (t : State) (B : BitVec 32) : Prop where
  fit : B.toNat + 16 ≤ 2 ^ 32
  w : (⟨w64 B, 16⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩
  wr : Covers [⟨w64 B, 16⟩] t.wr
  inm : InMut p [⟨w64 B, 16⟩]

theorem BBlk.of_eq {p : Prm} {t t' : State} {B : BitVec 32} (h : BBlk p t B) (hwr : t'.wr = t.wr) : BBlk p t' B :=
  ⟨h.fit, h.w, by rw [hwr]; exact h.wr, h.inm⟩

/-- A word of `W` after a word of a block `B` apart from it written. -/
theorem readW_BW {p : Prm} (L : Lay p) {B : Addr}
    (hd : (⟨B, 16⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩) (m : Mem) (v : BitVec 32) {a b : Nat} (ha : a + 4 ≤ 2560)
    (hb : b + 4 ≤ 16) :
    (m.writeW (B + BitVec.ofNat 64 b) v).readW (w64 p.W + BitVec.ofNat 64 a) 32 =
      m.readW (w64 p.W + BitVec.ofNat 64 a) 32 :=
  Mem.readW_writeW_sep (hd.symm.sep (Offset.contains_base _ ha (by have := L.ww; omega))
    (Offset.contains_base _ hb (by omega))) (by decide)

/-- What a body does to the block at `B` (in `esi`) and the checksum, with
the offset at `W + ofsO`. -/
def BodyOk (p : Prm) (body : List Instr) (fB : Block → Block → Block) (fC : Block → Block → Block → Block) : Prop :=
  ∀ (t : State) (B : BitVec 32), Env p t → t.gpr .esi = B → BBlk p t B →
    ∃ t', runBlock isa body t = some t' ∧
      blockAtMem t'.mem (w64 B) = fB (blockAtMem t.mem (w64 B)) (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO)) ∧
      blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 ckO) = fC (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO))
        (blockAtMem t.mem (w64 B)) (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO)) ∧
      Frame [⟨w64 B, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩] t.mem t'.mem ∧
      (∀ r, r ≠ .eax → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr

theorem xorOfs_ok {p : Prm} (L : Lay p) : BodyOk p xorOfs (fun b o => b ^^^ o) (fun c _ _ => c) := by
  intro t B E hsi hB
  have aB : ∀ {k : Nat}, k < 16 → w64 (B + BitVec.ofNat 32 k) = w64 B + BitVec.ofNat 64 k := fun hk =>
    w64_add (by have := hB.fit; omega)
  have rB : ∀ {k : Nat}, k + 4 ≤ 16 → InRegions (t.rd ++ t.wr) (w64 B + BitVec.ofNat 64 k) 4 := fun hk =>
    in_left (in_off hB.wr hk (by decide))
  have wB : ∀ {k : Nat}, k + 4 ≤ 16 → InRegions t.wr (w64 B + BitVec.ofNat 64 k) 4 := fun hk =>
    in_off hB.wr hk (by decide)
  obtain ⟨t', run, m', g', rd', wr'⟩ : ∃ t', runBlock isa xorOfs t = some t' ∧
      t'.mem = xor2Mem t.mem (w64 B) (w64 p.W + BitVec.ofNat 64 ofsO) (w64 B) ∧
      (∀ r, r ≠ .eax → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
    refine ⟨_, by grun [xorOfs, List.flatMap_cons, List.flatMap_nil, hsi, aB, rB, wB, E.ebp, L.aW, E.perm.wR,
      (readW_BW L hB.w)], ?_, fun r h => by gregs [h], by gmems [], by gmems []⟩
    gmems [(readW_BW L hB.w)]
    simp only [xor2Mem, Proof.Cmac.store4, add_ofNat_assoc, Nat.reduceAdd,
      show w64 B + BitVec.ofNat 64 0 = w64 B from BitVec.add_zero _]
  have fB : Frame [⟨w64 B, 16⟩] t.mem t'.mem := by rw [m']; exact Proof.Cmac.frame_store4 _ _ _ _ _
  refine ⟨t', run, by rw [m', xor2Mem_block], ?_, fB.mono (by simp), g', rd', wr'⟩
  exact Proof.Ocb.blockAtMem_frame fB fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hB.w.sub_right (Lay.wSub (by decide))).symm

/-- `addCk`: the checksum XORed with the block at `B`. -/
theorem addCk_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {B : BitVec 32} (hsi : t.gpr .esi = B)
    (hB : BBlk p t B) :
    ∃ t', runBlock isa addCk t = some t' ∧
      t'.mem = xorMem16 t.mem (w64 B) 0 (w64 p.W) ckO ∧
      (∀ r, r ≠ .eax → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr :=
  xor16R_ok L E (b := .esi) (by decide) hsi hB.fit hB.w (Proof.AesGcm.X86.covers_left hB.wr) (s := 0) (d := ckO) (by decide) (by decide)

theorem blockAtMem_ck {p : Prm} {B : BitVec 32} (hBW : (⟨w64 B, 16⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩) {m m' : Mem}
    (h : Frame [⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩] m m') : blockAtMem m' (w64 B) = blockAtMem m (w64 B) :=
  Proof.Ocb.blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hBW.sub_right (Lay.wSub (by decide))

theorem blockAtMem_ofs_ck {p : Prm} {m m' : Mem} (h : Frame [⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩] m m') :
    blockAtMem m' (w64 p.W + BitVec.ofNat 64 ofsO) = blockAtMem m (w64 p.W + BitVec.ofNat 64 ofsO) :=
  Proof.Ocb.blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)

theorem addCk_val (m : Mem) (B : BitVec 32) (W : BitVec 32) :
    blockAtMem (xorMem16 m (w64 B) 0 (w64 W) ckO) (w64 W + BitVec.ofNat 64 ckO) =
      blockAtMem m (w64 W + BitVec.ofNat 64 ckO) ^^^ blockAtMem m (w64 B) := by
  rw [xorMem16_block, show w64 B + BitVec.ofNat 64 0 = w64 B from BitVec.add_zero _]

/-- `seal`'s first pass: the checksum of the block, then the block XORed with the offset. -/
theorem sealPre_ok {p : Prm} (L : Lay p) :
    BodyOk p (addCk ++ xorOfs) (fun b o => b ^^^ o) (fun c b _ => c ^^^ b) := by
  intro t B E hsi hB
  obtain ⟨t₁, run₁, m₁, g₁, rd₁, wr₁⟩ := addCk_ok L E hsi hB
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩] t.mem t₁.mem := by rw [m₁]; exact xorMem16_frame _ _ _ _ _
  have E₁ : Env p t₁ := E.mut L (by rw [g₁ _ (by decide), E.ebp]) (by rw [g₁ _ (by decide), E.esp]) rd₁ wr₁
    (frame_toMut f₁ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide)))
  obtain ⟨t₂, run₂, b₂, c₂, f₂, g₂, rd₂, wr₂⟩ := xorOfs_ok L t₁ B E₁ (by rw [g₁ _ (by decide), hsi]) (hB.of_eq wr₁)
  refine ⟨t₂, runBlock_app_of run₁ run₂, ?_, ?_, ?_, fun r h => ?_, by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · rw [b₂, blockAtMem_ck hB.w f₁, blockAtMem_ofs_ck f₁]
  · rw [c₂, m₁, addCk_val]
  · exact (f₁.mono (by simp)).trans f₂
  · rw [g₂ r h, g₁ r h]

/-- `open`'s third pass: the block XORed with the offset, then its checksum. -/
theorem openPost_ok {p : Prm} (L : Lay p) :
    BodyOk p (xorOfs ++ addCk) (fun b o => b ^^^ o) (fun c b o => c ^^^ (b ^^^ o)) := by
  intro t B E hsi hB
  obtain ⟨t₁, run₁, b₁, c₁, f₁, g₁, rd₁, wr₁⟩ := xorOfs_ok L t B E hsi hB
  have E₁ : Env p t₁ := E.mut L (by rw [g₁ _ (by decide), E.ebp]) (by rw [g₁ _ (by decide), E.esp]) rd₁ wr₁
    (frame_toMut f₁ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hB.inm _ (List.mem_singleton_self _)
      · exact inMut_w p (.inl (by decide)))
  obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := addCk_ok L E₁ (by rw [g₁ _ (by decide), hsi]) (hB.of_eq wr₁)
  have f₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩] t₁.mem t₂.mem := by rw [m₂]; exact xorMem16_frame _ _ _ _ _
  refine ⟨t₂, runBlock_app_of run₁ run₂, ?_, ?_, ?_, fun r h => ?_, by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · rw [blockAtMem_ck hB.w f₂, b₁]
  · rw [m₂, addCk_val, c₁, b₁]
  · exact f₁.trans (f₂.mono (by simp))
  · rw [g₂ r h, g₁ r h]

/-- Block `i` of the data. -/
theorem dblk {p : Prm} (L : Lay p) {t : State} (E : Env p t) {i : Nat} (hi : 16 * (i + 1) ≤ p.n) :
    BBlk p t (p.D + BitVec.ofNat 32 (16 * i)) := by
  have hd := L.dw
  have a16 : w64 (p.D + BitVec.ofNat 32 (16 * i)) = w64 p.D + BitVec.ofNat 64 (16 * i) := w64_add (by omega)
  have sub : Region.Sub ⟨w64 (p.D + BitVec.ofNat 32 (16 * i)), 16⟩ ⟨w64 p.D, p.n⟩ := by
    rw [a16]; exact Offset.sub_base _ (by omega)
  refine ⟨by rw [toNat_add32 (by omega)]; omega, L.d_w.sub_left sub, ?_, fun r hr => ?_⟩
  · rw [a16]; exact covers_off E.perm.d (by omega) (by omega)
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp, sub⟩

/-- A pass over the `m` whole blocks of the data (`X k` at its start, `t₀`),
after `i` of them. -/
structure PassInv (p : Prm) (m : Nat) (O0 l : Block) (X : Nat → Block) (fB : Block → Block → Block)
    (ckF : Nat → Block) (t₀ t : State) (i : Nat) : Prop where
  env : Env p t
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩,
    ⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩, ⟨w64 p.D, 16 * m⟩] t₀.mem t.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  esi : t.gpr .esi = p.D + BitVec.ofNat 32 (16 * i)
  edi : t.gpr .edi = BitVec.ofNat 32 (i + 1)
  ebx : t.gpr .ebx = BitVec.ofNat 32 (m - i)
  ofs : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) = offAt O0 l i
  ck : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) = ckF i
  blk : ∀ k < m, blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) =
    if k < i then fB (X k) (offAt O0 l (k + 1)) else X k
  l0 : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0
  gpr : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → t.gpr r = t₀.gpr r

theorem pass_step {p : Prm} (L : Lay p) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : BodyOk p body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hm : 16 * m ≤ p.n) {t : State} {i : Nat} (hi : i < m)
    (P : PassInv p m O0 l X fB ckF t₀ t i) :
    WP isa (.seq nextOffset (.block (body ++ nextBlock))) t fun t' =>
      PassInv p m O0 l X fB ckF t₀ t' (i + 1) ∧ t'.zf = some (decide (m - (i + 1) = 0)) := by
  have hn := L.n32
  have hd := L.dw
  have a16 : ∀ k, 16 * (k + 1) ≤ p.n → w64 (p.D + BitVec.ofNat 32 (16 * k)) = w64 p.D + BitVec.ofNat 64 (16 * k) :=
    fun k hk => w64_add (by omega)
  unfold nextOffset
  refine WP.seq (WP.seq (WP.mono (lNtz_ok L P.env (by omega) (by omega) P.edi P.l0) fun t₁ P₁ => ?_))
  have E₁ := P₁.env L P.env
  obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := xor16W_ok L E₁ (s := lO) (d := ofsO) (by decide) (by decide)
    (.inr (by decide))
  refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
  have E₂ : Env p t₂ := E₁.mut L (by rw [g₂ _ (by decide), E₁.ebp]) (by rw [g₂ _ (by decide), E₁.esp]) rd₂ wr₂
    (frame_toMut (by rw [m₂]; exact xorMem16_frame _ _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide)))
  have g₂' : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t₂.gpr r = t.gpr r := fun r h₁ h₂ h₃ => by
    rw [g₂ r h₁, P₁.gpr r h₁ h₂ h₃]
  have fW₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩,
      ⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩] t.mem t₂.mem :=
    (P₁.frame.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp).trans (by
      rw [m₂]
      exact (xorMem16_frame _ _ _ _ _).mono fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; simp)
  have kW₂ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩ → blockAtMem t₂.mem Q = blockAtMem t.mem Q :=
    fun hQ => Proof.Ocb.blockAtMem_frame fW₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hQ.sub_right (Lay.wSub (by decide))
  have ofs₂ : blockAtMem t₂.mem (w64 p.W + BitVec.ofNat 64 ofsO) = offAt O0 l (i + 1) := by
    rw [m₂, xorMem16_block, Proof.Ocb.blockAtMem_frame P₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide)), P.ofs, P₁.val]
    rfl
  have ck₂ : blockAtMem t₂.mem (w64 p.W + BitVec.ofNat 64 ckO) = ckF i := by
    rw [Proof.Ocb.blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide)), P.ck]
  have hBi := dblk L E₂ (i := i) (by omega)
  have Bi₂ : blockAtMem t₂.mem (w64 (p.D + BitVec.ofNat 32 (16 * i))) = X i := by
    rw [kW₂ hBi.w, a16 i (by omega), P.blk i hi]; simp
  obtain ⟨t₃, run₃, blk₃, ck₃, fr₃, g₃, rd₃, wr₃⟩ := hB t₂ _ E₂
    (by rw [g₂' _ (by decide) (by decide) (by decide), P.esi]) hBi
  have g₃' : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t₃.gpr r = t.gpr r := fun r h₁ h₂ h₃ => by
    rw [g₃ r h₁, g₂' r h₁ h₂ h₃]
  have si₃ : t₃.gpr .esi = p.D + BitVec.ofNat 32 (16 * i) := by rw [g₃' _ (by decide) (by decide) (by decide), P.esi]
  have di₃ : t₃.gpr .edi = BitVec.ofNat 32 (i + 1) := by rw [g₃' _ (by decide) (by decide) (by decide), P.edi]
  have bx₃ : t₃.gpr .ebx = BitVec.ofNat 32 (m - i) := by rw [g₃' _ (by decide) (by decide) (by decide), P.ebx]
  obtain ⟨t₄, run₄, si₄, di₄, bx₄, zf₄, g₄, m₄, rd₄, wr₄⟩ : ∃ t₄, runBlock isa nextBlock t₃ = some t₄ ∧
      t₄.gpr .esi = p.D + BitVec.ofNat 32 (16 * (i + 1)) ∧ t₄.gpr .edi = BitVec.ofNat 32 (i + 1 + 1) ∧
      t₄.gpr .ebx = BitVec.ofNat 32 (m - (i + 1)) ∧ t₄.zf = some (decide (m - (i + 1) = 0)) ∧
      (∀ r, r ≠ .ebx → r ≠ .esi → r ≠ .edi → t₄.gpr r = t₃.gpr r) ∧ t₄.mem = t₃.mem ∧ t₄.rd = t₃.rd ∧
      t₄.wr = t₃.wr := by
    refine ⟨_, by grun [nextBlock], ?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems [],
      by gmems []⟩
    · gregs [si₃]; rw [add_ofNat_assoc32, show 16 * i + 16 = 16 * (i + 1) by omega]
    · gregs [di₃]; rw [← BitVec.ofNat_add]
    · gregs [bx₃]; rw [sub1_32 (by omega) (by omega), show m - i - 1 = m - (i + 1) by omega]
    · gmems [bx₃]
      rw [sub1_32 (by omega) (by omega), beq_zero32 (by omega)]
      exact congrArg some (decide_eq_decide.mpr (by omega))
  refine WP.of_runBlock ⟨t₄, runBlock_app_of run₃ run₄, ?_⟩
  have kB₃ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨w64 (p.D + BitVec.ofNat 32 (16 * i)), 16⟩ →
      (⟨Q, 16⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩ → blockAtMem t₃.mem Q = blockAtMem t.mem Q := fun h₁ h₂ => by
    rw [Proof.Ocb.blockAtMem_frame fr₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁
      · exact h₂.sub_right (Lay.wSub (by decide))), kW₂ h₂]
  have kW₃ : ∀ {d : Nat}, (d + 16 ≤ ckO ∨ ckO + 16 ≤ d) → d + 16 ≤ 2560 →
      blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 d) = blockAtMem t₂.mem (w64 p.W + BitVec.ofNat 64 d) := fun h h' =>
    Proof.Ocb.blockAtMem_frame fr₃ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hBi.w.sub_right (Lay.wSub h')).symm
      · exact Lay.w_w h h' (by decide)
  refine ⟨⟨?_, ?_, ?_, ?_, si₄, di₄, bx₄, ?_, ?_, fun k hk => ?_, ?_, fun r h₁ h₂ h₃ h₄ h₅ h₆ => ?_⟩, zf₄⟩
  · exact E₂.mut L (by rw [g₄ _ (by decide) (by decide) (by decide), g₃ _ (by decide), E₂.ebp])
      (by rw [g₄ _ (by decide) (by decide) (by decide), g₃ _ (by decide), E₂.esp]) (by rw [rd₄, rd₃])
      (by rw [wr₄, wr₃]) (frame_toMut (by rw [m₄]; exact fr₃) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hBi.inm _ (List.mem_singleton_self _)
        · exact inMut_w p (.inl (by decide)))
  · rw [m₄]
    exact P.frame.trans ((fW₂.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> simp).trans
      (fr₃.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨w64 p.D, 16 * m⟩, by simp, by rw [a16 i (by omega)]; exact Offset.sub_base _ (by omega)⟩
        · exact ⟨_, by simp, fun _ h => h⟩))
  · rw [rd₄, rd₃, rd₂, P₁.rd, P.rd]
  · rw [wr₄, wr₃, wr₂, P₁.wr, P.wr]
  · rw [m₄, kW₃ (.inl (by decide)) (by decide), ofs₂]
  · rw [m₄, ck₃, ck₂, Bi₂, ofs₂, hckF i hi]
  · rw [m₄]
    by_cases hki : k = i
    · subst hki
      rw [← a16 k (by omega), blk₃, Bi₂, ofs₂]; simp
    · have hBk := dblk L E₂ (i := k) (by omega)
      rw [← a16 k (by omega), kB₃ (by
        rw [a16 k (by omega), a16 i (by omega)]; exact Offset.disjoint _ (by omega) (by omega) (by omega)) hBk.w,
        a16 k (by omega), P.blk k hk]
      by_cases hk' : k < i
      · simp [hk', show k < i + 1 by omega]
      · simp [hk', show ¬ k < i + 1 by omega]
  · rw [m₄, kW₃ (.inr (by decide)) (by decide), Proof.Ocb.blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide)), P.l0]
  · rw [g₄ r h₂ h₅ h₆, g₃' r h₁ h₃ h₄, P.gpr r h₁ h₂ h₃ h₄ h₅ h₆]

theorem pass_ok {p : Prm} (L : Lay p) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : BodyOk p body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hm : 16 * m ≤ p.n) (hm0 : 0 < m) {t : State} (P : PassInv p m O0 l X fB ckF t₀ t 0) :
    WP isa (pass body) t (fun t' => PassInv p m O0 l X fB ckF t₀ t' m) := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (u : State) => ∃ i, k = m - i ∧ i < m ∧ PassInv p m O0 l X fB ckF t₀ u i) ?_ (m - 0) _
    ⟨0, rfl, hm0, P⟩
  rintro k u ⟨i, rfl, hi, P⟩
  refine WP.mono (pass_step L hB hckF hm hi P) fun u' ⟨P', hz⟩ => ?_
  by_cases he : m - (i + 1) = 0
  · left
    exact ⟨(eval_ne hz).trans (by simp [he]), (show i + 1 = m by omega) ▸ P'⟩
  · right
    exact ⟨(eval_ne hz).trans (by simp [he]), m - (i + 1), by omega, i + 1, rfl, by omega, P'⟩

end VG.Proof.AesOcb.X86
