module

public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Env
import VerifiedGarbage.Proof.AesOcb.PPC64LE.LNtz
public import VerifiedGarbage.Proof.Ocb.Spec
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Words
import VerifiedGarbage.Proof.AesOcb.PPC64LE.PadTo
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.AesOcb.PPC64LE
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Ocb

/-!
# AES-OCB on PPC64LE: a pass over the whole blocks (`pass`)

Untrusted: everything here is checked by Lean. A pass over the `m` whole
blocks of the data computes each block's offset (`lNtz_ok`, `xorB_ok`),
replaces the block with `fB` of it and the offset, and the checksum with
`fC` of them (`BodyOk`: `xorOfs`, `addCk ++ xorOfs`, `xorOfs ++ addCk`);
`pass_ok` gives the blocks and the checksum after all `m`. As on AArch64
(`Proof/AesOcb/AArch64/Pass.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.PPC64LE (in_left in_off)
open VG.Proof.ChaCha20Poly1305.PPC64LE renaming wp_addi → cwp_addi, wp_subi → cwp_subi

/-- The registers a body writes. -/
abbrev bodyRegs : List Reg := [.r3, .r4]

/-- What a body does to the block at `B` (in `r24`) and the checksum, with
the offset at `W + ofsO`. -/
def BodyOk (W : Addr) (body : List Instr) (fB : Block → Block → Block) (fC : Block → Block → Block → Block) :
    Prop :=
  ∀ (t : State) (B : Addr), t.gpr .r24 = B → t.gpr .r31 = W →
    InRegions (t.rd ++ t.wr) B 8 → InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 8) 8 →
    InRegions t.wr B 8 → InRegions t.wr (B + BitVec.ofNat 64 8) 8 →
    Covers [⟨W, 2560⟩] t.wr → (⟨B, 16⟩ : Region).Disjoint ⟨W, 2560⟩ →
    WP isa (.block body) t fun t' =>
      blockAtMem t'.mem B = fB (blockAtMem t.mem B) (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO)) ∧
      blockAtMem t'.mem (W + BitVec.ofNat 64 ckO) = fC (blockAtMem t.mem (W + BitVec.ofNat 64 ckO))
        (blockAtMem t.mem B) (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO)) ∧
      Frame [⟨B, 16⟩, ⟨W + BitVec.ofNat 64 ckO, 16⟩] t.mem t'.mem ∧
      (∀ r, r ∉ bodyRegs → t'.gpr r = t.gpr r) ∧ t'.sp = t.sp ∧ t'.lr = t.lr ∧ t'.rd = t.rd ∧ t'.wr = t.wr

theorem add0 (B : Addr) : B + BitVec.ofNat 64 0 = B := BitVec.add_zero _

/-- `xorOfs`: the block at `B` XORed with the offset. -/
theorem xorOfs_ok' {W B : Addr} {t : State} (h24 : t.gpr .r24 = B) (h31 : t.gpr .r31 = W)
    (rB₀ : InRegions (t.rd ++ t.wr) B 8) (rB₈ : InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 8) 8)
    (wB₀ : InRegions t.wr B 8) (wB₈ : InRegions t.wr (B + BitVec.ofNat 64 8) 8) (hw : Covers [⟨W, 2560⟩] t.wr)
    (hBW : (⟨B, 16⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa (.block xorOfs) t (BlkStep B 0 (blockAtMem t.mem B ^^^ blockAtMem t.mem (W + BitVec.ofNat 64 ofsO))
      bodyRegs t) := by
  have e := add0 B
  have hb := xorB_ok (s := t) (P := B) (Q := W) (C := B) (pd := 0) (qd := ofsO) (cd := 0) (pb := .r24)
    (qb := .r31) (cb := .r24) (by decide) (by decide) (by decide) h24 h31 h24 (by decide) (by decide) (by decide)
    (by rw [e]; exact rB₀) rB₈ (in_left (in_off hw (by decide) (by decide)))
    (in_left (in_off hw (by decide) (by decide))) (by rw [e]; exact wB₀) wB₈
    (Offset.sep B (d := 8) (n := 8) (e := 0) (k := 8) (.inr (by decide)) (by decide) (by decide))
    (by
      rw [e]
      exact Region.Disjoint.sep (hBW.sub_right (Lay.wSub (W := W) (d := ofsO + 8) (n := 8) (by decide))).symm
        (Region.contains_self _ _) (contains_pre _ (by decide)))
  rw [e] at hb
  exact hb

/-- `addCk`: the checksum XORed with the block at `B`. -/
theorem addCk_ok {W B : Addr} {t : State} (h24 : t.gpr .r24 = B) (h31 : t.gpr .r31 = W)
    (rB₀ : InRegions (t.rd ++ t.wr) B 8) (rB₈ : InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 8) 8)
    (hw : Covers [⟨W, 2560⟩] t.wr) (hBW : (⟨B, 16⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa (.block addCk) t
      (BlkStep W ckO (blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ blockAtMem t.mem B) bodyRegs t) := by
  have e := add0 B
  have hb := xorB_ok (s := t) (P := W) (Q := B) (C := W) (pd := ckO) (qd := 0) (cd := ckO) (pb := .r31)
    (qb := .r24) (cb := .r31) (by decide) (by decide) (by decide) h31 h24 h31 (by decide) (by decide) (by decide)
    (in_left (in_off hw (by decide) (by decide))) (in_left (in_off hw (by decide) (by decide)))
    (by rw [e]; exact rB₀) rB₈ (in_off hw (by decide) (by decide)) (in_off hw (by decide) (by decide))
    (Offset.sep W (.inr (by decide)) (by decide) (by decide))
    (Region.Disjoint.sep (hBW.sub_right (Lay.wSub (W := W) (d := ckO) (n := 8) (by decide)))
      (Offset.contains_base B (d := 8) (n := 8) (k := 16) (by decide) (by decide)) (Region.contains_self _ _))
  rw [e] at hb
  exact hb

theorem blockAtMem_ck {W B : Addr} (hBW : (⟨B, 16⟩ : Region).Disjoint ⟨W, 2560⟩) {m m' : Mem}
    (h : Frame [⟨W + BitVec.ofNat 64 ckO, 16⟩] m m') : blockAtMem m' B = blockAtMem m B :=
  blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hBW.sub_right (Lay.wSub (by decide))

theorem blockAtMem_ofs_ck {W : Addr} {m m' : Mem}
    (h : Frame [⟨W + BitVec.ofNat 64 ckO, 16⟩] m m') :
    blockAtMem m' (W + BitVec.ofNat 64 ofsO) = blockAtMem m (W + BitVec.ofNat 64 ofsO) :=
  blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint W (d := 16) (n := 16) (e := 32) (k := 16) (.inl (by decide)) (by omega) (by omega)

theorem blockAtMem_B_ck {W B : Addr} (hBW : (⟨B, 16⟩ : Region).Disjoint ⟨W, 2560⟩) {m m' : Mem}
    (h : Frame [⟨B + BitVec.ofNat 64 0, 16⟩] m m') {d : Nat} (hd : d + 16 ≤ 2560) :
    blockAtMem m' (W + BitVec.ofNat 64 d) = blockAtMem m (W + BitVec.ofNat 64 d) :=
  blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [add0]; exact (hBW.sub_right (Lay.wSub hd)).symm

theorem xorOfs_ok {W : Addr} : BodyOk W xorOfs (fun b o => b ^^^ o) (fun c _ _ => c) := by
  intro t B h24 h31 rB₀ rB₈ wB₀ wB₈ hw hBW
  refine WP.mono (xorOfs_ok' h24 h31 rB₀ rB₈ wB₀ wB₈ hw hBW) fun t' Bk => ?_
  have f := Bk.frame
  have v := Bk.val
  rw [add0] at f v
  exact ⟨v, blockAtMem_frame f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hBW.sub_right (Lay.wSub (W := W) (d := ckO) (n := 16) (by decide))).symm),
    f.mono (by simp), Bk.gpr, Bk.sp, Bk.lr, Bk.rd, Bk.wr⟩

/-- `seal`'s first pass: the checksum of the block, then the block XORed with the offset. -/
theorem sealPre_ok {W : Addr} :
    BodyOk W (addCk ++ xorOfs) (fun b o => b ^^^ o) (fun c b _ => c ^^^ b) := by
  intro t B h24 h31 rB₀ rB₈ wB₀ wB₈ hw hBW
  refine WP.block_append (WP.mono (addCk_ok h24 h31 rB₀ rB₈ hw hBW) fun t₁ B₁ => ?_)
  refine WP.mono (xorOfs_ok t₁ B (by rw [B₁.gpr _ (by decide), h24]) (by rw [B₁.gpr _ (by decide), h31])
    (by rw [B₁.rd, B₁.wr]; exact rB₀) (by rw [B₁.rd, B₁.wr]; exact rB₈) (by rw [B₁.wr]; exact wB₀)
    (by rw [B₁.wr]; exact wB₈) (by rw [B₁.wr]; exact hw) hBW) fun t₂ ⟨b₂, c₂, f₂, g₂, sp₂, lr₂, rd₂, wr₂⟩ => ?_
  refine ⟨?_, ?_, (B₁.frame.mono (by simp)).trans f₂, fun r hr => by rw [g₂ r hr, B₁.gpr r hr],
    by rw [sp₂, B₁.sp], by rw [lr₂, B₁.lr], by rw [rd₂, B₁.rd], by rw [wr₂, B₁.wr]⟩
  · rw [b₂, blockAtMem_ck hBW B₁.frame, blockAtMem_ofs_ck B₁.frame]
  · rw [c₂, B₁.val]

/-- `open`'s third pass: the block XORed with the offset, then its checksum. -/
theorem openPost_ok {W : Addr} :
    BodyOk W (xorOfs ++ addCk) (fun b o => b ^^^ o) (fun c b o => c ^^^ (b ^^^ o)) := by
  intro t B h24 h31 rB₀ rB₈ wB₀ wB₈ hw hBW
  refine WP.block_append (WP.mono (xorOfs_ok t B h24 h31 rB₀ rB₈ wB₀ wB₈ hw hBW)
    fun t₁ ⟨b₁, c₁, f₁, g₁, sp₁, lr₁, rd₁, wr₁⟩ => ?_)
  refine WP.mono (addCk_ok (t := t₁) (by rw [g₁ _ (by decide), h24]) (by rw [g₁ _ (by decide), h31])
    (by rw [rd₁, wr₁]; exact rB₀) (by rw [rd₁, wr₁]; exact rB₈) (by rw [wr₁]; exact hw) hBW) fun t₂ B₂ => ?_
  refine ⟨?_, ?_, f₁.trans (B₂.frame.mono (by simp)), fun r hr => by rw [B₂.gpr r hr, g₁ r hr],
    by rw [B₂.sp, sp₁], by rw [B₂.lr, lr₁], by rw [B₂.rd, rd₁], by rw [B₂.wr, wr₁]⟩
  · rw [blockAtMem_ck hBW B₂.frame, b₁]
  · rw [B₂.val, c₁, b₁]

/-- The registers a pass writes. -/
abbrev passRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r12, .r24, .r25, .r26]

/-- A pass over the `m` whole blocks at `D` (`X k` at its start, `t₀`), after
`i` of them. -/
structure PassInv (V : Reg → BitVec 64) (sp D : Addr) (m : Nat) (O0 l : Block) (X : Nat → Block)
    (fB : Block → Block → Block) (ckF : Nat → Block) (t₀ t : State) (i : Nat) : Prop where
  env : Env V sp t
  frame : Frame [⟨V .r31 + BitVec.ofNat 64 lO, 16⟩, ⟨V .r31 + BitVec.ofNat 64 ofsO, 16⟩,
    ⟨V .r31 + BitVec.ofNat 64 ckO, 16⟩, ⟨D, 16 * m⟩] t₀.mem t.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  r24 : t.gpr .r24 = D + BitVec.ofNat 64 (16 * i)
  r26 : t.gpr .r26 = BitVec.ofNat 64 (i + 1)
  r25 : t.gpr .r25 = BitVec.ofNat 64 (m - i)
  ofs : blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ofsO) = offAt O0 l i
  ck : blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ckO) = ckF i
  blk : ∀ k < m, blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k)) =
    if k < i then fB (X k) (offAt O0 l (k + 1)) else X k
  l0 : blockAtMem t.mem (V .r31 + BitVec.ofNat 64 l0O) = lAt l 0
  gpr : ∀ r, r ∉ passRegs → t.gpr r = t₀.gpr r

theorem pass_step {V : Reg → BitVec 64} {sp D : Addr} (L : Lay (V .r29) (V .r31)) {m : Nat} {O0 l : Block}
    {X : Nat → Block} {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block}
    {body : List Instr} (hB : BodyOk (V .r31) body fB fC)
    (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hD : DBuf (V .r29) (V .r31) t₀ D (16 * m)) (hm : m < 2 ^ 60) {t : State} {i : Nat} (hi : i < m)
    (P : PassInv V sp D m O0 l X fB ckF t₀ t i) :
    WP isa (.seq nextOffset (.block (body ++ nextBlock))) t fun t' =>
      PassInv V sp D m O0 l X fB ckF t₀ t' (i + 1) := by
  have hDt : DBuf (V .r29) (V .r31) t D (16 * m) := hD.of_eq P.rd P.wr
  have hBi := hDt.slice (a := 16 * i) (k := 16) (by omega)
  have E := P.env
  have hw := E.perm.w
  refine WP.seq (WP.seq (WP.mono (lNtz_ok E.r31 hw (by omega) (by omega) P.r26 P.l0) fun t₁ P₁ => ?_))
  have h31₁ : t₁.gpr .r31 = V .r31 := by rw [P₁.gpr _ (by decide), E.r31]
  have hw₁ : Covers [⟨V .r31, 2560⟩] t₁.wr := by rw [P₁.wr]; exact hw
  refine WP.mono (xorB_ok (s := t₁) (pd := ofsO) (qd := lO) (cd := ofsO) (by decide) (by decide) (by decide)
    h31₁ h31₁ h31₁ (by decide) (by decide) (by decide) (in_left (in_off hw₁ (by decide) (by decide)))
    (in_left (in_off hw₁ (by decide) (by decide))) (in_left (in_off hw₁ (by decide) (by decide)))
    (in_left (in_off hw₁ (by decide) (by decide))) (in_off hw₁ (by decide) (by decide))
    (in_off hw₁ (by decide) (by decide)) (Offset.sep _ (by decide) (by decide) (by decide))
    (Offset.sep _ (by decide) (by decide) (by decide))) fun t₂ B₂ => ?_
  have g₂ : ∀ r, r ∉ ntzRegs → t₂.gpr r = t.gpr r := fun r hr => by
    rw [B₂.gpr r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with h | h <;> simp [h])),
      P₁.gpr r hr]
  have rd₂ : t₂.rd = t.rd := by rw [B₂.rd, P₁.rd]
  have wr₂ : t₂.wr = t.wr := by rw [B₂.wr, P₁.wr]
  have sp₂ : t₂.sp = t.sp := by rw [B₂.sp, P₁.sp]
  have lr₂ : t₂.lr = t.lr := by rw [B₂.lr, P₁.lr]
  have h31₂ : t₂.gpr .r31 = V .r31 := by rw [g₂ _ (by decide), E.r31]
  have h24₂ : t₂.gpr .r24 = D + BitVec.ofNat 64 (16 * i) := by rw [g₂ _ (by decide), P.r24]
  have fW₂ : Frame [⟨V .r31 + BitVec.ofNat 64 lO, 16⟩, ⟨V .r31 + BitVec.ofNat 64 ofsO, 16⟩] t.mem t₂.mem :=
    (P₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp))
  have kW₂ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨V .r31, 2560⟩ →
      blockAtMem t₂.mem Q = blockAtMem t.mem Q :=
    fun hQ => blockAtMem_frame fW₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact hQ.sub_right (Lay.wSub (by decide))
  have ofs₂ : blockAtMem t₂.mem (V .r31 + BitVec.ofNat 64 ofsO) = offAt O0 l (i + 1) := by
    rw [B₂.val, blockAtMem_frame P₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), P.ofs,
      P₁.val]
    rfl
  have ck₂ : blockAtMem t₂.mem (V .r31 + BitVec.ofNat 64 ckO) = ckF i := by
    rw [blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)), P.ck]
  have Bi₂ : blockAtMem t₂.mem (D + BitVec.ofNat 64 (16 * i)) = X i := by
    rw [kW₂ hBi.w, P.blk i hi]; simp
  refine WP.block_append (WP.mono (hB t₂ _ h24₂ h31₂
    (by rw [rd₂, wr₂]; exact hBi.rd _ _ ⟨_, List.mem_singleton_self _, contains_pre _ (by decide)⟩)
    (by rw [rd₂, wr₂]; exact hBi.rd _ _ ⟨_, List.mem_singleton_self _,
      Offset.contains_base _ (d := 8) (n := 8) (k := 16) (by decide) (by decide)⟩)
    (by rw [wr₂]; exact hBi.wr _ _ ⟨_, List.mem_singleton_self _, contains_pre _ (by decide)⟩)
    (by rw [wr₂]; exact hBi.wr _ _ ⟨_, List.mem_singleton_self _,
      Offset.contains_base _ (d := 8) (n := 8) (k := 16) (by decide) (by decide)⟩)
    (by rw [wr₂]; exact hw) hBi.w) fun t₃ ⟨blk₃, ck₃, fr₃, g₃, sp₃, lr₃, rd₃, wr₃⟩ => ?_)
  have g₃' : ∀ r, r ∉ ntzRegs → t₃.gpr r = t.gpr r := fun r hr => by
    rw [g₃ r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with h | h <;> simp [h])), g₂ r hr]
  have r25₃ : t₃.gpr .r25 = BitVec.ofNat 64 (m - i) := by rw [g₃' _ (by decide), P.r25]
  have r26₃ : t₃.gpr .r26 = BitVec.ofNat 64 (i + 1) := by rw [g₃' _ (by decide), P.r26]
  have r24₃ : t₃.gpr .r24 = D + BitVec.ofNat 64 (16 * i) := by rw [g₃' _ (by decide), P.r24]
  have kB₃ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * i), 16⟩ →
      (⟨Q, 16⟩ : Region).Disjoint ⟨V .r31, 2560⟩ → blockAtMem t₃.mem Q = blockAtMem t.mem Q := fun h₁ h₂ => by
    rw [blockAtMem_frame fr₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁
      · exact h₂.sub_right (Lay.wSub (by decide))), kW₂ h₂]
  refine cwp_addi (by decide) (by decide) fun t₄ u₄ => cwp_addi (by decide) (by decide) fun t₅ u₅ =>
    cwp_subi (by decide) (by decide) fun t₆ u₆ => WP.block_nil ?_
  have hmem : t₆.mem = t₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  have hwr := hD.wrap
  refine
    { env := E.keep (fun r hr => by
          obtain ⟨h0, h24, h25, h26⟩ := (show ∀ r ∈ Proof.AesGcm.PPC64LE.frozen,
            r ∉ ntzRegs ∧ r ≠ .r24 ∧ r ≠ .r25 ∧ r ≠ .r26 by decide) r hr
          rw [u₆.other _ h25, u₅.other _ h26, u₄.other _ h24, g₃' r h0])
        (by rw [u₆.sp, u₅.sp, u₄.sp, sp₃, sp₂]) (by rw [u₆.rd, u₅.rd, u₄.rd, rd₃, rd₂])
        (by rw [u₆.wr, u₅.wr, u₄.wr, wr₃, wr₂])
      frame := by
        rw [hmem]
        exact P.frame.trans ((fW₂.mono (by simp)).trans (fr₃.sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact ⟨⟨D, 16 * m⟩, by simp, Offset.sub_base D (by omega)⟩
          · exact ⟨⟨V .r31 + BitVec.ofNat 64 ckO, 16⟩, by simp, fun _ h => h⟩))
      rd := by rw [u₆.rd, u₅.rd, u₄.rd, rd₃, rd₂, P.rd]
      wr := by rw [u₆.wr, u₅.wr, u₄.wr, wr₃, wr₂, P.wr]
      r24 := by
        rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, r24₃, Offset.add_add,
          show 16 * i + 16 = 16 * (i + 1) by omega]
      r26 := by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), r26₃, ← BitVec.ofNat_add]
      r25 := by
        rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), r25₃, Offset.ofNat_sub_ofNat (by omega),
          Nat.sub_sub]
      ofs := by
        rw [hmem, blockAtMem_frame fr₃ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact (hBi.w.sub_right (Lay.wSub (W := V .r31) (d := 16) (n := 16) (by decide))).symm
          · exact L.w_w (.inl (by decide)) (by decide) (by decide)), ofs₂]
      ck := by rw [hmem, ck₃, ck₂, Bi₂, ofs₂, hckF i hi]
      blk := fun k hk => ?_
      l0 := by
        rw [hmem, blockAtMem_frame fr₃ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact (hBi.w.sub_right (Lay.wSub (W := V .r31) (d := 80) (n := 16) (by decide))).symm
          · exact L.w_w (.inr (by decide)) (by decide) (by decide)), blockAtMem_frame fW₂ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact L.w_w (.inl (by decide)) (by decide) (by decide)
          · exact L.w_w (.inr (by decide)) (by decide) (by decide)), P.l0]
      gpr := fun r hr => by
        simp only [passRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [u₆.other _ hr.2.2.2.2.2.2.2.1, u₅.other _ hr.2.2.2.2.2.2.2.2, u₄.other _ hr.2.2.2.2.2.2.1,
          g₃' r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1]),
          P.gpr r (by simp [passRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
            hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2])] }
  rw [hmem]
  by_cases hki : k = i
  · subst hki
    rw [blk₃, Bi₂, ofs₂]; simp
  · have hBk := hDt.slice (a := 16 * k) (k := 16) (by omega)
    rw [kB₃ (Offset.disjoint D (by omega) (by omega) (by omega)) hBk.w, P.blk k hk]
    by_cases hk' : k < i
    · simp [hk', show k < i + 1 by omega]
    · simp [hk', show ¬ k < i + 1 by omega]

theorem pass_ok {V : Reg → BitVec 64} {sp D : Addr} (L : Lay (V .r29) (V .r31)) {m : Nat} {O0 l : Block}
    {X : Nat → Block} {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block}
    {body : List Instr} (hB : BodyOk (V .r31) body fB fC)
    (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hD : DBuf (V .r29) (V .r31) t₀ D (16 * m)) {j : Nat} (hj : j < m) (hm : m < 2 ^ 60) {t : State}
    (P : PassInv V sp D m O0 l X fB ckF t₀ t j) :
    WP isa (pass body) t (fun t' => PassInv V sp D m O0 l X fB ckF t₀ t' m) := by
  refine WP.loop (M := isa)
    (fun (k : Nat) (u : State) => ∃ i, k = m - i ∧ i < m ∧ PassInv V sp D m O0 l X fB ckF t₀ u i) ?_
    (m - j) _ ⟨j, rfl, hj, P⟩
  rintro k u ⟨i, rfl, hi, P⟩
  refine WP.mono (pass_step L hB hckF hD hm hi P) fun u' P' => ?_
  have ev := eval_nonzero P'.r25 (by omega)
  by_cases he : m - (i + 1) = 0
  · left
    exact ⟨ev.trans (by simp [he]), (show i + 1 = m by omega) ▸ P'⟩
  · right
    exact ⟨ev.trans (by simp [he]), m - (i + 1), by omega, i + 1, rfl, by omega, P'⟩

end VG.Proof.AesOcb.PPC64LE
