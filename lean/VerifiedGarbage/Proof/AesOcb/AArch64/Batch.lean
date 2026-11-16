module

public import VerifiedGarbage.Proof.AesOcb.AArch64.Env
public import VerifiedGarbage.Proof.AesOcb.AArch64.LNtz
public import VerifiedGarbage.Proof.AesOcb.AArch64.Words
public import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `AesOcb.AArch64.Pass`, which only this module used -/

section

/-!
# AES-OCB on AArch64: a scalar pass over whole blocks (`passScalar`)

Untrusted: everything here is checked by Lean. `passScalar body` goes over the
`m` whole blocks of the data at `D`: for block `i` it computes
`Offset_{i+1}` (`lNtz_ok`, `xor16_ok`), then runs `body` on the block, which
replaces it with `fB` of it and the offset, and the checksum with `fC` of
them (`BodyOk`: `xorOfs`, `addCk ++ xorOfs`, `xorOfs ++ addCk`); `passScalar_ok`
gives the blocks and the checksum after all `m`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.AArch64 (in_left in_off eval_nonzero toNat_ofNat_of_lt)

/-- The registers a body writes. -/
abbrev bodyRegs : List Reg := [.x9, .x10, .x11, .x12]

/-- What a body does to the block at `B` (in `x23`) and the checksum, with
the offset at `W + ofsO`. -/
def BodyOk (W : Addr) (body : List Instr) (fB : Block → Block → Block) (fC : Block → Block → Block → Block) : Prop :=
  ∀ (t : State) (B : Addr), t.gpr .x23 = B → t.gpr .x19 = W →
    InRegions (t.rd ++ t.wr) B 8 → InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 8) 8 →
    InRegions t.wr B 8 → InRegions t.wr (B + BitVec.ofNat 64 8) 8 →
    InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 16) 8 → InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 24) 8 →
    InRegions t.wr (W + BitVec.ofNat 64 32) 8 → InRegions t.wr (W + BitVec.ofNat 64 40) 8 →
    (⟨B, 16⟩ : Region).Disjoint ⟨W, 2560⟩ →
    ∃ t', runBlock isa body t = some t' ∧
      blockAtMem t'.mem B = fB (blockAtMem t.mem B) (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO)) ∧
      blockAtMem t'.mem (W + BitVec.ofNat 64 ckO) = fC (blockAtMem t.mem (W + BitVec.ofNat 64 ckO))
        (blockAtMem t.mem B) (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO)) ∧
      Frame [⟨B, 16⟩, ⟨W + BitVec.ofNat 64 ckO, 16⟩] t.mem t'.mem ∧
      (∀ r, r ∉ bodyRegs → t'.gpr r = t.gpr r) ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr

theorem xorOfs_ok {W : Addr} : BodyOk W xorOfs (fun b o => b ^^^ o) (fun c _ _ => c) := by
  intro t B h23 h19 rB₀ rB₈ wB₀ wB₈ rO₀ rO₈ _ _ hBW
  refine ⟨_, by orun [xorOfs, h23, h19, rB₀, rB₈, wB₀, wB₈, rO₀, rO₈], ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩ <;>
    try simp only [mem_write, sp_write, rd_write, wr_write]
  · rw [blockAtMem_store2, show W + 24#64 = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 8 from (addr8 W 16).symm,
      blockAtMem_xor_words]; rfl
  · rw [blockAtMem_frame (Proof.Cmac.frame_store2 _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hBW.sub_right (Lay.wSub (W := W) (d := 32) (n := 16) (by decide))).symm]
  · exact (Proof.Cmac.frame_store2 _ _ _).mono (by simp)
  · simp only [bodyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]
  all_goals rfl

/-- `addCk`: the checksum XORed with the block at `B`. -/
theorem addCk_ok {W B : Addr} {t : State} (h23 : t.gpr .x23 = B) (h19 : t.gpr .x19 = W)
    (rB₀ : InRegions (t.rd ++ t.wr) B 8) (rB₈ : InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 8) 8)
    (wC₀ : InRegions t.wr (W + BitVec.ofNat 64 32) 8) (wC₈ : InRegions t.wr (W + BitVec.ofNat 64 40) 8) :
    ∃ t', runBlock isa addCk t = some t' ∧
      BlkStep W ckO (blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ blockAtMem t.mem B) bodyRegs t t' := by
  obtain ⟨t', run, Bk⟩ := xor16_ok (s := t) (b := .x23) (a := 0) (d := ckO) (by decide) (by decide) h19 h23
    (by decide) (by decide) (by decide) (by rw [BitVec.add_zero]; exact rB₀) rB₈ wC₀ wC₈
  rw [BitVec.add_zero] at Bk
  exact ⟨t', run, Bk⟩

theorem blockAtMem_ck {W B : Addr} (hBW : (⟨B, 16⟩ : Region).Disjoint ⟨W, 2560⟩) {m m' : Mem}
    (h : Frame [⟨W + BitVec.ofNat 64 ckO, 16⟩] m m') : blockAtMem m' B = blockAtMem m B :=
  blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hBW.sub_right (Lay.wSub (by decide))

theorem blockAtMem_ofs_ck {W : Addr} {m m' : Mem}
    (h : Frame [⟨W + BitVec.ofNat 64 ckO, 16⟩] m m') :
    blockAtMem m' (W + BitVec.ofNat 64 ofsO) = blockAtMem m (W + BitVec.ofNat 64 ofsO) :=
  blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint W (d := 16) (n := 16) (e := 32) (k := 16) (.inl (by decide)) (by omega_arith) (by omega_arith)

/-- `seal`'s first pass: the checksum of the block, then the block XORed with the offset. -/
theorem sealPre_ok {W : Addr} :
    BodyOk W (addCk ++ xorOfs) (fun b o => b ^^^ o) (fun c b _ => c ^^^ b) := by
  intro t B h23 h19 rB₀ rB₈ wB₀ wB₈ rO₀ rO₈ wC₀ wC₈ hBW
  obtain ⟨t₁, run₁, B₁⟩ := addCk_ok h23 h19 rB₀ rB₈ wC₀ wC₈
  obtain ⟨t₂, run₂, b₂, c₂, f₂, g₂, sp₂, rd₂, wr₂⟩ := xorOfs_ok t₁ B (by rw [B₁.gpr _ (by decide), h23])
    (by rw [B₁.gpr _ (by decide), h19]) (by rw [B₁.rd, B₁.wr]; exact rB₀) (by rw [B₁.rd, B₁.wr]; exact rB₈)
    (by rw [B₁.wr]; exact wB₀) (by rw [B₁.wr]; exact wB₈) (by rw [B₁.rd, B₁.wr]; exact rO₀)
    (by rw [B₁.rd, B₁.wr]; exact rO₈) (by rw [B₁.wr]; exact wC₀) (by rw [B₁.wr]; exact wC₈) hBW
  refine ⟨t₂, by rw [runBlock_append, run₁, Option.bind_some, run₂], ?_, ?_, ?_, fun r hr => ?_,
    by rw [sp₂, B₁.sp], by rw [rd₂, B₁.rd], by rw [wr₂, B₁.wr]⟩
  · rw [b₂, blockAtMem_ck hBW B₁.frame, blockAtMem_ofs_ck B₁.frame]
  · rw [c₂, B₁.val]
  · exact (B₁.frame.mono (by simp)).trans f₂
  · rw [g₂ r hr, B₁.gpr r hr]

/-- `open`'s third pass: the block XORed with the offset, then its checksum. -/
theorem openPost_ok {W : Addr} :
    BodyOk W (xorOfs ++ addCk) (fun b o => b ^^^ o) (fun c b o => c ^^^ (b ^^^ o)) := by
  intro t B h23 h19 rB₀ rB₈ wB₀ wB₈ rO₀ rO₈ wC₀ wC₈ hBW
  obtain ⟨t₁, run₁, b₁, c₁, f₁, g₁, sp₁, rd₁, wr₁⟩ := xorOfs_ok t B h23 h19 rB₀ rB₈ wB₀ wB₈ rO₀ rO₈ wC₀ wC₈ hBW
  obtain ⟨t₂, run₂, B₂⟩ := addCk_ok (t := t₁) (by rw [g₁ _ (by decide), h23])
    (by rw [g₁ _ (by decide), h19]) (by rw [rd₁, wr₁]; exact rB₀) (by rw [rd₁, wr₁]; exact rB₈)
    (by rw [wr₁]; exact wC₀) (by rw [wr₁]; exact wC₈)
  refine ⟨t₂, by rw [runBlock_append, run₁, Option.bind_some, run₂], ?_, ?_, ?_, fun r hr => ?_,
    by rw [B₂.sp, sp₁], by rw [B₂.rd, rd₁], by rw [B₂.wr, wr₁]⟩
  · rw [blockAtMem_ck hBW B₂.frame, b₁]
  · rw [B₂.val, c₁, b₁]
  · exact f₁.trans (B₂.frame.mono (by simp))
  · rw [B₂.gpr r hr, g₁ r hr]

/-- The registers a pass writes. -/
abbrev passRegs : List Reg := [.x9, .x10, .x11, .x12, .x13, .x14, .x23, .x24, .x25]

/-- A pass over the `m` whole blocks at `D` (`X k` at its start, `t₀`), after
`i` of them. -/
structure PassInv (K W D : Addr) (R n : Nat) (SP : Addr) (m : Nat) (O0 l : Block) (X : Nat → Block)
    (fB : Block → Block → Block) (ckF : Nat → Block) (t₀ t : State) (i : Nat) : Prop where
  env : Env K W D R n SP t
  frame : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩, ⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 ckO, 16⟩,
    ⟨D, 16 * m⟩] t₀.mem t.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  x23 : t.gpr .x23 = D + BitVec.ofNat 64 (16 * i)
  x25 : t.gpr .x25 = BitVec.ofNat 64 (i + 1)
  x24 : t.gpr .x24 = BitVec.ofNat 64 (m - i)
  ofs : blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) = offAt O0 l i
  ck : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) = ckF i
  blk : ∀ k < m, blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k)) =
    if k < i then fB (X k) (offAt O0 l (k + 1)) else X k
  l0 : blockAtMem t.mem (W + BitVec.ofNat 64 l0O) = lAt l 0
  gpr : ∀ r, r ∉ passRegs → t.gpr r = t₀.gpr r

theorem pass_step_with {K W D : Addr} {R n : Nat} {SP : Addr} (L : Lay K W) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : BodyOk W body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hD : DBuf K W t₀ D (16 * m)) (_hm : m < 2 ^ 60) {t : State} {i : Nat} (hi : i < m)
    (P : PassInv K W D R n SP m O0 l X fB ckF t₀ t i) {offset : Prog isa}
    (ho : WP isa offset t (LNtzPost W l (i + 1) t)) :
    WP isa (.seq (.seq offset (.block (xor16 .x19 lO ofsO))) (.block (body ++ nextBlock))) t fun t' =>
      PassInv K W D R n SP m O0 l X fB ckF t₀ t' (i + 1) := by
  obtain hDt : DBuf K W t D (16 * m) := hD.of_eq P.rd P.wr
  obtain hBi := hDt.slice (a := 16 * i) (k := 16) (by omega_arith)
  have E := P.env
  refine WP.seq (WP.seq (WP.mono ho fun t₁ P₁ => ?_))
  obtain h19₁ : t₁.gpr .x19 = W := by rw [P₁.gpr _ (by decide), E.x19]
  obtain ⟨t₂, run₂, B₂⟩ := xor16_ok (s := t₁) (b := .x19) (a := lO) (d := ofsO) (by decide) (by decide) h19₁ h19₁
    (by decide) (by decide) (by decide) (by rw [P₁.rd, P₁.wr]; exact E.perm.wR (by decide))
    (by rw [P₁.rd, P₁.wr]; exact E.perm.wR (by decide))
    (by rw [P₁.wr]; exact E.perm.wW (by decide)) (by rw [P₁.wr]; exact E.perm.wW (by decide))
  refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
  obtain g₂ : ∀ r, r ∉ ntzRegs → t₂.gpr r = t.gpr r := fun r hr => by
    rw [B₂.gpr r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with h | h | h | h <;> simp [h])),
      P₁.gpr r hr]
  obtain rd₂ : t₂.rd = t.rd := by rw [B₂.rd, P₁.rd]
  obtain wr₂ : t₂.wr = t.wr := by rw [B₂.wr, P₁.wr]
  obtain sp₂ : t₂.sp = t.sp := by rw [B₂.sp, P₁.sp]
  obtain h19₂ : t₂.gpr .x19 = W := by rw [g₂ _ (by decide), E.x19]
  obtain h23₂ : t₂.gpr .x23 = D + BitVec.ofNat 64 (16 * i) := by rw [g₂ _ (by decide), P.x23]
  obtain fW₂ : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩, ⟨W + BitVec.ofNat 64 ofsO, 16⟩] t.mem t₂.mem :=
    (P₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp))
  obtain kW₂ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨W, 2560⟩ → blockAtMem t₂.mem Q = blockAtMem t.mem Q :=
    fun hQ => blockAtMem_frame fW₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact hQ.sub_right (Lay.wSub (by decide))
  obtain ofs₂ : blockAtMem t₂.mem (W + BitVec.ofNat 64 ofsO) = offAt O0 l (i + 1) := by
    rw [B₂.val, blockAtMem_frame P₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), P.ofs,
      P₁.val]
    rfl
  obtain ck₂ : blockAtMem t₂.mem (W + BitVec.ofNat 64 ckO) = ckF i := by
    rw [blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)), P.ck]
  obtain Bi₂ : blockAtMem t₂.mem (D + BitVec.ofNat 64 (16 * i)) = X i := by
    rw [kW₂ hBi.w, P.blk i hi]; simp
  obtain ⟨t₃, run₃, blk₃, ck₃, fr₃, g₃, sp₃, rd₃, wr₃⟩ := hB t₂ _ h23₂ h19₂
    (by rw [rd₂, wr₂]; exact hBi.rd _ _ ⟨_, List.mem_singleton_self _,
      by simpa using Offset.contains_base (D + BitVec.ofNat 64 (16 * i)) (d := 0) (n := 8) (k := 16) (by decide) (by decide)⟩)
    (by rw [rd₂, wr₂]; exact hBi.rd _ _ ⟨_, List.mem_singleton_self _,
      Offset.contains_base _ (d := 8) (n := 8) (k := 16) (by decide) (by decide)⟩)
    (by rw [wr₂]; exact hBi.wr _ _ ⟨_, List.mem_singleton_self _,
      by simpa using Offset.contains_base (D + BitVec.ofNat 64 (16 * i)) (d := 0) (n := 8) (k := 16) (by decide) (by decide)⟩)
    (by rw [wr₂]; exact hBi.wr _ _ ⟨_, List.mem_singleton_self _,
      Offset.contains_base _ (d := 8) (n := 8) (k := 16) (by decide) (by decide)⟩)
    (by rw [rd₂, wr₂]; exact E.perm.wR (by decide)) (by rw [rd₂, wr₂]; exact E.perm.wR (by decide))
    (by rw [wr₂]; exact E.perm.wW (by decide)) (by rw [wr₂]; exact E.perm.wW (by decide)) hBi.w
  obtain g₃' : ∀ r, r ∉ ntzRegs → t₃.gpr r = t.gpr r := fun r hr => by
    rw [g₃ r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with h | h | h | h <;> simp [h])),
      g₂ r hr]
  obtain x24₃ : t₃.gpr .x24 = BitVec.ofNat 64 (m - i) := by rw [g₃' _ (by decide), P.x24]
  obtain x25₃ : t₃.gpr .x25 = BitVec.ofNat 64 (i + 1) := by rw [g₃' _ (by decide), P.x25]
  obtain x23₃ : t₃.gpr .x23 = D + BitVec.ofNat 64 (16 * i) := by rw [g₃' _ (by decide), P.x23]
  obtain kB₃ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * i), 16⟩ →
      (⟨Q, 16⟩ : Region).Disjoint ⟨W, 2560⟩ → blockAtMem t₃.mem Q = blockAtMem t.mem Q := fun h₁ h₂ => by
    rw [blockAtMem_frame fr₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁
      · exact h₂.sub_right (Lay.wSub (by decide))), kW₂ h₂]
  refine Proof.AesGcm.AArch64.WP.run (Q := fun t' => t' = ((t₃.write .x .x23 (t₃.gpr .x23 + 16#64)).write .x .x25
    (t₃.gpr .x25 + 1#64)).write .x .x24 (t₃.gpr .x24 - 1#64))
    ⟨_, by rw [runBlock_append, run₃, Option.bind_some]; orun [nextBlock], rfl⟩ fun t' ht' => ?_
  subst ht'
  have hw := hD.wrap
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, ?_, fun r hr => ?_⟩ <;>
    try simp only [mem_write, rd_write, wr_write]
  · exact E.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [gpr_write, reduceCtorEq, ite_false] <;>
        exact g₃' _ (by decide))
      (by simp only [sp_write]; rw [sp₃, sp₂]) (by simp only [rd_write]; rw [rd₃, rd₂])
      (by simp only [wr_write]; rw [wr₃, wr₂])
  · exact P.frame.trans ((fW₂.mono (by simp)).trans (fr₃.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨D, 16 * m⟩, by simp, Offset.sub_base D (by omega_arith)⟩
      · exact ⟨⟨W + BitVec.ofNat 64 ckO, 16⟩, by simp, fun _ h => h⟩))
  · rw [rd₃, rd₂, P.rd]
  · rw [wr₃, wr₂, P.wr]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, x23₃, Offset.add_add]
    rw [show 16 * i + 16 = 16 * (i + 1) by omega_arith]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, x25₃, ← BitVec.ofNat_add]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, x24₃]
    rw [Offset.ofNat_sub_ofNat (by omega_arith), Nat.sub_sub]
  · rw [blockAtMem_frame fr₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hBi.w.sub_right (Lay.wSub (W := W) (d := 16) (n := 16) (by decide))).symm
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)), ofs₂]
  · rw [ck₃, ck₂, Bi₂, ofs₂, hckF i hi]
  · by_cases hki : k = i
    · subst hki
      rw [blk₃, Bi₂, ofs₂]; simp
    · have hBk := hDt.slice (a := 16 * k) (k := 16) (by omega_arith)
      rw [kB₃ (Offset.disjoint D (by omega_arith) (by omega_arith) (by omega_arith)) hBk.w, P.blk k hk]
      by_cases hk' : k < i
      · simp [hk', show k < i + 1 by omega_arith]
      · simp [hk', show ¬ k < i + 1 by omega_arith]
  · rw [blockAtMem_frame fr₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hBi.w.sub_right (Lay.wSub (W := W) (d := 80) (n := 16) (by decide))).symm
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)), blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)), P.l0]
  · simp only [passRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]
    rw [g₃' r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1]),
      P.gpr r (by simp [passRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2])]

theorem passScalar_ok {K W D : Addr} {R n : Nat} {SP : Addr} (L : Lay K W) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : BodyOk W body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hD : DBuf K W t₀ D (16 * m)) {j : Nat} (hj : j < m) (hm : m < 2 ^ 60) {t : State}
    (P : PassInv K W D R n SP m O0 l X fB ckF t₀ t j) :
    WP isa (passScalar body) t (fun t' => PassInv K W D R n SP m O0 l X fB ckF t₀ t' m) := by
  refine WP.loop (M := isa)
    (fun (k : Nat) (u : State) => ∃ i, k = m - i ∧ i < m ∧ PassInv K W D R n SP m O0 l X fB ckF t₀ u i) ?_
    (m - j) _ ⟨j, rfl, hj, P⟩
  rintro k u ⟨i, rfl, hi, P⟩
  refine WP.mono (pass_step_with L hB hckF hD hm hi P
    (lNtz_ok P.env.x19 P.env.perm.w (by omega_arith) (by omega_arith) P.x25 P.l0)) fun u' P' => ?_
  obtain ev := eval_nonzero P'.x24 (by omega_arith)
  by_cases he : m - (i + 1) = 0
  · left
    exact ⟨ev.trans (by simp [he]), (show i + 1 = m by omega_arith) ▸ P'⟩
  · right
    exact ⟨ev.trans (by simp [he]), m - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, P'⟩

end VG.Proof.AesOcb.AArch64

end

end


/-! Cached increments for batches of eight payload blocks. -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (blockAtMem_frame offAt)

/-- Interpret a loaded vector as OCB's big-endian block. -/
def vBlock (x : BitVec 128) : Block :=
  Spec.Ocb.ofBytes ((List.range 16).map fun j => x.extractLsb' (8 * j) 8)

theorem vBlock_read (m : Mem) (p : Addr) : vBlock (m.read p 16) = blockAtMem m p := by
  unfold vBlock blockAtMem
  congr 1
  apply List.map_congr_left
  intro j hj
  exact Mem.extractLsb'_read _ _ (List.mem_range.mp hj)

/-- The three increments needed for the first seven blocks of each batch. -/
def LCache (l : Block) (s : State) : Prop :=
  vBlock (s.v .v0) = lAt l 0 ∧ vBlock (s.v .v1) = lAt l 1 ∧ vBlock (s.v .v2) = lAt l 2

def keepsCache (i : Instr) : Bool :=
  decide (vdstOf i ≠ some .v0 ∧ vdstOf i ≠ some .v1 ∧ vdstOf i ≠ some .v2)

theorem keepCache {p : Prog isa} {s : State} {Q : State → Prop} {l : Block}
    (h : WP isa p s Q) (hc : p.allInstrs keepsCache = true) (C : LCache l s) :
    WP isa p s fun t => Q t ∧ LCache l t := by
  obtain ⟨tr, t, ex, hq⟩ := h
  obtain hs := List.all_eq_true.mp ((Code.allInstrs_eq keepsCache p) ▸ hc)
  obtain h0 := Exec.vec (r := .v0) (fun i hi => (of_decide_eq_true (hs i hi)).1) ex
  obtain h1 := Exec.vec (r := .v1) (fun i hi => (of_decide_eq_true (hs i hi)).2.1) ex
  obtain h2 := Exec.vec (r := .v2) (fun i hi => (of_decide_eq_true (hs i hi)).2.2) ex
  exact ⟨tr, t, ex, hq, by simpa only [LCache, h0, h1, h2] using C⟩

theorem vBlock_words (x : BitVec 128) :
    Spec.Ocb.ofBytes (Proof.Cmac.le8 (x.extractLsb' 0 64) ++ Proof.Cmac.le8 (x.extractLsb' 64 64)) = vBlock x := by
  unfold vBlock
  congr 1
  apply List.ext_getElem
  · simp [Proof.Cmac.le8]
  · intro j h₁ h₂
    obtain hj : j < 16 := by simpa using h₂
    by_cases h : j < 8
    · rw [List.getElem_append_left (by simpa [Proof.Cmac.le8] using h)]
      simp only [Proof.Cmac.le8, List.getElem_map, List.getElem_range]
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      simp only [BitVec.getLsbD_extractLsb', show k < 8 by omega_using [hk], decide_true, Bool.true_and,
        show 8*j+k < 64 by omega_using [h, hk], Nat.zero_add]
    · rw [List.getElem_append_right (by simpa [Proof.Cmac.le8] using Nat.le_of_not_gt h)]
      simp only [Proof.Cmac.le8, List.length_map, List.length_range, List.getElem_map, List.getElem_range]
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      simp only [BitVec.getLsbD_extractLsb', show k < 8 by omega_using [hk], decide_true, Bool.true_and,
        show 8*(j-8)+k < 64 by omega_using [hj, hk], show 64+(8*(j-8)+k) = 8*j+k by omega_using [h]]

theorem cachedIncrement_ok {K W D : Addr} {R n : Nat} {SP : Addr} {s : State}
    (E : Env K W D R n SP s) {v : VReg} {l : Block} {i : Nat}
    (hv : vBlock (s.v v) = lAt l (ntz i)) :
    WP isa (.block (cachedIncrement v)) s (LNtzPost W l i s) := by
  obtain w₀ : InRegions s.wr (W + 96#64) 8 := E.perm.wW (d := lO) (n := 8) (by decide)
  obtain w₁ : InRegions s.wr (W + 104#64) 8 := E.perm.wW (d := lO+8) (n := 8) (by decide)
  refine WP.of_runBlock ⟨_, by orun [cachedIncrement, E.x19, w₀, w₁, v_write], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · change Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem
      ((s.mem.writeW (W + BitVec.ofNat 64 lO) ((s.v v).extractLsb' 0 64)).writeW
        (W + BitVec.ofNat 64 (lO+8)) ((s.v v).extractLsb' 64 64))
    rw [← addr8 W lO]; exact Proof.Cmac.frame_store2 _ _ _
  · change blockAtMem ((s.mem.writeW (W + BitVec.ofNat 64 lO) ((s.v v).extractLsb' 0 64)).writeW
      (W + BitVec.ofNat 64 (lO+8)) ((s.v v).extractLsb' 64 64)) _ = _
    rw [← addr8 W lO, blockAtMem_store2, vBlock_words, hv]
  · have h₉ : r ≠ .x9 := fun h => hr (by simp [ntzRegs, h])
    obtain h₁₀ : r ≠ .x10 := fun h => hr (by simp [ntzRegs, h])
    simp [gpr_write, h₉, h₁₀]

/-- Changes confined to the temporary increment preserve a pass invariant. -/
theorem PassInv.of_temp {K W D : Addr} {R n : Nat} {SP : Addr} {m i : Nat} {O0 l : Block}
    {X : Nat → Block} {fB : Block → Block → Block} {ckF : Nat → Block} {s t u : State}
    (P : PassInv K W D R n SP m O0 l X fB ckF s t i) (hD : DBuf K W s D (16*m))
    (fr : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] t.mem u.mem)
    (g : ∀ r, r ∉ ntzRegs → u.gpr r = t.gpr r) (sp : u.sp = t.sp) (rd : u.rd = t.rd) (wr : u.wr = t.wr) :
    PassInv K W D R n SP m O0 l X fB ckF s u i := by
  have wb {a : Nat} (ha : a + 16 ≤ 96) :
      blockAtMem u.mem (W + BitVec.ofNat 64 a) = blockAtMem t.mem (W + BitVec.ofNat 64 a) :=
    blockAtMem_frame fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl ha) (by omega_using [ha]) (by decide)
  refine { P with
    env := P.env.keep (fun r hr => g r (by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)) sp rd wr
    frame := P.frame.trans (fr.mono (by simp))
    rd := rd.trans P.rd, wr := wr.trans P.wr
    x23 := (g _ (by decide)).trans P.x23
    x24 := (g _ (by decide)).trans P.x24
    x25 := (g _ (by decide)).trans P.x25
    ofs := (wb (by decide)).trans P.ofs
    ck := (wb (by decide)).trans P.ck
    l0 := (wb (by decide)).trans P.l0
    blk := ?_
    gpr := fun r hr => (g r (fun h => hr (by
      simp only [ntzRegs, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [passRegs]))).trans (P.gpr r hr) }
  intro k hk
  rw [blockAtMem_frame fr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hD.slice (a := 16*k) (k := 16) (by omega_using [hk])).w.sub_right (Lay.wSub (by decide))), P.blk k hk]

theorem block_keepsVec {is : List Instr} {s t : State} {v : VReg}
    (h : runBlock isa is s = some t) (hv : ∀ i ∈ is, vdstOf i ≠ some v) : t.v v = s.v v := by
  obtain ⟨tr, u, ex, rfl⟩ := (WP.of_runBlock ⟨t, h, rfl⟩ : WP isa (.block is) s (fun u => u = t))
  exact Exec.vec (c := .block is) (r := v) hv ex

theorem loadV_run {W : Addr} {s : State} (v : VReg) {a : Nat}
    (ha : a % 16 = 0 ∧ a < 65536) (h19 : s.gpr .x19 = W)
    (rq : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 a) 16) :
    runBlock isa [.ldrq v .x19 a] s = some (s.setV v (s.mem.read (W + BitVec.ofNat 64 a) 16)) := by
  orun [ha.1, ha.2, h19, rq]

/-- Double a scratch block and retain its result in a caller-saved vector. -/
theorem cacheDouble_ok {W : Addr} {s : State} (v : VReg) {a : Nat}
    (ha : a % 8 = 0 ∧ a + 8 < 32768) (h19 : s.gpr .x19 = W)
    (hw : Covers [⟨W, 2560⟩] s.wr) (haW : a + 16 ≤ 2560) :
    ∃ t, runBlock isa (dbl .x19 a lO ++ ([.ldrq v .x19 lO] : List Instr)) s = some t ∧
      BlkStep W lO (Spec.Ocb.double (blockAtMem s.mem (W + BitVec.ofNat 64 a))) ntzRegs s t ∧
      vBlock (t.v v) = Spec.Ocb.double (blockAtMem s.mem (W + BitVec.ofNat 64 a)) ∧
      (∀ r, r ≠ v → t.v r = s.v r) := by
  obtain wW : ∀ {d n : Nat}, d + n ≤ 2560 → InRegions s.wr (W + BitVec.ofNat 64 d) n := fun h =>
    Proof.AesGcm.AArch64.in_off hw h (by decide)
  obtain ⟨u, run, B⟩ := dbl_ok (b := .x19) (a := a) (d := lO) ha (by decide) h19 h19 (by decide)
    (Proof.AesGcm.AArch64.in_left (wW (by omega_using [haW])))
    (Proof.AesGcm.AArch64.in_left (wW (by omega_using [haW]))) (wW (by decide)) (wW (by decide))
  obtain load := loadV_run (s := u) v (a := lO) (by decide) (by rw [B.gpr _ (by decide), h19])
    (by rw [B.rd, B.wr]; exact Proof.AesGcm.AArch64.in_left (wW (by decide)))
  refine ⟨_, by rw [runBlock_append, run, Option.bind_some, load], ?_, ?_, fun r hr => ?_⟩
  · exact ⟨B.frame, B.val, fun r hr => B.gpr r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [ntzRegs])), B.sp, B.rd, B.wr⟩
  · rw [v_setV_self, vBlock_read, B.val]
  · rw [v_setV_of_ne _ _ hr]
    exact block_keepsVec run (by simp [dbl, vdstOf, ld, st, Impl.AesGcm.AArch64.imm])

/-- Cache initialization touches only the already permitted increment slot. -/
theorem passCacheInit_ok {K W D : Addr} {R n : Nat} {SP : Addr} {m i : Nat} {O0 l : Block}
    {X : Nat → Block} {fB : Block → Block → Block} {ckF : Nat → Block} {s t : State}
    (P : PassInv K W D R n SP m O0 l X fB ckF s t i) (hD : DBuf K W s D (16*m)) :
    WP isa passCacheInit t fun u => PassInv K W D R n SP m O0 l X fB ckF s u i ∧ LCache l u := by
  let t₁ := t.setV .v0 (t.mem.read (W + BitVec.ofNat 64 l0O) 16)
  obtain run₁ := loadV_run (s := t) .v0 (a := l0O) (by decide) P.env.x19 (P.env.perm.wR (by decide))
  obtain P₁ : PassInv K W D R n SP m O0 l X fB ckF s t₁ i :=
    P.of_temp hD (Frame.refl _ _) (fun _ _ => rfl) rfl rfl rfl
  obtain v₀ : vBlock (t₁.v .v0) = lAt l 0 := by rw [v_setV_self, vBlock_read, P.l0]
  obtain ⟨t₂, run₂, B₂, v₁, keep₂⟩ := cacheDouble_ok .v1 (a := l0O) (by decide) P₁.env.x19 P₁.env.perm.w (by decide)
  obtain P₂ := P₁.of_temp hD B₂.frame B₂.gpr B₂.sp B₂.rd B₂.wr
  obtain ⟨t₃, run₃, B₃, v₂, keep₃⟩ := cacheDouble_ok .v2 (a := lO) (by decide) P₂.env.x19 P₂.env.perm.w (by decide)
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.of_runBlock ⟨t₂, run₂, ?_⟩)
  refine WP.of_runBlock ⟨t₃, run₃, P₂.of_temp hD B₃.frame B₃.gpr B₃.sp B₃.rd B₃.wr, ?_⟩
  refine ⟨by rw [keep₃ _ (by decide), keep₂ _ (by decide), v₀], ?_, ?_⟩
  · rw [keep₃ _ (by decide), v₁, P₁.l0]; rfl
  · rw [v₂, B₂.val, P₁.l0]; rfl

theorem batchLastIncrement_ok {K W D : Addr} {R n : Nat} {SP : Addr} {s : State}
    (E : Env K W D R n SP s) {l : Block} (C : LCache l s) {k : Nat}
    (hi : 8*k+8 < 2^64) (h25 : s.gpr .x25 = BitVec.ofNat 64 (8*k+8)) :
    WP isa batchLastIncrement s (LNtzPost W l (8*k+8) s) := by
  unfold batchLastIncrement
  refine WP.seq (WP.mono (cachedIncrement_ok (i := 4) E
    (by simpa only [show ntz 4 = 2 by decide] using C.2.2)) fun u P => ?_)
  let t := u.write .x .x14 (u.gpr .x25 >>> 2)
  obtain run : runBlock isa [.lsr .x .x14 .x25 2] u = some t := by orun []
  obtain h14 : t.gpr .x14 = BitVec.ofNat 64 ((8*k+8)/2^2) := by
    simp only [t,gpr_write,ite_true,BitVec.setWidth_eq,P.gpr .x25 (by decide),h25,
      Proof.AesGcm.AArch64.lsr_ofNat _ _ hi]
  obtain hntz : ntz (8*k+8) = 2 + ntz ((8*k+8)/2^2) := by
    rw [Proof.Ocb.ntz_even (by omega_using []) (by omega_using []),
      show (8*k+8)/2 = 4*k+4 by omega_using [],Proof.Ocb.ntz_even (by omega_using []) (by omega_using [])]
    simp only [show (4*k+4)/2 = 2*k+2 by omega_using [], show (8*k+8)/2^2 = 2*k+2 by omega_using []]
    omega_using []
  refine WP.seq (WP.of_runBlock ⟨t,run,?_⟩)
  refine WP.mono (lNtzLoop_ok (s := t)
    (by simp only [t,gpr_write,reduceCtorEq,ite_false]; rw [P.gpr _ (by decide),E.x19])
    (by change Covers _ u.wr; rw [P.wr]; exact E.perm.w) hi (by omega_using []) (by omega_using []) hntz h14
    (by change blockAtMem u.mem _ = _; simpa only [show ntz 4 = 2 by decide] using P.val)) fun z Q => ?_
  refine ⟨P.frame.trans Q.frame,Q.val,fun r hr => ?_,Q.sp.trans P.sp,Q.rd.trans P.rd,Q.wr.trans P.wr⟩
  rw [Q.gpr r hr]
  obtain h : r ≠ .x14 := fun h => hr (by simp [ntzRegs,h])
  simp only [t,gpr_write,h,ite_false]
  exact P.gpr r hr

open VG.Proof.AesGcm.AArch64 (lsr_ofNat eval_zero eval_nonzero)

theorem passCount_ok {K W D : Addr} {R n : Nat} {SP : Addr} {m i : Nat} {O0 l : Block}
    {X : Nat → Block} {fB : Block → Block → Block} {ckF : Nat → Block} {s t : State}
    (P : PassInv K W D R n SP m O0 l X fB ckF s t i) (hD : DBuf K W s D (16*m))
    (hm : m < 2^60) :
    WP isa (.block [.lsr .x .x9 .x24 3]) t fun u =>
      PassInv K W D R n SP m O0 l X fB ckF s u i ∧
      u.gpr .x9 = BitVec.ofNat 64 ((m-i)/8) ∧ u.v = t.v := by
  refine WP.of_runBlock ⟨t.write .x .x9 (t.gpr .x24 >>> 3), by orun [], ?_⟩
  refine ⟨P.of_temp hD (Frame.refl _ _) (fun r hr => ?_) rfl rfl rfl, ?_, rfl⟩
  · have h : r ≠ .x9 := fun h => hr (by simp [ntzRegs, h])
    simp [gpr_write, h]
  · simp [gpr_write, P.x24, lsr_ofNat _ _ (show m-i < 2^64 by omega_using [hm])]

theorem ntz_eight_two (k : Nat) : ntz (8*k+2) = 1 := by
  rw [Proof.Ocb.ntz_even (by omega_using []) (by omega_using []), show (8*k+2)/2 = 4*k+1 by omega_using [],
    Proof.Ocb.ntz_odd (by omega_using [])]
theorem ntz_eight_four (k : Nat) : ntz (8*k+4) = 2 := by
  rw [Proof.Ocb.ntz_even (by omega_using []) (by omega_using []), show (8*k+4)/2 = 4*k+2 by omega_using [],
    Proof.Ocb.ntz_even (by omega_using []) (by omega_using []), show (4*k+2)/2 = 2*k+1 by omega_using [],
    Proof.Ocb.ntz_odd (by omega_using [])]
theorem ntz_eight_six (k : Nat) : ntz (8*k+6) = 1 := by
  rw [Proof.Ocb.ntz_even (by omega_using []) (by omega_using []), show (8*k+6)/2 = 4*k+3 by omega_using [],
    Proof.Ocb.ntz_odd (by omega_using [])]

end VG.Proof.AesOcb.AArch64
