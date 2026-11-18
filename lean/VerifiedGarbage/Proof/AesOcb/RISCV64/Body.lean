module

import VerifiedGarbage.Proof.AesOcb.RISCV64.RestTag
public import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Callee
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Env
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Args
import VerifiedGarbage.Proof.AesOcb.RISCV64.Offset0
import VerifiedGarbage.Proof.AesOcb.RISCV64.NonceBlock
public import VerifiedGarbage.Impl.AesOcb.RISCV64
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Spec.Ocb
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Words
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.AesOcb.RISCV64.LNtz
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.AesGcm.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics

/-! ### `AesOcb.RISCV64.Whole`, which this module and modules that import it used -/

section

/-! ### `AesOcb.RISCV64.Pass`, which this module and modules that import it used -/

section

/-!
# AES-OCB on RISCV64: a pass over the whole blocks (`pass`)

Untrusted: everything here is checked by Lean. A pass over the `m` whole
blocks of the data computes each block's offset (`lNtz_ok`, `xorB_ok`),
replaces the block with `fB` of it and the offset, and the checksum with
`fC` of them (`BodyOk`: `xorOfs`, `addCk` then `xorOfs`, `xorOfs` then
`addCk`); `pass_ok` gives the blocks and the checksum after all `m`. As on
PPC64LE (`Proof/AesOcb/PPC64LE/Body.lean`), but the data's blocks, which
need not be aligned, are XORed with the offset (`xorLoop`) and copied to
`W + t2O` to be added to the checksum (`copyLoop`) a byte at a time.
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesOcb.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz ofBytes)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.RISCV64 (in_left in_off covers_off covers_left LoopPre LoopOut copyLoop_ok xorLoop_ok
  xorBytes length_xorBytes bytesAt_writeBytes_self' writeBytes_frame')

/-- The registers a body writes. -/
abbrev bodyRegs : List Reg := [.t0, .t1, .t2, .a0, .a1, .a2, .a3]

/-- What a body leaves: the block at `B` and the checksum, written only
there and at `W + t2O`. -/
structure BodyPost (W B : Addr) (vB vC : Block) (t t' : State) : Prop where
  blk : blockAtMem t'.mem B = vB
  ck : blockAtMem t'.mem (W + BitVec.ofNat 64 ckO) = vC
  frame : Frame [⟨B, 16⟩, ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩] t.mem t'.mem
  gpr : ∀ r, r ∉ bodyRegs → t'.gpr r = t.gpr r
  sp : t'.sp = t.sp
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

/-- What a body does to the block at `B` (in `s4`) and the checksum, with
the offset at `W + ofsO`. -/
def BodyOk (W : Addr) (body : Prog isa) (fB : Block → Block → Block) (fC : Block → Block → Block → Block) :
    Prop :=
  ∀ (t : State) (B : Addr), t.gpr .s4 = B → t.gpr .s0 = W →
    Covers [⟨B, 16⟩] (t.rd ++ t.wr) → Covers [⟨B, 16⟩] t.wr →
    Covers [⟨W, 2560⟩] t.wr → (⟨B, 16⟩ : Region).Disjoint ⟨W, 2560⟩ →
    WP isa body t (BodyPost W B (fB (blockAtMem t.mem B) (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO)))
      (fC (blockAtMem t.mem (W + BitVec.ofNat 64 ckO)) (blockAtMem t.mem B)
        (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO))) t)

/-- The block at `B` after writing 16 bytes there. -/
theorem blockAtMem_write (m : Mem) (B : Addr) {xs : List Byte} (hx : xs.length = 16) :
    blockAtMem (writeBytes m B xs) B = ofBytes xs := by
  rw [blockAtMem, bytesAt_writeBytes_self' m B hx (by decide)]

/-- `xorOfs`: the block at `B` XORed with the offset. -/
theorem xorOfs_ok {W : Addr} : BodyOk W xorOfs (fun b o => b ^^^ o) (fun c _ _ => c) := by
  intro t B h4 h0 hBr hBw hw hBW
  unfold xorOfs
  refine WP.seq (wp_addi (imm := ofsO) (by decide) fun t₁ u₁ => wp_mv fun t₂ u₂ =>
    wp_li (imm := 16) (by decide) fun t₃ u₃ => WP.block_nil ?_)
  obtain m₃ : t₃.mem = t.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain rd₃ : t₃.rd = t.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  obtain wr₃ : t₃.wr = t.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  obtain lp : LoopPre t₃ (W + BitVec.ofNat 64 ofsO) B 16 :=
    ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h0],
      by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h4], u₃.gpr, by decide, by decide,
      by rw [rd₃, wr₃]; exact covers_left (covers_off hw (by decide) (by decide)),
      by rw [wr₃]; exact hBw, (hBW.sub_right (Lay.wSub (by decide))).symm⟩
  refine WP.mono (xorLoop_ok t₃ lp) fun t' ⟨hm, lo⟩ => ?_
  rw [m₃] at hm
  obtain hl := length_xorBytes t.mem B (W + BitVec.ofNat 64 ofsO) 16
  obtain fw : Frame [⟨B, 16⟩] t.mem t'.mem := by rw [hm]; exact writeBytes_frame' _ hl
  refine ⟨?_, ?_, fw.mono (by simp), fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [hm, blockAtMem_write _ _ hl, xorBytes]
    exact Proof.Ocb.ofBytes_xor (Proof.Ocb.length_bytesAt _ _ _) (Proof.Ocb.length_bytesAt _ _ _)
  · exact blockAtMem_frame fw fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hBW.sub_right (Lay.wSub (by decide))).symm
  · simp only [bodyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨n0, -, -, n3, n4, n5, n6⟩ := hr
    rw [lo.other r n0 n3 n4 n5 n6, u₃.other r n5, u₂.other r n4, u₁.other r n3]
  · rw [lo.keeps.2.2, u₃.sp, u₂.sp, u₁.sp]
  · rw [lo.keeps.1, rd₃]
  · rw [lo.keeps.2.1, wr₃]

/-- `addCk`: the checksum XORed with the block at `B`. -/
theorem addCk_ok {W : Addr} (hW : W.toNat % 8 = 0) :
    BodyOk W addCk (fun b _ => b) (fun c b _ => c ^^^ b) := by
  intro t B h4 h0 hBr hBw hw hBW
  unfold addCk
  refine WP.seq (wp_mv fun t₁ u₁ => wp_addi (imm := t2O) (by decide) fun t₂ u₂ =>
    wp_li (imm := 16) (by decide) fun t₃ u₃ => WP.block_nil ?_)
  obtain m₃ : t₃.mem = t.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain rd₃ : t₃.rd = t.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  obtain wr₃ : t₃.wr = t.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  obtain lp : LoopPre t₃ B (W + BitVec.ofNat 64 t2O) 16 :=
    ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h4],
      by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h0], u₃.gpr, by decide, by decide,
      by rw [rd₃, wr₃]; exact hBr, by rw [wr₃]; exact covers_off hw (by decide) (by decide),
      hBW.sub_right (Lay.wSub (by decide))⟩
  refine WP.seq (WP.mono (copyLoop_ok t₃ lp) fun t₄ ⟨hm, lo⟩ => ?_)
  rw [m₃] at hm
  obtain hl := Proof.Ocb.length_bytesAt t.mem B 16
  obtain fw : Frame [⟨W + BitVec.ofNat 64 t2O, 16⟩] t.mem t₄.mem := by rw [hm]; exact writeBytes_frame' _ hl
  obtain g₄ : ∀ r, r ∉ bodyRegs → t₄.gpr r = t.gpr r := fun r hr => by
    simp only [bodyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨n0, -, -, n3, n4, n5, n6⟩ := hr
    rw [lo.other r n0 n3 n4 n5 n6, u₃.other r n5, u₂.other r n4, u₁.other r n3]
  obtain rd₄ : t₄.rd = t.rd := by rw [lo.keeps.1, rd₃]
  obtain wr₄ : t₄.wr = t.wr := by rw [lo.keeps.2.1, wr₃]
  obtain hw₄ : Covers [⟨W, 2560⟩] t₄.wr := by rw [wr₄]; exact hw
  obtain h0₄ : t₄.gpr .s0 = W := by rw [g₄ _ (by decide), h0]
  refine WP.mono (xorB_ok (s := t₄) (pd := ckO) (qd := t2O) (cd := ckO) hW hW hW (by decide) (by decide)
    (by decide) h0₄ h0₄ h0₄ (by decide) (by decide) (by decide) (in_left (in_off hw₄ (by decide) (by decide)))
    (in_left (in_off hw₄ (by decide) (by decide))) (in_left (in_off hw₄ (by decide) (by decide)))
    (in_left (in_off hw₄ (by decide) (by decide))) (in_off hw₄ (by decide) (by decide))
    (in_off hw₄ (by decide) (by decide)) (Offset.sep _ (.inr (by decide)) (by decide) (by decide))
    (Offset.sep _ (.inr (by decide)) (by decide) (by decide))) fun t' B' => ?_
  obtain dB : ∀ d, d + 16 ≤ 2560 → (⟨B, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, 16⟩ :=
    fun _ hd => hBW.sub_right (Lay.wSub hd)
  obtain kB : blockAtMem t'.mem B = blockAtMem t.mem B := by
    rw [blockAtMem_frame B'.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dB _ (by decide)),
      blockAtMem_frame fw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dB _ (by decide))]
  refine ⟨kB, ?_, (fw.mono (by simp)).trans (B'.frame.mono (by simp)), fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [B'.val, hm, blockAtMem_write _ _ hl, blockAtMem_frame (writeBytes_frame' t.mem hl) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))]
    rfl
  · rw [B'.gpr r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with h | h <;> simp [h])), g₄ r hr]
  · rw [B'.sp, lo.keeps.2.2, u₃.sp, u₂.sp, u₁.sp]
  · rw [B'.rd, rd₄]
  · rw [B'.wr, wr₄]

/-- The offset, after a body. -/
theorem BodyPost.ofs {W B : Addr} {vB vC : Block} {t t' : State} (h : BodyPost W B vB vC t t')
    (hBW : (⟨B, 16⟩ : Region).Disjoint ⟨W, 2560⟩) :
    blockAtMem t'.mem (W + BitVec.ofNat 64 ofsO) = blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) :=
  blockAtMem_frame h.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hBW.sub_right (Lay.wSub (by decide))).symm
    · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
    · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)

/-- Two bodies, one after the other. -/
theorem BodyOk.seq {W : Addr} {p q : Prog isa} {fB₁ fB₂ : Block → Block → Block}
    {fC₁ fC₂ : Block → Block → Block → Block} (h₁ : BodyOk W p fB₁ fC₁) (h₂ : BodyOk W q fB₂ fC₂) :
    BodyOk W (.seq p q) (fun b o => fB₂ (fB₁ b o) o) (fun c b o => fC₂ (fC₁ c b o) (fB₁ b o) o) := by
  intro t B h4 h0 hBr hBw hw hBW
  refine WP.seq (WP.mono (h₁ t B h4 h0 hBr hBw hw hBW) fun t₁ P₁ => ?_)
  refine WP.mono (h₂ t₁ B (by rw [P₁.gpr _ (by decide), h4]) (by rw [P₁.gpr _ (by decide), h0])
    (by rw [P₁.rd, P₁.wr]; exact hBr) (by rw [P₁.wr]; exact hBw) (by rw [P₁.wr]; exact hw) hBW) fun t₂ P₂ => ?_
  rw [P₁.blk, P₁.ck, P₁.ofs hBW] at P₂
  exact ⟨P₂.blk, P₂.ck, P₁.frame.trans P₂.frame, fun r hr => by rw [P₂.gpr r hr, P₁.gpr r hr],
    by rw [P₂.sp, P₁.sp], by rw [P₂.rd, P₁.rd], by rw [P₂.wr, P₁.wr]⟩

/-- `seal`'s first pass: the checksum of the block, then the block XORed with the offset. -/
theorem sealPre_ok {W : Addr} (hW : W.toNat % 8 = 0) :
    BodyOk W (.seq addCk xorOfs) (fun b o => b ^^^ o) (fun c b _ => c ^^^ b) :=
  (addCk_ok hW).seq xorOfs_ok

/-- `open`'s third pass: the block XORed with the offset, then its checksum. -/
theorem openPost_ok {W : Addr} (hW : W.toNat % 8 = 0) :
    BodyOk W (.seq xorOfs addCk) (fun b o => b ^^^ o) (fun c b o => c ^^^ (b ^^^ o)) :=
  xorOfs_ok.seq (addCk_ok hW)

/-- The registers the offset and a body write. -/
abbrev stepRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .a0, .a1, .a2, .a3, .a5]

/-- The registers a pass writes. -/
abbrev passRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .a0, .a1, .a2, .a3, .a5, .s4, .s5, .s6]

theorem ntz_step : ∀ r ∈ ntzRegs, r ∈ stepRegs := by decide
theorem body_step : ∀ r ∈ bodyRegs, r ∈ stepRegs := by decide
theorem t12_step : ∀ r ∈ [Reg.t1, Reg.t2], r ∈ stepRegs := by decide
theorem step_pass : ∀ r ∈ stepRegs, r ∈ passRegs := by decide

theorem pass_step_regs {r : Reg} (hr : r ∉ passRegs) : r ∉ stepRegs ∧ r ≠ .s4 ∧ r ≠ .s5 ∧ r ≠ .s6 :=
  ⟨fun h => hr (step_pass r h), by rintro rfl; exact hr (by decide), by rintro rfl; exact hr (by decide),
    by rintro rfl; exact hr (by decide)⟩

theorem frozen_step : ∀ r ∈ Proof.AesGcm.RISCV64.frozen, r ∉ passRegs := by decide

/-- A pass over the `m` whole blocks at `D` (`X k` at its start, `t₀`), after
`i` of them. -/
structure PassInv (V : Reg → BitVec 64) (sp D : Addr) (m : Nat) (O0 l : Block) (X : Nat → Block)
    (fB : Block → Block → Block) (ckF : Nat → Block) (t₀ t : State) (i : Nat) : Prop where
  env : Env V sp t
  frame : Frame [⟨V .s0 + BitVec.ofNat 64 lO, 16⟩, ⟨V .s0 + BitVec.ofNat 64 ofsO, 16⟩,
    ⟨V .s0 + BitVec.ofNat 64 ckO, 16⟩, ⟨V .s0 + BitVec.ofNat 64 t2O, 16⟩, ⟨D, 16 * m⟩] t₀.mem t.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  s4 : t.gpr .s4 = D + BitVec.ofNat 64 (16 * i)
  s6 : t.gpr .s6 = BitVec.ofNat 64 (i + 1)
  s5 : t.gpr .s5 = BitVec.ofNat 64 (m - i)
  ofs : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ofsO) = offAt O0 l i
  ck : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ckO) = ckF i
  blk : ∀ k < m, blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k)) =
    if k < i then fB (X k) (offAt O0 l (k + 1)) else X k
  l0 : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 l0O) = lAt l 0
  gpr : ∀ r, r ∉ passRegs → t.gpr r = t₀.gpr r

theorem pass_step {V : Reg → BitVec 64} {sp D : Addr} (L : Lay (V .s2) (V .s0)) {m : Nat} {O0 l : Block}
    {X : Nat → Block} {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block}
    {body : Prog isa} (hB : BodyOk (V .s0) body fB fC)
    (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hD : DBuf (V .s2) (V .s0) t₀ D (16 * m)) {t : State} {i : Nat} (hi : i < m)
    (P : PassInv V sp D m O0 l X fB ckF t₀ t i) :
    WP isa (.seq nextOffset (.seq body (.block nextBlock))) t fun t' =>
      PassInv V sp D m O0 l X fB ckF t₀ t' (i + 1) := by
  obtain hDt : DBuf (V .s2) (V .s0) t D (16 * m) := hD.of_eq P.rd P.wr
  have hm := hD.lt
  obtain hBi := hDt.slice (a := 16 * i) (k := 16) (by omega_arith)
  have E := P.env
  have hw := E.perm.w
  have hW := L.wal
  refine WP.seq (WP.seq (WP.mono (lNtz_ok E.s0 hW hw (by omega_arith) (by omega_arith) P.s6 P.l0)
    fun t₁ P₁ => ?_))
  obtain h0₁ : t₁.gpr .s0 = V .s0 := by rw [P₁.gpr _ (by decide), E.s0]
  obtain hw₁ : Covers [⟨V .s0, 2560⟩] t₁.wr := by rw [P₁.wr]; exact hw
  refine WP.mono (xorB_ok (s := t₁) (pd := ofsO) (qd := lO) (cd := ofsO) hW hW hW (by decide) (by decide)
    (by decide) h0₁ h0₁ h0₁ (by decide) (by decide) (by decide) (in_left (in_off hw₁ (by decide) (by decide)))
    (in_left (in_off hw₁ (by decide) (by decide))) (in_left (in_off hw₁ (by decide) (by decide)))
    (in_left (in_off hw₁ (by decide) (by decide))) (in_off hw₁ (by decide) (by decide))
    (in_off hw₁ (by decide) (by decide)) (Offset.sep _ (.inr (by decide)) (by decide) (by decide))
    (Offset.sep _ (.inr (by decide)) (by decide) (by decide))) fun t₂ B₂ => ?_
  obtain g₂ : ∀ r, r ∉ stepRegs → t₂.gpr r = t.gpr r := fun r hr => by
    rw [B₂.gpr r (fun h => hr (t12_step r h)), P₁.gpr r (fun h => hr (ntz_step r h))]
  obtain rd₂ : t₂.rd = t.rd := by rw [B₂.rd, P₁.rd]
  obtain wr₂ : t₂.wr = t.wr := by rw [B₂.wr, P₁.wr]
  obtain sp₂ : t₂.sp = t.sp := by rw [B₂.sp, P₁.sp]
  obtain h0₂ : t₂.gpr .s0 = V .s0 := by rw [g₂ _ (by decide), E.s0]
  obtain h4₂ : t₂.gpr .s4 = D + BitVec.ofNat 64 (16 * i) := by rw [g₂ _ (by decide), P.s4]
  obtain fW₂ : Frame [⟨V .s0 + BitVec.ofNat 64 lO, 16⟩, ⟨V .s0 + BitVec.ofNat 64 ofsO, 16⟩] t.mem t₂.mem :=
    (P₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp))
  obtain kW₂ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨V .s0, 2560⟩ →
      blockAtMem t₂.mem Q = blockAtMem t.mem Q :=
    fun hQ => blockAtMem_frame fW₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact hQ.sub_right (Lay.wSub (by decide))
  obtain ofs₂ : blockAtMem t₂.mem (V .s0 + BitVec.ofNat 64 ofsO) = offAt O0 l (i + 1) := by
    rw [B₂.val, blockAtMem_frame P₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), P.ofs,
      P₁.val]
    rfl
  obtain ck₂ : blockAtMem t₂.mem (V .s0 + BitVec.ofNat 64 ckO) = ckF i := by
    rw [blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)), P.ck]
  obtain Bi₂ : blockAtMem t₂.mem (D + BitVec.ofNat 64 (16 * i)) = X i := by
    rw [kW₂ hBi.w, P.blk i hi]; simp
  obtain l0₂ : blockAtMem t₂.mem (V .s0 + BitVec.ofNat 64 l0O) = lAt l 0 := by
    rw [blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)), P.l0]
  refine WP.seq (WP.mono (hB t₂ _ h4₂ h0₂ (by rw [rd₂, wr₂]; exact hBi.rd) (by rw [wr₂]; exact hBi.wr)
    (by rw [wr₂]; exact hw) hBi.w) fun t₃ P₃ => ?_)
  obtain g₃ : ∀ r, r ∉ stepRegs → t₃.gpr r = t.gpr r := fun r hr => by rw [P₃.gpr r (fun h => hr (body_step r h)), g₂ r hr]
  obtain s5₃ : t₃.gpr .s5 = BitVec.ofNat 64 (m - i) := by rw [g₃ _ (by decide), P.s5]
  obtain s6₃ : t₃.gpr .s6 = BitVec.ofNat 64 (i + 1) := by rw [g₃ _ (by decide), P.s6]
  obtain s4₃ : t₃.gpr .s4 = D + BitVec.ofNat 64 (16 * i) := by rw [g₃ _ (by decide), P.s4]
  obtain kB₃ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * i), 16⟩ →
      (⟨Q, 16⟩ : Region).Disjoint ⟨V .s0, 2560⟩ → blockAtMem t₃.mem Q = blockAtMem t.mem Q := fun h₁ h₂ => by
    rw [blockAtMem_frame P₃.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h₁
      · exact h₂.sub_right (Lay.wSub (by decide))
      · exact h₂.sub_right (Lay.wSub (by decide))), kW₂ h₂]
  obtain dWB : ∀ d, d + 16 ≤ 2560 →
      (⟨V .s0 + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * i), 16⟩ :=
    fun _ hd => (hBi.w.sub_right (Lay.wSub hd)).symm
  unfold nextBlock
  refine wp_addi (imm := 16) (by decide) fun t₄ u₄ => wp_addi (imm := 1) (by decide) fun t₅ u₅ =>
    wp_subi (imm := 1) (by decide) fun t₆ u₆ => WP.block_nil ?_
  obtain hmem : t₆.mem = t₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  refine
    { env := E.keep (fun r hr => by
          obtain ⟨h0, h4, h5, h6⟩ := pass_step_regs (frozen_step r hr)
          rw [u₆.other _ h5, u₅.other _ h6, u₄.other _ h4, g₃ r h0])
        (by rw [u₆.sp, u₅.sp, u₄.sp, P₃.sp, sp₂]) (by rw [u₆.rd, u₅.rd, u₄.rd, P₃.rd, rd₂])
        (by rw [u₆.wr, u₅.wr, u₄.wr, P₃.wr, wr₂])
      frame := by
        rw [hmem]
        exact P.frame.trans ((fW₂.mono (by simp)).trans (P₃.frame.sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact ⟨⟨D, 16 * m⟩, by simp, Offset.sub_base D (by omega_arith)⟩
          · exact ⟨_, by simp, fun _ h => h⟩
          · exact ⟨_, by simp, fun _ h => h⟩))
      rd := by rw [u₆.rd, u₅.rd, u₄.rd, P₃.rd, rd₂, P.rd]
      wr := by rw [u₆.wr, u₅.wr, u₄.wr, P₃.wr, wr₂, P.wr]
      s4 := by
        rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, s4₃, Offset.add_add,
          show 16 * i + 16 = 16 * (i + 1) by omega_arith]
      s6 := by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), s6₃, ← BitVec.ofNat_add]
      s5 := by
        rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), s5₃, Offset.ofNat_sub_ofNat (by omega_arith),
          Nat.sub_sub]
      ofs := by
        rw [hmem, blockAtMem_frame P₃.frame (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact dWB _ (by decide)
          · exact L.w_w (.inl (by decide)) (by decide) (by decide)
          · exact L.w_w (.inl (by decide)) (by decide) (by decide)), ofs₂]
      ck := by rw [hmem, P₃.ck, ck₂, Bi₂, ofs₂, hckF i hi]
      blk := fun k hk => ?_
      l0 := by
        rw [hmem, blockAtMem_frame P₃.frame (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact dWB _ (by decide)
          · exact L.w_w (.inr (by decide)) (by decide) (by decide)
          · exact L.w_w (.inl (by decide)) (by decide) (by decide)), l0₂]
      gpr := fun r hr => by
        obtain ⟨h0, h4, h5, h6⟩ := pass_step_regs hr
        rw [u₆.other _ h5, u₅.other _ h6, u₄.other _ h4, g₃ r h0, P.gpr r hr] }
  rw [hmem]
  by_cases hki : k = i
  · subst hki
    rw [P₃.blk, Bi₂, ofs₂]; simp
  · have hBk := hDt.slice (a := 16 * k) (k := 16) (by omega_arith)
    rw [kB₃ (Offset.disjoint D (by omega_arith) (by omega_arith) (by omega_arith)) hBk.w, P.blk k hk]
    by_cases hk' : k < i
    · simp [hk', show k < i + 1 by omega_arith]
    · simp [hk', show ¬ k < i + 1 by omega_arith]

theorem pass_ok {V : Reg → BitVec 64} {sp D : Addr} (L : Lay (V .s2) (V .s0)) {m : Nat} {O0 l : Block}
    {X : Nat → Block} {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block}
    {body : Prog isa} (hB : BodyOk (V .s0) body fB fC)
    (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hD : DBuf (V .s2) (V .s0) t₀ D (16 * m)) {j : Nat} (hj : j < m) {t : State}
    (P : PassInv V sp D m O0 l X fB ckF t₀ t j) :
    WP isa (pass body) t (fun t' => PassInv V sp D m O0 l X fB ckF t₀ t' m) := by
  have hm := hD.lt
  refine WP.loop (M := isa)
    (fun (k : Nat) (u : State) => ∃ i, k = m - i ∧ i < m ∧ PassInv V sp D m O0 l X fB ckF t₀ u i) ?_
    (m - j) _ ⟨j, rfl, hj, P⟩
  rintro k u ⟨i, rfl, hi, P⟩
  refine WP.mono (pass_step L hB hckF hD hi P) fun u' P' => ?_
  obtain ev := eval_nonzero P'.s5 (by omega_arith)
  by_cases he : m - (i + 1) = 0
  · left
    exact ⟨ev.trans (by simp [he]), (show i + 1 = m by omega_arith) ▸ P'⟩
  · right
    exact ⟨ev.trans (by simp [he]), m - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, P'⟩

end VG.Proof.AesOcb.RISCV64

end

end

/-!
# AES-OCB on RISCV64: the whole blocks (`whole`)

Untrusted: everything here is checked by Lean. `whole f pre post` runs a
pass with `pre` over the `m` whole blocks of the data, calls `f` on all of
them (`callBlocks_ok`), copies `Offset_0` back and runs a pass with `post`
(`whole_ok`): each block becomes `G (X ⊕ Offset_i) ⊕ Offset_i`, and the
checksum is the second pass's. As on PPC64LE
(`Proof/AesOcb/PPC64LE/Body.lean`), but the data's address is loaded from
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
  have := h.slice (a := 0) (k := k) (by omega_using [hk])
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
  obtain hmn : 16 * m ≤ len := by omega_using [hmd]
  obtain hDm := hD.take' hmn
  obtain hal := L.alW (d := dataO) (by decide)
  -- the first pass
  unfold whole
  refine WP.seq (WP.mono (passStart_ok E.s0 hal (E.perm.wR (by decide)) hS hl (E.s11.trans h11))
    fun s₁ ⟨s4₁, s5₁, s6₁, g₁, k₁⟩ => ?_)
  rw [hmd] at s5₁
  obtain E₁ := E.others g₁ k₁.sp k₁.rd k₁.wr
  obtain hD₁ : DBuf (V .s2) (V .s0) s₁ D (16 * m) := hDm.of_eq k₁.rd k₁.wr
  obtain P₀ : PassInv V sp D m O0 l (fun k => blockAtMem s₁.mem (D + BitVec.ofNat 64 (16 * k)))
      (fun b o => b ^^^ o) ckF1 s₁ s₁ 0 :=
    { env := E₁, frame := Frame.refl _ _, rd := rfl, wr := rfl, s4 := s4₁, s6 := s6₁, s5 := s5₁
      ofs := by rw [k₁.mem, hofs]; rfl
      ck := by rw [k₁.mem, hck]
      blk := fun k _ => by simp
      l0 := by rw [k₁.mem, hl0]
      gpr := fun _ _ => rfl }
  refine WP.seq (WP.mono (pass_ok L hB1 (fun i _ => by rw [hckF1, k₁.mem]) hD₁ hm0 P₀) fun s₂ P₂ => ?_)
  obtain hD₂ : DBuf (V .s2) (V .s0) s₂ D (16 * m) := hD₁.of_eq P₂.rd P₂.wr
  obtain F₂ : Frame (wholeR (V .s0) D (16 * m)) t.mem s₂.mem := by rw [← k₁.mem]; exact P₂.frame.sub pass_sub
  obtain S₂ : s₂.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D := by rw [slot_kept L hD₁.w F₂, hS]
  refine WP.assoc (WP.seq (WP.mono (callBlocks_ok (f := f) L ok nf hR hs3 P₂.env
    (fun s₃ g₃ k₃ => by
      have := dataArgs_ok (t := s₃) (by rw [g₃ _ (by decide) (by decide) (by decide), P₂.env.s0]) hal
        (by rw [k₃.rd, k₃.wr]; exact P₂.env.perm.wR (by decide)) (by rw [k₃.mem, S₂]) hl
        (by rw [g₃ _ (by decide) (by decide) (by decide), P₂.env.s11, h11])
      rwa [hmd] at this) (dstD hD₂)) fun s₃ P₃ => ?_))
  obtain E₃ := P₃.env P₂.env
  obtain kC : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨D, 16 * m⟩ →
      (⟨Q, 16⟩ : Region).Disjoint ⟨V .s0 + BitVec.ofNat 64 512, 2048⟩ → blockAtMem s₃.mem Q = blockAtMem s₂.mem Q :=
    fun h₁ h₂ => blockAtMem_frame P₃.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁
      · exact h₂
  obtain kWP : ∀ {d : Nat}, (d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 96) ∨ (112 ≤ d ∧ d + 16 ≤ 256) ∨
      (272 ≤ d ∧ d + 16 ≤ 512)) →
      blockAtMem s₃.mem (V .s0 + BitVec.ofNat 64 d) = blockAtMem s₁.mem (V .s0 + BitVec.ofNat 64 d) := fun hd => by
    rw [kC ((hD₂.w.sub_right (Lay.wSub (by omega_using [hd]))).symm) (L.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)),
      blockAtMem_frame P₂.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact L.w_w (a := _) (d := 96) (k := 16) (by omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact L.w_w (a := _) (d := 16) (k := 16) (by omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact L.w_w (a := _) (d := 32) (k := 16) (by omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact L.w_w (a := _) (d := 256) (k := 16) (by omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact (hD₁.w.sub_right (Lay.wSub (by omega_using [hd]))).symm)]
  obtain o0₃ : blockAtMem s₃.mem (V .s0 + BitVec.ofNat 64 o0O) = O0 := by rw [kWP (by decide), k₁.mem, ho0]
  obtain F₃ : Frame (wholeR (V .s0) D (16 * m)) t.mem s₃.mem :=
    F₂.trans (P₃.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨D, 16 * m⟩, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩)
  -- `Offset_0` again
  refine WP.seq (WP.block_append (WP.mono (copy16_ok (s := s₃) (a := o0O) (d := ofsO) L.wal (by decide)
    (by decide) E₃.s0 (E₃.perm.wR (by decide)) (E₃.perm.wR (by decide)) (E₃.perm.wW (by decide))
    (E₃.perm.wW (by decide))) fun s₄a B₄ => ?_))
  obtain F₄a : Frame (wholeR (V .s0) D (16 * m)) t.mem s₄a.mem :=
    F₃.trans (B₄.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub _ (d := 16) (n := 16) (e := 16) (k := 32) (by decide)
        (by decide)⟩)
  refine WP.mono (passStart_ok (t := s₄a) (D := D) (by rw [B₄.gpr _ (by decide), E₃.s0]) hal
    (by rw [B₄.rd, B₄.wr]; exact E₃.perm.wR (by decide)) (by rw [slot_kept L hD₁.w F₄a, hS]) hl
    (by rw [B₄.gpr _ (by decide), E₃.s11, h11])) fun s₄ ⟨s4₄, s5₄, s6₄, g₄, k₄⟩ => ?_
  obtain E₄a := E₃.others B₄.gpr B₄.sp B₄.rd B₄.wr
  rw [hmd] at s5₄
  obtain E₄ := E₄a.others g₄ k₄.sp k₄.rd k₄.wr
  obtain hD₄ : DBuf (V .s2) (V .s0) s₄ D (16 * m) :=
    hD₂.of_eq (by rw [k₄.rd, B₄.rd, P₃.rd]) (by rw [k₄.wr, B₄.wr, P₃.wr])
  obtain kB₄ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨V .s0, 2560⟩ → blockAtMem s₄.mem Q = blockAtMem s₃.mem Q :=
    fun hQ => by
      rw [k₄.mem]; exact blockAtMem_frame B₄.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hQ.sub_right (Lay.wSub (by decide))
  obtain hK : bytesAt s₂.mem (V .s2) (16 * (R + 1)) = bytesAt t.mem (V .s2) (16 * (R + 1)) := by
    obtain hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
    rw [Proof.Cmac.bytesAt_frame P₂.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact hD₁.k.sub_left (Region.sub_prefix hRb)) (by omega_using [hR]), k₁.mem]
  obtain X₄ : ∀ k < m, blockAtMem s₄.mem (D + BitVec.ofNat 64 (16 * k)) =
      G (bytesAt t.mem (V .s2) (16 * (R + 1)))
        (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)) :=
    fun k hk => by
      rw [kB₄ (hD₂.slice (a := 16 * k) (k := 16) (by omega_using [hk])).w, hcall P₃ k hk, hK, P₂.blk k hk]
      simp only [hk, ↓reduceIte, k₁.mem]
  obtain ck₃ : blockAtMem s₃.mem (V .s0 + BitVec.ofNat 64 ckO) = ckF2 0 := by
    rw [kC ((hD₂.w.sub_right (Lay.wSub (by decide))).symm) (L.w_w (.inl (by decide)) (by decide) (by decide)),
      P₂.ck, hckF2₀]
  obtain P₀' : PassInv V sp D m O0 l (fun k => blockAtMem s₄.mem (D + BitVec.ofNat 64 (16 * k)))
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

end

end

/-! ### `AesOcb.RISCV64.Nonce`, which this module and modules that import it used -/

section

/-!
# AES-OCB on RISC-V: `Offset_0` from the nonce (`nonce`)

Untrusted: everything here is checked by Lean. `nonce` writes `Nonce` with
its last 6 bits cleared and `bottom` (`nonceBlock_ok`), enciphers the block
(`Ktop`, `encOne_ok`), and computes `Offset_0` (`offset0_ok`), to
`W + ofsO` and `W + o0O` (`nonce_ok`): §4.2's `Offset_0`
(`Proof.Ocb.offset0_eq`). As on PPC64LE (`Proof/AesOcb/PPC64LE/Nonce.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.Impl.AesOcb.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem ctxCiph ctxInv ctxLstar)
open VG.Proof.Ocb (blockAtMem_frame)

/-- The key schedule, after a frame within the parts the pieces write. -/
theorem ctxCiph_mut {K W D : Addr} {n : Nat} (L : Lay K W) (hD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩)
    {m m' : Mem} (h : Frame (mutR W D n) m m') {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    ctxCiph m' K R = ctxCiph m K R := by
  unfold ctxCiph
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  rw [Proof.Cmac.bytesAt_frame h (fun r hr => (k_mut L hD r hr).sub_left (Region.sub_prefix hRb)) (by omega_using [hR])]

theorem ctxLstar_mut {K W D : Addr} {n : Nat} (L : Lay K W) (hD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩)
    {m m' : Mem} (h : Frame (mutR W D n) m m') : ctxLstar m' K = ctxLstar m K := by
  show blockAtMem m' (K + BitVec.ofNat 64 240) = blockAtMem m (K + BitVec.ofNat 64 240)
  exact blockAtMem_frame h fun r hr => (k_mut L hD r hr).sub_left (Lay.kSub (by decide))

/-- What `nonce` writes: `[16, 128)` and `[256, 2560)` of `W`. -/
abbrev nonceR (W : Addr) : List Region := [⟨W + BitVec.ofNat 64 16, 112⟩, wB W]

theorem nonceR_mut {W D : Addr} {n : Nat} {m m' : Mem} (h : Frame (nonceR W) m m') :
    Frame (mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact in_mutA (by decide)
  · exact ⟨_, by simp, fun _ h => h⟩

/-- A part of `W` within `[16, 128)` or from 256 on, as a part `nonce` writes. -/
theorem in_nonceR {W : Addr} {d k : Nat} (h : (16 ≤ d ∧ d + k ≤ 128) ∨ (256 ≤ d ∧ d + k ≤ 2560)) :
    ∃ r' ∈ nonceR W, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨_, List.mem_cons_self .., Offset.sub W h₁ (by omega_using [h₂])⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_wB h₁ h₂⟩

/-- What `nonce` leaves. -/
structure NonceOk (V : Reg → BitVec 64) (sp : Addr) (o : Block) (s s' : State) : Prop where
  env : Env V sp s'
  frame : Frame (nonceR (V .s0)) s.mem s'.mem
  ofs : blockAtMem s'.mem (V .s0 + BitVec.ofNat 64 ofsO) = o
  o0 : blockAtMem s'.mem (V .s0 + BitVec.ofNat 64 o0O) = o
  keep : ∀ {d : Nat}, 32 ≤ d → d + 16 ≤ 112 →
    blockAtMem s'.mem (V .s0 + BitVec.ofNat 64 d) = blockAtMem s.mem (V .s0 + BitVec.ofNat 64 d)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem nonce_ok {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s0)) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) {s : State} (E : Env V sp s)
    {N : Addr} {nl t : Nat} (hs4 : s.gpr .s4 = N) (hs5 : s.gpr .s5 = BitVec.ofNat 64 nl)
    (hs8 : V .s8 = BitVec.ofNat 64 t) (h1 : 1 ≤ nl) (h15 : nl ≤ 15) (ht : t < 2 ^ 64) (hB : Buf (V .s0) s N nl)
    {D : Addr} {n : Nat} (hKD : (⟨V .s2, 256⟩ : Region).Disjoint ⟨D, n⟩) :
    WP isa nonce s (NonceOk V sp (Spec.Ocb.offset0 (ctxCiph s.mem (V .s2) R) t (bytesAt s.mem N nl)) s) := by
  unfold nonce
  refine WP.seq (WP.mono (nonceBlock_ok L E.s0 E.perm.w hs4 hs5 (E.s8.trans hs8) h1 h15 ht hB) fun s₁ P₁ => ?_)
  have E₁ : Env V sp s₁ := E.others P₁.gpr P₁.sp P₁.rd P₁.wr
  have F₁ : Frame (nonceR (V .s0)) s.mem s₁.mem := P₁.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact in_nonceR (.inl ⟨by decide, by decide⟩)
    · exact in_nonceR (.inr ⟨by decide, by decide⟩)
  refine WP.seq (WP.mono (encOne_ok L hR hs3 E₁ (d := tmpO) (by decide)) fun s₂ P₂ => ?_)
  have E₂ : Env V sp s₂ := P₂.env E₁
  have F₂ : Frame (nonceR (V .s0)) s₁.mem s₂.mem := P₂.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact in_nonceR (.inl ⟨by decide, by decide⟩)
    · exact in_nonceR (.inr ⟨by decide, by decide⟩)
  have ktop : blockAtMem s₂.mem (V .s0 + BitVec.ofNat 64 tmpO) =
      ctxCiph s.mem (V .s2) R (Proof.Ocb.nonceN t (bytesAt s.mem N nl) &&& ~~~(63 : Block)) := by
    rw [P₂.enc0, P₁.blk]
    exact congrFun (ctxCiph_mut L hKD (nonceR_mut F₁) hR) _
  have hbv : ((Proof.Ocb.nonceN t (bytesAt s.mem N nl)).extractLsb' 0 6).toNat < 64 :=
    (BitVec.extractLsb' 0 6 _).isLt
  have bot₂ : s₂.mem.readW (V .s0 + BitVec.ofNat 64 botO) 64 =
      BitVec.ofNat 64 ((Proof.Ocb.nonceN t (bytesAt s.mem N nl)).extractLsb' 0 6).toNat := by
    rw [P₂.frame.readW (r := ⟨V .s0 + BitVec.ofNat 64 botO, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)) (by decide), P₁.bot]
  refine WP.mono (offset0_ok L E₂.s0 E₂.perm.w hbv bot₂) fun s₃ P₃ => ?_
  refine ⟨E₂.others P₃.gpr P₃.sp P₃.rd P₃.wr,
    F₁.trans (F₂.trans (P₃.frame.sub fun r hr => ?_)), ?_, ?_, fun {d} h₁ h₂ => ?_, by rw [P₃.rd, P₂.rd, P₁.rd],
    by rw [P₃.wr, P₂.wr, P₁.wr]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact in_nonceR (.inl ⟨by decide, by decide⟩)
    · exact in_nonceR (.inr ⟨by decide, by decide⟩)
  · rw [P₃.ofs, ktop, Proof.Ocb.offset0_eq]; rfl
  · rw [P₃.o0, ktop, Proof.Ocb.offset0_eq]; rfl
  · rw [blockAtMem_frame P₃.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact L.w_w (by simp only [ofsO, o0O]; omega_arith) (by omega_using [h₂]) (by decide)),
      blockAtMem_frame P₂.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact L.w_w (by simp only [tmpO]; omega_using [h₂]) (by omega_using [h₂]) (by decide)
        · exact L.w_w (by omega_using [h₂]) (by omega_using [h₂]) (by decide)),
      blockAtMem_frame P₁.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact L.w_w (by simp only [tmpO, botO]; omega_using [h₂]) (by omega_using [h₂]) (by decide))]

end VG.Proof.AesOcb.RISCV64

end

end

/-!
# AES-OCB on RISC-V: the data (`body`)

Untrusted: everything here is checked by Lean. `body` runs the whole blocks,
if any (`wholeIte_ok`), and the rest, if any (`restIte_ok`): for `seal`
`OCB-ENCRYPT`'s ciphertext, offset and checksum (`bodySeal_ok`), for `open`
`OCB-DECRYPT`'s (`bodyOpen_ok`). As on PPC64LE
(`Proof/AesOcb/PPC64LE/Body.lean`), but the data's address is in its slot in
`W` (`Slots`), from which the whole blocks and the rest load it.
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesOcb.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt length_bytesAt blockAtMem_frame)
open VG.Proof.AesGcm.RISCV64 (and15 shr4 ofNat_sub64 Keeps)
open VG.Impl.AesGcm.RISCV64 (dataO)

/-- The whole blocks, if there are any. -/
theorem wholeIte_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksRISCV64 f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksRISCV64 f).post s s')
    (nf : c.noFrames = true) {G : List Byte → Cipher}
    (hcall : ∀ {s s' : State} {K D S : Addr} {R n : Nat}, BPost f s K D S R n s' → ∀ i < n,
      blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) = G (bytesAt s.mem K (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))))
    {pre post : Prog isa} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    {V : Reg → BitVec 64} {sp : Addr}
    (hB1 : BodyOk (V .s0) pre (fun b o => b ^^^ o) fC1) (hB2 : BodyOk (V .s0) post (fun b o => b ^^^ o) fC2)
    (L : Lay (V .s2) (V .s0)) {s : State} (E : Env V sp s)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) {n : Nat}
    (h11 : V .s11 = BitVec.ofNat 64 n) {D : Addr} (hS : s.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hD : DBuf (V .s2) (V .s0) s D n) {O0 l : Block}
    (hofs : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)))
      (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 (n / 16))
    (hckF2 : ∀ i, ckF2 (i + 1) = fC2 (ckF2 i)
      (G (bytesAt s.mem (V .s2) (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
      (offAt O0 l (i + 1))) :
    WP isa (.seq (.block [.shift .srl .d .t1 .s11 4]) (.ite (.zero .t1) (.block []) (whole (.call name c) pre post))) s
      (WholePost V sp D (n / 16) O0 l
        (fun k => G (bytesAt s.mem (V .s2) (16 * (R + 1)))
          (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
        (ckF2 (n / 16)) s) := by
  have hn := hD.lt
  refine WP.seq (wp_srl (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have t1₁ : s₁.gpr .t1 = BitVec.ofNat 64 (n / 16) := by rw [u₁.gpr, E.s11, h11, shr4 hn]
  have E₁ : Env V sp s₁ := E.others (rs := [.t1]) (fun r hr => u₁.other r (by simpa using hr)) u₁.sp u₁.rd u₁.wr
  refine WP.ite _ (eval_zero t1₁ (by omega_using [hn])) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hm : n / 16 = 0 := of_decide_eq_true h0
    exact ⟨E₁, by rw [u₁.mem]; exact Frame.refl _ _, u₁.rd, u₁.wr, fun k hk => absurd hk (by omega_using [hm]),
      by rw [u₁.mem, hofs, hm]; rfl, by rw [u₁.mem, hck, hm, hckF2₀, hm]⟩
  · have hm : n / 16 ≠ 0 := of_decide_eq_false h0
    have hD₁ := hD.of_eq u₁.rd u₁.wr
    refine WP.mono (whole_ok (O0 := O0) (l := l) ok nf hcall hB1 hB2 L E₁ hR hs3 h11 (by rw [u₁.mem, hS]) hD₁
      (by omega_using [hm]) (by rw [u₁.mem, hofs]) (by rw [u₁.mem, ho0]) (by rw [u₁.mem, hck]) (by rw [u₁.mem, hl0])
      (fun i => by rw [u₁.mem, hckF1]) hckF2₀ (fun i => by rw [u₁.mem, hckF2])) fun t P => ?_
    refine ⟨P.env, by have f := P.frame; rwa [u₁.mem] at f, by rw [P.rd, u₁.rd], by rw [P.wr, u₁.wr],
      fun k hk => by rw [P.blk k hk, u₁.mem], P.ofs, by rw [P.ck]⟩

theorem andi15 (x : BitVec 64) : x &&& BitVec.ofInt 64 15 = BitVec.ofNat 64 (x.toNat % 16) := and15 x

/-- Where the rest of the data is, and how long it is. -/
theorem bodyTail_ok {V : Reg → BitVec 64} {sp : Addr} {K : Addr} (L : Lay K (V .s0)) {t : State} (E : Env V sp t)
    {n : Nat} (hn : n < 2 ^ 64) (h11 : V .s11 = BitVec.ofNat 64 n) {D : Addr}
    (hS : t.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D) :
    WP isa (.block [.logicImm .and .s5 .s11 15, .sub .s4 .s11 .s5, .load .d .t1 .s0 dataO, .add .s4 .s4 .t1]) t
      fun t₁ => t₁.gpr .s4 = D + BitVec.ofNat 64 (16 * (n / 16)) ∧ t₁.gpr .s5 = BitVec.ofNat 64 (n % 16) ∧
        (∀ r, r ∉ [.t1, .s4, .s5] → t₁.gpr r = t.gpr r) ∧ Keeps t t₁ := by
  have hsub : BitVec.ofNat 64 n - BitVec.ofNat 64 (n % 16) = BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [ofNat_sub64 (Nat.mod_le _ _) hn, show n - n % 16 = 16 * (n / 16) by omega_using []]
  refine wp_andi (by decide) fun t₁ u₁ => wp_sub fun t₂ u₂ => ?_
  have s5₁ : t₁.gpr .s5 = BitVec.ofNat 64 (n % 16) := by
    rw [u₁.gpr, E.s11, h11, andi15, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have s4₂ : t₂.gpr .s4 = BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [u₂.gpr, u₁.other _ (by decide), E.s11, h11, s5₁, hsub]
  refine wp_ld (a := V .s0 + BitVec.ofNat 64 dataO) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), E.s0]) (L.alW (by decide))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact E.perm.wR (by decide)) fun t₃ u₃ => wp_add fun t₄ u₄ =>
    WP.block_nil ⟨?_, ?_, fun r hr => ?_, ⟨by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
      by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr], by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]⟩⟩
  · rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), s4₂, u₂.mem, u₁.mem, hS, BitVec.add_comm]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), s5₁]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₄.other _ hr.2.1, u₃.other _ hr.1, u₂.other _ hr.2.1, u₁.other _ hr.2.2]

/-- What the rest of the data leaves, if there is any: `r` bytes at `P`. -/
structure TailPost (enc : Bool) (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (P : Addr) (r : Nat) (t t' : State) :
    Prop where
  env : Env V sp t'
  frame : Frame [⟨V .s0 + BitVec.ofNat 64 ofsO, 16⟩, ⟨V .s0 + BitVec.ofNat 64 tmpO, 16⟩,
    ⟨V .s0 + BitVec.ofNat 64 t2O, 16⟩, ⟨V .s0 + BitVec.ofNat 64 ckO, 16⟩, ⟨V .s0 + BitVec.ofNat 64 512, 2048⟩,
    ⟨P, r⟩] t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  ofs : blockAtMem t'.mem (V .s0 + BitVec.ofNat 64 ofsO) =
    if 0 < r then blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (V .s2)
    else blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ofsO)
  out : bytesAt t'.mem P r =
    if 0 < r then Spec.Ocb.xor (bytesAt t.mem P r)
      (Spec.Ocb.toBytes (ctxCiph t.mem (V .s2) R
        (blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (V .s2))))
    else bytesAt t.mem P r
  ck : blockAtMem t'.mem (V .s0 + BitVec.ofNat 64 ckO) =
    if 0 < r then
      blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt (if enc then t.mem else t'.mem) P r)
    else blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ckO)

/-- The rest of the data, if there is any. -/
theorem restIte_ok (enc : Bool) {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s0)) {t : State}
    (E : Env V sp t) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) {n : Nat}
    (h11 : V .s11 = BitVec.ofNat 64 n) {D : Addr} (hS : t.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hD : DBuf (V .s2) (V .s0) t D n) :
    WP isa (.seq (.block [.logicImm .and .s5 .s11 15, .sub .s4 .s11 .s5, .load .d .t1 .s0 dataO, .add .s4 .s4 .t1])
        (.ite (.zero .s5) (.block []) (rest enc))) t
      (TailPost enc V sp R (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) t) := by
  have hn := hD.lt
  refine WP.seq (WP.mono (bodyTail_ok L E hn h11 hS) fun t₁ ⟨s4₁, s5₁, g₁, k₁⟩ => ?_)
  have E₁ := E.others g₁ k₁.sp k₁.rd k₁.wr
  refine WP.ite _ (eval_zero s5₁ (by omega_using [])) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hr : ¬ 0 < n % 16 := by have := of_decide_eq_true h0; omega_using [this]
    refine ⟨E₁, by rw [k₁.mem]; exact Frame.refl _ _, k₁.rd, k₁.wr, ?_, ?_, ?_⟩ <;> simp only [hr, ↓reduceIte, k₁.mem]
  · have hr : 0 < n % 16 := by have := of_decide_eq_false h0; omega_using [this]
    have hP : DBuf (V .s2) (V .s0) t₁ (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
      (hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega_using [])).of_eq k₁.rd k₁.wr
    refine WP.mono (rest_ok enc L E₁ hR hs3 hr (Nat.mod_lt _ (by decide)) s4₁ s5₁ hP) fun t' P => ?_
    refine ⟨P.env, by rw [← k₁.mem]; exact P.frame, by rw [P.rd, k₁.rd], by rw [P.wr, k₁.wr], ?_, ?_, ?_⟩ <;>
      simp only [hr, ↓reduceIte]
    · rw [P.ofs, k₁.mem]
    · rw [P.out, k₁.mem]
    · rw [P.ck, k₁.mem]

/-- What `body` writes: the offset and the checksum, `L_{ntz(i)}`, `Pad` and
`pad(·)`, the working space of the functions called and the data. -/
abbrev bodyR (W D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 32⟩, ⟨W + BitVec.ofNat 64 96, 32⟩, ⟨W + BitVec.ofNat 64 256, 16⟩,
    ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨D, n⟩]

theorem bodyR_mut {W D : Addr} {n : Nat} {m m' : Mem} (h : Frame (bodyR W D n) m m') :
    Frame (mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact in_mutA (by decide)
  · exact in_mutA (by decide)
  · exact in_mutB (by decide) (by decide)
  · exact in_mutB (by decide) (by decide)
  · exact in_mutD fun _ h => h

/-- What `body` leaves: the data, the offset and the checksum. -/
structure BodyOut (V : Reg → BitVec 64) (sp D : Addr) (n : Nat) (out : List Byte) (ofs ck : Block) (s t : State) :
    Prop where
  env : Env V sp t
  frame : Frame (bodyR (V .s0) D n) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  out : bytesAt t.mem D n = out
  ofs : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ofsO) = ofs
  ck : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ckO) = ck

/-- A checksum of blocks `X i`. -/
def ckOf (X : Nat → Block) : Nat → Block
  | 0 => 0
  | i + 1 => ckOf X i ^^^ X i

theorem ckOf_eq {X : Nat → Block} {p : List Byte} {m : Nat} (h : ∀ i < m, X i = Spec.Ocb.blockAt p i) :
    ckOf X m = Proof.Ocb.ckAt p m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [ckOf, Proof.Ocb.ckAt, ih (fun i hi => h i (by omega_using [hi])), h m (by omega_using [])]

theorem flatMap_range_congr {α : Type} {f g : Nat → List α} {m : Nat} (h : ∀ i < m, f i = g i) :
    (List.range m).flatMap f = (List.range m).flatMap g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, ih (fun i hi => h i (by omega_using [hi]))]
    simp only [List.flatMap_cons, List.flatMap_nil, h m (by omega_using [])]

/-- `ENCIPHER` from the key schedule, whatever its length. -/
def encG (ks : List Byte) : Cipher := Spec.Ocb.aesWith (ks.length / 16 - 1) ks

/-- `DECIPHER` from the key schedule, whatever its length. -/
def decG (ks : List Byte) : Cipher := Spec.Ocb.aesInvWith (ks.length / 16 - 1) ks

theorem encG_eq (m : Mem) (K : Addr) (R : Nat) : encG (bytesAt m K (16 * (R + 1))) = ctxCiph m K R := by
  rw [encG, length_bytesAt, show 16 * (R + 1) / 16 - 1 = R by omega_using []]; rfl

theorem decG_eq (m : Mem) (K : Addr) (R : Nat) : decG (bytesAt m K (16 * (R + 1))) = Spec.Ocb.ctxInv m K R := by
  rw [decG, length_bytesAt, show 16 * (R + 1) / 16 - 1 = R by omega_using []]; rfl

theorem hcall_enc {s s' : State} {K D S : Addr} {R n : Nat} (h : BPost Spec.Aes.cipher s K D S R n s') :
    ∀ i < n, blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) =
      encG (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) := fun i hi => by
  rw [h.enc hi, encG_eq]; rfl

theorem hcall_dec {s s' : State} {K D S : Addr} {R n : Nat} (h : BPost Spec.Aes.invCipher s K D S R n s') :
    ∀ i < n, blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) =
      decG (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) := fun i hi => by
  rw [h.dec hi, decG_eq]; rfl

/-- A buffer apart from `W` and `⟨P, r⟩` misses what `rest` writes. -/
theorem disj_tail {W Q P : Addr} {k r : Nat} (hw : (⟨Q, k⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hp : (⟨Q, k⟩ : Region).Disjoint ⟨P, r⟩) :
    ∀ x ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
      ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨P, r⟩], (⟨Q, k⟩ : Region).Disjoint x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hp

/-- A buffer apart from `W` and `⟨D, n⟩` misses what `whole` writes. -/
theorem disj_whole {W Q D : Addr} {k n : Nat} (hw : (⟨Q, k⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hp : (⟨Q, k⟩ : Region).Disjoint ⟨D, n⟩) :
    ∀ x ∈ wholeR W D n, (⟨Q, k⟩ : Region).Disjoint x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hp

theorem wholeR_sub {W D : Addr} {k n : Nat} (hk : k ≤ n) :
    ∀ r ∈ wholeR W D k, ∃ r' ∈ bodyR W D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, Region.sub_prefix hk⟩

theorem tailR_sub {W D : Addr} {n a r : Nat} (h : a + r ≤ n) :
    ∀ x ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
      ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨D + BitVec.ofNat 64 a, r⟩],
      ∃ r' ∈ bodyR W D n, Region.Sub x r' := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
  · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, Offset.sub_base D h⟩

/-- `body` for `seal`. -/
theorem bodySeal_ok {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s0)) {s : State} (E : Env V sp s)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) {n : Nat}
    (h11 : V .s11 = BitVec.ofNat 64 n) {D : Addr} (hS : s.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hD : DBuf (V .s2) (V .s0) s D n) {O0 : Block}
    (hofs : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (V .s2)) 0) :
    WP isa (body true) s (BodyOut V sp D n
      (if 0 < n % 16 then
        Proof.Ocb.encBlocks (ctxCiph s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem (V .s2) R (offAt O0 (ctxLstar s.mem (V .s2)) (n / 16) ^^^ ctxLstar s.mem (V .s2))))
      else Proof.Ocb.encBlocks (ctxCiph s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16))
      (if 0 < n % 16 then offAt O0 (ctxLstar s.mem (V .s2)) (n / 16) ^^^ ctxLstar s.mem (V .s2)
       else offAt O0 (ctxLstar s.mem (V .s2)) (n / 16))
      (if 0 < n % 16 then
        Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16) ^^^ pad ((bytesAt s.mem D n).drop (16 * (n / 16)))
      else Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16)) s) := by
  have hn := hD.lt
  have hmn : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hDm : DBuf (V .s2) (V .s0) s D (16 * (n / 16)) := hD.take' hmn
  have hP : DBuf (V .s2) (V .s0) s (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega_using [])
  have dDP : (⟨D, 16 * (n / 16)⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ :=
    Offset.base_disjoint D (Nat.le_refl _) (by omega_using [hn])
  have hl : ∀ i < n / 16, blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) = Spec.Ocb.blockAt (bytesAt s.mem D n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem D (by omega_using [hi])).symm
  simp only [body, ↓reduceIte]
  refine WP.assoc (WP.seq (WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem (V .s2))
    (ckF1 := ckOf fun i => blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)))
    (ckF2 := fun _ => ckOf (fun i => blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) (n / 16))
    Proof.Aes.RISCV64.encryptBlocks_correct encryptBlocks_noFrames hcall_enc (sealPre_ok L.wal) xorOfs_ok L E hR hs3
    h11 hS hD hofs ho0 hck hl0
    (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  have fW : Frame (mutR (V .s0) D (16 * (n / 16))) s.mem t.mem := wholeR_mut Pw.frame
  have hSt : t.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D := by rw [slot_kept L hDm.w Pw.frame, hS]
  refine WP.mono (restIte_ok true L Pw.env hR hs3 h11 hSt (hD.of_eq Pw.rd Pw.wr)) fun t' Pt => ?_
  have cT : ctxCiph t.mem (V .s2) R = ctxCiph s.mem (V .s2) R := ctxCiph_mut L hDm.k fW hR
  have lT : ctxLstar t.mem (V .s2) = ctxLstar s.mem (V .s2) := ctxLstar_mut L hDm.k fW
  have pT : bytesAt t.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    Proof.Cmac.bytesAt_frame Pw.frame (disj_whole hP.w dDP.symm) (by omega_using [])
  have rest : (bytesAt s.mem D n).drop (16 * (n / 16)) = bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem D hmn, show n - 16 * (n / 16) = n % 16 by omega_using []]
  have ckT : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ckO) = Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16) := by
    rw [Pw.ck, ckOf_eq hl]
  have blk : bytesAt t'.mem D (16 * (n / 16)) =
      Proof.Ocb.encBlocks (ctxCiph s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16) := by
    rw [Proof.Cmac.bytesAt_frame Pt.frame (disj_tail hDm.w dDP) (by omega_using [hn]), Proof.Ocb.bytesAt_blocks,
      Proof.Ocb.encBlocks]
    refine flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, encG_eq, hl i hi,
      BitVec.xor_comm]
  refine ⟨Pt.env, (Pw.frame.sub (wholeR_sub hmn)).trans (Pt.frame.sub (tailR_sub (by omega_using []))),
    by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · have e := Proof.Ocb.bytesAt_append t'.mem D (16 * (n / 16)) (n % 16)
    rw [show 16 * (n / 16) + n % 16 = n by omega_using []] at e
    rw [e, blk, Pt.out]
    by_cases hr : 0 < n % 16
    · simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, rest]
    · have b0 : ∀ (m : Mem) (p : Addr), bytesAt m p 0 = [] := fun _ _ => rfl
      simp only [↓reduceIte, show n % 16 = 0 by omega_using [hr], b0, List.append_nil, Nat.lt_irrefl]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    simp only [↓reduceIte, pT, rest]

theorem ckOf_dck {X : Nat → Block} {inv : Cipher} {o0 l : Block} {c : List Byte} {m : Nat}
    (h : ∀ i < m, X i = Proof.Ocb.decBlock inv o0 l c i) : ckOf X m = Proof.Ocb.dckAt inv o0 l c m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [ckOf, Proof.Ocb.dckAt, ih (fun i hi => h i (by omega_using [hi])), h m (by omega_using [])]

/-- `body` for `open`. -/
theorem bodyOpen_ok {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s0)) {s : State} (E : Env V sp s)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) {n : Nat}
    (h11 : V .s11 = BitVec.ofNat 64 n) {D : Addr} (hS : s.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hD : DBuf (V .s2) (V .s0) s D n) {O0 : Block}
    (hofs : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (V .s2)) 0) :
    WP isa (body false) s (BodyOut V sp D n
      (if 0 < n % 16 then
        Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem (V .s2) R (offAt O0 (ctxLstar s.mem (V .s2)) (n / 16) ^^^ ctxLstar s.mem (V .s2))))
      else Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16))
      (if 0 < n % 16 then offAt O0 (ctxLstar s.mem (V .s2)) (n / 16) ^^^ ctxLstar s.mem (V .s2)
       else offAt O0 (ctxLstar s.mem (V .s2)) (n / 16))
      (if 0 < n % 16 then
        Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16) ^^^
          pad (Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem (V .s2) R (offAt O0 (ctxLstar s.mem (V .s2)) (n / 16) ^^^ ctxLstar s.mem (V .s2)))))
      else Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16)) s) := by
  have hn := hD.lt
  have hmn : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hDm : DBuf (V .s2) (V .s0) s D (16 * (n / 16)) := hD.take' hmn
  have hP : DBuf (V .s2) (V .s0) s (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega_using [])
  have dDP : (⟨D, 16 * (n / 16)⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ :=
    Offset.base_disjoint D (Nat.le_refl _) (by omega_using [hn])
  have hl : ∀ i < n / 16, blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) = Spec.Ocb.blockAt (bytesAt s.mem D n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem D (by omega_using [hi])).symm
  simp only [body, Bool.false_eq_true, ↓reduceIte]
  refine WP.assoc (WP.seq (WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem (V .s2)) (ckF1 := fun _ => 0)
    (ckF2 := ckOf fun i => decG (bytesAt s.mem (V .s2) (16 * (R + 1)))
      (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 (ctxLstar s.mem (V .s2)) (i + 1)) ^^^
        offAt O0 (ctxLstar s.mem (V .s2)) (i + 1))
    Proof.Aes.RISCV64.decryptBlocks_correct decryptBlocks_noFrames hcall_dec xorOfs_ok (openPost_ok L.wal) L E hR hs3
    h11 hS hD hofs ho0 hck hl0
    (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  have fW : Frame (mutR (V .s0) D (16 * (n / 16))) s.mem t.mem := wholeR_mut Pw.frame
  have hSt : t.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D := by rw [slot_kept L hDm.w Pw.frame, hS]
  refine WP.mono (restIte_ok false L Pw.env hR hs3 h11 hSt (hD.of_eq Pw.rd Pw.wr)) fun t' Pt => ?_
  have cT : ctxCiph t.mem (V .s2) R = ctxCiph s.mem (V .s2) R := ctxCiph_mut L hDm.k fW hR
  have lT : ctxLstar t.mem (V .s2) = ctxLstar s.mem (V .s2) := ctxLstar_mut L hDm.k fW
  have pT : bytesAt t.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    Proof.Cmac.bytesAt_frame Pw.frame (disj_whole hP.w dDP.symm) (by omega_using [])
  have rest : (bytesAt s.mem D n).drop (16 * (n / 16)) = bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem D hmn, show n - 16 * (n / 16) = n % 16 by omega_using []]
  have ckT : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ckO) =
      Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16) := by
    rw [Pw.ck, ckOf_dck fun i hi => by rw [decG_eq, hl i hi, Proof.Ocb.decBlock, BitVec.xor_comm]]
  have blk : bytesAt t'.mem D (16 * (n / 16)) =
      Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16) := by
    rw [Proof.Cmac.bytesAt_frame Pt.frame (disj_tail hDm.w dDP) (by omega_using [hn]), Proof.Ocb.bytesAt_blocks,
      Proof.Ocb.decBlocks]
    refine flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, decG_eq, hl i hi,
      Proof.Ocb.decBlock, BitVec.xor_comm]
  have e := Proof.Ocb.bytesAt_append t'.mem D (16 * (n / 16)) (n % 16)
  rw [show 16 * (n / 16) + n % 16 = n by omega_using []] at e
  refine ⟨Pt.env, (Pw.frame.sub (wholeR_sub hmn)).trans (Pt.frame.sub (tailR_sub (by omega_using []))),
    by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · rw [e, blk, Pt.out]
    by_cases hr : 0 < n % 16
    · simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, rest]
    · have b0 : ∀ (m : Mem) (p : Addr), bytesAt m p 0 = [] := fun _ _ => rfl
      simp only [↓reduceIte, show n % 16 = 0 by omega_using [hr], b0, List.append_nil, Nat.lt_irrefl]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    by_cases hr : 0 < n % 16
    · simp only [hr, Bool.false_eq_true, ↓reduceIte, Pt.out, pT, cT, lT, Pw.ofs, rest]
    · simp only [hr, ↓reduceIte]

end VG.Proof.AesOcb.RISCV64
