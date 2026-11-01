module

public import VerifiedGarbage.Proof.AesOcb.RISCV64.Env
public import VerifiedGarbage.Proof.AesOcb.RISCV64.LNtz
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Ocb.Spec
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Words
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.AesGcm.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.AesOcb.RISCV64
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Ocb

/-!
# AES-OCB on RISCV64: a pass over the whole blocks (`pass`)

Untrusted: everything here is checked by Lean. A pass over the `m` whole
blocks of the data computes each block's offset (`lNtz_ok`, `xorB_ok`),
replaces the block with `fB` of it and the offset, and the checksum with
`fC` of them (`BodyOk`: `xorOfs`, `addCk` then `xorOfs`, `xorOfs` then
`addCk`); `pass_ok` gives the blocks and the checksum after all `m`. As on
PPC64LE (`Proof/AesOcb/PPC64LE/Pass.lean`), but the data's blocks, which
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
  have m₃ : t₃.mem = t.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : t₃.rd = t.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : t₃.wr = t.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have lp : LoopPre t₃ (W + BitVec.ofNat 64 ofsO) B 16 :=
    ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h0],
      by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h4], u₃.gpr, by decide, by decide,
      by rw [rd₃, wr₃]; exact covers_left (covers_off hw (by decide) (by decide)),
      by rw [wr₃]; exact hBw, (hBW.sub_right (Lay.wSub (by decide))).symm⟩
  refine WP.mono (xorLoop_ok t₃ lp) fun t' ⟨hm, lo⟩ => ?_
  rw [m₃] at hm
  have hl := length_xorBytes t.mem B (W + BitVec.ofNat 64 ofsO) 16
  have fw : Frame [⟨B, 16⟩] t.mem t'.mem := by rw [hm]; exact writeBytes_frame' _ hl
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
  have m₃ : t₃.mem = t.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : t₃.rd = t.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : t₃.wr = t.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have lp : LoopPre t₃ B (W + BitVec.ofNat 64 t2O) 16 :=
    ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h4],
      by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h0], u₃.gpr, by decide, by decide,
      by rw [rd₃, wr₃]; exact hBr, by rw [wr₃]; exact covers_off hw (by decide) (by decide),
      hBW.sub_right (Lay.wSub (by decide))⟩
  refine WP.seq (WP.mono (copyLoop_ok t₃ lp) fun t₄ ⟨hm, lo⟩ => ?_)
  rw [m₃] at hm
  have hl := Proof.Ocb.length_bytesAt t.mem B 16
  have fw : Frame [⟨W + BitVec.ofNat 64 t2O, 16⟩] t.mem t₄.mem := by rw [hm]; exact writeBytes_frame' _ hl
  have g₄ : ∀ r, r ∉ bodyRegs → t₄.gpr r = t.gpr r := fun r hr => by
    simp only [bodyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨n0, -, -, n3, n4, n5, n6⟩ := hr
    rw [lo.other r n0 n3 n4 n5 n6, u₃.other r n5, u₂.other r n4, u₁.other r n3]
  have rd₄ : t₄.rd = t.rd := by rw [lo.keeps.1, rd₃]
  have wr₄ : t₄.wr = t.wr := by rw [lo.keeps.2.1, wr₃]
  have hw₄ : Covers [⟨W, 2560⟩] t₄.wr := by rw [wr₄]; exact hw
  have h0₄ : t₄.gpr .s0 = W := by rw [g₄ _ (by decide), h0]
  refine WP.mono (xorB_ok (s := t₄) (pd := ckO) (qd := t2O) (cd := ckO) hW hW hW (by decide) (by decide)
    (by decide) h0₄ h0₄ h0₄ (by decide) (by decide) (by decide) (in_left (in_off hw₄ (by decide) (by decide)))
    (in_left (in_off hw₄ (by decide) (by decide))) (in_left (in_off hw₄ (by decide) (by decide)))
    (in_left (in_off hw₄ (by decide) (by decide))) (in_off hw₄ (by decide) (by decide))
    (in_off hw₄ (by decide) (by decide)) (Offset.sep _ (.inr (by decide)) (by decide) (by decide))
    (Offset.sep _ (.inr (by decide)) (by decide) (by decide))) fun t' B' => ?_
  have dB : ∀ d, d + 16 ≤ 2560 → (⟨B, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, 16⟩ :=
    fun _ hd => hBW.sub_right (Lay.wSub hd)
  have kB : blockAtMem t'.mem B = blockAtMem t.mem B := by
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
  have hDt : DBuf (V .s2) (V .s0) t D (16 * m) := hD.of_eq P.rd P.wr
  have hm := hD.lt
  have hBi := hDt.slice (a := 16 * i) (k := 16) (by omega_arith)
  have E := P.env
  have hw := E.perm.w
  have hW := L.wal
  refine WP.seq (WP.seq (WP.mono (lNtz_ok E.s0 hW hw (by omega_arith) (by omega_arith) P.s6 P.l0)
    fun t₁ P₁ => ?_))
  have h0₁ : t₁.gpr .s0 = V .s0 := by rw [P₁.gpr _ (by decide), E.s0]
  have hw₁ : Covers [⟨V .s0, 2560⟩] t₁.wr := by rw [P₁.wr]; exact hw
  refine WP.mono (xorB_ok (s := t₁) (pd := ofsO) (qd := lO) (cd := ofsO) hW hW hW (by decide) (by decide)
    (by decide) h0₁ h0₁ h0₁ (by decide) (by decide) (by decide) (in_left (in_off hw₁ (by decide) (by decide)))
    (in_left (in_off hw₁ (by decide) (by decide))) (in_left (in_off hw₁ (by decide) (by decide)))
    (in_left (in_off hw₁ (by decide) (by decide))) (in_off hw₁ (by decide) (by decide))
    (in_off hw₁ (by decide) (by decide)) (Offset.sep _ (.inr (by decide)) (by decide) (by decide))
    (Offset.sep _ (.inr (by decide)) (by decide) (by decide))) fun t₂ B₂ => ?_
  have g₂ : ∀ r, r ∉ stepRegs → t₂.gpr r = t.gpr r := fun r hr => by
    rw [B₂.gpr r (fun h => hr (t12_step r h)), P₁.gpr r (fun h => hr (ntz_step r h))]
  have rd₂ : t₂.rd = t.rd := by rw [B₂.rd, P₁.rd]
  have wr₂ : t₂.wr = t.wr := by rw [B₂.wr, P₁.wr]
  have sp₂ : t₂.sp = t.sp := by rw [B₂.sp, P₁.sp]
  have h0₂ : t₂.gpr .s0 = V .s0 := by rw [g₂ _ (by decide), E.s0]
  have h4₂ : t₂.gpr .s4 = D + BitVec.ofNat 64 (16 * i) := by rw [g₂ _ (by decide), P.s4]
  have fW₂ : Frame [⟨V .s0 + BitVec.ofNat 64 lO, 16⟩, ⟨V .s0 + BitVec.ofNat 64 ofsO, 16⟩] t.mem t₂.mem :=
    (P₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp))
  have kW₂ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨V .s0, 2560⟩ →
      blockAtMem t₂.mem Q = blockAtMem t.mem Q :=
    fun hQ => blockAtMem_frame fW₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact hQ.sub_right (Lay.wSub (by decide))
  have ofs₂ : blockAtMem t₂.mem (V .s0 + BitVec.ofNat 64 ofsO) = offAt O0 l (i + 1) := by
    rw [B₂.val, blockAtMem_frame P₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), P.ofs,
      P₁.val]
    rfl
  have ck₂ : blockAtMem t₂.mem (V .s0 + BitVec.ofNat 64 ckO) = ckF i := by
    rw [blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)), P.ck]
  have Bi₂ : blockAtMem t₂.mem (D + BitVec.ofNat 64 (16 * i)) = X i := by
    rw [kW₂ hBi.w, P.blk i hi]; simp
  have l0₂ : blockAtMem t₂.mem (V .s0 + BitVec.ofNat 64 l0O) = lAt l 0 := by
    rw [blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)), P.l0]
  refine WP.seq (WP.mono (hB t₂ _ h4₂ h0₂ (by rw [rd₂, wr₂]; exact hBi.rd) (by rw [wr₂]; exact hBi.wr)
    (by rw [wr₂]; exact hw) hBi.w) fun t₃ P₃ => ?_)
  have g₃ : ∀ r, r ∉ stepRegs → t₃.gpr r = t.gpr r := fun r hr => by rw [P₃.gpr r (fun h => hr (body_step r h)), g₂ r hr]
  have s5₃ : t₃.gpr .s5 = BitVec.ofNat 64 (m - i) := by rw [g₃ _ (by decide), P.s5]
  have s6₃ : t₃.gpr .s6 = BitVec.ofNat 64 (i + 1) := by rw [g₃ _ (by decide), P.s6]
  have s4₃ : t₃.gpr .s4 = D + BitVec.ofNat 64 (16 * i) := by rw [g₃ _ (by decide), P.s4]
  have kB₃ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * i), 16⟩ →
      (⟨Q, 16⟩ : Region).Disjoint ⟨V .s0, 2560⟩ → blockAtMem t₃.mem Q = blockAtMem t.mem Q := fun h₁ h₂ => by
    rw [blockAtMem_frame P₃.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h₁
      · exact h₂.sub_right (Lay.wSub (by decide))
      · exact h₂.sub_right (Lay.wSub (by decide))), kW₂ h₂]
  have dWB : ∀ d, d + 16 ≤ 2560 →
      (⟨V .s0 + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * i), 16⟩ :=
    fun _ hd => (hBi.w.sub_right (Lay.wSub hd)).symm
  unfold nextBlock
  refine wp_addi (imm := 16) (by decide) fun t₄ u₄ => wp_addi (imm := 1) (by decide) fun t₅ u₅ =>
    wp_subi (imm := 1) (by decide) fun t₆ u₆ => WP.block_nil ?_
  have hmem : t₆.mem = t₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
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
  have ev := eval_nonzero P'.s5 (by omega_arith)
  by_cases he : m - (i + 1) = 0
  · left
    exact ⟨ev.trans (by simp [he]), (show i + 1 = m by omega_arith) ▸ P'⟩
  · right
    exact ⟨ev.trans (by simp [he]), m - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, P'⟩

end VG.Proof.AesOcb.RISCV64
