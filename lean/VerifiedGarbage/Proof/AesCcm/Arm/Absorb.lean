import VerifiedGarbage.Proof.AesCcm.Arm.Tag

/-!
# AES-CCM on ARMv7: a buffer padded, chained (`absorbPad y`)

Untrusted: everything here is checked by Lean. The calls of
`vg_cmac_aes_update` take the key schedule, the MAC state at `W + y` and
the working space at `W + 384` from the environment (`updCall_of`).
`updBlock y` chains `B` (at `W + 32`) into the MAC state (`updBlock_ok`);
`absorbPad y` chains the `len` bytes at `P`, padded with zeros to whole
blocks: its whole blocks in one call (`absorbWhole_ok`), then its last
`len mod 16` bytes copied into the zeroed `B` (`absorbTail_ok`); together,
the blocks of the padded string (`absorbPad_ok`,
`Proof.AesCcm.blocks_pad16`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI zero16 copyLoop)
open VG.Proof.AesGcm.Arm (LoopOut LoopPre copyLoop_ok covers_cons covers_left bytesAt_frame
  runBlock_app_of and15 shr4 toNat32 ofNat_sub32 z_cmp eval_eq' Keeps z_subFlags gpr_subFlags)
open VG.Proof.CmacAes.Stream.Arm (blw16)
open VG.Proof.AesCcm (ctxCiph_frame bytesAt_prefix bytesAt_suffix bytesAt_writeBytes_base length_bytesAt)

/-- What the pieces of the MAC write: the MAC state at `W + y`, `B`, the
working space of the functions called and the stack below `sp`. -/
abbrev macR (w sp : BitVec 32) (y : Nat) : List Region :=
  [⟨State.addr w + BitVec.ofNat 64 y, 16⟩, ⟨State.addr w + BitVec.ofNat 64 32, 16⟩, scrR w, blw sp]

theorem blw16_eq {s : State} {sp : BitVec 32} (h : s.sp = sp) : blw16 s = blw sp := by
  subst h; rfl

/-- The last bytes of a string, padded to a block, if any are left after
its whole blocks. -/
def tailBlocks (x : List Byte) : List (List Byte) :=
  if x.length % 16 = 0 then [] else [x.drop (16 * (x.length / 16)) ++ Spec.Ccm.zeros (16 - x.length % 16)]

/-- What `absorbPad`'s pieces keep: the environment, the registers holding
the string, and what they write. -/
structure Absorbed (k w sp : BitVec 32) (R q1 : Nat) (s : State) (y : Nat) (P : BitVec 32) (len : Nat)
    (Y : List Byte) (s' : State) : Prop where
  env : Env k w sp R q1 s'
  r4 : s'.gpr .r4 = P
  r5 : s'.gpr .r5 = BitVec.ofNat 32 len
  frame : Frame (macR w sp y) s.mem s'.mem
  out : bytesAt s'.mem (State.addr w + BitVec.ofNat 64 y) 16 = Y
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

section
variable {k w sp : BitVec 32} {R q1 : Nat} (L : Lay k w sp)
include L

/-- A call of `vg_cmac_aes_update` with the key schedule, the MAC state at
`W + y`, `n` blocks at `D` and the working space at `W + 384`. -/
theorem updCall_of {s : State} (he : Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat}
    (hy : y + 16 ≤ 384) {D : BitVec 32} {n : Nat} (hn : 16 * n < 2 ^ 32) (fD : D.toNat + 16 * n ≤ 2 ^ 32)
    (dC : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 y, 16⟩)
    (dS : (⟨State.addr D, 16 * n⟩ : Region).Disjoint (scrR w))
    (dB : (blw sp).Disjoint ⟨State.addr D, 16 * n⟩) (rD : Covers [⟨State.addr D, 16 * n⟩] (s.rd ++ s.wr))
    (h0 : s.gpr .r0 = k) (h1 : s.gpr .r1 = BitVec.ofNat 32 R) (h2 : s.gpr .r2 = w + BitVec.ofNat 32 y)
    (h3 : s.gpr .r3 = D) (h12 : s.gpr .r12 = BitVec.ofNat 32 n) (hlr : s.gpr .lr = w + BitVec.ofNat 32 384) :
    UArgs s k (w + BitVec.ofNat 32 y) D (w + BitVec.ofNat 32 384) R n := by
  have eY := L.wA (d := y) (by omega)
  have e384 := L.wA (d := 384) (by decide)
  have hb := blw16_eq he.sp
  refine ⟨h0, h1, h2, h3, h12, hlr, hR, hn, by rw [he.sp]; exact L.sp16, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    L.kw, ?_, fD, ?_, covers_cons he.perm.k rD, ?_⟩
  · rw [eY]; exact L.k_w' (by omega)
  · rw [e384]; exact L.k_w' (by decide)
  · rw [eY]; exact dC
  · rw [e384]; exact dS
  · rw [eY, e384]; exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · rw [hb]; exact L.stk_k
  · rw [hb]; exact dB
  · rw [hb, eY]; exact L.stk_w' (by omega)
  · rw [hb, e384]; exact L.stk_w' (by decide)
  · rw [L.wN (by omega)]; have := L.ww; omega
  · rw [L.wN (by decide)]; have := L.ww; omega
  · rw [eY, e384]; exact covers_cons (he.perm.wC (by omega)) (he.perm.wC (by decide))

/-- `B` (at `W + 32`) chained into the MAC state at `W + y`. -/
theorem updBlock_ok {s : State} (he : Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat}
    (hy : y = 0 ∨ y = 112) :
    WP isa (updBlock y) s fun s' => Env k w sp R q1 s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 y, 16⟩, scrR w, blw sp] s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 y) 16 =
        Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (State.addr k) R)
          (bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16) [bytesAt s.mem (State.addr w + BitVec.ofNat 64 32) 16] := by
  have eo : encodable (BitVec.ofNat 32 y) = true := by rcases hy with rfl | rfl <;> decide
  obtain ⟨s₁, run₁, a0, a1, a2, a3, a12, alr, g₁, k₁⟩ : ∃ s₁, runBlock isa (updArgs y ++
      [addI .r3 .r11 bO, .mov .r12 (imm 1)]) s = some s₁ ∧
      s₁.gpr .r0 = k ∧ s₁.gpr .r1 = BitVec.ofNat 32 R ∧ s₁.gpr .r2 = w + BitVec.ofNat 32 y ∧
      s₁.gpr .r3 = w + BitVec.ofNat 32 32 ∧ s₁.gpr .r12 = BitVec.ofNat 32 1 ∧
      s₁.gpr .lr = w + BitVec.ofNat 32 384 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by simp only [updArgs, bO, scrO]; arun [he.r9, he.r8, he.r11, eo], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, he.r9]
    · simp [gpr_setReg, he.r8]
    · simp [gpr_setReg, he.r11]
    · simp [gpr_setReg, he.r11]
    · simp [gpr_setReg]
    · simp [gpr_setReg, he.r11]
    · intro r a b c d e f; simp [gpr_setReg, a, b, c, d, e, f]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  have e32 := L.wA (d := 32) (by decide)
  have eY := L.wA (d := y) (by omega)
  have dYB : (⟨State.addr w + BitVec.ofNat 64 32, 16⟩ : Region).Disjoint
      ⟨State.addr w + BitVec.ofNat 64 y, 16⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have U := updCall_of L he₁ hR (y := y) (by omega) (D := w + BitVec.ofNat 32 32) (n := 1) (by decide)
    (by rw [L.wN (by decide)]; have := L.ww; omega) (by rw [e32]; exact dYB)
    (by rw [e32]; exact L.w_w (.inl (by decide)) (by decide) (by decide))
    (by rw [e32]; exact L.stk_w' (by decide)) (by rw [e32]; exact covers_left (he₁.perm.wC (by decide)))
    a0 a1 a2 a3 a12 alr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.mono (upd_call U) fun s₂ h => ?_
  refine ⟨he₁.of_saved h.saved h.sp h.rd h.wr, by rw [h.rd, k₁.rd], by rw [h.wr, k₁.wr], fun r hr hlr => ?_,
    ?_, ?_⟩
  · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [h.saved r hr hlr, g₁ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 hlr]
  · have f := h.frame
    rw [blw16_eq (k₁.sp.trans he.sp), eY, L.wA (d := 384) (by decide), k₁.mem] at f
    exact f
  · have o := h.out
    rw [eY, Proof.Cmac.Stream.blocksAt_eq, Nat.mul_one, Proof.Cmac.Stream.blocks_single
      (Proof.Cmac.bytesAt_length _ _ _), k₁.mem, e32] at o
    rw [o]; rfl

omit L in
theorem sub_mac {y : Nat} {r : Region} (hr : r ∈ macR w sp y) : ∃ r' ∈ macR w sp y, Region.Sub r r' :=
  ⟨r, hr, fun _ h => h⟩

/-- The whole blocks of the string. -/
theorem absorbWhole_ok {s : State} (he : Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat}
    (hy : y = 0 ∨ y = 112) {P : BitVec 32} {len : Nat} (hP : len ≠ 0 → Buf w sp s P len) (hl : len < 2 ^ 32)
    (h4 : s.gpr .r4 = P) (h5 : s.gpr .r5 = BitVec.ofNat 32 len) :
    WP isa (absorbWhole y) s (Absorbed k w sp R q1 s y P len
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (State.addr k) R) (bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16)
        (Spec.Cmac.blocks 16 ((bytesAt s.mem (State.addr P) len).take (16 * (len / 16)))))) := by
  obtain ⟨s₁, run₁, h12₁, hz, g₁, k₁⟩ : ∃ s₁, runBlock isa [.mov .r12 (.shifted .r5 .lsr 4), .cmp .r12 (imm 0)] s =
      some s₁ ∧ s₁.gpr .r12 = BitVec.ofNat 32 (len / 16) ∧ s₁.z = decide (len / 16 = 0) ∧
      (∀ r, r ≠ .r12 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h5, shr4 hl]
    · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, shr4 hl]
      rw [z_cmp (by omega) (by decide)]
    · intro r a; simp [gpr_setReg, a]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.sp k₁.rd k₁.wr
  refine WP.ite (decide (len / 16 = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : len / 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨he₁, by rw [g₁ _ (by decide), h4], by rw [g₁ _ (by decide), h5],
      by rw [k₁.mem]; exact Frame.refl _ _, ?_, k₁.rd, k₁.wr⟩
    rw [k₁.mem, h0, Nat.mul_zero, List.take_zero]; rfl
  · have h0 : len / 16 ≠ 0 := by simpa using hf
    obtain ⟨s₂, run₂, a0, a1, a2, a3, alr, g₂, k₂⟩ : ∃ s₂, runBlock isa (updArgs y ++ [.mov .r3 (.reg .r4)]) s₁ =
        some s₂ ∧ s₂.gpr .r0 = k ∧ s₂.gpr .r1 = BitVec.ofNat 32 R ∧ s₂.gpr .r2 = w + BitVec.ofNat 32 y ∧
        s₂.gpr .r3 = P ∧ s₂.gpr .lr = w + BitVec.ofNat 32 384 ∧
        (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .lr → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
      have eo : encodable (BitVec.ofNat 32 y) = true := by rcases hy with rfl | rfl <;> decide
      refine ⟨_, by simp only [updArgs, scrO]; arun [he₁.r9, he₁.r8, he₁.r11, eo], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, he₁.r9]
      · simp [gpr_setReg, he₁.r8]
      · simp [gpr_setReg, he₁.r11]
      · simp [gpr_setReg, g₁ .r4 (by decide), h4]
      · simp [gpr_setReg, he₁.r11]
      · intro r a b c d e; simp [gpr_setReg, a, b, c, d, e]
      · exact ⟨rfl, rfl, rfl, rfl⟩
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have he₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide) (by decide) (by decide)
        (by decide)) k₂.sp k₂.rd k₂.wr
    have hb : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
    have hq := (hP (by omega)).take hb
    have U := updCall_of L he₂ hR (y := y) (by omega) (D := P) (n := len / 16) (by omega) hq.fit
      (hq.w.sub_right (Lay.wSub (by omega))) (hq.w.sub_right (Lay.wSub (by decide))) hq.stk
      (by rw [k₂.rd, k₂.wr, k₁.rd, k₁.wr]; exact hq.rd) a0 a1 a2 a3
      (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), h12₁]) alr
    refine WP.mono (upd_call U) fun s₃ h => ⟨he₂.of_saved h.saved h.sp h.rd h.wr, ?_, ?_, ?_, ?_,
      by rw [h.rd, k₂.rd, k₁.rd], by rw [h.wr, k₂.wr, k₁.wr]⟩
    · rw [h.saved _ (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₁ _ (by decide), h4]
    · rw [h.saved _ (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₁ _ (by decide), h5]
    · have f := h.frame
      rw [blw16_eq (k₂.sp.trans (k₁.sp.trans he.sp)), L.wA (d := y) (by omega), L.wA (d := 384) (by decide),
        k₂.mem, k₁.mem] at f
      exact f.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact sub_mac (by simp)
    · have o := h.out
      rw [L.wA (d := y) (by omega), Proof.Cmac.Stream.blocksAt_eq, k₂.mem, k₁.mem, bytesAt_prefix _ _ hb] at o
      rw [o]; rfl

/-- The last bytes of the string, padded with zeros in `B`. -/
theorem absorbTail_ok {s : State} (he : Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat}
    (hy : y = 0 ∨ y = 112) {P : BitVec 32} {len : Nat} (hP : len ≠ 0 → Buf w sp s P len) (hl : len < 2 ^ 32)
    (h4 : s.gpr .r4 = P) (h5 : s.gpr .r5 = BitVec.ofNat 32 len) :
    WP isa (absorbTail y) s (Absorbed k w sp R q1 s y P len
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (State.addr k) R) (bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16)
        (tailBlocks (bytesAt s.mem (State.addr P) len)))) := by
  have hxl := length_bytesAt s.mem (State.addr P) len
  have hand := and15 (BitVec.ofNat 32 len)
  rw [toNat32 hl] at hand
  obtain ⟨s₁, run₁, h6₁, hz, g₁, k₁⟩ : ∃ s₁, runBlock isa [.dp .and .r6 .r5 (imm 15), .cmp .r6 (imm 0)] s =
      some s₁ ∧ s₁.gpr .r6 = BitVec.ofNat 32 (len % 16) ∧ s₁.z = decide (len % 16 = 0) ∧
      (∀ r, r ≠ .r6 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h5, imm, hand]
    · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, imm, hand]
      rw [z_cmp (by omega) (by decide)]
    · intro r a; simp [gpr_setReg, a]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.sp k₁.rd k₁.wr
  refine WP.ite (decide (len % 16 = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : len % 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨he₁, by rw [g₁ _ (by decide), h4], by rw [g₁ _ (by decide), h5],
      by rw [k₁.mem]; exact Frame.refl _ _, ?_, k₁.rd, k₁.wr⟩
    simp only [k₁.mem, tailBlocks, hxl, h0, ↓reduceIte]; rfl
  · have h0 : len % 16 ≠ 0 := by simpa using hf
    obtain ⟨s₂, run₂, hm₂, g₂, rd₂, wr₂, sp₂, -⟩ := zero16_ok L he₁ (d := bO) (by decide) (by decide)
    simp only [bO] at hm₂
    have hj : 16 * (len / 16) + len % 16 = len := by omega
    have hsub : BitVec.ofNat 32 len - BitVec.ofNat 32 (len % 16) = BitVec.ofNat 32 (16 * (len / 16)) := by
      rw [ofNat_sub32 (Nat.mod_le _ _) hl]; congr 1; omega
    obtain ⟨s₃, run₃, a1, a2, a3, g₃, k₃⟩ : ∃ s₃, runBlock isa [.dp .sub .r1 .r5 (.reg .r6), .dp .add .r1 .r1 (.reg .r4),
        addI .r2 .r11 bO, .mov .r3 (.reg .r6)] s₂ = some s₃ ∧
        s₃.gpr .r1 = P + BitVec.ofNat 32 (16 * (len / 16)) ∧ s₃.gpr .r2 = w + BitVec.ofNat 32 32 ∧
        s₃.gpr .r3 = BitVec.ofNat 32 (len % 16) ∧
        (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ := by
      have r4₂ : s₂.gpr .r4 = P := by rw [g₂ _ (by decide), g₁ _ (by decide), h4]
      have r5₂ : s₂.gpr .r5 = BitVec.ofNat 32 len := by rw [g₂ _ (by decide), g₁ _ (by decide), h5]
      have r6₂ : s₂.gpr .r6 = BitVec.ofNat 32 (len % 16) := by rw [g₂ _ (by decide), h6₁]
      have r11₂ : s₂.gpr .r11 = w := by rw [g₂ _ (by decide), he₁.r11]
      refine ⟨_, by simp only [bO]; arun [r11₂], ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, r4₂, r5₂, r6₂, hsub, BitVec.add_comm]
      · simp [gpr_setReg, r11₂]
      · simp [gpr_setReg, r6₂]
      · intro r a b c; simp [gpr_setReg, a, b, c]
      · exact ⟨rfl, rfl, rfl, rfl⟩
    refine WP.seq (WP.of_runBlock ⟨s₃, by
      rw [show zero16 bO ++ [.dp .sub .r1 .r5 (.reg .r6), .dp .add .r1 .r1 (.reg .r4), addI .r2 .r11 bO,
        .mov .r3 (.reg .r6)] = zero16 bO ++ ([.dp .sub .r1 .r5 (.reg .r6), .dp .add .r1 .r1 (.reg .r4),
        addI .r2 .r11 bO, .mov .r3 (.reg .r6)] : List Instr) from rfl]
      exact runBlock_app_of run₂ run₃, ?_⟩)
    have he₃ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        rw [g₃ _ (by decide) (by decide) (by decide), g₂ _ (by decide)]) (k₃.sp.trans sp₂)
      (k₃.rd.trans rd₂) (k₃.wr.trans wr₂)
    have hT := ((hP (by omega)).sub (j := 16 * (len / 16)) (k := len % 16) (by omega) (by omega)).of_eq (s' := s₃)
      (by rw [k₃.rd, rd₂, k₁.rd]) (by rw [k₃.wr, wr₂, k₁.wr])
    have e32 := L.wA (d := 32) (by decide)
    have eT := (hP (by omega)).addr (j := 16 * (len / 16)) (by omega)
    have lp : LoopPre s₃ (P + BitVec.ofNat 32 (16 * (len / 16))) (w + BitVec.ofNat 32 32) (len % 16) := by
      refine ⟨a1, a2, a3, by omega, by omega, hT.fit, by rw [L.wN (by decide)]; have := L.ww; omega, hT.rd, ?_, ?_⟩
      · rw [e32]; exact he₃.perm.wC (by omega)
      · rw [e32]; exact hT.w.sub_right (Lay.wSub (by omega))
    refine WP.seq (WP.mono (copyLoop_ok s₃ lp) fun s₄ ⟨hm₄, lo⟩ => ?_)
    have he₄ := he₃.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact lo.other _ (by decide) (by decide) (by decide) (by decide)
        (by decide)) lo.sp lo.rd lo.wr
    rw [k₃.mem, e32, eT] at hm₄
    -- What was written: only `B`.
    have fZ : Frame [⟨State.addr w + BitVec.ofNat 64 32, 16⟩] s.mem s₂.mem := by
      rw [hm₂, k₁.mem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
    have fB : Frame [⟨State.addr w + BitVec.ofNat 64 32, 16⟩] s.mem s₄.mem := by
      rw [hm₄]
      exact fZ.trans (writeBytes_frame _ _ _ (by
        rw [length_bytesAt]
        exact Offset.contains _ (d := 32) (n := len % 16) (e := 32) (k := 16) (by decide) (by omega) (by decide)))
    have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
    have hK₄ : Spec.Ccm.ctxCiph s₄.mem (State.addr k) R = Spec.Ccm.ctxCiph s.mem (State.addr k) R :=
      ctxCiph_frame fB (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.k_w' (by decide)) hRb
    have hY₄ : bytesAt s₄.mem (State.addr w + BitVec.ofNat 64 y) 16 =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16 :=
      bytesAt_frame fB (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rcases hy with rfl | rfl
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
        · exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)
    have hB₄ : bytesAt s₄.mem (State.addr w + BitVec.ofNat 64 32) 16 =
        (bytesAt s.mem (State.addr P) len).drop (16 * (len / 16)) ++ Spec.Ccm.zeros (16 - len % 16) := by
      have hs₂ : bytesAt s₂.mem (State.addr P + BitVec.ofNat 64 (16 * (len / 16))) (len % 16) =
          (bytesAt s.mem (State.addr P) len).drop (16 * (len / 16)) := by
        rw [bytesAt_frame fZ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; rw [← eT]
            exact hT.w.sub_right (Lay.wSub (by decide))) (by omega),
          show len % 16 = len - 16 * (len / 16) by omega, bytesAt_suffix _ _ (by omega)]
      have hz : bytesAt s₂.mem (State.addr w + BitVec.ofNat 64 32) 16 = Spec.Ccm.zeros 16 := by
        rw [hm₂]; exact store4_zero_bytes' _ _
      rw [hm₄, bytesAt_writeBytes_base _ _ _ (by rw [length_bytesAt]; omega) (by decide), hs₂, hz,
        List.length_drop, hxl]
      simp only [Spec.Ccm.zeros, List.drop_replicate]
      congr 2
      omega
    refine WP.mono (updBlock_ok L he₄ hR hy) fun s₅ ⟨he₅, rd₅, wr₅, g₅, f₅, o₅⟩ =>
      ⟨he₅, ?_, ?_, ?_, ?_, by rw [rd₅, lo.rd, k₃.rd, rd₂, k₁.rd], by rw [wr₅, lo.wr, k₃.wr, wr₂, k₁.wr]⟩
    · rw [g₅ _ (by decide) (by decide), lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₃ _ (by decide) (by decide) (by decide), g₂ _ (by decide), g₁ _ (by decide), h4]
    · rw [g₅ _ (by decide) (by decide), lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₃ _ (by decide) (by decide) (by decide), g₂ _ (by decide), g₁ _ (by decide), h5]
    · refine (fB.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr; exact sub_mac (by simp)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact sub_mac (by simp)
    · rw [o₅, hY₄, hB₄, hK₄]
      simp only [tailBlocks, hxl, h0, ↓reduceIte]

omit L in
/-- A buffer missing `W` and the stack below `sp` keeps its bytes. -/
theorem buf_kept {s : State} {P : BitVec 32} {len : Nat} (hP : Buf w sp s P len) {y : Nat}
    (hy : y + 16 ≤ 2560) {m m' : Mem} (hf : Frame (macR w sp y) m m') :
    bytesAt m' (State.addr P) len = bytesAt m (State.addr P) len :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Lay.wSub hy)
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm) (by have := hP.lt; omega)

theorem k_macR {y : Nat} (hy : y + 16 ≤ 2560) : ∀ r ∈ macR w sp y, (⟨State.addr k, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.k_w' hy
  · exact L.k_w' (by decide)
  · exact L.k_w' (by decide)
  · exact L.stk_k.symm

/-- The `len` bytes at `P`, padded with zeros to whole blocks, chained into
the MAC state at `W + y`. -/
theorem absorbPad_ok {s : State} (he : Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat}
    (hy : y = 0 ∨ y = 112) {P : BitVec 32} {len : Nat} (hP : len ≠ 0 → Buf w sp s P len) (hl : len < 2 ^ 32)
    (h4 : s.gpr .r4 = P) (h5 : s.gpr .r5 = BitVec.ofNat 32 len) :
    WP isa (absorbPad y) s (Absorbed k w sp R q1 s y P len
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (State.addr k) R) (bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16)
        (Spec.Cmac.blocks 16 (Spec.Ccm.pad16 (bytesAt s.mem (State.addr P) len))))) := by
  refine WP.seq (WP.mono (absorbWhole_ok L he hR hy hP hl h4 h5) fun s₁ A₁ => ?_)
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  refine WP.mono (absorbTail_ok L A₁.env hR hy (fun h => (hP h).of_eq A₁.rd A₁.wr) hl A₁.r4 A₁.r5) fun s₂ A₂ =>
    ⟨A₂.env, A₂.r4, A₂.r5, A₁.frame.trans A₂.frame, ?_, A₂.rd.trans A₁.rd, A₂.wr.trans A₁.wr⟩
  have hk : bytesAt s₁.mem (State.addr P) len = bytesAt s.mem (State.addr P) len := by
    rcases Nat.eq_zero_or_pos len with e | e
    · subst e; rfl
    · exact buf_kept (hP (by omega)) (by omega) A₁.frame
  rw [A₂.out, A₁.out, hk, ctxCiph_frame A₁.frame (k_macR L (by omega)) hRb,
    ← Proof.Cmac.chain_append, Proof.AesCcm.blocks_pad16, length_bytesAt, tailBlocks, length_bytesAt]

end

end VG.Proof.AesCcm.Arm
