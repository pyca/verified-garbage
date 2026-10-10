import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Tail

/-!
# ChaCha20 on x86-64 with AVX2: the last 385 to 511 bytes

`last8` computes eight blocks as the loop does (`setup`, `rounds`) and
writes them out with `finishWith xorRow8` (`Finish.lean`): blocks 0 to 5
XORed into the 384 bytes of data at `rsi`, and blocks 6 and 7 stored to
`buf` (`b67Off`). `move67` then moves those two to `buf[0, 128)`, from
which `Avx2Tail.fromBuf` XORs the rest of the data.
-/

namespace VG.Proof.ChaCha20.X86_64.Avx2

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx2
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word stateAt keystream serialize)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx512Tail (Done win win_sub not_win ks_at data_step fromBuf_ok fin_ok
  Done.fin r9_not_calleeSaved)

/-! ## Writing out a row -/

/-- The first six blocks' 384 bytes of data. -/
abbrev dR3 (a : Addr) : Region := ⟨a, 384⟩

/-- Every access within the 384 bytes at `a` is permitted by `ws`. -/
def DWin3 (ws : List Region) (a : Addr) : Prop :=
  ∀ off n, off + n ≤ 384 → InRegions ws (a + BitVec.ofNat 64 off) n

/-- Where block `6 + j` is stored in `buf`. -/
abbrev bR (buf : Addr) (j : Nat) : Region := ⟨buf + BitVec.ofNat 64 (b67Off j), 64⟩

theorem xor16_3_ok {x : XReg} (hx : x ≠ .xmm12) {off : Nat} (ho : off + 16 ≤ 384) {a : Addr}
    {s : State} (hrsi : s.gpr .rsi = a) (hw : DWin3 s.wr a) :
    WP isa (.block (xor16 x off)) s fun s' =>
      (∀ k < 512, s'.mem (a + BitVec.ofNat 64 k) = if off ≤ k ∧ k < off + 16 then
        s.mem (a + BitVec.ofNat 64 k) ^^^ byte (s.lane x 0) (k - off) else s.mem (a + BitVec.ofNat 64 k)) ∧
      Frame [dR3 a] s.mem s'.mem ∧
      (∀ r l, r ≠ .xmm12 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have c : (dR3 a).Contains (a + BitVec.ofNat 64 off) 16 := Offset.contains_base a ho (by lit_omega)
  have o1 : InRegions s.wr (a + BitVec.ofNat 64 off) 16 := hw off 16 ho
  have i1 : InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 off) 16 :=
    let ⟨r, hr, hc⟩ := o1; ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.of_runBlock
  simp only [xor16, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hrsi, State.load128,
    State.store128_eq, i1, o1, ite_true, Option.map_some, Option.some.injEq,
    exists_eq_left', VOp.exec_gpr, VOp.exec_mem, VOp.exec_rd, VOp.exec_wr, State.setV_gpr,
    State.setV_mem, State.setV_rd, State.setV_wr, State.setMem_gpr, State.setMem_mem,
    State.setMem_rd, State.setMem_wr, State.xmm_lane, lane_vbin128, State.lane_setV128, hx,
    ite_false, VBinOp.sse, XBinOp.eval]
  refine ⟨fun k hk => ?_, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c,
    fun r l hr => ?_, trivial, trivial, trivial⟩
  · rw [byte_write16 _ _ _ (by lit_omega) hk]
    by_cases h : off ≤ k ∧ k < off + 16
    · simp only [h.1, h.2, and_self, ite_true, byte]
      rw [BitVec.extractLsb'_xor, byte_readW _ _ (by lit_omega), add_ofNat, Nat.add_sub_cancel' h.1]
    · simp only [h, ite_false]
  · simp only [State.setMem_lane, lane_vbin128, State.lane_setV128, hr, ite_false]

/-- `piece`, for blocks `i` and `i + 4` of the first six. -/
theorem piece3_ok {row i : Nat} (hrow : row < 4) (hi : i < 2) {x : XReg} (hx12 : x ≠ .xmm12)
    {a : Addr} {s : State} (hrsi : s.gpr .rsi = a) (hw : DWin3 s.wr a) :
    WP isa (.block (piece row x i)) s fun s' =>
      (∀ k < 512, s'.mem (a + BitVec.ofNat 64 k) =
        if (k / 64 = i ∨ k / 64 = i + 4) ∧ k % 64 / 16 = row then
          s.mem (a + BitVec.ofNat 64 k) ^^^ byte (s.lane x (k / 64 / 4)) (k % 16)
        else s.mem (a + BitVec.ofNat 64 k)) ∧
      Frame [dR3 a] s.mem s'.mem ∧
      (∀ r l, r ≠ .xmm12 → r ≠ .xmm13 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.block_append (WP.block_append (WP.mono (xor16_3_ok hx12 (by lit_omega) hrsi hw)
    fun s₁ ⟨m₁, f₁, l₁, g₁, r₁, w₁⟩ => ?_))
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  refine WP.mono (xor16_3_ok (x := .xmm13) (by decide) (off := 64 * (i + 4) + 16 * row) (a := a) (by lit_omega)
    (by rw [VOp.exec_gpr, g₁, hrsi]) (by rw [VOp.exec_wr, w₁]; exact hw))
    fun s₃ ⟨m₃, f₃, l₃, g₃, r₃, w₃⟩ => ?_
  simp only [VOp.exec_gpr, VOp.exec_mem, VOp.exec_rd, VOp.exec_wr, lane_vextracti128_1, ite_true,
    l₁ x 1 hx12] at m₃ f₃ l₃ g₃ r₃ w₃
  refine ⟨fun k hk => ?_, f₁.trans f₃, fun r l h12 h13 => ?_, g₃.trans g₁, r₃.trans r₁, w₃.trans w₁⟩
  · rw [m₃ k hk, m₁ k hk]
    by_cases h1 : 64 * i + 16 * row ≤ k ∧ k < 64 * i + 16 * row + 16
    · have h2 : ¬ (64 * (i + 4) + 16 * row ≤ k ∧ k < 64 * (i + 4) + 16 * row + 16) := by omega
      have hc : (k / 64 = i ∨ k / 64 = i + 4) ∧ k % 64 / 16 = row := by omega
      rw [ite_eq_right h2, ite_eq_left h1, ite_eq_left hc, show k / 64 / 4 = 0 by omega,
        show k - (64 * i + 16 * row) = k % 16 by omega]
    · by_cases h2 : 64 * (i + 4) + 16 * row ≤ k ∧ k < 64 * (i + 4) + 16 * row + 16
      · have hc : (k / 64 = i ∨ k / 64 = i + 4) ∧ k % 64 / 16 = row := by omega
        rw [ite_eq_left h2, ite_eq_right h1, ite_eq_left hc, show k / 64 / 4 = 1 by omega,
          show k - (64 * (i + 4) + 16 * row) = k % 16 by omega]
      · have hc : ¬ ((k / 64 = i ∨ k / 64 = i + 4) ∧ k % 64 / 16 = row) := by omega
        rw [ite_eq_right h2, ite_eq_right h1, ite_eq_right hc]
  · rw [l₃ r l h12, ite_eq_right h13, l₁ r l h12]

/-- Row `row` of block `2 + j` from lane 0 of `x` into the data, and of block
`6 + j` from lane 1 to `buf`. -/
def pieceS (row : Nat) (x : XReg) (j : Nat) : List Instr :=
  xor16 x (64 * (2 + j) + 16 * row) ++
    [.vop (.vextracti128 .xmm13 x 1), .vmovdquStore .l128 (at_ .rcx (b67Off j + 16 * row)) .xmm13]

theorem b67Off_le {j : Nat} : b67Off j + 64 ≤ 288 := by
  simp only [b67Off]; split <;> omega

theorem pieceS_ok {row j : Nat} (hrow : row < 4) (hj : j < 2) {x : XReg} (hx12 : x ≠ .xmm12)
    {a buf : Addr} {s : State} (hrsi : s.gpr .rsi = a) (hrcx : s.gpr .rcx = buf) (hw : DWin3 s.wr a)
    (hb : bufR buf ∈ s.wr) (hd : (dR3 a).Disjoint (bufR buf)) :
    WP isa (.block (pieceS row x j)) s fun s' =>
      (∀ k < 384, s'.mem (a + BitVec.ofNat 64 k) =
        if 64 * (2 + j) + 16 * row ≤ k ∧ k < 64 * (2 + j) + 16 * row + 16 then
          s.mem (a + BitVec.ofNat 64 k) ^^^ byte (s.lane x 0) (k % 16)
        else s.mem (a + BitVec.ofNat 64 k)) ∧
      (∀ k < 64, s'.mem (buf + BitVec.ofNat 64 (b67Off j) + BitVec.ofNat 64 k) =
        if k / 16 = row then byte (s.lane x 1) (k % 16)
        else s.mem (buf + BitVec.ofNat 64 (b67Off j) + BitVec.ofNat 64 k)) ∧
      Frame [dR3 a, bR buf j] s.mem s'.mem ∧
      (∀ r l, r ≠ .xmm12 → r ≠ .xmm13 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hbo := b67Off_le (j := j)
  refine WP.block_append (WP.mono (xor16_3_ok hx12 (by lit_omega) hrsi hw)
    fun s₁ ⟨m₁, f₁, l₁, g₁, r₁, w₁⟩ => ?_)
  have o : InRegions s₁.wr (buf + BitVec.ofNat 64 (b67Off j + 16 * row)) 16 := by
    rw [w₁]; exact out_buf hb (by lit_omega)
  have c : (bR buf j).Contains (buf + BitVec.ofNat 64 (b67Off j + 16 * row)) 16 :=
    Offset.contains buf (by lit_omega) (by lit_omega) (by lit_omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, VOp.exec_gpr, VOp.exec_wr, g₁, hrcx,
    State.store128_eq, o, ite_true, Option.some.injEq, exists_eq_left']
  simp only [VOp.exec_mem, VOp.exec_gpr, VOp.exec_rd, VOp.exec_wr, State.setMem_mem, State.setMem_gpr,
    State.setMem_rd, State.setMem_wr, State.setMem_lane, State.xmm_lane, lane_vextracti128_1, ite_true,
    l₁ x 1 hx12]
  have W : Frame [bR buf j] s₁.mem
      (s₁.mem.writeW (buf + BitVec.ofNat 64 (b67Off j + 16 * row)) (s.lane x 1)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c
  have hbuf : ∀ k < 64, s₁.mem (buf + BitVec.ofNat 64 (b67Off j) + BitVec.ofNat 64 k) =
      s.mem (buf + BitVec.ofNat 64 (b67Off j) + BitVec.ofNat 64 k) := fun k hk => by
    rw [add_ofNat]
    exact f₁ _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact fun hc => hd _ hc (bufR_contains buf (by lit_omega))
  refine ⟨fun k hk => ?_, fun k hk => ?_, (f₁.mono (by simp)).trans (W.mono (by simp)),
    fun r l h12 h13 => ?_, g₁, r₁, w₁⟩
  · rw [W _ fun r hr => ?_, m₁ k (by omega)]
    · by_cases h : 64 * (2 + j) + 16 * row ≤ k ∧ k < 64 * (2 + j) + 16 * row + 16
      · rw [ite_eq_left h, ite_eq_left h, show k - (64 * (2 + j) + 16 * row) = k % 16 by omega]
      · rw [ite_eq_right h, ite_eq_right h]
    · simp only [List.mem_singleton] at hr; subst hr
      exact fun hc => hd _ (Offset.contains_base a (d := k) (n := 1) (by omega) (by lit_omega))
        (Offset.sub_base buf (k := 320) (by lit_omega) _ hc)
  · rw [← add_ofNat, byte_write16 _ _ _ (by lit_omega) (by lit_omega)]
    by_cases h : 16 * row ≤ k ∧ k < 16 * row + 16
    · rw [ite_eq_left h, ite_eq_left (by omega), show k - 16 * row = k % 16 by omega]
    · rw [ite_eq_right h, ite_eq_right (by omega), hbuf k hk]
  · rw [ite_eq_right h13, l₁ r l h12]


theorem xorRow8_eq (row : Nat) (x0 x1 x2 x3 : XReg) : xorRow8 row [x0, x1, x2, x3] =
    piece row x0 0 ++ (piece row x1 1 ++ (pieceS row x2 0 ++ pieceS row x3 1)) := rfl

section
variable {a buf : Addr}

theorem bR_dR3 (hd : (dR3 a).Disjoint (bufR buf)) (j : Nat) : (bR buf j).Disjoint (dR3 a) :=
  (hd.sub_right (Offset.sub_base buf (k := 320) (by have := b67Off_le (j := j); omega))).symm

theorem bR_01 : (bR buf 0).Disjoint (bR buf 1) := Offset.disjoint buf (by decide) (by decide) (by decide)

end

theorem xorRow8_ok {row : Nat} (hrow : row < 4) {x0 x1 x2 x3 : XReg}
    (h0 : x0 ≠ .xmm12 ∧ x0 ≠ .xmm13) (h1 : x1 ≠ .xmm12 ∧ x1 ≠ .xmm13)
    (h2 : x2 ≠ .xmm12 ∧ x2 ≠ .xmm13) (h3 : x3 ≠ .xmm12 ∧ x3 ≠ .xmm13) {a buf : Addr} {s : State}
    (hrsi : s.gpr .rsi = a) (hrcx : s.gpr .rcx = buf) (hw : DWin3 s.wr a) (hb : bufR buf ∈ s.wr)
    (hd : (dR3 a).Disjoint (bufR buf)) :
    WP isa (.block (xorRow8 row [x0, x1, x2, x3])) s fun s' =>
      (∀ k < 384, s'.mem (a + BitVec.ofNat 64 k) =
        if k % 64 / 16 = row then
          s.mem (a + BitVec.ofNat 64 k) ^^^
            byte (s.lane ([x0, x1, x2, x3].getD (k / 64 % 4) .xmm0) (k / 64 / 4)) (k % 16)
        else s.mem (a + BitVec.ofNat 64 k)) ∧
      (∀ j < 2, ∀ k < 64, s'.mem (buf + BitVec.ofNat 64 (b67Off j) + BitVec.ofNat 64 k) =
        if k / 16 = row then byte (s.lane ([x2, x3].getD j .xmm0) 1) (k % 16)
        else s.mem (buf + BitVec.ofNat 64 (b67Off j) + BitVec.ofNat 64 k)) ∧
      Frame [dR3 a, bR buf 0, bR buf 1] s.mem s'.mem ∧
      (∀ r l, r ≠ .xmm12 → r ≠ .xmm13 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [xorRow8_eq]
  refine WP.block_append (WP.mono (piece3_ok hrow (i := 0) (by decide) h0.1 hrsi hw)
    fun s₁ ⟨m₁, f₁, l₁, g₁, r₁, w₁⟩ => ?_)
  refine WP.block_append (WP.mono (piece3_ok hrow (i := 1) (a := a) (by decide) h1.1 (by rw [g₁, hrsi])
    (by rw [w₁]; exact hw)) fun s₂ ⟨m₂, f₂, l₂, g₂, r₂, w₂⟩ => ?_)
  refine WP.block_append (WP.mono (pieceS_ok hrow (j := 0) (a := a) (buf := buf) (by decide) h2.1
    (by rw [g₂, g₁, hrsi]) (by rw [g₂, g₁, hrcx]) (by rw [w₂, w₁]; exact hw) (by rw [w₂, w₁]; exact hb) hd)
    fun s₃ ⟨m₃, b₃, f₃, l₃, g₃, r₃, w₃⟩ => ?_)
  refine WP.mono (pieceS_ok hrow (j := 1) (a := a) (buf := buf) (by decide) h3.1
    (by rw [g₃, g₂, g₁, hrsi]) (by rw [g₃, g₂, g₁, hrcx]) (by rw [w₃, w₂, w₁]; exact hw)
    (by rw [w₃, w₂, w₁]; exact hb) hd) fun s₄ ⟨m₄, b₄, f₄, l₄, g₄, r₄, w₄⟩ => ?_
  have e1 : ∀ l, s₁.lane x1 l = s.lane x1 l := fun l => l₁ _ l h1.1 h1.2
  have e2 : ∀ l, s₂.lane x2 l = s.lane x2 l := fun l => (l₂ _ l h2.1 h2.2).trans (l₁ _ l h2.1 h2.2)
  have e3 : ∀ l, s₃.lane x3 l = s.lane x3 l := fun l =>
    ((l₃ _ l h3.1 h3.2).trans (l₂ _ l h3.1 h3.2)).trans (l₁ _ l h3.1 h3.2)
  have bd := bR_dR3 hd
  have fb : ∀ j, ∀ k < 64, s₂.mem (buf + BitVec.ofNat 64 (b67Off j) + BitVec.ofNat 64 k) =
      s.mem (buf + BitVec.ofNat 64 (b67Off j) + BitVec.ofNat 64 k) := fun j k hk => by
    have d : ∀ r ∈ [dR3 a], (bR buf j).Disjoint r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact bd _
    exact (f₂.bytes d (show 64 ≤ 2 ^ 64 by decide) hk).trans (f₁.bytes d (show 64 ≤ 2 ^ 64 by decide) hk)
  refine ⟨fun k hk => ?_, fun j hj k hk => ?_, ?_, fun r l n12 n13 => ?_,
    by rw [g₄, g₃, g₂, g₁], by rw [r₄, r₃, r₂, r₁], by rw [w₄, w₃, w₂, w₁]⟩
  · rw [m₄ k hk, m₃ k hk, m₂ k (by omega), m₁ k (by omega), e1, e2, e3]
    rcases (by omega : k / 64 = 0 ∨ k / 64 = 1 ∨ k / 64 = 2 ∨ k / 64 = 3 ∨
      k / 64 = 4 ∨ k / 64 = 5) with h | h | h | h | h | h <;>
      by_cases hr : k % 64 / 16 = row <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right] <;>
      simp only [h, Nat.reduceMod, Nat.reduceDiv, List.getD_cons_zero, List.getD_cons_succ]
  · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · have d : ∀ r ∈ [dR3 a, bR buf 1], (bR buf 0).Disjoint r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact bd _
        · exact bR_01
      rw [f₄.bytes d (show 64 ≤ 2 ^ 64 by decide) hk, b₃ k hk, fb _ k hk, e2]; rfl
    · have d : ∀ r ∈ [dR3 a, bR buf 0], (bR buf 1).Disjoint r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact bd _
        · exact bR_01.symm
      rw [b₄ k hk, f₃.bytes d (show 64 ≤ 2 ^ 64 by decide) hk, fb _ k hk, e3]; rfl
  · exact (((f₁.mono (by simp)).trans (f₂.mono (by simp))).trans (f₃.mono (by simp))).trans (f₄.mono (by simp))
  · rw [l₄ r l n12 n13, l₃ r l n12 n13, l₂ r l n12 n13, l₁ r l n12 n13]

/-- `xorRow8`'s effect: row `row` of the blocks `B 0, …, B 5` XORed into the
384 bytes at `a`, and of `B 6`, `B 7` stored to `buf` (`bR`). -/
def Eff8 (a buf : Addr) (row : Nat) (B : Nat → CState) (m m' : Mem) : Prop :=
  (∀ k < 384, m' (a + BitVec.ofNat 64 k) =
    if k % 64 / 16 = row then m (a + BitVec.ofNat 64 k) ^^^ (serialize (B (k / 64))).getD (k % 64) 0
    else m (a + BitVec.ofNat 64 k)) ∧
  ∀ j < 2, ∀ k < 64, m' (buf + BitVec.ofNat 64 (b67Off j) + BitVec.ofNat 64 k) =
    if k / 16 = row then (serialize (B (6 + j))).getD k 0
    else m (buf + BitVec.ofNat 64 (b67Off j) + BitVec.ofNat 64 k)

theorem xorRow8_out {a buf : Addr} {g : Reg → BitVec 64} {w : List Region} (hrsi : g .rsi = a)
    (hrcx : g .rcx = buf) (hw : DWin3 w a) (hb : bufR buf ∈ w) (hd : (dR3 a).Disjoint (bufR buf))
    {row : Nat} (hrow : row < 4) {x0 x1 x2 x3 : XReg} (e01 : x0 ≠ x1) (e02 : x0 ≠ x2)
    (e03 : x0 ≠ x3) (e12 : x1 ≠ x2) (e13 : x1 ≠ x3) (e23 : x2 ≠ x3)
    (h0 : x0 ≠ .xmm12 ∧ x0 ≠ .xmm13 ∧ x0 ≠ .xmm14 ∧ x0 ≠ .xmm15)
    (h1 : x1 ≠ .xmm12 ∧ x1 ≠ .xmm13 ∧ x1 ≠ .xmm14 ∧ x1 ≠ .xmm15)
    (h2 : x2 ≠ .xmm12 ∧ x2 ≠ .xmm13 ∧ x2 ≠ .xmm14 ∧ x2 ≠ .xmm15)
    (h3 : x3 ≠ .xmm12 ∧ x3 ≠ .xmm13 ∧ x3 ≠ .xmm14 ∧ x3 ≠ .xmm15) :
    OutOk xorRow8 (Eff8 a buf) [dR3 a, bR buf 0, bR buf 1] g w row x0 x1 x2 x3 := by
  intro B s hB hg hws
  refine WP.block_append (WP.mono (transpose_ok e01 e02 e03 e12 e13 e23 h0 h1 h2 h3)
    fun s₁ ⟨lt, lo, g₁, m₁, r₁, w₁⟩ => ?_)
  refine WP.mono (xorRow8_ok hrow (a := a) (buf := buf) ⟨h0.1, h0.2.1⟩ ⟨h1.1, h1.2.1⟩ ⟨h2.1, h2.2.1⟩
    ⟨h3.1, h3.2.1⟩ (by rw [g₁, hg]; exact hrsi) (by rw [g₁, hg]; exact hrcx) (by rw [w₁, hws]; exact hw)
    (by rw [w₁, hws]; exact hb) hd) fun s₂ ⟨d₂, b₂, f₂, l₂, g₂, r₂, w₂⟩ => ?_
  rw [m₁] at d₂ b₂ f₂
  -- Row `row` of block `4 l + q`, from lane `l` of the `q`th register.
  have blk : ∀ l q, l < 2 → q < 4 → ∀ k, k % 64 / 16 = row →
      byte (s₁.lane ([x0, x1, x2, x3].getD q .xmm0) l) (k % 16) =
        (serialize (B (4 * l + q))).getD (k % 64) 0 := by
    intro l q hl hq k hr
    rw [serialize_row _ hrow hr]
    obtain ⟨b0, b1, b2, b3⟩ := hB l q hl hq hrow
    rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl
    · rw [List.getD_cons_zero, (lt l).1, b0, b1, b2, b3]
    · rw [List.getD_cons_succ, List.getD_cons_zero, (lt l).2.1, b0, b1, b2, b3]
    · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero, (lt l).2.2.1, b0, b1, b2, b3]
    · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero,
        (lt l).2.2.2, b0, b1, b2, b3]
  refine ⟨⟨fun k hk => ?_, fun j hj k hk => ?_⟩, f₂, fun r l n0 n1 n2 n3 n12 n13 n14 n15 => ?_,
    g₂.trans g₁, r₂.trans r₁, w₂.trans w₁⟩
  · rw [d₂ k hk]
    by_cases hr : k % 64 / 16 = row
    · rw [ite_eq_left hr, ite_eq_left hr, blk _ _ (by omega) (by omega) k hr,
        show 4 * (k / 64 / 4) + k / 64 % 4 = k / 64 by omega]
    · rw [ite_eq_right hr, ite_eq_right hr]
  · rw [b₂ j hj k hk]
    by_cases hr : k / 16 = row
    · have e := blk 1 (2 + j) (by decide) (by omega) k (by rw [Nat.mod_eq_of_lt hk]; exact hr)
      rw [Nat.mod_eq_of_lt hk, show 4 * 1 + (2 + j) = 6 + j by omega] at e
      rw [ite_eq_left hr, ite_eq_left hr, ← e]
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> rfl
    · rw [ite_eq_right hr, ite_eq_right hr]
  · rw [l₂ r l n12 n13, lo r l n0 n1 n2 n3 n12 n13 n14 n15]

/-! ## Moving blocks 6 and 7 -/

/-- Copy `buf[src, src + 32)` to `buf[dst, dst + 32)`, through `ymm12`. -/
def cp (src dst : Nat) : List Instr :=
  [.vmovdquLoad .l256 .xmm12 (at_ .rcx src), .vmovdquStore .l256 (at_ .rcx dst) .xmm12]

theorem halves (v : BitVec 256) : v.extractLsb' 128 128 ++ v.extractLsb' 0 128 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 128
  · simp [h]
  · simp [h, show i - 128 < 128 by omega, show 128 + (i - 128) = i by omega]

theorem move67_eq : move67 = cp 128 0 ++ (cp 160 32 ++ (cp 224 64 ++ cp 256 96)) := rfl

theorem cp_ok {src dst : Nat} (hs : src + 32 ≤ 320) (hd : dst + 32 ≤ 320) {buf : Addr} {s : State}
    (hrcx : s.gpr .rcx = buf) (hb : bufR buf ∈ s.wr) :
    WP isa (.block (cp src dst)) s fun s' =>
      (∀ k < 32, s'.mem (buf + BitVec.ofNat 64 (dst + k)) = s.mem (buf + BitVec.ofNat 64 (src + k))) ∧
      Frame [⟨buf + BitVec.ofNat 64 dst, 32⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i1 := in_buf (rs := s.rd) hb (d := src) (n := 32) hs
  have o1 := out_buf hb (d := dst) (n := 32) hd
  apply WP.of_runBlock
  simp only [cp, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hrcx, State.load256, i1,
    State.store256_eq, o1, ite_true, Option.map_some, Option.some.injEq, exists_eq_left', State.setV_gpr,
    State.setV_mem, State.setV_rd, State.setV_wr, State.setMem_gpr, State.setMem_mem, State.setMem_rd,
    State.setMem_wr, State.ymm_eq, State.lane_setV256, ite_true, Nat.reduceEqDiff, ite_false, halves]
  refine ⟨fun k hk => ?_, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _),
    trivial, trivial, trivial⟩
  rw [← add_ofNat, writeW_byte _ _ _ (by lit_omega) (by lit_omega), byte_readW _ _ (by lit_omega), add_ofNat]

theorem nc {buf : Addr} {x d : Nat} (hx : x < 320) (hd : d + 32 ≤ 320) (h : x < d ∨ d + 32 ≤ x) :
    ¬ (⟨buf + BitVec.ofNat 64 d, 32⟩ : Region).Contains (buf + BitVec.ofNat 64 x) 1 := by
  simp only [Region.Contains]
  rw [Offset.sub_toNat' buf (by lit_omega) (by lit_omega)]
  split <;> omega

/-- `move67`: blocks 6 and 7 (`bR`) to `buf[0, 128)`. -/
theorem move67_ok {buf : Addr} {s : State} (hrcx : s.gpr .rcx = buf) (hb : bufR buf ∈ s.wr) :
    WP isa (.block move67) s fun s' =>
      (∀ j < 2, ∀ k < 64, s'.mem (buf + BitVec.ofNat 64 (64 * j + k)) =
        s.mem (buf + BitVec.ofNat 64 (b67Off j) + BitVec.ofNat 64 k)) ∧
      Frame [slotsR buf] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [move67_eq]
  refine WP.block_append (WP.mono (cp_ok (src := 128) (dst := 0) (by decide) (by decide) hrcx hb)
    fun s₁ ⟨c₁, f₁, g₁, r₁, w₁⟩ => ?_)
  refine WP.block_append (WP.mono (cp_ok (src := 160) (dst := 32) (buf := buf) (by decide) (by decide)
    (by rw [g₁]; exact hrcx) (by rw [w₁]; exact hb)) fun s₂ ⟨c₂, f₂, g₂, r₂, w₂⟩ => ?_)
  refine WP.block_append (WP.mono (cp_ok (src := 224) (dst := 64) (buf := buf) (by decide) (by decide)
    (by rw [g₂, g₁]; exact hrcx) (by rw [w₂, w₁]; exact hb)) fun s₃ ⟨c₃, f₃, g₃, r₃, w₃⟩ => ?_)
  refine WP.mono (cp_ok (src := 256) (dst := 96) (buf := buf) (by decide) (by decide)
    (by rw [g₃, g₂, g₁]; exact hrcx) (by rw [w₃, w₂, w₁]; exact hb)) fun s₄ ⟨c₄, f₄, g₄, r₄, w₄⟩ => ?_
  -- A byte outside the copies' destinations, or before one, is unchanged by it.
  have u : ∀ {m m' : Mem} {d : Nat}, Frame [⟨buf + BitVec.ofNat 64 d, 32⟩] m m' → d + 32 ≤ 320 →
      ∀ x < 320, (x < d ∨ d + 32 ≤ x) → m' (buf + BitVec.ofNat 64 x) = m (buf + BitVec.ofNat 64 x) :=
    fun f hd x hx h => f _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact nc hx hd h
  have hs₂ : ∀ x, 128 ≤ x → x < 320 → s₂.mem (buf + BitVec.ofNat 64 x) = s.mem (buf + BitVec.ofNat 64 x) :=
    fun x h₁ h₂ => by rw [u f₂ (by decide) x h₂ (by omega), u f₁ (by decide) x h₂ (by omega)]
  have hs₃ : ∀ x, 128 ≤ x → x < 320 → s₃.mem (buf + BitVec.ofNat 64 x) = s.mem (buf + BitVec.ofNat 64 x) :=
    fun x h₁ h₂ => by rw [u f₃ (by decide) x h₂ (by omega), hs₂ x h₁ h₂]
  refine ⟨fun j hj k hk => ?_, ?_, by rw [g₄, g₃, g₂, g₁], by rw [r₄, r₃, r₂, r₁], by rw [w₄, w₃, w₂, w₁]⟩
  · rw [add_ofNat]
    rcases (by omega : (64 * j + k) / 32 = 0 ∨ (64 * j + k) / 32 = 1 ∨ (64 * j + k) / 32 = 2 ∨
      (64 * j + k) / 32 = 3) with h | h | h | h
    · obtain rfl : j = 0 := by omega
      have e := c₁ k (by omega)
      rw [Nat.zero_add] at e
      rw [Nat.mul_zero, Nat.zero_add, u f₄ (by decide) k (by omega) (by omega),
        u f₃ (by decide) k (by omega) (by omega), u f₂ (by decide) k (by omega) (by omega), e]
      rfl
    · obtain rfl : j = 0 := by omega
      have e := c₂ (k - 32) (by omega)
      rw [show 32 + (k - 32) = k by omega, show 160 + (k - 32) = 128 + k by omega] at e
      rw [Nat.mul_zero, Nat.zero_add, u f₄ (by decide) k (by omega) (by omega),
        u f₃ (by decide) k (by omega) (by omega), e, u f₁ (by decide) (128 + k) (by omega) (by omega)]
      rfl
    · obtain rfl : j = 1 := by omega
      have e := c₃ k (by omega)
      rw [show 64 + k = 64 * 1 + k by omega] at e
      rw [u f₄ (by decide) (64 * 1 + k) (by omega) (by omega), e, hs₂ _ (by omega) (by omega)]
      rfl
    · obtain rfl : j = 1 := by omega
      have e := c₄ (k - 32) (by omega)
      rw [show 96 + (k - 32) = 64 * 1 + k by omega, show 256 + (k - 32) = 224 + k by omega] at e
      rw [e, hs₃ _ (by omega) (by omega)]
      rfl
  · have sub : ∀ d, d + 32 ≤ 128 → ∀ r ∈ [(⟨buf + BitVec.ofNat 64 d, 32⟩ : Region)],
        ∃ r' ∈ [slotsR buf], Region.Sub r r' := fun d hd r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨slotsR buf, by simp, Offset.sub_base buf hd⟩
    exact (((f₁.sub (sub 0 (by decide))).trans (f₂.sub (sub 32 (by decide)))).trans
      (f₃.sub (sub 64 (by decide)))).trans (f₄.sub (sub 96 (by decide)))

/-! ## The whole pass -/

theorem adv8_ok {s₀ : State} {p : Nat} (hge : 384 ≤ eL s₀ - p) {s : State}
    (hrsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 p) (hrdx : s.gpr .rdx = BitVec.ofNat 64 (eL s₀ - p)) :
    WP isa (.block ([.mov .r9 (.reg .rcx), .alu .add .rsi (.imm 384), .alu .sub .rdx (.imm 384)] : List Instr))
      s fun s' =>
      s'.gpr .rsi = edp s₀ + BitVec.ofNat 64 (p + 384) ∧
      s'.gpr .rdx = BitVec.ofNat 64 (eL s₀ - (p + 384)) ∧ s'.gpr .r9 = s.gpr .rcx ∧
      (∀ r, r ≠ .r9 → r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have hL := eL_lt s₀
  have se : BitVec.signExtend 64 (384 : BitVec 32) = 384 := by decide
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', se]
  refine ⟨?_, ?_, trivial, fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃], trivial, trivial, trivial⟩
  · rw [hrsi]; exact Offset.add_add _ _ _
  · rw [hrdx, show (384 : BitVec 64) = BitVec.ofNat 64 384 from rfl, Offset.ofNat_sub_ofNat (by omega),
      show eL s₀ - p - 384 = eL s₀ - (p + 384) by omega]

theorem last8_eq : last8 = .seq (.block setup) (.seq (rounds 10) (.seq
    (.block (finishWith xorRow8 ++ (move67 ++
      ([.mov .r9 (.reg .rcx), .alu .add .rsi (.imm 384), .alu .sub .rdx (.imm 384)] : List Instr))))
    (.seq Impl.ChaCha20.X86_64.Avx2Tail.fromBuf (.block [.vop .vzeroupper, .mov .rsi (.reg .r9)])))) := by
  simp only [last8, List.append_assoc]

/-- The last 385 to 511 bytes, after `t` chunks. -/
theorem last8_ok {s₀ : State} (hp : APre s₀) {t : Nat} (hge : 385 ≤ eL s₀ - 512 * t)
    (hlt : eL s₀ - 512 * t < 512) {s : State} (h : LInv s₀ t s) :
    WP isa last8 s fun s' =>
      (gprPreserved s₀ s' ∧ xorAvx2X86_64.post s₀ s') ∧ s'.gpr .rsi = s₀.gpr .rcx := by
  have hL := eL_lt s₀
  have hw : 512 * t + 384 ≤ eL s₀ := by omega
  have hst : stR (est s₀) ∈ s.wr := by rw [h.wr]; exact hp.w_st
  have hb : bufR (ebp s₀) ∈ s.wr := by rw [h.wr]; exact hp.w_b
  have hd : edR s₀ ∈ s.wr := by rw [h.wr]; exact hp.w_d
  have sw : Region.Sub (dR3 (edp s₀ + BitVec.ofNat 64 (512 * t))) (edR s₀) := Avx512Tail.win_sub hw
  have dsd := hp.st_d.sub_right sw
  have dbd := hp.d_b.symm.sub_right sw
  have dss : (stR (est s₀)).Disjoint (slotsR (ebp s₀)) := hp.st_b.sub_right (slotsR_sub _)
  have hsl : ∀ r ∈ [slotsR (ebp s₀)], (hiR (ebp s₀)).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hiR_slots _
  rw [last8_eq]
  refine WP.seq (WP.mono (setup_ok h.rdi h.rcx hst hb h.consts)
    fun s₁ ⟨hh, h15, g₁, rd₁, wr₁, y₁, y₂, m₁⟩ => ?_)
  have c₁ : Consts s₁.mem (ebp s₀) := by rw [m₁]; exact h.consts.w2 (by decide) y₁ y₂
  have F₁ : Frame [slotsR (ebp s₀)] s.mem s₁.mem := by
    rw [m₁]; exact W2_frame _ (by decide) y₁ y₂ (Frame.refl _ _)
  refine WP.seq (WP.mono (rounds_ok hh h15 (by rw [g₁]; exact h.rcx) (by rw [wr₁]; exact hb) c₁.m8 10)
    fun s₂ hr => ?_)
  have F₂ := F₁.trans hr.frame
  have g₂ : s₂.gpr = s.gpr := hr.gpr.trans g₁
  have wr₂ : s₂.wr = s.wr := hr.wr.trans wr₁
  have hS₂ : stateAt s₂.mem (est s₀) = stateAt s.mem (est s₀) :=
    Xor.stateAt_frame F₂ (by simpa using dss)
  have hS : stateAt s.mem (est s₀) = ctr (Avx2.S0 s₀) (512 * t / 64) := by
    rw [h.cnt, show 512 * t / 64 = 8 * t by omega]
  -- The regions the output writes.
  have hR : ∀ r ∈ [dR3 (edp s₀ + BitVec.ofNat 64 (512 * t)), bR (ebp s₀) 0, bR (ebp s₀) 1],
      (stR (est s₀)).Disjoint r ∧ (slotsR (ebp s₀)).Disjoint r ∧ (incR (ebp s₀)).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨dsd, dbd.sub_left (slotsR_sub _), dbd.sub_left (Offset.sub_base _ (by lit_omega))⟩
    · exact ⟨hp.st_b.sub_right (Offset.sub_base _ (by decide)),
        (Offset.disjoint_base _ (by decide) (by decide)).symm, Offset.disjoint _ (by decide) (by decide) (by decide)⟩
    · exact ⟨hp.st_b.sub_right (Offset.sub_base _ (by decide)),
        (Offset.disjoint_base _ (by decide) (by decide)).symm, Offset.disjoint _ (by decide) (by decide) (by decide)⟩
  have hw₂ : DWin3 s₂.wr (edp s₀ + BitVec.ofNat 64 (512 * t)) := by
    intro off n hn
    refine ⟨edR s₀, by rw [wr₂]; exact hd, ?_⟩
    rw [Offset.add_add]; exact Offset.contains_base _ (by lit_omega) (by lit_omega)
  have o : ∀ {row : Nat} {x0 x1 x2 x3 : XReg}, row < 4 → x0 ≠ x1 → x0 ≠ x2 → x0 ≠ x3 → x1 ≠ x2 →
      x1 ≠ x3 → x2 ≠ x3 → (x0 ≠ .xmm12 ∧ x0 ≠ .xmm13 ∧ x0 ≠ .xmm14 ∧ x0 ≠ .xmm15) →
      (x1 ≠ .xmm12 ∧ x1 ≠ .xmm13 ∧ x1 ≠ .xmm14 ∧ x1 ≠ .xmm15) →
      (x2 ≠ .xmm12 ∧ x2 ≠ .xmm13 ∧ x2 ≠ .xmm14 ∧ x2 ≠ .xmm15) →
      (x3 ≠ .xmm12 ∧ x3 ≠ .xmm13 ∧ x3 ≠ .xmm14 ∧ x3 ≠ .xmm15) →
      OutOk xorRow8 (Eff8 (edp s₀ + BitVec.ofNat 64 (512 * t)) (ebp s₀))
        [dR3 (edp s₀ + BitVec.ofNat 64 (512 * t)), bR (ebp s₀) 0, bR (ebp s₀) 1] s₂.gpr s₂.wr row x0 x1 x2 x3 :=
    fun hrow => xorRow8_out (by rw [g₂]; exact h.rsi) (by rw [g₂]; exact h.rcx) hw₂ (by rw [wr₂]; exact hb)
      dbd.symm hrow
  refine WP.seq (WP.block_append (WP.mono (finishWith_ok (out := xorRow8) hr.holds (st := est s₀)
    (by rw [g₂]; exact h.rdi) (by rw [g₂]; exact h.rcx) (by rw [wr₂]; exact hst) (by rw [wr₂]; exact hb)
    (incs_frame c₁.inc hr.frame hsl) hp.st_b hR
    (o (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    (o (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    (o (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    (o (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)))
    fun s₃ ⟨n₀, n₁, n₂, n₃, f₀, e₀, e₁, e₃, e₂, F₃, g₃, rd₃, wr₃⟩ => ?_))
  rw [hS₂] at e₀ e₁ e₂ e₃
  -- The keystream of block `j` of the eight.
  have ks : ∀ k, 512 * t ≤ k → k < eL s₀ → (KS s₀).getD k 0 =
      (serialize (plus (fun j => Nat.repeat Spec.ChaCha20.innerBlock 10 (ctr (stateAt s.mem (est s₀)) j))
        (stateAt s.mem (est s₀)) ((k - 512 * t) / 64))).getD ((k - 512 * t) % 64) 0 := by
    intro k h₁ h₂
    rw [ks_at ⟨8 * t, by omega⟩ h₁ h₂, hS]
  -- The output: the first six blocks XORed into the data, the last two in `buf`.
  have D₃ : ∀ k < 384, s₃.mem (edp s₀ + BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 k) =
      s.mem (edp s₀ + BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 k) ^^^ (KS s₀).getD (512 * t + k) 0 := by
    intro k hk
    have z : n₀ (edp s₀ + BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 k) =
        s₂.mem (edp s₀ + BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 k) :=
      f₀.bytes (R := dR3 _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dbd.sub_left (slotsR_sub _)).symm)
        (show 384 ≤ 2 ^ 64 by decide) hk
    have y : s₂.mem (edp s₀ + BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 k) =
        s.mem (edp s₀ + BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 k) :=
      F₂.bytes (R := dR3 _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dbd.sub_left (slotsR_sub _)).symm)
        (show 384 ≤ 2 ^ 64 by decide) hk
    rw [e₂.1 k hk, e₃.1 k hk, e₁.1 k hk, e₀.1 k hk, z, y, ks _ (by omega) (by omega),
      Nat.add_sub_cancel_left]
    rcases (by omega : k % 64 / 16 = 0 ∨ k % 64 / 16 = 1 ∨ k % 64 / 16 = 2 ∨ k % 64 / 16 = 3)
      with h | h | h | h <;> simp only [h, Nat.reduceEqDiff, ite_true, ite_false]
  have K₃ : ∀ j < 2, ∀ k < 64, 512 * t + 384 + (64 * j + k) < eL s₀ →
      s₃.mem (ebp s₀ + BitVec.ofNat 64 (b67Off j) + BitVec.ofNat 64 k) =
        (KS s₀).getD (512 * t + 384 + (64 * j + k)) 0 := by
    intro j hj k hk hL
    rw [e₂.2 j hj k hk, e₃.2 j hj k hk, e₁.2 j hj k hk, e₀.2 j hj k hk, ks _ (by omega) (by omega),
      show (512 * t + 384 + (64 * j + k) - 512 * t) / 64 = 6 + j by omega,
      show (512 * t + 384 + (64 * j + k) - 512 * t) % 64 = k by omega]
    rcases (by omega : k / 16 = 0 ∨ k / 16 = 1 ∨ k / 16 = 2 ∨ k / 16 = 3)
      with h | h | h | h <;> simp only [h, Nat.reduceEqDiff, ite_true, ite_false]
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  refine WP.block_append (WP.mono (move67_ok (buf := ebp s₀) (by rw [g₃']; exact h.rcx)
    (by rw [wr₃, wr₂]; exact hb)) fun s₄ ⟨mv, F₄, g₄, rd₄, wr₄⟩ => ?_)
  have g₄' : s₄.gpr = s.gpr := g₄.trans g₃'
  refine WP.mono (adv8_ok (s₀ := s₀) (p := 512 * t) (by omega) (by rw [g₄']; exact h.rsi)
    (by rw [g₄']; exact h.rdx)) fun s₅ ⟨a₁, a₂, a₃, a₄, m₅, rd₅, wr₅⟩ => ?_
  have nb : ∀ k < eL s₀, ∀ (r : Region), Region.Sub r (bufR (ebp s₀)) →
      ¬ r.Contains (edp s₀ + BitVec.ofNat 64 k) 1 := fun k hk r hs hc => hp.d_b _ (in_dR hk) (hs _ hc)
  have F₃' : Frame [slotsR (ebp s₀), dR3 (edp s₀ + BitVec.ofNat 64 (512 * t)), bR (ebp s₀) 0, bR (ebp s₀) 1]
      s.mem s₃.mem := (F₂.mono (by simp)).trans F₃
  have DS := data_step (s₀ := s₀) (p := 512 * t) (n := 384) F₃' (fun r hr k hk ho => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact nb k hk _ (slotsR_sub _)
    · exact not_win (by omega) hk ho
    · exact nb k hk _ (Offset.sub_base _ (by decide))
    · exact nb k hk _ (Offset.sub_base _ (by decide))) D₃ h.data
  have M₄ : ∀ k < eL s₀, s₅.mem (edp s₀ + BitVec.ofNat 64 k) = s₃.mem (edp s₀ + BitVec.ofNat 64 k) :=
    fun k hk => by
      rw [m₅]; exact F₄ _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact nb k hk _ (slotsR_sub _)
  refine WP.seq (WP.mono (fromBuf_ok hp (p := 512 * t + 384) (n := eL s₀ - (512 * t + 384)) (by omega)
    (by omega) a₁ (by rw [a₃, g₄']; exact h.rcx) a₂ (by rw [rd₅, rd₄, rd₃, hr.rd, rd₁, h.rd])
    (by rw [wr₅, wr₄, wr₃, wr₂, h.wr]) (fun r hr => ?_) (fun k hk => ?_) (fun k hk => ?_)
    (fun k hk => ?_) ?_) fun s₆ d => fin_ok (d.fin hp))
  · obtain ⟨_, b, c⟩ := calleeSaved_ne hr
    rw [a₄ r (r9_not_calleeSaved hr).1 b c, g₄']; exact h.keep r hr
  · rw [M₄ k (by omega), DS k (by omega), ite_eq_left hk]
  · rw [add_ofNat, M₄ _ (by omega), DS _ (by omega), ite_eq_right (by omega)]
  · have e := Nat.div_add_mod k 64
    rw [m₅, ← e, mv (k / 64) (by omega) (k % 64) (by omega), K₃ _ (by omega) _ (by omega) (by omega)]
  · rw [m₅]
    refine h.frame.trans ((F₃'.trans (F₄.mono (by simp))).sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨bufR (ebp s₀), by simp, slotsR_sub _⟩
    · exact ⟨edR s₀, by simp, sw⟩
    · exact ⟨bufR (ebp s₀), by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨bufR (ebp s₀), by simp, Offset.sub_base _ (by decide)⟩

end VG.Proof.ChaCha20.X86_64.Avx2
