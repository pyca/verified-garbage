import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemLoop
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.ZFrameBlock

/-!
# The setup of the blocks after the last group

`remSetup_ok`: `StitchZH.remSetup`, from `r9 = 16 + r`, stores the counter
after the `r` blocks (`r` added to the first counter, `paddd_rep`), and
points `rax` at the powers of the `r` blocks, `16 (16 - r)` bytes into the
working space, with `r10 = 16 r`.
-/

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.StitchZH (remSetup)
open VG.Proof.Aes.X86_64.AesNi (one paddd_one)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt inc32)

theorem dword_ofNat {n : Nat} (hn : n < 2 ^ 32) {k : Nat} (hk : k < 4) :
    dword ((0 : BitVec 64) ++ BitVec.ofNat 64 n) k = if k = 0 then BitVec.ofNat 32 n else 0 := by
  apply BitVec.eq_of_toNat_eq
  have z : (0 : BitVec 64).toNat = 0 := rfl
  have z32 : (0 : BitVec 32).toNat = 0 := rfl
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  simp only [dword, BitVec.extractLsb'_toNat, BitVec.toNat_append, BitVec.toNat_ofNat, ↓reduceIte, z, z32,
    Nat.shiftRight_eq_div_pow, Nat.reduceEqDiff, Nat.zero_shiftLeft, Nat.zero_or, Nat.reduceMul,
    Nat.reducePow] <;>
  omega

/-- `r` added to doubleword 0: `r` steps of `inc₃₂`. -/
theorem paddd_rep (c : Block) : ∀ r, r < 2 ^ 32 →
    XBinOp.eval .paddd c ((0 : BitVec 64) ++ BitVec.ofNat 64 r) = Nat.repeat inc32 r c
  | 0, _ => by
    apply ext_dword <;> rw [dword_paddd _ _ (by decide), dword_ofNat (by decide) (by decide)] <;>
      simp only [↓reduceIte, Nat.reduceEqDiff, BitVec.ofNat_eq_ofNat, BitVec.add_zero] <;> rfl
  | r + 1, hr => by
    rw [Nat.repeat, ← paddd_rep c r (by omega), ← paddd_one]
    have o : ∀ k < 4, dword one k = if k = 0 then 1 else 0 := fun k hk => by
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> decide
    apply ext_dword <;>
    rw [dword_paddd _ _ (by decide), dword_paddd _ _ (by decide), dword_paddd _ _ (by decide),
      dword_ofNat hr (by decide), dword_ofNat (by omega) (by decide), o _ (by decide), BitVec.add_assoc] <;>
    simp only [↓reduceIte, Nat.reduceEqDiff]
    all_goals first | (rw [BitVec.ofNat_add]; rfl) | rfl

/-- The counter after `r` more blocks, byte-reversed, into `xmm13`. -/
theorem remCtr_ok (s : State) {r : Nat} (hr : r < 2 ^ 32) (h10 : s.gpr .r10 = BitVec.ofNat 64 r)
    (h0 : s.lane .xmm0 0 = revMask) :
    WP isa (.block [.vop (.vmovq .xmm13 .r10), .vop (.vbin .vpaddd .l128 .xmm13 .xmm14 .xmm13),
      .vop (.vbin .vpshufb .l128 .xmm13 .xmm13 .xmm0)]) s fun s' =>
      s'.lane .xmm13 0 = XBinOp.eval .pshufb (Nat.repeat inc32 r (s.lane .xmm14 0)) revMask ∧ ZFrame [.xmm13] s s' := by
  refine WP.zframe (by decide) ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  simp only [VOp.exec, VBinOp.sse, State.lane_setV128, ↓reduceIte, reduceCtorEq, h10, h0, paddd_rep _ r hr]

/-- A 16-byte store of `x` to `[b]`. -/
theorem store16_ok (x : XReg) (b : Reg) (s : State) (hin : InRegions s.wr (s.gpr b + BitVec.ofInt 64 ((0 : Nat) : Int)) 16) :
    WP isa (.block [.vmovdquStore .l128 (at_ b 0) x]) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr b + BitVec.ofInt 64 ((0 : Nat) : Int)) (s.xmm x) ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r l, s'.zlane r l = s.zlane r l) := by
  rw [WP.block_cons_iff]
  refine ⟨s.setMem (s.mem.writeW (s.gpr b + BitVec.ofInt 64 ((0 : Nat) : Int)) (s.xmm x)),
    by simp only [isa, exec, State.store128_eq, VG.Proof.Gcm.X86_64.Pclmul.ea_at, hin, ite_true],
    WP.block_nil ⟨by simp, by simp, by simp, by simp, fun _ _ => by cases s; rfl⟩⟩

/-- `r10 = r9 - 16`. -/
theorem remAlu1_ok (s : State) {r : Nat} (h15 : r ≤ 15) (h9 : s.gpr .r9 = BitVec.ofNat 64 (16 + r)) :
    WP isa (.block [.mov .r10 (.reg .r9), .alu .sub .r10 (.imm 16)]) s fun s' =>
      s'.gpr .r10 = BitVec.ofNat 64 r ∧ (∀ q, q ≠ .r10 → s'.gpr q = s.gpr q) ∧
      (∀ x l, s'.zlane x l = s.zlane x l) ∧ (∀ x l, s'.lane x l = s.lane x l) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have sr : BitVec.ofNat 64 (16 + r) - 16 = BitVec.ofNat 64 r := by
    rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      VG.Proof.Gcm.X86_64.Pclmul.ofNat_sub_ofNat (by omega) (by omega)]
    congr 1; omega
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags,
    State.setFlags, isa, State.setReg, e16, h9, sr, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  exact ⟨trivial, fun q hq => by simp only [hq, ↓reduceIte], fun _ _ => rfl, fun _ _ => rfl, trivial, trivial,
    trivial⟩

/-- `r10 = 16 r`, `rax = r11 + 256 - 16 r`. -/
theorem remAlu2_ok (s : State) {r : Nat} (h15 : r ≤ 15) (h10 : s.gpr .r10 = BitVec.ofNat 64 r) :
    WP isa (.block [.alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
      .alu .add .r10 (.reg .r10), .mov .rax (.reg .r11), .alu .add .rax (.imm 256), .alu .sub .rax (.reg .r10)])
      s fun s' =>
      s'.gpr .r10 = BitVec.ofNat 64 (16 * r) ∧ s'.gpr .rax = s.gpr .r11 + BitVec.ofNat 64 (256 - 16 * r) ∧
      (∀ q, q ≠ .r10 → q ≠ .rax → s'.gpr q = s.gpr q) ∧
      (∀ x l, s'.zlane x l = s.zlane x l) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  have x16 : BitVec.ofNat 64 r + BitVec.ofNat 64 r + (BitVec.ofNat 64 r + BitVec.ofNat 64 r) +
      (BitVec.ofNat 64 r + BitVec.ofNat 64 r + (BitVec.ofNat 64 r + BitVec.ofNat 64 r)) +
      (BitVec.ofNat 64 r + BitVec.ofNat 64 r + (BitVec.ofNat 64 r + BitVec.ofNat 64 r) +
      (BitVec.ofNat 64 r + BitVec.ofNat 64 r + (BitVec.ofNat 64 r + BitVec.ofNat 64 r))) =
      BitVec.ofNat 64 (16 * r) := by
    simp only [← BitVec.ofNat_add]; congr 1; omega
  have wa : s.gpr .r11 + 256 - BitVec.ofNat 64 (16 * r) = s.gpr .r11 + BitVec.ofNat 64 (256 - 16 * r) := by
    rw [show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      ← BitVec.sub_eq_add_neg, VG.Proof.Gcm.X86_64.Pclmul.ofNat_sub_ofNat (by omega) (by omega)]
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags,
    State.setFlags, isa, State.setReg, e256, h10, x16, wa, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun q h1 h2 => by simp only [h1, h2, ↓reduceIte], fun _ _ => rfl, trivial, trivial,
    trivial⟩

/-- The setup of the `r` blocks, `r9 = 16 + r`. -/
theorem remSetup_ok (s : State) {r : Nat} (h1 : 1 ≤ r) (h15 : r ≤ 15)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (16 + r)) (h0 : s.lane .xmm0 0 = revMask)
    (hin : InRegions s.wr (s.gpr .rax + BitVec.ofInt 64 ((0 : Nat) : Int)) 16) :
    WP isa (.block remSetup) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rax + BitVec.ofInt 64 ((0 : Nat) : Int))
        (XBinOp.eval .pshufb (Nat.repeat inc32 r (s.lane .xmm14 0)) revMask) ∧
      s'.gpr .r10 = BitVec.ofNat 64 (16 * r) ∧ s'.gpr .rax = s.gpr .r11 + BitVec.ofNat 64 (256 - 16 * r) ∧
      (∀ q, q ≠ .r10 → q ≠ .rax → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ x, x ≠ .xmm13 → ∀ l < 4, s'.zlane x l = s.zlane x l) := by
  rw [remSetup, show ([.mov .r10 (.reg .r9), .alu .sub .r10 (.imm 16), .vop (.vmovq .xmm13 .r10),
      .vop (.vbin .vpaddd .l128 .xmm13 .xmm14 .xmm13), .vop (.vbin .vpshufb .l128 .xmm13 .xmm13 .xmm0),
      .vmovdquStore .l128 (at_ .rax 0) .xmm13,
      .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
      .mov .rax (.reg .r11), .alu .add .rax (.imm 256), .alu .sub .rax (.reg .r10)] : List Instr) =
    [.mov .r10 (.reg .r9), .alu .sub .r10 (.imm 16)] ++ ([.vop (.vmovq .xmm13 .r10),
      .vop (.vbin .vpaddd .l128 .xmm13 .xmm14 .xmm13), .vop (.vbin .vpshufb .l128 .xmm13 .xmm13 .xmm0)] ++
      ([.vmovdquStore .l128 (at_ .rax 0) .xmm13] ++
      [.alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
      .mov .rax (.reg .r11), .alu .add .rax (.imm 256), .alu .sub .rax (.reg .r10)])) from rfl]
  rw [WP.block_append_iff]
  refine WP.mono (remAlu1_ok s h15 h9) fun s₁ ⟨a₁, g₁, z₁, l₁, m₁, rd₁, wr₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (remCtr_ok s₁ (r := r) (by omega) a₁ (by rw [l₁]; exact h0)) fun s₂ ⟨c₂, f₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (store16_ok .xmm13 .rax s₂ (by
      rw [f₂.gpr, f₂.wr, g₁ _ (by decide), wr₁]; exact hin)) fun s₃ ⟨m₃, g₃, rd₃, wr₃, z₃⟩ => ?_
  refine WP.mono (remAlu2_ok s₃ h15 (by rw [g₃, f₂.gpr, a₁])) fun s' ⟨a', ax', g', z', m', rd', wr'⟩ =>
    ⟨?_, a', ?_, fun q h1 h2 => ?_, by rw [rd', rd₃, f₂.rd, rd₁], by rw [wr', wr₃, f₂.wr, wr₁],
      fun x hx l hl => ?_⟩
  · rw [m', m₃, f₂.gpr, f₂.mem, m₁, g₁ _ (by decide), show s₂.xmm .xmm13 = s₂.lane .xmm13 0 from rfl, c₂, l₁]
  · rw [ax', g₃, f₂.gpr, g₁ _ (by decide)]
  · rw [g' q h1 h2, g₃, f₂.gpr, g₁ q h1]
  · rw [z', z₃, f₂.zlane x (by simp [hx]) l hl, z₁]

end VG.Proof.Gcm.X86_64.StitchZH
