module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Copy
import VerifiedGarbage.Proof.Framework.Cold
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Framework.X86_64.StraightZ
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Small
import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp

/-!
# AES-GCM's short path on x86-64: the text into `G` by its groups

Untrusted: everything here is checked by Lean. `copyG`
(`Impl.AesGcm.X86_64.Short`) copies the `n` bytes of text at `D` to `G`,
`16 t` bytes in, by whole 64-byte groups of `G` from the one the text starts
in, `P = G + 16 (t - sh)` (`sh = t mod 4`, `c = 16 sh`): the first group is
the bytes of `G` before the text ORed with the text's first `64 - c` bytes,
the last has zeros after the text, which `G` holds there (`copyG_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)

theorem zlane_setFlags (s : State) (a b c d : Option Bool) (x : XReg) (l : Nat) :
    (s.setFlags a b c d).zlane x l = s.zlane x l := rfl

theorem ofNat_and3 {x : Nat} (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 x &&& 3#64 = BitVec.ofNat 64 (x % 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (3#64).toNat = 2 ^ 2 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt (show x % 4 < 2 ^ 64 by omega)]

/-- `W + a - b = W + (a - b)` for `b ≤ a`. -/
theorem add_ofNat_sub_ofNat (W : Addr) {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    W + BitVec.ofNat 64 a - BitVec.ofNat 64 b = W + BitVec.ofNat 64 (a - b) := by
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg, ofNat_sub h ha]

/-- `gShift`: `rax = sh = t mod 4` from `rdi = W + 512 + 16 t` and `r15 = W`, and ZF set if it is 0. -/
theorem gShift_ok (s : State) {W : Addr} {t : Nat} (h15 : s.gpr .r15 = W)
    (hdi : s.gpr .rdi = W + BitVec.ofNat 64 (512 + 16 * t)) (ht : t < 64) :
    WP isa (.block gShift) s fun u =>
      u.gpr .rax = BitVec.ofNat 64 (t % 4) ∧ u.zf = some (decide (t % 4 = 0)) ∧
      (∀ r, r ≠ .rax → u.gpr r = s.gpr r) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      ∀ r l, u.zlane r l = s.zlane r l := by
  have e₁ : W + BitVec.ofNat 64 (512 + 16 * t) - W = BitVec.ofNat 64 (512 + 16 * t) :=
    Offset.add_sub_cancel_left _ _
  have e₂ : BitVec.ofNat 64 (512 + 16 * t) >>> 4 = BitVec.ofNat 64 (32 + t) := by
    rw [shr4 _ (by omega)]; congr 1; omega
  have e₃ : BitVec.ofNat 64 (32 + t) &&& 3#64 = BitVec.ofNat 64 (t % 4) := by
    rw [ofNat_and3 (by omega)]; congr 1; omega
  refine WP.of_runBlock ⟨_, by xrun [gShift, execShift, h15, hdi, e₁, e₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, imm, e₃]
  · rw [zf_setReg, zf_arithFlags, e₃]
    have hx : t % 4 < 4 := Nat.mod_lt _ (by decide)
    generalize t % 4 = x at hx ⊢
    rcases (by omega : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) with rfl | rfl | rfl | rfl <;> decide
  · intro r a; simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, a]
  · simp only [mem_setReg, mem_setFlags, mem_arithFlags]
  · simp only [rd_setReg, rd_setFlags, rd_arithFlags]
  · simp only [wr_setReg, wr_setFlags, wr_arithFlags]
  · intro r l; simp only [zlane_setReg, zlane_arithFlags, zlane_setFlags]

/-- `copyG`'s arguments, from `rdi = W + 512 + 16 t`, `rsi = D`, `rcx = n`
and `rax = t mod 4`: `rdi = P`, `r8 = c`, `rsi = D - c`, `r9 = c + n`. -/
theorem gArgs_ok {W D : Addr} {n t : Nat} (s : State)
    (hdi : s.gpr .rdi = W + BitVec.ofNat 64 (512 + 16 * t)) (hsi : s.gpr .rsi = D)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 n) (hax : s.gpr .rax = BitVec.ofNat 64 (t % 4)) (ht : t < 64) :
    ∃ u, runBlock isa gArgs s = some u ∧
      u.gpr .rdi = W + BitVec.ofNat 64 (512 + 16 * (t - t % 4)) ∧
      u.gpr .r8 = BitVec.ofNat 64 (16 * (t % 4)) ∧
      u.gpr .rsi = D - BitVec.ofNat 64 (16 * (t % 4)) ∧
      u.gpr .r9 = BitVec.ofNat 64 (16 * (t % 4) + n) ∧
      (∀ r, r ≠ .rdi → r ≠ .r8 → r ≠ .rsi → r ≠ .r9 → u.gpr r = s.gpr r) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧
      u.wr = s.wr ∧ ∀ r l, u.zlane r l = s.zlane r l := by
  have e₄ : BitVec.ofNat 64 (t % 4) <<< 4 = BitVec.ofNat 64 (16 * (t % 4)) := by
    rw [shl_ofNat (by omega)]; congr 1; omega
  have e₅ : W + BitVec.ofNat 64 (512 + 16 * t) - BitVec.ofNat 64 (16 * (t % 4)) =
      W + BitVec.ofNat 64 (512 + 16 * (t - t % 4)) := by
    rw [add_ofNat_sub_ofNat W (by omega) (by omega)]; congr 2; omega
  refine ⟨_, by xrun [gArgs, execShift, hdi, hsi, hcx, hax, e₄], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, reduceCtorEq, ite_true, ite_false, hdi, e₄, e₅]
  · simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, e₄]
  · simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, hsi, e₄]
  · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, reduceCtorEq, ite_true, ite_false, hcx, e₄]
    rw [ofNat_add_ofNat, Nat.add_comm]
  · intro r a b c d; simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, a, b, c, d]
  · simp only [mem_setReg, mem_setFlags, mem_arithFlags]
  · simp only [rd_setReg, rd_setFlags, rd_arithFlags]
  · simp only [wr_setReg, wr_setFlags, wr_arithFlags]
  · intro r l; simp only [zlane_setReg, zlane_arithFlags, zlane_setFlags]

/-- The mask of the first group's text bytes: `-1 << c`. -/
abbrev maskHi (c : Nat) : BitVec 64 := BitVec.allOnes 64 <<< c

theorem getLsbD_maskHi {c j : Nat} (hj : j < 64) : (maskHi c).getLsbD j = decide (c ≤ j) := by
  simp only [maskHi, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes]
  by_cases h : c ≤ j <;> simp [h, hj] <;> omega

/-- The bytes `maskHi c` enables are those from `c` on. -/
theorem mem_bOn_maskHi {c j : Nat} : j ∈ State.bOn (maskHi c) ↔ c ≤ j ∧ j < 64 := by
  simp only [State.bOn, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hj, h⟩; rw [getLsbD_maskHi hj] at h; exact ⟨of_decide_eq_true h, hj⟩
  · rintro ⟨h, hj⟩; exact ⟨hj, by rw [getLsbD_maskHi hj]; exact decide_eq_true h⟩

/-- The register after a `vporq` of two registers holds their OR. -/
theorem zmm_vporq (s : State) (d a b : XReg) :
    ((ZOp.zbin .vporq d a b).exec s).zmm d = s.zmm a ||| s.zmm b := by
  rw [StraightZ.zmm_lanes, zlane_zbin _ _ _ _ _ _ (by decide), zlane_zbin _ _ _ _ _ _ (by decide),
    zlane_zbin _ _ _ _ _ _ (by decide), zlane_zbin _ _ _ _ _ _ (by decide), StraightZ.zmm_lanes s a,
    StraightZ.zmm_lanes s b]
  simp only [ite_true, ZBinOp.sse, XBinOp.eval]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_or]
  split <;> split <;> rfl

/-- The bytes `copyG`'s first group stores at `P`: byte `j` of `G` ORed with
byte `j` of the text's view from `S = D - c`, `c ≤ j`, or zero. -/
def headBytes (m : Mem) (S P : Addr) (c : Nat) : List Byte :=
  (List.range 64).map fun j => (if c ≤ j then m (S + BitVec.ofNat 64 j) else 0) ||| m (P + BitVec.ofNat 64 j)

/-- The mask of the first group: `rax = -1 << c`, from `r8 = c`. -/
theorem maskHi_ok (s : State) {c : Nat} (hc : c < 64) (h8 : s.gpr .r8 = BitVec.ofNat 64 c) :
    WP isa (.block [.mov .rcx (.reg .r8), .mov .rax (.imm (BitVec.ofNat 32 0xFFFFFFFF)), .shiftCl .shl .rax]) s
      fun t => t.gpr .rax = maskHi c ∧ (∀ r, r ≠ .rax → r ≠ .rcx → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ ∀ x l, t.zlane x l = s.zlane x l := by
  apply WP.of_runBlock
  refine ⟨_, by xrun [execShiftCl], ?_⟩
  have hk : (BitVec.ofNat 64 c).toNat % 64 = c := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega), Nat.mod_eq_of_lt hc]
  refine ⟨?_, fun r a b => by simp [gpr_setReg, gpr_setFlags, a, b], rfl, rfl, rfl, fun _ _ => rfl⟩
  simp only [gpr_setReg, gpr_setFlags, h8, hk, ite_true, reduceCtorEq, ite_false]
  simp [VarShiftOp.eval, maskHi]

/-- A 64-byte store is a write of its bytes. -/
theorem writeW512_eq (m : Mem) (P : Addr) (V : BitVec 512) :
    m.writeW P V = writeBytes m P ((List.range 64).map fun j => V.extractLsb' (8 * j) 8) := by
  simp only [Mem.writeW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]
  exact write_eq_writeBytes m P 64 V

/-- The first group's store: byte `j` of the masked load ORed with byte `j` of the group. -/
theorem writeW_head (m : Mem) (S P : Addr) {c : Nat} :
    m.writeW P (Mem.readW (fun x => if (maskHi c).getLsbD (x - S).toNat then m x else 0) S 512 ||| m.readW P 512) =
      writeBytes m P (headBytes m S P c) := by
  generalize hf : (fun x => if (maskHi c).getLsbD (x - S).toNat then m x else 0) = f
  rw [writeW512_eq]
  congr 1
  simp only [headBytes]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  rw [BitVec.extractLsb'_or, readW512_byte _ _ hj, readW512_byte _ _ hj, ← hf]
  simp only [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega),
    getLsbD_maskHi hj]
  by_cases h : c ≤ j <;> simp [h]

/-- The first group: the text's first bytes ORed into it and stored, then
`r10 = 64` and `r8 = 64 ⌊E / 64⌋`. -/
theorem gHead_ok (s : State) {S P : Addr} {c E : Nat} (hc : c < 64) (hE : E < 2 ^ 63)
    (hsi : s.gpr .rsi = S) (hdi : s.gpr .rdi = P) (h8 : s.gpr .r8 = BitVec.ofNat 64 c)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 E)
    (r : ∀ j, c ≤ j → j < 64 → InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 j) 1)
    (rP : InRegions (s.rd ++ s.wr) P 64) (wP : InRegions s.wr P 64) :
    WP isa (.block gHead) s fun t =>
      t.mem = writeBytes s.mem P (headBytes s.mem S P c) ∧ t.gpr .r10 = BitVec.ofNat 64 64 ∧
      t.gpr .r8 = BitVec.ofNat 64 (64 * (E / 64)) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      ZKeep [.xmm4, .xmm6] s t := by
  rw [show gHead = ([.mov .rcx (.reg .r8), .mov .rax (.imm (BitVec.ofNat 32 0xFFFFFFFF)), .shiftCl .shl .rax] :
      List Instr) ++ (([.kLoad8 .rax .xmm4 (at_ .rsi 0), .vmovdqu32Load .xmm6 (at_ .rdi 0),
      .zop (.zbin .vporq .xmm4 .xmm4 .xmm6), .vmovdqu32Store (at_ .rdi 0) .xmm4] : List Instr) ++
      [.mov32 .r10 (imm 64), .mov .r8 (.reg .r9), .shift .shr .r8 6, .shift .shl .r8 6]) from rfl]
  refine WP.block_append (WP.mono (maskHi_ok s hc h8) fun t₁ ⟨rax₁, g₁, m₁, rd₁, wr₁, z₁⟩ => ?_)
  refine WP.block_append ?_
  -- The masked load, the group, their OR, stored at `P`.
  have hsi₁ : t₁.gpr .rsi = S := by rw [g₁ _ (by decide) (by decide), hsi]
  have hdi₁ : t₁.gpr .rdi = P := by rw [g₁ _ (by decide) (by decide), hdi]
  have eaS : t₁.ea (at_ .rsi 0) = S := by simp [State.ea, at_, hsi₁]
  have eaP : t₁.ea (at_ .rdi 0) = P := by simp [State.ea, at_, hdi₁]
  generalize hL : Mem.readW (fun x => if (maskHi c).getLsbD (x - S).toNat then t₁.mem x else 0) S 512 = L
  have hl : t₁.loadMasked512B S (maskHi c) = some L := by
    unfold State.loadMasked512B
    rw [ite_eq_left (fun j hj => by rw [mem_bOn_maskHi] at hj; rw [rd₁, wr₁]; exact r j hj.1 hj.2), hL]
  generalize ht₂ : t₁.setZ .xmm4 (L.extractLsb' 0 128) (L.extractLsb' 128 128) (L.extractLsb' 256 128)
    (L.extractLsb' 384 128) = t₂
  have e₁ : exec (.kLoad8 .rax .xmm4 (at_ .rsi 0)) t₁ = some t₂ := by
    simp only [exec, eaS, rax₁, hl, Option.map_some, ht₂]
  generalize hG : t₁.mem.readW P 512 = G0
  have hld : t₂.load512 P = some G0 := by
    unfold State.load512
    rw [ite_eq_left (by rw [← ht₂, State.setZ_rd, State.setZ_wr, rd₁, wr₁]; exact rP), ← ht₂, State.setZ_mem, hG]
  generalize ht₃ : t₂.setZ .xmm6 (G0.extractLsb' 0 128) (G0.extractLsb' 128 128) (G0.extractLsb' 256 128)
    (G0.extractLsb' 384 128) = t₃
  have e₂ : exec (.vmovdqu32Load .xmm6 (at_ .rdi 0)) t₂ = some t₃ := by
    simp only [exec, ← ht₂, State.setZ_ea, eaP]; rw [ht₂, hld]; simp only [Option.map_some, ht₃]
  generalize ht₄ : (ZOp.zbin .vporq .xmm4 .xmm4 .xmm6).exec t₃ = t₄
  have e₃ : exec (.zop (.zbin .vporq .xmm4 .xmm4 .xmm6)) t₃ = some t₄ := by simp only [exec, ht₄]
  have hV : t₄.zmm .xmm4 = L ||| G0 := by
    rw [← ht₄, zmm_vporq, ← ht₃, StraightZ.zmm_setZ_other _ (by decide), zmm_setZ_lanes, ← ht₂,
      zmm_setZ_lanes]
  have wP₄ : InRegions t₄.wr P 64 := by
    rw [← ht₄, ZOp.exec_wr, ← ht₃, State.setZ_wr, ← ht₂, State.setZ_wr, wr₁]; exact wP
  have eaP₄ : t₄.ea (at_ .rdi 0) = P := by
    rw [← ht₄, ZOp.exec_ea, ← ht₃, State.setZ_ea, ← ht₂, State.setZ_ea, eaP]
  have e₄ : exec (.vmovdqu32Store (at_ .rdi 0) .xmm4) t₄ = some (t₄.setMem (t₄.mem.writeW P (L ||| G0))) := by
    simp only [exec, eaP₄, hV, State.store512_eq, ite_eq_left wP₄]
  refine WP.block_cons_iff.mpr ⟨_, e₁, WP.block_cons_iff.mpr ⟨_, e₂, WP.block_cons_iff.mpr ⟨_, e₃,
    WP.block_cons_iff.mpr ⟨_, e₄, WP.block_nil ?_⟩⟩⟩⟩
  have g₄ : t₄.gpr = t₁.gpr := by rw [← ht₄, ZOp.exec_gpr, ← ht₃, State.setZ_gpr, ← ht₂, State.setZ_gpr]
  have m₄ : t₄.mem = s.mem := by rw [← ht₄, ZOp.exec_mem, ← ht₃, State.setZ_mem, ← ht₂, State.setZ_mem, m₁]
  have hL' : L = Mem.readW (fun x => if (maskHi c).getLsbD (x - S).toNat then s.mem x else 0) S 512 := by
    rw [← hL, m₁]
  have hG' : G0 = s.mem.readW P 512 := by rw [← hG, m₁]
  -- `r10 = 64`, `r8 = 64 ⌊E / 64⌋`.
  have h9₅ : (t₄.setMem (t₄.mem.writeW P (L ||| G0))).gpr .r9 = BitVec.ofNat 64 E := by
    rw [State.setMem_gpr, g₄, g₁ _ (by decide) (by decide), h9]
  have e₅ : BitVec.ofNat 64 E >>> 6 = BitVec.ofNat 64 (E / 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
  have e₆ : BitVec.ofNat 64 (E / 64) <<< 6 = BitVec.ofNat 64 (64 * (E / 64)) := by
    rw [shl_ofNat (by omega)]; congr 1; omega
  apply WP.of_runBlock
  refine ⟨_, by xrun [execShift, h9₅, e₅, e₆], ?_⟩
  refine ⟨?_, by simp [gpr_setReg, gpr_setFlags, gpr_arithFlags], by simp [gpr_setReg, gpr_setFlags, gpr_arithFlags],
    fun r a b c d => ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_setFlags, mem_arithFlags, State.setMem_mem]
    rw [m₄, hL', hG', writeW_head]
  · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, b, c, d, ite_false, State.setMem_gpr]
    rw [g₄, g₁ r a b]
  · simp only [rd_setReg, rd_setFlags, rd_arithFlags, State.setMem_rd]
    rw [← ht₄, ZOp.exec_rd, ← ht₃, State.setZ_rd, ← ht₂, State.setZ_rd, rd₁]
  · simp only [wr_setReg, wr_setFlags, wr_arithFlags, State.setMem_wr]
    rw [← ht₄, ZOp.exec_wr, ← ht₃, State.setZ_wr, ← ht₂, State.setZ_wr, wr₁]
  · intro x hx l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [zlane_setReg, zlane_setFlags, zlane_arithFlags, State.setMem_zlane]
    rw [← ht₄, zlane_zbin _ _ _ _ _ _ hl, ite_eq_right hx.1, ← ht₃, State.zlane_setZ _ _ _ _ _ _ _ hl, ite_eq_right hx.2,
      ← ht₂, State.zlane_setZ _ _ _ _ _ _ _ hl, ite_eq_right hx.1, z₁ x l]

/-- The whole groups after the first: the `64 (q - 1)` bytes at `S + 64`
copied to `P + 64`, while `r10` runs from 64 to `r8 = 64 q`. -/
theorem gLoop_ok (s : State) {S P : Addr} {q : Nat} (hq : 2 ≤ q) (hq' : 64 * q < 2 ^ 63)
    (hsi : s.gpr .rsi = S) (hdi : s.gpr .rdi = P) (h10 : s.gpr .r10 = BitVec.ofNat 64 64)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 (64 * q))
    (rd : Covers [⟨S + BitVec.ofNat 64 64, 64 * (q - 1)⟩] (s.rd ++ s.wr))
    (wr : Covers [⟨P + BitVec.ofNat 64 64, 64 * (q - 1)⟩] s.wr)
    (disj : (⟨S + BitVec.ofNat 64 64, 64 * (q - 1)⟩ : Region).Disjoint ⟨P + BitVec.ofNat 64 64, 64 * (q - 1)⟩) :
    WP isa (.loop (.block gBody) .ne) s fun t =>
      t.mem = writeBytes s.mem (P + BitVec.ofNat 64 64) (bytesAt s.mem (S + BitVec.ofNat 64 64) (64 * (q - 1))) ∧
      t.gpr .r10 = BitVec.ofNat 64 (64 * q) ∧ (∀ r, r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      ZKeep [.xmm4] s t := by
  let S' := S + BitVec.ofNat 64 64
  let D' := P + BitVec.ofNat 64 64
  refine WP.loop (M := isa) (body := .block gBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = q - 1 - j ∧ j < q - 1 ∧ t.gpr .r10 = BitVec.ofNat 64 (64 + 64 * j) ∧
      t.mem = writeBytes s.mem D' (bytesAt s.mem S' (64 * j)) ∧ (∀ r, r ≠ .r10 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ ZKeep [.xmm4] s t) ?_ (q - 1 - 0) _
    ⟨0, rfl, by omega, by rw [h10], by simp [bytesAt, writeBytes_nil], fun _ _ => rfl, rfl, rfl, ZKeep.refl _ _⟩
  rintro k t ⟨j, rfl, hj, r10, mem, g, rd', wr', z⟩
  have hj64 : 64 * j + 64 ≤ 64 * (q - 1) := by omega
  obtain ⟨t', run', mem', r10', zf', g', rd'', wr'', z'⟩ := copy64Step_ok t (i := 64 + 64 * j)
    (by rw [g _ (by decide), hsi]) (by rw [g _ (by decide), hdi]) r10 (by rw [g _ (by decide), h8])
    (by rw [rd', wr', ← Offset.add_add_eq S rfl]; exact in_of_covers64 rd hj64 (by omega))
    (by rw [wr', ← Offset.add_add_eq P rfl]; exact in_of_covers64 wr hj64 (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have eS : S + BitVec.ofNat 64 (64 + 64 * j) = S' + BitVec.ofNat 64 (64 * j) := (Offset.add_add S 64 (64 * j)).symm
  have eD : P + BitVec.ofNat 64 (64 + 64 * j) = D' + BitVec.ofNat 64 (64 * j) := (Offset.add_add P 64 (64 * j)).symm
  have hlen : (bytesAt s.mem S' (64 * j)).length = 64 * j := length_bytesAt _ _ _
  have hsrc : bytesAt t.mem (S' + BitVec.ofNat 64 (64 * j)) 64 = bytesAt s.mem (S' + BitVec.ofNat 64 (64 * j)) 64 := by
    rw [mem]
    refine bytesAt_frame (writeBytes_frame' s.mem hlen) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact (disj.sub_left (Offset.sub_base S' hj64)).sub_right (Region.sub_prefix (by omega))
  have hmem : t'.mem = writeBytes s.mem D' (bytesAt s.mem S' (64 * (j + 1))) := by
    rw [mem', eS, eD, hsrc, mem, show 64 * (j + 1) = 64 * j + 64 by omega, bytesAt_add]
    conv => lhs; rw [show D' + BitVec.ofNat 64 (64 * j) = D' + BitVec.ofNat 64 (bytesAt s.mem S' (64 * j)).length
      by rw [hlen]]
    exact writeBytes_append s.mem D' (bytesAt s.mem S' (64 * j)) (bytesAt s.mem (S' + BitVec.ofNat 64 (64 * j)) 64)
      (by rw [length_bytesAt, length_bytesAt]; omega)
  have hz : t'.zf = some (decide (j + 1 = q - 1)) := by
    rw [zf', show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, ofNat_add_ofNat, sub_beq (by omega) (by omega)]
    congr 1; simp only [decide_eq_decide]; omega
  have gg : ∀ r, r ≠ .r10 → t'.gpr r = s.gpr r := fun r a => by rw [g' r a, g r a]
  have r10'' : t'.gpr .r10 = BitVec.ofNat 64 (64 + 64 * (j + 1)) := by
    rw [r10', show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, ofNat_add_ofNat]; congr 1
  by_cases he : j + 1 = q - 1
  · left
    refine ⟨by simp [eval, hz, he], ?_, by rw [r10'']; congr 1; omega, gg, by rw [rd'', rd'], by rw [wr'', wr'],
      z.trans z'⟩
    rw [hmem, he]
  · right
    refine ⟨by simp [eval, hz, he], q - 1 - (j + 1), by omega, j + 1, rfl, by omega, r10'', hmem, gg,
      by rw [rd'', rd'], by rw [wr'', wr'], z.trans z'⟩

/-- The bytes of the last group: the `k` bytes at `A`, then zeros. -/
def tailBytes (m : Mem) (A : Addr) (k : Nat) : List Byte :=
  (List.range 64).map fun j => if j < k then m (A + BitVec.ofNat 64 j) else 0

/-- The last group's store: the masked load of the `k` bytes at `A`, stored whole. -/
theorem writeW_tail (m : Mem) (A B : Addr) {k : Nat} (hk : k < 64) :
    m.writeW B (Mem.readW (fun x => if (BitVec.ofNat 64 (2 ^ k - 1)).getLsbD (x - A).toNat then m x else 0) A 512) =
      writeBytes m B (tailBytes m A k) := by
  generalize hf : (fun x => if (BitVec.ofNat 64 (2 ^ k - 1)).getLsbD (x - A).toNat then m x else 0) = f
  rw [writeW512_eq]
  congr 1
  simp only [tailBytes]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  rw [readW512_byte _ _ hj, ← hf]
  simp only [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega)]
  by_cases h : j < k
  · simp [h, getLsbD_low h hk]
  · simp only [h, ite_false]
    rw [BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]; simp [h]

/-- The last group: the `E mod 64` bytes left at `S + 64 q`, zeros after them,
stored whole at `P + 64 q`. -/
theorem gTail_ok (s : State) {S P : Addr} {q E : Nat} (hE : E < 2 ^ 63)
    (hsi : s.gpr .rsi = S) (hdi : s.gpr .rdi = P) (h10 : s.gpr .r10 = BitVec.ofNat 64 (64 * q))
    (h9 : s.gpr .r9 = BitVec.ofNat 64 E)
    (r : ∀ j < E % 64, InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 (64 * q) + BitVec.ofNat 64 j) 1)
    (w : InRegions s.wr (P + BitVec.ofNat 64 (64 * q)) 64) :
    WP isa (.block gTail) s fun t =>
      t.mem = writeBytes s.mem (P + BitVec.ofNat 64 (64 * q))
        (tailBytes s.mem (S + BitVec.ofNat 64 (64 * q)) (E % 64)) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ ZKeep [.xmm4] s t := by
  rw [show gTail = ([.mov .rcx (.reg .r9)] : List Instr) ++
      (([.mov32 .rax (imm 1), .shiftCl .shl .rax, .alu .sub .rax (imm 1)] : List Instr) ++
      [.kLoad8 .rax .xmm4 srcB, .vmovdqu32Store dstB .xmm4]) from rfl]
  refine WP.block_append (WP.of_runBlock ⟨s.setReg .rcx (s.gpr .r9), by xrun [], ?_⟩)
  have hk : ((s.setReg .rcx (s.gpr .r9)).gpr .rcx).toNat % 64 = E % 64 := by
    rw [gpr_setReg_self, h9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show E < 2 ^ 64 by omega)]
  refine WP.block_append (WP.mono (maskSetup_ok _ hk) fun t₁ ⟨rax₁, g₁, m₁, rd₁, wr₁, z₁⟩ => ?_)
  have g₁' : ∀ r, r ≠ .rax → r ≠ .rcx → t₁.gpr r = s.gpr r := fun r a b => by
    rw [g₁ r a]; simp [gpr_setReg, b]
  have hA : t₁.ea srcB = S + BitVec.ofNat 64 (64 * q) :=
    ea_idx t₁ .rsi (by rw [g₁' _ (by decide) (by decide), hsi]) (by rw [g₁' _ (by decide) (by decide), h10])
  have hB : t₁.ea dstB = P + BitVec.ofNat 64 (64 * q) :=
    ea_idx t₁ .rdi (by rw [g₁' _ (by decide) (by decide), hdi]) (by rw [g₁' _ (by decide) (by decide), h10])
  have hk64 : E % 64 < 64 := Nat.mod_lt _ (by decide)
  generalize hV : Mem.readW (fun x => if (BitVec.ofNat 64 (2 ^ (E % 64) - 1)).getLsbD
    (x - (S + BitVec.ofNat 64 (64 * q))).toNat then t₁.mem x else 0) (S + BitVec.ofNat 64 (64 * q)) 512 = V
  have hl : t₁.loadMasked512B (S + BitVec.ofNat 64 (64 * q)) (BitVec.ofNat 64 (2 ^ (E % 64) - 1)) = some V := by
    unfold State.loadMasked512B
    rw [bOn_low hk64, ite_eq_left (fun j hj => by
      rw [rd₁, wr₁]; exact r j (List.mem_range.mp hj)), hV]
  generalize ht₂ : t₁.setZ .xmm4 (V.extractLsb' 0 128) (V.extractLsb' 128 128) (V.extractLsb' 256 128)
    (V.extractLsb' 384 128) = t₂
  have e₁ : exec (.kLoad8 .rax .xmm4 srcB) t₁ = some t₂ := by
    simp only [exec, hA, rax₁, hl, Option.map_some, ht₂]
  have hz : t₂.zmm .xmm4 = V := by rw [← ht₂]; exact zmm_setZ_lanes t₁ .xmm4 V
  have w₂ : InRegions t₂.wr (P + BitVec.ofNat 64 (64 * q)) 64 := by
    rw [← ht₂, State.setZ_wr, wr₁]; exact w
  have e₂ : exec (.vmovdqu32Store dstB .xmm4) t₂ =
      some (t₂.setMem (t₂.mem.writeW (P + BitVec.ofNat 64 (64 * q)) V)) := by
    simp only [exec, ← ht₂, State.setZ_ea, hB]; rw [ht₂, hz, State.store512_eq, ite_eq_left w₂]
  refine WP.block_cons_iff.mpr ⟨_, e₁, WP.block_cons_iff.mpr ⟨_, e₂, WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩⟩⟩
  · rw [State.setMem_mem, ← ht₂, State.setZ_mem, ← hV, m₁, mem_setReg, writeW_tail _ _ _ hk64]
  · intro r a b; rw [State.setMem_gpr, ← ht₂, State.setZ_gpr, g₁' r a b]
  · rw [State.setMem_rd, ← ht₂, State.setZ_rd, rd₁]; rfl
  · rw [State.setMem_wr, ← ht₂, State.setZ_wr, wr₁]; rfl
  · intro x hx l hl
    simp only [List.mem_singleton] at hx
    rw [State.setMem_zlane, ← ht₂, State.zlane_setZ _ _ _ _ _ _ _ hl, ite_eq_right hx, z₁ x (by simp) l hl]
    rfl

/-- `a - (P + d)` from `a - P`, for `d < 2⁶³`. -/
theorem toNat_sub_add' (a P : Addr) {d : Nat} (hd : d < 2 ^ 63) :
    (a - (P + BitVec.ofNat 64 d)).toNat =
      if d ≤ (a - P).toNat then (a - P).toNat - d else 2 ^ 64 - d + (a - P).toNat := by
  have e : a - (P + BitVec.ofNat 64 d) = (a - P) - BitVec.ofNat 64 d := by rw [Offset.sub_add_eq]
  rw [e, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega)]
  have := (a - P).isLt
  split <;> omega

theorem getD_map_range {α : Type} (f : Nat → α) {n i : Nat} (d : α) (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]

/-- The memory after `copyG`'s groups, from `m`: the first group at `P`, the
whole groups after it, and the last. -/
def gWrites (m : Mem) (D P : Addr) (c n q : Nat) : Mem :=
  writeBytes (writeBytes (writeBytes m P (headBytes m (D - BitVec.ofNat 64 c) P c)) (P + BitVec.ofNat 64 64)
      (bytesAt m (D - BitVec.ofNat 64 c + BitVec.ofNat 64 64) (64 * (q - 1))))
    (P + BitVec.ofNat 64 (64 * q)) (tailBytes m (D - BitVec.ofNat 64 c + BitVec.ofNat 64 (64 * q)) ((c + n) % 64))

/-- The groups `copyG` stores, over `G` holding zeros from the text on, are the
text written at `P + c`. -/
theorem copyG_mem (m : Mem) (D P : Addr) {c n q : Nat} (hc : c < 64) (hq : q = (c + n) / 64) (h2 : 2 ≤ q)
    (hn : n < 2 ^ 60)
    (hz : ∀ o, c ≤ o → o < 64 * q + 64 → m (P + BitVec.ofNat 64 o) = 0) :
    gWrites m D P c n q = writeBytes m (P + BitVec.ofNat 64 c) (bytesAt m D n) := by
  unfold gWrites
  have hS : ∀ o, c ≤ o → D - BitVec.ofNat 64 c + BitVec.ofNat 64 o = D + BitVec.ofNat 64 (o - c) := fun o h => by
    rw [show BitVec.ofNat 64 o = BitVec.ofNat 64 c + BitVec.ofNat 64 (o - c) by rw [ofNat_add_ofNat]; congr 1; omega,
      ← BitVec.add_assoc, BitVec.sub_add_cancel]
  funext a
  generalize ho : (a - P).toNat = o
  have hoL : o < 2 ^ 64 := ho ▸ (a - P).isLt
  have ha : a = P + BitVec.ofNat 64 o := by
    rw [← ho, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  simp only [writeBytes, headBytes, tailBytes, bytesAt, List.length_map, List.length_range]
  rw [toNat_sub_add' a P (show 64 * q < 2 ^ 63 by omega), toNat_sub_add' a P (show 64 < 2 ^ 63 by omega),
    toNat_sub_add' a P (show c < 2 ^ 63 by omega), ho]
  have hE : 64 * q ≤ c + n ∧ c + n < 64 * q + 64 := by omega
  by_cases h1 : 64 * q ≤ o
  · by_cases h1' : o - 64 * q < 64
    · simp only [h1, h1', ite_true, show c ≤ o by omega]
      rw [getD_map_range _ _ h1']
      by_cases hk : o - 64 * q < (c + n) % 64
      · simp only [hk, ite_true, show o - c < n by omega]
        rw [getD_map_range _ _ (show o - c < n by omega), Offset.add_add, show 64 * q + (o - 64 * q) = o by omega,
          hS o (by omega)]
      · simp only [hk, ite_false, show ¬o - c < n by omega]
        rw [ha, hz o (by omega) (by omega)]
    · simp only [h1, h1', ite_true, ite_false, show 64 ≤ o by omega, show ¬o - 64 < 64 * (q - 1) by omega,
        show ¬o < 64 by omega, show c ≤ o by omega, show ¬o - c < n by omega]
  · simp only [h1, ite_false, show ¬2 ^ 64 - 64 * q + o < 64 by omega]
    by_cases h3 : 64 ≤ o
    · simp only [h3, ite_true, show o - 64 < 64 * (q - 1) by omega, show c ≤ o by omega, show o - c < n by omega]
      rw [getD_map_range _ _ (show o - 64 < 64 * (q - 1) by omega), getD_map_range _ _ (show o - c < n by omega),
        Offset.add_add, show 64 + (o - 64) = o by omega, hS o (by omega)]
    · simp only [h3, ite_false, show ¬2 ^ 64 - 64 + o < 64 * (q - 1) by omega, show o < 64 by omega, ite_true]
      rw [getD_map_range _ _ (show o < 64 by omega)]
      by_cases hco : c ≤ o
      · simp only [hco, ite_true, show o - c < n by omega]
        rw [getD_map_range _ _ (show o - c < n by omega), hS o hco, hz o hco (by omega)]
        simp
      · simp only [hco, ite_false, show ¬2 ^ 64 - c + o < n by omega]
        rw [ha]; simp

/-- The bytes of the last group from `m'` are those from `m` when `m'` keeps the `k` bytes at `A`. -/
theorem tailBytes_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {A : Addr} {k : Nat}
    (hd : ∀ r ∈ rs, (⟨A, k⟩ : Region).Disjoint r) (hk : k ≤ 2 ^ 64) :
    tailBytes m' A k = tailBytes m A k := by
  simp only [tailBytes]
  refine List.map_congr_left fun j _ => ?_
  by_cases h : j < k
  · simp only [h, ite_true]; exact hf.bytes (R := ⟨A, k⟩) hd hk h
  · simp [h]

/-- What `copyG` needs: `W` (`r15`) with `lead`, `na`, `D` and `n` in it,
the `n` bytes of text at `D` readable and apart from `W`, at least 192 of
them, and the text starting off a group of `G` and ending before its last block. -/
structure CopyGPre (s : State) (W D : Addr) (lead na n : Nat) : Prop where
  hw : Covers [⟨W, 2560⟩] s.wr
  rdi : s.gpr .rdi = W + BitVec.ofNat 64 (512 + 16 * (lead + na))
  rsi : s.gpr .rsi = D
  rcx : s.gpr .rcx = BitVec.ofNat 64 n
  rax : s.gpr .rax = BitVec.ofNat 64 ((lead + na) % 4)
  n192 : 192 ≤ n
  sh : (lead + na) % 4 ≠ 0
  fit : 16 * (lead + na) + n ≤ 496
  rd : Covers [⟨D, n⟩] (s.rd ++ s.wr)
  disj : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩

theorem copyG_ok (s : State) {W D : Addr} {lead na n : Nat} (h : CopyGPre s W D lead na n) :
    WP isa copyG s fun s' =>
      s'.mem = gWrites s.mem D (W + BitVec.ofNat 64 (512 + 16 * (lead + na - (lead + na) % 4)))
        (16 * ((lead + na) % 4)) n ((16 * ((lead + na) % 4) + n) / 64) ∧
      Frame [⟨W + BitVec.ofNat 64 512, 512⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rsi → r ≠ .rdi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ZKeep [.xmm4, .xmm6] s s' := by
  have hfit := h.fit
  have h192 := h.n192
  have hsh := h.sh
  have hrd := h.rd
  have hdisj := h.disj
  have hw := h.hw
  obtain ⟨t₀, run₀, di₀, r8₀, si₀, r9₀, g₀, m₀, rd₀, wr₀, z₀⟩ :=
    gArgs_ok (t := lead + na) s h.rdi h.rsi h.rcx h.rax (by omega)
  generalize ht : lead + na = t at *
  generalize hc : 16 * (t % 4) = c at *
  generalize hP : W + BitVec.ofNat 64 (512 + 16 * (t - t % 4)) = P at *
  have hc1 : 16 ≤ c ∧ c ≤ 48 := by omega
  have hq3 : 3 ≤ (c + n) / 64 := by omega
  have hqP : 16 * (t - t % 4) + 64 * ((c + n) / 64) + 64 ≤ 512 := by omega
  generalize hq : (c + n) / 64 = q at hq3 hqP
  have hqE : 64 * q ≤ c + n ∧ c + n < 64 * q + 64 := by omega
  have hPo : ∀ o, P + BitVec.ofNat 64 o = W + BitVec.ofNat 64 (512 + 16 * (t - t % 4) + o) := fun o => by
    rw [← hP, Offset.add_add]
  have hS : ∀ o, c ≤ o → D - BitVec.ofNat 64 c + BitVec.ofNat 64 o = D + BitVec.ofNat 64 (o - c) := fun o hco => by
    rw [show BitVec.ofNat 64 o = BitVec.ofNat 64 c + BitVec.ofNat 64 (o - c) by rw [ofNat_add_ofNat]; congr 1; omega,
      ← BitVec.add_assoc, BitVec.sub_add_cancel]
  have inW : ∀ {o k : Nat}, 512 + 16 * (t - t % 4) + o + k ≤ 2560 → InRegions s.wr (P + BitVec.ofNat 64 o) k :=
    fun hk => by rw [hPo]; exact in_off hw hk (by decide)
  have inW0 : InRegions s.wr P 64 := by
    have := inW (o := 0) (k := 64) (by omega)
    rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
  have subW : ∀ {o k : Nat}, 512 + 16 * (t - t % 4) + o + k ≤ 2560 →
      Region.Sub ⟨P + BitVec.ofNat 64 o, k⟩ ⟨W, 2560⟩ := fun hk => by rw [hPo]; exact Offset.sub_base W hk
  have subW0 : Region.Sub ⟨P, 64⟩ ⟨W, 2560⟩ := by
    have := subW (o := 0) (k := 64) (by omega)
    rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
  have subD : ∀ {o k : Nat}, c ≤ o → o - c + k ≤ n →
      Region.Sub ⟨D - BitVec.ofNat 64 c + BitVec.ofNat 64 o, k⟩ ⟨D, n⟩ := fun hco hk => by
    rw [hS _ hco]; exact Offset.sub_base D hk
  have rdD : ∀ {o : Nat}, c ≤ o → o - c < n → InRegions (s.rd ++ s.wr) (D - BitVec.ofNat 64 c + BitVec.ofNat 64 o) 1 :=
    fun hco hk => by rw [hS _ hco]; exact in_of_covers hrd hk (by omega)
  unfold copyG
  -- The first group.
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨t₀, run₀, WP.mono (gHead_ok t₀ (c := c) (E := c + n)
    (by omega) (by omega) si₀ di₀ r8₀ r9₀
    (fun j hj hj' => by rw [rd₀, wr₀]; exact rdD hj (by omega))
    (by rw [rd₀, wr₀]; exact in_left inW0) (by rw [wr₀]; exact inW0))
    fun t₁ ⟨m₁, r10₁, r8₁, g₁, rd₁, wr₁, z₁⟩ => ?_⟩))
  rw [hq] at r8₁
  have gg₁ : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rsi → r ≠ .rdi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → t₁.gpr r = s.gpr r :=
    fun r a b c' d e f g' => by rw [g₁ r a b e g', g₀ r d e c' f]
  have si₁ : t₁.gpr .rsi = D - BitVec.ofNat 64 c := by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), si₀]
  have di₁ : t₁.gpr .rdi = P := by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), di₀]
  have r9₁ : t₁.gpr .r9 = BitVec.ofNat 64 (c + n) := by
    rw [g₁ _ (by decide) (by decide) (by decide) (by decide), r9₀]
  -- The whole groups.
  refine WP.seq (WP.mono (gLoop_ok t₁ (q := q) (by omega) (by omega) si₁ di₁ r10₁ r8₁
    (by
      rw [rd₁, wr₁, rd₀, wr₀]
      exact Covers.trans (Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨D, n⟩, List.mem_singleton_self _, 64 - c, hS 64 (by omega), by dsimp only; omega⟩) hrd)
    (by
      rw [wr₁, wr₀]
      exact Covers.trans (Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨W, 2560⟩, List.mem_singleton_self _, 512 + 16 * (t - t % 4) + 64, hPo 64, by dsimp only; omega⟩) hw)
    ((hdisj.sub_left (subD (by omega) (by omega))).sub_right (subW (by omega))))
    fun t₂ ⟨m₂, r10₂, g₂, rd₂, wr₂, z₂⟩ => ?_)
  have si₂ : t₂.gpr .rsi = D - BitVec.ofNat 64 c := by rw [g₂ _ (by decide), si₁]
  have di₂ : t₂.gpr .rdi = P := by rw [g₂ _ (by decide), di₁]
  have r9₂ : t₂.gpr .r9 = BitVec.ofNat 64 (c + n) := by rw [g₂ _ (by decide), r9₁]
  -- The last group.
  refine WP.mono (gTail_ok t₂ (q := q) (E := c + n) (by omega) si₂ di₂ r10₂ r9₂
    (fun j hj => by
      rw [rd₂, wr₂, rd₁, wr₁, rd₀, wr₀, Offset.add_add]
      exact rdD (by omega) (by omega))
    (by rw [wr₂, wr₁, wr₀]; exact inW (by omega)))
    fun t₃ ⟨m₃, g₃, rd₃, wr₃, z₃⟩ => ?_
  -- The memory.
  have f₁ : Frame [⟨P, 64⟩] s.mem t₁.mem := by
    rw [m₁, m₀]; exact writeBytes_frame' _ (by simp [headBytes])
  have f₂ : Frame [⟨P + BitVec.ofNat 64 64, 64 * (q - 1)⟩] t₁.mem t₂.mem := by
    rw [m₂]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  have f₁₂ : Frame [⟨P, 64⟩, ⟨P + BitVec.ofNat 64 64, 64 * (q - 1)⟩] s.mem t₂.mem :=
    (f₁.mono (by simp)).trans (f₂.mono (by simp))
  have dD : ∀ {o k : Nat}, c ≤ o → o - c + k ≤ n → ∀ r ∈ [(⟨P, 64⟩ : Region), ⟨P + BitVec.ofNat 64 64, 64 * (q - 1)⟩],
      (⟨D - BitVec.ofNat 64 c + BitVec.ofNat 64 o, k⟩ : Region).Disjoint r := fun hco hk r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hdisj.sub_left (subD hco hk)).sub_right subW0
    · exact (hdisj.sub_left (subD hco hk)).sub_right (subW (by omega))
  have hmid : bytesAt t₁.mem (D - BitVec.ofNat 64 c + BitVec.ofNat 64 64) (64 * (q - 1)) =
      bytesAt s.mem (D - BitVec.ofNat 64 c + BitVec.ofNat 64 64) (64 * (q - 1)) :=
    bytesAt_frame f₁ (fun r hr => dD (by omega) (by omega) r (by simp at hr; simp [hr])) (by omega)
  have htail : tailBytes t₂.mem (D - BitVec.ofNat 64 c + BitVec.ofNat 64 (64 * q)) ((c + n) % 64) =
      tailBytes s.mem (D - BitVec.ofNat 64 c + BitVec.ofNat 64 (64 * q)) ((c + n) % 64) :=
    tailBytes_frame f₁₂ (dD (by omega) (by omega)) (by omega)
  have f₃ : Frame [⟨P + BitVec.ofNat 64 (64 * q), 64⟩] t₂.mem t₃.mem := by
    rw [m₃]; exact writeBytes_frame' _ (by simp [tailBytes])
  refine ⟨?_, ?_, fun r a b c' d e f g' => by rw [g₃ r a b, g₂ r g', gg₁ r a b c' d e f g'],
    by rw [rd₃, rd₂, rd₁, rd₀], by rw [wr₃, wr₂, wr₁, wr₀], ?_⟩
  · rw [m₃, htail, m₂, hmid, m₁, m₀]; rfl
  · refine ((f₁₂.mono (rs' := [⟨P, 64⟩, ⟨P + BitVec.ofNat 64 64, 64 * (q - 1)⟩,
      ⟨P + BitVec.ofNat 64 (64 * q), 64⟩]) (by simp)).trans (f₃.mono (by simp))).sub fun r hr => ?_
    have hG : ∀ {o k : Nat}, 16 * (t - t % 4) + o + k ≤ 512 →
        Region.Sub ⟨P + BitVec.ofNat 64 o, k⟩ ⟨W + BitVec.ofNat 64 512, 512⟩ := fun {o k} hk => by
      rw [hPo, Nat.add_assoc, ← Offset.add_add W 512 (16 * (t - t % 4) + o)]
      exact Offset.sub_base _ hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    rcases hr with rfl | rfl | rfl
    · have := hG (o := 0) (k := 64) (by omega)
      rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
    · exact hG (by omega)
    · exact hG (by omega)
  · exact (((ZKeep.mono (rs := []) (fun r _ l _ => z₀ r l) (by simp)).trans z₁).trans (z₂.mono (by simp))).trans
      (z₃.mono (by simp))

/-- The copy's setup: `r10 = 0` and `r8 = 64 ⌊n / 64⌋`, compared with 64. -/
theorem copyHdr_ok (s : State) {n : Nat} (hn : s.gpr .rcx = BitVec.ofNat 64 n) (hlt : n < 2 ^ 63) :
    WP isa (.block [.mov32 .r10 (imm 0), .mov .r8 (.reg .rcx), .shift .shr .r8 6, .shift .shl .r8 6,
        .alu .cmp .r8 (imm 64)]) s fun s' =>
      s'.gpr .r10 = BitVec.ofNat 64 0 ∧ s'.gpr .r8 = BitVec.ofNat 64 (64 * (n / 64)) ∧
      s'.cf = some (decide (64 * (n / 64) < 64)) ∧ s'.zf = some (decide (64 * (n / 64) = 64)) ∧
      (∀ r, r ≠ .r8 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ZKeep [] s s' := by
  have e₁ : BitVec.ofNat 64 n >>> 6 = BitVec.ofNat 64 (n / 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
  have e₂ : BitVec.ofNat 64 (n / 64) <<< 6 = BitVec.ofNat 64 (64 * (n / 64)) := by
    rw [shl_ofNat (by omega)]; congr 1; omega
  obtain ⟨u₁, run₁, r10₁, r8₁, g₁, m₁, rd₁, wr₁, z₁⟩ : ∃ u₁, runBlock isa [.mov32 .r10 (imm 0), .mov .r8 (.reg .rcx),
      .shift .shr .r8 6, .shift .shl .r8 6] s = some u₁ ∧ u₁.gpr .r10 = BitVec.ofNat 64 0 ∧
      u₁.gpr .r8 = BitVec.ofNat 64 (64 * (n / 64)) ∧ (∀ r, r ≠ .r8 → r ≠ .r10 → u₁.gpr r = s.gpr r) ∧
      u₁.mem = s.mem ∧ u₁.rd = s.rd ∧ u₁.wr = s.wr ∧ ∀ r l, u₁.zlane r l = s.zlane r l := by
    refine ⟨_, by xrun [execShift, hn, e₁, e₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, gpr_setFlags, gpr_arithFlags]
    · simp [gpr_setReg, gpr_setFlags, gpr_arithFlags]
    · intro r a b; simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, a, b]
    · simp only [mem_setReg, mem_setFlags, mem_arithFlags]
    · simp only [rd_setReg, rd_setFlags, rd_arithFlags]
    · simp only [wr_setReg, wr_setFlags, wr_arithFlags]
    · intro r l; simp only [zlane_setReg, zlane_arithFlags, zlane_setFlags]
  obtain ⟨u₂, run₂, zf₂, cf₂, g₂, m₂, rd₂, wr₂⟩ := cmpImm_ok u₁ .r8 r8₁ (by omega) (show 64 < 2 ^ 31 by decide)
  have z₂ : ∀ r l, u₂.zlane r l = u₁.zlane r l := by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, imm] at run₂
    cases run₂; intro r l; rfl
  rw [show ([.mov32 .r10 (imm 0), .mov .r8 (.reg .rcx), .shift .shr .r8 6, .shift .shl .r8 6,
      .alu .cmp .r8 (imm 64)] : List Instr) = [.mov32 .r10 (imm 0), .mov .r8 (.reg .rcx), .shift .shr .r8 6,
      .shift .shl .r8 6] ++ [.alu .cmp .r8 (imm 64)] from rfl]
  refine WP.block_append_iff.mpr (WP.of_runBlock ⟨u₁, run₁, WP.of_runBlock ⟨u₂, run₂, by rw [g₂, r10₁],
    by rw [g₂, r8₁], cf₂, zf₂, fun r a b => by rw [g₂, g₁ r a b], by rw [m₂, m₁], by rw [rd₂, rd₁],
    by rw [wr₂, wr₁], fun r _ l _ => by rw [z₂, z₁]⟩⟩)

/-- `copyCG`: the text copied to `G`, by `copyG` from 192 bytes on unless it
starts at a group, otherwise as `copyBytes` copies. -/
theorem copyCG_ok (s : State) {W D : Addr} {lead na n : Nat} (h15 : s.gpr .r15 = W)
    (hw : Covers [⟨W, 2560⟩] s.wr) (hlead : s.mem.readW (W + BitVec.ofNat 64 296) 64 = BitVec.ofNat 64 lead)
    (hna : s.mem.readW (W + BitVec.ofNat 64 272) 64 = BitVec.ofNat 64 na)
    (hD : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hn : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n) (hfit : 16 * (lead + na) + n ≤ 496)
    (hrd : Covers [⟨D, n⟩] (s.rd ++ s.wr)) (hdisj : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa copyCG s fun s' =>
      Frame [⟨W + BitVec.ofNat 64 512, 512⟩] s.mem s'.mem ∧
      ((∀ j, 16 * (lead + na) ≤ j → j < 512 → s.mem (W + BitVec.ofNat 64 (512 + j)) = 0) →
        s'.mem = writeBytes s.mem (W + BitVec.ofNat 64 (512 + 16 * (lead + na))) (bytesAt s.mem D n)) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rsi → r ≠ .rdi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ZKeep [.xmm4, .xmm6] s s' := by
  -- The arguments: `rdi` at the text in `G`, `rsi` the text, `rcx` its length.
  obtain ⟨u₁, run₁, di₁, si₁, cx₁, g₁, m₁, rd₁, wr₁, z₁⟩ := copyCArgs_ok (W := W) (D := D) (n := n) (lead := lead)
    (na := na) s h15 hw hlead hna hD hn (by omega)
  have cp : CopyPre u₁ D (W + BitVec.ofNat 64 (512 + 16 * (lead + na))) n := ⟨si₁, di₁, cx₁, by omega,
    by rw [rd₁, wr₁]; exact hrd,
    by rw [wr₁]; exact Covers.trans (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨W, 2560⟩, List.mem_singleton_self _, 512 + 16 * (lead + na), rfl, by dsimp only; omega⟩) hw,
    hdisj.sub_right (Offset.sub_base W (by omega))⟩
  -- What `copyBytes`'s copy leaves, as the theorem states it.
  have fin : ∀ w : State, CopyPost u₁ D (W + BitVec.ofNat 64 (512 + 16 * (lead + na))) n w →
      Frame [⟨W + BitVec.ofNat 64 512, 512⟩] s.mem w.mem ∧
      ((∀ j, 16 * (lead + na) ≤ j → j < 512 → s.mem (W + BitVec.ofNat 64 (512 + j)) = 0) →
        w.mem = writeBytes s.mem (W + BitVec.ofNat 64 (512 + 16 * (lead + na))) (bytesAt s.mem D n)) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rsi → r ≠ .rdi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → w.gpr r = s.gpr r) ∧
      w.rd = s.rd ∧ w.wr = s.wr ∧ ZKeep [.xmm4, .xmm6] s w := fun w ⟨m₂, g₂, rd₂, wr₂, z₂⟩ => by
    have hm : w.mem = writeBytes s.mem (W + BitVec.ofNat 64 (512 + 16 * (lead + na))) (bytesAt s.mem D n) := by
      rw [m₂, m₁]
    refine ⟨by
        rw [hm]
        refine (writeBytes_frame' _ (length_bytesAt _ _ _)).sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
        simp only [List.mem_singleton] at hr; subst hr
        rw [← Offset.add_add W 512 (16 * (lead + na))]
        exact Offset.sub_base _ (by omega),
      fun _ => hm, fun r a b c' d e f g' => by rw [g₂ r a e g', g₁ r d c' b],
      by rw [rd₂, rd₁], by rw [wr₂, wr₁], ?_⟩
    exact (ZKeep.mono (rs := []) (fun r _ l _ => by rw [z₁ r l]) (by simp)).trans (z₂.mono (by simp))
  -- The loop and the masked move, from a state with the setup's registers.
  have viaLoop : ∀ v : State, v.gpr .r10 = BitVec.ofNat 64 0 → v.gpr .r8 = BitVec.ofNat 64 (64 * (n / 64)) →
      (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → v.gpr r = u₁.gpr r) → v.mem = u₁.mem → v.rd = u₁.rd →
      v.wr = u₁.wr → ZKeep [.xmm4] u₁ v → 0 < n / 64 →
      WP isa (.seq loop64 (.block tailMove)) v fun s' =>
        Frame [⟨W + BitVec.ofNat 64 512, 512⟩] s.mem s'.mem ∧
        ((∀ j, 16 * (lead + na) ≤ j → j < 512 → s.mem (W + BitVec.ofNat 64 (512 + j)) = 0) →
          s'.mem = writeBytes s.mem (W + BitVec.ofNat 64 (512 + 16 * (lead + na))) (bytesAt s.mem D n)) ∧
        (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rsi → r ≠ .rdi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ ZKeep [.xmm4, .xmm6] s s' :=
    fun v r10 r8 g m rd wr z hq => WP.seq (WP.mono (copyLoop_ok u₁ cp v r10 r8 g m rd wr z hq)
      fun w hw => WP.mono (copyTail_ok u₁ cp w hw) fin)
  refine WP.seq ?_
  rw [copyArgs, WP.block_append_iff]
  refine WP.of_runBlock ⟨u₁, run₁, WP.mono (copyHdr_ok u₁ cx₁ (by omega))
    fun u₂ ⟨r10₂, r8₂, cf₂, zf₂, g₂, m₂, rd₂, wr₂, z₂⟩ => ?_⟩
  have gq : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → u₂.gpr r = u₁.gpr r := fun r _ b c => g₂ r b c
  have zq : ZKeep [.xmm4] u₁ u₂ := z₂.mono (by simp)
  -- Fewer than 64 bytes: the masked move alone.
  refine WP.ite (decide (64 * (n / 64) < 64)) (by simp only [eval, cf₂]) (fun hb => ?_) (fun hb => ?_)
  · have hq : 64 * (n / 64) = 0 := by have := of_decide_eq_true hb; omega
    exact WP.mono (copyTail_ok u₁ cp u₂ ⟨by rw [r10₂, hq], by rw [m₂, hq]; simp [bytesAt, writeBytes_nil],
      gq, rd₂, wr₂, zq⟩) fin
  have h64 : 64 ≤ n := by have := of_decide_eq_false hb; omega
  -- 64 to 127 bytes: the loop, once.
  refine WP.ite (decide (64 * (n / 64) = 64)) (by simp only [eval, zf₂]) (fun he => ?_) (fun he => ?_)
  · exact viaLoop u₂ r10₂ r8₂ gq m₂ rd₂ wr₂ zq (by omega)
  have h128 : 128 ≤ n := by have := of_decide_eq_false he; omega
  -- `n` compared with 192.
  obtain ⟨u₃, run₃, -, cf₃, g₃, m₃, rd₃, wr₃⟩ := cmpImm_ok u₂ .rcx
    (by rw [g₂ _ (by decide) (by decide), cx₁]) (by omega) (show 192 < 2 ^ 31 by decide)
  have z₃ : ∀ r l, u₃.zlane r l = u₂.zlane r l := by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, imm] at run₃
    cases run₃; intro r l; rfl
  have gq₃ : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → u₃.gpr r = u₁.gpr r := fun r a b c => by rw [g₃, gq r a b c]
  have zq₃ : ZKeep [.xmm4] u₁ u₃ := zq.trans (fun r _ l _ => z₃ r l)
  refine WP.seq (WP.of_runBlock ⟨u₃, run₃, ?_⟩)
  refine WP.iteCold_iff.mpr (WP.ite (!decide (n < 192)) (by show u₃.cf.map _ = _; rw [cf₃]; rfl)
    (fun hb => ?_) (fun hb => ?_))
  rotate_left
  · exact viaLoop u₃ (by rw [g₃, r10₂]) (by rw [g₃, r8₂]) gq₃ (by rw [m₃, m₂]) (by rw [rd₃, rd₂])
      (by rw [wr₃, wr₂]) zq₃ (by omega)
  have h192 : 192 ≤ n := by simpa using hb
  -- `t = lead + na` tested for a multiple of 4, from `rdi`.
  refine WP.seq (WP.mono (gShift_ok u₃ (W := W) (t := lead + na)
    (by rw [g₃, g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide), h15])
    (by rw [g₃, g₂ _ (by decide) (by decide), di₁]) (by omega))
    fun u₄ ⟨ax₄, zf₄, g₄, m₄, rd₄, wr₄, z₄⟩ => ?_)
  have gq₄ : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → u₄.gpr r = u₁.gpr r := fun r a b c => by
    rw [g₄ r a, gq₃ r a b c]
  refine WP.ite (decide ((lead + na) % 4 = 0)) (by simp only [eval, zf₄]) (fun hz => ?_) (fun hz => ?_)
  · exact viaLoop u₄ (by rw [g₄ _ (by decide), g₃, r10₂]) (by rw [g₄ _ (by decide), g₃, r8₂]) gq₄
      (by rw [m₄, m₃, m₂]) (by rw [rd₄, rd₃, rd₂]) (by rw [wr₄, wr₃, wr₂])
      (zq₃.trans (fun r _ l _ => z₄ r l)) (by omega)
  have hsh : (lead + na) % 4 ≠ 0 := by simpa using hz
  have m₄s : u₄.mem = s.mem := by rw [m₄, m₃, m₂, m₁]
  have rd₄s : u₄.rd = s.rd := by rw [rd₄, rd₃, rd₂, rd₁]
  have wr₄s : u₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, wr₁]
  have g₄s : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rsi → r ≠ .rdi → r ≠ .r8 → r ≠ .r10 → u₄.gpr r = s.gpr r :=
    fun r a b c d e f => by rw [gq₄ r a e f, g₁ r d c b]
  have z₄s : ZKeep [] s u₄ := fun r _ l _ => by rw [z₄, z₃, z₂ r (by simp) l (by omega), z₁]
  refine WP.mono (copyG_ok u₄ ⟨by rw [wr₄s]; exact hw,
    by rw [g₄ _ (by decide), g₃, g₂ _ (by decide) (by decide), di₁],
    by rw [g₄ _ (by decide), g₃, g₂ _ (by decide) (by decide), si₁],
    by rw [g₄ _ (by decide), g₃, g₂ _ (by decide) (by decide), cx₁], ax₄, h192, hsh, hfit,
    by rw [rd₄s, wr₄s]; exact hrd, hdisj⟩)
    fun s' ⟨m', f', g', rd', wr', z'⟩ => ⟨by rw [← m₄s]; exact f', fun hz => by
      rw [m', m₄s, copyG_mem s.mem D _ (by omega) rfl (by omega) (by omega) (fun o hco ho => ?_)]
      · rw [Offset.add_add, show 512 + 16 * (lead + na - (lead + na) % 4) + 16 * ((lead + na) % 4) =
          512 + 16 * (lead + na) by omega]
      · rw [Offset.add_add, Nat.add_assoc]
        exact hz _ (by omega) (by omega),
      fun r a b c' d e f g'' => by rw [g' r a b c' d e f g'', g₄s r a b c' d e g''],
      by rw [rd', rd₄s], by rw [wr', wr₄s], (ZKeep.mono (rs := []) z₄s (by simp)).trans z'⟩

end VG.Proof.AesGcm.X86_64.Short
