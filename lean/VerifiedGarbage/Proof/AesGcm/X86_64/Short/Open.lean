module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Seal
public import VerifiedGarbage.Proof.AesGcm.X86_64.Seal
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.AesGcm.X86_64.Open
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamVerify
import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Copy
import VerifiedGarbage.Proof.Framework.Cold
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Framework.X86_64.StraightZ
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Small

/-! ### `AesGcm.X86_64.Short.CopyG`, which this module and modules that import it used -/

section

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
    Nat.mod_eq_of_lt (show x % 4 < 2 ^ 64 by omega_arith)]

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
  obtain e₁ : W + BitVec.ofNat 64 (512 + 16 * t) - W = BitVec.ofNat 64 (512 + 16 * t) :=
    Offset.add_sub_cancel_left _ _
  obtain e₂ : BitVec.ofNat 64 (512 + 16 * t) >>> 4 = BitVec.ofNat 64 (32 + t) := by
    rw [shr4 _ (by omega_arith)]; congr 1; omega_arith
  obtain e₃ : BitVec.ofNat 64 (32 + t) &&& 3#64 = BitVec.ofNat 64 (t % 4) := by
    rw [ofNat_and3 (by omega_arith)]; congr 1; omega_arith
  refine WP.of_runBlock ⟨_, by xrun [gShift, execShift, h15, hdi, e₁, e₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, imm, e₃]
  · rw [zf_setReg, zf_arithFlags, e₃]
    obtain hx : t % 4 < 4 := Nat.mod_lt _ (by decide)
    generalize t % 4 = x at hx ⊢
    rcases (by omega_arith : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) with rfl | rfl | rfl | rfl <;> decide
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
  obtain e₄ : BitVec.ofNat 64 (t % 4) <<< 4 = BitVec.ofNat 64 (16 * (t % 4)) := by
    rw [shl_ofNat (by omega_arith)]; congr 1; omega_arith
  obtain e₅ : W + BitVec.ofNat 64 (512 + 16 * t) - BitVec.ofNat 64 (16 * (t % 4)) =
      W + BitVec.ofNat 64 (512 + 16 * (t - t % 4)) := by
    rw [add_ofNat_sub_ofNat W (by omega_arith) (by omega_arith)]; congr 2; omega_arith
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
  by_cases h : c ≤ j <;> simp [h, hj] <;> omega_arith

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
  obtain hk : (BitVec.ofNat 64 c).toNat % 64 = c := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt hc]
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
  obtain hj := List.mem_range.mp hj
  rw [BitVec.extractLsb'_or, readW512_byte _ _ hj, readW512_byte _ _ hj, ← hf]
  simp only [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega_arith),
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
  obtain hsi₁ : t₁.gpr .rsi = S := by rw [g₁ _ (by decide) (by decide), hsi]
  obtain hdi₁ : t₁.gpr .rdi = P := by rw [g₁ _ (by decide) (by decide), hdi]
  obtain eaS : t₁.ea (at_ .rsi 0) = S := by simp [State.ea, at_, hsi₁]
  obtain eaP : t₁.ea (at_ .rdi 0) = P := by simp [State.ea, at_, hdi₁]
  generalize hL : Mem.readW (fun x => if (maskHi c).getLsbD (x - S).toNat then t₁.mem x else 0) S 512 = L
  obtain hl : t₁.loadMasked512B S (maskHi c) = some L := by
    unfold State.loadMasked512B
    rw [ite_eq_left (fun j hj => by rw [mem_bOn_maskHi] at hj; rw [rd₁, wr₁]; exact r j hj.1 hj.2), hL]
  generalize ht₂ : t₁.setZ .xmm4 (L.extractLsb' 0 128) (L.extractLsb' 128 128) (L.extractLsb' 256 128)
    (L.extractLsb' 384 128) = t₂
  obtain e₁ : exec (.kLoad8 .rax .xmm4 (at_ .rsi 0)) t₁ = some t₂ := by
    simp only [exec, eaS, rax₁, hl, Option.map_some, ht₂]
  generalize hG : t₁.mem.readW P 512 = G0
  obtain hld : t₂.load512 P = some G0 := by
    unfold State.load512
    rw [ite_eq_left (by rw [← ht₂, State.setZ_rd, State.setZ_wr, rd₁, wr₁]; exact rP), ← ht₂, State.setZ_mem, hG]
  generalize ht₃ : t₂.setZ .xmm6 (G0.extractLsb' 0 128) (G0.extractLsb' 128 128) (G0.extractLsb' 256 128)
    (G0.extractLsb' 384 128) = t₃
  obtain e₂ : exec (.vmovdqu32Load .xmm6 (at_ .rdi 0)) t₂ = some t₃ := by
    simp only [exec, ← ht₂, State.setZ_ea, eaP]; rw [ht₂, hld]; simp only [Option.map_some, ht₃]
  generalize ht₄ : (ZOp.zbin .vporq .xmm4 .xmm4 .xmm6).exec t₃ = t₄
  obtain e₃ : exec (.zop (.zbin .vporq .xmm4 .xmm4 .xmm6)) t₃ = some t₄ := by simp only [exec, ht₄]
  obtain hV : t₄.zmm .xmm4 = L ||| G0 := by
    rw [← ht₄, zmm_vporq, ← ht₃, StraightZ.zmm_setZ_other _ (by decide), zmm_setZ_lanes, ← ht₂,
      zmm_setZ_lanes]
  obtain wP₄ : InRegions t₄.wr P 64 := by
    rw [← ht₄, ZOp.exec_wr, ← ht₃, State.setZ_wr, ← ht₂, State.setZ_wr, wr₁]; exact wP
  obtain eaP₄ : t₄.ea (at_ .rdi 0) = P := by
    rw [← ht₄, ZOp.exec_ea, ← ht₃, State.setZ_ea, ← ht₂, State.setZ_ea, eaP]
  obtain e₄ : exec (.vmovdqu32Store (at_ .rdi 0) .xmm4) t₄ = some (t₄.setMem (t₄.mem.writeW P (L ||| G0))) := by
    simp only [exec, eaP₄, hV, State.store512_eq, ite_eq_left wP₄]
  refine WP.block_cons_iff.mpr ⟨_, e₁, WP.block_cons_iff.mpr ⟨_, e₂, WP.block_cons_iff.mpr ⟨_, e₃,
    WP.block_cons_iff.mpr ⟨_, e₄, WP.block_nil ?_⟩⟩⟩⟩
  obtain g₄ : t₄.gpr = t₁.gpr := by rw [← ht₄, ZOp.exec_gpr, ← ht₃, State.setZ_gpr, ← ht₂, State.setZ_gpr]
  obtain m₄ : t₄.mem = s.mem := by rw [← ht₄, ZOp.exec_mem, ← ht₃, State.setZ_mem, ← ht₂, State.setZ_mem, m₁]
  obtain hL' : L = Mem.readW (fun x => if (maskHi c).getLsbD (x - S).toNat then s.mem x else 0) S 512 := by
    rw [← hL, m₁]
  obtain hG' : G0 = s.mem.readW P 512 := by rw [← hG, m₁]
  -- `r10 = 64`, `r8 = 64 ⌊E / 64⌋`.
  obtain h9₅ : (t₄.setMem (t₄.mem.writeW P (L ||| G0))).gpr .r9 = BitVec.ofNat 64 E := by
    rw [State.setMem_gpr, g₄, g₁ _ (by decide) (by decide), h9]
  obtain e₅ : BitVec.ofNat 64 E >>> 6 = BitVec.ofNat 64 (E / 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith), Nat.shiftRight_eq_div_pow]
  obtain e₆ : BitVec.ofNat 64 (E / 64) <<< 6 = BitVec.ofNat 64 (64 * (E / 64)) := by
    rw [shl_ofNat (by omega_arith)]; congr 1; omega_arith
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
    ⟨0, rfl, by omega_arith, by rw [h10], by simp [bytesAt, writeBytes_nil], fun _ _ => rfl, rfl, rfl, ZKeep.refl _ _⟩
  rintro k t ⟨j, rfl, hj, r10, mem, g, rd', wr', z⟩
  obtain hj64 : 64 * j + 64 ≤ 64 * (q - 1) := by omega_arith
  obtain ⟨t', run', mem', r10', zf', g', rd'', wr'', z'⟩ := copy64Step_ok t (i := 64 + 64 * j)
    (by rw [g _ (by decide), hsi]) (by rw [g _ (by decide), hdi]) r10 (by rw [g _ (by decide), h8])
    (by rw [rd', wr', ← Offset.add_add_eq S rfl]; exact in_of_covers64 rd hj64 (by omega_arith))
    (by rw [wr', ← Offset.add_add_eq P rfl]; exact in_of_covers64 wr hj64 (by omega_arith))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  obtain eS : S + BitVec.ofNat 64 (64 + 64 * j) = S' + BitVec.ofNat 64 (64 * j) := (Offset.add_add S 64 (64 * j)).symm
  obtain eD : P + BitVec.ofNat 64 (64 + 64 * j) = D' + BitVec.ofNat 64 (64 * j) := (Offset.add_add P 64 (64 * j)).symm
  obtain hlen : (bytesAt s.mem S' (64 * j)).length = 64 * j := length_bytesAt _ _ _
  obtain hsrc : bytesAt t.mem (S' + BitVec.ofNat 64 (64 * j)) 64 = bytesAt s.mem (S' + BitVec.ofNat 64 (64 * j)) 64 := by
    rw [mem]
    refine bytesAt_frame (writeBytes_frame' s.mem hlen) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact (disj.sub_left (Offset.sub_base S' hj64)).sub_right (Region.sub_prefix (by omega_arith))
  obtain hmem : t'.mem = writeBytes s.mem D' (bytesAt s.mem S' (64 * (j + 1))) := by
    rw [mem', eS, eD, hsrc, mem, show 64 * (j + 1) = 64 * j + 64 by omega_arith, bytesAt_add]
    conv => lhs; rw [show D' + BitVec.ofNat 64 (64 * j) = D' + BitVec.ofNat 64 (bytesAt s.mem S' (64 * j)).length
      by rw [hlen]]
    exact writeBytes_append s.mem D' (bytesAt s.mem S' (64 * j)) (bytesAt s.mem (S' + BitVec.ofNat 64 (64 * j)) 64)
      (by rw [length_bytesAt, length_bytesAt]; omega_arith)
  obtain hz : t'.zf = some (decide (j + 1 = q - 1)) := by
    rw [zf', show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, ofNat_add_ofNat, sub_beq (by omega_arith) (by omega_arith)]
    congr 1; simp only [decide_eq_decide]; omega_arith
  obtain gg : ∀ r, r ≠ .r10 → t'.gpr r = s.gpr r := fun r a => by rw [g' r a, g r a]
  obtain r10'' : t'.gpr .r10 = BitVec.ofNat 64 (64 + 64 * (j + 1)) := by
    rw [r10', show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, ofNat_add_ofNat]; congr 1
  by_cases he : j + 1 = q - 1
  · left
    refine ⟨by simp [eval, hz, he], ?_, by rw [r10'']; congr 1; omega_arith, gg, by rw [rd'', rd'], by rw [wr'', wr'],
      z.trans z'⟩
    rw [hmem, he]
  · right
    refine ⟨by simp [eval, hz, he], q - 1 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, r10'', hmem, gg,
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
  obtain hj := List.mem_range.mp hj
  rw [readW512_byte _ _ hj, ← hf]
  simp only [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega_arith)]
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
  obtain hk : ((s.setReg .rcx (s.gpr .r9)).gpr .rcx).toNat % 64 = E % 64 := by
    rw [gpr_setReg_self, h9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show E < 2 ^ 64 by omega_arith)]
  refine WP.block_append (WP.mono (maskSetup_ok _ hk) fun t₁ ⟨rax₁, g₁, m₁, rd₁, wr₁, z₁⟩ => ?_)
  obtain g₁' : ∀ r, r ≠ .rax → r ≠ .rcx → t₁.gpr r = s.gpr r := fun r a b => by
    rw [g₁ r a]; simp [gpr_setReg, b]
  obtain hA : t₁.ea srcB = S + BitVec.ofNat 64 (64 * q) :=
    ea_idx t₁ .rsi (by rw [g₁' _ (by decide) (by decide), hsi]) (by rw [g₁' _ (by decide) (by decide), h10])
  obtain hB : t₁.ea dstB = P + BitVec.ofNat 64 (64 * q) :=
    ea_idx t₁ .rdi (by rw [g₁' _ (by decide) (by decide), hdi]) (by rw [g₁' _ (by decide) (by decide), h10])
  obtain hk64 : E % 64 < 64 := Nat.mod_lt _ (by decide)
  generalize hV : Mem.readW (fun x => if (BitVec.ofNat 64 (2 ^ (E % 64) - 1)).getLsbD
    (x - (S + BitVec.ofNat 64 (64 * q))).toNat then t₁.mem x else 0) (S + BitVec.ofNat 64 (64 * q)) 512 = V
  obtain hl : t₁.loadMasked512B (S + BitVec.ofNat 64 (64 * q)) (BitVec.ofNat 64 (2 ^ (E % 64) - 1)) = some V := by
    unfold State.loadMasked512B
    rw [bOn_low hk64, ite_eq_left (fun j hj => by
      rw [rd₁, wr₁]; exact r j (List.mem_range.mp hj)), hV]
  generalize ht₂ : t₁.setZ .xmm4 (V.extractLsb' 0 128) (V.extractLsb' 128 128) (V.extractLsb' 256 128)
    (V.extractLsb' 384 128) = t₂
  obtain e₁ : exec (.kLoad8 .rax .xmm4 srcB) t₁ = some t₂ := by
    simp only [exec, hA, rax₁, hl, Option.map_some, ht₂]
  obtain hz : t₂.zmm .xmm4 = V := by rw [← ht₂]; exact zmm_setZ_lanes t₁ .xmm4 V
  obtain w₂ : InRegions t₂.wr (P + BitVec.ofNat 64 (64 * q)) 64 := by
    rw [← ht₂, State.setZ_wr, wr₁]; exact w
  obtain e₂ : exec (.vmovdqu32Store dstB .xmm4) t₂ =
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
  obtain e : a - (P + BitVec.ofNat 64 d) = (a - P) - BitVec.ofNat 64 d := by rw [Offset.sub_add_eq]
  rw [e, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega_arith)]
  have := (a - P).isLt
  split <;> omega_arith

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
  obtain hS : ∀ o, c ≤ o → D - BitVec.ofNat 64 c + BitVec.ofNat 64 o = D + BitVec.ofNat 64 (o - c) := fun o h => by
    rw [show BitVec.ofNat 64 o = BitVec.ofNat 64 c + BitVec.ofNat 64 (o - c) by rw [ofNat_add_ofNat]; congr 1; omega_arith,
      ← BitVec.add_assoc, BitVec.sub_add_cancel]
  funext a
  generalize ho : (a - P).toNat = o
  obtain hoL : o < 2 ^ 64 := ho ▸ (a - P).isLt
  obtain ha : a = P + BitVec.ofNat 64 o := by
    rw [← ho, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  simp only [writeBytes, headBytes, tailBytes, bytesAt, List.length_map, List.length_range]
  rw [toNat_sub_add' a P (show 64 * q < 2 ^ 63 by omega_arith), toNat_sub_add' a P (show 64 < 2 ^ 63 by omega_arith),
    toNat_sub_add' a P (show c < 2 ^ 63 by omega_arith), ho]
  obtain hE : 64 * q ≤ c + n ∧ c + n < 64 * q + 64 := by omega_arith
  by_cases h1 : 64 * q ≤ o
  · by_cases h1' : o - 64 * q < 64
    · simp only [h1, h1', ite_true, show c ≤ o by omega_arith]
      rw [getD_map_range _ _ h1']
      by_cases hk : o - 64 * q < (c + n) % 64
      · simp only [hk, ite_true, show o - c < n by omega_arith]
        rw [getD_map_range _ _ (show o - c < n by omega_arith), Offset.add_add, show 64 * q + (o - 64 * q) = o by omega_arith,
          hS o (by omega_arith)]
      · simp only [hk, ite_false, show ¬o - c < n by omega_arith]
        rw [ha, hz o (by omega_arith) (by omega_arith)]
    · simp only [h1, h1', ite_true, ite_false, show 64 ≤ o by omega_arith, show ¬o - 64 < 64 * (q - 1) by omega_arith,
        show ¬o < 64 by omega_arith, show c ≤ o by omega_arith, show ¬o - c < n by omega_arith]
  · simp only [h1, ite_false, show ¬2 ^ 64 - 64 * q + o < 64 by omega_arith]
    by_cases h3 : 64 ≤ o
    · simp only [h3, ite_true, show o - 64 < 64 * (q - 1) by omega_arith, show c ≤ o by omega_arith, show o - c < n by omega_arith]
      rw [getD_map_range _ _ (show o - 64 < 64 * (q - 1) by omega_arith), getD_map_range _ _ (show o - c < n by omega_arith),
        Offset.add_add, show 64 + (o - 64) = o by omega_arith, hS o (by omega_arith)]
    · simp only [h3, ite_false, show ¬2 ^ 64 - 64 + o < 64 * (q - 1) by omega_arith, show o < 64 by omega_arith, ite_true]
      rw [getD_map_range _ _ (show o < 64 by omega_arith)]
      by_cases hco : c ≤ o
      · simp only [hco, ite_true, show o - c < n by omega_arith]
        rw [getD_map_range _ _ (show o - c < n by omega_arith), hS o hco, hz o hco (by omega_arith)]
        simp
      · simp only [hco, ite_false, show ¬2 ^ 64 - c + o < n by omega_arith]
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
    gArgs_ok (t := lead + na) s h.rdi h.rsi h.rcx h.rax (by omega_arith)
  generalize ht : lead + na = t at *
  generalize hc : 16 * (t % 4) = c at *
  generalize hP : W + BitVec.ofNat 64 (512 + 16 * (t - t % 4)) = P at *
  obtain hc1 : 16 ≤ c ∧ c ≤ 48 := by omega_arith
  obtain hq3 : 3 ≤ (c + n) / 64 := by omega_arith
  obtain hqP : 16 * (t - t % 4) + 64 * ((c + n) / 64) + 64 ≤ 512 := by omega_arith
  generalize hq : (c + n) / 64 = q at hq3 hqP
  obtain hqE : 64 * q ≤ c + n ∧ c + n < 64 * q + 64 := by omega_arith
  obtain hPo : ∀ o, P + BitVec.ofNat 64 o = W + BitVec.ofNat 64 (512 + 16 * (t - t % 4) + o) := fun o => by
    rw [← hP, Offset.add_add]
  obtain hS : ∀ o, c ≤ o → D - BitVec.ofNat 64 c + BitVec.ofNat 64 o = D + BitVec.ofNat 64 (o - c) := fun o hco => by
    rw [show BitVec.ofNat 64 o = BitVec.ofNat 64 c + BitVec.ofNat 64 (o - c) by rw [ofNat_add_ofNat]; congr 1; omega_arith,
      ← BitVec.add_assoc, BitVec.sub_add_cancel]
  obtain inW : ∀ {o k : Nat}, 512 + 16 * (t - t % 4) + o + k ≤ 2560 → InRegions s.wr (P + BitVec.ofNat 64 o) k :=
    fun hk => by rw [hPo]; exact in_off hw hk (by decide)
  obtain inW0 : InRegions s.wr P 64 := by
    have := inW (o := 0) (k := 64) (by omega_arith)
    rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
  obtain subW : ∀ {o k : Nat}, 512 + 16 * (t - t % 4) + o + k ≤ 2560 →
      Region.Sub ⟨P + BitVec.ofNat 64 o, k⟩ ⟨W, 2560⟩ := fun hk => by rw [hPo]; exact Offset.sub_base W hk
  obtain subW0 : Region.Sub ⟨P, 64⟩ ⟨W, 2560⟩ := by
    have := subW (o := 0) (k := 64) (by omega_arith)
    rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
  obtain subD : ∀ {o k : Nat}, c ≤ o → o - c + k ≤ n →
      Region.Sub ⟨D - BitVec.ofNat 64 c + BitVec.ofNat 64 o, k⟩ ⟨D, n⟩ := fun hco hk => by
    rw [hS _ hco]; exact Offset.sub_base D hk
  obtain rdD : ∀ {o : Nat}, c ≤ o → o - c < n → InRegions (s.rd ++ s.wr) (D - BitVec.ofNat 64 c + BitVec.ofNat 64 o) 1 :=
    fun hco hk => by rw [hS _ hco]; exact in_of_covers hrd hk (by omega_arith)
  unfold copyG
  -- The first group.
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨t₀, run₀, WP.mono (gHead_ok t₀ (c := c) (E := c + n)
    (by omega_arith) (by omega_arith) si₀ di₀ r8₀ r9₀
    (fun j hj hj' => by rw [rd₀, wr₀]; exact rdD hj (by omega_arith))
    (by rw [rd₀, wr₀]; exact in_left inW0) (by rw [wr₀]; exact inW0))
    fun t₁ ⟨m₁, r10₁, r8₁, g₁, rd₁, wr₁, z₁⟩ => ?_⟩))
  rw [hq] at r8₁
  obtain gg₁ : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rsi → r ≠ .rdi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → t₁.gpr r = s.gpr r :=
    fun r a b c' d e f g' => by rw [g₁ r a b e g', g₀ r d e c' f]
  obtain si₁ : t₁.gpr .rsi = D - BitVec.ofNat 64 c := by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), si₀]
  obtain di₁ : t₁.gpr .rdi = P := by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), di₀]
  obtain r9₁ : t₁.gpr .r9 = BitVec.ofNat 64 (c + n) := by
    rw [g₁ _ (by decide) (by decide) (by decide) (by decide), r9₀]
  -- The whole groups.
  refine WP.seq (WP.mono (gLoop_ok t₁ (q := q) (by omega_arith) (by omega_arith) si₁ di₁ r10₁ r8₁
    (by
      rw [rd₁, wr₁, rd₀, wr₀]
      exact Covers.trans (Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨D, n⟩, List.mem_singleton_self _, 64 - c, hS 64 (by omega_arith), by dsimp only; omega_arith⟩) hrd)
    (by
      rw [wr₁, wr₀]
      exact Covers.trans (Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨W, 2560⟩, List.mem_singleton_self _, 512 + 16 * (t - t % 4) + 64, hPo 64, by dsimp only; omega_arith⟩) hw)
    ((hdisj.sub_left (subD (by omega_arith) (by omega_arith))).sub_right (subW (by omega_arith))))
    fun t₂ ⟨m₂, r10₂, g₂, rd₂, wr₂, z₂⟩ => ?_)
  obtain si₂ : t₂.gpr .rsi = D - BitVec.ofNat 64 c := by rw [g₂ _ (by decide), si₁]
  obtain di₂ : t₂.gpr .rdi = P := by rw [g₂ _ (by decide), di₁]
  obtain r9₂ : t₂.gpr .r9 = BitVec.ofNat 64 (c + n) := by rw [g₂ _ (by decide), r9₁]
  -- The last group.
  refine WP.mono (gTail_ok t₂ (q := q) (E := c + n) (by omega_arith) si₂ di₂ r10₂ r9₂
    (fun j hj => by
      rw [rd₂, wr₂, rd₁, wr₁, rd₀, wr₀, Offset.add_add]
      exact rdD (by omega_arith) (by omega_arith))
    (by rw [wr₂, wr₁, wr₀]; exact inW (by omega_arith)))
    fun t₃ ⟨m₃, g₃, rd₃, wr₃, z₃⟩ => ?_
  -- The memory.
  obtain f₁ : Frame [⟨P, 64⟩] s.mem t₁.mem := by
    rw [m₁, m₀]; exact writeBytes_frame' _ (by simp [headBytes])
  obtain f₂ : Frame [⟨P + BitVec.ofNat 64 64, 64 * (q - 1)⟩] t₁.mem t₂.mem := by
    rw [m₂]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  obtain f₁₂ : Frame [⟨P, 64⟩, ⟨P + BitVec.ofNat 64 64, 64 * (q - 1)⟩] s.mem t₂.mem :=
    (f₁.mono (by simp)).trans (f₂.mono (by simp))
  obtain dD : ∀ {o k : Nat}, c ≤ o → o - c + k ≤ n → ∀ r ∈ [(⟨P, 64⟩ : Region), ⟨P + BitVec.ofNat 64 64, 64 * (q - 1)⟩],
      (⟨D - BitVec.ofNat 64 c + BitVec.ofNat 64 o, k⟩ : Region).Disjoint r := fun hco hk r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hdisj.sub_left (subD hco hk)).sub_right subW0
    · exact (hdisj.sub_left (subD hco hk)).sub_right (subW (by omega_arith))
  obtain hmid : bytesAt t₁.mem (D - BitVec.ofNat 64 c + BitVec.ofNat 64 64) (64 * (q - 1)) =
      bytesAt s.mem (D - BitVec.ofNat 64 c + BitVec.ofNat 64 64) (64 * (q - 1)) :=
    bytesAt_frame f₁ (fun r hr => dD (by omega_arith) (by omega_arith) r (by simp at hr; simp [hr])) (by omega_arith)
  obtain htail : tailBytes t₂.mem (D - BitVec.ofNat 64 c + BitVec.ofNat 64 (64 * q)) ((c + n) % 64) =
      tailBytes s.mem (D - BitVec.ofNat 64 c + BitVec.ofNat 64 (64 * q)) ((c + n) % 64) :=
    tailBytes_frame f₁₂ (dD (by omega_arith) (by omega_arith)) (by omega_arith)
  obtain f₃ : Frame [⟨P + BitVec.ofNat 64 (64 * q), 64⟩] t₂.mem t₃.mem := by
    rw [m₃]; exact writeBytes_frame' _ (by simp [tailBytes])
  refine ⟨?_, ?_, fun r a b c' d e f g' => by rw [g₃ r a b, g₂ r g', gg₁ r a b c' d e f g'],
    by rw [rd₃, rd₂, rd₁, rd₀], by rw [wr₃, wr₂, wr₁, wr₀], ?_⟩
  · rw [m₃, htail, m₂, hmid, m₁, m₀]; rfl
  · refine ((f₁₂.mono (rs' := [⟨P, 64⟩, ⟨P + BitVec.ofNat 64 64, 64 * (q - 1)⟩,
      ⟨P + BitVec.ofNat 64 (64 * q), 64⟩]) (by simp)).trans (f₃.mono (by simp))).sub fun r hr => ?_
    obtain hG : ∀ {o k : Nat}, 16 * (t - t % 4) + o + k ≤ 512 →
        Region.Sub ⟨P + BitVec.ofNat 64 o, k⟩ ⟨W + BitVec.ofNat 64 512, 512⟩ := fun {o k} hk => by
      rw [hPo, Nat.add_assoc, ← Offset.add_add W 512 (16 * (t - t % 4) + o)]
      exact Offset.sub_base _ hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    rcases hr with rfl | rfl | rfl
    · have := hG (o := 0) (k := 64) (by omega_arith)
      rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
    · exact hG (by omega_arith)
    · exact hG (by omega_arith)
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
  obtain e₁ : BitVec.ofNat 64 n >>> 6 = BitVec.ofNat 64 (n / 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith), Nat.shiftRight_eq_div_pow]
  obtain e₂ : BitVec.ofNat 64 (n / 64) <<< 6 = BitVec.ofNat 64 (64 * (n / 64)) := by
    rw [shl_ofNat (by omega_arith)]; congr 1; omega_arith
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
  obtain ⟨u₂, run₂, zf₂, cf₂, g₂, m₂, rd₂, wr₂⟩ := cmpImm_ok u₁ .r8 r8₁ (by omega_arith) (show 64 < 2 ^ 31 by decide)
  obtain z₂ : ∀ r l, u₂.zlane r l = u₁.zlane r l := by
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
    (na := na) s h15 hw hlead hna hD hn (by omega_arith)
  obtain cp : CopyPre u₁ D (W + BitVec.ofNat 64 (512 + 16 * (lead + na))) n := ⟨si₁, di₁, cx₁, by omega_arith,
    by rw [rd₁, wr₁]; exact hrd,
    by rw [wr₁]; exact Covers.trans (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨W, 2560⟩, List.mem_singleton_self _, 512 + 16 * (lead + na), rfl, by dsimp only; omega_arith⟩) hw,
    hdisj.sub_right (Offset.sub_base W (by omega_arith))⟩
  -- What `copyBytes`'s copy leaves, as the theorem states it.
  obtain fin : ∀ w : State, CopyPost u₁ D (W + BitVec.ofNat 64 (512 + 16 * (lead + na))) n w →
      Frame [⟨W + BitVec.ofNat 64 512, 512⟩] s.mem w.mem ∧
      ((∀ j, 16 * (lead + na) ≤ j → j < 512 → s.mem (W + BitVec.ofNat 64 (512 + j)) = 0) →
        w.mem = writeBytes s.mem (W + BitVec.ofNat 64 (512 + 16 * (lead + na))) (bytesAt s.mem D n)) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rsi → r ≠ .rdi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → w.gpr r = s.gpr r) ∧
      w.rd = s.rd ∧ w.wr = s.wr ∧ ZKeep [.xmm4, .xmm6] s w := fun w ⟨m₂, g₂, rd₂, wr₂, z₂⟩ => by
    obtain hm : w.mem = writeBytes s.mem (W + BitVec.ofNat 64 (512 + 16 * (lead + na))) (bytesAt s.mem D n) := by
      rw [m₂, m₁]
    refine ⟨by
        rw [hm]
        refine (writeBytes_frame' _ (length_bytesAt _ _ _)).sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
        simp only [List.mem_singleton] at hr; subst hr
        rw [← Offset.add_add W 512 (16 * (lead + na))]
        exact Offset.sub_base _ (by omega_arith),
      fun _ => hm, fun r a b c' d e f g' => by rw [g₂ r a e g', g₁ r d c' b],
      by rw [rd₂, rd₁], by rw [wr₂, wr₁], ?_⟩
    exact (ZKeep.mono (rs := []) (fun r _ l _ => by rw [z₁ r l]) (by simp)).trans (z₂.mono (by simp))
  -- The loop and the masked move, from a state with the setup's registers.
  obtain viaLoop : ∀ v : State, v.gpr .r10 = BitVec.ofNat 64 0 → v.gpr .r8 = BitVec.ofNat 64 (64 * (n / 64)) →
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
  refine WP.of_runBlock ⟨u₁, run₁, WP.mono (copyHdr_ok u₁ cx₁ (by omega_arith))
    fun u₂ ⟨r10₂, r8₂, cf₂, zf₂, g₂, m₂, rd₂, wr₂, z₂⟩ => ?_⟩
  obtain gq : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → u₂.gpr r = u₁.gpr r := fun r _ b c => g₂ r b c
  obtain zq : ZKeep [.xmm4] u₁ u₂ := z₂.mono (by simp)
  -- Fewer than 64 bytes: the masked move alone.
  refine WP.ite (decide (64 * (n / 64) < 64)) (by simp only [eval, cf₂]) (fun hb => ?_) (fun hb => ?_)
  · have hq : 64 * (n / 64) = 0 := by have := of_decide_eq_true hb; omega_arith
    exact WP.mono (copyTail_ok u₁ cp u₂ ⟨by rw [r10₂, hq], by rw [m₂, hq]; simp [bytesAt, writeBytes_nil],
      gq, rd₂, wr₂, zq⟩) fin
  obtain h64 : 64 ≤ n := by have := of_decide_eq_false hb; omega_arith
  -- 64 to 127 bytes: the loop, once.
  refine WP.ite (decide (64 * (n / 64) = 64)) (by simp only [eval, zf₂]) (fun he => ?_) (fun he => ?_)
  · exact viaLoop u₂ r10₂ r8₂ gq m₂ rd₂ wr₂ zq (by omega_arith)
  obtain h128 : 128 ≤ n := by have := of_decide_eq_false he; omega_arith
  -- `n` compared with 192.
  obtain ⟨u₃, run₃, -, cf₃, g₃, m₃, rd₃, wr₃⟩ := cmpImm_ok u₂ .rcx
    (by rw [g₂ _ (by decide) (by decide), cx₁]) (by omega_arith) (show 192 < 2 ^ 31 by decide)
  obtain z₃ : ∀ r l, u₃.zlane r l = u₂.zlane r l := by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, imm] at run₃
    cases run₃; intro r l; rfl
  obtain gq₃ : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → u₃.gpr r = u₁.gpr r := fun r a b c => by rw [g₃, gq r a b c]
  obtain zq₃ : ZKeep [.xmm4] u₁ u₃ := zq.trans (fun r _ l _ => z₃ r l)
  refine WP.seq (WP.of_runBlock ⟨u₃, run₃, ?_⟩)
  refine WP.iteCold_iff.mpr (WP.ite (!decide (n < 192)) (by show u₃.cf.map _ = _; rw [cf₃]; rfl)
    (fun hb => ?_) (fun hb => ?_))
  rotate_left
  · exact viaLoop u₃ (by rw [g₃, r10₂]) (by rw [g₃, r8₂]) gq₃ (by rw [m₃, m₂]) (by rw [rd₃, rd₂])
      (by rw [wr₃, wr₂]) zq₃ (by omega_arith)
  obtain h192 : 192 ≤ n := by simpa using hb
  -- `t = lead + na` tested for a multiple of 4, from `rdi`.
  refine WP.seq (WP.mono (gShift_ok u₃ (W := W) (t := lead + na)
    (by rw [g₃, g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide), h15])
    (by rw [g₃, g₂ _ (by decide) (by decide), di₁]) (by omega_arith))
    fun u₄ ⟨ax₄, zf₄, g₄, m₄, rd₄, wr₄, z₄⟩ => ?_)
  obtain gq₄ : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → u₄.gpr r = u₁.gpr r := fun r a b c => by
    rw [g₄ r a, gq₃ r a b c]
  refine WP.ite (decide ((lead + na) % 4 = 0)) (by simp only [eval, zf₄]) (fun hz => ?_) (fun hz => ?_)
  · exact viaLoop u₄ (by rw [g₄ _ (by decide), g₃, r10₂]) (by rw [g₄ _ (by decide), g₃, r8₂]) gq₄
      (by rw [m₄, m₃, m₂]) (by rw [rd₄, rd₃, rd₂]) (by rw [wr₄, wr₃, wr₂])
      (zq₃.trans (fun r _ l _ => z₄ r l)) (by omega_arith)
  obtain hsh : (lead + na) % 4 ≠ 0 := by simpa using hz
  obtain m₄s : u₄.mem = s.mem := by rw [m₄, m₃, m₂, m₁]
  obtain rd₄s : u₄.rd = s.rd := by rw [rd₄, rd₃, rd₂, rd₁]
  obtain wr₄s : u₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, wr₁]
  obtain g₄s : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rsi → r ≠ .rdi → r ≠ .r8 → r ≠ .r10 → u₄.gpr r = s.gpr r :=
    fun r a b c d e f => by rw [gq₄ r a e f, g₁ r d c b]
  obtain z₄s : ZKeep [] s u₄ := fun r _ l _ => by rw [z₄, z₃, z₂ r (by simp) l (by omega_arith), z₁]
  refine WP.mono (copyG_ok u₄ ⟨by rw [wr₄s]; exact hw,
    by rw [g₄ _ (by decide), g₃, g₂ _ (by decide) (by decide), di₁],
    by rw [g₄ _ (by decide), g₃, g₂ _ (by decide) (by decide), si₁],
    by rw [g₄ _ (by decide), g₃, g₂ _ (by decide) (by decide), cx₁], ax₄, h192, hsh, hfit,
    by rw [rd₄s, wr₄s]; exact hrd, hdisj⟩)
    fun s' ⟨m', f', g', rd', wr', z'⟩ => ⟨by rw [← m₄s]; exact f', fun hz => by
      rw [m', m₄s, copyG_mem s.mem D _ (by omega_arith) rfl (by omega_arith) (by omega_arith) (fun o hco ho => ?_)]
      · rw [Offset.add_add, show 512 + 16 * (lead + na - (lead + na) % 4) + 16 * ((lead + na) % 4) =
          512 + 16 * (lead + na) by omega_arith]
      · rw [Offset.add_add, Nat.add_assoc]
        exact hz _ (by omega_arith) (by omega_arith),
      fun r a b c' d e f g'' => by rw [g' r a b c' d e f g'', g₄s r a b c' d e g''],
      by rw [rd', rd₄s], by rw [wr', wr₄s], (ZKeep.mono (rs := []) z₄s (by simp)).trans z'⟩

end VG.Proof.AesGcm.X86_64.Short

end

end

/-!
# AES-GCM's short path on x86-64: `open`

Untrusted: everything here is checked by Lean. After `front_ok`, the
ciphertext is copied to `G` (`copyC`), the lengths block ends `G` (`lens`),
`GHASH` of `G` (`ghash`) and the tag at `W + 112` (`tagK uO`), compared
with the received one (`recv`, `cmp uO`, as `open` does), and the data is
decrypted in place only if they match (`xorText false`): `openChk_ok` up to
the comparison, `openTail_ok` after it.
With `shortStart_ok` and `front_ok`, `openShort_ok`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt blocks inc32 zeros ctxH ctxCiph gctr ghash ghashFrom ofBytes toBytes)
open VG.Proof.Gcm (padded lensBlock)

/-- What `open`'s short path leaves: the tag compared and the data decrypted
if it matches. -/
abbrev OpenPost (s₀ : State) (Ctx W SP D : Addr) (n R al t : Nat) (Tp : Addr) (H J : Block) (a : List Byte)
    (s : State) : Prop :=
  Env Ctx (W + BitVec.ofNat 64 16) W SP s ∧ SavedAt s.mem W s₀ ∧
    Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP 24] s₀.mem s.mem ∧
    let T := toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt s₀.mem D n)))) [ofBytes (lensBlock al n)] ^^^
      ctxCiph s₀.mem Ctx R J)
    s.gpr .rax = BitVec.ofNat 64 (if T.take t = bytesAt s₀.mem Tp t then 1 else 0) ∧
    bytesAt s.mem D n = if T.take t = bytesAt s₀.mem Tp t then gctr (ctxCiph s₀.mem Ctx R) (inc32 J) (bytesAt s₀.mem D n)
      else bytesAt s₀.mem D n

/-- `SM.keep` for a step that keeps the environment. -/
theorem SM.keepE {s₀ : State} {Ctx W SP A D : Addr} {R al n : Nat} {J : Block} {tl : BitVec 64} {s s' : State}
    (S : SM s₀ Ctx W SP A D R al n J tl s) (dD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {rs : List Region} (f : Frame rs s.mem s'.mem) (hrs : ∀ r ∈ rs, Wk W D n r)
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    SM s₀ Ctx W SP A D R al n J tl s' :=
  S.keep dD f hrs (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [he.r13, S.env.r13]
    · rw [he.r14, S.env.r14]
    · rw [he.r15, S.env.r15]
    · rw [he.rsp, S.env.rsp]) hrd hwr

theorem OutWDS.frame3 {W D SP : Addr} {n : Nat} {X : Region} (h : OutWDS W D SP n X) :
    ∀ r ∈ [(⟨W, 2560⟩ : Region), ⟨D, n⟩, below SP 24], X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h _ (.inl fun _ h => h)
  · exact h _ (.inr (.inl fun _ h => h))
  · exact h _ (.inr (.inr fun _ h => h))

/-- The comparison's result: 1 if the first `t` bytes of the tag of the
ciphertext at `D` are the received ones at `Tp`, 0 if not. -/
abbrev openK (s₀ : State) (Ctx A D : Addr) (R al n : Nat) (J : Block) (t : Nat) (Tp : Addr) : Nat :=
  if (toBytes (ghashFrom (ctxH s₀.mem Ctx) (ghash (ctxH s₀.mem Ctx)
      (blocks (padded (bytesAt s₀.mem A al) (bytesAt s₀.mem D n)))) [ofBytes (lensBlock al n)] ^^^
      ctxCiph s₀.mem Ctx R J)).take t = bytesAt s₀.mem Tp t then 1 else 0

/-- After `openChk`: the comparison's result `k` at `W + 216` and in ZF, the
data and the keystream after `K[0]` as `front_ok` left them. -/
structure OpenChk (s₀ : State) (Ctx W SP A D : Addr) (R al n : Nat) (J : Block) (t k : Nat) (s : State) :
    Prop where
  sm : SM s₀ Ctx W SP A D R al n J (BitVec.ofNat 64 t) s
  zf : s.zf = some (decide (k = 0))
  aux : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k
  dat : bytesAt s.mem D n = bytesAt s₀.mem D n
  ks : ∀ b, 16 * b < n → blockAt s.mem (W + BitVec.ofNat 64 1040 + BitVec.ofNat 64 (16 * b)) =
    ctxCiph s₀.mem Ctx R (Nat.repeat inc32 (b + 1) J)

/-- After `front_ok`: the ciphertext into `G`, the tag and the comparison. -/
theorem openChk_ok (hF : ShortFacts) {gh : Prog isa} {tm : Mem → Mem} {k : Nat} {s₀ s : State}
    {Ctx W SP Np A D : Addr} {nl al n R : Nat} {J : Block} {t : Nat}
    {Tp : Addr} (hgh : GhFrom gh tm s₀ Ctx W SP) (htv : TabView tm W D n)
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (hal5 : al < 512) (hn5 : n < 512)
    (h32 : nb16 al + nb16 n < 32)
    (F : Front tm s₀ Ctx W SP A D R al n J (BitVec.ofNat 64 t) (bytesAt s₀.mem A al) s) (h1 : 1 ≤ t) (h16 : t ≤ 16)
    (hTa : s₀.mem.readW (SP + BitVec.ofNat 64 24) 64 = Tp)
    (hTar : InRegions (s₀.rd ++ s₀.wr) (SP + BitVec.ofNat 64 24) 8) (hTr : Covers [⟨Tp, t⟩] (s₀.rd ++ s₀.wr))
    (oT : OutWDS W D SP n ⟨Tp, t⟩) (oA : OutWDS W D SP n ⟨SP + BitVec.ofNat 64 24, 8⟩) :
    WP isa (openChk gh) s (OpenChk s₀ Ctx W SP A D R al n J t (openK s₀ Ctx A D R al n J t Tp)) := by
  have L := C.lay
  have dD := C.dE
  have h32' := h32
  simp only [nb16] at h32'
  obtain hg1 : 1 ≤ grp al n := by simp only [grp, nb16]; omega_arith
  obtain hg8 : grp al n ≤ 8 := by simp only [grp, nb16]; omega_arith
  obtain hmp : 4 * grp al n = (4 * grp al n - (nb16 al + nb16 n + 1)) + nb16 al + nb16 n + 1 := by
    simp only [grp, nb16]; omega_arith
  obtain hlead : 4 * grp al n - (nb16 al + nb16 n + 1) < 4 := by simp only [grp, nb16]; omega_arith
  obtain hna : al ≤ 16 * nb16 al ∧ 16 * nb16 al < al + 16 := by simp only [nb16]; omega_arith
  obtain hnc : n ≤ 16 * nb16 n ∧ 16 * nb16 n < n + 16 := by simp only [nb16]; omega_arith
  have S := F.sm
  obtain dWD : ∀ {d j : Nat}, d + j ≤ 2560 → (⟨D, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, j⟩ :=
    fun h => dD.sub_right (Lay.wSub h)
  -- The ciphertext copied to `G`.
  obtain hz : ∀ j, 16 * (4 * grp al n - (nb16 al + nb16 n + 1) + nb16 al) ≤ j → j < 512 →
      s.mem (W + BitVec.ofNat 64 (512 + j)) = 0 := by
    intro j hj hj5
    obtain ⟨mZ, hZ, fK⟩ := F.gz
    obtain hx : W + BitVec.ofNat 64 (512 + j) = W + BitVec.ofNat 64 512 + BitVec.ofNat 64 j := (Offset.add_add _ _ _).symm
    obtain e₁ : bytesAt s.mem (W + BitVec.ofNat 64 (512 + j)) 1 =
        bytesAt (writeBytes mZ (W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1))))
          (bytesAt s₀.mem A al)) (W + BitVec.ofNat 64 (512 + j)) 1 :=
      bytesAt_frame fK (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide)
    obtain e₂ : bytesAt (writeBytes mZ (W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1))))
          (bytesAt s₀.mem A al)) (W + BitVec.ofNat 64 (512 + j)) 1 = bytesAt mZ (W + BitVec.ofNat 64 (512 + j)) 1 :=
      bytesAt_frame (writeBytes_frame' _ (length_bytesAt _ _ _)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide)
    obtain e₃ : bytesAt mZ (W + BitVec.ofNat 64 (512 + j)) 1 = zeros 1 := by
      rw [hx]; exact bytesAt_zeros hZ (by omega_arith)
    have := e₁.trans (e₂.trans e₃)
    rw [bytesAt_one] at this
    simpa [zeros] using this
  obtain dW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩ := by
    have := dWD (d := 0) (j := 2560) (by decide)
    simpa only [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using this
  refine WP.seq (WP.mono (copyCG_ok s (lead := 4 * grp al n - (nb16 al + nb16 n + 1)) (na := nb16 al) (n := n)
    S.env.r15 S.env.perm.w S.r296 S.r272 S.r200 S.r208 (by omega_arith)
    (by rw [S.rd, S.wr]; exact C.data.ok.rd) dW)
    fun s₂ ⟨_, mE₂, g₂, rd₂, wr₂, z₂⟩ => ?_)
  obtain m₂ := mE₂ hz
  rw [F.dat] at m₂
  obtain fC : Frame [⟨W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1) + nb16 al)), n⟩]
      s.mem s₂.mem := by
    rw [m₂]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  obtain S₂ := S.keep dD fC (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact wk_G (by omega_arith))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
    rd₂ wr₂
  -- The lengths block.
  refine WP.seq ?_
  obtain ⟨s₃, run₃, fL, hL, g₃, rd₃, wr₃, z₃⟩ := lensG_ok s₂ S₂.env.r15 S₂.env.perm.w S₂.r288 (by omega_arith) (by omega_arith)
    S₂.r184 S₂.r208 (by omega_arith) (by omega_arith)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  obtain S₃ := S₂.keep dD fL (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl (Offset.sub W (by omega_arith) (by omega_arith))))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide)) rd₃ wr₃
  -- `GHASH` of `G`.
  obtain zz : ∀ r, r ≠ .xmm4 → r ≠ .xmm6 → ∀ l < 4, s₃.zlane r l = s.zlane r l := fun r h h' l hl => by
    rw [z₃ r l, z₂ r (by simp [h, h']) l hl]
  refine WP.seq (WP.mono (hgh s₃ S₃.env S₃.r288 hg1 hg8
    (fun l hl => by rw [zz _ (by decide) (by decide) l hl, F.z0 l hl]) (fun l hl => by rw [zz _ (by decide) (by decide) l hl, F.z1 l hl])
    S₃.rd S₃.wr)
    fun s₄ ⟨y0, y1, g₄, m₄, rd₄, wr₄, z₄⟩ => ?_)
  obtain S₄ := S₃.keep dD (rs := []) (by rw [m₄]; exact Frame.refl _ _) (by simp)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₄ _ (by decide) (by decide) (by decide)) rd₄ wr₄
  -- The tag, at `W + 112`.
  obtain x0 : s₄.xmm .xmm0 = revMask := by
    rw [show s₄.xmm .xmm0 = s₄.zlane .xmm0 0 from rfl, z₄ _ (by decide) 0 (by decide), zz _ (by decide) (by decide) 0 (by decide),
      F.z0 0 (by decide)]
  refine WP.seq (WP.block_append ?_)
  obtain ⟨s₅, run₅, tag₅, fU, g₅, rd₅, wr₅⟩ := tagK_ok (o := 112) s₄ S₄.env.r15 S₄.env.perm.w (by decide) x0
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  obtain S₅ := S₄.keep dD fU (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inr (.inr (.inl fun _ h => h))))
    (fun r _ => by rw [g₅]) rd₅ wr₅
  obtain hT₅ : bytesAt s₅.mem (W + BitVec.ofNat 64 112) 16 =
      toBytes (ghashFrom (ctxH s₀.mem Ctx) (ghash (ctxH s₀.mem Ctx)
        (blocks (padded (bytesAt s₀.mem A al) (bytesAt s₀.mem D n)))) [ofBytes (lensBlock al n)] ^^^
        ctxCiph s₀.mem Ctx R J) := by
    have Ftab := F.tab
    have Fks := F.ks
    obtain ⟨mZ, hZ, fK⟩ := F.gz
    generalize hl : 4 * grp al n - (nb16 al + nb16 n + 1) = lead at *
    generalize hna' : nb16 al = na at *
    generalize hnc' : nb16 n = nc at *
    generalize hg' : grp al n = g at *
    obtain hmp' : 4 * g = lead + na + nc + 1 := by omega_arith
    obtain T₃ : TabOk (tm s₃.mem) (W + BitVec.ofNat 64 1536) (ctxH s₀.mem Ctx) g :=
      TabOk.view htv (TabOk.view htv Ftab hg8 fC fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨Offset.disjoint W (.inr (by omega_arith)) (by omega_arith) (by omega_arith),
          .inl (Offset.sub_base W (by omega_arith))⟩) hg8 fL fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨Offset.disjoint W (.inr (by omega_arith)) (by omega_arith) (by omega_arith),
          .inl (Offset.sub_base W (by omega_arith))⟩
    obtain hGv : blocksAt (tm s₃.mem) (W + BitVec.ofNat 64 512) (4 * g) =
        blocksAt s₃.mem (W + BitVec.ofNat 64 512) (4 * g) := by
      rw [Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq, bytesAt_frame (htv.out s₃.mem) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by omega_arith)]
    obtain hx2 : s₄.xmm .xmm2 = ghashFrom (ctxH s₀.mem Ctx) 0 (blocksAt s₃.mem (W + BitVec.ofNat 64 512) (4 * g)) := by
      rw [show s₄.xmm .xmm2 = s₄.zlane .xmm2 0 from rfl, y0, hF.ghash T₃, hGv]
    obtain hK₀ : blockAt s₄.mem (W + BitVec.ofNat 64 1024) = ctxCiph s₀.mem Ctx R J := by
      rw [m₄, blockAt_frame fL (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint W (.inr (by omega_arith)) (by omega_arith) (by omega_arith)),
        blockAt_frame fC (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint W (.inr (by omega_arith)) (by omega_arith) (by omega_arith))]
      have := Fks 0 (by omega_arith)
      simpa [Nat.repeat] using this
    obtain hcl : (bytesAt s₀.mem D n).length = n := length_bytesAt _ _ _
    obtain hlay := gLayout (G := W + BitVec.ofNat 64 512) (lead := lead) (na := na) (nc := nc)
      (a := bytesAt s₀.mem A al) (c := bytesAt s₀.mem D n) (lens := lensBlock al n) (mZ := mZ) (mK := s.mem)
      (mX := s₂.mem) (mL := s₃.mem) (by rw [length_bytesAt]; omega_arith) (by omega_arith) (by omega_arith) hZ
      (by rw [add_ofNat_ofNat]; exact fK)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide))
      (rsX := [⟨W + BitVec.ofNat 64 (512 + 16 * (lead + na)), n⟩]) fC
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact .inl (by rw [hcl, add_ofNat_ofNat]))
      (by
        rw [m₂, add_ofNat_ofNat]
        exact bytesAt_writeBytes_self _ _ _ (by omega_arith))
      (by rw [add_ofNat_ofNat, show 512 + 16 * (lead + na + nc) = 496 + 16 * (4 * g) by omega_arith]; exact fL)
      (by rw [add_ofNat_ofNat, show 512 + 16 * (lead + na + nc) = 496 + 16 * (4 * g) by omega_arith]; exact hL)
    obtain hpad := padded_layout (bytesAt s₀.mem A al) (bytesAt s₀.mem D n)
    rw [length_bytesAt, hcl, hna', hnc'] at hpad
    rw [length_bytesAt, hcl] at hlay
    obtain hG : bytesAt s₃.mem (W + BitVec.ofNat 64 512) (16 * (4 * g)) =
        zeros (16 * lead) ++ padded (bytesAt s₀.mem A al) (bytesAt s₀.mem D n) ++
          lensBlock (bytesAt s₀.mem A al).length (bytesAt s₀.mem D n).length := by
      rw [hmp', hlay, ← hpad, length_bytesAt, hcl]; simp only [List.append_assoc]
    have t5 : blockAt s₅.mem (W + BitVec.ofNat 64 112) = s₄.xmm .xmm2 ^^^ blockAt s₄.mem (W + BitVec.ofNat 64 1024) :=
      tag₅
    rw [bytesAt_toBytes']
    refine congrArg toBytes ?_
    rw [t5, hx2, hK₀, Proof.Gcm.blocksAt_eq, hG, gBlocks, List.append_assoc, ghashFrom_zeros,
      Proof.Gcm.ghashFrom_append, length_bytesAt, hcl]
    rfl
  -- The tag's length and address.
  obtain q₁ := S₅.env.perm.wR (show 224 + 8 ≤ 2560 by decide)
  obtain q₂ : InRegions (s₅.rd ++ s₅.wr) (SP + BitVec.ofNat 64 24) 8 := by rw [S₅.rd, S₅.wr]; exact hTar
  obtain hTa₅ : s₅.mem.readW (SP + BitVec.ofNat 64 24) 64 = Tp := by
    rw [S₅.frame.readW (r := ⟨SP + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _) (OutWDS.frame3 oA) (by decide), hTa]
  have htl₅ := S₅.r224
  obtain ⟨s₆, run₆, hbx₆, hsi₆, hg₆, hm₆, hrd₆, hwr₆⟩ : ∃ s₆, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO)),
      .mov .rsi (.mem (at_ .rsp 24))] s₅ = some s₆ ∧ s₆.gpr .rbx = BitVec.ofNat 64 t ∧ s₆.gpr .rsi = Tp ∧
      (∀ r, r ≠ .rbx → r ≠ .rsi → s₆.gpr r = s₅.gpr r) ∧ s₆.mem = s₅.mem ∧ s₆.rd = s₅.rd ∧ s₆.wr = s₅.wr := by
    refine ⟨_, by xrun [S₅.env.r15, S₅.env.rsp, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, htl₅]
    · simp [gpr_setReg, hTa₅]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  obtain S₆ := S₅.keep dD (rs := []) (by rw [hm₆]; exact Frame.refl _ _) (by simp)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₆ _ (by decide) (by decide)) hrd₆ hwr₆
  -- The received tag, padded, and the comparison.
  refine WP.seq (WP.mono (WP.with_rdwr (recv_ok S₆.env hbx₆ h1 h16 hsi₆
    (by rw [S₆.rd, S₆.wr]; exact hTr) (oT _ (.inl (Lay.wSub (by decide))))))
    fun s₇ ⟨⟨he₇, hr₇, f₇, hbx₇⟩, hrd₇, hwr₇⟩ => ?_)
  obtain S₇ := S₆.keepE dD f₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inr (.inr (.inr (.inr (.inr (Offset.sub W (by decide) (by decide)))))))
    he₇ hrd₇ hwr₇
  rw [hbx₆] at hbx₇
  refine WP.seq (WP.mono (WP.with_rdwr (cmp_ok L (by decide) (o := 112) (.inr rfl) he₇ hbx₇ h1 h16 (length_bytesAt _ _ _) hr₇))
    fun s₈ ⟨⟨he₈, hax₈, f₈⟩, hrd₈, hwr₈⟩ => ?_)
  obtain S₈ := S₇.keepE dD f₈ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inr (.inr (.inr (.inr (.inr (Offset.sub W (by decide) (by decide)))))))
    he₈ hrd₈ hwr₈
  obtain hU : bytesAt s₇.mem (W + BitVec.ofNat 64 112) t = (bytesAt s₅.mem (W + BitVec.ofNat 64 112) 16).take t := by
    rw [bytesAt_take _ _ h16, bytesAt_frame f₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide), hm₆]
  obtain hTp₅ : bytesAt s₅.mem Tp t = bytesAt s₀.mem Tp t := bytesAt_frame S₅.frame (OutWDS.frame3 oT) (by omega_arith)
  rw [hU, hm₆, hTp₅, ite_ofNat] at hax₈
  generalize hk : (if (bytesAt s₅.mem (W + BitVec.ofNat 64 112) 16).take t = bytesAt s₀.mem Tp t then 1 else 0) = k
    at hax₈
  obtain hk1 : k < 2 ^ 64 := by rw [← hk]; split <;> decide
  -- The result kept at `W + 216`.
  obtain w₉ := he₈.perm.wW (show 216 + 8 ≤ 2560 by decide)
  obtain ⟨s₉, run₉, hz₉, hg₉, hm₉, hrd₉, hwr₉⟩ : ∃ s₉, runBlock isa [.store (at_ .r15 auxO) .rax,
      .alu .test .rax (.reg .rax)] s₈ = some s₉ ∧ s₉.zf = some (decide (k = 0)) ∧ (∀ r, s₉.gpr r = s₈.gpr r) ∧
      s₉.mem = s₈.mem.writeW (W + BitVec.ofNat 64 216) (BitVec.ofNat 64 k) ∧ s₉.rd = s₈.rd ∧ s₉.wr = s₈.wr := by
    refine ⟨_, by xrun [he₈.r15, w₉], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, gpr_setReg, ite_true, hax₈, mem_setReg]
      exact congrArg some (and_self_beq hk1)
    · intro r; simp [gpr_arithFlags, gpr_setReg]
    · simp [mem_arithFlags, mem_setReg, hax₈]
    all_goals simp [rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.of_runBlock ⟨s₉, run₉, ?_⟩
  obtain f₉ : Frame [⟨W + BitVec.ofNat 64 216, 8⟩] s₈.mem s₉.mem := by
    rw [hm₉]; exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  obtain S₉ := S₈.keep dD f₉ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inr (.inr (.inr (.inl fun _ h => h)))))
    (fun r _ => hg₉ r) hrd₉ hwr₉
  obtain hax₉ : s₉.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k := by
    rw [hm₉, Mem.readW_writeW_self64]
  -- `G`, the tag and the result written since `s`, and nothing else.
  obtain wo : ∀ {d j e i : Nat}, e ≤ d → d + j ≤ e + i →
      ∀ r ∈ [(⟨W + BitVec.ofNat 64 d, j⟩ : Region)], ∃ r' ∈ [(⟨W + BitVec.ofNat 64 e, i⟩ : Region)], r.Sub r' :=
    fun h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, Offset.sub W h₁ h₂⟩
  let Wo : List Region := [⟨W + BitVec.ofNat 64 512, 512⟩, ⟨W + BitVec.ofNat 64 112, 16⟩,
    ⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 240, 32⟩]
  obtain fO : Frame Wo s.mem s₉.mem :=
    (fC.sub (rs' := Wo) fun r hr => by
      obtain ⟨r', hr', hs⟩ := wo (e := 512) (i := 512) (by omega_arith) (by omega_arith) r hr
      exact ⟨r', by simp only [List.mem_singleton] at hr'; subst hr'; simp [Wo], hs⟩).trans <|
    (fL.sub (rs' := Wo) fun r hr => by
      obtain ⟨r', hr', hs⟩ := wo (e := 512) (i := 512) (by omega_arith) (by omega_arith) r hr
      exact ⟨r', by simp only [List.mem_singleton] at hr'; subst hr'; simp [Wo], hs⟩).trans <|
    (by rw [m₄]; exact Frame.refl _ _ : Frame Wo s₃.mem s₄.mem).trans <|
    (fU.sub (rs' := Wo) fun r hr => by
      obtain ⟨r', hr', hs⟩ := wo (e := 112) (i := 16) (by omega_arith) (by omega_arith) r hr
      exact ⟨r', by simp only [List.mem_singleton] at hr'; subst hr'; simp [Wo], hs⟩).trans <|
    (by rw [hm₆]; exact Frame.refl _ _ : Frame Wo s₅.mem s₆.mem).trans <|
    (f₇.sub (rs' := Wo) fun r hr => by
      obtain ⟨r', hr', hs⟩ := wo (e := 240) (i := 32) (by omega_arith) (by omega_arith) r hr
      exact ⟨r', by simp only [List.mem_singleton] at hr'; subst hr'; simp [Wo], hs⟩).trans <|
    (f₈.sub (rs' := Wo) fun r hr => by
      obtain ⟨r', hr', hs⟩ := wo (e := 240) (i := 32) (by omega_arith) (by omega_arith) r hr
      exact ⟨r', by simp only [List.mem_singleton] at hr'; subst hr'; simp [Wo], hs⟩).trans <|
    (f₉.mono (by simp [Wo]))
  obtain dO : ∀ {d j : Nat}, 1024 ≤ d → d + j ≤ 2560 → ∀ r ∈ Wo, (⟨W + BitVec.ofNat 64 d, j⟩ : Region).Disjoint r := by
    intro d j h₁ h₂ r hr
    simp only [Wo, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact Offset.disjoint W (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  obtain hD₉ : bytesAt s₉.mem D n = bytesAt s₀.mem D n := by
    rw [bytesAt_frame fO (fun r hr => by
      simp only [Wo, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact dWD (by decide)) (by omega_arith), F.dat]
  obtain hK₉ : ∀ b, 16 * b < n → blockAt s₉.mem (W + BitVec.ofNat 64 1040 + BitVec.ofNat 64 (16 * b)) =
      ctxCiph s₀.mem Ctx R (Nat.repeat inc32 (b + 1) J) := fun b hb => by
    rw [show W + BitVec.ofNat 64 1040 + BitVec.ofNat 64 (16 * b) =
        W + BitVec.ofNat 64 1024 + BitVec.ofNat 64 (16 * (b + 1)) by
      rw [add_ofNat_ofNat, add_ofNat_ofNat, show 1040 + 16 * b = 1024 + 16 * (b + 1) by omega_arith]]
    rw [blockAt_frame fO (by rw [add_ofNat_ofNat]; exact dO (by omega_arith) (by omega_arith))]
    exact F.ks (b + 1) (by omega_arith)
  rw [hT₅] at hk
  subst hk
  exact ⟨S₉, hz₉, hax₉, hD₉, hK₉⟩

/-- After `openChk`: the data decrypted if the tags match, and `rax` the
comparison's result. -/
theorem openTail_ok {k : Nat} {s₀ s : State} {Ctx W SP Np A D : Addr} {nl al n R : Nat} {J : Block} {t K : Nat}
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (_hal5 : al < 512) (hn5 : n < 512)
    (h32 : nb16 al + nb16 n < 32) (O : OpenChk s₀ Ctx W SP A D R al n J t K s) :
    WP isa (.seq (.ite .e (.block []) (.seq (.block textArgs) (xorText false)))
        (.block [.mov .rax (.mem (at_ .r15 auxO))])) s fun s' =>
      SM s₀ Ctx W SP A D R al n J (BitVec.ofNat 64 t) s' ∧ s'.gpr .rax = BitVec.ofNat 64 K ∧
      bytesAt s'.mem D n = if K = 0 then bytesAt s₀.mem D n
        else gctr (ctxCiph s₀.mem Ctx R) (inc32 J) (bytesAt s₀.mem D n) := by
  have dD := C.dE
  have h32' := h32
  simp only [nb16] at h32'
  obtain hlead : 4 * grp al n - (nb16 al + nb16 n + 1) < 4 := by simp only [grp, nb16]; omega_arith
  obtain hna : al ≤ 16 * nb16 al ∧ 16 * nb16 al < al + 16 := by simp only [nb16]; omega_arith
  obtain hnc : n ≤ 16 * nb16 n ∧ 16 * nb16 n < n + 16 := by simp only [nb16]; omega_arith
  obtain dWD : ∀ {d j : Nat}, d + j ≤ 2560 → (⟨D, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, j⟩ :=
    fun h => dD.sub_right (Lay.wSub h)
  have S₉ := O.sm
  have hz₉ := O.zf
  have hax₉ := O.aux
  have hD₉ := O.dat
  have hK₉ := O.ks
  -- The data decrypted if the tags match.
  refine WP.seq (WP.mono (Q := fun (s₁₀ : State) => SM s₀ Ctx W SP A D R al n J (BitVec.ofNat 64 t) s₁₀ ∧
      s₁₀.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 K ∧
      bytesAt s₁₀.mem D n = if K = 0 then bytesAt s₀.mem D n
        else gctr (ctxCiph s₀.mem Ctx R) (inc32 J) (bytesAt s₀.mem D n))
    (WP.ite (decide (K = 0)) (eval_e hz₉) (fun ht => ?_) (fun hf => ?_)) fun s₁₀ h₁₀ => ?_)
  · have h0 : K = 0 := by simpa using ht
    exact WP.block_nil ⟨S₉, hax₉, by simp only [h0, ↓reduceIte]; exact hD₉⟩
  · have h0 : K ≠ 0 := by simpa using hf
    refine WP.seq ?_
    obtain ⟨s₁₀, run₁₀, di₁₀, si₁₀, dx₁₀, cx₁₀, g₁₀, m₁₀, rd₁₀, wr₁₀, z₁₀⟩ := textArgs_ok s S₉.env.r15
      S₉.env.perm.w S₉.r296 S₉.r272 S₉.r200 S₉.r208 (by omega_arith)
    refine WP.of_runBlock ⟨s₁₀, run₁₀, ?_⟩
    obtain xp : XorPre false s₁₀ D (W + BitVec.ofNat 64 1040)
        (W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1) + nb16 al))) n :=
      ⟨si₁₀, dx₁₀, di₁₀, cx₁₀, by omega_arith, by rw [rd₁₀, wr₁₀, S₉.rd, S₉.wr]; exact C.data.ok.rd,
        by rw [rd₁₀, wr₁₀]; exact covers_left (S₉.env.perm.wC (by omega_arith)),
        by rw [wr₁₀, S₉.wr]; exact C.data.wr, fun h => absurd h (by decide),
        dWD (by omega_arith), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
    refine WP.mono (xorText_ok false s₁₀ xp) fun s₁₁ ⟨m₁₁, g₁₁, rd₁₁, wr₁₁, _⟩ => ?_
    simp only [xw, Bool.false_eq_true, ↓reduceIte] at m₁₁
    obtain hxl : (xb s₁₀.mem D (W + BitVec.ofNat 64 1040) n).length = n := length_xb ..
    obtain f₁₁ : Frame [⟨D, n⟩] s.mem s₁₁.mem := by
      rw [m₁₁, m₁₀]; exact writeBytes_frame' _ (length_xb ..)
    obtain S₁₁ := S₉.keep dD f₁₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inr (.inl fun _ h => h)))
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;>
          rw [g₁₁ _ (by decide) (by decide) (by decide) (by decide),
            g₁₀ _ (by decide) (by decide) (by decide) (by decide)])
      (rd₁₁.trans rd₁₀) (wr₁₁.trans wr₁₀)
    refine ⟨S₁₁, ?_, ?_⟩
    · rw [f₁₁.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (w := 64) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dWD (by decide)).symm) (by decide), hax₉]
    · simp only [h0, ↓reduceIte]
      obtain e := bytesAt_writeBytes_self s₁₀.mem D (xb s₁₀.mem D (W + BitVec.ofNat 64 1040) n) (by rw [hxl]; omega_arith)
      rw [hxl] at e
      rw [m₁₁, e, m₁₀, xb_gctr hK₉, hD₉]
  · obtain ⟨S₁₀, hax₁₀, hD₁₀⟩ := h₁₀
    obtain q₁₀ := S₁₀.env.perm.wR (show 216 + 8 ≤ 2560 by decide)
    refine WP.run (Q := fun s₁₂ => s₁₂.gpr .rax = BitVec.ofNat 64 K ∧ (∀ r, r ≠ .rax → s₁₂.gpr r = s₁₀.gpr r) ∧
        s₁₂.mem = s₁₀.mem ∧ s₁₂.rd = s₁₀.rd ∧ s₁₂.wr = s₁₀.wr)
      ⟨_, by xrun [S₁₀.env.r15, q₁₀], by simp [gpr_setReg, hax₁₀], fun r hr => by simp [gpr_setReg, hr], by rfl,
        by rfl, by rfl⟩
      fun s₁₂ ⟨hax₁₂, hg₁₂, hm₁₂, hrd₁₂, hwr₁₂⟩ => ?_
    obtain S₁₂ := S₁₀.keep dD (rs := []) (by rw [hm₁₂]; exact Frame.refl _ _) (by simp)
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁₂ _ (by decide)) hrd₁₂ hwr₁₂
    exact ⟨S₁₂, hax₁₂, by rw [hm₁₂, hD₁₀]⟩


/-- The short `open`, after the entry and the tag's length checked, for a
12-byte nonce and at most 32 blocks to hash. -/
theorem openShort_ok (hF : ShortFacts) {pw gh : Prog isa} {tm : Mem → Mem} {k : Nat} {s₀ s₁ : State}
    {Ctx W SP Np A D : Addr} {nl al n t : Nat} {Tp : Addr}
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (hpw : PowFrom pw gh tm s₀ Ctx W SP D n)
    (E : OneEntry s₀ Ctx W SP A D n s₁)
    (hNp : s₀.gpr .rdx = Np) (hnl' : (s₀.gpr .rcx).toNat = nl) (hal' : (s₀.gpr .r9).toNat = al)
    (hnl : nl = 12) (hal5 : al < 512) (hn5 : n < 512) (h32 : nb16 al + nb16 n < 32)
    (htl : s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) (h1 : 1 ≤ t) (h16 : t ≤ 16)
    (hTa : s₀.mem.readW (SP + BitVec.ofNat 64 24) 64 = Tp)
    (hTar : InRegions (s₀.rd ++ s₀.wr) (SP + BitVec.ofNat 64 24) 8) (hTr : Covers [⟨Tp, t⟩] (s₀.rd ++ s₀.wr))
    (oT : OutWDS W D SP n ⟨Tp, t⟩) (oA : OutWDS W D SP n ⟨SP + BitVec.ofNat 64 24, 8⟩) :
    WP isa (openShort pw gh) s₁ (OpenPost s₀ Ctx W SP D n (s₀.gpr .rsi).toNat al t Tp (ctxH s₀.mem Ctx)
      (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl)) (bytesAt s₀.mem A al)) := by
  subst hnl
  refine WP.seq (WP.mono (shortStart_ok C E hNp hnl' rfl hal' hal5 hn5) fun s₂ ⟨S, haad, hdat⟩ =>
    WP.seq (WP.mono (front_ok C hpw rfl hal5 hn5 h32 (htl ▸ S) haad hdat fun _ F =>
      openChk_ok hF hpw.gh hpw.view C hal5 hn5 h32 F h1 h16 hTa hTar hTr oT oA) fun s₃ O =>
    WP.mono (openTail_ok C hal5 hn5 h32 O) fun s' ⟨S', hax, hD⟩ => ⟨S'.env, S'.saved, S'.frame, ?_⟩))
  refine ⟨hax, ?_⟩
  rw [hD]
  simp only [openK]
  split <;> rename_i h <;> simp [h]

end VG.Proof.AesGcm.X86_64.Short
